{-
 - Copyright 2026 Google LLC
 -
 - SPDX-License-Identifier: MIT
 -}

-- Prints a Guru CompiledModule as MLIR in CIRCT's dialects; see README.md for the design.

module CirctPrinter (Mode(..), ppCirctTop) where

import Data.Char (isAlpha, isAlphaNum, ord, chr)
import Data.List (intercalate, genericIndex, genericLength)
import qualified Data.Map.Strict as M
import Numeric (showHex, readOct)
import Compile
  ( Kind(..), Expr(..), Compiled(..), SysT(..), Elem(..), Reg(..), Mem(..)
  , CExpr, CompiledModule, Any, unsafeCoerce, kindSize, log2_up, regKind, memKind, memSize, memPort )
import CodePrinter
  ( ppTmp, ppReg, ppMem, ppMeth, ppFullFormat, ppCExprList, deformat, gallinaCalls
  , gallinaWidth, ppIndent )
import ModPrinter (filteredElems, ppSimIoDecls, ppGallinaDecls, ppPorts, ppTopInstantiation, memIdxWidth)

data Mode = Rtl | Sim deriving Eq

-- ---------------------------------------------------------------------------------
-- Types

-- Kinds of size 0 have no type: values of these kinds are VUnit, and zero-size struct
-- fields, union parts and ports are left out, as in ModPrinter.ppKindImmStart.
data Ty = TInt Integer | TStruct [(String, Ty)] | TArray Integer Ty | TUArray Integer Ty
  deriving (Eq, Ord)

width :: Ty -> Integer
width (TInt n) = n
width (TStruct fs) = sum (map (width . snd) fs)
width (TArray n t) = n * width t
width (TUArray n t) = n * width t

unionDataSize :: [(String, Kind)] -> Integer
unionDataSize ls = maximum (0 : map (kindSize . snd) ls)

unionTagSize :: [(String, Kind)] -> Integer
unionTagSize ls = log2_up (genericLength ls)

kty :: Kind -> Maybe Ty
kty k | kindSize k <= 0 = Nothing
kty Bool = Just (TInt 1)
kty (Bit n) = Just (TInt n)
kty (Struct ls) = Just (TStruct [(s, t) | (s, fk) <- ls, Just t <- [kty fk]])
kty (Array n k) = TArray n <$> kty k
kty (TaggedUnion ls) =
  let d = unionDataSize ls
      l = unionTagSize ls
  in Just (TStruct ([("data", TInt d) | d > 0] ++ [("tag", TInt l) | l > 0]))

ktyE :: Kind -> Ty
ktyE k = maybe (error "CirctPrinter: kind of size 0 has no type") id (kty k)

-- A struct field name, quoted unless it is an MLIR bare identifier
fieldName :: String -> String
fieldName s@(c : cs)
  | (isAlpha c || c == '_') && all (\x -> isAlphaNum x || x == '_') cs = s
fieldName s = mlirStr s

-- An MLIR string literal
mlirStr :: String -> String
mlirStr s = "\"" ++ concatMap esc s ++ "\""
  where
    esc '"' = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c | ord c < 32 || ord c > 126 = '\\' : hex2 (ord c)
          | otherwise = [c]
    hex2 x = let h = showHex x "" in if length h < 2 then '0' : h else h

-- ---------------------------------------------------------------------------------
-- The printing monad: the lines printed so far, a counter for SSA names, the type aliases
-- and the module-level declarations of the module being printed.

data V = V String Ty | VUnit

vName :: V -> String
vName (V n _) = n
vName VUnit = error "CirctPrinter: value of size 0 used"

vTy :: V -> Ty
vTy (V _ t) = t
vTy VUnit = error "CirctPrinter: value of size 0 used"

sameV :: V -> V -> Bool
sameV (V a _) (V b _) = a == b
sameV VUnit VUnit = True
sameV _ _ = False

data S = S
  { sBody :: [String]          -- reversed
  , sInd :: Int
  , sCnt :: Integer
  , sAlias :: M.Map String String
  , sAliasDefs :: [String]     -- reversed
  , sDecls :: [String]         -- reversed module-level declarations
  , sProc :: [M ()]            -- reversed statements of the RTL always block
  }

newtype M a = M { runM :: S -> (a, S) }

instance Functor M where
  fmap f (M g) = M (\s -> let (a, s') = g s in (f a, s'))

instance Applicative M where
  pure a = M (\s -> (a, s))
  M f <*> M g = M (\s -> let (h, s1) = f s; (a, s2) = g s1 in (h a, s2))

instance Monad M where
  M g >>= f = M (\s -> let (a, s1) = g s in runM (f a) s1)

getS :: M S
getS = M (\s -> (s, s))

modifyS :: (S -> S) -> M ()
modifyS f = M (\s -> ((), f s))

emit :: String -> M ()
emit l = modifyS (\s -> s { sBody = (ppIndent (sInd s) ++ l) : sBody s })

decl :: String -> M ()
decl l = modifyS (\s -> s { sDecls = ("    " ++ l) : sDecls s })

indented :: M a -> M a
indented m = do
  modifyS (\s -> s { sInd = sInd s + 1 })
  a <- m
  modifyS (\s -> s { sInd = sInd s - 1 })
  return a

-- Runs m, returning the lines it printed instead of printing them
capture :: M a -> M (a, [String])
capture m = do
  old <- sBody <$> getS
  modifyS (\s -> s { sBody = [] })
  a <- m
  new <- sBody <$> getS
  modifyS (\s -> s { sBody = old })
  return (a, reverse new)

emitLines :: [String] -> M ()
emitLines ls = modifyS (\s -> s { sBody = reverse ls ++ sBody s })

fresh :: M String
fresh = M (\s -> ("%v" ++ show (sCnt s), s { sCnt = sCnt s + 1 }))

-- The printed type; struct and array types get an alias
tyS :: Ty -> M String
tyS t = case t of
  TInt n -> return ("i" ++ show n)
  TStruct fs -> do
    ss <- mapM (\(f, ft) -> (\x -> fieldName f ++ ": " ++ x) <$> tyS ft) fs
    alias ("!hw.struct<" ++ intercalate ", " ss ++ ">")
  TArray n et -> tyS et >>= \x -> alias ("!hw.array<" ++ show n ++ "x" ++ x ++ ">")
  TUArray n et -> tyS et >>= \x -> alias ("!hw.uarray<" ++ show n ++ "x" ++ x ++ ">")
  where
    alias body = do
      s <- getS
      case M.lookup body (sAlias s) of
        Just a -> return a
        Nothing -> do
          let a = "!gk" ++ show (M.size (sAlias s))
          modifyS (\st -> st { sAlias = M.insert body a (sAlias st), sAliasDefs = (a ++ " = " ++ body) : sAliasDefs st })
          return a

inoutS :: Ty -> M String
inoutS t = (\x -> "!hw.inout<" ++ x ++ ">") <$> tyS t

-- Prints "%vN = rhs" and returns %vN
def :: Ty -> String -> M V
def t rhs = do
  n <- fresh
  emit (n ++ " = " ++ rhs)
  return (V n t)

-- ---------------------------------------------------------------------------------
-- Building blocks

lit :: Integer -> String
lit x = if x < 2 ^ (32 :: Integer) then show x else "0x" ++ showHex x ""

iconst :: Integer -> Integer -> M V
iconst w x = def (TInt w) ("hw.constant " ++ lit (x `mod` (2 ^ w)) ++ " : i" ++ show w)

true, false :: M V
true = iconst 1 1
false = iconst 1 0

-- The bits of a value (structs and arrays through hw.bitcast)
bitsOf :: V -> M V
bitsOf VUnit = return VUnit
bitsOf v@(V _ (TInt _)) = return v
bitsOf (V n t) = do
  ts <- tyS t
  def (TInt (width t)) ("hw.bitcast " ++ n ++ " : (" ++ ts ++ ") -> i" ++ show (width t))

fromBitsV :: Ty -> V -> M V
fromBitsV (TInt _) v = return v
fromBitsV t (V n (TInt w)) = do
  ts <- tyS t
  def t ("hw.bitcast " ++ n ++ " : (i" ++ show w ++ ") -> " ++ ts)
fromBitsV _ _ = error "CirctPrinter: fromBitsV of a non-integer"

-- A constant of the given type from its bits
constTy :: Ty -> Integer -> M V
constTy t x = iconst (width t) x >>= fromBitsV t

zeroOf :: Kind -> M V
zeroOf k = maybe (return VUnit) (\t -> constTy t 0) (kty k)

-- A variadic comb operation on integers
varOp :: String -> [V] -> M V
varOp _ [v] = return v
varOp op vs@(v : _) = def (vTy v) (op ++ " " ++ intercalate ", " (map vName vs) ++ " : " ++ intTy v)
varOp op [] = error ("CirctPrinter: empty " ++ op)

intTy :: V -> String
intTy v = "i" ++ show (width (vTy v))

binOp :: String -> V -> V -> M V
binOp op a b = def (vTy a) (op ++ " " ++ vName a ++ ", " ++ vName b ++ " : " ++ intTy a)

icmp :: String -> V -> V -> M V
icmp p a b = def (TInt 1) ("comb.icmp " ++ p ++ " " ++ vName a ++ ", " ++ vName b ++ " : " ++ intTy a)

notV :: V -> M V
notV v = do
  o <- iconst (width (vTy v)) (-1)
  binOp "comb.xor" v o

andV :: V -> V -> M V
andV = binOp "comb.and"

mux :: V -> V -> V -> M V
mux _ VUnit VUnit = return VUnit
mux p t f
  | sameV t f = return t
  | otherwise = do
      ts <- tyS (vTy t)
      def (vTy t) ("comb.mux " ++ vName p ++ ", " ++ vName t ++ ", " ++ vName f ++ " : " ++ ts)

-- Bits [lo, lo + w) of an integer
extract :: V -> Integer -> Integer -> M V
extract v lo w
  | lo == 0 && w == width (vTy v) = return v
  | otherwise = def (TInt w) ("comb.extract " ++ vName v ++ " from " ++ show lo ++ " : (" ++ intTy v ++ ") -> i" ++ show w)

concatV :: [V] -> M V
concatV [v] = return v
concatV vs = def (TInt (sum (map (width . vTy) vs)))
  ("comb.concat " ++ intercalate ", " (map vName vs) ++ " : " ++ intercalate ", " (map intTy vs))

-- Zero-extends or truncates an integer (VUnit is 0) to w bits
resize :: Integer -> V -> M V
resize w VUnit = iconst w 0
resize w v
  | cur == w = return v
  | cur > w = extract v 0 w
  | otherwise = do
      z <- iconst (w - cur) 0
      concatV [z, v]
  where cur = width (vTy v)

structExtract :: V -> String -> Ty -> M V
structExtract s f t = do
  ts <- tyS (vTy s)
  def t ("hw.struct_extract " ++ vName s ++ "[" ++ mlirStr f ++ "] : " ++ ts)

structCreate :: Ty -> [V] -> M V
structCreate t vs = do
  ts <- tyS t
  def t ("hw.struct_create (" ++ intercalate ", " (map vName vs) ++ ") : " ++ ts)

arrayGet :: V -> V -> M V
arrayGet a i = do
  let et = case vTy a of { TArray _ t -> t; _ -> error "CirctPrinter: array_get of a non-array" }
  ts <- tyS (vTy a)
  def et ("hw.array_get " ++ vName a ++ "[" ++ vName i ++ "] : " ++ ts ++ ", " ++ intTy i)

arrayInject :: V -> V -> V -> M V
arrayInject a i x = do
  ts <- tyS (vTy a)
  def (vTy a) ("hw.array_inject " ++ vName a ++ "[" ++ vName i ++ "], " ++ vName x ++ " : " ++ ts ++ ", " ++ intTy i)

-- Elements listed from index 0
arrayCreate :: [V] -> M V
arrayCreate vs@(v : _) = do
  ets <- tyS (vTy v)
  def (TArray (genericLength vs) (vTy v)) ("hw.array_create " ++ intercalate ", " (map vName (reverse vs)) ++ " : " ++ ets)
arrayCreate [] = error "CirctPrinter: empty array"

-- The index type of an array of n elements has log2_up n bits (0 bits for one element)
idxConst :: Integer -> Integer -> M V
idxConst n i = iconst (log2_up n) i

-- An sv variable (its value is the inout; the type is the type of its contents)
data SVar = SVar String Ty

readVar :: SVar -> M V
readVar (SVar n t) = do
  it <- inoutS t
  def t ("sv.read_inout " ++ n ++ " : " ++ it)

bpassign, passign :: SVar -> V -> M ()
bpassign (SVar n t) v = do
  ts <- tyS t
  emit ("sv.bpassign " ++ n ++ ", " ++ vName v ++ " : " ++ ts)
passign (SVar n t) v = do
  ts <- tyS t
  emit ("sv.passign " ++ n ++ ", " ++ vName v ++ " : " ++ ts)

-- A module-level sv.reg named n, optionally initialized
declReg :: String -> Ty -> Maybe V -> M SVar
declReg n t initV = do
  it <- inoutS t
  decl ("%" ++ n ++ " = sv.reg " ++ maybe "" (\v -> "init " ++ vName v ++ " ") initV ++ ": " ++ it)
  return (SVar ("%" ++ n) t)

-- Runs m under the condition (no condition: unconditionally)
guarded :: Maybe V -> M () -> M ()
guarded Nothing m = m
guarded (Just c) m = do
  emit ("sv.if " ++ vName c ++ " {")
  indented m
  emit "}"

verbatim :: String -> [V] -> M ()
verbatim txt [] = emit ("sv.verbatim " ++ mlirStr txt)
verbatim txt vs = do
  ts <- mapM (tyS . vTy) vs
  emit ("sv.verbatim " ++ mlirStr txt ++ " (" ++ intercalate ", " (map vName vs) ++ ") : " ++ intercalate ", " ts)

-- Same, with variables (inouts) as the substitutions
verbatimVars :: String -> [Either V SVar] -> M ()
verbatimVars txt args = do
  ts <- mapM (\a -> case a of Left v -> tyS (vTy v); Right (SVar _ t) -> inoutS t) args
  let ns = map (\a -> case a of Left v -> vName v; Right (SVar n _) -> n) args
  emit ("sv.verbatim " ++ mlirStr txt ++ " (" ++ intercalate ", " ns ++ ") : " ++ intercalate ", " ts)

verbatimExprSE :: Integer -> String -> M V
verbatimExprSE w txt = def (TInt w) ("sv.verbatim.expr.se " ++ mlirStr txt ++ " : () -> i" ++ show w)

-- ---------------------------------------------------------------------------------
-- Constants (extracted values; see CodePrinter.ppConst): their bits, as in evalToBit

tupleToList :: [a] -> Any -> [Any]
tupleToList [] _ = []
tupleToList (_ : xs) v = let (a, b) = unsafeCoerce v :: (Any, Any) in a : tupleToList xs b

constBits :: Kind -> Any -> Integer
constBits Bool v = if (unsafeCoerce v :: Bool) then 1 else 0
constBits (Bit n) v = (unsafeCoerce v :: Integer) `mod` (2 ^ n)
constBits (Struct ls) v =
  foldl' (\acc ((_, k), fv) -> acc * 2 ^ kindSize k + constBits k fv) 0 (zip ls (tupleToList ls v))
constBits (Array _ k) v =
  foldr (\x acc -> acc * 2 ^ kindSize k + constBits k x) 0 (unsafeCoerce v :: [Any])
constBits (TaggedUnion ls) v =
  let (d, t) = unsafeCoerce v :: (Integer, Integer)
      dl = unionDataSize ls
      tl = unionTagSize ls
  in (d `mod` (2 ^ dl)) * 2 ^ tl + (t `mod` (2 ^ tl))

-- ---------------------------------------------------------------------------------
-- Expressions (ground truth: evalExpr in Guru/Semantics.v; the Verilog of
-- CodePrinter.ppCExpr is matched where the two agree)

type Tmps = M.Map Integer V

ex :: Tmps -> CExpr -> M V
ex tmps e = case e of
  Var k (_, i) -> if kindSize k <= 0 then return VUnit
                  else return (M.findWithDefault (error ("CirctPrinter: unbound temporary " ++ show i)) i tmps)
  Const k v -> maybe (return VUnit) (\t -> constTy t (constBits k v)) (kty k)
  Or k ls -> logic "comb.or" 0 k ls
  And k ls -> logic "comb.and" (-1) k ls
  Xor k ls -> logic "comb.xor" 0 k ls
  Not k a -> case kty k of
    Nothing -> return VUnit
    Just t -> ex tmps a >>= bitsOf >>= notV >>= fromBitsV t
  TruncLsb _ lsb a -> if lsb <= 0 then return VUnit else do
    v <- ex tmps a
    extract v 0 lsb
  TruncMsb msb lsb a -> if msb <= 0 then return VUnit else do
    v <- ex tmps a
    extract v lsb msb
  UXor n a -> if n <= 0 then false else do
    v <- ex tmps a
    def (TInt 1) ("comb.parity " ++ vName v ++ " : " ++ intTy v)
  Add n ls -> arith "comb.add" 0 n ls
  Mul n ls -> arith "comb.mul" 1 n ls
  Div n a b -> if n <= 0 then return VUnit else do
    x <- ex tmps a
    y <- ex tmps b
    binOp "comb.divu" x y
  Rem n a b -> if n <= 0 then return VUnit else do
    x <- ex tmps a
    y <- ex tmps b
    binOp "comb.modu" x y
  Sll n m a b -> shift "comb.shl" n m a b
  Srl n m a b -> shift "comb.shru" n m a b
  Sra n m a b -> shift "comb.shrs" n m a b
  Concat n m a b
    | n <= 0 -> ex tmps b
    | m <= 0 -> ex tmps a
    | otherwise -> do
        x <- ex tmps a
        y <- ex tmps b
        concatV [x, y]
  ITE k p t f -> case kty k of
    Nothing -> return VUnit
    Just _ -> do
      pv <- ex tmps p
      tv <- ex tmps t
      fv <- ex tmps f
      mux pv tv fv
  Eq0 k a b -> if kindSize k <= 0 then true else do
    x <- ex tmps a >>= bitsOf
    y <- ex tmps b >>= bitsOf
    icmp "eq" x y
  Ult n a b -> if n <= 0 then false else do
    x <- ex tmps a
    y <- ex tmps b
    icmp "ult" x y
  ReadStruct ls a i ->
    let (f, fk) = genericIndex ls i
    in case kty fk of
         Nothing -> return VUnit
         Just t -> do
           s <- ex tmps a
           structExtract s f t
  ReadArray n m k a i
    | n <= 0 || kindSize k <= 0 -> zeroOf k
    | m <= 0 -> ex tmps (ReadArrayConst n k a 0)
    | otherwise -> do
        arr <- ex tmps a
        idx <- ex tmps i
        el <- resize (log2_up n) idx >>= arrayGet arr
        if n >= 2 ^ m then return el else do
          bound <- iconst m n
          ok <- icmp "ult" idx bound
          z <- zeroOf k
          mux ok el z
  ReadArrayConst n k a i
    | n <= 0 || kindSize k <= 0 -> return VUnit
    | otherwise -> do
        arr <- ex tmps a
        idxConst n i >>= arrayGet arr
  UpdateStruct ls a p v ->
    let (f, fk) = genericIndex ls p
    in if kindSize fk <= 0 then ex tmps a else do
         s <- ex tmps a
         x <- ex tmps v
         ts <- tyS (vTy s)
         def (vTy s) ("hw.struct_inject " ++ vName s ++ "[" ++ mlirStr f ++ "], " ++ vName x ++ " : " ++ ts)
  UpdateArray n k a m p v
    | n <= 0 || kindSize k <= 0 -> ex tmps a
    | m <= 0 -> ex tmps (UpdateArrayConst n k a 0 v)
    | otherwise -> do
        arr <- ex tmps a
        idx <- ex tmps p
        x <- ex tmps v
        upd <- resize (log2_up n) idx >>= \i' -> arrayInject arr i' x
        if n >= 2 ^ m then return upd else do
          bound <- iconst m n
          ok <- icmp "ult" idx bound
          mux ok upd arr
  UpdateArrayConst n k a i v
    | n <= 0 || kindSize k <= 0 -> ex tmps a
    | otherwise -> do
        arr <- ex tmps a
        x <- ex tmps v
        idx <- idxConst n i
        arrayInject arr idx x
  ToBit _ a -> ex tmps a >>= bitsOf
  FromBit k a -> case kty k of
    Nothing -> return VUnit
    Just t -> ex tmps a >>= fromBitsV t
  ReadUnionTag ls a i ->
    let l = unionTagSize ls
    in if l <= 0 then true else do
         u <- ex tmps a
         tg <- structExtract u "tag" (TInt l)
         c <- iconst l i
         icmp "eq" tg c
  ReadUnionData ls a i ->
    let fk = snd (genericIndex ls i)
        d = unionDataSize ls
    in case kty fk of
         Nothing -> return VUnit
         Just t -> do
           u <- ex tmps a
           dv <- structExtract u "data" (TInt d)
           extract dv 0 (kindSize fk) >>= fromBitsV t
  BuildUnion ls i a -> case kty (TaggedUnion ls) of
    Nothing -> return VUnit
    Just t -> do
      let d = unionDataSize ls
          l = unionTagSize ls
      dv <- if d > 0 then (: []) <$> (ex tmps a >>= bitsOf >>= resize d) else return []
      tv <- if l > 0 then (: []) <$> iconst l i else return []
      structCreate t (dv ++ tv)
  BuildStruct ls vals -> case kty (Struct ls) of
    Nothing -> return VUnit
    Just t -> do
      vs <- mapM (\((_, fk), v) -> if kindSize fk > 0 then (: []) <$> ex tmps (unsafeCoerce v :: CExpr) else return [])
                 (zip ls (tupleToList ls vals))
      structCreate t (concat vs)
  BuildArray _ k vals -> case kty k of
    Nothing -> return VUnit
    Just _ -> if null vals then return VUnit else mapM (ex tmps) vals >>= arrayCreate
  where
    logic op identity k ls = case kty k of
      Nothing -> return VUnit
      Just t -> do
        bs <- mapM (\x -> ex tmps x >>= bitsOf) ls
        r <- if null bs then iconst (width t) identity else varOp op bs
        fromBitsV t r
    arith op identity n ls
      | n <= 0 = return VUnit
      | null ls = iconst n identity
      | otherwise = mapM (ex tmps) ls >>= varOp op
    -- Shifting by the width or more gives 0 (all sign bits for comb.shrs), as in Verilog
    shift op n m a b
      | n <= 0 = return VUnit
      | m <= 0 = ex tmps a
      | otherwise = do
          x <- ex tmps a
          y <- ex tmps b
          if m <= n then resize n y >>= binOp op x else do
            lo <- extract y 0 n
            hi <- extract y n (m - n)
            z <- iconst (m - n) 0
            big <- icmp "ne" hi z
            r <- binOp op x lo
            over <- if op == "comb.shrs" then iconst n (n - 1) >>= binOp op x else iconst n 0
            mux big over r

-- ---------------------------------------------------------------------------------
-- Compiled code

data MemSt = MemSt { mRq :: [V], mRqEn :: [V], mWrIdx :: V, mWrVal :: V, mWrEn :: V }

data Env = Env
  { eTmps :: Tmps
  , eRegs :: M.Map Integer V            -- register shadows
  , eSends :: M.Map Integer (V, V)      -- RTL: Send value and enable
  , eMems :: M.Map Integer MemSt        -- RTL: memory request ports
  , ePath :: Maybe V                    -- path condition (Nothing is true)
  }

data MemInfo = MemInfo { miRam :: SVar, miRp :: [SVar] }

data Ctx = Ctx
  { cMode :: Mode
  , cSimIoWidth :: Integer
  , cGallinaWidth :: Integer
  , cGallinaCycle :: Maybe SVar          -- Sim: guru_gallina_cycle
  , cRecvs :: M.Map Integer V           -- RTL: Recv ports
  , cMemRp :: M.Map Integer V           -- RTL: memory response ports
  , cMems :: M.Map Integer MemInfo      -- Sim: memory arrays
  }

bindTmp :: Integer -> V -> Env -> Env
bindTmp i v env = env { eTmps = M.insert i v (eTmps env) }

-- Merges the states after the two branches of an if-then-else
merge :: V -> Env -> Env -> Env -> M Env
merge p env t f = do
  regs <- sequence (M.unionWith (\a b -> do { x <- a; y <- b; mux p x y })
                       (M.map return (eRegs t)) (M.map return (eRegs f)))
  sends <- sequence (M.intersectionWith (\(tv, te) (fv, fe) -> do { v <- mux p tv fv; en <- mux p te fe; return (v, en) })
                       (eSends t) (eSends f))
  mems <- sequence (M.intersectionWith mergeMem (eMems t) (eMems f))
  return env { eRegs = regs, eSends = sends, eMems = mems }
  where
    mergeMem a b = do
      rq <- sequence (zipWith (mux p) (mRq a) (mRq b))
      rqEn <- sequence (zipWith (mux p) (mRqEn a) (mRqEn b))
      wi <- mux p (mWrIdx a) (mWrIdx b)
      wv <- mux p (mWrVal a) (mWrVal b)
      we <- mux p (mWrEn a) (mWrEn b)
      return (MemSt rq rqEn wi wv we)

andPath :: Maybe V -> V -> M (Maybe V)
andPath Nothing c = return (Just c)
andPath (Just p) c = Just <$> andV p c

-- An RTL statement of the always block, run under the path condition
deferProc :: Maybe V -> M () -> M ()
deferProc p m = modifyS (\s -> s { sProc = guarded p m : sProc s })

-- A Sim side effect whose result (w bits) is kept in its own variable
siteResult :: String -> Integer -> Maybe V -> (M V) -> M V
siteResult name w p call = do
  var <- declReg name (TInt w) Nothing
  guarded p (call >>= bpassign var)
  readVar var

execC :: Ctx -> Env -> Compiled -> M (Env, ((String, Integer), V))
execC ctx env c = case c of
  CReadReg (_, ri) k (_, ti) rest ->
    let v = if kindSize k > 0 then M.findWithDefault (error "CirctPrinter: unknown register") ri (eRegs env) else VUnit
    in next (bindTmp ti v env) rest
  CWriteReg (_, ri) k val rest ->
    if kindSize k <= 0 then next env rest else do
      v <- ex tmps val
      next env { eRegs = M.insert ri v (eRegs env) } rest
  CReadRqMem (_, mi) sz k ports i p rest ->
    if not (isMem sz k ports) then next env rest else do
      idx <- ex tmps i
      case mode of
        Rtl -> do
          let MemSt rq rqEn wi wv we = memSt mi
              lg = memIdxWidth sz
          idx' <- resize lg idx
          t <- true
          next env { eMems = M.insert mi (MemSt (setAt p idx' rq) (setAt p t rqEn) wi wv we) (eMems env) } rest
        Sim -> do
          let info = cMems ctx M.! mi
          ok <- inRange sz idx
          idx' <- resize (log2_up sz) idx
          guarded (ePath env) $ do
            slot <- arrayIndexInOut (miRam info) idx'
            el <- readVar slot
            z <- zeroOf k
            r <- mux ok el z
            bpassign (genericIndex (miRp info) p) r
          next env rest
  CReadRpMem (_, mi) sz k ports p (s, ti) rest ->
    if not (isMem sz k ports) then next (bindTmp ti VUnit env) rest else
      case mode of
        Rtl -> do
          let rp = cMemRp ctx M.! mi
          v <- idxConst ports p >>= arrayGet rp
          next (bindTmp ti v env) rest
        Sim -> do
          let info = cMems ctx M.! mi
              t = ktyE k
          var <- declReg ("rp_" ++ ppTmp (s, ti)) t Nothing
          readVar (genericIndex (miRp info) p) >>= bpassign var
          v <- readVar var
          next (bindTmp ti v env) rest
  CWriteMem (_, mi) sz k ports i val rest ->
    if not (isMem sz k ports) then next env rest else do
      idx <- ex tmps i
      v <- ex tmps val
      case mode of
        Rtl -> do
          let MemSt rq rqEn _ _ _ = memSt mi
          idx' <- resize (memIdxWidth sz) idx
          t <- true
          next env { eMems = M.insert mi (MemSt rq rqEn idx' v t) (eMems env) } rest
        Sim -> do
          let info = cMems ctx M.! mi
          ok <- inRange sz idx
          cond <- andPath (ePath env) ok
          idx' <- resize (log2_up sz) idx
          guarded cond $ do
            slot <- arrayIndexInOut (miRam info) idx'
            bpassign slot v
          next env rest
  CSend meth@(_, si) k e rest -> do
    v <- if kindSize k > 0 then ex tmps e else return VUnit
    case mode of
      Rtl -> do
        t <- true
        next env { eSends = M.insert si (v, t) (eSends env) } rest
      Sim -> do
        let call = "sim_io.send(\"" ++ ppMeth "Send" meth ++ "\", "
        case v of
          VUnit -> guarded (ePath env) (verbatim (call ++ "'0);") [])
          _ -> do
            b <- bitsOf v >>= resize (cSimIoWidth ctx)
            guarded (ePath env) (verbatim (call ++ "{{0}});") [b])
        next env rest
  CRecv meth@(_, ri) k tmp@(_, ti) rest ->
    case kty k of
      Nothing -> next (bindTmp ti VUnit env) rest
      Just t -> case mode of
        Rtl -> next (bindTmp ti (cRecvs ctx M.! ri) env) rest
        Sim -> do
          let w = cSimIoWidth ctx
          r <- siteResult ("recv_" ++ ppTmp tmp) w (ePath env)
                 (verbatimExprSE w ("sim_io.recv(\"" ++ ppMeth "Recv" meth ++ "\")"))
          v <- extract r 0 (width t) >>= fromBitsV t
          next (bindTmp ti v env) rest
  CLetExpr (_, ti) k e rest -> do
    v <- if kindSize k > 0 then ex tmps e else return VUnit
    next (bindTmp ti v env) rest
  CLetAction _ act rest -> do
    (env1, ((_, ti), v)) <- execC ctx env act
    next (bindTmp ti v env1 { eTmps = tmps }) rest
  CNonDet tmp@(_, ti) k rest -> case kty k of
    Nothing -> next (bindTmp ti VUnit env) rest
    Just t -> do
      let n = width t
          words32 = (n + 31) `div` 32
          rnd = verbatimExprSE (32 * words32) ("{" ++ intercalate ", " (replicate (fromInteger words32) "$urandom()") ++ "}")
      r <- case mode of
        Sim -> siteResult ("nondet_" ++ ppTmp tmp) (32 * words32) (ePath env) rnd
        Rtl -> do
          var <- declReg ("nondet_" ++ ppTmp tmp) (TInt (32 * words32)) Nothing
          deferProc Nothing (rnd >>= passign var)
          readVar var
      v <- extract r 0 n >>= fromBitsV t
      next (bindTmp ti v env) rest
  -- Both branches are evaluated and their results merged with comb.mux, in both modes (the
  -- side effects of the simulation mode are guarded by the path conditions of the branches)
  CIfElse p _ t f rest -> do
    pv <- ex tmps p
    np <- notV pv
    pt <- andPath (ePath env) pv
    pf <- andPath (ePath env) np
    (envT, ((_, ti), vT)) <- execC ctx env { ePath = pt } t
    (envF, (_, vF)) <- execC ctx env { ePath = pf } f
    env' <- merge pv env envT envF
    v <- mux pv vT vF
    next (bindTmp ti v env') rest
  CSys ls rest -> do
    mapM_ sys ls
    next env rest
  CReturn tmp k val -> do
    v <- if kindSize k > 0 then ex tmps val else return VUnit
    return (env, (tmp, v))
  CCallGallina (_, gIdx) kIn e kOut _ tmp@(_, site) rest -> case mode of
    Rtl -> error "CirctPrinter: CallGallina is specification-only and has no RTL"
    Sim -> do
      let gw = cGallinaWidth ctx
          Just cyc = cGallinaCycle ctx
      inV <- if kindSize kIn > 0 then ex tmps e >>= bitsOf >>= resize gw else iconst gw 0
      out <- declReg ("gallina_" ++ ppTmp tmp) (TInt gw) Nothing
      guarded (ePath env) $ do
        cv <- readVar cyc
        verbatimVars ("guru_gallina_call(" ++ show site ++ ", " ++ show gIdx ++ ", {{0}}, {{1}}, {{2}});")
                     [Left cv, Left inV, Right out]
      v <- case kty kOut of
        Nothing -> return VUnit
        Just t -> readVar out >>= \o -> extract o 0 (width t) >>= fromBitsV t
      -- the call site is the index of the output temporary
      next (bindTmp site v env) rest
  where
    mode = cMode ctx
    tmps = eTmps env
    next = execC ctx
    isMem sz k ports = kindSize k > 0 && sz > 0 && ports > 0
    memSt mi = M.findWithDefault (error "CirctPrinter: unknown memory") mi (eMems env)
    setAt p x xs = [if j == p then x else y | (j, y) <- zip [0 ..] xs]
    inRange sz idx = if sz >= 2 ^ width (vTy idx) then true else do
      b <- iconst (width (vTy idx)) sz
      icmp "ult" idx b
    sys (DispString s) = do
      let fmt = vUnescape (deformat s)
      case mode of
        Sim -> guarded (ePath env) (emit ("sv.write " ++ mlirStr fmt))
        Rtl -> deferProc (ePath env) (emit ("sv.write " ++ mlirStr fmt))
    sys (DispExpr k e f) =
      if kindSize k <= 0 then return () else do
        vs <- mapM (\x -> ex tmps x >>= bitsOf) (ppCExprList k e)
        let w = do
              ts <- mapM (tyS . vTy) vs
              emit ("sv.write " ++ mlirStr (ppFullFormat f) ++ "(" ++ intercalate ", " (map vName vs) ++ ") : " ++ intercalate ", " ts)
        case mode of
          Sim -> guarded (ePath env) w
          Rtl -> deferProc (ePath env) w
    sys Finish = case mode of
      Sim -> guarded (ePath env) (emit "sv.finish 1")
      Rtl -> deferProc (ePath env) (emit "sv.finish 1")

arrayIndexInOut :: SVar -> V -> M SVar
arrayIndexInOut (SVar n t@(TUArray _ et)) i = do
  it <- inoutS t
  s <- fresh
  emit (s ++ " = sv.array_index_inout " ++ n ++ "[" ++ vName i ++ "] : " ++ it ++ ", " ++ intTy i)
  return (SVar s et)
arrayIndexInOut _ _ = error "CirctPrinter: array_index_inout of a non-array"

-- Undoes the escapes of a Verilog string literal: a DispString is printed by PrettyPrinter
-- as the literal of $write, while the format string of sv.write is the text itself
vUnescape :: String -> String
vUnescape ('\\' : c : rest) = case c of
  'n' -> '\n' : vUnescape rest
  't' -> '\t' : vUnescape rest
  'r' -> '\r' : vUnescape rest
  '\\' -> '\\' : vUnescape rest
  '"' -> '"' : vUnescape rest
  _ | isOct c ->
        let (ds, rest') = span isOct (c : rest)
            (d3, more) = splitAt 3 ds
        in case readOct d3 of
             ((x, _) : _) -> chr x : vUnescape (more ++ rest')
             [] -> '\\' : vUnescape (c : rest)
    | otherwise -> '\\' : c : vUnescape rest
  where isOct x = x >= '0' && x <= '7'
vUnescape (x : rest) = x : vUnescape rest
vUnescape [] = []

-- ---------------------------------------------------------------------------------
-- Modules

type Elems = [(Integer, (String, Elem))]

-- The reset value of a register, if any
regInit :: Kind -> Maybe Any -> Maybe Integer
regInit k = fmap (constBits k)

-- core_design in RTL mode
ppCoreRtl :: Elems -> Compiled -> M ()
ppCoreRtl elems code = do
  -- ports: Sends and Recvs, then the memory ports, then clk and rst_n (see ModPrinter)
  ioPorts <- concat <$> mapM ioPort elems
  memPorts <- concat <$> mapM memPortDecls elems
  emit ("hw.module @core_design(" ++ intercalate ", " (ioPorts ++ memPorts ++ ["in %clk : i1", "in %rst_n : i1"]) ++ ") {")
  indented $ do
    t <- true
    clock <- def (TInt 1) "seq.to_clock %clk"
    rst <- binOp "comb.xor" (V "%rst_n" (TInt 1)) t
    let regs = M.fromList [(i, V ("%" ++ "decl_" ++ ppReg (s, i)) (ktyE (regKind r))) | (i, (s, EReg r)) <- elems]
        recvs = M.fromList [(i, V ("%" ++ ppMeth "Recv" (s, i)) (ktyE k)) | (i, (s, ERecv k)) <- elems]
        rps = M.fromList [(i, V ("%" ++ ppMem "Rp" (s, i)) (TArray (memPort m) (ktyE (memKind m)))) | (i, (s, EMem m)) <- elems]
    sends0 <- M.fromList <$> sequence [ do { z <- zeroOf k; f <- false; return (i, (z, f)) } | (i, (_, ESend k)) <- elems ]
    mems0 <- M.fromList <$> sequence [ do
               let lg = memIdxWidth (memSize m)
               rq <- mapM (const (iconst lg 0)) [1 .. memPort m]
               en <- mapM (const false) [1 .. memPort m]
               wi <- iconst lg 0
               wv <- zeroOf (memKind m)
               we <- false
               return (i, MemSt rq en wi wv we)
             | (i, (_, EMem m)) <- elems ]
    let ctx = Ctx Rtl 0 0 Nothing recvs rps M.empty
        env0 = Env M.empty regs sends0 mems0 Nothing
    (env, _) <- execC ctx env0 code
    -- registers
    sequence_ [ do
        let V n ty = regs M.! i
            nextV = eRegs env M.! i
        ts <- tyS ty
        case regInit (regKind r) initVal of
          Just bits -> do
            iv <- constTy ty bits
            emit (n ++ " = seq.firreg " ++ vName nextV ++ " clock " ++ vName clock ++ " reset async " ++ vName rst ++ ", " ++ vName iv ++ " : " ++ ts)
          Nothing -> emit (n ++ " = seq.firreg " ++ vName nextV ++ " clock " ++ vName clock ++ " : " ++ ts)
      | (i, (_, EReg r@(Build_Reg _ initVal))) <- elems ]
    -- displays, Finish and NonDet
    ds <- reverse . sDecls <$> getS
    modifyS (\s -> s { sDecls = [] })
    emitLines ds
    procs <- reverse . sProc <$> getS
    if null procs then return () else do
      emit "sv.always posedge %clk {"
      indented $ do
        emit "sv.if %rst_n {"
        indented (sequence_ procs)
        emit "}"
      emit "}"
    -- outputs
    let outs = concat [ case e of
                          ESend k -> let (v, en) = eSends env M.! i in [v | kindSize k > 0] ++ [en]
                          _ -> []
                      | (i, (_, e)) <- elems ]
    memOuts <- concat <$> sequence [ do
                 let MemSt rq en wi wv we = eMems env M.! i
                 rqA <- arrayCreate rq
                 enA <- arrayCreate en
                 return ([rqA, enA, wi] ++ [wv] ++ [we])
               | (i, (_, EMem _)) <- elems ]
    let allOuts = outs ++ memOuts
    if null allOuts then emit "hw.output" else do
      ts <- mapM (tyS . vTy) allOuts
      emit ("hw.output " ++ intercalate ", " (map vName allOuts) ++ " : " ++ intercalate ", " ts)
  emit "}"
  where
    memPortDecls (i, (s, EMem m)) = map snd <$> memInterface (s, i) m "decl_" True
    memPortDecls _ = return []

-- The Send and Recv ports of core_design and top
ioPort :: (Integer, (String, Elem)) -> M [String]
ioPort (i, (s, ESend k)) = do
  ps <- case kty k of
    Just t -> (\ts -> ["out decl_" ++ ppMeth "Send" (s, i) ++ " : " ++ ts]) <$> tyS t
    Nothing -> return []
  return (ps ++ ["out decl_" ++ ppMeth "SendEn" (s, i) ++ " : i1"])
ioPort (i, (s, ERecv k)) = (\ts -> ["in %" ++ ppMeth "Recv" (s, i) ++ " : " ++ ts]) <$> tyS (ktyE k)
ioPort _ = return []

-- The ports of a memory, from the point of view of core_design (isCore) or verilog_mem
memInterface :: (String, Integer) -> Mem -> String -> Bool -> M [(Integer, String)]
memInterface si@(_, i) m pre isCore = do
  let lg = memIdxWidth (memSize m)
      p = memPort m
      t = ktyE (memKind m)
      o = if isCore then "out " else "in %"
      inp = if isCore then "in %" else "out "
      nm which = if isCore then pre ++ ppMem which si else which
      rpName = if isCore then ppMem "Rp" si else "Rp"
  rqT <- tyS (TArray p (TInt lg))
  enT <- tyS (TArray p (TInt 1))
  vT <- tyS t
  rpT <- tyS (TArray p t)
  return [ (i, o ++ nm "Rq" ++ " : " ++ rqT), (i, o ++ nm "RqEn" ++ " : " ++ enT)
         , (i, o ++ nm "WrIdx" ++ " : i" ++ show lg), (i, o ++ nm "WrVal" ++ " : " ++ vT)
         , (i, o ++ nm "WrEn" ++ " : i1"), (i, inp ++ rpName ++ " : " ++ rpT) ]

-- top in RTL mode: core_design and an instance of verilog_mem (Verilog/GuruLibrary.sv) per
-- memory, as in Rtl.sv. Returns the hw.module.extern declarations of verilog_mem.
ppTopRtl :: Elems -> M [String]
ppTopRtl elems = do
  ports <- concat <$> mapM ioPort elems
  -- one extern declaration of verilog_mem per memory, with its own port types and parameters
  externs <- concat <$> mapM extern elems
  emit ("hw.module @top(" ++ intercalate ", " (ports ++ ["in %clk : i1", "in %rst_n : i1"]) ++ ") {")
  indented $ do
    -- in the order of the ports of core_design: Sends and Recvs, then the memory ports
    coreIns <- (++) <$> (concat <$> mapM coreIn [e | e@(_, (_, ERecv _)) <- elems])
                    <*> (concat <$> mapM coreIn [e | e@(_, (_, EMem _)) <- elems])
    coreOuts <- (++) <$> (concat <$> mapM coreOut [e | e@(_, (_, ESend _)) <- elems])
                     <*> (concat <$> mapM coreOut [e | e@(_, (_, EMem _)) <- elems])
    let ins = coreIns ++ [("clk", "%clk", "i1"), ("rst_n", "%rst_n", "i1")]
        resNames = [r | (_, r, _) <- coreOuts]
    emit ((if null resNames then "" else intercalate ", " resNames ++ " = ")
          ++ "hw.instance \"core_design_inst\" @core_design("
          ++ intercalate ", " [n ++ ": " ++ v ++ ": " ++ t | (n, v, t) <- ins] ++ ") -> ("
          ++ intercalate ", " [n ++ ": " ++ t | (n, _, t) <- coreOuts] ++ ")")
    mapM_ memInst elems
    let sendOuts = [(r, t) | (n, r, t) <- coreOuts, not (isMemPort n)]
    if null sendOuts then emit "hw.output" else
      emit ("hw.output " ++ intercalate ", " (map fst sendOuts) ++ " : " ++ intercalate ", " (map snd sendOuts))
  emit "}"
  return externs
  where
    -- the memory ports of core_design are decl_memRq_..., decl_memRqEn_..., and so on
    isMemPort n = take 8 n == "decl_mem"
    coreIn (i, (s, ERecv k)) = (\ts -> [(ppMeth "Recv" (s, i), "%" ++ ppMeth "Recv" (s, i), ts)]) <$> tyS (ktyE k)
    coreIn (i, (s, EMem m)) = (\ts -> [(ppMem "Rp" (s, i), "%" ++ ppMem "Rp" (s, i), ts)]) <$> tyS (TArray (memPort m) (ktyE (memKind m)))
    coreIn _ = return []
    coreOut (i, (s, ESend k)) = do
      ps <- case kty k of
        Just t -> (\ts -> [("decl_" ++ ppMeth "Send" (s, i), "%core_" ++ ppMeth "Send" (s, i), ts)]) <$> tyS t
        Nothing -> return []
      return (ps ++ [("decl_" ++ ppMeth "SendEn" (s, i), "%core_" ++ ppMeth "SendEn" (s, i), "i1")])
    coreOut (i, (s, EMem m)) = do
      let lg = memIdxWidth (memSize m)
          p = memPort m
      rqT <- tyS (TArray p (TInt lg))
      enT <- tyS (TArray p (TInt 1))
      vT <- tyS (ktyE (memKind m))
      return [ ("decl_" ++ ppMem w (s, i), "%core_" ++ ppMem w (s, i), t)
             | (w, t) <- [("Rq", rqT), ("RqEn", enT), ("WrIdx", "i" ++ show lg), ("WrVal", vT), ("WrEn", "i1")] ]
    coreOut _ = return []
    -- the parameters of verilog_mem, as printed by ModPrinter.ppMemParams
    params m = case m of
      Build_Mem n k p initVal ->
        let base = [("n", 32, n), ("clgn", 32, memIdxWidth n), ("sizeK", 32, kindSize k), ("p", 32, p)]
        in base ++ case initVal of
             Just (Just val) -> [("init", 32, 1), ("def", 32, 0), ("initVal", n * kindSize k, constBits (Array n k) val)]
             Just Nothing -> [("init", 32, 1), ("def", 32, 1)]
             Nothing -> [("init", 32, 0)]
    extern (i, (s, EMem m)) = do
      ps <- memInterface (s, i) m "" False
      let decls = intercalate ", " [n ++ ": i" ++ show w | (n, w, _) <- params m]
      return ["hw.module.extern @verilog_mem_" ++ show i ++ "<" ++ decls ++ ">("
              ++ intercalate ", " (map snd ps ++ ["in %clk : i1", "in %rst_n : i1"])
              ++ ") attributes {verilogName = \"verilog_mem\"}"]
    extern _ = return []
    memInst (i, (s, EMem m)) = do
      let lg = memIdxWidth (memSize m)
          p = memPort m
      rqT <- tyS (TArray p (TInt lg))
      enT <- tyS (TArray p (TInt 1))
      vT <- tyS (ktyE (memKind m))
      rpT <- tyS (TArray p (ktyE (memKind m)))
      let ins = [ (w, "%core_" ++ ppMem w (s, i), t)
                | (w, t) <- [("Rq", rqT), ("RqEn", enT), ("WrIdx", "i" ++ show lg), ("WrVal", vT), ("WrEn", "i1")] ]
                ++ [("clk", "%clk", "i1"), ("rst_n", "%rst_n", "i1")]
          ps = intercalate ", " [n ++ ": i" ++ show w ++ " = " ++ lit v | (n, w, v) <- params m]
      emit ("%" ++ ppMem "Rp" (s, i) ++ " = hw.instance " ++ mlirStr (ppMem "" (s, i)) ++ " @verilog_mem_" ++ show i
            ++ "<" ++ ps ++ ">(" ++ intercalate ", " [n ++ ": " ++ v ++ ": " ++ t | (n, v, t) <- ins]
            ++ ") -> (Rp: " ++ rpT ++ ")")
    memInst _ = return ()

-- core_design in simulation mode
ppCoreSim :: Elems -> Compiled -> M ()
ppCoreSim elems code = do
  emit "hw.module @core_design(in %clk : i1, in %rst_n : i1) {"
  indented $ do
    let calls = gallinaCalls code
        ioSizes = [kindSize k | (_, (_, ESend k)) <- elems] ++ [kindSize k | (_, (_, ERecv k)) <- elems]
        simIoWidth = maximum (1 : ioSizes)
        gw = gallinaWidth calls
        regVars = M.fromList [(i, SVar ("%decl_" ++ ppReg (s, i)) (ktyE (regKind r))) | (i, (s, EReg r)) <- elems]
    -- registers
    sequence_ [ do { it <- inoutS t; decl (n ++ " = sv.reg : " ++ it) } | SVar n t <- M.elems regVars ]
    -- guru_gallina_cycle
    cyc <- if null calls then return Nothing else Just <$> declReg "guru_gallina_cycle" (TInt 64) Nothing
    -- memories: the array and one response variable per port, initialized in an initial block
    (mems, memInit) <- capture (indented (indented (fmap M.fromList (sequence [ simMem i s m | (i, (s, EMem m)) <- elems ]))))
    let ctx = Ctx Sim simIoWidth gw cyc M.empty M.empty mems
    -- the clock cycle
    ((), cycleLines) <- capture $ indented $ indented $ do
      regs <- M.fromList <$> sequence [ (,) i <$> readVar v | (i, v) <- M.toList regVars ]
      (env, _) <- execC ctx (Env M.empty regs M.empty M.empty Nothing) code
      sequence_ [ if sameV (regs M.! i) nv then return () else passign (regVars M.! i) nv
                | (i, nv) <- M.toList (eRegs env) ]
      case cyc of
        Just cv -> do
          x <- readVar cv
          one <- iconst 64 1
          binOp "comb.add" x one >>= bpassign cv
        Nothing -> return ()
    ((), resetLines) <- capture $ indented $ indented $ do
      sequence_ [ case regInit (regKind r) initVal of
                    Just bits -> constTy t bits >>= passign v
                    Nothing -> return ()
                | (i, (_, EReg r@(Build_Reg _ initVal))) <- elems, let v@(SVar _ t) = regVars M.! i ]
      case cyc of
        Just cv -> do
          verbatim "guru_gallina_reset();" []
          iconst 64 0 >>= bpassign cv
        Nothing -> return ()
    ds <- reverse . sDecls <$> getS
    modifyS (\s -> s { sDecls = [] })
    emitLines ds
    if null memInit then return () else do
      emit "sv.initial {"
      emitLines memInit
      emit "}"
    emit "sv.always posedge %clk, negedge %rst_n {"
    indented $ do
      emit "sv.if %rst_n {"
      emitLines cycleLines
      emit "} else {"
      emitLines resetLines
      emit "}"
    emit "}"
    emit "hw.output"
  emit "}"
  where
    simMem i s m@(Build_Mem n k p initVal) = do
      let t = ktyE k
      zero <- constTy t 0
      ram <- declReg (ppMem "Ram" (s, i)) (TUArray n t) Nothing
      rps <- mapM (\j -> do
                     z <- constTyDecl t
                     declReg (ppMem "Rp" (s, i) ++ "_" ++ show j) t (Just z))
                  [0 .. p - 1]
      let vals = case initVal of
            Just (Just val) -> map (constBits k) (unsafeCoerce val :: [Any])
            _ -> replicate (fromInteger n) 0
      sequence_ [ do
                    idx <- idxConst n j
                    slot <- arrayIndexInOut ram idx
                    v <- if x == 0 then return zero else constTy t x
                    bpassign slot v
                | (j, x) <- zip [0 ..] vals ]
      let _ = m
      return (i, MemInfo ram rps)
    -- a constant at module level, for the initializer of a declaration
    constTyDecl t = do
      ((v, ls)) <- capture (constTy t 0)
      mapM_ (\l -> decl (dropWhile (== ' ') l)) ls
      return v

ppTopSim :: M ()
ppTopSim = do
  emit "hw.module @top(in %clk : i1, in %rst_n : i1) {"
  indented $ do
    emit "hw.instance \"core_design_inst\" @core_design(clk: %clk: i1, rst_n: %rst_n: i1) -> ()"
    emit "hw.output"
  emit "}"

-- The tb module of ModPrinter.ppTop
ppTb :: Mode -> Elems -> String
ppTb mode elems =
  "`ifndef SYNTHESIS\n"
  ++ "// synopsys translate_off\n"
  ++ "module tb();\n"
  ++ "  logic clk;\n  logic rst_n;\n\n"
  ++ (if mode == Sim then "" else ppPorts ";" False 1 elems ++ "\n")
  ++ ppTopInstantiation 1 (if mode == Sim then [] else elems) ++ "\n"
  ++ "  initial begin\n"
  ++ "    clk = 1'h0;\n    rst_n = 1'h0;\n"
  ++ "    #40;\n"
  ++ "    rst_n = 1'h1;\n"
  ++ "    #2000 $finish;\n"
  ++ "  end\n\n"
  ++ "  always begin\n"
  ++ "    #10;\n"
  ++ "    clk = 1'h1;\n"
  ++ "    #10;\n"
  ++ "    clk = 1'h0;\n"
  ++ "  end\n\n"
  ++ "endmodule\n"
  ++ "// synopsys translate_on\n"
  ++ "`endif\n"

-- The whole MLIR file
ppCirctTop :: Mode -> CompiledModule -> String
ppCirctTop mode (((_, tree), _), code) =
  let elems = filteredElems tree
      calls = gallinaCalls code
      s0 = S [] 1 0 M.empty [] [] []
      body = case mode of
        Rtl -> do
          ppCoreRtl elems code
          ppTopRtl elems
        Sim -> do
          ppCoreSim elems code
          ppTopSim
          return []
      (externs, s) = runM body s0
      -- GuruLibrary.sv has verilog_mem, the memories of the RTL mode
      header = case mode of
        Sim -> "`include \"GuruLibrary.sv\"\n" ++ ppSimIoDecls 0 elems ++ "\n" ++ ppGallinaDecls calls
        Rtl -> "`include \"GuruLibrary.sv\"\n"
  in unlines $
       [ "// Generated by GuruCirct from a Guru compiled module (" ++ (if mode == Sim then "simulation" else "RTL") ++ " mode)." ]
       ++ reverse (sAliasDefs s)
       ++ [ "module attributes {circt.loweringOptions = \"locationInfoStyle=none,omitVersionComment\"} {"
          , "  sv.verbatim " ++ mlirStr header ]
       ++ map ("  " ++) externs
       ++ reverse (sBody s)
       ++ [ "  sv.verbatim " ++ mlirStr (ppTb mode elems)
          , "}" ]
