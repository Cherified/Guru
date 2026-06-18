module CodePrinter where

import Numeric
import Data.Char (intToDigit)
import Data.List (intercalate, genericIndex)
import Compile
import GHC.Num (integerToInt)

getStringFields :: (Kind -> a -> String) -> [(String, Kind)] -> b -> [String]
getStringFields f [] _ = []
getStringFields f ((s, k): xs) val = let (v1, v2) = unsafeCoerce val :: (a, b) in
                                     let rest = getStringFields f xs v2 in
                                     if (kindSize k > 0)
                                     then f k v1 : rest
                                     else rest

ppConst :: Kind -> Any -> String
ppConst Bool val = if (unsafeCoerce val :: Prelude.Bool) then "1\'h1" else "1\'h0"
ppConst (Bit n) val = show n ++ "\'h" ++ (showIntAtBase 16 intToDigit (unsafeCoerce val :: Integer) "")
ppConst (Struct ls) val = '{' : intercalate ", " (getStringFields ppConst ls val) ++ "}"
ppConst (Array n k) val = '{' : intercalate ", " (Prelude.map (ppConst k) (unsafeCoerce val :: [Any])) ++ "}"
ppConst (TaggedUnion ls) val =
  let (v1, v2) = unsafeCoerce val :: (Any, Any)
      dataSize = max_list (Prelude.map (\x -> kindSize (Prelude.snd x)) ls)
      tagSize = log2_up (of_nat (Prelude.toInteger (Prelude.length ls))) in
  "{" ++ ppConst (Bit dataSize) v1 ++ ", " ++ ppConst (Bit tagSize) v2 ++ "}"

isVar :: CExpr -> Bool
isVar (Var _ _) = True
isVar _ = False

ppExtract :: Integer -> Integer -> Integer -> Bool -> String -> String
ppExtract n last first isV s =
  if isV
  then s ++ "[" ++ show last ++ " : " ++ show first ++ "]"
  else "verilog_bits#(" ++ show n ++ ", " ++ show last ++ ", " ++ show first ++ ")::extract(" ++ s ++ ")"

ppArrVarExtract :: Integer -> Integer -> Kind -> String -> String -> String
ppArrVarExtract n m k s idx = "verilog_var_array#(" ++ show n ++ ", " ++ show (kindSize k) ++ ", " ++ show m ++
                                                  ")::extract(" ++ s ++ ", " ++ idx ++ ")"

ppArrConstExtract :: Integer -> Kind -> String -> Integer -> String
ppArrConstExtract n k s idx = "verilog_const_array#(" ++ show n ++ ", " ++ show (kindSize k) ++ ", " ++ show idx ++
                                                    ")::extract(" ++ s ++ ")"

ppArrVarUpdate :: Integer -> Integer -> Kind -> String -> String -> String -> String
ppArrVarUpdate n m k s idx val = "verilog_var_array#(" ++ show n ++ ", " ++ show (kindSize k) ++ ", " ++ show m ++
                                                     ")::update(" ++ s ++ ", " ++ idx ++ ", " ++ val ++ ")"

ppArrConstUpdate :: Integer -> Kind -> String -> Integer -> String -> String
ppArrConstUpdate n k s idx val = "verilog_const_array#(" ++ show n ++ ", " ++ show (kindSize k) ++ ", " ++ show idx ++
                                                    ")::update(" ++ s ++ ", " ++ val ++ ")"

ppStructUpdate :: [(String, Kind)] -> String -> Integer -> String -> String
ppStructUpdate ls e p v = "verilog_bits#(" ++ show (kindSize (Struct ls)) ++ ", " ++ show msbPos ++ ", " ++ show lsbPos ++ ")::update(" ++ e ++ ", /* ." ++ name ++ " = */ " ++ v ++ ")"
  where
    includedSize [] 0 = error "Hit struct update includedSize when list is zero"
    includedSize ((name, k) : xs) 0 = kindSize k
    includedSize ((name, k) : xs) m = kindSize k + includedSize xs (m-1)
    (name, k) = genericIndex ls p
    lsbPos = kindSize (Struct ls) - includedSize ls p
    msbPos = kindSize k + lsbPos-1

tagHelp :: Integer -> [a] -> [(Integer, a)]
tagHelp n [] = []
tagHelp n (x:xs) = (n, x): tagHelp (n+1) xs

tag = tagHelp 0

unsafeHd :: [a] -> a
unsafeHd [] = error "empty list"
unsafeHd (x : xs) = x

ppUnionDataExtract :: Integer -> Integer -> CExpr -> String
ppUnionDataExtract dataSize data_width e
  | data_width <= 0 = "0"
  | data_width == dataSize = exprStr ++ ".data"
  | otherwise = ppExtract dataSize (data_width - 1) 0 (isVar e) (exprStr ++ ".data")
  where
    exprStr = ppCExpr e

ppUnionDataPad :: Integer -> Integer -> CExpr -> String
ppUnionDataPad dataSize data_width e
  | data_width == dataSize = ppCExpr e
  | data_width == 0 = show dataSize ++ "'h0"
  | otherwise = "{ " ++ show (dataSize - data_width) ++ "'h0, " ++ ppCExpr e ++ " }"

ppReadArrayCond n m k idxStr valStr =
  if n >= (2 ^ m)
  then valStr
  else "($unsigned(" ++ idxStr ++ ") < " ++ show m ++ "'d" ++ show n ++ " ? " ++ valStr ++ " : " ++ show (kindSize k) ++ "'b0)"

ppCExpr :: CExpr -> String
ppCExpr (Var k tmp) = ppTmp tmp
ppCExpr (Const k val) = ppConst k val
ppCExpr (Or k ls) = '(' : intercalate " | " (Prelude.map ppCExpr ls) ++ " | " ++ show (kindSize k) ++ "'h0)"
ppCExpr (And k ls) = '(' : intercalate " & " (Prelude.map ppCExpr ls) ++ " & ~(" ++ show (kindSize k) ++ "'h0))"
ppCExpr (Xor k ls) = '(' : intercalate " ^ " (Prelude.map ppCExpr ls) ++ " ^ " ++ show (kindSize k) ++ "'h0)"
ppCExpr (Not k val) = "~(" ++ ppCExpr val ++ ")"
ppCExpr (TruncLsb msb lsb val) = ppExtract (msb+lsb) (lsb-1) 0 (isVar val) (ppCExpr val)
ppCExpr (TruncMsb msb lsb val) = ppExtract (msb+lsb) (msb+lsb-1) lsb (isVar val) (ppCExpr val)
ppCExpr (UXor 0 val) = "1\'h0"
ppCExpr (UXor n val) = "^(" ++ ppCExpr val ++ ")"
ppCExpr (Add n ls) = '(' : intercalate " + " (Prelude.map ppCExpr ls) ++ " + " ++ show n ++ "'h0)"
ppCExpr (Mul n ls) = '(' : intercalate " * " (Prelude.map ppCExpr ls) ++ " * " ++ show n ++ "'h1)"
ppCExpr (Div n a b) = '(' : ppCExpr a ++ " / " ++ ppCExpr b ++ ")"
ppCExpr (Rem n a b) = '(' : ppCExpr a ++ " % " ++ ppCExpr b ++ ")"
ppCExpr (Sll n m a b) = '(' : ppCExpr a ++ " << " ++ ppCExpr b ++ ")"
ppCExpr (Srl n m a b) = '(' : ppCExpr a ++ " >> " ++ ppCExpr b ++ ")"
ppCExpr (Sra n m a b) = "($signed(" ++ ppCExpr a ++ ") >>> " ++ ppCExpr b ++ ")"
ppCExpr (Concat 0 m a b) = ppCExpr b
ppCExpr (Concat n 0 a b) = ppCExpr a
ppCExpr (Concat n m a b) = '{' : ppCExpr a ++ " , " ++ ppCExpr b ++ "}"
ppCExpr (ITE k p t f) = '(' : ppCExpr p ++ " ? " ++ ppCExpr t ++ " : " ++ ppCExpr f ++ ")"
ppCExpr (Eq0 k a b) = if kindSize k <= 0 then "1'h1" else '(' : ppCExpr a ++ " == " ++ ppCExpr b ++ ")"
ppCExpr (ReadStruct ls val@(Var _ _) i) = ppCExpr val ++ "." ++ Prelude.fst (genericIndex ls i)
ppCExpr (ReadStruct ls val i) =
  let dropLs = drop (integerToInt i) ls in
  let dropSize = kindSize (Struct dropLs) in
  let msb = dropSize - 1 in
  let lsb = dropSize - kindSize (Prelude.snd (unsafeHd dropLs)) in
  let totalWidth = kindSize (Struct ls) in
  "/* ." ++ Prelude.fst (genericIndex ls i) ++ " */ " ++ ppExtract totalWidth msb lsb False (ppCExpr val)
ppCExpr (ReadArray n m k val@(Var _ _) i) = ppReadArrayCond n m k (ppCExpr i) (ppCExpr val ++ "[" ++ ppCExpr i ++ "]")
ppCExpr (ReadArray n m k val i) = ppReadArrayCond n m k (ppCExpr i) (ppArrVarExtract n m k (ppCExpr val) (ppCExpr i))
ppCExpr (ReadArrayConst n k val@(Var _ _) i) = ppCExpr val ++ "[" ++ show i ++ "]"
ppCExpr (ReadArrayConst n k val i) = ppArrConstExtract n k (ppCExpr val) i
ppCExpr (UpdateStruct ls e p v) = ppStructUpdate ls (ppCExpr e) p (ppCExpr v) -- '{' : intercalate ", " (Prelude.map (\i -> if i == p then ppCExpr v else ppCExpr (ReadStruct ls e i)) [0 .. (Compile.length ls - 1)]) ++ "}"
ppCExpr (UpdateArrayConst n k e p v) = ppArrConstUpdate n k (ppCExpr e) p (ppCExpr v) -- '{' : intercalate ", " (Prelude.map (\i -> if i == p then ppCExpr v else ppCExpr (ReadArrayConst n k e i)) [0 .. n - 1]) ++ "}"
ppCExpr (UpdateArray n k e m p v) = ppArrVarUpdate n m k (ppCExpr e) (ppCExpr p) (ppCExpr v) -- '{' : intercalate ", " (Prelude.map (\i -> ppCExpr (ITE k (Eq0 (Bit m) p (Const (Bit m) (unsafeCoerce i :: Type))) v (ReadArrayConst n k e i))) [0 .. n - 1]) ++ "}"
ppCExpr (ToBit k val) = ppCExpr val
ppCExpr (FromBit k val) = ppCExpr val
ppCExpr (ReadUnionTag ls e i) =
  let tagSize = log2_up (toInteger (Prelude.length ls)) in
  let tagName = Prelude.fst (genericIndex ls i) in
  if tagSize <= 0
  then "1'b1 /* " ++ tagName ++ " */"
  else "(" ++ ppCExpr e ++ ".tag == " ++ show i ++ " /* " ++ tagName ++ " */)"
ppCExpr (ReadUnionData ls e i) =
  let tagName = Prelude.fst (genericIndex ls i) in
  let dataSize = maximum (0 : Prelude.map (kindSize . Prelude.snd) ls) in
  let data_width = kindSize (Prelude.snd (genericIndex ls i)) in
  "(" ++ ppUnionDataExtract dataSize data_width e ++ " /* " ++ tagName ++ ".data */)"
ppCExpr (BuildUnion ls i e) =
  let tagName = Prelude.fst (genericIndex ls i) in
  let dataSize = maximum (0 : Prelude.map (kindSize . Prelude.snd) ls) in
  let data_width = kindSize (Prelude.snd (genericIndex ls i)) in
  let tagSize = log2_up (toInteger (Prelude.length ls)) in
  if tagSize <= 0
  then "'{data: " ++ ppUnionDataPad dataSize data_width e ++ "}"
  else if dataSize <= 0
       then "'{tag: " ++ show i ++ " /* " ++ tagName ++ " */}"
       else "'{data: " ++ ppUnionDataPad dataSize data_width e ++ ", tag: " ++ show i ++ " /* " ++ tagName ++ " */}"
ppCExpr (BuildStruct ls vals) = '{' : intercalate ", " (getStringFields (\_ -> ppCExpr) ls vals) ++ "}"
ppCExpr (BuildArray k n vals) = '{' : intercalate ", " (Prelude.map ppCExpr vals) ++ "}"

ppBitFormat :: BitFormat -> String
ppBitFormat Binary = "b"
ppBitFormat Decimal = "d"
ppBitFormat Hex = "x"

ppFullFormat :: FullFormat -> String
ppFullFormat (FBool sz bf) = "%" ++ show sz ++ ppBitFormat bf
ppFullFormat (FBit n sz bf) = "%" ++ show sz ++ ppBitFormat bf
ppFullFormat (FStruct ls vals) = '{' : intercalate "; " (getStringFields (\_ -> ppFullFormat) ls vals) ++ "}"
ppFullFormat (FArray n k val) = '[' : intercalate "; " (Prelude.map (\i -> show i ++ "=" ++ ppFullFormat val ++ "; ") [0..n-1]) ++ "]"
ppFullFormat (FTaggedUnion ls tagBF dataBF) =
  let tagSize = log2_up (toInteger (Prelude.length ls)) in
  let dataSize = maximum (0 : Prelude.map (kindSize . Prelude.snd) ls) in
  if tagSize <= 0
  then "{data=%" ++ show dataSize ++ ppBitFormat dataBF ++ "}"
  else if dataSize <= 0
       then "{tag=%" ++ show tagSize ++ ppBitFormat tagBF ++ "}"
       else "{data=%" ++ show dataSize ++ ppBitFormat dataBF ++ ", tag=%" ++ show tagSize ++ ppBitFormat tagBF ++ "}"

ppIndent :: Int -> String
ppIndent q = replicate (2 * q) ' '

deformat :: String -> String
deformat = concatMap (\c -> case c of
                             '\n' -> "\\n"
                             '\t' -> "\\t"
                             '\r' -> "\\r"
                             _    -> c:[])

ppCExprList :: Kind -> CExpr -> [CExpr]
ppCExprList Bool e = [e]
ppCExprList (Bit _) e = [e]
ppCExprList (Struct ls) e = concatMap (\(i, (s, k)) -> ppCExprList k (ReadStruct ls e i)) (tag ls)
ppCExprList (Array n k) e = concatMap (\i -> ppCExprList k (ReadArrayConst n k e i)) [0 .. n - 1]
ppCExprList (TaggedUnion ls) e =
  let tagSize = log2_up (toInteger (Prelude.length ls)) in
  let dataSize = maximum (0 : Prelude.map (kindSize . Prelude.snd) ls) in
  let unionBitVal = ToBit (TaggedUnion ls) e in
  if tagSize <= 0
  then [unionBitVal]
  else if dataSize <= 0
       then [unionBitVal]
       else [TruncMsb dataSize tagSize unionBitVal, TruncLsb dataSize tagSize unionBitVal]

ppSys :: Int -> SysT CTmp -> String
ppSys q (DispString s) = ppIndent q ++ "$write(\"" ++ deformat s ++ "\");\n"
ppSys q (DispExpr k e f) = if (kindSize k > 0) then ppIndent q ++ "$write(\"" ++ ppFullFormat f ++ "\"," ++ (intercalate ", " (Prelude.map ppCExpr (ppCExprList k e))) ++ ");\n" else ""
ppSys q (Finish) = ppIndent q ++ "$finish();\n"

ppName :: String -> (String, Integer) -> String
ppName suffix (name, idx) = name ++ "_" ++ suffix ++ "_" ++ show idx

ppTmp :: (String, Integer) -> String
ppTmp tmp = ppName "let" tmp

ppReg :: (String, Integer) -> String
ppReg reg = ppName "reg" reg

ppMem :: String -> (String, Integer) -> String
ppMem which mem = ppName ("mem" ++ which) mem

ppMeth :: String -> (String, Integer) -> String
ppMeth which meth = ppName which meth

condPrint :: Bool -> String -> String
condPrint b s = if b then s else ""

compHelper :: Int -> Bool -> [String] -> Compiled -> String
compHelper q cond strs rest = (condPrint cond $ concatMap (\str -> ppIndent q ++ str ++ ";\n") strs) ++ ppCompiled q rest

ppRandom :: Integer -> String
ppRandom n = ppExtract (32 * (Prelude.div (n + 31) 32)) (n - 1) 0 False ("{" ++ intercalate ", " (replicate (integerToInt (Prelude.div (n + 31) 32)) "$urandom()") ++ "}")

ppCompiled :: Int -> Compiled -> String
ppCompiled q (CReadReg reg k tmp rest) = compHelper q (kindSize k > 0) [ppTmp tmp ++ " = " ++ ppReg reg] rest
ppCompiled q (CWriteReg reg k val rest) = compHelper q (kindSize k > 0) [ppReg reg ++ " = " ++ ppCExpr val] rest
ppCompiled q (CReadRqMem mem sz k ports i p rest) = compHelper q (kindSize k > 0 && sz > 0 && ports > 0) [ppMem "Rq" mem ++ "[" ++ show p ++ "] = " ++ ppCExpr i, ppMem "RqEn" mem ++ "[" ++ show p ++ "] = 1'h1"] rest
ppCompiled q (CReadRpMem mem sz k ports p tmp rest) = compHelper q (kindSize k > 0 && sz > 0 && ports > 0) [ppTmp tmp ++ " = " ++ ppMem "Rp" mem ++ "[" ++ show p ++ "]"] rest
ppCompiled q (CWriteMem mem sz k ports i val rest) = compHelper q (kindSize k > 0 && sz > 0 && ports > 0) [ppMem "WrIdx" mem ++ " = " ++ ppCExpr i, ppMem "WrVal" mem ++ " = " ++ ppCExpr val, ppMem "WrEn" mem ++ " = 1'h1"] rest
ppCompiled q (CSend meth k e rest) = compHelper q (kindSize k > 0) [ppMeth "Send" meth ++ " = " ++ ppCExpr e, ppMeth "SendEn" meth ++ " = 1'h1"] rest
ppCompiled q (CRecv meth k tmp rest) = compHelper q (kindSize k > 0) [ppTmp tmp ++ " = " ++ ppMeth "Recv" meth] rest
ppCompiled q (CLetExpr tmp k e rest) = compHelper q (kindSize k > 0) [ppTmp tmp ++ " = " ++ ppCExpr e] rest
ppCompiled q (CLetAction k act rest) = ppIndent q ++ "begin\n" ++ ppCompiled (q+1) act ++ ppIndent q ++ "end\n" ++ ppCompiled q rest
ppCompiled q (CNonDet tmp k rest) = compHelper q (kindSize k > 0) [ppTmp tmp ++ " = " ++  ppRandom (kindSize k)] rest
ppCompiled q (CIfElse p k t f rest) = ppIndent q ++ "if(" ++ ppCExpr p ++ ") begin\n" ++ ppCompiled (q+1) t ++ ppIndent q ++ "end else begin\n" ++ ppCompiled (q+1) f ++ ppIndent q ++ "end\n" ++ ppCompiled q rest
ppCompiled q (CSys ls rest) = (concatMap (\x -> ppSys q x) ls) ++ ppCompiled q rest
ppCompiled q (CReturn tmp k val) = if (kindSize k > 0) then ppIndent q ++ ppTmp tmp ++ " = " ++ ppCExpr val ++ ";\n" else ""
