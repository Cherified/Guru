module CodePrinter where

import Numeric
import Data.Char (intToDigit)
import Data.List (intercalate)
import Compile
import GHC.Num (integerToInt)

getStringFields :: (Kind -> a -> String) -> [(String, Kind)] -> b -> [String]
getStringFields f [] _ = []
getStringFields f ((s, k): xs) val = let (v1, v2) = unsafeCoerce val :: (a, b) in
                                     let rest = getStringFields f xs v2 in
                                     if (size k > 0)
                                     then f k v1 : rest
                                     else rest

ppConst :: Kind -> Any -> String
ppConst Bool val = if (unsafeCoerce val :: Prelude.Bool) then "1\'h1" else "1\'h0"
ppConst (Bit n) val = show n ++ "\'h" ++ (showIntAtBase 16 intToDigit (unsafeCoerce val :: Integer) "")
ppConst (Struct ls) val = '{' : intercalate ", " (getStringFields ppConst ls val) ++ "}"
ppConst (Array n k) val = '{' : intercalate ", " (Prelude.map (ppConst k) (unsafeCoerce val :: [Any])) ++ "}"

ppExtract :: Integer -> Integer -> Integer -> String -> String
ppExtract n last first s = "verilog_bits#(" ++ show n ++ ", " ++ show last ++ ", " ++ show first ++ ")::extract(" ++ s ++ ")"

ppArrVarExtract :: Integer -> Integer -> Kind -> String -> String -> String
ppArrVarExtract n m k s idx = "verilog_var_array#(" ++ show n ++ ", " ++ show (size k) ++ ", " ++ show m ++
                                                  ")::extract(" ++ s ++ ", " ++ idx ++ ")"

ppArrConstExtract :: Integer -> Kind -> String -> Integer -> String
ppArrConstExtract n k s idx = "verilog_const_array#(" ++ show n ++ ", " ++ show (size k) ++ ", " ++ show idx ++
                                                    ")::extract(" ++ s ++ ")"
tagHelp :: Integer -> [a] -> [(Integer, a)]
tagHelp n [] = []
tagHelp n (x:xs) = (n, x): tagHelp (n+1) xs

tag = tagHelp 0

unsafeHd :: [a] -> a
unsafeHd [] = error "empty list"
unsafeHd (x : xs) = x

ppCExpr :: CExpr -> String
ppCExpr (Var k tmp) = ppTmp tmp
ppCExpr (Const k val) = ppConst k val
ppCExpr (Or k ls) = '(' : intercalate " | " (Prelude.map ppCExpr ls) ++ " | " ++ show (size k) ++ "\'h0)"
ppCExpr (And k ls) = '(' : intercalate " & " (Prelude.map ppCExpr ls) ++ " & " ++ show (size k) ++ "\'h1)"
ppCExpr (Xor k ls) = '(' : intercalate " ^ " (Prelude.map ppCExpr ls) ++ " ^ " ++ show (size k) ++ "\'h0)"
ppCExpr (Not k val) = "~(" ++ ppCExpr val ++ ")"
ppCExpr (TruncLsb msb lsb val) = ppExtract (msb+lsb) (lsb-1) 0 (ppCExpr val)
ppCExpr (TruncMsb msb lsb val) = ppExtract (msb+lsb) (msb+lsb-1) lsb (ppCExpr val)
ppCExpr (UXor 0 val) = "1\'h0"
ppCExpr (UXor n val) = "^(" ++ ppCExpr val ++ ")" 
ppCExpr (Add n ls) = '(' : intercalate " + " (Prelude.map ppCExpr ls) ++ " + " ++ show n ++ "\'h0)"
ppCExpr (Mul n ls) = '(' : intercalate " * " (Prelude.map ppCExpr ls) ++ " * " ++ show n ++ "\'h1)"
ppCExpr (Div n a b) = '(' : ppCExpr a ++ " / " ++ ppCExpr b ++ ")"
ppCExpr (Rem n a b) = '(' : ppCExpr a ++ " % " ++ ppCExpr b ++ ")"
ppCExpr (Sll n m a b) = '(' : ppCExpr a ++ " << " ++ ppCExpr b ++ ")"
ppCExpr (Srl n m a b) = '(' : ppCExpr a ++ " >> " ++ ppCExpr b ++ ")"
ppCExpr (Sra n m a b) = "($signed(" ++ ppCExpr a ++ ") >>> " ++ ppCExpr b ++ ")"
ppCExpr (Concat 0 m a b) = ppCExpr b
ppCExpr (Concat n 0 a b) = ppCExpr a
ppCExpr (Concat n m a b) = '{' : ppCExpr a ++ " , " ++ ppCExpr b ++ "}"
ppCExpr (ITE k p t f) = '(' : ppCExpr p ++ " ? " ++ ppCExpr t ++ " : " ++ ppCExpr f ++ ")"
ppCExpr (Eq0 k a b) = if size k <= 0 then "1'h1" else '(' : ppCExpr a ++ " == " ++ ppCExpr b ++ ")"
ppCExpr (ReadStruct ls val@(Var _ _) i) = ppCExpr val ++ "." ++ fieldName ls i
ppCExpr (ReadStruct ls val i) = let dropLs = drop (integerToInt i) ls in
                                let dropSize = size (Struct dropLs) in
                                ppExtract (size (Struct ls)) (dropSize-1)
                                  (dropSize-size (Prelude.snd (unsafeHd dropLs))) (ppCExpr val)
ppCExpr (ReadArray n m k val@(Var _ _) i) = ppCExpr val ++ "[" ++ ppCExpr i ++ "]"
ppCExpr (ReadArray n m k val i) = ppArrVarExtract n m k (ppCExpr val) (ppCExpr i)
ppCExpr (ReadArrayConst n k val@(Var _ _) i) = ppCExpr val ++ "[" ++ show i ++ "]"
ppCExpr (ReadArrayConst n k val i) = ppArrConstExtract n k (ppCExpr val) i
ppCExpr (UpdateStruct ls e p v) = '{' : intercalate ", " (Prelude.map (\i -> if i == p then ppCExpr v else ppCExpr (ReadStruct ls e i)) [0 .. (Compile.length ls - 1)]) ++ "}"
ppCExpr (UpdateArrayConst n k e p v) = '{' : intercalate ", " (Prelude.map (\i -> if i == p then ppCExpr v else ppCExpr (ReadArrayConst n k e i)) [0 .. n - 1]) ++ "}"
ppCExpr (UpdateArray n k e m p v) = '{' : intercalate ", " (Prelude.map (\i -> ppCExpr (ITE k (Eq0 (Bit m) p (Const (Bit m) (unsafeCoerce i :: Type))) v (ReadArrayConst n k e i))) [0 .. n - 1]) ++ "}"
ppCExpr (ToBit k val) = ppCExpr val
ppCExpr (FromBit k val) = ppCExpr val
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

ppSys :: Int -> SysT CTmp -> String
ppSys q (DispString s) = ppIndent q ++ "$write(\"" ++ deformat s ++ "\");\n"
ppSys q (DispExpr k e f) = if (size k > 0) then ppIndent q ++ "$write(\"" ++ ppFullFormat f ++ "\"," ++ (intercalate ", " (Prelude.map ppCExpr (ppCExprList k e))) ++ ");\n" else ""
ppSys q (Finish) = ppIndent q ++ "$finish();\n"

ppName :: String -> (String, Integer) -> String
ppName prefix (name, idx) = name ++ "_" ++ prefix ++ "_" ++ show idx

ppTmp :: (String, Integer) -> String
ppTmp tmp = ppName "let" tmp

ppReg :: (String, Integer) -> String
ppReg reg = ppName "reg" reg

ppMem :: String -> (String, Integer) -> String
ppMem which mem = ppName ("mem" ++ which) mem

ppRegU :: (String, Integer) -> String
ppRegU regU = ppName "regU" regU

ppMeth :: String -> (String, Integer) -> String
ppMeth which meth = ppName which meth

condPrint :: Bool -> String -> String
condPrint b s = if b then s else ""

compHelper :: Int -> Bool -> [String] -> Compiled -> String
compHelper q cond strs rest = (condPrint cond $ concatMap (\str -> ppIndent q ++ str ++ ";\n") strs) ++ ppCompiled q rest

ppRandom :: Integer -> String
ppRandom n = ppExtract (32 * (div (n + 31) 32)) (n - 1) 0 ("{" ++ intercalate ", " (replicate (integerToInt (div (n + 31) 32)) "$urandom()") ++ "}")

ppCompiled :: Int -> Compiled -> String
ppCompiled q (CReadReg reg k tmp rest) = compHelper q (size k > 0) [ppTmp tmp ++ " = " ++ ppReg reg] rest
ppCompiled q (CWriteReg reg k val rest) = compHelper q (size k > 0) [ppReg reg ++ " = " ++ ppCExpr val] rest
ppCompiled q (CReadRqMem mem k sz i p rest) = compHelper q (size k > 0 && sz > 0) [ppMem "Rq" mem ++ "[" ++ show p ++ "] = " ++ ppCExpr i, ppMem "RqEn" mem ++ "[" ++ show p ++ "] = 1'h1"] rest
ppCompiled q (CReadRpMem mem p k sz tmp rest) = compHelper q (size k > 0 && sz > 0) [ppTmp tmp ++ " = " ++ ppMem "Rp" mem ++ "[" ++ show p ++ "]"] rest
ppCompiled q (CWriteMem mem sz i k val ports rest) = compHelper q (size k > 0 && sz > 0 && ports > 0) [ppMem "WrIdx" mem ++ " = " ++ ppCExpr i, ppMem "WrVal" mem ++ " = " ++ ppCExpr val, ppMem "WrEn" mem ++ " = 1'h1"] rest
ppCompiled q (CReadRegU reg k tmp rest) = compHelper q (size k > 0) [ppTmp tmp ++ " = " ++ ppRegU reg] rest
ppCompiled q (CWriteRegU reg k val rest) = compHelper q (size k > 0) [ppRegU reg ++ " = " ++ ppCExpr val] rest
ppCompiled q (CReadRqMemU mem k sz i p rest) = compHelper q (size k > 0 && sz > 0) [ppMem "URq" mem ++ "[" ++ show p ++ "] = " ++ ppCExpr i, ppMem "URqEn" mem ++ "[" ++ show p ++ "] = 1'h1"] rest
ppCompiled q (CReadRpMemU mem p k sz tmp rest) = compHelper q (size k > 0 && sz > 0) [ppTmp tmp ++ " = " ++ ppMem "URp" mem ++ "[" ++ show p ++ "]"] rest
ppCompiled q (CWriteMemU mem sz i k val ports rest) = compHelper q (size k > 0 && sz > 0 && ports > 0) [ppMem "UWrIdx" mem ++ " = " ++ ppCExpr i, ppMem "UWrVal" mem ++ " = " ++ ppCExpr val, ppMem "UWrEn" mem ++ " = 1'h1"] rest
ppCompiled q (CSend meth k e rest) = compHelper q (size k > 0) [ppMeth "Send" meth ++ " = " ++ ppCExpr e, ppMeth "SendEn" meth ++ " = 1'h1"] rest
ppCompiled q (CRecv meth k tmp rest) = compHelper q (size k > 0) [ppTmp tmp ++ " = " ++ ppMeth "Recv" meth] rest
ppCompiled q (CLetExpr tmp k e rest) = compHelper q (size k > 0) [ppTmp tmp ++ " = " ++ ppCExpr e] rest
ppCompiled q (CLetAction k act rest) = ppIndent q ++ "begin\n" ++ ppCompiled (q+1) act ++ ppIndent q ++ "end\n" ++ ppCompiled q rest
ppCompiled q (CNonDet tmp k rest) = compHelper q (size k > 0) [ppTmp tmp ++ " = " ++  ppRandom (size k)] rest
ppCompiled q (CIfElse p k t f rest) = ppIndent q ++ "if(" ++ ppCExpr p ++ ") begin\n" ++ ppCompiled (q+1) t ++ ppIndent q ++ "end else begin\n" ++ ppCompiled (q+1) f ++ ppIndent q ++ "end\n" ++ ppCompiled q rest
ppCompiled q (CSys ls rest) = (concatMap (\x -> ppSys q x) ls) ++ ppCompiled q rest
ppCompiled q (CReturn tmp k val) = if (size k > 0) then ppIndent q ++ ppTmp tmp ++ " = " ++ ppCExpr val ++ ";\n" else ""

