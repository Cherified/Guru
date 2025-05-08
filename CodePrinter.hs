module CodePrinter where

import Numeric
import Data.Char (intToDigit)
import Data.List (intercalate)
import Compile

getStringFields :: (Kind -> Any -> String) -> [(String, Kind)] -> Any -> [String]
getStringFields f [] _ = []
getStringFields f ((s, k): xs) val = let (v1, v2) = unsafeCoerce val :: (Any, Any) in
                                     let rest = getStringFields f xs v2 in
                                     if (size k == 0)
                                     then rest
                                     else f k v1 : rest

getStringElems :: (Any -> String) -> Int -> Any -> [String]
getStringElems f 0 _ = []
getStringElems f m val = let (v1, v2) = unsafeCoerce val :: (Any, Any) in
                         f v1 : getStringElems f m v2

ppConst :: Kind -> Any -> String
ppConst Bool val = if (unsafeCoerce val :: Prelude.Bool) then "1\'b1" else "1\'b0"
ppConst (Bit n) val = show n ++ "\'h" ++ (showIntAtBase 16 intToDigit (unsafeCoerce val :: Integer) "")
ppConst (Struct ls) val = '{' : intercalate ", " (getStringFields ppConst ls val) ++ "}"
ppConst (Array n k) val = '{' : intercalate ", " (getStringElems (ppConst k) n val) ++ "}"

ppExtract :: Int -> Int -> Int -> String -> String
ppExtract n last first s = "verilog_bits#(" ++ show n ++ ", " ++ show last ++ ", " ++ show first ++ ")::extract(" ++ s ++ ")"

ppArrVarExtract :: Int -> Int -> Kind -> String -> String -> String
ppArrVarExtract n m k s idx = "verilog_var_array#(" ++ show n ++ ", " ++ show (size k) ++ ", " ++ show m ++
                                                  ")::extract(" ++ s ++ ", " ++ idx ++ ")"

ppArrConstExtract :: Int -> Kind -> String -> Int -> String
ppArrConstExtract n k s idx = "verilog_const_array#(" ++ show n ++ ", " ++ show (size k) ++ ", " ++ show idx ++
                                                    ")::extract(" ++ s ++ ")"

unsafeHd :: [a] -> a
unsafeHd [] = error "empty list"
unsafeHd (x : xs) = x

ppTmp :: (String, Int) -> String
ppTmp (tName, tIdx) = "let_" ++ tName ++ "_" ++ show tIdx

ppReg :: (String, Int) -> String
ppReg (rName, rPos) = "reg_" ++ rName ++ "_" ++ show rPos

ppCExpr :: CExpr -> String
ppCExpr (Var k tmp) = ppTmp tmp
ppCExpr (Const k val) = ppConst k val
ppCExpr (Or k ls) = '(' : intercalate " | " (Prelude.map ppCExpr ls) ++ " | " ++ show (size k) ++ "\'b0)"
ppCExpr (And ls) = '(' : intercalate " && " (Prelude.map ppCExpr ls) ++ " && 1'b1)"
ppCExpr (Xor ls) = '(' : intercalate " ^ " (Prelude.map ppCExpr ls) ++ " ^ 1'b0)"
ppCExpr (Not val) = "!(" ++ ppCExpr val ++ ")"
ppCExpr (Inv n val) = "~(" ++ ppCExpr val ++ ")"
ppCExpr (TruncLsb msb lsb val) = ppExtract (msb+lsb) (lsb-1) 0 (ppCExpr val)
ppCExpr (TruncMsb msb lsb val) = ppExtract (msb+lsb) (msb+lsb-1) lsb (ppCExpr val)
ppCExpr (UOr 0 val)  = "1\'b0"
ppCExpr (UAnd 0 val) = "1\'b0"
ppCExpr (UXor 0 val) = "1\'b0"
ppCExpr (UOr n val)  = "|(" ++ ppCExpr val ++ ")" 
ppCExpr (UAnd n val) = "&(" ++ ppCExpr val ++ ")" 
ppCExpr (UXor n val) = "^(" ++ ppCExpr val ++ ")" 
ppCExpr (Add n ls) = '(' : intercalate " + " (Prelude.map ppCExpr ls) ++ show n ++ "\'b0)"
ppCExpr (Mul n ls) = '(' : intercalate " * " (Prelude.map ppCExpr ls) ++ show n ++ "\'b1)"
ppCExpr (Band n ls) = '(' : intercalate " & " (Prelude.map ppCExpr ls) ++ show n ++ "\'b1)"
ppCExpr (Bxor n ls) = '(' : intercalate " ^ " (Prelude.map ppCExpr ls) ++ show n ++ "\'b0)"
ppCExpr (Div n a b) = '(' : ppCExpr a ++ " / " ++ ppCExpr b ++ ")"
ppCExpr (Rem n a b) = '(' : ppCExpr a ++ " % " ++ ppCExpr b ++ ")"
ppCExpr (Sll n m a b) = '(' : ppCExpr a ++ " << " ++ ppCExpr b ++ ")"
ppCExpr (Srl n m a b) = '(' : ppCExpr a ++ " >> " ++ ppCExpr b ++ ")"
ppCExpr (Sra n m a b) = '(' : ppCExpr a ++ " >>> " ++ ppCExpr b ++ ")"
ppCExpr (Concat 0 m a b) = ppCExpr b
ppCExpr (Concat n 0 a b) = ppCExpr a
ppCExpr (Concat n m a b) = '{' : ppCExpr a ++ " , " ++ ppCExpr b ++ "}"
ppCExpr (ITE k p t f) = '(' : ppCExpr p ++ " ? " ++ ppCExpr t ++ " : " ++ ppCExpr f ++ ")"
ppCExpr (Eq0 k a b) = if size k == 0 then "1'b1" else '(' : ppCExpr a ++ " == " ++ ppCExpr b ++ ")"
ppCExpr (ReadStruct ls val@(Var _ _) i) = ppCExpr val ++ "." ++ fieldName ls i
ppCExpr (ReadStruct ls val i) = let dropLs = drop (finStruct_to_nat ls i) ls in
                                let dropSize = size (Struct dropLs) in
                                ppExtract (size (Struct ls)) (dropSize-1) (dropSize-size (Prelude.snd (unsafeHd dropLs)))
                                          (ppCExpr val)
ppCExpr (ReadArray n m k val@(Var _ _) i) = ppCExpr val ++ "[" ++ ppCExpr i ++ "]"
ppCExpr (ReadArray n m k val i) = ppArrVarExtract n m k (ppCExpr val) (ppCExpr i)
ppCExpr (ReadArrayConst n k val@(Var _ _) i) = ppCExpr val ++ "[" ++ show (finArray_to_nat n i) ++ "]"
ppCExpr (ReadArrayConst n k val i) = ppArrConstExtract n k (ppCExpr val) (finArray_to_nat n i)
ppCExpr (BuildStruct ls func) = '{' : intercalate ", " (Prelude.map (\i -> ppCExpr (func i)) (filter (\i -> size (fieldK ls i) /= 0) (genFinStruct ls))) ++ "}"
ppCExpr (BuildArray k n func) = '{' : intercalate ", " (Prelude.map (\i -> ppCExpr (func i)) (genFinArray n)) ++ "}"
ppCExpr (ToBit k val) = ppCExpr val
ppCExpr (FromBit k val) = ppCExpr val

ppIndent :: Int -> String
ppIndent i = replicate (4 * i) ' '

{-
ppCompiled :: Int -> Compiled -> String
ppCompiled i CReadReg reg tmp rest = ppIndent i ++ tmp ++ " = " ++ reg ++ ";\n" ++ ppCompiled rest
ppCompiled i CWriteReg reg k val rest = 
-}
