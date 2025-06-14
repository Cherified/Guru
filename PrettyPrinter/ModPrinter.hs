module ModPrinter where

import Data.List
import Compile
import CodePrinter
import GHC.Num

ppArrayKind :: Kind -> Kind
ppArrayKind k@(Array _ k') = ppArrayKind k'
ppArrayKind (Bit n') = Bool
ppArrayKind k = k

ppArrayList :: Kind -> [Integer]
ppArrayList k@(Array n' k') = (n': ppArrayList k')
ppArrayList (Bit n') = n' : []
ppArrayList _ = []

ppKindImmStart :: Int -> Kind -> String
ppKindImmStart q Bool = "logic "
ppKindImmStart q (Bit n) = ppKindImmStart q (Array n Bool)
ppKindImmStart q (Struct ls) = "struct packed {\n" ++ concatMap (\(s, k) -> ppIndent (q+1) ++ ppKindImmStart (q+1) k ++ s ++ ";\n") ls ++ ppIndent q ++ "} "
ppKindImmStart q a@(Array n k) = ppKindImmStart q (ppArrayKind a) ++ concatMap (\i -> "[" ++ show (i-1) ++ " : 0]") (ppArrayList a) ++ " "

ppKindDecl :: Int -> Kind -> String
ppKindDecl q k = ppIndent q ++ ppKindImmStart q k

clog2 :: Integer -> Integer
clog2 = ceiling . (logBase 2) . fromIntegral

condMem :: Integer -> Kind -> Integer -> String -> String
condMem n k p s = condPrint (n > 0 && size k > 0 && p > 0) s

ppIfc :: Int -> CompiledModule -> String
ppIfc q ((Build_ModDecl regs mems regUs memUs sends recvs, tmps), compiled) =
  concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppKindDecl q (Array p (Bit (clog2 n))) ++ ppMem "Rq" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppKindDecl q (Array p Bool) ++ ppMem "RqEn" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppKindDecl q (Bit (clog2 n)) ++ ppMem "WrIdx" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppKindDecl q k ++ ppMem "WrVal" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppKindDecl q Bool ++ ppMem "WrEn" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppKindDecl q (Array p (Bit (clog2 n))) ++ ppMem "URq" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppKindDecl q (Array p Bool) ++ ppMem "URqEn" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppKindDecl q (Bit (clog2 n)) ++ ppMem "UWrIdx" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppKindDecl q k ++ ppMem "UWrVal" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppKindDecl q Bool ++ ppMem "UWrEn" (s, i) ++ ";\n") (tag memUs)

ppMod :: CompiledModule -> String
ppMod mod@((Build_ModDecl regs mems regUs memUs sends recvs, tmps), compiled) =
  "module system (\n"
  ++ concatMap (\(i, (s, k)) -> condPrint (size k > 0) $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 k ++ "decl_" ++ ppMeth "Send" (s, i) ++ ",\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 Bool ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ ",\n") (tag sends)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p (Bit (clog2 n))) ++ "decl_" ++ ppMem "Rq" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p Bool) ++ "decl_" ++ ppMem "RqEn" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Bit (clog2 n)) ++ "decl_" ++ ppMem "WrIdx" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 k ++ "decl_" ++ ppMem "WrVal" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 Bool ++ "decl_" ++ ppMem "WrEn" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p (Bit (clog2 n))) ++ "decl_" ++ ppMem "URq" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p Bool) ++ "decl_" ++ ppMem "URqEn" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Bit (clog2 n)) ++ "decl_" ++ ppMem "UWrIdx" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 k ++ "decl_" ++ ppMem "UWrVal" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 1 ++ "output " ++ ppKindImmStart 1 Bool ++ "decl_" ++ ppMem "UWrEn" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppIndent 1 ++ "input " ++ ppKindImmStart 1 k ++ " " ++ ppMeth "Recv" (s, i) ++ ",\n") (tag recvs)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 1 ++ "input " ++ ppKindImmStart 1 (Array p k) ++ ppMem "Rp" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 1 ++ "input " ++ ppKindImmStart 1 (Array p k) ++ ppMem "URp" (s, i) ++ ",\n") (tag memUs)
  ++ ppIndent 1 ++ "input CLK,\n"
  ++ ppIndent 1 ++ "input RESET);\n"
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppKindDecl 1 k ++ ppMeth "Send" (s, i) ++ ";\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppKindDecl 1 Bool ++ ppMeth "SendEn" (s, i) ++ ";\n") (tag sends)
  ++ ppIfc 1 mod
  ++ concatMap (\(i, (s, (Build_Reg k _))) -> condPrint (size k /= 0) $ ppKindDecl 1 k ++ "decl_" ++ ppReg (s, i) ++ ";\n") (tag regs)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppKindDecl 1 k ++ "decl_" ++ ppRegU (s, i) ++ ";\n") (tag regUs)
  ++ concatMap (\(i, (s, (Build_Reg k _))) -> condPrint (size k /= 0) $ ppKindDecl 1 k ++ ppReg (s, i) ++ ";\n") (tag regs)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppKindDecl 1 k ++ ppRegU (s, i) ++ ";\n") (tag regUs)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppKindDecl 1 k ++ ppTmp (s, integerFromInt (Prelude.length tmps) - 1 - i) ++ ";\n") (tag tmps)
  ++ ppIndent 1 ++ "initial begin\n"
  ++ concatMap (\(i, (s, (Build_Reg k val))) -> condPrint (size k /= 0) $ ppIndent 2 ++ " decl_" ++ ppReg (s, i) ++ " = " ++ ppConst k val ++ ";\n") (tag regs)
  ++ ppIndent 1 ++ "end\n"
  ++ ppIndent 1 ++ "always@(posedge CLK) begin\n"
  ++ ppIndent 2 ++ "if(RESET) begin\n"
 ++ concatMap (\(i, (s, (Build_Reg k val))) -> condPrint (size k /= 0) $ ppIndent 3 ++ " decl_" ++ ppReg (s, i) ++ " <= " ++ ppConst k val ++ ";\n") (tag regs)
  ++ ppIndent 2 ++ "end else begin\n"
  ++ concatMap (\(i, (s, (Build_Reg k _))) -> condPrint (size k /= 0) $ ppIndent 3 ++ ppReg (s, i) ++ " = decl_" ++ ppReg (s, i) ++ ";\n") (tag regs)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppIndent 3 ++ ppRegU (s, i) ++ " = decl_" ++ ppRegU (s, i) ++ ";\n") (tag regUs)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppIndent 3 ++ ppTmp (s, integerFromInt (Prelude.length tmps) - 1 - i) ++ " = " ++ show (size k) ++ "\'h0;\n") (tag tmps)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppIndent 3 ++ ppMeth "Send" (s, i) ++ " = " ++ show (size k) ++ "\'h0;\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 3 ++ ppMeth "SendEn" (s, i) ++ " = 1\'b0;\n") (tag sends)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ ppMem "Rq" (s, i) ++ " = " ++ show (p * clog2 n) ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ ppMem "RqEn" (s, i) ++ " = " ++ show p ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ ppMem "WrIdx" (s, i) ++ " = " ++ show (clog2 n) ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ ppMem "WrVal" (s, i) ++ " = " ++ show (size k) ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ ppMem "WrEn" (s, i) ++ " = " ++ "1\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ ppMem "URq" (s, i) ++ " = " ++ show (p * clog2 n) ++ "\'h0;\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ ppMem "URqEn" (s, i) ++ " = " ++ show p ++  "\'b0;\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ ppMem "UWrIdx" (s, i) ++ " = " ++ show (clog2 n) ++ "\'h0;\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ ppMem "UWrVal" (s, i) ++ " = " ++ show (size k) ++ "\'h0;\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ ppMem "UWrEn" (s, i) ++ " = " ++ "1\'b0;\n") (tag memUs)
  ++ "\n"
  ++ ppCompiled 3 compiled
  ++ "\n"
  ++ concatMap (\(i, (s, (Build_Reg k _))) -> condPrint (size k /= 0) $ ppIndent 3 ++ "decl_" ++ ppReg (s, i) ++ " <= " ++ ppReg (s, i) ++ ";\n") (tag regs)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppIndent 3 ++ "decl_" ++ ppRegU (s, i) ++ " <= " ++ ppRegU (s, i) ++ ";\n") (tag regUs)
  ++ concatMap (\(i, (s, k)) -> condPrint (size k /= 0) $ ppIndent 3 ++ "decl_" ++ ppMeth "Send" (s, i) ++ " = " ++ ppMeth "Send" (s, i) ++ ";\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 3 ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ " = " ++ ppMeth "SendEn" (s, i) ++ ";\n") (tag sends)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "Rq" (s, i) ++ " = " ++ ppMem "Rq" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "RqEn" (s, i) ++ " = " ++ ppMem "RqEn" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "WrIdx" (s, i) ++ " = " ++ ppMem "WrIdx" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "WrVal" (s, i) ++ " = " ++ ppMem "WrVal" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "WrEn" (s, i) ++ " = " ++ ppMem "WrEn" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "URq" (s, i) ++ " = " ++ ppMem "URq" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "URqEn" (s, i) ++ " = " ++ ppMem "URqEn" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "UWrIdx" (s, i) ++ " = " ++ ppMem "UWrIdx" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "UWrVal" (s, i) ++ " = " ++ ppMem "UWrVal" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> condMem n k p $ ppIndent 3 ++ "decl_" ++ ppMem "UWrEn" (s, i) ++ " = " ++ ppMem "UWrEn" (s, i) ++ ";\n") (tag memUs)
  ++ ppIndent 2 ++ "end\n"
  ++ ppIndent 1 ++ "end\n"
  ++ "endmodule\n"
