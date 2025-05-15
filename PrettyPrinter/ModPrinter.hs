module ModPrinter where

import Data.List
import Compile
import CodePrinter

tagHelp :: Int -> [a] -> [(Int, a)]
tagHelp n [] = []
tagHelp n (x:xs) = (n, x): tagHelp (n+1) xs

tag = tagHelp 0

ppArrayKind :: Kind -> Kind
ppArrayKind k@(Array _ k') = ppArrayKind k'
ppArrayKind k = k

ppArrayList :: Kind -> [Int]
ppArrayList k@(Array n' k') = (n': ppArrayList k')
ppArrayList k = []

ppKindImmStart :: Int -> Kind -> String
ppKindImmStart q Bool = "logic "
ppKindImmStart q (Bit n) = "logic [" ++ show (n-1) ++ " : 0] "
ppKindImmStart q (Struct ls) = "struct packed {\n" ++ concatMap (\(s, k) -> ppIndent (q+1) ++ ppKindImmStart (q+1) k ++ " " ++ s ++ ";\n") ls ++ ppIndent q ++ "} "
ppKindImmStart q a@(Array n k) = ppKindImmStart q (ppArrayKind a) ++ concatMap (\i -> "[" ++ show (i-1) ++ " : 0]") (ppArrayList a) ++ " "

ppKindDecl :: Int -> Kind -> String
ppKindDecl q k = ppIndent q ++ ppKindImmStart q k

log2_up :: Int -> Int
log2_up = ceiling . (logBase 2) . fromIntegral


ppIfc :: CompiledModule -> String
ppIfc ((Build_ModDecl regs mems regUs memUs sends recvs, tmps), compiled) =
  concatMap (\(i, (s, (Build_Mem n k p _))) -> ppKindDecl 1 (Array p (Bit (log2_up n))) ++ " " ++ ppMem "Rq" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppKindDecl 1 (Array p Bool) ++ " " ++ ppMem "RqEn" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppKindDecl 1 (Array p (Bit (log2_up n))) ++ " " ++ ppMem "WrIdx" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppKindDecl 1 (Array p k) ++ " " ++ ppMem "WrVal" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppKindDecl 1 (Array p Bool) ++ " " ++ ppMem "WrEn" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppKindDecl 1 (Array p (Bit (log2_up n))) ++ " " ++ ppMem "URq" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppKindDecl 1 (Array p Bool) ++ " " ++ ppMem "URqEn" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppKindDecl 1 (Array p (Bit (log2_up n))) ++ " " ++ ppMem "UWrIdx" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppKindDecl 1 (Array p k) ++ " " ++ ppMem "UWrVal" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppKindDecl 1 (Array p Bool) ++ " " ++ ppMem "UWrEn" (s, i) ++ ";\n") (tag memUs)

ppMod :: CompiledModule -> String
ppMod mod@((Build_ModDecl regs mems regUs memUs sends recvs, tmps), compiled) =
  "module design (\n"
  ++ concatMap (\(i, (s, k)) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 k ++ " decl_" ++ ppMeth "Send" (s, i) ++ ",\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 Bool ++ " decl_" ++ ppMeth "SendEn" (s, i) ++ ",\n") (tag sends)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p (Bit (log2_up n))) ++ " decl_" ++ ppMem "Rq" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p Bool) ++ " decl_" ++ ppMem "RqEn" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p (Bit (log2_up n))) ++ " decl_" ++ ppMem "WrIdx" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p k) ++ " decl_" ++ ppMem "WrVal" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p Bool) ++ " decl_" ++ ppMem "WrEn" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p (Bit (log2_up n))) ++ " decl_" ++ ppMem "URq" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p Bool) ++ " decl_" ++ ppMem "URqEn" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p (Bit (log2_up n))) ++ " decl_" ++ ppMem "UWrIdx" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p k) ++ " decl_" ++ ppMem "UWrVal" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 (Array p Bool) ++ " decl_" ++ ppMem "UWrEn" (s, i) ++ ",\n") (tag memUs)
  ++ concatMap (\(i, (s, k)) -> ppIndent 1 ++ "input " ++ ppKindImmStart 1 k ++ " " ++ ppMeth "Recv" (s, i) ++ ",\n") (tag recvs)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 1 ++ "input " ++ ppKindImmStart 1 (Array p k) ++ " " ++ ppMem "Rp" (s, i) ++ ",\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 1 ++ "input " ++ ppKindImmStart 1 (Array p k) ++ " " ++ ppMem "URp" (s, i) ++ ",\n") (tag memUs)
  ++ ppIndent 1 ++ "input CLK,\n"
  ++ ppIndent 1 ++ "input RESET);\n"
  ++ concatMap (\(i, (s, k)) -> ppKindDecl 1 k ++ " " ++ ppMeth "Send" (s, i) ++ ";\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppKindDecl 1 Bool ++ " " ++ ppMeth "SendEn" (s, i) ++ ";\n") (tag sends)
  ++ ppIfc mod
  ++ concatMap (\(i, (s, (Build_Reg k _))) -> ppKindDecl 1 k ++ " decl_" ++ ppReg (s, i) ++ ";\n") (tag regs)
  ++ concatMap (\(i, (s, k)) -> ppKindDecl 1 k ++ " decl_" ++ ppRegU (s, i) ++ ";\n") (tag regUs)
  ++ concatMap (\(i, (s, (Build_Reg k _))) -> ppKindDecl 1 k ++ " " ++ ppReg (s, i) ++ ";\n") (tag regs)
  ++ concatMap (\(i, (s, k)) -> ppKindDecl 1 k ++ " " ++ ppRegU (s, i) ++ ";\n") (tag regUs)
  ++ concatMap (\(i, (s, k)) -> ppKindDecl 1 k ++ " " ++ ppTmp (s, Prelude.length tmps - 1 - i) ++ ";\n") (tag tmps)
  ++ ppIndent 1 ++ "initial begin\n"
  ++ concatMap (\(i, (s, (Build_Reg k val))) -> ppIndent 2 ++ " decl_" ++ ppReg (s, i) ++ " <= " ++ ppConst k val ++ ";\n") (tag regs)
  ++ ppIndent 1 ++ "end\n"
  ++ ppIndent 1 ++ "always@(posedge CLK) begin\n"
  ++ ppIndent 2 ++ "if(RESET) begin\n"
  ++ concatMap (\(i, (s, (Build_Reg k val))) -> ppIndent 3 ++ " decl_" ++ ppReg (s, i) ++ " <= " ++ ppConst k val ++ ";\n") (tag regs)
  ++ ppIndent 2 ++ "end else begin"
  ++ concatMap (\(i, (s, _)) -> ppIndent 3 ++ ppReg (s, i) ++ " = decl_" ++ ppReg (s, i) ++ ";\n") (tag regs)
  ++ concatMap (\(i, (s, _)) -> ppIndent 3 ++ ppRegU (s, i) ++ " = decl_" ++ ppRegU (s, i) ++ ";\n") (tag regUs)
  ++ concatMap (\(i, (s, k)) -> ppIndent 3 ++ ppTmp (s, Prelude.length tmps - 1 - i) ++ " = " ++ show (size k) ++ "\'h0;\n") (tag tmps)
  ++ concatMap (\(i, (s, k)) -> ppIndent 3 ++ ppMeth "Send" (s, i) ++ " = " ++ show (size k) ++ "\'h0;\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 3 ++ ppMeth "SendEn" (s, i) ++ " = 1\'b0;\n") (tag sends)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ ppMem "Rq" (s, i) ++ " = " ++ show (p * log2_up n) ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ ppMem "RqEn" (s, i) ++ " = " ++ show p ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ ppMem "WrIdx" (s, i) ++ " = " ++ show (p * log2_up n) ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ ppMem "WrVal" (s, i) ++ " = " ++ show (p * size k) ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ ppMem "WrEn" (s, i) ++ " = " ++ show p ++ "\'h0;\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ ppMem "URq" (s, i) ++ " = " ++ show (p * log2_up n) ++ "\'h0;\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ ppMem "URqEn" (s, i) ++ " = " ++ show p ++  "\'b0;\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ ppMem "UWrIdx" (s, i) ++ " = " ++ show (p * log2_up n) ++ "\'h0;\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ ppMem "UWrVal" (s, i) ++ " = " ++ show (p * size k) ++ "\'h0;\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ ppMem "UWrEn" (s, i) ++ " = " ++ show p ++ "\'b0;\n") (tag memUs)
  ++ "\n"
  ++ ppCompiled 3 compiled
  ++ "\n"
  ++ concatMap (\(i, (s, _)) -> ppIndent 3 ++ "decl_" ++ ppReg (s, i) ++ " <= " ++ ppReg (s, i) ++ ";\n") (tag regs)
  ++ concatMap (\(i, (s, _)) -> ppIndent 3 ++ "decl_" ++ ppRegU (s, i) ++ " <= " ++ ppRegU (s, i) ++ ";\n") (tag regUs)
  ++ concatMap (\(i, (s, k)) -> ppIndent 3 ++ "decl_" ++ ppMeth "Send" (s, i) ++ " = " ++ ppMeth "Send" (s, i) ++ ";\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 3 ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ " = " ++ ppMeth "SendEn" (s, i) ++ ";\n") (tag sends)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ "decl_" ++ ppMem "Rq" (s, i) ++ " = " ++ ppMem "Rq" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ "decl_" ++ ppMem "RqEn" (s, i) ++ " = " ++ ppMem "RqEn" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ "decl_" ++ ppMem "WrIdx" (s, i) ++ " = " ++ ppMem "WrIdx" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ "decl_" ++ ppMem "WrVal" (s, i) ++ " = " ++ ppMem "WrVal" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 3 ++ "decl_" ++ ppMem "WrEn" (s, i) ++ " = " ++ ppMem "WrEn" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ "decl_" ++ ppMem "URq" (s, i) ++ " = " ++ ppMem "URq" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ "decl_" ++ ppMem "URqEn" (s, i) ++ " = " ++ ppMem "URqEn" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ "decl_" ++ ppMem "UWrIdx" (s, i) ++ " = " ++ ppMem "UWrIdx" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ "decl_" ++ ppMem "UWrVal" (s, i) ++ " = " ++ ppMem "UWrVal" (s, i) ++ ";\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 3 ++ "decl_" ++ ppMem "UWrEn" (s, i) ++ " = " ++ ppMem "UWrEn" (s, i) ++ ";\n") (tag memUs)
  ++ ppIndent 2 ++ "end\n"
  ++ ppIndent 1 ++ "end\n"
  ++ "endmodule\n"
