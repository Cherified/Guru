module TopPrinter where

import Compile
import CodePrinter
import ModPrinter

ppMemInit :: Maybe (Any, VerilogMem) -> String
ppMemInit Nothing = "1, 1, 0, \"\", 0, 0"
ppMemInit (Just (_, (Build_VerilogMem ascii name offset size))) = "1, 0, " ++ if ascii then "1, " else "0, \"" ++ name ++ "\", " ++ show offset ++ ", " ++ show size

ppTop :: CompiledModule -> String
ppTop mod@((Build_ModDecl regs mems regUs memUs sends recvs, tmps), _) =
  "module top(\n"
  ++ concatMap (\(i, (s, k)) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 k ++ " " ++ ppMeth "Send" (s, i) ++ ",\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 1 ++ "output " ++ ppKindImmStart 1 Bool ++ " " ++ ppMeth "SendEn" (s, i) ++ ",\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 1 ++ "input " ++ ppKindImmStart 1 k ++ " " ++ ppMeth "Recv" (s, i) ++ ",\n") (tag recvs)
  ++ ppIndent 1 ++ "input CLK,\n"
  ++ ppIndent 1 ++ "input RESET);\n"
  ++ ppIfc mod
  ++ concatMap (\(i, (s, (Build_Mem n k p init))) -> ppIndent 1 ++ "verilog_mem#(" ++ show n ++ ", " ++ show (size k) ++ ", " ++ show p ++ ppMemInit init ++ ");\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 1 ++ "verilog_mem#(" ++ show n ++ ", " ++ show (size k) ++ ", " ++ show p ++ "0, 0, 0, \"\", 0, 0);\n") (tag memUs)
  ++ ppIndent 1 ++ "design d(\n"
  ++ concatMap (\(i, (s, k)) -> ppIndent 2 ++ ".decl_" ++ ppMeth "Send" (s, i) ++ "(" ++ ppMeth "Send" (s, i) ++ "),\n") (tag sends)
  ++ concatMap (\(i, (s, k)) -> ppIndent 2 ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ "(" ++ ppMeth "SendEn" (s, i) ++ "),\n") (tag sends)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 2 ++ ".decl_" ++ ppMem "Rq" (s, i) ++ "(" ++ ppMem "Rq" (s, i) ++ "),\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 2 ++ ".decl_" ++ ppMem "RqEn" (s, i) ++ "(" ++ ppMem "RqEn" (s, i) ++ "),\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 2 ++ ".decl_" ++ ppMem "WrIdx" (s, i) ++ "(" ++ ppMem "WrIdx" (s, i) ++ "),\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 2 ++ ".decl_" ++ ppMem "WrVal" (s, i) ++ "(" ++ ppMem "WrVal" (s, i) ++ "),\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 2 ++ ".decl_" ++ ppMem "WrEn" (s, i) ++ "(" ++ ppMem "WrEn" (s, i) ++ "),\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 2 ++ ".decl_" ++ ppMem "URq" (s, i) ++ "(" ++ ppMem "URq" (s, i) ++ "),\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 2 ++ ".decl_" ++ ppMem "URqEn" (s, i) ++ "(" ++ ppMem "URqEn" (s, i) ++ "),\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 2 ++ ".decl_" ++ ppMem "UWrIdx" (s, i) ++ "(" ++ ppMem "UWrIdx" (s, i) ++ "),\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 2 ++ ".decl_" ++ ppMem "UWrVal" (s, i) ++ "(" ++ ppMem "UWrVal" (s, i) ++ "),\n") (tag memUs)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 2 ++ ".decl_" ++ ppMem "UWrEn" (s, i) ++ "(" ++ ppMem "UWrEn" (s, i) ++ "),\n") (tag memUs)
  ++ concatMap (\(i, (s, k)) -> ppIndent 2 ++ "." ++ ppMeth "Recv" (s, i) ++ "(" ++ ppMeth "Recv" (s, i) ++ "),\n") (tag recvs)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 2 ++ "." ++ ppMem "Rp" (s, i) ++ "(" ++ ppMem "Rp" (s, i) ++ "),\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 2 ++ "." ++ ppMem "URp" (s, i) ++ "(" ++ ppMem "URp" (s, i) ++ "),\n") (tag memUs)
  ++ ppIndent 2 ++ ".CLK(CLK),\n"
  ++ ppIndent 2 ++ ".RESET(RESET)\n"
  ++ ppIndent 1 ++ ");\n"
  ++ "endmodule\n"

ppTb :: CompiledModule -> String
ppTb mod@((Build_ModDecl regs mems regUs memUs sends recvs, tmps), _) =
  "module tb();\n"
  ++ concatMap (\(i, (s, k)) -> ppKindDecl 1 k ++ " " ++ ppMeth "Recv" (s, i) ++ ";\n") (tag recvs)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppKindDecl 1 (Array p k) ++ " " ++ ppMem "Rp" (s, i) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppKindDecl 1 (Array p k) ++ " " ++ ppMem "URp" (s, i) ++ ";\n") (tag memUs)
  ++ ppIndent 1 ++ "top t(\n"
  ++ concatMap (\(i, (s, k)) -> ppIndent 2 ++ "." ++ ppMeth "Recv" (s, i) ++ "(" ++ ppMeth "Recv" (s, i) ++ "),\n") (tag recvs)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 2 ++ "." ++ ppMem "Rp" (s, i) ++ "(" ++ ppMem "Rp" (s, i) ++ "),\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 2 ++ "." ++ ppMem "URp" (s, i) ++ "(" ++ ppMem "URp" (s, i) ++ "),\n") (tag memUs)
  ++ ppIndent 2 ++ ".CLK(CLK),\n"
  ++ ppIndent 2 ++ ".RESET(RESET)\n"
  ++ ppIndent 1 ++ ");\n"
  ++ ppIndent 1 ++ "initial begin\n"
  ++ ppIndent 2 ++ "CLK = 1'b0;\n"
  ++ ppIndent 2 ++ "RESET = 1'b1;\n"
  ++ ppIndent 2 ++ "RESET = #40 1'b0;\n"
  ++ ppIndent 2 ++ "#2000 $finish;\n"
  ++ ppIndent 1 ++ "end\n"
  ++ ppIndent 1 ++ "always begin\n"
  ++ concatMap (\(i, (s, k)) -> ppIndent 2 ++ ppMeth "Recv" (s, i) ++ " = " ++ ppRandom (size k) ++ ";\n") (tag recvs)
  ++ concatMap (\(i, (s, (Build_Mem n k p _))) -> ppIndent 2 ++ ppMem "Rp" (s, i) ++ " = " ++ ppRandom (size k) ++ ";\n") (tag mems)
  ++ concatMap (\(i, (s, (Build_MemU n k p))) -> ppIndent 2 ++ ppMem "URp" (s, i) ++ " = " ++ ppRandom (size k) ++ ";\n") (tag memUs)
  ++ ppIndent 2 ++ "CLK = #10 1'b1;\n"
  ++ ppIndent 2 ++ "CLK = #10 1'b0;\n"
  ++ ppIndent 1 ++ "end\n"
  ++ "endmodule\n"
