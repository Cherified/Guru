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

sizeElem :: ModElem -> Bool
sizeElem (EReg r) = size (regKind r) > 0
sizeElem (EMem m) = size (memKind m) > 0 && memSize m > 0 && memPort m > 0
sizeElem (ESend k) = size k > 0
sizeElem (ERecv k) = size k > 0

dfsModElems :: Tree ModElem -> [([String], ModElem)]
dfsModElems tree = helper [] tree
  where
    helper path (Leaf name elem) = [(name : path, elem)]
    helper path (Node name children) =
      concatMap (helper (name : path)) children

modElems :: Tree ModElem -> [(Integer, (String, ModElem))]
modElems tree =
  filter (sizeElem . Prelude.snd . Prelude.snd)
    (Prelude.map (\(i, (path, elem)) -> (i, (intercalate "_" (reverse path), elem)))
      (tag (dfsModElems tree)))

ppPorts :: String -> Bool -> Int -> [(Integer, (String, ModElem))] -> String
ppPorts term showDir q elems = concatMap ppPort elems
  where
    dir s = if showDir then s else ""
    ppPort (i, (s, ESend k)) =
      ppIndent q ++ dir "output " ++ ppKindImmStart q k ++ "decl_" ++ ppMeth "Send" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q Bool ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ term ++ "\n"
    ppPort (i, (s, ERecv k)) =
      ppIndent q ++ dir "input " ++ ppKindImmStart q k ++ " " ++ ppMeth "Recv" (s, i) ++ term ++ "\n"
    ppPort _ = ""

ppModElemDecls :: Int -> [(Integer, (String, ModElem))] -> String
ppModElemDecls q elems = concatMap ppModElemDecl elems
  where
    ppModElemDecl (i, (s, EReg r)) =
      ppKindDecl q (regKind r) ++ "decl_" ++ ppReg (s, i) ++ ";\n"
    ppModElemDecl (i, (s, EMem m)) =
      ppKindDecl q (Array (memPort m) (Bit (clog2 (memSize m)))) ++ "decl_" ++ ppMem "Rq" (s, i) ++ ";\n"
      ++ ppKindDecl q (Array (memPort m) Bool) ++ "decl_" ++ ppMem "RqEn" (s, i) ++ ";\n"
      ++ ppKindDecl q (Bit (clog2 (memSize m))) ++ "decl_" ++ ppMem "WrIdx" (s, i) ++ ";\n"
      ++ ppKindDecl q (memKind m) ++ "decl_" ++ ppMem "WrVal" (s, i) ++ ";\n"
      ++ ppKindDecl q Bool ++ "decl_" ++ ppMem "WrEn" (s, i) ++ ";\n"
      ++ ppKindDecl q (Array (memPort m) (memKind m)) ++ ppMem "Rp" (s, i) ++ ";\n"
    ppModElemDecl (i, (s, ESend _)) = ""
    ppModElemDecl (i, (s, ERecv _)) = ""

ppCTmpDecls :: Int -> [(String, Integer, Kind)] -> String
ppCTmpDecls q tmps = concatMap ppCTmpDecl tmps
  where
    ppCTmpDecl (s, idx, k) = ppKindDecl q k ++ ppTmp (s, idx) ++ ";\n"

ppShadowDecls :: Int -> [(Integer, (String, ModElem))] -> String
ppShadowDecls q elems = concatMap ppShadowDecl elems
  where
    ppShadowDecl (i, (s, EReg r)) =
      ppKindDecl q (regKind r) ++ ppReg (s, i) ++ ";\n"
    ppShadowDecl (i, (s, ESend k)) =
      ppKindDecl q k ++ ppMeth "Send" (s, i) ++ ";\n"
      ++ ppKindDecl q Bool ++ ppMeth "SendEn" (s, i) ++ ";\n"
    ppShadowDecl (i, (s, EMem m)) =
      ppKindDecl q (Array (memPort m) (Bit (clog2 (memSize m)))) ++ ppMem "Rq" (s, i) ++ ";\n"
      ++ ppKindDecl q (Array (memPort m) Bool) ++ ppMem "RqEn" (s, i) ++ ";\n"
      ++ ppKindDecl q (Bit (clog2 (memSize m))) ++ ppMem "WrIdx" (s, i) ++ ";\n"
      ++ ppKindDecl q (memKind m) ++ ppMem "WrVal" (s, i) ++ ";\n"
      ++ ppKindDecl q Bool ++ ppMem "WrEn" (s, i) ++ ";\n"
    ppShadowDecl (i, (s, ERecv k)) = ""

ppRegisterResets :: Int -> String -> [(Integer, (String, ModElem))] -> String
ppRegisterResets q op elems = concatMap ppRegisterReset elems
  where
    ppRegisterReset (i, (s, EReg (Build_Reg k (Just val)))) =
      ppIndent q ++ "decl_" ++ ppReg (s, i) ++ " " ++ op ++ " " ++ ppConst k val ++ ";\n"
    ppRegisterReset _ = ""

ppCTmpInits :: Int -> [(String, Integer, Kind)] -> String
ppCTmpInits q tmps = concatMap ppCTmpInit tmps
  where
    ppCTmpInit (s, idx, k) =
      ppIndent q ++ ppTmp (s, idx) ++ " = " ++ show (size k) ++ "'h0;\n"

ppShadowInits :: Int -> [(Integer, (String, ModElem))] -> String
ppShadowInits q elems = concatMap ppShadowInit elems
  where
    ppShadowInit (i, (s, EReg r)) =
      ppIndent q ++ ppReg (s, i) ++ " = decl_" ++ ppReg (s, i) ++ ";\n"
    ppShadowInit (i, (s, ESend k)) =
      ppIndent q ++ ppMeth "Send" (s, i) ++ " = " ++ show (size k) ++ "'h0;\n"
      ++ ppIndent q ++ ppMeth "SendEn" (s, i) ++ " = 1'b0;\n"
    ppShadowInit (i, (s, EMem m)) =
      ppIndent q ++ ppMem "Rq" (s, i) ++ " = " ++ show (memPort m * clog2 (memSize m)) ++ "'h0;\n"
      ++ ppIndent q ++ ppMem "RqEn" (s, i) ++ " = " ++ show (memPort m) ++ "'h0;\n"
      ++ ppIndent q ++ ppMem "WrIdx" (s, i) ++ " = " ++ show (clog2 (memSize m)) ++ "'h0;\n"
      ++ ppIndent q ++ ppMem "WrVal" (s, i) ++ " = " ++ show (size (memKind m)) ++ "'h0;\n"
      ++ ppIndent q ++ ppMem "WrEn" (s, i) ++ " = 1'h0;\n"
    ppShadowInit (i, (s, ERecv k)) = ""

ppFinalAssigns :: Int -> [(Integer, (String, ModElem))] -> String
ppFinalAssigns q elems = concatMap ppFinalAssign elems
  where
    ppFinalAssign (i, (s, ESend k)) =
      ppIndent q ++ "decl_" ++ ppMeth "Send" (s, i) ++ " = " ++ ppMeth "Send" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ " = " ++ ppMeth "SendEn" (s, i) ++ ";\n"
    ppFinalAssign (i, (s, EMem m)) =
      ppIndent q ++ "decl_" ++ ppMem "Rq" (s, i) ++ " = " ++ ppMem "Rq" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMem "RqEn" (s, i) ++ " = " ++ ppMem "RqEn" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMem "WrIdx" (s, i) ++ " = " ++ ppMem "WrIdx" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMem "WrVal" (s, i) ++ " = " ++ ppMem "WrVal" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMem "WrEn" (s, i) ++ " = " ++ ppMem "WrEn" (s, i) ++ ";\n"
    ppFinalAssign (i, (s, EReg _)) = ""
    ppFinalAssign (i, (s, ERecv _)) = ""

ppRegisterUpdates :: Int -> [(Integer, (String, ModElem))] -> String
ppRegisterUpdates q elems = concatMap ppRegisterUpdate elems
  where
    ppRegisterUpdate (i, (s, EReg r)) =
      ppIndent q ++ "decl_" ++ ppReg (s, i) ++ " <= " ++ ppReg (s, i) ++ ";\n"
    ppRegisterUpdate (i, (s, ESend _)) = ""
    ppRegisterUpdate (i, (s, EMem _)) = ""
    ppRegisterUpdate (i, (s, ERecv _)) = ""

ppModMemParams :: Int -> Mem -> String
ppModMemParams q (Build_Mem n k p initVal) =
  ppIndent q ++ ".n(" ++ show n ++ "),\n" ++
  ppIndent q ++ ".clgn(" ++ show (clog2 n) ++ "),\n" ++
  ppIndent q ++ ".sizeK(" ++ show (size k) ++ "),\n" ++
  ppIndent q ++ ".p(" ++ show p ++ "),\n" ++
  case initVal of
    Just (Just val) ->
      ppIndent q ++ ".init(1),\n" ++
      ppIndent q ++ ".def(0),\n" ++
      ppIndent q ++ ".initVal(" ++ ppConst (Array n k) val ++ ")\n"
    Just Nothing ->
      ppIndent q ++ ".init(1),\n" ++
      ppIndent q ++ ".def(1)\n"
    Nothing ->
      ppIndent q ++ ".init(0)\n"

ppModMemPorts :: Int -> (String, Integer) -> String
ppModMemPorts q (s, i) =
  ppIndent q ++ ".Rq(" ++ ("decl_" ++ ppMem "Rq" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".RqEn(" ++ ("decl_" ++ ppMem "RqEn" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrIdx(" ++ ("decl_" ++ ppMem "WrIdx" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrVal(" ++ ("decl_" ++ ppMem "WrVal" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrEn(" ++ ("decl_" ++ ppMem "WrEn" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".Rp(" ++ ppMem "Rp" (s, i) ++ "),\n" ++
  ppIndent q ++ ".CLK(CLK),\n" ++
  ppIndent q ++ ".RESET(RESET)\n"

ppMemInstantiations :: Int -> [(Integer, (String, ModElem))] -> String
ppMemInstantiations q elems = concatMap ppMemInst elems
  where
    ppMemInst (i, (s, EMem m)) =
      ppIndent q ++ "verilog_mem#(\n" ++
      ppModMemParams (q+1) m ++
      ppIndent q ++ ") mem_" ++ ppMem "" (s, i) ++ " (\n" ++
      ppModMemPorts (q+1) (s, i) ++
      ppIndent q ++ ");\n"
    ppMemInst _ = ""

ppTopInstantiation :: Int -> [(Integer, (String, ModElem))] -> String
ppTopInstantiation q elems =
  ppIndent q ++ "top inst (\n"
  ++ concatMap ppTopInstPort elems ++ "\n"
  ++ ppIndent (q+1) ++ ".CLK(CLK),\n"
  ++ ppIndent (q+1) ++ ".RESET(RESET)\n"
  ++ ppIndent q ++ ");\n"
  where
    ppTopInstPort (i, (s, ESend k)) =
      ppIndent (q+1) ++ ".decl_" ++ ppMeth "Send" (s, i) ++ "(decl_" ++ ppMeth "Send" (s, i) ++ "),\n"
      ++ ppIndent (q+1) ++ ".decl_" ++ ppMeth "SendEn" (s, i) ++ "(decl_" ++ ppMeth "SendEn" (s, i) ++ "),\n"
    ppTopInstPort (i, (s, ERecv k)) =
      ppIndent (q+1) ++ "." ++ ppMeth "Recv" (s, i) ++ "(" ++ ppMeth "Recv" (s, i) ++ "),\n"
    ppTopInstPort _ = ""

ppTop :: CompiledModule -> String
ppTop ((tree, tmpsRaw), code) =
  "module top (\n"
  ++ ppPorts "," True 1 elems ++ "\n"
  ++ "  input CLK,\n"
  ++ "  input RESET\n"
  ++ ");\n"
  ++ ppModElemDecls 1 elems ++ "\n"
  ++ ppCTmpDecls 1 tmps ++ "\n"
  ++ ppShadowDecls 1 elems ++ "\n"
  ++ ppMemInstantiations 1 elems ++ "\n"
  ++ "  initial begin\n"
  ++ ppRegisterResets 2 "=" elems
  ++ "  end\n\n"
  ++ "  always_comb begin\n"
  ++ ppCTmpInits 2 tmps ++ "\n"
  ++ ppShadowInits 2 elems ++ "\n"
  ++ ppCompiled 2 code ++ "\n"
  ++ ppFinalAssigns 2 elems
  ++ "  end\n\n"
  ++ "  always_ff @(posedge CLK) begin\n"
  ++ "    if (RESET) begin\n"
  ++ ppRegisterResets 3 "<=" elems
  ++ "    end else begin\n"
  ++ ppRegisterUpdates 3 elems
  ++ "    end\n"
  ++ "  end\n"
  ++ "endmodule\n\n"
  ++ "module tb();\n"
  ++ "  logic CLK;\n"
  ++ "  logic RESET;\n\n"
  ++ ppPorts ";" False 1 elems ++ "\n"
  ++ ppTopInstantiation 1 elems ++ "\n"
  ++ "  initial begin\n"
  ++ "    CLK = 1'h0;\n"
  ++ "    RESET = 1'h1;\n"
  ++ "    RESET = #40 1'h0;\n"
  ++ "    #2000 $finish;\n"
  ++ "  end\n\n"
  ++ "  always begin\n"
  ++ "    CLK = #10 1'h1;\n"
  ++ "    CLK = #10 1'h0;\n"
  ++ "  end\n"
  ++ "endmodule\n"
  where
    elems = modElems tree
    len = genericLength tmpsRaw
    tmpsOriginal = Prelude.map (\(i, (s, k)) -> (s, len - 1 - i, k)) (tag tmpsRaw)
    tmps = filter (\(_, _, k) -> size k > 0) tmpsOriginal
