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
ppKindImmStart q (TaggedUnion ls) =
  let tagSize = log2_up (toInteger (Prelude.length ls)) in
  let dataSize = maximum (0 : Prelude.map (kindSize . Prelude.snd) ls) in
  let tagNames = intercalate ", " (Prelude.map Prelude.fst ls) in
  "struct packed {\n" ++
  (if dataSize > 0 then ppIndent (q+1) ++ "logic [" ++ show (dataSize-1) ++ " : 0] data;\n" else "") ++
  (if tagSize > 0 then ppIndent (q+1) ++ "logic [" ++ show (tagSize-1) ++ " : 0] tag; /* TAGS: " ++ tagNames ++ " */\n" else "") ++
  ppIndent q ++ "} "
ppKindImmStart q a@(Array n k) = ppKindImmStart q (ppArrayKind a) ++ concatMap (\i -> "[" ++ show (i-1) ++ " : 0]") (ppArrayList a) ++ " "

ppKindDecl :: Int -> Kind -> String
ppKindDecl q k = ppIndent q ++ ppKindImmStart q k

sizeElem :: Elem -> Bool
sizeElem (EReg r) = kindSize (regKind r) > 0
sizeElem (EMem m) = kindSize (memKind m) > 0 && memSize m > 0 && memPort m > 0
sizeElem (ESend k) = kindSize k > 0
sizeElem (ERecv k) = kindSize k > 0

dfsElems :: Tree Elem -> [([String], Elem)]
dfsElems tree = helper [] tree
  where
    helper path (Leaf name elem) = [(name : path, elem)]
    helper path (Node name children) =
      concatMap (helper (name : path)) children

filteredElems :: Tree Elem -> [(Integer, (String, Elem))]
filteredElems tree =
  filter (sizeElem . Prelude.snd . Prelude.snd)
    (Prelude.map (\(i, (path, elem)) -> (i, (intercalate "_" (reverse path), elem)))
      (tag (dfsElems tree)))

ppPorts :: String -> Bool -> Int -> [(Integer, (String, Elem))] -> String
ppPorts term showDir q elems = concatMap ppPort elems
  where
    dir s = if showDir then s else ""
    ppPort (i, (s, ESend k)) =
      ppIndent q ++ dir "output " ++ ppKindImmStart q k ++ "decl_" ++ ppMeth "Send" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q Bool ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ term ++ "\n"
    ppPort (i, (s, ERecv k)) =
      ppIndent q ++ dir "input " ++ ppKindImmStart q k ++ " " ++ ppMeth "Recv" (s, i) ++ term ++ "\n"
    ppPort _ = ""

ppElemDecls :: Int -> [(Integer, (String, Elem))] -> String
ppElemDecls q elems = concatMap ppElemDecl elems
  where
    ppElemDecl (i, (s, EReg r)) =
      ppKindDecl q (regKind r) ++ "decl_" ++ ppReg (s, i) ++ ";\n"
    ppElemDecl _ = ""

ppCTmpDecls :: Int -> [(String, Integer, Kind)] -> String
ppCTmpDecls q tmps = concatMap ppCTmpDecl tmps
  where
    ppCTmpDecl (s, idx, k) = ppKindDecl q k ++ ppTmp (s, idx) ++ ";\n"

ppShadowDecls :: Int -> [(Integer, (String, Elem))] -> String
ppShadowDecls q elems = concatMap ppShadowDecl elems
  where
    ppShadowDecl (i, (s, EReg r)) =
      ppKindDecl q (regKind r) ++ ppReg (s, i) ++ ";\n"
    ppShadowDecl (i, (s, ESend k)) =
      ppKindDecl q k ++ ppMeth "Send" (s, i) ++ ";\n"
      ++ ppKindDecl q Bool ++ ppMeth "SendEn" (s, i) ++ ";\n"
    ppShadowDecl (i, (s, EMem m)) =
      ppKindDecl q (Array (memPort m) (Bit (log2_up (memSize m)))) ++ ppMem "Rq" (s, i) ++ ";\n"
      ++ ppKindDecl q (Array (memPort m) Bool) ++ ppMem "RqEn" (s, i) ++ ";\n"
      ++ ppKindDecl q (Bit (log2_up (memSize m))) ++ ppMem "WrIdx" (s, i) ++ ";\n"
      ++ ppKindDecl q (memKind m) ++ ppMem "WrVal" (s, i) ++ ";\n"
      ++ ppKindDecl q Bool ++ ppMem "WrEn" (s, i) ++ ";\n"
    ppShadowDecl _ = ""

ppRegisterResets :: Int -> String -> [(Integer, (String, Elem))] -> String
ppRegisterResets q op elems = concatMap ppRegisterReset elems
  where
    ppRegisterReset (i, (s, EReg (Build_Reg k (Just val)))) =
      ppIndent q ++ "decl_" ++ ppReg (s, i) ++ " " ++ op ++ " " ++ ppConst k val ++ ";\n"
    ppRegisterReset _ = ""

ppCTmpInits :: Int -> [(String, Integer, Kind)] -> String
ppCTmpInits q tmps = concatMap ppCTmpInit tmps
  where
    ppCTmpInit (s, idx, k) =
      ppIndent q ++ ppTmp (s, idx) ++ " = " ++ show (kindSize k) ++ "'h0;\n"

ppShadowInits :: Int -> [(Integer, (String, Elem))] -> String
ppShadowInits q elems = concatMap ppShadowInit elems
  where
    ppShadowInit (i, (s, EReg r)) =
      ppIndent q ++ ppReg (s, i) ++ " = decl_" ++ ppReg (s, i) ++ ";\n"
    ppShadowInit (i, (s, ESend k)) =
      ppIndent q ++ ppMeth "Send" (s, i) ++ " = " ++ show (kindSize k) ++ "'h0;\n"
      ++ ppIndent q ++ ppMeth "SendEn" (s, i) ++ " = 1'b0;\n"
    ppShadowInit (i, (s, EMem m)) =
      ppIndent q ++ ppMem "Rq" (s, i) ++ " = " ++ show (memPort m * log2_up (memSize m)) ++ "'h0;\n"
      ++ ppIndent q ++ ppMem "RqEn" (s, i) ++ " = " ++ show (memPort m) ++ "'h0;\n"
      ++ ppIndent q ++ ppMem "WrIdx" (s, i) ++ " = " ++ show (log2_up (memSize m)) ++ "'h0;\n"
      ++ ppIndent q ++ ppMem "WrVal" (s, i) ++ " = " ++ show (kindSize (memKind m)) ++ "'h0;\n"
      ++ ppIndent q ++ ppMem "WrEn" (s, i) ++ " = 1'h0;\n"
    ppShadowInit _ = ""

ppFinalAssigns :: Int -> [(Integer, (String, Elem))] -> String
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
    ppFinalAssign _ = ""

ppRegisterUpdates :: Int -> [(Integer, (String, Elem))] -> String
ppRegisterUpdates q elems = concatMap ppRegisterUpdate elems
  where
    ppRegisterUpdate (i, (s, EReg r)) =
      ppIndent q ++ "decl_" ++ ppReg (s, i) ++ " <= " ++ ppReg (s, i) ++ ";\n"
    ppRegisterUpdate _ = ""

ppMemParams :: Int -> Mem -> String
ppMemParams q (Build_Mem n k p initVal) =
  ppIndent q ++ ".n(" ++ show n ++ "),\n" ++
  ppIndent q ++ ".clgn(" ++ show (log2_up n) ++ "),\n" ++
  ppIndent q ++ ".sizeK(" ++ show (kindSize k) ++ "),\n" ++
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

ppMemPorts :: Int -> (String, Integer) -> String
ppMemPorts q (s, i) =
  ppIndent q ++ ".Rq(" ++ ("decl_" ++ ppMem "Rq" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".RqEn(" ++ ("decl_" ++ ppMem "RqEn" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrIdx(" ++ ("decl_" ++ ppMem "WrIdx" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrVal(" ++ ("decl_" ++ ppMem "WrVal" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrEn(" ++ ("decl_" ++ ppMem "WrEn" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".Rp(" ++ ppMem "Rp" (s, i) ++ "),\n" ++
  ppIndent q ++ ".CLK(CLK),\n" ++
  ppIndent q ++ ".RESET(RESET)\n"

ppMemInstantiations :: Int -> [(Integer, (String, Elem))] -> String
ppMemInstantiations q elems = concatMap ppMemInst elems
  where
    ppMemInst (i, (s, EMem m)) =
      ppIndent q ++ "verilog_mem#(\n" ++
      ppMemParams (q+1) m ++
      ppIndent q ++ ") mem_" ++ ppMem "" (s, i) ++ " (\n" ++
      ppMemPorts (q+1) (s, i) ++
      ppIndent q ++ ");\n"
    ppMemInst _ = ""

ppMemPortsDecl :: String -> Bool -> Int -> [(Integer, (String, Elem))] -> String
ppMemPortsDecl term showDir q elems = concatMap ppMemPort elems
  where
    dir s = if showDir then s else ""
    ppMemPort (i, (s, EMem m)) =
      ppIndent q ++ dir "output " ++ ppKindImmStart q (Array (memPort m) (Bit (log2_up (memSize m)))) ++ "decl_" ++ ppMem "Rq" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q (Array (memPort m) Bool) ++ "decl_" ++ ppMem "RqEn" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q (Bit (log2_up (memSize m))) ++ "decl_" ++ ppMem "WrIdx" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q (memKind m) ++ "decl_" ++ ppMem "WrVal" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q Bool ++ "decl_" ++ ppMem "WrEn" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "input " ++ ppKindImmStart q (Array (memPort m) (memKind m)) ++ ppMem "Rp" (s, i) ++ term ++ "\n"
    ppMemPort _ = ""

ppInstantiation :: String -> Bool -> Int -> [(Integer, (String, Elem))] -> String
ppInstantiation modName showMem q elems =
  ppIndent q ++ modName ++ " " ++ modName ++ "_inst (\n"
  ++ concatMap ppInstPort elems ++ "\n"
  ++ ppIndent (q+1) ++ ".CLK(CLK),\n"
  ++ ppIndent (q+1) ++ ".RESET(RESET)\n"
  ++ ppIndent q ++ ");\n"
  where
    ppInstPort (i, (s, ESend k)) =
      ppIndent (q+1) ++ ".decl_" ++ ppMeth "Send" (s, i) ++ "(decl_" ++ ppMeth "Send" (s, i) ++ "),\n"
      ++ ppIndent (q+1) ++ ".decl_" ++ ppMeth "SendEn" (s, i) ++ "(decl_" ++ ppMeth "SendEn" (s, i) ++ "),\n"
    ppInstPort (i, (s, ERecv k)) =
      ppIndent (q+1) ++ "." ++ ppMeth "Recv" (s, i) ++ "(" ++ ppMeth "Recv" (s, i) ++ "),\n"
    ppInstPort (i, (s, EMem m)) =
      if showMem then
        ppIndent (q+1) ++ ".decl_" ++ ppMem "Rq" (s, i) ++ "(decl_" ++ ppMem "Rq" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ ".decl_" ++ ppMem "RqEn" (s, i) ++ "(decl_" ++ ppMem "RqEn" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ ".decl_" ++ ppMem "WrIdx" (s, i) ++ "(decl_" ++ ppMem "WrIdx" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ ".decl_" ++ ppMem "WrVal" (s, i) ++ "(decl_" ++ ppMem "WrVal" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ ".decl_" ++ ppMem "WrEn" (s, i) ++ "(decl_" ++ ppMem "WrEn" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ "." ++ ppMem "Rp" (s, i) ++ "(" ++ ppMem "Rp" (s, i) ++ "),\n"
      else ""
    ppInstPort _ = ""

ppDesignInstantiation :: Int -> [(Integer, (String, Elem))] -> String
ppDesignInstantiation = ppInstantiation "design" True

ppTopInstantiation :: Int -> [(Integer, (String, Elem))] -> String
ppTopInstantiation = ppInstantiation "top" False

ppTop :: CompiledModule -> String
ppTop ((tree, tmpsRaw), code) =
  "module design (\n"
  ++ ppPorts "," True 1 elems ++ "\n"
  ++ ppMemPortsDecl "," True 1 elems ++ "\n"
  ++ "  input CLK,\n"
  ++ "  input RESET\n"
  ++ ");\n"
  ++ ppElemDecls 1 elems ++ "\n"
  ++ ppCTmpDecls 1 tmps ++ "\n"
  ++ ppShadowDecls 1 elems ++ "\n"
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
  ++ "module top (\n"
  ++ ppPorts "," True 1 elems ++ "\n"
  ++ "  input CLK,\n"
  ++ "  input RESET\n"
  ++ ");\n"
  ++ ppMemPortsDecl ";" False 1 elems ++ "\n"
  ++ ppDesignInstantiation 1 elems ++ "\n"
  ++ ppMemInstantiations 1 elems ++ "\n"
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
    elems = filteredElems tree
    len = genericLength tmpsRaw
    tmpsOriginal = Prelude.map (\(i, (s, k)) -> (s, len - 1 - i, k)) (tag tmpsRaw)
    tmps = filter (\(_, _, k) -> kindSize k > 0) tmpsOriginal
