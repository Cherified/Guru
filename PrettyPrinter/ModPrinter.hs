{-
 - Copyright (c) 2025-2026 Cherified Systems LLC
 -
 - SPDX-License-Identifier: MIT
 -}

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
ppKindImmStart q (Struct ls) = "struct packed {\n" ++ concatMap (\(s, k) -> if kindSize k > 0 then ppIndent (q+1) ++ ppKindImmStart (q+1) k ++ s ++ ";\n" else "") ls ++ ppIndent q ++ "} "
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

dfsElems :: Tree DomainElem -> [([String], DomainElem)]
dfsElems tree = helper [] tree
  where
    helper path (Leaf name elem) = [(name : path, elem)]
    helper path (Node name children) =
      concatMap (helper (name : path)) children

filteredElems :: Tree DomainElem -> [(Integer, (String, DomainElem))]
filteredElems tree =
  Prelude.filter (sizeElem . Prelude.snd . Prelude.snd . Prelude.snd)
    (Prelude.map (\(i, (path, elem)) -> (i, (intercalate "_" (reverse path), elem)))
      (tag (dfsElems tree)))

ppPorts :: String -> Bool -> Int -> [(Integer, (String, DomainElem))] -> String
ppPorts term showDir q elems = concatMap ppPort elems
  where
    dir s = if showDir then s else ""
    ppPort (i, (s, (_, ESend k))) =
      ppIndent q ++ dir "output " ++ ppKindImmStart q k ++ "decl_" ++ ppMeth "Send" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q Bool ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ term ++ "\n"
    ppPort (i, (s, (_, ERecv k))) =
      ppIndent q ++ dir "input " ++ ppKindImmStart q k ++ " " ++ ppMeth "Recv" (s, i) ++ term ++ "\n"
    ppPort _ = ""

ppElemDecls :: Int -> [(Integer, (String, DomainElem))] -> String
ppElemDecls q elems = concatMap ppElemDecl elems
  where
    ppElemDecl (i, (s, (_, EReg r))) =
      ppKindDecl q (regKind r) ++ "decl_" ++ ppReg (s, i) ++ ";\n"
    ppElemDecl _ = ""

ppCrossSyncDecls :: Int -> [(((String, Integer), Kind), String)] -> String
ppCrossSyncDecls q crossReads = concatMap ppSyncDecl (Prelude.filter (\((_, k), _) -> kindSize k > 0) crossReads)
  where
    ppSyncDecl (((s, i), k), _) =
      ppKindDecl q k ++ "sync_out_" ++ ppReg (s, i) ++ ";\n"

ppCrossSyncInstantiations :: Int -> [(((String, Integer), Kind), String)] -> String
ppCrossSyncInstantiations q crossReads = concatMap ppSyncInst (Prelude.filter (\((_, k), _) -> kindSize k > 0) crossReads)
  where
    ppSyncInst (((s, i), k), dstDom) =
      let rName = ppReg (s, i)
          w = kindSize k
          modHdr = if w == 1
                   then "sync_ff2 sync_ff2_cdc_inst_" ++ rName ++ " (\n"
                   else "sync_opt #(.WIDTH(" ++ show w ++ ")) sync_opt_cdc_inst_" ++ rName ++ " (\n"
      in ppIndent q ++ modHdr
         ++ ppIndent (q+1) ++ ".clk(clk_" ++ dstDom ++ "),\n"
         ++ ppIndent (q+1) ++ ".rst_n(rst_n_" ++ dstDom ++ "),\n"
         ++ ppIndent (q+1) ++ ".d(decl_" ++ rName ++ "),\n"
         ++ ppIndent (q+1) ++ ".q(sync_out_" ++ rName ++ ")\n"
         ++ ppIndent q ++ ");\n"

ppCTmpDecls :: Int -> [(String, Integer, Kind)] -> String
ppCTmpDecls q tmps = concatMap ppCTmpDecl tmps
  where
    ppCTmpDecl (s, idx, k) = ppKindDecl q k ++ ppTmp (s, idx) ++ ";\n"

ppShadowDecls :: Int -> [(Integer, (String, DomainElem))] -> String
ppShadowDecls q elems = concatMap ppShadowDecl elems
  where
    ppShadowDecl (i, (s, (_, EReg r))) =
      ppKindDecl q (regKind r) ++ ppReg (s, i) ++ ";\n"
    ppShadowDecl (i, (s, (_, ESend k))) =
      ppKindDecl q k ++ ppMeth "Send" (s, i) ++ ";\n"
      ++ ppKindDecl q Bool ++ ppMeth "SendEn" (s, i) ++ ";\n"
    ppShadowDecl (i, (s, (_, EMem m))) =
      ppKindDecl q (Array (memPort m) (Bit (log2_up (memSize m)))) ++ ppMem "Rq" (s, i) ++ ";\n"
      ++ ppKindDecl q (Array (memPort m) Bool) ++ ppMem "RqEn" (s, i) ++ ";\n"
      ++ ppKindDecl q (Bit (log2_up (memSize m))) ++ ppMem "WrIdx" (s, i) ++ ";\n"
      ++ ppKindDecl q (memKind m) ++ ppMem "WrVal" (s, i) ++ ";\n"
      ++ ppKindDecl q Bool ++ ppMem "WrEn" (s, i) ++ ";\n"
    ppShadowDecl _ = ""

ppRegisterResets :: Int -> String -> [(Integer, (String, DomainElem))] -> String
ppRegisterResets q op elems = concatMap ppRegisterReset elems
  where
    ppRegisterReset (i, (s, (_, EReg (Build_Reg k (Just val) _)))) =
      if isEq k val (getDefault k)
      then ppIndent q ++ "decl_" ++ ppReg (s, i) ++ " " ++ op ++ " '0;\n"
      else ppIndent q ++ "decl_" ++ ppReg (s, i) ++ " " ++ op ++ " " ++ ppConst k val ++ ";\n"
    ppRegisterReset _ = ""

ppCTmpInits :: Int -> [(String, Integer, Kind)] -> String
ppCTmpInits q tmps = concatMap ppCTmpInit tmps
  where
    ppCTmpInit (s, idx, k) =
      ppIndent q ++ ppTmp (s, idx) ++ " = '0;\n"

ppShadowInits :: Int -> [(Integer, (String, DomainElem))] -> String
ppShadowInits q elems = concatMap ppShadowInit elems
  where
    ppShadowInit (i, (s, (_, EReg r))) =
      ppIndent q ++ ppReg (s, i) ++ " = decl_" ++ ppReg (s, i) ++ ";\n"
    ppShadowInit (i, (s, (_, ESend k))) =
      ppIndent q ++ ppMeth "Send" (s, i) ++ " = '0;\n"
      ++ ppIndent q ++ ppMeth "SendEn" (s, i) ++ " = 1'b0;\n"
    ppShadowInit (i, (s, (_, EMem m))) =
      ppIndent q ++ ppMem "Rq" (s, i) ++ " = '0;\n"
      ++ ppIndent q ++ ppMem "RqEn" (s, i) ++ " = '0;\n"
      ++ ppIndent q ++ ppMem "WrIdx" (s, i) ++ " = '0;\n"
      ++ ppIndent q ++ ppMem "WrVal" (s, i) ++ " = '0;\n"
      ++ ppIndent q ++ ppMem "WrEn" (s, i) ++ " = 1'b0;\n"
    ppShadowInit _ = ""

ppFinalAssigns :: Int -> [(Integer, (String, DomainElem))] -> String
ppFinalAssigns q elems = concatMap ppFinalAssign elems
  where
    ppFinalAssign (i, (s, (_, ESend k))) =
      ppIndent q ++ "decl_" ++ ppMeth "Send" (s, i) ++ " = " ++ ppMeth "Send" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMeth "SendEn" (s, i) ++ " = " ++ ppMeth "SendEn" (s, i) ++ ";\n"
    ppFinalAssign (i, (s, (_, EMem m))) =
      ppIndent q ++ "decl_" ++ ppMem "Rq" (s, i) ++ " = " ++ ppMem "Rq" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMem "RqEn" (s, i) ++ " = " ++ ppMem "RqEn" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMem "WrIdx" (s, i) ++ " = " ++ ppMem "WrIdx" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMem "WrVal" (s, i) ++ " = " ++ ppMem "WrVal" (s, i) ++ ";\n"
      ++ ppIndent q ++ "decl_" ++ ppMem "WrEn" (s, i) ++ " = " ++ ppMem "WrEn" (s, i) ++ ";\n"
    ppFinalAssign _ = ""

ppRegisterUpdates :: Int -> [(Integer, (String, DomainElem))] -> String
ppRegisterUpdates q elems = concatMap ppRegisterUpdate elems
  where
    ppRegisterUpdate (i, (s, (_, EReg r))) =
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

ppMemPorts :: Int -> String -> (String, Integer) -> String
ppMemPorts q dom (s, i) =
  ppIndent q ++ ".Rq(" ++ ("decl_" ++ ppMem "Rq" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".RqEn(" ++ ("decl_" ++ ppMem "RqEn" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrIdx(" ++ ("decl_" ++ ppMem "WrIdx" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrVal(" ++ ("decl_" ++ ppMem "WrVal" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".WrEn(" ++ ("decl_" ++ ppMem "WrEn" (s, i)) ++ "),\n" ++
  ppIndent q ++ ".Rp(" ++ ppMem "Rp" (s, i) ++ "),\n" ++
  ppIndent q ++ ".clk(clk_" ++ dom ++ "),\n" ++
  ppIndent q ++ ".rst_n(rst_n_" ++ dom ++ ")\n"

ppMemInstantiations :: Int -> [(Integer, (String, DomainElem))] -> String
ppMemInstantiations q elems = concatMap ppMemInst elems
  where
    ppMemInst (i, (s, (dom, EMem m))) =
      ppIndent q ++ "verilog_mem#(\n" ++
      ppMemParams (q+1) m ++
      ppIndent q ++ ") mem_" ++ ppMem "" (s, i) ++ " (\n" ++
      ppMemPorts (q+1) dom (s, i) ++
      ppIndent q ++ ");\n"
    ppMemInst _ = ""

ppMemPortsDecl :: String -> Bool -> Int -> [(Integer, (String, DomainElem))] -> String
ppMemPortsDecl term showDir q elems = concatMap ppMemPort elems
  where
    dir s = if showDir then s else ""
    ppMemPort (i, (s, (_, EMem m))) =
      ppIndent q ++ dir "output " ++ ppKindImmStart q (Array (memPort m) (Bit (log2_up (memSize m)))) ++ "decl_" ++ ppMem "Rq" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q (Array (memPort m) Bool) ++ "decl_" ++ ppMem "RqEn" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q (Bit (log2_up (memSize m))) ++ "decl_" ++ ppMem "WrIdx" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q (memKind m) ++ "decl_" ++ ppMem "WrVal" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "output " ++ ppKindImmStart q Bool ++ "decl_" ++ ppMem "WrEn" (s, i) ++ term ++ "\n"
      ++ ppIndent q ++ dir "input " ++ ppKindImmStart q (Array (memPort m) (memKind m)) ++ ppMem "Rp" (s, i) ++ term ++ "\n"
    ppMemPort _ = ""

ppClkRstDecls :: Int -> [String] -> String
ppClkRstDecls q doms =
  intercalate ",\n" (Prelude.map (\d -> ppIndent q ++ "input clk_" ++ d ++ ",\n" ++ ppIndent q ++ "input rst_n_" ++ d) doms)

ppClkRstInstPorts :: Int -> [String] -> String
ppClkRstInstPorts q doms =
  intercalate ",\n" (Prelude.map (\d -> ppIndent q ++ ".clk_" ++ d ++ "(clk_" ++ d ++ "),\n" ++ ppIndent q ++ ".rst_n_" ++ d ++ "(rst_n_" ++ d ++ ")") doms)

ppInstantiation :: String -> Bool -> Int -> [String] -> [(Integer, (String, DomainElem))] -> String
ppInstantiation modName showMem q doms elems =
  ppIndent q ++ modName ++ " " ++ modName ++ "_inst (\n"
  ++ concatMap ppInstPort elems ++ "\n"
  ++ ppClkRstInstPorts (q+1) doms ++ "\n"
  ++ ppIndent q ++ ");\n"
  where
    ppInstPort (i, (s, (_, ESend k))) =
      ppIndent (q+1) ++ ".decl_" ++ ppMeth "Send" (s, i) ++ "(decl_" ++ ppMeth "Send" (s, i) ++ "),\n"
      ++ ppIndent (q+1) ++ ".decl_" ++ ppMeth "SendEn" (s, i) ++ "(decl_" ++ ppMeth "SendEn" (s, i) ++ "),\n"
    ppInstPort (i, (s, (_, ERecv k))) =
      ppIndent (q+1) ++ "." ++ ppMeth "Recv" (s, i) ++ "(" ++ ppMeth "Recv" (s, i) ++ "),\n"
    ppInstPort (i, (s, (_, EMem m))) =
      if showMem then
        ppIndent (q+1) ++ ".decl_" ++ ppMem "Rq" (s, i) ++ "(decl_" ++ ppMem "Rq" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ ".decl_" ++ ppMem "RqEn" (s, i) ++ "(decl_" ++ ppMem "RqEn" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ ".decl_" ++ ppMem "WrIdx" (s, i) ++ "(decl_" ++ ppMem "WrIdx" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ ".decl_" ++ ppMem "WrVal" (s, i) ++ "(decl_" ++ ppMem "WrVal" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ ".decl_" ++ ppMem "WrEn" (s, i) ++ "(decl_" ++ ppMem "WrEn" (s, i) ++ "),\n"
        ++ ppIndent (q+1) ++ "." ++ ppMem "Rp" (s, i) ++ "(" ++ ppMem "Rp" (s, i) ++ "),\n"
      else ""
    ppInstPort _ = ""

ppDesignInstantiation :: Int -> [String] -> [(Integer, (String, DomainElem))] -> String
ppDesignInstantiation = ppInstantiation "core_design" True

ppTopInstantiation :: Int -> [String] -> [(Integer, (String, DomainElem))] -> String
ppTopInstantiation = ppInstantiation "top" False

ppSimIoDecls :: Int -> [(Integer, (String, DomainElem))] -> String
ppSimIoDecls q elems =
  ppIndent q ++ "class sim_io_t;\n"
  ++ concatMap ppIoDecl elems
  ++ ppIndent q ++ "endclass\n"
  ++ ppIndent q ++ "sim_io_t sim_io = new;\n"
  where
    ppIoDecl (i, (s, (_, ESend k))) =
      ppIndent (q+1) ++ "virtual function void " ++ ppMeth "Send" (s, i) ++ "(input " ++ ppKindImmStart (q+1) k ++ "val);\n"
      ++ ppIndent (q+1) ++ "endfunction\n"
    ppIoDecl (i, (s, (_, ERecv k))) =
      ppIndent (q+1) ++ "virtual function " ++ ppKindImmStart (q+1) k ++ ppMeth "Recv" (s, i) ++ "();\n"
      ++ ppIndent (q+2) ++ "return '0;\n"
      ++ ppIndent (q+1) ++ "endfunction\n"
    ppIoDecl _ = ""

ppSimMemDecls :: Int -> [(Integer, (String, DomainElem))] -> String
ppSimMemDecls q elems = concatMap ppSimMem elems
  where
    ppSimMem (i, (s, (_, EMem (Build_Mem n k p initVal)))) =
      let clgn    = max 1 (log2_up n)
          ram     = ppMem "Ram" (s, i)
          rp      = ppMem "Rp" (s, i)
          ramInit = case initVal of
            Just (Just val) -> '\'' : ppConst (Array n k) val
            _               -> "'{default: '0}"
      in ppKindDecl q k ++ ram ++ " [" ++ show (n - 1) ++ " : 0] = " ++ ramInit ++ ";\n"
         ++ ppKindDecl q (Array p k) ++ rp ++ " = '0;\n"
         ++ ppIndent q ++ "function automatic void sim_" ++ ppMem "Rq" (s, i) ++ "(input int port, input logic [" ++ show (clgn - 1) ++ " : 0] idx);\n"
         ++ ppIndent (q+1) ++ rp ++ "[port] = (idx <= " ++ show clgn ++ "'(" ++ show (n - 1) ++ ")) ? " ++ ram ++ "[idx] : '0;\n"
         ++ ppIndent q ++ "endfunction\n"
         ++ ppIndent q ++ "function automatic void sim_" ++ ppMem "Wr" (s, i) ++ "(input logic [" ++ show (clgn - 1) ++ " : 0] idx, input " ++ ppKindImmStart q k ++ "val);\n"
         ++ ppIndent (q+1) ++ "if (idx <= " ++ show clgn ++ "'(" ++ show (n - 1) ++ ")) " ++ ram ++ "[idx] = val;\n"
         ++ ppIndent q ++ "endfunction\n"
    ppSimMem _ = ""

ppDomainCombBlock :: Bool -> Int -> [(Integer, (String, DomainElem))] -> (([(String, Kind)], Compiled), String) -> String
ppDomainCombBlock sim q elems ((tmpsRaw, code), dom) =
  let isReg (_, (_, (_, EReg _))) = True
      isReg _                     = False
      elemsDom = Prelude.filter (if sim then isReg else (\(_, (_, (d, _))) -> d == dom)) elems
      len = genericLength tmpsRaw
      tmpsOriginal = Prelude.map (\(i, (s, k)) -> (s, len - 1 - i, k)) (tag tmpsRaw)
      tmps = Prelude.filter (\(_, _, k) -> kindSize k > 0) tmpsOriginal
  in if sim
     then "  /* Clock domain: " ++ dom ++ " (simulation) */\n"
          ++ "  always @(posedge clk_" ++ dom ++ " or negedge rst_n_" ++ dom ++ ") begin : sim_" ++ dom ++ "\n"
          ++ ppShadowDecls (q+1) elemsDom
          ++ ppCTmpDecls (q+1) tmps ++ "\n"
          ++ "    if (!rst_n_" ++ dom ++ ") begin\n"
          ++ ppRegisterResets (q+2) "<=" elemsDom
          ++ "    end else begin\n"
          ++ ppCTmpInits (q+2) tmps ++ "\n"
          ++ ppShadowInits (q+2) elemsDom ++ "\n"
          ++ ppCompiled True (q+2) code ++ "\n"
          ++ ppRegisterUpdates (q+2) elemsDom
          ++ "    end\n"
          ++ "  end\n\n"
     else "  /* Clock domain: " ++ dom ++ " (combinational) */\n"
          ++ "  always_comb begin : comb_" ++ dom ++ "\n"
          ++ ppCTmpDecls (q+1) tmps ++ "\n"
          ++ ppCTmpInits (q+1) tmps ++ "\n"
          ++ ppShadowInits (q+1) elemsDom ++ "\n"
          ++ ppCompiled False (q+1) code ++ "\n"
          ++ ppFinalAssigns (q+1) elemsDom
          ++ "  end\n\n"

ppDomainFFBlock :: Int -> [(Integer, (String, DomainElem))] -> String -> String
ppDomainFFBlock q elems dom =
  let elemsDom = Prelude.filter (\(_, (_, (d, _))) -> d == dom) elems
  in "  /* Clock domain: " ++ dom ++ " (sequential) */\n"
     ++ "  always_ff @(posedge clk_" ++ dom ++ " or negedge rst_n_" ++ dom ++ ") begin\n"
     ++ "    if (!rst_n_" ++ dom ++ ") begin\n"
     ++ ppRegisterResets (q+2) "<=" elemsDom
     ++ "    end else begin\n"
     ++ ppRegisterUpdates (q+2) elemsDom
     ++ "    end\n"
     ++ "  end\n\n"

ppTop :: CompiledModule -> String
ppTop ((((sim, _), tree), crossReads), codes) =
  (if sim then ppSimIoDecls 0 elems ++ "\n" else "")
  ++ "module core_design (\n"
  ++ (if sim then "" else ppPorts "," True 1 elems ++ "\n")
  ++ (if sim then "" else ppMemPortsDecl "," True 1 elems ++ "\n")
  ++ ppClkRstDecls 1 doms ++ "\n"
  ++ ");\n"
  ++ ppElemDecls 1 elems ++ "\n"
  ++ (if sim then "" else ppCrossSyncDecls 1 crossReads ++ "\n")
  ++ (if sim then "" else ppShadowDecls 1 elems ++ "\n")
  ++ (if sim then ppSimMemDecls 1 elems ++ "\n" else "")
  ++ (if sim then "\n" else ppCrossSyncInstantiations 1 crossReads ++ "\n\n")
  ++ concatMap (ppDomainCombBlock sim 1 elems) codes
  ++ (if sim then "" else concatMap (ppDomainFFBlock 1 elems) doms)
  ++ "endmodule\n\n"
  ++ "module top (\n"
  ++ (if sim then "" else ppPorts "," True 1 elems ++ "\n")
  ++ ppClkRstDecls 1 doms ++ "\n"
  ++ ");\n"
  ++ (if sim then "" else ppMemPortsDecl ";" False 1 elems ++ "\n")
  ++ ppDesignInstantiation 1 doms (if sim then [] else elems) ++ "\n"
  ++ (if sim then "" else ppMemInstantiations 1 elems ++ "\n")
  ++ "endmodule\n\n"
  ++ "module tb();\n"
  ++ concatMap (\d -> "  logic clk_" ++ d ++ ";\n  logic rst_n_" ++ d ++ ";\n") doms ++ "\n"
  ++ (if sim then "" else ppPorts ";" False 1 elems ++ "\n")
  ++ ppTopInstantiation 1 doms (if sim then [] else elems) ++ "\n"
  ++ "  initial begin\n"
  ++ concatMap (\d -> "    clk_" ++ d ++ " = 1'h0;\n    rst_n_" ++ d ++ " = 1'h0;\n") doms
  ++ "    #40;\n"
  ++ concatMap (\d -> "    rst_n_" ++ d ++ " = 1'h1;\n") doms
  ++ "    #2000 $finish;\n"
  ++ "  end\n\n"
  ++ "  always begin\n"
  ++ "    #10;\n"
  ++ concatMap (\d -> "    clk_" ++ d ++ " = 1'h1;\n") doms
  ++ "    #10;\n"
  ++ concatMap (\d -> "    clk_" ++ d ++ " = 1'h0;\n") doms
  ++ "  end\n\n"
  ++ "endmodule\n"
  where
    elems = filteredElems tree
    domsRaw = Prelude.map Prelude.snd codes
    doms = if Prelude.null domsRaw then ["default"] else domsRaw
