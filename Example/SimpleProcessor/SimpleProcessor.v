From Stdlib Require Import String List ZArith Zmod Ascii.
From Guru Require Import Library Syntax Semantics Notations Theorems Ltacs Compiler Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section SimpleProcessor.
  Local Open Scope string.

  Variable InstMem DataMem: Kind.
  Variable Addr: Kind.
  Variable Inst: Kind.

  Variable PcInit: type Addr.
  Variable InstMemInit: type InstMem.
  Variable DataMemInit: type DataMem.
  
  Variable getInst: forall ty, ty Addr -> ty InstMem -> Expr ty Inst.
  Variable execInst: forall ty, ty Addr -> ty Inst -> ty DataMem -> Expr ty DataMem.
  Variable nextPc: forall ty, ty Addr -> ty Inst -> ty DataMem -> Expr ty Addr.

  Section Spec.
    Definition specTree : Tree Elem :=
      Node ""
        [ Leaf "pc" (EReg (Build_Reg Addr (Some PcInit)));
          Leaf "instMem" (EReg (Build_Reg InstMem (Some InstMemInit)));
          Leaf "dataMem" (EReg (Build_Reg DataMem (Some DataMemInit)));
          Leaf "pcSend" (ESend Addr) ].

    Local Open Scope guru_scope.

    Definition specProc ty: Action ty specTree (Bit 0) :=
      ( RegRead insts <- ".instMem" in specTree;
        RegRead pc <- ".pc" in specTree;
        Put ".pcSend" in specTree <- #pc;
        RegRead datas <- ".dataMem" in specTree;
        Let inst: Inst <- getInst pc insts;
        Let newDatas: DataMem <- execInst pc inst datas;
        Let newPc: Addr <- nextPc pc inst datas;
        RegWrite ".dataMem" in specTree <- #newDatas;
        RegWrite ".pc" in specTree <- #newPc;
        Retv ).

    Definition spec: Mod specTree :=
      fun ty => [ specProc ty; Retv ].
  End Spec.

  Section Implementation.
    Variable PredState: Kind.
    Variable PredStateInit: type PredState.
    Variable predictedPc: forall ty, ty Addr -> ty PredState -> Expr ty Addr.
    Variable updatePredState: forall ty, ty Addr -> ty Addr -> ty PredState -> Expr ty PredState.

    Definition implTree : Tree Elem :=
      Node ""
        [ Leaf "pc" (EReg (Build_Reg Addr (Some PcInit)));
          Leaf "instMem" (EReg (Build_Reg InstMem (Some InstMemInit)));
          Leaf "dataMem" (EReg (Build_Reg DataMem (Some DataMemInit)));
          Leaf "instValid" (EReg (Build_Reg Bool (Some false)));
          Leaf "inst" (EReg (Build_Reg Inst (Some (getDefault _))));
          Leaf "instPc" (EReg (Build_Reg Addr (Some (getDefault _))));
          Leaf "predState" (EReg (Build_Reg PredState (Some PredStateInit)));
          Leaf "predPc" (EReg (Build_Reg Addr (Some PcInit)));
          Leaf "redirectValid" (EReg (Build_Reg Bool (Some false)));
          Leaf "redirect" (EReg (Build_Reg Addr (Some (getDefault _))));
          Leaf "pcSend" (ESend Addr) ].

    Local Open Scope guru_scope.

    Definition implExec ty: Action ty implTree (Bit 0) :=
      ( RegRead instValid <- ".instValid" in implTree;
        RegRead inst <- ".inst" in implTree;
        RegRead instPc <- ".instPc" in implTree;
        RegRead redirectValid <- ".redirectValid" in implTree;
        RegRead pc <- ".pc" in implTree;
        If #instValid Then (
            If (Not (Eq #instPc #pc)) Then (
                If (Not #redirectValid) Then (
                    RegWrite ".redirectValid" in implTree <- ConstBool true;
                    RegWrite ".redirect" in implTree <- #pc;
                    RegWrite ".instValid" in implTree <- ConstBool false;
                    Retv);
                Retv)
              Else (
                Put ".pcSend" in implTree <- #pc;
                RegRead datas <- ".dataMem" in implTree;
                Let newDatas: DataMem <- execInst pc inst datas;
                Let newPc: Addr <- nextPc pc inst datas;
                RegRead predState <- ".predState" in implTree;
                Let newPredState: PredState <- updatePredState pc newPc predState;
                RegWrite ".dataMem" in implTree <- #newDatas;
                RegWrite ".predState" in implTree <- #newPredState;
                RegWrite ".pc" in implTree <- #newPc;
                RegWrite ".instValid" in implTree <- ConstBool false;
                Retv);
            Retv );
        Retv).

    Definition implFetch ty: Action ty implTree (Bit 0) :=
      ( RegRead predState <- ".predState" in implTree;
        RegRead predPc <- ".predPc" in implTree;
        RegRead redirectValid <- ".redirectValid" in implTree;
        RegRead redirect <- ".redirect" in implTree;
        Let fetchPc : Addr <- ITE #redirectValid #redirect #predPc;
        RegRead instValid <- ".instValid" in implTree;
        If (Not #instValid) Then (
            RegWrite ".redirectValid" in implTree <- ConstBool false;
            RegRead insts <- ".instMem" in implTree;
            Let inst: Inst <- getInst fetchPc insts;
            RegWrite ".instValid" in implTree <- ConstBool true;
            RegWrite ".inst" in implTree <- #inst;
            RegWrite ".instPc" in implTree <- #fetchPc;
            Let newPredPc <- predictedPc predPc predState;
            RegWrite ".predPc" in implTree <- #newPredPc;
            Retv );
        Retv ).

    Definition impl: Mod implTree :=
      fun ty => [ implExec ty; implFetch ty ].

    Section StateRel.
      Variable implSt: TreeState ElemState implTree.
      Variable specSt: TreeState ElemState specTree.

      Record stateRel: Prop := {
          pcSame: RdReg(specSt, ".pc") = RdReg(implSt, ".pc");
          instSameSpec: RdReg(specSt, ".instMem") = InstMemInit;
          instSameImpl: RdReg(implSt, ".instMem") = InstMemInit;
          dataSame: RdReg(specSt, ".dataMem") = RdReg(implSt, ".dataMem");
          instValidProp:
            RdReg(implSt, ".instValid") = true ->
            RdReg(implSt, ".inst") = evalExpr (getInst (RdReg(implSt, ".instPc")) InstMemInit);
          sendSame:
            RdSend(specSt, ".pcSend") = RdSend(implSt, ".pcSend")
        }.
    End StateRel.

    Theorem implSpec: ModSimulation impl spec stateRel.
    Proof.
      apply ActionToModSimulation with (rel := stateRel); intros.
      - simplifyHyps stateRel.
        repeat econstructor; eauto.
      - destructActionInList impl.
        + unfold implExec in *; invertAction; simplifyHyps stateRel.
          * simulateRetv specTree.
          * simulateRetv specTree.
          * specialize (instValidProp0 eq_refl).
            pose proof (isEq_BoolSpec Fst41 Fst3) as sth; destruct sth; [subst; simulateAction (specProc type) | discriminate].
          * simulateRetv specTree.
        + unfold implFetch in *; invertAction; simplifyHyps stateRel.
          * simulateRetv specTree.
          * simulateRetv specTree.
    Qed.
  End Implementation.
End SimpleProcessor.

Section Compile.
  Local Open Scope string.
  Local Open Scope guru_scope.

  Let LgAddr: Z := 5.
  Let NumAddr   := Nat.pow 2 (Z.to_nat LgAddr).
  Let Addr    := Bit LgAddr.
  Let Inst    := STRUCT_TYPE { "isBranchIfEq" :: Bool; "src1" :: Addr; "src2" :: Addr; "dst" :: Addr }.
  Let InstMem := Array NumAddr Inst.
  Let DataMem := Array NumAddr (Bit 16).

  (* Fetch: instruction = instMem[pc] *)
  Let spGetInst ty (addr : ty Addr) (imem : ty InstMem) : Expr ty Inst :=
    #imem @[ #addr ].

  (* Execute: write instruction value into data memory at PC address *)
  Let spExecInst ty (addr : ty Addr) (inst : ty Inst) (dmem : ty DataMem)
    : Expr ty DataMem :=
        ITE (##inst`"isBranchIfEq")
          #dmem
          (#dmem @[##inst`"dst" <- Add [#dmem @[ ##inst`"src1"]; #dmem @[ ##inst`"src2"]]]).

  (* Next PC: sequential, PC + 1 *)
  Let spNextPc ty (addr : ty Addr) (inst : ty Inst) (dmem : ty DataMem) : Expr ty Addr :=
        ITE (##inst`"isBranchIfEq")
          (ITE (Eq #dmem @[ ##inst`"src1"] #dmem @[ ##inst`"src2"]) (##inst`"dst") (Add [#addr; $1]))
          (Add [#addr; $1]).

  (* Trivial branch predictor: always predict PC+1, no state *)
  Let PredState := Bit 0.
  Let spPredictedPc ty (addr : ty Addr) (_ : ty PredState) : Expr ty Addr :=
    Add [#addr; $1].
  Let spUpdatePredState ty (_ _ : ty Addr) (_ : ty PredState)
      : Expr ty PredState := ConstDef.

  (* Instantiate the pipelined implementation *)
  Let sp : Mod _ :=
    impl (getDefault Addr) (getDefault InstMem) (getDefault DataMem)
         spGetInst spExecInst spNextPc
         (getDefault PredState)
         spPredictedPc spUpdatePredState.

  Local Definition compiledMod := compile sp.
End Compile.

Set Extraction Output Directory "./Example/SimpleProcessor".
Extraction "Compile" kindSize Z.log2_up getDefault isEq compiledMod.
