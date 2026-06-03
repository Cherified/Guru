From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Library Syntax Semantics Notations Theorems Ltacs Compiler Extraction.
From Stdlib Require Import Eqdep.

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
    Definition specTree : Tree ModElem :=
      Node ""
        [ Leaf "pc" (ERegister (Build_Register Addr (Some PcInit)));
          Leaf "instMem" (ERegister (Build_Register InstMem (Some InstMemInit)));
          Leaf "dataMem" (ERegister (Build_Register DataMem (Some DataMemInit)));
          Leaf "pcSend" (ESend Addr) ].

    Local Open Scope guru_scope.

    Definition specProc ty: ActionTree ty specTree (Bit 0) :=
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

    Definition spec: ModTree specTree :=
      fun ty => [ specProc ty; Retv ].
  End Spec.

  Section Implementation.
    Variable PredState: Kind.
    Variable PredStateInit: type PredState.
    Variable predictedPc: forall ty, ty Addr -> ty PredState -> Expr ty Addr.
    Variable updatePredState: forall ty, ty Addr -> ty Addr -> ty PredState -> Expr ty PredState.

    Definition implTree : Tree ModElem :=
      Node ""
        [ Leaf "pc" (ERegister (Build_Register Addr (Some PcInit)));
          Leaf "instMem" (ERegister (Build_Register InstMem (Some InstMemInit)));
          Leaf "dataMem" (ERegister (Build_Register DataMem (Some DataMemInit)));
          Leaf "instValid" (ERegister (Build_Register Bool (Some false)));
          Leaf "inst" (ERegister (Build_Register Inst (Some (Default _))));
          Leaf "instPc" (ERegister (Build_Register Addr (Some (Default _))));
          Leaf "predState" (ERegister (Build_Register PredState (Some PredStateInit)));
          Leaf "predPc" (ERegister (Build_Register Addr (Some PcInit)));
          Leaf "redirectValid" (ERegister (Build_Register Bool (Some false)));
          Leaf "redirect" (ERegister (Build_Register Addr (Some (Default _))));
          Leaf "pcSend" (ESend Addr) ].

    Local Open Scope guru_scope.

    Definition implFetch ty: ActionTree ty implTree (Bit 0) :=
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

    Definition implExec ty: ActionTree ty implTree (Bit 0) :=
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

    Definition impl: ModTree implTree :=
      fun ty => [ implExec ty; implFetch ty ].

    Section StateRel.
      Variable implSt: TreeState ModElemState implTree.
      Variable specSt: TreeState ModElemState specTree.

      Record stateRel: Prop := {
          pcSame: ReadReg(specSt, ".pc") = ReadReg(implSt, ".pc");
          instSameSpec: ReadReg(specSt, ".instMem") = InstMemInit;
          instSameImpl: ReadReg(implSt, ".instMem") = InstMemInit;
          dataSame: ReadReg(specSt, ".dataMem") = ReadReg(implSt, ".dataMem");
          instValidProp:
            ReadReg(implSt, ".instValid") = true ->
            ReadReg(implSt, ".inst") = evalExpr (getInst (ReadReg(implSt, ".instPc")) InstMemInit);
          pcSendSame: ReadSend(specSt, ".pcSend") = ReadSend(implSt, ".pcSend")
        }.
    End StateRel.

    Lemma spec_pcSend_eq: forall (old2: TreeState ModElemState specTree),
      ReadSend(old2, ".pcSend") = old2.(Snd).(Snd).(Snd).(Fst).
    Proof.
      intros.
      repeat match goal with
      | x: _ ** _ |- _ => destruct x
      | x: unit |- _ => destruct x
      end.
      unfold readTreeSend, castStateSend.
      cbn.
      reflexivity.
    Qed.

    Lemma impl_pcSend_eq: forall (old1: TreeState ModElemState implTree),
      ReadSend(old1, ".pcSend") = old1.(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Snd).(Fst).
    Proof.
      intros.
      repeat match goal with
      | x: _ ** _ |- _ => destruct x
      | x: unit |- _ => destruct x
      end.
      unfold readTreeSend, castStateSend.
      cbn.
      reflexivity.
    Qed.

    Theorem implSpec: TraceInclusionTree impl spec stateRel.
    Proof.
      Ltac destructTreeCasts :=
        unfold readTreeReg, readTreeRecv, readTreeSend, castStateReg, castStateRegInv, castStateRecv, castStateRecvInv, castStateSend, castStateSendInv, castStateRecvInv in *;
        cbn in *.
      apply StepInclusionTree.
      - intros old1 old2 H_init H_rel.
        destruct H_rel.
        rewrite spec_pcSend_eq, impl_pcSend_eq in *.
        destructTreeCasts.
        repeat match goal with
               | H: _ /\ _ |- _ => destruct H
               end.
        subst.
        rewrite pcSendSame0, pcSame0, dataSame0.
        repeat split; auto.
      - intros a1 old1 new1 H_in H_sem old2 H_rel.
        pose proof H_rel as H_rel_copy.
        destruct H_rel_copy.
        rewrite spec_pcSend_eq, impl_pcSend_eq in *.
        Ltac simplify_bools :=
          unfold Is_true in *;
          try change (negb true) with false in *;
          try change (negb false) with true in *;
          try change (if true then True else False) with True in *;
          try change (if false then True else False) with False in *.
        Ltac invertSemActionTree :=
          repeat match goal with
            | H: SemActionTree _ _ _ _ |- _ => apply InversionSemActionTree in H
            | H: exists _, _ |- _ => destruct H
            | H: _ /\ _ |- _ => destruct H
            | H: context [evalExpr (Not _)] |- _ => simpl in H
            | H: ?P = true -> SemActionTree _ _ _ _ |- _ => destruct P eqn:?
            | H: ?P = false -> SemActionTree _ _ _ _ |- _ => destruct P eqn:?
            | H: True -> _ |- _ => specialize (H I)
            | H: False -> _ |- _ => clear H
            | H: ?a = ?a -> _ |- _ => specialize (H eq_refl)
            | H: true = false -> _ |- _ => clear H
            | H: false = true -> _ |- _ => clear H
            end;
          repeat match goal with
            | H: ?P = true |- _ => rewrite H in *; rename H into H_done
            | H: ?P = false |- _ => rewrite H in *; rename H into H_done
            end;
          simplify_bools; subst; cbn in *; simpl in *;
          repeat match goal with
            | H: True -> _ |- _ => specialize (H I)
            | H: False -> _ |- _ => clear H
            | H: SemActionTree _ _ _ _ |- _ => apply InversionSemActionTree in H
            | H: exists _, _ |- _ => destruct H
            | H: _ /\ _ |- _ => destruct H
            end;
          simplify_bools; subst; cbn in *; simpl in *.
        Ltac useOldTree old :=
          repeat match goal with
          | H: True -> _ |- _ => specialize (H I)
          | H: False -> _ |- _ => clear H
          | H: SemActionTree _ _ _ _ |- _ => apply InversionSemActionTree in H
          | H: exists _, _ |- _ => destruct H
          | H: _ /\ _ |- _ => destruct H
          end;
          subst; cbn in *;
          exists (ReturnTree (ConstBit 0%Zmod)), old;
          split; [right; left; reflexivity | split; [| econstructor; eauto]];
          try rewrite spec_pcSend_eq, impl_pcSend_eq in *;
          constructor;
          destructTreeCasts;
          try repeat match goal with
          | H : _ = InstMemInit |- _ => rewrite H in *
          | H : InstMemInit = _ |- _ => rewrite <- H in *
          end;
          subst; auto; try discriminate;
          try match goal with
          | H: ?P = true, H_prop: ?P = true -> _ |- _ => specialize (H_prop H)
          | H: ?P = false, H_prop: ?P = false -> _ |- _ => specialize (H_prop H)
          | H: ?P = true, H_prop: Is_true ?P -> _ |- _ =>
              assert (H_istrue: Is_true P) by (rewrite H; exact I); specialize (H_prop H_istrue); clear H_istrue
          | H: ?P = false, H_prop: Is_true (negb ?P) -> _ |- _ =>
              assert (H_istrue: Is_true (negb P)) by (rewrite H; exact I); specialize (H_prop H_istrue); clear H_istrue
          end;
          cbn in *; subst; auto; try discriminate.
        repeat match goal with
               | H: In _ _ |- _ => destruct H; try discriminate; subst
               end.
        + unfold implExec in H_sem.
          invertSemActionTree.
          * { useOldTree old2. }
          * { useOldTree old2. }
          * { destructTreeCasts.
              pose proof (instValidProp0 Heqt) as H_prop.
              pose proof (isEq_BoolSpec old1.(Snd).(Snd).(Snd).(Snd).(Snd).(Fst) old1.(Fst)) as sth; destruct sth as [H_eq | H_neq]; subst; try discriminate.
              exists (specProc type).
              exists (evalExpr (nextPc old2.(Fst) (evalExpr (getInst old2.(Fst) InstMemInit)) old2.(Snd).(Snd).(Fst)) ,,
                      (old2.(Snd).(Fst) ,,
                       (evalExpr (execInst old2.(Fst) (evalExpr (getInst old2.(Fst) InstMemInit)) old2.(Snd).(Snd).(Fst)) ,,
                        (old2.(Fst) :: old2.(Snd).(Snd).(Snd).(Fst) ,,
                         tt)))).
              split; [left; reflexivity | split].
              - repeat match goal with
                | x: _ ** _ |- _ => destruct x
                | x: unit |- _ => destruct x
                end.
                constructor;
                destructTreeCasts;
                try rewrite H_eq in *;
                try rewrite pcSendSame0, pcSame0, dataSame0 in *;
                subst; auto; try discriminate.
              - repeat match goal with
                | x: _ ** _ |- _ => destruct x
                | x: unit |- _ => destruct x
                end.
                try rewrite <- instSameSpec0 in *;
                unfold specProc; repeat (econstructor; cbn); eauto. }
          * { useOldTree old2. }
        + unfold implFetch in H_sem.
          invertSemActionTree.
          * { useOldTree old2. }
          * { useOldTree old2. }
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
  Let spMod : ModTree _ :=
    impl (Default Addr) (Default InstMem) (Default DataMem)
         spGetInst spExecInst spNextPc
         (Default PredState)
         spPredictedPc spUpdatePredState.

  Local Definition compiledMod := compileTree spMod.
End Compile.

Set Extraction Output Directory "./Example/SimpleProcessor".
Extraction "Compile" size compiledMod.
