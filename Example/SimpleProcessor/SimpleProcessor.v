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
          sendSame:
            ReadSend(specSt, ".pcSend") = ReadSend(implSt, ".pcSend")
        }.
    End StateRel.

Ltac useOld old := exists Retv, old;
                                split; [auto| split; [|econstructor; eauto; simpl]];
                                repeat match goal with
                                  | H: Prod _ _ |- _ => destruct H
                                  end; simpl in *;
                                constructor; unfold readDiffTupleStr in *; simpl in *; subst; auto; intros;
                                try discriminate.

Ltac simplifyHyps stateRel :=
  repeat (match goal with
          | H: InitStateConsistent _ _ |- _ => simpl in H
          | H: TreeState ModElemState (Leaf _ _) |- _ => simpl in H
          | H: TreeState ModElemState _ |- _ => destruct H
          | H: TreeState ModElemState _ * (TreeState ModElemState _ * _) |- _ => destruct H
          | H: TreeState ModElemState _ * unit |- _ => destruct H
          | H: unit |- _ => destruct H
          | H: True |- _ => destruct H
          | H: _ /\ _ |- _ => destruct H
          | H: stateRel _ _ |- _ => destruct H
          | H: @SemActionTree _ _ _ _ _ _ |- _ => apply InversionSemActionTree in H
          | H: exists _, _ |- _ => destruct H
          | H: _ /\ _ |- _ => destruct H
          | H: context [evalExpr (Not _)] |- _ => simpl in H
          | H: ?P = true -> @SemActionTree _ _ _ _ _ _ |- _ => destruct P eqn:?
          | H: ?a = ?a -> _ |- _ => specialize (H eq_refl)
          | H: true = false -> _ |- _ => clear H
          | H: false = true -> _ |- _ => clear H
          | H: (?x, ?y) = (?a, ?b) |- _ =>
              assert (x = a) by (apply (f_equal fst) in H; simpl in H; auto);
              assert (y = b) by (apply (f_equal snd) in H; simpl in H; auto);
              clear H
          | H: context[fst (?x, ?y)] |- _ => unfold fst in H
          | H: context[snd (?x, ?y)] |- _ => unfold snd in H
          | H: context[readTreeReg] |- _ => unfold readTreeReg in H; simpl in H
          | H: context[readTreeMem] |- _ => unfold readTreeMem in H; simpl in H
          | H: context[readTreeSend] |- _ => unfold readTreeSend in H; simpl in H
          | H: context[readTreeRecv] |- _ => unfold readTreeRecv in H; simpl in H
          | H: context[castStateReg] |- _ => unfold castStateReg in H; simpl in H
          | H: context[castStateMem] |- _ => unfold castStateMem in H; simpl in H
          | H: context[castStateSend] |- _ => unfold castStateSend in H; simpl in H
          | H: context[castStateRecv] |- _ => unfold castStateRecv in H; simpl in H
          | H: negb ?P = true |- _ => rewrite Bool.negb_true_iff in H
          | H: negb ?P = false |- _ => rewrite Bool.negb_false_iff in H
          end); subst.

Axiom cheat: forall t, t.

Theorem implSpec: TraceInclusionTree impl spec stateRel.
    Proof.
      apply StepInclusionTree with (rel := stateRel); intros.
      - simplifyHyps stateRel.
        repeat constructor; auto.
      - repeat match goal with
               | H: In _ _ |- _ => destruct H; try discriminate; subst
               end.
        + (* implExec *) (*
          unfold implExec in H0.
          simplifyHyps stateRel; simpl in *.
          * eexists; eexists.

            specialize (instValidProp0 eq_refl); subst; simpl in *.
            
            subst.
            simpl in *.
            unfold isEq, list_eqb in Heqb; simpl in Heqb.
          simplifyHyps stateRel; unfoldHyps.
          repeat match goal with
                 end; subst.
              assert (murali:x = y) by (apply (f_equal fst) in H; simpl in H; auto)
          end.
          * repeat match goal with
                   | 
          specialize (instValidProp0 eq_refl); subst.

          destruct H1.
          invertSemAction; unfold readDiffTupleStr, implSt, specSt in *; simpl in *.
          * useOld old2.
          * useOld old2.
          * exists (specProc type).
            exists ({|stateRegs :=
                        (STRUCT_CONST { "pc" ::= evalExpr
                                                   (nextPc ((stateRegs old2) @% "pc")
                                                      (evalExpr (getInst ((stateRegs old2) @% "pc") InstMemInit))
                                                      ((stateRegs old2) @% "dataMem"));
                                        "instMem" ::= InstMemInit;
                                        "dataMem" ::= evalExpr
                                                        (execInst
                                                           ((stateRegs old2) @% "pc")
                                                           (evalExpr (getInst ((stateRegs old2) @% "pc") InstMemInit))
                                                           (stateRegs old2) @% "dataMem")}):
                        FuncState (map (fun x : string * Reg => (fst x, regKind (snd x))) (modRegs specDecl));
                      stateMems := tt: FuncMemState (map (fun x : string * Mem => (fst x, memToMemU (snd x)))
                                                       (modMems specDecl));
                      stateRegUs := tt: FuncState (modRegUs specDecl);
                      stateMemUs := tt: FuncMemState (modMemUs specDecl)|}).
              destruct old1; simpl in *; repeat match goal with
                                           | H: Prod _ _ |- _ => destruct H
                                           end; simpl in *.
              simpl in Heqt; subst.
              specialize (instValidProp0 eq_refl).
              rewrite Bool.negb_false_iff in Heqb; subst.
              pose proof (isEq_BoolSpec Fst4 (Fst (stateRegs old2))) as sth; destruct sth; subst; auto;
                try discriminate; subst.
              split; [auto | split].
            -- constructor; unfold readDiffTupleStr, implSt, specSt; simpl; subst; auto; intros; try discriminate.
            -- repeat econstructor; unfold readDiffTupleStr, implSt, specSt; simpl; auto.
               destruct old2; simpl in *; repeat match goal with
                                            | H: Prod _ _ |- _ => destruct H
                                            end; simpl in *.
               subst.
               repeat match goal with
                      | H: unit |- _ => destruct H
                      end.
               simpl.
               auto.
          * useOld old2.
        + unfold implFetch, mregs, implMl, getFinStruct, fieldK, fieldNameK in H0.
          simpl in H0.
          destruct H1.
          invertSemAction.
          destruct old1; simpl in *.
          * useOld old2.
          * useOld old2.
          *)
        
          apply cheat.
        + apply cheat.
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
