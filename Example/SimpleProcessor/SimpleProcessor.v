From Stdlib Require Import String List ZArith Zmod.
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
    Definition specRegs :=
      [ ("pc", Build_Reg Addr PcInit);
        ("instMem", Build_Reg InstMem InstMemInit);
        ("dataMem", Build_Reg DataMem DataMemInit) ].

    Definition specDecl := {|modRegs := specRegs;
                             modMems := [];
                             modRegUs := [];
                             modMemUs := [];
                             modSends := [("pc", Addr)];
                             modRecvs := []|}.

    Definition specMl := getModLists specDecl.

    Local Open Scope guru_scope.

    Definition specProc ty: Action ty specMl (Bit 0) :=
      ( RegRead insts <- "instMem" in specMl;
        RegRead pc <- "pc" in specMl;
        Put "pc" in specMl <- #pc;
        RegRead datas <- "dataMem" in specMl;
        Let inst: Inst <- getInst pc insts;
        Let newDatas: DataMem <- execInst pc inst datas;
        Let newPc: Addr <- nextPc pc inst datas;
        RegWrite "dataMem" in specMl <- #newDatas;
        RegWrite "pc" in specMl <- #newPc;
        Retv ).

    Definition spec: Mod := {|modDecl := specDecl;
                              modActions ty := [ specProc ty; Retv ] |}.
  End Spec.

  Section Implementation.
    Variable PredState: Kind.
    Variable PredStateInit: type PredState.
    Variable predictedPc: forall ty, ty Addr -> ty PredState -> Expr ty Addr.
    Variable updatePredState: forall ty, ty Addr -> ty Addr -> ty PredState -> Expr ty PredState.

    Definition implRegs :=
      [ ("pc", Build_Reg Addr PcInit);
        ("instMem", Build_Reg InstMem InstMemInit);
        ("dataMem", Build_Reg DataMem DataMemInit);
        ("instValid", Build_Reg Bool false);
        ("inst", Build_Reg Inst (Default _));
        ("instPc", Build_Reg Addr (Default _));
        ("predState", Build_Reg PredState PredStateInit);
        ("predPc", Build_Reg Addr PcInit);
        ("redirectValid", Build_Reg Bool false);
        ("redirect", Build_Reg Addr (Default _))].

    Definition implDecl := {|modRegs := implRegs;
                             modMems := [];
                             modRegUs := [];
                             modMemUs := [];
                             modSends := [("pc", Addr)];
                             modRecvs := []|}.

    Definition implMl := getModLists implDecl.

    Local Open Scope guru_scope.
    Definition implFetch ty: Action ty implMl (Bit 0) :=
      ( RegRead predState <- "predState" in implMl;
        RegRead predPc <- "predPc" in implMl;
        RegRead redirectValid <- "redirectValid" in implMl;
        RegRead redirect <- "redirect" in implMl;
        Let fetchPc : Addr <- ITE #redirectValid #redirect #predPc;
        RegRead instValid <- "instValid" in implMl;
        If (Not #instValid) Then (
            RegWrite "redirectValid" in implMl <- ConstBool false;
            RegRead insts <- "instMem" in implMl;
            Let inst: Inst <- getInst fetchPc insts;
            RegWrite "instValid" in implMl <- ConstBool true;
            RegWrite "inst" in implMl <- #inst;
            RegWrite "instPc" in implMl <- #fetchPc;
            Let newPredPc <- predictedPc predPc predState;
            RegWrite "predPc" in implMl <- #newPredPc;
            Retv );
        Retv ).

    Definition implExec ty: Action ty implMl (Bit 0) :=
      ( RegRead instValid <- "instValid" in implMl;
        RegRead inst <- "inst" in implMl;
        RegRead instPc <- "instPc" in implMl;
        RegRead redirectValid <- "redirectValid" in implMl;
        RegRead pc <- "pc" in implMl;
        If #instValid Then (
            If (Not (Eq #instPc #pc)) Then (
                If (Not #redirectValid) Then (
                    RegWrite "redirectValid" in implMl <- ConstBool true;
                    RegWrite "redirect" in implMl <- #pc;
                    RegWrite "instValid" in implMl <- ConstBool false;
                    Retv);
                Retv)
              Else (
                Put "pc" in implMl <- #pc;
                RegRead datas <- "dataMem" in implMl;
                Let newDatas: DataMem <- execInst pc inst datas;
                Let newPc: Addr <- nextPc pc inst datas;
                RegRead predState <- "predState" in implMl;
                Let newPredState: PredState <- updatePredState pc newPc predState;
                RegWrite "dataMem" in implMl <- #newDatas;
                RegWrite "predState" in implMl <- #newPredState;
                RegWrite "pc" in implMl <- #newPc;
                RegWrite "instValid" in implMl <- ConstBool false;
                Retv);
            Retv );
        Retv).

    Definition impl: Mod := {|modDecl := implDecl;
                              modActions ty := [ implExec ty; implFetch ty] |}.

    Section StateRel.
      Variable implStFull: ModStateModDecl implDecl.
      Variable specStFull: ModStateModDecl specDecl.

      Definition specSt := specStFull.(stateRegs).
      Definition implSt := implStFull.(stateRegs).

      Record stateRel: Prop := {
          pcSame: specSt @% "pc" = implSt @% "pc";
          instSameSpec: specSt @% "instMem" = InstMemInit;
          instSameImpl: implSt @% "instMem" = InstMemInit;
          dataSame: specSt @% "dataMem" = implSt @% "dataMem";
          instValidProp:
            implSt @% "instValid" = true ->
            implSt @% "inst" = evalExpr (getInst (implSt @% "instPc") InstMemInit)
        }.
    End StateRel.

    Lemma isSameSends: modSends (modDecl impl) = modSends (modDecl spec).
    Proof.
      reflexivity.
    Defined.

    Lemma isSameRecvs: modRecvs (modDecl impl) = modRecvs (modDecl spec).
    Proof.
      reflexivity.
    Defined.

    Theorem implSpec: TraceInclusion impl spec.
    Proof.
      apply StepInclusion with (rel := stateRel) (sameSends := isSameSends) (sameRecvs := isSameRecvs); intros.
      - simplifyInit.
      - repeat match goal with
               | H: In _ _ |- _ => destruct H; try discriminate; subst
               end.
        + unfold implExec, mregs, implMl, getFinStruct, fieldK, fieldNameK in H0.
          simpl in H0.
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
  Let spMod : Mod :=
    impl (Default Addr) (Default InstMem) (Default DataMem)
         spGetInst spExecInst spNextPc
         (Default PredState)
         spPredictedPc spUpdatePredState.

  Local Definition compiledMod := compile spMod.
End Compile.

Set Extraction Output Directory "./Example/SimpleProcessor".
Extraction "Compile" size compiledMod.
