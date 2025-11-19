From Stdlib Require Import String List ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Notations Guru.Theorems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.

Section ReadDiffTuple.
  Variable K: Type.
  Variable Convert: (string * K) -> Type.
  Variable ls: list (string * K).
  Variable dt: DiffTuple Convert ls.
  Variable s: string.

  Definition readDiffTupleStr :=
    match getFinStructOption s ls as x return match x with
                                              | Some p => Convert (nth_pf (ls:=ls) (i:=finNum p) (finLt p))
                                              | None => unit
                                              end with
    | Some p => readDiffTuple dt p
    | None => tt
    end.
End ReadDiffTuple.

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
  Variable nextPc: forall ty, ty Addr -> ty Inst -> Expr ty Addr.

  Notation Retv := (Return (ConstDefK (Bit 0))).
  Notation "a @% b" := (readDiffTupleStr a b) (at level 0).

  Section Spec.
    Definition specRegs :=
      [ ("pc", Build_Reg Addr PcInit);
        ("instMem", Build_Reg InstMem InstMemInit);
        ("dataMem", Build_Reg DataMem DataMemInit) ].

    Definition specDecl := {|modRegs := specRegs;
                             modMems := [];
                             modRegUs := [];
                             modMemUs := [];
                             modSends := [];
                             modRecvs := []|}.

    Definition specMl := getModLists specDecl.

    Local Open Scope guru_scope.
    Definition specProc ty: Action ty specMl (Bit 0) :=
      ( RegRead insts <- "instMem" in specMl;
        RegRead pc <- "pc" in specMl;
        RegRead datas <- "dataMem" in specMl;
        Let inst: Inst <- getInst pc insts;
        Let newDatas: DataMem <- execInst pc inst datas;
        Let newPc: Addr <- nextPc pc inst;
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
                             modSends := [];
                             modRecvs := []|}.

    Definition implMl := getModLists implDecl.

    Local Open Scope guru_scope.
    Definition implFetch ty: Action ty implMl (Bit 0) :=
      ( RegRead predState <- "predState" in implMl;
        RegRead prevPredPc <- "predPc" in implMl;
        Let newPredPc <- predictedPc prevPredPc predState;
        RegRead redirectValid <- "redirectValid" in implMl;
        RegRead redirect <- "redirect" in implMl;
        Let fetchPc : Addr <- ITE #redirectValid #redirect #newPredPc;
        RegRead instValid <- "instValid" in implMl;
        RegWrite "redirectValid" in implMl <- ConstBool false;
        If (Not #instValid) Then (
            RegRead insts <- "instMem" in implMl;
            Let inst: Inst <- getInst fetchPc insts;
            RegWrite "instValid" in implMl <- ConstBool true;
            RegWrite "inst" in implMl <- #inst;
            RegWrite "instPc" in implMl <- #fetchPc;
            Retv );
        Retv ).

    Definition implExec ty: Action ty implMl (Bit 0) :=
      ( RegRead instValid <- "instValid" in implMl;
        RegRead inst <- "inst" in implMl;
        RegRead instPc <- "instPc" in implMl;
        RegRead redirectValid <- "redirectValid" in implMl;
        RegRead pc <- "pc" in implMl;
        If (And [Not #redirectValid; #instValid]) Then (
            RegWrite "instValid" in implMl <- ConstBool false;
            If (Not (Eq #instPc #pc)) Then (
                RegWrite "redirectValid" in implMl <- ConstBool true;
                RegWrite "redirect" in implMl <- #pc;
                Retv)
              Else (
                RegRead datas <- "dataMem" in implMl;
                Let newDatas: DataMem <- execInst pc inst datas;
                Let newPc: Addr <- nextPc pc inst;
                RegRead predState <- "predState" in implMl;
                Let newPredState: PredState <- updatePredState pc newPc predState;
                RegWrite "dataMem" in implMl <- #newDatas;
                RegWrite "predState" in implMl <- #newPredState;
                RegWrite "pc" in implMl <- #newPc;
                Retv);
            Retv );
        Retv).

    Definition impl: Mod := {|modDecl := implDecl;
                              modActions ty := [ implFetch ty; implExec ty] |}.

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

    Ltac simplifyInit :=
      repeat match goal with
        | H: InitModConsistent _ |- _ => destruct H
        | t: unit |- _ => destruct t
        end; simpl in *; subst;
    constructor; unfold readDiffTupleStr; auto; intros; try discriminate.

    Ltac invertSemAction :=
      repeat match goal with
        | H: @SemAction _ _ _ _ _ _ _ _ |- _ => apply InversionSemAction in H
        | H: exists _, _ |- _ => destruct H
        | H: _ /\ _ |- _ => destruct H
        | H: context [evalExpr (Not _)] |- _ => simpl in H
        | H: ?P = true -> @SemAction _ _ _ _ _ _ _ _ |- _ => destruct P eqn:?
        | H: true = true -> _ |- _ => specialize (H eq_refl)
        | H: false = false -> _ |- _ => specialize (H eq_refl)
        | H: true = false -> _ |- _ => clear H
        | H: false = true -> _ |- _ => clear H
        end; subst; simpl.

    Theorem implSpec: TraceInclusion impl spec.
    Proof.
      apply StepInclusion with (rel := stateRel) (sameSends := isSameSends) (sameRecvs := isSameRecvs); intros.
      - simplifyInit.
      - repeat match goal with
               | H: In _ _ |- _ => destruct H; try discriminate; subst
               end.
        + unfold implFetch, mregs, implMl, getFinStruct, fieldK, fieldNameK in H0.
          simpl in H0.
          destruct H1.
          invertSemAction.
          destruct old1; simpl in *.
          Ltac useOld old := exists Retv, old;
                                          split; [auto| split; [|econstructor; eauto; simpl]];
                                          repeat match goal with
                                            | H: Prod _ _ |- _ => destruct H
                                            end; simpl in *;
                                          constructor; unfold readDiffTupleStr in *; simpl in *; subst; auto; intros;
                                          try discriminate.
          * useOld old2.
          * useOld old2.
        + unfold implExec, mregs, implMl, getFinStruct, fieldK, fieldNameK in H0.
          simpl in H0.
          destruct H1.
          invertSemAction.
          * destruct old1; simpl in *. useOld old2.
          * unfold readDiffTupleStr, implSt, specSt in *.
            simpl in *.
            exists (specProc type).
            exists ({|stateRegs :=
                        (STRUCT_CONST { "pc" ::= evalExpr
                                                   (nextPc ((stateRegs old2) @% "pc")
                                                      (evalExpr (getInst ((stateRegs old2) @% "pc")
                                                                   (stateRegs old2) @% "instMem")));
                                        "instMem" ::= InstMemInit;
                                        "dataMem" ::= evalExpr
                                                        (execInst
                                                           ((stateRegs old2) @% "pc")
                                                           (evalExpr (getInst ((stateRegs old2) @% "pc")
                                                                        (stateRegs old2) @% "instMem"))
                                                           (stateRegs old2) @% "dataMem")}):
                        FuncState (map (fun x : string * Reg => (fst x, regKind (snd x))) (modRegs specDecl));
                      stateMems := tt: FuncMemState (map (fun x : string * Mem => (fst x, memToMemU (snd x)))
                                                       (modMems specDecl));
                      stateRegUs := tt: FuncState (modRegUs specDecl);
                      stateMemUs := tt: FuncMemState (modMemUs specDecl)|}).
              destruct old1; simpl in *; repeat match goal with
                                           | H: Prod _ _ |- _ => destruct H
                                           end; simpl in *.
              simpl in Heqt.
              apply andb_prop in Heqt; destruct Heqt.
              split.
            -- constructor; unfold readDiffTupleStr, implSt, specSt; simpl; subst; auto; intros; try discriminate.
            -- constructor.
               ++ subst; specialize (instValidProp0 eq_refl).
                  constructor; unfold readDiffTupleStr, implSt, specSt; simpl; subst; auto; intros; try discriminate.
                  ** rewrite instSameSpec0.
                     rewrite Bool.negb_false_iff in Heqb.
                     pose proof (isEq_BoolSpec Fst4 (Fst (stateRegs old2))) as sth.
                     destruct sth; subst; [auto| try discriminate].
                  ** rewrite instSameSpec0.
                     rewrite Bool.negb_false_iff in Heqb.
                     pose proof (isEq_BoolSpec Fst4 (Fst (stateRegs old2))) as sth.
                     destruct sth; subst; [auto| try discriminate].
               ++ repeat constructor; unfold readDiffTupleStr, implSt, specSt; simpl; auto.
                  destruct old2; simpl in *; repeat match goal with
                                               | H: Prod _ _ |- _ => destruct H
                                               end; simpl in *.
                  subst.
                  destruct Snd0, stateMems0, stateRegUs0, stateMemUs0.
                  auto.
          * useOld old2.
    Qed.
  End Implementation.
End SimpleProcessor.
