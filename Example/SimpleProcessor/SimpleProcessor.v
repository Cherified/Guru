(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 * Copyright 2026 Google LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List ZArith Zmod Ascii.
From Guru Require Import Primitives Library Syntax Combinators Semantics Notations Theorems HelperLemmas Ltacs Liveness.

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
            (* Predict from the address just fetched, so that after a redirect, prediction
               continues from the redirect target instead of the stale prediction. *)
            Let newPredPc <- predictedPc fetchPc predState;
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

    Theorem implSpec:
      forall env1 env2,
        ModSimulation env1 env2 impl spec stateRel.
    Proof.
      intros env1 env2.
      apply ActionToModSimulation with (rel := stateRel); intros.
      - simplifyHyps stateRel.
        repeat econstructor; eauto.
      - destructActionInList impl.
        + unfold implExec in *; invertAction; simplifyHyps stateRel.
          * simulateRetv specTree.
          * simulateRetv specTree.
          * specialize (instValidProp0 eq_refl).
            match goal with
            | H: context [isEq ?x ?y] |- _ =>
                pose proof (@isEq_BoolSpec Addr x y) as sth;
                destruct sth; [subst; simulateAction (specProc type) | discriminate]
            end.
          * simulateRetv specTree.
        + unfold implFetch in *; invertAction; simplifyHyps stateRel.
          * simulateRetv specTree.
          * simulateRetv specTree.
    Qed.

    (* =======================================================================
     * Liveness: the implementation commits by sending on `.pcSend`.
     *
     * The rank is the number of helpful steps left before the next commit:
     *
     *   state                       rank  helpful action
     *   instValid,  instPc = pc       1   Exec: commits
     *   ~instValid, redirectValid     2   Fetch: fetches at redirect (= pc), giving rank 1
     *   instValid,  instPc <> pc      3   Exec: sets the redirect, giving rank 2
     *   ~instValid, ~redirectValid    4   Fetch: fetches at predPc, giving rank 1 or 3
     *
     * Exec is helpful exactly when `instValid` is true, Fetch otherwise; in every row, the other
     * action does nothing. The invariant `implInv` says that while a redirect is pending,
     * `redirect = pc` and `instValid` is false.
     * ======================================================================= *)

    (* A commit: a step that sends on `.pcSend`. *)
    Definition implCommits (s s': TreeState ElemState implTree) : Prop :=
      length RdSend(s, ".pcSend") < length RdSend(s', ".pcSend").

    Definition implInv (s: TreeState ElemState implTree) : Prop :=
      RdReg(s, ".redirectValid") = true ->
      RdReg(s, ".instValid") = false /\ RdReg(s, ".redirect") = RdReg(s, ".pc").

    Definition implRank (s: TreeState ElemState implTree) : nat :=
      if RdReg(s, ".instValid")
      then (if isEq RdReg(s, ".instPc") RdReg(s, ".pc") then 1 else 3)
      else (if RdReg(s, ".redirectValid") then 2 else 4).

    Definition implHelpful (s: TreeState ElemState implTree) (a: Action type implTree (Bit 0)) : Prop :=
      a = (if RdReg(s, ".instValid") then implExec type else implFetch type).

    (* Case-split every `isEq` in the goal and the hypotheses. *)
    Local Ltac destructIsEq :=
      repeat match goal with
        | |- context [@isEq ?k ?x ?y] => destruct (@isEq_BoolSpec k x y); subst
        | H: context [@isEq ?k ?x ?y] |- _ => destruct (@isEq_BoolSpec k x y); subst
        end.

    (* Close one case of an action: split the remaining booleans, apply the invariant, compare
     * addresses, then do the arithmetic. *)
    Local Ltac closeCase :=
      intros; repeat match goal with b: bool |- _ => destruct b end; simpl in *;
      repeat match goal with
        | H: true = true -> _ |- _ => specialize (H eq_refl)
        | H: _ /\ _ |- _ => destruct H
        end;
      subst; try discriminate; destructIsEq; simpl in *; try discriminate; try congruence; try lia.

    Lemma implInv_step : forall env s s' a,
        implInv s -> In a (impl type) -> SemAction env a s s' Zmod.zero -> implInv s'.
    Proof.
      intros env s s' a Hinv Hin Hsem.
      destructActionInList impl; [unfold implExec in * | unfold implFetch in *]; invertAction;
        unfold implInv in *; simplifyHyps implInv.
      all: intros; repeat match goal with
                   | H: true = true -> _ |- _ => specialize (H eq_refl)
                   | H: ?b = true -> _, H': ?b = true |- _ => specialize (H H')
                   | H: _ /\ _ |- _ => destruct H
                   end; subst; try discriminate; try (split; congruence).
    Qed.

    Lemma implInv_reachable : forall env s, Reachable env impl s -> implInv s.
    Proof.
      intros env s [s0 Hmod]; destruct Hmod as [old new init acts].
      assert (Hinit: implInv old) by (unfold implInv; simplifyHyps implInv; intros; discriminate).
      clear init; revert Hinit; induction acts as [old new Heq | old new mid a inA aPf rest IH]; intros Hinit.
      - subst; exact Hinit.
      - exact (IH (implInv_step Hinit inA aPf)).
    Qed.

    Theorem implLive : forall env, Live env impl implCommits.
    Proof.
      intros env.
      apply (@LiveRank_Live implTree env impl implCommits nat lt lt_wf implRank implHelpful).
      - (* NonBlocking: there is no Recv, so both actions always run *)
        intros s a _ Hin.
        assert (Hev: evalActionPropGen env a s (fun _ _ => True)).
        { destructActionInList impl; [unfold implExec | unfold implFetch]; cbn [evalActionPropGen];
            repeat match goal with |- context [if ?c then _ else _] => destruct c end; exact I. }
        destruct (evalActionPropGen_to_SemAction a s _ Hev) as [s' [r [Hsem _]]].
        exists s'; rewrite (Zmod_1_0 r) in Hsem; exact Hsem.
      - constructor.
        + (* helpExists *)
          intros s _; exists (if RdReg(s, ".instValid") then implExec type else implFetch type).
          split; [destruct RdReg(s, ".instValid"); simpl; auto | reflexivity].
        + (* helpDecr *)
          intros s s' a Hreach _ Ha Hsem.
          pose proof (implInv_reachable Hreach) as Hinv.
          unfold implHelpful in Ha; subst a.
          unfold implCommits, implRank, implInv in *.
          destruct RdReg(s, ".instValid") eqn:Hv; [unfold implExec in Hsem | unfold implFetch in Hsem];
            invertAction; simplifyHyps implInv.
          all: closeCase.
        + (* noRegress *)
          intros s s' b Hreach Hin Hsem.
          pose proof (implInv_reachable Hreach) as Hinv.
          unfold implCommits, implRank, implInv in *.
          destructActionInList impl; [unfold implExec in * | unfold implFetch in *];
            invertAction; simplifyHyps implInv.
          all: closeCase.
        + (* helpPersist: the rank determines `instValid` (odd ranks when true, even when false),
           * and `instValid` determines the helpful action *)
          intros s s' a b _ _ Ha _ _ Hrank.
          unfold implHelpful in *; subst a.
          assert (Hv: RdReg(s', ".instValid") = RdReg(s, ".instValid")).
          { unfold implRank in Hrank; revert Hrank.
            repeat match goal with |- context [if ?c then _ else _] => destruct c end;
              intros; congruence. }
          rewrite Hv; reflexivity.
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

  (* Fetch: instruction = instMem[addr] *)
  Let spGetInst ty (addr : ty Addr) (imem : ty InstMem) : Expr ty Inst :=
    #imem @[ #addr ].

  (* Execute: unless the instruction is a branch, dataMem[dst] := dataMem[src1] + dataMem[src2] *)
  Let spExecInst ty (addr : ty Addr) (inst : ty Inst) (dmem : ty DataMem)
    : Expr ty DataMem :=
        ITE (##inst`"isBranchIfEq")
          #dmem
          (#dmem @[##inst`"dst" <- Add [#dmem @[ ##inst`"src1"]; #dmem @[ ##inst`"src2"]]]).

  (* Next PC: a taken branch (dataMem[src1] = dataMem[src2]) goes to dst; otherwise PC + 1 *)
  Let spNextPc ty (addr : ty Addr) (inst : ty Inst) (dmem : ty DataMem) : Expr ty Addr :=
        ITE (##inst`"isBranchIfEq")
          (ITE (Eq #dmem @[ ##inst`"src1"] #dmem @[ ##inst`"src2"]) (##inst`"dst") (Add [#addr; $1]))
          (Add [#addr; $1]).

  (* Trivial branch predictor: always predicts PC + 1; no state *)
  Let PredState := Bit 0.
  Let spPredictedPc ty (addr : ty Addr) (_ : ty PredState) : Expr ty Addr :=
    Add [#addr; $1].
  Let spUpdatePredState ty (_ _ : ty Addr) (_ : ty PredState)
      : Expr ty PredState := ConstDef.

  (* Instantiate the pipelined implementation *)
  Definition sp : Mod _ :=
    impl (getDefault Addr) (getDefault InstMem) (getDefault DataMem)
         spGetInst spExecInst spNextPc
         (getDefault PredState)
         spPredictedPc spUpdatePredState.
End Compile.

From Guru Require Import Extraction.
Set Extraction Output Directory "./Example/SimpleProcessor".

From Guru Require Import Compiler.
Definition compiledMod := compile sp.
Extraction "Compile" kindSize Z.log2_up getDefault isEq compiledMod.
