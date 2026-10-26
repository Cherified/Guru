(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Semantics Theorems.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section ActionSimAuto.
  Context {t1 t2: Tree DomainElem}.
  Context {env1: Env t1} {env2: Env t2}.
  Context {rel: TreeState DomainElemState t1 -> TreeState DomainElemState t2 -> Prop}.
  Context {env2Exists: EnvInhabited env2}.
  Context {envConsistent: EnvConsistent env1 env2 rel}.

  Lemma LetAction_sim: forall {K K'} (s: string) (a1: Action type t1 K') (a2: Action type t2 K')
                              (cont1: type K' -> Action type t1 K) (cont2: type K' -> Action type t2 K),
    ActionSimulation env1 env2 a1 a2 rel env2Exists envConsistent ->
    (forall v, ActionSimulation env1 env2 (cont1 v) (cont2 v) rel env2Exists envConsistent) ->
    ActionSimulation env1 env2 (LetAction s a1 cont1) (LetAction s a2 cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K K' s a1 a2 cont1 cont2 Ha1 Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    destruct Hstep as [s_mid1 [v_mid [Hstep_a1 Hstep_cont1]]].
    specialize (Ha1 s1 s2 Hrel s_mid1 v_mid Hstep_a1).
    destruct Ha1 as [s_mid2 [Hstep_a2 Hrel_mid]].
    specialize (Hcont v_mid s_mid1 s_mid2 Hrel_mid s1' v Hstep_cont1).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemLetAction with (midState := s_mid2) (midRet := v_mid); auto.
  Qed.

  Lemma LetExp_sim: forall {K K'} (s: string) (e: Expr type K')
                           (cont1: type K' -> Action type t1 K) (cont2: type K' -> Action type t2 K),
    (forall v, ActionSimulation env1 env2 (cont1 v) (cont2 v) rel env2Exists envConsistent) ->
    ActionSimulation env1 env2 (LetExp s e cont1) (LetExp s e cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K K' s e cont1 cont2 Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont (evalExpr e) s1 s2 Hrel s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemLetExp; auto.
  Qed.

  Lemma Return_sim: forall {K} (e: Expr type K),
    ActionSimulation env1 env2 (Return e) (Return e) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K e s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep. destruct Hstep as [H_s H_ret]. subst.
    exists s2. split; auto.
    apply SemReturn; auto.
  Qed.

  Lemma IfElse_sim: forall {K K'} (s: string) (p: Expr type Bool)
                           (ta1: Action type t1 K') (ta2: Action type t2 K')
                           (fa1: Action type t1 K') (fa2: Action type t2 K')
                           (cont1: type K' -> Action type t1 K) (cont2: type K' -> Action type t2 K),
    (evalExpr p = true -> ActionSimulation env1 env2 ta1 ta2 rel env2Exists envConsistent) ->
    (evalExpr p = false -> ActionSimulation env1 env2 fa1 fa2 rel env2Exists envConsistent) ->
    (forall v, ActionSimulation env1 env2 (cont1 v) (cont2 v) rel env2Exists envConsistent) ->
    ActionSimulation env1 env2 (IfElse s p ta1 fa1 cont1) (IfElse s p ta2 fa2 cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K K' s p ta1 ta2 fa1 fa2 cont1 cont2 Ht Hf Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    destruct Hstep as [s_mid1 [v_mid [Ht_step [Hf_step Hcont_step]]]].
    destruct (evalExpr p) eqn:Hp.
    - specialize (Ht eq_refl s1 s2 Hrel s_mid1 v_mid (Ht_step eq_refl)).
      destruct Ht as [s_mid2 [Ht_step2 Hrel_mid]].
      specialize (Hcont v_mid s_mid1 s_mid2 Hrel_mid s1' v Hcont_step).
      destruct Hcont as [s2' [Hcont_step2 Hrel_final]].
      exists s2'. split; auto.
      apply SemIfElse with (midState := s_mid2) (midRet := v_mid); auto.
      intros Hfalse. congruence.
    - specialize (Hf eq_refl s1 s2 Hrel s_mid1 v_mid (Hf_step eq_refl)).
      destruct Hf as [s_mid2 [Hf_step2 Hrel_mid]].
      specialize (Hcont v_mid s_mid1 s_mid2 Hrel_mid s1' v Hcont_step).
      destruct Hcont as [s2' [Hcont_step2 Hrel_final]].
      exists s2'. split; auto.
      apply SemIfElse with (midState := s_mid2) (midRet := v_mid); auto.
      intros Htrue. congruence.
  Qed.

  Lemma System_sim: forall {K} (ls: list (SysT type)) (cont1: Action type t1 K) (cont2: Action type t2 K),
    ActionSimulation env1 env2 cont1 cont2 rel env2Exists envConsistent ->
    ActionSimulation env1 env2 (System ls cont1) (System ls cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K ls cont1 cont2 Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont s1 s2 Hrel s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemSystem. auto.
  Qed.

  Lemma NonDet_sim: forall {K K'} (s: string) (cont1: type K' -> Action type t1 K) (cont2: type K' -> Action type t2 K),
    (forall v, ActionSimulation env1 env2 (cont1 v) (cont2 v) rel env2Exists envConsistent) ->
    ActionSimulation env1 env2 (NonDet s K' cont1) (NonDet s K' cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K K' s cont1 cont2 Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    destruct Hstep as [v_nd Hstep_cont1].
    specialize (Hcont v_nd s1 s2 Hrel s1' v Hstep_cont1).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemNonDet with (v := v_nd). auto.
  Qed.

End ActionSimAuto.

Section ActionSimAutoSameTree.
  Context {t: Tree DomainElem}.
  Context {env1 env2: Env t}.
  Context {rel: TreeState DomainElemState t -> TreeState DomainElemState t -> Prop}.
  Context {env2Exists: EnvInhabited env2}.
  Context {envConsistent: EnvConsistent env1 env2 rel}.

  Lemma ReadReg_sim: forall {K} (s: string) (x: RegPath t)
                            (cont1 cont2: _ -> Action type t K),
    (forall s1 s2, rel s1 s2 ->
        castStateReg x (readTreeState t s1 x.(regPath)) =
        castStateReg x (readTreeState t s2 x.(regPath))) ->
    (forall v, ActionSimulation env1 env2 (cont1 v) (cont2 v) rel env2Exists envConsistent) ->
    ActionSimulation env1 env2 (ReadReg s x cont1) (ReadReg s x cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K s x cont1 cont2 Hval Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    pose proof (Hval s1 s2 Hrel) as Heq.
    specialize (Hcont (castStateReg x (readTreeState t s1 x.(regPath))) s1 s2 Hrel s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemReadReg.
    rewrite <- Heq. auto.
  Qed.

  Lemma WriteReg_sim: forall {K} (x: RegPath t) (v_expr: Expr type (regKind (getRegFromPath x)))
                             (cont1 cont2: Action type t K),
    (forall s1 s2, rel s1 s2 ->
        rel (writeTreeState t s1 x.(regPath) (castStateRegInv x (evalExpr v_expr)))
            (writeTreeState t s2 x.(regPath) (castStateRegInv x (evalExpr v_expr)))) ->
    ActionSimulation env1 env2 cont1 cont2 rel env2Exists envConsistent ->
    ActionSimulation env1 env2 (WriteReg x v_expr cont1) (WriteReg x v_expr cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K x v_expr cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    pose proof (Hrel_update s1 s2 Hrel) as Hrel_mid.
    specialize (Hcont _ _ Hrel_mid s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemWriteReg. auto.
  Qed.

  Lemma ReadRqMem_sim: forall {K} (x: MemPath t)
                              (i: Expr type (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x))))))
                              (p: FinType (memPort (getMemFromPath x)))
                              (cont1 cont2: Action type t K),
    (forall s1 s2, rel s1 s2 ->
        let arr1 := castStateMem x (readTreeState t s1 x.(memPath)) in
        let val1 := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr1.(Fst).(tupleElems) (getDefault _) in
        let arr2 := castStateMem x (readTreeState t s2 x.(memPath)) in
        let val2 := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr2.(Fst).(tupleElems) (getDefault _) in
        rel (writeTreeState t s1 x.(memPath) (castStateMemInv x (arr1.(Fst) ,, updSameTuple arr1.(Snd) p val1)))
            (writeTreeState t s2 x.(memPath) (castStateMemInv x (arr2.(Fst) ,, updSameTuple arr2.(Snd) p val2)))) ->
    ActionSimulation env1 env2 cont1 cont2 rel env2Exists envConsistent ->
    ActionSimulation env1 env2 (ReadRqMem x i p cont1) (ReadRqMem x i p cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K x i p cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont _ _ (Hrel_update s1 s2 Hrel) s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemReadRqMem. auto.
  Qed.

  Lemma ReadRpMem_sim: forall {K} (s: string) (x: MemPath t)
                              (p: FinType (memPort (getMemFromPath x)))
                              (cont1 cont2: _ -> Action type t K),
    (forall s1 s2, rel s1 s2 ->
        readSameTuple (castStateMem x (readTreeState t s1 x.(memPath))).(Snd) p =
        readSameTuple (castStateMem x (readTreeState t s2 x.(memPath))).(Snd) p) ->
    (forall v, ActionSimulation env1 env2 (cont1 v) (cont2 v) rel env2Exists envConsistent) ->
    ActionSimulation env1 env2 (ReadRpMem s x p cont1) (ReadRpMem s x p cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K s x p cont1 cont2 Hval Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    pose proof (Hval s1 s2 Hrel) as Heq.
    specialize (Hcont (readSameTuple (castStateMem x (readTreeState t s1 x.(memPath))).(Snd) p) s1 s2 Hrel s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemReadRpMem.
    rewrite <- Heq. auto.
  Qed.

  Lemma WriteMem_sim: forall {K} (x: MemPath t)
                             (i: Expr type (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x))))))
                             (v_expr: Expr type (memKind (getMemFromPath x)))
                             (cont1 cont2: Action type t K),
    (forall s1 s2, rel s1 s2 ->
        let arr1 := castStateMem x (readTreeState t s1 x.(memPath)) in
        let arr2 := castStateMem x (readTreeState t s2 x.(memPath)) in
        rel (writeTreeState t s1 x.(memPath) (castStateMemInv x (updSameTupleNat arr1.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v_expr) ,, arr1.(Snd))))
            (writeTreeState t s2 x.(memPath) (castStateMemInv x (updSameTupleNat arr2.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v_expr) ,, arr2.(Snd))))) ->
    ActionSimulation env1 env2 cont1 cont2 rel env2Exists envConsistent ->
    ActionSimulation env1 env2 (WriteMem x i v_expr cont1) (WriteMem x i v_expr cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K x i v_expr cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont _ _ (Hrel_update s1 s2 Hrel) s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemWriteMem. auto.
  Qed.

  Lemma Send_sim: forall {K} (x: SendPath t) (v_expr: Expr type (getSendKind x))
                             (cont1 cont2: Action type t K),
    (forall s1 s2, rel s1 s2 ->
        rel (let currentTrace1 := castStateSend x (readTreeState t s1 x.(sendPath)) in
             writeTreeState t s1 x.(sendPath) (castStateSendInv x (evalExpr v_expr :: currentTrace1)))
            (let currentTrace2 := castStateSend x (readTreeState t s2 x.(sendPath)) in
             writeTreeState t s2 x.(sendPath) (castStateSendInv x (evalExpr v_expr :: currentTrace2)))) ->
    ActionSimulation env1 env2 cont1 cont2 rel env2Exists envConsistent ->
    ActionSimulation env1 env2 (Send x v_expr cont1) (Send x v_expr cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K x v_expr cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont _ _ (Hrel_update s1 s2 Hrel) s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemSend. auto.
  Qed.

  Lemma Recv_sim: forall {K} (s: string) (x: RecvPath t)
                           (cont1 cont2: _ -> Action type t K),
    (forall recvVal s1 s2,
        rel s1 s2 ->
        env1 s1 x recvVal ->
        env2 s2 x recvVal) ->
    (forall v, ActionSimulation env1 env2 (cont1 v) (cont2 v) rel env2Exists envConsistent) ->
    ActionSimulation env1 env2 (Recv s x cont1) (Recv s x cont2) rel env2Exists envConsistent.
  Proof.
    unfold ActionSimulation; intros K s x cont1 cont2 Henv_rel Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    destruct Hstep as [recvVal [Henv1 Hstep_cont1]].
    pose proof (Henv_rel recvVal s1 s2 Hrel Henv1) as Henv2.
    pose proof (@envConsistent s1 s2 x x recvVal recvVal Hrel Henv1 Henv2) as Hrel_upd.
    specialize (Hcont recvVal _ _ Hrel_upd s1' v Hstep_cont1).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemRecv with (recvVal := recvVal); auto.
  Qed.

End ActionSimAutoSameTree.

Ltac action_sim_auto :=
  repeat match goal with
  | |- forall _, ActionSimulation _ _ _ _ _ _ _ => intros
  | |- ActionSimulation _ _ (LetAction _ _ _) (LetAction _ _ _) _ _ _ => apply LetAction_sim
  | |- ActionSimulation _ _ (LetExp _ _ _) (LetExp _ _ _) _ _ _ => apply LetExp_sim
  | |- ActionSimulation _ _ (Return _) (Return _) _ _ _ => apply Return_sim
  | |- ActionSimulation _ _ (ReadReg _ _ _) (ReadReg _ _ _) _ _ _ => apply ReadReg_sim
  | |- ActionSimulation _ _ (WriteReg _ _ _) (WriteReg _ _ _) _ _ _ => apply WriteReg_sim
  | |- ActionSimulation _ _ (ReadRqMem _ _ _ _) (ReadRqMem _ _ _ _) _ _ _ => apply ReadRqMem_sim
  | |- ActionSimulation _ _ (ReadRpMem _ _ _ _) (ReadRpMem _ _ _ _) _ _ _ => apply ReadRpMem_sim
  | |- ActionSimulation _ _ (WriteMem _ _ _ _) (WriteMem _ _ _ _) _ _ _ => apply WriteMem_sim
  | |- ActionSimulation _ _ (Send _ _ _) (Send _ _ _) _ _ _ => apply Send_sim
  | |- ActionSimulation _ _ (Recv _ _ _) (Recv _ _ _) _ _ _ => apply Recv_sim
  | |- ActionSimulation _ _ (System _ _) (System _ _) _ _ _ => apply System_sim
  | |- ActionSimulation _ _ (IfElse _ _ _ _ _) (IfElse _ _ _ _ _) _ _ _ => apply IfElse_sim
  | |- ActionSimulation _ _ (NonDet _ _ _) (NonDet _ _ _) _ _ _ => apply NonDet_sim

  | H_meth : forall val, ActionSimulation _ _ (?m val) (?m' val) _ _ _
    |- ActionSimulation _ _ (?m ?arg) (?m' ?arg) _ _ _ =>
      apply H_meth

  | |- _ => eauto
  end.
