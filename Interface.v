(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

(*
 * Interface contracts: what a child module guarantees to any parent that uses it through its
 * methods, stated without reference to the parent.
 *
 * A child is a tree `tc`, method actions (any return kind) and internal rules. Its contract is
 * given against an abstract state `A`:
 * - `View s a`: impl state `s` stands for abstract state `a`;
 * - `MethodOk m step`: a call of method `m` returning `v` moves the abstract state by `step _ v _`;
 * - `RuleOk r istep`: internal rule `r` moves the abstract state by `istep`;
 * - `InitOk a0`: every initial state stands for `a0`.
 *
 * Two uses:
 * - flush: `A` is the state with every issued operation applied; `istep a a' := a' = a`
 *   (`RuleStutters`), so internal rules are invisible;
 * - ghost list: `A` holds the issued, uncommitted operations, each pending or completed; `istep`
 *   completes pending ones.
 *
 * `MethodOk_lift` / `RuleOk_lift` transport a contract into any parent tree holding the child at
 * path `p`: a parent proof applies them at each call site `liftAction p m` and to each lifted
 * child rule, and never unfolds the child.
 *)

From Stdlib Require Import String List Bool ZArith Zmod Relations.
From Guru Require Import Primitives Library Syntax Combinators Semantics Composition HelperLemmas.

Import ListNotations.

Section Contract.
  Variable tc : Tree Elem.
  Variable A : Type.
  (* The environments the contract holds for (`fun _ => True` for a child without `Recv`). *)
  Variable EnvOk : Env tc -> Prop.
  Variable View : TreeState ElemState tc -> A -> Prop.

  Definition MethodOk {K : Kind} (m : Action type tc K) (step : A -> type K -> A -> Prop) : Prop :=
    forall (env : Env tc) s s' v a,
      EnvOk env -> View s a -> SemAction env m s s' v ->
      exists a', step a v a' /\ View s' a'.

  Definition RuleOk (r : Action type tc (Bit 0)) (istep : A -> A -> Prop) : Prop :=
    MethodOk r (fun a _ a' => istep a a').

  Definition RulesOk (rs : list (Action type tc (Bit 0))) (istep : A -> A -> Prop) : Prop :=
    forall r, In r rs -> RuleOk r istep.

  (* Internal rules that the abstract state does not see (flush). *)
  Definition RuleStutters (r : Action type tc (Bit 0)) : Prop := RuleOk r (fun a a' => a' = a).
  Definition RulesStutter (rs : list (Action type tc (Bit 0))) : Prop := RulesOk rs (fun a a' => a' = a).

  Definition InitOk (a0 : A) : Prop := forall s, InitStateConsistent tc s -> View s a0.

  (* Any run of the internal rules. *)
  Lemma RulesOk_SemActions : forall rs istep, RulesOk rs istep ->
    forall (env : Env tc), EnvOk env ->
    forall s s', SemActions env rs s s' ->
    forall a, View s a -> exists a', clos_refl_trans A istep a a' /\ View s' a'.
  Proof.
    intros rs istep Hok env Henv s s' Hsem.
    induction Hsem as [old new eqPf | old new mid r inA aPf rest IH]; intros a Hv.
    - subst new; exists a; split; [apply rt_refl | exact Hv].
    - destruct (Hok r inA env old mid Zmod.zero a Henv Hv aPf) as [a1 [Hs1 Hv1]].
      destruct (IH a1 Hv1) as [a' [Hs' Hv']].
      exists a'; split; [eapply rt_trans; [apply rt_step; exact Hs1 | exact Hs'] | exact Hv'].
  Qed.

  Lemma RulesStutter_SemActions : forall rs, RulesStutter rs ->
    forall (env : Env tc), EnvOk env ->
    forall s s', SemActions env rs s s' -> forall a, View s a -> View s' a.
  Proof.
    intros rs Hok env Henv s s' Hsem.
    induction Hsem as [old new eqPf | old new mid r inA aPf rest IH]; intros a Hv.
    - subst new; exact Hv.
    - destruct (Hok r inA env old mid Zmod.zero a Henv Hv aPf) as [a1 [-> Hv1]].
      exact (IH a Hv1).
  Qed.
End Contract.

Arguments MethodOk {tc A} EnvOk View {K} m step.
Arguments RuleOk {tc A} EnvOk View r istep.
Arguments RulesOk {tc A} EnvOk View rs istep.
Arguments RuleStutters {tc A} EnvOk View r.
Arguments RulesStutter {tc A} EnvOk View rs.
Arguments InitOk {tc A} View a0.

(* The contract inside a parent tree `t` holding the child at path `p`. The step also says that
 * the rest of the parent state is unchanged (`S'` is `S` with a new child subtree). *)
Section Lift.
  Context {t : Tree Elem}.
  Variable p : NodePath t.
  Context {A : Type}.
  Variable EnvOk : Env (getNode p) -> Prop.
  Variable View : TreeState ElemState (getNode p) -> A -> Prop.

  Lemma MethodOk_lift : forall {K : Kind} (m : Action type (getNode p) K) step,
    MethodOk EnvOk View m step ->
    forall (env : Env t) S S' v a,
      EnvOk (subEnv p env S) -> View (readSubTreeState p S) a ->
      SemAction env (liftAction p m) S S' v ->
      exists a', step a v a' /\ View (readSubTreeState p S') a' /\
                 S' = writeSubTreeState p S (readSubTreeState p S').
  Proof.
    intros K m step Hok env S S' v a Henv Hv Hsem.
    apply SemAction_liftAction_iff in Hsem; destruct Hsem as [sub' [Hsub ->]].
    destruct (Hok _ _ _ _ _ Henv Hv Hsub) as [a' [Hs Hv']].
    exists a'; rewrite readSubTreeState_writeSubTreeState_same.
    split; [exact Hs | split; [exact Hv' | reflexivity]].
  Qed.

  Lemma RuleOk_lift : forall (r : Action type (getNode p) (Bit 0)) istep,
    RuleOk EnvOk View r istep ->
    forall (env : Env t) S S' a,
      EnvOk (subEnv p env S) -> View (readSubTreeState p S) a ->
      SemAction env (liftAction p r) S S' Zmod.zero ->
      exists a', istep a a' /\ View (readSubTreeState p S') a' /\
                 S' = writeSubTreeState p S (readSubTreeState p S').
  Proof. intros r istep Hok env S S' a; exact (MethodOk_lift r _ Hok env S S' Zmod.zero a). Qed.

  (* A lifted stuttering rule keeps the view. *)
  Lemma RuleStutters_lift : forall (r : Action type (getNode p) (Bit 0)),
    RuleStutters EnvOk View r ->
    forall (env : Env t) S S' a,
      EnvOk (subEnv p env S) -> View (readSubTreeState p S) a ->
      SemAction env (liftAction p r) S S' Zmod.zero ->
      View (readSubTreeState p S') a /\ S' = writeSubTreeState p S (readSubTreeState p S').
  Proof.
    intros r Hok env S S' a Henv Hv Hsem.
    destruct (RuleOk_lift r _ Hok env S S' a Henv Hv Hsem) as [a' [-> H]]; exact H.
  Qed.
End Lift.
