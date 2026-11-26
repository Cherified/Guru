(*
 * Copyright 2026 Google LLC
 *
 * SPDX-License-Identifier: MIT
 *)

(*
 * Liveness of a module, as a property of the implementation alone (no spec, no refinement).
 *
 * Progress is a relation `P s s'` on single action steps (e.g. "this step commits an
 * instruction"). Liveness says that progress steps keep occurring on every fair execution.
 *
 * Fairness. Guru actions have no guards, so a fair run is one in which every action fires
 * infinitely often. Every fair run can be cut into consecutive finite *rounds*, each firing every
 * action of the module at least once, in any order. A compiled clock cycle (`combineActions` of
 * the schedule) is one round, whatever the schedule order and including duplicated actions
 * (superscalar); see `Quiet_combineActions`. Liveness is therefore stated over rounds:
 *
 *   Live m := NonBlocking m /\ forall s, Reachable m s -> EvProgress s
 *
 * where `NonBlocking m` says that the environment admits a value at every `Recv`, so every action
 * can fire in every reachable state, and `EvProgress s` (inductive) says that every chain of
 * rounds from `s` without a progress step is finite.
 *
 * Proof method: `LiveRank`, parameterized by
 * - `rank s`: how far `s` is from the next progress step, in a well-founded order;
 * - `Helpful s a`: action `a` is responsible for moving `s` closer to the next progress step.
 * The fields of `LiveRank` are the proof obligations, each about a single step `s -> s'` of an
 * action of `m` from a reachable state `s` that is not a progress step:
 * - `helpExists`: some action of `m` is helpful in every reachable state;
 * - `helpDecr`: a helpful action strictly decreases the rank;
 * - `noRegress`: no action increases the rank;
 * - `helpPersist`: a helpful action stays helpful across any step that leaves the rank unchanged.
 * `LiveRank_Live` proves `Live` from `NonBlocking` and `LiveRank`. All fields are per action, so
 * the result holds for every schedule.
 *)

From Stdlib Require Import String List Bool ZArith Zmod Relations Wellfounded.
From Guru Require Import Primitives Library Syntax Combinators Semantics Theorems.

Set Implicit Arguments.
Set Asymmetric Patterns.

Import ListNotations.

Section Liveness.
  Variable t: Tree Elem.
  Variable env: Env t.
  Variable m: Mod t.
  (* Progress steps. *)
  Variable P: TreeState ElemState t -> TreeState ElemState t -> Prop.

  (* States reachable by some finite run of `m` from an initial state. *)
  Definition Reachable (s: TreeState ElemState t) : Prop :=
    exists s0, SemMod env m s0 s.

  (* Running a list of actions in exactly the given order, with no progress step. *)
  Inductive Quiet : list (Action type t (Bit 0)) -> TreeState ElemState t -> TreeState ElemState t -> Prop :=
  | QuietNil s : Quiet nil s s
  | QuietCons (a: Action type t (Bit 0)) (l: list (Action type t (Bit 0)))
      (s mid s': TreeState ElemState t)
      (aPf: SemAction env a s mid Zmod.zero)
      (noProgress: ~ P s mid)
      (rest: Quiet l mid s') : Quiet (a :: l) s s'.

  (* A round without a progress step: every action of `m` fires at least once, in any order, and
   * nothing else fires. *)
  Definition QuietRound (s s': TreeState ElemState t) : Prop :=
    exists l,
      (forall a, In a (m type) -> In a l) /\
      (forall a, In a l -> In a (m type)) /\
      Quiet l s s'.

  (* A quiet run of `l` is a run of the compiled cycle `combineActions l`. *)
  Lemma Quiet_combineActions : forall l s s',
      Quiet l s s' -> SemAction env (combineActions l) s s' Zmod.zero.
  Proof.
    induction 1; simpl.
    - constructor; reflexivity.
    - econstructor; [exact aPf | exact IHQuiet].
  Qed.

  (* Every chain of rounds from `s` without a progress step is finite. *)
  Inductive EvProgress (s: TreeState ElemState t) : Prop :=
  | EvProgressStep (next: forall s', QuietRound s s' -> EvProgress s').

  (* The environment never blocks an action in a reachable state. Without this, `EvProgress` would
   * hold vacuously in any state from which no round can run. Only `Recv` can block, so this is a
   * condition on `env`; it holds for every `m` when `env` admits a value in every state. *)
  Definition NonBlocking : Prop :=
    forall s a, Reachable s -> In a (m type) -> exists s', SemAction env a s s' Zmod.zero.

  (* `NonBlocking` is a conjunct for `Live`, not a hypothesis. Whether `NonBlocking` holds is not
   * purely a property of the environment: it quantifies over the states `m` can reach, so a module
   * can violate it by driving the environment into a state where it admits nothing at some `Recv`.
   * For example, an `env` that refuses a response to a malformed request blocks a module that
   * issues one. That is a deadlock, and liveness should catch it.
   * - With the conjunction, `Live` fails in that case.
   * - With the implication, `Live` holds trivially and the deadlock goes unnoticed. *)
  Definition Live : Prop :=
    NonBlocking /\ forall s, Reachable s -> EvProgress s.

  (* --- Reachability is closed under steps and rounds --- *)

  Lemma Reachable_step : forall s s' a,
      Reachable s -> In a (m type) -> SemAction env a s s' Zmod.zero -> Reachable s'.
  Proof.
    intros s s' a [s0 Hs0] Hin Ha.
    destruct Hs0 as [old new init acts].
    exists old; constructor; [exact init |].
    eapply combineSemActions; [exact acts |].
    econstructor 2; [exact Hin | exact Ha | constructor 1; reflexivity].
  Qed.

  Lemma Quiet_Reachable : forall l s s',
      Quiet l s s' -> (forall a, In a l -> In a (m type)) -> Reachable s -> Reachable s'.
  Proof.
    induction 1; intros Hincl Hreach; [exact Hreach |].
    apply IHQuiet; [intros; apply Hincl; right; assumption |].
    eapply Reachable_step; [exact Hreach | apply Hincl; left; reflexivity | exact aPf].
  Qed.

  (* --- The proof method --- *)

  Section Rank.
    (* `rank s`: how far `s` is from the next progress step, in the well-founded order `ltM`. *)
    Variable M: Type. (* the type of the measure *)
    Variable ltM: M -> M -> Prop. (* the `lt` for the measure *)
    Hypothesis ltM_wf: well_founded ltM.
    Variable rank: TreeState ElemState t -> M.
    (* `Helpful s a`: action `a` is responsible for moving `s` closer to the next progress step. *)
    Variable Helpful: TreeState ElemState t -> Action type t (Bit 0) -> Prop.

    (* The fields are the proof obligations. Each is about a single step `s -> s'` of an action of
     * `m` from a reachable state `s` that is not a progress step (`~ P s s'`). *)
    Record LiveRank : Prop := {
      (* Some action of `m` is helpful in every reachable state. *)
      helpExists : forall s, Reachable s -> exists a, In a (m type) /\ Helpful s a;
      (* A helpful action strictly decreases the rank. *)
      helpDecr : forall s s' a,
          Reachable s -> In a (m type) -> Helpful s a -> SemAction env a s s' Zmod.zero ->
          ~ P s s' -> ltM (rank s') (rank s);
      (* No action increases the rank. *)
      noRegress : forall s s' b,
          Reachable s -> In b (m type) -> SemAction env b s s' Zmod.zero ->
          ~ P s s' -> rank s' = rank s \/ ltM (rank s') (rank s);
      (* An action that is helpful stays helpful across any step that leaves the rank unchanged.
       * Without this, two actions could hand the helpful role back and forth, each firing exactly
       * when it is not the helpful one, so that the rank never decreases: a livelock. See
       * Muralidaran Vijayaraghavan, "Modular Verification of Hardware Systems" (PhD thesis, MIT,
       * 2016), which shows examples of such livelocks in buggy cache-coherence protocols, where
       * actions interfere destructively. *)
      helpPersist : forall s s' a b,
          Reachable s -> In b (m type) -> Helpful s a -> SemAction env b s s' Zmod.zero ->
          ~ P s s' -> rank s' = rank s -> Helpful s' a
    }.

    Section Proof.
      Hypothesis lr: LiveRank.

      Let ltT := clos_trans M ltM.

      (* Over a quiet sequence of actions of `m`, the rank never increases. *)
      Lemma Quiet_rank : forall l s s',
          Quiet l s s' -> (forall a, In a l -> In a (m type)) -> Reachable s ->
          rank s' = rank s \/ ltT (rank s') (rank s).
      Proof.
        induction 1 as [s | b l s mid s' Hb Hnp Hrest IH]; intros Hincl Hreach.
        - left; reflexivity.
        - assert (HbIn: In b (m type)) by (apply Hincl; left; reflexivity).
          assert (Hincl': forall a, In a l -> In a (m type)) by (intros; apply Hincl; right; assumption).
          assert (Hmid: Reachable mid) by (eapply Reachable_step; eassumption).
          destruct (noRegress lr Hreach HbIn Hb Hnp) as [Heq | Hlt];
            destruct (IH Hincl' Hmid) as [Heq' | Htr].
          + left; congruence.
          + right; rewrite <- Heq; exact Htr.
          + right; rewrite Heq'; apply t_step; exact Hlt.
          + right; eapply t_trans; [exact Htr | apply t_step; exact Hlt].
      Qed.

      (* Over a quiet sequence containing an action `a` that is helpful at its start, the rank
       * strictly decreases: `a` stays helpful until it fires (`helpPersist`), and then decreases
       * the rank (`helpDecr`). *)
      Lemma Quiet_walk : forall l s s',
          Quiet l s s' -> (forall b, In b l -> In b (m type)) -> Reachable s ->
          forall a, In a l -> Helpful s a -> ltT (rank s') (rank s).
      Proof.
        induction 1 as [s | b l s mid s' Hb Hnp Hrest IH]; intros Hincl Hreach a Hin Ha.
        - destruct Hin.
        - assert (HbIn: In b (m type)) by (apply Hincl; left; reflexivity).
          assert (Hincl': forall c, In c l -> In c (m type)) by (intros; apply Hincl; right; assumption).
          assert (Hmid: Reachable mid) by (eapply Reachable_step; eassumption).
          pose proof (Quiet_rank Hrest Hincl' Hmid) as Hrest_rank.
          destruct Hin as [Heq | Hin].
          + (* `a` fires now *)
            subst b.
            pose proof (helpDecr lr Hreach HbIn Ha Hb Hnp) as Hlt.
            destruct Hrest_rank as [Heq' | Htr].
            * rewrite Heq'; apply t_step; exact Hlt.
            * eapply t_trans; [exact Htr | apply t_step; exact Hlt].
          + (* another action fires *)
            destruct (noRegress lr Hreach HbIn Hb Hnp) as [Heq | Hlt].
            * pose proof (helpPersist lr Hreach HbIn Ha Hb Hnp Heq) as Ha'.
              rewrite <- Heq; exact (IH Hincl' Hmid a Hin Ha').
            * destruct Hrest_rank as [Heq' | Htr].
              -- rewrite Heq'; apply t_step; exact Hlt.
              -- eapply t_trans; [exact Htr | apply t_step; exact Hlt].
      Qed.

      (* Every quiet round from a reachable state strictly decreases the rank. *)
      Theorem LiveRank_EvProgress : forall s, Reachable s -> EvProgress s.
      Proof.
        assert (Hwf: well_founded ltT) by (apply wf_clos_trans; exact ltM_wf).
        enough (Hall: forall mu s, rank s = mu -> Reachable s -> EvProgress s)
          by (intros s; exact (Hall _ s eq_refl)).
        intros mu; induction mu as [mu IH] using (well_founded_ind Hwf).
        intros s Hmu Hreach; constructor.
        intros s' [l [Hall [Hincl Hquiet]]].
        destruct (helpExists lr Hreach) as [a [HaIn Ha]].
        pose proof (Quiet_walk Hquiet Hincl Hreach (Hall _ HaIn) Ha) as Htr.
        eapply IH; [subst mu; exact Htr | reflexivity |].
        eapply Quiet_Reachable; eassumption.
      Qed.
    End Proof.

    Theorem LiveRank_Live : NonBlocking -> LiveRank -> Live.
    Proof. intros Hnb lr; split; [exact Hnb | exact (LiveRank_EvProgress lr)]. Qed.
  End Rank.
End Liveness.
