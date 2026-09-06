(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List ZArith Lia Bool Zmod.
Import ListNotations.
Open Scope string_scope.
From Guru Require Import Library Syntax Notations Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Open Scope guru_scope.
Local Open Scope list_scope.

(* ===========================================================================
 * 1. Abstract Merge Fold Definitions
 * =========================================================================== *)

Section AbstractMergeFold.
  Variable A : Type.
  Variable f : A -> A -> A.
  Variable e : A.

  (* Depth-based power-of-2 merge fold: evaluates a balanced tree of depth d *)
  Fixpoint merge_fold_pow2 (depth : nat) (get : nat -> A) (offset : nat) : A :=
    match depth with
    | 0%nat => get offset
    | S d =>
        let span := 2 ^ d in
        f (merge_fold_pow2 d get offset)
          (merge_fold_pow2 d get (offset + span))
    end.

  (* The sequence of elements evaluated by a tree of given depth *)
  Definition slice (depth : nat) (get : nat -> A) (offset : nat) : list A :=
    map get (seq offset (2 ^ depth)).

  (* General list wrapper rounding up to next power-of-2 depth *)
  Definition merge_fold_list (l : list A) : A :=
    let n := length l in
    match n with
    | 0%nat => e
    | 1%nat => nth 0 l e
    | _ =>
        let depth := Z.to_nat (Z.log2_up (Z.of_nat n)) in
        merge_fold_pow2 depth (fun i => nth i l e) 0
    end.

End AbstractMergeFold.

Arguments merge_fold_pow2 {A} f depth get offset.
Arguments slice {A} depth get offset.
Arguments merge_fold_list {A} f e l.

(* ===========================================================================
 * 2. Abstract Equivalence: merge_fold = fold_right = fold_left
 * =========================================================================== *)

Section AbstractEquivalence.
  Variable A : Type.
  Variable f : A -> A -> A.
  Variable e : A.

  Hypothesis Hassoc : forall x y z, f x (f y z) = f (f x y) z.
  Hypothesis Hid_l  : forall x, f e x = x.
  Hypothesis Hid_r  : forall x, f x e = x.

  Lemma fold_right_f_acc : forall l acc,
    fold_right f acc l = f (fold_right f e l) acc.
  Proof.
    induction l as [| x xs IH]; intros acc.
    - simpl. rewrite Hid_l. reflexivity.
    - simpl. rewrite IH. rewrite Hassoc. reflexivity.
  Qed.

  Lemma fold_right_app_monoid : forall l1 l2,
    fold_right f e (l1 ++ l2) = f (fold_right f e l1) (fold_right f e l2).
  Proof.
    intros l1 l2.
    rewrite fold_right_app.
    apply fold_right_f_acc.
  Qed.

  Lemma seq_split_pow2 : forall d offset,
    seq offset (2 ^ (S d)) = seq offset (2 ^ d) ++ seq (offset + 2 ^ d) (2 ^ d).
  Proof.
    intros d offset.
    simpl (2 ^ S d).
    replace (2 ^ d + (2 ^ d + 0)) with (2 ^ d + 2 ^ d) by lia.
    rewrite seq_app.
    reflexivity.
  Qed.

  Theorem merge_fold_pow2_equiv_fold_right : forall depth get offset,
    merge_fold_pow2 f depth get offset = fold_right f e (slice depth get offset).
  Proof.
    induction depth as [| d IH]; intros get offset.
    - unfold slice. simpl.
      rewrite Hid_r. reflexivity.
    - simpl (merge_fold_pow2 f (S d) get offset).
      rewrite IH.
      rewrite IH.
      unfold slice.
      rewrite seq_split_pow2.
      rewrite map_app.
      rewrite fold_right_app_monoid.
      reflexivity.
  Qed.

  Lemma fold_left_f_acc : forall l acc,
    fold_left f l acc = f acc (fold_left f l e).
  Proof.
    induction l as [| x xs IH]; intros acc.
    - simpl. rewrite Hid_r. reflexivity.
    - simpl. rewrite (IH (f acc x)).
      rewrite (IH (f e x)).
      rewrite Hid_l.
      rewrite Hassoc.
      reflexivity.
  Qed.

  Theorem fold_left_fold_right_monoid : forall l,
    fold_left f l e = fold_right f e l.
  Proof.
    induction l as [| x xs IH].
    - reflexivity.
    - simpl fold_right.
      simpl fold_left.
      rewrite fold_left_f_acc.
      rewrite Hid_l.
      rewrite IH.
      reflexivity.
  Qed.

  Theorem merge_fold_pow2_equiv_fold_left : forall depth get offset,
    merge_fold_pow2 f depth get offset = fold_left f (slice depth get offset) e.
  Proof.
    intros depth get offset.
    rewrite fold_left_fold_right_monoid.
    apply merge_fold_pow2_equiv_fold_right.
  Qed.

  Lemma fold_right_repeat_e : forall n,
    fold_right f e (repeat e n) = e.
  Proof.
    induction n as [| n' IH]; simpl.
    - reflexivity.
    - rewrite IH. apply Hid_l.
  Qed.

  Lemma map_nth_seq_aux : forall l start,
    map (fun i => nth (i - start) l e) (seq start (length l)) = l.
  Proof.
    induction l as [| x xs IH]; intros start.
    - reflexivity.
    - simpl (length (x :: xs)).
      simpl (seq start (S (length xs))).
      change (map (fun i => nth (i - start) (x :: xs) e) (start :: seq (S start) (length xs)))
        with (nth (start - start) (x :: xs) e :: map (fun i => nth (i - start) (x :: xs) e) (seq (S start) (length xs))).
      replace (start - start) with 0 by lia.
      simpl (nth 0 (x :: xs) e).
      f_equal.
      rewrite <- (IH (S start)) at 2.
      apply map_ext_in.
      intros i Hin.
      apply in_seq in Hin.
      destruct Hin as [Hge Hlt].
      replace (i - start) with (S (i - S start)) by lia.
      simpl.
      reflexivity.
  Qed.

  Lemma map_nth_seq_0 : forall l,
    map (fun i => nth i l e) (seq 0 (length l)) = l.
  Proof.
    intros l.
    rewrite <- (map_nth_seq_aux l 0) at 2.
    apply map_ext.
    intros i.
    replace (i - 0) with i by lia.
    reflexivity.
  Qed.

  Lemma map_nth_overflow : forall l len start,
    length l <= start ->
    map (fun i => nth i l e) (seq start len) = repeat e len.
  Proof.
    induction len as [| len' IH]; intros start Hle.
    - reflexivity.
    - simpl.
      rewrite nth_overflow by lia.
      f_equal.
      apply IH.
      lia.
  Qed.

  Lemma slice_pow2_ge : forall depth l,
    length l <= 2 ^ depth ->
    slice depth (fun i => nth i l e) 0 = l ++ repeat e (2 ^ depth - length l).
  Proof.
    intros depth l Hle.
    unfold slice.
    replace (2 ^ depth) with (length l + (2 ^ depth - length l)) at 1 by lia.
    rewrite seq_app.
    rewrite map_app.
    rewrite map_nth_seq_0.
    f_equal.
    apply map_nth_overflow.
    lia.
  Qed.

  Theorem merge_fold_list_equiv_fold_right : forall l,
    merge_fold_list f e l = fold_right f e l.
  Proof.
    intros l.
    unfold merge_fold_list.
    destruct (length l) as [| n] eqn:Elen.
    - destruct l; [ reflexivity | discriminate ].
    - destruct n as [| n'].
      + destruct l as [| x [| y ys]]; try discriminate.
        simpl. rewrite Hid_r. reflexivity.
      + remember (S (S n')) as len eqn:Elen2.
        rewrite merge_fold_pow2_equiv_fold_right.
        assert (Hbound: len <= 2 ^ (Z.to_nat (Z.log2_up (Z.of_nat len)))).
        { assert (Hle: (Z.of_nat len <= 2 ^ Z.log2_up (Z.of_nat len))%Z).
          { apply (proj2 (Z.log2_log2_up_spec (Z.of_nat len) ltac:(lia))). }
          apply (Z2Nat.inj_le (Z.of_nat len) (2 ^ Z.log2_up (Z.of_nat len))) in Hle;
            [| lia | apply Z.pow_nonneg; lia ].
          rewrite Nat2Z.id in Hle.
          assert (Hpow: (2 ^ Z.log2_up (Z.of_nat len))%Z = Z.of_nat (2 ^ Z.to_nat (Z.log2_up (Z.of_nat len)))).
          { rewrite Nat2Z.inj_pow.
            rewrite Z2Nat.id by (apply Z.log2_up_nonneg).
            reflexivity. }
          rewrite Hpow in Hle.
          rewrite Nat2Z.id in Hle.
          exact Hle. }
        assert (Hbound_l: length l <= 2 ^ (Z.to_nat (Z.log2_up (Z.of_nat len)))) by lia.
        rewrite (slice_pow2_ge (Z.to_nat (Z.log2_up (Z.of_nat len))) l Hbound_l).
        rewrite fold_right_app_monoid.
        rewrite fold_right_repeat_e.
        rewrite Hid_r.
        reflexivity.
  Qed.

  Theorem merge_fold_list_equiv_fold_left : forall l,
    merge_fold_list f e l = fold_left f l e.
  Proof.
    intros l.
    rewrite fold_left_fold_right_monoid.
    apply merge_fold_list_equiv_fold_right.
  Qed.

End AbstractEquivalence.

(* ===========================================================================
 * 3. Expr (Syntax) to Semantics Equivalence
 * =========================================================================== *)

Section ExprSemantics.
  Variable k : Kind.
  Variable f_syn : Expr type k -> Expr type k -> Expr type k.
  Variable e_syn : Expr type k.

  Variable f_sem : type k -> type k -> type k.
  Variable e_sem : type k.

  Hypothesis Heval_f : forall a b, evalExpr (f_syn a b) = f_sem (evalExpr a) (evalExpr b).
  Hypothesis Heval_e : evalExpr e_syn = e_sem.

  Hypothesis Hassoc : forall x y z, f_sem x (f_sem y z) = f_sem (f_sem x y) z.
  Hypothesis Hid_l  : forall x, f_sem e_sem x = x.
  Hypothesis Hid_r  : forall x, f_sem x e_sem = x.

  Lemma evalExpr_fold_left : forall l acc_syn,
    evalExpr (fold_left f_syn l acc_syn) =
    fold_left f_sem (map (@evalExpr k) l) (evalExpr acc_syn).
  Proof.
    induction l as [| x xs IH]; intros acc_syn.
    - simpl. reflexivity.
    - simpl. rewrite IH. rewrite Heval_f. reflexivity.
  Qed.

  Theorem evalExpr_fold_left_base : forall l,
    evalExpr (fold_left f_syn l e_syn) =
    fold_left f_sem (map (@evalExpr k) l) e_sem.
  Proof.
    intros l.
    rewrite evalExpr_fold_left.
    rewrite Heval_e.
    reflexivity.
  Qed.

  Lemma evalExpr_fold_right : forall l acc_syn,
    evalExpr (fold_right f_syn acc_syn l) =
    fold_right f_sem (evalExpr acc_syn) (map (@evalExpr k) l).
  Proof.
    induction l as [| x xs IH]; intros acc_syn.
    - simpl. reflexivity.
    - simpl. rewrite Heval_f. rewrite IH. reflexivity.
  Qed.

  Theorem evalExpr_merge_fold_pow2 : forall depth (get : nat -> Expr type k) offset,
    evalExpr (merge_fold_pow2 f_syn depth get offset) =
    merge_fold_pow2 f_sem depth (fun i => evalExpr (get i)) offset.
  Proof.
    induction depth as [| d IH]; intros get offset.
    - reflexivity.
    - change (merge_fold_pow2 f_syn (S d) get offset) with
        (f_syn (merge_fold_pow2 f_syn d get offset)
               (merge_fold_pow2 f_syn d get (offset + 2 ^ d))).
      rewrite Heval_f.
      rewrite IH.
      rewrite IH.
      reflexivity.
  Qed.

  (* The grand equivalence for Expr: evaluating tree fold = semantic fold_left *)
  Theorem evalExpr_merge_fold_pow2_equiv_fold_left : forall depth (get : nat -> Expr type k) offset,
    evalExpr (merge_fold_pow2 f_syn depth get offset) =
    fold_left f_sem (map (@evalExpr k) (slice depth get offset)) e_sem.
  Proof.
    intros depth get offset.
    rewrite evalExpr_merge_fold_pow2.
    rewrite (@merge_fold_pow2_equiv_fold_left _ f_sem e_sem Hassoc Hid_l Hid_r).
    unfold slice.
    rewrite map_map.
    reflexivity.
  Qed.

  (* Bridge theorem: evaluating tree fold = evaluating syntactic fold_left *)
  Theorem evalExpr_merge_fold_pow2_equiv_evalExpr_fold_left : forall depth (get : nat -> Expr type k) offset,
    evalExpr (merge_fold_pow2 f_syn depth get offset) =
    evalExpr (fold_left f_syn (slice depth get offset) e_syn).
  Proof.
    intros depth get offset.
    rewrite evalExpr_merge_fold_pow2_equiv_fold_left.
    rewrite evalExpr_fold_left.
    rewrite Heval_e.
    reflexivity.
  Qed.

  Theorem evalExpr_merge_fold_pow2_equiv_evalExpr_fold_right : forall depth (get : nat -> Expr type k) offset,
    evalExpr (merge_fold_pow2 f_syn depth get offset) =
    evalExpr (fold_right f_syn e_syn (slice depth get offset)).
  Proof.
    intros depth get offset.
    rewrite evalExpr_merge_fold_pow2.
    rewrite (@merge_fold_pow2_equiv_fold_right _ f_sem e_sem Hassoc Hid_l Hid_r).
    rewrite evalExpr_fold_right.
    rewrite Heval_e.
    unfold slice.
    rewrite map_map.
    reflexivity.
  Qed.

  Lemma evalExpr_nth : forall l i,
    evalExpr (nth i l e_syn) = nth i (map (@evalExpr k) l) e_sem.
  Proof.
    induction l as [| x xs IH]; intros i.
    - destruct i; simpl; apply Heval_e.
    - destruct i; simpl.
      + reflexivity.
      + apply IH.
  Qed.

  Lemma merge_fold_pow2_ext_expr : forall depth (get1 get2 : nat -> type k) offset,
    (forall i, get1 i = get2 i) ->
    merge_fold_pow2 f_sem depth get1 offset = merge_fold_pow2 f_sem depth get2 offset.
  Proof.
    induction depth as [| d IH]; intros get1 get2 offset Heq; simpl.
    - apply Heq.
    - f_equal; apply IH; intros i; apply Heq.
  Qed.

  Theorem evalExpr_merge_fold_list : forall l,
    evalExpr (merge_fold_list f_syn e_syn l) =
    merge_fold_list f_sem e_sem (map (@evalExpr k) l).
  Proof.
    intros l.
    unfold merge_fold_list.
    rewrite length_map.
    destruct l as [| x [| y ys]].
    - simpl. apply Heval_e.
    - simpl. reflexivity.
    - simpl.
      rewrite evalExpr_merge_fold_pow2.
      apply merge_fold_pow2_ext_expr.
      intros i.
      destruct i as [| [| i']]; simpl; [reflexivity | reflexivity | apply evalExpr_nth].
  Qed.

  Theorem evalExpr_fold_right_base : forall l,
    evalExpr (fold_right f_syn e_syn l) =
    fold_right f_sem e_sem (map (@evalExpr k) l).
  Proof.
    intros l.
    rewrite evalExpr_fold_right.
    rewrite Heval_e.
    reflexivity.
  Qed.

  Theorem evalExpr_merge_fold_list_equiv_fold_left : forall l,
    evalExpr (merge_fold_list f_syn e_syn l) =
    fold_left f_sem (map (@evalExpr k) l) e_sem.
  Proof.
    intros l.
    rewrite evalExpr_merge_fold_list.
    apply merge_fold_list_equiv_fold_left; assumption.
  Qed.

  Theorem evalExpr_merge_fold_list_equiv_evalExpr_fold_left : forall l,
    evalExpr (merge_fold_list f_syn e_syn l) =
    evalExpr (fold_left f_syn l e_syn).
  Proof.
    intros l.
    rewrite evalExpr_merge_fold_list_equiv_fold_left.
    rewrite evalExpr_fold_left_base.
    reflexivity.
  Qed.

  Theorem evalExpr_merge_fold_list_equiv_fold_right : forall l,
    evalExpr (merge_fold_list f_syn e_syn l) =
    fold_right f_sem e_sem (map (@evalExpr k) l).
  Proof.
    intros l.
    rewrite evalExpr_merge_fold_list.
    apply merge_fold_list_equiv_fold_right; assumption.
  Qed.

  Theorem evalExpr_merge_fold_list_equiv_evalExpr_fold_right : forall l,
    evalExpr (merge_fold_list f_syn e_syn l) =
    evalExpr (fold_right f_syn e_syn l).
  Proof.
    intros l.
    rewrite evalExpr_merge_fold_list_equiv_fold_right.
    rewrite evalExpr_fold_right_base.
    reflexivity.
  Qed.

End ExprSemantics.

(* ===========================================================================
 * 4. LetExpr (Hardware Wire-Binding) to Semantics Equivalence
 * =========================================================================== *)

Section LiftLet.
  Variable ty : Kind -> Type.
  Variable k : Kind.
  Variable comb : ty k -> ty k -> LetExpr ty k.

  Definition liftLet (e1 e2 : LetExpr ty k) : LetExpr ty k :=
    LETE v1 : k <- e1 ;
    LETE v2 : k <- e2 ;
    comb v1 v2.
End LiftLet.

Arguments liftLet {ty k} comb e1 e2.

Section LetExprSemantics.
  Variable k : Kind.
  Variable comb : type k -> type k -> LetExpr type k.

  Definition f_sem (v1 v2 : type k) : type k :=
    evalLetExpr (comb v1 v2).

  Variable e_syn : LetExpr type k.
  Variable e_sem : type k.
  Hypothesis Heval_e : evalLetExpr e_syn = e_sem.

  Hypothesis Hassoc : forall x y z, f_sem x (f_sem y z) = f_sem (f_sem x y) z.
  Hypothesis Hid_l  : forall x, f_sem e_sem x = x.
  Hypothesis Hid_r  : forall x, f_sem x e_sem = x.

  Lemma evalLetExpr_liftLet : forall e1 e2,
    evalLetExpr (liftLet comb e1 e2) = f_sem (evalLetExpr e1) (evalLetExpr e2).
  Proof.
    intros e1 e2.
    unfold liftLet, f_sem.
    simpl.
    reflexivity.
  Qed.

  Lemma evalLetExpr_fold_left : forall l acc,
    evalLetExpr (fold_left (liftLet comb) l acc) =
    fold_left f_sem (map (@evalLetExpr k) l) (evalLetExpr acc).
  Proof.
    induction l as [| x xs IH]; intros acc.
    - simpl. reflexivity.
    - simpl. rewrite IH. rewrite evalLetExpr_liftLet. reflexivity.
  Qed.

  Theorem evalLetExpr_fold_left_base : forall l,
    evalLetExpr (fold_left (liftLet comb) l e_syn) =
    fold_left f_sem (map (@evalLetExpr k) l) e_sem.
  Proof.
    intros l.
    rewrite evalLetExpr_fold_left.
    rewrite Heval_e.
    reflexivity.
  Qed.

  Lemma evalLetExpr_fold_right : forall l acc,
    evalLetExpr (fold_right (liftLet comb) acc l) =
    fold_right f_sem (evalLetExpr acc) (map (@evalLetExpr k) l).
  Proof.
    induction l as [| x xs IH]; intros acc.
    - reflexivity.
    - change (fold_right (liftLet comb) acc (x :: xs)) with
        (liftLet comb x (fold_right (liftLet comb) acc xs)).
      rewrite evalLetExpr_liftLet.
      rewrite IH.
      reflexivity.
  Qed.

  Theorem evalLetExpr_merge_fold_pow2 : forall depth (get : nat -> LetExpr type k) offset,
    evalLetExpr (merge_fold_pow2 (liftLet comb) depth get offset) =
    merge_fold_pow2 f_sem depth (fun i => evalLetExpr (get i)) offset.
  Proof.
    induction depth as [| d IH]; intros get offset.
    - reflexivity.
    - change (merge_fold_pow2 (liftLet comb) (S d) get offset) with
        (liftLet comb (merge_fold_pow2 (liftLet comb) d get offset)
                      (merge_fold_pow2 (liftLet comb) d get (offset + 2 ^ d))).
      rewrite evalLetExpr_liftLet.
      rewrite IH.
      rewrite IH.
      reflexivity.
  Qed.

  (* The grand equivalence for LetExpr: evaluating hardware tree = semantic fold_left *)
  Theorem evalLetExpr_merge_fold_pow2_equiv_fold_left : forall depth (get : nat -> LetExpr type k) offset,
    evalLetExpr (merge_fold_pow2 (liftLet comb) depth get offset) =
    fold_left f_sem (map (@evalLetExpr k) (slice depth get offset)) e_sem.
  Proof.
    intros depth get offset.
    rewrite evalLetExpr_merge_fold_pow2.
    rewrite (@merge_fold_pow2_equiv_fold_left _ f_sem e_sem Hassoc Hid_l Hid_r).
    unfold slice.
    rewrite map_map.
    reflexivity.
  Qed.

  (* Bridge theorem: evaluating hardware tree = evaluating syntactic fold_left *)
  Theorem evalLetExpr_merge_fold_pow2_equiv_evalLetExpr_fold_left : forall depth (get : nat -> LetExpr type k) offset,
    evalLetExpr (merge_fold_pow2 (liftLet comb) depth get offset) =
    evalLetExpr (fold_left (liftLet comb) (slice depth get offset) e_syn).
  Proof.
    intros depth get offset.
    rewrite evalLetExpr_merge_fold_pow2_equiv_fold_left.
    rewrite evalLetExpr_fold_left.
    rewrite Heval_e.
    reflexivity.
  Qed.

  Theorem evalLetExpr_merge_fold_pow2_equiv_evalLetExpr_fold_right : forall depth (get : nat -> LetExpr type k) offset,
    evalLetExpr (merge_fold_pow2 (liftLet comb) depth get offset) =
    evalLetExpr (fold_right (liftLet comb) e_syn (slice depth get offset)).
  Proof.
    intros depth get offset.
    rewrite evalLetExpr_merge_fold_pow2.
    rewrite (@merge_fold_pow2_equiv_fold_right _ f_sem e_sem Hassoc Hid_l Hid_r).
    rewrite evalLetExpr_fold_right.
    rewrite Heval_e.
    unfold slice.
    rewrite map_map.
    reflexivity.
  Qed.

  Lemma evalLetExpr_nth : forall l i,
    evalLetExpr (nth i l e_syn) = nth i (map (@evalLetExpr k) l) e_sem.
  Proof.
    induction l as [| x xs IH]; intros i.
    - destruct i; simpl; apply Heval_e.
    - destruct i; simpl.
      + reflexivity.
      + apply IH.
  Qed.

  Theorem evalLetExpr_merge_fold_list : forall l,
    evalLetExpr (merge_fold_list (liftLet comb) e_syn l) =
    merge_fold_list f_sem e_sem (map (@evalLetExpr k) l).
  Proof.
    intros l.
    unfold merge_fold_list.
    rewrite length_map.
    destruct l as [| x [| y ys]].
    - simpl. apply Heval_e.
    - simpl. reflexivity.
    - simpl.
      rewrite evalLetExpr_merge_fold_pow2.
      apply merge_fold_pow2_ext_expr.
      intros i.
      destruct i as [| [| i']]; simpl; [reflexivity | reflexivity | apply evalLetExpr_nth].
  Qed.

  Theorem evalLetExpr_merge_fold_list_equiv_fold_left : forall l,
    evalLetExpr (merge_fold_list (liftLet comb) e_syn l) =
    fold_left f_sem (map (@evalLetExpr k) l) e_sem.
  Proof.
    intros l.
    rewrite evalLetExpr_merge_fold_list.
    apply merge_fold_list_equiv_fold_left; assumption.
  Qed.

  Theorem evalLetExpr_merge_fold_list_equiv_evalLetExpr_fold_left : forall l,
    evalLetExpr (merge_fold_list (liftLet comb) e_syn l) =
    evalLetExpr (fold_left (liftLet comb) l e_syn).
  Proof.
    intros l.
    rewrite evalLetExpr_merge_fold_list_equiv_fold_left.
    rewrite evalLetExpr_fold_left_base.
    reflexivity.
  Qed.

  Theorem evalLetExpr_fold_right_base : forall l,
    evalLetExpr (fold_right (liftLet comb) e_syn l) =
    fold_right f_sem e_sem (map (@evalLetExpr k) l).
  Proof.
    intros l.
    rewrite evalLetExpr_fold_right.
    rewrite Heval_e.
    reflexivity.
  Qed.

  Theorem evalLetExpr_merge_fold_list_equiv_fold_right : forall l,
    evalLetExpr (merge_fold_list (liftLet comb) e_syn l) =
    fold_right f_sem e_sem (map (@evalLetExpr k) l).
  Proof.
    intros l.
    rewrite evalLetExpr_merge_fold_list.
    apply merge_fold_list_equiv_fold_right; assumption.
  Qed.

  Theorem evalLetExpr_merge_fold_list_equiv_evalLetExpr_fold_right : forall l,
    evalLetExpr (merge_fold_list (liftLet comb) e_syn l) =
    evalLetExpr (fold_right (liftLet comb) e_syn l).
  Proof.
    intros l.
    rewrite evalLetExpr_merge_fold_list_equiv_fold_right.
    rewrite evalLetExpr_fold_right_base.
    reflexivity.
  Qed.

End LetExprSemantics.

(* ===========================================================================
 * 5. Tree-based Hardware Array Count Operations
 * =========================================================================== *)

Unset Implicit Arguments.

Section CountArrayOps.

  Definition ClzResType (no : Z) : Kind :=
    STRUCT_TYPE { "all_zeros" :: Bool ; "count" :: Bit no }.

  Definition mkClzRes (no : Z) {ty : Kind -> Type} (az : Expr ty Bool) (cnt : Expr ty (Bit no)) : Expr ty (ClzResType no) :=
    STRUCT { "all_zeros" ::= az ; "count" ::= cnt }.

  Definition clzEmpty (no : Z) {ty : Kind -> Type} : Expr ty (ClzResType no) :=
    mkClzRes no (Const ty Bool true) ($(0) : Expr ty (Bit no)).

  Definition clzComb (no : Z) {ty : Kind -> Type} (a b : ty (ClzResType no)) : LetExpr ty (ClzResType no) :=
    LetE a_az  : Bool   <- ##a`"all_zeros" ;
    LetE a_cnt : Bit no <- ##a`"count" ;
    LetE b_az  : Bool   <- ##b`"all_zeros" ;
    LetE b_cnt : Bit no <- ##b`"count" ;
    LetE out_az  : Bool   <- And [ #a_az ; #b_az ] ;
    LetE out_cnt : Bit no <- ITE #a_az (Add [ #a_cnt ; #b_cnt ]) #a_cnt ;
    RetE (mkClzRes no #out_az #out_cnt).

  Fixpoint makeClzLeaves {ni : nat} (no : Z) {ty : Kind -> Type} (arr : Expr ty (Array ni Bool)) (count : nat) : list (LetExpr ty (ClzResType no)) :=
    match count with
    | 0%nat => []
    | S m =>
        (LetE bitVal : Bool <- readNatToFinType (Const ty Bool false) (ReadArrayConst arr) m ;
         RetE (ITE #bitVal
                   (mkClzRes no (Const ty Bool false) ($(0) : Expr ty (Bit no)))
                   (mkClzRes no (Const ty Bool true)  ($(1) : Expr ty (Bit no)))))
        :: makeClzLeaves no arr m
    end.

  Definition countLeadingZerosArray {ni : nat} {ty : Kind -> Type} (arr: Expr ty (Array ni Bool)) (no : Z): LetExpr ty (Bit no) :=
    LETE res : ClzResType no <- merge_fold_list (liftLet (clzComb no)) (RetE (clzEmpty no)) (makeClzLeaves no arr ni) ;
    LetE cnt : Bit no <- ##res`"count" ;
    RetE #cnt.

  Fixpoint makeCtzLeaves {ni : nat} (no : Z) {ty : Kind -> Type} (arr : Expr ty (Array ni Bool)) (idx count : nat) : list (LetExpr ty (ClzResType no)) :=
    match count with
    | 0%nat => []
    | S m =>
        (LetE bitVal : Bool <- readNatToFinType (Const ty Bool false) (ReadArrayConst arr) idx ;
         RetE (ITE #bitVal
                   (mkClzRes no (Const ty Bool false) ($(0) : Expr ty (Bit no)))
                   (mkClzRes no (Const ty Bool true)  ($(1) : Expr ty (Bit no)))))
        :: makeCtzLeaves no arr (S idx) m
    end.

  Definition countTrailingZerosArray {ni : nat} {ty : Kind -> Type} (arr: Expr ty (Array ni Bool)) (no : Z): LetExpr ty (Bit no) :=
    LETE res : ClzResType no <- merge_fold_list (liftLet (clzComb no)) (RetE (clzEmpty no)) (makeCtzLeaves no arr 0 ni) ;
    LetE cnt : Bit no <- ##res`"count" ;
    RetE #cnt.

  Fixpoint makeCountOnesLeaves {ni : nat} (no : Z) {ty : Kind -> Type} (arr : Expr ty (Array ni Bool)) (idx count : nat) : list (Expr ty (Bit no)) :=
    match count with
    | 0%nat => []
    | S m =>
        let curr := readNatToFinType (Const ty Bool false) (ReadArrayConst arr) idx in
        ITE curr (Const ty (Bit no) Zmod.one) (Const ty (Bit no) Zmod.zero)
        :: makeCountOnesLeaves no arr (S idx) m
    end.

  Definition countOnesArray {ni : nat} {ty : Kind -> Type} (arr: Expr ty (Array ni Bool)) (no : Z): LetExpr ty (Bit no) :=
    RetE (merge_fold_list
            (fun a b => Add [a; b])
            (Const ty (Bit no) Zmod.zero)
            (makeCountOnesLeaves no arr 0 ni)).

End CountArrayOps.

Section CountArrayTheorems.

  Definition clzSem (no : Z) (a b : type (ClzResType no)) : type (ClzResType no) :=
    let a_az := a.(Fst) in
    let a_cnt := a.(Snd).(Fst) in
    let b_az := b.(Fst) in
    let b_cnt := b.(Snd).(Fst) in
    let out_az := (a_az && b_az)%bool in
    let out_cnt := (if a_az then (a_cnt + b_cnt)%Zmod else a_cnt) in
    (out_az ,, (out_cnt ,, tt)).

  Definition clzEmptySem (no : Z) : type (ClzResType no) :=
    (true ,, ((Zmod.zero : bits no) ,, tt)).

  Lemma evalLetExpr_clzComb : forall no (a b : type (ClzResType no)),
    evalLetExpr (clzComb no a b) = clzSem no a b.
  Proof.
    intros no [a_az [a_cnt []]] [b_az [b_cnt []]].
    unfold clzComb, clzSem, mkClzRes.
    cbn [evalLetExpr evalExpr Fst Snd mapDiffTuple readDiffTuple
         readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb finNum
         evalAndBinary fold_left map InvDefault evalFromBit].
    cbv [getFinStruct structList ClzResType getFinStructOption String.eqb Ascii.eqb finNum readDiffTuple nth_pf].
    cbn [Fst Snd].
    rewrite Zmod.add_0_l.
    reflexivity.
  Qed.

  Lemma evalExpr_clzEmpty : forall no,
    evalExpr (clzEmpty no) = clzEmptySem no.
  Proof.
    intros no.
    unfold clzEmpty, clzEmptySem, mkClzRes.
    cbn [evalExpr Fst Snd mapDiffTuple].
    reflexivity.
  Qed.

  Lemma clzSem_assoc : forall no (x y z : type (ClzResType no)),
    clzSem no x (clzSem no y z) = clzSem no (clzSem no x y) z.
  Proof.
    intros no [x_az [x_cnt []]] [y_az [y_cnt []]] [z_az [z_cnt []]].
    unfold clzSem.
    cbn [Fst Snd].
    rewrite andb_assoc.
    destruct x_az, y_az; simpl.
    - rewrite Zmod.add_assoc. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma clzSem_id_l : forall no (x : type (ClzResType no)),
    clzSem no (clzEmptySem no) x = x.
  Proof.
    intros no [x_az [x_cnt []]].
    unfold clzSem, clzEmptySem.
    cbn [Fst Snd].
    rewrite Zmod.add_0_l.
    reflexivity.
  Qed.

  Lemma clzSem_id_r : forall no (x : type (ClzResType no)),
    clzSem no x (clzEmptySem no) = x.
  Proof.
    intros no [x_az [x_cnt []]].
    unfold clzSem, clzEmptySem.
    cbn [Fst Snd].
    rewrite andb_true_r.
    destruct x_az; simpl.
    - rewrite Zmod.add_0_r. reflexivity.
    - reflexivity.
  Qed.

  Fixpoint clzLoopSem (ni : nat) (no : Z) (arr : Expr type (Array ni Bool)) (count : nat) (over : bool) (accum : bits no) : bits no :=
    match count with
    | 0%nat => accum
    | S m =>
        let curr := evalExpr (readNatToFinType (Const type Bool false) (ReadArrayConst arr) m) in
        let cond := (over || curr)%bool in
        let accum_next := (accum + (if cond then Zmod.zero else Zmod.one))%Zmod in
        clzLoopSem ni no arr m cond accum_next
    end.

  Lemma evalLetExpr_countLeadingZerosLoop : forall ni no arr count over accum,
    evalLetExpr (@countLeadingZerosLoop type ni no arr count over accum) =
    clzLoopSem ni no arr count over accum.
  Proof.
    induction count as [| m IH]; intros over accum.
    - simpl. reflexivity.
    - simpl.
      cbn [evalLetExpr evalExpr Fst Snd snd mapDiffTuple fold_left map InvDefault evalFromBit
           readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum evalAndBinary].
      rewrite Zmod.add_0_l.
      rewrite IH.
      reflexivity.
  Qed.

  Definition clzLeafSem (ni : nat) (no : Z) (arr : Expr type (Array ni Bool)) (idx : nat) : type (ClzResType no) :=
    let b := evalExpr (readNatToFinType (Const type Bool false) (ReadArrayConst arr) idx) in
    (negb b ,, ((if b then Zmod.zero else Zmod.one : bits no) ,, tt)).

  Fixpoint clzLeavesFrom (ni : nat) (no : Z) (arr : Expr type (Array ni Bool)) (count : nat) : list (type (ClzResType no)) :=
    match count with
    | 0%nat => []
    | S m => clzLeafSem ni no arr m :: clzLeavesFrom ni no arr m
    end.

  Lemma fold_left_clzSem_clzLoopSem : forall count ni no (arr : Expr type (Array ni Bool)) over accum,
    (fold_left (clzSem no) (clzLeavesFrom ni no arr count) (negb over ,, (accum ,, tt))).(Snd).(Fst) =
    clzLoopSem ni no arr count over accum.
  Proof.
    induction count as [| m IH]; intros ni no arr over accum.
    - simpl. reflexivity.
    - simpl (clzLeavesFrom ni no arr (S m)).
      simpl (fold_left _ (_ :: _)).
      unfold clzSem, clzLeafSem.
      cbn [Fst Snd].
      simpl clzLoopSem.
      destruct over; destruct (evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst arr) m)); simpl.
      + rewrite Zmod.add_0_r. change false with (negb true). apply IH.
      + rewrite Zmod.add_0_r. change false with (negb true). apply IH.
      + change false with (negb true). apply IH.
      + change true with (negb false). apply IH.
  Qed.

  Lemma map_evalLetExpr_makeClzLeaves : forall count ni no (arr : Expr type (Array ni Bool)),
    map (@evalLetExpr (ClzResType no)) (makeClzLeaves no arr count) =
    clzLeavesFrom ni no arr count.
  Proof.
    induction count as [| m IH]; intros ni no arr.
    - reflexivity.
    - simpl.
      f_equal.
      + unfold clzLeafSem, mkClzRes.
        cbn [evalLetExpr evalExpr Fst Snd mapDiffTuple readDiffTuple
             readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb finNum
             evalAndBinary fold_left map InvDefault evalFromBit].
        destruct (evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst arr) m));
          simpl; reflexivity.
      + apply IH.
  Qed.

  Theorem evalLetExpr_countLeadingZerosArray : forall ni no (arr : Expr type (Array ni Bool)),
    evalLetExpr (countLeadingZerosArray arr no) =
    evalLetExpr (@countLeadingZerosLoop type ni no arr ni false Zmod.zero).
  Proof.
    intros ni no arr.
    unfold countLeadingZerosArray.
    cbn [evalLetExpr evalExpr Fst Snd snd mapDiffTuple fold_left map InvDefault evalFromBit
         readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum evalAndBinary].
    assert (Heval_empty: evalLetExpr (RetE (clzEmpty no)) = clzEmptySem no).
    { simpl. apply evalExpr_clzEmpty. }
    assert (Hassoc: forall x y z,
      evalLetExpr (clzComb no x (evalLetExpr (clzComb no y z))) =
      evalLetExpr (clzComb no (evalLetExpr (clzComb no x y)) z)).
    { intros. rewrite !evalLetExpr_clzComb. apply clzSem_assoc. }
    assert (Hid_l: forall x, evalLetExpr (clzComb no (clzEmptySem no) x) = x).
    { intros. rewrite evalLetExpr_clzComb. apply clzSem_id_l. }
    assert (Hid_r: forall x, evalLetExpr (clzComb no x (clzEmptySem no)) = x).
    { intros. rewrite evalLetExpr_clzComb. apply clzSem_id_r. }
    rewrite (@evalLetExpr_merge_fold_list_equiv_fold_left
               (ClzResType no) (clzComb no) (RetE (clzEmpty no)) (clzEmptySem no)
               Heval_empty Hassoc Hid_l Hid_r).
    assert (Hfold: forall l acc, fold_left (f_sem (clzComb no)) l acc = fold_left (clzSem no) l acc).
    { induction l as [| x xs IHl]; intros acc.
      - reflexivity.
      - simpl. unfold f_sem. rewrite evalLetExpr_clzComb. apply IHl. }
    rewrite Hfold.
    rewrite map_evalLetExpr_makeClzLeaves.
    change (clzEmptySem no) with (negb false ,, (Zmod.zero : bits no ,, tt)).
    rewrite fold_left_clzSem_clzLoopSem.
    rewrite evalLetExpr_countLeadingZerosLoop.
    reflexivity.
  Qed.

  Fixpoint ctzLoopSem (ni : nat) (no : Z) (arr : Expr type (Array ni Bool)) (idx count : nat) (over : bool) (accum : bits no) : bits no :=
    match count with
    | 0%nat => accum
    | S m =>
        let curr := evalExpr (readNatToFinType (Const type Bool false) (ReadArrayConst arr) idx) in
        let cond := (over || curr)%bool in
        let accum_next := (accum + (if cond then Zmod.zero else Zmod.one))%Zmod in
        ctzLoopSem ni no arr (S idx) m cond accum_next
    end.

  Lemma evalLetExpr_countTrailingZerosLoop : forall ni no arr count idx over accum,
    evalLetExpr (@countTrailingZerosLoop type ni no arr idx count over accum) =
    ctzLoopSem ni no arr idx count over accum.
  Proof.
    intros ni no arr.
    induction count as [| m IH]; intros idx over accum.
    - simpl. reflexivity.
    - simpl.
      cbn [evalLetExpr evalExpr Fst Snd snd mapDiffTuple fold_left map InvDefault evalFromBit
           readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum evalAndBinary].
      rewrite Zmod.add_0_l.
      rewrite IH.
      reflexivity.
  Qed.

  Fixpoint ctzLeavesFrom (ni : nat) (no : Z) (arr : Expr type (Array ni Bool)) (idx count : nat) : list (type (ClzResType no)) :=
    match count with
    | 0%nat => []
    | S m => clzLeafSem ni no arr idx :: ctzLeavesFrom ni no arr (S idx) m
    end.

  Lemma fold_left_clzSem_ctzLoopSem : forall count idx ni no (arr : Expr type (Array ni Bool)) over accum,
    (fold_left (clzSem no) (ctzLeavesFrom ni no arr idx count) (negb over ,, (accum ,, tt))).(Snd).(Fst) =
    ctzLoopSem ni no arr idx count over accum.
  Proof.
    induction count as [| m IH]; intros idx ni no arr over accum.
    - simpl. reflexivity.
    - simpl (ctzLeavesFrom ni no arr idx (S m)).
      simpl (fold_left _ (_ :: _)).
      unfold clzSem, clzLeafSem.
      cbn [Fst Snd].
      simpl ctzLoopSem.
      destruct over; destruct (evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst arr) idx)); simpl.
      + rewrite Zmod.add_0_r. change false with (negb true). apply IH.
      + rewrite Zmod.add_0_r. change false with (negb true). apply IH.
      + change false with (negb true). apply IH.
      + change true with (negb false). apply IH.
  Qed.

  Lemma map_evalLetExpr_makeCtzLeaves : forall count idx ni no (arr : Expr type (Array ni Bool)),
    map (@evalLetExpr (ClzResType no)) (makeCtzLeaves no arr idx count) =
    ctzLeavesFrom ni no arr idx count.
  Proof.
    induction count as [| m IH]; intros idx ni no arr.
    - reflexivity.
    - simpl.
      f_equal.
      + unfold clzLeafSem, mkClzRes.
        cbn [evalLetExpr evalExpr Fst Snd mapDiffTuple readDiffTuple
             readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb finNum
             evalAndBinary fold_left map InvDefault evalFromBit].
        destruct (evalExpr (readNatToFinType (ConstBool false) (ReadArrayConst arr) idx));
          simpl; reflexivity.
      + apply IH.
  Qed.

  Theorem evalLetExpr_countTrailingZerosArray : forall ni no (arr : Expr type (Array ni Bool)),
    evalLetExpr (countTrailingZerosArray arr no) =
    evalLetExpr (@countTrailingZerosLoop type ni no arr 0 ni false Zmod.zero).
  Proof.
    intros ni no arr.
    unfold countTrailingZerosArray.
    cbn [evalLetExpr evalExpr Fst Snd snd mapDiffTuple fold_left map InvDefault evalFromBit
         readDiffTupleStr getFinStructOption String.eqb Ascii.eqb fst eqb readDiffTuple finNum evalAndBinary].
    assert (Heval_empty: evalLetExpr (RetE (clzEmpty no)) = clzEmptySem no).
    { simpl. apply evalExpr_clzEmpty. }
    assert (Hassoc: forall x y z,
      evalLetExpr (clzComb no x (evalLetExpr (clzComb no y z))) =
      evalLetExpr (clzComb no (evalLetExpr (clzComb no x y)) z)).
    { intros. rewrite !evalLetExpr_clzComb. apply clzSem_assoc. }
    assert (Hid_l: forall x, evalLetExpr (clzComb no (clzEmptySem no) x) = x).
    { intros. rewrite evalLetExpr_clzComb. apply clzSem_id_l. }
    assert (Hid_r: forall x, evalLetExpr (clzComb no x (clzEmptySem no)) = x).
    { intros. rewrite evalLetExpr_clzComb. apply clzSem_id_r. }
    rewrite (@evalLetExpr_merge_fold_list_equiv_fold_left
               (ClzResType no) (clzComb no) (RetE (clzEmpty no)) (clzEmptySem no)
               Heval_empty Hassoc Hid_l Hid_r).
    assert (Hfold: forall l acc, fold_left (f_sem (clzComb no)) l acc = fold_left (clzSem no) l acc).
    { induction l as [| x xs IHl]; intros acc.
      - reflexivity.
      - simpl. unfold f_sem. rewrite evalLetExpr_clzComb. apply IHl. }
    rewrite Hfold.
    rewrite map_evalLetExpr_makeCtzLeaves.
    change (clzEmptySem no) with (negb false ,, (Zmod.zero : bits no ,, tt)).
    rewrite fold_left_clzSem_ctzLoopSem.
    rewrite evalLetExpr_countTrailingZerosLoop.
    reflexivity.
  Qed.

End CountArrayTheorems.

Set Implicit Arguments.

