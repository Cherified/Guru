(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List Bool ZArith Zmod Zmod.Bits.
From Guru Require Import Primitives Library Syntax Combinators Semantics Theorems.

Set Implicit Arguments.
Set Asymmetric Patterns.

(* Helper functions for semantic evaluations and simplifications *)

Fixpoint evalLetPropGen {k} (le: LetExpr type k) (P: type k -> Prop) : Prop :=
  match le with
  | RetE e => P (evalExpr e)
  | SystemE ls cont => evalLetPropGen cont P
  | LetEx s le cont => forall res, res = evalLetExpr le -> evalLetPropGen (cont res) P
  | IfElseE s p t f cont =>
      if evalExpr p then forall res, res = evalLetExpr t -> evalLetPropGen (cont res) P
                    else forall res, res = evalLetExpr f -> evalLetPropGen (cont res) P
  end.

Lemma evalLetPropGen_sound :
  forall {k} (le: LetExpr type k) P,
    evalLetPropGen le P -> P (evalLetExpr le).
Proof.
  fix evalLetPropGen_sound 2.
  intros k le P H.
  destruct le as [e | ls cont | s k' le1 cont | s p k' t f cont].
  - exact H.
  - apply (evalLetPropGen_sound _ cont P H).
  - apply (evalLetPropGen_sound _ (cont (evalLetExpr le1)) P (H (evalLetExpr le1) eq_refl)).
  - simpl in H. simpl.
    destruct (evalExpr p).
    + apply (evalLetPropGen_sound _ (cont (evalLetExpr t)) P (H (evalLetExpr t) eq_refl)).
    + apply (evalLetPropGen_sound _ (cont (evalLetExpr f)) P (H (evalLetExpr f) eq_refl)).
Qed.

Section EvalActionPropGen.
  Variable t: Tree DomainElem.
  Variable env: Env t.

  Fixpoint evalActionPropGen {k} (a: @Action type t k)
    (old: TreeState DomainElemState t)
    (P: TreeState DomainElemState t -> type k -> Prop) : Prop :=
    match a with
    | ReadReg s x cont =>
        evalActionPropGen (cont (castStateReg x (readTreeState t old x.(regPath)))) old P
    | WriteReg x v cont =>
        evalActionPropGen cont (writeTreeState t old x.(regPath) (castStateRegInv x (evalExpr v))) P
    | ReadRqMem x i p cont =>
        let arr := castStateMem x (readTreeState t old x.(memPath)) in
        let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (getDefault _) in
        evalActionPropGen cont (writeTreeState t old x.(memPath) (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) p val))) P
    | ReadRpMem s x p cont =>
        evalActionPropGen (cont (readSameTuple (castStateMem x (readTreeState t old x.(memPath))).(Snd) p)) old P
    | WriteMem x i v cont =>
        let arr := castStateMem x (readTreeState t old x.(memPath)) in
        evalActionPropGen cont (writeTreeState t old x.(memPath) (castStateMemInv x (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd)))) P
    | Send x v cont =>
        let currentTrace := castStateSend x (readTreeState t old x.(sendPath)) in
        evalActionPropGen cont (writeTreeState t old x.(sendPath) (castStateSendInv x (evalExpr v :: currentTrace))) P
    | Recv s x cont =>
        exists recvVal,
        env old x recvVal /\
        let currentTrace := castStateRecv x (readTreeState t old x.(recvPath)) in
        evalActionPropGen (cont recvVal) (writeTreeState t old x.(recvPath) (castStateRecvInv x (recvVal :: currentTrace))) P
    | LetExp s e cont =>
        evalActionPropGen (cont (evalExpr e)) old P
    | LetAction s a' cont =>
        evalActionPropGen a' old (fun midState midRet => evalActionPropGen (cont midRet) midState P)
    | NonDet s k' cont =>
        exists v, evalActionPropGen (cont v) old P
    | IfElse s p t_branch f_branch cont =>
        if evalExpr p
        then evalActionPropGen t_branch old (fun midState midRet => evalActionPropGen (cont midRet) midState P)
        else evalActionPropGen f_branch old (fun midState midRet => evalActionPropGen (cont midRet) midState P)
    | System ls cont =>
        evalActionPropGen cont old P
    | Return e =>
        P old (evalExpr e)
    end.

  Lemma evalActionPropGen_mono:
    forall k (a: @Action type t k) old
      (P1 P2: TreeState DomainElemState t -> type k -> Prop),
      (forall s r, P1 s r -> P2 s r) ->
      evalActionPropGen a old P1 ->
      evalActionPropGen a old P2.
  Proof.
    induction a; simpl; intros.
    - apply H with (P1 := P1); auto.
    - apply IHa with (P1 := P1); auto.
    - apply IHa with (P1 := P1); auto.
    - apply H with (P1 := P1); auto.
    - apply IHa with (P1 := P1); auto.
    - apply IHa with (P1 := P1); auto.
    - destruct H1 as [recvVal [Henv H1]]; exists recvVal; split; [exact Henv | apply H with (P1 := P1); auto].
    - apply H with (P1 := P1); auto.
    - apply IHa with (P1 := fun midState midRet => evalActionPropGen (cont midRet) midState P1); auto.
      intros s1 r1 Hsr1. apply H with (P1 := P1); auto.
    - destruct H1 as [v H1]; exists v; apply H with (P1 := P1); auto.
    - destruct (evalExpr p).
      + apply IHa1 with (P1 := fun midState midRet => evalActionPropGen (cont midRet) midState P1); auto.
        intros s1 r1 Hsr1. apply H with (P1 := P1); auto.
      + apply IHa2 with (P1 := fun midState midRet => evalActionPropGen (cont midRet) midState P1); auto.
        intros s1 r1 Hsr1. apply H with (P1 := P1); auto.
    - apply IHa with (P1 := P1); auto.
    - apply H; auto.
  Qed.

  Theorem InversionActionPropGen:
    forall k (a: @Action type t k) old new ret,
      SemAction env a old new ret ->
      evalActionPropGen a old (fun new' ret' => new' = new /\ ret' = ret).
  Proof.
    intros k a old new ret Hsem.
    induction Hsem; simpl.
    - exact IHHsem.
    - exact IHHsem.
    - exact IHHsem.
    - exact IHHsem.
    - exact IHHsem.
    - exact IHHsem.
    - exists recvVal. split; [exact envPf | exact IHHsem].
    - exact IHHsem.
    - eapply evalActionPropGen_mono; [| exact IHHsem1 ].
      intros s1 r1 [? ?]; subst. exact IHHsem2.
    - exists v. exact IHHsem.
    - destruct (evalExpr p).
      + specialize (H eq_refl).
        eapply evalActionPropGen_mono; [| exact H ].
        intros s1 r1 [? ?]; subst. exact IHHsem.
      + specialize (H0 eq_refl).
        eapply evalActionPropGen_mono; [| exact H0 ].
        intros s1 r1 [? ?]; subst. exact IHHsem.
    - exact IHHsem.
    - subst. split; reflexivity.
  Qed.
End EvalActionPropGen.

(* ===========================================================================
 * Common Guru Theorems:
 * 1. `Kind` Decidable Equality & UIP
 * 2. `SemAction` <-> `evalActionPropGen` Equivalence
 * 3. Subtree State Read / Write & General `liftAction` Theorems
 * 4. `readTreeState` / `writeTreeState` & `readRegsList` / `writeRegsList` Evaluation
 * 5. Deterministic Initialization (`allTreeInitDet`) & Content Equivalence (`TreeContentRel`)
 * =========================================================================== *)

From Stdlib Require Import Lia Eqdep_dec.
From Guru Require Import Composition.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* ---------------------------------------------------------------------------
 * 1. `Kind` Decidable Equality & UIP
 * --------------------------------------------------------------------------- *)

Lemma Kind_eq_dec : forall k1 k2 : Kind, {k1 = k2} + {k1 <> k2}.
Proof.
  intros k1 k2.
  case_eq (Kind_eqb k1 k2); intros Heq; [left | right];
    pose proof (Kind_BoolSpec k1 k2) as Hspec;
    rewrite Heq in Hspec; inversion Hspec; assumption.
Qed.

Lemma Kind_eqb_refl : forall k : Kind, Kind_eqb k k = true.
Proof.
  intros k.
  destruct (Kind_BoolSpec k k) as [_ | Hne]; [reflexivity | exfalso; apply Hne; reflexivity].
Qed.

Lemma Kind_uip_refl : forall (k : Kind) (pf : k = k), pf = eq_refl.
Proof.
  intros k pf.
  apply (UIP_dec Kind_eq_dec).
Qed.

Lemma eq_rect_Kind_refl : forall (k : Kind) (P : Kind -> Type) (v : P k) (pf : k = k),
  eq_rect k P v k pf = v.
Proof.
  intros k P v pf.
  rewrite (Kind_uip_refl k pf).
  reflexivity.
Qed.

Lemma eq_rect_nat_refl : forall (n : nat) (P : nat -> Type) (v : P n) (pf : n = n),
  eq_rect n P v n pf = v.
Proof.
  intros n P v pf.
  rewrite (UIP_dec Nat.eq_dec pf eq_refl).
  reflexivity.
Qed.

Lemma getRegFromElemTypeEq_irrel :
  forall (e : Elem) (pf1 pf2 : Is_true (isRegElem e)),
    getRegFromElemTypeEq e pf1 = getRegFromElemTypeEq e pf2.
Proof.
  intros [r | m | k | k] pf1 pf2; try contradiction; reflexivity.
Qed.

Lemma getMemFromElemTypeEq_irrel :
  forall (e : Elem) (pf1 pf2 : Is_true (isMemElem e)),
    getMemFromElemTypeEq e pf1 = getMemFromElemTypeEq e pf2.
Proof.
  intros [r | m | k | k] pf1 pf2; try contradiction; reflexivity.
Qed.

Lemma getSendFromElemTypeEq_irrel :
  forall (e : Elem) (pf1 pf2 : Is_true (isSendElem e)),
    getSendFromElemTypeEq e pf1 = getSendFromElemTypeEq e pf2.
Proof.
  intros [r | m | k | k] pf1 pf2; try contradiction; reflexivity.
Qed.

Lemma getRecvFromElemTypeEq_irrel :
  forall (e : Elem) (pf1 pf2 : Is_true (isRecvElem e)),
    getRecvFromElemTypeEq e pf1 = getRecvFromElemTypeEq e pf2.
Proof.
  intros [r | m | k | k] pf1 pf2; try contradiction; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
 * 2. Action Semantics (`SemAction`) <-> `evalActionPropGen`
 * --------------------------------------------------------------------------- *)

Lemma evalActionPropGen_toAction :
  forall {t k} {env : Env t} (le : LetExpr type k) s P,
    evalActionPropGen env (@toAction type t k le) s P <-> P s (evalLetExpr le).
Proof.
  intros t k env le.
  induction le; intros s0 P; cbn [toAction evalActionPropGen evalLetExpr].
  - tauto.
  - apply IHle.
  - rewrite IHle. apply H.
  - destruct (evalExpr p); [rewrite IHle1 | rewrite IHle2]; apply H.
Qed.

Lemma evalActionPropGen_ext :
  forall {t : Tree DomainElem} {env : Env t} {k : Kind} (a : @Action type t k)
         (old : TreeState DomainElemState t)
         (P1 P2 : TreeState DomainElemState t -> type k -> Prop),
    (forall s r, P1 s r <-> P2 s r) ->
    (evalActionPropGen env a old P1 <-> evalActionPropGen env a old P2).
Proof.
  intros t env k a old P1 P2 Hiff.
  split; apply evalActionPropGen_mono; intros s r H; apply Hiff; exact H.
Qed.

Lemma evalActionPropGen_env_mono :
  forall {t : Tree DomainElem} (env1 env2 : Env t) {k : Kind} (a : @Action type t k)
         (old : TreeState DomainElemState t)
         (P : TreeState DomainElemState t -> type k -> Prop),
    (forall s x v, env1 s x v -> env2 s x v) ->
    evalActionPropGen env1 a old P ->
    evalActionPropGen env2 a old P.
Proof.
  intros t env1 env2 k a old P Henv.
  revert old P.
  induction a; intros old P Heval; cbn [evalActionPropGen] in Heval |- *.
  - apply H; exact Heval.
  - apply IHa; exact Heval.
  - apply IHa; exact Heval.
  - apply H; exact Heval.
  - apply IHa; exact Heval.
  - apply IHa; exact Heval.
  - destruct Heval as [recvVal [Henv1 Heval]].
    exists recvVal; split; [apply Henv; exact Henv1 | apply H; exact Heval].
  - apply H; exact Heval.
  - eapply evalActionPropGen_mono; [| apply IHa; exact Heval].
    intros s1 r1 Hsr1; apply H; exact Hsr1.
  - destruct Heval as [v Heval]; exists v; apply H; exact Heval.
  - destruct (evalExpr p).
    + eapply evalActionPropGen_mono; [| apply IHa1; exact Heval].
      intros s1 r1 Hsr1; apply H; exact Hsr1.
    + eapply evalActionPropGen_mono; [| apply IHa2; exact Heval].
      intros s1 r1 Hsr1; apply H; exact Hsr1.
  - apply IHa; exact Heval.
  - exact Heval.
Qed.

Lemma evalActionPropGen_env_ext :
  forall {t : Tree DomainElem} (env1 env2 : Env t) {k : Kind} (a : @Action type t k)
         (old : TreeState DomainElemState t)
         (P : TreeState DomainElemState t -> type k -> Prop),
    (forall s x v, env1 s x v <-> env2 s x v) ->
    (evalActionPropGen env1 a old P <-> evalActionPropGen env2 a old P).
Proof.
  intros t env1 env2 k a old P Hiff.
  split; apply evalActionPropGen_env_mono; intros s x v H; apply Hiff; exact H.
Qed.

Lemma evalActionPropGen_to_SemAction :
  forall {t : Tree DomainElem} {env : Env t} {k : Kind} (a : @Action type t k)
         (old : TreeState DomainElemState t)
         (P : TreeState DomainElemState t -> type k -> Prop),
    evalActionPropGen env a old P ->
    exists new ret, SemAction env a old new ret /\ P new ret.
Proof.
  intros t env k a.
  induction a; intros old P Heval; cbn [evalActionPropGen] in Heval.
  - destruct (H _ old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (H _ old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct Heval as [recvVal [Henv Heval]].
    destruct (H recvVal _ P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; [exact Henv | exact Hsem] | exact HP].
  - destruct (H (evalExpr e) old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - destruct (IHa old _ Heval) as [midState [midRet [Hsem1 Heval2]]].
    destruct (H midRet midState P Heval2) as [new [ret [Hsem2 HP]]].
    exists new, ret; split; [econstructor; [exact Hsem1 | exact Hsem2] | exact HP].
  - destruct Heval as [v Heval].
    destruct (H v old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [econstructor; exact Hsem | exact HP].
  - destruct (evalExpr p) eqn:Hp.
    + destruct (IHa1 old _ Heval) as [midState [midRet [Hsem1 Heval2]]].
      destruct (H midRet midState P Heval2) as [new [ret [Hsem2 HP]]].
      exists new, ret; split; [| exact HP].
      eapply SemIfElse with (midState := midState) (midRet := midRet);
        [intros _; exact Hsem1 | intros Hfalse; congruence | exact Hsem2].
    + destruct (IHa2 old _ Heval) as [midState [midRet [Hsem1 Heval2]]].
      destruct (H midRet midState P Heval2) as [new [ret [Hsem2 HP]]].
      exists new, ret; split; [| exact HP].
      eapply SemIfElse with (midState := midState) (midRet := midRet);
        [intros Htrue; congruence | intros _; exact Hsem1 | exact Hsem2].
  - destruct (IHa old P Heval) as [new [ret [Hsem HP]]].
    exists new, ret; split; [constructor; exact Hsem | exact HP].
  - exists old, (evalExpr e); split; [constructor; reflexivity | exact Heval].
Qed.

Theorem SemAction_iff_evalActionPropGen :
  forall {t : Tree DomainElem} {env : Env t} {k : Kind} (a : @Action type t k)
         (old new : TreeState DomainElemState t) (ret : type k),
    SemAction env a old new ret <->
    evalActionPropGen env a old (fun new' ret' => new' = new /\ ret' = ret).
Proof.
  intros t env k a old new ret; split.
  - apply InversionActionPropGen.
  - intros Heval.
    destruct (evalActionPropGen_to_SemAction a old _ Heval) as [new' [ret' [Hsem [Hnew Hret]]]].
    subst; exact Hsem.
Qed.

Lemma SemAction_env_mono :
  forall {t : Tree DomainElem} (env1 env2 : Env t) {k : Kind} (a : @Action type t k)
         (old new : TreeState DomainElemState t) (ret : type k),
    (forall s x v, env1 s x v -> env2 s x v) ->
    SemAction env1 a old new ret ->
    SemAction env2 a old new ret.
Proof.
  intros t env1 env2 k a old new ret Henv Hsem.
  rewrite SemAction_iff_evalActionPropGen in Hsem.
  rewrite SemAction_iff_evalActionPropGen.
  eapply evalActionPropGen_env_mono; eauto.
Qed.

(* ---------------------------------------------------------------------------
 * 3. Subtree State Read / Write & General `liftAction` Theorems
 * --------------------------------------------------------------------------- *)

Fixpoint readSubTreeState_child {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p_child : NodeChildren t), TreeState f t -> TreeState f (getNodeChildren p_child) :=
  match t return forall (p_child : NodeChildren t), TreeState f t -> TreeState f (getNodeChildren p_child) with
  | Leaf _ _ => fun empty => match empty with end
  | Node _ children =>
      (fix loop (ls : list (Tree A)) :
         forall (p_list : NodePathList ls),
           TreeState f (Node "" ls) ->
           TreeState f ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
                           match l return NodePathList l -> Tree A with
                           | nil => fun empty => match empty with end
                           | x :: xs => fun p_sum =>
                               match p_sum with
                               | inl p_x =>
                                   match p_x with
                                   | inl _ => x
                                   | inr p_child => getNodeChildren p_child
                                   end
                               | inr p_xs => loop_node xs p_xs
                               end
                           end) ls p_list) :=
         match ls return
           forall (p_list : NodePathList ls),
             TreeState f (Node "" ls) ->
             TreeState f ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
                             match l return NodePathList l -> Tree A with
                             | nil => fun empty => match empty with end
                             | x :: xs => fun p_sum =>
                                 match p_sum with
                                 | inl p_x =>
                                     match p_x with
                                     | inl _ => x
                                     | inr p_child => getNodeChildren p_child
                                     end
                                 | inr p_xs => loop_node xs p_xs
                                 end
                             end) ls p_list)
         with
         | nil => fun empty => match empty with end
         | x :: xs => fun p_list s =>
             match p_list with
             | inl p_x =>
                 match p_x with
                 | inl _ => s.(Fst)
                 | inr p_child => @readSubTreeState_child A f x p_child s.(Fst)
                 end
             | inr p_xs => loop xs p_xs s.(Snd)
             end
         end) children
  end.

Definition readSubTreeState {A : Type} {f : A -> Type} {t : Tree A}
  (p : NodePath t) (s : TreeState f t) : TreeState f (getNode p) :=
  match p as p_ return TreeState f (getNode p_) with
  | inl _ => s
  | inr p_child => readSubTreeState_child p_child s
  end.

Fixpoint writeSubTreeState_child {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p_child : NodeChildren t),
    TreeState f t -> TreeState f (getNodeChildren p_child) -> TreeState f t :=
  match t return
    forall (p_child : NodeChildren t),
      TreeState f t -> TreeState f (getNodeChildren p_child) -> TreeState f t
  with
  | Leaf _ _ => fun empty => match empty with end
  | Node _ children =>
      (fix loop (ls : list (Tree A)) :
         forall (p_list : NodePathList ls),
           TreeState f (Node "" ls) ->
           TreeState f ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
                           match l return NodePathList l -> Tree A with
                           | nil => fun empty => match empty with end
                           | x :: xs => fun p_sum =>
                               match p_sum with
                               | inl p_x =>
                                   match p_x with
                                   | inl _ => x
                                   | inr p_child => getNodeChildren p_child
                                   end
                               | inr p_xs => loop_node xs p_xs
                               end
                           end) ls p_list) ->
           TreeState f (Node "" ls) :=
         match ls return
           forall (p_list : NodePathList ls),
             TreeState f (Node "" ls) ->
             TreeState f ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
                             match l return NodePathList l -> Tree A with
                             | nil => fun empty => match empty with end
                             | x :: xs => fun p_sum =>
                                 match p_sum with
                                 | inl p_x =>
                                     match p_x with
                                     | inl _ => x
                                     | inr p_child => getNodeChildren p_child
                                     end
                                 | inr p_xs => loop_node xs p_xs
                                 end
                             end) ls p_list) ->
             TreeState f (Node "" ls)
         with
         | nil => fun empty => match empty with end
         | x :: xs => fun p_list s v =>
             match p_list as p_list_ return
               TreeState f (match p_list_ with
                            | inl p_x =>
                                match p_x with
                                | inl _ => x
                                | inr p_child => getNodeChildren p_child
                                end
                            | inr p_xs => _
                            end) ->
               TreeState f (Node "" (x :: xs))
             with
             | inl p_x =>
                 match p_x as p_x_ return
                   TreeState f (match p_x_ with
                                | inl _ => x
                                | inr p_child => getNodeChildren p_child
                                end) ->
                   TreeState f (Node "" (x :: xs))
                 with
                 | inl _ => fun v_x => (v_x ,, s.(Snd))
                 | inr p_child => fun v_child => (@writeSubTreeState_child A f x p_child s.(Fst) v_child ,, s.(Snd))
                 end
             | inr p_xs => fun v_xs => (s.(Fst) ,, loop xs p_xs s.(Snd) v_xs)
             end v
         end) children
  end.

Definition writeSubTreeState {A : Type} {f : A -> Type} {t : Tree A}
  (p : NodePath t) (s : TreeState f t) (v : TreeState f (getNode p)) : TreeState f t :=
  match p as p_ return TreeState f (getNode p_) -> TreeState f t with
  | inl _ => fun v_root => v_root
  | inr p_child => fun v_child => writeSubTreeState_child p_child s v_child
  end v.

Fixpoint readSubTreeState_writeSubTreeState_same {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t) (v : TreeState f (getNode p)),
    readSubTreeState p (writeSubTreeState p s v) = v.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s v.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ exact (@readSubTreeState_writeSubTreeState_same A f c (inr p_c_child) s.(Fst) v).
        -- exact (IHcs p_cs s.(Snd) v).
Qed.

Fixpoint writeSubTreeState_writeSubTreeState_same {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t) (v1 v2 : TreeState f (getNode p)),
    writeSubTreeState p (writeSubTreeState p s v1) v2 = writeSubTreeState p s v2.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s v1 v2.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ f_equal.
              exact (@writeSubTreeState_writeSubTreeState_same A f c (inr p_c_child) s.(Fst) v1 v2).
        -- f_equal.
           exact (IHcs p_cs s.(Snd) v1 v2).
Qed.

Fixpoint writeSubTreeState_readSubTreeState {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t),
    writeSubTreeState p s (readSubTreeState p s) = s.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ exact (f_equal2 (@Build_Prod _ _) (@writeSubTreeState_readSubTreeState A f c (inr p_c_child) s.(Fst)) eq_refl).
        -- exact (f_equal2 (@Build_Prod _ _) eq_refl (IHcs p_cs s.(Snd))).
Qed.

Fixpoint readTreeState_embedLeafIntoPath {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t) (l : LeafPath (getNode p)),
    readTreeState t s (@embedLeafIntoPath _ t p l) =
    eq_rect_r f (readTreeState (getNode p) (readSubTreeState p s) l) (getLeaf_embedLeafIntoPath p l).
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s l.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ change (embedLeafIntoPath_child (p_child:=p_c_child) l) with (embedLeafIntoPath (inr p_c_child) l).
              exact (@readTreeState_embedLeafIntoPath A f c (inr p_c_child) s.(Fst) l).
        -- exact (IHcs p_cs s.(Snd) l).
Qed.

Fixpoint writeTreeState_embedLeafIntoPath {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : NodePath t) (s : TreeState f t) (l : LeafPath (getNode p))
         (v : f (getLeaf (@embedLeafIntoPath _ t p l))),
    writeTreeState t s (@embedLeafIntoPath _ t p l) v =
    writeSubTreeState p s
      (writeTreeState (getNode p) (readSubTreeState p s) l
         (eq_rect (getLeaf (@embedLeafIntoPath _ t p l)) f v (getLeaf l) (getLeaf_embedLeafIntoPath p l))).
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children s l v.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ change (embedLeafIntoPath_child (p_child:=p_c_child) l) with (embedLeafIntoPath (inr p_c_child) l) in *.
              exact (f_equal2 (@Build_Prod _ _) (@writeTreeState_embedLeafIntoPath A f c (inr p_c_child) s.(Fst) l v) eq_refl).
        -- exact (f_equal2 (@Build_Prod _ _) eq_refl (IHcs p_cs s.(Snd) l v)).
Qed.

Lemma evalExpr_eq_rect_Kind :
  forall (k1 k2 : Kind) (pf : k1 = k2) (e : Expr type k1),
    evalExpr (eq_rect k1 (Expr type) e k2 pf) =
    eq_rect k1 type (evalExpr e) k2 pf.
Proof.
  intros k1 k2 pf e; destruct pf; reflexivity.
Qed.

Lemma evalExpr_eq_rect_nat_Bit :
  forall (n1 n2 : nat) (pf : n1 = n2) (e : Expr type (Bit (Z.log2_up (Z.of_nat n1)))),
    evalExpr (eq_rect n1 (fun s => Expr type (Bit (Z.log2_up (Z.of_nat s)))) e n2 pf) =
    eq_rect n1 (fun s => type (Bit (Z.log2_up (Z.of_nat s)))) (evalExpr e) n2 pf.
Proof.
  intros n1 n2 pf e; destruct pf; reflexivity.
Qed.

Lemma Zmod_to_Z_eq_rect_nat :
  forall (n1 n2 : nat) (pf : n1 = n2) (v : type (Bit (Z.log2_up (Z.of_nat n1)))),
    Zmod.to_Z (eq_rect n1 (fun s => type (Bit (Z.log2_up (Z.of_nat s)))) v n2 pf) =
    Zmod.to_Z v.
Proof.
  intros n1 n2 pf v; destruct pf; reflexivity.
Qed.

Lemma cast_reg_read_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : RegPath (getNode p))
         (s : TreeState DomainElemState t),
    cast_reg p x (castStateReg (embedRegPath p x) (readTreeState t s (embedRegPath p x).(regPath))) =
    castStateReg x (readTreeState (getNode p) (readSubTreeState p s) x.(regPath)).
Proof.
  intros t p x s.
  unfold cast_reg, castStateReg, getRegFromPathTypeEq.
  change (embedRegPath p x).(regPath) with (@embedLeafIntoPath _ t p x.(regPath)).
  rewrite readTreeState_embedLeafIntoPath.
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(regPath)).
  generalize (regKind_embed p x).
  generalize (embedRegPath p x).(regPathPf).
  generalize x.(regPathPf).
  generalize (getLeaf_embedLeafIntoPath p x.(regPath)).
  unfold getRegFromPath, getRegFromPathUnsafe, getLeafElem.
  change (embedRegPath p x).(regPath) with (@embedLeafIntoPath _ t p x.(regPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk v; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getRegFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma write_reg_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : RegPath (getNode p))
         (v : Expr type (regKind (getRegFromPath x)))
         (s : TreeState DomainElemState t),
    writeTreeState t s (embedRegPath p x).(regPath)
      (castStateRegInv (embedRegPath p x) (evalExpr (cast_reg_expr p x v))) =
    writeSubTreeState p s
      (writeTreeState (getNode p) (readSubTreeState p s) x.(regPath)
         (castStateRegInv x (evalExpr v))).
Proof.
  intros t p x v s.
  unfold cast_reg_expr.
  rewrite evalExpr_eq_rect_Kind.
  unfold castStateRegInv, getRegFromPathTypeEq.
  change (embedRegPath p x).(regPath) with (@embedLeafIntoPath _ t p x.(regPath)).
  rewrite writeTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize (evalExpr v).
  generalize (regKind_embed p x).
  generalize (embedRegPath p x).(regPathPf).
  generalize x.(regPathPf).
  generalize (getLeaf_embedLeafIntoPath p x.(regPath)).
  unfold getRegFromPath, getRegFromPathUnsafe, getLeafElem.
  change (embedRegPath p x).(regPath) with (@embedLeafIntoPath _ t p x.(regPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk val; cbn [eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getRegFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma read_rq_mem_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : MemPath (getNode p))
         (i : Expr type (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x))))))
         (port : FinType (memPort (getMemFromPath x)))
         (s : TreeState DomainElemState t),
    (let arr := castStateMem (embedMemPath p x) (readTreeState t s (embedMemPath p x).(memPath)) in
     let val := nth (Z.to_nat (Zmod.to_Z (evalExpr (cast_mem_idx p x i)))) arr.(Fst).(tupleElems) (getDefault _) in
     writeTreeState t s (embedMemPath p x).(memPath)
       (castStateMemInv (embedMemPath p x) (arr.(Fst) ,, updSameTuple arr.(Snd) (cast_mem_port p x port) val))) =
    writeSubTreeState p s
      (let arr := castStateMem x (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)) in
       let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (getDefault _) in
       writeTreeState (getNode p) (readSubTreeState p s) x.(memPath)
         (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) port val))).
Proof.
  intros t p x i port s.
  cbv zeta.
  unfold cast_mem_idx, cast_mem_port.
  rewrite evalExpr_eq_rect_nat_Bit, Zmod_to_Z_eq_rect_nat.
  set (idx := Z.to_nat (Zmod.to_Z (evalExpr i))); clearbody idx.
  unfold castStateMem, castStateMemInv, getMemFromPathTypeEq.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  rewrite writeTreeState_embedLeafIntoPath, readTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize port.
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)).
  generalize (memPort_embed p x).
  generalize (embedMemPath p x).(memPathPf).
  generalize x.(memPathPf).
  generalize (getLeaf_embedLeafIntoPath p x.(memPath)).
  unfold getMemFromPath, getMemFromPathUnsafe, getLeafElem.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hport v port0; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_nat_refl.
  rewrite (getMemFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma cast_mem_read_rp_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : MemPath (getNode p))
         (port : FinType (memPort (getMemFromPath x)))
         (s : TreeState DomainElemState t),
    cast_mem p x
      (readSameTuple (castStateMem (embedMemPath p x) (readTreeState t s (embedMemPath p x).(memPath))).(Snd)
         (cast_mem_port p x port)) =
    readSameTuple (castStateMem x (readTreeState (getNode p) (readSubTreeState p s) x.(memPath))).(Snd) port.
Proof.
  intros t p x port s.
  unfold cast_mem, cast_mem_port, castStateMem, getMemFromPathTypeEq.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  rewrite readTreeState_embedLeafIntoPath.
  generalize port.
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)).
  generalize (memKind_embed p x).
  generalize (memPort_embed p x).
  generalize (embedMemPath p x).(memPathPf).
  generalize x.(memPathPf).
  generalize (getLeaf_embedLeafIntoPath p x.(memPath)).
  unfold getMemFromPath, getMemFromPathUnsafe, getLeafElem.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hport Hk v port0; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl, eq_rect_nat_refl.
  rewrite (getMemFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma write_mem_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : MemPath (getNode p))
         (i : Expr type (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x))))))
         (v : Expr type (memKind (getMemFromPath x)))
         (s : TreeState DomainElemState t),
    (let arr := castStateMem (embedMemPath p x) (readTreeState t s (embedMemPath p x).(memPath)) in
     writeTreeState t s (embedMemPath p x).(memPath)
       (castStateMemInv (embedMemPath p x)
          (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr (cast_mem_idx p x i))))
             (evalExpr (cast_mem_expr p x v)) ,, arr.(Snd)))) =
    writeSubTreeState p s
      (let arr := castStateMem x (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)) in
       writeTreeState (getNode p) (readSubTreeState p s) x.(memPath)
         (castStateMemInv x
            (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd)))).
Proof.
  intros t p x i v s.
  cbv zeta.
  unfold cast_mem_idx, cast_mem_expr.
  rewrite evalExpr_eq_rect_nat_Bit, Zmod_to_Z_eq_rect_nat, evalExpr_eq_rect_Kind.
  set (idx := Z.to_nat (Zmod.to_Z (evalExpr i))); clearbody idx.
  unfold castStateMem, castStateMemInv, getMemFromPathTypeEq.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  rewrite writeTreeState_embedLeafIntoPath, readTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize (evalExpr v).
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(memPath)).
  generalize (memKind_embed p x).
  generalize (embedMemPath p x).(memPathPf).
  generalize x.(memPathPf).
  generalize (getLeaf_embedLeafIntoPath p x.(memPath)).
  unfold getMemFromPath, getMemFromPathUnsafe, getLeafElem.
  change (embedMemPath p x).(memPath) with (@embedLeafIntoPath _ t p x.(memPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk st_v val; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getMemFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma send_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : SendPath (getNode p))
         (v : Expr type (getSendKind x))
         (s : TreeState DomainElemState t),
    (let currentTrace := castStateSend (embedSendPath p x) (readTreeState t s (embedSendPath p x).(sendPath)) in
     writeTreeState t s (embedSendPath p x).(sendPath)
       (castStateSendInv (embedSendPath p x) (evalExpr (cast_send_expr p x v) :: currentTrace))) =
    writeSubTreeState p s
      (let currentTrace := castStateSend x (readTreeState (getNode p) (readSubTreeState p s) x.(sendPath)) in
       writeTreeState (getNode p) (readSubTreeState p s) x.(sendPath)
         (castStateSendInv x (evalExpr v :: currentTrace))).
Proof.
  intros t p x v s.
  cbv zeta.
  unfold cast_send_expr.
  rewrite evalExpr_eq_rect_Kind.
  unfold castStateSend, castStateSendInv, getSendFromPathTypeEq.
  change (embedSendPath p x).(sendPath) with (@embedLeafIntoPath _ t p x.(sendPath)).
  rewrite writeTreeState_embedLeafIntoPath, readTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize (evalExpr v).
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(sendPath)).
  generalize (sendKind_embed p x).
  generalize (embedSendPath p x).(sendPathPf).
  generalize x.(sendPathPf).
  generalize (getLeaf_embedLeafIntoPath p x.(sendPath)).
  unfold getSendKind, getSendKindFromPath, getLeafElem.
  change (embedSendPath p x).(sendPath) with (@embedLeafIntoPath _ t p x.(sendPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk st_v val; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getSendFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Lemma recv_write_embed :
  forall {t : Tree DomainElem} (p : NodePath t) (x : RecvPath (getNode p))
         (recvVal : type (getRecvKind (embedRecvPath p x)))
         (s : TreeState DomainElemState t),
    (let currentTrace := castStateRecv (embedRecvPath p x) (readTreeState t s (embedRecvPath p x).(recvPath)) in
     writeTreeState t s (embedRecvPath p x).(recvPath)
       (castStateRecvInv (embedRecvPath p x) (recvVal :: currentTrace))) =
    writeSubTreeState p s
      (let currentTrace := castStateRecv x (readTreeState (getNode p) (readSubTreeState p s) x.(recvPath)) in
       writeTreeState (getNode p) (readSubTreeState p s) x.(recvPath)
         (castStateRecvInv x (cast_recv p x recvVal :: currentTrace))).
Proof.
  intros t p x recvVal s.
  cbv zeta.
  unfold cast_recv, castStateRecv, castStateRecvInv, getRecvFromPathTypeEq.
  change (embedRecvPath p x).(recvPath) with (@embedLeafIntoPath _ t p x.(recvPath)).
  rewrite writeTreeState_embedLeafIntoPath, readTreeState_embedLeafIntoPath.
  f_equal; f_equal.
  generalize recvVal.
  generalize (readTreeState (getNode p) (readSubTreeState p s) x.(recvPath)).
  generalize (recvKind_embed p x).
  generalize (embedRecvPath p x).(recvPathPf).
  generalize x.(recvPathPf).
  generalize (getLeaf_embedLeafIntoPath p x.(recvPath)).
  unfold getRecvKind, getRecvKindFromPath, getLeafElem.
  change (embedRecvPath p x).(recvPath) with (@embedLeafIntoPath _ t p x.(recvPath)).
  intros Hleaf; destruct Hleaf; intros pf2 pf1 Hk st_v rv; cbn [eq_rect_r eq_rect eq_sym].
  rewrite eq_rect_Kind_refl.
  rewrite (getRecvFromElemTypeEq_irrel _ pf1 pf2).
  reflexivity.
Qed.

Definition cast_recv_inv {t : Tree DomainElem} (p : NodePath t)
  (x : RecvPath (getNode p))
  (v : type (getRecvKind x)) : type (getRecvKind (embedRecvPath p x)) :=
  eq_rect (getRecvKind x) type v (getRecvKind (embedRecvPath p x)) (eq_sym (recvKind_embed p x)).

Definition subEnv {t : Tree DomainElem} (p : NodePath t)
  (env : Env t) (s : TreeState DomainElemState t) : Env (getNode p) :=
  fun sub x v => env (writeSubTreeState p s sub) (embedRecvPath p x) (cast_recv_inv p x v).

Lemma cast_recv_cast_recv_inv :
  forall {t : Tree DomainElem} (p : NodePath t) (x : RecvPath (getNode p))
         (v : type (getRecvKind x)),
    cast_recv p x (cast_recv_inv p x v) = v.
Proof.
  intros t p x v.
  unfold cast_recv, cast_recv_inv.
  generalize (recvKind_embed p x) v; intros Hk rv; destruct Hk; reflexivity.
Qed.

Lemma cast_recv_inv_cast_recv :
  forall {t : Tree DomainElem} (p : NodePath t) (x : RecvPath (getNode p))
         (v : type (getRecvKind (embedRecvPath p x))),
    cast_recv_inv p x (cast_recv p x v) = v.
Proof.
  intros t p x v.
  unfold cast_recv, cast_recv_inv.
  generalize (recvKind_embed p x) v; intros Hk rv; destruct Hk; reflexivity.
Qed.

Lemma evalActionPropGen_subEnv_writeSubTreeState :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         {env : Env t} (a : @Action type (getNode p) k)
         (s : TreeState DomainElemState t)
         (sub1 sub2 : TreeState DomainElemState (getNode p))
         (P : TreeState DomainElemState (getNode p) -> type k -> Prop),
    evalActionPropGen (subEnv p env (writeSubTreeState p s sub1)) a sub2 P <->
    evalActionPropGen (subEnv p env s) a sub2 P.
Proof.
  intros t p k env a s sub1 sub2 P.
  apply evalActionPropGen_env_ext; intros sub x v.
  unfold subEnv.
  rewrite writeSubTreeState_writeSubTreeState_same.
  reflexivity.
Qed.

Theorem evalActionPropGen_liftAction :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         {env : Env t} (a : @Action type (getNode p) k)
         (s : TreeState DomainElemState t)
         (P : TreeState DomainElemState t -> type k -> Prop),
    evalActionPropGen env (@liftAction type t p k a) s P <->
    evalActionPropGen (subEnv p env s) a (readSubTreeState p s) (fun sub' r => P (writeSubTreeState p s sub') r).
Proof.
  intros t p k env a.
  induction a; intros s0 P; cbn [liftAction evalActionPropGen].
  - rewrite cast_reg_read_embed.
    apply H.
  - rewrite write_reg_embed, IHa, readSubTreeState_writeSubTreeState_same.
    rewrite evalActionPropGen_subEnv_writeSubTreeState.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - rewrite read_rq_mem_embed, IHa, readSubTreeState_writeSubTreeState_same.
    rewrite evalActionPropGen_subEnv_writeSubTreeState.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - rewrite cast_mem_read_rp_embed.
    apply H.
  - rewrite write_mem_embed, IHa, readSubTreeState_writeSubTreeState_same.
    rewrite evalActionPropGen_subEnv_writeSubTreeState.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - rewrite send_embed, IHa, readSubTreeState_writeSubTreeState_same.
    rewrite evalActionPropGen_subEnv_writeSubTreeState.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - split.
    + intros [recvVal [Henv Hrv]].
      rewrite recv_write_embed, H, readSubTreeState_writeSubTreeState_same in Hrv.
      rewrite evalActionPropGen_subEnv_writeSubTreeState in Hrv.
      exists (cast_recv p x recvVal).
      split.
      * unfold subEnv.
        rewrite writeSubTreeState_readSubTreeState, cast_recv_inv_cast_recv.
        exact Henv.
      * revert Hrv; apply evalActionPropGen_mono.
        intros sub' r Hsub'; rewrite writeSubTreeState_writeSubTreeState_same in Hsub'; exact Hsub'.
    + intros [recvVal2 [Henv2 Hrv2]].
      exists (cast_recv_inv p x recvVal2).
      split.
      * unfold subEnv in Henv2.
        rewrite writeSubTreeState_readSubTreeState in Henv2.
        exact Henv2.
      * rewrite recv_write_embed, H, readSubTreeState_writeSubTreeState_same.
        rewrite evalActionPropGen_subEnv_writeSubTreeState.
        rewrite cast_recv_cast_recv_inv.
        revert Hrv2; apply evalActionPropGen_mono.
        intros sub' r Hsub'; rewrite writeSubTreeState_writeSubTreeState_same; exact Hsub'.
  - apply H.
  - rewrite IHa.
    apply evalActionPropGen_ext; intros sub_mid midRet.
    rewrite H, readSubTreeState_writeSubTreeState_same.
    rewrite evalActionPropGen_subEnv_writeSubTreeState.
    apply evalActionPropGen_ext; intros sub' r.
    rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - split; intros [v Hv]; exists v; apply H; exact Hv.
  - destruct (evalExpr p0).
    + rewrite IHa1.
      apply evalActionPropGen_ext; intros sub_mid midRet.
      rewrite H, readSubTreeState_writeSubTreeState_same.
      rewrite evalActionPropGen_subEnv_writeSubTreeState.
      apply evalActionPropGen_ext; intros sub' r.
      rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
    + rewrite IHa2.
      apply evalActionPropGen_ext; intros sub_mid midRet.
      rewrite H, readSubTreeState_writeSubTreeState_same.
      rewrite evalActionPropGen_subEnv_writeSubTreeState.
      apply evalActionPropGen_ext; intros sub' r.
      rewrite writeSubTreeState_writeSubTreeState_same; reflexivity.
  - apply IHa.
  - rewrite writeSubTreeState_readSubTreeState; reflexivity.
Qed.

Lemma evalActionPropGen_liftAction_child0Path :
  forall {name x xs k} {env : Env (Node name (x :: xs))} (a : @Action type x k) sx sxs P,
    evalActionPropGen env (@liftAction type (Node name (x :: xs)) child0Path k a) (sx ,, sxs) P <->
    evalActionPropGen (subEnv child0Path env (sx ,, sxs)) a sx (fun sx' r => P (sx' ,, sxs) r).
Proof.
  intros name x xs k env a sx sxs P.
  exact (evalActionPropGen_liftAction child0Path a (sx ,, sxs) P).
Qed.

Lemma evalActionPropGen_liftAction_child1Path :
  forall {name c0 c1 cs k} {env : Env (Node name (c0 :: c1 :: cs))} (a : @Action type c1 k) sc0 sc1 scs P,
    evalActionPropGen env (@liftAction type (Node name (c0 :: c1 :: cs)) child1Path k a) (sc0 ,, (sc1 ,, scs)) P <->
    evalActionPropGen (subEnv child1Path env (sc0 ,, (sc1 ,, scs))) a sc1 (fun sc1' r => P (sc0 ,, (sc1' ,, scs)) r).
Proof.
  intros name c0 c1 cs k env a sc0 sc1 scs P.
  exact (evalActionPropGen_liftAction child1Path a (sc0 ,, (sc1 ,, scs)) P).
Qed.

Theorem SemAction_liftAction_iff :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         {env : Env t} (a : @Action type (getNode p) k)
         (old new : TreeState DomainElemState t) (ret : type k),
    SemAction env (@liftAction type t p k a) old new ret <->
    exists sub',
      SemAction (subEnv p env old) a (readSubTreeState p old) sub' ret /\
      new = writeSubTreeState p old sub'.
Proof.
  intros t p k env a old new ret.
  rewrite SemAction_iff_evalActionPropGen, evalActionPropGen_liftAction.
  split.
  - intros Heval.
    destruct (evalActionPropGen_to_SemAction a (readSubTreeState p old) _ Heval)
      as [sub' [ret' [Hsem [Hnew Hret]]]].
    subst ret'.
    exists sub'; split; [exact Hsem | symmetry; exact Hnew].
  - intros [sub' [Hsem Hnew]].
    subst new.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    eapply evalActionPropGen_mono; [| exact Hsem].
    intros sub'' r [Hsub Hr]; subst; split; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
 * 4. `readRegsList` / `writeRegsList` Evaluation & Register-Bank Lemmas
 * --------------------------------------------------------------------------- *)

Definition readRegOfKind {t : Tree DomainElem} {k : Kind}
  (rk : RegOfKind (t:=t) k) (s : TreeState DomainElemState t) : type k :=
  eq_rect (regKind (getRegFromPath rk.(rk_path))) type
    (castStateReg rk.(rk_path) (readTreeState t s rk.(rk_path).(regPath)))
    k (Kind_eqb_eq _ _ rk.(rk_pf)).

Definition writeRegOfKind {t : Tree DomainElem} {k : Kind}
  (rk : RegOfKind (t:=t) k) (val : type k)
  (s : TreeState DomainElemState t) : TreeState DomainElemState t :=
  let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
  writeTreeState t s rk.(rk_path).(regPath)
    (castStateRegInv rk.(rk_path) (eq_rect k type val _ (eq_sym pf_eq))).

Fixpoint evalWriteRegsListHelper (curr : nat) {k sz t}
  (paths : list (RegOfKind (t:=t) k)) (idx : bits sz) (newVal : type k)
  (s : TreeState DomainElemState t) : TreeState DomainElemState t :=
  match paths with
  | nil => s
  | rk :: rest =>
      let s' := if @isEq (Bit sz) idx (Zmod.of_Z _ (Z.of_nat curr))
                then writeRegOfKind rk newVal s
                else s in
      evalWriteRegsListHelper (S curr) rest idx newVal s'
  end.

Definition evalWriteRegsList {k sz t}
  (paths : list (RegOfKind (t:=t) k)) (idx : bits sz) (newVal : type k)
  (s : TreeState DomainElemState t) : TreeState DomainElemState t :=
  evalWriteRegsListHelper 0 paths idx newVal s.

Fixpoint evalReadRegsListHelper (curr : nat) {k} (acc : list (type k)) {sz t}
  (paths : list (RegOfKind (t:=t) k)) (idx : bits sz)
  (s : TreeState DomainElemState t) : type k :=
  match paths with
  | nil => fold_left (@evalOrBinary k) acc (getDefault k)
  | rk :: rest =>
      let v := readRegOfKind rk s in
      let iteVal := if @isEq (Bit sz) idx (Zmod.of_Z _ (Z.of_nat curr)) then v else getDefault k in
      evalReadRegsListHelper (S curr) (iteVal :: acc) rest idx s
  end.

Definition evalReadRegsList {k sz t}
  (paths : list (RegOfKind (t:=t) k)) (idx : bits sz)
  (s : TreeState DomainElemState t) : type k :=
  evalReadRegsListHelper 0 nil paths idx s.

Lemma evalActionPropGen_writeRegsListHelper :
  forall {k sz t} {env : Env t} (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (idx : Expr type (Bit sz)) (newVal : Expr type k)
         (s : TreeState DomainElemState t) P,
    evalActionPropGen env (@writeRegsListHelper type curr k sz t paths idx newVal) s P <->
    P (evalWriteRegsListHelper curr paths (evalExpr idx) (evalExpr newVal) s) Zmod.zero.
Proof.
  intros k sz t env paths.
  induction paths as [| rk rest IH]; intros curr idx newVal s P;
    cbn [writeRegsListHelper evalWriteRegsListHelper evalActionPropGen evalExpr].
  - reflexivity.
  - unfold writeRegOfKind.
    rewrite evalExpr_eq_rect_Kind.
    destruct (@isEq (Bit sz) (evalExpr idx) (Zmod.of_Z (2 ^ sz) (Z.of_nat curr)));
      cbn [evalActionPropGen]; apply IH.
Qed.

Theorem evalActionPropGen_writeRegsList :
  forall {k sz t} {env : Env t} (paths : list (RegOfKind (t:=t) k))
         (idx : Expr type (Bit sz)) (newVal : Expr type k)
         (s : TreeState DomainElemState t) P,
    evalActionPropGen env (@writeRegsList type k sz t paths idx newVal) s P <->
    P (evalWriteRegsList paths (evalExpr idx) (evalExpr newVal) s) Zmod.zero.
Proof.
  intros k sz t env paths idx newVal s P.
  apply evalActionPropGen_writeRegsListHelper.
Qed.

Lemma evalActionPropGen_readRegsListHelper :
  forall {k sz t} {env : Env t} (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (acc : list (Expr type k)) (idx : Expr type (Bit sz))
         (s : TreeState DomainElemState t) P,
    evalActionPropGen env (@readRegsListHelper type curr k acc sz t paths idx) s P <->
    P s (evalReadRegsListHelper curr (map (@evalExpr k) acc) paths (evalExpr idx) s).
Proof.
  intros k sz t env paths.
  induction paths as [| rk rest IH]; intros curr acc idx s P;
    cbn [readRegsListHelper evalReadRegsListHelper evalActionPropGen evalExpr].
  - reflexivity.
  - rewrite IH.
    unfold readRegOfKind.
    cbn [map evalExpr].
    reflexivity.
Qed.

Theorem evalActionPropGen_readRegsList :
  forall {k sz t} {env : Env t} (paths : list (RegOfKind (t:=t) k))
         (idx : Expr type (Bit sz))
         (s : TreeState DomainElemState t) P,
    evalActionPropGen env (@readRegsList type k sz t paths idx) s P <->
    P s (evalReadRegsList paths (evalExpr idx) s).
Proof.
  intros k sz t env paths idx s P.
  exact (@evalActionPropGen_readRegsListHelper k sz t env paths 0 nil idx s P).
Qed.

Lemma readRegOfKind_embed :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         (rk : RegOfKind (t := getNode p) k)
         (s : TreeState DomainElemState t),
    readRegOfKind (embedRegOfKind p rk) s = readRegOfKind rk (readSubTreeState p s).
Proof.
  intros t p k rk s.
  unfold readRegOfKind.
  pose proof (cast_reg_read_embed p rk.(rk_path) s) as Hcast.
  unfold cast_reg in Hcast.
  rewrite <- Hcast.
  change (embedRegOfKind p rk).(rk_path) with (embedRegPath p rk.(rk_path)).
  generalize (castStateReg (embedRegPath p rk.(rk_path))
                (readTreeState t s (embedRegPath p rk.(rk_path)).(regPath))).
  generalize (Kind_eqb_eq (regKind (getRegFromPath (embedRegPath p rk.(rk_path)))) k (embedRegOfKind p rk).(rk_pf)).
  generalize (Kind_eqb_eq (regKind (getRegFromPath rk.(rk_path))) k rk.(rk_pf)).
  generalize (regKind_embed p rk.(rk_path)).
  generalize (regKind (getRegFromPath rk.(rk_path))).
  generalize (regKind (getRegFromPath (embedRegPath p rk.(rk_path)))).
  intros k1 k2 Hemb Hk2 Hk1 v.
  destruct Hemb; destruct Hk2; cbn [eq_rect].
  rewrite eq_rect_Kind_refl; reflexivity.
Qed.

Lemma writeRegOfKind_embed :
  forall {t : Tree DomainElem} (p : NodePath t) {k : Kind}
         (rk : RegOfKind (t := getNode p) k) (val : type k)
         (s : TreeState DomainElemState t),
    writeRegOfKind (embedRegOfKind p rk) val s =
    writeSubTreeState p s (writeRegOfKind rk val (readSubTreeState p s)).
Proof.
  intros t p k rk val s.
  unfold writeRegOfKind.
  change (embedRegOfKind p rk).(rk_path) with (embedRegPath p rk.(rk_path)).
  set (w := eq_rect k type val (regKind (getRegFromPath rk.(rk_path)))
              (eq_sym (Kind_eqb_eq (regKind (getRegFromPath rk.(rk_path))) k rk.(rk_pf)))).
  pose proof (write_reg_embed p rk.(rk_path) (Const type _ w) s) as Hwr.
  cbn [evalExpr] in Hwr.
  rewrite <- Hwr.
  f_equal; f_equal.
  unfold cast_reg_expr; rewrite evalExpr_eq_rect_Kind; cbn [evalExpr].
  subst w.
  generalize (Kind_eqb_eq (regKind (getRegFromPath (embedRegPath p rk.(rk_path)))) k (embedRegOfKind p rk).(rk_pf)).
  generalize (Kind_eqb_eq (regKind (getRegFromPath rk.(rk_path))) k rk.(rk_pf)).
  generalize (regKind_embed p rk.(rk_path)).
  generalize (regKind (getRegFromPath rk.(rk_path))).
  generalize (regKind (getRegFromPath (embedRegPath p rk.(rk_path)))).
  intros k1 k2 Hemb Hk2 Hk1.
  destruct Hemb; destruct Hk2; cbn [eq_rect eq_sym].
  rewrite eq_rect_Kind_refl; reflexivity.
Qed.

Lemma evalWriteRegsListHelper_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k sz}
         (paths : list (RegOfKind (t := getNode p) k)) (curr : nat)
         (idx : bits sz) (val : type k) (s : TreeState DomainElemState t),
    evalWriteRegsListHelper curr (map (embedRegOfKind p) paths) idx val s =
    writeSubTreeState p s (evalWriteRegsListHelper curr paths idx val (readSubTreeState p s)).
Proof.
  intros t p k sz paths.
  induction paths as [| rk rest IH]; intros curr idx val s; cbn [map evalWriteRegsListHelper].
  - symmetry; apply writeSubTreeState_readSubTreeState.
  - destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + rewrite writeRegOfKind_embed, IH, readSubTreeState_writeSubTreeState_same, writeSubTreeState_writeSubTreeState_same.
      reflexivity.
    + apply IH.
Qed.

Theorem evalWriteRegsList_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k sz}
         (paths : list (RegOfKind (t := getNode p) k))
         (idx : bits sz) (val : type k) (s : TreeState DomainElemState t),
    evalWriteRegsList (map (embedRegOfKind p) paths) idx val s =
    writeSubTreeState p s (evalWriteRegsList paths idx val (readSubTreeState p s)).
Proof.
  intros t p k sz paths idx val s.
  apply evalWriteRegsListHelper_map_embedRegOfKind.
Qed.

Lemma evalReadRegsListHelper_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k sz}
         (paths : list (RegOfKind (t := getNode p) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz) (s : TreeState DomainElemState t),
    evalReadRegsListHelper curr acc (map (embedRegOfKind p) paths) idx s =
    evalReadRegsListHelper curr acc paths idx (readSubTreeState p s).
Proof.
  intros t p k sz paths.
  induction paths as [| rk rest IH]; intros curr acc idx s; cbn [map evalReadRegsListHelper].
  - reflexivity.
  - rewrite readRegOfKind_embed; apply IH.
Qed.

Theorem evalReadRegsList_map_embedRegOfKind :
  forall {t : Tree DomainElem} (p : NodePath t) {k sz}
         (paths : list (RegOfKind (t := getNode p) k))
         (idx : bits sz) (s : TreeState DomainElemState t),
    evalReadRegsList (map (embedRegOfKind p) paths) idx s =
    evalReadRegsList paths idx (readSubTreeState p s).
Proof.
  intros t p k sz paths idx s.
  apply evalReadRegsListHelper_map_embedRegOfKind.
Qed.

Fixpoint readTreeState_writeTreeState_same {A : Type} {f : A -> Type} {t : Tree A} :
  forall (s : TreeState f t) (p : LeafPath t) (v : f (getLeaf p)),
    readTreeState t (writeTreeState t s p v) p = v.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - reflexivity.
  - revert s p v.
    induction children as [| c cs IHcs]; simpl; intros.
    + destruct p.
    + destruct p as [p_c | p_cs]; simpl.
      * exact (@readTreeState_writeTreeState_same A f c s.(Fst) p_c v).
      * exact (IHcs s.(Snd) p_cs v).
Qed.

Fixpoint readTreeState_writeTreeState_other {A : Type} {f : A -> Type} {t : Tree A} :
  forall (s : TreeState f t) (p1 p2 : LeafPath t) (v : f (getLeaf p2)),
    p1 <> p2 ->
    readTreeState t (writeTreeState t s p2 v) p1 = readTreeState t s p1.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - exfalso; apply H; destruct p1, p2; reflexivity.
  - revert s p1 p2 v H.
    induction children as [| c cs IHcs]; simpl; intros.
    + destruct p1.
    + destruct p1 as [p1_c | p1_cs], p2 as [p2_c | p2_cs]; simpl; try reflexivity.
      * apply (@readTreeState_writeTreeState_other A f c s.(Fst) p1_c p2_c v).
        intro Heq; apply H; subst; reflexivity.
      * apply (IHcs s.(Snd) p1_cs p2_cs v).
        intro Heq; apply H; subst; reflexivity.
Qed.

Fixpoint writeTreeState_writeTreeState_same {A : Type} {f : A -> Type} {t : Tree A} :
  forall (s : TreeState f t) (p : LeafPath t) (v1 v2 : f (getLeaf p)),
    writeTreeState t (writeTreeState t s p v1) p v2 = writeTreeState t s p v2.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - reflexivity.
  - revert s p v1 v2.
    induction children as [| c cs IHcs]; simpl; intros.
    + destruct p.
    + destruct p as [p_c | p_cs]; simpl; f_equal.
      * exact (@writeTreeState_writeTreeState_same A f c s.(Fst) p_c v1 v2).
      * exact (IHcs s.(Snd) p_cs v1 v2).
Qed.

Fixpoint writeTreeState_writeTreeState_comm {A : Type} {f : A -> Type} {t : Tree A} :
  forall (s : TreeState f t) (p1 p2 : LeafPath t) (v1 : f (getLeaf p1)) (v2 : f (getLeaf p2)),
    p1 <> p2 ->
    writeTreeState t (writeTreeState t s p1 v1) p2 v2 =
    writeTreeState t (writeTreeState t s p2 v2) p1 v1.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - exfalso; apply H; destruct p1, p2; reflexivity.
  - revert s p1 p2 v1 v2 H.
    induction children as [| c cs IHcs]; simpl; intros.
    + destruct p1.
    + destruct p1 as [p1_c | p1_cs], p2 as [p2_c | p2_cs]; simpl; try reflexivity.
      * f_equal; apply (@writeTreeState_writeTreeState_comm A f c s.(Fst) p1_c p2_c v1 v2).
        intro Heq; apply H; subst; reflexivity.
      * f_equal; apply (IHcs s.(Snd) p1_cs p2_cs v1 v2).
        intro Heq; apply H; subst; reflexivity.
Qed.

Lemma castStateReg_castStateRegInv :
  forall {t : Tree DomainElem} (x : RegPath t) (v : type (regKind (getRegFromPath x))),
    castStateReg x (castStateRegInv x v) = v.
Proof.
  intros t x v.
  unfold castStateReg, castStateRegInv.
  generalize (getRegFromPathTypeEq x) v.
  intros H v0; destruct H; reflexivity.
Qed.

Lemma readRegOfKind_writeRegOfKind_same :
  forall {t : Tree DomainElem} {k : Kind} (rk : RegOfKind (t:=t) k)
         (v : type k) (s : TreeState DomainElemState t),
    readRegOfKind rk (writeRegOfKind rk v s) = v.
Proof.
  intros t k rk v s.
  unfold readRegOfKind, writeRegOfKind.
  rewrite readTreeState_writeTreeState_same, castStateReg_castStateRegInv.
  generalize (Kind_eqb_eq (regKind (getRegFromPath rk.(rk_path))) k rk.(rk_pf)).
  generalize (regKind (getRegFromPath rk.(rk_path))).
  intros k0 Hk; destruct Hk; reflexivity.
Qed.

Lemma readRegOfKind_writeRegOfKind_other :
  forall {t : Tree DomainElem} {k1 k2 : Kind}
         (rk1 : RegOfKind (t:=t) k1) (rk2 : RegOfKind (t:=t) k2)
         (v : type k2) (s : TreeState DomainElemState t),
    rk1.(rk_path).(regPath) <> rk2.(rk_path).(regPath) ->
    readRegOfKind rk1 (writeRegOfKind rk2 v s) = readRegOfKind rk1 s.
Proof.
  intros t k1 k2 rk1 rk2 v s Hneq.
  unfold readRegOfKind, writeRegOfKind.
  rewrite (readTreeState_writeTreeState_other s rk1.(rk_path).(regPath) rk2.(rk_path).(regPath) _ Hneq).
  reflexivity.
Qed.

Lemma writeRegOfKind_writeRegOfKind_same :
  forall {t : Tree DomainElem} {k : Kind} (rk : RegOfKind (t:=t) k)
         (v1 v2 : type k) (s : TreeState DomainElemState t),
    writeRegOfKind rk v2 (writeRegOfKind rk v1 s) = writeRegOfKind rk v2 s.
Proof.
  intros t k rk v1 v2 s.
  unfold writeRegOfKind.
  apply writeTreeState_writeTreeState_same.
Qed.

Lemma writeRegOfKind_writeRegOfKind_comm :
  forall {t : Tree DomainElem} {k1 k2 : Kind}
         (rk1 : RegOfKind (t:=t) k1) (rk2 : RegOfKind (t:=t) k2)
         (v1 : type k1) (v2 : type k2) (s : TreeState DomainElemState t),
    rk1.(rk_path).(regPath) <> rk2.(rk_path).(regPath) ->
    writeRegOfKind rk2 v2 (writeRegOfKind rk1 v1 s) =
    writeRegOfKind rk1 v1 (writeRegOfKind rk2 v2 s).
Proof.
  intros t k1 k2 rk1 rk2 v1 v2 s Hneq.
  unfold writeRegOfKind.
  apply writeTreeState_writeTreeState_comm; exact Hneq.
Qed.

Lemma Zmod_or_0_r : forall w (x : bits w),
  Zmod.or x Zmod.zero = x.
Proof.
  intros w x; apply Zmod.unsigned_inj; rewrite bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_r; reflexivity.
Qed.

Lemma evalBinaryArray_or_default_r :
  forall (k : Kind) (IHk : forall x : type k, evalOrBinary x (getDefault k) = x)
         (n : nat) (elems : list (type k)) (pf1 : Is_true (Nat.eqb (length elems) n))
         (pf2 : Is_true (Nat.eqb (length (repeat (getDefault k) n)) n)),
    evalBinaryArray (@evalOrBinary k)
      (@Build_SameTuple (type k) n elems pf1)
      (@Build_SameTuple (type k) n (repeat (getDefault k) n) pf2) =
    @Build_SameTuple (type k) n elems pf1.
Proof.
  intros k IHk.
  induction n as [| m IHm]; intros elems pf1 pf2.
  - destruct elems; [| contradiction].
    destruct pf1; reflexivity.
  - destruct elems as [| x xs]; [contradiction |].
    cbn -[evalOrBinary getDefault].
    rewrite IHk, IHm.
    reflexivity.
Qed.

Theorem evalOrBinary_getDefault_r :
  forall (k : Kind) (x : type k),
    evalOrBinary x (getDefault k) = x.
Proof.
  induction k using KindCustomInd; intros x.
  - apply orb_false_r.
  - apply Zmod_or_0_r.
  - induction ls as [| [fname fk] xs IHxs].
    + destruct x; reflexivity.
    + destruct X as [Hx Hxs]; destruct x as [xf xs_val].
      cbn [evalOrBinary evalBinary KindCustomInd getDefault DiffTupleDefault evalBinaryStruct Fst Snd].
      f_equal; [apply Hx | apply (IHxs Hxs)].
  - destruct x as [elems pf1].
    unfold evalOrBinary, evalBinary; cbn [KindCustomInd getDefault SameTupleDefault];
      fold (@evalBinary orb (fun n0 : Z => @Zmod.or (2 ^ n0)) k);
      fold (@evalOrBinary k).
    apply (@evalBinaryArray_or_default_r k IHk).
  - destruct x as [f s].
    cbn [evalOrBinary evalBinary KindCustomInd getDefault Fst Snd].
    rewrite !Zmod_or_0_r; reflexivity.
Qed.

Lemma fold_left_evalOrBinary_default :
  forall {k : Kind} (acc : list (type k)) (init : type k),
    Forall (fun x => x = getDefault k) acc ->
    fold_left (@evalOrBinary k) acc init = init.
Proof.
  intros k acc init Hacc.
  revert init.
  induction Hacc as [| x rest Hx Hrest IH]; intros init; cbn [fold_left].
  - reflexivity.
  - subst x; rewrite evalOrBinary_getDefault_r; apply IH.
Qed.

Lemma evalWriteRegsListHelper_writeRegOfKind_comm :
  forall {t : Tree DomainElem} {k1 k2 : Kind} {sz : Z}
         (rk : RegOfKind (t:=t) k1) (paths : list (RegOfKind (t:=t) k2))
         (curr : nat) (idx : bits sz) (v1 : type k1) (v2 : type k2)
         (s : TreeState DomainElemState t),
    Forall (fun rk' => rk.(rk_path).(regPath) <> rk'.(rk_path).(regPath)) paths ->
    evalWriteRegsListHelper curr paths idx v2 (writeRegOfKind rk v1 s) =
    writeRegOfKind rk v1 (evalWriteRegsListHelper curr paths idx v2 s).
Proof.
  intros t k1 k2 sz rk paths.
  induction paths as [| rk0 rest IH]; intros curr idx v1 v2 s Hfor; cbn [evalWriteRegsListHelper].
  - reflexivity.
  - inversion Hfor as [| ? ? Hneq Hrest]; subst.
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + rewrite (writeRegOfKind_writeRegOfKind_comm rk rk0 v1 v2 s Hneq).
      apply IH; exact Hrest.
    + apply IH; exact Hrest.
Qed.

Lemma readRegOfKind_evalWriteRegsListHelper_other :
  forall {t : Tree DomainElem} {k1 k2 : Kind} {sz : Z}
         (rk : RegOfKind (t:=t) k1) (paths : list (RegOfKind (t:=t) k2))
         (curr : nat) (idx : bits sz) (v : type k2) (s : TreeState DomainElemState t),
    Forall (fun rk' => rk.(rk_path).(regPath) <> rk'.(rk_path).(regPath)) paths ->
    readRegOfKind rk (evalWriteRegsListHelper curr paths idx v s) =
    readRegOfKind rk s.
Proof.
  intros t k1 k2 sz rk paths.
  induction paths as [| rk0 rest IH]; intros curr idx v s Hfor; cbn [evalWriteRegsListHelper].
  - reflexivity.
  - inversion Hfor as [| ? ? Hneq Hrest]; subst.
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + rewrite (IH (S curr) idx v _ Hrest).
      apply (readRegOfKind_writeRegOfKind_other rk rk0 v s Hneq).
    + apply (IH (S curr) idx v s Hrest).
Qed.

Lemma evalReadRegsListHelper_writeRegOfKind_other :
  forall {t : Tree DomainElem} {k1 k2 : Kind} {sz : Z}
         (rk : RegOfKind (t:=t) k2) (paths : list (RegOfKind (t:=t) k1))
         (curr : nat) (acc : list (type k1)) (idx : bits sz) (v : type k2)
         (s : TreeState DomainElemState t),
    Forall (fun rk' => rk'.(rk_path).(regPath) <> rk.(rk_path).(regPath)) paths ->
    evalReadRegsListHelper curr acc paths idx (writeRegOfKind rk v s) =
    evalReadRegsListHelper curr acc paths idx s.
Proof.
  intros t k1 k2 sz rk paths.
  induction paths as [| rk0 rest IH]; intros curr acc idx v s Hfor; cbn [evalReadRegsListHelper].
  - reflexivity.
  - inversion Hfor as [| ? ? Hneq Hrest]; subst.
    rewrite (readRegOfKind_writeRegOfKind_other rk0 rk v s Hneq).
    apply IH; exact Hrest.
Qed.

Lemma not_In_map_regPath_Forall :
  forall {t : Tree DomainElem} {k : Kind}
         (rk : RegOfKind (t:=t) k) (rest : list (RegOfKind (t:=t) k)),
    ~ In rk.(rk_path).(regPath) (map (fun r : RegOfKind k => r.(rk_path).(regPath)) rest) ->
    Forall (fun rk' : RegOfKind k => rk.(rk_path).(regPath) <> rk'.(rk_path).(regPath)) rest /\
    Forall (fun rk' : RegOfKind k => rk'.(rk_path).(regPath) <> rk.(rk_path).(regPath)) rest.
Proof.
  intros t k rk rest Hnin.
  induction rest as [| r rs IH]; cbn [map In] in *.
  - split; constructor.
  - destruct (IH (fun H => Hnin (or_intror H))) as [HF1 HF2].
    split; constructor; auto.
Qed.

Lemma isEq_Bit_true_iff :
  forall {sz : Z} (a b : bits sz),
    @isEq (Bit sz) a b = true <-> a = b.
Proof.
  intros sz a b; apply Zmod.eqb_eq.
Qed.

Lemma evalWriteRegsListHelper_same :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (idx : bits sz) (v1 v2 : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    evalWriteRegsListHelper curr paths idx v2 (evalWriteRegsListHelper curr paths idx v1 s) =
    evalWriteRegsListHelper curr paths idx v2 s.
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr idx v1 v2 s Hnd; cbn [evalWriteRegsListHelper].
  - reflexivity.
  - cbn [map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
    destruct (not_In_map_regPath_Forall rk rest Hnin) as [HF1 _].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx v1 v1 s HF1).
      rewrite writeRegOfKind_writeRegOfKind_same.
      rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx v2 v2 _ HF1).
      rewrite (IH (S curr) idx v1 v2 s Hnd_rest).
      symmetry; apply (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx v2 v2 s HF1).
    + apply IH; exact Hnd_rest.
Qed.

Theorem evalWriteRegsList_same :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k))
         (idx : bits sz) (v1 v2 : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    evalWriteRegsList paths idx v2 (evalWriteRegsList paths idx v1 s) =
    evalWriteRegsList paths idx v2 s.
Proof.
  intros t k sz paths idx v1 v2 s Hnd.
  apply evalWriteRegsListHelper_same; exact Hnd.
Qed.

Lemma evalWriteRegsListHelper_comm :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (idx1 idx2 : bits sz) (v1 v2 : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    idx1 <> idx2 ->
    evalWriteRegsListHelper curr paths idx2 v2 (evalWriteRegsListHelper curr paths idx1 v1 s) =
    evalWriteRegsListHelper curr paths idx1 v1 (evalWriteRegsListHelper curr paths idx2 v2 s).
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr idx1 idx2 v1 v2 s Hnd Hneq; cbn [evalWriteRegsListHelper].
  - reflexivity.
  - cbn [map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
    destruct (not_In_map_regPath_Forall rk rest Hnin) as [HF1 _].
    destruct (@isEq (Bit sz) idx1 (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq1;
    destruct (@isEq (Bit sz) idx2 (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq2.
    + apply isEq_Bit_true_iff in Heq1; apply isEq_Bit_true_iff in Heq2; subst; exfalso; apply Hneq; reflexivity.
    + rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx1 v1 v1 s HF1).
      rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx2 v1 v2 _ HF1).
      rewrite (IH (S curr) idx1 idx2 v1 v2 s Hnd_rest Hneq).
      symmetry; apply (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx1 v1 v1 _ HF1).
    + rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx2 v2 v2 s HF1).
      rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx1 v2 v1 _ HF1).
      rewrite <- (IH (S curr) idx1 idx2 v1 v2 s Hnd_rest Hneq).
      apply (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx2 v2 v2 _ HF1).
    + apply IH; [exact Hnd_rest | exact Hneq].
Qed.

Theorem evalWriteRegsList_comm :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k))
         (idx1 idx2 : bits sz) (v1 v2 : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    idx1 <> idx2 ->
    evalWriteRegsList paths idx2 v2 (evalWriteRegsList paths idx1 v1 s) =
    evalWriteRegsList paths idx1 v1 (evalWriteRegsList paths idx2 v2 s).
Proof.
  intros t k sz paths idx1 idx2 v1 v2 s Hnd Hneq.
  apply evalWriteRegsListHelper_comm; [exact Hnd | exact Hneq].
Qed.

Lemma evalReadRegsListHelper_evalWriteRegsListHelper_other :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (acc : list (type k)) (idx1 idx2 : bits sz) (v : type k)
         (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    idx1 <> idx2 ->
    evalReadRegsListHelper curr acc paths idx1 (evalWriteRegsListHelper curr paths idx2 v s) =
    evalReadRegsListHelper curr acc paths idx1 s.
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr acc idx1 idx2 v s Hnd Hneq;
    cbn [evalReadRegsListHelper evalWriteRegsListHelper].
  - reflexivity.
  - cbn [map] in Hnd; inversion Hnd as [| ? ? Hnin Hnd_rest]; subst.
    destruct (not_In_map_regPath_Forall rk rest Hnin) as [HF1 HF2].
    destruct (@isEq (Bit sz) idx1 (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq1;
    destruct (@isEq (Bit sz) idx2 (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq2.
    + apply isEq_Bit_true_iff in Heq1; apply isEq_Bit_true_iff in Heq2; subst; exfalso; apply Hneq; reflexivity.
    + rewrite (readRegOfKind_evalWriteRegsListHelper_other rk rest (S curr) idx2 v s HF1).
      apply (IH (S curr) _ idx1 idx2 v s Hnd_rest Hneq).
    + rewrite (evalWriteRegsListHelper_writeRegOfKind_comm rk rest (S curr) idx2 v v s HF1).
      rewrite (evalReadRegsListHelper_writeRegOfKind_other rk rest (S curr) _ idx1 v _ HF2).
      apply (IH (S curr) _ idx1 idx2 v s Hnd_rest Hneq).
    + apply (IH (S curr) _ idx1 idx2 v s Hnd_rest Hneq).
Qed.

Theorem evalReadRegsList_evalWriteRegsList_other :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k))
         (idx1 idx2 : bits sz) (v : type k) (s : TreeState DomainElemState t),
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths) ->
    idx1 <> idx2 ->
    evalReadRegsList paths idx1 (evalWriteRegsList paths idx2 v s) =
    evalReadRegsList paths idx1 s.
Proof.
  intros t k sz paths idx1 idx2 v s Hnd Hneq.
  apply evalReadRegsListHelper_evalWriteRegsListHelper_other; [exact Hnd | exact Hneq].
Qed.

Lemma isEq_Bit_of_Z_neq :
  forall {sz : Z} (idx : bits sz) (curr : nat),
    (Z.of_nat curr < 2 ^ sz)%Z ->
    Zmod.to_Z idx <> Z.of_nat curr ->
    @isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr)) = false.
Proof.
  intros sz idx curr Hlt Hneq.
  destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))) eqn:Heq; [| reflexivity].
  apply isEq_Bit_true_iff in Heq; subst idx.
  rewrite Zmod.to_Z_of_Z, Z.mod_small in Hneq by lia.
  exfalso; apply Hneq; reflexivity.
Qed.

Lemma isEq_Bit_of_Z_eq :
  forall {sz : Z} (idx : bits sz) (curr : nat),
    Zmod.to_Z idx = Z.of_nat curr ->
    @isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr)) = true.
Proof.
  intros sz idx curr Heq.
  apply isEq_Bit_true_iff.
  rewrite <- Heq, Zmod.of_Z_to_Z; reflexivity.
Qed.

Lemma evalWriteRegsListHelper_above :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (idx : bits sz) (v : type k) (s : TreeState DomainElemState t),
    (Zmod.to_Z idx < Z.of_nat curr)%Z ->
    (Z.of_nat (curr + length paths) <= 2 ^ sz)%Z ->
    evalWriteRegsListHelper curr paths idx v s = s.
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr idx v s Hlt Hpow; cbn [evalWriteRegsListHelper length] in *.
  - reflexivity.
  - rewrite isEq_Bit_of_Z_neq by lia.
    apply IH; lia.
Qed.

Lemma evalReadRegsListHelper_above :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz) (s : TreeState DomainElemState t),
    (Zmod.to_Z idx < Z.of_nat curr)%Z ->
    (Z.of_nat (curr + length paths) <= 2 ^ sz)%Z ->
    evalReadRegsListHelper curr acc paths idx s =
    fold_left (@evalOrBinary k) acc (getDefault k).
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr acc idx s Hlt Hpow; cbn [evalReadRegsListHelper length] in *.
  - reflexivity.
  - rewrite isEq_Bit_of_Z_neq by lia.
    rewrite IH by lia.
    cbn [fold_left]; rewrite evalOrBinary_getDefault_l; reflexivity.
Qed.

Lemma evalReadRegsListHelper_evalWriteRegsListHelper_same :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz) (v : type k)
         (s : TreeState DomainElemState t),
    (Z.of_nat curr <= Zmod.to_Z idx < Z.of_nat (curr + length paths))%Z ->
    (Z.of_nat (curr + length paths) <= 2 ^ sz)%Z ->
    Forall (fun x => x = getDefault k) acc ->
    evalReadRegsListHelper curr acc paths idx (evalWriteRegsListHelper curr paths idx v s) = v.
Proof.
  intros t k sz paths.
  induction paths as [| rk rest IH]; intros curr acc idx v s Hbound Hpow Hacc;
    cbn [evalReadRegsListHelper evalWriteRegsListHelper length] in *.
  - lia.
  - destruct (Z.eq_dec (Zmod.to_Z idx) (Z.of_nat curr)) as [Heq | Hneq].
    + rewrite (isEq_Bit_of_Z_eq idx curr Heq).
      rewrite evalWriteRegsListHelper_above by lia.
      rewrite readRegOfKind_writeRegOfKind_same.
      rewrite evalReadRegsListHelper_above by lia.
      cbn [fold_left].
      rewrite evalOrBinary_getDefault_l.
      apply fold_left_evalOrBinary_default; exact Hacc.
    + rewrite isEq_Bit_of_Z_neq by lia.
      apply IH; [lia | lia | constructor; [reflexivity | exact Hacc]].
Qed.

Theorem evalReadRegsList_evalWriteRegsList_same :
  forall {t : Tree DomainElem} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t:=t) k))
         (idx : bits sz) (v : type k) (s : TreeState DomainElemState t),
    (0 < 2 ^ sz)%Z ->
    Z.of_nat (length paths) = (2 ^ sz)%Z ->
    evalReadRegsList paths idx (evalWriteRegsList paths idx v s) = v.
Proof.
  intros t k sz paths idx v s Hpos Hlen.
  pose proof (Zmod.unsigned_pos_bound idx Hpos) as Hbound.
  apply evalReadRegsListHelper_evalWriteRegsListHelper_same; [lia | lia | constructor].
Qed.

Fixpoint leafPath_id {A : Type} {t : Tree A} : LeafPath t -> list bool :=
  match t return LeafPath t -> list bool with
  | Leaf _ _ => fun _ => nil
  | Node _ children =>
      (fix loop (ls : list (Tree A)) : LeafPath (Node "" ls) -> list bool :=
         match ls return LeafPath (Node "" ls) -> list bool with
         | nil => fun empty => match empty with end
         | x :: xs => fun p =>
             match p with
             | inl px => false :: @leafPath_id A x px
             | inr pxs => true :: loop xs pxs
             end
         end) children
  end.

Lemma NoDup_map_inv :
  forall {A B : Type} (f : A -> B) (ls : list A),
    NoDup (map f ls) ->
    NoDup ls.
Proof.
  intros A B f ls Hnd.
  induction ls as [| x xs IH]; cbn [map] in *; constructor.
  - inversion Hnd as [| ? ? Hnin _]; intros Hin.
    apply Hnin, in_map; exact Hin.
  - inversion Hnd as [| ? ? _ Hnd']; apply IH; exact Hnd'.
Qed.

Lemma NoDup_regPath_of_leafPath_id :
  forall {t : Tree DomainElem} {k : Kind} (paths : list (RegOfKind (t:=t) k)),
    NoDup (map (fun r : RegOfKind k => leafPath_id r.(rk_path).(regPath)) paths) ->
    NoDup (map (fun r : RegOfKind k => r.(rk_path).(regPath)) paths).
Proof.
  intros t k paths Hnd.
  apply (NoDup_map_inv (@leafPath_id DomainElem t)).
  rewrite map_map; exact Hnd.
Qed.

(* ---------------------------------------------------------------------------
 * 5. Deterministic Initialization (`allTreeInitDet`) & Content Equivalence (`TreeContentRel`)
 * --------------------------------------------------------------------------- *)

Definition allElemInitDet (e : Elem) : bool :=
  match e with
  | EReg r =>
      match r.(regInit) with
      | Some _ => true
      | None => false
      end
  | EMem _ => false
  | ESend _ => true
  | ERecv _ => true
  end.

Fixpoint allTreeInitDet (t : Tree DomainElem) : bool :=
  match t with
  | Leaf _ de => allElemInitDet (snd de)
  | Node _ children =>
      (fix loop (ls : list (Tree DomainElem)) : bool :=
         match ls with
         | nil => true
         | x :: xs => andb (allTreeInitDet x) (loop xs)
         end) children
  end.

Lemma allElemInitDet_InitState :
  forall (e : Elem) (s : ElemState e),
    allElemInitDet e = true ->
    InitStateElemConsistent e s ->
    s = InitStateElem e.
Proof.
  intros [r | m | k | k] s Hdet Hinit; cbn in Hdet, Hinit |- *.
  - destruct (regInit r) as [init |]; [exact Hinit | discriminate Hdet].
  - discriminate Hdet.
  - exact Hinit.
  - exact Hinit.
Qed.

Theorem allTreeInitDet_InitState :
  forall (t : Tree DomainElem) (s : TreeState DomainElemState t),
    allTreeInitDet t = true ->
    InitStateConsistent t s ->
    s = InitState t.
Proof.
  fix F 1.
  intros [name de | name children] s Hdet Hinit; cbn in Hdet, Hinit |- *.
  - apply allElemInitDet_InitState; assumption.
  - induction children as [| x xs IH].
    + destruct s; reflexivity.
    + destruct s as [sx sxs]; cbn [Fst Snd] in Hinit.
      apply andb_prop in Hdet; destruct Hdet as [Hdet_x Hdet_xs].
      destruct Hinit as [Hinit_x Hinit_xs].
      f_equal.
      * apply F; assumption.
      * apply IH; assumption.
Qed.

Corollary allTreeInitDet_InitStateConsistent_eq :
  forall (t : Tree DomainElem) (s1 s2 : TreeState DomainElemState t),
    allTreeInitDet t = true ->
    InitStateConsistent t s1 ->
    InitStateConsistent t s2 ->
    s1 = s2.
Proof.
  intros t s1 s2 Hdet H1 H2.
  rewrite (allTreeInitDet_InitState t s1 Hdet H1).
  rewrite (allTreeInitDet_InitState t s2 Hdet H2).
  reflexivity.
Qed.

Definition ElemContentRel (e : Elem) : ElemState e -> ElemState e -> Prop :=
  match e return ElemState e -> ElemState e -> Prop with
  | EReg r =>
      match r.(regInit) with
      | None => fun _ _ => True
      | Some _ => fun s1 s2 => s1 = s2
      end
  | EMem m =>
      match m.(memInit) with
      | None => fun _ _ => True
      | Some _ => fun s1 s2 => s1.(Fst) = s2.(Fst)
      end
  | ESend _ => fun s1 s2 => s1 = s2
  | ERecv _ => fun s1 s2 => s1 = s2
  end.

Fixpoint TreeContentRel (t : Tree DomainElem)
  : TreeState DomainElemState t -> TreeState DomainElemState t -> Prop :=
  match t return TreeState DomainElemState t -> TreeState DomainElemState t -> Prop with
  | Leaf _ de => ElemContentRel (snd de)
  | Node _ children =>
      (fix loop (ls : list (Tree DomainElem))
         : ListTreeState DomainElemState ls -> ListTreeState DomainElemState ls -> Prop :=
         match ls return ListTreeState DomainElemState ls -> ListTreeState DomainElemState ls -> Prop with
         | nil => fun _ _ => True
         | x :: xs => fun s1 s2 => TreeContentRel x s1.(Fst) s2.(Fst) /\ loop xs s1.(Snd) s2.(Snd)
         end) children
  end.

Lemma ElemContentRel_refl :
  forall (e : Elem) (s : ElemState e),
    ElemContentRel e s s.
Proof.
  intros [r | m | k | k] s; cbn.
  - destruct (regInit r); [reflexivity | exact I].
  - destruct (memInit m); [reflexivity | exact I].
  - reflexivity.
  - reflexivity.
Qed.

Theorem TreeContentRel_refl :
  forall (t : Tree DomainElem) (s : TreeState DomainElemState t),
    TreeContentRel t s s.
Proof.
  fix F 1.
  intros [name de | name children] s; cbn.
  - apply ElemContentRel_refl.
  - induction children as [| x xs IH].
    + exact I.
    + split; [apply F | apply IH].
Qed.

Lemma InitStateElemConsistent_ElemContentRel :
  forall (e : Elem) (s1 s2 : ElemState e),
    InitStateElemConsistent e s1 ->
    InitStateElemConsistent e s2 ->
    ElemContentRel e s1 s2.
Proof.
  intros [r | m | k | k] s1 s2 H1 H2; cbn in H1, H2 |- *.
  - destruct (regInit r); [congruence | exact I].
  - destruct (memInit m); [congruence | exact I].
  - congruence.
  - congruence.
Qed.

Theorem InitStateConsistent_TreeContentRel :
  forall (t : Tree DomainElem) (s1 s2 : TreeState DomainElemState t),
    InitStateConsistent t s1 ->
    InitStateConsistent t s2 ->
    TreeContentRel t s1 s2.
Proof.
  fix F 1.
  intros [name de | name children] s1 s2 H1 H2; cbn in H1, H2 |- *.
  - apply InitStateElemConsistent_ElemContentRel; assumption.
  - induction children as [| x xs IH].
    + exact I.
    + split.
      * apply F; [exact (proj1 H1) | exact (proj1 H2)].
      * apply IH; [exact (proj2 H1) | exact (proj2 H2)].
Qed.

Lemma ElemContentRel_InitStateElemConsistent :
  forall (e : Elem) (s1 s2 : ElemState e),
    InitStateElemConsistent e s1 ->
    ElemContentRel e s1 s2 ->
    InitStateElemConsistent e s2.
Proof.
  intros [r | m | k | k] s1 s2 Hinit Hrel; cbn in Hinit, Hrel |- *.
  - destruct (regInit r) as [init |]; [congruence | exact I].
  - destruct (memInit m) as [init |]; [congruence | exact I].
  - congruence.
  - congruence.
Qed.

Theorem TreeContentRel_InitStateConsistent :
  forall (t : Tree DomainElem) (s1 s2 : TreeState DomainElemState t),
    InitStateConsistent t s1 ->
    TreeContentRel t s1 s2 ->
    InitStateConsistent t s2.
Proof.
  fix F 1.
  intros [name de | name children] s1 s2 Hinit Hrel; cbn in Hinit, Hrel |- *.
  - exact (ElemContentRel_InitStateElemConsistent (snd de) s1 s2 Hinit Hrel).
  - induction children as [| x xs IH].
    + exact I.
    + destruct s1 as [sx1 sxs1], s2 as [sx2 sxs2].
      cbn [Fst Snd] in Hinit, Hrel |- *.
      destruct Hinit as [Hinit_x Hinit_xs], Hrel as [Hrel_x Hrel_xs].
      split.
      * exact (F x sx1 sx2 Hinit_x Hrel_x).
      * exact (IH sxs1 sxs2 Hinit_xs Hrel_xs).
Qed.

(* ---------------------------------------------------------------------------
 * 6. Child-Subtree Register-Bank Localization, `NoDup_getTreeRegsOfKind`, & `ActionCommutes`
 * --------------------------------------------------------------------------- *)

Definition is_child0_reg {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inl _ => true
  | inr _ => false
  end.

Definition is_child1_reg {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: c1 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inr (inl _) => true
  | _ => false
  end.

Definition is_child2_reg {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
  (r : RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k) : bool :=
  match r.(rk_path).(regPath) with
  | inr (inr (inl _)) => true
  | _ => false
  end.

Lemma writeRegOfKind_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    is_child0_reg r = true ->
    (writeRegOfKind r val s1).(Snd) = s1.(Snd) /\
    (s1.(Fst) = s2.(Fst) ->
     (writeRegOfKind r val s1).(Fst) = (writeRegOfKind r val s2).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 cs k r val s1 s2 Hc0.
  unfold is_child0_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) w).(Snd) = s1.(Snd) /\
          (s1.(Fst) = s2.(Fst) ->
           (writeTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) =
           (writeTreeState (Node name (c0 :: cs)) s2 r.(rk_path).(regPath) w).(Fst) /\
           readTreeState (Node name (c0 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: cs)) s2 r.(rk_path).(regPath))) as [H1 H2].
  { split; [exact H1 | intros Hfst; destruct (H2 Hfst) as [H3 H4]; split; [exact H3 | rewrite H4; reflexivity]]. }
  clearbody w; revert Hc0 w; generalize (r.(rk_path).(regPath)); intros [p0 | p_rest] Hc0 w; [| discriminate Hc0].
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | intros Hfst; rewrite Hfst; split; reflexivity].
Qed.

Lemma writeRegOfKind_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: c1 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    is_child1_reg r = true ->
    (writeRegOfKind r val s1).(Fst) = s1.(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Snd) = s1.(Snd).(Snd) /\
    (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
     (writeRegOfKind r val s1).(Snd).(Fst) = (writeRegOfKind r val s2).(Snd).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 c1 cs k r val s1 s2 Hc1.
  unfold is_child1_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) = s1.(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd) = s1.(Snd).(Snd) /\
          (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
           (writeTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Fst) =
           (writeTreeState (Node name (c0 :: c1 :: cs)) s2 r.(rk_path).(regPath) w).(Snd).(Fst) /\
           readTreeState (Node name (c0 :: c1 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: c1 :: cs)) s2 r.(rk_path).(regPath))) as [H1 [H2 H3]].
  { split; [exact H1 | split; [exact H2 | intros Hsf; destruct (H3 Hsf) as [H4 H5]; split; [exact H4 | rewrite H5; reflexivity]]]. }
  clearbody w; revert Hc1 w; generalize (r.(rk_path).(regPath)); intros [p0 | [p1 | p_rest]] Hc1 w; try discriminate Hc1.
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | split; [reflexivity | intros Hsf; rewrite Hsf; split; reflexivity]].
Qed.

Lemma writeRegOfKind_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind}
         (r : RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    is_child2_reg r = true ->
    (writeRegOfKind r val s1).(Fst) = s1.(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Fst) = s1.(Snd).(Fst) /\
    (writeRegOfKind r val s1).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
    (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
     (writeRegOfKind r val s1).(Snd).(Snd).(Fst) = (writeRegOfKind r val s2).(Snd).(Snd).(Fst) /\
     readRegOfKind r s1 = readRegOfKind r s2).
Proof.
  intros name c0 c1 c2 cs k r val s1 s2 Hc2.
  unfold is_child2_reg, writeRegOfKind, readRegOfKind in *.
  set (w := castStateRegInv r.(rk_path)
              (eq_rect k type val (regKind (getRegFromPath r.(rk_path)))
                 (eq_sym (Kind_eqb_eq (regKind (getRegFromPath r.(rk_path))) k r.(rk_pf))))).
  enough ((writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Fst) = s1.(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Fst) = s1.(Snd).(Fst) /\
          (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
          (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
           (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) w).(Snd).(Snd).(Fst) =
           (writeTreeState (Node name (c0 :: c1 :: c2 :: cs)) s2 r.(rk_path).(regPath) w).(Snd).(Snd).(Fst) /\
           readTreeState (Node name (c0 :: c1 :: c2 :: cs)) s1 r.(rk_path).(regPath) =
           readTreeState (Node name (c0 :: c1 :: c2 :: cs)) s2 r.(rk_path).(regPath))) as [H1 [H2 [H3 H4]]].
  { split; [exact H1 | split; [exact H2 | split; [exact H3 | intros Hssf; destruct (H4 Hssf) as [H5 H6]; split; [exact H5 | rewrite H6; reflexivity]]]]. }
  clearbody w; revert Hc2 w; generalize (r.(rk_path).(regPath)); intros [p0 | [p1 | [p2 | p_rest]]] Hc2 w; try discriminate Hc2.
  cbn [writeTreeState readTreeState Fst Snd].
  split; [reflexivity | split; [reflexivity | split; [reflexivity | intros Hssf; rewrite Hssf; split; reflexivity]]].
Qed.

Lemma evalWriteRegsListHelper_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    forallb is_child0_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Snd) = s1.(Snd) /\
    (s1.(Fst) = s2.(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Fst)).
Proof.
  intros name c0 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | exact id].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child0 r val s1 s2 Hr) as [Hsnd Hfst].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest) as [IHsnd IHfst].
      split; [rewrite IHsnd; exact Hsnd | intros Heq; apply IHfst, Hfst, Heq].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child0 :
  forall {name : string} {c0 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: cs))),
    forallb is_child0_reg paths = true ->
    s1.(Fst) = s2.(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child0 r (getDefault k) s1 s2 Hr) as [_ Hfst].
    destruct (Hfst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma evalWriteRegsListHelper_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    forallb is_child1_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Fst) = s1.(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd) = s1.(Snd).(Snd) /\
    (s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Snd).(Fst)).
Proof.
  intros name c0 c1 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | split; [reflexivity | exact id]].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child1 r val s1 s2 Hr) as [Hfst [Hsndsnd Hsndfst]].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest)
        as [IHfst [IHsndsnd IHsndfst]].
      split; [rewrite IHfst; exact Hfst | split; [rewrite IHsndsnd; exact Hsndsnd | intros Heq; apply IHsndfst, Hsndfst, Heq]].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child1 :
  forall {name : string} {c0 c1 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: cs))),
    forallb is_child1_reg paths = true ->
    s1.(Snd).(Fst) = s2.(Snd).(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 c1 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child1 r (getDefault k) s1 s2 Hr) as [_ [_ Hsndfst]].
    destruct (Hsndfst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma evalWriteRegsListHelper_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k)) (curr : nat)
         (idx : bits sz) (val : type k)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    forallb is_child2_reg paths = true ->
    (evalWriteRegsListHelper curr paths idx val s1).(Fst) = s1.(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Fst) = s1.(Snd).(Fst) /\
    (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd).(Snd) = s1.(Snd).(Snd).(Snd) /\
    (s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
     (evalWriteRegsListHelper curr paths idx val s1).(Snd).(Snd).(Fst) =
     (evalWriteRegsListHelper curr paths idx val s2).(Snd).(Snd).(Fst)).
Proof.
  intros name c0 c1 c2 cs k sz paths.
  induction paths as [| r rest IH]; intros curr idx val s1 s2 Hall; cbn [evalWriteRegsListHelper forallb] in *.
  - split; [reflexivity | split; [reflexivity | split; [reflexivity | exact id]]].
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (@isEq (Bit sz) idx (Zmod.of_Z (2 ^ sz) (Z.of_nat curr))).
    + destruct (writeRegOfKind_child2 r val s1 s2 Hr) as [Hfst [Hsndfst [Hsnd3 Hsnd2fst]]].
      destruct (IH (S curr) idx val (writeRegOfKind r val s1) (writeRegOfKind r val s2) Hrest)
        as [IHfst [IHsndfst [IHsnd3 IHsnd2fst]]].
      split; [rewrite IHfst; exact Hfst |
        split; [rewrite IHsndfst; exact Hsndfst |
          split; [rewrite IHsnd3; exact Hsnd3 |
            intros Heq; apply IHsnd2fst, Hsnd2fst, Heq]]].
    + apply IH; exact Hrest.
Qed.

Lemma evalReadRegsListHelper_child2 :
  forall {name : string} {c0 c1 c2 : Tree DomainElem} {cs : list (Tree DomainElem)} {k : Kind} {sz : Z}
         (paths : list (RegOfKind (t := Node name (c0 :: c1 :: c2 :: cs)) k)) (curr : nat)
         (acc : list (type k)) (idx : bits sz)
         (s1 s2 : TreeState DomainElemState (Node name (c0 :: c1 :: c2 :: cs))),
    forallb is_child2_reg paths = true ->
    s1.(Snd).(Snd).(Fst) = s2.(Snd).(Snd).(Fst) ->
    evalReadRegsListHelper curr acc paths idx s1 =
    evalReadRegsListHelper curr acc paths idx s2.
Proof.
  intros name c0 c1 c2 cs k sz paths.
  induction paths as [| r rest IH]; intros curr acc idx s1 s2 Hall Heq; cbn [evalReadRegsListHelper forallb] in *.
  - reflexivity.
  - apply andb_prop in Hall as [Hr Hrest].
    destruct (writeRegOfKind_child2 r (getDefault k) s1 s2 Hr) as [_ [_ [_ Hsnd2fst]]].
    destruct (Hsnd2fst Heq) as [_ Hread].
    rewrite Hread; apply IH; [exact Hrest | exact Heq].
Qed.

Lemma NoDup_map_inj :
  forall {A B : Type} (f : A -> B) (l : list A),
    (forall x y, f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros A B f l Hinj Hnodup.
  induction Hnodup as [| x xs HnotIn Hnodup IH]; cbn [map].
  - constructor.
  - constructor; [| exact IH].
    intros Hin; apply in_map_iff in Hin as [y [Heq Hin]].
    apply Hinj in Heq; subst y; contradiction.
Qed.

Lemma NoDup_app_disj :
  forall {A : Type} (l1 l2 : list A),
    NoDup l1 ->
    NoDup l2 ->
    (forall x, In x l1 -> In x l2 -> False) ->
    NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 Hdisj.
  induction H1 as [| x xs HnotIn H1 IH]; cbn [app].
  - exact H2.
  - constructor.
    + intros Hin; apply in_app_or in Hin as [Hin | Hin].
      * contradiction.
      * eapply Hdisj; [left; reflexivity | exact Hin].
    + apply IH; intros y Hy1 Hy2; eapply Hdisj; [right; exact Hy1 | exact Hy2].
Qed.

Lemma NoDup_map_if_bool :
  forall {A B : Type} (g : A -> B) (b : bool)
         (f1 : b = true -> list A)
         (f2 : b = false -> list A),
    (forall pf, NoDup (map g (f1 pf))) ->
    (forall pf, NoDup (map g (f2 pf))) ->
    NoDup (map g ((if b as b0 return (b = b0 -> list A) then f1 else f2) eq_refl)).
Proof.
  intros A B g [|] f1 f2 H1 H2; [apply H1 | apply H2].
Qed.

Fixpoint NoDup_getTreeRegsOfKind (k : Kind) (t : Tree DomainElem) :
  NoDup (map (fun rk : RegOfKind (t:=t) k => rk.(rk_path).(regPath)) (getTreeRegsOfKind k t)).
Proof.
  destruct t as [name [dom elem] | name children]; simpl.
  - destruct elem as [r | m | sk | rk]; simpl; try constructor.
    apply NoDup_map_if_bool; intros pf; simpl; repeat constructor; simpl; auto.
  - induction children as [| x xs IHxs]; simpl.
    + constructor.
    + rewrite map_app, !map_map; simpl.
      apply NoDup_app_disj.
      * rewrite <- (map_map (fun rk : RegOfKind (t:=x) k => rk.(rk_path).(regPath))
                            (@inl (LeafPath x) (LeafPath (Node name xs)))).
        eapply NoDup_map_inj.
        -- intros a b H; injection H; auto.
        -- apply NoDup_getTreeRegsOfKind.
      * rewrite <- (map_map (fun rk : RegOfKind (t:=Node name xs) k => rk.(rk_path).(regPath))
                            (@inr (LeafPath x) (LeafPath (Node name xs)))).
        eapply NoDup_map_inj.
        -- intros a b H; injection H; auto.
        -- exact IHxs.
      * intros p Hin1 Hin2.
        apply in_map_iff in Hin1 as [rk1 [Heq1 _]].
        apply in_map_iff in Hin2 as [rk2 [Heq2 _]].
        congruence.
Qed.

Definition ActionCommutes {t : Tree DomainElem} {k : Kind} {env : Env t}
  (f : TreeState DomainElemState t -> TreeState DomainElemState t)
  (act : Action type t k) : Prop :=
  forall (s : TreeState DomainElemState t)
         (P : TreeState DomainElemState t -> type k -> Prop),
    evalActionPropGen env act (f s) P <->
    evalActionPropGen env act s (fun s' v => P (f s') v).

Lemma ActionCommutes_Return :
  forall {t : Tree DomainElem} {k : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (e : Expr type k),
    @ActionCommutes t k env f (Return e).
Proof.
  intros t k env f e s P; reflexivity.
Qed.

Lemma ActionCommutes_LetExp :
  forall {t : Tree DomainElem} {k k' : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (nm : string) (e : Expr type k') (cont : type k' -> Action type t k),
    (forall v, @ActionCommutes t k env f (cont v)) ->
    @ActionCommutes t k env f (LetExp nm e cont).
Proof.
  intros t k k' env f nm e cont Hcont s P.
  cbn [evalActionPropGen].
  apply Hcont.
Qed.

Lemma ActionCommutes_LetExp_eval :
  forall {t : Tree DomainElem} {k k' : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (nm : string) (e : Expr type k') (cont : type k' -> Action type t k),
    @ActionCommutes t k env f (cont (evalExpr e)) ->
    @ActionCommutes t k env f (LetExp nm e cont).
Proof.
  intros t k k' env f nm e cont Hcont s P.
  exact (Hcont s P).
Qed.

Lemma ActionCommutes_LetAction :
  forall {t : Tree DomainElem} {k k' : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (nm : string) (a : Action type t k') (cont : type k' -> Action type t k),
    @ActionCommutes t k' env f a ->
    (forall v, @ActionCommutes t k env f (cont v)) ->
    @ActionCommutes t k env f (LetAction nm a cont).
Proof.
  intros t k k' env f nm a cont Ha Hcont s P.
  cbn [evalActionPropGen].
  rewrite (Ha s (fun s1 v1 => evalActionPropGen env (cont v1) s1 P)).
  apply evalActionPropGen_ext; intros s1 v1.
  apply Hcont.
Qed.

Lemma ActionCommutes_Seq :
  forall {t : Tree DomainElem} {k k' : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (nm : string) (a : Action type t k') (b : Action type t k),
    @ActionCommutes t k' env f a ->
    @ActionCommutes t k env f b ->
    @ActionCommutes t k env f (LetAction nm a (fun _ => b)).
Proof.
  intros t k k' env f nm a b Ha Hb.
  apply ActionCommutes_LetAction; [exact Ha | intros _; exact Hb].
Qed.

Lemma ActionCommutes_IfElse :
  forall {t : Tree DomainElem} {k k' : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (nm : string) (cond : Expr type Bool)
         (aT aF : Action type t k')
         (cont : type k' -> Action type t k),
    @ActionCommutes t k' env f aT ->
    @ActionCommutes t k' env f aF ->
    (forall v, @ActionCommutes t k env f (cont v)) ->
    @ActionCommutes t k env f (IfElse nm cond aT aF cont).
Proof.
  intros t k k' env f nm cond aT aF cont HT HF Hcont s P.
  cbn [evalActionPropGen].
  destruct (evalExpr cond).
  - rewrite (HT s (fun s1 v1 => evalActionPropGen env (cont v1) s1 P)).
    apply evalActionPropGen_ext; intros s1 v1; apply Hcont.
  - rewrite (HF s (fun s1 v1 => evalActionPropGen env (cont v1) s1 P)).
    apply evalActionPropGen_ext; intros s1 v1; apply Hcont.
Qed.

Lemma ActionCommutes_IfElse_dep :
  forall {t : Tree DomainElem} {k k' : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (nm : string) (cond : Expr type Bool)
         (aT aF : Action type t k')
         (cont : type k' -> Action type t k),
    (evalExpr cond = true -> @ActionCommutes t k' env f aT) ->
    (evalExpr cond = false -> @ActionCommutes t k' env f aF) ->
    (forall v, @ActionCommutes t k env f (cont v)) ->
    @ActionCommutes t k env f (IfElse nm cond aT aF cont).
Proof.
  intros t k k' env f nm cond aT aF cont HT HF Hcont s P.
  cbn [evalActionPropGen].
  destruct (evalExpr cond) eqn:Hcond.
  - rewrite (HT eq_refl s (fun s1 v1 => evalActionPropGen env (cont v1) s1 P)).
    apply evalActionPropGen_ext; intros s1 v1; apply Hcont.
  - rewrite (HF eq_refl s (fun s1 v1 => evalActionPropGen env (cont v1) s1 P)).
    apply evalActionPropGen_ext; intros s1 v1; apply Hcont.
Qed.

Lemma ActionCommutes_SemAction :
  forall {t : Tree DomainElem} {k : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (act : Action type t k)
         (s s' : TreeState DomainElemState t) (res : type k),
    @ActionCommutes t k env f act ->
    SemAction env act s s' res ->
    SemAction env act (f s) (f s') res.
Proof.
  intros t k env f act s s' res Hcomm Hsem.
  rewrite SemAction_iff_evalActionPropGen in Hsem |- *.
  rewrite (Hcomm s (fun new' ret' => new' = f s' /\ ret' = res)).
  eapply evalActionPropGen_mono; [| exact Hsem].
  intros new' ret' [-> ->]; split; reflexivity.
Qed.

Lemma ActionCommutes_SemAction_inv :
  forall {t : Tree DomainElem} {k : Kind} {env : Env t}
         (f : TreeState DomainElemState t -> TreeState DomainElemState t)
         (act : Action type t k)
         (s s_new : TreeState DomainElemState t) (res : type k),
    @ActionCommutes t k env f act ->
    SemAction env act (f s) s_new res ->
    exists s', s_new = f s' /\ SemAction env act s s' res.
Proof.
  intros t k env f act s s_new res Hcomm Hsem.
  rewrite SemAction_iff_evalActionPropGen in Hsem.
  rewrite (Hcomm s (fun new' ret' => new' = s_new /\ ret' = res)) in Hsem.
  destruct (evalActionPropGen_to_SemAction act s _ Hsem) as [s' [ret' [Hsem' [Hs_new Hret]]]].
  subst ret'; exists s'; split; [symmetry; exact Hs_new | exact Hsem'].
Qed.

Lemma evalActionPropGen_ex_iff :
  forall {t : Tree DomainElem} {env : Env t} {k : Kind} {A : Type}
         (a : Action type t k) (old : TreeState DomainElemState t)
         (f : TreeState DomainElemState t -> A) (s' : A) (v : type k),
    evalActionPropGen env a old (fun m' v0 => f m' = s' /\ v0 = v) <->
    exists m',
      evalActionPropGen env a old (fun new' ret' => new' = m' /\ ret' = v) /\
      s' = f m'.
Proof.
  intros t env k A a old f s' v; split.
  - intros Heval.
    destruct (evalActionPropGen_to_SemAction a old _ Heval)
      as [m' [v0 [Hsem [Hs' Hv0]]]].
    subst s' v0.
    rewrite SemAction_iff_evalActionPropGen in Hsem.
    exists m'; split; [exact Hsem | reflexivity].
  - intros [m' [Heval Hs']].
    subst s'.
    eapply evalActionPropGen_mono; [| exact Heval].
    intros sub' r [Hsub Hr]; subst; split; reflexivity.
Qed.
