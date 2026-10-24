(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Semantics Theorems HelperLemmas Notations.

Ltac simplifyHyps stateRel :=
  repeat match goal with
    | H: stateRel _ _ |- _ => destruct H
    | H: InitStateConsistent _ _ |- _ => simpl in H
    | H: TreeState DomainElemState (Leaf _ _) |- _ => simpl in H
    | H: TreeState DomainElemState _ |- _ => destruct H
    | H: _ ** _ |- _ => destruct H
    | H: exists _, _ |- _ => destruct H
    | H: unit |- _ => clear H
    | H: _ /\ _ |- _ => destruct H
    end;
  simpl in *;
  repeat (
    match goal with
    | H: @Build_Prod _ _ ?x ?y = @Build_Prod _ _ ?a ?b |- _ =>
        injection H; clear H; intros
    end;
    subst
  );
  subst.

Lemma simulateAction_evalActionPropGen :
  forall {t2 : Tree DomainElem} (env2 : Env t2)
         (Pin : Prop) (a2 : @Action type t2 (Bit 0))
         (old2 : TreeState DomainElemState t2)
         (Q : TreeState DomainElemState t2 -> Prop),
    Pin ->
    evalActionPropGen env2 a2 old2 (fun new2 _ => Q new2) ->
    exists new2, Pin /\ SemAction env2 a2 old2 new2 Zmod.zero /\ Q new2.
Proof.
  intros t2 env2 Pin a2 old2 Q HPin Heval.
  destruct (evalActionPropGen_to_SemAction env2 a2 old2 _ Heval) as [new2 [ret [Hsem HQ]]].
  exists new2.
  rewrite (Zmod_1_0 ret) in Hsem.
  exact (conj HPin (conj Hsem HQ)).
Qed.

Ltac simulateAction specAction :=
  exists specAction;
  match goal with
  | |- exists _, ?Pin /\ @SemAction ?t2 ?env2 _ ?a2 ?old2 _ _ /\ _ =>
      eapply (@simulateAction_evalActionPropGen t2 env2 Pin a2 old2)
  end;
  [ simpl; auto
  | match goal with
    | |- evalActionPropGen ?env2 ?a ?old2 ?P =>
        let a' := eval hnf in a in
        change (evalActionPropGen env2 a' old2 P);
        cbn [evalActionPropGen]
    end;
    repeat match goal with
    | Hinh: EnvInhabited ?env2 |- exists recvVal, ?env2 ?s2 ?x recvVal /\ _ =>
        let val := fresh "recvVal" in
        let Henv2 := fresh "Henv" in
        destruct (Hinh s2 x) as [val Henv2];
        exists val; split; [exact Henv2 | cbn [evalActionPropGen]]
    end;
    constructor; simpl; auto ].

Ltac simulateRetv t :=
  simulateAction (@Return type t (Bit 0) ConstDef).

Ltac invertAction :=
  repeat match goal with
    | H: SemAction _ _ _ _ _ |- _ =>
        apply InversionActionPropGen in H;
        cbn [evalActionPropGen] in H
    | H: if ?c then _ else _ |- _ => destruct c eqn:?
    | H: exists _, _ |- _ => destruct H
    | H: _ /\ _ |- _ => destruct H
    | H: ?P = true -> SemAction _ _ _ _ _ |- _ => destruct P eqn:?
    | H: ?P = false -> SemAction _ _ _ _ _ |- _ => destruct P eqn:?
    | H: ?a = ?a -> _ |- _ => specialize (H eq_refl)
    | H: true = false -> _ |- _ => clear H
    | H: false = true -> _ |- _ => clear H
    end.

Ltac destructActionInList impl :=
  unfold impl in *;
  repeat match goal with
    | H: In ?a _ |- _ =>
        match type of a with
        | @Action _ _ _ => simpl map in H; destruct H; try discriminate; subst
        end
    end.
