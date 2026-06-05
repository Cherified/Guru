From Stdlib Require Import String List ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Theorems Guru.Notations.

Ltac simplifyHyps stateRel :=
  repeat match goal with
    | H: stateRel _ _ |- _ => destruct H
    | H: InitStateConsistent _ _ |- _ => simpl in H
    | H: TreeState ElemState (Leaf _ _) |- _ => simpl in H
    | H: TreeState ElemState _ |- _ => destruct H
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

Ltac simulateStep specAction :=
  exists specAction;
  eexists;
  split; [simpl; auto | split; [ repeat econstructor; eauto | constructor; simpl; auto ]].

Ltac simulateRetv t :=
  simulateStep (@Return type t (Bit 0) ConstDef).

Ltac invertAction :=
  repeat match goal with
    | H: SemAction _ _ _ _ |- _ => apply InversionSemAction in H
    | H: exists _, _ |- _ => destruct H
    | H: _ /\ _ |- _ => destruct H
    | H: ?P = true -> SemAction _ _ _ _ |- _ => destruct P eqn:?
    | H: ?P = false -> SemAction _ _ _ _ |- _ => destruct P eqn:?
    | H: ?a = ?a -> _ |- _ => specialize (H eq_refl)
    | H: true = false -> _ |- _ => clear H
    | H: false = true -> _ |- _ => clear H
    end.

Ltac destructActionInList impl :=
  unfold impl in *;
  repeat match goal with
    | H: In ?a _ |- _ =>
        match type of a with
        | @Action _ _ _ => destruct H; try discriminate; subst
        end
    end.
