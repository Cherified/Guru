From Stdlib Require Import String List ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Theorems Guru.Notations.

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
    | H: ?a = ?a -> _ |- _ => specialize (H eq_refl)
    | H: true = false -> _ |- _ => clear H
    | H: false = true -> _ |- _ => clear H
    end; subst; simpl.

Ltac useOld old := exists Retv, old;
                                split; [auto| split; [|econstructor; eauto; simpl]];
                                repeat match goal with
                                  | H: Prod _ _ |- _ => destruct H
                                  end; simpl in *;
                                constructor; unfold readDiffTupleStr in *; simpl in *; subst; auto; intros;
                                try discriminate.
