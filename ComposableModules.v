From Stdlib Require Import List String Zmod.
Import ListNotations.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Theorems.
From Stdlib Require Import Program.Equality.

Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive ModuleType : Type :=
| MkMod : ModuleType
| MkMeth (K_in K_out : Kind) : ModuleType
| BindMod (B : ModuleType) : ModuleType
| BindMeth (K_in K_out : Kind) (B : ModuleType) : ModuleType.

Fixpoint ModuleSem (mt : ModuleType) (t_acc : Tree Elem) (t_curr : Tree Elem) : Type :=
  match mt with
  | MkMod => Mod t_acc
  | MkMeth K_in K_out => type K_in -> Action type t_curr K_out
  | BindMod B => forall (t_new : Tree Elem), Mod t_new -> ModuleSem B (Node "" [t_acc; t_new]) t_new
  | BindMeth K_in K_out B => (type K_in -> Action type t_curr K_out) -> ModuleSem B t_acc t_curr
  end.

Definition MethSimulation {t1 t2: Tree Elem} {K_in K_out: Kind}
  (M1: type K_in -> Action type t1 K_out) (M2: type K_in -> Action type t2 K_out)
  (rel: TreeState ElemState t1 -> TreeState ElemState t2 -> Prop) : Prop :=
  forall (v_in : type K_in),
    ActionSimulation (M1 v_in) (M2 v_in) rel.

Fixpoint Simulation (mt : ModuleType)
                     (t_acc1 t_acc2 : Tree Elem)
                     (rel_acc : TreeState ElemState t_acc1 -> TreeState ElemState t_acc2 -> Prop)
                     (t_curr1 t_curr2 : Tree Elem)
                     (rel_curr : TreeState ElemState t_curr1 -> TreeState ElemState t_curr2 -> Prop)
                     (m1 : ModuleSem mt t_acc1 t_curr1) (m2 : ModuleSem mt t_acc2 t_curr2) : Prop :=
  match mt as mt0 return ModuleSem mt0 t_acc1 t_curr1 -> ModuleSem mt0 t_acc2 t_curr2 -> Prop with
  | MkMod => fun m1 m2 =>
      ModSimulation m1 m2 rel_acc
  | MkMeth K_in K_out => fun m1 m2 =>
      MethSimulation m1 m2 rel_curr
  | BindMod B => fun F1 F2 =>
      forall (t_new1 t_new2 : Tree Elem)
             (m1_in : Mod t_new1)
             (m2_in : Mod t_new2)
             (rel_new : TreeState ElemState t_new1 -> TreeState ElemState t_new2 -> Prop),
        ModSimulation m1_in m2_in rel_new ->
        Simulation B (Node "" [t_acc1; t_new1]) (Node "" [t_acc2; t_new2])
            (fun s1 s2 => rel_acc s1.(Fst) s2.(Fst) /\ rel_new s1.(Snd).(Fst) s2.(Snd).(Fst))
            t_new1 t_new2
            rel_new
            (F1 t_new1 m1_in)
            (F2 t_new2 m2_in)
  | BindMeth K_in K_out B => fun F1 F2 =>
      forall (M1 : type K_in -> Action type t_curr1 K_out) (M2 : type K_in -> Action type t_curr2 K_out),
        MethSimulation M1 M2 rel_curr ->
        Simulation B t_acc1 t_acc2 rel_acc t_curr1 t_curr2 rel_curr (F1 M1) (F2 M2)
  end m1 m2.
