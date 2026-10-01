(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String Ascii List Bool Zmod NArith ZArith BinPos Lia.
From Guru Require Import Primitives.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Fixpoint positive_cast (P: positive -> Type) {n m} : n = m -> P n -> P m :=
  match n, m return n = m -> P n -> P m with
  | xH, xH => fun _ v => v
  | xI p1, xI p2 => fun pf => @positive_cast (fun p => P (xI p)) p1 p2 (f_equal (fun v => match v with
                                                                                          | xI q => q
                                                                                          | _ => xH
                                                                                          end) pf)
  | xO p1, xO p2 => fun pf => @positive_cast (fun p => P (xO p)) p1 p2 (f_equal (fun v => match v with
                                                                                          | xO q => q
                                                                                          | _ => xH
                                                                                          end) pf)
  | _, _ => fun pf => ltac:(discriminate)
  end.

Definition Z_cast (P : Z -> Type) {n m} : n = m -> P n -> P m :=
  match n, m return n = m -> P n -> P m with
  | Z0, Z0 => fun _ v => v
  | Zpos p1, Zpos p2 => fun pf => @positive_cast (fun p => P (Zpos p)) p1 p2 (f_equal (fun v => match v with
                                                                                                | Zpos q => q
                                                                                                | _ => xH
                                                                                                end) pf)
  | Zneg p1, Zneg p2 => fun pf => @positive_cast (fun p => P (Zneg p)) p1 p2 (f_equal (fun v => match v with
                                                                                                | Zneg q => q
                                                                                                | _ => xH
                                                                                                end) pf)
  | _, _ => fun pf => ltac:(discriminate)
  end.

Section prod_BoolSpec.
  Variable A B: Type.
  Variable Aeqb: A -> A -> bool.
  Variable A_BoolSpec: forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (Aeqb a1 a2).
  Variable Beqb: B -> B -> bool.
  Variable B_BoolSpec: forall b1 b2, BoolSpec (b1 = b2) (b1 <> b2) (Beqb b1 b2).
  Definition prod_eqb (x y: (A * B)%type) := andb (Aeqb (fst x) (fst y)) (Beqb (snd x) (snd y)).
  Theorem prod_BoolSpec (x y: (A * B)%type): BoolSpec (x = y) (x <> y) (prod_eqb x y).
  Proof.
    destruct x, y.
    specialize (A_BoolSpec a a0).
    specialize (B_BoolSpec b b0).
    unfold prod_eqb, fst, snd.
    destruct A_BoolSpec.
    - destruct B_BoolSpec.
      + constructor.
        subst; auto.
      + constructor.
        intro pf; inversion pf; subst; tauto.
    - constructor 2.
      intro pf; inversion pf; subst; tauto.
  Qed.
End prod_BoolSpec.

Section Prod_BoolSpec.
  Variable A B: Type.
  Variable Aeqb: A -> A -> bool.
  Variable A_BoolSpec: forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (Aeqb a1 a2).
  Variable Beqb: B -> B -> bool.
  Variable B_BoolSpec: forall b1 b2, BoolSpec (b1 = b2) (b1 <> b2) (Beqb b1 b2).
  Definition Prod_eqb (x y: (Prod A B)) := andb (Aeqb x.(Fst) y.(Fst)) (Beqb x.(Snd) y.(Snd)).
  Theorem Prod_BoolSpec (x y: (Prod A B)): BoolSpec (x = y) (x <> y) (Prod_eqb x y).
  Proof.
    destruct x as [Fst0 Snd0], y as [Fst1 Snd1]; simpl.
    specialize (A_BoolSpec Fst0 Fst1).
    specialize (B_BoolSpec Snd0 Snd1).
    unfold Prod_eqb; simpl.
    destruct A_BoolSpec.
    - destruct B_BoolSpec.
      + constructor.
        subst; auto.
      + constructor.
        intro pf; inversion pf; subst; tauto.
    - constructor 2.
      intro pf; inversion pf; subst; tauto.
  Qed.
End Prod_BoolSpec.

Section List_BoolSpec.
  Variable A: Type.
  Variable Aeqb: A -> A -> bool.
  Variable A_BoolSpec: forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (Aeqb a1 a2).
  Theorem list_BoolSpec (x: list A): forall y, BoolSpec (x = y) (x <> y) (list_eqb Aeqb x y).
  Proof.
    induction x; destruct y; intros; simpl; try (constructor; (auto || discriminate)).
    specialize (A_BoolSpec a a0).
    specialize (IHx y).
    destruct A_BoolSpec, IHx; subst; simpl; auto; constructor; auto; intro pf; inversion pf; subst; tauto.
  Qed.
End List_BoolSpec.

Section Nat_BoolSpec.
  Variable n1 n2: nat.
  Theorem Nat_BoolSpec: BoolSpec (n1 = n2) (n1 <> n2) (Nat.eqb n1 n2).
  Proof.
    pose proof (Nat.eqb_spec n1 n2) as pf.
    destruct pf; [subst |]; constructor; [|intro pf2; subst]; auto.
  Qed.
End Nat_BoolSpec.

Section FinTypeHelpers.
  Definition FinType_eqb n (n1 n2: FinType n) := n1.(finNum) =? n2.(finNum).

  Theorem FinType_BoolSpec n: forall (n1 n2: FinType n), BoolSpec (n1 = n2) (n1 <> n2) (FinType_eqb n1 n2).
  Proof.
    intros.
    destruct n1 as [n1 n1Lt], n2 as [n2 n2Lt]; unfold FinType_eqb; simpl.
    pose proof (Nat_BoolSpec n1 n2) as pf.
    destruct pf; [subst |]; constructor; [|intro pf2; subst]; auto.
    - assert (sth: n1Lt = n2Lt). {
        destruct (n2 <? n); [|contradiction].
        destruct n1Lt, n2Lt.
        reflexivity.
      }
      subst.
      reflexivity.
    - inversion pf2; subst; auto.
  Qed.

  Fixpoint m_ltb_n_S_n n : forall m, Is_true (m <? n) -> Is_true (m <? S n) :=
    match n return forall m, Is_true (m <? n) -> Is_true (m <? S n) with
    | 0 => fun _ pf => match pf with end
    | S k => fun m => match m return Is_true (m <? S k) -> Is_true (m <? S (S k)) with
                      | 0 => fun _ => I
                      | S l => fun pf => @m_ltb_n_S_n k l pf
                      end
    end.

  Fixpoint genFinType n: list (FinType n) :=
    match n return list (FinType n) with
    | 0 => nil
    | S m => Build_FinType 0 (I: Is_true (0 <? S m)) ::
               map (fun x => @Build_FinType (S m) (S x.(finNum)) x.(finLt)) (genFinType m)
    end.

  Theorem genFinType_length n: length (genFinType n) = n.
  Proof.
    induction n; auto; simpl.
    rewrite length_map.
    auto.
  Qed.
End FinTypeHelpers.

Theorem string_eqb_spec s1 s2: BoolSpec (s1 = s2) (s1 <> s2) (String.eqb s1 s2).
Proof.
  destruct (String.eqb_spec s1 s2); constructor; auto.
Qed.

Section Kind_BoolSpec.
  Fixpoint Kind_eqb (k1 k2: Kind): bool :=
    match k1, k2 return bool with
    | Bool, Bool => true
    | Bit n, Bit m => Z.eqb n m
    | Struct ls1, Struct ls2 => list_eqb (prod_eqb String.eqb Kind_eqb) ls1 ls2
    | Array n1 k1, Array n2 k2 => andb (Nat.eqb n1 n2) (Kind_eqb k1 k2)
    | TaggedUnion ls1, TaggedUnion ls2 => list_eqb (prod_eqb String.eqb Kind_eqb) ls1 ls2
    | _, _ => false
    end.
  Theorem Kind_BoolSpec k1: forall k2, BoolSpec (k1 = k2) (k1 <> k2) (Kind_eqb k1 k2).
  Proof.
    induction k1 using KindCustomInd; destruct k2; simpl; try (constructor; auto; discriminate).
    - destruct (Z.eqb_spec n z).
      + subst.
        constructor; auto.
      + constructor; intro pf; inversion pf; auto.
    - generalize l X. clear.
      induction ls; destruct l; simpl; auto; intros; try (constructor; (auto || discriminate)).
      destruct X as (elem, rest).
      specialize (IHls l rest).
      destruct a, p; unfold prod_eqb at 1; simpl in *.
      specialize (elem k0).
      destruct (string_eqb_spec s s0); subst; simpl; auto.
      + destruct IHls, elem; simpl; constructor; subst; try inversion H;
          subst; auto; try intro pf; inversion pf; subst; auto.
      + constructor; intro pf; inversion pf; subst; auto.
    - destruct (Nat.eqb_spec n n0); subst; simpl; auto.
      + destruct (IHk1 k2); constructor; subst; auto.
        intro pf; inversion pf; subst; auto.
      + constructor; intro pf; inversion pf; subst; auto.
    - generalize l X. clear.
      induction ls; destruct l; simpl; auto; intros; try (constructor; (auto || discriminate)).
      destruct X as (elem, rest).
      specialize (IHls l rest).
      destruct a, p; unfold prod_eqb at 1; simpl in *.
      specialize (elem k0).
      destruct (string_eqb_spec s s0); subst; simpl; auto.
      + destruct IHls, elem; simpl; constructor; subst; try inversion H;
          subst; auto; try intro pf; inversion pf; subst; auto.
      + constructor; intro pf; inversion pf; subst; auto.
  Qed.
End Kind_BoolSpec.

Section SameTupleBoolSpec.
  Variable A: Type.
  Variable Aeq: A -> A -> bool.
  Variable Aeq_spec: forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (Aeq a1 a2).

  Theorem SameTuple_eqb_spec n: forall (t1 t2: SameTuple A n),
      BoolSpec (t1 = t2) (t1 <> t2) (list_eqb Aeq t1.(tupleElems) t2.(tupleElems)).
  Proof.
    induction n; simpl; auto; intros.
    - destruct t1 as [tupleElems0 tupleSize0], t2 as [tupleElems1 tupleSize1]; simpl in *.
      destruct tupleElems0, tupleElems1; simpl in *; destruct tupleSize0, tupleSize1; try constructor; auto.
    - destruct t1 as [tupleElems0 tupleSize0], t2 as [tupleElems1 tupleSize1]; simpl in *.
      destruct tupleElems0; [contradiction|].
      destruct tupleElems1; [contradiction|].
      simpl in *.
      specialize (IHn (@Build_SameTuple _ _ tupleElems0 tupleSize0)
                    (@Build_SameTuple _ _ tupleElems1 tupleSize1)).
      specialize (Aeq_spec a a0).
      unfold Is_true in *.
      destruct Aeq_spec.
      + subst.
        simpl in *.
        destruct IHn.
        * constructor.
          inversion H; subst.
          assert (sth: tupleSize0 = tupleSize1). {
            clear.
            destruct (length tupleElems1 =? n), tupleSize0, tupleSize1.
            auto.
          }
          subst.
          reflexivity.
        * constructor.
          intro pf.
          inversion pf.
          subst.
          assert (sth: tupleSize0 = tupleSize1). {
            clear.
            destruct (length tupleElems1 =? n), tupleSize0, tupleSize1.
            auto.
          }
          subst.
          auto.
      + constructor.
        intro pf; inversion pf; subst; auto.
  Qed.
End SameTupleBoolSpec.

Theorem bool_eqb_spec b1 b2: BoolSpec (b1 = b2) (b1 <> b2) (Bool.eqb b1 b2).
Proof.
  destruct (Bool.eqb_spec b1 b2); constructor; auto.
Qed.

Section IsEq_BoolSpec.
  Theorem isEq_BoolSpec k: forall e1 e2, BoolSpec (e1 = e2) (e1 <> e2) (@isEq k e1 e2).
  Proof.
    induction k using KindCustomInd; auto.
    - apply bool_eqb_spec.
    - apply Zmod.eqb_spec.
    - induction ls.
      + constructor; destruct e1, e2; auto.
      + intros e1 e2.
        destruct X as [curr rest].
        specialize (IHls rest e1.(Snd) e2.(Snd)).
        specialize (curr e1.(Fst) e2.(Fst)).
        destruct a, e1 as [e1_f e1_s], e2 as [e2_f e2_s]; unfold Fst, Snd in *.
        simpl in *.
        destruct curr, IHls; subst; simpl; try (constructor; auto; intro pf; inversion pf; auto).
    - intros.
      unfold isEq; fold (@isEq k).
      apply (SameTuple_eqb_spec IHk).
    - intros.
      destruct e1 as [f1 s1], e2 as [f2 s2]; unfold Fst, Snd in *; simpl in *.
      destruct (Zmod.eqb_spec f1 f2), (Zmod.eqb_spec s1 s2); simpl; constructor; subst;
        try (constructor; auto); try (intro pf; inversion pf; auto).
  Qed.
End IsEq_BoolSpec.

Section ForceOption.
  Variable A: Type.
  Definition forceOption (o : option A) : match o with
                                          | Some _ => A
                                          | None => unit
                                          end :=
    match o with
    | Some a => a
    | None => tt
    end.
End ForceOption.

Section FinStructLookup.
  Variable K: Type.

  Fixpoint getFinStructOption (s: string) (ls: list (string * K)): option (FinStruct ls) :=
    match ls with
    | nil => None
    | x :: xs => match String.eqb s (fst x) return option (FinStruct (_ :: xs)) with
                 | true => Some (@Build_FinType (length (x :: xs)) 0 I)
                 | false => match getFinStructOption s xs return option (FinStruct (_ :: xs)) with
                            | None => None
                            | Some (Build_FinType i pf) => Some (@Build_FinType (length (x :: xs)) (S i) pf)
                            end
                 end
    end.

  Definition getFinStruct s ls := forceOption (getFinStructOption s ls).
End FinStructLookup.

Lemma Z_of_nat_S n : Z.of_nat (S n) = (1 + Z.of_nat n)%Z.
Proof.
  lia.
Qed.

Lemma NatZ_mul_mult n w : NatZ_mul n w = (Z.of_nat n * w)%Z.
Proof.
  induction n.
  - simpl; lia.
  - rewrite Z_of_nat_S.
    change (NatZ_mul (S n) w) with (w + NatZ_mul n w)%Z.
    rewrite IHn.
    ring.
Qed.

Lemma NatZ_mul_n_1 n: NatZ_mul n 1 = Z.of_nat n.
Proof.
  rewrite NatZ_mul_mult.
  rewrite Z.mul_1_r.
  auto.
Qed.

Section fieldK_repeat.
  Variable K: Type.
  Variable sk: (string * K).
  Lemma fieldK_repeat n : forall i: FinStruct (repeat sk n), fieldK i = snd sk.
  Proof.
    induction n; simpl; auto; intros; destruct i as [finNum0 finLt0].
    - contradiction.
    - destruct finNum0.
      + reflexivity.
      + specialize (IHn (Build_FinType finNum0 finLt0)).
        apply IHn.
  Qed.
End fieldK_repeat.

Section ReadDiffTuple.
  Variable K: Type.
  Variable Convert: (string * K) -> Type.
  Variable ls: list (string * K).
  Variable dt: DiffTuple Convert ls.
  Variable s: string.

  Definition readDiffTupleStr :=
    match getFinStructOption s ls as x return match x with
                                              | Some p => Convert (nth_pf (ls:=ls) (i:=finNum p) (finLt p))
                                              | None => unit
                                              end with
    | Some p => readDiffTuple dt p
    | None => tt
    end.
End ReadDiffTuple.

Section TreeOps.
  Variable A: Type.

  Fixpoint NodeChildren (t: Tree A) : Type :=
    match t with
    | Leaf _ _ => Empty_set
    | Node _ children =>
        (fix loop (ls: list (Tree A)) : Type :=
           match ls with
           | nil => Empty_set
           | x :: xs => ((unit + NodeChildren x) + loop xs)%type
           end) children
    end.

  Definition NodePath (t: Tree A) : Type :=
    (unit + NodeChildren t)%type.

  Fixpoint leaf_list_path_seq (f : nat -> Tree A) (default_path : forall k, LeafPath (f k))
    (start n : nat) (p : FinType n) :
    (fix loop (ls : list (Tree A)) : Type :=
       match ls with
       | nil => Empty_set
       | x :: xs => (LeafPath x + loop xs)%type
       end) (map f (seq start n)) :=
    match n return forall (p : FinType n),
      (fix loop (ls : list (Tree A)) : Type :=
         match ls with
         | nil => Empty_set
         | x :: xs => (LeafPath x + loop xs)%type
         end) (map f (seq start n)) with
    | O => fun p => match (Nat_ltb_0 p.(finLt)) with end
    | S m => fun p =>
        match p.(finNum) as inum return forall pf : Is_true (inum <? S m)%nat,
          (fix loop (ls : list (Tree A)) : Type :=
             match ls with
             | nil => Empty_set
             | x :: xs => (LeafPath x + loop xs)%type
             end) (map f (seq start (S m))) with
        | O => fun _ => inl (default_path start)
        | S k => fun pf => inr (@leaf_list_path_seq f default_path (S start) m (Build_FinType k pf))
        end p.(finLt)
    end p.

  Lemma getLeaf_seq (nodeName : string) (f : nat -> Tree A) (default_path : forall k, LeafPath (f k))
    (start n : nat) (i : FinType n) :
    @getLeaf A (Node nodeName (map f (seq start n))) (@leaf_list_path_seq f default_path start n i) =
    @getLeaf A (f (start + i.(finNum))%nat) (default_path (start + i.(finNum))%nat).
  Proof.
    revert start.
    induction n; intros start.
    - destruct i as [inum ilt].
      destruct (Nat_ltb_0 ilt).
    - destruct i as [inum ilt].
      simpl.
      destruct inum.
      + rewrite Nat.add_0_r. reflexivity.
      + simpl.
        pose proof (IHn (Build_FinType inum ilt) (S start)) as H.
        simpl in H.
        rewrite H.
        rewrite Nat.add_succ_r.
        reflexivity.
  Qed.

  Fixpoint repeat_eq_map_seq {B} (x : B) (start n : nat) :
    repeat x n = map (fun _ => x) (seq start n) :=
    match n with
    | O => eq_refl
    | S m => f_equal (cons x) (repeat_eq_map_seq x (S start) m)
    end.

  Definition leaf_list_path_repeat (t: Tree A) (default_path: LeafPath t) (n: nat) (p: FinType n) :
    (fix loop (ls: list (Tree A)) : Type :=
       match ls with
       | nil => Empty_set
       | x :: xs => (LeafPath x + loop xs)%type
       end) (repeat t n) :=
    match eq_sym (repeat_eq_map_seq t 0 n) in _ = Y return
      (fix loop (ls: list (Tree A)) : Type :=
         match ls with
         | nil => Empty_set
         | x :: xs => (LeafPath x + loop xs)%type
         end) Y with
    | eq_refl => @leaf_list_path_seq (fun _ => t) (fun _ => default_path) 0 n p
    end.

  Lemma getLeaf_repeat (nodeName: string) (t: Tree A) (default_path: LeafPath t) n (i: FinType n) :
    @getLeaf A (Node nodeName (repeat t n)) (leaf_list_path_repeat default_path i) = getLeaf default_path.
  Proof.
    unfold leaf_list_path_repeat.
    pose proof (@getLeaf_seq nodeName (fun _ => t) (fun _ => default_path) 0 n i) as H.
    destruct (eq_sym (repeat_eq_map_seq t 0 n)).
    exact H.
  Qed.

  Fixpoint getTreePaths (t: Tree A) : list (LeafPath t) :=
    match t return list (LeafPath t) with
    | Leaf _ _ => tt :: nil
    | Node _ children =>
        (fix loop (ls: list (Tree A)) : list (LeafPath (Node "" ls)) :=
           match ls return list (LeafPath (Node "" ls)) with
           | nil => nil
           | x :: xs => (map inl (getTreePaths x)) ++ (map inr (loop xs))
           end) children
    end.

  Fixpoint NodePathList (ls: list (Tree A)) : Type :=
    match ls with
    | nil => Empty_set
    | x :: xs => (NodePath x + NodePathList xs)%type
    end.

  Fixpoint getNodeChildren {t : Tree A} : NodeChildren t -> Tree A :=
    match t return NodeChildren t -> Tree A with
    | Leaf _ _ => fun empty => match empty with end
    | Node _ children =>
        (fix loop (ls: list (Tree A)) : NodePathList ls -> Tree A :=
           match ls return NodePathList ls -> Tree A with
           | nil => fun empty => match empty with end
           | x :: xs => fun p_sum =>
               match p_sum with
               | inl p_x =>
                   match p_x with
                   | inl _ => x
                   | inr p_child => getNodeChildren p_child
                   end
               | inr p_xs => loop xs p_xs
               end
           end) children
    end.

  Definition getNode {t : Tree A} (p : NodePath t) : Tree A :=
    match p with
    | inl _ => t
    | inr p_children => getNodeChildren p_children
    end.

  Fixpoint LeafPathList (ls: list (Tree A)) : Type :=
    match ls with
    | nil => Empty_set
    | x :: xs => (LeafPath x + LeafPathList xs)%type
    end.

  Fixpoint embedLeafIntoPath_child {t : Tree A} :
    forall (p_child : NodeChildren t), LeafPath (getNodeChildren p_child) -> LeafPath t :=
    match t return forall (p_child : NodeChildren t), LeafPath (getNodeChildren p_child) -> LeafPath t with
    | Leaf _ _ => fun empty => match empty with end
    | Node name children =>
        (fix loop (ls : list (Tree A)) :
           forall (p_list : NodePathList ls),
             LeafPath ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
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
               LeafPathList ls :=
           match ls return
             forall (p_list : NodePathList ls),
               LeafPath ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
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
                 LeafPathList ls
           with
           | nil => fun empty => match empty with end
           | x :: xs => fun p_list =>
               match p_list as p_list_ return
                 LeafPath (match p_list_ with
                           | inl p_x =>
                               match p_x with
                               | inl _ => x
                               | inr p_child => getNodeChildren p_child
                               end
                           | inr p_xs => _
                           end) ->
                 (LeafPath x + LeafPathList xs)%type
               with
               | inl p_x =>
                   match p_x as p_x_ return
                     LeafPath (match p_x_ with
                               | inl _ => x
                               | inr p_child => getNodeChildren p_child
                               end) ->
                     (LeafPath x + LeafPathList xs)%type
                   with
                   | inl _ => fun p_local => inl p_local
                   | inr p_child => fun p_local => inl (@embedLeafIntoPath_child x p_child p_local)
                   end
               | inr p_xs => fun p_local => inr (loop xs p_xs p_local)
               end
           end) children
    end.

  Definition embedLeafIntoPath {t : Tree A} (p : NodePath t) : LeafPath (getNode p) -> LeafPath t :=
    match p as p_ return LeafPath (getNode p_) -> LeafPath t with
    | inl _ => fun p_local => p_local
    | inr p_child => fun p_local => @embedLeafIntoPath_child t p_child p_local
    end.

  Fixpoint embedNodeIntoPath_child {t : Tree A} :
    forall (p_child : NodeChildren t), NodePath (getNodeChildren p_child) -> NodeChildren t :=
    match t return forall (p_child : NodeChildren t), NodePath (getNodeChildren p_child) -> NodeChildren t with
    | Leaf _ _ => fun empty => match empty with end
    | Node name children =>
        (fix loop (ls : list (Tree A)) :
           forall (p_list : NodePathList ls),
             NodePath ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
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
               NodePathList ls :=
           match ls return
             forall (p_list : NodePathList ls),
               NodePath ((fix loop_node (l : list (Tree A)) : NodePathList l -> Tree A :=
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
                 NodePathList ls
           with
           | nil => fun empty => match empty with end
           | x :: xs => fun p_list =>
               match p_list as p_list_ return
                 NodePath (match p_list_ with
                           | inl p_x =>
                               match p_x with
                               | inl _ => x
                               | inr p_child => getNodeChildren p_child
                               end
                           | inr p_xs => _
                           end) ->
                 (NodePath x + NodePathList xs)%type
               with
               | inl p_x =>
                   match p_x as p_x_ return
                     NodePath (match p_x_ with
                               | inl _ => x
                               | inr p_child => getNodeChildren p_child
                               end) ->
                     (NodePath x + NodePathList xs)%type
                   with
                   | inl _ => fun p_local => inl p_local
                   | inr p_child => fun p_local => inl (inr (@embedNodeIntoPath_child x p_child p_local))
                   end
               | inr p_xs => fun p_local => inr (loop xs p_xs p_local)
               end
           end) children
    end.

  Definition embedNodeIntoPath {t : Tree A} (p : NodePath t) : NodePath (getNode p) -> NodePath t :=
    match p as p_ return NodePath (getNode p_) -> NodePath t with
    | inl _ => fun p_inner => p_inner
    | inr p_child => fun p_inner => inr (@embedNodeIntoPath_child t p_child p_inner)
    end.

  Fixpoint solveNodePath (t : Tree A) (path_lst : list string) : option (NodePath t) :=
    match path_lst with
    | nil => Some (inl tt)
    | x :: xs =>
        match t return option (NodePath t) with
        | Leaf name _ =>
            if String.eqb x name then
              match xs with
              | nil => Some (inl tt)
              | _ => None
              end
            else None
        | Node name children =>
            if String.eqb x name then
              match xs with
              | nil => Some (inl tt)
              | _ =>
                  let fix loop (ls : list (Tree A)) : option (NodePathList ls) :=
                    match ls return option (NodePathList ls) with
                    | nil => None
                    | c :: cs =>
                        match solveNodePath c xs with
                        | Some p_c => Some (inl p_c)
                        | None =>
                            match loop cs with
                            | Some p_cs => Some (inr p_cs)
                            | None => None
                            end
                        end
                    end
                  in
                  match loop children with
                  | Some p_children => Some (inr p_children)
                  | None => None
                  end
              end
            else None
        end
    end.
End TreeOps.

Arguments NodeChildren [A] t.
Arguments NodePath [A] t.
Arguments NodePathList [A] ls.
Arguments getNode [A] [t] p.
Arguments embedLeafIntoPath [A] [t] p p_local.
Arguments embedNodeIntoPath [A] [t] p p_inner.
Arguments solveNodePath [A] t path_lst.
Arguments leaf_list_path_seq [A] f default_path start [n] p.
Arguments getLeaf_seq [A] nodeName f default_path start [n] i.
Arguments leaf_list_path_repeat [A] t default_path [n] p.
Arguments getLeaf_repeat [A] nodeName [t] default_path [n] i.
Arguments getTreePaths [A] t.

Fixpoint reverseStringHelper (s : string) (acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => reverseStringHelper s' (String c acc)
  end.

Definition reverseString (s : string) : string :=
  reverseStringHelper s EmptyString.

Fixpoint splitStringHelper (delim : ascii) (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => reverseString acc :: nil
  | String c s' =>
      if Ascii.eqb c delim then
        reverseString acc :: splitStringHelper delim s' EmptyString
      else
        splitStringHelper delim s' (String c acc)
  end.

Definition splitString (delim : ascii) (s : string) : list string :=
  splitStringHelper delim s EmptyString.

Delimit Scope char_scope with ascii.

Definition splitDot (s : string) : list string :=
  splitString "."%ascii s.

Definition hex_char (b0 b1 b2 b3 : bool) : ascii :=
  match b3, b2, b1, b0 with
  | false, false, false, false => "0"%ascii
  | false, false, false, true  => "1"%ascii
  | false, false, true,  false => "2"%ascii
  | false, false, true,  true  => "3"%ascii
  | false, true,  false, false => "4"%ascii
  | false, true,  false, true  => "5"%ascii
  | false, true,  true,  false => "6"%ascii
  | false, true,  true,  true  => "7"%ascii
  | true,  false, false, false => "8"%ascii
  | true,  false, false, true  => "9"%ascii
  | true,  false, true,  false => "a"%ascii
  | true,  false, true,  true  => "b"%ascii
  | true,  true,  false, false => "c"%ascii
  | true,  true,  false, true  => "d"%ascii
  | true,  true,  true,  false => "e"%ascii
  | true,  true,  true,  true  => "f"%ascii
  end.

Fixpoint pos_to_bits (p : positive) : list bool :=
  match p with
  | xH    => true :: nil
  | xO p' => false :: pos_to_bits p'
  | xI p' => true  :: pos_to_bits p'
  end.

Fixpoint bits_to_hex (l : list bool) : string :=
  match l with
  | nil => EmptyString
  | b0 :: nil => String (hex_char b0 false false false) EmptyString
  | b0 :: b1 :: nil => String (hex_char b0 b1 false false) EmptyString
  | b0 :: b1 :: b2 :: nil => String (hex_char b0 b1 b2 false) EmptyString
  | b0 :: b1 :: b2 :: b3 :: rest =>
      (bits_to_hex rest ++ String (hex_char b0 b1 b2 b3) EmptyString)%string
  end.

Definition hex_string_of_Z (z : Z) : string :=
  match z with
  | Z0 => "0"%string
  | Zpos p => bits_to_hex (pos_to_bits p)
  | Zneg _ => "0"%string
  end.

Definition getNodePath {A: Type} (t : Tree A) (path : string) :=
  forceOption (solveNodePath t (splitDot path)).

Definition singletonChildPath {A: Type} {name: string} {t: Tree A} : NodePath (Node name (t :: nil)) :=
  inr (inl (inl tt)).

Arguments singletonChildPath {A name t}.

Fixpoint sumUnit n : Type :=
  match n with
  | 0 => Empty_set
  | S m => unit + sumUnit m
  end.

Fixpoint sumUnit_to_FinType (n : nat) : sumUnit n -> FinType n :=
  match n return sumUnit n -> FinType n with
  | 0 => fun s => match s with end
  | S m => fun s =>
      match s with
      | inl tt => Build_FinType 0 (I : Is_true (0 <? S m)%nat)
      | inr s' =>
          match sumUnit_to_FinType s' return FinType (S m) with
          | Build_FinType inum ilt => @Build_FinType (S m) (S inum) ilt
          end
      end
  end.

Fixpoint FinType_to_sumUnit (n : nat) : FinType n -> sumUnit n :=
  match n return FinType n -> sumUnit n with
  | 0 => fun p => match (Nat_ltb_0 p.(finLt)) with end
  | S m => fun p =>
      match p.(finNum) as inum return Is_true (inum <? S m)%nat -> sumUnit (S m) with
      | 0 => fun _ => inl tt
      | S k => fun pf => inr (FinType_to_sumUnit (Build_FinType k pf))
      end p.(finLt)
  end.

Fixpoint rev_tail {A : Type} (l acc : list A) : list A :=
  match l with
  | nil => acc
  | x :: xs => rev_tail xs (x :: acc)
  end.

Lemma rev_tail_rev : forall A (l acc : list A),
  rev_tail l acc = rev l ++ acc.
Proof.
  induction l; intros.
  - reflexivity.
  - cbn. rewrite IHl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rev_tail_fast : forall A (l : list A),
  rev_tail l nil = rev l.
Proof.
  intros. rewrite rev_tail_rev. rewrite app_nil_r. reflexivity.
Qed.
