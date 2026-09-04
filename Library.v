From Stdlib Require Import String Ascii List Bool Zmod NArith ZArith BinPos.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Theorem Nat_ltb_0 n: Is_true (n <? 0) -> False.
Proof.
  case_eq (n <? 0); intros; auto.
  rewrite Nat.ltb_lt in H.
  lia.
Qed.

Theorem Is_true_Nat_eq_implies n m: n = m -> Is_true (n =? m).
Proof.
  intros; subst.
  rewrite Nat.eqb_refl.
  apply I.
Qed.

Theorem Is_true_Nat_eqb_implies n m: Is_true (n =? m) -> n = m.
Proof.
  intros H.
  apply Is_true_eq_true in H.
  apply Nat.eqb_eq; auto.
Qed.

Theorem Is_true_Nat_eqb_ltb_implies n m i: Is_true (m =? n) -> Is_true (i <? n) -> Is_true (i <? m).
Proof.
  intros pf1 pf2.
  apply Is_true_Nat_eqb_implies in pf1.
  subst.
  auto.
Qed.

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

#[projections(primitive)]
Record Prod (A B : Type) : Type := {
  Fst : A;
  Snd : B
}.

#[global] Notation "A ** B" := (Prod A B) (at level 40, left associativity) : type_scope.
#[global] Notation "( a ,, b )" := (Build_Prod a b).

Inductive Kind :=
| Bool   : Kind
| Bit    : Z -> Kind
| Struct : list (string * Kind) -> Kind
| Array  : nat -> Kind -> Kind
| TaggedUnion : list (string * Kind) -> Kind.

Fixpoint max_list (ls: list Z) : Z :=
  match ls with
  | nil => 0%Z
  | x :: xs => Z.max x (max_list xs)
  end.

Fixpoint NatZ_mul n (k: Z): Z :=
  match n with
  | 0 => 0%Z
  | S m => (k + NatZ_mul m k)%Z
  end.

Fixpoint kindSize (k: Kind): Z :=
  match k with
  | Bool => 1%Z
  | Bit n => n
  | Struct ls => (let fix help xs :=
                    match xs with
                    | nil => 0%Z
                    | x :: xs => (help xs + kindSize (snd x))%Z
                    end in help ls)
  | Array n k => NatZ_mul n (kindSize k)
  | TaggedUnion ls => (Z.log2_up (Z.of_nat (length ls)) + max_list (map (fun x => kindSize (snd x)) ls))%Z
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
    destruct x, y; simpl.
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
  Fixpoint list_eqb (ls1 ls2: list A): bool :=
    match ls1, ls2 with
    | nil, nil => true
    | x :: xs, y :: ys => andb (Aeqb x y) (list_eqb xs ys)
    | _, _ => false
    end.
  Theorem list_BoolSpec (x: list A): forall y, BoolSpec (x = y) (x <> y) (list_eqb x y).
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

Section FinType.
  #[projections(primitive)]
  Record FinType (n: nat) := { finNum: nat;
                               finLt: Is_true (finNum <? n) }.
  #[global] Add Printing Constructor FinType.

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
    | S m => Build_FinType (finNum := 0) (I: Is_true (0 <? S m)) ::
               map (fun x => @Build_FinType (S m) (S x.(finNum)) x.(finLt)) (genFinType m)
    end.

  Theorem genFinType_length n: length (genFinType n) = n.
  Proof.
    induction n; auto; simpl.
    rewrite length_map.
    auto.
  Defined.
End FinType.
Arguments Build_FinType [n]%_nat_scope finNum%_nat_scope finLt.

Section Nth_pf.
  Variable A: Type.

  Fixpoint nth_pf (ls: list A): forall i, Is_true (i <? length ls) -> A :=
    match ls return forall i, Is_true (i <? length ls) -> A with
    | nil => fun i pf => match Nat_ltb_0 pf with end
    | x :: xs => fun i => match i return Is_true (i <? length (x :: xs)) -> A with
                          | 0 => fun _ => x
                          | S m => fun pf => @nth_pf xs m pf
                          end
    end.
End Nth_pf.

Section DiffTuple.
  Variable A: Type.
  Variable Convert: A -> Type.
  Fixpoint DiffTuple (ls: list A) := match ls return Type with
                                     | nil => unit
                                     | a :: xs => (Prod (Convert a) (DiffTuple xs))
                                     end.

  Fixpoint updDiffTuple (ls: list A): DiffTuple ls -> forall (p: FinType (length ls)),
        Convert (nth_pf p.(finLt)) -> DiffTuple ls :=
      match ls return DiffTuple ls -> forall (i: FinType (length ls)), Convert (nth_pf i.(finLt)) -> DiffTuple ls with
      | nil => fun _ _ _ => tt
      | x :: xs =>
          fun vals p =>
            match p.(finNum) as i return forall (pf : Is_true (i <? length (x :: xs))),
                Convert (nth_pf pf) -> DiffTuple (x :: xs) with
            | 0 => fun _ v => Build_Prod v vals.(Snd)
            | S m => fun pf v => Build_Prod vals.(Fst) (@updDiffTuple xs vals.(Snd) (Build_FinType m pf) v)
            end p.(finLt)
      end.

  Fixpoint readDiffTuple (ls: list A): DiffTuple ls -> forall (p: FinType (length ls)), Convert (nth_pf p.(finLt)) :=
      match ls return DiffTuple ls -> forall (i: FinType (length ls)), Convert (nth_pf i.(finLt)) with
      | nil => fun _ p => match p.(finLt) with end
      | x :: xs =>
          fun vals p =>
            match p.(finNum) as i return forall (pf : Is_true (i <? length (x :: xs))), Convert (nth_pf pf) with
            | 0 => fun _ => vals.(Fst)
            | S m => fun pf => @readDiffTuple xs vals.(Snd) (Build_FinType m pf)
            end p.(finLt)
      end.
  

  Section CreateDiffTuple.
    Variable f: forall a, Convert a.
    Fixpoint createDiffTuple (ls: list A) : DiffTuple ls :=
      match ls return DiffTuple ls with
      | nil => tt
      | x :: xs => Build_Prod (f x) (createDiffTuple xs)
      end.
  End CreateDiffTuple.
End DiffTuple.

Section MapDiffTuple.
  Variable A: Type.
  Variable Conv1: A -> Type.
  Variable Conv2: A -> Type.
  Variable f: forall a, Conv1 a -> Conv2 a.
  Fixpoint mapDiffTuple ls: DiffTuple Conv1 ls -> DiffTuple Conv2 ls :=
    match ls return DiffTuple Conv1 ls -> DiffTuple Conv2 ls with
    | nil => fun _ => tt
    | x :: xs => fun vs => Build_Prod (f vs.(Fst)) (mapDiffTuple vs.(Snd))
    end.
End MapDiffTuple.



Section KindInd.
  Variable P: Kind -> Type.
  Variable pBool: P Bool.
  Variable pBit: forall n, P (Bit n).
  Variable pStruct: forall ls: list (string * Kind), DiffTuple (fun x => P (snd x)) ls -> P (Struct ls).
  Variable pArray: forall n k, P k -> P (Array n k).
  Variable pTaggedUnion: forall ls: list (string * Kind), DiffTuple (fun x => P (snd x)) ls -> P (TaggedUnion ls).

  Fixpoint KindCustomInd (k: Kind): P k :=
    match k return P k with
    | Bool => pBool
    | Bit n => pBit n
    | Struct ls => pStruct (createDiffTuple (fun x => KindCustomInd (snd x)) ls)
    | Array n k => pArray n (KindCustomInd k)
    | TaggedUnion ls => pTaggedUnion (createDiffTuple (fun x => KindCustomInd (snd x)) ls)
    end.
End KindInd.

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

Section UpdList.
  Variable A: Type.
  Variable v: A.
  Fixpoint updList (ls: list A): nat -> list A :=
    match ls return nat -> list A with
    | nil => fun _ => nil
    | x :: xs => fun n => match n with
                          | 0 => v :: xs
                          | S m => x :: updList xs m
                          end
    end.

  Fixpoint updListLength ls: forall n, Is_true (length ls =? n) -> forall i, Is_true (length (updList ls i) =? n) :=
    match ls return forall n, Is_true (length ls =? n) -> forall i, Is_true (length (updList ls i) =? n) with
    | nil => fun _ pf _ => pf
    | x :: xs => fun n =>
                   match n return Is_true (length (x :: xs) =? n) -> forall i,
                             Is_true (length (updList (x :: xs) i) =? n) with
                   | 0 => fun pf _ => match pf with end
                   | S m => fun pf i =>
                              match i return Is_true (length (updList (x :: xs) i) =? S m) with
                              | 0 => pf
                              | S k => @updListLength xs m pf k
                              end
                   end
    end.
  #[global] Opaque updListLength.

End UpdList.

Section ReadNatToFinType.
  Variable A: Type.
  Variable def: A.
  Variable n: nat.
  Variable reader : forall p: FinType n, A.
  Variable i: nat.

  Definition readNatToFinType : A :=
    match (i <? n) as b return (i <? n) = b -> A with
    | true => fun pf => reader (Build_FinType _ (transparent_Is_true _ (Is_true_eq_left _ pf)))
    | false => fun _ => def
    end eq_refl.
End ReadNatToFinType.

Section SameTuple.
  Variable A: Type.
  #[projections(primitive)]
  Record SameTuple n := { tupleElems: list A;
                          tupleSize: Is_true (Nat.eqb (length tupleElems) n) }.
  #[global] Add Printing Constructor SameTuple.

  Definition updSameTupleNat n (st: SameTuple n) (i: nat) (v: A): SameTuple n :=
    @Build_SameTuple _ (updList v st.(tupleElems) i) (transparent_Is_true _ (updListLength v st.(tupleSize) i)).

  Definition updSameTuple n (st: SameTuple n) (i: FinType n) (v: A): SameTuple n :=
    updSameTupleNat st i.(finNum) v.

  Definition readSameTuple n (vals: SameTuple n) (p: FinType n) : A :=
    @nth_pf _ vals.(tupleElems) p.(finNum) (Is_true_Nat_eqb_ltb_implies vals.(tupleSize) p.(finLt)).



  Section BoolSpec.
    Variable Aeq: A -> A -> bool.
    Variable Aeq_spec: forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (Aeq a1 a2).

    Theorem SameTuple_eqb_spec n: forall (t1 t2: SameTuple n),
        BoolSpec (t1 = t2) (t1 <> t2) (list_eqb Aeq t1.(tupleElems) t2.(tupleElems)).
    Proof.
      induction n; simpl; auto; intros.
      - destruct t1, t2; simpl in *.
        destruct tupleElems0, tupleElems1; simpl in *; destruct tupleSize0, tupleSize1; try constructor; auto.
      - destruct t1, t2; simpl in *.
        destruct tupleElems0; [contradiction|].
        destruct tupleElems1; [contradiction|].
        simpl in *.
        specialize (IHn (@Build_SameTuple _ tupleElems0 tupleSize0)
                      (@Build_SameTuple _ tupleElems1 tupleSize1)).
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
  End BoolSpec.
End SameTuple.

Section SameTupleMap.
  Variable A B: Type.
  Variable f: A -> B.

  Definition mapSameTuple n (st: SameTuple A n): SameTuple B n :=
    @Build_SameTuple B n (map f st.(tupleElems))
      (transparent_Is_true _
         (match length_map f (tupleElems st) in (_ = a) return
                Is_true (a =? n) -> Is_true (Datatypes.length (map f (tupleElems st)) =? n) with
          | eq_refl => id
          end st.(tupleSize))).
End SameTupleMap.

Fixpoint type (k: Kind): Type :=
  match k with
  | Bool => bool
  | Bit n => bits n
  | Struct ls => DiffTuple (fun x => type (snd x)) ls
  | Array n k' => SameTuple (type k') n
  | TaggedUnion ls => bits (max_list (map (fun x => kindSize (snd x)) ls)) ** bits (Z.log2_up (Z.of_nat (length ls)))
  end.

Theorem bool_eqb_spec b1 b2: BoolSpec (b1 = b2) (b1 <> b2) (Bool.eqb b1 b2).
Proof.
  destruct (Bool.eqb_spec b1 b2); constructor; auto.
Qed.

Section IsEq_BoolSpec.
  Fixpoint isEqStruct ls: DiffTuple (fun x => type (snd x) -> type (snd x) -> bool) ls ->
                          type (Struct ls) -> type (Struct ls) -> bool :=
    match ls return DiffTuple (fun x => type (snd x) -> type (snd x) -> bool) ls ->
                    type (Struct ls) -> type (Struct ls) -> bool with
    | nil => fun _ _ _ => true
    | _ :: xs => fun fs v1 v2 => andb (fs.(Fst) v1.(Fst) v2.(Fst)) (isEqStruct fs.(Snd) v1.(Snd) v2.(Snd))
    end.
  
  Definition isEq: forall k, type k -> type k -> bool :=
    KindCustomInd (P := fun k => type k -> type k -> bool)
      Bool.eqb
      (fun n => @Zmod.eqb _)
      isEqStruct
      (fun n k f v1 v2 => list_eqb f v1.(tupleElems) v2.(tupleElems))
      (fun ls helps v1 v2 => andb (Zmod.eqb v1.(Fst) v2.(Fst)) (Zmod.eqb v1.(Snd) v2.(Snd))).

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
        destruct a, e1, e2; unfold Fst, Snd in *.
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

Section FinStruct.
  Variable K: Type.
  Definition FinStruct (ls: list (string * K)) := FinType (length ls).

  Definition fieldNameK (ls: list (string * K)) (i: FinStruct ls) : (string * K) := nth_pf i.(finLt).

  Definition fieldName (ls: list (string * K)) (i: FinStruct ls): string := fst (fieldNameK i).

  Definition fieldK (ls: list (string * K)) (i: FinStruct ls): K := snd (fieldNameK i).

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
End FinStruct.

Section DiffTupleDefault.
  Variable A: Type.
  Variable ConvertType: A -> Type.
  Variable convertVal: forall a, ConvertType a.

  Fixpoint DiffTupleDefault ls :=
    match ls return DiffTuple ConvertType ls with
    | nil => tt
    | x :: xs => Build_Prod (convertVal x) (DiffTupleDefault xs)
    end.
End DiffTupleDefault.

Section SameTupleDefault.
  Variable A: Type.
  Variable val: A.

  Definition SameTupleDefault n := Build_SameTuple (Is_true_Nat_eq_implies (repeat_length val n)).
End SameTupleDefault.

Fixpoint getDefault (k: Kind): type k :=
  match k return type k with
  | Bool => false
  | Bit n => @Zmod.zero _
  | Struct ls => DiffTupleDefault (fun x => getDefault (snd x)) ls
  | Array n k' => SameTupleDefault (getDefault k') n
  | TaggedUnion ls => (@Zmod.zero _ ,, @Zmod.zero _)
  end.

Fixpoint InvDefault (k: Kind): type k :=
  match k return type k with
  | Bool => true
  | Bit n => Zmod.of_Z _ (-1)
  | Struct ls => DiffTupleDefault (fun x => InvDefault (snd x)) ls
  | Array n k' => SameTupleDefault (InvDefault k') n
  | TaggedUnion ls => (Zmod.of_Z _ (-1) ,, Zmod.of_Z _ (-1))
  end.

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

Definition Zmod_lastn n {w} (a : bits w) : bits n := bits.of_Z _ (Z.shiftr (Zmod.to_Z a) (w - n)).

Fixpoint pos_uxor (p : positive) : bool :=
  match p with
  | xH => true
  | xI p' => negb (pos_uxor p')
  | xO p' => (pos_uxor p')
  end.

Definition Z_uxor (z : Z) : bool :=
  match z with
  | Z0 => false
  | Zpos p => pos_uxor p
  | Zneg p => pos_uxor p
  end.

Section EvalToBit.
  Fixpoint evalToBitStruct ls :
    forall (helps: DiffTuple (fun x : string * Kind => type (snd x) -> bits (kindSize (snd x))) ls)
           (vals: type (Struct ls)), bits (kindSize (Struct ls)) :=
    match ls return DiffTuple (fun x : string * Kind => type (snd x) -> bits (kindSize (snd x))) ls
                    -> type (Struct ls) -> bits (kindSize (Struct ls)) with
    | nil => fun _ _ => Zmod.zero
    | x :: xs => fun fs v => Zmod.app (@evalToBitStruct xs fs.(Snd) v.(Snd)) (fs.(Fst) v.(Fst))
    end.

  Fixpoint evalToBitArray n :
    forall k (helps: type k -> type (Bit (kindSize k))) (vals: type (Array n k)), bits (kindSize (Array n k)) :=
    match n return
          forall k, (type k -> type (Bit (kindSize k))) -> type (Array n k) -> bits (kindSize (Array n k)) with
    | 0 => fun _ _ _ => Zmod.zero
    | S m =>
        fun k f st =>
          (match st.(tupleElems) as ls return Is_true (length ls =? S m) -> bits (NatZ_mul (S m) (kindSize k)) with
           | nil => fun pf => match pf with end
           | x :: xs => fun pf => Zmod.app (f x) (@evalToBitArray m k f (@Build_SameTuple _ _ xs pf))
           end) st.(tupleSize)
    end.

  Definition evalToBit: forall k, type k -> bits (kindSize k) :=
    KindCustomInd (P := fun k => type k -> bits (kindSize k))
      (fun v => if v then Zmod.one else Zmod.zero)
      (fun n v => v)
      evalToBitStruct
      evalToBitArray
      (fun ls helps v => Zmod.app v.(Snd) v.(Fst)).
End EvalToBit.

Arguments evalToBitStruct [ls]%_list_scope helps !vals.
Arguments evalToBitArray [n]%_nat_scope [k] helps%_function_scope !vals.

Section EvalFromBit.
  Fixpoint evalFromBitStruct ls:
    forall (helps: DiffTuple (fun x : string * Kind => bits (kindSize (snd x)) -> type (snd x)) ls)
           (vals: bits (kindSize (Struct ls))), type (Struct ls) :=
    match ls return DiffTuple (fun x : string * Kind => bits (kindSize (snd x)) -> type (snd x)) ls
                    -> bits (kindSize (Struct ls)) -> type (Struct ls) with
    | nil => fun _ _ => tt
    | x :: xs => fun fs v => Build_Prod (fs.(Fst) (Zmod_lastn (kindSize (snd x)) v))
                               (@evalFromBitStruct xs fs.(Snd) (Zmod.firstn (kindSize (Struct xs)) v))
    end.

  Fixpoint evalFromBitArray n :
    forall k (helps: type (Bit (kindSize k)) -> type k) (vals: bits (kindSize (Array n k))), type (Array n k) :=
    match n return
          forall k, (type (Bit (kindSize k)) -> type k) -> bits (kindSize (Array n k)) -> type (Array n k) with
    | 0 => fun _ _ _ => @Build_SameTuple _ 0 nil I
    | S m => fun k f v => let '(Build_SameTuple rest pf) :=
                            @evalFromBitArray m k f (Zmod_lastn (NatZ_mul m (kindSize k)) v) in
                          @Build_SameTuple _ (S m) (f (Zmod.firstn (kindSize k) v) :: rest) pf
    end.
  
  Definition evalFromBit: forall k (v: bits (kindSize k)), type k :=
    KindCustomInd (P := fun k => bits (kindSize k) -> type k)
      (fun v => Zmod.eqb v Zmod.one)
      (fun n v => v)
      evalFromBitStruct
      evalFromBitArray
      (fun ls helps v => (Zmod.firstn (max_list (map (fun x => kindSize (snd x)) ls)) v ,,
                            Zmod_lastn (Z.log2_up (Z.of_nat (length ls))) v)).
End EvalFromBit.

Arguments evalFromBitStruct [ls]%_list_scope helps !vals%_Zmod_scope.
Arguments evalFromBitArray [n]%_nat_scope [k] helps%_function_scope !vals%_Zmod_scope.

Section EvalBinary.
  Fixpoint evalBinaryStruct ls:
    DiffTuple (fun x : string * Kind => type (snd x) -> type (snd x) -> type (snd x)) ls
    -> type (Struct ls) -> type (Struct ls) -> type (Struct ls) :=
    match ls return DiffTuple (fun x : string * Kind => type (snd x) -> type (snd x) -> type (snd x)) ls
                    -> type (Struct ls) -> type (Struct ls) -> type (Struct ls) with
    | nil => fun _ _ _ => tt
    | x :: xs => fun fs v1 v2 => Build_Prod (fs.(Fst) v1.(Fst) v2.(Fst))
                                   (@evalBinaryStruct xs fs.(Snd) v1.(Snd) v2.(Snd))
    end.

  Fixpoint evalBinaryArray n:
    forall k, (type k -> type k -> type k) -> type (Array n k) -> type (Array n k) -> type (Array n k) :=
    match n return forall k, (type k -> type k -> type k) ->
                             type (Array n k) -> type (Array n k) -> type (Array n k) with
    | 0 => fun _ _ _ _ => @Build_SameTuple _ 0 nil I
    | S m =>
        fun k f st1 st2 =>
          match st1.(tupleElems) as ls1 return Is_true (length ls1 =? S m) -> SameTuple (type k) (S m) with
          | nil => fun pf1 => match pf1 with end
          | x :: xs =>
              fun pf1 =>
                match st2.(tupleElems) as ls2 return Is_true (length ls2 =? S m) -> SameTuple (type k) (S m) with
                | nil => fun pf2 => match pf2 with end
                | y :: ys =>
                    fun pf2 =>
                      let st := @evalBinaryArray m k f (@Build_SameTuple _ _ xs pf1) (@Build_SameTuple _ _ ys pf2)
                      in @Build_SameTuple _ (S m) (f x y :: st.(tupleElems)) st.(tupleSize)
                end st2.(tupleSize)
          end st1.(tupleSize)
    end.

  Section EvalFuncBinary.
    Variable pBool: bool -> bool -> bool.
    Variable pBit: forall n, bits n -> bits n -> bits n.
    Definition evalBinary: forall k, type k -> type k -> type k :=
      KindCustomInd (P := fun k => type k -> type k -> type k)
        pBool
        pBit
        evalBinaryStruct
        evalBinaryArray
        (fun ls helps v1 v2 => (pBit v1.(Fst) v2.(Fst) ,, pBit v1.(Snd) v2.(Snd))).
  End EvalFuncBinary.

  Definition evalOrBinary := evalBinary orb (fun n => @Zmod.or _).
  Definition evalAndBinary := evalBinary andb (fun n => @Zmod.and _).
  Definition evalXorBinary := evalBinary xorb (fun n => @Zmod.xor _).
End EvalBinary.

Section EvalUnary.
  Fixpoint evalUnaryStruct ls:
    DiffTuple (fun x : string * Kind => type (snd x) -> type (snd x)) ls
    -> type (Struct ls) -> type (Struct ls) :=
    match ls return DiffTuple (fun x : string * Kind => type (snd x) -> type (snd x)) ls
                    -> type (Struct ls) -> type (Struct ls) with
    | nil => fun _ _ => tt
    | x :: xs => fun fs v => Build_Prod (fs.(Fst) v.(Fst))
                                   (@evalUnaryStruct xs fs.(Snd) v.(Snd))
    end.

  Fixpoint evalUnaryArray n:
    forall k, (type k -> type k) -> type (Array n k) -> type (Array n k) :=
    match n return forall k, (type k -> type k) ->
                             type (Array n k) -> type (Array n k) with
    | 0 => fun _ _ _ => @Build_SameTuple _ 0 nil I
    | S m =>
        fun k f st =>
          match st.(tupleElems) as ls return Is_true (length ls =? S m) -> SameTuple (type k) (S m) with
          | nil => fun pf => match pf with end
          | x :: xs =>
              fun pf =>
                let ret := @evalUnaryArray m k f (@Build_SameTuple _ _ xs pf)
                in @Build_SameTuple _ (S m) (f x :: ret.(tupleElems)) ret.(tupleSize)
          end st.(tupleSize)
    end.

  Definition evalNot: forall k, type k -> type k :=
    KindCustomInd (P := fun k => type k -> type k)
      negb
      (fun n => @Zmod.not _)
      evalUnaryStruct
      evalUnaryArray
      (fun ls helps v => (Zmod.not v.(Fst) ,, Zmod.not v.(Snd))).
End EvalUnary.
Section fieldK_repeat.
  Variable K: Type.
  Variable sk: (string * K).
  Lemma fieldK_repeat n : forall i: FinStruct (repeat sk n), fieldK i = snd sk.
  Proof.
    induction n; simpl; auto; intros; destruct i.
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

Inductive Tree (A : Type) :=
| Leaf (name : string) (a : A)
| Node (name : string) (children : list (Tree A)).

Section TreeOps.
  Variable A: Type.

  Fixpoint LeafPath (t: Tree A) : Type :=
    match t with
    | Leaf _ _ => unit
    | Node _ children =>
        (fix loop (ls: list (Tree A)) : Type :=
           match ls with
           | nil => Empty_set
           | x :: xs => (LeafPath x + loop xs)%type
           end) children
    end.

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

  Fixpoint getLeaf (t: Tree A) : LeafPath t -> A :=
    match t return LeafPath t -> A with
    | Leaf _ a => fun _ => a
    | Node _ children =>
        (fix loop (ls: list (Tree A)) :
           ((fix loop (ls : list (Tree A)) : Type :=
              match ls with
              | nil => Empty_set
              | x :: xs => (LeafPath x + loop xs)%type
              end) ls) -> A :=
           match ls return
             ((fix loop (ls : list (Tree A)) : Type :=
                match ls with
                | nil => Empty_set
                | x :: xs => (LeafPath x + loop xs)%type
                end) ls) -> A with
           | nil => fun empty => match empty with end
           | x :: xs => fun p_sum =>
               match p_sum with
               | inl p_x => getLeaf p_x
               | inr p_xs => loop xs p_xs
               end
           end) children
    end.

  Fixpoint leaf_list_path_repeat (t: Tree A) (default_path: LeafPath t) (n: nat) (p: FinType n) :
    (fix loop (ls: list (Tree A)) : Type :=
       match ls with
       | nil => Empty_set
       | x :: xs => (LeafPath x + loop xs)%type
       end) (repeat t n) :=
    match n return forall (p: FinType n),
      (fix loop (ls: list (Tree A)) : Type :=
         match ls with
         | nil => Empty_set
         | x :: xs => (LeafPath x + loop xs)%type
         end) (repeat t n) with
    | O => fun p => match (Nat_ltb_0 p.(finLt)) with end
    | S m => fun p =>
        match p.(finNum) as inum return forall pf: Is_true (inum <? S m)%nat,
          (fix loop (ls: list (Tree A)) : Type :=
             match ls with
             | nil => Empty_set
             | x :: xs => (LeafPath x + loop xs)%type
             end) (repeat t (S m)) with
        | O => fun _ => inl default_path
        | S k => fun pf => inr (@leaf_list_path_repeat t default_path m (Build_FinType k pf))
        end p.(finLt)
    end p.

  Lemma getLeaf_repeat (nodeName: string) (t: Tree A) (default_path: LeafPath t) n (i: FinType n) :
    @getLeaf (Node nodeName (repeat t n)) (leaf_list_path_repeat default_path i) = getLeaf default_path.
  Proof.
    induction n.
    - destruct i as [inum ilt].
      destruct (Nat_ltb_0 ilt).
    - destruct i as [inum ilt].
      simpl.
      destruct inum.
      + reflexivity.
      + simpl.
        apply (IHn (Build_FinType inum ilt)).
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

Arguments LeafPath [A] t.
Arguments NodeChildren [A] t.
Arguments NodePath [A] t.
Arguments NodePathList [A] ls.
Arguments getLeaf [A] [t] p.
Arguments getNode [A] [t] p.
Arguments embedLeafIntoPath [A] [t] p p_local.
Arguments embedNodeIntoPath [A] [t] p p_inner.
Arguments solveNodePath [A] t path_lst.
Arguments leaf_list_path_repeat [A] t default_path [n] p.
Arguments getLeaf_repeat [A] nodeName [t] default_path [n] i.
Arguments getTreePaths [A] t.

Section TreeStateOps.
  Variable A: Type.
  Variable f: A -> Type.

  Fixpoint TreeState (t: Tree A) : Type :=
    match t with
    | Leaf _ a => f a
    | Node _ children =>
        (fix loop (ls: list (Tree A)) : Type :=
           match ls with
           | nil => unit
           | x :: xs => TreeState x ** loop xs
           end) children
    end.

  Fixpoint ListTreeState (ls: list (Tree A)) : Type :=
    match ls with
    | nil => unit
    | x :: xs => TreeState x ** ListTreeState xs
    end.

  Fixpoint readTreeState (t: Tree A) : TreeState t -> forall (p: LeafPath t), f (getLeaf p) :=
    match t return TreeState t -> forall (p: LeafPath t), f (getLeaf p) with
    | Leaf _ a => fun s _ => s
    | Node _ children => fun s p =>
        (fix loop (ls: list (Tree A)) :
           TreeState (Node "" ls) -> forall (pl: LeafPath (Node "" ls)), f (@getLeaf A (Node "" ls) pl) :=
           match ls return
             TreeState (Node "" ls) -> forall (pl: LeafPath (Node "" ls)), f (@getLeaf A (Node "" ls) pl) with
           | nil => fun _ pl => match (pl : Empty_set) with end
           | x :: xs => fun sx plx =>
               match plx return f (@getLeaf A (Node "" (x :: xs)) plx) with
               | inl pl => @readTreeState x sx.(Fst) pl
               | inr pr => loop xs sx.(Snd) pr
               end
           end) children s p
    end.

  Fixpoint writeTreeState (t: Tree A) : TreeState t -> forall (p: LeafPath t), f (getLeaf p) -> TreeState t :=
    match t return TreeState t -> forall (p: LeafPath t), f (getLeaf p) -> TreeState t with
    | Leaf _ a => fun _ _ v => v
    | Node _ children => fun s p v =>
        (fix loop (ls: list (Tree A)) :
          TreeState (Node "" ls) ->
          forall (pl: LeafPath (Node "" ls)), f (@getLeaf A (Node "" ls) pl) -> TreeState (Node "" ls) :=
           match ls return
                 TreeState (Node "" ls) ->
                 forall (pl: LeafPath (Node "" ls)), f (@getLeaf A (Node "" ls) pl) -> TreeState (Node "" ls) with
           | nil => fun sx pl _ => match (pl : Empty_set) with end
           | x :: xs => fun sx plx =>
               match plx return f (@getLeaf A (Node "" (x :: xs)) plx) -> TreeState (Node "" (x :: xs)) with
               | inl pl => fun v => (@writeTreeState x sx.(Fst) pl v ,, sx.(Snd))
               | inr pr => fun v => (sx.(Fst) ,, loop xs sx.(Snd) pr v)
               end
           end) children s p v
    end.
End TreeStateOps.

Arguments readTreeState [A] [f] t s p.
Arguments writeTreeState [A] [f] t s p v.
Arguments ListTreeState [A] f ls.

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
