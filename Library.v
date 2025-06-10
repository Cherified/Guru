From Stdlib Require Import String Ascii List Bool Zmod NArith.

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

Section Prod.
  Variable A B: Type.
  #[projections(primitive)]
    Record Prod := { Fst: A;
                     Snd: B }.
End Prod.

Inductive Kind :=
| Bool   : Kind
| Bit    : Z -> Kind
| Struct : list (string * Kind) -> Kind
| Array  : nat -> Kind -> Kind.

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
  
  Section DefaultDiffTuple.
    Variable def: forall a, Convert a.
    Fixpoint defaultDiffTuple (ls: list A): DiffTuple ls :=
      match ls return DiffTuple ls with
      | nil => tt
      | x :: xs => Build_Prod (def x) (@defaultDiffTuple xs)
      end.
  End DefaultDiffTuple.

  Section CombineDiffTuple.
    Variable Combine: forall a, Convert a -> Convert a -> Convert a.
    Fixpoint combineDiffTuple (ls: list A): DiffTuple ls -> DiffTuple ls -> DiffTuple ls :=
      match ls return DiffTuple ls -> DiffTuple ls -> DiffTuple ls with
      | nil => fun _ _ => tt
      | x :: xs => fun vs1 vs2 => Build_Prod (Combine vs1.(Fst) vs2.(Fst)) (@combineDiffTuple xs vs1.(Snd) vs2.(Snd))
      end.

    Theorem combineDiffTupleDef def (pf: forall a (x: Convert a), Combine (def _) x = x) ls:
      forall val,
        combineDiffTuple (defaultDiffTuple def ls) val = val.
    Proof.
      induction ls; simpl; auto; intros.
      - destruct val; auto.
      - rewrite pf.
        rewrite IHls.
        destruct val; auto.
    Qed.

    Theorem combineDiffTupleAssoc
      (pf: forall a (x y z: Convert a), Combine x (Combine y z) = Combine (Combine x y) z)
      ls: forall (val1 val2 val3: DiffTuple ls),
        combineDiffTuple val1 (combineDiffTuple val2 val3) = combineDiffTuple (combineDiffTuple val1 val2) val3.
    Proof.
      induction ls; simpl; auto; intros.
      - erewrite IHls with (val2 := val2.(Snd)), pf; eauto.
    Qed.
  End CombineDiffTuple.

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

Section CreateDiffTupleMap.
  Variable A B: Type.
  Variable mapF: A -> B.
  Variable Convert: B -> Type.
  Variable f: forall a, Convert (mapF a).
  Fixpoint createDiffTupleMap (ls: list A) : DiffTuple Convert (map mapF ls) :=
    match ls return DiffTuple Convert (map mapF ls) with
    | nil => tt
    | x :: xs => Build_Prod (f x) (createDiffTupleMap xs)
    end.
End CreateDiffTupleMap.

Section mapDiffTuple_createDiffTupleMap.
  Variable A B: Type.
  Variable Conv1: A -> Type.
  Variable Conv2: A -> Type.
  Variable f: forall a, Conv1 a -> Conv2 a.
  Variable mapF: B -> A.
  Variable g: forall b, Conv1 (mapF b).
  Theorem mapDiffTuple_createDiffTupleMap ls:
    (mapDiffTuple f (createDiffTupleMap (mapF := mapF) g ls)) =
      createDiffTupleMap (mapF := mapF) (fun a => f (g a)) ls.
  Proof.
    induction ls; simpl; auto.
    rewrite IHls.
    auto.
  Qed.
End mapDiffTuple_createDiffTupleMap.

Section FoldDiffTuple.
  Variable A B C: Type.
  Variable f: B -> C -> C.
  Variable def: C.
  Fixpoint foldDiffTuple ls: DiffTuple (fun _ => B) ls -> C :=
    match ls return DiffTuple (fun (_: A) => B) ls -> C with
    | nil => fun _ => def
    | x :: xs => fun vals => f vals.(Fst) (@foldDiffTuple xs vals.(Snd))
    end.
End FoldDiffTuple.

Section KindInd.
  Variable P: Kind -> Type.
  Variable pBool: P Bool.
  Variable pBit: forall n, P (Bit n).
  Variable pStruct: forall ls: list (string * Kind), DiffTuple (fun x => P (snd x)) ls -> P (Struct ls).
  Variable pArray: forall n k, P k -> P (Array n k).

  Fixpoint KindCustomInd (k: Kind): P k :=
    match k return P k with
    | Bool => pBool
    | Bit n => pBit n
    | Struct ls => pStruct (createDiffTuple (fun x => KindCustomInd (snd x)) ls)
    | Array n k => pArray n (KindCustomInd k)
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
      + destruct IHls, elem; simpl; constructor; subst; try inversion H; subst; auto; try intro pf; inversion pf; subst; auto.
      + constructor; intro pf; inversion pf; subst; auto.
    - destruct (Nat.eqb_spec n n0); subst; simpl; auto.
      + destruct (IHk1 k2); constructor; subst; auto.
        intro pf; inversion pf; subst; auto.
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

  Section CombineList.
    Variable combine: A -> A -> A.

    Fixpoint combineList ls1: list A -> list A :=
      match ls1 with
      | nil => fun _ => nil
      | x :: xs => fun ls2 => match ls2 with
                              | nil => nil
                              | y :: ys => combine x y :: combineList xs ys
                              end
      end.

    Fixpoint combineListLength ls: forall n, Is_true (length ls =? n) ->
                                             forall ls2, Is_true (length ls2 =? n) ->
                                                         Is_true (length (combineList ls ls2) =? n) :=
      match ls return forall n, Is_true (length ls =? n) ->
                                forall ls2, Is_true (length ls2 =? n) ->
                                            Is_true (length (combineList ls ls2) =? n) with
      | nil => fun _ pf _ _ => pf
      | x :: xs => fun n =>
                     match n return Is_true (length (x :: xs) =? n) ->
                                    forall ls2, Is_true (length ls2 =? n) ->
                                                Is_true (length (combineList (x :: xs) ls2) =? n) with
                     | 0 => fun pf _ _ => match pf with end
                     | S m => fun pf ls2 => match ls2 return Is_true (length ls2 =? S m) ->
                                                             Is_true (length (combineList (x :: xs) ls2) =? S m) with
                                            | nil => fun pf2 => match pf2 with end
                                            | y :: ys => fun pf2 => @combineListLength xs m pf ys pf2
                                            end
                     end
      end.
    #[global] Opaque combineListLength.
  End CombineList.
End UpdList.

Section ReadNatToFinType.
  Variable A: Type.
  Variable def: A.
  Variable n: nat.
  Variable reader : forall p: FinType n, A.
  Variable i: nat.

  Definition readNatToFinType: A.
    refine _.
    case_eq (i <? n); intros pf.
    - exact (reader (Build_FinType _ (transparent_Is_true _ (Is_true_eq_left _ pf)))).
    - exact def.
  Defined.
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

  Section CombineSameTuple.
    Variable combine: A -> A -> A.
    Definition combineSameTuple n (vs1 vs2: SameTuple n) : SameTuple n :=
      Build_SameTuple (transparent_Is_true _ (combineListLength combine vs1.(tupleSize) vs2.(tupleSize))).
  End CombineSameTuple.

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
      (fun n k f v1 v2 => list_eqb f v1.(tupleElems) v2.(tupleElems)).

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
  Qed.
End IsEq_BoolSpec.

Section ForceOption.
  Variable A: Type.
  Definition forceOption A (o : option A) : match o with
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

Fixpoint Default (k: Kind): type k :=
  match k return type k with
  | Bool => false
  | Bit n => @Zmod.zero _
  | Struct ls => DiffTupleDefault (fun x => Default (snd x)) ls
  | Array n k' => SameTupleDefault (Default k') n
  end.

Fixpoint InvDefault (k: Kind): type k :=
  match k return type k with
  | Bool => true
  | Bit n => Zmod.of_Z _ (-1)
  | Struct ls => DiffTupleDefault (fun x => InvDefault (snd x)) ls
  | Array n k' => SameTupleDefault (InvDefault k') n
  end.

Fixpoint NatZ_mul n (k: Z): Z :=
  match n with
  | 0 => 0%Z
  | S m => NatZ_mul m k + k
  end.

Fixpoint size (k: Kind) :=
  match k with
  | Bool => 1%Z
  | Bit n => n
  | Struct ls => (fix help ls :=
                    match ls with
                    | nil => 0%Z
                    | x :: xs => (help xs + size (snd x))%Z
                    end) ls
  | Array n k => NatZ_mul n (size k)
  end.

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
    forall (helps: DiffTuple (fun x : string * Kind => type (snd x) -> bits (size (snd x))) ls)
           (vals: type (Struct ls)), bits (size (Struct ls)) :=
    match ls return DiffTuple (fun x : string * Kind => type (snd x) -> bits (size (snd x))) ls
                    -> type (Struct ls) -> bits (size (Struct ls)) with
    | nil => fun _ _ => Zmod.zero
    | x :: xs => fun fs v => Zmod.app (@evalToBitStruct xs fs.(Snd) v.(Snd)) (fs.(Fst) v.(Fst))
    end.

  Fixpoint evalToBitArray n :
    forall k (helps: type k -> type (Bit (size k))) (vals: type (Array n k)), bits (size (Array n k)) :=
    match n return forall k, (type k -> type (Bit (size k))) -> type (Array n k) -> bits (size (Array n k)) with
    | 0 => fun _ _ _ => Zmod.zero
    | S m =>
        fun k f st =>
          (match st.(tupleElems) as ls return Is_true (length ls =? S m) -> bits (NatZ_mul (S m) (size k)) with
           | nil => fun pf => match pf with end
           | x :: xs => fun pf => Zmod.app (@evalToBitArray m k f (@Build_SameTuple _ _ xs pf)) (f x)
           end) st.(tupleSize)
    end.

  Definition evalToBit: forall k, type k -> bits (size k) :=
    KindCustomInd (P := fun k => type k -> bits (size k))
      (fun v => if v then Zmod.one else Zmod.zero)
      (fun n v => v)
      evalToBitStruct
      evalToBitArray.
End EvalToBit.

Arguments evalToBitStruct [ls]%_list_scope helps !vals.
Arguments evalToBitArray [n]%_nat_scope [k] helps%_function_scope !vals.

Section EvalFromBit.
  Fixpoint evalFromBitStruct ls:
    forall (helps: DiffTuple (fun x : string * Kind => bits (size (snd x)) -> type (snd x)) ls)
           (vals: bits (size (Struct ls))), type (Struct ls) :=
    match ls return DiffTuple (fun x : string * Kind => bits (size (snd x)) -> type (snd x)) ls
                    -> bits (size (Struct ls)) -> type (Struct ls) with
    | nil => fun _ _ => tt
    | x :: xs => fun fs v => Build_Prod (fs.(Fst) (Zmod_lastn (size (snd x)) v))
                               (@evalFromBitStruct xs fs.(Snd) (Zmod.firstn (size (Struct xs)) v))
    end.

  Fixpoint evalFromBitArray n :
    forall k (helps: type (Bit (size k)) -> type k) (vals: bits (size (Array n k))), type (Array n k) :=
    match n return forall k, (type (Bit (size k)) -> type k) -> bits (size (Array n k)) -> type (Array n k) with
    | 0 => fun _ _ _ => @Build_SameTuple _ 0 nil I
    | S m => fun k f v => let '(Build_SameTuple rest pf) :=
                            @evalFromBitArray m k f (Zmod.firstn (NatZ_mul m (size k)) v) in
                          @Build_SameTuple _ (S m) (f (Zmod_lastn (size k) v) :: rest) pf
    end.
  
  Definition evalFromBit: forall k (v: bits (size k)), type k :=
    KindCustomInd (P := fun k => bits (size k) -> type k)
      (fun v => Zmod.eqb v Zmod.one)
      (fun n v => v)
      evalFromBitStruct
      evalFromBitArray.
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
        evalBinaryArray.
  End EvalFuncBinary.

  Definition evalOrBinary := evalBinary orb (fun n => @Zmod.or _).
  Definition evalAndBinary := evalBinary orb (fun n => @Zmod.and _).
  Definition evalXorBinary := evalBinary orb (fun n => @Zmod.xor _).
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
      evalUnaryArray.
End EvalUnary.

Section MultiStep.
  Variable S Out Inp: Type.
  Variable Step1: S -> S -> Out -> Inp -> Prop.
  Variable defOut: Out.
  Variable defInp: Inp.
  Variable combineOut: Out -> Out -> Out.
  Variable combineInp: Inp -> Inp -> Inp.

  Inductive MultiStep: S -> S -> Out -> Inp -> Prop :=
  | NilStep old new puts gets
      (oldIsNew: new = old)
      (putsEmpty: puts = defOut)
      (getsEmpty: gets = defInp):
    MultiStep old new puts gets
  | ConsStep old new puts gets
      newStep putsStep getsStep
      (step: Step1 old newStep putsStep getsStep)
      (contPf: MultiStep newStep new puts gets)
      finalPuts finalGets
      (finalPutsEq: finalPuts = combineOut putsStep puts)
      (finalGetsEq: finalGets = combineInp getsStep gets):
    MultiStep old new finalPuts finalGets.
End MultiStep.
