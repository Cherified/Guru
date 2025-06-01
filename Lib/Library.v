From Stdlib Require Import String Ascii PeanoNat List Bool Zmod NArith.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Inductive Kind :=
| Bool   : Kind
| Bit    : Z -> Kind
| Struct : list (string * Kind) -> Kind
| Array  : nat -> Kind -> Kind.

Section Prod_BoolSpec.
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

Section DiffTuple.
  Variable A: Type.
  Variable Convert: A -> Type.
  Fixpoint DiffTuple (ls: list A) := match ls return Type with
                                     | nil => unit
                                     | a :: xs => (Convert a * DiffTuple xs)%type
                                     end.
End DiffTuple.

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
    | Struct ls => pStruct ((fix help2 ls :=
                               match ls return DiffTuple (fun x => P (snd x)) ls with
                               | nil => tt
                               | x :: xs => (KindCustomInd (snd x), help2 xs)
                               end) ls)
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

Section SameTuple.
  Variable A: Type.
  Record SameTuple n := { tupleElems: list A;
                          tupleSize: Is_true (Nat.eqb (length tupleElems) n) }.

  Variable Aeq: A -> A -> bool.
  Variable Aeq_spec: forall a1 a2, BoolSpec (a1 = a2) (a1 <> a2) (Aeq a1 a2).

  Theorem SameTuple_eqb_spec n: forall (t1 t2: SameTuple n), BoolSpec (t1 = t2) (t1 <> t2) (list_eqb Aeq (tupleElems t1) (tupleElems t2)).
  Proof.
    induction n; simpl; auto; intros.
    - destruct t1, t2; simpl in *.
      destruct tupleElems0, tupleElems1; simpl in *; destruct tupleSize0, tupleSize1; try constructor; auto.
    - destruct t1, t2; simpl in *.
      destruct tupleElems0; [contradiction|].
      destruct tupleElems1; [contradiction|].
      simpl in *.
      specialize (IHn {| tupleElems := tupleElems0; tupleSize := tupleSize0 |} {| tupleElems := tupleElems1; tupleSize := tupleSize1 |}).
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
End SameTuple.

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
  Fixpoint isEq k: type k -> type k -> bool :=
    match k return type k -> type k -> bool with
    | Bool => Bool.eqb
    | Bit n => Zmod.eqb
    | Struct ls => (fix help ls :=
                      match ls return type (Struct ls) -> type (Struct ls) -> bool with
                      | nil => fun _ _ => true
                      | (s, k) :: xs => fun e1 e2 => andb (@isEq k (fst e1) (fst e2)) (help xs (snd e1) (snd e2))
                      end) ls
    | Array n k' => fun e1 e2 => list_eqb (@isEq k') (tupleElems e1) (tupleElems e2)
    end.

  Theorem isEq_BoolSpec k: forall e1 e2, BoolSpec (e1 = e2) (e1 <> e2) (@isEq k e1 e2).
  Proof.
    induction k using KindCustomInd; auto.
    - apply bool_eqb_spec.
    - apply Zmod.eqb_spec.
    - induction ls.
      + constructor; destruct e1, e2; auto.
      + intros e1 e2.
        destruct X as [curr rest].
        specialize (IHls rest (snd e1) (snd e2)).
        specialize (curr (fst e1) (fst e2)).
        destruct a, e1, e2; unfold fst, snd in curr, IHls; unfold fst, snd.
        unfold isEq; fold (@isEq (Struct ls)); fold (@isEq k).
        unfold fst, snd.
        destruct curr, IHls; subst; auto; simpl; constructor; auto; intro pf; inversion pf; auto.
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

Section Nat_BoolSpec.
  Variable n1 n2: nat.
  Theorem Nat_BoolSpec: BoolSpec (n1 = n2) (n1 <> n2) (Nat.eqb n1 n2).
  Proof.
    pose proof (Nat.eqb_spec n1 n2) as pf.
    destruct pf; [subst |]; constructor; [|intro pf2; subst]; auto.
  Qed.
End Nat_BoolSpec.

Section FinType.
  Record FinType (n: nat) := { finNum: nat;
                               finLt: Is_true (finNum <? n) }.

  Definition FinType_eqb n (n1 n2: FinType n) := finNum n1 =? finNum n2.

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

Theorem Nat_ltb_0 n: Is_true (n <? 0) -> False.
Proof.
  case_eq (n <? 0); intros; auto.
  rewrite Nat.ltb_lt in H.
  lia.
Qed.

Section Nth_pf.
  Variable A: Type.

  Fixpoint nth_pf (ls: list A): FinType (length ls) -> A :=
    match ls return FinType (length ls) -> A with
    | nil => fun rec => match Nat_ltb_0 (finLt rec) with end
    | x :: xs => fun rec => match (finNum rec) as i return Is_true (i <? length (x :: xs)) -> A with
                            | 0 => fun _ => x
                            | S m => fun pf => @nth_pf xs (@Build_FinType _ m pf)
                            end (finLt rec)
    end.
End Nth_pf.

Section FinStruct.
  Variable K: Type.
  Definition FinStruct (ls: list (string * K)) := FinType (length ls).

  Definition fieldNameK (ls: list (string * K)) (i: FinStruct ls) : (string * K) := nth_pf i.

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
    | x :: xs => (convertVal x, DiffTupleDefault xs)
    end.
End DiffTupleDefault.

Theorem Is_true_nat_eqb n m: n = m -> Is_true (n =? m).
Proof.
  intros; subst.
  rewrite Nat.eqb_refl.
  apply I.
Qed.

Section SameTupleDefault.
  Variable A: Type.
  Variable val: A.

  Definition SameTupleDefault n := Build_SameTuple (Is_true_nat_eqb (repeat_length val n)).
End SameTupleDefault.

Fixpoint Default (k: Kind): type k :=
  match k return type k with
  | Bool => false
  | Bit n => @Zmod.zero _
  | Struct ls => DiffTupleDefault (fun x => Default (snd x)) ls
  | Array n k' => SameTupleDefault (Default k') n
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

Definition evalToBit: forall k, type k -> bits (size k) :=
  KindCustomInd (P := fun k => type k -> bits (size k))
    (fun v => if v then Zmod.one else Zmod.zero)
    (fun n v => v)
    (fun ls => (fix help ls :=
                  match ls return DiffTuple (fun x : string * Kind => type (snd x) -> bits (size (snd x))) ls
                                  -> type (Struct ls) -> bits (size (Struct ls)) with
                  | nil => fun _ _ => Zmod.zero
                  | x :: xs => fun fs v => Zmod.app (help xs (snd fs) (snd v)) (fst fs (fst v))
                  end) ls)
    (fun n k f =>
       (fix help n :=
          match n return SameTuple (type k) n -> bits (NatZ_mul n (size k)) with
          | 0 => fun _ => Zmod.zero
          | S m =>
              fun '(Build_SameTuple ls pf) =>
                (match ls return Is_true (length ls =? S m) -> bits (NatZ_mul (S m) (size k)) with
                 | nil => fun pf => match pf with end
                 | x :: xs => fun pf => Zmod.app (help m (@Build_SameTuple _ _ xs pf)) (f x)
                 end) pf
          end) n).

Definition Zmod_lastn n {w} (a : bits w) : bits n := Zmod.of_Z _ (Z.shiftr (Zmod.to_Z a) (w - n)).

Definition evalFromBit: forall k, bits (size k) -> type k :=
  KindCustomInd (P := fun k => bits (size k) -> type k)
    (fun v => Zmod.eqb v Zmod.one)
    (fun n v => v)
    (fun ls => (fix help ls :=
                  match ls return DiffTuple (fun x : string * Kind => bits (size (snd x)) -> type (snd x)) ls
                                  -> bits (size (Struct ls)) -> type (Struct ls) with
                  | nil => fun _ _ => tt
                  | x :: xs => fun fs v => (fst fs (Zmod_lastn (size (snd x)) v),
                                              help xs (snd fs) (Zmod.firstn (size (Struct xs)) v))
                  end) ls)
    (fun n k f =>
       (fix help n :=
          match n return bits (NatZ_mul n (size k)) -> SameTuple (type k) n with
          | 0 => fun _ => @Build_SameTuple _ 0 nil I
          | S m => fun v => let '(Build_SameTuple rest pf) := help m (Zmod.firstn (NatZ_mul m (size k)) v) in
                            @Build_SameTuple _ (S m) (f (Zmod_lastn (size k) v) :: rest) pf
          end) n).

Definition evalOrBinary: forall k, type k -> type k -> type k :=
  KindCustomInd (P := fun k => type k -> type k -> type k)
    orb
    (fun n => @Zmod.or (2 ^ n))
    (fun ls => (fix help ls :=
                  match ls return DiffTuple (fun x : string * Kind => type (snd x) -> type (snd x) -> type (snd x)) ls
                                  -> type (Struct ls) -> type (Struct ls) -> type (Struct ls) with
                  | nil => fun _ _ _ => tt
                  | x :: xs => fun fs v1 v2 => (fst fs (fst v1) (fst v2),
                                                 help xs (snd fs) (snd v1) (snd v2))
                  end) ls)
    (fun n k f =>
       (fix help n :=
          match n return SameTuple (type k) n -> SameTuple (type k) n -> SameTuple (type k) n with
          | 0 => fun _ _ => @Build_SameTuple _ 0 nil I
          | S m =>
              fun '(Build_SameTuple ls1 pf1) '(Build_SameTuple ls2 pf2) =>
                match ls1 return Is_true (length ls1 =? S m) -> SameTuple (type k) (S m) with
                | nil => fun pf1 => match pf1 with end
                | x :: xs =>
                    fun pf1 =>
                      match ls2 return Is_true (length ls2 =? S m) -> SameTuple (type k) (S m) with
                      | nil => fun pf2 => match pf2 with end
                      | y :: ys =>
                          fun pf2 =>
                            let '(Build_SameTuple rest pfFinal) := help m (@Build_SameTuple _ _ xs pf1)
                                                                        (@Build_SameTuple _ _ ys pf2) in
                            @Build_SameTuple _ (S m) (f x y :: rest) pfFinal
                      end pf2
                end pf1
          end
       ) n).

Section WordArray.
  Variable T: Type.
  Variable val: T.
  Variable n: nat.
  Variable finMap: FinArray n -> T.
  Variable w: word (Nat.log2_up n).

  Definition readArray : T :=
    match lt_dec (Z.to_nat (wordVal _ w)) n with
    | left pf => finMap (FinArray_of_nat_lt pf)
    | right _ => val
    end.

  Definition writeArray : FinArray n -> T :=
    match lt_dec (Z.to_nat (wordVal _ w)) n return FinArray n -> T with
    | left pf => fun i => match FinArray_dec (FinArray_of_nat_lt pf) i return T with
                          | left _ => val
                          | right _ => finMap i
                          end
    | right _ => finMap
    end.
End WordArray.

Section UpdFinStruct.
  Variable K: Type.
  Variable ty: K -> Type.
  Variable ls: list (string * K).
  Variable orig: forall i: FinStruct ls, ty (fieldK i).
  Variable x: FinStruct ls.
  Variable updVal: ty (fieldK x).
  Definition updStruct (i: FinStruct ls): ty (fieldK i) :=
    match FinStruct_dec x i with
    | left pf => match pf in _ = Y return ty (fieldK Y) with
                 | eq_refl => updVal
                 end
    | right _ => orig i
    end.
End UpdFinStruct.

Section UpdFinArray.
  Variable A: Type.
  Variable n: nat.
  Variable orig: forall i: FinArray n, A.
  Variable p: FinArray n.
  Variable updVal: A.
  Definition updArray (i: FinArray n): A :=
    match FinArray_dec p i with
    | left pf => match pf in _ = Y return A with
                 | eq_refl => updVal
                 end
    | right _ => orig i
    end.
End UpdFinArray.
  
Section FoldFinStruct.
  Variable K A B: Type.
  Variable def: A.
  Variable ls: list (string * K).
  Variable f: B -> A -> A.
  Fixpoint foldFinStruct (ls: list (string * K)): (FinStruct ls -> B) -> A :=
    match ls return (FinStruct ls -> B) -> A with
    | nil => fun _ => def
    | x :: xs => fun func => f (func (inl tt)) (@foldFinStruct xs (fun i => func (inr i)))
    end.
End FoldFinStruct.

Section GenFinStruct.
  Variable K: Type.
  Fixpoint genFinStruct ls: list (@FinStruct K ls) :=
    match ls with
    | nil => nil
    | _ :: xs => inl tt :: map inr (genFinStruct xs)
    end.
End GenFinStruct.

Fixpoint genFinArray n: list (FinArray n) :=
  match n with
  | 0 => nil
  | S m => inl tt :: map inr (genFinArray m)
  end.

Section StringToNum.
  Local Open Scope Z.
  Local Open Scope char.
  Definition hexDigitToZ (c : ascii) : option Z :=
    match c with
    | "0" => Some 0
    | "1" => Some 1
    | "2" => Some 2
    | "3" => Some 3
    | "4" => Some 4
    | "5" => Some 5
    | "6" => Some 6
    | "7" => Some 7
    | "8" => Some 8
    | "9" => Some 9
    | "a" | "A" => Some 10
    | "b" | "B" => Some 11
    | "c" | "C" => Some 12
    | "d" | "D" => Some 13
    | "e" | "E" => Some 14
    | "f" | "F" => Some 15
    | _   => None
    end.

  Definition binDigitToZ c : option Z :=
    match c with
    | "0" => Some 0
    | "1" => Some 1
    | _   => None
    end.
  Local Close Scope char.

  Fixpoint readHexZAux acc s : option Z :=
  match s with
    | ""%string => Some acc
    | String c s' =>
      match hexDigitToZ c with
        | Some n => readHexZAux (16 * acc + n) s'
        | None => None
      end
  end.

  Definition readHexZ := readHexZAux 0.

  Definition hex s := forceOption (readHexZ s).

  Fixpoint readBinAux acc s : option Z :=
    match s with
    | ""%string => Some acc
    | String c s' =>
        match binDigitToZ c with
        | Some n => readBinAux (2 * acc + n) s'
        | None => None
        end
    end.

  Definition readBinZ := readBinAux 0.

  Definition bin s := forceOption (readBinZ s).
End StringToNum.

Section Nth_pf.
  Variable A: Type.

  Fixpoint nth_pf (ls: list A): forall i, i < length ls -> A.
    refine (
    match ls return forall i, i < length ls -> A with
    | nil => fun _ pf => _
    | x :: xs => fun i => match i return i < length (x :: xs) -> A with
                          | 0 => fun _ => x
                          | S m => fun pf => nth_pf xs m (PeanoNat.lt_S_n _ _ pf)
                          end
    end).
    abstract (simpl in pf; Lia.lia).
  Defined.
End Nth_pf.

Theorem idx_offset_len idx offset len (pfGe: idx >= offset) (pfLt: idx < offset + len): idx - offset < len.
Proof.
  Lia.lia.
Qed.

Definition evalReadArray (n m: nat) (k: Kind) (i: word m) (v: type (Array n k)) :=
  match lt_dec (Z.to_nat (wordVal _ i)) n return type k with
  | left pf => arrayToFunc v (FinArray_of_nat_lt pf)
  | right _ => Default k
  end.

Arguments evalReadArray [n m k] i !v.

Section ArrayFromListZ.
  Variable width: nat.
  Fixpoint arrayFromListZ (ls: list Z): SameTuple (word width) (length ls) :=
    match ls return SameTuple (word width) (length ls) with
    | nil => tt
    | x :: xs => (ZToWord width x, arrayFromListZ xs)
    end.

  Fixpoint arrayFromListZSize size (ls: list Z): SameTuple (word width) size :=
    match size with
    | 0 => tt
    | S m => match ls with
             | x :: xs => (ZToWord width x, arrayFromListZSize m xs)
             | nil => (wzero width, arrayFromListZSize m nil)
             end
    end.

  Fixpoint arrayFromListZSizeOffset (size: nat): forall offset: nat, list Z -> SameTuple (word width) size :=
    match size return nat -> list Z -> SameTuple (word width) size with
    | 0 => fun _ _ => tt
    | S m => fun offset ls => match offset with
                              | 0 => match ls with
                                     | nil => (wzero width, arrayFromListZSizeOffset m 0 nil)
                                     | x :: xs => (ZToWord width x, arrayFromListZSizeOffset m 0 xs)
                                     end
                              | S k => (wzero width, arrayFromListZSizeOffset m k ls)
                              end
    end.

  Section ArrayFromListZEq.
    Variable size: nat.
    Variable arr: type (Array size (Bit width)).
    Variable offset: nat.
    Variable ls: list Z.

    Definition ArrayFromListZEq := forall (i: FinArray size)
                                          (pfGe: FinArray_to_nat i >= offset)
                                          (pfLt: FinArray_to_nat i < offset + length ls),
        nth_pf (idx_offset_len pfGe pfLt) = wordVal width (arrayToFunc (ty := type) (k := Bit width) arr i).

    Definition ReadArrayFromListZEq := forall m (i: word m)
                                              (pfGe: Z.to_nat (wordVal m i) >= offset)
                                              (pfLt: Z.to_nat (wordVal m i) < offset + length ls),
        evalReadArray i arr = ZToWord width (nth_pf (idx_offset_len pfGe pfLt)).
  End ArrayFromListZEq.
End ArrayFromListZ.

Definition lgCeil i := S (Nat.log2_iter (pred (pred i)) 0 1 0).

Section FinStruct_FinArray.
  Variable K: Type.

  Fixpoint FinArray_to_FinStruct n: forall (ls: list (string * K)) (i: FinArray n), length ls = n -> FinStruct ls :=
    match n return forall (ls: list (string * K)) (i: FinArray n), length ls = n -> FinStruct ls with
    | 0 => fun _ i _ => match i with
                        end
    | S m => fun ls => match ls return forall (i: FinArray (S m)), length ls = S m -> FinStruct ls with
                       | nil => fun _ pf => match Nat.neq_0_succ _ pf with
                                            end
                       | x :: xs => fun i pf => match i return FinStruct (x :: xs) with
                                                | inl _ => inl tt
                                                | inr y => inr (@FinArray_to_FinStruct m xs y (f_equal pred pf))
                                                end
                       end
    end.

  Fixpoint FinStruct_to_FinArray (ls: list (string * K)): forall n (i: FinStruct ls), length ls = n -> FinArray n :=
    match ls return forall n (i: FinStruct ls), length ls = n -> FinArray n with
    | nil => fun _ i _ => match i with
                          end
    | x :: xs => fun n => match n return forall (i: FinStruct (x :: xs)), length (x :: xs) = n -> FinArray n with
                          | 0 => fun _ pf => match Nat.neq_succ_0 _ pf with
                                             end
                          | S m => fun i pf => match i return FinArray (S m) with
                                                   | inl _ => inl tt
                                                   | inr y => inr (@FinStruct_to_FinArray xs m y (f_equal pred pf))
                                                   end
                          end
    end.  
End FinStruct_FinArray.

Section fieldK_repeat.
  Variable K: Type.
  Variable sk: (string * K).
  Lemma fieldK_repeat n : forall i: FinStruct (repeat sk n), fieldK i = snd sk.
  Proof.
    induction n; simpl; auto; intros; destruct i.
    - auto.
    - exact (IHn f).
  Qed.
End fieldK_repeat.

Lemma pow_2_n_gt_0 n: Nat.pow 2 n > 0.
Proof.
  induction n; auto; simpl.
  Lia.lia.
Qed.
