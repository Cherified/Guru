(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String Ascii List Bool Zmod NArith ZArith BinPos Lia.

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

#[projections(primitive)]
Record Prod (A B : Type) : Type := {
  Fst : A;
  Snd : B
}.

#[global] Notation "A ** B" := (Prod A B) (at level 40, left associativity) : type_scope.
#[global] Notation "( a ,, b )" := (Build_Prod a b).

Scheme All for prod.
Scheme All for list.

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

Section FinType.
  #[projections(primitive)]
  Record FinType (n: nat) := { finNum: nat;
                               finLt: Is_true (finNum <? n) }.
  #[global] Add Printing Constructor FinType.
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

Section IsEq.
  Variable A: Type.
  Variable Aeqb: A -> A -> bool.
  Fixpoint list_eqb (ls1 ls2: list A): bool :=
    match ls1, ls2 with
    | nil, nil => true
    | x :: xs, y :: ys => andb (Aeqb x y) (list_eqb xs ys)
    | _, _ => false
    end.
End IsEq.

Section IsEqKind.
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
End IsEqKind.

Section FinStruct.
  Variable K: Type.
  Definition FinStruct (ls: list (string * K)) := FinType (length ls).

  Definition fieldNameK (ls: list (string * K)) (i: FinStruct ls) : (string * K) := nth_pf i.(finLt).

  Definition fieldName (ls: list (string * K)) (i: FinStruct ls): string := fst (fieldNameK i).

  Definition fieldK (ls: list (string * K)) (i: FinStruct ls): K := snd (fieldNameK i).
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
    | S m => fun k f v => let st :=
                            @evalFromBitArray m k f (Zmod_lastn (NatZ_mul m (kindSize k)) v) in
                          @Build_SameTuple _ (S m) (f (Zmod.firstn (kindSize k) v) :: st.(tupleElems)) st.(tupleSize)
    end.

  Definition evalFromBit: forall k (v: bits (kindSize k)), type k :=
    KindCustomInd (P := fun k => bits (kindSize k) -> type k)
      (fun v => Zmod.eqb v Zmod.one)
      (fun n v => v)
      evalFromBitStruct
      evalFromBitArray
      (fun ls helps v => (Zmod_lastn (max_list (map (fun x => kindSize (snd x)) ls)) v ,,
                            Zmod.firstn (Z.log2_up (Z.of_nat (length ls))) v)).
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

Inductive Tree (A : Type) :=
| Leaf (name : string) (a : A)
| Node (name : string) (children : list (Tree A)).

Section TreeCoreOps.
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
End TreeCoreOps.

Arguments LeafPath [A] t.
Arguments getLeaf [A] [t] p.

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
