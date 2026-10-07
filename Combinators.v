(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List Zmod Bool ZArith.
From Guru Require Import Primitives Library Syntax Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Import ListNotations.

(* ===========================================================================
 * Derived PHOAS Expression & Action Combinators
 * =========================================================================== *)

Section Phoas.
  Variable ty: Kind -> Type.
  Local Notation Expr := (Expr ty).

  Definition Neq k (e1 e2: Expr k) := Not (Eq e1 e2).

  Definition Sub n (a b: Expr (Bit n)): Expr (Bit n) := Add [a; Not b; Const _ (Bit n) Zmod.one].

  Definition Neg n (a: Expr (Bit n)): Expr (Bit n) := Add [Not a; Const _ (Bit n) Zmod.one].

  Definition Ugt n (a b: Expr (Bit n)): Expr Bool := Ult b a.

  Definition Ule n (a b: Expr (Bit n)): Expr Bool := Not (Ugt a b).

  Definition Uge n (a b: Expr (Bit n)): Expr Bool := Not (Ult a b).

  Definition castBits ni no (pf: ni = no) (e: Expr (Bit ni)) :=
    Z_cast (P := fun n => Expr (Bit n)) pf e.

  Definition castBitsKind1 k: forall n (pf: Bit n = k), Expr (Bit n) -> Expr k :=
    match k return forall n (pf: Bit n = k), Expr (Bit n) -> Expr k with
    | Bit m => fun _ pf e => castBits (f_equal (fun k'=> match k' with
                                                         | Bit n' => n'
                                                         | _ => Z0
                                                         end) pf) e
    | k' => fun _ pf _ => match match pf in _ = Y return match Y with
                                                         | Bit _ => True
                                                         | _ => False
                                                         end with
                                | eq_refl => I
                                end return Expr k'
                          with
                          end
      end.

  Definition castBitsKind2 k: forall n (pf: Bit n = k), Expr k -> Expr (Bit n) :=
    match k return forall n (pf: Bit n = k), Expr k -> Expr (Bit n) with
    | Bit m => fun _ pf e => castBits (f_equal (fun k'=> match k' with
                                                         | Bit n' => n'
                                                         | _ => Z0
                                                         end) (eq_sym pf)) e
    | _ => fun n pf _ => match match pf in _ = Y return match Y with
                                                        | Bit _ => True
                                                        | _ => False
                                                        end with
                               | eq_refl => I
                               end return Expr (Bit n)
                         with
                         end
      end.

  Definition ConstExtract msb n lsb (e: Expr (Bit (lsb + n + msb))): Expr (Bit n) :=
    @TruncMsb _ n lsb (@TruncLsb _ msb (lsb + n) e).

  Definition isZero k (e: Expr k) := Eq e (Const _ k (getDefault k)).
  Definition isNotZero k (e: Expr k) := Not (isZero e).
  Definition UOr k (e: Expr k) := isNotZero e.
  Definition isAllOnes k (e: Expr k) := Eq e (Const _ k (InvDefault k)).
  Definition UAnd k (e: Expr k) := isAllOnes e.

  Definition msbIsZero k (e: Expr k): Expr Bool :=
    (isZero (TruncMsb 1 (kindSize k-1) (castBits (eq_sym (Z.sub_add _ _)) (ToBit e)))).

  Definition SignExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (lsb + msb)) :=
    Concat (ITE (msbIsZero e)
              (Const _ (Bit _) (getDefault _))
              (Const _ (Bit _) (InvDefault _))) e.

  Definition OneExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (lsb + msb)) :=
    Concat (Const _ (Bit msb) (Zmod.of_Z _ (-1))) e.

  Definition ZeroExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (lsb + msb)) :=
    Concat (Const _ (Bit _) Zmod.zero) e.

  Definition ZeroExtendTo outSz inSz (e: Expr (Bit inSz)) := ZeroExtend (outSz - inSz) e.
  Definition SignExtendTo outSz inSz (e: Expr (Bit inSz)) := SignExtend (outSz - inSz) e.

  Fixpoint replicate sz (e: Expr (Bit sz)) n : Expr (Bit (NatZ_mul n sz)) :=
    match n return Expr (Bit (NatZ_mul n sz)) with
    | 0 => Const _ (Bit _) Zmod.zero
    | S m => Concat (replicate e m) e
    end.

  Definition rotateRight n (e: Expr (Bit n)) m (shamt: Expr (Bit m)) :=
    ( Or [Srl e shamt; Sll e (Sub (Const _ (Bit m) (Zmod.of_Z _ n)) shamt)]).

  Definition rotateLeft n (e: Expr (Bit n)) m (shamt: Expr (Bit m)) :=
    ( Or [Sll e shamt; Srl e (Sub (Const _ (Bit m) (Zmod.of_Z _ n)) shamt)]).

  Definition mkBoolArray n := FromBit (ty := ty) (Array (Z.to_nat n) Bool).

  Section ArrayBuilder.
    Variable n: nat.
    Variable k: Kind.
    Variable f: FinType n -> Expr k.
    Definition ArrayBuilder: Expr (Array n k).
      Proof.
        refine (BuildArray (@Build_SameTuple _ n (map f (genFinType n))
                              (transparent_Is_true _ _))).
        abstract (rewrite length_map, genFinType_length, Nat.eqb_refl; auto).
      Defined.
  End ArrayBuilder.

  Section ArrayReverse.
    Variable n: nat.
    Variable k: Kind.
    Variable arr: Expr (Array n k).
    Definition ArrayReverse: Expr (Array n k).
      Proof.
        refine (BuildArray (@Build_SameTuple _ n (map (fun i => ReadArrayConst arr i) (rev_tail (genFinType n) nil))
                              (transparent_Is_true _ _))).
        abstract (rewrite rev_tail_fast, length_map, length_rev, genFinType_length, Nat.eqb_refl; auto).
      Defined.
  End ArrayReverse.

  Inductive LetExpr (k: Kind): Type :=
  | RetE (e: Expr k)
  | SystemE (ls: list (SysT ty)) (cont: LetExpr k)
  | LetEx (s: string) k' (e: LetExpr k') (cont: ty k' -> LetExpr k)
  | IfElseE (s: string) (p: Expr Bool) k' (t f: LetExpr k') (cont: ty k' -> LetExpr k).

  Section ArrayShiftRotate.
    Variable n: nat.
    Variable k: Kind.
    Variable arr: Expr (Array n k).
    Variable p: Z.
    Variable shamt: Expr (Bit p).

    Section StagedShift.
      Variable step: FinType n -> nat -> Expr (Array n k) -> Expr k.
      Fixpoint stagedShift (cur: ty (Array n k))
                           (stage: nat) (count: nat) : LetExpr (Array n k) :=
        match count with
        | 0 => RetE (Var _ _ cur)
        | S rem =>
            let cond := isNotZero (And [shamt; Const _ (Bit p) (bits.of_Z p (Z.of_nat (Nat.pow 2 stage)))]) in
            let d := Nat.pow 2 stage in
            let shifted := ArrayBuilder (fun i: FinType n => step i d (Var _ _ cur)) in
            LetEx "nextArr" (RetE (ITE cond shifted (Var _ _ cur)))
              (fun nextArr => stagedShift nextArr (S stage) rem)
        end.

      Definition fullShift : LetExpr (Array n k) :=
        LetEx "initArr" (RetE arr) (fun initArr => stagedShift initArr 0 (Nat.log2_up n)).
    End StagedShift.

    Definition ArraySll : LetExpr (Array n k) :=
      fullShift (fun i d cur =>
        if Nat.leb d i.(finNum)
        then ReadArray cur (Const _ (Bit p) (bits.of_Z p (Z.of_nat (i.(finNum) - d))))
        else Const _ k (getDefault k)).

    Definition ArraySrl : LetExpr (Array n k) :=
      fullShift (fun i d cur =>
        if Nat.ltb (i.(finNum) + d) n
        then ReadArray cur (Const _ (Bit p) (bits.of_Z p (Z.of_nat (i.(finNum) + d))))
        else Const _ k (getDefault k)).

    Definition ArrayRotl : LetExpr (Array n k) :=
      fullShift (fun i d cur =>
        let src := (i.(finNum) + n - (d mod n)) mod n in
        ReadArray cur (Const _ (Bit p) (bits.of_Z p (Z.of_nat src)))).

    Definition ArrayRotr : LetExpr (Array n k) :=
      fullShift (fun i d cur =>
        let src := (i.(finNum) + (d mod n)) mod n in
        ReadArray cur (Const _ (Bit p) (bits.of_Z p (Z.of_nat src)))).
  End ArrayShiftRotate.

  Section InvMask.
    Variable n: nat.
    Variable m: Z.
    Variable shamt: Expr (Bit m).
    Definition invMask: Expr (Array n Bool) := FromBit (Array n Bool) (Sll (Const _ _ (InvDefault _)) shamt).
  End InvMask.

  Section MaskArray.
    Variable n: nat.
    Variable k: Kind.
    Variable arr: Expr (Array n k).
    Variable mask: Expr (Array n Bool).
    Variable def: Expr k.
    Definition maskArray := ArrayBuilder (fun i => ITE (ReadArrayConst mask i) (ReadArrayConst arr i) def).
  End MaskArray.

  Section ZeroExtendArray.
    Variable n: nat.
    Variable m: Z.
    Variable shamt: Expr (Bit m).
    Variable k: Kind.
    Variable arr: Expr (Array n k).

    Section ExtendArray.
      Variable val: Expr k.
      Definition extendArray := maskArray arr (Not (invMask _ shamt)) val.
    End ExtendArray.

    Definition ArrayZeroExtend := extendArray (Const _ _ (getDefault k)).
    Definition ArrayOneExtend := extendArray (Const _ _ (InvDefault k)).
    Definition ArraySignExtend := extendArray
                                    (ITE (msbIsZero (ReadArray arr (Sub shamt (Const _ (Bit _) (bits.of_Z _ 1)))))
                                       (Const _ _ (getDefault k))
                                       (Const _ _ (InvDefault k))).
  End ZeroExtendArray.

  (* To be used only if there are multiple disjoint cases *)
  Section CaseDefault.
      Variable k: Kind.
      Variable ls: list (Expr Bool * Expr k).
      Variable def: Expr k.
      Definition caseDefault :=
        ITE (Or (map fst ls)) (Or (map (fun '(p, v) => ITE p v (Const _ k (getDefault k))) ls)) def.
  End CaseDefault.

  Section UpdateArrayBySz.
    Definition updateArrayBySz (m: Z)
      (shamt: Expr (Bit m))
      (k: Kind)
      (n: nat)
      (oldVal newVal: Expr (Array n k))
      : Expr (Array n k) :=
      ArrayBuilder (fun i => ITE (ReadArrayConst (Not (invMask n shamt)) i)
                               (ReadArrayConst newVal i)
                               (ReadArrayConst oldVal i)).

    Definition updateBitsByChunkSz (n: nat) (sz: Z) (m: Z)
      (shamt: Expr (Bit m))
      (oldVal newVal: Expr (Bit (NatZ_mul n sz)))
      : Expr (Bit (NatZ_mul n sz)) :=
      ToBit (updateArrayBySz shamt
               (FromBit (Array n (Bit sz)) oldVal)
               (FromBit (Array n (Bit sz)) newVal)).
  End UpdateArrayBySz.

  Definition fullFormat zeroPad format: forall k, FullFormat k :=
    KindCustomInd (P := fun k => FullFormat k)
      (FBool zeroPad 1 format)
      (fun n => FBit n zeroPad ((n+3)/4) format)
      FStruct
      FArray
      (fun ls _ => FTaggedUnion format format).

  Definition DispHex k (e: Expr k) :=
    DispExpr e (fullFormat false Hex k).

  Definition DispBinary k (e: Expr k) :=
    DispExpr e (fullFormat false Binary k).

  Definition DispDecimal k (e: Expr k) :=
    DispExpr e (fullFormat false Decimal k).

  Definition DispHex0 k (e: Expr k) :=
    DispExpr e (fullFormat true Hex k).

  Definition DispBinary0 k (e: Expr k) :=
    DispExpr e (fullFormat true Binary k).

  Definition DispDecimal0 k (e: Expr k) :=
    DispExpr e (fullFormat true Decimal k).

  Fixpoint countLeadingZerosLoop ni no (arr: Expr (Array ni Bool)) (count: nat) (over: ty Bool) (accum: ty (Bit no))
    : LetExpr (Bit no) :=
    match count with
    | 0 => RetE (Var _ _ accum)
    | S m =>
      let curr := readNatToFinType (Const _ Bool false) (ReadArrayConst arr) m in
      LetEx "cond" (RetE (Or [Var _ _ over; curr]))
        (fun cond => LetEx "accum_next" (RetE (Add [Var _ _ accum; ITE (Var _ _ cond) (Const _ (Bit no) Zmod.zero)
                                                                     (Const _ (Bit no) Zmod.one)]))
                       (fun accum_next => @countLeadingZerosLoop ni no arr m cond accum_next))
    end.

  Fixpoint countTrailingZerosLoop ni no (arr: Expr (Array ni Bool)) (idx: nat) (count: nat) (over: ty Bool)
    (accum: ty (Bit no)) : LetExpr (Bit no) :=
    match count with
    | 0 => RetE (Var _ _ accum)
    | S m =>
      let curr := readNatToFinType (Const _ Bool false) (ReadArrayConst arr) idx in
      LetEx "cond" (RetE (Or [Var _ _ over; curr]))
        (fun cond => LetEx "accum_next" (RetE (Add [Var _ _ accum; ITE (Var _ _ cond) (Const _ (Bit no) Zmod.zero)
                                                                     (Const _ (Bit no) Zmod.one)]))
                       (fun accum_next => @countTrailingZerosLoop ni no arr (S idx) m cond accum_next))
    end.

  Section Slice.
    Variable n: nat.
    Variable k: Kind.
    Variable arr: Expr (Array n k).
    Variable m: Z.
    Variable addr: Expr (Bit m).
    Variable sliceSz: nat.
    Definition slice: Expr (Array sliceSz k) :=
      ArrayBuilder (fun i => (ReadArray arr (Add [addr; Const _ (Bit _) (Zmod.of_Z _ (Z.of_nat i.(finNum)))]))).

    Variable upd: Expr (Array sliceSz k).
    Variable updSzSz: Z.
    Variable updSz: Expr (Bit updSzSz).
    Definition updSlice: LetExpr (Array n k) :=
      LetEx "iMask" (RetE (invMask sliceSz updSz))
        (fun iMask => RetE (fold_left (fun updArr i =>
                                         let idx := Add [addr; Const _ (Bit _) (Zmod.of_Z _ (Z.of_nat i.(finNum)))] in
                                         UpdateArray updArr idx
                                                     (ITE (ReadArrayConst (Var _ _ iMask) i)
                                                          (ReadArray arr idx)
                                                          (ReadArrayConst upd i))) (genFinType sliceSz) arr)).
  End Slice.

End Phoas.

Fixpoint evalLetExpr k (le: LetExpr type k): type k :=
  match le with
  | RetE e => evalExpr e
  | SystemE ls cont => evalLetExpr cont
  | LetEx s le cont => let t := evalLetExpr le in evalLetExpr (cont t)
  | IfElseE s p t f cont => evalLetExpr (cont (if evalExpr p
                                                  then evalLetExpr t
                                                  else evalLetExpr f))
  end.

Section ActionDef.
  Variable ty: Kind -> Type.
  Variable t: Tree DomainElem.

  Fixpoint toAction k (le: LetExpr ty k) : @Action ty t k :=
    match le with
    | RetE e => Return e
    | SystemE ls cont => System ls (toAction cont)
    | LetEx s le cont => LetAction s (toAction le) (fun x => toAction (cont x))
    | IfElseE s p t' f' cont => IfElse s p (toAction t') (toAction f') (fun x => toAction (cont x))
    end.
End ActionDef.

Definition ITE0 {ty k} (p: Expr ty Bool) (e: Expr ty k) : Expr ty k :=
  ITE p e (Const _ k (getDefault k)).

Definition Kind_eqb_eq (k1 k2: Kind) : Is_true (Kind_eqb k1 k2) -> k1 = k2 :=
  match Kind_BoolSpec k1 k2 in (BoolSpec _ _ b) return Is_true b -> k1 = k2 with
  | BoolSpecT x => fun _ => x
  | BoolSpecF _ => fun pf => match pf with end
  end.

Section HeteroRegActions.
  Variable ty : Kind -> Type.

  Record RegOfKind {t: Tree DomainElem} (k: Kind) := {
    rk_path : RegPath t;
    rk_pf : Is_true (Kind_eqb (regKind (getRegFromPath rk_path)) k)
  }.

  Fixpoint writeRegsListHelper
    (curr: nat)
    {k sz t}
    (paths: list (RegOfKind (t:=t) k))
    (idx: Expr ty (Bit sz))
    (newVal: Expr ty k) : @Action ty t (Bit 0) :=
    match paths with
    | nil => Return (Const _ (Bit 0) Zmod.zero)
    | rk :: rest =>
        let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
        let castedVal := eq_rect k (fun K => Expr ty K) newVal _ (eq_sym pf_eq) in
        IfElse EmptyString (Eq idx (Const _ (Bit sz) (Zmod.of_Z _ (Z.of_nat curr))))
          (WriteReg rk.(rk_path) castedVal (Return (Const _ (Bit 0) Zmod.zero)))
          (Return (Const _ (Bit 0) Zmod.zero))
          (fun _ => writeRegsListHelper (S curr) rest idx newVal)
    end.

  Definition writeRegsList := @writeRegsListHelper 0.

  Fixpoint readRegsListHelper (curr: nat) {k} (acc: list (Expr ty k)) {sz t}
    (paths: list (RegOfKind (t:=t) k))
    (idx: Expr ty (Bit sz)) : @Action ty t k :=
    match paths with
    | nil => Return (Or acc)
    | rk :: rest =>
        ReadReg "" rk.(rk_path) (fun val_ty =>
          let pf_eq := Kind_eqb_eq _ _ rk.(rk_pf) in
          let casted_ty := eq_rect (regKind (getRegFromPath rk.(rk_path))) (fun K => ty K) val_ty _ pf_eq in
          let iteVal := ITE0 (Eq idx (Const _ (Bit sz) (Zmod.of_Z _ (Z.of_nat curr)))) (Var _ _ casted_ty) in
          readRegsListHelper (S curr) (iteVal :: acc) rest idx
        )
    end.

  Definition readRegsList {k} := @readRegsListHelper 0 _ (@nil (Expr ty k)).
End HeteroRegActions.
