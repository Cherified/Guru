(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Library Syntax Notations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ===========================================================================
 * Generic Multi-Item Slice Operations for EMem (Non-synthesizable, Spec/Sim only)
 * =========================================================================== *)

Section MemSliceOperations.

  Fixpoint sliceMemLoop
           {t : Tree Elem}
           {ty : Kind -> Type}
           (memPath : MemPath t)
           (portPos : Is_true (0 <? (getMemFromPath memPath).(memPort))%nat)
           {sliceSz : nat}
           (curr : nat)
           (acc : Expr ty (Array sliceSz (getMemFromPath memPath).(memKind)))
           (addr : Expr ty (Bit (Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)))))
           : Action ty t (Array sliceSz (getMemFromPath memPath).(memKind)) :=
    match curr with
    | 0%nat => Return acc
    | S rest =>
        let idxSz := Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)) in
        let idxExpr := Const ty (Bit idxSz) (Zmod.of_Z _ (Z.of_nat rest)) in
        let arrIdxExpr := Const ty (Bit (Z.log2_up (Z.of_nat sliceSz))) (Zmod.of_Z _ (Z.of_nat rest)) in
        ReadRqMem memPath (Add [ addr ; idxExpr ]) (@Build_FinType (getMemFromPath memPath).(memPort) 0 portPos) (
          ReadRpMem "" memPath (@Build_FinType (getMemFromPath memPath).(memPort) 0 portPos) (fun v =>
            Let nextAcc : Array sliceSz (getMemFromPath memPath).(memKind) <- UpdateArray acc arrIdxExpr (Var _ _ v) ;
            sliceMemLoop (memPath := memPath) portPos rest #nextAcc addr
          )
        )
    end.

  Definition sliceMem
             {t : Tree Elem}
             {ty : Kind -> Type}
             (memPath : MemPath t)
             (portPos : Is_true (0 <? (getMemFromPath memPath).(memPort))%nat)
             (sliceSz : nat)
             (addr : Expr ty (Bit (Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)))))
             : Action ty t (Array sliceSz (getMemFromPath memPath).(memKind)) :=
    sliceMemLoop (memPath := memPath) portPos (sliceSz := sliceSz) sliceSz ConstDef addr.

  Fixpoint updSliceMemLoop
           {t : Tree Elem}
           {ty : Kind -> Type}
           (memPath : MemPath t)
           {sliceSz : nat}
           (curr : nat)
           (addr : Expr ty (Bit (Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)))))
           (upd : Expr ty (Array sliceSz (getMemFromPath memPath).(memKind)))
           (mask : Expr ty (Array sliceSz Bool))
           : Action ty t (Bit 0) :=
    match curr with
    | 0%nat => Retv
    | S rest =>
        let idxSz := Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)) in
        let idxExpr := Const ty (Bit idxSz) (Zmod.of_Z _ (Z.of_nat rest)) in
        let arrIdxExpr := Const ty (Bit (Z.log2_up (Z.of_nat sliceSz))) (Zmod.of_Z _ (Z.of_nat rest)) in
        Let isEn : Bool <- ReadArray mask arrIdxExpr ;
        If #isEn Then (
          WriteMem memPath (Add [ addr ; idxExpr ]) (ReadArray upd arrIdxExpr) Retv
        ) ;
        updSliceMemLoop (memPath := memPath) rest addr upd mask
    end.

  Definition updSliceMem
             {t : Tree Elem}
             {ty : Kind -> Type}
             (memPath : MemPath t)
             (sliceSz : nat)
             (addr : Expr ty (Bit (Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)))))
             (upd : Expr ty (Array sliceSz (getMemFromPath memPath).(memKind)))
             (mask : Expr ty (Array sliceSz Bool))
             : Action ty t (Bit 0) :=
    updSliceMemLoop (memPath := memPath) (sliceSz := sliceSz) sliceSz addr upd mask.

End MemSliceOperations.

Arguments sliceMem [t] [ty] memPath portPos sliceSz addr.
Arguments updSliceMem [t] [ty] memPath sliceSz addr upd mask.
