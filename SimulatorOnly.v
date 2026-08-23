(*
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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
           {updSzSz : Z}
           (addr : Expr ty (Bit (Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)))))
           (upd : Expr ty (Array sliceSz (getMemFromPath memPath).(memKind)))
           (updSz : Expr ty (Bit updSzSz))
           : Action ty t (Bit 0) :=
    match curr with
    | 0%nat => Retv
    | S rest =>
        let idxSz := Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)) in
        let idxExpr := Const ty (Bit idxSz) (Zmod.of_Z _ (Z.of_nat rest)) in
        let arrIdxExpr := Const ty (Bit (Z.log2_up (Z.of_nat sliceSz))) (Zmod.of_Z _ (Z.of_nat rest)) in
        let szIdxExpr := Const ty (Bit updSzSz) (Zmod.of_Z _ (Z.of_nat rest)) in
        Let isEn : Bool <- Slt szIdxExpr updSz ;
        If #isEn Then (
          WriteMem memPath (Add [ addr ; idxExpr ]) (ReadArray upd arrIdxExpr) Retv
        ) ;
        updSliceMemLoop (memPath := memPath) rest addr upd updSz
    end.

  Definition updSliceMem
             {t : Tree Elem}
             {ty : Kind -> Type}
             (memPath : MemPath t)
             (sliceSz : nat)
             {updSzSz : Z}
             (addr : Expr ty (Bit (Z.log2_up (Z.of_nat (getMemFromPath memPath).(memSize)))))
             (upd : Expr ty (Array sliceSz (getMemFromPath memPath).(memKind)))
             (updSz : Expr ty (Bit updSzSz))
             : Action ty t (Bit 0) :=
    updSliceMemLoop (memPath := memPath) (sliceSz := sliceSz) sliceSz addr upd updSz.

End MemSliceOperations.

Arguments sliceMem [t] [ty] memPath portPos sliceSz addr.
Arguments updSliceMem [t] [ty] memPath sliceSz [updSzSz] addr upd updSz.
