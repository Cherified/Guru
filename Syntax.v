(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List Zmod Bool ZArith.
From Guru Require Import Primitives.

Set Implicit Arguments.
Set Asymmetric Patterns.

Import ListNotations.

(* ===========================================================================
 * PHOAS Expressions (Expr)
 * =========================================================================== *)

Unset Positivity Checking.
Section Phoas.
  Variable ty: Kind -> Type.

  Inductive Expr: Kind -> Type :=
  | Var k: ty k -> Expr k
  | Const k: type k -> Expr k
  | Or k: list (Expr k) -> Expr k
  | And k: list (Expr k) -> Expr k
  | Xor k: list (Expr k) -> Expr k
  | Not k: Expr k -> Expr k
  | TruncLsb msb lsb: Expr (Bit (lsb + msb)%Z) -> Expr (Bit lsb)
  | TruncMsb msb lsb: Expr (Bit (lsb + msb)%Z) -> Expr (Bit msb)
  | UXor n: Expr (Bit n) -> Expr Bool
  | Add n: list (Expr (Bit n)) -> Expr (Bit n)
  | Mul n: list (Expr (Bit n)) -> Expr (Bit n)
  | Div n: Expr (Bit n) -> Expr (Bit n) -> Expr (Bit n)
  | Rem n: Expr (Bit n) -> Expr (Bit n) -> Expr (Bit n)
  | Sll n m: Expr (Bit n) -> Expr (Bit m) -> Expr (Bit n)
  | Srl n m: Expr (Bit n) -> Expr (Bit m) -> Expr (Bit n)
  | Sra n m: Expr (Bit n) -> Expr (Bit m) -> Expr (Bit n)
  | Concat msb lsb: Expr (Bit msb) -> Expr (Bit lsb) -> Expr (Bit (lsb + msb))
  | ITE k: Expr Bool -> Expr k -> Expr k -> Expr k
  | Eq k: Expr k -> Expr k -> Expr Bool
  | Ult n: Expr (Bit n) -> Expr (Bit n) -> Expr Bool
  | ReadStruct (ls: list (string * Kind)) (e: Expr (Struct ls)) (i: FinStruct ls): Expr (fieldK i)
  | ReadArray n m k: Expr (Array n k) -> Expr (Bit m) -> Expr k
  | ReadArrayConst n k: Expr (Array n k) -> FinType n -> Expr k
  | UpdateStruct [ls: list (string * Kind)] (e: Expr (Struct ls)) (p: FinStruct ls) (v: Expr (fieldK p)):
    Expr (Struct ls)
  | UpdateArray [n k] (e: Expr (Array n k)) m (i: Expr (Bit m)) (v: Expr k): Expr (Array n k)
  | UpdateArrayConst [n k] (e: Expr (Array n k)) (p: FinType n) (v: Expr k): Expr (Array n k)
  | ToBit k (e: Expr k): Expr (Bit (kindSize k))
  | FromBit k (e: Expr (Bit (kindSize k))): Expr k
  | ReadUnionTag [ls: list (string * Kind)] (e: Expr (TaggedUnion ls)) (i: FinType (length ls)): Expr Bool
  | ReadUnionData [ls: list (string * Kind)] (e: Expr (TaggedUnion ls)) (i: FinType (length ls)):
    Expr (snd (nth_pf i.(finLt)))
  | BuildUnion [ls: list (string * Kind)] (i: FinType (length ls)) (e: Expr (snd (nth_pf i.(finLt)))):
    Expr (TaggedUnion ls)
  (* The following 2 don't pass positivity check in Rocq *)
  | BuildStruct [ls: list (string * Kind)] (vals: DiffTuple (fun x => Expr (snd x)) ls): Expr (Struct ls)
  | BuildArray [n k] (vals: SameTuple (Expr k) n): Expr (Array n k).
End Phoas.
Set Positivity Checking.

Inductive BitFormat :=
| Binary
| Decimal
| Hex.

Unset Positivity Checking.
Section Phoas.
  Inductive FullFormat: Kind -> Type :=
  | FBool: bool -> Z -> BitFormat -> FullFormat Bool
  | FBit n: bool -> Z -> BitFormat -> FullFormat (Bit n)
  | FStruct [ls]: DiffTuple (fun x => FullFormat (snd x)) ls -> FullFormat (Struct ls)
  | FArray n k: FullFormat k -> FullFormat (@Array n k)
  | FTaggedUnion [ls]: BitFormat -> BitFormat -> FullFormat (TaggedUnion ls).
End Phoas.
Set Positivity Checking.

Section Phoas.
  Variable ty: Kind -> Type.
  Local Abbreviation Expr := (Expr ty).

  Inductive SysT: Type :=
  | DispString (s: string): SysT
  | DispExpr k (e: Expr k) (ff: FullFormat k): SysT
  | Finish: SysT.
End Phoas.

(* ===========================================================================
 * Hardware State Elements & Tree Structure (Elem, Tree)
 * =========================================================================== *)

Record Reg := {
  regKind : Kind ;
  regInit: option (type regKind)
}.

Record Mem := {
  memSize: nat;
  memKind: Kind;
  memPort: nat;
  memInit: option (option (type (Array memSize memKind)))
}.

(* A specification-only register holding an arbitrary Gallina value. It is read
   and written only by CallGallina, and the compiler ignores it. Unlike Reg it
   always has an initial value, since an arbitrary Type has no default. *)
Record GallinaReg := {
  gRegType : Type ;
  gRegInit : gRegType
}.

Inductive Elem :=
| EReg (r : Reg)
| EMem (m : Mem)
| ESend (k : Kind)
| ERecv (k : Kind)
| EGallinaReg (r : GallinaReg).

Definition ElemState (e: Elem) : Type :=
  match e with
  | EReg r => type (regKind r)
  | EMem m => type (Array (memSize m) (memKind m)) ** type (Array (memPort m) (memKind m))
  | ESend k => list (type k)
  | ERecv k => list (type k)
  | EGallinaReg r => gRegType r
  end.

Definition isRegElem (e: Elem) : bool :=
  match e with
  | EReg _ => true
  | _ => false
  end.

Definition isMemElem (e: Elem) : bool :=
  match e with
  | EMem _ => true
  | _ => false
  end.

Definition isSendElem (e: Elem) : bool :=
  match e with
  | ESend _ => true
  | _ => false
  end.

Definition isRecvElem (e: Elem) : bool :=
  match e with
  | ERecv _ => true
  | _ => false
  end.

Definition isGallinaRegElem (e: Elem) : bool :=
  match e with
  | EGallinaReg _ => true
  | _ => false
  end.

Definition getRegFromElemUnsafe (e: Elem) : Reg :=
  match e with
  | EReg r => r
  | _ => {| regKind := Bool; regInit := None |}
  end.

Definition getMemFromElemUnsafe (e: Elem) : Mem :=
  match e with
  | EMem m => m
  | _ => {| memSize := 0; memKind := Bool; memPort := 0; memInit := None |}
  end.

Definition getSendKindFromElem (e: Elem) : Kind :=
  match e with
  | ESend k => k
  | _ => Bool
  end.

Definition getRecvKindFromElem (e: Elem) : Kind :=
  match e with
  | ERecv k => k
  | _ => Bool
  end.

Definition getGallinaRegFromElemUnsafe (e: Elem) : GallinaReg :=
  match e with
  | EGallinaReg r => r
  | _ => {| gRegType := unit; gRegInit := tt |}
  end.

Definition getLeafElem {t: Tree Elem} (p: LeafPath t) : Elem :=
  getLeaf p.

Definition getRegFromPathUnsafe (t: Tree Elem) (p: LeafPath t) : Reg :=
  getRegFromElemUnsafe (getLeafElem p).

Definition getMemFromPathUnsafe (t: Tree Elem) (p: LeafPath t) : Mem :=
  getMemFromElemUnsafe (getLeafElem p).

Definition getSendKindFromPath (t: Tree Elem) (p: LeafPath t) : Kind :=
  getSendKindFromElem (getLeafElem p).

Definition getRecvKindFromPath (t: Tree Elem) (p: LeafPath t) : Kind :=
  getRecvKindFromElem (getLeafElem p).

Definition getGallinaRegFromPathUnsafe (t: Tree Elem) (p: LeafPath t) : GallinaReg :=
  getGallinaRegFromElemUnsafe (getLeafElem p).

Arguments getLeafElem [t] p / .
Arguments getRegFromPathUnsafe [t] p / .
Arguments getMemFromPathUnsafe [t] p / .
Arguments getSendKindFromPath [t] p / .
Arguments getRecvKindFromPath [t] p / .
Arguments getGallinaRegFromPathUnsafe [t] p / .

Record RegPath (t: Tree Elem) := {
  regPath : LeafPath t;
  regPathPf : Is_true (isRegElem (getLeafElem regPath))
}.

Record MemPath (t: Tree Elem) := {
  memPath : LeafPath t;
  memPathPf : Is_true (isMemElem (getLeafElem memPath))
}.

Record SendPath (t: Tree Elem) := {
  sendPath : LeafPath t;
  sendPathPf : Is_true (isSendElem (getLeafElem sendPath))
}.

Record RecvPath (t: Tree Elem) := {
  recvPath : LeafPath t;
  recvPathPf : Is_true (isRecvElem (getLeafElem recvPath))
}.

Record GallinaRegPath (t: Tree Elem) := {
  gRegPath : LeafPath t;
  gRegPathPf : Is_true (isGallinaRegElem (getLeafElem gRegPath))
}.

Definition getRegFromPath (t: Tree Elem) (x: RegPath t) : Reg :=
  getRegFromPathUnsafe x.(regPath).

Definition getMemFromPath (t: Tree Elem) (x: MemPath t) : Mem :=
  getMemFromPathUnsafe x.(memPath).

Definition getSendKind (t: Tree Elem) (x: SendPath t) : Kind :=
  getSendKindFromPath x.(sendPath).

Definition getRecvKind (t: Tree Elem) (x: RecvPath t) : Kind :=
  getRecvKindFromPath x.(recvPath).

Definition getGallinaRegFromPath (t: Tree Elem) (x: GallinaRegPath t) : GallinaReg :=
  getGallinaRegFromPathUnsafe x.(gRegPath).

Arguments getRegFromPath [t] x.
Arguments getMemFromPath [t] x.
Arguments getSendKind [t] x.
Arguments getRecvKind [t] x.
Arguments getGallinaRegFromPath [t] x.

Definition getRegFromElemTypeEq (e: Elem) (pf: Is_true (isRegElem e)) :
  ElemState e = type (regKind (getRegFromElemUnsafe e)) :=
  match e return Is_true (isRegElem e) -> ElemState e = type (regKind (getRegFromElemUnsafe e)) with
  | EReg r => fun _ => eq_refl
  | EMem _ => fun pf => match pf with end
  | ESend _ => fun pf => match pf with end
  | ERecv _ => fun pf => match pf with end
  | EGallinaReg _ => fun pf => match pf with end
  end pf.
Arguments getRegFromElemTypeEq e pf / .

Definition getRegFromPathTypeEq (t: Tree Elem) (x: RegPath t) :
  ElemState (getLeaf x.(regPath)) = type (regKind (getRegFromPath x)) :=
  getRegFromElemTypeEq (getLeafElem x.(regPath)) x.(regPathPf).
Arguments getRegFromPathTypeEq [t] x / .

Definition getMemFromElemTypeEq (e: Elem) (pf: Is_true (isMemElem e)) :
  ElemState e =
  type (Array (getMemFromElemUnsafe e).(memSize) (getMemFromElemUnsafe e).(memKind)) **
  type (Array (getMemFromElemUnsafe e).(memPort) (getMemFromElemUnsafe e).(memKind)) :=
  match e return Is_true (isMemElem e) ->
                 ElemState e =
                 type (Array (getMemFromElemUnsafe e).(memSize) (getMemFromElemUnsafe e).(memKind)) **
                 type (Array (getMemFromElemUnsafe e).(memPort) (getMemFromElemUnsafe e).(memKind)) with
  | EReg _ => fun pf => match pf with end
  | EMem m => fun _ => eq_refl
  | ESend _ => fun pf => match pf with end
  | ERecv _ => fun pf => match pf with end
  | EGallinaReg _ => fun pf => match pf with end
  end pf.
Arguments getMemFromElemTypeEq e pf / .

Definition getMemFromPathTypeEq (t: Tree Elem) (x: MemPath t) :
  ElemState (getLeaf x.(memPath)) =
  type (Array (getMemFromPath x).(memSize) (getMemFromPath x).(memKind)) **
  type (Array (getMemFromPath x).(memPort) (getMemFromPath x).(memKind)) :=
  getMemFromElemTypeEq (getLeafElem x.(memPath)) x.(memPathPf).
Arguments getMemFromPathTypeEq [t] x / .

Definition getSendFromElemTypeEq (e: Elem) (pf: Is_true (isSendElem e)) :
  ElemState e = list (type (getSendKindFromElem e)) :=
  match e return Is_true (isSendElem e) -> ElemState e = list (type (getSendKindFromElem e)) with
  | EReg _ => fun pf => match pf with end
  | EMem _ => fun pf => match pf with end
  | ESend k => fun _ => eq_refl
  | ERecv _ => fun pf => match pf with end
  | EGallinaReg _ => fun pf => match pf with end
  end pf.
Arguments getSendFromElemTypeEq e pf / .

Definition getSendFromPathTypeEq (t: Tree Elem) (x: SendPath t) :
  ElemState (getLeaf x.(sendPath)) = list (type (getSendKind x)) :=
  getSendFromElemTypeEq (getLeafElem x.(sendPath)) x.(sendPathPf).
Arguments getSendFromPathTypeEq [t] x / .

Definition getRecvFromElemTypeEq (e: Elem) (pf: Is_true (isRecvElem e)) :
  ElemState e = list (type (getRecvKindFromElem e)) :=
  match e return Is_true (isRecvElem e) -> ElemState e = list (type (getRecvKindFromElem e)) with
  | EReg _ => fun pf => match pf with end
  | EMem _ => fun pf => match pf with end
  | ESend _ => fun pf => match pf with end
  | ERecv k => fun _ => eq_refl
  | EGallinaReg _ => fun pf => match pf with end
  end pf.
Arguments getRecvFromElemTypeEq e pf / .

Definition getRecvFromPathTypeEq (t: Tree Elem) (x: RecvPath t) :
  ElemState (getLeaf x.(recvPath)) = list (type (getRecvKind x)) :=
  getRecvFromElemTypeEq (getLeafElem x.(recvPath)) x.(recvPathPf).
Arguments getRecvFromPathTypeEq [t] x / .

Definition getGallinaRegFromElemTypeEq (e: Elem) (pf: Is_true (isGallinaRegElem e)) :
  ElemState e = gRegType (getGallinaRegFromElemUnsafe e) :=
  match e return Is_true (isGallinaRegElem e) -> ElemState e = gRegType (getGallinaRegFromElemUnsafe e) with
  | EReg _ => fun pf => match pf with end
  | EMem _ => fun pf => match pf with end
  | ESend _ => fun pf => match pf with end
  | ERecv _ => fun pf => match pf with end
  | EGallinaReg r => fun _ => eq_refl
  end pf.
Arguments getGallinaRegFromElemTypeEq e pf / .

Definition getGallinaRegFromPathTypeEq (t: Tree Elem) (x: GallinaRegPath t) :
  ElemState (getLeaf x.(gRegPath)) = gRegType (getGallinaRegFromPath x) :=
  getGallinaRegFromElemTypeEq (getLeafElem x.(gRegPath)) x.(gRegPathPf).
Arguments getGallinaRegFromPathTypeEq [t] x / .

Definition castStateReg (t: Tree Elem) (x: RegPath t)
  (s: ElemState (getLeaf x.(regPath))) : type (regKind (getRegFromPath x)) :=
  match getRegFromPathTypeEq x in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateReg [t] x s / .

Definition castStateRegInv (t: Tree Elem) (x: RegPath t)
  (s: type (regKind (getRegFromPath x))) : ElemState (getLeaf x.(regPath)) :=
  match eq_sym (getRegFromPathTypeEq x) in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateRegInv [t] x s / .

Definition castStateMem (t: Tree Elem) (x: MemPath t)
  (s: ElemState (getLeaf x.(memPath))) :
  type (Array (getMemFromPath x).(memSize) (getMemFromPath x).(memKind)) **
  type (Array (getMemFromPath x).(memPort) (getMemFromPath x).(memKind)) :=
  match getMemFromPathTypeEq x in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateMem [t] x s / .

Definition castStateMemInv (t: Tree Elem) (x: MemPath t)
  (s: type (Array (getMemFromPath x).(memSize) (getMemFromPath x).(memKind)) **
      type (Array (getMemFromPath x).(memPort) (getMemFromPath x).(memKind))) :
  ElemState (getLeaf x.(memPath)) :=
  match eq_sym (getMemFromPathTypeEq x) in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateMemInv [t] x s / .

Definition castStateSend (t: Tree Elem) (x: SendPath t)
  (s: ElemState (getLeaf x.(sendPath))) : list (type (getSendKind x)) :=
  match getSendFromPathTypeEq x in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateSend [t] x s / .

Definition castStateSendInv (t: Tree Elem) (x: SendPath t)
  (s: list (type (getSendKind x))) : ElemState (getLeaf x.(sendPath)) :=
  match eq_sym (getSendFromPathTypeEq x) in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateSendInv [t] x s / .

Definition castStateRecv (t: Tree Elem) (x: RecvPath t)
  (s: ElemState (getLeaf x.(recvPath))) : list (type (getRecvKind x)) :=
  match getRecvFromPathTypeEq x in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateRecv [t] x s / .

Definition castStateRecvInv (t: Tree Elem) (x: RecvPath t)
  (s: list (type (getRecvKind x))) : ElemState (getLeaf x.(recvPath)) :=
  match eq_sym (getRecvFromPathTypeEq x) in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateRecvInv [t] x s / .

Definition castStateGallinaReg (t: Tree Elem) (x: GallinaRegPath t)
  (s: ElemState (getLeaf x.(gRegPath))) : gRegType (getGallinaRegFromPath x) :=
  match getGallinaRegFromPathTypeEq x in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateGallinaReg [t] x s / .

Definition castStateGallinaRegInv (t: Tree Elem) (x: GallinaRegPath t)
  (s: gRegType (getGallinaRegFromPath x)) : ElemState (getLeaf x.(gRegPath)) :=
  match eq_sym (getGallinaRegFromPathTypeEq x) in _ = Y return Y with
  | eq_refl => s
  end.
Arguments castStateGallinaRegInv [t] x s / .

(* ===========================================================================
 * PHOAS Actions (Action)
 * =========================================================================== *)

Section Action.
  Variable ty: Kind -> Type.
  Variable t: Tree Elem.

  Inductive Action (k: Kind) : Type :=
  | ReadReg (s: string) (x: RegPath t) (cont: ty (regKind (getRegFromPath x)) -> Action k)
  | WriteReg (x: RegPath t) (v: Expr ty (regKind (getRegFromPath x))) (cont: Action k)
  | ReadRqMem (x: MemPath t) (i: Expr ty (Bit (Z.log2_up (Z.of_nat (getMemFromPath x).(memSize)))))
      (p: FinType (getMemFromPath x).(memPort)) (cont: Action k)
  | ReadRpMem (s: string) (x: MemPath t) (p: FinType (getMemFromPath x).(memPort))
      (cont: ty (getMemFromPath x).(memKind) -> Action k)
  | WriteMem (x: MemPath t) (i: Expr ty (Bit (Z.log2_up (Z.of_nat (getMemFromPath x).(memSize)))))
      (v: Expr ty (getMemFromPath x).(memKind)) (cont: Action k)
  | Send (x: SendPath t) (v: Expr ty (getSendKind x)) (cont: Action k)
  | Recv (s: string) (x: RecvPath t) (cont: ty (getRecvKind x) -> Action k)
  | LetExp (s: string) k' (e: Expr ty k') (cont: ty k' -> Action k)
  | LetAction (s: string) k' (a: Action k') (cont: ty k' -> Action k)
  | NonDet (s: string) k' (cont: ty k' -> Action k)
  | IfElse (s: string) (p: Expr ty Bool) k' (t_branch f_branch: Action k') (cont: ty k' -> Action k)
  | System (ls: list (SysT ty)) (cont: Action k)
  | Return (e: Expr ty k)
  (* Specification-only call of the Gallina function f on the Gallina register x.
     f gets an oracle (one nondeterministic nat per index, and a new oracle each
     time the call executes), the value of e, and the register's current value.
     It returns the output, passed to cont, and the register's new value. Only the
     semantics runs f, so cont stays parametric in ty and the compiler can
     traverse it; the compiler ignores the call itself. *)
  | CallGallina (s: string) (x: GallinaRegPath t) (kIn kOut: Kind) (e: Expr ty kIn)
      (f: (nat -> nat) -> type kIn -> gRegType (getGallinaRegFromPath x) ->
          type kOut * gRegType (getGallinaRegFromPath x))
      (cont: ty kOut -> Action k).
End Action.

Arguments Return [ty t k] e.

Definition Mod (t: Tree Elem) : Type :=
  forall ty, list (@Action ty t (Bit 0)).

Section CombineActionsDef.
  Variable ty: Kind -> Type.
  Variable t: Tree Elem.

  Fixpoint combineActions (ls: list (@Action ty t (Bit 0))): @Action ty t (Bit 0) :=
    match ls return @Action ty t (Bit 0) with
    | nil => Return (Const _ (Bit 0) Zmod.zero)
    | x :: xs => LetAction EmptyString x (fun _ => combineActions xs)
    end.
End CombineActionsDef.
