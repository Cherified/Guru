From Stdlib Require Import String List Zmod Bool.
Require Import Guru.Library.

Set Implicit Arguments.
Set Asymmetric Patterns.

Import ListNotations.

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
  | ReadUnionData [ls: list (string * Kind)] (e: Expr (TaggedUnion ls)) (i: FinType (length ls)): Expr (snd (nth_pf i.(finLt)))
  | BuildUnion [ls: list (string * Kind)] (i: FinType (length ls)) (e: Expr (snd (nth_pf i.(finLt)))): Expr (TaggedUnion ls)
  (* The following 2 don't pass positivity check in Rocq *)
  | BuildStruct [ls: list (string * Kind)] (vals: DiffTuple (fun x => Expr (snd x)) ls): Expr (Struct ls)
  | BuildArray [n k] (vals: SameTuple (Expr k) n): Expr (Array n k).
End Phoas.
Set Positivity Checking.

Section Phoas.
  Variable ty: Kind -> Type.
  Local Notation Expr := (Expr ty).

  Definition Neq k (e1 e2: Expr k) := Not (Eq e1 e2).

  Definition Sub n (a b: Expr (Bit n)): Expr (Bit n) := Add [a; Not b; Const _ (Bit n) Zmod.one].

  Definition Slt n (a b: Expr (Bit n)): Expr Bool :=
    FromBit Bool
      (TruncMsb 1 n (Sub (Concat (Const _ (Bit 1) Zmod.zero) a) (Concat (Const _ (Bit 1) Zmod.zero) b))).

  Definition Sgt n (a b: Expr (Bit n)): Expr Bool := Slt b a.

  Definition Sle n (a b: Expr (Bit n)): Expr Bool := Not (Sgt b a).

  Definition Sge n (a b: Expr (Bit n)): Expr Bool := Not (Slt b a).

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
    | S m => Concat e (replicate e m)
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
      refine (BuildArray (@Build_SameTuple _ n (map f (genFinType n))
                            (transparent_Is_true _ _))).
      Proof.
        rewrite length_map, genFinType_length, Nat.eqb_refl; auto.
      Defined.
  End ArrayBuilder.

  Section Transpose.
    Variable n m: nat.
    Variable k: Kind.
    Variable arr: Expr (Array n (Array m k)).
    Definition transpose: Expr (Array m (Array n k)) :=
      ArrayBuilder (fun j => (ArrayBuilder (fun i => ReadArrayConst (ReadArrayConst arr i) j))).
  End Transpose.

  Section ArrayShiftRotate.
    Variable n m: nat.
    Variable arr: Expr (Array n (Bit (NatZ_mul m 1))).
    
    Section Fn.
      Variable fn: Expr (Bit (NatZ_mul n 1)) -> Expr (Bit (NatZ_mul n 1)).
      Definition arrayProcess: Expr (Array n (Bit (NatZ_mul m 1))) :=
        FromBit (Array n (Bit (NatZ_mul m 1)))
          (ToBit
             (transpose
                (FromBit (Array m (Array n Bool))
                   (ToBit
                      (ArrayBuilder
                         (fun i =>
                            fn (ReadArrayConst
                                  (FromBit (Array m (Bit (NatZ_mul n 1)))
                                     (ToBit (transpose (FromBit (Array n (Array m Bool)) (ToBit arr))))) i))))))).
    End Fn.

    Variable p: Z.
    Variable shamt: Expr (Bit p).

    Definition ArraySll := arrayProcess (fun v => Sll v shamt).
    Definition ArraySrl := arrayProcess (fun v => Srl v shamt).
    Definition ArrayRotl := arrayProcess (fun v => rotateLeft v shamt).
    Definition ArrayRotr := arrayProcess (fun v => rotateRight v shamt).
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
    Definition  ArrayOneExtend := extendArray (Const _ _ (InvDefault k)).
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
End Phoas.

Inductive BitFormat :=
| Binary
| Decimal
| Hex.

Unset Positivity Checking.
Section Phoas.
  Inductive FullFormat: Kind -> Type :=
  | FBool: Z -> BitFormat -> FullFormat Bool
  | FBit n: Z -> BitFormat -> FullFormat (Bit n)
  | FStruct [ls]: DiffTuple (fun x => FullFormat (snd x)) ls -> FullFormat (Struct ls)
  | FArray n k: FullFormat k -> FullFormat (@Array n k)
  | FTaggedUnion [ls]: BitFormat -> BitFormat -> FullFormat (TaggedUnion ls).
End Phoas.
Set Positivity Checking.

Section Phoas.
  Variable ty: Kind -> Type.
  Local Notation Expr := (Expr ty).
  Definition fullFormat format: forall k, FullFormat k :=
    KindCustomInd (P := fun k => FullFormat k)
      (FBool 1 format)
      (fun n => FBit n ((n+3)/4) format)
      FStruct
      FArray
      (fun ls _ => FTaggedUnion format format).

  Inductive SysT: Type :=
  | DispString (s: string): SysT
  | DispExpr k (e: Expr k) (ff: FullFormat k): SysT
  | Finish: SysT.

  Definition DispHex k (e: Expr k) :=
    DispExpr e (fullFormat Hex k).

  Definition DispBinary k (e: Expr k) :=
    DispExpr e (fullFormat Binary k).

  Definition DispDecimal k (e: Expr k) :=
    DispExpr e (fullFormat Decimal k).

  Inductive LetExpr (k: Kind): Type :=
  | RetE (e: Expr k)
  | SystemE (ls: list SysT) (cont: LetExpr k)
  | LetEx (s: string) k' (e: LetExpr k') (cont: ty k' -> LetExpr k)
  | IfElseE (s: string) (p: Expr Bool) k' (t f: LetExpr k') (cont: ty k' -> LetExpr k).

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

  Definition countLeadingZerosArray ni (arr: Expr (Array ni Bool)) no: LetExpr (Bit no) :=
    LetEx "over_init" (RetE (Const _ Bool false)) (fun over_init =>
      LetEx "accum_init" (RetE (Const _ (Bit no) Zmod.zero)) (fun accum_init =>
        @countLeadingZerosLoop ni no arr ni over_init accum_init)).

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

  Definition countTrailingZerosArray ni (arr: Expr (Array ni Bool)) no: LetExpr (Bit no) :=
    LetEx "over_init" (RetE (Const _ Bool false)) (fun over_init =>
      LetEx "accum_init" (RetE (Const _ (Bit no) Zmod.zero)) (fun accum_init =>
        @countTrailingZerosLoop ni no arr 0 ni over_init accum_init)).

  Definition countOnesArray ni (arr: Expr (Array ni Bool)) no: LetExpr (Bit no) :=
    RetE (fold_left (fun accum i =>
                 let curr := readNatToFinType (Const _ Bool false) (ReadArrayConst arr) i in
                 Add [accum;
                      ITE curr
                        (Const _ (Bit no) Zmod.one)
                        (Const _ (Bit no) Zmod.zero)]) (seq 0 ni)
      (Const _ (Bit no) Zmod.zero)).

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

Inductive Elem :=
| EReg (r : Reg)
| EMem (m : Mem)
| ESend (k : Kind)
| ERecv (k : Kind).

Definition ElemState (e: Elem) : Type :=
  match e with
  | EReg r => type (regKind r)
  | EMem m => type (Array (memSize m) (memKind m)) ** type (Array (memPort m) (memKind m))
  | ESend k => list (type k)
  | ERecv k => list (type k)
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

Definition getRegFromPathUnsafe (t: Tree Elem) (p: LeafPath t) : Reg :=
  getRegFromElemUnsafe (getLeaf p).

Definition getMemFromPathUnsafe (t: Tree Elem) (p: LeafPath t) : Mem :=
  getMemFromElemUnsafe (getLeaf p).

Definition getSendKindFromPath (t: Tree Elem) (p: LeafPath t) : Kind :=
  getSendKindFromElem (getLeaf p).

Definition getRecvKindFromPath (t: Tree Elem) (p: LeafPath t) : Kind :=
  getRecvKindFromElem (getLeaf p).

Arguments getRegFromPathUnsafe [t] p.
Arguments getMemFromPathUnsafe [t] p.
Arguments getSendKindFromPath [t] p.
Arguments getRecvKindFromPath [t] p.

Record RegPath (t: Tree Elem) := {
  regPath : LeafPath t;
  regPathPf : Is_true (isRegElem (getLeaf regPath))
}.

Record MemPath (t: Tree Elem) := {
  memPath : LeafPath t;
  memPathPf : Is_true (isMemElem (getLeaf memPath))
}.

Record SendPath (t: Tree Elem) := {
  sendPath : LeafPath t;
  sendPathPf : Is_true (isSendElem (getLeaf sendPath))
}.

Record RecvPath (t: Tree Elem) := {
  recvPath : LeafPath t;
  recvPathPf : Is_true (isRecvElem (getLeaf recvPath))
}.

Definition getRegFromPath (t: Tree Elem) (x: RegPath t) : Reg :=
  getRegFromPathUnsafe x.(regPath).

Definition getMemFromPath (t: Tree Elem) (x: MemPath t) : Mem :=
  getMemFromPathUnsafe x.(memPath).

Definition getSendKind (t: Tree Elem) (x: SendPath t) : Kind :=
  getSendKindFromPath x.(sendPath).

Definition getRecvKind (t: Tree Elem) (x: RecvPath t) : Kind :=
  getRecvKindFromPath x.(recvPath).

Arguments getRegFromPath [t] x.
Arguments getMemFromPath [t] x.
Arguments getSendKind [t] x.
Arguments getRecvKind [t] x.

Lemma getRegFromElemTypeEq (e: Elem) (pf: Is_true (isRegElem e)) :
  ElemState e = type (regKind (getRegFromElemUnsafe e)).
Proof.
  destruct e as [r | m | k | k].
  - reflexivity.
  - destruct pf.
  - destruct pf.
  - destruct pf.
Defined.
Arguments getRegFromElemTypeEq e pf / .

Lemma getRegFromPathTypeEq (t: Tree Elem) (x: RegPath t) :
  ElemState (getLeaf x.(regPath)) = type (regKind (getRegFromPath x)).
Proof.
  apply getRegFromElemTypeEq.
  exact x.(regPathPf).
Defined.
Arguments getRegFromPathTypeEq [t] x / .

Lemma getMemFromElemTypeEq (e: Elem) (pf: Is_true (isMemElem e)) :
  ElemState e =
  type (Array (getMemFromElemUnsafe e).(memSize) (getMemFromElemUnsafe e).(memKind)) **
  type (Array (getMemFromElemUnsafe e).(memPort) (getMemFromElemUnsafe e).(memKind)).
Proof.
  destruct e as [r | m | k | k].
  - destruct pf.
  - reflexivity.
  - destruct pf.
  - destruct pf.
Defined.
Arguments getMemFromElemTypeEq e pf / .

Lemma getMemFromPathTypeEq (t: Tree Elem) (x: MemPath t) :
  ElemState (getLeaf x.(memPath)) =
  type (Array (getMemFromPath x).(memSize) (getMemFromPath x).(memKind)) **
  type (Array (getMemFromPath x).(memPort) (getMemFromPath x).(memKind)).
Proof.
  apply getMemFromElemTypeEq.
  exact x.(memPathPf).
Defined.
Arguments getMemFromPathTypeEq [t] x / .

Lemma getSendFromElemTypeEq (e: Elem) (pf: Is_true (isSendElem e)) :
  ElemState e = list (type (getSendKindFromElem e)).
Proof.
  destruct e as [r | m | k | k].
  - destruct pf.
  - destruct pf.
  - reflexivity.
  - destruct pf.
Defined.
Arguments getSendFromElemTypeEq e pf / .

Lemma getSendFromPathTypeEq (t: Tree Elem) (x: SendPath t) :
  ElemState (getLeaf x.(sendPath)) = list (type (getSendKind x)).
Proof.
  apply getSendFromElemTypeEq.
  exact x.(sendPathPf).
Defined.
Arguments getSendFromPathTypeEq [t] x / .

Lemma getRecvFromElemTypeEq (e: Elem) (pf: Is_true (isRecvElem e)) :
  ElemState e = list (type (getRecvKindFromElem e)).
Proof.
  destruct e as [r | m | k | k].
  - destruct pf.
  - destruct pf.
  - destruct pf.
  - reflexivity.
Defined.
Arguments getRecvFromElemTypeEq e pf / .

Lemma getRecvFromPathTypeEq (t: Tree Elem) (x: RecvPath t) :
  ElemState (getLeaf x.(recvPath)) = list (type (getRecvKind x)).
Proof.
  apply getRecvFromElemTypeEq.
  exact x.(recvPathPf).
Defined.
Arguments getRecvFromPathTypeEq [t] x / .

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
  | Return (e: Expr ty k).
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

Section ActionDef.
  Variable ty: Kind -> Type.
  Variable t: Tree Elem.

  Fixpoint toAction k (le: LetExpr ty k) : @Action ty t k :=
    match le with
    | RetE e => Return e
    | SystemE ls cont => System ls (toAction cont)
    | LetEx s k' le cont => LetAction s (toAction le) (fun x => toAction (cont x))
    | IfElseE s p k' t' f' cont => IfElse s p (toAction t') (toAction f') (fun x => toAction (cont x))
    end.
End ActionDef.
