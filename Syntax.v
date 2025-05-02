Require Export Bool Ascii String List Psatz PeanoNat.
Require Export Guru.Lib.Library.
Require Export Guru.Lib.Word Guru.Lib.WordProperties Guru.Lib.EclecticLib.

Global Set Implicit Arguments.
Global Set Asymmetric Patterns.

Import ListNotations.

Global Open Scope string_scope.
Global Open Scope nat_scope.
Global Open Scope list_scope.

Inductive UniBoolOp: Set :=
| Not: UniBoolOp.

Inductive CABoolOp: Set :=
| And: CABoolOp
| Xor: CABoolOp.

Inductive UniBitOp: nat -> nat -> Set :=
| Inv n: UniBitOp n n
| TruncLsb msb lsb: UniBitOp (msb + lsb) lsb
| TruncMsb msb lsb: UniBitOp (msb + lsb) msb
| UAnd n: UniBitOp n 1
| UOr n: UniBitOp n 1
| UXor n: UniBitOp n 1.

Inductive BinSign := SignSS | SignSU | SignUU.

Inductive BinBitOp: nat -> nat -> nat -> Set :=
| Sub n: BinBitOp n n n
| Div n: BinBitOp n n n
| Rem n: BinBitOp n n n
| Sll n m: BinBitOp n m n
| Srl n m: BinBitOp n m n
| Sra n m: BinBitOp n m n
| Concat msb lsb: BinBitOp msb lsb (msb + lsb).

Inductive CABitOp: Set :=
| Add: CABitOp
| Mul: CABitOp
| Band: CABitOp
| Bxor: CABitOp.

Inductive BinBitBoolOp: nat -> nat -> Set :=
| LessThan n: BinBitBoolOp n n.

Section Phoas.
  Variable ty: Kind -> Type.

  Inductive Expr: Kind -> Type :=
  | Var k: ty k -> Expr k
  | Const k: type k -> Expr k
  | UniBool: UniBoolOp -> Expr Bool -> Expr Bool
  | CABool: CABoolOp -> list (Expr Bool) -> Expr Bool
  | UniBit n1 n2: UniBitOp n1 n2 -> Expr (Bit n1) -> Expr (Bit n2)
  | CABit n: CABitOp -> list (Expr (Bit n)) -> Expr (Bit n)
  | BinBit n1 n2 n3: BinBitOp n1 n2 n3 -> Expr (Bit n1) -> Expr (Bit n2) -> Expr (Bit n3)
  | BinBitBool n1 n2: BinBitBoolOp n1 n2 -> Expr (Bit n1) -> Expr (Bit n2) -> Expr Bool
  | ITE k: Expr Bool -> Expr k -> Expr k -> Expr k
  | Eq k: Expr k -> Expr k -> Expr Bool
  | Kor k: list (Expr k) -> Expr k
  | ReadStruct (ls: list (string * Kind)) (e: Expr (Struct ls)) (i: FinStruct ls): Expr (fieldK i)
  | ReadArray n m k: Expr (Array n k) -> Expr (Bit m) -> Expr k
  | ReadArrayConst n k: Expr (Array n k) -> FinArray n -> Expr k
  | BuildArray k n (vals: FinArray n -> Expr k): Expr (Array n k)
  | BuildStruct (ls: list (string * Kind)) (vals: forall i: FinStruct ls, Expr (fieldK i)): Expr (Struct ls)
  | ToBit k (e: Expr k): Expr (Bit (size k))
  | FromBit k (e: Expr (Bit (size k))): Expr k.

  Definition UpdateStruct ls (e: Expr (Struct ls)) (j: FinStruct ls) (v: Expr (fieldK j)): Expr (Struct ls) :=
    BuildStruct _ (fun i => match FinStruct_dec _  j i return Expr (fieldK i) with
                            | left pf => match pf in _ = Y return Expr (fieldK Y) with
                                         | eq_refl => v
                                         end
                            | right _ => ReadStruct e i
                            end).

  Definition UpdateArrayConst n k (e: Expr (Array n k)) (i: FinArray n) (v: Expr k): Expr (Array n k) :=
    BuildArray _ (fun j => match FinArray_dec _  i j return Expr k with
                           | left pf => v
                           | right _ => ReadArrayConst e j
                           end).

  Definition UpdateArray n k (e: Expr (Array n k)) m (i: Expr (Bit m)) (v: Expr k): Expr (Array n k) :=
    BuildArray _ (fun j => ITE (Eq i (Const (Bit _) (natToWord _ (FinArray_to_nat _ j)))) v (ReadArrayConst e j)).

  Section BitOps.
    Definition castBits ni no (pf: ni = no) (e: Expr (Bit ni)) :=
      nat_cast (fun n => Expr (Bit n)) pf e.

    Definition Slt n (e1 e2: Expr (Bit (1 + n))) :=
      Eq (Eq (UniBit (TruncMsb 1 n) e1) (UniBit (TruncMsb 1 n) e2)) (BinBitBool (LessThan _) e1 e2).

    Definition ConstExtract msb n lsb (e: Expr (Bit (msb + n + lsb))): Expr (Bit n) :=
      UniBit (TruncLsb msb n) (UniBit (TruncMsb (msb + n) lsb) e).

    Definition OneExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (msb + lsb)) :=
      BinBit (Concat msb lsb) (Const (Bit _) (wones msb)) e.

    Definition ZeroExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (msb + lsb)) :=
      BinBit (Concat msb lsb) (Const (Bit _) (wzero msb)) e.

    Definition SignExtend msb lsb: Expr (Bit lsb) -> Expr (Bit (msb + lsb)).
      refine
        match lsb return Expr (Bit lsb) -> Expr (Bit (msb + lsb)) with
        | 0 => fun _ => castBits _ (Const (Bit _) (wzero msb))
        | S m => fun e => BinBit (Concat msb (S m)) (ITE (Eq (UniBit (TruncMsb 1 m) e)
                                                            (Const (Bit _) (WO~0)%word))
                                                         (Const (Bit _) (wzero msb))
                                                         (Const (Bit _) (wones msb))) e
        end; abstract lia.
    Defined.

    Fixpoint replicate sz (e: Expr (Bit sz)) n : Expr (Bit (n * sz)) :=
      match n return Expr (Bit (n * sz)) with
      | 0 => Const (Bit _) WO
      | S m => BinBit (Concat sz (m * sz)) e (replicate e m)
      end.
    
    Definition OneExtendTruncLsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@OneExtend (no - ni) ni e)
        | right isGe => UniBit (TruncLsb (ni - no) no) (castBits _ e)
        end; abstract lia.
    Defined.

    Definition ZeroExtendTruncLsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@ZeroExtend (no - ni) ni e)
        | right isGe => UniBit (TruncLsb (ni - no) no) (castBits _ e)
        end; abstract lia.
    Defined.

    Definition SignExtendTruncLsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@SignExtend (no - ni) ni e)
        | right isGe => UniBit (TruncLsb (ni - no) no) (castBits _ e)
        end; abstract lia.
    Defined.
    
    Definition ZeroExtendTruncMsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@ZeroExtend (no - ni) ni e)
        | right isGe => UniBit (TruncMsb no (ni - no)) (castBits _ e)
        end; abstract lia.
    Defined.
    
    Definition SignExtendTruncMsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@SignExtend (no - ni) ni e)
        | right isGe => UniBit (TruncMsb no (ni - no)) (castBits _ e)
        end; abstract lia.
    Defined.

    Definition isNotZero n (e: Expr (Bit n)) := FromBit Bool (UniBit (UOr n) e).
    Definition isZero n (e: Expr (Bit n)) := UniBool Not (isNotZero e).
    Definition isAllOnes n (e: Expr (Bit n)) := FromBit Bool (UniBit (UAnd n) e).

    Fixpoint countLeadingZeros ni no: Expr (Bit ni) -> Expr (Bit no) :=
      match ni return Expr (Bit ni) -> Expr (Bit no) with
      | 0 => fun _ => Const (Bit _) (wzero _)
      | S m => fun e =>
                 ITE (Eq (UniBit (TruncMsb 1 m) e) (Const (Bit _) WO~0))
                     (CABit Add [Const (Bit _) (natToWord _ 1);
                                 @countLeadingZeros _ _ (UniBit (TruncLsb 1 m) e)])
                     (Const (Bit _) (wzero _))
      end.

    Fixpoint countTrailingZeros ni no: Expr (Bit ni) -> Expr (Bit no) :=
      match ni return Expr (Bit ni) -> Expr (Bit no) with
      | 0 => fun _ => Const (Bit _) (wzero _)
      | S m => fun e =>
                 let eCast := castBits (eq_sym (Nat.add_1_r m)) e in
                 ITE (Eq (UniBit (TruncLsb m 1) eCast) (Const (Bit _) WO~0))
                        (CABit Add [Const (Bit _) (natToWord _ 1);
                                    @countTrailingZeros _ _ (UniBit (TruncMsb m 1) eCast)])
                     (Const (Bit _) (wzero _))
      end.
  End BitOps.
End Phoas.
