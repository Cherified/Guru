Require Import String List Psatz.
Require Import Guru.Lib.Library Guru.Lib.Word.

Set Implicit Arguments.
Set Asymmetric Patterns.

Import ListNotations.

Section Phoas.
  Variable ty: Kind -> Type.

  Inductive Expr: Kind -> Type :=
  | Var k: ty k -> Expr k
  | Const k: type k -> Expr k
  | Or k: list (Expr k) -> Expr k
  | And: list (Expr Bool) -> Expr Bool
  | Xor: list (Expr Bool) -> Expr Bool
  | Not: Expr Bool -> Expr Bool
  | Inv n: Expr (Bit n) -> Expr (Bit n)
  | TruncLsb msb lsb: Expr (Bit (msb + lsb)) -> Expr (Bit lsb)
  | TruncMsb msb lsb: Expr (Bit (msb + lsb)) -> Expr (Bit msb)
  | UOr n: Expr (Bit n) -> Expr Bool
  | UAnd n: Expr (Bit n) -> Expr Bool
  | UXor n: Expr (Bit n) -> Expr Bool
  | Add n: list (Expr (Bit n)) -> Expr (Bit n)
  | Mul n: list (Expr (Bit n)) -> Expr (Bit n)
  | Band n: list (Expr (Bit n)) -> Expr (Bit n)
  | Bxor n: list (Expr (Bit n)) -> Expr (Bit n)
  | Div n: Expr (Bit n) -> Expr (Bit n) -> Expr (Bit n)
  | Rem n: Expr (Bit n) -> Expr (Bit n) -> Expr (Bit n)
  | Sll n m: Expr (Bit n) -> Expr (Bit m) -> Expr (Bit n)
  | Srl n m: Expr (Bit n) -> Expr (Bit m) -> Expr (Bit n)
  | Sra n m: Expr (Bit n) -> Expr (Bit m) -> Expr (Bit n)
  | Concat msb lsb: Expr (Bit msb) -> Expr (Bit lsb) -> Expr (Bit (msb + lsb))
  | ITE k: Expr Bool -> Expr k -> Expr k -> Expr k
  | Eq k: Expr k -> Expr k -> Expr Bool
  | ReadStruct (ls: list (string * Kind)) (e: Expr (Struct ls)) (i: FinStruct ls): Expr (fieldK i)
  | ReadArray n m k: Expr (Array n k) -> Expr (Bit m) -> Expr k
  | ReadArrayConst n k: Expr (Array n k) -> FinArray n -> Expr k
  | BuildStruct [ls: list (string * Kind)] (vals: forall i: FinStruct ls, Expr (fieldK i)): Expr (Struct ls)
  | BuildArray [k n] (vals: FinArray n -> Expr k): Expr (Array n k)
  | ToBit k (e: Expr k): Expr (Bit (size k))
  | FromBit k (e: Expr (Bit (size k))): Expr k.

  Definition UpdateStruct ls (e: Expr (Struct ls)) (j: FinStruct ls) (v: Expr (fieldK j)): Expr (Struct ls) :=
    BuildStruct (fun i => match FinStruct_dec j i return Expr (fieldK i) with
                          | left pf => match pf in _ = Y return Expr (fieldK Y) with
                                       | eq_refl => v
                                       end
                          | right _ => ReadStruct e i
                          end).

  Definition UpdateArrayConst n k (e: Expr (Array n k)) (i: FinArray n) (v: Expr k): Expr (Array n k) :=
    BuildArray (fun j => match FinArray_dec i j return Expr k with
                         | left pf => v
                         | right _ => ReadArrayConst e j
                         end).

  Definition UpdateArray n k (e: Expr (Array n k)) m (i: Expr (Bit m)) (v: Expr k): Expr (Array n k) :=
    BuildArray (fun j => ITE (Eq i (@Const (Bit _) (natToWord _ (FinArray_to_nat j)))) v (ReadArrayConst e j)).

  Section BitOps.
    Definition Sub n (a b: Expr (Bit n)): Expr (Bit n) := Add [a; Inv b; @Const (Bit n) (ZToWord n 1)].
    
    Definition castBits ni no (pf: ni = no) (e: Expr (Bit ni)) :=
      nat_cast (fun n => Expr (Bit n)) pf e.

    Definition ConstExtract msb n lsb (e: Expr (Bit (msb + n + lsb))): Expr (Bit n) :=
      @TruncLsb msb n (@TruncMsb (msb + n) lsb e).

    Definition OneExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (msb + lsb)) :=
      Concat (@Const (Bit _) (wones msb)) e.

    Definition ZeroExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (msb + lsb)) :=
      Concat (@Const (Bit _) (wzero msb)) e.

    Definition SignExtend msb lsb: Expr (Bit lsb) -> Expr (Bit (msb + lsb)).
      refine
        match lsb return Expr (Bit lsb) -> Expr (Bit (msb + lsb)) with
        | 0 => fun _ => castBits _ (@Const (Bit _) (wzero msb))
        | S m => fun e => Concat (ITE (Eq (@TruncMsb 1 m e) (@Const (Bit _) (WO~0)%word))
                                    (@Const (Bit _) (wzero msb))
                                    (@Const (Bit _) (wones msb))) e
        end; abstract lia.
    Defined.

    Fixpoint replicate sz (e: Expr (Bit sz)) n : Expr (Bit (n * sz)) :=
      match n return Expr (Bit (n * sz)) with
      | 0 => @Const (Bit _) WO
      | S m => Concat e (replicate e m)
      end.
    
    Definition OneExtendTruncLsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@OneExtend (no - ni) ni e)
        | right isGe => @TruncLsb (ni - no) no (castBits _ e)
        end; abstract lia.
    Defined.

    Definition ZeroExtendTruncLsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@ZeroExtend (no - ni) ni e)
        | right isGe => @TruncLsb (ni - no) no (castBits _ e)
        end; abstract lia.
    Defined.

    Definition SignExtendTruncLsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@SignExtend (no - ni) ni e)
        | right isGe => @TruncLsb (ni - no) no (castBits _ e)
        end; abstract lia.
    Defined.
    
    Definition ZeroExtendTruncMsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@ZeroExtend (no - ni) ni e)
        | right isGe => @TruncMsb no (ni - no) (castBits _ e)
        end; abstract lia.
    Defined.
    
    Definition SignExtendTruncMsb ni no (e: Expr (Bit ni)):
      Expr (Bit no).
      refine
        match Compare_dec.lt_dec ni no with
        | left isLt => castBits _ (@SignExtend (no - ni) ni e)
        | right isGe => @TruncMsb no (ni - no) (castBits _ e)
        end; abstract lia.
    Defined.

    Definition isNotZero n (e: Expr (Bit n)) := (UOr e).
    Definition isZero n (e: Expr (Bit n)) := Not (isNotZero e).
    Definition isAllOnes n (e: Expr (Bit n)) := UAnd e.

    Fixpoint countLeadingZeros ni no: Expr (Bit ni) -> Expr (Bit no) :=
      match ni return Expr (Bit ni) -> Expr (Bit no) with
      | 0 => fun _ => @Const (Bit _) (wzero _)
      | S m => fun e =>
                 ITE (Eq (@TruncMsb 1 m e) (@Const (Bit _) WO~0))
                     (Add [@Const (Bit _) (natToWord _ 1);
                           @countLeadingZeros _ _ (@TruncLsb 1 m e)])
                     (@Const (Bit _) (wzero _))
      end.

    Fixpoint countTrailingZeros ni no: Expr (Bit ni) -> Expr (Bit no) :=
      match ni return Expr (Bit ni) -> Expr (Bit no) with
      | 0 => fun _ => @Const (Bit _) (wzero _)
      | S m => fun e =>
                 let eCast := castBits (eq_sym (Nat.add_1_r m)) e in
                 ITE (Eq (@TruncLsb m 1 eCast) (@Const (Bit _) WO~0))
                        (Add [@Const (Bit _) (natToWord _ 1);
                              @countTrailingZeros _ _ (@TruncMsb m 1 eCast)])
                     (@Const (Bit _) (wzero _))
      end.
  End BitOps.

  Inductive BitFormat :=
  | Binary
  | Decimal
  | Hex.

  Inductive FullFormat: Kind -> Type :=
  | FBool: nat -> BitFormat -> FullFormat Bool
  | FBit n: nat -> BitFormat -> FullFormat (Bit n)
  | FStruct [ls]: (forall i, FullFormat (@fieldK _ ls i)) -> FullFormat (Struct ls)
  | FArray n k: FullFormat k -> FullFormat (@Array n k).

  Fixpoint fullFormatHex k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Hex
    | Bit n => FBit n ((n+3)/4) Hex
    | Struct ls => FStruct (fun i => fullFormatHex (fieldK i))
    | Array n k => FArray n (fullFormatHex k)
    end.

  Fixpoint fullFormatBinary k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Binary
    | Bit n => FBit n n Binary
    | Struct ls => FStruct (fun i => fullFormatBinary (fieldK i))
    | Array n k => FArray n (fullFormatBinary k)
    end.

  Fixpoint fullFormatDecimal k : FullFormat k :=
    match k return FullFormat k with
    | Bool => FBool 1 Decimal
    | Bit n => FBit n 0 Decimal
    | Struct ls => FStruct (fun i => fullFormatDecimal (fieldK i))
    | Array n k => FArray n (fullFormatDecimal k)
    end.

  Inductive SysT: Type :=
  | DispString (s: string): SysT
  | DispExpr k (e: Expr k) (ff: FullFormat k): SysT
  | Finish: SysT.

  Definition DispHex k (e: Expr k) :=
    DispExpr e (fullFormatHex k).

  Definition DispBinary k (e: Expr k) :=
    DispExpr e (fullFormatBinary k).

  Definition DispDecimal k (e: Expr k) :=
    DispExpr e (fullFormatDecimal k).

  Record VerilogReadMem := { readMemAscii      : bool ;
                             readMemArg        : bool ;
                             readMemName       : string ;
                             readMemOffsetSize : option (nat * nat) }.

  Record Reg := { regName : string ;
                  regKind : Kind ;
                  regInit : type regKind }.

  Definition getStringKindFromReg (r: Reg) := (regName r, regKind r).

  Inductive MemInit (n: nat) (k: Kind) :=
  | MemNotInit
  | MemSame (init: type k)
  | MemDiff (init: SameTuple (type k) n) (useReadMem: option VerilogReadMem).

  Record Mem := { memName : string ;
                  memSize : nat ;
                  memKind : Kind ;
                  memInit : MemInit memSize memKind }.

  Definition getStringNatKindFromMem (m: Mem) := (memName m, (memSize m, memKind m)).

  Section Action.
    Variable regs: list (string * Kind).
    Variable asyncMems: list (string * (nat * Kind)).
    Variable syncMems: list (string * (nat * Kind)).
    Variable sends: list (string * Kind).
    Variable recvs: list (string * Kind).

    Inductive Action (k: Kind) : Type :=
    | ReadReg (x: FinStruct regs) (cont: ty (fieldK x) -> Action k)
    | WriteReg (x: FinStruct regs) (v: Expr (fieldK x)) (cont: Action k)
    | ReadAsyncMem (x: FinStruct asyncMems) (i: Expr (Bit (Nat.log2_up (fst (fieldK x)))))
        (cont: ty (snd (fieldK x)) -> Action k)
    | WriteAsyncMem (x: FinStruct asyncMems) (i: Expr (Bit (Nat.log2_up (fst (fieldK x)))))
        (v: Expr (snd (fieldK x))) (cont: Action k)
    | ReadRqSyncMem (x: FinStruct syncMems) (i: Expr (Bit (Nat.log2_up (fst (fieldK x))))) (cont: Action k)
    | ReadRpSyncMem (x: FinStruct syncMems) (cont: ty (snd (fieldK x)) -> Action k)
    | WriteSyncMem (x: FinStruct syncMems) (i: Expr (Bit (Nat.log2_up (fst (fieldK x)))))
        (v: Expr (snd (fieldK x))) (cont: Action k)
    | Send (x: FinStruct sends) (v: Expr (fieldK x)) (cont: Action k)
    | Recv (x: FinStruct recvs) (cont: ty (fieldK x) -> Action k)
    | LetExpr (s: string) k' (e: Expr k') (cont: ty k' -> Action k)
    | LetAction (s: string) k' (a: Action k') (cont: ty k' -> Action k)
    | NonDet (s: string) k' (cont: ty k' -> Action k)
    | IfElse (s: string) (p: Expr Bool) k' (t f: Action k') (cont: ty k' -> Action k)
    | Sys (ls: list SysT) (cont: Action k)
    | Return (e: Expr k).
  End Action.

  Record Mod := { modRegs : list Reg ;
                  modAsyncMems: list Mem ;
                  modSyncMems: list Mem ;
                  modSends: list (string * Kind) ;
                  modRecvs: list (string * Kind) ;
                  modRules: list (Action
                                    (map getStringKindFromReg modRegs)
                                    (map getStringNatKindFromMem modAsyncMems)
                                    (map getStringNatKindFromMem modSyncMems)
                                    modSends
                                    modRecvs
                                    (Bit 0)) }.
End Phoas.

Arguments Return [ty regs asyncMems syncMems sends recvs k] e.

