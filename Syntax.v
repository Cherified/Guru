From Stdlib Require Import String List Zmod.
Require Import Guru.Lib.Library.

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
  | And: list (Expr Bool) -> Expr Bool
  | Xor: list (Expr Bool) -> Expr Bool
  | Not: Expr Bool -> Expr Bool
  | Inv n: Expr (Bit n) -> Expr (Bit n)
  | TruncLsb msb lsb: Expr (Bit (msb + lsb)%Z) -> Expr (Bit lsb)
  | TruncMsb msb lsb: Expr (Bit (msb + lsb)%Z) -> Expr (Bit msb)
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
  | Concat msb lsb: Expr (Bit msb) -> Expr (Bit lsb) -> Expr (Bit (lsb + msb))
  | ITE k: Expr Bool -> Expr k -> Expr k -> Expr k
  | Eq k: Expr k -> Expr k -> Expr Bool
  | ReadStruct (ls: list (string * Kind)) (e: Expr (Struct ls)) (i: FinStruct ls): Expr (fieldK i)
  | ReadArray n m k: Expr (Array n k) -> Expr (Bit m) -> Expr k
  | ReadArrayConst n k: Expr (Array n k) -> FinType n -> Expr k
  | BuildStruct [ls: list (string * Kind)] (vals: DiffTuple (fun x => Expr (snd x)) ls): Expr (Struct ls)
  | BuildArray [k n] (vals: SameTuple (Expr k) n): Expr (Array n k)
  | ToBit k (e: Expr k): Expr (Bit (size k))
  | FromBit k (e: Expr (Bit (size k))): Expr k.
End Phoas.
Set Positivity Checking.

Section Phoas.
  Variable ty: Kind -> Type.
  Local Notation Expr := (Expr ty).
  
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

  Definition Neq k (e1 e2: Expr k) := Not (Eq e1 e2).

  Definition Sub n (a b: Expr (Bit n)): Expr (Bit n) := Add [a; Inv b; @Const (Bit n) (ZToWord n 1)].

  Definition Slt n (a b: Expr (Bit n)): Expr Bool :=
    FromBit Bool (TruncMsb 1 n (Sub (Concat (Const (Bit 1) WO~0) a) (Concat (Const (Bit 1) WO~0) b))).

  Definition Sgt n (a b: Expr (Bit n)): Expr Bool := Slt b a.

  Definition Sle n (a b: Expr (Bit n)): Expr Bool := Not (Sgt b a).

  Definition Sge n (a b: Expr (Bit n)): Expr Bool := Not (Slt b a).
  
  Definition castBits ni no (pf: ni = no) (e: Expr (Bit ni)) :=
    nat_cast (fun n => Expr (Bit n)) pf e.

  Definition castBitsKind1 k: forall n (pf: Bit n = k), Expr (Bit n) -> Expr k :=
    match k return forall n (pf: Bit n = k), Expr (Bit n) -> Expr k with
    | Bit m => fun _ pf e => castBits (f_equal (fun k'=> match k' with
                                                         | Bit n' => n'
                                                         | _ => 0
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
                                                         | _ => 0
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

  Definition ZeroExtendTo outSz inSz (e: Expr (Bit inSz)) := ZeroExtend (outSz - inSz) e.
  Definition SignExtendTo outSz inSz (e: Expr (Bit inSz)) := SignExtend (outSz - inSz) e.

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

  Fixpoint countOnes ni no :=
    match ni return Expr (Bit ni) -> Expr (Bit no) with
    | 0 => fun _ => Const (Bit no) (wzero no)
    | S m => fun e =>
               Add [ITE (FromBit Bool (TruncMsb 1 m e))
                      (Const (Bit no) (natToWord no 1)) (Const (Bit no) (wzero no));
                    @countOnes m no (TruncLsb 1 m e)]
    end.

  Definition rotateRight n (e: Expr (Bit n)) m (shamt: Expr (Bit m)) :=
    ( Or [Srl e shamt; Sll e (Sub (Const (Bit m) (natToWord m n)) shamt)]).

  Definition rotateLeft n (e: Expr (Bit n)) m (shamt: Expr (Bit m)) :=
    ( Or [Sll e shamt; Srl e (Sub (Const (Bit m) (natToWord m n)) shamt)]).

  (* To be used only if there are multiple disjoint cases *)
  Section CaseDefault.
      Variable k: Kind.
      Variable ls: list (Expr Bool * Expr k).
      Variable def: Expr k.
      Definition caseDefault :=
        ITE (Or (map fst ls)) (Or (map (fun '(p, v) => ITE p v (Const k (Default k))) ls)) def.
  End CaseDefault.
  
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

  Record VerilogMem := { verilogAscii  : bool ;
                         verilogName   : string ;
                         verilogOffset : nat ;
                         verilogSize   : nat }.

  Record Reg := { regKind : Kind ;
                  regInit : type regKind }.

  Record Mem := { memSize : nat ;
                  memKind : Kind ;
                  memPort : nat ;
                  memInit : option (type (Array memSize memKind) * VerilogMem) }.

  Definition memInitFull m := match memInit m return type (Array (memSize m) (memKind m)) with
                              | None => Default _
                              | Some (init, _) => init
                              end.

  Record MemU := { memUSize : nat ;
                   memUKind : Kind ;
                   memUPort : nat }.

  Definition memToMemU (m: Mem) := Build_MemU (memSize m) (memKind m) (memPort m).

  Inductive LetExpr (k: Kind): Type :=
  | RetE (e: Expr k)
  | SystemE (ls: list SysT) (cont: LetExpr k)
  | LetEx (s: string) k' (e: LetExpr k') (cont: ty k' -> LetExpr k)
  | IfElseE (s: string) (p: Expr Bool) k' (t f: LetExpr k') (cont: ty k' -> LetExpr k).

  Record ModLists := {
      mregs : list (string * Kind);
      mmems : list (string * MemU);
      mregUs: list (string * Kind);
      mmemUs: list (string * MemU);
      msends: list (string * Kind);
      mrecvs: list (string * Kind) }.

  Section Action.
    Variable modLists: ModLists.

    Inductive Action (k: Kind) : Type :=
    | ReadReg (s: string) (x: FinStruct (mregs modLists)) (cont: ty (fieldK x) -> Action k)
    | WriteReg (x: FinStruct (mregs modLists)) (v: Expr (fieldK x)) (cont: Action k)
    | ReadRqMem (x: FinStruct (mmems modLists)) (i: Expr (Bit (Nat.log2_up (memUSize (fieldK x)))))
        (p: FinArray (memUPort (fieldK x))) (cont: Action k)
    | ReadRpMem (s: string) (x: FinStruct (mmems modLists)) (p: FinArray (memUPort (fieldK x)))
        (cont: ty (memUKind (fieldK x)) -> Action k)
    | WriteMem (x: FinStruct (mmems modLists)) (i: Expr (Bit (Nat.log2_up (memUSize (fieldK x)))))
        (v: Expr (memUKind (fieldK x))) (cont: Action k)
    | ReadRegU (s: string) (x: FinStruct (mregUs modLists)) (cont: ty (fieldK x) -> Action k)
    | WriteRegU (x: FinStruct (mregUs modLists)) (v: Expr (fieldK x)) (cont: Action k)
    | ReadRqMemU (x: FinStruct (mmemUs modLists)) (i: Expr (Bit (Nat.log2_up (memUSize (fieldK x)))))
        (p: FinArray (memUPort (fieldK x))) (cont: Action k)
    | ReadRpMemU (s: string) (x: FinStruct (mmemUs modLists)) (p: FinArray (memUPort (fieldK x)))
        (cont: ty (memUKind (fieldK x)) -> Action k)
    | WriteMemU (x: FinStruct (mmemUs modLists)) (i: Expr (Bit (Nat.log2_up (memUSize (fieldK x)))))
        (v: Expr (memUKind (fieldK x))) (cont: Action k)
    | Send (x: FinStruct (msends modLists)) (v: Expr (fieldK x)) (cont: Action k)
    | Recv (s: string) (x: FinStruct (mrecvs modLists)) (cont: ty (fieldK x) -> Action k)
    | LetExp (s: string) k' (e: Expr k') (cont: ty k' -> Action k)
    | LetAction (s: string) k' (a: Action k') (cont: ty k' -> Action k)
    | NonDet (s: string) k' (cont: ty k' -> Action k)
    | IfElse (s: string) (p: Expr Bool) k' (t f: Action k') (cont: ty k' -> Action k)
    | System (ls: list SysT) (cont: Action k)
    | Return (e: Expr k).

    Fixpoint toAction k (le: LetExpr k): Action k :=
      match le with
      | RetE e => Return e
      | SystemE ls cont => System ls (toAction cont)
      | LetEx s k' le cont => LetAction s (toAction le) (fun x => toAction (cont x))
      | IfElseE s p k' t f cont => IfElse s p (toAction t) (toAction f) (fun x => toAction (cont x))
      end.
  End Action.
End Phoas.

Arguments Return [ty modLists k] e.
Arguments toAction [ty modLists k] le.

Record ModDecl := { modRegs : list (string * Reg) ;
                    modMems : list (string * Mem) ;
                    modRegUs: list (string * Kind) ;
                    modMemUs: list (string * MemU) ;
                    modSends: list (string * Kind) ;
                    modRecvs: list (string * Kind) }.

Definition getModLists (decl: ModDecl) : ModLists :=
  (Build_ModLists
     (map (fun x => (fst x, regKind (snd x))) (modRegs decl))
     (map (fun x => (fst x, memToMemU (snd x))) (modMems decl))
     (modRegUs decl)
     (modMemUs decl)
     (modSends decl)
     (modRecvs decl)).

Record Mod := {
    modDecl: ModDecl;
    modActions: forall ty, list (Action ty (getModLists modDecl) (Bit 0)) }.

Section CombineActionsDef.
  Variable ty: Kind -> Type.
  Variable modLists: ModLists.

  Fixpoint combineActions (ls: list (Action ty modLists (Bit 0))): Action ty modLists (Bit 0) :=
    match ls return Action ty modLists (Bit 0) with
    | nil => Return (Const _ (Bit 0) WO)
    | x :: xs => LetAction ""%string x (fun _ => combineActions xs)
    end.
End CombineActionsDef.
