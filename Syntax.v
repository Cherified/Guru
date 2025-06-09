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
  | And: list (Expr Bool) -> Expr Bool
  | Xor: list (Expr Bool) -> Expr Bool
  | Not: Expr Bool -> Expr Bool
  | Inv n: Expr (Bit n) -> Expr (Bit n)
  | TruncLsb msb lsb: Expr (Bit (lsb + msb)%Z) -> Expr (Bit lsb)
  | TruncMsb msb lsb: Expr (Bit (lsb + msb)%Z) -> Expr (Bit msb)
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
  | UpdateStruct [ls: list (string * Kind)] (e: Expr (Struct ls)) (p: FinStruct ls) (v: Expr (fieldK p)):
    Expr (Struct ls)
  | UpdateArray [n k] (e: Expr (Array n k)) m (i: Expr (Bit m)) (v: Expr k): Expr (Array n k)
  | UpdateArrayConst [n k] (e: Expr (Array n k)) (p: FinType n) (v: Expr k): Expr (Array n k)
  | ToBit k (e: Expr k): Expr (Bit (size k))
  | FromBit k (e: Expr (Bit (size k))): Expr k
  (* The following 2 don't pass positivity check in Rocq *)
  | BuildStruct [ls: list (string * Kind)] (vals: DiffTuple (fun x => Expr (snd x)) ls): Expr (Struct ls)
  | BuildArray [n k] (vals: SameTuple (Expr k) n): Expr (Array n k).
End Phoas.
Set Positivity Checking.

Section Phoas.
  Variable ty: Kind -> Type.
  Local Notation Expr := (Expr ty).

  Definition Neq k (e1 e2: Expr k) := Not (Eq e1 e2).

  Definition Sub n (a b: Expr (Bit n)): Expr (Bit n) := Add [a; Inv b; Const _ (Bit n) Zmod.one].

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

  Definition OneExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (lsb + msb)) :=
    Concat (Const _ (Bit msb) (Zmod.of_Z _ (-1))) e.

  Definition ZeroExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (lsb + msb)) :=
    Concat (Const _ (Bit _) Zmod.zero) e.

  Definition SignExtend msb lsb (e: Expr (Bit lsb)): Expr (Bit (lsb + msb)) :=
    Concat (ITE (Eq (TruncMsb 1 (lsb-1) (castBits (eq_sym (Z.sub_add _ _)) e)) (Const _ (Bit _) Zmod.zero))
              (Const _ (Bit _) Zmod.zero)
              (Const _ (Bit _) (Zmod.of_Z _ (-1)))) e.

  Definition ZeroExtendTo outSz inSz (e: Expr (Bit inSz)) := ZeroExtend (outSz - inSz) e.
  Definition SignExtendTo outSz inSz (e: Expr (Bit inSz)) := SignExtend (outSz - inSz) e.

  Fixpoint replicate sz (e: Expr (Bit sz)) n : Expr (Bit (NatZ_mul n sz)) :=
    match n return Expr (Bit (NatZ_mul n sz)) with
    | 0 => Const _ (Bit _) Zmod.zero
    | S m => Concat e (replicate e m)
    end.

  Definition isZero n (e: Expr (Bit n)) := Eq e (Const _ (Bit _) Zmod.zero).
  Definition isNotZero n (e: Expr (Bit n)) := Not (isZero e).
  Definition UOr n (e: Expr (Bit n)) := isNotZero e.
  Definition isAllOnes n (e: Expr (Bit n)) := Eq e (Const _ (Bit _) (Zmod.of_Z _ (-1))).
  Definition UAnd n (e: Expr (Bit n)) := isAllOnes e.

  Definition rotateRight n (e: Expr (Bit n)) m (shamt: Expr (Bit m)) :=
    ( Or [Srl e shamt; Sll e (Sub (Const _ (Bit m) (Zmod.of_Z _ n)) shamt)]).

  Definition rotateLeft n (e: Expr (Bit n)) m (shamt: Expr (Bit m)) :=
    ( Or [Sll e shamt; Srl e (Sub (Const _ (Bit m) (Zmod.of_Z _ n)) shamt)]).

  Definition mkBoolArray n := FromBit (ty := ty) (Array (Z.to_nat n) Bool).

  Definition countLeadingZerosArray ni (arr: Expr (Array ni Bool)) no: Expr (Bit no) :=
    snd (fold_left (fun '(over, accum) i =>
                      let curr := readNatToFinType (Const _ Bool false) (ReadArrayConst arr) i in
                      let cond := Or [over; curr] in
                      (cond,
                        Add [accum;
                             ITE cond
                               (Const _ (Bit no) Zmod.zero)
                               (Const _ (Bit no) Zmod.one)])) (seq 0 ni)
           (Const _ Bool false, Const _ (Bit no) Zmod.zero)).

  Definition countTrailingZerosArray ni (arr: Expr (Array ni Bool)) no: Expr (Bit no) :=
    snd (fold_left (fun '(over, accum) i =>
                      let curr := readNatToFinType (Const _ Bool false) (ReadArrayConst arr) i in
                      let cond := Or [over; curr] in
                      (cond,
                        Add [accum;
                             ITE cond
                               (Const _ (Bit no) Zmod.zero)
                               (Const _ (Bit no) Zmod.one)])) (seq 0 ni)
           (Const _ Bool false, Const _ (Bit no) Zmod.zero)).

  Definition countOnesArray ni (arr: Expr (Array ni Bool)) no: Expr (Bit no) :=
    fold_left (fun accum i =>
                 let curr := readNatToFinType (Const _ Bool false) (ReadArrayConst arr) i in
                 Add [accum;
                      ITE curr
                        (Const _ (Bit no) Zmod.one)
                        (Const _ (Bit no) Zmod.zero)]) (seq 0 ni)
      (Const _ (Bit no) Zmod.zero).

  (* To be used only if there are multiple disjoint cases *)
  Section CaseDefault.
      Variable k: Kind.
      Variable ls: list (Expr Bool * Expr k).
      Variable def: Expr k.
      Definition caseDefault :=
        ITE (Or (map fst ls)) (Or (map (fun '(p, v) => ITE p v (Const _ k (Default k))) ls)) def.
  End CaseDefault.

  Inductive BitFormat :=
  | Binary
  | Decimal
  | Hex.
End Phoas.

Unset Positivity Checking.
Section Phoas.
  Inductive FullFormat: Kind -> Type :=
  | FBool: nat -> BitFormat -> FullFormat Bool
  | FBit n: Z -> BitFormat -> FullFormat (Bit n)
  | FStruct [ls]: DiffTuple (fun x => FullFormat (snd x)) ls -> FullFormat (Struct ls)
  | FArray n k: FullFormat k -> FullFormat (@Array n k).
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
      FArray.

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

  #[projections(primitive)]
  Record VerilogMem := { verilogAscii  : bool ;
                         verilogName   : string ;
                         verilogOffset : nat ;
                         verilogSize   : nat }.

  #[projections(primitive)]
  Record Reg := { regKind : Kind ;
                  regInit : type regKind }.

  #[projections(primitive)]
  Record Mem := { memSize : nat ;
                  memKind : Kind ;
                  memPort : nat ;
                  memInit : option (type (Array memSize memKind) * VerilogMem) }.

  Definition memInitFull m := match m.(memInit) return type (Array m.(memSize) m.(memKind)) with
                              | None => Default _
                              | Some (init, _) => init
                              end.

  #[projections(primitive)]
  Record MemU := { memUSize : nat ;
                   memUKind : Kind ;
                   memUPort : nat }.

  Definition memToMemU (m: Mem) := Build_MemU m.(memSize) m.(memKind) m.(memPort).

  Inductive LetExpr (k: Kind): Type :=
  | RetE (e: Expr k)
  | SystemE (ls: list SysT) (cont: LetExpr k)
  | LetEx (s: string) k' (e: LetExpr k') (cont: ty k' -> LetExpr k)
  | IfElseE (s: string) (p: Expr Bool) k' (t f: LetExpr k') (cont: ty k' -> LetExpr k).

  #[projections(primitive)]
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
    | ReadReg (s: string) (x: FinStruct modLists.(mregs)) (cont: ty (fieldK x) -> Action k)
    | WriteReg (x: FinStruct modLists.(mregs)) (v: Expr (fieldK x)) (cont: Action k)
    | ReadRqMem (x: FinStruct modLists.(mmems)) (i: Expr (Bit (Z.log2_up (Z.of_nat ((fieldK x).(memUSize))))))
        (p: FinType (fieldK x).(memUPort)) (cont: Action k)
    | ReadRpMem (s: string) (x: FinStruct modLists.(mmems)) (p: FinType (fieldK x).(memUPort))
        (cont: ty (fieldK x).(memUKind) -> Action k)
    | WriteMem (x: FinStruct modLists.(mmems)) (i: Expr (Bit (Z.log2_up (Z.of_nat ((fieldK x).(memUSize))))))
        (v: Expr (fieldK x).(memUKind)) (cont: Action k)
    | ReadRegU (s: string) (x: FinStruct modLists.(mregUs)) (cont: ty (fieldK x) -> Action k)
    | WriteRegU (x: FinStruct modLists.(mregUs)) (v: Expr (fieldK x)) (cont: Action k)
    | ReadRqMemU (x: FinStruct modLists.(mmemUs)) (i: Expr (Bit (Z.log2_up (Z.of_nat (fieldK x).(memUSize)))))
        (p: FinType (fieldK x).(memUPort)) (cont: Action k)
    | ReadRpMemU (s: string) (x: FinStruct modLists.(mmemUs)) (p: FinType (fieldK x).(memUPort))
        (cont: ty (fieldK x).(memUKind) -> Action k)
    | WriteMemU (x: FinStruct modLists.(mmemUs)) (i: Expr (Bit (Z.log2_up (Z.of_nat (fieldK x).(memUSize)))))
        (v: Expr (fieldK x).(memUKind)) (cont: Action k)
    | Send (x: FinStruct modLists.(msends)) (v: Expr (fieldK x)) (cont: Action k)
    | Recv (s: string) (x: FinStruct modLists.(mrecvs)) (cont: ty (fieldK x) -> Action k)
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

Arguments Return [ty]%_function_scope [modLists k] e.

#[projections(primitive)]
Record ModDecl := { modRegs : list (string * Reg) ;
                    modMems : list (string * Mem) ;
                    modRegUs: list (string * Kind) ;
                    modMemUs: list (string * MemU) ;
                    modSends: list (string * Kind) ;
                    modRecvs: list (string * Kind) }.

Definition getModLists (decl: ModDecl) : ModLists :=
  (Build_ModLists
     (map (fun x => (fst x, (snd x).(regKind))) decl.(modRegs))
     (map (fun x => (fst x, (memToMemU (snd x)))) decl.(modMems))
     decl.(modRegUs)
     decl.(modMemUs)
     decl.(modSends)
     decl.(modRecvs)).

Record Mod := {
    modDecl: ModDecl;
    modActions: forall ty, list (Action ty (getModLists modDecl) (Bit 0)) }.

Section CombineActionsDef.
  Variable ty: Kind -> Type.
  Variable modLists: ModLists.

  Fixpoint combineActions (ls: list (Action ty modLists (Bit 0))): Action ty modLists (Bit 0) :=
    match ls return Action ty modLists (Bit 0) with
    | nil => Return (Const _ (Bit 0) Zmod.zero)
    | x :: xs => LetAction EmptyString x (fun _ => combineActions xs)
    end.
End CombineActionsDef.
