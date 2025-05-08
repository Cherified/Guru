Require Import String List.
Require Import Guru.Lib.Library.
Require Import Guru.Syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Local Definition CTmp := (string * nat)%type.
Definition CExpr := Expr (fun k => CTmp).
Section CTmp.
  Variable x: CTmp.
  Local Definition cTmpName: string := fst x.
  Local Definition cTmpIdx: nat := snd x.
End CTmp.

Local Definition CReg := (string * nat)%type.
Section CReg.
  Variable x: CReg.
  Local Definition cRegName: string := fst x.
  Local Definition cRegPos: nat := snd x.
End CReg.

Local Definition CMem := (string * nat)%type.
Section CMem.
  Variable x: CMem.
  Local Definition cMemName: string := fst x.
  Local Definition cMemPos: nat := snd x.
End CMem.

Local Definition CMeth := (string * nat * nat)%type.
Section CMeth.
  Variable x: CMeth.
  Local Definition cMethName: string := fst (fst x).
  Local Definition cMethPos: nat := snd (fst x).
  Local Definition cMethIdx: nat := snd x.
End CMeth.

Inductive Compiled :=
| CReadReg (x : CReg) (k: Kind) (t: CTmp) (cont: Compiled)
| CWriteReg (x : CReg) k (v: CExpr k) (cont: Compiled)
| CReadRqMem (x: CMem) (k: Kind) sz (i: CExpr (Bit (PeanoNat.Nat.log2_up sz))) (p: nat) (cont: Compiled)
| CReadRpMem (x: CMem) (p: nat) (k: Kind) (sz: nat) (t: CTmp) (cont: Compiled)
| CWriteMem (x: CMem) sz (i: CExpr (Bit (PeanoNat.Nat.log2_up sz))) k (v: CExpr k) (cont: Compiled)
| CReadRegU (x : CReg) (k: Kind) (t: CTmp) (cont: Compiled)
| CWriteRegU (x : CReg) k (e: CExpr k) (cont: Compiled)
| CReadRqMemU (x: CMem) (k: Kind) sz (i: CExpr (Bit (PeanoNat.Nat.log2_up sz))) (p: nat) (cont: Compiled)
| CReadRpMemU (x: CMem) (p: nat) (k: Kind) (sz: nat) (t: CTmp) (cont: Compiled)
| CWriteMemU (x: CMem) sz (i: CExpr (Bit (PeanoNat.Nat.log2_up sz))) k (v: CExpr k) (cont: Compiled)
| CSend (x: CMeth) k (v: CExpr k) (cont: Compiled)
| CRecv (x: CMeth) (k: Kind) (t: CTmp) (cont: Compiled)
| CLetExpr (t: CTmp) k (v: CExpr k) (cont: Compiled)
| CLetAction (k': Kind) (a: Compiled) (cont: Compiled)
| CNonDet (t: CTmp) (k: Kind) (cont: Compiled)
| CIfElse (p: CExpr Bool) (k': Kind) (t f cont: Compiled)
| CSys (ls: list (SysT (fun k => CTmp))) (cont: Compiled)
| CReturn (t: CTmp) k (v: CExpr k).


(* Synchronous memory issues:
   - Bypass if ReadRq before ReadRp
   - Bypass if Write before ReadRp (from address reg if address is registered)
   - Bypass if Write before ReadRq (to data reg if data is registered)
   - Correct orders for address registered: ReadRp, ReadRq, Write; ReadRp, Write, ReadRq
   - Only Correct order for data registered: ReadRp, ReadRq, Write

   We support just data registered synchronous memory for now,
   and error out in the compiler if any of the above bypass conditions arise.
   The compiler also errors out if multiple Writes occur *)

(* Structure to keep track of Mem ReadRq, ReadRp and Write,
   to ensure only order [ReadRp; ReadRq; Write] is used *)
Section MemCalls.
  Variable ls: list (string * (nat * Kind * nat)).
  Definition MemCalls := forall i: FinStruct ls, (bool * (FinArray (snd (fieldK i)) -> (bool * bool))).
  Variable portCalls: MemCalls.
  Definition memCallsAddRq x p := updStruct (ty := fun K => (bool * (FinArray (snd K) -> (bool * bool)))%type)
                                    portCalls (let (write, rqRps) := portCalls x in
                                               let (rq, rp) := rqRps p in
                                               (write, updArray rqRps p (true, rp))).
  Definition memCallsAddRp x p := updStruct (ty := fun K => (bool * (FinArray (snd K) -> (bool * bool)))%type)
                                    portCalls (let (write, rqRps) := portCalls x in
                                               let (rq, rp) := rqRps p in
                                               (write, updArray rqRps p (rq, true))).
  Definition memCallsAddWr x := updStruct (ty := fun K => (bool * (FinArray (snd K) -> (bool * bool)))%type)
                                  portCalls (let (write, rqRps) := portCalls x in
                                             (true, rqRps)).
  Definition memCallsHasRq x p := fst (snd (portCalls x) p).
  Definition memCallsHasRp x p := snd (snd (portCalls x) p).
  Definition memCallsHasWr x := fst (portCalls x).
End MemCalls.

Section UnionMemCalls.
  Variable ls: list (string * (nat * Kind * nat)).
  Variable p1 p2: MemCalls ls.
  Local Open Scope bool.
  Definition unionMemCalls : MemCalls ls :=
    (fun x =>
       (memCallsHasWr p1 x || memCallsHasWr p2 x,
         fun p => (memCallsHasRq p1 p || memCallsHasRq p2 p,
                    memCallsHasRp p1 p || memCallsHasRp p2 p))).
End UnionMemCalls.

Section CompileAction.
  Variable regs: list (string * Kind).
  Variable mems: list (string * (nat * Kind * nat)).
  Variable regUs: list (string * Kind).
  Variable memUs: list (string * (nat * Kind * nat)).
  Variable sends: list (string * Kind).
  Variable recvs: list (string * Kind).

  
  Definition CompileState :=
    ((FinStruct sends -> nat) * (* Generate a new port for each same Send *)
       (FinStruct recvs -> nat) * (* Generate a new port for each same Recv *)
       list (string * Kind) * (* List of LET names and Kinds. List position determines the full name *)
       MemCalls mems *
       MemCalls memUs )%type.

  Local Open Scope bool.

  Fixpoint compileAction k (a: @Action (fun k => CTmp) regs mems regUs memUs sends recvs k):
    CompileState -> CTmp -> (bool * CompileState * Compiled) :=
    match a return CompileState -> CTmp -> (bool * CompileState * Compiled) with
    | ReadReg s x cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in
          let (result, rest) :=
            compileAction (cont tmp)
              (sends, recvs, (s, fieldK x) :: tmps, memCalls, memUCalls) retVar in
          (result, CReadReg (fieldName x, FinStruct_to_nat x) (fieldK x) tmp rest)
    | WriteReg x v cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let (result, rest) :=
            compileAction cont
              (sends, recvs, tmps, memCalls, memUCalls) retVar in
          (result, CWriteReg (fieldName x, FinStruct_to_nat x) v rest)
    | ReadRqMem x i p cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let '(valid, newSt, rest) :=
            compileAction cont
              (sends, recvs, tmps, memCallsAddRq memCalls p, memUCalls) retVar in
          (* [Write; ReadRq] is not allowed *)
          ((negb (memCallsHasRq memCalls p || memCallsHasWr memCalls x)) && valid, newSt,
            CReadRqMem (fieldName x, FinStruct_to_nat x) (snd (fst (fieldK x))) i (FinArray_to_nat p) rest)
    | ReadRpMem s x p cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in
          let '(valid, newSt, rest) :=
            compileAction (cont tmp)
              (sends, recvs, (s, snd (fst (fieldK x))) :: tmps,
                memCallsAddRp memCalls p, memUCalls) retVar in
          (* [ReadRq; ReadRp] is not allowed *)
          ((negb (memCallsHasRp memCalls p || memCallsHasRq memCalls p)) && valid, newSt,
            CReadRpMem (fieldName x, FinStruct_to_nat x) (FinArray_to_nat p) (snd (fst (fieldK x))) (fst (fst (fieldK x))) tmp rest)
    | WriteMem x i v cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let '(valid, newSt, rest) :=
            compileAction cont
              (sends, recvs, tmps,  memCallsAddWr memCalls x, memUCalls) retVar in
          ((negb (memCallsHasWr memCalls x)) && valid, newSt,
            CWriteMem (fieldName x, FinStruct_to_nat x) i v rest)
    | ReadRegU s x cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in
          let (result, rest) :=
            compileAction (cont tmp)
              (sends, recvs, (s, fieldK x) :: tmps, memCalls, memUCalls) retVar in
          (result, CReadRegU (fieldName x, FinStruct_to_nat x) (fieldK x) tmp rest)
    | WriteRegU x v cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let (result, rest) :=
            compileAction cont
              (sends, recvs, tmps, memCalls, memUCalls) retVar in
          (result, CWriteRegU (fieldName x, FinStruct_to_nat x) v rest)
    | ReadRqMemU x i p cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let '(valid, newSt, rest) :=
            compileAction cont
              (sends, recvs, tmps, memCalls, memCallsAddRq memUCalls p) retVar in
          (* [Write; ReadRq] is not allowed *)
          ((negb (memCallsHasRq memUCalls p || memCallsHasWr memUCalls x)) && valid, newSt,
            CReadRqMemU (fieldName x, FinStruct_to_nat x) (snd (fst (fieldK x))) i (FinArray_to_nat p) rest)
    | ReadRpMemU s x p cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in
          let '(valid, newSt, rest) :=
            compileAction (cont tmp)
              (sends, recvs, (s, snd (fst (fieldK x))) :: tmps, memCalls,
                memCallsAddRp memUCalls p) retVar in
          (* [ReadRq; ReadRp] is not allowed *)
          ((negb (memCallsHasRp memUCalls p || memCallsHasRq memUCalls p)) && valid, newSt,
            CReadRpMemU (fieldName x, FinStruct_to_nat x) (FinArray_to_nat p) (snd (fst (fieldK x))) (fst (fst (fieldK x))) tmp rest)
    | WriteMemU x i v cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let '(valid, newSt, rest) :=
            compileAction cont
              (sends, recvs, tmps,  memCalls, memCallsAddWr memUCalls x) retVar in
          ((negb (memCallsHasWr memUCalls x)) && valid, newSt,
            CWriteMemU (fieldName x, FinStruct_to_nat x) i v rest)
    | Send x v cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let (result, rest) :=
            compileAction cont (updStruct (ty := fun _ => nat) sends (x := x) (S (sends x)),
                recvs, tmps, memCalls, memUCalls) retVar in
          (result, CSend (fieldName x, FinStruct_to_nat x, sends x) v rest)
    | Recv s x cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let (result, rest) :=
            compileAction (cont tmp) (sends, updStruct (ty := fun _ => nat) recvs (x := x) (S (recvs x)),
                (s, fieldK x) :: tmps, memCalls, memUCalls) retVar in
          (result, CRecv (fieldName x, FinStruct_to_nat x,recvs x) (fieldK x) tmp rest)
    | LetExpr s k' v cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let (result, rest) :=
            compileAction (cont tmp) (sends, recvs, (s, k') :: tmps, memCalls, memUCalls) retVar in
          (result, CLetExpr tmp v rest)
    | LetAction s k' act cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let '(valid1, newSt1, rest1) :=
            compileAction act (sends, recvs, (s, k') :: tmps, memCalls, memUCalls) tmp in
          let '(valid, newSt, rest) := compileAction (cont tmp) newSt1 retVar in
          (valid1 && valid, newSt, CLetAction k' rest1 rest)
    | NonDet s k' cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let (result, rest) :=
            compileAction (cont tmp) (sends, recvs, (s, k') :: tmps, memCalls, memUCalls) retVar in
          (result, CNonDet tmp k' rest)
    | IfElse s p k' t f cont =>
        fun '(sends, recvs, tmps, memCalls, memUCalls) retVar =>
          let tmp := (s, length tmps) in          
          let '(validT, (sendsT, recvsT, tmpsT, memCallsT, memUCallsT), restT) :=
            compileAction t (sends, recvs, (s, k') :: tmps, memCalls, memUCalls) tmp in
          let '(validF, (sendsF, recvsF, tmpsF, memCallsF, memUCallsF), restF) :=
            compileAction f (sends, recvs, tmpsT, memCalls, memUCalls) tmp in
          let '(valid, newSt, rest) :=
            compileAction (cont tmp)
              (fun i => Nat.max (sendsT i) (sendsF i), fun i => Nat.max (recvsT i) (recvsF i), tmpsF,
                unionMemCalls memCallsT memCallsF, unionMemCalls memUCallsT memUCallsF) retVar in
          (validT && validF && valid, newSt, CIfElse p k' restT restF rest)
    | Sys ls cont =>
        fun st retVar =>
          let (result, rest) := compileAction cont st retVar in
          (result, CSys ls rest)
    | Return v =>
        fun st retVar =>
          (true, st, CReturn retVar v)
    end.
End CompileAction.

Section Compile.
  Variable m: Mod.

  Local Definition noMemCalls ls: MemCalls ls := fun x => (false, fun p => (false, false)).

  Definition CompiledModule := (ModDecl *
                                  (FinStruct (modSends (modDecl m)) -> nat) *
                                  (FinStruct (modRecvs (modDecl m)) -> nat) *
                                  list (string * Kind) *
                                  Compiled)%type.

  Definition compile: option CompiledModule :=
    let retString := "final"%string in
    let initState := (fun i => 0, fun i => 0, (retString, Bit 0) :: nil, @noMemCalls _, @noMemCalls _) in
    let '(valid, (sends, recvs, tmps, _, _), code) :=
      compileAction (combineActions (modActions m (fun k => CTmp))) initState (retString, 0) in
    if valid
    then Some (modDecl m, sends, recvs, tmps, code)
    else None.
End Compile.
