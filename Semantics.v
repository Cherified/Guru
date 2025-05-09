Require Import String List Psatz.
Require Import Guru.Lib.Library Guru.Lib.Word.
Require Import Guru.Syntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

Fixpoint evalExpr k (e: Expr type k): type k :=
  match e in Expr _ k return type k with
  | Var _ v => v
  | Const _ v => v
  | Or _ ls => fold_left (@evalOrBinary _) (map (@evalExpr _) ls) (Default _)
  | And ls => fold_left andb (map (@evalExpr Bool) ls) true
  | Xor ls => fold_left xorb (map (@evalExpr Bool) ls) false
  | Not v => negb (evalExpr v)
  | Inv _ v => wneg (evalExpr v)
  | TruncLsb _ _ v => truncLsb (evalExpr v)
  | TruncMsb _ _ v => truncMsb (evalExpr v)
  | UOr n v => wuor (evalExpr v)
  | UAnd n v => wuand (evalExpr v)
  | UXor n v => wuxor (evalExpr v)
  | Add n ls => fold_left wadd (map (@evalExpr (Bit n)) ls) (ZToWord n 0)
  | Mul n ls => fold_left wmul (map (@evalExpr (Bit n)) ls) (ZToWord n 0)
  | Band n ls => fold_left wand (map (@evalExpr (Bit n)) ls) (ZToWord n 0)
  | Bxor n ls => fold_left wxor (map (@evalExpr (Bit n)) ls) (ZToWord n 0)
  | Div n a b => wdiv (evalExpr a) (evalExpr b)
  | Rem n a b => wmod (evalExpr a) (evalExpr b)
  | Sll _ _ a b => wslu (evalExpr a) (ZToWord _ (wordVal _ (evalExpr b)))
  | Srl _ _ a b => wsru (evalExpr a) (ZToWord _ (wordVal _ (evalExpr b)))
  | Sra _ _ a b => wsra (evalExpr a) (evalExpr b)
  | Concat _ _ a b => wcombine (evalExpr a) (evalExpr b)
  | ITE _ p t f => if evalExpr p then evalExpr t else evalExpr f
  | Eq _ a b => if isEq (evalExpr a) (evalExpr b) then true else false
  | ReadStruct _ v i => (structToFunc (evalExpr v)) i
  | ReadArray n _ k v i =>
      match lt_dec (Z.to_nat (wordVal _ (evalExpr i))) n return type k with
      | left pf => arrayToFunc (evalExpr v) (FinArray_of_nat_lt pf)
      | right _ => Default k
      end
  | ReadArrayConst _ _ v i => (arrayToFunc (evalExpr v)) i
  | BuildStruct _ vs => funcToStruct (fun i => evalExpr (vs i))
  | BuildArray _ _ vs => funcToArray (fun i => evalExpr (vs i))
  | ToBit _ v => evalToBit (evalExpr v)
  | FromBit _ v => evalFromBit (evalExpr v)
  end.

Definition FuncState (ls: list (string * Kind)) := forall i: FinStruct ls, type (fieldK i).
Definition FuncMemState (ls: list (string * (nat * Kind * nat))) :=
  forall i: FinStruct ls,
    (type (Array (fst (fst (fieldK i))) (snd (fst (fieldK i)))) *
             type (Array (snd (fieldK i)) (snd (fst (fieldK i))))).
Definition FuncIo (ls: list (string * Kind)) := forall i: FinStruct ls, list (type (fieldK i)).

Record ModState regs mems regUs memUs :=
  { stateRegs  : FuncState regs;
    stateMems  : FuncMemState mems;
    stateRegUs : FuncState regUs;
    stateMemUs : FuncMemState memUs}.

Section SemAction.
  Variable regs: list (string * Kind).
  Variable mems: list (string * (nat * Kind * nat)).
  Variable regUs: list (string * Kind).
  Variable memUs: list (string * (nat * Kind * nat)).
  Variable sends: list (string * Kind).
  Variable recvs: list (string * Kind).

  Inductive SemAction k: Action type regs mems regUs memUs sends recvs k ->
                         ModState regs mems regUs memUs ->
                         ModState regs mems regUs memUs ->
                         FuncIo sends ->
                         FuncIo recvs ->
                         type k -> Prop :=
  | SemReadReg s x cont old new puts gets ret
      (contPf: SemAction (cont (stateRegs old x)) old new puts gets ret):
    SemAction (ReadReg s x cont) old new puts gets ret
  | SemWriteReg x (v: Expr type (fieldK x)) cont old new puts gets ret
      (contPf: SemAction cont {|stateRegs := updStruct (stateRegs old) (evalExpr v);
                                stateMems := stateMems old;
                                stateRegUs := stateRegUs old;
                                stateMemUs := stateMemUs old|} new puts gets ret):
    SemAction (WriteReg x v cont) old new puts gets ret
  | SemReadRqMem x (i: Expr type (Bit (Nat.log2_up (fst (fst (fieldK x)))))) p cont old new puts gets ret
      (contPf:
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems := updStruct (stateMems old)
                           (ty := fun K => (type (Array (fst (fst K)) (snd (fst K))) *
                                              type (Array (snd K) (snd (fst K))))%type)
                           (let arr := stateMems old x in
                            (fst arr,
                              funcToArray (updArray (arrayToFunc (snd arr)) p
                                             (readArray (Default _) (arrayToFunc (fst arr)) (evalExpr i)))));
            stateRegUs := stateRegUs old;
            stateMemUs := stateMemUs old|} new puts gets ret):
    SemAction (ReadRqMem x i p cont) old new puts gets ret
  | SemReadRpMem s x p cont old new puts gets ret
      (contPf: SemAction (cont (arrayToFunc (snd (stateMems old x)) p)) old new puts gets ret):
      SemAction (ReadRpMem s x p cont) old new puts gets ret
  | SemWriteMem x (i: Expr type (Bit (Nat.log2_up (fst (fst (fieldK x)))))) v cont old new puts gets ret
      (contPf:
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems := updStruct (stateMems old)
                           (ty := fun K => (type (Array (fst (fst K)) (snd (fst K))) *
                                              type (Array (snd K) (snd (fst K))))%type)
                           (let arr := stateMems old x in
                            (funcToArray (writeArray (evalExpr v) (arrayToFunc (fst arr)) (evalExpr i)),
                              snd arr));
            stateRegUs := stateRegUs old;
            stateMemUs := stateMemUs old|} new puts gets ret):
    SemAction (WriteMem x i v cont) old new puts gets ret
  | SemReadRegU s x cont old new puts gets ret
      (contPf: SemAction (cont (stateRegUs old x)) old new puts gets ret):
    SemAction (ReadRegU s x cont) old new puts gets ret
  | SemWriteRegU x (v: Expr type (fieldK x)) cont old new puts gets ret
      (contPf: SemAction cont {|stateRegs := stateRegs old;
                                stateMems := stateMems old;
                                stateRegUs := updStruct (stateRegUs old) (evalExpr v);
                                stateMemUs := stateMemUs old|} new puts gets ret):
    SemAction (WriteRegU x v cont) old new puts gets ret
  | SemReadRqMemU x (i: Expr type (Bit (Nat.log2_up (fst (fst (fieldK x)))))) p cont old new puts gets ret
      (contPf:
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems := stateMems old;
            stateRegUs := stateRegUs old;
            stateMemUs := updStruct (stateMemUs old)
                           (ty := fun K => (type (Array (fst (fst K)) (snd (fst K))) *
                                              type (Array (snd K) (snd (fst K))))%type)
                           (let arr := stateMemUs old x in
                            (fst arr,
                              funcToArray (updArray (arrayToFunc (snd arr)) p
                                             (readArray (Default _) (arrayToFunc (fst arr)) (evalExpr i)))))|}
          new puts gets ret):
      SemAction (ReadRqMemU x i p cont) old new puts gets ret
  | SemReadRpMemU s x p cont old new puts gets ret
      (contPf: SemAction (cont (arrayToFunc (snd (stateMemUs old x)) p)) old new puts gets ret):
      SemAction (ReadRpMemU s x p cont) old new puts gets ret
  | SemWriteMemU x (i: Expr type (Bit (Nat.log2_up (fst (fst (fieldK x)))))) v cont old new puts gets ret
      (contPf:
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems := stateMems old;
            stateRegUs := stateRegUs old;
            stateMemUs := updStruct (stateMemUs old)
                            (ty := fun K => (type (Array (fst (fst K)) (snd (fst K))) *
                                               type (Array (snd K) (snd (fst K))))%type)
                            (let arr := stateMemUs old x in
                             (funcToArray (writeArray (evalExpr v) (arrayToFunc (fst arr)) (evalExpr i)),
                               snd arr)) |} new puts gets ret):
    SemAction (WriteMemU x i v cont) old new puts gets ret
  | SemSend x v cont old new puts gets ret
      putsStep
      (contPf: SemAction cont old new putsStep gets ret)
      (putsVal: puts = updStruct (ty := fun K => list (type K)) putsStep (evalExpr v :: putsStep x)):
      SemAction (Send x v cont) old new puts gets ret
  | SemRecv s x cont old new puts gets ret
      recvStep getsStep
      (contPf: SemAction (cont recvStep) old new puts getsStep ret)
      (putsVal: gets = updStruct (ty := fun K => list (type K)) getsStep (recvStep :: getsStep x)):
      SemAction (Recv s x cont) old new puts gets ret
  | SemLetExpr s k' (e: Expr type k') cont old new puts gets ret
      (contPf: SemAction (cont (evalExpr e)) old new puts gets ret):
    SemAction (LetExpr s e cont) old new puts gets ret
  | SemLetAction s k' a cont old new puts gets ret
      newStep putsStep getsStep (retStep: type k') interPuts interGets
      (aPf: SemAction a old newStep putsStep getsStep retStep)
      (contPf: SemAction (cont retStep) newStep new interPuts interGets ret)
      (interPutsEq: puts = fun i => putsStep i ++ interPuts i)
      (interGetsEq: gets = fun i => getsStep i ++ interGets i):
    SemAction (LetAction s a cont) old new puts gets ret
  | SemNonDet s k' cont old new puts gets ret v
      (contPf: SemAction (cont v) old new puts gets ret):
    SemAction (NonDet s k' cont) old new puts gets ret
  | SemIfElse s (p: Expr type Bool) k' t f cont old new puts gets ret
      newStep putsStep getsStep (retStep: type k') interPuts interGets
      (tPf: evalExpr p = true -> SemAction t old newStep putsStep getsStep retStep)
      (fPf: evalExpr p = false -> SemAction f old newStep putsStep getsStep retStep)
      (contPf: SemAction (cont retStep) newStep new interPuts interGets ret)
      (interPutsEq: puts = fun i => putsStep i ++ interPuts i)
      (interGetsEq: gets = fun i => getsStep i ++ interGets i):
    SemAction (IfElse s p t f cont) old new puts gets ret
  | SemSys ls cont old new puts gets ret
      (contPf: SemAction cont old new puts gets ret): SemAction (Sys ls cont) old new puts gets ret
  | SemReturn e old new puts gets ret
      (oldIsNew: new = old)
      (putsEmpty: puts = fun i => nil)
      (getsEmpty: gets = fun i => nil)
      (retEval: ret = evalExpr e): SemAction (Return e) old new puts gets ret.

  Section AnyAction.
    Variable ls: list (Action type regs mems regUs memUs sends recvs (Bit 0)).
    Inductive SemAnyAction: ModState regs mems regUs memUs ->
                            ModState regs mems regUs memUs ->
                            FuncIo sends ->
                            FuncIo recvs ->
                            Prop :=
    | NullStep old new puts gets
        (oldIsNew: new = old)
        (putsEmpty: puts = fun i => nil)
        (getsEmpty: gets = fun i => nil):
      SemAnyAction old new puts gets
    | Step old new puts gets
        a newStep putsStep getsStep
        (inA: In a ls)
        (aPf: SemAction a old newStep putsStep getsStep WO)
        (contPf: SemAnyAction newStep new puts gets)
        finalPuts finalGets
        (finalPutsEq: finalPuts = fun i => putsStep i ++ puts i)
        (finalGetsEq: finalGets = fun i => getsStep i ++ gets i):
      SemAnyAction old new finalPuts finalGets.
  End AnyAction.
End SemAction.

Section SemMod.
  Variable decl: ModDecl.

  Definition ModStateModDecl :=
    ModState (map (fun x => (fst x, regKind (snd x))) (modRegs decl))
      (map (fun x => (fst x, memSizeKindPort (snd x))) (modMems decl))
      (modRegUs decl)
      (modMemUs decl).

  Inductive InitModConsistent: ModStateModDecl -> Prop :=
  | InitModStateCreate
      (mems: FuncMemState (map (fun x => (fst x, memSizeKindPort (snd x))) (modMems decl)))
      (regUs: FuncState (modRegUs decl))
      (memUs: FuncMemState (modMemUs decl))
      (memsEq: forall i, fst (mems i) =
                           @convFinStruct _ _ memSizeKindPort
                             (fun x => type (Array (fst (fst x)) (snd (fst x)))) memInitFull (modMems decl) i)
      old (oldEq: old = {|stateRegs := @convFinStruct _ _ _ _ regInit (modRegs decl);
                          stateMems := mems;
                          stateRegUs := regUs;
                          stateMemUs := memUs|}): InitModConsistent old.

  Definition SemMod
               (ls: forall ty,
                   list (Action ty
                           (map (fun x => (fst x, regKind (snd x))) (modRegs decl))
                           (map (fun x => (fst x, memSizeKindPort (snd x))) (modMems decl))
                           (modRegUs decl)
                           (modMemUs decl)
                           (modSends decl)
                           (modRecvs decl)
                           (Bit 0)))
               puts gets := exists old new, InitModConsistent old /\
                                              SemAnyAction (ls type) old new puts gets.
End SemMod.

(* Given a consistent initial condition and a trace for m1, m1 implements m2 iff
   there exists some initial condition for m2 that produces the same trace as m1.
   Note that this permits that if ununitialized registers are initialized badly,
   then m2 can never produce the same trace as m1.
   This is okay because m2 does indeed exhibit the behavior of m1 because of some initialization,
   which is what m1 is trying to simulate.
   For instance, if the spec says emit any random number based on the initialization value of a register,
   an implementation that produces the same deterministic value everytime is a valid implementation *)
Record TraceInclusion m1 m2 := { traceSendsEq: modSends (modDecl m1) = modSends (modDecl m2);
                                 traceRecvsEq: modRecvs (modDecl m1) = modRecvs (modDecl m2);
                                 traceInclusion: forall puts gets,
                                   SemMod (modDecl m1) (modActions m1) puts gets ->
                                   SemMod (modDecl m2) (modActions m2)
                                     (match traceSendsEq in _ = Y return _ Y with
                                              | eq_refl => puts
                                              end)
                                     (match traceRecvsEq in _ = Y return _ Y with
                                      | eq_refl => gets
                                      end) }.

(* TODO Pretty Printer (in Coq/Haskell/OCaml?) *)
(* TODO Notations *)
(* TODO CHERIoT *)
(* TODO Simulator *)
