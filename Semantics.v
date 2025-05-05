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
Definition FuncMemState (ls: list (string * (nat * Kind))) :=
  forall i: FinStruct ls, type (Array (fst (fieldK i)) (snd (fieldK i))).
Definition FuncIo (ls: list (string * Kind)) := forall i: FinStruct ls, list (type (fieldK i)).

Record ModState (regs: list (string * Kind)) (mems: list (string * (nat * Kind))) :=
  { stateRegs : FuncState regs;
    stateMems : FuncMemState mems }.

Section SemAction.
  Variable regs: list (string * Kind).
  Variable mems: list (string * (nat * Kind)).
  Variable sends: list (string * Kind).
  Variable recvs: list (string * Kind).

  Inductive SemAction k: Action type regs mems sends recvs k ->
                         ModState regs mems ->
                         ModState regs mems ->
                         FuncIo sends ->
                         FuncIo recvs ->
                         type k -> Prop :=
  | SemReadReg x cont old new puts gets ret
      (contPf: SemAction (cont (stateRegs old x)) old new puts gets ret):
    SemAction (ReadReg x cont) old new puts gets ret
  | SemWriteReg x (v: Expr type (fieldK x)) cont old new puts gets ret
      (contPf: SemAction cont {|stateRegs := fun i => match FinStruct_dec x i with
                                                      | left pf => match pf in _ = Y return type (fieldK Y) with
                                                                   | eq_refl => evalExpr v
                                                                   end
                                                      | right _ => stateRegs old i
                                                      end;
                                stateMems := stateMems old |} new puts gets ret):
    SemAction (WriteReg x v cont) old new puts gets ret
  | SemReadMem x (i: Expr type (Bit (Nat.log2_up (fst (fieldK x))))) cont old new puts gets ret
      (contPf: SemAction (cont (readArray (Default _) (arrayToFunc (stateMems old x)) (evalExpr i)))
                 old new puts gets ret):
      SemAction (ReadMem x i cont) old new puts gets ret
  | SemWriteMem x (i: Expr type (Bit (Nat.log2_up (fst (fieldK x))))) v cont old new puts gets ret
      (contPf: SemAction
                 cont
                 {|stateRegs := stateRegs old;
                   stateMems :=
                     fun j =>
                       match FinStruct_dec x j with
                       | left pf =>
                           match pf in _ = Y
                                 return type (Array (fst (fieldK Y)) (snd (fieldK Y))) with
                           | eq_refl => funcToArray (writeArray (evalExpr v)
                                                       (arrayToFunc (stateMems old x)) (evalExpr i))
                           end
                       | right _ => stateMems old j
                       end |} new puts gets ret):
    SemAction (WriteMem x i v cont) old new puts gets ret
  | SemSend x v cont old new puts gets ret
      putsStep
      (contPf: SemAction cont old new putsStep gets ret)
      (putsVal: puts = fun i => match FinStruct_dec x i with
                                | left pf => match pf in _ = Y return list (type (fieldK Y)) with
                                             | eq_refl => evalExpr v :: putsStep x
                                             end
                                | right _ => putsStep i
                                end):
      SemAction (Send x v cont) old new puts gets ret
  | SemRecv x cont old new puts gets ret
      recvStep getsStep
      (contPf: SemAction (cont recvStep) old new puts getsStep ret)
      (putsVal: gets = fun i => match FinStruct_dec x i with
                                | left pf => match pf in _ = Y return list (type (fieldK Y)) with
                                             | eq_refl => recvStep :: getsStep x
                                             end
                                | right _ => getsStep i
                                end):
      SemAction (Recv x cont) old new puts gets ret
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
    Variable ls: list (Action type regs mems sends recvs (Bit 0)).
    Inductive SemAnyAction: ModState regs mems ->
                            ModState regs mems ->
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
  Variable m: Mod.

  Definition ModStateMod :=
    ModState (map (fun x => (fst x, regKind (snd x))) (modRegs (modDecls m)) ++ modRegUs (modDecls m))
      (map (fun x => (fst x, memNatKind (snd x))) (modMems (modDecls m)) ++
         map (fun x => (fst x, memUNatKind (snd x))) (modMemUs (modDecls m))).

  Inductive InitModConsistent: ModStateMod -> Prop :=
  | InitModStateCreate
      regUs (regUsEq: map (fun x => (fst x, regKind (snd x))) regUs = modRegUs (modDecls m))
      memUs (memUsEq: map (fun x => (fst x, memNatKind (snd x))) memUs =
                        map (fun x => (fst x, memUNatKind (snd x))) (modMemUs (modDecls m)))
      old (oldEq: old = match regUsEq in _ = RegUs return ModState (_ RegUs) _ with
                        | eq_refl =>
                            match map_app _ (modRegs (modDecls m)) regUs in _ = RegUsApp
                                  return ModState RegUsApp _ with
                            | eq_refl =>
                                match memUsEq in _ = MemUs return ModState _ (_ MemUs) with
                                | eq_refl =>
                                    match map_app _ (modMems (modDecls m)) memUs in _ = MemUsApp
                                          return ModState _ MemUsApp with
                                    | eq_refl =>
                                        {|stateRegs := @convFinStruct _ _ _ _ regInit
                                                         (modRegs (modDecls m) ++ regUs) ;
                                          stateMems := @convFinStruct _ _ (fun a => (memSize a, memKind a))
                                                         (fun x => type (Array (fst x) (snd x))) memInitFull
                                                         (modMems (modDecls m) ++ memUs) |}
                                    end
                                end
                            end
                        end): InitModConsistent old.
End SemMod.

Record TraceInclusion m1 m2 := { traceSendsEq: modSends (modDecls m1) = modSends (modDecls m2);
                                 traceRecvsEq: modRecvs (modDecls m1) = modRecvs (modDecls m2);
                                 traceInclusion: forall old1 new1 puts gets,
                                   InitModConsistent old1 ->
                                   SemAnyAction (modActions m1 type) old1 new1 puts gets ->
                                   forall old2,
                                     InitModConsistent old2 ->
                                     exists new2,
                                       SemAnyAction (modActions m2 type) old2 new2
                                         (match traceSendsEq in _ = Y return _ Y with
                                          | eq_refl => puts
                                          end)
                                         (match traceRecvsEq in _ = Y return _ Y with
                                          | eq_refl => gets
                                          end) }.

(* Proof of combining actions leads to simulation relation held *)
(* Must switch to asynchronous memory *)

(* Pretty printer/compiler. Should be really simple this time around! *)
(* Simulator *)
