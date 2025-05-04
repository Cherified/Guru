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
Definition FuncAsyncState (ls: list (string * (nat * Kind))) :=
  forall i: FinStruct ls, type (Array (fst (fieldK i)) (snd (fieldK i))).
Definition FuncSyncState (ls: list (string * (nat * Kind))) :=
  forall i: FinStruct ls,
    (type (Array (fst (fieldK i)) (snd (fieldK i))) * word (Nat.log2_up (fst (fieldK i)))).
Definition FuncIo (ls: list (string * Kind)) := forall i: FinStruct ls, list (type (fieldK i)).

Record ModState (regs: list (string * Kind)) (asyncMems syncMems: list (string * (nat * Kind))) :=
  { stateRegs : FuncState regs;
    stateAsyncMems : FuncAsyncState asyncMems;
    stateSyncMems : FuncSyncState syncMems }.

Section SemAction.
  Variable regs: list (string * Kind).
  Variable asyncMems: list (string * (nat * Kind)).
  Variable syncMems: list (string * (nat * Kind)).
  Variable sends: list (string * Kind).
  Variable recvs: list (string * Kind).

  Inductive SemAction k: Action type regs asyncMems syncMems sends recvs k ->
                         ModState regs asyncMems syncMems ->
                         ModState regs asyncMems syncMems ->
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
                                stateAsyncMems := stateAsyncMems old;
                                stateSyncMems := stateSyncMems old |} new puts gets ret):
    SemAction (WriteReg x v cont) old new puts gets ret
  | SemReadAsyncMem x (i: Expr type (Bit (Nat.log2_up (fst (fieldK x))))) cont old new puts gets ret
      (contPf: SemAction (cont (readArray (Default _) (arrayToFunc (stateAsyncMems old x)) (evalExpr i)))
                 old new puts gets ret):
      SemAction (ReadAsyncMem x i cont) old new puts gets ret
  | SemWriteAsyncMem x (i: Expr type (Bit (Nat.log2_up (fst (fieldK x))))) v cont old new puts gets ret
      (contPf: SemAction
                 cont
                 {|stateRegs := stateRegs old;
                   stateAsyncMems :=
                     fun j =>
                       match FinStruct_dec x j with
                       | left pf =>
                           match pf in _ = Y
                                 return type (Array (fst (fieldK Y)) (snd (fieldK Y))) with
                           | eq_refl => funcToArray (writeArray (evalExpr v)
                                                       (arrayToFunc (stateAsyncMems old x)) (evalExpr i))
                           end
                       | right _ => stateAsyncMems old j
                       end;
                   stateSyncMems := stateSyncMems old
                   |} new puts gets ret):
    SemAction (WriteAsyncMem x i v cont) old new puts gets ret
  | SemReadRqSyncMem x (i: Expr type (Bit (Nat.log2_up (fst (fieldK x))))) cont old new puts gets ret
      (contPf: SemAction
                 cont
                 {|stateRegs := stateRegs old;
                   stateAsyncMems := stateAsyncMems old;
                   stateSyncMems :=
                     fun j =>
                       match FinStruct_dec x j with
                       | left pf =>
                             match pf in _ = Y
                                   return
                                   (type (Array (fst (fieldK Y)) (snd (fieldK Y))) *
                                      word (Nat.log2_up (fst (fieldK Y)))) with
                             | eq_refl => (fst (stateSyncMems old x), evalExpr i)
                             end
                       | right _ => stateSyncMems old j
                       end |} new puts gets ret):
    SemAction (ReadRqSyncMem x i cont) old new puts gets ret
  | SemReadRpSyncMem x cont old new puts gets ret
      (contPf: SemAction (cont (readArray (Default _)
                                  (arrayToFunc (fst (stateSyncMems old x)))
                                  (snd (stateSyncMems old x))))
                            old new puts gets ret):
    SemAction (ReadRpSyncMem x cont) old new puts gets ret
  | SemWriteSyncMem x (i: Expr type (Bit (Nat.log2_up (fst (fieldK x))))) v cont old new puts gets ret
      (contPf: SemAction
                 cont
                 {|stateRegs := stateRegs old;
                   stateAsyncMems := stateAsyncMems old;
                   stateSyncMems :=
                     fun j =>
                       match FinStruct_dec x j with
                       | left pf =>
                             match pf in _ = Y
                                   return
                                   (type (Array (fst (fieldK Y)) (snd (fieldK Y))) *
                                      word (Nat.log2_up (fst (fieldK Y)))) with
                             | eq_refl => (funcToArray (writeArray (evalExpr v)
                                                          (arrayToFunc (fst (stateSyncMems old x))) (evalExpr i)),
                                            snd (stateSyncMems old x))
                             end
                       | right _ => stateSyncMems old j
                       end |} new puts gets ret):
    SemAction (WriteSyncMem x i v cont) old new puts gets ret
  | SemSend x v cont old new puts gets ret
      puts1
      (contPf: SemAction cont old new puts1 gets ret)
      (putsVal: puts = fun i => match FinStruct_dec x i with
                                | left pf => match pf in _ = Y return list (type (fieldK Y)) with
                                             | eq_refl => evalExpr v :: puts1 x
                                             end
                                | right _ => puts1 i
                                end):
      SemAction (Send x v cont) old new puts gets ret
  | SemRecv x cont old new puts gets ret
      recv1 gets1
      (contPf: SemAction (cont recv1) old new puts gets1 ret)
      (putsVal: gets = fun i => match FinStruct_dec x i with
                                | left pf => match pf in _ = Y return list (type (fieldK Y)) with
                                             | eq_refl => recv1 :: gets1 x
                                             end
                                | right _ => gets1 i
                                end):
      SemAction (Recv x cont) old new puts gets ret
  | SemLetExpr s k' (e: Expr type k') cont old new puts gets ret
      (contPf: SemAction (cont (evalExpr e)) old new puts gets ret):
    SemAction (LetExpr s e cont) old new puts gets ret
  | SemLetAction s k' a cont old new puts gets ret
      new1 puts1 gets1 (ret1: type k')
      (aPf: SemAction a old new1 puts1 gets1 ret1)
      (contPf: SemAction (cont ret1) new1 new (fun i => puts1 i ++ puts i) (fun i => gets1 i ++ gets i) ret):
    SemAction (LetAction s a cont) old new puts gets ret
  | SemNonDet s k' cont old new puts gets ret v
      (contPf: SemAction (cont v) old new puts gets ret):
    SemAction (NonDet s k' cont) old new puts gets ret
  | SemIfElse s (p: Expr type Bool) k' t f cont old new puts gets ret
      new1 puts1 gets1 (ret1: type k')
      (tPf: evalExpr p = true -> SemAction t old new1 puts1 gets1 ret1)
      (fPf: evalExpr p = false -> SemAction f old new1 puts1 gets1 ret1)
      (contPf: SemAction (cont ret1) new1 new (fun i => puts1 i ++ puts i) (fun i => gets1 i ++ gets i) ret):
    SemAction (IfElse s p t f cont) old new puts gets ret
  | SemSys ls cont old new puts gets ret
      (contPf: SemAction cont old new puts gets ret): SemAction (Sys ls cont) old new puts gets ret
  | SemReturn e old new puts gets ret
      (oldIsNew: new = old)
      (putsEmpty: puts = fun i => nil)
      (getsEmpty: gets = fun i => nil)
      (retEval: ret = evalExpr e): SemAction (Return e) old new puts gets ret.

  Section NonDetActions.
    Variable ls: list (Action type regs asyncMems syncMems sends recvs (Bit 0)).
    Inductive SemNonDetActions: ModState regs asyncMems syncMems ->
                                ModState regs asyncMems syncMems ->
                                FuncIo sends ->
                                FuncIo recvs ->
                                Prop :=
    | NullStep old new puts gets
        (oldIsNew: new = old)
        (putsEmpty: puts = fun i => nil)
        (getsEmpty: gets = fun i => nil):
      SemNonDetActions old new puts gets
    | Step old new puts gets
        a new1 puts1 gets1
        (inA: In a ls)
        (aPf: SemAction a old new1 puts1 gets1 WO)
        (contPf: SemNonDetActions new1 new (fun i => puts1 i ++ puts i) (fun i => gets1 i ++ gets i)):
      SemNonDetActions old new puts gets.
  End NonDetActions.
End SemAction.

Section SemMod.
  Variable m: Mod type.

  Inductive SemMod: FuncIo (modSends m) -> FuncIo (modRecvs m) -> Prop :=
  | Trace new puts gets
      regUs (regUsEq: map (fun x => (fst x, regKind (snd x))) regUs = modRegUs m)
      asyncUs (asyncUsEq: map (fun x => (fst x, memNatKind (snd x))) asyncUs = map (fun x => (fst x, memUNatKind (snd x))) (modAsyncUs m))
      syncUs (syncUsEq: map (fun x => (fst x, memNatKind (snd x))) syncUs = map (fun x => (fst x, memUNatKind (snd x))) (modSyncUs m))
      (tracePf:
        SemNonDetActions
          (modActions m)
          match regUsEq in _ = RegUs return ModState (_ RegUs) _ _
          with
          | eq_refl =>
              match map_app _ (modRegs m) regUs in _ = RegUsApp return ModState RegUsApp _ _
              with
              | eq_refl =>
                  match asyncUsEq in _ = AsyncUs return ModState _ (_ AsyncUs) _
                  with
                  | eq_refl =>
                      match map_app _ (modAsyncs m) asyncUs in _ = AsyncUsApp return ModState _ AsyncUsApp _
                      with
                      | eq_refl =>
                          {|stateRegs := @convFinStruct _ _ _ _ regInit (modRegs m ++ regUs) ;
                            stateAsyncMems := @convFinStruct _ _ (fun a => (memSize a, memKind a))
                                                (fun x => type (Array (fst x) (snd x))) memInitFull (modAsyncs m ++ asyncUs);
                            stateSyncMems := (fun i => (Default _, wzero _)) |}
                      end
                  end
              end
          end new puts gets):
    SemMod puts gets.
End SemMod.

(* Definition of trace equivalence *)
(* Proof of simulation relation single step *)
(* Proof of combining actions leads to simulation relation held *)

(* Pretty printer/compiler. Should be really simple this time around! *)
(* MAYBE Restrict to one write port for synthesis *)
