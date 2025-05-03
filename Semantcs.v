Require Import String List Psatz.
Require Import Guru.Lib.Library Guru.Lib.Word.
Require Import Guru.Syntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

Fixpoint evalExpr k (e: Expr type k): type k :=
  match e in Expr _ k return type k with
  | Var _ v => v
  | Const _ v => v
  | Or _ ls => fold_left (evalOrBinary _) (map (@evalExpr _) ls) (getDefault _)
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
  | Eq _ a b => if isEq _ (evalExpr a) (evalExpr b) then true else false
  | ReadStruct _ v i => (structToFunc _ _ (evalExpr v)) i
  | ReadArray n _ k v i =>
      match lt_dec (Z.to_nat (wordVal _ (evalExpr i))) n return type k with
      | left pf => arrayToFunc type _ _ (evalExpr v) (FinArray_of_nat_lt pf)
      | right _ => getDefault k
      end
  | ReadArrayConst _ _ v i => (arrayToFunc _ _ _ (evalExpr v)) i
  | BuildStruct _ vs => funcToStruct _ _ (fun i => evalExpr (vs i))
  | BuildArray _ _ vs => funcToArray _ _ _ (fun i => evalExpr (vs i))
  | ToBit _ v => evalToBit _ (evalExpr v)
  | FromBit _ v => evalFromBit _ (evalExpr v)
  end.

Definition FuncState (ls: list (string * Kind)) := forall i: FinStruct ls, type (fieldK _ i).
Definition FuncIo (ls: list (string * Kind)) := forall i: FinStruct ls, list (type (fieldK _ i)).

Record ModState (regs asyncMems syncMems: list (string * Kind)) :=
  { stateRegs : FuncState regs;
    stateAsyncMems : FuncState asyncMems;
    stateSyncMems : FuncState syncMems }.

Section SemAction.
  Variable regs: list (string * Kind).
  Variable asyncMems: list (string * Kind).
  Variable syncMems: list (string * Kind).
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
  | SemWriteReg x (v: Expr type (fieldK _ x)) cont old new puts gets ret
      (contPf: SemAction cont {| stateRegs := fun i => match FinStruct_dec _ x i with
                                                       | left pf => match pf in _ = Y return type (fieldK _ Y) with
                                                                    | eq_refl => evalExpr v
                                                                    end
                                                       | right _ => stateRegs old i
                                                       end;
                                stateAsyncMems := stateAsyncMems old;
                                stateSyncMems := stateSyncMems old |} new puts gets ret):
    SemAction (WriteReg x v cont) old new puts gets ret
      (*
  | SemReadRpSyncMem x cont old new puts gets ret
      (contPf: SemAction (cont (structToFunc _ _ (stateSyncMems old x) (inr (inl tt)))) old new puts gets ret):
    SemAction (ReadRpSyncMem x cont) old new puts gets ret
       *)
  | SemWriteSyncMem x i v cont old new puts gets ret
      (contPf: SemAction cont {| stateRegs := stateRegs old;
                                stateAsyncMems := stateAsyncMems old;
                                stateSyncMems := fun j => match FinStruct_dec _ x j with
                                                          | left pf => match pf in _ = Y return type (fieldK syncMems Y) with
                                                                       | eq_refl => cheat _
                                                                       end
                                                          | right _ => stateSyncMems old j
                                                          end |} new puts gets ret):
    SemAction (WriteSyncMem x i v cont) old new puts gets ret
  | SemSend x v cont old new puts gets ret
      puts1
      (contPf: SemAction cont old new puts1 gets ret)
      (putsVal: puts = fun i => match FinStruct_dec _ x i with
                                | left pf => match pf in _ = Y return list (type (fieldK _ Y)) with
                                             | eq_refl => evalExpr v :: puts1 x
                                             end
                                | right _ => puts1 i
                                end):
      SemAction (Send x v cont) old new puts gets ret
  | SemRecv x cont old new puts gets ret
      recv1 gets1
      (contPf: SemAction (cont recv1) old new puts gets1 ret)
      (putsVal: gets = fun i => match FinStruct_dec _ x i with
                                | left pf => match pf in _ = Y return list (type (fieldK _ Y)) with
                                             | eq_refl => recv1 :: gets1 x
                                             end
                                | right _ => gets1 i
                                end):
      SemAction (Recv x cont) old new puts gets ret
  | SemLetExpr k' (e: Expr type k') cont old new puts gets ret
      (contPf: SemAction (cont (evalExpr e)) old new puts gets ret):
    SemAction (LetExpr e cont) old new puts gets ret
  | SemLetAction k' a cont old new puts gets ret
      new1 puts1 gets1 (ret1: type k')
      (aPf: SemAction a old new1 puts1 gets1 ret1)
      (contPf: SemAction (cont ret1) new1 new (fun i => puts1 i ++ puts i) (fun i => gets1 i ++ gets i) ret):
    SemAction (LetAction a cont) old new puts gets ret
  | SemNonDet k' cont old new puts gets ret v
      (contPf: SemAction (cont v) old new puts gets ret):
    SemAction (NonDet k' cont) old new puts gets ret
  | SemIfElse (p: Expr type Bool) k' t f cont old new puts gets ret
      new1 puts1 gets1 (ret1: type k')
      (tPf: evalExpr p = true -> SemAction t old new1 puts1 gets1 ret1)
      (fPf: evalExpr p = false -> SemAction f old new1 puts1 gets1 ret1)
      (contPf: SemAction (cont ret1) new1 new (fun i => puts1 i ++ puts i) (fun i => gets1 i ++ gets i) ret):
    SemAction (IfElse p t f cont) old new puts gets ret
  | SemSys ls cont old new puts gets ret
      (contPf: SemAction cont old new puts gets ret): SemAction (Sys ls cont) old new puts gets ret
  | SemReturn e old new puts gets ret
      (oldIsNew: new = old)
      (putsEmpty: puts = fun i => nil)
      (getsEmpty: gets = fun i => nil)
      (retEval: ret = evalExpr e): SemAction (Return _ _ _ _ _ e) old new puts gets ret.
  (*
  Inductive Action (k: Kind) : Type :=
  | ReadAsyncMem (x: FinStruct asyncMems) (i: Expr (MemArrayIdx (fieldK _ x)))
      (cont: ty (MemKind (fieldK _ x)) -> Action k)
  | WriteAsyncMem (x: FinStruct asyncMems) (i: Expr (MemArrayIdx (fieldK _ x)))
      (v: Expr (MemKind (fieldK _ x))) (cont: Action k)
  | ReadRqSyncMem (x: FinStruct syncMems) (i: Expr (MemArrayIdx (fieldK _ x))) (cont: Action k)
  | ReadRpSyncMem (x: FinStruct syncMems) (cont: ty (MemKind (fieldK _ x)) -> Action k)
  | WriteSyncMem (x: FinStruct syncMems) (i: Expr (MemArrayIdx (fieldK _ x)))
      (v: Expr (MemKind (fieldK _ x))) (cont: ty (MemKind (fieldK _ x)) -> Action k)
*)
End SemAction.

(* Write updates of RegFiles *)
(* Definition of trace equivalence *)
(* Proof of simulation relation single step *)
(* Proof of combining actions leads to simulation relation held *)

(* Pretty printer/compiler. Should be really simple this time around! *)
(* Restrict to one write port for synthesis *)
