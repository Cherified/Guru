From Stdlib Require Import String List Psatz Zmod Bool.
Require Import Guru.Library Guru.Syntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

#[bypass_check(guard)]
Fixpoint evalExpr k (e: Expr type k) {struct e}: type k :=
  match e in Expr _ k return type k with
  | Var _ v => v
  | Const _ v => v
  | Or _ ls => fold_left (@evalOrBinary _) (map (@evalExpr _) ls) (Default _)
  | And _ ls => fold_left (@evalAndBinary _) (map (@evalExpr _) ls) (InvDefault _)
  | Xor _ ls => fold_left (@evalXorBinary _) (map (@evalExpr _) ls) (Default _)
  | Not k v => evalNot (@evalExpr _ v)
  | TruncLsb _ _ v => Zmod_lastn _ (@evalExpr _ v)
  | TruncMsb _ _ v => Zmod.firstn _ (@evalExpr _ v)
  | UXor n v => Z_uxor (Zmod.to_Z (@evalExpr _ v))
  | Add n ls => fold_left Zmod.add (map (@evalExpr (Bit n)) ls) Zmod.zero
  | Mul n ls => fold_left Zmod.mul (map (@evalExpr (Bit n)) ls) Zmod.one
  | Div n a b => Zmod.udiv (@evalExpr _ a) (@evalExpr _ b)
  | Rem n a b => Zmod.umod (@evalExpr _ a) (@evalExpr _ b)
  | Sll _ _ a b => Zmod.slu (@evalExpr _ a) (Zmod.to_Z (@evalExpr _ b))
  | Srl _ _ a b => Zmod.sru (@evalExpr _ a) (Zmod.to_Z (@evalExpr _ b))
  | Sra _ _ a b => Zmod.srs (@evalExpr _ a) (Zmod.to_Z (@evalExpr _ b))
  | Concat _ _ a b => Zmod.app (@evalExpr _ b) (@evalExpr _ a)
  | ITE _ p t f => if @evalExpr _ p then @evalExpr _ t else @evalExpr _ f
  | Eq _ a b => isEq (@evalExpr _ a) (@evalExpr _ b)
  | ReadStruct _ v i => readDiffTuple (Convert := fun x => type (snd x)) (@evalExpr _ v) i
  | ReadArray n _ k v i =>
      readNatToFinType (Default _) (readSameTuple (@evalExpr _ v)) (Z.to_nat (Zmod.to_Z (@evalExpr _ i)))
  | ReadArrayConst _ _ v i => readSameTuple (@evalExpr _ v) i
  | UpdateStruct ls vs p v => updDiffTuple (Convert := fun x => type (snd x)) (@evalExpr _ vs) (@evalExpr _ v)
  | UpdateArrayConst n k vs p v => updSameTuple (@evalExpr _ vs) p (@evalExpr _ v)
  | UpdateArray n k vs m i v =>
      updSameTupleNat (@evalExpr _ vs) (Z.to_nat (Zmod.to_Z (@evalExpr _ i))) (@evalExpr _ v)
  | ToBit _ v => evalToBit (@evalExpr _ v)
  | FromBit _ v => evalFromBit (@evalExpr _ v)
  (* The following 2 don't pass the guardedness checks in Rocq *)
  | BuildStruct ls vs => mapDiffTuple (fun x => @evalExpr (snd x)) vs
  | BuildArray n k vs => mapSameTuple (@evalExpr k) vs
  end.

Fixpoint evalLetExpr k (le: LetExpr type k): type k :=
  match le with
  | RetE e => evalExpr e
  | SystemE ls cont => evalLetExpr cont
  | LetEx s k' le cont => let t := evalLetExpr le in evalLetExpr (cont t)
  | IfElseE s p k' t f cont => evalLetExpr (cont (if evalExpr p
                                                  then evalLetExpr t
                                                  else evalLetExpr f))
  end.




Definition memoryInitFull (m: Memory) : type (Array m.(memorySize) m.(memoryKind)) :=
  match m.(memoryInit) with
  | None => Default _
  | Some None => Default _
  | Some (Some init) => init
  end.

Definition InitStateElem (e: ModElem) : ModElemState e :=
  match e return ModElemState e with
  | ERegister r => match r.(registerInit) with
                    | None => Default _
                    | Some init => init
                    end
  | EMemory m => (memoryInitFull m ,, Default (Array m.(memoryPort) m.(memoryKind)))
  | ESend _ => nil
  | ERecv _ => nil
  end.

Fixpoint InitState (t: Tree ModElem) : TreeState ModElemState t :=
  match t return TreeState ModElemState t with
  | Leaf _ e => InitStateElem e
  | Node _ children =>
      (fix loop (ls: list (Tree ModElem)) : ModListTreeState ls :=
         match ls return ModListTreeState ls with
         | nil => tt
         | x :: xs => (InitState x ,, loop xs)
         end) children
  end.
Definition InitStateElemConsistent (e: ModElem) : ModElemState e -> Prop :=
  match e return ModElemState e -> Prop with
  | ERegister r => match r.(registerInit) with
                    | None => fun s => True
                    | Some init => fun s => s = init
                    end
  | EMemory m => match m.(memoryInit) with
                  | None => fun s => True
                  | Some _ => fun s => s.(Fst) = memoryInitFull m
                  end
  | ESend _ => fun s => s = nil
  | ERecv _ => fun s => s = nil
  end.

Fixpoint InitStateConsistent (t: Tree ModElem) : TreeState ModElemState t -> Prop :=
  match t return TreeState ModElemState t -> Prop with
  | Leaf _ e => InitStateElemConsistent e
  | Node _ children =>
      (fix loop (ls: list (Tree ModElem)) : ModListTreeState ls -> Prop :=
         match ls return ModListTreeState ls -> Prop with
         | nil => fun _ => True
         | x :: xs => fun s => InitStateConsistent x s.(Fst) /\ loop xs s.(Snd)
         end) children
  end.

Section SemActionTree.
  Variable t: Tree ModElem.

  Inductive SemActionTree k: @ActionTree type t k ->
                             TreeState ModElemState t ->
                             TreeState ModElemState t ->
                             type k -> Prop :=
  | SemReadRegTree s x cont old new ret
      (contPf: SemActionTree (cont (castStateReg x (readTreeState t old x.(regPath)))) old new ret):
    SemActionTree (ReadRegTree s x cont) old new ret
  | SemWriteRegTree x (v: Expr type (registerKind (getRegFromPath x))) cont old new ret
      (contPf: SemActionTree cont (writeTreeState t old x.(regPath) (castStateRegInv x (evalExpr v))) new ret):
    SemActionTree (WriteRegTree x v cont) old new ret
  | SemReadRqMemTree x (i: Expr type (Bit (Z.log2_up (Z.of_nat (getMemFromPath x).(memorySize))))) p cont old new ret
      (contPf:
        SemActionTree
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (Default _) in
           writeTreeState t old x.(memPath) (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) p val)))
          new ret):
    SemActionTree (ReadRqMemTree x i p cont) old new ret
  | SemReadRpMemTree s x p cont old new ret
      (contPf: SemActionTree (cont (readSameTuple (castStateMem x (readTreeState t old x.(memPath))).(Snd) p)) old new ret):
    SemActionTree (ReadRpMemTree s x p cont) old new ret
  | SemWriteMemTree x (i: Expr type (Bit (Z.log2_up (Z.of_nat (getMemFromPath x).(memorySize))))) (v: Expr type (getMemFromPath x).(memoryKind)) cont old new ret
      (contPf:
        SemActionTree
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           writeTreeState t old x.(memPath) (castStateMemInv x (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd))))
          new ret):
    SemActionTree (WriteMemTree x i v cont) old new ret
  | SemSendTree x v cont old new ret
      (contPf: SemActionTree cont
                 (let currentTrace := castStateSend x (readTreeState t old x.(sendPath)) in
                  writeTreeState t old x.(sendPath) (castStateSendInv x (evalExpr v :: currentTrace)))
                 new ret):
    SemActionTree (SendTree x v cont) old new ret
  | SemRecvTree s x cont old new ret
      recvVal
      (contPf: SemActionTree (cont recvVal)
                 (let currentTrace := castStateRecv x (readTreeState t old x.(recvPath)) in
                  writeTreeState t old x.(recvPath) (castStateRecvInv x (recvVal :: currentTrace)))
                 new ret):
    SemActionTree (RecvTree s x cont) old new ret
  | SemLetExpTree s k' (e: Expr type k') cont old new ret
      (contPf: SemActionTree (cont (evalExpr e)) old new ret):
    SemActionTree (LetExpTree s e cont) old new ret
  | SemLetActionTree s k' a cont old new ret
      newStep (retStep: type k')
      (aPf: SemActionTree a old newStep retStep)
      (contPf: SemActionTree (cont retStep) newStep new ret):
    SemActionTree (LetActionTree s a cont) old new ret
  | SemNonDetTree s k' cont old new ret v
      (contPf: SemActionTree (cont v) old new ret):
    SemActionTree (NonDetTree s k' cont) old new ret
  | SemIfElseTree s (p: Expr type Bool) k' t_branch f_branch cont old new ret
      newStep (retStep: type k')
      (tPf: evalExpr p = true -> SemActionTree t_branch old newStep retStep)
      (fPf: evalExpr p = false -> SemActionTree f_branch old newStep retStep)
      (contPf: SemActionTree (cont retStep) newStep new ret):
    SemActionTree (IfElseTree s p t_branch f_branch cont) old new ret
  | SemSystemTree ls cont old new ret
      (contPf: SemActionTree cont old new ret): SemActionTree (SystemTree ls cont) old new ret
  | SemReturnTree e old new ret
      (oldIsNew: new = old)
      (retEval: ret = evalExpr e): SemActionTree (ReturnTree e) old new ret.

  Section StepTree.
    Variable ls: list (@ActionTree type t (Bit 0)).

    Inductive StepTree: TreeState ModElemState t ->
                        TreeState ModElemState t ->
                        Prop :=
    | SingleStepTree (old newStep: TreeState ModElemState t)
          a (inA: In a ls) (aPf: SemActionTree a old newStep Zmod.zero):
      StepTree old newStep.

    Inductive SemAnyActionTree: TreeState ModElemState t -> TreeState ModElemState t -> Prop :=
    | NilStepTree (old new: TreeState ModElemState t) (eqPf: new = old) : SemAnyActionTree old new
    | ConsStepTree (old new newStep: TreeState ModElemState t)
        (step: StepTree old newStep)
        (rest: SemAnyActionTree newStep new) : SemAnyActionTree old new.
  End StepTree.
End SemActionTree.

Section SemModTree.
  Variable t: Tree ModElem.

  Section SemModTreeDefn.
    Variable m: ModTree t.

    Inductive SemModTree : TreeState ModElemState t -> TreeState ModElemState t -> Prop :=
    | SemModTreeProp (old new : TreeState ModElemState t)
        (initGood: InitStateConsistent t old)
        (steps: SemAnyActionTree (m type) old new) : SemModTree old new.
  End SemModTreeDefn.
End SemModTree.

Definition TraceInclusionTree {t1 t2: Tree ModElem} (m1: ModTree t1) (m2: ModTree t2)
  (rel: TreeState ModElemState t1 -> TreeState ModElemState t2 -> Prop) : Prop :=
  forall old1 new1,
    SemModTree m1 old1 new1 ->
    forall old2,
      rel old1 old2 ->
      exists new2,
        SemModTree m2 old2 new2 /\
        rel new1 new2.

