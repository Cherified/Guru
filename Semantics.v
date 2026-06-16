From Stdlib Require Import String List Psatz Zmod Bool.
Require Import Guru.Library Guru.Syntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

#[bypass_check(guard)]
Fixpoint evalExpr k (e: Expr type k) {struct e}: type k :=
  match e in Expr _ k return type k with
  | Var _ v => v
  | Const _ v => v
  | Or _ ls => fold_left (@evalOrBinary _) (map (@evalExpr _) ls) (getDefault _)
  | And _ ls => fold_left (@evalAndBinary _) (map (@evalExpr _) ls) (InvDefault _)
  | Xor _ ls => fold_left (@evalXorBinary _) (map (@evalExpr _) ls) (getDefault _)
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
      readNatToFinType (getDefault _) (readSameTuple (@evalExpr _ v)) (Z.to_nat (Zmod.to_Z (@evalExpr _ i)))
  | ReadArrayConst _ _ v i => readSameTuple (@evalExpr _ v) i
  | UpdateStruct ls vs p v => updDiffTuple (Convert := fun x => type (snd x)) (@evalExpr _ vs) (@evalExpr _ v)
  | UpdateArrayConst n k vs p v => updSameTuple (@evalExpr _ vs) p (@evalExpr _ v)
  | UpdateArray n k vs m i v =>
      updSameTupleNat (@evalExpr _ vs) (Z.to_nat (Zmod.to_Z (@evalExpr _ i))) (@evalExpr _ v)
  | ToBit _ v => evalToBit (@evalExpr _ v)
  | FromBit _ v => evalFromBit (@evalExpr _ v)
  | ReadUnionTag _ e i => Zmod.eqb (evalExpr e).(Snd) (Zmod.of_Z _ (Z.of_nat i.(finNum)))
  | ReadUnionData _ e i => evalFromBit (Zmod.of_Z _ (Zmod.to_Z (evalExpr e).(Fst)))
  | BuildUnion _ i e => (Zmod.of_Z _ (Zmod.to_Z (evalToBit (evalExpr e))) ,, Zmod.of_Z _ (Z.of_nat i.(finNum)))
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

Definition memInitFull (m: Mem) : type (Array m.(memSize) m.(memKind)) :=
  match m.(memInit) with
  | None => getDefault _
  | Some None => getDefault _
  | Some (Some init) => init
  end.

Definition InitStateElem (e: Elem) : ElemState e :=
  match e return ElemState e with
  | EReg r => match r.(regInit) with
                    | None => getDefault _
                    | Some init => init
                    end
  | EMem m => (memInitFull m ,, getDefault (Array m.(memPort) m.(memKind)))
  | ESend _ => nil
  | ERecv _ => nil
  end.

Fixpoint InitState (t: Tree Elem) : TreeState ElemState t :=
  match t return TreeState ElemState t with
  | Leaf _ e => InitStateElem e
  | Node _ children =>
      (fix loop (ls: list (Tree Elem)) : ListTreeState ElemState ls :=
         match ls return ListTreeState ElemState ls with
         | nil => tt
         | x :: xs => (InitState x ,, loop xs)
         end) children
  end.
Definition InitStateElemConsistent (e: Elem) : ElemState e -> Prop :=
  match e return ElemState e -> Prop with
  | EReg r => match r.(regInit) with
                    | None => fun s => True
                    | Some init => fun s => s = init
                    end
  | EMem m => match m.(memInit) with
                  | None => fun s => True
                  | Some _ => fun s => s.(Fst) = memInitFull m
                  end
  | ESend _ => fun s => s = nil
  | ERecv _ => fun s => s = nil
  end.

Fixpoint InitStateConsistent (t: Tree Elem) : TreeState ElemState t -> Prop :=
  match t return TreeState ElemState t -> Prop with
  | Leaf _ e => InitStateElemConsistent e
  | Node _ children =>
      (fix loop (ls: list (Tree Elem)) : ListTreeState ElemState ls -> Prop :=
         match ls return ListTreeState ElemState ls -> Prop with
         | nil => fun _ => True
         | x :: xs => fun s => InitStateConsistent x s.(Fst) /\ loop xs s.(Snd)
         end) children
  end.

Section SemAction.
  Variable t: Tree Elem.

  Inductive SemAction k: @Action type t k ->
                         TreeState ElemState t ->
                         TreeState ElemState t ->
                         type k -> Prop :=
  | SemReadReg s x cont old new ret
      (contPf: SemAction (cont (castStateReg x (readTreeState t old x.(regPath)))) old new ret):
    SemAction (ReadReg s x cont) old new ret
  | SemWriteReg x (v: Expr type (regKind (getRegFromPath x))) cont old new ret
      (contPf: SemAction cont (writeTreeState t old x.(regPath) (castStateRegInv x (evalExpr v))) new ret):
    SemAction (WriteReg x v cont) old new ret
  | SemReadRqMem x (i: Expr type (Bit (Z.log2_up (Z.of_nat (getMemFromPath x).(memSize))))) p cont old new ret
      (contPf:
        SemAction
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (getDefault _) in
           writeTreeState t old x.(memPath) (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) p val)))
          new ret):
    SemAction (ReadRqMem x i p cont) old new ret
  | SemReadRpMem s x p cont old new ret
      (contPf: SemAction (cont (readSameTuple (castStateMem x (readTreeState t old x.(memPath))).(Snd) p)) old new ret):
    SemAction (ReadRpMem s x p cont) old new ret
  | SemWriteMem x (i: Expr type (Bit (Z.log2_up (Z.of_nat (getMemFromPath x).(memSize))))) (v: Expr type (getMemFromPath x).(memKind)) cont old new ret
      (contPf:
        SemAction
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           writeTreeState t old x.(memPath) (castStateMemInv x (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd))))
          new ret):
    SemAction (WriteMem x i v cont) old new ret
  | SemSend x v cont old new ret
      (contPf: SemAction cont
                 (let currentTrace := castStateSend x (readTreeState t old x.(sendPath)) in
                  writeTreeState t old x.(sendPath) (castStateSendInv x (evalExpr v :: currentTrace)))
                 new ret):
    SemAction (Send x v cont) old new ret
  | SemRecv s x cont old new ret
      recvVal
      (contPf: SemAction (cont recvVal)
                 (let currentTrace := castStateRecv x (readTreeState t old x.(recvPath)) in
                  writeTreeState t old x.(recvPath) (castStateRecvInv x (recvVal :: currentTrace)))
                 new ret):
    SemAction (Recv s x cont) old new ret
  | SemLetExp s k' (e: Expr type k') cont old new ret
      (contPf: SemAction (cont (evalExpr e)) old new ret):
    SemAction (LetExp s e cont) old new ret
  | SemLetAction s k' a cont old new ret
      midState (midRet: type k')
      (aPf: SemAction a old midState midRet)
      (contPf: SemAction (cont midRet) midState new ret):
    SemAction (LetAction s a cont) old new ret
  | SemNonDet s k' cont old new ret v
      (contPf: SemAction (cont v) old new ret):
    SemAction (NonDet s k' cont) old new ret
  | SemIfElse s (p: Expr type Bool) k' t_branch f_branch cont old new ret
      midState (midRet: type k')
      (tPf: evalExpr p = true -> SemAction t_branch old midState midRet)
      (fPf: evalExpr p = false -> SemAction f_branch old midState midRet)
      (contPf: SemAction (cont midRet) midState new ret):
    SemAction (IfElse s p t_branch f_branch cont) old new ret
  | SemSystem ls cont old new ret
      (contPf: SemAction cont old new ret): SemAction (System ls cont) old new ret
  | SemReturn e old new ret
      (oldIsNew: new = old)
      (retEval: ret = evalExpr e): SemAction (Return e) old new ret.

  Section ActionsSeq.
    Variable ls: list (@Action type t (Bit 0)).

    Inductive SemActions: TreeState ElemState t -> TreeState ElemState t -> Prop :=
    | NilAction (old new: TreeState ElemState t) (eqPf: new = old) : SemActions old new
    | ConsAction (old new midState: TreeState ElemState t)
        a (inA: In a ls) (aPf: SemAction a old midState Zmod.zero)
        (rest: SemActions midState new) : SemActions old new.
  End ActionsSeq.
End SemAction.

Section SemMod.
  Variable t: Tree Elem.

  Section SemModDefn.
    Variable m: Mod t.

    Inductive SemMod : TreeState ElemState t -> TreeState ElemState t -> Prop :=
    | SemModProp (old new : TreeState ElemState t)
        (initGood: InitStateConsistent t old)
        (actions: SemActions (m type) old new) : SemMod old new.
  End SemModDefn.
End SemMod.

Definition ActionSimulation {t1 t2: Tree Elem} {K: Kind} (I1: Action type t1 K) (I2: Action type t2 K)
  (rel: TreeState ElemState t1 -> TreeState ElemState t2 -> Prop) : Prop :=
  forall (s1 : TreeState ElemState t1) (s2 : TreeState ElemState t2),
    rel s1 s2 ->
    forall (s1' : TreeState ElemState t1) (v : type K),
      SemAction I1 s1 s1' v ->
      exists (s2' : TreeState ElemState t2),
        SemAction I2 s2 s2' v /\ rel s1' s2'.

Definition ActionsSimulation {t1 t2: Tree Elem} (m1: Mod t1) (m2: Mod t2)
  (rel: TreeState ElemState t1 -> TreeState ElemState t2 -> Prop) : Prop :=
  forall (s1 : TreeState ElemState t1) (s2 : TreeState ElemState t2),
    rel s1 s2 ->
    forall (s1' : TreeState ElemState t1),
      SemActions (m1 type) s1 s1' ->
      exists (s2' : TreeState ElemState t2),
        SemActions (m2 type) s2 s2' /\ rel s1' s2'.

Definition ModSimulation {t1 t2: Tree Elem} (m1: Mod t1) (m2: Mod t2)
  (rel: TreeState ElemState t1 -> TreeState ElemState t2 -> Prop) : Prop :=
  forall old1 new1,
    SemMod m1 old1 new1 ->
    forall old2,
      rel old1 old2 ->
      exists new2,
        SemMod m2 old2 new2 /\
        rel new1 new2.
