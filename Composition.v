From Stdlib Require Import String List ZArith Bool.
From Guru Require Import Library Syntax Notations.

Fixpoint getLeaf_embedLeafIntoPath {A: Type} {t: Tree A} : forall (p: NodePath t) (l: LeafPath (getNode p)),
  getLeaf (@embedLeafIntoPath _ t p l) = getLeaf l.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - destruct p as [u | empty]; [reflexivity | destruct empty].
  - destruct p as [p_node | p_children]; simpl.
    + reflexivity.
    + revert p_children l.
      induction children as [| c cs IHcs]; simpl; intros.
      * destruct p_children.
      * destruct p_children as [p_c | p_cs]; simpl.
        -- destruct p_c as [u | p_c_child]; simpl.
           ++ reflexivity.
           ++ change (embedLeafIntoPath_child (p_child:=p_c_child) l) with (embedLeafIntoPath (inr p_c_child) l).
              apply getLeaf_embedLeafIntoPath.
        -- apply IHcs.
Qed.

Section LiftActionDefs.
  Context {ty : Kind -> Type}.

  Definition embedRegPath {t: Tree Elem} (p: NodePath t) (x: RegPath (getNode p)) : RegPath t :=
    {| regPath := @embedLeafIntoPath _ t p x.(regPath);
       regPathPf := eq_rect_r (fun l => Is_true (isRegElem l)) x.(regPathPf) (getLeaf_embedLeafIntoPath p x.(regPath)) |}.

  Definition embedMemPath {t: Tree Elem} (p: NodePath t) (x: MemPath (getNode p)) : MemPath t :=
    {| memPath := @embedLeafIntoPath _ t p x.(memPath);
       memPathPf := eq_rect_r (fun l => Is_true (isMemElem l)) x.(memPathPf) (getLeaf_embedLeafIntoPath p x.(memPath)) |}.

  Definition embedSendPath {t: Tree Elem} (p: NodePath t) (x: SendPath (getNode p)) : SendPath t :=
    {| sendPath := @embedLeafIntoPath _ t p x.(sendPath);
       sendPathPf := eq_rect_r (fun l => Is_true (isSendElem l)) x.(sendPathPf) (getLeaf_embedLeafIntoPath p x.(sendPath)) |}.

  Definition embedRecvPath {t: Tree Elem} (p: NodePath t) (x: RecvPath (getNode p)) : RecvPath t :=
    {| recvPath := @embedLeafIntoPath _ t p x.(recvPath);
       recvPathPf := eq_rect_r (fun l => Is_true (isRecvElem l)) x.(recvPathPf) (getLeaf_embedLeafIntoPath p x.(recvPath)) |}.

  Lemma regKind_embed {t: Tree Elem} (p: NodePath t) (x: RegPath (getNode p)) :
    regKind (getRegFromPath (embedRegPath p x)) = regKind (getRegFromPath x).
  Proof. unfold getRegFromPath, getRegFromPathUnsafe; simpl; rewrite getLeaf_embedLeafIntoPath; reflexivity. Qed.

  Lemma memKind_embed {t: Tree Elem} (p: NodePath t) (x: MemPath (getNode p)) :
    memKind (getMemFromPath (embedMemPath p x)) = memKind (getMemFromPath x).
  Proof. unfold getMemFromPath, getMemFromPathUnsafe; simpl; rewrite getLeaf_embedLeafIntoPath; reflexivity. Qed.

  Lemma sendKind_embed {t: Tree Elem} (p: NodePath t) (x: SendPath (getNode p)) :
    getSendKind (embedSendPath p x) = getSendKind x.
  Proof. unfold getSendKind, getSendKindFromPath, getSendKindFromElem; simpl; rewrite getLeaf_embedLeafIntoPath; reflexivity. Qed.

  Lemma recvKind_embed {t: Tree Elem} (p: NodePath t) (x: RecvPath (getNode p)) :
    getRecvKind (embedRecvPath p x) = getRecvKind x.
  Proof. unfold getRecvKind, getRecvKindFromPath, getRecvKindFromElem; simpl; rewrite getLeaf_embedLeafIntoPath; reflexivity. Qed.

  Lemma memSize_embed {t: Tree Elem} (p: NodePath t) (x: MemPath (getNode p)) :
    memSize (getMemFromPath (embedMemPath p x)) = memSize (getMemFromPath x).
  Proof. unfold getMemFromPath, getMemFromPathUnsafe; simpl; rewrite getLeaf_embedLeafIntoPath; reflexivity. Qed.

  Lemma memPort_embed {t: Tree Elem} (p: NodePath t) (x: MemPath (getNode p)) :
    memPort (getMemFromPath (embedMemPath p x)) = memPort (getMemFromPath x).
  Proof. unfold getMemFromPath, getMemFromPathUnsafe; simpl; rewrite getLeaf_embedLeafIntoPath; reflexivity. Qed.

  Definition cast_reg {ty: Kind -> Type} {t} (p: NodePath t) (x: RegPath (getNode p))
    (v: ty (regKind (getRegFromPath (embedRegPath p x)))) : ty (regKind (getRegFromPath x)) :=
    eq_rect _ ty v _ (regKind_embed p x).

  Definition cast_mem {ty: Kind -> Type} {t} (p: NodePath t) (x: MemPath (getNode p))
    (v: ty (memKind (getMemFromPath (embedMemPath p x)))) : ty (memKind (getMemFromPath x)) :=
    eq_rect _ ty v _ (memKind_embed p x).

  Definition cast_send {ty: Kind -> Type} {t} (p: NodePath t) (x: SendPath (getNode p))
    (v: ty (getSendKind (embedSendPath p x))) : ty (getSendKind x) :=
    eq_rect _ ty v _ (sendKind_embed p x).

  Definition cast_recv {ty: Kind -> Type} {t} (p: NodePath t) (x: RecvPath (getNode p))
    (v: ty (getRecvKind (embedRecvPath p x))) : ty (getRecvKind x) :=
    eq_rect _ ty v _ (recvKind_embed p x).

  Definition cast_reg_expr {ty: Kind -> Type} {t} (p: NodePath t) (x: RegPath (getNode p))
    (v: Expr ty (regKind (getRegFromPath x))) : Expr ty (regKind (getRegFromPath (embedRegPath p x))) :=
    eq_rect _ (Expr ty) v _ (eq_sym (regKind_embed p x)).

  Definition cast_mem_expr {ty: Kind -> Type} {t} (p: NodePath t) (x: MemPath (getNode p))
    (v: Expr ty (memKind (getMemFromPath x))) : Expr ty (memKind (getMemFromPath (embedMemPath p x))) :=
    eq_rect _ (Expr ty) v _ (eq_sym (memKind_embed p x)).

  Definition cast_mem_idx {ty: Kind -> Type} {t} (p: NodePath t) (x: MemPath (getNode p))
    (v: Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x)))))) :
    Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath (embedMemPath p x)))))) :=
    eq_rect _ (fun s => Expr ty (Bit (Z.log2_up (Z.of_nat s)))) v _ (eq_sym (memSize_embed p x)).

  Definition cast_mem_port {t} (p: NodePath t) (x: MemPath (getNode p))
    (port: FinType (memPort (getMemFromPath x))) : FinType (memPort (getMemFromPath (embedMemPath p x))) :=
    eq_rect _ FinType port _ (eq_sym (memPort_embed p x)).

  Definition cast_send_expr {ty: Kind -> Type} {t} (p: NodePath t) (x: SendPath (getNode p))
    (v: Expr ty (getSendKind x)) : Expr ty (getSendKind (embedSendPath p x)) :=
    eq_rect _ (Expr ty) v _ (eq_sym (sendKind_embed p x)).

  Fixpoint liftAction {t: Tree Elem} (p: NodePath t) {k} (a: Action ty (getNode p) k) : Action ty t k :=
    match a with
    | ReadReg s x cont => ReadReg s (embedRegPath p x) (fun v => liftAction p (cont (cast_reg p x v)))
    | WriteReg x v cont => WriteReg (embedRegPath p x) (cast_reg_expr p x v) (liftAction p cont)
    | ReadRqMem x i port cont => ReadRqMem (embedMemPath p x) (cast_mem_idx p x i) (cast_mem_port p x port)
                                (liftAction p cont)
    | ReadRpMem s x port cont => ReadRpMem s (embedMemPath p x) (cast_mem_port p x port)
                                (fun v => liftAction p (cont (cast_mem p x v)))
    | WriteMem x i v cont => WriteMem (embedMemPath p x) (cast_mem_idx p x i) (cast_mem_expr p x v)
                               (liftAction p cont)
    | Send x v cont => Send (embedSendPath p x) (cast_send_expr p x v) (liftAction p cont)
    | Recv s x cont => Recv s (embedRecvPath p x) (fun v => liftAction p (cont (cast_recv p x v)))
    | LetExp s e cont => LetExp s e (fun v => liftAction p (cont v))
    | LetAction s a' cont => LetAction s (liftAction p a') (fun v => liftAction p (cont v))
    | NonDet s k' cont => NonDet s k' (fun v => liftAction p (cont v))
    | IfElse s cond t' f' cont => IfElse s cond (liftAction p t') (liftAction p f') (fun v => liftAction p (cont v))
    | System ls cont => System ls (liftAction p cont)
    | Return e => Return e
    end.
End LiftActionDefs.

Arguments liftAction [ty] [t] p [k] a.

Notation "'LiftAction' a 'for' path 'under' t" :=
  (liftAction (getNodePath t path) a)
  (at level 0, path at level 0, only parsing).

Definition liftMod {t} (p: NodePath t) (m: Mod (getNode p)) : Mod t :=
  fun ty => map (liftAction (ty:=ty) p (k:=Bit 0)) (m ty).

Definition embedRegOfKind {t: Tree Elem} (p: NodePath t) {k: Kind} (x: RegOfKind (t:=getNode p) k) :
  RegOfKind (t:=t) k.
Proof.
  refine ({| rk_path := embedRegPath p x.(rk_path) ; rk_pf := _ x.(rk_pf) |}).
  abstract (rewrite regKind_embed; auto).
Defined.

Fixpoint getTreeRegPaths (t: Tree Elem) : list (RegPath t) :=
  match t return list (RegPath t) with
  | Leaf name (EReg r) => {| regPath := (tt : LeafPath (Leaf name (EReg r))) ; regPathPf := I |} :: nil
  | Leaf _ _ => nil
  | Node name children =>
      (fix loop (ls: list (Tree Elem)) : list (RegPath (Node name ls)) :=
         match ls return list (RegPath (Node name ls)) with
         | nil => nil
         | x :: xs =>
             (map (fun (p : RegPath x) =>
               {| regPath := (inl p.(regPath) : LeafPath (Node name (x :: xs))) ;
                  regPathPf := p.(regPathPf) |}) (getTreeRegPaths x)) ++
             (map (fun (p : RegPath (Node name xs)) =>
               {| regPath := (inr p.(regPath) : LeafPath (Node name (x :: xs))) ;
                  regPathPf := p.(regPathPf) |}) (loop xs))
         end) children
  end.

Fixpoint getTreeRegsOfKind (k: Kind) (t: Tree Elem) : list (RegOfKind (t:=t) k) :=
  match t return list (RegOfKind (t:=t) k) with
  | Leaf name (EReg r) =>
      match Kind_eqb (regKind r) k as b return (Kind_eqb (regKind r) k = b -> list (RegOfKind (t:=Leaf name (EReg r)) k)) with
      | true => fun pf => {| rk_path := {| regPath := (tt : LeafPath (Leaf name (EReg r))) ; regPathPf := I |} ;
                             rk_pf := eq_rect_r (fun b' => Is_true b') (I : Is_true true) pf |} :: nil
      | false => fun _ => nil
      end eq_refl
  | Leaf _ _ => nil
  | Node name children =>
      (fix loop (ls: list (Tree Elem)) : list (RegOfKind (t:=Node name ls) k) :=
         match ls return list (RegOfKind (t:=Node name ls) k) with
         | nil => nil
         | x :: xs =>
             (map (fun (p : RegOfKind (t:=x) k) =>
               {| rk_path := {| regPath := (inl p.(rk_path).(regPath) : LeafPath (Node name (x :: xs))) ;
                                regPathPf := p.(rk_path).(regPathPf) |} ;
                  rk_pf := p.(rk_pf) |}) (getTreeRegsOfKind k x)) ++
             (map (fun (p : RegOfKind (t:=Node name xs) k) =>
               {| rk_path := {| regPath := (inr p.(rk_path).(regPath) : LeafPath (Node name (x :: xs))) ;
                                regPathPf := p.(rk_path).(regPathPf) |} ;
                  rk_pf := p.(rk_pf) |}) (loop xs))
         end) children
  end.
