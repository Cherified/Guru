From Stdlib Require Import String List ZArith.
From Guru Require Import Library Syntax Notations.

Section NodePathDefs.
  Variable A : Type.

  #[projections(primitive)]
  Record NodePath (t_super t_sub : Tree A) := {
    np_embed : LeafPath t_sub -> LeafPath t_super;
    np_getLeaf : forall p, getLeaf (np_embed p) = getLeaf p
  }.

  Definition np_id (t : Tree A) : NodePath t t := {| np_embed := fun p => p; np_getLeaf := fun p => eq_refl |}.
End NodePathDefs.

Arguments NodePath [A] t_super t_sub.
Arguments np_embed [A t_super t_sub] _.
Arguments np_getLeaf [A t_super t_sub] _ _.

Section LiftActionDefs.
  Context {ty : Kind -> Type}.

  Definition embedRegPath {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: RegPath t1) : RegPath t2.
  Proof.
    refine ({| regPath := np.(np_embed) x.(regPath) |}).
    rewrite (np.(np_getLeaf) x.(regPath)).
    exact x.(regPathPf).
  Defined.

  Definition embedMemPath {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: MemPath t1) : MemPath t2.
  Proof.
    refine ({| memPath := np.(np_embed) x.(memPath) |}).
    rewrite (np.(np_getLeaf) x.(memPath)).
    exact x.(memPathPf).
  Defined.

  Definition embedSendPath {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: SendPath t1) : SendPath t2.
  Proof.
    refine ({| sendPath := np.(np_embed) x.(sendPath) |}).
    rewrite (np.(np_getLeaf) x.(sendPath)).
    exact x.(sendPathPf).
  Defined.

  Definition embedRecvPath {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: RecvPath t1) : RecvPath t2.
  Proof.
    refine ({| recvPath := np.(np_embed) x.(recvPath) |}).
    rewrite (np.(np_getLeaf) x.(recvPath)).
    exact x.(recvPathPf).
  Defined.

  Lemma regKind_embed {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: RegPath t1) :
    regKind (getRegFromPath (embedRegPath np x)) = regKind (getRegFromPath x).
  Proof. unfold getRegFromPath, getRegFromPathUnsafe; simpl; rewrite (np.(np_getLeaf) x.(regPath)); reflexivity. Defined.

  Lemma memKind_embed {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: MemPath t1) :
    memKind (getMemFromPath (embedMemPath np x)) = memKind (getMemFromPath x).
  Proof. unfold getMemFromPath, getMemFromPathUnsafe; simpl; rewrite (np.(np_getLeaf) x.(memPath)); reflexivity. Defined.

  Lemma sendKind_embed {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: SendPath t1) :
    getSendKind (embedSendPath np x) = getSendKind x.
  Proof. unfold getSendKind, getSendKindFromPath, getSendKindFromElem; simpl; rewrite (np.(np_getLeaf) x.(sendPath)); reflexivity. Defined.

  Lemma recvKind_embed {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: RecvPath t1) :
    getRecvKind (embedRecvPath np x) = getRecvKind x.
  Proof. unfold getRecvKind, getRecvKindFromPath, getRecvKindFromElem; simpl; rewrite (np.(np_getLeaf) x.(recvPath)); reflexivity. Defined.

  Lemma memSize_embed {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: MemPath t1) :
    memSize (getMemFromPath (embedMemPath np x)) = memSize (getMemFromPath x).
  Proof. unfold getMemFromPath, getMemFromPathUnsafe; simpl; rewrite (np.(np_getLeaf) x.(memPath)); reflexivity. Defined.

  Lemma memPort_embed {t1 t2: Tree Elem} (np: NodePath t2 t1) (x: MemPath t1) :
    memPort (getMemFromPath (embedMemPath np x)) = memPort (getMemFromPath x).
  Proof. unfold getMemFromPath, getMemFromPathUnsafe; simpl; rewrite (np.(np_getLeaf) x.(memPath)); reflexivity. Defined.

  Definition cast_reg {ty: Kind -> Type} {t1 t2} (np: NodePath t2 t1) (x: RegPath t1)
    (v: ty (regKind (getRegFromPath (embedRegPath np x)))) : ty (regKind (getRegFromPath x)) :=
    eq_rect _ ty v _ (regKind_embed np x).

  Definition cast_mem {ty: Kind -> Type} {t1 t2} (np: NodePath t2 t1) (x: MemPath t1)
    (v: ty (memKind (getMemFromPath (embedMemPath np x)))) : ty (memKind (getMemFromPath x)) :=
    eq_rect _ ty v _ (memKind_embed np x).

  Definition cast_send {ty: Kind -> Type} {t1 t2} (np: NodePath t2 t1) (x: SendPath t1)
    (v: ty (getSendKind (embedSendPath np x))) : ty (getSendKind x) :=
    eq_rect _ ty v _ (sendKind_embed np x).

  Definition cast_recv {ty: Kind -> Type} {t1 t2} (np: NodePath t2 t1) (x: RecvPath t1)
    (v: ty (getRecvKind (embedRecvPath np x))) : ty (getRecvKind x) :=
    eq_rect _ ty v _ (recvKind_embed np x).

  Definition cast_reg_expr {ty: Kind -> Type} {t1 t2} (np: NodePath t2 t1) (x: RegPath t1)
    (v: Expr ty (regKind (getRegFromPath x))) : Expr ty (regKind (getRegFromPath (embedRegPath np x))) :=
    eq_rect _ (Expr ty) v _ (eq_sym (regKind_embed np x)).

  Definition cast_mem_expr {ty: Kind -> Type} {t1 t2} (np: NodePath t2 t1) (x: MemPath t1)
    (v: Expr ty (memKind (getMemFromPath x))) : Expr ty (memKind (getMemFromPath (embedMemPath np x))) :=
    eq_rect _ (Expr ty) v _ (eq_sym (memKind_embed np x)).

  Definition cast_mem_idx {ty: Kind -> Type} {t1 t2} (np: NodePath t2 t1) (x: MemPath t1)
    (v: Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x)))))) : Expr ty (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath (embedMemPath np x)))))) :=
    eq_rect _ (fun s => Expr ty (Bit (Z.log2_up (Z.of_nat s)))) v _ (eq_sym (memSize_embed np x)).

  Definition cast_mem_port {t1 t2} (np: NodePath t2 t1) (x: MemPath t1)
    (p: FinType (memPort (getMemFromPath x))) : FinType (memPort (getMemFromPath (embedMemPath np x))) :=
    eq_rect _ FinType p _ (eq_sym (memPort_embed np x)).

  Definition cast_send_expr {ty: Kind -> Type} {t1 t2} (np: NodePath t2 t1) (x: SendPath t1)
    (v: Expr ty (getSendKind x)) : Expr ty (getSendKind (embedSendPath np x)) :=
    eq_rect _ (Expr ty) v _ (eq_sym (sendKind_embed np x)).

  Fixpoint liftAction {t1 t2} (np: NodePath t2 t1) {k} (a: Action ty t1 k) : Action ty t2 k :=
    match a with
    | ReadReg s x cont => ReadReg s (embedRegPath np x) (fun v => liftAction np (cont (cast_reg np x v)))
    | WriteReg x v cont => WriteReg (embedRegPath np x) (cast_reg_expr np x v) (liftAction np cont)
    | ReadRqMem x i p cont => ReadRqMem (embedMemPath np x) (cast_mem_idx np x i) (cast_mem_port np x p) (liftAction np cont)
    | ReadRpMem s x p cont => ReadRpMem s (embedMemPath np x) (cast_mem_port np x p) (fun v => liftAction np (cont (cast_mem np x v)))
    | WriteMem x i v cont => WriteMem (embedMemPath np x) (cast_mem_idx np x i) (cast_mem_expr np x v) (liftAction np cont)
    | Send x v cont => Send (embedSendPath np x) (cast_send_expr np x v) (liftAction np cont)
    | Recv s x cont => Recv s (embedRecvPath np x) (fun v => liftAction np (cont (cast_recv np x v)))
    | LetExp s e cont => LetExp s e (fun v => liftAction np (cont v))
    | LetAction s a' cont => LetAction s (liftAction np a') (fun v => liftAction np (cont v))
    | NonDet s k' cont => NonDet s k' (fun v => liftAction np (cont v))
    | IfElse s p t' f' cont => IfElse s p (liftAction np t') (liftAction np f') (fun v => liftAction np (cont v))
    | System ls cont => System ls (liftAction np cont)
    | Return e => Return e
    end.
End LiftActionDefs.

Arguments liftAction [ty] [t1] [t2] np [k] a.

Ltac solve_node_path_embed t_super path_lst t_sub :=
  match path_lst with
  | nil => exact (fun (p: LeafPath t_sub) => p)
  | ?x :: ?xs =>
      match t_super with
      | Node ?name ?children =>
          let b := eval cbv in (String.eqb x name) in
          match b with
          | true =>
              let rec loop ls :=
                match ls with
                | nil => fail "not found"
                | ?y :: ?ys =>
                    let ty := constr:(LeafPath y) in
                    let tys := constr:((fix loop_f (l: list (Tree Elem)) : Type :=
                                          match l with
                                          | nil => Empty_set
                                          | x' :: xs' => (LeafPath x' + loop_f xs')%type
                                          end) ys) in
                    let tys' := eval cbv in tys in
                    first [
                       let f := constr:(ltac:(solve_node_path_embed y xs t_sub)) in
                       exact (fun (p: LeafPath t_sub) => @inl ty tys' (f p))
                    |
                       let f := constr:(ltac:(loop ys)) in
                       exact (fun (p: LeafPath t_sub) => @inr ty tys' (f p))
                    ]
                end
              in loop children
          end
      end
  end.

Ltac solveNodePath t_super path t_sub :=
  let path_lst := eval cbv in (splitDot path) in
  let t_super' := eval unfold t_super in t_super in
  let embed_f := constr:(ltac:(solve_node_path_embed t_super' path_lst t_sub)) in
  let np := constr:({| 
    np_embed := (embed_f : LeafPath t_sub -> LeafPath t_super) ;
    np_getLeaf := ltac:(intro p; reflexivity)
  |} : NodePath t_super t_sub) in
  exact np.

Notation "'LiftAction' a 'for' path 'under' t_super 'as' t_sub" := 
  (liftAction ltac:(solveNodePath t_super path t_sub) a) 
  (at level 0, path at level 0, only parsing).
