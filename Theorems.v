From Stdlib Require Import List String ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.



Section InversionSemAction.
  Variable t: Tree Elem.

  Theorem InversionSemAction
    k (a: @Action type t k) old new ret
    (semA: SemAction a old new ret):
    match a with
    | ReadReg s x cont => SemAction (cont (castStateReg x (readTreeState t old x.(regPath)))) old new ret
    | WriteReg x v cont =>
        SemAction cont (writeTreeState t old x.(regPath) (castStateRegInv x (evalExpr v))) new ret
    | ReadRqMem x i p cont =>
        SemAction
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (getDefault _) in
           writeTreeState t old x.(memPath) (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) p val))) new ret
    | ReadRpMem s x p cont =>
        SemAction (cont (readSameTuple (castStateMem x (readTreeState t old x.(memPath))).(Snd) p)) old new ret
    | WriteMem x i v cont =>
        SemAction
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           writeTreeState t old x.(memPath) (castStateMemInv x (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd)))) new ret
    | Send x v cont =>
        SemAction cont
          (let currentTrace := castStateSend x (readTreeState t old x.(sendPath)) in
           writeTreeState t old x.(sendPath) (castStateSendInv x (evalExpr v :: currentTrace)))
          new ret
    | Recv s x cont =>
        exists recvVal,
        SemAction (cont recvVal)
          (let currentTrace := castStateRecv x (readTreeState t old x.(recvPath)) in
           writeTreeState t old x.(recvPath) (castStateRecvInv x (recvVal :: currentTrace)))
          new ret
    | LetExp s k' e cont =>
        SemAction (cont (evalExpr e)) old new ret
    | LetAction s k' a' cont =>
        exists midState midRet,
        SemAction a' old midState midRet /\
          SemAction (cont midRet) midState new ret
    | NonDet s k' cont =>
        exists v,
        SemAction (cont v) old new ret
    | IfElse s p k' t_branch f_branch cont =>
        exists midState midRet,
        (evalExpr p = true -> SemAction t_branch old midState midRet) /\
          (evalExpr p = false -> SemAction f_branch old midState midRet) /\
          SemAction (cont midRet) midState new ret
    | System ls cont =>
        SemAction cont old new ret
    | Return e =>
        new = old /\ ret = evalExpr e
    end.
  Proof.
    destruct semA; eauto; repeat eexists; eauto; try discriminate.
  Qed.
End InversionSemAction.


Section LetExpr.
  Variable t: Tree Elem.

  Local Ltac destructAll := repeat (match goal with
                                    | H: exists _, _ |- _ => destruct H
                                    | H: _ /\ _ |- _ => destruct H
                                    end).

  Theorem SemActionLetExpr k (le: LetExpr type k):
    forall old new ret,
      SemAction (@toAction _ t _ le) old new ret ->
      new = old /\ ret = (evalLetExpr le).
  Proof.
    induction le; simpl; intros;
      match goal with
      | H: SemAction _ _ _ _ |- _ => apply InversionSemAction in H
      end; auto.
    - destructAll.
      specialize (IHle _ _ _ H0).
      specialize (H _ _ _ _ H1).
      destructAll; subst; simpl.
      auto.
    - destructAll.
      case_eq (evalExpr p); intros sth.
      + specialize (IHle1 _ _ _ (H0 sth)).
        specialize (H _ _ _ _ H2).
        destructAll; subst; simpl; auto.
      + specialize (IHle2 _ _ _ (H1 sth)).
        specialize (H _ _ _ _ H2).
        destructAll; subst; simpl; auto.
  Qed.
End LetExpr.

Theorem Zmod_1_0: forall x: Zmod 1, x = Zmod.zero.
Proof.
  intros.
  apply (Zmod.hprop_Zmod_1 x Zmod.zero).
Qed.


Definition InitStateElemConsistentPf (e: Elem) : InitStateElemConsistent e (InitStateElem e) :=
  match e return InitStateElemConsistent e (InitStateElem e) with
  | EReg r =>
      match r.(regInit) as opt return
        (match opt with
         | None => fun s => True
         | Some init => fun s => s = init
         end)
        (match opt with
         | None => getDefault (regKind r)
         | Some init => init
         end)
      with
      | None => I
      | Some init => eq_refl
      end
  | EMem m =>
      match m.(memInit) as opt return
        (match opt with
         | None => fun s => True
         | Some _ => fun s => s.(Fst) = memInitFull m
         end) (memInitFull m ,, getDefault (Array m.(memPort) m.(memKind)))
      with
      | None => I
      | Some _ => eq_refl
      end
  | ESend _ => eq_refl
  | ERecv _ => eq_refl
  end.


Fixpoint InitStateConsistentPf (t: Tree Elem) : InitStateConsistent t (InitState t) :=
  match t return InitStateConsistent t (InitState t) with
  | Leaf name a => InitStateElemConsistentPf a
  | Node name children =>
      (fix loop (ls: list (Tree Elem)) :
         (fix loop (ls : list (Tree Elem)) : ListTreeState ElemState ls -> Prop :=
            match ls with
            | nil => fun _ => True
            | x :: xs => fun s => InitStateConsistent x s.(Fst) /\ loop xs s.(Snd)
            end) ls
           ((fix loop (ls : list (Tree Elem)) : ListTreeState ElemState ls :=
              match ls with
              | nil => tt
              | x :: xs => (InitState x ,, loop xs)
              end) ls) :=
         match ls return
           (fix loop (ls : list (Tree Elem)) : ListTreeState ElemState ls -> Prop :=
              match ls with
              | nil => fun _ => True
              | x :: xs => fun s => InitStateConsistent x s.(Fst) /\ loop xs s.(Snd)
              end) ls
             ((fix loop (ls : list (Tree Elem)) : ListTreeState ElemState ls :=
                match ls with
                | nil => tt
                | x :: xs => (InitState x ,, loop xs)
                end) ls)
         with
         | nil => I
         | x :: xs => conj (InitStateConsistentPf x) (loop xs)
         end) children
  end.

Definition ExistsInitStateConsistent (t: Tree Elem) : exists old, InitStateConsistent t old.
Proof.
  exists (InitState t).
  apply InitStateConsistentPf.
Qed.

Section ActionToModSimulation.
  Variable t1 t2: Tree Elem.
  Variable m1: Mod t1.
  Variable m2: Mod t2.
  Variable rel: TreeState ElemState t1 -> TreeState ElemState t2 -> Prop.
  Variable relConsistent: forall old1 old2,
      InitStateConsistent t1 old1 ->
      rel old1 old2 ->
      InitStateConsistent t2 old2.

  Variable actionSimulation: forall a1 old1 new1,
      In a1 (m1 type) ->
      SemAction a1 old1 new1 Zmod.zero ->
      forall old2: TreeState ElemState t2,
        rel old1 old2 ->
        exists a2 new2,
          In a2 (m2 type) /\ SemAction a2 old2 new2 Zmod.zero /\
          rel new1 new2.

  Lemma actionsSimulation: ActionsSimulation m1 m2 rel.
  Proof.
    unfold ActionsSimulation.
    intros s1 old2 H s2 H_sems.
    revert old2 H.
    induction H_sems as [old_nil new_nil eqPf | old_cons new_cons midState a inA aPf rest IHrest]; intros.
    - subst.
      exists old2.
      split; [constructor 1; auto | exact H].
    - specialize (@actionSimulation a old_cons midState inA aPf old2 H) as H_act.
      destruct H_act as [a2 [midState2 [inA2 [semA2 relMidState2]]]].
      specialize (IHrest midState2 relMidState2) as [new2 [restActions relNew2]].
      exists new2.
      split; [| exact relNew2].
      econstructor 2; eauto.
  Qed.

  Theorem ActionToModSimulation: ModSimulation m1 m2 rel.
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    pose proof (@relConsistent old1 old2 old1Consistent relOld) as old2Consistent.
    pose proof actionsSimulation as H_inc.
    unfold ActionsSimulation in H_inc.
    destruct (H_inc old1 old2 relOld new1 semAny1) as [new2 [semAny2 relNew2]].
    exists new2.
    split.
    - constructor; auto.
    - exact relNew2.
  Qed.
End ActionToModSimulation.

Section SemActionsProperties.
  Variable t: Tree Elem.

  Lemma SemActions_subset: forall (ls1 ls2: list (Action type t (Bit 0))) old new,
      SemActions ls1 old new ->
      (forall a, In a ls1 -> In a ls2) ->
      SemActions ls2 old new.
  Proof.
    intros ls1 ls2 old new H.
    induction H; intros Hincl.
    - subst.
      constructor 1.
      reflexivity.
    - econstructor 2.
      + apply Hincl. exact inA.
      + exact aPf.
      + apply IHSemActions. exact Hincl.
  Qed.

  Lemma SemActions_trans: forall (m: list (Action type t (Bit 0))) old mid new,
      SemActions m old mid ->
      SemActions m mid new ->
      SemActions m old new.
  Proof.
    intros m old mid new H1.
    induction H1; intros H2.
    - subst. exact H2.
    - econstructor 2.
      + exact inA.
      + exact aPf.
      + apply IHSemActions. exact H2.
  Qed.
End SemActionsProperties.

Section SubsetActionModSimulation.
  Variable t: Tree Elem.
  Variable m1 m2: Mod t.
  Variable H_inc: forall ty a, In a (m1 ty) -> In a (m2 ty).

  Theorem SubsetActionModSimulation: ModSimulation m1 m2 (fun s1 s2 => s1 = s2).
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    subst old2.
    exists new1.
    split; [| reflexivity].
    constructor; auto.
    apply SemActions_subset with (ls1 := m1 type); auto.
  Qed.
End SubsetActionModSimulation.

Section CombineActionsHelpers.
  Variable t: Tree Elem.

  Lemma addSemActions ls old new:
    SemActions ls old new ->
    forall (a: @Action type t (Bit 0)),
      SemActions (a :: ls) old new.
  Proof.
    induction 1 as [old_nil new_nil eqPf | old_cons new_cons midState a' inA' aPf' rest IHrest]; subst; intros.
    - constructor 1; auto.
    - econstructor 2 with (midState := midState).
      + right; exact inA'.
      + exact aPf'.
      + apply IHrest.
  Qed.

  Lemma combineSemActionToSemActions (ls: list (@Action type t (Bit 0))):
    forall old new,
      SemAction (combineActions ls) old new Zmod.zero ->
      SemActions ls old new.
  Proof.
    induction ls; simpl; intros; apply InversionSemAction in H; cbn in H.
    - destruct H; subst.
      constructor 1; auto.
    - destruct H as [midState [midRet [semA semCb]]].
      specialize (IHls _ _ semCb).
      pose proof (Zmod.hprop_Zmod_1 midRet Zmod.zero) as retEq.
      subst.
      pose proof (addSemActions IHls a) as pf.
      econstructor 2 with (midState := midState).
      + simpl; auto.
      + exact semA.
      + apply pf.
  Qed.

  Section CombineSemActions.
    Variable ls: list (@Action type t (Bit 0)).
    Lemma combineSemActions:
      forall old new1 new2,
        SemActions ls old new1 ->
        SemActions ls new1 new2 ->
        SemActions ls old new2.
    Proof.
      induction 1 as [old_nil new_nil eqPf | old_cons new_cons midState a inA aPf rest IHrest]; intros.
      - subst.
        exact H.
      - econstructor 2 with (midState := midState); eauto.
    Qed.
  End CombineSemActions.

  Lemma combineActionsSemantics (ls: list (@Action type t (Bit 0))):
    forall old new,
      SemActions (combineActions ls :: nil) old new ->
      SemActions ls old new.
  Proof.
    induction 1 as [old_nil new_nil eqPf | old_cons new_cons midState a inA aPf rest IHrest]; intros.
    - constructor 1; subst; auto.
    - subst.
      destruct inA; [subst | contradiction].
      apply combineSemActionToSemActions in aPf.
      eapply combineSemActions; eauto.
  Qed.
End CombineActionsHelpers.

Section CombineActionsTraceSimulation.
  Variable t: Tree Elem.
  Variable ls: forall ty, list (@Action ty t (Bit 0)).

  Theorem CombineActionsModSimulation: ModSimulation (fun ty => combineActions (ls ty) :: nil)
                                                             ls
                                                             (fun s1 s2 => s1 = s2).
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    subst old2.
    apply combineActionsSemantics in semAny1.
    exists new1.
    split.
    - constructor; auto.
    - reflexivity.
  Qed.
End CombineActionsTraceSimulation.
