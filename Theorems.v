From Stdlib Require Import List String ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.



Section InversionSemAction.
  Variable t: Tree ModElem.

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
           let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (Default _) in
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
        exists newStep retStep,
        SemAction a' old newStep retStep /\
          SemAction (cont retStep) newStep new ret
    | NonDet s k' cont =>
        exists v,
        SemAction (cont v) old new ret
    | IfElse s p k' t_branch f_branch cont =>
        exists newStep retStep,
        (evalExpr p = true -> SemAction t_branch old newStep retStep) /\
          (evalExpr p = false -> SemAction f_branch old newStep retStep) /\
          SemAction (cont retStep) newStep new ret
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
  Variable t: Tree ModElem.

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


Definition InitStateElemConsistentPf (e: ModElem) : InitStateElemConsistent e (InitStateElem e) :=
  match e return InitStateElemConsistent e (InitStateElem e) with
  | EReg r =>
      match r.(regInit) as opt return
        (match opt with
         | None => fun s => True
         | Some init => fun s => s = init
         end)
        (match opt with
         | None => Default (regKind r)
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
         end) (memInitFull m ,, Default (Array m.(memPort) m.(memKind)))
      with
      | None => I
      | Some _ => eq_refl
      end
  | ESend _ => eq_refl
  | ERecv _ => eq_refl
  end.

Fixpoint InitStateConsistentPf (t: Tree ModElem) : InitStateConsistent t (InitState t) :=
  match t return InitStateConsistent t (InitState t) with
  | Leaf name a => InitStateElemConsistentPf a
  | Node name children =>
      (fix loop (ls: list (Tree ModElem)) :
         (fix loop (ls : list (Tree ModElem)) : ModListTreeState ls -> Prop :=
            match ls with
            | nil => fun _ => True
            | x :: xs => fun s => InitStateConsistent x s.(Fst) /\ loop xs s.(Snd)
            end) ls
           ((fix loop (ls : list (Tree ModElem)) : ModListTreeState ls :=
              match ls with
              | nil => tt
              | x :: xs => (InitState x ,, loop xs)
              end) ls) :=
         match ls return
           (fix loop (ls : list (Tree ModElem)) : ModListTreeState ls -> Prop :=
              match ls with
              | nil => fun _ => True
              | x :: xs => fun s => InitStateConsistent x s.(Fst) /\ loop xs s.(Snd)
              end) ls
             ((fix loop (ls : list (Tree ModElem)) : ModListTreeState ls :=
                match ls with
                | nil => tt
                | x :: xs => (InitState x ,, loop xs)
                end) ls)
         with
         | nil => I
         | x :: xs => conj (InitStateConsistentPf x) (loop xs)
         end) children
  end.

Definition ExistsInitModConsistent (t: Tree ModElem) : exists old, InitStateConsistent t old.
Proof.
  exists (InitState t).
  apply InitStateConsistentPf.
Qed.

Section StepInclusion.
  Variable t1 t2: Tree ModElem.
  Variable m1: Mod t1.
  Variable m2: Mod t2.
  Variable rel: TreeState ModElemState t1 -> TreeState ModElemState t2 -> Prop.
  Variable relConsistent: forall old1 old2,
      InitStateConsistent t1 old1 ->
      rel old1 old2 ->
      InitStateConsistent t2 old2.

  Variable stepMod: forall a1 old1 new1,
      In a1 (m1 type) ->
      SemAction a1 old1 new1 Zmod.zero ->
      forall old2: TreeState ModElemState t2,
        rel old1 old2 ->
        exists a2 new2,
          In a2 (m2 type) /\ SemAction a2 old2 new2 Zmod.zero /\
          rel new1 new2.

  Lemma stepInclusionHelper: forall s1 s2,
      SemAnyAction (m1 type) s1 s2 ->
      forall old2,
        rel s1 old2 ->
        exists new2,
          rel s2 new2 /\
          SemAnyAction (m2 type) old2 new2.
  Proof.
    induction 1 as [old_nil new_nil eqPf | old_cons new_cons newStep step rest IHrest]; intros.
    - subst.
      exists old2.
      split; [exact H | constructor 1; auto].
    - destruct step.
      specialize (@stepMod a old newStep inA aPf old2 H) as H_step.
      destruct H_step as [a2 [newStep2 [inA2 [semA2 relNewStep2]]]].
      specialize (IHrest newStep2 relNewStep2) as [new2 [relNew2 restSteps]].
      exists new2.
      split; [exact relNew2 |].
      econstructor 2; eauto.
      constructor 1 with (a := a2); auto.
  Qed.

  Theorem StepInclusion: TraceInclusion m1 m2 rel.
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    pose proof (@relConsistent old1 old2 old1Consistent relOld) as old2Consistent.
    pose proof (stepInclusionHelper semAny1 relOld) as [new2 [relNew2 semAny2]].
    exists new2.
    split.
    - constructor; auto.
    - exact relNew2.
  Qed.
End StepInclusion.

Section CombineActionsHelpers.
  Variable t: Tree ModElem.

  Lemma addStep ls old new:
    Step ls old new ->
    forall (act: @Action type t (Bit 0)),
      Step (act :: ls) old new.
  Proof.
    intros.
    destruct H; subst.
    constructor 1 with (a := a); simpl; tauto.
  Qed.

  Lemma addSemAnyAction ls old new:
    SemAnyAction ls old new ->
    forall (a: @Action type t (Bit 0)),
      SemAnyAction (a :: ls) old new.
  Proof.
    induction 1; subst; intros.
    - constructor 1; auto.
    - econstructor 2 with (newStep := newStep); eauto.
      apply addStep; auto.
  Qed.

  Lemma combineSemActionToSemAnyAction (ls: list (@Action type t (Bit 0))):
    forall old new,
      SemAction (combineActions ls) old new Zmod.zero ->
      SemAnyAction ls old new.
  Proof.
    induction ls; simpl; intros; apply InversionSemAction in H; cbn in H.
    - destruct H; subst.
      constructor 1; auto.
    - destruct H as [newStep [retStep [semA semCb]]].
      specialize (IHls _ _ semCb).
      pose proof (Zmod.hprop_Zmod_1 retStep Zmod.zero) as retEq.
      subst.
      pose proof (addSemAnyAction IHls a) as pf.
      econstructor 2 with (newStep := newStep); eauto.
      econstructor; eauto.
      simpl; tauto.
  Qed.

  Section CombineSemAnyAction.
    Variable ls: list (@Action type t (Bit 0)).
    Lemma combineSemAnyActions:
      forall old new1 new2,
        SemAnyAction ls old new1 ->
        SemAnyAction ls new1 new2 ->
        SemAnyAction ls old new2.
    Proof.
      induction 1 as [old_nil new_nil eqPf | old_cons new_cons newStep step rest IHrest]; intros.
      - subst.
        exact H.
      - econstructor 2 with (newStep := newStep); eauto.
    Qed.
  End CombineSemAnyAction.

  Lemma combineActionsSemantics (ls: list (@Action type t (Bit 0))):
    forall old new,
      SemAnyAction (combineActions ls :: nil) old new ->
      SemAnyAction ls old new.
  Proof.
    induction 1 as [old_nil new_nil eqPf | old_cons new_cons newStep step rest IHrest]; intros.
    - constructor 1; subst; auto.
    - subst.
      destruct step.
      destruct inA; [subst | contradiction].
      apply combineSemActionToSemAnyAction in aPf.
      eapply combineSemAnyActions; eauto.
  Qed.
End CombineActionsHelpers.

Section CombineActionsTraceInclusion.
  Variable t: Tree ModElem.
  Variable ls: forall ty, list (@Action ty t (Bit 0)).

  Theorem CombineActionsTraceInclusion: TraceInclusion (fun ty => combineActions (ls ty) :: nil)
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
End CombineActionsTraceInclusion.
