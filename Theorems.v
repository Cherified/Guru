From Stdlib Require Import List String ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.



Section InversionSemActionTree.
  Variable t: Tree ModElem.

  Theorem InversionSemActionTree
    k (a: @ActionTree type t k) old new ret
    (semA: SemActionTree a old new ret):
    match a with
    | ReadRegTree s x cont => SemActionTree (cont (castStateReg x (readTreeState t old x.(regPath)))) old new ret
    | WriteRegTree x v cont =>
        SemActionTree cont (writeTreeState t old x.(regPath) (castStateRegInv x (evalExpr v))) new ret
    | ReadRqMemTree x i p cont =>
        SemActionTree
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (Default _) in
           writeTreeState t old x.(memPath) (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) p val))) new ret
    | ReadRpMemTree s x p cont =>
        SemActionTree (cont (readSameTuple (castStateMem x (readTreeState t old x.(memPath))).(Snd) p)) old new ret
    | WriteMemTree x i v cont =>
        SemActionTree
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           writeTreeState t old x.(memPath) (castStateMemInv x (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd)))) new ret
    | SendTree x v cont =>
        SemActionTree cont
          (let currentTrace := castStateSend x (readTreeState t old x.(sendPath)) in
           writeTreeState t old x.(sendPath) (castStateSendInv x (evalExpr v :: currentTrace)))
          new ret
    | RecvTree s x cont =>
        exists recvVal,
        SemActionTree (cont recvVal)
          (let currentTrace := castStateRecv x (readTreeState t old x.(recvPath)) in
           writeTreeState t old x.(recvPath) (castStateRecvInv x (recvVal :: currentTrace)))
          new ret
    | LetExpTree s k' e cont =>
        SemActionTree (cont (evalExpr e)) old new ret
    | LetActionTree s k' a' cont =>
        exists newStep retStep,
        SemActionTree a' old newStep retStep /\
          SemActionTree (cont retStep) newStep new ret
    | NonDetTree s k' cont =>
        exists v,
        SemActionTree (cont v) old new ret
    | IfElseTree s p k' t_branch f_branch cont =>
        exists newStep retStep,
        (evalExpr p = true -> SemActionTree t_branch old newStep retStep) /\
          (evalExpr p = false -> SemActionTree f_branch old newStep retStep) /\
          SemActionTree (cont retStep) newStep new ret
    | SystemTree ls cont =>
        SemActionTree cont old new ret
    | ReturnTree e =>
        new = old /\ ret = evalExpr e
    end.
  Proof.
    destruct semA; eauto; repeat eexists; eauto; try discriminate.
  Qed.
End InversionSemActionTree.


Section LetExpr.
  Variable t: Tree ModElem.

  Local Ltac destructAll := repeat (match goal with
                                    | H: exists _, _ |- _ => destruct H
                                    | H: _ /\ _ |- _ => destruct H
                                    end).

  Theorem SemActionLetExpr k (le: LetExpr type k):
    forall old new ret,
      SemActionTree (@toActionTree _ t _ le) old new ret ->
      new = old /\ ret = (evalLetExpr le).
  Proof.
    induction le; simpl; intros;
      match goal with
      | H: SemActionTree _ _ _ _ |- _ => apply InversionSemActionTree in H
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
  | ERegister r =>
      match r.(registerInit) as opt return
        (match opt with
         | None => fun s => True
         | Some init => fun s => s = init
         end)
        (match opt with
         | None => Default (registerKind r)
         | Some init => init
         end)
      with
      | None => I
      | Some init => eq_refl
      end
  | EMemory m =>
      match m.(memoryInit) as opt return
        (match opt with
         | None => fun s => True
         | Some _ => fun s => s.(Fst) = memoryInitFull m
         end) (memoryInitFull m ,, Default (Array m.(memoryPort) m.(memoryKind)))
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

Definition ExistsInitModConsistentTree (t: Tree ModElem) : exists old, InitStateConsistent t old.
Proof.
  exists (InitState t).
  apply InitStateConsistentPf.
Qed.

Section StepInclusionTree.
  Variable t1 t2: Tree ModElem.
  Variable m1: ModTree t1.
  Variable m2: ModTree t2.
  Variable rel: TreeState ModElemState t1 -> TreeState ModElemState t2 -> Prop.
  Variable relConsistent: forall old1 old2,
      InitStateConsistent t1 old1 ->
      rel old1 old2 ->
      InitStateConsistent t2 old2.

  Variable stepMod: forall a1 old1 new1,
      In a1 (m1 type) ->
      SemActionTree a1 old1 new1 Zmod.zero ->
      forall old2: TreeState ModElemState t2,
        rel old1 old2 ->
        exists a2 new2,
          In a2 (m2 type) /\ SemActionTree a2 old2 new2 Zmod.zero /\
          rel new1 new2.

  Lemma stepInclusionHelperTree: forall s1 s2,
      SemAnyActionTree (m1 type) s1 s2 ->
      forall old2,
        rel s1 old2 ->
        exists new2,
          rel s2 new2 /\
          SemAnyActionTree (m2 type) old2 new2.
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

  Theorem StepInclusionTree: TraceInclusionTree m1 m2 rel.
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    pose proof (@relConsistent old1 old2 old1Consistent relOld) as old2Consistent.
    pose proof (stepInclusionHelperTree semAny1 relOld) as [new2 [relNew2 semAny2]].
    exists new2.
    split.
    - constructor; auto.
    - exact relNew2.
  Qed.
End StepInclusionTree.

Section CombineActionsTreeHelpers.
  Variable t: Tree ModElem.

  Lemma addStepTree ls old new:
    StepTree ls old new ->
    forall (act: @ActionTree type t (Bit 0)),
      StepTree (act :: ls) old new.
  Proof.
    intros.
    destruct H; subst.
    constructor 1 with (a := a); simpl; tauto.
  Qed.

  Lemma addSemAnyActionTree ls old new:
    SemAnyActionTree ls old new ->
    forall (a: @ActionTree type t (Bit 0)),
      SemAnyActionTree (a :: ls) old new.
  Proof.
    induction 1; subst; intros.
    - constructor 1; auto.
    - econstructor 2 with (newStep := newStep); eauto.
      apply addStepTree; auto.
  Qed.

  Lemma combineSemActionToSemAnyActionTree (ls: list (@ActionTree type t (Bit 0))):
    forall old new,
      SemActionTree (combineActionsTree ls) old new Zmod.zero ->
      SemAnyActionTree ls old new.
  Proof.
    induction ls; simpl; intros; apply InversionSemActionTree in H; cbn in H.
    - destruct H; subst.
      constructor 1; auto.
    - destruct H as [newStep [retStep [semA semCb]]].
      specialize (IHls _ _ semCb).
      pose proof (Zmod.hprop_Zmod_1 retStep Zmod.zero) as retEq.
      subst.
      pose proof (addSemAnyActionTree IHls a) as pf.
      econstructor 2 with (newStep := newStep); eauto.
      econstructor; eauto.
      simpl; tauto.
  Qed.

  Section CombineSemAnyActionTree.
    Variable ls: list (@ActionTree type t (Bit 0)).
    Lemma combineSemAnyActionsTree:
      forall old new1 new2,
        SemAnyActionTree ls old new1 ->
        SemAnyActionTree ls new1 new2 ->
        SemAnyActionTree ls old new2.
    Proof.
      induction 1 as [old_nil new_nil eqPf | old_cons new_cons newStep step rest IHrest]; intros.
      - subst.
        exact H.
      - econstructor 2 with (newStep := newStep); eauto.
    Qed.
  End CombineSemAnyActionTree.

  Lemma combineActionsSemanticsTree (ls: list (@ActionTree type t (Bit 0))):
    forall old new,
      SemAnyActionTree (combineActionsTree ls :: nil) old new ->
      SemAnyActionTree ls old new.
  Proof.
    induction 1 as [old_nil new_nil eqPf | old_cons new_cons newStep step rest IHrest]; intros.
    - constructor 1; subst; auto.
    - subst.
      destruct step.
      destruct inA; [subst | contradiction].
      apply combineSemActionToSemAnyActionTree in aPf.
      eapply combineSemAnyActionsTree; eauto.
  Qed.
End CombineActionsTreeHelpers.

Section CombineActionsTreeTraceInclusion.
  Variable t: Tree ModElem.
  Variable ls: forall ty, list (@ActionTree ty t (Bit 0)).

  Theorem CombineActionsTreeTraceInclusion: TraceInclusionTree (fun ty => combineActionsTree (ls ty) :: nil)
                                                              ls
                                                              (fun s1 s2 => s1 = s2).
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    subst old2.
    apply combineActionsSemanticsTree in semAny1.
    exists new1.
    split.
    - constructor; auto.
    - reflexivity.
  Qed.
End CombineActionsTreeTraceInclusion.

