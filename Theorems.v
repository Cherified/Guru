From Stdlib Require Import List String ZArith Zmod.
Require Import Guru.Library Guru.Syntax Guru.Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section InversionSemAction.
  Variable modLists: ModLists.

  Theorem InversionSemAction
    k (a: Action type modLists k) old new puts gets ret
    (semA: SemAction a old new puts gets ret):
    match a with
    | ReadReg s x cont => SemAction (cont (readDiffTuple old.(stateRegs) x)) old new puts gets ret
    | WriteReg x v cont =>
        SemAction cont {|stateRegs := updDiffTuple old.(stateRegs) (evalExpr v);
                         stateMems := old.(stateMems);
                         stateRegUs := old.(stateRegUs);
                         stateMemUs := old.(stateMemUs)|} new puts gets ret
    | ReadRqMem x i p cont =>
        SemAction
          cont
          {|stateRegs := old.(stateRegs);
            stateMems := let arr := readDiffTuple old.(stateMems) x in
                         updDiffTuple (old.(stateMems))
                           (fst arr, updSameTuple (snd arr) p (readNatToFinType (Default _) (readSameTuple (fst arr))
                                                                 (Z.to_nat (Zmod.to_Z (evalExpr i)))));
            stateRegUs := old.(stateRegUs);
            stateMemUs := old.(stateMemUs)|} new puts gets ret
    | ReadRpMem s x p cont =>
        SemAction (cont (readSameTuple (snd (readDiffTuple old.(stateMems) x)) p)) old new puts gets ret
    | WriteMem x i v cont =>
        SemAction
          cont
          {|stateRegs := old.(stateRegs);
            stateMems := let arr := readDiffTuple old.(stateMems) x in
                         updDiffTuple (old.(stateMems))
                           (updSameTupleNat (fst arr) (Z.to_nat (Zmod.to_Z (@evalExpr _ i))) (evalExpr v), snd arr);
            stateRegUs := old.(stateRegUs);
            stateMemUs := old.(stateMemUs)|} new puts gets ret
    | ReadRegU s x cont => SemAction (cont (readDiffTuple old.(stateRegUs) x)) old new puts gets ret
    | WriteRegU x v cont =>
        SemAction cont {|stateRegs := old.(stateRegs);
                         stateMems := old.(stateMems);
                         stateRegUs := updDiffTuple old.(stateRegUs) (evalExpr v);
                         stateMemUs := stateMemUs old|} new puts gets ret
    | ReadRqMemU x i p cont =>
        SemAction
          cont
          {|stateRegs := old.(stateRegs);
            stateMems := old.(stateMems);
            stateRegUs := old.(stateRegUs);
            stateMemUs := let arr := readDiffTuple old.(stateMemUs) x in
                          updDiffTuple (old.(stateMemUs))
                            (fst arr, updSameTuple (snd arr) p (readNatToFinType (Default _) (readSameTuple (fst arr))
                                                                  (Z.to_nat (Zmod.to_Z (evalExpr i)))))|}
          new puts gets ret
    | ReadRpMemU s x p cont =>
        SemAction (cont (readSameTuple (snd (readDiffTuple old.(stateMemUs) x)) p)) old new puts gets ret
    | WriteMemU x i v cont =>
        SemAction
          cont
          {|stateRegs := old.(stateRegs);
            stateMems := old.(stateMems);
            stateRegUs := old.(stateRegUs);
            stateMemUs := let arr := readDiffTuple old.(stateMemUs) x in
                          updDiffTuple (old.(stateMemUs))
                            (updSameTupleNat (fst arr) (Z.to_nat (Zmod.to_Z (@evalExpr _ i))) (evalExpr v), snd arr)|}
          new puts gets ret
    | Send x v cont =>
        exists putsStep,
        SemAction cont old new putsStep gets ret /\
          puts = updDiffTuple putsStep (evalExpr v :: readDiffTuple putsStep x)
    | Recv s x cont =>
        exists recvStep getsStep,
        SemAction (cont recvStep) old new puts getsStep ret /\
          gets = updDiffTuple getsStep (recvStep :: readDiffTuple getsStep x)
    | LetExp s k' e cont =>
        SemAction (cont (evalExpr e)) old new puts gets ret
    | LetAction s k' a cont =>
        exists newStep putsStep getsStep retStep interPuts interGets,
        SemAction a old newStep putsStep getsStep retStep /\
          SemAction (cont retStep) newStep new interPuts interGets ret /\
          (puts = combineDiffTuple (fun _ => @List.app _) putsStep interPuts) /\
          gets = combineDiffTuple (fun _ => @List.app _) getsStep interGets
    | NonDet s k' cont =>
        exists v,
        SemAction (cont v) old new puts gets ret
    | IfElse s p k' t f cont =>
        exists newStep putsStep getsStep retStep interPuts interGets,
        (evalExpr p = true -> SemAction t old newStep putsStep getsStep retStep) /\
          (evalExpr p = false -> SemAction f old newStep putsStep getsStep retStep) /\
          SemAction (cont retStep) newStep new interPuts interGets ret /\
          (puts = combineDiffTuple (fun _ => @List.app _) putsStep interPuts) /\
          gets = combineDiffTuple (fun _ => @List.app _) getsStep interGets
    | System ls cont =>
        SemAction cont old new puts gets ret
    | Return e =>
        new = old /\ (puts = defaultDiffTuple (fun _ => nil) _) /\ (gets = defaultDiffTuple (fun _ => nil) _) /\
          ret = evalExpr e
    end.
  Proof.
    destruct semA; eauto; repeat eexists; eauto; try discriminate.
  Qed.
End InversionSemAction.

Section LetExpr.
  Variable modLists: ModLists.

  Local Ltac destructAll := repeat (match goal with
                                    | H: exists _, _ |- _ => destruct H
                                    | H: _ /\ _ |- _ => destruct H
                                    end).

  Theorem SemActionLetExpr k (le: LetExpr type k):
    forall old new puts gets ret,
      SemAction (@toAction _ modLists _ le) old new puts gets ret ->
      new = old /\ (puts = defaultDiffTuple (fun _ => nil) _) /\ (gets = defaultDiffTuple (fun _ => nil) _) /\
        ret = (evalLetExpr le).
  Proof.
    induction le; simpl; intros;
      match goal with
      | H: SemAction _ _ _ _ _ _ |- _ => apply InversionSemAction in H
      end; auto.
    - destructAll.
      specialize (IHle _ _ _ _ _ H0).
      specialize (H _ _ _ _ _ _ H1).
      destructAll; subst; simpl.
      repeat split; auto; apply combineDiffTupleDef; auto.
    - destructAll.
      case_eq (evalExpr p); intros sth.
      + specialize (IHle1 _ _ _ _ _ (H0 sth)).
        specialize (H _ _ _ _ _ _ H2).
        destructAll; subst; simpl.
        repeat split; auto; apply combineDiffTupleDef; auto.
      + specialize (IHle2 _ _ _ _ _ (H1 sth)).
        specialize (H _ _ _ _ _ _ H2).
        destructAll; subst; simpl.
        repeat split; auto; apply combineDiffTupleDef; auto.
  Qed.
End LetExpr.

Unset Strict Implicit.
Section mapDiffTuple_createDiffTupleMap.
  Variable A B: Type.
  Variable Conv1: A -> Type.
  Variable Conv2: A -> Type.
  Variable f: forall a, Conv1 a -> Conv2 a.
  Variable mapF: B -> A.
  Variable g: forall b, Conv1 (mapF b).
  Theorem mapDiffTuple_createDiffTupleMap ls:
    (mapDiffTuple f (createDiffTupleMap (mapF := mapF) g ls)) =
      createDiffTupleMap (mapF := mapF) (fun a => f (g a)) ls.
  Proof.
    induction ls; simpl; auto.
    rewrite IHls.
    auto.
  Qed.
End mapDiffTuple_createDiffTupleMap.
Set Strict Implicit.

Section ExistsInitModConsistent.
  Theorem ExistsInitModConsistent (decl: ModDecl): exists state, @InitModConsistent decl state.
  Proof.
    eexists.
    eexact (@InitModStateCreate decl _
              (defaultDiffTuple (fun x => Default (snd x)) decl.(modRegUs))
              (defaultDiffTuple (fun x => (Default (Array (snd x).(memUSize) (snd x).(memUKind)),
                                            Default (Array (snd x).(memUPort) (snd x).(memUKind))))
                 decl.(modMemUs))
              (mapDiffTuple_createDiffTupleMap
                 (Conv1 := fun x => (type (Array (snd x).(memUSize) (snd x).(memUKind)) *
                                       type (Array (snd x).(memUPort) (snd x).(memUKind)))%type)
                 (fun _ => fst)
                 (mapF := fun x => (fst x, memToMemU (snd x)))
                 (fun x => (memInitFull (snd x), Default (Array (snd x).(memPort) (snd x).(memKind))))
                 decl.(modMems))
              _
              eq_refl).
  Qed.
End ExistsInitModConsistent.

Section StepInclusion.
  Variable m1 m2: Mod.
  Variable rel: ModStateModDecl (modDecl m1) -> ModStateModDecl (modDecl m2) -> Prop.
  Variable initRel: forall init1, InitModConsistent init1 ->
                                  forall init2, InitModConsistent init2 -> rel init1 init2.
  Variable sameSends: modSends (modDecl m1) = modSends (modDecl m2).
  Variable sameRecvs: modRecvs (modDecl m1) = modRecvs (modDecl m2).

  Variable step: forall a1 (old1 new1: ModStateModDecl (modDecl m1)) puts gets,
      In a1 (modActions m1 type) ->
      SemAction a1 old1 new1 puts gets Zmod.zero ->
      forall old2: ModStateModDecl (modDecl m2),
        rel old1 old2 ->
        exists (a2: Action _ _ (Bit 0)) (new2: ModStateModDecl (modDecl m2)),
          In a2 (modActions m2 type) /\ rel new1 new2 /\
          SemAction a2 old2 new2
            (match sameSends in _ = Y return _ Y with
             | eq_refl => puts
             end)
            (match sameRecvs in _ = Y return _ Y with
             | eq_refl => gets
             end) Zmod.zero.

  Lemma stepInclusionHelper: forall (old1 new1: ModStateModDecl (modDecl m1)) puts gets,
      SemAnyAction (modActions m1 type) old1 new1 puts gets ->
      forall old2: ModStateModDecl (modDecl m2),
        rel old1 old2 ->
        exists (new2: ModStateModDecl (modDecl m2)),
          rel new1 new2 /\ SemAnyAction (modActions m2 type) old2 new2
                             (match sameSends in _ = Y return _ Y with
                              | eq_refl => puts
                              end)
                             (match sameRecvs in _ = Y return _ Y with
                              | eq_refl => gets
                              end).
  Proof.
    unfold getModLists in *; unfold SemAnyAction; induction 1; intros; subst; simpl in *.
    - exists old2.
      split; [intuition|].
      constructor 1; auto; clear - sameSends sameRecvs.
      + destruct sameSends; auto.
      + destruct sameRecvs; auto.
    - destruct step0.
      specialize (@step a old newStep putsStep getsStep inA aPf old2 H0) as
        [a2 [newStep2 [inA2 [relNewStep2 semA2]]]].
      specialize (IHMultiStep newStep2 relNewStep2) as [new2 [relNew2 rest]].
      exists new2.
      split; [intuition|].
      constructor 2 with (puts := match sameSends in (_ = Y) return (FuncIo Y) with
                                  | eq_refl => puts
                                  end)
                         (gets := match sameRecvs in (_ = Y) return (FuncIo Y) with
                                  | eq_refl => gets
                                  end)
                         (newStep := newStep2)
                         (putsStep := match sameSends in (_ = Y) return (FuncIo Y) with
                                      | eq_refl => putsStep
                                      end)
                         (getsStep := match sameRecvs in (_ = Y) return (FuncIo Y) with
                                      | eq_refl => getsStep
                                      end); auto; try (constructor 1 with (a := a2); auto);
        clear - sameSends sameRecvs.
      + destruct sameSends; auto.
      + destruct sameRecvs; auto.
  Qed.

  Theorem StepInclusion: TraceInclusion m1 m2.
  Proof.
    constructor 1 with (traceSendsEq := sameSends) (traceRecvsEq := sameRecvs).
    intros.
    destruct H as [old1 new1 old1Consistent semAny1].
    pose proof (ExistsInitModConsistent (modDecl m2)) as [old2 old2Consistent].
    specialize (initRel old1Consistent old2Consistent).
    pose proof (stepInclusionHelper semAny1 initRel) as [new2 [new2Rel semAny2]].
    eexists; eauto.
  Qed.
End StepInclusion.

Section CombineActionsHelpers.
  Variable modLists: ModLists.

  Definition combineActionsType := @combineActions type.

  Lemma addStep ls old new puts gets:
    Step ls old new puts gets ->
    forall (act: Action type modLists (Bit 0)),
      Step (act :: ls) old new puts gets.
  Proof.
    intros.
    destruct H; subst.
    constructor 1 with (a := a); simpl; tauto.
  Qed.

  Lemma addSemAnyAction ls old new puts gets:
    SemAnyAction ls old new puts gets ->
    forall (a: Action type modLists (Bit 0)),
      SemAnyAction (a :: ls) old new puts gets.
  Proof.
    unfold SemAnyAction.
    induction 1; subst; intros.
    - constructor 1; auto.
    - econstructor 2 with (newStep := newStep); eauto.
      apply addStep; auto.
  Qed.

  Theorem Zmod_1_0: forall x: Zmod 1, x = Zmod.zero.
  Proof.
    intros.
    apply (Zmod.hprop_Zmod_1 x Zmod.zero).
  Qed.

  Lemma combineSemActionToSemAnyAction (ls: list (Action type modLists (Bit 0))):
    forall old new puts gets,
      SemAction (combineActionsType ls) old new puts gets Zmod.zero ->
      SemAnyAction ls old new puts gets.
  Proof.
    induction ls; simpl; intros; apply InversionSemAction in H.
    - destruct H as [? [? [? ?]]]; subst.
      constructor 1; auto.
    - destruct H as
        [newStep [putsStep [getsStep [retStep [interPuts [interGets [semA [semCb [putsEq getsEq]]]]]]]]].
      specialize (IHls _ _ _ _ semCb).
      pose proof (Zmod.hprop_Zmod_1 retStep Zmod.zero) as retEq.
      subst.
      pose proof (addSemAnyAction IHls a) as pf.
      econstructor 2 with (newStep := newStep); eauto.
      econstructor; eauto.
      simpl; tauto.
  Qed.

  Section CombineSemAnyAction.
    Variable ls: list (Action type modLists (Bit 0)).
    Lemma combineSemAnyActions:
      forall old new1 puts1 gets1 new2 puts2 gets2,
        SemAnyAction ls old new1 puts1 gets1 ->
        SemAnyAction ls new1 new2 puts2 gets2 ->
        SemAnyAction ls old new2 (combineDiffTuple (fun _ => @List.app _) puts1 puts2)
          (combineDiffTuple (fun _ => @List.app _) gets1 gets2).
    Proof.
      induction 1; subst; simpl; intros.
      - repeat (rewrite combineDiffTupleDef; auto).
      - specialize (IHMultiStep H0).
        repeat (erewrite <- combineDiffTupleAssoc by (intros; eapply app_assoc; eauto)).
        econstructor 2; eauto.
    Qed.
  End CombineSemAnyAction.

  Lemma combineActionsSemantics (ls: list (Action type modLists (Bit 0))):
    forall old new puts gets,
      SemAnyAction (combineActionsType ls :: nil) old new puts gets ->
      SemAnyAction ls old new puts gets.
  Proof.
    induction 1.
    - constructor 1; subst; auto.
    - subst.
      destruct step.
      destruct inA; [subst | contradiction].
      apply combineSemActionToSemAnyAction in aPf.
      eapply combineSemAnyActions; eauto.
  Qed.
End CombineActionsHelpers.

Section CombineActionsTraceInclusion.
  Variable decl: ModDecl.
  Variable ls: forall ty,
      list (Action ty (getModLists decl) (Bit 0)).

  Theorem CombineActionsTraceInclusion: TraceInclusion {|modDecl := decl;
                                                         modActions := fun ty => combineActions (ls ty) :: nil |}
                                                       {|modDecl := decl;
                                                         modActions := ls |}.
  Proof.
    econstructor 1 with
      (m1 := {| modDecl := decl; modActions := fun ty => combineActions (ls ty) :: nil |})
      (m2 := {| modDecl := decl; modActions := ls |})
      (traceSendsEq := eq_refl) (traceRecvsEq := eq_refl); auto; simpl; intros.
    destruct H.
    apply combineActionsSemantics in steps.
    econstructor; eauto.
  Qed.
End CombineActionsTraceInclusion.

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
           let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) (fst arr).(tupleElems) (Default _) in
           writeTreeState t old x.(memPath) (castStateMemInv x (fst arr, updSameTuple (snd arr) p val))) new ret
    | ReadRpMemTree s x p cont =>
        SemActionTree (cont (readSameTuple (snd (castStateMem x (readTreeState t old x.(memPath)))) p)) old new ret
    | WriteMemTree x i v cont =>
        SemActionTree
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           writeTreeState t old x.(memPath) (castStateMemInv x (updSameTupleNat (fst arr) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v), snd arr))) new ret
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
         | Some _ => fun s => fst s = memoryInitFull m
         end) (memoryInitFull m, Default (Array m.(memoryPort) m.(memoryKind)))
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
            | x :: xs => fun s => InitStateConsistent x (fst s) /\ loop xs (snd s)
            end) ls
           ((fix loop (ls : list (Tree ModElem)) : ModListTreeState ls :=
              match ls with
              | nil => tt
              | x :: xs => (InitState x, loop xs)
              end) ls) :=
         match ls return
           (fix loop (ls : list (Tree ModElem)) : ModListTreeState ls -> Prop :=
              match ls with
              | nil => fun _ => True
              | x :: xs => fun s => InitStateConsistent x (fst s) /\ loop xs (snd s)
              end) ls
             ((fix loop (ls : list (Tree ModElem)) : ModListTreeState ls :=
                match ls with
                | nil => tt
                | x :: xs => (InitState x, loop xs)
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
          In a2 (m2 type) /\ rel new1 new2 /\
          SemActionTree a2 old2 new2 Zmod.zero.

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
      destruct H_step as [a2 [newStep2 [inA2 [relNewStep2 semA2]]]].
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

