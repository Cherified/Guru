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
                           (let p := Z.to_nat (Zmod.to_Z (@evalExpr _ i)) in
                            Build_SameTuple (updListLength (evalExpr v) (fst arr).(tupleSize) p), snd arr);
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
                            (let p := Z.to_nat (Zmod.to_Z (@evalExpr _ i)) in
                             Build_SameTuple (updListLength (evalExpr v) (fst arr).(tupleSize) p), snd arr)|}
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
      repeat split; auto; apply combineDef.
    - destructAll.
      case_eq (evalExpr p); intros sth.
      + specialize (IHle1 _ _ _ _ _ (H0 sth)).
        specialize (H _ _ _ _ _ _ H2).
        destructAll; subst; simpl.
        repeat split; auto; apply combineDef.
      + specialize (IHle2 _ _ _ _ _ (H1 sth)).
        specialize (H _ _ _ _ _ _ H2).
        destructAll; subst; simpl.
        repeat split; auto; apply combineDef.
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

  Lemma addSemAnyAction ls old new puts gets:
    SemAnyAction ls old new puts gets ->
    forall (a: Action type modLists (Bit 0)),
      SemAnyAction (a :: ls) old new puts gets.
  Proof.
    induction 1; subst; intros.
    - constructor 1; auto.
    - econstructor 2; eauto.
      constructor 2; auto.
  Qed.

  Lemma combineSemActionToSemAnyAction (ls: list (Action type modLists (Bit 0))):
    forall old new puts gets,
      SemAction (combineActionsType ls) old new puts gets WO ->
      SemAnyAction ls old new puts gets.
  Proof.
    induction ls; simpl; intros; apply InversionSemAction in H.
    - destruct H as [? [? [? ?]]]; subst.
      constructor 1; auto.
    - destruct H as
        [newStep [putsStep [getsStep [retStep [interPuts [interGets [semA [semCb [putsEq getsEq]]]]]]]]].
      specialize (IHls _ _ _ _ semCb).
      pose proof (unique_word_0 retStep) as retEq.
      subst.
      econstructor 2 with (a := a) (newStep := newStep); eauto.
      + constructor; auto.
      + apply addSemAnyAction; auto.
  Qed.

  Section CombineSemAnyAction.
    Variable ls: list (Action type modLists (Bit 0)).
    Lemma combineSemAnyActions:
      forall old new1 puts1 gets1 new2 puts2 gets2,
        SemAnyAction ls old new1 puts1 gets1 ->
        SemAnyAction ls new1 new2 puts2 gets2 ->
        SemAnyAction ls old new2 (fun i => puts1 i ++ puts2 i) (fun i => gets1 i ++ gets2 i).
    Proof.
      induction 1; subst; simpl; intros.
      - Local Ltac func_extension_basic := (apply functional_extensionality_dep; tauto).
        assert (ppf: puts2 = fun i => puts2 i) by func_extension_basic.
        assert (gpf: gets2 = fun i => gets2 i) by func_extension_basic.
        rewrite <- ppf, <- gpf.
        intuition.
      - specialize (IHSemAnyAction H0).
        pose proof (Step inA aPf IHSemAnyAction eq_refl eq_refl) as final.
        simpl in final.
        Local Ltac func_extension_assoc := (
                                            apply functional_extensionality_dep;
                                            intros;
                                            rewrite <- app_assoc;
                                            reflexivity).
        assert (ppf: (fun i => (putsStep i ++ puts i) ++ puts2 i) = fun i => putsStep i ++ puts i ++ puts2 i) by
          func_extension_assoc.
        assert (gpf: (fun i => (getsStep i ++ gets i) ++ gets2 i) = fun i => getsStep i ++ gets i ++ gets2 i) by
          func_extension_assoc.
        rewrite ppf, gpf.
        intuition.
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
      (traceSendsEq := eq_refl) (traceRecvsEq := eq_refl); auto; unfold SemMod; simpl; intros.
    destruct H as [old [new [oldConsistent semAny]]].
    apply combineActionsSemantics in semAny.
    exists old.
    exists new.
    split; auto.
  Qed.
End CombineActionsTraceInclusion.
