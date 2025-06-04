From Stdlib Require Import List String FunctionalExtensionality.
Require Import Guru.Library Guru.Syntax Guru.Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section InversionSemAction.
  Variable modLists: ModLists.

  Theorem InversionSemAction
    k (a: Action type modLists k) old new puts gets ret
    (semA: SemAction a old new puts gets ret):
    match a with
    | ReadReg s x cont => SemAction (cont (stateRegs old x)) old new puts gets ret
    | WriteReg x v cont =>
        SemAction cont {|stateRegs := updStruct (stateRegs old) (evalExpr v);
                         stateMems := stateMems old;
                         stateRegUs := stateRegUs old;
                         stateMemUs := stateMemUs old|} new puts gets ret
    | ReadRqMem x i p cont =>
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems := updStruct (stateMems old)
                           (ty := fun K => (type (Array (memUSize K) (memUKind K)) *
                                              type (Array (memUPort K) (memUKind K)))%type)
                           (let arr := stateMems old x in
                            (fst arr,
                              funcToArray (updArray (arrayToFunc (snd arr)) p
                                             (readArray (Default _) (arrayToFunc (fst arr)) (evalExpr i)))));
            stateRegUs := stateRegUs old;
            stateMemUs := stateMemUs old|} new puts gets ret
    | ReadRpMem s x p cont => SemAction (cont (arrayToFunc (snd (stateMems old x)) p)) old new puts gets ret
    | WriteMem x i v cont =>
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems := updStruct (stateMems old)
                           (ty := fun K => (type (Array (memUSize K) (memUKind K)) *
                                              type (Array (memUPort K) (memUKind K)))%type)
                           (let arr := stateMems old x in
                            (funcToArray (writeArray (evalExpr v) (arrayToFunc (fst arr)) (evalExpr i)),
                              snd arr));
            stateRegUs := stateRegUs old;
            stateMemUs := stateMemUs old|} new puts gets ret
    | ReadRegU s x cont => SemAction (cont (stateRegUs old x)) old new puts gets ret
    | WriteRegU x v cont =>
        SemAction cont {|stateRegs := stateRegs old;
                         stateMems := stateMems old;
                         stateRegUs := updStruct (stateRegUs old) (evalExpr v);
                         stateMemUs := stateMemUs old|} new puts gets ret
    | ReadRqMemU x i p cont =>
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems := stateMems old;
            stateRegUs := stateRegUs old;
            stateMemUs := updStruct (stateMemUs old)
                           (ty := fun K => (type (Array (memUSize K) (memUKind K)) *
                                              type (Array (memUPort K) (memUKind K)))%type)
                           (let arr := stateMemUs old x in
                            (fst arr,
                              funcToArray (updArray (arrayToFunc (snd arr)) p
                                             (readArray (Default _) (arrayToFunc (fst arr)) (evalExpr i)))))|}
          new puts gets ret
    | ReadRpMemU s x p cont => SemAction (cont (arrayToFunc (snd (stateMemUs old x)) p)) old new puts gets ret
    | WriteMemU x i v cont =>
        SemAction
          cont
          {|stateRegs := stateRegs old;
            stateMems := stateMems old;
            stateRegUs := stateRegUs old;
            stateMemUs := updStruct (stateMemUs old)
                            (ty := fun K => (type (Array (memUSize K) (memUKind K)) *
                                               type (Array (memUPort K) (memUKind K)))%type)
                            (let arr := stateMemUs old x in
                             (funcToArray (writeArray (evalExpr v) (arrayToFunc (fst arr)) (evalExpr i)),
                               snd arr)) |} new puts gets ret
    | Send x v cont =>
        exists putsStep,
        SemAction cont old new putsStep gets ret /\
          puts = updStruct (ty := fun K => list (type K)) putsStep (evalExpr v :: putsStep x)
    | Recv s x cont =>
        exists recvStep getsStep,
        SemAction (cont recvStep) old new puts getsStep ret /\
          gets = updStruct (ty := fun K => list (type K)) getsStep (recvStep :: getsStep x)
    | LetExp s k' e cont =>
        SemAction (cont (evalExpr e)) old new puts gets ret
    | LetAction s k' a cont =>
        exists newStep putsStep getsStep retStep interPuts interGets,
        SemAction a old newStep putsStep getsStep retStep /\
          SemAction (cont retStep) newStep new interPuts interGets ret /\
          (puts = fun i => putsStep i ++ interPuts i) /\
          gets = fun i => getsStep i ++ interGets i
    | NonDet s k' cont =>
        exists v,
        SemAction (cont v) old new puts gets ret
    | IfElse s p k' t f cont =>
        exists newStep putsStep getsStep retStep interPuts interGets,
        (evalExpr p = true -> SemAction t old newStep putsStep getsStep retStep) /\
          (evalExpr p = false -> SemAction f old newStep putsStep getsStep retStep) /\
          SemAction (cont retStep) newStep new interPuts interGets ret /\
          (puts = fun i => putsStep i ++ interPuts i) /\
          gets = fun i => getsStep i ++ interGets i          
    | System ls cont =>
        SemAction cont old new puts gets ret
    | Return e =>
        new = old /\ (puts = fun i => nil) /\ (gets = fun i => nil) /\ ret = evalExpr e
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
      new = old /\ (puts = fun i => nil) /\ (gets = fun i => nil) /\ ret = (evalLetExpr le).
  Proof.
    induction le; simpl; intros;
      match goal with
      | H: SemAction _ _ _ _ _ _ |- _ => apply InversionSemAction in H
      end; auto.
    - destructAll.
      specialize (IHle _ _ _ _ _ H0).
      specialize (H _ _ _ _ _ _ H1).
      destructAll; subst; simpl.
      repeat split; auto.
    - destructAll.
      case_eq (evalExpr p); intros sth.
      + specialize (IHle1 _ _ _ _ _ (H0 sth)).
        specialize (H _ _ _ _ _ _ H2).
        destructAll; subst; simpl.
        repeat split; auto.
      + specialize (IHle2 _ _ _ _ _ (H1 sth)).
        specialize (H _ _ _ _ _ _ H2).
        destructAll; subst; simpl.
        repeat split; auto.
  Qed.
End LetExpr.

Section ExistsInitModConsistent.
  Lemma memDefInitConsistent ls:
    forall i, fst (convFinStruct (getK := memToMemU)
                     (ty := fun x => (type (Array (memUSize x) (memUKind x)) *
                                        type (Array (memUPort x) (memUKind x)))%type)
                     (fun m => (memInitFull m, Default (Array (memPort m) (memKind m)))) (ls:= ls) i) =
                convFinStruct (getK := memToMemU)
                  (ty := fun x => type (Array (memUSize x) (memUKind x))) memInitFull (ls:= ls) i.
  Proof.
    induction ls; intros.
    - contradiction.
    - destruct i.
      + auto.
      + specialize (IHls f); auto.
  Qed.

  Theorem ExistsInitModConsistent (decl: ModDecl): exists state, @InitModConsistent decl state.
  Proof.
    pose proof (@InitModStateCreate decl _ (fun i => Default _) (fun i => (Default _, Default _))
                                    (memDefInitConsistent _)
                                    _ eq_refl) as pf.
    eexists; eauto.
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
      SemAction a1 old1 new1 puts gets WO ->
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
             end) WO.

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
    unfold getModLists in *; induction 1; intros; subst; simpl in *.
    - exists old2.
      split; [intuition|].
      constructor 1; auto; clear - sameSends sameRecvs.
      + destruct sameSends; auto.
      + destruct sameRecvs; auto.
    - specialize (@step a old newStep putsStep getsStep inA aPf old2 H0) as
        [a2 [newStep2 [inA2 [relNewStep2 semA2]]]].
      specialize (IHSemAnyAction newStep2 relNewStep2) as [new2 [relNew2 rest]].
      exists new2.
      split; [intuition|].
      constructor 2 with (a := a2)
                         (puts := match sameSends in (_ = Y) return (FuncIo Y) with
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
                                      end); auto; clear - sameSends sameRecvs.
      + destruct sameSends; auto.
      + destruct sameRecvs; auto.
  Qed.

  Theorem StepInclusion: TraceInclusion m1 m2.
  Proof.
    constructor 1 with (traceSendsEq := sameSends) (traceRecvsEq := sameRecvs).
    intros.
    destruct H as [old1 [new1 [old1Consistent semAny1]]].
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
