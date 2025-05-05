Require Import List String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Guru.Lib.Library Guru.Lib.Word Guru.Lib.WordProperties.
Require Import Guru.Syntax Guru.Semantics Guru.InversionSemAction.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section StepInclusion.
  Variable m1 m2: Mod.
  Variable rel: ModStateMod m1 -> ModStateMod m2 -> Prop.
  Variable initRel: forall init1 init2, InitModConsistent init1 -> InitModConsistent init2 -> rel init1 init2.
  Variable sameSends: modSends (modDecls m1) = modSends (modDecls m2).
  Variable sameRecvs: modRecvs (modDecls m1) = modRecvs (modDecls m2).

  Variable step: forall a1 (old1 new1: ModStateMod m1) puts gets,
      In a1 (modActions m1 type) ->
      SemAction a1 old1 new1 puts gets WO ->
      forall old2: ModStateMod m2,
        rel old1 old2 ->
        exists (a2: Action _ _ _ _ _ (Bit 0)) (new2: ModStateMod m2),
          In a2 (modActions m2 type) /\ rel new1 new2 /\
          SemAction a2 old2 new2
            (match sameSends in _ = Y return _ Y with
             | eq_refl => puts
             end)
            (match sameRecvs in _ = Y return _ Y with
             | eq_refl => gets
             end) WO.

  Lemma stepInclusionHelper: forall (old1 new1: ModStateMod m1) puts gets,
      SemAnyAction (modActions m1 type) old1 new1 puts gets ->
      forall old2: ModStateMod m2,
        rel old1 old2 ->
        exists (new2: ModStateMod m2),
          rel new1 new2 /\ SemAnyAction (modActions m2 type) old2 new2
                             (match sameSends in _ = Y return _ Y with
                              | eq_refl => puts
                              end)
                             (match sameRecvs in _ = Y return _ Y with
                              | eq_refl => gets
                              end).
  Proof.
    induction 1; intros; subst.
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
    intros old1 new1 puts gets old1Consistent semAny1 old2 old2Consistent.
    pose proof (stepInclusionHelper semAny1) as semAny2.
    specialize (semAny2 old2 (@initRel _ _ old1Consistent old2Consistent)) as [new2 [relNew2 rest]].
    eexists; eauto.
  Qed.
End StepInclusion.

Section CombineActionsDef.
  Variable ty: Kind -> Type.
  Variable regs: list (string * Kind).
  Variable mems: list (string * (nat * Kind)).
  Variable sends: list (string * Kind).
  Variable recvs: list (string * Kind).

  Fixpoint combineActions (ls: list (Action ty regs mems sends recvs (Bit 0))):
    Action ty regs mems sends recvs (Bit 0) :=
    match ls return Action ty regs mems sends recvs (Bit 0) with
    | nil => Return (Const ty (Bit 0) WO)
    | x :: xs => LetAction ""%string x (fun _ => combineActions xs)
    end.
End CombineActionsDef.

Section CombineActionsHelpers.
  Variable regs: list (string * Kind).
  Variable mems: list (string * (nat * Kind)).
  Variable sends: list (string * Kind).
  Variable recvs: list (string * Kind).

  Definition combineActionsType := @combineActions type.

  Lemma addSemAnyAction ls old new puts gets:
    SemAnyAction ls old new puts gets ->
    forall (a: Action type regs mems sends recvs (Bit 0)),
      SemAnyAction (a :: ls) old new puts gets.
  Proof.
    induction 1; subst; intros.
    - constructor 1; auto.
    - econstructor 2; eauto.
      constructor 2; auto.
  Qed.

  Lemma combineSemActionToSemAnyAction (ls: list (Action type regs mems sends recvs (Bit 0))):
    forall old new puts gets,
      SemAction (combineActionsType ls) old new puts gets WO ->
      SemAnyAction ls old new puts gets.
  Proof.
    induction ls; simpl; intros; apply InversionSemAction in H.
    - destruct H as [? [? ?]]; subst.
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
    Variable ls: list (Action type regs mems sends recvs (Bit 0)).
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

  Lemma combineActionsSemantics (ls: list (Action type regs mems sends recvs (Bit 0))):
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
  Variable decls: ModDecl.
  Variable ls: forall ty,
      list (Action ty
              ((map (fun x => (fst x, regKind (snd x))) (modRegs decls)) ++ modRegUs decls)
              ((map (fun x => (fst x, memNatKind (snd x))) (modMems decls)) ++
                 map (fun x => (fst x, memUNatKind (snd x))) (modMemUs decls))
              (modSends decls)
              (modRecvs decls)
              (Bit 0)).

  Theorem CombineActionsTraceInclusion: TraceInclusion {|modDecls := decls;
                                                         modActions := fun ty => combineActions (ls ty) :: nil |}
                                                       {|modDecls := decls;
                                                         modActions := ls |}.
  Proof.
    econstructor 1 with
      (m1 := {| modDecls := decls; modActions := fun ty => combineActions (ls ty) :: nil |})
      (m2 := {| modDecls := decls; modActions := ls |})
      (traceSendsEq := eq_refl) (traceRecvsEq := eq_refl); auto; simpl; intros.
    apply combineActionsSemantics in H0.
    exists new1.
  Admitted.
End CombineActionsTraceInclusion.
