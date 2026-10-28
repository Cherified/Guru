(*
 * Copyright (c) 2025-2026 Cherified Systems LLC
 *
 * SPDX-License-Identifier: MIT
 *)

From Stdlib Require Import String List Bool ZArith Zmod Zmod.Bits.
From Guru Require Import Primitives Library Syntax Combinators Semantics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section InversionSemAction.
  Variable t: Tree DomainElem.
  Variable env: Env t.

  Theorem InversionSemAction
    k (a: @Action type t k) old new ret
    (semA: SemAction env a old new ret):
    match a with
    | ReadReg s x cont => SemAction env (cont (castStateReg x (readTreeState t old x.(regPath)))) old new ret
    | WriteReg x v cont =>
        SemAction env cont (writeTreeState t old x.(regPath) (castStateRegInv x (evalExpr v))) new ret
    | ReadRqMem x i p cont =>
        SemAction env
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           let val := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr.(Fst).(tupleElems) (getDefault _) in
           writeTreeState t old x.(memPath) (castStateMemInv x (arr.(Fst) ,, updSameTuple arr.(Snd) p val))) new ret
    | ReadRpMem s x p cont =>
        SemAction env (cont (readSameTuple (castStateMem x (readTreeState t old x.(memPath))).(Snd) p)) old new ret
    | WriteMem x i v cont =>
        SemAction env
          cont
          (let arr := castStateMem x (readTreeState t old x.(memPath)) in
           writeTreeState t old x.(memPath) (castStateMemInv x (updSameTupleNat arr.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v) ,, arr.(Snd)))) new ret
    | Send x v cont =>
        SemAction env cont
          (let currentTrace := castStateSend x (readTreeState t old x.(sendPath)) in
           writeTreeState t old x.(sendPath) (castStateSendInv x (evalExpr v :: currentTrace)))
          new ret
    | Recv s x cont =>
        exists recvVal,
        env old x recvVal /\
        SemAction env (cont recvVal)
          (let currentTrace := castStateRecv x (readTreeState t old x.(recvPath)) in
           writeTreeState t old x.(recvPath) (castStateRecvInv x (recvVal :: currentTrace)))
          new ret
    | LetExp s e cont =>
        SemAction env (cont (evalExpr e)) old new ret
    | LetAction s a' cont =>
        exists midState midRet,
        SemAction env a' old midState midRet /\
          SemAction env (cont midRet) midState new ret
    | NonDet s k' cont =>
        exists v,
        SemAction env (cont v) old new ret
    | IfElse s p t_branch f_branch cont =>
        exists midState midRet,
        (evalExpr p = true -> SemAction env t_branch old midState midRet) /\
          (evalExpr p = false -> SemAction env f_branch old midState midRet) /\
          SemAction env (cont midRet) midState new ret
    | System ls cont =>
        SemAction env cont old new ret
    | Return e =>
        new = old /\ ret = evalExpr e
    end.
  Proof.
    destruct semA; eauto; repeat eexists; eauto; try discriminate.
  Qed.
End InversionSemAction.


Section LetExpr.
  Variable t: Tree DomainElem.
  Variable env: Env t.

  Local Ltac destructAll := repeat (match goal with
                                    | H: exists _, _ |- _ => destruct H
                                    | H: _ /\ _ |- _ => destruct H
                                    end).

  Theorem SemActionLetExpr k (le: LetExpr type k):
    forall old new ret,
      SemAction env (@toAction _ t _ le) old new ret ->
      new = old /\ ret = (evalLetExpr le).
  Proof.
    induction le; simpl; intros;
      match goal with
      | H: SemAction _ _ _ _ _ |- _ => apply InversionSemAction in H
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

Theorem Zmod_or_0_l : forall w (x : bits w),
  Zmod.or Zmod.zero x = x.
Proof.
  intros w x; apply Zmod.unsigned_inj; rewrite bits.unsigned_or, Zmod.unsigned_0, Z.lor_0_l; reflexivity.
Qed.

Lemma evalBinaryArray_or_default :
  forall (k : Kind) (IHk : forall x : type k, evalOrBinary (getDefault k) x = x)
         (n : nat) (pf1 : Is_true (length (repeat (getDefault k) n) =? n))
         (elems : list (type k)) (pf2 : Is_true (length elems =? n)),
    evalBinaryArray (@evalOrBinary k)
      (@Build_SameTuple (type k) n (repeat (getDefault k) n) pf1)
      (@Build_SameTuple (type k) n elems pf2) =
    @Build_SameTuple (type k) n elems pf2.
Proof.
  intros k IHk.
  induction n as [| m IHm]; intros pf1 elems pf2.
  - destruct elems; [| contradiction].
    destruct pf2; reflexivity.
  - destruct elems as [| y ys]; [contradiction |].
    cbn -[evalOrBinary getDefault].
    rewrite IHk, IHm.
    reflexivity.
Qed.

Theorem evalOrBinary_getDefault_l :
  forall (k : Kind) (x : type k),
    evalOrBinary (getDefault k) x = x.
Proof.
  induction k using KindCustomInd; intros x.
  - reflexivity.
  - apply Zmod_or_0_l.
  - induction ls as [| [fname fk] xs IHxs].
    + destruct x; reflexivity.
    + destruct X as [Hx Hxs]; destruct x as [xf xs_val].
      cbn [evalOrBinary evalBinary KindCustomInd getDefault DiffTupleDefault evalBinaryStruct Fst Snd].
      f_equal; [apply Hx | apply (IHxs Hxs)].
  - destruct x as [elems pf2].
    unfold evalOrBinary, evalBinary; cbn [KindCustomInd getDefault SameTupleDefault];
      fold (@evalBinary orb (fun n0 : Z => @Zmod.or (2 ^ n0)) k);
      fold (@evalOrBinary k).
    apply (@evalBinaryArray_or_default k IHk).
  - destruct x as [f s].
    cbn [evalOrBinary evalBinary KindCustomInd getDefault Fst Snd].
    rewrite !Zmod_or_0_l; reflexivity.
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


Fixpoint InitStateConsistentPf (t: Tree DomainElem) : InitStateConsistent t (InitState t) :=
  match t return InitStateConsistent t (InitState t) with
  | Leaf name a => InitStateElemConsistentPf (snd a)
  | Node name children =>
      (fix loop (ls: list (Tree DomainElem)) :
         (fix loop (ls : list (Tree DomainElem)) : ListTreeState DomainElemState ls -> Prop :=
            match ls with
            | nil => fun _ => True
            | x :: xs => fun s => InitStateConsistent x s.(Fst) /\ loop xs s.(Snd)
            end) ls
           ((fix loop (ls : list (Tree DomainElem)) : ListTreeState DomainElemState ls :=
              match ls with
              | nil => tt
              | x :: xs => (InitState x ,, loop xs)
              end) ls) :=
         match ls return
           (fix loop (ls : list (Tree DomainElem)) : ListTreeState DomainElemState ls -> Prop :=
              match ls with
              | nil => fun _ => True
              | x :: xs => fun s => InitStateConsistent x s.(Fst) /\ loop xs s.(Snd)
              end) ls
             ((fix loop (ls : list (Tree DomainElem)) : ListTreeState DomainElemState ls :=
                match ls with
                | nil => tt
                | x :: xs => (InitState x ,, loop xs)
                end) ls)
         with
         | nil => I
         | x :: xs => conj (InitStateConsistentPf x) (loop xs)
         end) children
  end.

Definition ExistsInitStateConsistent (t: Tree DomainElem) : exists old, InitStateConsistent t old.
Proof.
  exists (InitState t).
  apply InitStateConsistentPf.
Qed.

Section ActionToModSimulation.
  Variable t1 t2: Tree DomainElem.
  Variable env1: Env t1.
  Variable env2: Env t2.
  Variable m1: Mod t1.
  Variable m2: Mod t2.
  Variable rel: TreeState DomainElemState t1 -> TreeState DomainElemState t2 -> Prop.
  Variable relConsistent: forall old1 old2,
      InitStateConsistent t1 old1 ->
      rel old1 old2 ->
      InitStateConsistent t2 old2.

  Variable actionSimulation: forall a1 old1 new1,
      In a1 (map snd (m1 type)) ->
      SemAction env1 a1 old1 new1 Zmod.zero ->
      forall old2: TreeState DomainElemState t2,
        rel old1 old2 ->
        exists a2 new2,
          In a2 (map snd (m2 type)) /\ SemAction env2 a2 old2 new2 Zmod.zero /\
          rel new1 new2.

  Lemma actionsSimulation: ActionsSimulation env1 env2 m1 m2 rel.
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

  Theorem ActionToModSimulation: ModSimulation env1 env2 m1 m2 rel.
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

  Variable initRel: forall old1 old2,
      InitStateConsistent t1 old1 ->
      InitStateConsistent t2 old2 ->
      rel old1 old2.

  Theorem ActionToModSimulationInit:
    ModSimulationInit env1 env2 m1 m2 rel initRel.
  Proof.
    intros old1 new1 H_sem old2 old2Consistent.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    pose proof (@initRel old1 old2 old1Consistent old2Consistent) as relOld.
    pose proof actionsSimulation as H_inc.
    unfold ActionsSimulation in H_inc.
    destruct (H_inc old1 old2 relOld new1 semAny1) as [new2 [semAny2 relNew2]].
    exists new2.
    split.
    - constructor; auto.
    - exact relNew2.
  Qed.
End ActionToModSimulation.

Section ModSimulationToInit.
  Variable t1 t2: Tree DomainElem.
  Variable env1: Env t1.
  Variable env2: Env t2.
  Variable m1: Mod t1.
  Variable m2: Mod t2.
  Variable rel: TreeState DomainElemState t1 -> TreeState DomainElemState t2 -> Prop.
  Variable initRel: forall old1 old2,
      InitStateConsistent t1 old1 ->
      InitStateConsistent t2 old2 ->
      rel old1 old2.

  Theorem ModSimulationToInit:
    ModSimulation env1 env2 m1 m2 rel ->
    ModSimulationInit env1 env2 m1 m2 rel initRel.
  Proof.
    intros Hsim old1 new1 Hsem1 old2 Hinit2.
    inversion Hsem1 as [? ? Hinit1 _]; subst.
    exact (Hsim old1 new1 Hsem1 old2 (initRel old1 old2 Hinit1 Hinit2)).
  Qed.
End ModSimulationToInit.

Section SemActionsProperties.
  Variable t: Tree DomainElem.
  Variable env: Env t.

  Lemma SemActions_subset: forall (ls1 ls2: list (Action type t (Bit 0))) old new,
      SemActions env ls1 old new ->
      (forall a, In a ls1 -> In a ls2) ->
      SemActions env ls2 old new.
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
      SemActions env m old mid ->
      SemActions env m mid new ->
      SemActions env m old new.
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

Fixpoint readTreeState_writeTreeState_eq {A : Type} {f : A -> Type} {t : Tree A} :
  forall (p : LeafPath t) (s : TreeState f t) (v : f (getLeaf p)),
    readTreeState t (writeTreeState t s p v) p = v.
Proof.
  destruct t as [name a | name children]; simpl; intros.
  - reflexivity.
  - induction children as [| x xs IHxs]; simpl in *.
    + destruct p.
    + destruct p as [px | pxs]; simpl.
      * apply readTreeState_writeTreeState_eq.
      * apply IHxs.
Qed.

Lemma castStateRecv_castStateRecvInv :
  forall {t : Tree DomainElem} (x : RecvPath t) (l : list (type (getRecvKind x))),
    castStateRecv x (castStateRecvInv x l) = l.
Proof.
  intros t x l.
  unfold castStateRecv, castStateRecvInv.
  destruct (getRecvFromPathTypeEq x); reflexivity.
Qed.

Lemma writeRecv_inj_val :
  forall {t : Tree DomainElem} (s : TreeState DomainElemState t)
         (x : RecvPath t) (v1 v2 : type (getRecvKind x)),
    writeRecv s x v1 = writeRecv s x v2 ->
    v1 = v2.
Proof.
  intros t s x v1 v2 Heq.
  apply (f_equal (fun st => castStateRecv x (readTreeState t st x.(recvPath)))) in Heq.
  unfold writeRecv in Heq.
  rewrite !readTreeState_writeTreeState_eq, !castStateRecv_castStateRecvInv in Heq.
  injection Heq; auto.
Qed.

Lemma EnvConsistent_eq_mono :
  forall {t : Tree DomainElem} (env1 env2 : Env t),
    EnvInhabited env2 ->
    EnvConsistent env1 env2 (fun s1 s2 => s1 = s2) ->
    forall s x v, env1 s x v -> env2 s x v.
Proof.
  intros t env1 env2 Hinh Hcons s x v Henv1.
  destruct (Hinh s x) as [v2 Henv2].
  pose proof (Hcons s s x x v v2 eq_refl Henv1 Henv2) as Heq.
  apply writeRecv_inj_val in Heq; subst v2; exact Henv2.
Qed.

Lemma SemAction_env_mono_early :
  forall {t : Tree DomainElem} (env1 env2 : Env t) {k : Kind} (a : @Action type t k)
         (old new : TreeState DomainElemState t) (ret : type k),
    (forall s x v, env1 s x v -> env2 s x v) ->
    SemAction env1 a old new ret ->
    SemAction env2 a old new ret.
Proof.
  intros t env1 env2 k a old new ret Hmono Hsem.
  induction Hsem; econstructor; eauto.
Qed.

Lemma SemActions_env_mono :
  forall {t : Tree DomainElem} (env1 env2 : Env t)
         (ls : list (Action type t (Bit 0)))
         (old new : TreeState DomainElemState t),
    (forall s x v, env1 s x v -> env2 s x v) ->
    SemActions env1 ls old new ->
    SemActions env2 ls old new.
Proof.
  intros t env1 env2 ls old new Hmono Hsem.
  induction Hsem.
  - subst; constructor 1; reflexivity.
  - econstructor 2.
    + exact inA.
    + eapply SemAction_env_mono_early; [exact Hmono | exact aPf].
    + exact IHHsem.
Qed.

Section ActionToActionsModSimulation.
  Variable t1 t2: Tree DomainElem.
  Variable env1: Env t1.
  Variable env2: Env t2.
  Variable m1: Mod t1.
  Variable m2: Mod t2.
  Variable rel: TreeState DomainElemState t1 -> TreeState DomainElemState t2 -> Prop.
  Variable relConsistent: forall old1 old2,
      InitStateConsistent t1 old1 ->
      rel old1 old2 ->
      InitStateConsistent t2 old2.

  Variable actionToActionsSimulation: forall a1 old1 new1,
      In a1 (map snd (m1 type)) ->
      SemAction env1 a1 old1 new1 Zmod.zero ->
      forall old2: TreeState DomainElemState t2,
        rel old1 old2 ->
        exists new2,
          SemActions env2 (map snd (m2 type)) old2 new2 /\
          rel new1 new2.

  Lemma actionsToActionsSimulation: ActionsSimulation env1 env2 m1 m2 rel.
  Proof.
    unfold ActionsSimulation.
    intros s1 old2 H s2 H_sems.
    revert old2 H.
    induction H_sems as [old_nil new_nil eqPf | old_cons new_cons midState a inA aPf rest IHrest]; intros.
    - subst.
      exists old2.
      split; [constructor 1; auto | exact H].
    - specialize (@actionToActionsSimulation a old_cons midState inA aPf old2 H) as H_act.
      destruct H_act as [midState2 [semActs2 relMidState2]].
      specialize (IHrest midState2 relMidState2) as [new2 [restActions relNew2]].
      exists new2.
      split; [| exact relNew2].
      eapply SemActions_trans; eauto.
  Qed.

  Theorem ActionToActionsModSimulation: ModSimulation env1 env2 m1 m2 rel.
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    pose proof (@relConsistent old1 old2 old1Consistent relOld) as old2Consistent.
    pose proof actionsToActionsSimulation as H_inc.
    unfold ActionsSimulation in H_inc.
    destruct (H_inc old1 old2 relOld new1 semAny1) as [new2 [semAny2 relNew2]].
    exists new2.
    split.
    - constructor; auto.
    - exact relNew2.
  Qed.

  Variable initRel: forall old1 old2,
      InitStateConsistent t1 old1 ->
      InitStateConsistent t2 old2 ->
      rel old1 old2.

  Theorem ActionToActionsModSimulationInit:
    ModSimulationInit env1 env2 m1 m2 rel initRel.
  Proof.
    intros old1 new1 H_sem old2 old2Consistent.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    pose proof (@initRel old1 old2 old1Consistent old2Consistent) as relOld.
    pose proof actionsToActionsSimulation as H_inc.
    unfold ActionsSimulation in H_inc.
    destruct (H_inc old1 old2 relOld new1 semAny1) as [new2 [semAny2 relNew2]].
    exists new2.
    split.
    - constructor; auto.
    - exact relNew2.
  Qed.
End ActionToActionsModSimulation.

Section SubsetActionModSimulation.
  Variable t: Tree DomainElem.
  Variable env1 env2: Env t.
  Variable m1 m2: Mod t.
  Variable env2Exists: EnvInhabited env2.
  Variable envConsistent: EnvConsistent env1 env2 (fun s1 s2 => s1 = s2).
  Variable H_inc: forall ty a, In a (map snd (m1 ty)) -> In a (map snd (m2 ty)).

  Theorem SubsetActionModSimulation:
    ModSimulation env1 env2 m1 m2 (fun s1 s2 => s1 = s2).
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    subst old2.
    exists new1.
    split; [| reflexivity].
    constructor; auto.
    eapply SemActions_env_mono; [eapply EnvConsistent_eq_mono; eauto |].
    apply SemActions_subset with (ls1 := map snd (m1 type)); auto.
  Qed.
End SubsetActionModSimulation.

Section CombineActionsHelpers.
  Variable t: Tree DomainElem.
  Variable env: Env t.

  Lemma addSemActions ls old new:
    SemActions env ls old new ->
    forall (a: @Action type t (Bit 0)),
      SemActions env (a :: ls) old new.
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
      SemAction env (combineActions ls) old new Zmod.zero ->
      SemActions env ls old new.
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
        SemActions env ls old new1 ->
        SemActions env ls new1 new2 ->
        SemActions env ls old new2.
    Proof.
      induction 1 as [old_nil new_nil eqPf | old_cons new_cons midState a inA aPf rest IHrest]; intros.
      - subst.
        exact H.
      - econstructor 2 with (midState := midState); eauto.
    Qed.
  End CombineSemActions.

  Lemma combineActionsSemantics (ls: list (@Action type t (Bit 0))):
    forall old new,
      SemActions env (combineActions ls :: nil) old new ->
      SemActions env ls old new.
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
  Variable t: Tree DomainElem.
  Variable env1 env2: Env t.
  Variable d: string.
  Variable ls: forall ty, list (@Action ty t (Bit 0)).
  Variable env2Exists: EnvInhabited env2.
  Variable envConsistent: EnvConsistent env1 env2 (fun s1 s2 => s1 = s2).

  Theorem CombineActionsModSimulation:
    ModSimulation env1 env2
                  (fun ty => (d, combineActions (ls ty)) :: nil)
                  (fun ty => map (fun a => (d, a)) (ls ty))
                  (fun s1 s2 => s1 = s2).
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    subst old2.
    simpl in semAny1.
    apply combineActionsSemantics in semAny1.
    exists new1.
    split.
    - constructor; auto.
      rewrite map_map. simpl.
      rewrite map_id.
      eapply SemActions_env_mono; [eapply EnvConsistent_eq_mono; eauto | exact semAny1].
    - reflexivity.
  Qed.
End CombineActionsTraceSimulation.

Fixpoint nubStrings (ls : list string) : list string :=
  match ls with
  | nil => nil
  | x :: xs =>
      if existsb (String.eqb x) xs
      then nubStrings xs
      else x :: nubStrings xs
  end.

Definition extractDomains {A} (ls : list (string * A)) : list string :=
  nubStrings (map fst ls).

Definition actionsOfDomain {A} (d : string) (ls : list (string * A)) : list A :=
  map snd (filter (fun p => String.eqb (fst p) d) ls).

Definition combineByDomain {t : Tree DomainElem} (m : Mod t) : Mod t :=
  fun ty =>
    let doms := extractDomains (m ty) in
    map (fun d => (d, combineActions (actionsOfDomain d (m ty)))) doms.

Section CombineByDomainSimulation.
  Variable t : Tree DomainElem.
  Variable env1 env2 : Env t.
  Variable m : Mod t.
  Variable env2Exists: EnvInhabited env2.
  Variable envConsistent: EnvConsistent env1 env2 (fun s1 s2 => s1 = s2).

  Lemma in_actionsOfDomain:
    forall A d (a : A) ls,
      In a (actionsOfDomain d ls) ->
      In a (map snd ls).
  Proof.
    intros A d a ls H.
    unfold actionsOfDomain in H.
    apply in_map_iff in H as [[d' a'] [Heq Hin]].
    simpl in Heq; subst a'.
    apply filter_In in Hin as [Hin _].
    apply in_map_iff.
    exists (d', a); auto.
  Qed.

  Lemma combineByDomainActions_to_SemActions:
    forall (env : Env t) old new,
      SemActions env (map snd (combineByDomain m type)) old new ->
      SemActions env (map snd (m type)) old new.
  Proof.
    intros env old new H.
    induction H as [old_nil new_nil eqPf | old_cons new_cons midState a inA aPf rest IHrest].
    - subst; constructor 1; reflexivity.
    - unfold combineByDomain in inA.
      rewrite map_map in inA.
      simpl in inA.
      apply in_map_iff in inA as [d [Heq HinD]].
      subst a.
      apply combineSemActionToSemActions in aPf.
      assert (Hsub: SemActions env (map snd (m type)) old_cons midState).
      { eapply SemActions_subset; [exact aPf |].
        intros a' HinA'.
        eapply in_actionsOfDomain; exact HinA'. }
      eapply SemActions_trans; [exact Hsub | exact IHrest].
  Qed.

  Theorem CombineByDomainModSimulation:
    ModSimulation env1 env2 (combineByDomain m) m (fun s1 s2 => s1 = s2).
  Proof.
    intros old1 new1 H_sem old2 relOld.
    destruct H_sem as [old1 new1 old1Consistent semAny1].
    subst old2.
    exists new1.
    split; [| reflexivity].
    constructor; [exact old1Consistent |].
    eapply SemActions_env_mono; [eapply EnvConsistent_eq_mono; eauto |].
    apply combineByDomainActions_to_SemActions.
    exact semAny1.
  Qed.
End CombineByDomainSimulation.
