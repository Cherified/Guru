From Stdlib Require Import List String Zmod.
Import ListNotations.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Theorems Guru.ComposableModules.
From Stdlib Require Import Program.Equality.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Composition.
  Variable t_outer t_inner : Tree Elem.

  Definition t_comb : Tree Elem := Node "" [t_outer; t_inner].

  Definition liftRegPathOuter (x: RegPath t_outer) : RegPath t_comb :=
    {| regPath := (inl x.(regPath) : LeafPath t_comb); regPathPf := x.(regPathPf) |}.

  Definition liftRegPathInner (x: RegPath t_inner) : RegPath t_comb :=
    {| regPath := (inr (inl x.(regPath)) : LeafPath t_comb); regPathPf := x.(regPathPf) |}.

  Definition liftMemPathOuter (x: MemPath t_outer) : MemPath t_comb :=
    {| memPath := (inl x.(memPath) : LeafPath t_comb); memPathPf := x.(memPathPf) |}.

  Definition liftMemPathInner (x: MemPath t_inner) : MemPath t_comb :=
    {| memPath := (inr (inl x.(memPath)) : LeafPath t_comb); memPathPf := x.(memPathPf) |}.

  Definition liftSendPathOuter (x: SendPath t_outer) : SendPath t_comb :=
    {| sendPath := (inl x.(sendPath) : LeafPath t_comb); sendPathPf := x.(sendPathPf) |}.

  Definition liftSendPathInner (x: SendPath t_inner) : SendPath t_comb :=
    {| sendPath := (inr (inl x.(sendPath)) : LeafPath t_comb); sendPathPf := x.(sendPathPf) |}.

  Definition liftRecvPathOuter (x: RecvPath t_outer) : RecvPath t_comb :=
    {| recvPath := (inl x.(recvPath) : LeafPath t_comb); recvPathPf := x.(recvPathPf) |}.

  Definition liftRecvPathInner (x: RecvPath t_inner) : RecvPath t_comb :=
    {| recvPath := (inr (inl x.(recvPath)) : LeafPath t_comb); recvPathPf := x.(recvPathPf) |}.

  Section Lift.
    Variable ty : Kind -> Type.

    Fixpoint liftActionOuter {k} (a: Action ty t_outer k) : Action ty t_comb k :=
      match a with
      | ReadReg s x cont => ReadReg s (liftRegPathOuter x) (fun v => liftActionOuter (cont v))
      | WriteReg x v cont => WriteReg (liftRegPathOuter x) v (liftActionOuter cont)
      | ReadRqMem x i p cont => ReadRqMem (liftMemPathOuter x) i p (liftActionOuter cont)
      | ReadRpMem s x p cont => ReadRpMem s (liftMemPathOuter x) p (fun v => liftActionOuter (cont v))
      | WriteMem x i v cont => WriteMem (liftMemPathOuter x) i v (liftActionOuter cont)
      | Send x v cont => Send (liftSendPathOuter x) v (liftActionOuter cont)
      | Recv s x cont => Recv s (liftRecvPathOuter x) (fun v => liftActionOuter (cont v))
      | LetExp s k' e cont => LetExp s e (fun v => liftActionOuter (cont v))
      | LetAction s k' a' cont => LetAction s (liftActionOuter a') (fun v => liftActionOuter (cont v))
      | NonDet s k' cont => NonDet s k' (fun v => liftActionOuter (cont v))
      | IfElse s p k' t_br f_br cont => IfElse s p (liftActionOuter t_br) (liftActionOuter f_br) (fun v => liftActionOuter (cont v))
      | System ls cont => System ls (liftActionOuter cont)
      | Return e => Return e
      end.

    Fixpoint liftActionInner {k} (a: Action ty t_inner k) : Action ty t_comb k :=
      match a with
      | ReadReg s x cont => ReadReg s (liftRegPathInner x) (fun v => liftActionInner (cont v))
      | WriteReg x v cont => WriteReg (liftRegPathInner x) v (liftActionInner cont)
      | ReadRqMem x i p cont => ReadRqMem (liftMemPathInner x) i p (liftActionInner cont)
      | ReadRpMem s x p cont => ReadRpMem s (liftMemPathInner x) p (fun v => liftActionInner (cont v))
      | WriteMem x i v cont => WriteMem (liftMemPathInner x) i v (liftActionInner cont)
      | Send x v cont => Send (liftSendPathInner x) v (liftActionInner cont)
      | Recv s x cont => Recv s (liftRecvPathInner x) (fun v => liftActionInner (cont v))
      | LetExp s k' e cont => LetExp s e (fun v => liftActionInner (cont v))
      | LetAction s k' a' cont => LetAction s (liftActionInner a') (fun v => liftActionInner (cont v))
      | NonDet s k' cont => NonDet s k' (fun v => liftActionInner (cont v))
      | IfElse s p k' t_br f_br cont => IfElse s p (liftActionInner t_br) (liftActionInner f_br) (fun v => liftActionInner (cont v))
      | System ls cont => System ls (liftActionInner cont)
      | Return e => Return e
      end.
  End Lift.

  Definition composeModules (isPrepend : bool)
                           (m_outer: Mod t_outer)
                           (m_inner_internal: Mod t_inner) : Mod t_comb :=
    fun ty =>
      let liftedOuter := map (@liftActionOuter ty (Bit 0)) (m_outer ty) in
      let liftedInner := map (@liftActionInner ty (Bit 0)) (m_inner_internal ty) in
      if isPrepend
      then liftedInner ++ liftedOuter
      else liftedOuter ++ liftedInner.

  Lemma liftActionOuter_preserves_sem: forall k (a: Action type t_outer k) s_out s_out' ret,
      SemAction a s_out s_out' ret ->
      forall s_in,
        SemAction (liftActionOuter a) (s_out ,, (s_in ,, tt)) (s_out' ,, (s_in ,, tt)) ret.
  Proof.
    intros k a.
    induction a; intros s_out s_out' ret Hsem s_in.
    - (* ReadReg *)
      dependent destruction Hsem; simpl in *.
      change (getRegFromPath (liftRegPathOuter x)) with (getRegFromPath x).
      unfold liftRegPathOuter, castStateReg, castStateRegInv in *.
      constructor 1; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* WriteReg *)
      dependent destruction Hsem; simpl in *.
      unfold liftRegPathOuter, castStateReg, castStateRegInv in *.
      constructor 2; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* ReadRqMem *)
      dependent destruction Hsem; simpl in *.
      unfold liftMemPathOuter, castStateMem, castStateMemInv in *.
      constructor 3; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* ReadRpMem *)
      dependent destruction Hsem; simpl in *.
      change (getMemFromPath (liftMemPathOuter x)) with (getMemFromPath x).
      unfold liftMemPathOuter, castStateMem, castStateMemInv in *.
      constructor 4; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* WriteMem *)
      dependent destruction Hsem; simpl in *.
      unfold liftMemPathOuter, castStateMem, castStateMemInv in *.
      constructor 5; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* Send *)
      dependent destruction Hsem; simpl in *.
      change (getSendKind (liftSendPathOuter x)) with (getSendKind x).
      unfold liftSendPathOuter, castStateSend, castStateSendInv in *.
      constructor 6; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* Recv *)
      dependent destruction Hsem; simpl in *.
      change (getRecvKind (liftRecvPathOuter x)) with (getRecvKind x).
      unfold liftRecvPathOuter, castStateRecv, castStateRecvInv in *.
      econstructor 7; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* LetExp *)
      dependent destruction Hsem; simpl in *.
      constructor 8; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* LetAction *)
      dependent destruction Hsem; simpl in *.
      econstructor 9; simpl.
      + apply IHa; eassumption.
      + apply H; eassumption.
    - (* NonDet *)
      dependent destruction Hsem; simpl in *.
      econstructor 10; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* IfElse *)
      dependent destruction Hsem; simpl in *.
      econstructor 11; simpl.
      + intros; apply IHa1; auto.
      + intros; apply IHa2; auto.
      + apply H; eassumption.
    - (* System *)
      dependent destruction Hsem; simpl in *.
      constructor 12; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* Return *)
      dependent destruction Hsem; simpl in *.
      constructor 13; auto.
  Qed.

  Lemma liftActionInner_preserves_sem: forall k (a: Action type t_inner k) s_in s_in' ret,
      SemAction a s_in s_in' ret ->
      forall s_out,
        SemAction (liftActionInner a) (s_out ,, (s_in ,, tt)) (s_out ,, (s_in' ,, tt)) ret.
  Proof.
    intros k a.
    induction a; intros s_in s_in' ret Hsem s_out.
    - (* ReadReg *)
      dependent destruction Hsem; simpl in *.
      change (getRegFromPath (liftRegPathInner x)) with (getRegFromPath x).
      unfold liftRegPathInner, castStateReg, castStateRegInv in *.
      constructor 1; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* WriteReg *)
      dependent destruction Hsem; simpl in *.
      unfold liftRegPathInner, castStateReg, castStateRegInv in *.
      constructor 2; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* ReadRqMem *)
      dependent destruction Hsem; simpl in *.
      unfold liftMemPathInner, castStateMem, castStateMemInv in *.
      constructor 3; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* ReadRpMem *)
      dependent destruction Hsem; simpl in *.
      change (getMemFromPath (liftMemPathInner x)) with (getMemFromPath x).
      unfold liftMemPathInner, castStateMem, castStateMemInv in *.
      constructor 4; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* WriteMem *)
      dependent destruction Hsem; simpl in *.
      unfold liftMemPathInner, castStateMem, castStateMemInv in *.
      constructor 5; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* Send *)
      dependent destruction Hsem; simpl in *.
      change (getSendKind (liftSendPathInner x)) with (getSendKind x).
      unfold liftSendPathInner, castStateSend, castStateSendInv in *.
      constructor 6; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* Recv *)
      dependent destruction Hsem; simpl in *.
      change (getRecvKind (liftRecvPathInner x)) with (getRecvKind x).
      unfold liftRecvPathInner, castStateRecv, castStateRecvInv in *.
      econstructor 7; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* LetExp *)
      dependent destruction Hsem; simpl in *.
      constructor 8; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* LetAction *)
      dependent destruction Hsem; simpl in *.
      econstructor 9; simpl.
      + apply IHa; eassumption.
      + apply H; eassumption.
    - (* NonDet *)
      dependent destruction Hsem; simpl in *.
      econstructor 10; simpl; apply H; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* IfElse *)
      dependent destruction Hsem; simpl in *.
      econstructor 11; simpl.
      + intros; apply IHa1; auto.
      + intros; apply IHa2; auto.
      + apply H; eassumption.
    - (* System *)
      dependent destruction Hsem; simpl in *.
      constructor 12; simpl; apply IHa; match goal with | H : SemAction _ _ _ _ |- _ => exact H end.
    - (* Return *)
      dependent destruction Hsem; simpl in *.
      constructor 13; auto.
  Qed.

  Lemma composeModules_In: forall (isPrepend: bool) (m_outer: Mod t_outer) (child: Mod t_inner) a,
      In a (composeModules isPrepend m_outer child type) ->
      (exists a_inner, In a_inner (child type) /\ a = liftActionInner a_inner) \/
      (exists a_outer, In a_outer (m_outer type) /\ a = liftActionOuter a_outer).
  Proof.
    intros isPrepend m_outer child a H.
    unfold composeModules in H.
    destruct isPrepend.
    - apply in_app_or in H.
      destruct H.
      + apply in_map_iff in H.
        destruct H as [a_inner [H1 H2]].
        left. exists a_inner. auto.
      + apply in_map_iff in H.
        destruct H as [a_outer [H1 H2]].
        right. exists a_outer. auto.
    - apply in_app_or in H.
      destruct H.
      + apply in_map_iff in H.
        destruct H as [a_outer [H1 H2]].
        right. exists a_outer. auto.
      + apply in_map_iff in H.
        destruct H as [a_inner [H1 H2]].
        left. exists a_inner. auto.
  Qed.

  Lemma liftActionOuter_reflects_sem: forall k (a: Action type t_outer k) s_out s_in s' ret,
      SemAction (liftActionOuter a) (s_out ,, (s_in ,, tt)) s' ret ->
      exists s_out', s' = (s_out' ,, (s_in ,, tt)) /\ SemAction a s_out s_out' ret.
  Proof.
    intros k a.
    induction a; intros s_out s_in s' ret Hsem.
    - (* ReadReg *)
      dependent destruction Hsem; simpl in *.
      change (getRegFromPath (liftRegPathOuter x)) with (getRegFromPath x) in *.
      unfold liftRegPathOuter, castStateReg, castStateRegInv in *.
      apply H in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      constructor 1; auto.
    - (* WriteReg *)
      dependent destruction Hsem; simpl in *.
      unfold liftRegPathOuter, castStateReg, castStateRegInv in *.
      apply IHa in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      constructor 2; auto.
    - (* ReadRqMem *)
      dependent destruction Hsem; simpl in *.
      unfold liftMemPathOuter, castStateMem, castStateMemInv in *.
      apply IHa in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      constructor 3; auto.
    - (* ReadRpMem *)
      dependent destruction Hsem; simpl in *.
      change (getMemFromPath (liftMemPathOuter x)) with (getMemFromPath x) in *.
      unfold liftMemPathOuter, castStateMem, castStateMemInv in *.
      apply H in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      constructor 4; auto.
    - (* WriteMem *)
      dependent destruction Hsem; simpl in *.
      unfold liftMemPathOuter, castStateMem, castStateMemInv in *.
      apply IHa in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      constructor 5; auto.
    - (* Send *)
      dependent destruction Hsem; simpl in *.
      change (getSendKind (liftSendPathOuter x)) with (getSendKind x) in *.
      unfold liftSendPathOuter, castStateSend, castStateSendInv in *.
      apply IHa in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      constructor 6; auto.
    - (* Recv *)
      dependent destruction Hsem; simpl in *.
      change (getRecvKind (liftRecvPathOuter x)) with (getRecvKind x) in *.
      unfold liftRecvPathOuter, castStateRecv, castStateRecvInv in *.
      apply H in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      econstructor 7; eauto.
    - (* LetExp *)
      dependent destruction Hsem; simpl in *.
      apply H in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      constructor 8; auto.
    - (* LetAction *)
      dependent destruction Hsem; simpl in *.
      apply IHa in Hsem1.
      destruct Hsem1 as [mid_out [H1 H2]].
      subst.
      apply H in Hsem2.
      destruct Hsem2 as [s_out' [H3 H4]].
      subst.
      exists s_out'.
      split; auto.
      econstructor 9; eauto.
    - (* NonDet *)
      dependent destruction Hsem; simpl in *.
      apply H in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      econstructor 10; eauto.
    - (* IfElse *)
      dependent destruction Hsem; simpl in *.
      destruct (evalExpr p) eqn:Heq.
      + assert (Hact: SemAction (liftActionOuter a1) (s_out,, (s_in,, tt)) midState midRet) by (apply tPf; auto).
        apply IHa1 in Hact.
        destruct Hact as [s_out' [H1 H2]].
        subst.
        apply H in Hsem.
        destruct Hsem as [s_out'' [H3 H4]].
        subst.
        exists s_out''.
        split; auto.
        econstructor 11.
        * intros H_true. exact H2.
        * intros H_false. rewrite Heq in H_false. discriminate.
        * exact H4.
      + assert (Hact: SemAction (liftActionOuter a2) (s_out,, (s_in,, tt)) midState midRet) by (apply fPf; auto).
        apply IHa2 in Hact.
        destruct Hact as [s_out' [H1 H2]].
        subst.
        apply H in Hsem.
        destruct Hsem as [s_out'' [H3 H4]].
        subst.
        exists s_out''.
        split; auto.
        econstructor 11.
        * intros H_true. rewrite Heq in H_true. discriminate.
        * intros H_false. exact H2.
        * exact H4.
    - (* System *)
      dependent destruction Hsem; simpl in *.
      apply IHa in Hsem.
      destruct Hsem as [s_out' [H1 H2]].
      subst.
      exists s_out'.
      split; auto.
      constructor 12; auto.
    - (* Return *)
      dependent destruction Hsem; simpl in *.
      exists s_out.
      split; auto.
      constructor 13; auto.
  Qed.

  Lemma liftActionInner_reflects_sem: forall k (a: Action type t_inner k) s_out s_in s' ret,
      SemAction (liftActionInner a) (s_out ,, (s_in ,, tt)) s' ret ->
      exists s_in', s' = (s_out ,, (s_in' ,, tt)) /\ SemAction a s_in s_in' ret.
  Proof.
    intros k a.
    induction a; intros s_out s_in s' ret Hsem.
    - (* ReadReg *)
      dependent destruction Hsem; simpl in *.
      change (getRegFromPath (liftRegPathInner x)) with (getRegFromPath x) in *.
      unfold liftRegPathInner, castStateReg, castStateRegInv in *.
      apply H in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      constructor 1; auto.
    - (* WriteReg *)
      dependent destruction Hsem; simpl in *.
      unfold liftRegPathInner, castStateReg, castStateRegInv in *.
      apply IHa in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      constructor 2; auto.
    - (* ReadRqMem *)
      dependent destruction Hsem; simpl in *.
      unfold liftMemPathInner, castStateMem, castStateMemInv in *.
      apply IHa in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      constructor 3; auto.
    - (* ReadRpMem *)
      dependent destruction Hsem; simpl in *.
      change (getMemFromPath (liftMemPathInner x)) with (getMemFromPath x) in *.
      unfold liftMemPathInner, castStateMem, castStateMemInv in *.
      apply H in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      constructor 4; auto.
    - (* WriteMem *)
      dependent destruction Hsem; simpl in *.
      unfold liftMemPathInner, castStateMem, castStateMemInv in *.
      apply IHa in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      constructor 5; auto.
    - (* Send *)
      dependent destruction Hsem; simpl in *.
      change (getSendKind (liftSendPathInner x)) with (getSendKind x) in *.
      unfold liftSendPathInner, castStateSend, castStateSendInv in *.
      apply IHa in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      constructor 6; auto.
    - (* Recv *)
      dependent destruction Hsem; simpl in *.
      change (getRecvKind (liftRecvPathInner x)) with (getRecvKind x) in *.
      unfold liftRecvPathInner, castStateRecv, castStateRecvInv in *.
      apply H in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      econstructor 7; eauto.
    - (* LetExp *)
      dependent destruction Hsem; simpl in *.
      apply H in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      constructor 8; auto.
    - (* LetAction *)
      dependent destruction Hsem; simpl in *.
      apply IHa in Hsem1.
      destruct Hsem1 as [mid_in [H1 H2]].
      subst.
      apply H in Hsem2.
      destruct Hsem2 as [s_in' [H3 H4]].
      subst.
      exists s_in'.
      split; auto.
      econstructor 9; eauto.
    - (* NonDet *)
      dependent destruction Hsem; simpl in *.
      apply H in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      econstructor 10; eauto.
    - (* IfElse *)
      dependent destruction Hsem; simpl in *.
      destruct (evalExpr p) eqn:Heq.
      + assert (Hact: SemAction (liftActionInner a1) (s_out,, (s_in,, tt)) midState midRet) by (apply tPf; auto).
        apply IHa1 in Hact.
        destruct Hact as [s_in' [H1 H2]].
        subst.
        apply H in Hsem.
        destruct Hsem as [s_in'' [H3 H4]].
        subst.
        exists s_in''.
        split; auto.
        econstructor 11.
        * intros H_true. exact H2.
        * intros H_false. rewrite Heq in H_false. discriminate.
        * exact H4.
      + assert (Hact: SemAction (liftActionInner a2) (s_out,, (s_in,, tt)) midState midRet) by (apply fPf; auto).
        apply IHa2 in Hact.
        destruct Hact as [s_in' [H1 H2]].
        subst.
        apply H in Hsem.
        destruct Hsem as [s_in'' [H3 H4]].
        subst.
        exists s_in''.
        split; auto.
        econstructor 11.
        * intros H_true. rewrite Heq in H_true. discriminate.
        * intros H_false. exact H2.
        * exact H4.
    - (* System *)
      dependent destruction Hsem; simpl in *.
      apply IHa in Hsem.
      destruct Hsem as [s_in' [H1 H2]].
      subst.
      exists s_in'.
      split; auto.
      constructor 12; auto.
    - (* Return *)
      dependent destruction Hsem; simpl in *.
      exists s_in.
      split; auto.
      constructor 13; auto.
  Qed.

  Lemma composeModules_project_outer: forall isPrepend (m_outer: Mod t_outer) (child: Mod t_inner) old new,
      SemActions (composeModules isPrepend m_outer child type) old new ->
      SemActions (m_outer type) old.(Fst) new.(Fst).
  Proof.
    intros isPrepend m_outer child old new H.
    induction H.
    - subst.
      destruct old as [old_out [old_in []]].
      constructor 1.
      reflexivity.
    - destruct old as [old_out [old_in []]].
      destruct midState as [ns_out [ns_in []]].
      destruct new as [new_out [new_in []]].
      apply composeModules_In in inA.
      destruct inA as [[a_inner [Hin_inner Heq]] | [a_outer [Hin_outer Heq]]].
      + subst a.
         apply liftActionInner_reflects_sem in aPf.
         destruct aPf as [s_in' [Heq_midState aPf]].
         inversion Heq_midState; subst ns_out ns_in.
         simpl in *.
         exact IHSemActions.
      + subst a.
         apply liftActionOuter_reflects_sem in aPf.
         destruct aPf as [s_out' [Heq_midState aPf]].
         inversion Heq_midState; subst ns_out ns_in.
         simpl in *.
         econstructor 2.
         * exact Hin_outer.
         * exact aPf.
         * exact IHSemActions.
  Qed.

  Lemma composeModules_project_inner: forall isPrepend (m_outer: Mod t_outer) (child: Mod t_inner) old new,
      SemActions (composeModules isPrepend m_outer child type) old new ->
      SemActions (child type) old.(Snd).(Fst) new.(Snd).(Fst).
  Proof.
    intros isPrepend m_outer child old new H.
    induction H.
    - subst.
      destruct old as [old_out [old_in []]].
      constructor 1.
      reflexivity.
    - destruct old as [old_out [old_in []]].
      destruct midState as [ns_out [ns_in []]].
      destruct new as [new_out [new_in []]].
      apply composeModules_In in inA.
      destruct inA as [[a_inner [Hin_inner Heq]] | [a_outer [Hin_outer Heq]]].
      + subst a.
         apply liftActionInner_reflects_sem in aPf.
         destruct aPf as [s_in' [Heq_midState aPf]].
         inversion Heq_midState; subst ns_out ns_in.
         simpl in *.
         econstructor 2.
         * exact Hin_inner.
         * exact aPf.
         * exact IHSemActions.
      + subst a.
         apply liftActionOuter_reflects_sem in aPf.
         destruct aPf as [s_out' [Heq_midState aPf]].
         inversion Heq_midState; subst ns_out ns_in.
         simpl in *.
         exact IHSemActions.
  Qed.

  Lemma liftActionOuter_preserves_semActions: forall (m: list (Action type t_outer (Bit 0))) old new,
      SemActions m old new ->
      forall s_in,
        SemActions (map (@liftActionOuter type (Bit 0)) m) (old ,, (s_in ,, tt)) (new ,, (s_in ,, tt)).
  Proof.
    intros m old new H.
    induction H; intros s_in; simpl in *.
    - subst.
      constructor 1.
      reflexivity.
    - econstructor 2.
      + apply in_map. exact inA.
      + apply liftActionOuter_preserves_sem. exact aPf.
      + apply IHSemActions.
  Qed.

  Lemma liftActionInner_preserves_semActions: forall (m: list (Action type t_inner (Bit 0))) old new,
      SemActions m old new ->
      forall s_out,
        SemActions (map (@liftActionInner type (Bit 0)) m) (s_out ,, (old ,, tt)) (s_out ,, (new ,, tt)).
  Proof.
    intros m old new H.
    induction H; intros s_out; simpl in *.
    - subst.
      constructor 1.
      reflexivity.
    - econstructor 2.
      + apply in_map. exact inA.
      + apply liftActionInner_preserves_sem. exact aPf.
      + apply IHSemActions.
  Qed.
End Composition.

Definition instantiate_mod (mt : ModuleType) (t_acc : Tree Elem) (t_new : Tree Elem)
                           (F : ModuleSem (BindMod mt) t_acc t_new)
                           (child : Mod t_new) :
  ModuleSem mt (Node "" [t_acc; t_new]) t_new :=
  F t_new child.

Definition instantiate_meth (mt : ModuleType) (t_acc : Tree Elem) (t_curr : Tree Elem) (K_in K_out : Kind)
                            (F : ModuleSem (BindMeth K_in K_out mt) t_acc t_curr)
                            (meth : type K_in -> Action type t_curr K_out) :
  ModuleSem mt t_acc t_curr :=
  F meth.

Theorem Simulation_instantiate_mod :
  forall (mt : ModuleType) (t_acc1 t_acc2 : Tree Elem) (t_new1 t_new2 : Tree Elem)
         (rel_acc : TreeState ElemState t_acc1 -> TreeState ElemState t_acc2 -> Prop)
         (rel_new : TreeState ElemState t_new1 -> TreeState ElemState t_new2 -> Prop)
         (F1 : ModuleSem (BindMod mt) t_acc1 t_new1)
         (F2 : ModuleSem (BindMod mt) t_acc2 t_new2)
         (child1 : Mod t_new1) (child2 : Mod t_new2),
    Simulation (BindMod mt) t_acc1 t_acc2 rel_acc t_new1 t_new2 rel_new F1 F2 ->
    ModSimulation child1 child2 rel_new ->
    Simulation mt (Node "" [t_acc1; t_new1]) (Node "" [t_acc2; t_new2])
        (fun s1 s2 => rel_acc s1.(Fst) s2.(Fst) /\ rel_new s1.(Snd).(Fst) s2.(Snd).(Fst))
        t_new1 t_new2
        rel_new
        (instantiate_mod F1 child1)
        (instantiate_mod F2 child2).
Proof.
  intros mt t_acc1 t_acc2 t_new1 t_new2 rel_acc rel_new F1 F2 child1 child2 Hrel Hsim.
  unfold instantiate_mod.
  apply (Hrel t_new1 t_new2 child1 child2 rel_new Hsim).
Qed.

Theorem Simulation_instantiate_meth (mt : ModuleType) (t_acc1 t_acc2 : Tree Elem) (t_curr1 t_curr2 : Tree Elem)
                              (rel_acc : TreeState ElemState t_acc1 -> TreeState ElemState t_acc2 -> Prop)
                              (rel_curr : TreeState ElemState t_curr1 -> TreeState ElemState t_curr2 -> Prop)
                              (K_in K_out : Kind)
                              (F1 : ModuleSem (BindMeth K_in K_out mt) t_acc1 t_curr1)
                              (F2 : ModuleSem (BindMeth K_in K_out mt) t_acc2 t_curr2)
                              (meth1 : type K_in -> Action type t_curr1 K_out) (meth2 : type K_in -> Action type t_curr2 K_out) :
  Simulation (BindMeth K_in K_out mt) t_acc1 t_acc2 rel_acc t_curr1 t_curr2 rel_curr F1 F2 ->
  MethSimulation meth1 meth2 rel_curr ->
  Simulation mt t_acc1 t_acc2 rel_acc t_curr1 t_curr2 rel_curr
      (instantiate_meth F1 meth1)
      (instantiate_meth F2 meth2).
Proof.
  intros Hrel Hsim.
  apply (Hrel meth1 meth2 Hsim).
Qed.

Theorem Simulation_composeModules :
  forall (isPrepend1 isPrepend2 : bool)
         (t_acc1 t_acc2 : Tree Elem)
         (rel_acc : TreeState ElemState t_acc1 -> TreeState ElemState t_acc2 -> Prop)
         (m_outer1 : Mod t_acc1) (m_outer2 : Mod t_acc2),
  ModSimulation m_outer1 m_outer2 rel_acc ->
  forall (t_curr1 t_curr2 : Tree Elem)
         (rel_curr : TreeState ElemState t_curr1 -> TreeState ElemState t_curr2 -> Prop),
  Simulation (BindMod MkMod) t_acc1 t_acc2 rel_acc t_curr1 t_curr2 rel_curr
      (fun t child => composeModules isPrepend1 m_outer1 child)
      (fun t child => composeModules isPrepend2 m_outer2 child).
Proof.
  intros isPrepend1 isPrepend2 t_acc1 t_acc2 rel_acc m_outer1 m_outer2 Houter.
  intros t_curr1 t_curr2 rel_curr.
  simpl.
  intros t1 t2 child1 child2 rel_in Hinner.
  intros old1 new1 Hmod1 old2 Hrel_old.
  inversion Hmod1; subst.
  destruct initGood as [initGood_outer [initGood_inner _]].
  destruct Hrel_old as [Hrel_acc Hrel_in].
  destruct old1 as [old1_out [old1_in []]].
  destruct old2 as [old2_out [old2_in []]].
  destruct new1 as [new1_out [new1_in []]].
  simpl in *.
  assert (actions_outer : SemActions (m_outer1 type) old1_out new1_out) by (apply (composeModules_project_outer isPrepend1 m_outer1 child1) with (old:=(old1_out ,, (old1_in ,, tt))) (new:=(new1_out ,, (new1_in ,, tt))); exact actions).
  assert (actions_inner : SemActions (child1 type) old1_in new1_in) by (apply (composeModules_project_inner isPrepend1 m_outer1 child1) with (old:=(old1_out ,, (old1_in ,, tt))) (new:=(new1_out ,, (new1_in ,, tt))); exact actions).
  assert (Hmod_outer1 : SemMod m_outer1 old1_out new1_out) by (constructor; auto).
  unfold ModSimulation in Houter.
  apply Houter with (old2 := old2_out) in Hmod_outer1; auto.
  destruct Hmod_outer1 as [new2_out [Hmod_outer2 Hrel_acc']].
  inversion Hmod_outer2 as [old_out' new_out' initGood_outer2 actions_outer2]; subst.
  assert (Hmod_inner1 : SemMod child1 old1_in new1_in). { constructor; auto. }
  unfold ModSimulation in Hinner.
  apply Hinner with (old2 := old2_in) in Hmod_inner1; auto.
  destruct Hmod_inner1 as [new2_in [Hmod_inner2 Hrel_in']].
  inversion Hmod_inner2 as [old_in' new_in' initGood_inner2 actions_inner2]; subst.
  exists (new2_out ,, (new2_in ,, tt)).
  simpl.
  split.
  + constructor.
    * simpl. split; auto.
    * unfold composeModules.
      destruct isPrepend2.
      -- apply liftActionInner_preserves_semActions with (t_outer := t_acc2) (s_out := old2_out) in actions_inner2.
         apply liftActionOuter_preserves_semActions with (t_inner := t2) (s_in := new2_in) in actions_outer2.
         assert (H_weak1: SemActions (map (@liftActionInner t_acc2 t2 type (Bit 0)) (child2 type) ++ map (@liftActionOuter t_acc2 t2 type (Bit 0)) (m_outer2 type)) (old2_out ,, (old2_in ,, tt)) (old2_out ,, (new2_in ,, tt))).
         { apply SemActions_subset with (ls1 := map (@liftActionInner t_acc2 t2 type (Bit 0)) (child2 type)).
           ** exact actions_inner2.
           ** intros a H_in. apply in_or_app. left. exact H_in. }
         assert (H_weak2: SemActions (map (@liftActionInner t_acc2 t2 type (Bit 0)) (child2 type) ++ map (@liftActionOuter t_acc2 t2 type (Bit 0)) (m_outer2 type)) (old2_out ,, (new2_in ,, tt)) (new2_out ,, (new2_in ,, tt))).
         { apply SemActions_subset with (ls1 := map (@liftActionOuter t_acc2 t2 type (Bit 0)) (m_outer2 type)).
           ** exact actions_outer2.
           ** intros a H_in. apply in_or_app. right. exact H_in. }
         apply SemActions_trans with (mid := (old2_out ,, (new2_in ,, tt))); auto.
      -- apply liftActionOuter_preserves_semActions with (t_inner := t2) (s_in := old2_in) in actions_outer2.
         apply liftActionInner_preserves_semActions with (t_outer := t_acc2) (s_out := new2_out) in actions_inner2.
         assert (H_weak1: SemActions (map (@liftActionOuter t_acc2 t2 type (Bit 0)) (m_outer2 type) ++ map (@liftActionInner t_acc2 t2 type (Bit 0)) (child2 type)) (old2_out ,, (old2_in ,, tt)) (new2_out ,, (old2_in ,, tt))).
         { apply SemActions_subset with (ls1 := map (@liftActionOuter t_acc2 t2 type (Bit 0)) (m_outer2 type)).
           ** exact actions_outer2.
           ** intros a H_in. apply in_or_app. left. exact H_in. }
         assert (H_weak2: SemActions (map (@liftActionOuter t_acc2 t2 type (Bit 0)) (m_outer2 type) ++ map (@liftActionInner t_acc2 t2 type (Bit 0)) (child2 type)) (new2_out ,, (old2_in ,, tt)) (new2_out ,, (new2_in ,, tt))).
         { apply SemActions_subset with (ls1 := map (@liftActionInner t_acc2 t2 type (Bit 0)) (child2 type)).
           ** exact actions_inner2.
           ** intros a H_in. apply in_or_app. right. exact H_in. }
         apply SemActions_trans with (mid := (new2_out ,, (old2_in ,, tt))); auto.
  + split; auto.
Qed.
