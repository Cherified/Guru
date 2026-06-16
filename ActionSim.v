From Stdlib Require Import String List ZArith Zmod Bool.
Require Import Guru.Library Guru.Syntax Guru.Semantics Guru.Theorems.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section ActionSimAuto.
  Context {t1 t2: Tree Elem}.
  Variable rel: TreeState ElemState t1 -> TreeState ElemState t2 -> Prop.

  Lemma LetAction_sim: forall {K K'} (s: string) (a1: Action type t1 K') (a2: Action type t2 K')
                              (cont1: type K' -> Action type t1 K) (cont2: type K' -> Action type t2 K),
    ActionSimulation a1 a2 rel ->
    (forall v, ActionSimulation (cont1 v) (cont2 v) rel) ->
    ActionSimulation (LetAction s a1 cont1) (LetAction s a2 cont2) rel.
  Proof.
    unfold ActionSimulation; intros K K' s a1 a2 cont1 cont2 Ha1 Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    destruct Hstep as [s_mid1 [v_mid [Hstep_a1 Hstep_cont1]]].
    specialize (Ha1 s1 s2 Hrel s_mid1 v_mid Hstep_a1).
    destruct Ha1 as [s_mid2 [Hstep_a2 Hrel_mid]].
    specialize (Hcont v_mid s_mid1 s_mid2 Hrel_mid s1' v Hstep_cont1).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemLetAction with (midState := s_mid2) (midRet := v_mid); auto.
  Qed.

  Lemma LetExp_sim: forall {K K'} (s: string) (e: Expr type K')
                           (cont1: type K' -> Action type t1 K) (cont2: type K' -> Action type t2 K),
    (forall v, ActionSimulation (cont1 v) (cont2 v) rel) ->
    ActionSimulation (LetExp s e cont1) (LetExp s e cont2) rel.
  Proof.
    unfold ActionSimulation; intros K K' s e cont1 cont2 Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont (evalExpr e) s1 s2 Hrel s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemLetExp; auto.
  Qed.

  Lemma Return_sim: forall {K} (e: Expr type K),
    ActionSimulation (Return e) (Return e) rel.
  Proof.
    unfold ActionSimulation; intros K e s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep. destruct Hstep as [H_s H_ret]. subst.
    exists s2. split; auto.
    apply SemReturn; auto.
  Qed.

End ActionSimAuto.

Section ActionSimAutoSameTree.
  Context {t: Tree Elem}.
  Variable rel: TreeState ElemState t -> TreeState ElemState t -> Prop.

  Lemma ReadReg_sim: forall {K} (s: string) (x: RegPath t)
                           (cont1 cont2: _ -> Action type t K),
    (forall s1 s2, rel s1 s2 -> 
        castStateReg x (readTreeState t s1 x.(regPath)) = 
        castStateReg x (readTreeState t s2 x.(regPath))) ->
    (forall v, ActionSimulation (cont1 v) (cont2 v) rel) ->
    ActionSimulation (ReadReg s x cont1) (ReadReg s x cont2) rel.
  Proof.
    unfold ActionSimulation; intros K s x cont1 cont2 Hval Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont (castStateReg x (readTreeState t s1 (regPath x))) s1 s2 Hrel s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemReadReg. rewrite <- (Hval s1 s2 Hrel). auto.
  Qed.

  Lemma WriteReg_sim: forall {K} (x: RegPath t) (v_expr: Expr type _)
                             (cont1 cont2: Action type t K),
    (forall s1 s2, rel s1 s2 ->
       rel (writeTreeState t s1 x.(regPath) (castStateRegInv x (evalExpr v_expr)))
           (writeTreeState t s2 x.(regPath) (castStateRegInv x (evalExpr v_expr)))) ->
    ActionSimulation cont1 cont2 rel ->
    ActionSimulation (WriteReg x v_expr cont1) (WriteReg x v_expr cont2) rel.
  Proof.
    unfold ActionSimulation; intros K x v_expr cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont (writeTreeState t s1 (regPath x) (castStateRegInv x (evalExpr v_expr)))
                      (writeTreeState t s2 (regPath x) (castStateRegInv x (evalExpr v_expr)))
                      (Hrel_update s1 s2 Hrel) s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemWriteReg. auto.
  Qed.

  Lemma System_sim: forall {K} (ls: list (SysT type)) (cont1 cont2: Action type t K),
    ActionSimulation cont1 cont2 rel ->
    ActionSimulation (System ls cont1) (System ls cont2) rel.
  Proof.
    unfold ActionSimulation; intros K ls cont1 cont2 Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont s1 s2 Hrel s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemSystem; auto.
  Qed.

  Lemma IfElse_sim: forall {K} (s: string) (p: Expr type Bool)
                           (t_branch1 f_branch1: Action type t K)
                           (t_branch2 f_branch2: Action type t K)
                           (cont1 cont2: _ -> Action type t K),
    ActionSimulation t_branch1 t_branch2 rel ->
    ActionSimulation f_branch1 f_branch2 rel ->
    (forall v, ActionSimulation (cont1 v) (cont2 v) rel) ->
    ActionSimulation (IfElse s p t_branch1 f_branch1 cont1) (IfElse s p t_branch2 f_branch2 cont2) rel.
  Proof.
    unfold ActionSimulation; intros K s p tb1 fb1 tb2 fb2 cont1 cont2 Ht Hf Hcont s1 s2 Hrel s1' v Hstep.
    change (type Bool) with bool in *.
    apply InversionSemAction in Hstep.
    destruct Hstep as [s_mid1 [v_mid [Hstep_t [Hstep_f Hstep_cont1]]]].
    assert (Hb: evalExpr p = true \/ evalExpr p = false).
    { exact (if evalExpr p as b return (b = true \/ b = false) then or_introl eq_refl else or_intror eq_refl). }
    case Hb as [Hp | Hp].
    - specialize (Ht s1 s2 Hrel s_mid1 v_mid (Hstep_t Hp)).
      destruct Ht as [s_mid2 [Hstep_tb2 Hrel_mid]].
      specialize (Hcont v_mid s_mid1 s_mid2 Hrel_mid s1' v Hstep_cont1).
      destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
      exists s2'. split; auto.
      apply SemIfElse with (midState := s_mid2) (midRet := v_mid); auto.
      intros contra. rewrite Hp in contra. discriminate.
    - specialize (Hf s1 s2 Hrel s_mid1 v_mid (Hstep_f Hp)).
      destruct Hf as [s_mid2 [Hstep_fb2 Hrel_mid]].
      specialize (Hcont v_mid s_mid1 s_mid2 Hrel_mid s1' v Hstep_cont1).
      destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
      exists s2'. split; auto.
      apply SemIfElse with (midState := s_mid2) (midRet := v_mid); auto.
      intros contra. rewrite Hp in contra. discriminate.
  Qed.

  Lemma NonDet_sim: forall {K K'} (s: string) (cont1 cont2: type K' -> Action type t K),
    (forall v, ActionSimulation (cont1 v) (cont2 v) rel) ->
    ActionSimulation (NonDet s K' cont1) (NonDet s K' cont2) rel.
  Proof.
    unfold ActionSimulation; intros K K' s cont1 cont2 Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    destruct Hstep as [v_nd Hstep_cont1].
    specialize (Hcont v_nd s1 s2 Hrel s1' v Hstep_cont1).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemNonDet with (v := v_nd); auto.
  Qed.

  Lemma ReadRqMem_sim: forall {K} (x: MemPath t) 
                           (i: Expr type (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x)))))) 
                           (p: FinType (getMemFromPath x).(memPort))
                           (cont1 cont2: Action type t K),
    (forall s1 s2, rel s1 s2 ->
       rel (let arr1 := castStateMem x (readTreeState t s1 x.(memPath)) in
            let val1 := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr1.(Fst).(tupleElems) (getDefault _) in
            writeTreeState t s1 x.(memPath) (castStateMemInv x (arr1.(Fst) ,, updSameTuple arr1.(Snd) p val1)))
           (let arr2 := castStateMem x (readTreeState t s2 x.(memPath)) in
            let val2 := nth (Z.to_nat (Zmod.to_Z (evalExpr i))) arr2.(Fst).(tupleElems) (getDefault _) in
            writeTreeState t s2 x.(memPath) (castStateMemInv x (arr2.(Fst) ,, updSameTuple arr2.(Snd) p val2)))) ->
    ActionSimulation cont1 cont2 rel ->
    ActionSimulation (ReadRqMem x i p cont1) (ReadRqMem x i p cont2) rel.
  Proof.
    unfold ActionSimulation; intros K x i p cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont _ _ (Hrel_update s1 s2 Hrel) s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemReadRqMem. auto.
  Qed.

  Lemma ReadRpMem_sim: forall {K} (s: string) (x: MemPath t)
                           (p: FinType (getMemFromPath x).(memPort))
                           (cont1 cont2: _ -> Action type t K),
    (forall s1 s2, rel s1 s2 -> 
        readSameTuple (castStateMem x (readTreeState t s1 x.(memPath))).(Snd) p = 
        readSameTuple (castStateMem x (readTreeState t s2 x.(memPath))).(Snd) p) ->
    (forall v, ActionSimulation (cont1 v) (cont2 v) rel) ->
    ActionSimulation (ReadRpMem s x p cont1) (ReadRpMem s x p cont2) rel.
  Proof.
    unfold ActionSimulation; intros K s x p cont1 cont2 Hval Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont (readSameTuple (castStateMem x (readTreeState t s1 x.(memPath))).(Snd) p) s1 s2 Hrel s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemReadRpMem. rewrite <- (Hval s1 s2 Hrel). auto.
  Qed.

  Lemma WriteMem_sim: forall {K} (x: MemPath t)
                             (i: Expr type (Bit (Z.log2_up (Z.of_nat (memSize (getMemFromPath x)))))) 
                             (v_expr: Expr type (memKind (getMemFromPath x)))
                             (cont1 cont2: Action type t K),
    (forall s1 s2, rel s1 s2 ->
       rel (let arr1 := castStateMem x (readTreeState t s1 x.(memPath)) in
            writeTreeState t s1 x.(memPath) (castStateMemInv x (updSameTupleNat arr1.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v_expr) ,, arr1.(Snd))))
           (let arr2 := castStateMem x (readTreeState t s2 x.(memPath)) in
            writeTreeState t s2 x.(memPath) (castStateMemInv x (updSameTupleNat arr2.(Fst) (Z.to_nat (Zmod.to_Z (evalExpr i))) (evalExpr v_expr) ,, arr2.(Snd))))) ->
    ActionSimulation cont1 cont2 rel ->
    ActionSimulation (WriteMem x i v_expr cont1) (WriteMem x i v_expr cont2) rel.
  Proof.
    unfold ActionSimulation; intros K x i v_expr cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont _ _ (Hrel_update s1 s2 Hrel) s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemWriteMem. auto.
  Qed.

  Lemma Send_sim: forall {K} (x: SendPath t) (v_expr: Expr type (getSendKind x))
                             (cont1 cont2: Action type t K),
    (forall s1 s2, rel s1 s2 ->
       rel (let currentTrace1 := castStateSend x (readTreeState t s1 x.(sendPath)) in
            writeTreeState t s1 x.(sendPath) (castStateSendInv x (evalExpr v_expr :: currentTrace1)))
           (let currentTrace2 := castStateSend x (readTreeState t s2 x.(sendPath)) in
            writeTreeState t s2 x.(sendPath) (castStateSendInv x (evalExpr v_expr :: currentTrace2)))) ->
    ActionSimulation cont1 cont2 rel ->
    ActionSimulation (Send x v_expr cont1) (Send x v_expr cont2) rel.
  Proof.
    unfold ActionSimulation; intros K x v_expr cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    specialize (Hcont _ _ (Hrel_update s1 s2 Hrel) s1' v Hstep).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemSend. auto.
  Qed.

  Lemma Recv_sim: forall {K} (s: string) (x: RecvPath t)
                           (cont1 cont2: _ -> Action type t K),
    (forall recvVal s1 s2, rel s1 s2 -> 
        rel (let currentTrace1 := castStateRecv x (readTreeState t s1 x.(recvPath)) in
             writeTreeState t s1 x.(recvPath) (castStateRecvInv x (recvVal :: currentTrace1)))
            (let currentTrace2 := castStateRecv x (readTreeState t s2 x.(recvPath)) in
             writeTreeState t s2 x.(recvPath) (castStateRecvInv x (recvVal :: currentTrace2)))) ->
    (forall v, ActionSimulation (cont1 v) (cont2 v) rel) ->
    ActionSimulation (Recv s x cont1) (Recv s x cont2) rel.
  Proof.
    unfold ActionSimulation; intros K s x cont1 cont2 Hrel_update Hcont s1 s2 Hrel s1' v Hstep.
    apply InversionSemAction in Hstep.
    destruct Hstep as [recvVal Hstep_cont1].
    specialize (Hcont recvVal _ _ (Hrel_update recvVal s1 s2 Hrel) s1' v Hstep_cont1).
    destruct Hcont as [s2' [Hstep_cont2 Hrel_final]].
    exists s2'. split; auto.
    apply SemRecv with (recvVal := recvVal). auto.
  Qed.

End ActionSimAutoSameTree.

Ltac action_sim_auto :=
  repeat match goal with
  | |- ActionSimulation (LetAction _ _ _) (LetAction _ _ _) _ => apply LetAction_sim
  | |- ActionSimulation (LetExp _ _ _) (LetExp _ _ _) _ => apply LetExp_sim
  | |- ActionSimulation (Return _) (Return _) _ => apply Return_sim
  | |- ActionSimulation (ReadReg _ _ _) (ReadReg _ _ _) _ => apply ReadReg_sim
  | |- ActionSimulation (WriteReg _ _ _) (WriteReg _ _ _) _ => apply WriteReg_sim
  | |- ActionSimulation (ReadRqMem _ _ _ _) (ReadRqMem _ _ _ _) _ => apply ReadRqMem_sim
  | |- ActionSimulation (ReadRpMem _ _ _ _) (ReadRpMem _ _ _ _) _ => apply ReadRpMem_sim
  | |- ActionSimulation (WriteMem _ _ _ _) (WriteMem _ _ _ _) _ => apply WriteMem_sim
  | |- ActionSimulation (Send _ _ _) (Send _ _ _) _ => apply Send_sim
  | |- ActionSimulation (Recv _ _ _) (Recv _ _ _) _ => apply Recv_sim
  | |- ActionSimulation (System _ _) (System _ _) _ => apply System_sim
  | |- ActionSimulation (IfElse _ _ _ _ _) (IfElse _ _ _ _ _) _ => apply IfElse_sim
  | |- ActionSimulation (NonDet _ _ _) (NonDet _ _ _) _ => apply NonDet_sim

  | H_meth : forall val, ActionSimulation (?m val) (?m' val) _ 
    |- ActionSimulation (?m ?arg) (?m' ?arg) _ => 
      apply H_meth

  | |- _ => eauto
  end.
