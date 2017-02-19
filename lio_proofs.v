Require Import Arith.
Require Import Omega.
Require Import Bool.
Require Import List.
Require Import SfLib.
Require Export lio.

Lemma labels_are_values : forall l,
  is_l_of_t l ->
  is_v_of_t l.
Proof.
  intros l H.
  induction l; try solve [repeat auto; reflexivity; solve by inversion].
Qed.

Hint Resolve labels_are_values.

Lemma values_cannot_be_reduced : forall v t,
  is_v_of_t v ->
  ~ (pure_reduce v t).
Proof.
  intros l t H1.
  unfold not.
  intro H2.
  induction H2; repeat eauto.
Qed.

Hint Resolve values_cannot_be_reduced.

Corollary labels_cannot_be_reduced : forall l t,
  is_l_of_t l ->
  ~ (pure_reduce l t).
Proof.
  intros l t H1.
  eapply values_cannot_be_reduced.
  eapply labels_are_values.
  apply H1.
Qed.

Hint Resolve labels_cannot_be_reduced.

Lemma values_cannot_be_lio_reduced : forall l c v n m,
  is_v_of_t v ->
  ~ (lio_reduce (m_Config l c v) n m).
Proof.
  intros l c v n m H1.
  unfold not.
  intro H2.
  induction v; repeat (solve by inversion).
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
  inversion H2. subst. inversion H8.
Qed.

Hint Resolve values_cannot_be_lio_reduced.


Corollary labels_cannot_be_lio_reduced : forall l c v n m,
  is_l_of_t v ->
  ~ (lio_reduce (m_Config l c v) n m).
Proof.
  intros l c v n m H1.
  eapply values_cannot_be_lio_reduced.
  eapply labels_are_values.
  assumption.
Qed.


Hint Resolve labels_cannot_be_reduced.

Lemma deterministic_pure_reduce :
  deterministic pure_reduce.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  pure_reduce_cases (induction Hy1) Case; intros y2 Hy2.
  Case "Pr_appCtx". inversion Hy2.
   SCase "Pr_appCtx". apply IHHy1 in H2. subst. reflexivity.
   SCase "Pr_app". subst t3. subst. solve by inversion.
  Case "Pr_app". inversion Hy2. subst t3. solve by inversion.  reflexivity.
  Case "Pr_fixCtx". inversion Hy2. subst t5. apply IHHy1 in H0. subst t'0. reflexivity.
  subst. inversion Hy1.
  Case "Pr_fix". inversion Hy2.  solve by inversion. reflexivity.
  Case "Pr_ifCtx". inversion Hy2. apply IHHy1 in H3. subst. reflexivity.
   SCase "true". subst. inversion Hy1.
   SCase "false". subst. inversion Hy1.
  Case "Pr_ifTrue". inversion Hy2. solve by inversion. reflexivity.
  Case "Pr_ifFalse". inversion Hy2. solve by inversion. reflexivity.
  Case "Pr_joinCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_joinCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. solve by inversion. assumption.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.
  Case "Pr_joinBotL". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity.
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_joinBotR". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_joinEq". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H6. solve by inversion. assumption.
   subst. auto.
   reflexivity.
   reflexivity.
   subst. solve by inversion.
   subst. solve by inversion.
   reflexivity.
   subst. reflexivity.
  Case "Pr_joinAB". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
   auto.
  Case "Pr_joinBA". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_joinTopL". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_joinTopR". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   auto.
   reflexivity.
   reflexivity.
  Case "Pr_meetCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_meetCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. solve by inversion. assumption.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. reflexivity.
  Case "Pr_meetBotL". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity.
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_meetBotR". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   auto.
   reflexivity.
  Case "Pr_meetEq". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H6. solve by inversion. assumption.
   subst. auto.
   subst. reflexivity.
   reflexivity.
   subst. solve by inversion.
   subst. solve by inversion.
   subst. auto.
   reflexivity.
  Case "Pr_meetAB". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_meetBA". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_meetTopL". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   subst. auto.
   reflexivity.
   reflexivity.
  Case "Pr_meetTopR". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_canFlowToCtxL". inversion Hy2. subst t3 t1. apply IHHy1 in H2. subst t1'0. reflexivity.
   subst t2 t1. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst t1 y2. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. reflexivity.
   subst.  apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
  Case "Pr_canFlowToCtxR". inversion Hy2. apply labels_cannot_be_reduced in H3. solve by inversion. assumption.
   subst. apply IHHy1 in H4. subst t2'0. reflexivity.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. assumption.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
   subst. apply labels_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
  Case "Pr_canFlowToBot". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. reflexivity.
   subst. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   reflexivity.
   reflexivity.
   auto.
  Case "Pr_canFlowToEq". inversion Hy2. apply labels_cannot_be_reduced in H5. solve by inversion. assumption.
   subst. apply labels_cannot_be_reduced in H6. solve by inversion. assumption.
   subst. auto.
   subst. reflexivity.
   subst. solve by inversion.
   subst. solve by inversion.
   subst. reflexivity.
  Case "Pr_canFlowToAB". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_canFlowToBA". inversion Hy2. apply labels_cannot_be_reduced in H2. solve by inversion. reflexivity.
   apply labels_cannot_be_reduced in H3. solve by inversion. reflexivity.
   solve by inversion.
   reflexivity.
  Case "Pr_canFlowToTop". inversion Hy2. apply labels_cannot_be_reduced in H4. solve by inversion. assumption.
   apply labels_cannot_be_reduced in H5. solve by inversion. reflexivity.
   reflexivity.
   reflexivity.
   reflexivity.
  Case "Pr_labelOfCtx". inversion Hy2. subst. apply IHHy1 in H0. subst t'0. reflexivity.
    subst. apply values_cannot_be_reduced in Hy1. solve by inversion. simpl. trivial.
  Case "Pr_labelOf". inversion Hy2.
    subst. solve by inversion. reflexivity.
  Case "Pr_hole". inversion Hy2.  reflexivity.
Qed.

Hint Resolve deterministic_pure_reduce.


Lemma deterministic_lio_reduce_multi : forall l c t n l1 c1 t1 b1 l2 c2 t2 b2,
  lio_reduce_multi (m_Config l c t) n (m_Config l1 c1 (t_VLIO b1 t1)) ->
  lio_reduce_multi (m_Config l c t) n (m_Config l2 c2 (t_VLIO b2 t2)) ->
  l1 = l2 /\ c1 = c2 /\ t1 = t2 /\ b1 = b2.
Proof.
  intros.
  generalize dependent t1. generalize dependent c1. generalize dependent l1.
  generalize dependent t2. generalize dependent c2. generalize dependent l2.
  term_cases (induction t) Case; intros; try (inversion H; inversion H12; inversion H22).
  Case "term_VLIO".
  inversion H. subst. apply values_cannot_be_lio_reduced in H12. contradiction.
  unfold is_v_of_t. trivial. subst.
  inversion H0. subst. apply values_cannot_be_lio_reduced in H14. contradiction.
  unfold is_v_of_t. trivial. subst.
  eauto.
  Case "term_App".  subst.
  inversion H0. subst. inversion H17. subst.
  remember  (t_App (t_VAbs x t6) t2) as lhs.
  assert (t_VLIO b1 t3 = t_VLIO b2 t0).
  apply deterministic_pure_reduce with (x := lhs).
  assumption. assumption.
  inversion H1. subst. eauto.
  Case "term_Fix". subst.
  inversion H0. subst. inversion H17. subst.
  remember  (t_Fix (t_VAbs x t3)) as lhs.
  assert (t_VLIO b1 t1 = t_VLIO b2 t2).
  apply deterministic_pure_reduce with (x := lhs).
  assumption. assumption.
  inversion H1. subst. eauto.
  Case "term_IfEl". subst.
  inversion H0. subst. inversion H17. subst.
  remember  (t_IfEl t_VTrue (t_VLIO b1 t4) t3) as lhs.
  assert (t_VLIO b1 t4 = t_VLIO b2 t0).
  apply deterministic_pure_reduce with (x := lhs).
  assumption. assumption.
  inversion H1. subst. eauto.
  Case "term_IfEl". subst.
  inversion H0. subst. inversion H17. subst.
  remember  (t_IfEl t_VFalse t2 (t_VLIO b1 t4)) as lhs.
  assert (t_VLIO b1 t4 = t_VLIO b2 t0).
  apply deterministic_pure_reduce with (x := lhs).
  assumption. assumption.
  inversion H1. subst. eauto.
  Case "term_Join". subst. inversion H26. subst.
  inversion H26. subst. inversion H26. subst.
  Case "term_Meet". subst. inversion H26. subst.
  inversion H26. subst. inversion H26. subst.
  Case "term_Return".
    inversion H. subst. inversion H12. subst.
    inversion H0. subst. inversion H19. subst. eauto. subst.
    inversion H22. subst. inversion H15.
  Case "term_LabelOf".
    inversion H22. inversion H28.
  Case "term_ThrowLIO".
    inversion H. subst. inversion H12. subst.
    inversion H0. subst. inversion H19. subst. eauto. subst.
    inversion H22. subst. inversion H15.
Qed.

Lemma deterministic_lio_reduce : forall x n y1 y2,
  lio_reduce x n y1 ->
  lio_reduce x n y2 ->
  y1 = y2.
Proof.
  intros x n y1 y2 Hy1 Hy2.
  generalize dependent y2.
  lio_reduce_cases (induction Hy1) Case; intros.
  Case "LIO_return".
    inversion Hy2. subst. eauto.
    inversion H9.
  Case "LIO_bind".
    inversion Hy2.
    SCase "no ex".
    assert (l' = l'0 /\ c' = c'0 /\ t1' = t1'0 /\ false = false).
    apply deterministic_lio_reduce_multi with (l:=l5) (c:=c) (t0:=t1) (n:=n5).
    assumption. assumption.
    inversion H15.
    inversion H5.
    inversion H17.
    inversion H20.
    subst.
    reflexivity.
    SCase "ex".
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t1' = t1'0 /\ false = true).
    apply deterministic_lio_reduce_multi with (l:=l5) (c:=c) (t0:=t1) (n:=n5).
    assumption. assumption.
    inversion H4.
    inversion H6.
    inversion H10.
    solve by inversion.
    inversion H11.
  Case "LIO_bindEx".
    inversion Hy2.
    SCase "no ex".
    assert (l' = l'0 /\ c' = c'0 /\ t1' = t1'0 /\ true = false).
    apply deterministic_lio_reduce_multi with (l:=l5) (c:=c) (t0:=t1) (n:=n5).
    assumption. assumption.
    inversion H15.
    inversion H17.
    inversion H19.
    solve by inversion.
    SCase "ex".
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t1' = t1'0 /\ true = true).
    apply deterministic_lio_reduce_multi with (l:=l5) (c:=c) (t0:=t1) (n:=n5).
    assumption. assumption.
    inversion H4.
    inversion H6.
    inversion H10.
    subst.
    reflexivity.
    inversion H11.
  Case "LIO_getLabel".
    inversion Hy2.
    subst. eauto.
    inversion H9.
  Case "LIO_getClearance".
    inversion Hy2.
    subst. eauto.
    inversion H9.
  Case "LIO_labelCtx".
    inversion Hy2.
    subst.
    assert (t1' = t1'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. eauto.
    subst t1 c0 l_5 t2.
    apply labels_cannot_be_reduced in H1. contradiction. assumption.
    inversion H10.
  Case "LIO_label".
    inversion Hy2.
    subst.
    apply labels_cannot_be_reduced in H13. contradiction. assumption.
    subst. eauto.
    inversion H12.
  Case "LIO_unlabelCtx".
    inversion Hy2.
    subst.
    assert (t' = t'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t5). assumption. assumption.
    subst t'0. eauto.
    subst.
    apply values_cannot_be_reduced in H1. solve by inversion. simpl. trivial.
    subst.
    apply values_cannot_be_reduced in H1. solve by inversion. simpl. trivial.
    inversion H10.
 Case "LIO_unlabel".
    inversion Hy2.
    subst.
    apply values_cannot_be_reduced in H13. solve by inversion. simpl. trivial.
    subst.
    assert (l2 = l3).
    SCase "assertion". apply deterministic_pure_reduce with (x := t_Join l_5 l1). assumption. assumption.
    subst l3. eauto.
    inversion H13.
 Case "LIO_unlabelEx".
    inversion Hy2.
    subst.
    apply values_cannot_be_reduced in H13. solve by inversion. simpl. trivial.
    subst.
    assert (l2 = l3).
    SCase "assertion". apply deterministic_pure_reduce with (x := t_Join l_5 l1). assumption. assumption.
    subst l3. eauto.
    inversion H13.
  Case "LIO_toLabeledCtx".
    inversion Hy2.
    subst.
    assert (t1' = t1'0) as Hrwrt.
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. eauto.
    apply labels_cannot_be_reduced in H1. contradiction. assumption.
    subst.
    apply labels_cannot_be_reduced in H1. contradiction. assumption.
    inversion H10.
  Case "LIO_toLabeled".
    inversion Hy2.
    subst.
    apply labels_cannot_be_reduced in H17. contradiction. assumption.
    subst.
    assert (n5 = n0).
    SCase "assertion". (* trivial from H23: n5+1=n0+1 *) admit.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t' = t'0 /\ false = false) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l_5) (c := c) (t0 := t5) (n := n0).
    assumption. assumption.
    assert (t' = t'0) as Hrwrt_t. apply Hrwrt. rewrite Hrwrt_t.
    reflexivity.
    subst.
    assert (n5 = n0).
    SCase "assertion". (* trivial from H23: n5+1=n0+1 *) admit.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t' = t'0 /\ false = true) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l_5) (c := c) (t0 := t5) (n := n0).
    assumption. assumption.
    inversion Hrwrt.
    inversion H9.
    inversion H11.
    solve by inversion.
    inversion H16.
  Case "LIO_toLabeledEx".
    inversion Hy2.
    subst.
    apply labels_cannot_be_reduced in H17. contradiction. assumption.
    subst.
    assert (n5 = n0).
    SCase "assertion". (* trivial from H23: n5+1=n0+1 *) admit.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t' = t'0 /\ true = false) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l_5) (c := c) (t0 := t5) (n := n0).
    assumption. assumption.
    inversion Hrwrt.
    inversion H9.
    inversion H11.
    solve by inversion.
    subst.
    assert (n5 = n0).
    SCase "assertion". (* trivial from H23: n5+1=n0+1 *) admit.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t' = t'0 /\ true = true) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l_5) (c := c) (t0 := t5) (n := n0).
    assumption. assumption.
    inversion Hrwrt.
    inversion H9.
    inversion H11.
    subst.
    reflexivity.
    inversion H16.
  Case "LIO_lowerClrCtx".
    inversion Hy2.
    subst.
    assert (t' = t'0) as Hrwrt.
    SCase "assertion". apply  deterministic_pure_reduce with (x := t5). assumption. assumption.
    subst t'0. reflexivity.
    apply labels_cannot_be_reduced in H1. contradiction. assumption.
    inversion H10.
  Case "LIO_lowerClr".
    inversion Hy2.
    subst.
    apply labels_cannot_be_reduced in H12. contradiction. assumption.
    subst.
    reflexivity.
    inversion H12.
  Case "LIO_throwLIO".
    inversion Hy2.
    subst.
    reflexivity.
    inversion H9.
  Case "LIO_catchLIO".
    inversion Hy2.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t1' = t1'0 /\ false = false) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l5) (c := c) (t0 := t1) (n := n5).
    assumption.
    assumption.
    inversion Hrwrt.
    inversion H5.
    inversion H7.
    subst.
    reflexivity.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t1' = t1'0 /\ false = true) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l5) (c := c) (t0 := t1) (n := n5).
    assumption.
    assumption.
    inversion Hrwrt.
    inversion H5.
    inversion H7.
    solve by inversion.
    inversion H11.
  Case "LIO_catchLIOEx".
    inversion Hy2.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t1' = t1'0 /\ true = false) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l5) (c := c) (t0 := t1) (n := n5).
    assumption.
    assumption.
    inversion Hrwrt.
    inversion H5.
    inversion H7.
    solve by inversion.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t1' = t1'0 /\ true = true) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l5) (c := c) (t0 := t1) (n := n5).
    assumption.
    assumption.
    inversion Hrwrt.
    inversion H5.
    inversion H7.
    subst.
    reflexivity.
    inversion H11.
  Case "LIO_hole".
    inversion Hy2.
    subst. eauto.
    subst.
    inversion H6.
    trivial.
  Case "LIO_pure".
    subst.
    inversion Hy2; try (subst; inversion H1; trivial).
    subst.
    assert (t1'0 = (t_App t1'1 t2)).
    apply deterministic_pure_reduce with (x := t_App t0 t2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = (tsubst_t t2 x t0)).
    apply deterministic_pure_reduce with (x := t_App (t_VAbs x t0) t2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_Fix t').
    apply deterministic_pure_reduce with (x := t_Fix t5).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = (tsubst_t (t_Fix (t_VAbs x t5)) x t5)).
    apply deterministic_pure_reduce with (x := t_Fix (t_VAbs x t5)).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_IfEl t1'1 t2 t3).
    apply deterministic_pure_reduce with (x := t_IfEl t0 t2 t3).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t1').
    apply deterministic_pure_reduce with (x := t_IfEl t_VTrue t1' t3).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t1').
    apply deterministic_pure_reduce with (x := t_IfEl t_VFalse t2 t1').
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_Join t1'1 t2).
    apply deterministic_pure_reduce with (x := t_Join t0 t2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_Join l1 t2').
    apply deterministic_pure_reduce with (x := t_Join l1 t2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t1').
    apply deterministic_pure_reduce with (x := t_Join t_LBot t1').
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t1').
    apply deterministic_pure_reduce with (x := t_Join t1' t_LBot).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = l2).
    apply deterministic_pure_reduce with (x := t_Join l2 l2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LTop).
    apply deterministic_pure_reduce with (x := t_Join t_LA t_LB).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LTop).
    apply deterministic_pure_reduce with (x := t_Join t_LB t_LA).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LTop).
    apply deterministic_pure_reduce with (x := t_Join t_LTop l0).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LTop).
    apply deterministic_pure_reduce with (x := t_Join l0 t_LTop).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_Meet t1'1 t2).
    apply deterministic_pure_reduce with (x := t_Meet t0 t2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_Meet l1 t2').
    apply deterministic_pure_reduce with (x := t_Meet l1 t2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LBot).
    apply deterministic_pure_reduce with (x := t_Meet t_LBot l0).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LBot).
    apply deterministic_pure_reduce with (x := t_Meet l0 t_LBot).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = l2).
    apply deterministic_pure_reduce with (x := t_Meet l2 l2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LBot).
    apply deterministic_pure_reduce with (x := t_Meet t_LA t_LB).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LBot).
    apply deterministic_pure_reduce with (x := t_Meet t_LB t_LA).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t1').
    apply deterministic_pure_reduce with (x := t_Meet t_LTop t1').
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t1').
    apply deterministic_pure_reduce with (x := t_Meet t1' t_LTop).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_CanFlowTo t1'1 t2).
    apply deterministic_pure_reduce with (x := t_CanFlowTo t0 t2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_CanFlowTo l1 t2').
    apply deterministic_pure_reduce with (x := t_CanFlowTo l1 t2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_VTrue).
    apply deterministic_pure_reduce with (x := t_CanFlowTo t_LBot l0).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_VTrue).
    apply deterministic_pure_reduce with (x := t_CanFlowTo l2 l2).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_VFalse).
    apply deterministic_pure_reduce with (x := t_CanFlowTo t_LA t_LB).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_VFalse).
    apply deterministic_pure_reduce with (x := t_CanFlowTo t_LB t_LA).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_VTrue).
    apply deterministic_pure_reduce with (x := t_CanFlowTo l0  t_LTop).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_LabelOf t').
    apply deterministic_pure_reduce with (x := t_LabelOf t5).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t1').
    apply deterministic_pure_reduce with (x := t_LabelOf (t_VLabeled b5 t1' t2)).
    assumption. assumption. subst. reflexivity.
    subst.
    assert (t1'0 = t_VHole).
    apply deterministic_pure_reduce with (x := t_VHole).
    assumption. assumption. subst. reflexivity.
    Admitted.

Hint Resolve deterministic_lio_reduce.


Definition isLabel (t_6:t) : bool :=
  match t_6 with
  | t_LBot => (true)
  | t_LA => (true)
  | t_LB => (true)
  | t_LTop => (true)
  | _ => false
end.

Lemma isLabel_is_l_of_t : forall term,
  isLabel term = true <-> is_l_of_t term.
Proof.
  intros.
  induction term; simpl; eauto; try split; try reflexivity; try split; intros; try solve by inversion.
Qed.

Definition canFlowTo (l1 l2 :t) : option bool :=
  match l1 with
    | t_LBot =>  match l2 with
                 | t_LBot  => Some true
                 | t_LA    => Some true
                 | t_LB    => Some true
                 | t_LTop  => Some true
                 | _       => None
                 end
    | t_LA    =>  match l2 with
                 | t_LBot  => Some false
                 | t_LA     => Some true
                 | t_LB     => Some false
                 | t_LTop  => Some true
                 | _       => None
                 end
    | t_LB    =>  match l2 with
                 | t_LBot  => Some false
                 | t_LA     => Some false
                 | t_LB     => Some true
                 | t_LTop  => Some true
                 | _       => None
                 end
    | t_LTop =>  match l2 with
                 | t_LBot  => Some false
                 | t_LA     => Some false
                 | t_LB     => Some false
                 | t_LTop  => Some true
                 | _       => None
                 end
    | _       => None
  end.

Definition eq_option_bool (o1 o2 : option bool) : bool :=
  match o1, o2 with
    | Some x , Some y => eqb x y
    | _, _ => false
  end.

Notation " o1 '===' o2 " := (eq_option_bool o1 o2) (at level 40).

Notation " l1 '[=' l2 " := ((canFlowTo l1 l2 === Some true) = true) (at level 40).
Notation " l1 '[/=' l2 " := ((canFlowTo l1 l2 === Some true) = false) (at level 40).

Axiom canFlowToSyntaxRel : forall l1 l2,
  l1 [= l2 <-> pure_reduce (t_CanFlowTo l1 l2) t_VTrue.

Lemma canFlowTo_reflexive : forall l,
  is_l_of_t l ->
  l [= l.
Proof.
  intros. induction l; try repeat (unfold canFlowTo; trivial); inversion H.
Qed.

Lemma canFlowTo_transitivie : forall l1 l2 l3,
  is_l_of_t l1 ->
  is_l_of_t l2 ->
  is_l_of_t l3 ->
  l1 [= l2 ->
  l2 [= l3 ->
  l1 [= l3.
Proof. (* boring *)
Admitted.

Fixpoint erase_term (l term : t) : t :=
  match term with
   | t_LBot             => t_LBot
   | t_LA               => t_LA
   | t_LB               => t_LB
   | t_LTop             => t_LTop
   | t_VTrue            => t_VTrue
   | t_VFalse           => t_VFalse
   | t_VUnit            => t_VUnit
   | t_VAbs x t5        => t_VAbs x (erase_term l t5)
   | t_VLIO b t5        => t_VLIO b (erase_term l t5)
   | t_VLabeled b l1 t2 => t_VLabeled b (erase_term l l1)
                                      (if canFlowTo (erase_term l l1) l === Some true
                                         then erase_term l t2
                                         else t_VHole)
   | t_VException       => t_VException
   | t_VHole            => t_VHole
   | t_Var x            => t_Var x
   | t_App t5 t'        => t_App (erase_term l t5) (erase_term l t')
   | t_Fix t5           => t_Fix (erase_term l t5)
   | t_IfEl t1 t2 t3    => t_IfEl (erase_term l t1) (erase_term l t2) (erase_term l t3)
   | t_Join t1 t2       => t_Join (erase_term l t1) (erase_term l t2)
   | t_Meet t1 t2       => t_Meet (erase_term l t1) (erase_term l t2)
   | t_CanFlowTo t1 t2  => t_CanFlowTo (erase_term l t1) (erase_term l t2)
   | t_Return t5        => t_Return (erase_term l t5)
   | t_Bind t5 t'       => t_Bind (erase_term l t5) (erase_term l t')
   | t_GetLabel         => t_GetLabel
   | t_GetClearance     => t_GetClearance
   | t_LabelOf t5       => t_LabelOf (erase_term l t5)
   | t_Label t5 t'      => t_Label (erase_term l t5)
                           (if canFlowTo (erase_term l t5) l === Some true
                             then erase_term l t'
                             else t_VHole)
   | t_UnLabel t5       => t_UnLabel (erase_term l t5)
   | t_ToLabeled t1 t2  => t_ToLabeled (erase_term l t1) (erase_term l t2)
   | t_LowerClr t1      => t_LowerClr (erase_term l t1)
   | t_ThrowLIO t1      => t_ThrowLIO (erase_term l t1)
   | t_CatchLIO t1 t2   => t_CatchLIO (erase_term l t1) (erase_term l t2)
  end.

(* ~>L *)
Inductive pure_reduce_l : t -> t -> t -> Prop :=
   | pure_reduce_l_step : forall l t1 t2,
     is_l_of_t l ->
     pure_reduce t1 t2 ->
     pure_reduce_l l t1 (erase_term l t2).


(*
Lemma deterministic_pure_reduce_l : forall l x y1 y2,
  pure_reduce_l l x y1 ->
  pure_reduce_l l x y2 ->
  y1 = y2.
Proof.
  intros l x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  inversion Hy2.
  assert (t2 = t3).
  Case "assertion". apply deterministic_pure_reduce with (x := t1). assumption. assumption.
  subst t3 t1.
  reflexivity.
Qed.
*)

(* If the attack observer label does not flow to the current
   label, erase everything to a hole. This includes the current
   and clearance since they are protected by the current labe. *)
Definition erase_config (l : t) (cfg : m) : m :=
  match cfg with
   | m_Config l1 c1 t1 => if canFlowTo l1 l === Some true
                            then m_Config l1 c1 (erase_term l t1)
                            else m_Config t_VHole t_VHole t_VHole
  end.

Lemma erase_label_id : forall l l2,
  is_l_of_t l ->
  is_l_of_t l2 ->
  erase_term l l2 = l2.
Proof.
  intros.  induction l2; auto; inversion H0.
Qed.

Lemma t_subst_label_id : forall x t l,
  is_l_of_t l ->
  tsubst_t t x l = l.
Proof.
  intros.  induction l; auto; inversion H.
Qed.
  Ltac go :=
    repeat try first [ repeat auto; simpl; inversion IHt1_1; reflexivity].
Lemma erase_term_idempotent : forall l t1,
  is_l_of_t l ->
  erase_term l t1 = erase_term l (erase_term l t1).
Proof.
  intros l t1 H.
  term_cases (induction t1) Case; eauto.
  Case "term_VAbs". simpl. rewrite <- IHt1. reflexivity.
  Case "term_VLIO". simpl. rewrite <- IHt1. reflexivity.
  Case "term_VLabeled".
  induction l; try contradiction;
    (destruct t1_1; simpl;
     repeat try solve [ simpl; inversion IHt1_1; reflexivity
                      | rewrite <- IHt1_2; reflexivity
                      | repeat auto ]).
  Case "term_App". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_Fix". simpl. rewrite <- IHt1. reflexivity.
  Case "term_IfEl". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. rewrite <- IHt1_3. reflexivity.
  Case "term_Join". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_Meet". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_CanFlowTo". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_Return". simpl. rewrite <- IHt1. reflexivity.
  Case "term_Bind". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_LabelOf". simpl. rewrite <- IHt1. reflexivity.
  Case "term_Label".
  simpl. rewrite <- IHt1_1. remember (canFlowTo (erase_term l t1_1) l === Some true).
  destruct b.
  SCase "t1_1 [= l".
  rewrite <- IHt1_2. reflexivity.
  SCase "t1_1 [/= l". reflexivity.
  Case "term_UnLabel". simpl. rewrite <- IHt1. reflexivity.
  Case "term_ToLabeled".
  simpl. rewrite <- IHt1_1.
  rewrite <- IHt1_2. reflexivity.
  Case "term_LowerClr". simpl.
  rewrite <- IHt1.  reflexivity.
  Case "term_ThrowLIO". simpl.
  rewrite <- IHt1.  reflexivity.
  Case "term_CatchLIO". simpl.
  rewrite <- IHt1_1. rewrite <- IHt1_2.  reflexivity.
Qed.

Hint Resolve erase_term_idempotent.

Lemma pure_reduce_inv : forall l t1 t2,
  is_l_of_t l ->
  pure_reduce (erase_term l t1) t2 ->
  pure_reduce_l l (erase_term l t1) (erase_term l t2).
Proof.
  intros l t1 t2 l_of_t H.
  apply pure_reduce_l_step. assumption. assumption.
Qed.

Hint Resolve pure_reduce_inv.

Lemma erase_term_homo_if : forall l (b : bool)  t1 t2,
  is_l_of_t l ->
  erase_term l (if b then t1 else t2) =
                if b then erase_term l t1 else erase_term l t2.
Proof. intros. destruct b; eauto.
Qed.

Lemma tsubst_t_homo_if : forall (b : bool) t1 t2 t3  x,
  tsubst_t t1 x (if b then t2 else t3) =
  if b then (tsubst_t t1 x t2) else (tsubst_t t1 x t3).
Proof. intros. destruct b; eauto.
Qed.

Lemma tsubst_t_homo_if' : forall l1 l2 t1 t2 t3  x,
  tsubst_t t1 x (if canFlowTo l1 l2 === Some true then t2 else t3) =
  if canFlowTo (tsubst_t t1 x l1) (tsubst_t t1 x l2) === Some true
    then (tsubst_t t1 x t2) else (tsubst_t t1 x t3).
Admitted.

Lemma erase_term_homo_subst : forall l t1 x t2,
  is_l_of_t l ->
  erase_term l (tsubst_t t1 x t2) = tsubst_t (erase_term l t1) x (erase_term l t2).
Proof.
  intros l t1 x t2 l_of_t.
  generalize dependent t1.
  term_cases (induction t2) Case; intros t1; eauto.
  Case "term_VAbs". simpl. rewrite IHt2. reflexivity.
  Case "term_VLIO". simpl. rewrite IHt2. reflexivity.
  Case "term_VLabeled". simpl.
    rewrite tsubst_t_homo_if'.
    simpl.
    rewrite IHt2_1.
    assert (tsubst_t (erase_term l t1) x l = l) as Hrwrt.
    SCase "assertion". rewrite t_subst_label_id. reflexivity. assumption.
    rewrite -> Hrwrt.
    rewrite IHt2_2.
    reflexivity.
  Case "term_Var". simpl.
    assert (erase_term l (if eq_termvar x0 x then t1 else t_Var x0) =
            if eq_termvar x0 x then erase_term l t1 else erase_term l (t_Var x0)) as Hr.
    SCase "asert". destruct (eq_termvar x0 x); auto.
    rewrite Hr. simpl. reflexivity.
  Case "term_App". simpl. rewrite IHt2_1. rewrite IHt2_2. reflexivity.
  Case "term_Fix". simpl. rewrite IHt2. reflexivity.
  Case "term_IfEl". simpl. rewrite IHt2_1. rewrite IHt2_2. rewrite IHt2_3. reflexivity.
  Case "term_Join". simpl. rewrite IHt2_1. rewrite IHt2_2. reflexivity.
  Case "term_Meet". simpl. rewrite IHt2_1. rewrite IHt2_2. reflexivity.
  Case "term_CanFlowTo".  simpl. rewrite IHt2_1. rewrite IHt2_2. reflexivity.
  Case "term_Return". simpl. rewrite IHt2. reflexivity.
  Case "term_Bind". simpl. rewrite IHt2_1. rewrite IHt2_2. reflexivity.
  Case "term_LabelOf". simpl. rewrite IHt2. reflexivity.
  Case "term_Label". simpl.
    rewrite tsubst_t_homo_if'.
    simpl.
    rewrite IHt2_1. rewrite IHt2_2.
    assert (tsubst_t (erase_term l t1) x l = l) as Hrwrt.
    SCase "assertion". rewrite t_subst_label_id. reflexivity. assumption.
    rewrite -> Hrwrt.
    reflexivity.
  Case "term_UnLabel". simpl. rewrite IHt2. reflexivity.
  Case "term_ToLabeled". simpl.
    rewrite IHt2_1. rewrite IHt2_2. reflexivity.
  Case "term_LowerClr". simpl. rewrite IHt2. reflexivity.
  Case "term_ThrowLIO". simpl. rewrite IHt2. reflexivity.
  Case "term_CatchLIO". simpl. rewrite IHt2_1. rewrite IHt2_2. reflexivity.
Qed.

Hint Resolve erase_term_homo_subst.

Lemma pure_reduce_simulation_helper : forall l t1 t2,
  is_l_of_t l ->
  pure_reduce t1 t2 ->
  pure_reduce (erase_term l t1) (erase_term l t2).
Proof.
  intros l t1 t2 l_of_t H.
  generalize dependent t2.
  term_cases (induction t1) Case; intros t2 H.
    Case "term_LBot". apply labels_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_LA". apply labels_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_LB". apply labels_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_LTop". apply labels_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_VTrue". apply values_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_VFalse". apply values_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_VUnit". apply values_cannot_be_reduced in H. contradiction. simpl. trivial.
    Case "term_VAbs". inversion H.
    Case "term_VLIO". inversion H.
    Case "term_VLabeled". inversion H.
    Case "term_VException". inversion H.
    Case "term_VHole". inversion H. apply Pr_hole.
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
     SCase "appCtx".
     rewrite <- H1 in H.
     apply IHt1_1 in H3.
     simpl. apply Pr_appCtx. assumption.
     SCase "app".
     simpl. rewrite erase_term_homo_subst.
     apply Pr_app. assumption.
    Case "term_Fix". inversion H.
     SCase "fixCtx".
     rewrite <- H2 in H.
     apply IHt1 in H1.
     simpl. apply Pr_fixCtx. assumption.
     SCase "fix".
     simpl. rewrite erase_term_homo_subst.
     apply Pr_fix. assumption.
    Case "term_IfEl". inversion H.
     SCase "ifCtx".
     rewrite <- H1 in H.
     apply IHt1_1 in H4.
     simpl. apply Pr_ifCtx. assumption.
     SCase "ifTrue".
     simpl. apply Pr_ifTrue.
     SCase "ifFalse".
     simpl. apply Pr_ifFalse.
    Case "term_Join". inversion H.
      SCase "ctxL".
      simpl. apply Pr_joinCtxL. apply IHt1_1 in H3. assumption.
      SCase "ctxR".
      simpl. apply Pr_joinCtxR.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption. apply IHt1_2 in H4. assumption.
      SCase "joinBotL".
      simpl. subst. apply Pr_joinBotL.
      assert (erase_term l t2 = t2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t2 = t2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      SCase "joinBotR".
      simpl. subst. apply Pr_joinBotR.
      assert (erase_term l t2 = t2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t2 = t2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      SCase "joinEq".
      simpl. subst. apply Pr_joinEq.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption. reflexivity.
      SCase "joinAB".
      simpl. subst. assumption.
      SCase "joinBA".
      simpl. subst. assumption.
      SCase "joinTopL".
      simpl. subst. apply Pr_joinTopL.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      SCase "joinTopR".
      simpl. subst. apply Pr_joinTopR.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
    Case "term_Meet". inversion H.
      SCase "ctxL".
      simpl. apply Pr_meetCtxL. apply IHt1_1 in H3. assumption.
      SCase "ctxR".
      simpl. apply Pr_meetCtxR.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption. apply IHt1_2 in H4. assumption.
      SCase "meetBotL".
      simpl. subst. apply Pr_meetBotL.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      SCase "meetBotR".
      simpl. subst. apply Pr_meetBotR.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      SCase "meetEq".
      simpl. subst. apply Pr_meetEq.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption. reflexivity.
      SCase "meetAB".
      simpl. subst. assumption.
      SCase "meetBA".
      simpl. subst. assumption.
      SCase "meetTopL".
      simpl. subst. apply Pr_meetTopL.
      assert (erase_term l t2 = t2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t2 = t2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      SCase "meetTopR".
      simpl. subst. apply Pr_meetTopR.
      assert (erase_term l t2 = t2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t2 = t2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
    Case "term_CanFlowTo". inversion H.
      SCase "ctxL".
      simpl. apply Pr_canFlowToCtxL. apply IHt1_1 in H3. assumption.
      SCase "ctxR".
      simpl. apply Pr_canFlowToCtxR.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption. apply IHt1_2 in H4. assumption.
      SCase "canFlowToBot".
      simpl. subst. apply Pr_canFlowToBot.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      SCase "canFlowToEq".
      simpl. subst. apply Pr_canFlowToEq.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_2 = t1_2) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption. reflexivity.
      SCase "canFlowToAB".
      simpl. subst. assumption.
      SCase "canFlowToBA".
      simpl. subst. assumption.
      SCase "canFlowToTop".
      simpl. subst. apply Pr_canFlowToTop.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
      assert (erase_term l t1_1 = t1_1) as Hrwrite.
      SSCase "assertion". apply erase_label_id. assumption. assumption.
      rewrite Hrwrite. assumption.
    Case "term_Return". inversion H.
    Case "term_Bind". inversion H.
    Case "term_GetLabel". inversion H.
    Case "term_GetClearance". inversion H.
    Case "term_LabelOf". inversion H.
     SCase "labelOfCtx".
     simpl. apply Pr_labelOfCtx.
     apply IHt1 in H1. assumption.
     SCase "labelOf".
     simpl. destruct (canFlowTo t2 l === Some true).
     SSCase "true".
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. apply Pr_labelOf. assumption.
     SSCase "false".
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. apply Pr_labelOf. assumption.
    Case "term_Label". inversion H.
    Case "term_UnLabel". inversion H.
    Case "term_ToLabeled". inversion H.
    Case "term_LowerClr". inversion H.
    Case "term_ThrowLIO". inversion H.
    Case "term_CatchLIO". inversion H.
Qed.

Lemma pure_reduce_simulation : forall l t1 t2,
  is_l_of_t l ->
  pure_reduce t1 t2 ->
  pure_reduce_l l (erase_term l t1) (erase_term l t2).
Proof.
  intros l t1 t2 l_of_t H.
  assert (erase_term l t2 = (erase_term l (erase_term l t2))).
  rewrite <- erase_term_idempotent.
  reflexivity. assumption.
  rewrite -> H0.
  apply pure_reduce_l_step.
  assumption.
  apply pure_reduce_simulation_helper.
  assumption.
  assumption.
Qed.

(* -->L *)
Inductive lio_reduce_l : t -> nat -> m -> m -> Prop :=
   | lio_reduce_l_step : forall l n m1 m2,
     is_l_of_t l ->
     lio_reduce m1 n m2 ->
     lio_reduce_l l n m1 (erase_config l m2).

Lemma deterministic_lio_reduce_l : forall l n x y1 y2,
  lio_reduce_l l n x y1 ->
  lio_reduce_l l n x y2 ->
  y1 = y2.
Proof.
  intros l n x y1 y2 Hy1 Hy2.
  inversion Hy2.
  subst.
  inversion Hy1.
  subst.
  assert (m0 = m2 ).
  Case "assertion". apply deterministic_lio_reduce with (x := x) (n := n).
  assumption. assumption.
  subst. reflexivity.
Qed.

Hint Resolve deterministic_lio_reduce_l.

(*
XXX
Lemma deterministic_lio_reduce_l_gen : forall l n1 n2 x y1 y2,
  lio_reduce_l l n1 x y1 ->
  lio_reduce_l l n2 x y2 ->
  y1 = y2.
Proof.
  intros l n1 n2 x y1 y2 Hy1 Hy2.
  intros n_rel.
  inversion Hy2.
  subst.
  inversion Hy1.
  subst.
  assert (m0 = m2 ).
  Case "assertion". apply deterministic_lio_reduce with (x := x) (n := n).
  assumption. assumption.
  subst. reflexivity.
Qed.
*)

Lemma erase_config_homo_if : forall l (b : bool)  m1 m2,
  is_l_of_t l ->
  erase_config l (if b then m1 else m2) =
                  if b then erase_config l m1 else erase_config l m2.
Proof. intros. destruct b; eauto.
Qed.

Lemma erase_config_idempotent : forall l m1,
  is_l_of_t l ->
  erase_config l m1 = erase_config l (erase_config l m1).
Proof.
  intros.
  destruct m1.
  unfold erase_config.
  remember (canFlowTo t1 l === Some true).  destruct b.
  Case "t1 [= l".
  rewrite <- Heqb.
  rewrite <- erase_term_idempotent.
  reflexivity. assumption.
  Case "t1 [/= l".
  simpl.
  reflexivity.
Qed.

Lemma inv_erase_labeled : forall l b l1 (t2 : t),
  is_l_of_t l ->
  is_l_of_t l1 ->
  l1 [/= l ->
  t_VLabeled b l1 t_VHole = erase_term l (t_VLabeled b l1 t2).
Proof.
  intros.
  simpl.
  assert (erase_term l l1 = l1). rewrite erase_label_id. reflexivity. assumption. assumption.
  rewrite -> H2.
  rewrite H1.
  reflexivity.
Qed.

Lemma inv_erase_label : forall l l1 (t2 : t),
  is_l_of_t l ->
  is_l_of_t l1 ->
  l1 [/= l ->
  t_Label l1 t_VHole = erase_term l (t_Label l1 t2).
Proof.
  intros.
  simpl.
  assert (erase_term l l1 = l1). rewrite erase_label_id. reflexivity. assumption. assumption.
  rewrite -> H2.
  rewrite H1.
  reflexivity.
Qed.

Lemma inv_erase_conf0 : forall l l1 c1 (t2 : t),
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  l1 [/= l ->
  m_Config t_VHole t_VHole t_VHole = erase_config l (m_Config l1 c1 t2 ).
Proof.
  intros.
  simpl.
  rewrite H2.
  reflexivity.
Qed.

Lemma inv_erase_conf1 : forall l l1 c1 t1,
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l ->
  l1 [= l ->
  m_Config l1 c1 (erase_term l t1) = erase_config l (m_Config l1 c1 t1).
Proof.
  intros.
  simpl.
  rewrite H2.
  reflexivity.
Qed.

(*
Lemma inv_erase_return : forall l l1 c1 (t2 : t),
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l ->
  l1 [= l ->
  m_Config l1 c1 (t_Return (erase_term l t2)) = erase_config l (m_Config l1 c1 (t_Return t2)).
Proof.
  intros.
  simpl.
  rewrite H2.
  reflexivity.
Qed.

Lemma inv_erase_bind : forall l l1 c1 (t1 t2 : t),
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l ->
  l1 [= l ->
  m_Config l1 c1 (t_Bind (erase_term l t1) (erase_term l t2)) = erase_config l (m_Config l1 c1 (t_Bind t1 t2)).
Proof.
  intros.
  simpl.
  rewrite H2.
  reflexivity.
Qed.

Lemma inv_erase_app : forall l l1 c1 (t1 t2 : t),
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l ->
  l1 [= l ->
  m_Config l1 c1 (t_App (erase_term l t1) (erase_term l t2)) = erase_config l (m_Config l1 c1 (t_App t1 t2)).
Proof.
  intros.
  simpl.
  rewrite H2.
  reflexivity.
Qed.
*)


Lemma inv_erase_LIO : forall l b l1 c1 (t2 : t),
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l ->
  l1 [= l ->
  m_Config l1 c1 (t_VLIO b (erase_term l t2)) = erase_config l (m_Config l1 c1 (t_VLIO b t2)).
Proof.
  intros.
  simpl.
  rewrite H2.
  reflexivity.
Qed.

Lemma current_label_monotonicity : forall l1 c1 t1 n l2 c2 t2,
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  l1 [= l2.
Proof.
  intros.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent n.
  generalize dependent c1.
  generalize dependent l1.
  term_cases (induction t1) Case; intros;
  inversion H3; try repeat (subst; apply canFlowTo_reflexive; assumption).
  Case "term_Bind". subst.
  inversion H16. subst.
  apply IHt1_1 in H20. assumption.
  assumption. assumption. assumption. assumption.
  subst.
  apply canFlowTo_reflexive. assumption.
  subst.
  inversion H16. subst.
  apply IHt1_1 in H20. assumption.
  assumption. assumption. assumption. assumption.
  subst.
  apply canFlowTo_reflexive. assumption.
  Case "term_UnLabel". subst.
  inversion H3. subst.
  admit (* H20: l1 |_| l0 ~> l2
                l1 [= l2  by definitIon*).
  subst.
  inversion H3. subst.
  admit (* H20: l1 |_| l0 ~> l2
                l1 [= l2  by definitIon*).
  apply canFlowTo_reflexive. assumption.
  subst.
  admit (* H15: l1 |_| l0 ~> l2
                l1 [= l2  by definitIon*).
  subst.
  Case "term_CatchLIO". subst.
  inversion H16. subst.
  apply IHt1_1 in H20. assumption.
  assumption. assumption. assumption. assumption.
  subst.
  apply canFlowTo_reflexive. assumption.
  subst.
  inversion H16. subst.
  apply IHt1_1 in H20. assumption.
  assumption. assumption. assumption. assumption.
  subst.
  apply canFlowTo_reflexive. assumption.
Qed.

Lemma lio_reduce_multi_simulation_0_helper: forall l l1 c1 t1 l2 c2 t2 T1 T2,
  GtT G_nil t1 (T_TLIO T1) ->
  GtT G_nil t2 (T_TLIO T2) ->
  is_l_of_t l ->
  l1 [= l ->
  l2 [= l ->
  lio_reduce_multi (m_Config l1 c1 t1) 0 (m_Config l2 c2 t2) ->
  lio_reduce_multi (erase_config l (m_Config l1 c1 t1)) 0 (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l l1 c1 t1 l2 c2 t2 T1 T2 t1_type t2_type l_of_t l1_to_l l2_to_l H.
  generalize dependent t2.
  generalize dependent T2.
  generalize dependent c2.
  generalize dependent T1.
  term_cases (induction t1) Case; intros T1 t1_type c2 T2 t2 t2_type H; try inversion t1_type.
    Case "term_VLIO".
  inversion H. inversion H16. inversion H26. simpl. rewrite l2_to_l. apply LIO_done.
  assumption. assumption.
    Case "term_VHole".
  inversion H. inversion H13. simpl. apply LIO_done.
  subst. assumption. subst. assumption.
  subst. simpl. rewrite l2_to_l. inversion H13. subst.
  apply LIO_done. assumption. assumption.
  inversion H7. apply LIO_done. assumption. assumption.
  simpl. rewrite l2_to_l. apply LIO_done. assumption. assumption.
    Case "term_Var".
  inversion H. inversion H15. inversion H25. simpl. rewrite l2_to_l. apply LIO_done.
  assumption. assumption.
    Case "term_App".
  inversion H. inversion H17. inversion H27. simpl. rewrite l2_to_l. subst.
  apply LIO_onestep. assumption. assumption. assumption. assumption.
  apply LIO_pure. assumption. assumption.
  apply Pr_appCtx. apply pure_reduce_simulation_helper. assumption. assumption. auto.
  simpl. rewrite l2_to_l. subst.
  apply LIO_onestep. assumption. assumption. assumption. assumption.
  apply LIO_pure. assumption. assumption.
  rewrite erase_term_homo_subst.
  apply Pr_app. assumption. auto.
  simpl. rewrite l2_to_l. subst.
  apply LIO_done.
  assumption. assumption.
    Case "term_Fix".
  inversion H. inversion H15. inversion H25. simpl. rewrite l2_to_l. subst.
  apply LIO_onestep. assumption. assumption. assumption. assumption.
  apply LIO_pure. assumption. assumption.
  apply Pr_fixCtx. apply pure_reduce_simulation_helper. assumption. assumption. auto.
  simpl. rewrite l2_to_l. subst.
  apply LIO_onestep. assumption. assumption. assumption. assumption.
  apply LIO_pure. assumption. assumption.
  rewrite erase_term_homo_subst.
  apply Pr_fix. assumption. auto.
  simpl. rewrite l2_to_l. subst.
  apply LIO_done.
  assumption. assumption.
    Case "term_IfEl".
  inversion H. inversion H19. inversion H29. simpl. rewrite l2_to_l. subst.
  apply LIO_onestep. assumption. assumption. assumption. assumption.
  apply LIO_pure. assumption. assumption.
  apply Pr_ifCtx. apply pure_reduce_simulation_helper. assumption. assumption. auto.
  simpl. rewrite l2_to_l. subst.
  apply LIO_onestep. assumption. assumption. assumption. assumption.
  apply LIO_pure. assumption. assumption.
  apply Pr_ifTrue. eauto.
  simpl. rewrite l2_to_l. subst.
  apply LIO_onestep. assumption. assumption. assumption. assumption.
  apply LIO_pure. assumption. assumption.
  apply Pr_ifFalse. eauto.
  simpl. rewrite l2_to_l. subst.
  apply LIO_done. assumption. assumption.
    Case "term_Return". inversion H.  inversion H15.
     subst.
     simpl. rewrite l2_to_l.
     apply LIO_onestep. assumption. assumption. assumption. assumption.
     apply LIO_return. assumption. assumption. assumption.
     inversion H25. simpl. rewrite l2_to_l.
     apply LIO_done. assumption. assumption.
    Case "term_Bind". inversion H.  inversion H17.
     subst.
     simpl. rewrite l2_to_l.  rewrite l1_to_l.
     apply LIO_onestep. assumption. assumption. assumption. assumption.
     apply LIO_bind. assumption. assumption. assumption. assumption.
     rewrite inv_erase_LIO.
     rewrite inv_erase_conf1.
     apply IHt1_1 with (T1  := T3) (T2 := T3).
     inversion t1_type. subst.
     assumption. inversion t2_type. subst.
      assert (T3 = T4).
      SCase "assertion". admit.
      subst.
      apply GtT_lioVal. assumption.
     assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption. assumption.
     simpl. rewrite l2_to_l. rewrite l1_to_l.
     apply LIO_onestep. assumption. assumption. assumption. assumption.
     apply LIO_bindEx. assumption. assumption. assumption. assumption.
     rewrite inv_erase_LIO.
     rewrite inv_erase_conf1. subst.
     apply IHt1_1 with (T1 := T3) (T2 := T_TException).
     inversion t1_type. subst.
     assumption. subst. inversion t2_type. subst.
      apply GtT_lioVal. assumption.
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     inversion H27. simpl. rewrite l2_to_l.
     apply LIO_done. assumption. assumption.
    Case "term_GetLabel".
    inversion H. inversion H13. simpl. rewrite l2_to_l. rewrite erase_label_id.
    apply LIO_onestep.
    assumption. assumption. assumption. assumption.
    apply LIO_getLabel.
    assumption. assumption. assumption. assumption.
    assumption.
    inversion H23. simpl. rewrite l2_to_l.
    apply LIO_done. assumption. assumption.
    Case "term_GetClearance".
    inversion H. inversion H13. simpl. rewrite l2_to_l. rewrite erase_label_id.
    apply LIO_onestep.
    assumption. assumption. assumption. assumption.
    apply LIO_getClearance.
    assumption. assumption. assumption. assumption.
    assumption.
    inversion H23. simpl. rewrite l2_to_l.
    apply LIO_done. assumption. assumption.
    Case "term_Label". inversion H.  subst. inversion H17.
     subst.
     unfold erase_config.
     rewrite l2_to_l.
     simpl.
     assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
     SSCase "assertion". (* reducing label does not affect its value *) admit.
     rewrite H0.
     subst.
     remember (canFlowTo (erase_term l t1') l === Some true).  destruct b.
     SSCase "[=".
     apply LIO_onestep. assumption. assumption. assumption. assumption.
     apply LIO_labelCtx. assumption. assumption.
     apply pure_reduce_simulation_helper.
     assumption. assumption. assumption.
     SSCase "[/=".
     apply LIO_onestep. assumption. assumption. assumption. assumption.
     apply LIO_labelCtx. assumption. assumption.
     apply pure_reduce_simulation_helper.
     assumption. assumption. assumption.
     remember (canFlowTo (erase_term l t1_1) l === Some true).  destruct b.
     SSCase "[=".
     simpl.
     rewrite <- Heqb.
     rewrite l2_to_l.
     apply LIO_onestep. assumption. assumption.  assumption. assumption.
     apply LIO_label. assumption. assumption. rewrite erase_label_id.
     assumption. assumption. assumption. rewrite erase_label_id.
     assumption. assumption. assumption. rewrite erase_label_id.
     assumption. assumption. assumption. assumption.
     SSCase "[/=".
     simpl.
     rewrite <- Heqb.
     rewrite l2_to_l.
     apply LIO_onestep. assumption. assumption.  assumption. assumption.
     apply LIO_label. assumption. assumption. rewrite erase_label_id.
     assumption. assumption. assumption. rewrite erase_label_id.
     assumption. assumption. assumption. rewrite erase_label_id.
     assumption. assumption. assumption. assumption.
     inversion H11.
     unfold erase_config.
     rewrite l2_to_l.
     apply LIO_done.
     assumption. assumption.
    Case "term_UnLabel". inversion H.  subst. inversion H15.
     subst. simpl. rewrite l2_to_l.
     apply LIO_onestep.
     assumption. assumption. assumption. assumption.
     apply LIO_unlabelCtx.
     assumption. assumption.
     apply pure_reduce_simulation_helper.
     assumption. assumption. assumption.
     simpl. rewrite l2_to_l. rewrite l1_to_l.
     remember (canFlowTo (erase_term l l0) l === Some true).  destruct b.
     SCase "[=".
     apply LIO_onestep.
     assumption. assumption. assumption. assumption.
     apply LIO_unlabel.
     assumption. assumption. rewrite erase_label_id. assumption. assumption.
     assumption. assumption. rewrite erase_label_id. assumption. assumption.
     assumption. assumption. assumption.
     SCase "[/=". subst.
      (*  H16:     l2 = l1 |_| l0
          l1_to_l: l1 [= l
          l2_to_l: l2 [= l
          Heqb:    l0 [/= l
          contradiction: l2 [= l, i.e, l1 |_| l0 [= l so l0 [= l *)
      admit.
     simpl. rewrite l2_to_l. rewrite l1_to_l.
     remember (canFlowTo (erase_term l l0) l === Some true).  destruct b.
     SCase "[=".
     apply LIO_onestep.
     assumption. assumption. assumption. assumption.
     apply LIO_unlabelEx.
     assumption. assumption. rewrite erase_label_id. assumption. assumption.
     assumption. assumption. rewrite erase_label_id. assumption. assumption.
     assumption. assumption. assumption.
     SCase "[/=". subst.
      (*  H16:     l2 = l1 |_| l0
          l1_to_l: l1 [= l
          l2_to_l: l2 [= l
          Heqb:    l0 [/= l
          contradiction: l2 [= l, i.e, l1 |_| l0 [= l so l0 [= l *)
      admit.
     inversion H10. simpl. rewrite l2_to_l.
     apply LIO_done.
     assumption. assumption.
    Case "term_ToLabeled". inversion H.  subst. inversion H17.
      SCase "toLabeledCtx".
      subst. simpl. rewrite l2_to_l.
      apply LIO_onestep. assumption. assumption. assumption. assumption.
      apply LIO_toLabeledCtx.
      assumption. assumption.
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SCase "tolabeled".
      subst.
      assert (0 = n5 + 1 -> False).
      omega.
      apply H0 in H23.
      contradiction.
      assert (0 = n5 + 1 -> False).
      omega.
      apply H25 in H23.
      contradiction.
      inversion H11. simpl.
      assert (erase_term l l2 = l2). apply erase_label_id. assumption. assumption.
      rewrite l2_to_l.
      apply LIO_done. assumption. assumption.
    Case "term_LowerClr".
      inversion H. inversion H15. simpl. rewrite l2_to_l.
      subst.
      apply LIO_onestep. assumption. assumption. assumption. assumption.
      apply LIO_lowerClrCtx. assumption. assumption.
      apply pure_reduce_simulation_helper.
      assumption. assumption. assumption.
      subst. simpl. rewrite l2_to_l.
      apply LIO_onestep. assumption. assumption. assumption. assumption.
      rewrite erase_label_id.
      apply LIO_lowerClr. assumption. assumption.
      assumption. assumption. assumption.
      assumption. assumption. assumption.
      inversion H25. simpl. rewrite l2_to_l. apply LIO_done. assumption. assumption.
    Case "term_ThrowLIO".
      inversion H. inversion H15. simpl. rewrite l2_to_l.
      apply LIO_onestep. assumption. assumption. assumption. assumption.
      apply LIO_throwLIO. assumption. assumption. reflexivity.
      inversion H25. simpl. rewrite l2_to_l.
      apply LIO_done. assumption. assumption.
    Case "term_CatchLIO".
      inversion H. inversion H17. simpl. rewrite l2_to_l.  rewrite l1_to_l.
      apply LIO_onestep. assumption. assumption. assumption. assumption.
      apply LIO_catchLIO. assumption. assumption. assumption. assumption.
      rewrite inv_erase_LIO.
      rewrite inv_erase_conf1.
      subst.
      apply IHt1_1 with (T1  := T1) (T2 := T2).
      assumption.
      apply GtT_lioVal. inversion t2_type. assumption.
      assumption. assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. assumption.
      simpl. rewrite l2_to_l.  rewrite l1_to_l.
      apply LIO_onestep. assumption. assumption. assumption. assumption.
      apply LIO_catchLIOEx with (t1' := erase_term l t1'). assumption. assumption.
      assumption. assumption.
      subst.
      rewrite inv_erase_conf1.
      rewrite inv_erase_LIO.
      apply IHt1_1 with (T1  := T1) (T2 := T_TException).
      assumption. subst. inversion t2_type. subst.
      assert (T3 = T_TException).
      SCase "assertion". admit.
      subst. apply GtT_lioVal. assumption.
      assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. assumption.
      assumption.
      inversion H27. simpl. rewrite l2_to_l.
      apply LIO_done.
      assumption. assumption.
Qed.

Lemma lio_reduce_simulation_0_helper: forall l l1 c1 t1 l2 c2 t2 T1 T2,
  GtT G_nil t1 (T_TLIO T1) ->
  GtT G_nil t2 (T_TLIO T2) ->
  is_l_of_t l ->
  l1 [= l ->
  l2 [= l ->
  lio_reduce (m_Config l1 c1 t1) 0 (m_Config l2 c2 t2) ->
  lio_reduce (erase_config l (m_Config l1 c1 t1)) 0 (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l l1 c1 t1 l2 c2 t2 T1 T2 t1_type t2_type l_of_t l1_to_l l2_to_l H.
  generalize dependent t2.
  generalize dependent T2.
  generalize dependent c2.
  generalize dependent T1.
  term_cases (induction t1) Case; intros T1 t1_type c2 T2 t2 t2_type H; try inversion t1_type.
    Case "term_VLIO". inversion H. inversion H14.
    Case "term_VHole". inversion H. apply LIO_hole. inversion H11. simpl. rewrite l2_to_l. apply LIO_pure.
    assumption. assumption. apply Pr_hole. auto.
    Case "term_Var". inversion H. inversion H13.
    Case "term_App".  inversion H. inversion H15. simpl. rewrite l2_to_l.
      apply LIO_pure. assumption. assumption. apply Pr_appCtx.
      apply pure_reduce_simulation_helper.
      assumption. assumption. auto.
      inversion H15. simpl. rewrite l2_to_l. rewrite erase_term_homo_subst.
      apply LIO_pure. assumption. assumption.
      apply Pr_app. auto. assumption.
      simpl. rewrite l2_to_l. rewrite erase_term_homo_subst.
      apply LIO_pure. assumption. assumption.
      apply Pr_app. auto. assumption.
    Case "term_Fix". inversion H. inversion H13. simpl. rewrite l2_to_l.
      apply LIO_pure. assumption. assumption. apply Pr_fixCtx.
      apply pure_reduce_simulation_helper.
      assumption. assumption. auto.
      inversion H13. simpl. rewrite l2_to_l. rewrite erase_term_homo_subst.
      apply LIO_pure. assumption. assumption.
      apply Pr_fix. auto. assumption.
      simpl. rewrite l2_to_l. rewrite erase_term_homo_subst.
      apply LIO_pure. assumption. assumption.
      apply Pr_fix. auto. assumption.
    Case "term_IfEl". inversion H. inversion H17. simpl. rewrite l2_to_l.
      apply LIO_pure. assumption. assumption. apply Pr_ifCtx.
      apply pure_reduce_simulation_helper.
      assumption. assumption. auto.
      simpl. rewrite l2_to_l. apply LIO_pure. assumption. assumption. apply Pr_ifTrue. auto.
      simpl. rewrite l2_to_l. apply LIO_pure. assumption. assumption. apply Pr_ifFalse. auto.
    Case "term_Return". inversion H.
     subst.
     simpl. rewrite l2_to_l.
     apply LIO_return. assumption. assumption. assumption.
     inversion H13.
    Case "term_Bind". inversion H.
     subst. simpl. rewrite l1_to_l. rewrite l2_to_l.
     apply LIO_bind.
     assumption. assumption. assumption. assumption.
     rewrite inv_erase_conf1.
     rewrite inv_erase_LIO.
     apply lio_reduce_multi_simulation_0_helper with (T1:=T3) (T2:=T3).
     assumption. inversion t2_type. subst.
     assert (T3 = T4). admit (*see H5 & H3*). subst.
     apply GtT_lioVal. assumption.
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption.

     subst. simpl. rewrite l1_to_l. rewrite l2_to_l.
     apply LIO_bindEx.
     assumption. assumption. assumption. assumption.
     rewrite inv_erase_conf1.
     rewrite inv_erase_LIO.
     apply lio_reduce_multi_simulation_0_helper with (T1:=T3) (T2:=T_TException).
     assumption. inversion t2_type. subst.
     apply GtT_lioVal. assumption.
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption.
     inversion H15.
    Case "term_GetLabel". inversion H.
     subst.
     simpl. rewrite l2_to_l.
     rewrite erase_label_id.
     apply LIO_getLabel. assumption. assumption. assumption. assumption. assumption.
     inversion H11.
    Case "term_GetClearance". inversion H.
     subst.
     simpl. rewrite l2_to_l.
     rewrite erase_label_id.
     apply LIO_getClearance. assumption. assumption. assumption. assumption. assumption.
     inversion H11.
    Case "term_Label". inversion H.
     SCase "labelCtx".
     subst. simpl. rewrite l2_to_l.
     assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
     SSCase "assertion". (* reducing label does not affect its value *) admit.
     rewrite H0.
     destruct (canFlowTo (erase_term l t1') l === Some true).
     SSCase "t1' [= l".
     apply LIO_labelCtx.
     assumption. assumption.
     apply pure_reduce_simulation_helper.
     assumption. assumption. assumption.
     SSCase "t1' [/= l".
     apply LIO_labelCtx.
     assumption. assumption.
     apply pure_reduce_simulation_helper.
     assumption. assumption. assumption.
     SCase "label".
     subst. simpl. rewrite l2_to_l.
       assert (erase_term l t1_1 = t1_1) as Hrwrt.
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
       rewrite -> Hrwrt.
       remember (canFlowTo t1_1 l === Some true). destruct b.
       SSSCase "t1_1 [= l". apply LIO_label.
       assumption. assumption. assumption.
       assumption. assumption. assumption.
       SSSCase "t1_1 [/= l".
       apply LIO_label. assumption. assumption. assumption. assumption. assumption. assumption.
     inversion H15.
    Case "term_UnLabel". inversion H.
      SCase "unlabelCtx".
      subst. simpl. rewrite l2_to_l.
      apply LIO_unlabelCtx. assumption. assumption.
      apply pure_reduce_simulation_helper.
      assumption. assumption. assumption.
      SCase "unlabel".
      subst. simpl. rewrite l1_to_l. rewrite l2_to_l.
      assert (erase_term l l0 = l0) as Hrwrt.
      SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo l0 l === Some true). destruct b.
      SSSCase "l0 [= l". apply LIO_unlabel.
      assumption. assumption. assumption. assumption. assumption.
      assumption. assumption.
      SSSCase "l0 [/= l".
      (*  H11:     l2 = l1 |_| l0
          l1_to_l: l1 [= l
          l2_to_l: l2 [= l
          Heqb:    l0 [/= l
          contradiction: l2 [= l, i.e, l1 |_| l0 [= l so l0 [= l *)
      admit.

      subst. simpl. rewrite l1_to_l. rewrite l2_to_l.
      assert (erase_term l l0 = l0) as Hrwrt.
      SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo l0 l === Some true). destruct b.
      SSSCase "l0 [= l". apply LIO_unlabelEx.
      assumption. assumption. assumption. assumption. assumption.
      assumption. assumption.
      SSSCase "l0 [/= l".
      (*  H11:     l2 = l1 |_| l0
          l1_to_l: l1 [= l
          l2_to_l: l2 [= l
          Heqb:    l0 [/= l
          contradiction: l2 [= l, i.e, l1 |_| l0 [= l so l0 [= l *)
      admit.
      inversion H13.
    Case "term_ToLabeled". inversion H.
      SCase "toLabeledCtx".
      subst. simpl. rewrite l2_to_l.
      apply LIO_toLabeledCtx.
      assumption. assumption.
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SCase "tolabeled".
      subst.
      assert (0 = n5 + 1 -> False).
      omega.
      apply H0 in H22.
      contradiction.
      subst.
      assert (0 = n5 + 1 -> False).
      omega.
      apply H0 in H22.
      contradiction.
      inversion H15.
    Case "term_LowerClr". inversion H.
      SCase "lowerClrCtx".
      subst. simpl. rewrite l2_to_l.
      apply LIO_lowerClrCtx. assumption. assumption.
      apply pure_reduce_simulation_helper. assumption. assumption. reflexivity.
      SCase "lowerClr".
      subst. simpl. rewrite l2_to_l.
      assert (erase_term l c2 = c2). rewrite erase_label_id.
      reflexivity. assumption. assumption.
      rewrite H0.
      apply LIO_lowerClr. assumption. assumption.
      assumption. assumption. assumption. assumption.
      inversion H13.
    Case "term_ThrowLIO". inversion H.
      subst. simpl. rewrite l2_to_l.
      apply LIO_throwLIO. assumption. assumption. reflexivity.
      inversion H13.
    Case "term_CatchLIO". inversion H.
      subst. simpl. rewrite l2_to_l. rewrite l1_to_l.
      apply LIO_catchLIO. assumption. assumption. assumption. assumption.
      rewrite inv_erase_conf1.
      rewrite inv_erase_LIO.
      apply lio_reduce_multi_simulation_0_helper with (T1:=T1) (T2:=T2).
      assumption. inversion t2_type. subst.
      apply GtT_lioVal. assumption.
      assumption. assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. assumption. assumption.
      assumption. assumption.
      subst. simpl. rewrite l1_to_l. rewrite l2_to_l.
      apply LIO_catchLIOEx with (t1' := erase_term l t1'). assumption. assumption.
      assumption. assumption.
      rewrite inv_erase_conf1.
      rewrite inv_erase_LIO.
      apply lio_reduce_multi_simulation_0_helper with (T1:=T1) (T2:=T_TException).
      assumption. subst. inversion t2_type. subst.
      assert (T3 = T_TException). SCase "assertion". admit (*H5 & H3*). subst.
      subst. apply GtT_lioVal. assumption.
      assumption. assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. assumption. assumption.
      assumption. assumption.
      inversion H15.
Qed.

Lemma lio_reduce_simulation_1_helper: forall l n l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  is_l_of_t l1 -> is_l_of_t c1 ->
  is_l_of_t l2 -> is_l_of_t c2 ->
  l1 [/= l ->
  l2 [= l ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  lio_reduce (erase_config l (m_Config l1 c1 t1)) n (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l n l1 c1 t1 l2 c2 t2 l1_is_l c1_is_l l2_is_l c2_is_l l_of_t l1_to_l l2_to_l H.
  apply current_label_monotonicity in H.
  apply canFlowTo_transitivie with (l1 := l1) (l2 := l2) (l3 := l) in H.
  rewrite H in l1_to_l.
  solve by inversion.
  assumption. assumption. assumption. assumption. assumption. assumption.
  assumption. assumption.
Qed.

Lemma lio_reduce_simulation_2_helper: forall l n l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  l1 [/= l ->
  l2 [/= l ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  lio_reduce (erase_config l (m_Config l1 c1 t1)) n (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l n l1 c1 t1 l2 c2 t2 l_of_t l1_to_l l2_to_l H.
  simpl.
  rewrite l1_to_l.
  rewrite l2_to_l.
  apply LIO_hole.
Qed.

Lemma lio_reduce_simulation_3_unlabel : forall l n l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l1 [=l ->
  l2 [/= l ->
  lio_reduce (m_Config l1 c1 (t_UnLabel t1)) n (m_Config l2 c2 t2) ->
  lio_reduce_l l n (erase_config l (m_Config l1 c1 (t_UnLabel t1))) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l n l1 c1 t1 l2 c2 t2 l_of_t_l l_of_t_l1 l_of_t_c1 l_of_t_l2 l_of_t_c2
         H1 H H0.
    subst. inversion H0.
    SCase "term_UnLabelCtx". subst.
    rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_UnLabel t')).
    simpl. rewrite H1.
    apply lio_reduce_l_step.
    assumption.
    apply LIO_unlabelCtx.
    assumption. assumption.
    apply pure_reduce_simulation_helper.
    assumption. assumption. reflexivity.
    assumption.
    SCase "term_UnLabel". subst.
    rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Return t0)).
    remember (canFlowTo l0 l === Some true). destruct b.
    SSCase "l0 [= l".
    simpl.
    rewrite H. rewrite H1. rewrite erase_label_id. rewrite <- Heqb.
    rewrite inv_erase_conf0 with (l1 := l2) (c1 := c2) (t2 := t_Return (erase_term l t0)) (l := l).
    rewrite <- erase_config_idempotent.
    apply lio_reduce_l_step.
    assumption.
    apply LIO_unlabel.
    assumption. assumption. assumption. assumption.
    assumption. assumption. reflexivity. assumption.
    assumption. assumption. assumption. assumption.
    assumption. assumption.
    SSCase "l0 [/= l".
    simpl.
    rewrite H. rewrite H1. rewrite erase_label_id. rewrite <- Heqb.
    rewrite inv_erase_conf0 with (l1 := l2) (c1 := c2) (t2 := t_Return t_VHole) (l := l).
    rewrite <- erase_config_idempotent.
    apply lio_reduce_l_step.
    assumption.
    apply LIO_unlabel.
    assumption. assumption. assumption. assumption.
    assumption. assumption. reflexivity. assumption.
    assumption. assumption. assumption. assumption.
    assumption. assumption. assumption.
    SCase "term_UnLabelEx". subst.
    rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_ThrowLIO t0)).
    remember (canFlowTo (erase_term l l0) l  === Some true). destruct b.
    SSCase "l0 [= l".
    simpl.
    rewrite H. rewrite H1. rewrite <- Heqb.
    rewrite inv_erase_conf0 with (l1 := l2) (c1 := c2) (t2 := t_ThrowLIO (erase_term l t0)) (l := l).
    rewrite <- erase_config_idempotent.
    apply lio_reduce_l_step.
    assumption.
    apply LIO_unlabelEx.
    assumption. assumption. rewrite erase_label_id. assumption. assumption.
    assumption. assumption. rewrite erase_label_id. assumption. assumption.
    assumption. assumption. reflexivity. assumption.
    assumption. assumption. assumption. assumption.
    SSCase "l0 [/= l".
    simpl.
    rewrite H. rewrite H1. rewrite <- Heqb.
    rewrite inv_erase_conf0 with (l1 := l2) (c1 := c2) (t2 := t_ThrowLIO t_VHole) (l := l).
    rewrite <- erase_config_idempotent.
    apply lio_reduce_l_step.
    assumption.
    apply LIO_unlabelEx.
    assumption. assumption. rewrite erase_label_id. assumption. assumption.
    assumption. assumption. rewrite erase_label_id. assumption. assumption.
    assumption. assumption. reflexivity. assumption.
    assumption. assumption. assumption. assumption.
    assumption.
    inversion H11.
Qed.

Lemma lio_reduce_multi_helper: forall n l b l1 c1 t1 l2 c2 t2 T1,
  GtT G_nil t1 (T_TLIO T1) ->
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l1 [= l ->
  lio_reduce_multi (m_Config l1 c1 t1) n (m_Config l2 c2 (t_VLIO b t2)) ->
  lio_reduce_multi (m_Config l1 c1 (erase_term l t1)) n (m_Config l2 c2 (t_VLIO b (erase_term l t2))).
Proof.
  intros.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent c1.
  generalize dependent l1.
  generalize dependent b.
  generalize dependent T1.
  term_cases (induction t1) Case; intros; inversion H6; try (inversion H; inversion H18; inversion H28).
  Case "term_VLIO". subst.
    inversion H6.
    apply values_cannot_be_lio_reduced in H24. contradiction.
    simpl. trivial.
    simpl. apply LIO_done. assumption. assumption.
    subst.
    inversion H6. apply values_cannot_be_lio_reduced in H20. contradiction.
    simpl. trivial.
    simpl. apply LIO_done. assumption. assumption.
  Case "term_VHole". subst.
    inversion H18. subst. inversion H19. subst.
  Case "term_Var". subst.
    inversion H18. subst. inversion H19. subst.
  Case "term_App". subst.
    inversion H18. subst.
    apply LIO_onestep. assumption. assumption. assumption. assumption.
    apply LIO_pure. assumption. assumption.
    assert ( (t_VLIO b (erase_term l t2)) = erase_term l (t_VLIO b t2)).
    SCase "assertion". auto.
    rewrite H7.
    apply pure_reduce_simulation_helper.
    assumption. assumption. auto.
  Case "term_Fix". subst.
    inversion H18. subst.
    apply LIO_onestep. assumption. assumption. assumption. assumption.
    apply LIO_pure. assumption. assumption.
    assert ( (t_VLIO b (erase_term l t2)) = erase_term l (t_VLIO b t2)).
    SCase "assertion". auto.
    rewrite H7.
    apply pure_reduce_simulation_helper.
    assumption. assumption. auto.
  Case "term_IfEl". subst.
    inversion H18. subst.
    apply LIO_onestep. assumption. assumption. assumption. assumption.
    apply LIO_pure. assumption. assumption.
    assert ( (t_VLIO b (erase_term l t2)) = erase_term l (t_VLIO b t2)).
    SCase "assertion". auto.
    rewrite H7.
    apply pure_reduce_simulation_helper.
    assumption. assumption. auto.
  Case "term_Return". simpl. subst.
    inversion H18. subst.
    apply LIO_onestep. assumption. assumption. assumption. assumption.
    simpl. apply LIO_return. assumption. assumption. auto.
    subst. inversion H21.
  Case "term_Bind". subst.
    inversion H18. subst. inversion H19.
  Case "term_GetLabel". subst.
    inversion H18. subst. inversion H19.
  Case "term_GetClearance". subst.
    inversion H18. subst. inversion H19.
  Case "term_Label". subst.
    inversion H18. subst. inversion H19.
  Case "term_UnLabel". subst.
    inversion H18. subst. inversion H19.
  Case "term_ToLabeled". subst.
    inversion H18. subst. inversion H19.
  Case "term_LowerClr". subst.
    inversion H18. subst. inversion H19.
  Case "term_ThrowLIO". subst.
    apply LIO_onestep. assumption. assumption. assumption. assumption.
    simpl. inversion H18. apply LIO_throwLIO. assumption. assumption.
    auto. inversion H21.
  Case "term_CatchLIO". subst.
    inversion H18. subst. inversion H19.
Qed.

Lemma lio_reduce_simulation_3_catchLIO : forall l n l1 c1 t1_1 t1_2 l2 c2 t2 T1,
  GtT G_nil t1_1 (T_TLIO T1) ->
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l1 [=l ->
  l2 [/= l ->
  lio_reduce (m_Config l1 c1 (t_CatchLIO t1_1 t1_2)) n (m_Config l2 c2 t2) ->
  lio_reduce_l l n (erase_config l (m_Config l1 c1 (t_CatchLIO t1_1 t1_2))) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l n l1 c1 t1_1 t1_2 l2 c2 t2 T1 t1_1_type l_of_t_l l_of_t_l1 l_of_t_c1 l_of_t_l2 l_of_t_c2
         H1 H H0.
  subst.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent t1_2.
  generalize dependent c1.
  generalize dependent l1.
  generalize dependent l_of_t_l.
  generalize dependent n.
  generalize dependent l.
  generalize dependent T1.
  term_cases (induction t1_1) Case; intros; try (inversion t1_1_type).
  Case "term_VLIO".
    subst. inversion H0. subst.
    inversion H15. subst.
    apply values_cannot_be_lio_reduced in H19. contradiction.
    simpl. trivial. subst.
    rewrite H1 in H. solve by inversion.
    subst. inversion H0. subst.
    inversion H15. subst.
    apply values_cannot_be_lio_reduced in H24. contradiction.
    simpl. trivial. subst.
    rewrite H1 in H. solve by inversion.
    inversion H17.
    inversion H12.
  Case "term_VHole".
    inversion H0. subst. inversion H16. subst. inversion H18. subst. inversion H21. subst.
    inversion H16. subst. inversion H18. subst. inversion H21. subst.
    inversion H13.
  Case "term_Var".
    inversion H0. subst. inversion H18. subst. inversion H19. subst.
    inversion H22. subst. inversion H18. subst. inversion H19. subst.
    inversion H22. inversion H15.
  Case "term_App".
    inversion H0. subst. inversion H20. subst. inversion H16. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H20. subst. inversion H16. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_Fix".
    inversion H0. subst. inversion H18. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H18. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_IfEl".  subst.
    inversion H0. subst. inversion H17. subst. inversion H21. subst. inversion H24. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H17. subst. inversion H21. subst. inversion H24. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_Return".
    subst. inversion H0. subst. inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_Bind".
    subst. inversion H0. subst. inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_GetLabel".
    subst. inversion H0. subst. inversion H14. subst. inversion H18. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H14. subst. inversion H18. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_GetClearance".
    subst. inversion H0. subst. inversion H14. subst. inversion H18. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H14. subst. inversion H18. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_Label".
    subst. inversion H0. subst. inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_UnLabel".
    subst. inversion H0. subst. inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_ToLabeled".
    subst. inversion H0. subst. inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_LowerClr".
    subst. inversion H0. subst. inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_ThrowLIO".
    subst. inversion H0. subst. inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_CatchLIO".
    subst. inversion H0. subst. inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
Qed.


Lemma lio_reduce_simulation_3_bind : forall l n l1 c1 t1_1 t1_2 l2 c2 t2 T1,
  GtT G_nil t1_1 (T_TLIO T1) ->
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l1 [=l ->
  l2 [/= l ->
  lio_reduce (m_Config l1 c1 (t_Bind t1_1 t1_2)) n (m_Config l2 c2 t2) ->
  lio_reduce_l l n (erase_config l (m_Config l1 c1 (t_Bind t1_1 t1_2))) (erase_config l (m_Config l2 c2 t2)).
Proof.
(* TODO:  proofexactly as for catchLIO above *)
  intros l n l1 c1 t1_1 t1_2 l2 c2 t2 T1 t1_1_type l_of_t_l l_of_t_l1 l_of_t_c1 l_of_t_l2 l_of_t_c2
         H1 H H0.
    subst.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent t1_2.
  generalize dependent c1.
  generalize dependent l1.
  generalize dependent l_of_t_l.
  generalize dependent n.
  generalize dependent l.
  generalize dependent T1.
  term_cases (induction t1_1) Case; intros; try (inversion t1_1_type).
  Case "term_VLIO". subst. inversion H0. subst.
    inversion H15. subst.
    apply values_cannot_be_lio_reduced in H19. contradiction.
    simpl. trivial. subst.
    rewrite H1 in H. solve by inversion.
    subst. inversion H0. subst.
    inversion H15. subst.
    apply values_cannot_be_lio_reduced in H24. contradiction.
    simpl. trivial. subst.
    rewrite H1 in H. solve by inversion.
    inversion H17.
    inversion H12.
  Case "term_VHole".
    inversion H0. subst. inversion H16. subst. inversion H18. subst. inversion H21. subst.
    inversion H16. subst. inversion H18. subst. inversion H21. subst.
    inversion H13.
  Case "term_Var".
    inversion H0. subst. inversion H18. subst. inversion H19. subst.
    inversion H22. subst. inversion H18. subst. inversion H19. subst.
    inversion H22. inversion H15.
  Case "term_App".
    inversion H0. subst. inversion H20. subst. inversion H16. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H20. subst. inversion H16. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_Fix".
    inversion H0. subst. inversion H18. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H18. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_IfEl".  subst.
    inversion H0. subst. inversion H17. subst. inversion H21. subst. inversion H24. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H17. subst. inversion H21. subst. inversion H24. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_Return".
    subst. inversion H0. subst. inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_Bind".
    subst. inversion H0. subst. inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_GetLabel".
    subst. inversion H0. subst. inversion H14. subst. inversion H18. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H14. subst. inversion H18. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_GetClearance".
    subst. inversion H0. subst. inversion H14. subst. inversion H18. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H14. subst. inversion H18. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_Label".
    subst. inversion H0. subst. inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_UnLabel".
    subst. inversion H0. subst. inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_ToLabeled".
    subst. inversion H0. subst. inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_LowerClr".
    subst. inversion H0. subst. inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_ThrowLIO".
    subst. inversion H0. subst. inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H15. subst. inversion H19. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
  Case "term_CatchLIO".
    subst. inversion H0. subst. inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    inversion H16. subst. inversion H20. subst.
    rewrite H1 in H. solve by inversion. subst.
    rewrite H1 in H. solve by inversion.
Qed.

Lemma lio_reduce_simulation_3_helper : forall l n l1 c1 t1 l2 c2 t2 T1,
  GtT G_nil t1 (T_TLIO T1) ->
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l1 [=l ->
  l2 [/= l ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  lio_reduce_l l n (erase_config l (m_Config l1 c1 t1)) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l n l1 c1 t1 l2 c2 t2 T1 t1_type l_of_t_l l_of_t_l1 l_of_t_c1 l_of_t_l2 l_of_t_c2
         H1.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent n.
  generalize dependent l1.
  generalize dependent l_of_t_l.
  generalize dependent t1_type.
  term_cases (induction t1) Case; intros; try (inversion H0; subst; rewrite H1 in H; solve by inversion).
  Case "term_Bind".
    inversion t1_type. subst.
    apply lio_reduce_simulation_3_bind with (T1 := T0).
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption. assumption.
  Case "term_UnLabel".
    apply lio_reduce_simulation_3_unlabel.
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption.
  Case "term_CatchLIO".
    inversion t1_type. subst.
    apply lio_reduce_simulation_3_catchLIO with (T1 := T1).
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. assumption. assumption.
Qed.

Lemma lio_reduce_simulation_0 : forall l l1 c1 t1 l2 c2 t2 T1 T2,
  GtT G_nil t1 (T_TLIO T1) ->
  GtT G_nil t2 (T_TLIO T2) ->
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  lio_reduce (m_Config l1 c1 t1) 0 (m_Config l2 c2 t2) ->
  lio_reduce_l l 0 (erase_config l (m_Config l1 c1 t1)) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros.
  simpl.
  remember (canFlowTo l1 l === Some true). destruct b.
  Case "[=".
  remember (canFlowTo l2 l === Some true). destruct b.
  SCase "[=".
     rewrite inv_erase_conf1.
     rewrite inv_erase_conf1.
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 t2).
     apply lio_reduce_l_step.
     assumption.
     apply lio_reduce_simulation_0_helper with (T1 := T1) (T2 := T2).
     assumption. assumption.
     assumption. rewrite <- Heqb. trivial. rewrite <- Heqb0. trivial.
     assumption. assumption. assumption. assumption.
     assumption. rewrite <- Heqb0. trivial. assumption.
     assumption. assumption. rewrite <- Heqb. trivial.
  SCase "[/=".
     rewrite inv_erase_conf1.
     rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := t2).
     apply lio_reduce_simulation_3_helper with (T1 := T1).
     assumption. assumption. assumption. assumption. assumption. assumption.
     rewrite <- Heqb. trivial. rewrite <- Heqb0. trivial.
     assumption. assumption. assumption. assumption.
     rewrite <- Heqb0. trivial. assumption. assumption. assumption.
     rewrite <- Heqb. trivial.
  Case "[/=".
  remember (canFlowTo l2 l === Some true). destruct b.
  SCase "[=".
     rewrite inv_erase_conf1.
     rewrite inv_erase_conf0 with (l := l) (l1 := l1) (c1 := c1) (t2 := t1).
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 t2).
     apply lio_reduce_l_step. assumption.
     apply lio_reduce_simulation_1_helper.
     assumption. assumption. assumption. assumption. assumption.
     rewrite <- Heqb. trivial. rewrite <- Heqb0. trivial.
     assumption. assumption. assumption. assumption. assumption.
     rewrite <- Heqb. trivial. assumption. assumption. assumption.
     rewrite <- Heqb0. trivial.
  SCase "[/=".
     assert (lio_reduce_l l 0 (m_Config t_VHole t_VHole t_VHole)
                  (m_Config t_VHole t_VHole t_VHole) =
             lio_reduce_l l 0 (erase_config l (m_Config l1 c1 t1))
                  (erase_config l (erase_config l (m_Config l2 c2 t2)))).
     simpl. rewrite <- Heqb. rewrite <- Heqb0. reflexivity.
     rewrite H7.
     apply lio_reduce_l_step. assumption.
     apply lio_reduce_simulation_2_helper with (n := 0).
     assumption.
     rewrite <- Heqb. trivial. rewrite <- Heqb0. trivial. assumption.
Qed.

Lemma lio_reduce_simulation_n_helper': forall n l l1 c1 t1 l2 c2 t2 T1,
  GtT G_nil t1 (T_TLIO T1) ->
  is_l_of_t l ->
  l1 [= l ->
  l2 [= l ->
  lio_reduce (m_Config l1 c1 t1) (S n) (m_Config l2 c2 t2) ->
  lio_reduce_l l (S n) (erase_config l (m_Config l1 c1 t1)) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros n l l1 c1 t1 l2 c2 t2 T1 t1_type l_of_t l1_to_l l2_to_l H.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent c1.
  generalize dependent l1.
  generalize dependent l.
  generalize dependent n.
  generalize dependent T1.
  term_cases (induction t1) Case;
    intros; try (inversion H; subst; try (rewrite l2_to_l in H); solve by inversion).
    Case "term_Bind". inversion H.
     SCase "bind".
     subst.
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_App t1_2 t1')).
     simpl. rewrite l1_to_l. rewrite l2_to_l.
     apply lio_reduce_l_step. assumption.
     apply LIO_bind. assumption. assumption. assumption. assumption.
     inversion t1_type. subst.
     apply lio_reduce_multi_helper with (T1 := T0).
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     SCase "bindEx".
     subst.
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_ThrowLIO t1')).
     simpl. rewrite l1_to_l. rewrite l2_to_l.
     apply lio_reduce_l_step. assumption.
     apply LIO_bindEx. assumption. assumption. assumption. assumption.
     inversion t1_type. subst.
     apply lio_reduce_multi_helper with (T1 := T0).
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     inversion H9.
    Case "term_ToLabeled". inversion H.
      SCase "toLabeledCtx". subst.
      inversion H11.
      SCase "tolabeled". subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Label t1_1 t')).
      simpl.
      rewrite l1_to_l.
      assert (erase_term l t1_1 = t1_1) as Hrwrt.
      SSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo t1_1 l === Some true). destruct b.
      SSCase "t1_1 [= l".
      apply lio_reduce_l_step. assumption.
      apply LIO_toLabeled with (n5 := n5) (l' := l') (c' := c').
      assumption. assumption. assumption. assumption.
      assumption. assumption. assumption.
      inversion t1_type.
      apply lio_reduce_multi_helper with (T1 := T5).
      assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. assumption.
      assumption. assumption.
      SSCase "t1_1 [/= l".
      rewrite inv_erase_label with (l:=l) (t2:= erase_term l t').
      rewrite inv_erase_conf1.
      rewrite <- erase_config_idempotent.
      apply lio_reduce_l_step. assumption.
      apply LIO_toLabeled with (n5:=n5) (l':=l') (c':=c').
      assumption. assumption. assumption. assumption. assumption. assumption.
      assumption.
      inversion t1_type.
      apply lio_reduce_multi_helper with (T1 := T5).
      assumption. assumption. assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. assumption. assumption. rewrite <- Heqb.
      reflexivity. assumption.
      SCase "tolabeledEx". subst.
      rewrite erase_config_idempotent with
      (m1 := (m_Config l2 c2 (t_Return (t_VLabeled true l2 t')))).
      simpl. rewrite l2_to_l.
      assert (erase_term l l2 = l2). rewrite erase_label_id.
      reflexivity. assumption. assumption.
      rewrite H0. rewrite l2_to_l.
      apply lio_reduce_l_step. assumption.
      apply LIO_toLabeledEx with (n5:= n5) (l' := l') (c':=c').
      assumption. assumption. rewrite erase_label_id. assumption. assumption.
      assumption. assumption. assumption. rewrite erase_label_id. assumption.
      assumption. assumption. rewrite erase_label_id. assumption.
      assumption. assumption.
      inversion t1_type.
      apply lio_reduce_multi_helper with (T1 := T5).
      assumption. assumption. assumption. assumption.
      assumption. assumption. assumption.
      assumption. assumption.  rewrite erase_label_id. assumption.
      assumption. assumption. assumption.
      inversion H9.
    Case "term_CatchLIO". inversion H.
     SCase "no ex".
     subst.
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Return t1')).
     simpl. rewrite l1_to_l. rewrite l2_to_l.
     apply lio_reduce_l_step. assumption.
     apply LIO_catchLIO. assumption. assumption. assumption. assumption.
     inversion t1_type.
     apply lio_reduce_multi_helper with (T1 := T1).
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     SCase "ex".
     subst.
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_App t1_2 t1')).
     simpl. rewrite l1_to_l. rewrite l2_to_l.
     apply lio_reduce_l_step. assumption.
     apply LIO_catchLIOEx. assumption. assumption. assumption. assumption.
     inversion t1_type.
     apply lio_reduce_multi_helper with (T1 := T1).
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     inversion H9.
Qed.

Lemma lio_reduce_simulation_n_helper: forall n l l1 c1 t1 l2 c2 t2 T1 T2,
  GtT G_nil t1 (T_TLIO T1) ->
  GtT G_nil t2 (T_TLIO T2) ->
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l1 [= l ->
  l2 [= l ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  lio_reduce_l l n (erase_config l (m_Config l1 c1 t1)) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros.
  induction n as [| n' ].
  Case "0".
  apply lio_reduce_simulation_0 with (T1 := T1) (T2 := T2).
  assumption. assumption. assumption. assumption. assumption.
  assumption. assumption. assumption.
  Case "S n".
  apply lio_reduce_simulation_n_helper' with (T1 := T1).
  assumption. assumption. assumption. assumption. assumption.
Qed.

Lemma lio_reduce_simulation_n : forall n l l1 c1 t1 l2 c2 t2 T1 T2,
  GtT G_nil t1 (T_TLIO T1) ->
  GtT G_nil t2 (T_TLIO T2) ->
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  lio_reduce_l l n (erase_config l (m_Config l1 c1 t1)) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros.
  simpl.
  remember (canFlowTo l1 l === Some true). destruct b.
  Case "[=".
  remember (canFlowTo l2 l === Some true). destruct b.
  SCase "[=".
    rewrite inv_erase_conf1.
    rewrite inv_erase_conf1.
    apply lio_reduce_simulation_n_helper with (T1 := T1) (T2 := T2).
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption.
    rewrite <- Heqb. reflexivity.
    rewrite <- Heqb0. reflexivity.
    assumption. assumption. assumption. assumption.
    rewrite <- Heqb0. reflexivity.
    assumption. assumption. assumption.
    rewrite <- Heqb. reflexivity.
  SCase "[/=".
    rewrite inv_erase_conf1.
    rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := t2).
    apply lio_reduce_simulation_3_helper with (T1 := T1).
    assumption. assumption. assumption. assumption. assumption. assumption.
    rewrite <- Heqb. trivial. rewrite <- Heqb0. trivial.
    assumption. assumption. assumption. assumption.
    rewrite <- Heqb0. trivial. assumption. assumption. assumption.
    rewrite <- Heqb. trivial.
  Case "[/=".
  remember (canFlowTo l2 l === Some true). destruct b.
  SCase "[=".
    rewrite inv_erase_conf0 with (l := l) (l1 := l1) (c1 := c1) (t2 := t1).
    rewrite inv_erase_conf1.
    rewrite erase_config_idempotent with (m1 := m_Config l2 c2 t2).
    apply lio_reduce_l_step. assumption.
    apply lio_reduce_simulation_1_helper.
    assumption. assumption. assumption. assumption. assumption.
    rewrite <- Heqb. reflexivity.
    rewrite <- Heqb0. reflexivity.
    assumption. assumption. assumption. assumption. assumption.
    rewrite <- Heqb0. reflexivity.
    assumption. assumption. assumption.
    rewrite <- Heqb. reflexivity.
  SCase "[/=".
     assert (lio_reduce_l l n (m_Config t_VHole t_VHole t_VHole)
                  (m_Config t_VHole t_VHole t_VHole) =
             lio_reduce_l l n (erase_config l (m_Config l1 c1 t1))
                  (erase_config l (erase_config l (m_Config l2 c2 t2)))).
     simpl. rewrite <- Heqb. rewrite <- Heqb0. reflexivity.
     rewrite H7.
     apply lio_reduce_l_step. assumption.
     apply lio_reduce_simulation_2_helper.
     assumption.
     rewrite <- Heqb. trivial. rewrite <- Heqb0. trivial. assumption.
Qed.

Inductive lio_reduce_l_multi : t -> n -> m -> m -> Prop :=
 | LIO_l_onestep : forall l n m1 m2,
     is_l_of_t l ->
     lio_reduce_l l n m1 m2 ->
     lio_reduce_l_multi l n m1 m2
 | LIO_l_done : forall l n m1,
     is_l_of_t l ->
     lio_reduce_l_multi l n m1 m1.

Tactic Notation "lio_reduce_l_multi_cases" tactic(first) ident(c) :=
 first;
  [ Case_aux c "LIO_l_onestep"
  | Case_aux c "LIO_l_done"].

Lemma simulation_multi: forall n l l1 c1 t1 l2 c2 t2 T1 T2,
  GtT G_nil t1 (T_TLIO T1) ->
  GtT G_nil t2 (T_TLIO T2) ->
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  lio_reduce_multi (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  lio_reduce_l_multi l n (erase_config l (m_Config l1 c1 t1)) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros. inversion H6.
  Case "onestep".
  apply LIO_l_onestep.
  assumption.
  apply lio_reduce_simulation_n with (T1 := T1) (T2 := T2).
  assumption. assumption. assumption. assumption. assumption. assumption.
  assumption. assumption.
  Case "done".
  apply LIO_l_done.
  assumption.
Qed.


Lemma lio_reduce_l_refl : forall l n l1 c1 b1 t1 l2 c2 b2 t2,
   lio_reduce_l_multi l n (m_Config l1 c1 (t_VLIO b1 t1))  (m_Config l2 c2 (t_VLIO b2 t2)) ->
   l1 = l2 /\ c1 = c2 /\ t1 = t2 /\ b1 = b2.
Proof.
  intros.
  term_cases (induction t1) Case.
  Case "term_LBot".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_LA".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_LB".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_LTop".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_VTrue".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_VFalse".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_VUnit".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_VAbs".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_VLIO".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_VLabeled".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto. subst.
  Case "term_VException".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto. subst.
  Case "term_VHole".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_Var".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_App".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_Fix".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_IfEl".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_Join".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_Meet".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_CanFlowTo".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_Return".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_Bind".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_GetLabel".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_GetClearance".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_LabelOf".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_Label".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_UnLabel".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_ToLabeled".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_LowerClr".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_ThrowLIO".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
  Case "term_CatchLIO".
  inversion H. subst. inversion H1. subst.
  apply values_cannot_be_lio_reduced in H7. contradiction.
  unfold is_v_of_t. trivial. eauto.
Qed.


(*
Lemma deterministic_lio_reduce_l_multi : forall lA l c t n l1 c1 b1 t1 l2 c2 b2 t2,
  is_l_of_t lA ->
  lio_reduce_l_multi lA n (m_Config l c t) (m_Config l1 c1 (t_VLIO b1 t1)) ->
  lio_reduce_l_multi lA n (m_Config l c t) (m_Config l2 c2 (t_VLIO b2 t2)) ->
  l1 = l2 /\ c1 = c2 /\ t1 = t2 /\ b1 = b2.
Proof.
  intros lA l c t n l1 c1 b1 t1 l2 c2 b2 t2 lA_is_l H H0.
  term_cases (induction t) Case.
  Case "term_LBot". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_LBot).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LA". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_LA).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LB". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_LB).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LTop". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_LTop).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VTrue". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VTrue).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VFalse". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VFalse).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VUnit". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VUnit).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VAbs". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_VAbs x t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VLIO". intros.
  assert (l = l1 /\ c = c1 /\ t = t1 /\ b5 = b1) as Hrwrt1.
  SCase "assertion". apply lio_reduce_l_refl with (l := lA) (n := n). assumption.
  assert (l = l2 /\ c = c2 /\ t = t2 /\ b5 = b2) as Hrwrt2.
  SCase "assertion". apply lio_reduce_l_refl with (l := lA) (n := n). assumption.
  inversion Hrwrt1. inversion Hrwrt2. inversion H2. inversion H6.
  inversion H4. inversion H8. subst. assumption.
  Case "term_VLabeled". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_VLabeled b5 t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VException". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VException).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VHole". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VHole).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Var". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Var x)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_App". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_App t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Fix". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Fix t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_IfEl". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_IfEl t3 t4 t5)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Join". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Join t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Meet". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Meet t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_CanFlowTo". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_CanFlowTo t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Return". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Return t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Bind". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Bind t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_GetLabel". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_GetLabel)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_GetClearance". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_GetClearance)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LabelOf". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_LabelOf t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Label". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Label t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_UnLabel". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_UnLabel t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_ToLabeled". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_ToLabeled t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LowerClr". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_LowerClr t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_ThrowLIO". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_ThrowLIO t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_CatchLIO". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO b1 t1)) = (m_Config l2 c2 (t_VLIO b2 t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_CatchLIO t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
Qed.

Lemma label_does_not_decrease : forall lA l c t n l1 c1 b1 t1,
  is_l_of_t lA ->
  is_l_of_t l  ->
  is_l_of_t c  ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  l [/= lA ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) ->
  l1 [/= lA.
Proof.
  intros. simpl in H5.
  rewrite H4 in H5.
  remember (canFlowTo l1 lA === Some true). destruct b.
  Case "l1 [= lA". inversion H5. subst. inversion H7. subst. inversion H13. subst.
  inversion H8. subst. inversion H14.
  Case "l1 [/= lA". reflexivity.
Qed.

Lemma deterministic_lio_reduce_l_multi0 : forall lA l c t n l1 c1 b1 t1 l2 c2 b2 t2,
  is_l_of_t lA ->
  is_l_of_t l  ->
  is_l_of_t c  ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l [/= lA ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l2 c2 (t_VLIO b2 t2))) ->
  (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) = (erase_config lA (m_Config l2 c2 (t_VLIO b2 t2))).
Proof.
  intros.
  assert (l1 [/= lA).
  Case "assertion".
  apply label_does_not_decrease with (l := l) (c := c) (t0 := t) (n := n) (c1 := c1) (t1 := t1) (b1 := b1).
  assumption. assumption. assumption. assumption. assumption. eauto. assumption.
  assert (l2 [/= lA).
  Case "assertion".
  apply label_does_not_decrease with (l := l) (c := c) (t0 := t) (n := n) (c1 := c2) (t1 := t2) (b1 := b2).
  assumption. assumption. assumption. assumption. assumption. eauto. assumption.
  simpl.
  rewrite H9. rewrite H10.
  reflexivity.
Qed.

Lemma deterministic_lio_reduce_l_multi1 : forall lA l c t n l1 c1 b1 t1 l2 c2 b2 t2,
  is_l_of_t lA ->
  l [= lA ->
  (l1 [= lA /\ l2 [= lA) \/ (l1 [/= lA /\ l2 [/= lA) ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l2 c2 (t_VLIO b2 t2))) ->
  (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) = (erase_config lA (m_Config l2 c2 (t_VLIO b2 t2))).
Proof.
  intros.
  simpl.
  destruct H1.
  Case "l1 [= A /\ l2 [= lA".
  destruct H1.
  simpl in H2. rewrite H1 in H2. rewrite H0 in H2.
  simpl in H3. rewrite H4 in H3. rewrite H0 in H3.
  simpl in H1. rewrite H1. rewrite H4.
  assert (l1 = l2 /\ c1 = c2 /\ erase_term lA t1 = erase_term lA t2 /\ b1 = b2).
  SCase "assertion". apply deterministic_lio_reduce_l_multi with (lA := lA) (l := l) (c := c) (t0 := erase_term lA t) (n := n).
  assumption. assumption. assumption.
  inversion H5. subst l1. inversion H7. subst c1. inversion H8. subst b1.
  inversion H6. reflexivity.
  Case "l1 [/= A /\ l2 [/= lA".
  destruct H1.
  simpl in H2. rewrite H1 in H2. rewrite H0 in H2.
  simpl in H3. rewrite H4 in H3. rewrite H0 in H3.
  simpl in H1. rewrite H1. rewrite H4.
  reflexivity.
Qed.

Lemma deterministic_lio_reduce_l_multi2: forall lA l c t n l1 c1 b1 t1 l2 c2 b2 t2 ,
  is_l_of_t lA ->
  is_l_of_t l ->
  is_l_of_t c ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l [= lA ->
  l1 [= lA ->
  l2 [/= lA ->
  lio_reduce_l_multi lA n (m_Config l c (erase_term lA t)) (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) ->
  lio_reduce_l_multi lA n (m_Config l c (erase_term lA t)) (erase_config lA (m_Config l2 c2 (t_VLIO b2 t2))) ->
  (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) = (erase_config lA (m_Config l2 c2 (t_VLIO b2 t2))).
Proof.
  intros.
  generalize dependent t2.
  lio_reduce_l_multi_cases(inversion H9) Case.
  Case "LIO_l_onestep". intros.
  simpl in H9. simpl in H16.
  rewrite H7 in H9. rewrite H8 in H16.
  lio_reduce_l_multi_cases(inversion H16) SCase.
  SCase "LIO_l_onestep".
  simpl in H11. rewrite H7 in H11.
  assert ( (m_Config l1 c1 (t_VLIO b1 (erase_term lA t1))) = m_Config t_VHole t_VHole t_VHole).
  apply deterministic_lio_reduce_l with (l := lA) (n := n) (x := m_Config l c (erase_term lA t)).
  assumption. assumption.  inversion H23.
  SCase "LIO_l_done". rewrite H17 in H0. inversion H0.
  Case "LIO_l_done". intros.
  simpl in H9. simpl in H15.
  rewrite H7 in H9. rewrite H8 in H15.
  rewrite H7 in H10. inversion H10.
  rewrite H19 in H9.
  lio_reduce_l_multi_cases(inversion H15) SCase.
  SCase "LIO_l_onestep". subst.
  rewrite H19 in H15. rewrite H19 in H20.
  inversion H20.
  inversion H21.
  inversion H29.
  SCase "LIO_l_done". rewrite H16 in H0. inversion H0.
Qed.

Lemma deterministic_lio_reduce_l_multi' : forall lA l c t n l1 c1 b1 t1 l2 c2 b2 t2,
  is_l_of_t lA ->
  is_l_of_t l  ->
  is_l_of_t c  ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l2 c2 (t_VLIO b2 t2))) ->
  (erase_config lA (m_Config l1 c1 (t_VLIO b1 t1))) = (erase_config lA (m_Config l2 c2 (t_VLIO b2 t2))).
Proof.
  intros.
  simpl in H6. simpl in H7.
  remember (canFlowTo l lA === Some true). destruct b.
  Case "l [= lA". remember (canFlowTo l1 lA === Some true). destruct b.
   SCase "l1 [= lA". remember (canFlowTo l2 lA === Some true). destruct b.
    SSCase "l2 [= lA".
    apply deterministic_lio_reduce_l_multi1 with (l := l) (c := c) (t0 := t) (n := n).
    assumption. eauto. eauto.
    simpl. rewrite <- Heqb. rewrite <- Heqb0. assumption.
    simpl. rewrite <- Heqb. rewrite <- Heqb1. assumption.
    SSCase "l2 [/= lA".
    apply deterministic_lio_reduce_l_multi2 with (l := l) (c := c) (t0 := t) (n := n).
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. eauto. eauto.  eauto.
    simpl. rewrite <- Heqb0. assumption.
    simpl. rewrite <- Heqb1. assumption.
   SCase "l1 [/= lA". remember (canFlowTo l2 lA === Some true). destruct b.
    SSCase "l2 [= lA".
    symmetry.
    apply deterministic_lio_reduce_l_multi2 with (l := l) (c := c) (t0 := t) (n := n).
    assumption. assumption. assumption. assumption. assumption.
    assumption. assumption. eauto. eauto.  eauto.
    simpl. rewrite <- Heqb1. assumption.
    simpl. rewrite <- Heqb0. assumption.
    SSCase "l2 [/= lA".
    apply deterministic_lio_reduce_l_multi1 with (l := l) (c := c) (t0 := t) (n := n).
    assumption. eauto. eauto.
    simpl. rewrite <- Heqb. rewrite <- Heqb0. assumption.
    simpl. rewrite <- Heqb. rewrite <- Heqb1. assumption.
  Case "l [/= lA".
   apply deterministic_lio_reduce_l_multi0 with (l := l) (c := c) (t0 := t) (n := n).
   assumption. assumption. assumption. assumption. assumption. assumption.
   assumption. eauto.
   simpl. rewrite <- Heqb.
   assumption.
   simpl. rewrite <- Heqb.
   assumption.
Qed.

*)

Definition l_equiv_term (l t1 t2 :t) : Prop :=
  erase_term l t1 = erase_term l t2.

Definition l_equiv_config (l : t) (m1 m2 :m) : Prop :=
  erase_config l m1 = erase_config l m2.


(* surface syntax *)
Fixpoint safe (term : t) : Prop :=
  match term with
   | t_LBot            => True
   | t_LA              => True
   | t_LB              => True
   | t_LTop            => True
   | t_VTrue           => True
   | t_VFalse          => True
   | t_VUnit           => True
   | t_VAbs _ t1       => safe t1
   | t_VLIO _ _        => False
   | t_VLabeled _ _ _  => False
   | t_VException      => True
   | t_VHole           => False
   | t_Var _           => True
   | t_App t1 t2       => safe t1 /\ safe t2
   | t_Fix t1          => safe t1
   | t_IfEl t1 t2 t3   => safe t1 /\ safe t2 /\ safe t3
   | t_Join t1 t2      => safe t1 /\ safe t2
   | t_Meet t1 t2      => safe t1 /\ safe t2
   | t_CanFlowTo t1 t2 => safe t1 /\ safe t2
   | t_Return t1       => safe t1
   | t_Bind t1 t2      => safe t1 /\ safe t2
   | t_GetLabel        => True
   | t_GetClearance    => True
   | t_LabelOf t1      => safe t1
   | t_Label t1 t2     => safe t1 /\ safe t2
   | t_UnLabel t1      => safe t1
   | t_ToLabeled t1 t2 => safe t1 /\ safe t2
   | t_LowerClr t1     => safe t1
   | t_ThrowLIO t1     => safe t1
   | t_CatchLIO t1 t2  => safe t1 /\ safe t2
  end.

Lemma lequiv_config_replace_inner : forall l l1 c1 t1 t2,
  l_equiv_term l t1 t2 ->
  erase_config l (m_Config l1 c1 t1) = erase_config l (m_Config l1 c1 t2).
Proof.
  intros. inversion H.
  simpl. remember (canFlowTo l1 l === Some true). destruct b.
  Case "l1 [= l". rewrite H1. reflexivity.
  Case "l1 [/= l". reflexivity.
Qed.

Definition safe_config (cfg : m) : Prop :=
  match cfg with
    | m_Config l c t => safe l /\ safe c /\ safe t
  end.

(*
Theorem non_interference : forall l n f t1 b1 lv1 tv1 t2 b2 lv2 tv2 T T' l1 c1 l1' c1' b1' t1' l2' c2' b2' t2',
    is_l_of_t l
 -> is_l_of_t lv1 -> is_l_of_t lv2
 -> GtT G_nil lv1 T_TLabel -> GtT G_nil lv2 T_TLabel
 -> is_l_of_t l1  -> is_l_of_t c1
 -> is_l_of_t l1' -> is_l_of_t c1'
 -> is_l_of_t l2' -> is_l_of_t c2'

 -> GtT G_nil f  (T_TArrow (T_TLabeled T) (T_TLIO T')) -> safe f
    (* 0 |- f : Labeled T -> T' /\ safe f*)
 -> GtT G_nil tv1 T -> safe tv1 -> t1 = t_VLabeled b1 lv1 tv1
    (* 0 |- tv1 : T /\ safe tv1*)
 -> GtT G_nil tv2 T -> safe tv2 -> t2 = t_VLabeled b2 lv2 tv2
    (* 0 |- tv2 : T /\ safe tv2*)

 -> GtT G_nil t1' T'
    (* 0 |- t1' : T' *)
 -> GtT G_nil t2' T'
    (* 0 |- t2' : T' *)

 -> l_equiv_term l t1 t2
    (* Lb lv1 tv1 =L Lb lv2 tv2 *)
 -> lio_reduce_multi (m_Config l1 c1 (t_App f t1)) n (m_Config l1' c1' (t_VLIO b1' t1'))
    (*  <l1, c1, f t1> -->*n <l1' c1' t1'> *)
 -> lio_reduce_multi (m_Config l1 c1 (t_App f t2)) n (m_Config l2' c2' (t_VLIO b2' t2'))
    (*  <l1, c1, f t2> -->*n <l2' c2' t2'> *)
 -> l_equiv_config l (m_Config l1' c1' (t_VLIO b1' t1')) (m_Config l2' c2' (t_VLIO b2' t2'))
    (* <l1' c1' t1'> =L <l2' c2' t2'> *)
 .
Proof.
  intros. subst.
  apply simulation_multi with (l := l) (T1 := T') (T2 := T') in H21.
  apply simulation_multi with (l := l) (T1 := T') (T2 := T') in H22.
  assert (
    (erase_config l (m_Config l1 c1 (t_App f (t_VLabeled b1 lv1 tv1)))) =
    (erase_config l (m_Config l1 c1 (t_App f (t_VLabeled b2 lv2 tv2))))) as Hrwrt.
  Case "assert". apply lequiv_config_replace_inner. unfold l_equiv_term. simpl.
  assert (erase_term l lv1 = lv1) as Hrwrt_lv1. rewrite erase_label_id. reflexivity. assumption. assumption. rewrite Hrwrt_lv1.
  assert (erase_term l lv2 = lv2) as Hrwrt_lv2. rewrite erase_label_id. reflexivity. assumption. assumption. rewrite Hrwrt_lv2.
  remember (canFlowTo lv1 l === Some true). destruct b.
  SCase "lv1 [= l". remember (canFlowTo lv2 l === Some true). destruct b.
  SSCase "lv2 [= l".  inversion H20.
  rewrite Hrwrt_lv1 in H23. rewrite Hrwrt_lv2 in H23.
  subst lv1.
  rewrite erase_label_id in H24.
  rewrite <- Heqb in H24.
  inversion H24.
  reflexivity.
  assumption.
  assumption.
  SSCase "lv2 [/= l". inversion H20.
  rewrite Hrwrt_lv1 in H23.
  rewrite Hrwrt_lv2 in H23. subst lv1.
  rewrite <- Heqb0 in Heqb.
  solve by inversion.
  SCase "lv1 [/= l". remember (canFlowTo lv2 l === Some true). destruct b.
  SSCase "lv2 [= l". inversion H20.
  rewrite Hrwrt_lv1 in H23.
  rewrite Hrwrt_lv2 in H23. subst lv1.
  rewrite <- Heqb0 in Heqb.
  solve by inversion.
  SSCase "lv2 [/= l".  inversion H20.
  rewrite Hrwrt_lv1 in H23. rewrite Hrwrt_lv2 in H23.
  subst lv1.
  rewrite erase_label_id in H24.
  rewrite <- Heqb in H24.
  inversion H24.
  reflexivity.
  assumption.
  assumption.
  rewrite Hrwrt in H21.
  unfold l_equiv_config.
  apply deterministic_lio_reduce_l_multi' with (l := l1) (c := c1) (t0 := t_App f (t_VLabeled b2 lv2 tv2)) (n := n).
  assumption. assumption. assumption. assumption.
  assumption. assumption. assumption.
  assumption.
  assumption.
  apply GtT_app with (T1 := T_TLabeled T).
  assumption.
  apply GtT_labeledVal.
  assumption. assumption.
  apply GtT_lioVal.
  assumption. assumption. assumption.
  assumption. assumption. assumption.
  apply GtT_app with (T1 := T_TLabeled T).
  assumption.
  apply GtT_labeledVal.
  assumption. assumption.
  apply GtT_lioVal.
  assumption. assumption.
  assumption. assumption.
  assumption. assumption.
Qed.

*)


Theorem strong_non_interference : forall l n l1 c1 t1 l2 c2 t2 l1' c1' t1' l2' c2' t2' T T',
    is_l_of_t l
 -> is_l_of_t l1  -> is_l_of_t c1
 -> is_l_of_t l2  -> is_l_of_t c2
 -> is_l_of_t l1' -> is_l_of_t c1'
 -> is_l_of_t l2' -> is_l_of_t c2'

 -> GtT G_nil t1 (T_TLIO T)
    (* 0 |- t1 : (T_TLIO T) *)
 -> GtT G_nil t2 (T_TLIO T)
    (* 0 |- t2 : (T_TLIO T) *)

 -> GtT G_nil t1' (T_TLIO T')
    (* 0 |- t1' : (T_TLIO T') *)
 -> GtT G_nil t2' (T_TLIO T')
    (* 0 |- t2' : (T_TLIO T') *)

 -> l_equiv_config l (m_Config l1 c1 t1) (m_Config l2 c2 t2)
    (* <l1 c1 t1> =L <l2 c2 t2> *)
 -> lio_reduce (m_Config l1 c1 t1) n (m_Config l1' c1' t1')
    (*  <l1, c1, f t1> -->n <l1' c1' t1'> *)
 -> lio_reduce (m_Config l2 c2 t2) n (m_Config l2' c2' t2')
    (*  <l1, c1, f t2> -->n <l2' c2' t2'> *)
 -> l_equiv_config l (m_Config l1' c1' t1') (m_Config l2' c2' t2')
    (* <l1' c1' t1'> =L <l2' c2' t2'> *)
 .
Proof.
  intros. subst.
  apply lio_reduce_simulation_n with (l := l) (T1 := T) (T2 := T') in H13.
  apply lio_reduce_simulation_n with (l := l) (T1 := T) (T2 := T') in H14.
  unfold l_equiv_config in H12.
  rewrite <- H12 in H14.
  unfold l_equiv_config.
  apply deterministic_lio_reduce_l with (l := l) (n := n) (x := erase_config l (m_Config l1 c1 t1)).
  assumption. assumption. assumption. assumption.
  assumption. assumption. assumption. assumption.
  assumption. assumption. assumption. assumption.
  assumption. assumption. assumption. assumption.
Qed.

Lemma current_clearance_monotonicity : forall l1 c1 t1 n l2 c2 t2,
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  c2 [= c1.
Proof.
  intros.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent n.
  generalize dependent c1.
  generalize dependent l1.
  term_cases (induction t1) Case; intros;
  inversion H3; try repeat (subst; apply canFlowTo_reflexive; assumption).
  Case "term_Bind". subst.
  inversion H16. subst.
  apply IHt1_1 in H20. assumption.
  assumption. assumption. assumption. assumption.
  subst.
  apply canFlowTo_reflexive. assumption.
  subst.
  inversion H16. subst.
  apply IHt1_1 in H20. assumption.
  assumption. assumption. assumption. assumption.
  subst.
  apply canFlowTo_reflexive. assumption.
  Case "term_LowerClr". subst.
  admit (* H16: c2 c1 ~> true *).
  Case "term_CatchLIO". subst.
  inversion H16. subst.
  apply IHt1_1 in H20. assumption.
  assumption. assumption. assumption. assumption.
  subst.
  apply canFlowTo_reflexive. assumption.
  subst.
  inversion H16. subst.
  apply IHt1_1 in H20. assumption.
  assumption. assumption. assumption. assumption.
  subst.
  apply canFlowTo_reflexive. assumption.
Qed.

Lemma deterministic_lio_reduce_l_ex : forall l n1 x y1 y2,
  exists n2,
  lio_reduce_l l n1 x y1 ->
  lio_reduce_l l n2 x y2 ->
  y1 = y2.
Proof.
  intros.
  exists n1.
  apply deterministic_lio_reduce_l.
Qed.


Theorem strong_non_interference_ex : forall l n1 l1 c1 t1 l2 c2 t2 l1' c1' t1' l2' c2' t2' T T',
  exists n2,
    is_l_of_t l
 -> is_l_of_t l1  -> is_l_of_t c1
 -> is_l_of_t l2  -> is_l_of_t c2
 -> is_l_of_t l1' -> is_l_of_t c1'
 -> is_l_of_t l2' -> is_l_of_t c2'

 -> GtT G_nil t1 (T_TLIO T)
    (* 0 |- t1 : (T_TLIO T) *)
 -> GtT G_nil t2 (T_TLIO T)
    (* 0 |- t2 : (T_TLIO T) *)

 -> GtT G_nil t1' (T_TLIO T')
    (* 0 |- t1' : (T_TLIO T') *)
 -> GtT G_nil t2' (T_TLIO T')
    (* 0 |- t2' : (T_TLIO T') *)

 -> l_equiv_config l (m_Config l1 c1 t1) (m_Config l2 c2 t2)
    (* <l1 c1 t1> =L <l2 c2 t2> *)
 -> lio_reduce (m_Config l1 c1 t1) n1 (m_Config l1' c1' t1')
    (*  <l1, c1, f t1> -->n <l1' c1' t1'> *)
 -> lio_reduce (m_Config l2 c2 t2) n2 (m_Config l2' c2' t2')
    (*  <l1, c1, f t2> -->n <l2' c2' t2'> *)
 -> l_equiv_config l (m_Config l1' c1' t1') (m_Config l2' c2' t2')
    (* <l1' c1' t1'> =L <l2' c2' t2'> *)
 .
Proof.
  intros. subst.
  exists n1.
  apply strong_non_interference.
Qed.
