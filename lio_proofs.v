Require Import Arith.
Require Import Bool.
Require Import List.
Require Import SfLib.
Require Export lio.

Lemma labels_are_values : forall l,
  is_l_of_t l ->
  is_v_of_t l.
Proof.
  intros l H.
  induction l; repeat auto.
  reflexivity.
  reflexivity.
  reflexivity.
  solve by inversion.
  solve by inversion.
  solve by inversion.
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


Lemma deterministic_lio_reduce_multi : forall l c t n l1 c1 t1 l2 c2 t2,
  lio_reduce_multi (m_Config l c t) n (m_Config l1 c1 (t_VLIO t1)) ->
  lio_reduce_multi (m_Config l c t) n (m_Config l2 c2 (t_VLIO t2)) ->
  l1 = l2 /\ c1 = c2 /\ t1 = t2.
Proof.
  intros.
  term_cases (induction t) Case; try (inversion H; inversion H12).
  Case "term_VLIO". 
    inversion H. subst. inversion  H12. subst. 
    inversion H0. subst. inversion H14. subst. 
    eauto.
  Case "term_Return". 
    inversion H. subst. inversion H12. subst.
    inversion H0. subst. inversion H22. subst.
    eauto.
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
  Case "LIO_bindCtx".
    inversion Hy2.
    subst. apply IHHy1 in H13. 
    assert (m_Config l' c' t1' = m_Config l'0 c'0 t1'0). apply H13.
    inversion H13. inversion H3. subst. eauto.
    subst. 
    apply values_cannot_be_lio_reduced in Hy1. contradiction. unfold is_v_of_t. trivial.
  Case "LIO_bind".
    inversion Hy2.
    subst. inversion H12. subst. eauto.
  Case "LIO_getLabel".
    inversion Hy2.
    subst. eauto.
  Case "LIO_getClearance".
    inversion Hy2.
    subst. eauto.
  Case "LIO_labelCtx".
    inversion Hy2.
    subst. 
    assert (t1' = t1'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. eauto.
    subst t1 c0 l_5 t2.
    apply labels_cannot_be_reduced in H1. contradiction. assumption.
  Case "LIO_label".
    inversion Hy2.
    subst. 
    apply labels_cannot_be_reduced in H13. contradiction. assumption.
    subst. eauto.
  Case "LIO_unlabelCtx".
    inversion Hy2.
    subst. 
    assert (t' = t'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t5). assumption. assumption.
    subst t'0. eauto.
    subst. 
    apply values_cannot_be_reduced in H1. solve by inversion. simpl. trivial.
 Case "LIO_unlabel".
    inversion Hy2.
    subst.
    apply values_cannot_be_reduced in H13. solve by inversion. simpl. trivial.
    subst.
    assert (l2 = l3).
    SCase "assertion". apply deterministic_pure_reduce with (x := t_Join l_5 l1). assumption. assumption.
    subst l3. eauto.
  Case "LIO_toLabeledCtx".
    inversion Hy2.
    subst.
    assert (t1' = t1'0) as Hrwrt.
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. eauto.
    apply labels_cannot_be_reduced in H1. contradiction. assumption.
  Case "LIO_toLabeled".
    inversion Hy2.
    subst.
    apply labels_cannot_be_reduced in H17. contradiction. assumption.
    subst.
    assert (n5 = n0).
    SCase "assertion". (* trivial *) admit.
    subst.
    assert (l' = l'0 /\ c' = c'0 /\ t' = t'0) as Hrwrt.
    SCase "assertion".
    apply deterministic_lio_reduce_multi with (l := l_5) (c := c) (t0 := t5) (n := n0).
    assumption. assumption.
    assert (t' = t'0) as Hrwrt_t. apply Hrwrt. rewrite Hrwrt_t.
    reflexivity.
  Case "LIO_hole".
    inversion Hy2.
    subst. eauto.
Qed.

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
   | t_LBot            => t_LBot
   | t_LA              => t_LA
   | t_LB              => t_LB
   | t_LTop            => t_LTop
   | t_VTrue           => t_VTrue
   | t_VFalse          => t_VFalse
   | t_VUnit           => t_VUnit
   | t_VAbs x t5       => t_VAbs x (erase_term l t5)
   | t_VLIO t5         => t_VLIO (erase_term l t5)
   | t_VLabeled l1 t2  => t_VLabeled (erase_term l l1)
                                     (if canFlowTo (erase_term l l1) l === Some true
                                        then erase_term l t2
                                        else t_VHole)
   | t_VHole           => t_VHole
   | t_Var x           => t_Var x
   | t_App t5 t'       => t_App (erase_term l t5) (erase_term l t')
   | t_Fix t5          => t_Fix (erase_term l t5)
   | t_IfEl t1 t2 t3   => t_IfEl (erase_term l t1) (erase_term l t2) (erase_term l t3)
   | t_Join t1 t2      => t_Join (erase_term l t1) (erase_term l t2)
   | t_Meet t1 t2      => t_Meet (erase_term l t1) (erase_term l t2)
   | t_CanFlowTo t1 t2 => t_CanFlowTo (erase_term l t1) (erase_term l t2)
   | t_Return t5       => t_Return (erase_term l t5)
   | t_Bind t5 t'      => t_Bind (erase_term l t5) (erase_term l t')
   | t_GetLabel        => t_GetLabel
   | t_GetClearance    => t_GetClearance
   | t_LabelOf t5      => t_LabelOf (erase_term l t5)
   | t_Label t5 t'     => t_Label (erase_term l t5)
                          (if canFlowTo (erase_term l t5) l === Some true
                            then erase_term l t'
                            else t_VHole)
   | t_UnLabel t5      => t_UnLabel (erase_term l t5)
   | t_ToLabeled t1 t2 => t_ToLabeled (erase_term l t1)
                          (if canFlowTo (erase_term l t1) l === Some true
                            then erase_term l t2
                            else t_VLIO (t_VHole))
  end.

(* ~>L *)
Inductive pure_reduce_l : t -> t -> t -> Prop :=
   | pure_reduce_l_step : forall l t1 t2,
     is_l_of_t l ->
     pure_reduce t1 t2 ->
     pure_reduce_l l t1 (erase_term l t2).


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

Lemma erase_term_idempotent : forall l t1,
  is_l_of_t l ->
  erase_term l t1 = erase_term l (erase_term l t1).
Proof.
  intros l t1 H.
  term_cases (induction t1) Case; eauto.
  Case "term_VAbs". simpl. rewrite <- IHt1. reflexivity.
  Case "term_VLIO". simpl. rewrite <- IHt1. reflexivity.
  Case "term_VLabeled". induction l; try contradiction.
    SCase "LBot". simpl.
     destruct t1_1. simpl. rewrite <- IHt1_2; reflexivity.
     auto. auto. auto. auto. auto. auto. auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto.
     auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto. 
     auto. 
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
    SCase "LA". simpl.
     destruct t1_1. simpl. rewrite <- IHt1_2; reflexivity.
     auto. auto. auto. auto. auto. auto. auto.
     simpl. inversion IHt1_2. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto.
     auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto. 
     auto. 
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
    SCase "LB". simpl.
     destruct t1_1. simpl. rewrite <- IHt1_2; reflexivity.
     auto. auto. auto. auto. auto. auto. auto.
     simpl. inversion IHt1_2. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto.
     auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto. 
     auto. 
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
    SCase "LTop". simpl.
     destruct t1_1. simpl. rewrite <- IHt1_2; reflexivity.
     auto. auto. auto. auto. auto. auto. auto.
     simpl. inversion IHt1_2. reflexivity.
     simpl. rewrite <- IHt1_2. reflexivity.
     simpl. rewrite <- IHt1_2. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto.
     auto.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     auto. 
     auto. 
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
     simpl. inversion IHt1_1. reflexivity.
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
  simpl. rewrite <- IHt1_1. remember (canFlowTo (erase_term l t1_1) l === Some true).
  destruct b.
  SCase "t1_1 [= l".
  rewrite <- IHt1_2. reflexivity.
  SCase "t1_1 [/= l". reflexivity.
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
    rewrite tsubst_t_homo_if'.
    simpl.
    rewrite IHt2_1. rewrite IHt2_2. 
    assert (tsubst_t (erase_term l t1) x l = l) as Hrwrt.
    SCase "assertion". rewrite t_subst_label_id. reflexivity. assumption.
    rewrite -> Hrwrt.
    reflexivity.
Qed.

Hint Resolve erase_term_homo_subst.

Lemma erase_hole_implies_anything: forall l l1 t1,
  is_l_of_t l ->
  is_l_of_t l1 ->
  canFlowTo l1 l = Some false ->
  erase_term l (t_VLabeled l1 t_VHole) = erase_term l (t_VLabeled l1 t1).
Proof.
  intros. simpl. rewrite -> erase_label_id. rewrite H1. simpl. reflexivity.
  assumption. assumption.
Qed. 


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
Qed.

Lemma pure_reduce_simulation : forall l t1 t2,
  is_l_of_t l ->
  pure_reduce t1 t2 ->
  pure_reduce_l l (erase_term l t1) (erase_term l t2).
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
    Case "term_VHole". inversion H.
      subst. apply pure_reduce_l_step. assumption.
      simpl. assumption.
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
     SCase "appCtx".
     rewrite erase_term_idempotent with (t1 := t_App t1' t1_2).
     apply pure_reduce_l_step. assumption.
     simpl. 
     apply Pr_appCtx. 
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "app".  
     rewrite erase_term_idempotent with (t1 := tsubst_t t1_2 x t1).
     apply pure_reduce_l_step. assumption.
     simpl. rewrite erase_term_homo_subst.
     apply Pr_app. assumption. assumption.
    Case "term_Fix". inversion H.
     SCase "fixCtx".
     rewrite erase_term_idempotent with (t1 := t_Fix t').
     apply pure_reduce_l_step. assumption.
     simpl. 
     apply Pr_fixCtx. 
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "fix".
     rewrite erase_term_idempotent with (t1 := tsubst_t (t_Fix (t_VAbs x t5)) x t5).
     apply pure_reduce_l_step. assumption.
     simpl. rewrite erase_term_homo_subst.
     apply Pr_fix. assumption. assumption.
    Case "term_IfEl". inversion H.
     SCase "ifCtx".
     rewrite erase_term_idempotent with (t1 := t_IfEl t1' t1_2 t1_3).  
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_ifCtx.
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "ifTrue".
     rewrite erase_term_idempotent with (t1 := t2).  
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_ifTrue. assumption.
     SCase "ifFalse".
     rewrite erase_term_idempotent with (t1 := t2).  
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_ifFalse. assumption.
    Case "term_Join". inversion H.
     SCase "ctxL".
     rewrite erase_term_idempotent with (t1 := t_Join t1' t1_2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinCtxL.
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "ctxR".
     rewrite erase_term_idempotent with (t1 := t_Join t1_1 t2').
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinCtxR. 
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "botL".
     rewrite erase_term_idempotent with (t1 := t2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinBotL.
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
     SCase "botR".
     rewrite erase_term_idempotent with (t1 := t2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinBotR.
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
     SCase "Eq".
     rewrite erase_term_idempotent with (t1 := t2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinEq. 
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. subst. reflexivity. assumption.
     SCase "AB".
     rewrite erase_term_idempotent with (t1 := t_LTop).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinAB.  assumption.
     SCase "BA".
     rewrite erase_term_idempotent with (t1 := t_LTop).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinBA.  assumption.
     SCase "topL".
     rewrite erase_term_idempotent with (t1 := t_LTop).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinTopL.  
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
     SCase "topR".
     rewrite erase_term_idempotent with (t1 := t_LTop).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_joinTopR.  
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
    Case "term_Meet". inversion H.
     SCase "ctxL".
     rewrite erase_term_idempotent with (t1 := t_Meet t1' t1_2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetCtxL.
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "ctxR".
     rewrite erase_term_idempotent with (t1 := t_Meet t1_1 t2').
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetCtxR. 
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "botL".
     rewrite erase_term_idempotent with (t1 := t_LBot).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetBotL.  
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
     SCase "botR".
     rewrite erase_term_idempotent with (t1 := t_LBot).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetBotR.  
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
     SCase "Eq".
     rewrite erase_term_idempotent with (t1 := t2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetEq. 
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. subst. reflexivity. assumption.
     SCase "AB".
     rewrite erase_term_idempotent with (t1 := t_LBot).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetAB.  assumption.
     SCase "BA".
     rewrite erase_term_idempotent with (t1 := t_LBot).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetBA.  assumption.
     SCase "topL".
     rewrite erase_term_idempotent with (t1 := t2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetTopL.
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
     SCase "topR".
     rewrite erase_term_idempotent with (t1 := t2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_meetTopR.
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t2 = t2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
    Case "term_CanFlowTo". inversion H.
     SCase "ctxL".
     rewrite erase_term_idempotent with (t1 := t_CanFlowTo t1' t1_2).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_canFlowToCtxL.
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "ctxR".
     rewrite erase_term_idempotent with (t1 := t_CanFlowTo t1_1 t2').
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_canFlowToCtxR. 
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "bot".
     rewrite erase_term_idempotent with (t1 := t_VTrue).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_canFlowToBot.
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
     SCase "Eq".
     rewrite erase_term_idempotent with (t1 := t_VTrue).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_canFlowToEq. 
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_2 = t1_2) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. subst. reflexivity. assumption.
     SCase "AB".
     rewrite erase_term_idempotent with (t1 := t_VFalse).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_canFlowToAB.  assumption.
     SCase "BA".
     rewrite erase_term_idempotent with (t1 := t_VFalse).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_canFlowToBA.  assumption.
     SCase "top".
     rewrite erase_term_idempotent with (t1 := t_VTrue).
     apply pure_reduce_l_step. assumption.
     simpl. apply Pr_canFlowToTop.  
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption.
     assert (erase_term l t1_1 = t1_1) as Hrewrite.
     SSSCase "assertion".
     apply erase_label_id. assumption. assumption.
     rewrite Hrewrite. assumption. assumption.
    Case "term_Return". inversion H.
    Case "term_Bind". inversion H. 
    Case "term_GetLabel". inversion H.
    Case "term_GetClearance". inversion H.
    Case "term_LabelOf". inversion H.
     SCase "labelOfCtx".
     rewrite erase_term_idempotent with (t1 := t_LabelOf t').
     apply pure_reduce_l_step. assumption.
     simpl. 
     apply Pr_labelOfCtx. 
     apply pure_reduce_simulation_helper. assumption. assumption. assumption.
     SCase "labelOf". 
     rewrite erase_term_idempotent with (t1 := t2).  
     apply pure_reduce_l_step. assumption.
     subst.
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
     assumption.
    Case "term_Label". inversion H.
    Case "term_UnLabel". inversion H.
    Case "term_ToLabeled". inversion H.
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
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  inversion Hy2.
  subst n0.
  assert (m2 = m3 ).
  Case "assertion". apply deterministic_lio_reduce with (x := m1) (n := n).
  assumption. assumption. 
  subst m2. reflexivity.
Qed.

Hint Resolve deterministic_lio_reduce_l.

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
  simpl. reflexivity.
Admitted.

Lemma inv_erase_labeled : forall l l1 (t2 : t),
  is_l_of_t l ->
  is_l_of_t l1 ->
  l1 [/= l ->
  t_VLabeled l1 t_VHole = erase_term l (t_VLabeled l1 t2).
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

Lemma inv_erase_toLabeled : forall l l1 (t2 : t),
  is_l_of_t l ->
  is_l_of_t l1 ->
  l1 [/= l ->
  t_ToLabeled l1 (t_VLIO t_VHole) = erase_term l (t_ToLabeled l1 t2).
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

Lemma inv_erase_LIO : forall l l1 c1 (t2 : t),
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l ->
  l1 [= l ->
  m_Config l1 c1 (t_VLIO (erase_term l t2)) = erase_config l (m_Config l1 c1 (t_VLIO t2)).
Proof. 
  intros.
  simpl.
  rewrite H2.
  reflexivity.
Qed.

Lemma inv_erase_bind : forall l l1 c1 t2 t3,
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l ->
  l1 [= l ->
  m_Config l1 c1 (t_Bind (erase_term l t2) (erase_term l t3))
  = erase_config l (m_Config l1 c1 (t_Bind t2 t3)).
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
  induction t1; intros;
  inversion H3; try repeat (subst; apply canFlowTo_reflexive; assumption).
  subst.
  apply IHt1_1 in H16. assumption. assumption. assumption. assumption. assumption.
  subst.
  admit (* l2 = l1 |_| l0  and so l1 [= l2 *).
Qed.

Lemma lio_reduce_simulation_0_helper: forall l l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  l1 [= l ->
  l2 [= l ->
  lio_reduce (m_Config l1 c1 t1) 0 (m_Config l2 c2 t2) ->
  lio_reduce (erase_config l (m_Config l1 c1 t1)) 0 (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l l1 c1 t1 l2 c2 t2 l_of_t l1_to_l l2_to_l H.
  generalize dependent t2.
  generalize dependent c2.
  term_cases (induction t1) Case; intros c2 t2 H.
    Case "term_LBot". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LA". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LB". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LTop". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VTrue". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VFalse". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VUnit". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VAbs". inversion H. 
    Case "term_VLIO". inversion H.
    Case "term_VLabeled". inversion H.
    Case "term_VHole". inversion H. simpl. rewrite l2_to_l. apply LIO_hole.
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
    Case "term_Fix". inversion H.
    Case "term_IfEl". inversion H.
    Case "term_Join". inversion H.
    Case "term_Meet". inversion H.
    Case "term_CanFlowTo". inversion H.
    Case "term_Return". inversion H. 
     subst.  
     simpl. rewrite l2_to_l.
     apply LIO_return. assumption. assumption. assumption.
    Case "term_Bind". inversion H. 
     SCase "bindCtx".
     subst.  
     simpl. rewrite l1_to_l. rewrite l2_to_l.
     apply LIO_bindCtx. assumption. assumption. assumption. assumption.
     rewrite inv_erase_conf1.
     rewrite inv_erase_conf1.
     apply IHt1_1.
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption. 
     SCase "bind".
     subst. simpl.
     rewrite l1_to_l. apply LIO_bind.
     assumption. assumption. assumption.
    Case "term_GetLabel". inversion H. 
     subst.  
     simpl. rewrite l2_to_l.
     rewrite erase_label_id.
     apply LIO_getLabel. assumption. assumption. assumption. assumption. assumption.
    Case "term_GetClearance". inversion H. 
     subst.  
     simpl. rewrite l2_to_l.
     rewrite erase_label_id.
     apply LIO_getClearance. assumption. assumption. assumption. assumption. assumption.
    Case "term_LabelOf". inversion H.
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
      (* l2 = l1 |_| l0
          l1 [= l
          l2 [= l
          l0 [/= l
          contradiction: l2 [= l, i.e, l1 |_| l0 [= l so l0 [= l *)
      admit.
    Case "term_ToLabeled". inversion H.
      SCase "toLabeledCtx".
      subst. simpl. rewrite l2_to_l.
      assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
      SSCase "assertion". (* reducing label does not affect its value *) admit.
      rewrite H0.
      destruct (canFlowTo (erase_term l t1') l === Some true).
      SSCase "t1' [= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. assumption. 
      SSCase "t1' [/= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. assumption.
      SCase "tolabeled".
      subst.
      assert (0 = n5 + 1 -> False).
      omega.
      apply H0 in H16.
      contradiction.
Qed.

Lemma lio_reduce_simulation_0_helper': forall l l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  l1 [= l ->
  l2 [/= l ->
  lio_reduce (m_Config l1 c1 t1) 0 (m_Config l2 c2 t2) ->
  lio_reduce (m_Config l1 c1 (erase_term l t1)) 0 (m_Config l2 c2 (erase_term l t2)).
Proof.
  intros l l1 c1 t1 l2 c2 t2 l_of_t l1_to_l not_l2_to_l H.
  generalize dependent t2.
  generalize dependent c2.
  term_cases (induction t1) Case; intros c2 t2 H.
    Case "term_LBot". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LA". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LB". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LTop". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VTrue". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VFalse". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VUnit". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VAbs". inversion H. 
    Case "term_VLIO". inversion H.
    Case "term_VLabeled". inversion H.
    Case "term_VHole". inversion H. simpl. apply LIO_hole. 
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
    Case "term_Fix". inversion H.
    Case "term_IfEl". inversion H.
    Case "term_Join". inversion H.
    Case "term_Meet". inversion H.
    Case "term_CanFlowTo". inversion H.
    Case "term_Return". inversion H. subst. 
     simpl. apply LIO_return. assumption. assumption. reflexivity.
    Case "term_Bind". inversion H. 
     SCase "bindCtx".
     subst. simpl. 
     apply LIO_bindCtx. assumption. assumption. assumption. assumption.
     apply IHt1_1.
     assumption. 
     SCase "bind".
     subst. simpl. apply LIO_bind.
     assumption. assumption. reflexivity.
    Case "term_GetLabel". inversion H. 
     subst.  
     simpl. rewrite erase_label_id.
     apply LIO_getLabel. assumption. assumption. reflexivity. assumption. assumption.
    Case "term_GetClearance". inversion H. 
     subst.  
     simpl. rewrite erase_label_id.
     apply LIO_getClearance. assumption. assumption. reflexivity. assumption. assumption.
    Case "term_LabelOf". inversion H.
    Case "term_Label". inversion H.
     SCase "labelCtx".
     subst. simpl. 
     assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
     SSCase "assertion". (* reducing label does not affect its value *) admit.
     rewrite H0.
     destruct (canFlowTo (erase_term l t1') l === Some true).
     SSCase "t1' [= l".
     apply LIO_labelCtx.
     assumption. assumption. 
     apply pure_reduce_simulation_helper.
     assumption. assumption. reflexivity.
     SSCase "t1' [/= l".
     apply LIO_labelCtx.
     assumption. assumption. 
     apply pure_reduce_simulation_helper.
     assumption. assumption. reflexivity.
     SCase "label".
     subst. simpl. 
       assert (erase_term l t1_1 = t1_1) as Hrwrt. 
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
       rewrite -> Hrwrt.
       remember (canFlowTo t1_1 l === Some true). destruct b.
       SSSCase "t1_1 [= l". apply LIO_label.
       assumption. assumption. assumption.
       assumption. assumption. reflexivity.
       SSSCase "t1_1 [/= l". 
       apply LIO_label. assumption. assumption. assumption. assumption. assumption. reflexivity.
    Case "term_UnLabel". inversion H.
      SCase "unlabelCtx".
      subst. simpl. 
      apply LIO_unlabelCtx. assumption. assumption.
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SCase "unlabel".
      subst. simpl. 
      assert (erase_term l l0 = l0) as Hrwrt. 
      SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo l0 l === Some true). destruct b.
      SSSCase "l0 [= l". apply LIO_unlabel.
      assumption. assumption. assumption. assumption. assumption.
      assumption. reflexivity.
      SSSCase "l0 [/= l". 
      (* l2 = l1 |_| l0
          l1 [= l
          l2 [/= l
          l0 [/= l
          contradiction l2 [=l since l2 = l1 |_| l0 and  l1 [= l *)
      admit.
    Case "term_ToLabeled". inversion H.
     SCase "toLabeledCtx".
      subst. simpl. 
      assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
      SSCase "assertion". (* reducing label does not affect its value *) admit.
      rewrite H0.
      destruct (canFlowTo (erase_term l t1') l === Some true).
      SSCase "t1' [= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SSCase "t1' [/= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SCase "tolabeled".
      subst.
      assert (0 = n5 + 1 -> False).
      omega.
      apply H0 in H16.
      contradiction.
Qed.

Lemma lio_reduce_simulation_0 : forall l l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  lio_reduce (m_Config l1 c1 t1) 0 (m_Config l2 c2 t2) ->
  lio_reduce_l l 0 (erase_config l (m_Config l1 c1 t1)) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros l l1 c1 t1 l2 c2 t2 l_of_t_l l_of_t_l1 l_of_t_c1 l_of_t_l2 l_of_t_c2 H.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent c1.
  generalize dependent l1.
  generalize dependent l_of_t_l.
  term_cases (induction t1) Case; intros.
    Case "term_LBot". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LA". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LB". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LTop". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VTrue". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VFalse". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VUnit". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VAbs". inversion H. 
    Case "term_VLIO". inversion H.
    Case "term_VLabeled". inversion H.
    Case "term_VHole". inversion H.
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 t_VHole).
     apply lio_reduce_l_step with (n := 0). assumption. simpl. 
     subst. remember (canFlowTo l2 l === Some true). destruct b.
     simpl. rewrite <- Heqb. apply LIO_hole. 
     simpl. apply LIO_hole. assumption.
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
    Case "term_Fix". inversion H.
    Case "term_IfEl". inversion H.
    Case "term_Join". inversion H.
    Case "term_Meet". inversion H.
    Case "term_CanFlowTo". inversion H.
    Case "term_Return". inversion H. 
     subst.  
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_VLIO t1)).
     simpl. destruct (canFlowTo l2 l === Some true).
     SCase "l2 [= l". 
     apply lio_reduce_l_step with (n := 0). assumption. apply LIO_return.
     assumption. assumption. reflexivity.
     SCase "t1 [/= l". apply lio_reduce_l_step with (n := 0). assumption.
     apply LIO_hole. assumption.
   Case "term_Bind".  inversion H.
     SCase "bindCtx". subst.
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Bind t1' t1_2)).
     simpl. remember (canFlowTo l1 l === Some true). destruct b.
     SSCase "l1 [= l".
     remember (canFlowTo l2 l === Some true). destruct b.
     SSSCase "l2 [= l".
     apply lio_reduce_l_step with (n := 0). assumption.
     apply LIO_bindCtx. assumption. assumption. assumption. assumption.
     rewrite inv_erase_conf1.
     rewrite inv_erase_conf1.
     apply lio_reduce_simulation_0_helper.
     assumption. eauto. eauto.
     assumption. assumption.
     assumption. assumption.
     eauto. assumption. assumption. assumption.
     eauto.
     SSSCase "l2 [/= l". term_cases(induction t1_1) SSSSCase.
     SSSSCase "term_LBot". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_LA". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_LB". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_LTop". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_VTrue". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_VFalse". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_VUnit". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_VAbs". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_VLIO". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_VLabeled". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSCase "term_VHole". inversion H12. subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSCase "term_Var". inversion H12. 
     SSSSCase "term_App". inversion H12. 
     SSSSCase "term_Fix". inversion H12. 
     SSSSCase "term_IfEl". inversion H12. 
     SSSSCase "term_Join". inversion H12. 
     SSSSCase "term_Meet". inversion H12. 
     SSSSCase "term_CanFlowTo". inversion H12. 
     SSSSCase "term_Return". inversion H12. 
     subst.
     rewrite <- Heqb0  in Heqb. solve by inversion.
     SSSSCase "term_Bind". inversion H12.
     SSSSSCase "bindCtx". subst.
     rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := 
       (t_Bind (erase_term l (t_Bind t1'0 t1_1_2)) (erase_term l t1_2))).
     rewrite <- erase_config_idempotent.
     apply lio_reduce_l_step with (n := 0).
     assumption.
     apply LIO_bindCtx.
     assumption. assumption. assumption. assumption.
     simpl.
     apply LIO_bindCtx.
     assumption. assumption. assumption. assumption.
     subst.
     apply lio_reduce_simulation_0_helper'.
     assumption. eauto. eauto. assumption. assumption. assumption.
     assumption. assumption. eauto.
     SSSSSCase "bind". subst.
     rewrite <- Heqb0  in Heqb. solve by inversion.
     SSSSCase "term_GetLabel". inversion H12. 
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSCase "term_GetClearance". inversion H12. 
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSCase "term_LabelOf". inversion H12.
     SSSSCase "term_Label". inversion H12. 
     SSSSSCase "labelCtx".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSCase "label".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSCase "term_UnLabel". inversion H12. 
     SSSSSCase "unlabelCtx".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSCase "unlabel".
     subst.
     simpl.
     assert (erase_term l l0 = l0). rewrite erase_label_id. reflexivity.
     assumption. assumption. rewrite -> H0.
     destruct (canFlowTo l0 l === Some true).
     SSSSSSCase "l0 [= l". 
     rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := t_Bind (t_Return (erase_term l t2)) (erase_term l t1_2)).
     apply lio_reduce_l_step with (n := 0).
     assumption.
     apply LIO_bindCtx.
     assumption. assumption. assumption. assumption.
     apply LIO_unlabel.
     assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     assumption. assumption. eauto. 
     SSSSSSCase "l0 [/= l".  
     rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := t_Bind (t_Return t_VHole) (erase_term l t1_2)).
     apply lio_reduce_l_step with (n := 0).
     assumption.
     apply LIO_bindCtx.
     assumption. assumption. assumption. assumption.
     apply LIO_unlabel.
     assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     assumption. assumption. eauto.
     SSSSCase "term_ToLabeled". inversion H12. 
     SSSSSCase "toLabeledCtx".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSCase "toLabeled".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSCase "l1 [/= l".
     remember (canFlowTo l2 l === Some true). destruct b.
     SSSCase "l2 [= l".
     assert ((canFlowTo l1 l2 === Some true) = true).
     apply current_label_monotonicity with (l1 := l1) (c1 := c1) (t1 := t1_1) (l2 := l2) (c2 := c2) (t2 := t1') (n := 0). 
     assumption. assumption.
     assumption. assumption.
     assumption. 
     assert ((canFlowTo l1 l === Some true) = true).
     apply canFlowTo_transitivie with (l1 := l1) (l2 := l2) (l3 := l).
     assumption. assumption. assumption.
     assumption. eauto.
     rewrite H1 in Heqb. solve by inversion.
     SSSCase "l2 [/= l". 
     apply lio_reduce_l_step with (n := 0). assumption. apply LIO_hole.
     assumption.
     SCase "bind". subst.
     rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_App t1_2 t1)).
     simpl. remember (canFlowTo l2 l === Some true). destruct b.
     SSCase "l2 [= l".
     apply lio_reduce_l_step with (n := 0). assumption.
     apply LIO_bind. assumption. assumption. reflexivity.
     SSCase "l2 [/= l".
     apply lio_reduce_l_step with (n := 0). assumption.
     apply LIO_hole. assumption.
    Case "term_GetLabel". inversion H.
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Return l2)).
      simpl. destruct (canFlowTo l2 l === Some true).
      SCase "l2 [= l". apply lio_reduce_l_step with (n := 0). assumption.
      rewrite erase_label_id. apply LIO_getLabel. assumption. assumption. reflexivity. assumption. assumption.
      SCase "l2 [/= l". apply lio_reduce_l_step with (n := 0). assumption. apply LIO_hole. assumption.
    Case "term_GetClearance". inversion H.
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Return c2)).
      simpl. destruct (canFlowTo l2 l === Some true).
      SCase "l2 [= l". apply lio_reduce_l_step with (n := 0). assumption.
      rewrite erase_label_id. apply LIO_getClearance. assumption. assumption. reflexivity. assumption. assumption.
      SCase "l2 [/= l". apply lio_reduce_l_step with (n := 0). assumption. apply LIO_hole. assumption.
    Case "term_LabelOf". inversion H.
    Case "term_Label". inversion H.
      SCase "labelCtx".
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Label t1' t1_2)).
      simpl. 
      destruct (canFlowTo l2 l === Some true).
      SSCase "l2 [= l". apply lio_reduce_l_step with (n := 0). assumption.
      assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
      SSSCase "assertion". (* reducing label does not affect its value *) admit.
      rewrite H0.
      destruct (canFlowTo (erase_term l t1') l === Some true).
      SSSCase "t1' [= l".
      apply LIO_labelCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SSSCase "t1' [/= l".
      apply LIO_labelCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SSCase "l2 [/= l". apply lio_reduce_l_step with (n := 0).
      assumption. apply LIO_hole. assumption.
      SCase "label". subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Return (t_VLabeled t1_1 t1_2))).
      simpl. remember (canFlowTo l2 l === Some true). destruct b.
      SSCase "l2 [= l". 
       assert (erase_term l t1_1 = t1_1) as Hrwrt. 
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
       rewrite -> Hrwrt.
       remember (canFlowTo t1_1 l === Some true). destruct b.
       SSSCase "t1_1 [= l". apply lio_reduce_l_step with (n := 0). assumption.
       apply LIO_label. assumption. assumption. assumption. assumption. assumption. reflexivity.
       SSSCase "t1_1 [/= l". 
       rewrite inv_erase_labeled with (l := l) (l1 := t1_1) (t2 := t_VHole).
       rewrite inv_erase_return.
       rewrite <- erase_config_idempotent.
       apply lio_reduce_l_step with (n := 0). assumption.
       apply LIO_label. assumption. assumption. assumption. assumption. assumption. reflexivity.
       assumption. assumption. assumption. assumption. eauto.
       assumption. assumption. eauto.
      SSCase "l2 [/= l". apply lio_reduce_l_step with (n := 0). assumption. apply LIO_hole. assumption.
    Case "term_UnLabel". inversion H.
      SCase "unlabelCtx".
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_UnLabel t')).
      simpl. remember (canFlowTo l2 l === Some true). destruct b.
      SSCase "l2 [= l". apply lio_reduce_l_step with (n := 0). assumption.
      apply LIO_unlabelCtx. assumption. assumption. 
      apply pure_reduce_simulation_helper. assumption. assumption. reflexivity.
      SSCase "l2 [/= l". apply lio_reduce_l_step with (n := 0). assumption. apply LIO_hole. assumption.
      SCase "unlabel".
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Return t0)).
      simpl. remember (canFlowTo l1 l === Some true). destruct b.
      SSCase "l1 [= l".  remember (canFlowTo l2 l === Some true). destruct b.
      SSSCase "l2 [= l". 
      assert (erase_term l l0 = l0) as Hrwrt. 
      SSSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo l0 l === Some true). destruct b.
      SSSSCase "l0 [= l".
      apply lio_reduce_l_step with (n := 0). assumption.
      apply LIO_unlabel. assumption. assumption. 
      assumption. assumption. assumption. assumption. reflexivity.
      SSSSCase "l0 [/= l".
       (* l0 [/= l
          l2 [= l
          l1 [= l
          l2 = l1 |_| l0
          => contradiction (l0 should flow to l if l2 = l1 |_| l0 and l2 [= l) *)
        admit.
      SSSCase "l2 [/= l".
      assert (erase_term l l0 = l0) as Hrwrt. 
      SSSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo l0 l === Some true). destruct b.
      SSSSCase "l0 [= l". 
      rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := t_Return (erase_term l t0)).
      rewrite <- erase_config_idempotent.
      apply lio_reduce_l_step with (n := 0). assumption.
      apply LIO_unlabel. assumption. assumption. assumption. assumption.
      assumption. assumption. reflexivity. assumption. assumption.
      assumption. assumption. eauto.
      SSSSCase "l0 [/= l".
      rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := t_Return t_VHole).
      rewrite <- erase_config_idempotent.
      apply lio_reduce_l_step with (n := 0). assumption. 
      apply LIO_unlabel.
      assumption. assumption. assumption. assumption.
      assumption. assumption. reflexivity. assumption.
      assumption. assumption. assumption. eauto. 
      SSCase "l1 [/= l".  remember (canFlowTo l2 l === Some true).
      destruct b.
      SSSCase "l2 [= l". 
       (* l2 [= l
          l1 [/=l
          l2 = l1 |_| l0
          => contradiction : l1 [= l since l2 [= l and l2 = l1 |_| l0*)
       admit.
      SSSCase "l2 [/= l". apply lio_reduce_l_step with (n := 0). assumption. apply LIO_hole. assumption.      
    Case "term_ToLabeled". inversion H.
      SCase "toLabeledCtx".
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_ToLabeled t1' t1_2)).
      simpl. 
      destruct (canFlowTo l2 l === Some true).
      SSCase "l2 [= l". apply lio_reduce_l_step with (n := 0). assumption.
      assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
      SSSCase "assertion". (* reducing label does not affect its value *) admit.
      rewrite H0.
      destruct (canFlowTo (erase_term l t1') l === Some true).
      SSSCase "t1' [= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SSSCase "t1' [/= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SSCase "l2 [/= l". apply lio_reduce_l_step with (n := 0).
      assumption. apply LIO_hole. assumption.
      SCase "toLabeled".
      subst.
      assert (0 = n5 + 1 -> False).
      omega.
      apply H0 in H16.
      contradiction.
Qed.

Lemma lio_reduce_multi_helper : forall n l l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  l1 [= l ->
  l2 [= l ->
  lio_reduce_multi (m_Config l1 c1 t1) n (m_Config l2 c2 (t_VLIO t2)) ->
  lio_reduce_multi (m_Config l1 c1 (erase_term l t1)) n (m_Config l2 c2 (t_VLIO (erase_term l t2))).
Proof.
  intros.
  inversion H6.
  Case "onestep". 
  term_cases (induction t1) SCase; try (inversion H18).
  SCase "term_Return". 
    apply LIO_onestep. assumption. assumption. assumption. assumption.
    simpl. apply LIO_return. assumption. assumption. assumption.
  Case "done". simpl. apply LIO_done. assumption. assumption. 
Qed.

Lemma lio_reduce_simulation_n_helper: forall n l l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  l1 [= l ->
  l2 [= l ->
  lio_reduce (m_Config l1 c1 t1) (S n) (m_Config l2 c2 t2) ->
  lio_reduce (erase_config l (m_Config l1 c1 t1)) (S n) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros n l l1 c1 t1 l2 c2 t2 l_of_t l1_to_l l2_to_l H.
  generalize dependent t2.
  generalize dependent c2.
  term_cases (induction t1) Case; intros c2 t2 H.
    Case "term_LBot". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LA". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LB". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LTop". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VTrue". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VFalse". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VUnit". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VAbs". inversion H. 
    Case "term_VLIO". inversion H.
    Case "term_VLabeled". inversion H.
    Case "term_VHole". inversion H. simpl. rewrite l2_to_l. apply LIO_hole.
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
    Case "term_Fix". inversion H.
    Case "term_IfEl". inversion H.
    Case "term_Join". inversion H.
    Case "term_Meet". inversion H.
    Case "term_CanFlowTo". inversion H.
    Case "term_Return". inversion H. 
     subst.  
     simpl. rewrite l2_to_l.
     apply LIO_return. assumption. assumption. assumption.
    Case "term_Bind". inversion H. 
     SCase "bindCtx".
     subst.  
     simpl. rewrite l1_to_l. rewrite l2_to_l.
     apply LIO_bindCtx. assumption. assumption. assumption. assumption.
     rewrite inv_erase_conf1.
     rewrite inv_erase_conf1.
     apply IHt1_1.
     assumption. assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption. 
     SCase "bind".
     subst. simpl.
     rewrite l1_to_l. apply LIO_bind.
     assumption. assumption. assumption.
    Case "term_GetLabel". inversion H. 
     subst.  
     simpl. rewrite l2_to_l.
     rewrite erase_label_id.
     apply LIO_getLabel. assumption. assumption. assumption. assumption. assumption.
    Case "term_GetClearance". inversion H. 
     subst.  
     simpl. rewrite l2_to_l.
     rewrite erase_label_id.
     apply LIO_getClearance. assumption. assumption. assumption. assumption. assumption.
    Case "term_LabelOf". inversion H.
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
      (* l2 = l1 |_| l0
          l1 [= l
          l2 [= l
          l0 [/= l
          contradiction: l2 [= l, i.e, l1 |_| l0 [= l so l0 [= l *)
      admit.
    Case "term_ToLabeled". inversion H.
      SCase "toLabeledCtx".
      subst. simpl. rewrite l2_to_l.
      assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
      SSCase "assertion". (* reducing label does not affect its value *) admit.
      rewrite H0.
      destruct (canFlowTo (erase_term l t1') l === Some true).
      SSCase "t1' [= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. assumption. 
      SSCase "t1' [/= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. assumption.
      SCase "tolabeled".
      subst. simpl.
      rewrite l1_to_l.
      assert (erase_term l t1_1 = t1_1) as Hrwrt. 
      SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo t1_1 l === Some true). destruct b.
      SSSCase "t1_1 [= l". apply LIO_toLabeled with (n5 := n5) (l' := l') (c' := c').
      assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. 
      apply lio_reduce_multi_helper.
      assumption. assumption. assumption. assumption. 
      assumption. assumption. (* l' [= t1_1 and t1_1 [= l *) admit. 
      assumption. assumption. assumption.
      SSSSCase "t1_1 [/= l".
      apply LIO_toLabeled with (n5 := n) (l' := l2) (c' := c2).
      assumption. assumption. assumption. assumption. assumption. 
      assumption. assumption. 
      apply LIO_done.
      assumption. assumption. (*trivial *) admit. assumption. 
Qed.

Lemma lio_reduce_simulation_n_helper': forall n l l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  l1 [= l ->
  l2 [/= l ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  lio_reduce (m_Config l1 c1 (erase_term l t1)) n (m_Config l2 c2 (erase_term l t2)).
Proof.
  intros n l l1 c1 t1 l2 c2 t2 l_of_t l1_to_l not_l2_to_l H.
  generalize dependent t2.
  generalize dependent c2.
  term_cases (induction t1) Case; intros c2 t2 H.
    Case "term_LBot". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LA". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LB". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_LTop". apply labels_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VTrue". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VFalse". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VUnit". apply values_cannot_be_lio_reduced in H. contradiction. simpl. trivial.
    Case "term_VAbs". inversion H. 
    Case "term_VLIO". inversion H.
    Case "term_VLabeled". inversion H.
    Case "term_VHole". inversion H. simpl. apply LIO_hole. 
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
    Case "term_Fix". inversion H.
    Case "term_IfEl". inversion H.
    Case "term_Join". inversion H.
    Case "term_Meet". inversion H.
    Case "term_CanFlowTo". inversion H.
    Case "term_Return". inversion H. subst. 
     simpl. apply LIO_return. assumption. assumption. reflexivity.
    Case "term_Bind". inversion H. 
     SCase "bindCtx".
     subst. simpl. 
     apply LIO_bindCtx. assumption. assumption. assumption. assumption.
     apply IHt1_1.
     assumption. 
     SCase "bind".
     subst. simpl. apply LIO_bind.
     assumption. assumption. reflexivity.
    Case "term_GetLabel". inversion H. 
     subst.  
     simpl. rewrite erase_label_id.
     apply LIO_getLabel. assumption. assumption. reflexivity. assumption. assumption.
    Case "term_GetClearance". inversion H. 
     subst.  
     simpl. rewrite erase_label_id.
     apply LIO_getClearance. assumption. assumption. reflexivity. assumption. assumption.
    Case "term_LabelOf". inversion H.
    Case "term_Label". inversion H.
     SCase "labelCtx".
     subst. simpl. 
     assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
     SSCase "assertion". (* reducing label does not affect its value *) admit.
     rewrite H0.
     destruct (canFlowTo (erase_term l t1') l === Some true).
     SSCase "t1' [= l".
     apply LIO_labelCtx.
     assumption. assumption. 
     apply pure_reduce_simulation_helper.
     assumption. assumption. reflexivity.
     SSCase "t1' [/= l".
     apply LIO_labelCtx.
     assumption. assumption. 
     apply pure_reduce_simulation_helper.
     assumption. assumption. reflexivity.
     SCase "label".
     subst. simpl. 
       assert (erase_term l t1_1 = t1_1) as Hrwrt. 
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
       rewrite -> Hrwrt.
       remember (canFlowTo t1_1 l === Some true). destruct b.
       SSSCase "t1_1 [= l". apply LIO_label.
       assumption. assumption. assumption.
       assumption. assumption. reflexivity.
       SSSCase "t1_1 [/= l". 
       apply LIO_label. assumption. assumption. assumption. assumption. assumption. reflexivity.
    Case "term_UnLabel". inversion H.
      SCase "unlabelCtx".
      subst. simpl. 
      apply LIO_unlabelCtx. assumption. assumption.
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SCase "unlabel".
      subst. simpl. 
      assert (erase_term l l0 = l0) as Hrwrt. 
      SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo l0 l === Some true). destruct b.
      SSSCase "l0 [= l". apply LIO_unlabel.
      assumption. assumption. assumption. assumption. assumption.
      assumption. reflexivity.
      SSSCase "l0 [/= l". 
      (* l2 = l1 |_| l0
          l1 [= l
          l2 [/= l
          l0 [/= l
          contradiction l2 [=l since l2 = l1 |_| l0 and  l1 [= l *)
      admit.
    Case "term_ToLabeled". inversion H.
     SCase "toLabeledCtx".
      subst. simpl. 
      assert (canFlowTo (erase_term l t1_1) l = canFlowTo (erase_term l t1') l).
      SSCase "assertion". (* reducing label does not affect its value *) admit.
      rewrite H0.
      destruct (canFlowTo (erase_term l t1') l === Some true).
      SSCase "t1' [= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SSCase "t1' [/= l".
      apply LIO_toLabeledCtx.
      assumption. assumption. 
      apply pure_reduce_simulation_helper.
      assumption. assumption. reflexivity.
      SCase "tolabeled".
      subst. simpl.
      assert (erase_term l t1_1 = t1_1) as Hrwrt. 
      SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption.
      rewrite -> Hrwrt.
      remember (canFlowTo t1_1 l === Some true). destruct b.
      SSSCase "t1_1 [= l". apply LIO_toLabeled with (n5 := n5) (l' := l') (c' := c').
      assumption. assumption. assumption. assumption.
      assumption. assumption. assumption. 
      apply lio_reduce_multi_helper.
      assumption. assumption. assumption. assumption. 
      assumption. assumption. (* l' [= t1_1 and t1_1 [= l *) admit. 
      assumption. reflexivity. assumption. 
      SSSSCase "t1_1 [/= l".
      apply LIO_toLabeled with (n5 := n5) (l' := l2) (c' := c2).
      assumption. assumption. assumption. assumption. assumption. 
      assumption. assumption. 
      apply LIO_done.
      assumption. assumption. reflexivity. assumption. 
Qed.

Lemma lio_reduce_simulation_n : forall n l l1 c1 t1 l2 c2 t2,
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l2 ->
  is_l_of_t c2 ->
  lio_reduce (m_Config l1 c1 t1) n (m_Config l2 c2 t2) ->
  lio_reduce_l l n (erase_config l (m_Config l1 c1 t1)) (erase_config l (m_Config l2 c2 t2)).
Proof.
  intros n l.
  induction n as [|n'].
  Case "n = 0". apply lio_reduce_simulation_0.
  Case "n = S n'". 
  intros l1 c1 t1 l2 c2 t2 l_of_t_l l_of_t_l1 l_of_t_c1 l_of_t_l2 l_of_t_c2 H.
  generalize dependent t2.
  generalize dependent c2.
  generalize dependent l2.
  generalize dependent c1.
  generalize dependent l1.
  generalize dependent l_of_t_l.
  term_cases (induction t1) SCase; intros; try (inversion H; try inversion H8; inversion H9).
  SCase "term_VHole". inversion H. subst.
   rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_VHole)).
   apply lio_reduce_l_step.
   assumption. simpl. remember (canFlowTo l2 l === Some true). destruct b.
   SSCase "l2 [=l". simpl. rewrite <- Heqb. apply LIO_hole.
   SSCase "l2 [/=l". simpl. apply LIO_hole.
   assumption. 
  SCase "term_Bind". inversion H.
   SSCase "bindCtx". subst. 
   rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Bind t1' t1_2)).
   simpl. remember (canFlowTo l1 l === Some true). destruct b.
   SSSCase "l1 [= l". remember (canFlowTo l2 l === Some true). destruct b.
   SSSSCase "l2 [= l".
     apply lio_reduce_l_step with (n := S n'). assumption.
     apply LIO_bindCtx. assumption. assumption. assumption. assumption.
     rewrite inv_erase_conf1.
     rewrite inv_erase_conf1.
     apply lio_reduce_simulation_n_helper.
     assumption. eauto. eauto.
     assumption. assumption. assumption. assumption. 
     eauto. assumption. assumption. assumption. eauto. 
   SSSSCase "l2 [/= l". term_cases(induction t1_1) SSSSSCase.
     SSSSSCase "term_LBot". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_LA". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_LB". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_LTop". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_VTrue". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_VFalse". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_VUnit". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_VAbs". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_VLIO". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_VLabeled". apply values_cannot_be_lio_reduced in H12. contradiction. unfold is_v_of_t. trivial.
     SSSSSCase "term_VHole". inversion H12. subst.
     rewrite  <- Heqb0 in Heqb. solve by inversion.
     SSSSSCase "term_Var". inversion H12. 
     SSSSSCase "term_App". inversion H12. 
     SSSSSCase "term_Fix". inversion H12. 
     SSSSSCase "term_IfEl". inversion H12. 
     SSSSSCase "term_Join". inversion H12. 
     SSSSSCase "term_Meet". inversion H12. 
     SSSSSCase "term_CanFlowTo". inversion H12. 
     SSSSSCase "term_Return". inversion H12. 
     subst.
     rewrite <- Heqb0  in Heqb. solve by inversion.
     SSSSSCase "term_Bind". inversion H12.
     SSSSSSCase "bindCtx". subst.
     rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := 
       (t_Bind (erase_term l (t_Bind t1'0 t1_1_2)) (erase_term l t1_2))).
     rewrite <- erase_config_idempotent.
     apply lio_reduce_l_step with (n := S n').
     assumption.
     apply LIO_bindCtx.
     assumption. assumption. assumption. assumption.
     simpl.
     apply LIO_bindCtx.
     assumption. assumption. assumption. assumption.
     apply lio_reduce_simulation_n_helper'.
     assumption. eauto. eauto.
     assumption. assumption. assumption. assumption. assumption. 
     eauto. 
     SSSSSSCase "bind". subst.
     rewrite <- Heqb0  in Heqb. solve by inversion.
     SSSSSCase "term_GetLabel". inversion H12. 
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSCase "term_GetClearance". inversion H12. 
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSCase "term_LabelOf". inversion H12.
     SSSSSCase "term_Label". inversion H12. 
     SSSSSSCase "labelCtx".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSSCase "label".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSCase "term_UnLabel". inversion H12. 
     SSSSSSCase "unlabelCtx".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSSCase "unlabel".
     subst.
     simpl.
     assert (erase_term l l0 = l0). rewrite erase_label_id. reflexivity.
     assumption. assumption. rewrite -> H0.
     destruct (canFlowTo l0 l === Some true).
     SSSSSSSCase "l0 [= l". 
     rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := t_Bind (t_Return (erase_term l t2)) (erase_term l t1_2)).
     apply lio_reduce_l_step with (n := S n').
     assumption.
     apply LIO_bindCtx.
     assumption. assumption. assumption. assumption.
     apply LIO_unlabel.
     assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     assumption. assumption. eauto. 
     SSSSSSSCase "l0 [/= l".  
     rewrite inv_erase_conf0 with (l := l) (l1 := l2) (c1 := c2) (t2 := t_Bind (t_Return t_VHole) (erase_term l t1_2)).
     apply lio_reduce_l_step with (n := S n').
     assumption.
     apply LIO_bindCtx.
     assumption. assumption. assumption. assumption.
     apply LIO_unlabel.
     assumption. assumption. assumption. assumption.
     assumption. assumption. assumption. assumption.
     assumption. assumption. eauto.
     SSSSSCase "term_ToLabeled". inversion H12. 
     SSSSSSCase "toLabeledCtx".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSSSSCase "toLabeled".
     subst.
     rewrite <- Heqb0 in Heqb. solve by inversion.
     SSSCase "l1 [/= l".
     remember (canFlowTo l2 l === Some true). destruct b.
     SSSSCase "l2 [= l".
     assert ((canFlowTo l1 l2 === Some true) = true).
     apply current_label_monotonicity with (l1 := l1) (c1 := c1) (t1 := t1_1) (l2 := l2) (c2 := c2) (t2 := t1') (n := S n'). 
     assumption. assumption.
     assumption. assumption.
     assumption. 
     assert ((canFlowTo l1 l === Some true) = true).
     apply canFlowTo_transitivie with (l1 := l1) (l2 := l2) (l3 := l).
     assumption. assumption. assumption.
     assumption. eauto.
     rewrite H1 in Heqb. solve by inversion.
     SSSSCase "l2 [/= l". 
     apply lio_reduce_l_step with (n := S n'). assumption. apply LIO_hole.
     assumption.
   SSCase "bind". subst. inversion H10.
  SCase "term_Label". inversion H. inversion H11. inversion H13.
  SCase "term_UnLabel". inversion H. inversion H10. inversion H13.
  SCase "term_ToLabeled". inversion H.
   SSCase "toLabeledCtx". subst. inversion H11.
   SSCase "toLabeled". subst.
   rewrite erase_config_idempotent with (m1 := m_Config l2 c2 (t_Label t1_1 t')).
   apply lio_reduce_l_step. assumption.
   simpl. remember (canFlowTo l2 l === Some true). destruct b.
   SSSCase "l2 [= l".
   assert (erase_term l t1_1 = t1_1) as Hrwrt. rewrite erase_label_id.
   reflexivity. assumption. assumption. rewrite -> Hrwrt. clear Hrwrt.
   remember (canFlowTo t1_1 l === Some true). destruct b.
   SSSSCase "t1_1 [= l".
   apply LIO_toLabeled with (n5 := n') (l' := l') (c' := c').
   assumption. assumption. assumption. assumption. assumption.
   assumption. assumption. 
   apply lio_reduce_multi_helper.
   assumption. assumption. assumption. assumption. 
   assumption. rewrite <- Heqb. reflexivity. 
   (* l' [= t1_1 and t1_1 [= l *) admit. 
   assert (n' = n5). omega. subst n'.
   assumption. (* trivial *) admit.
   assumption. 
   SSSSCase "t1_1 [/= l".
   apply LIO_toLabeled with (n5 := n') (l' := l2) (c' := c2).
   assumption. assumption. assumption. assumption. assumption. 
   assumption. assumption. 
   apply LIO_done.
   assumption. assumption. (*trivial *) admit. assumption. 
   SSSCase "l2 [/= l". apply LIO_hole. assumption.
Qed.


Inductive lio_reduce_l_multi : t -> n -> m -> m -> Prop :=
 | LIO_l_onestep : forall l n m1 m2,
     is_l_of_t l ->
     lio_reduce_l l n m1 m2 ->
     lio_reduce_l_multi l n m1 m2
 | LIO_l_done : forall l n m1,
     is_l_of_t l ->
     lio_reduce_l_multi l n m1 m1.

Lemma simulation_multi: forall l n m1 m2,
     is_l_of_t l ->
     lio_reduce_multi m1 n m2 ->
     lio_reduce_l_multi l n (erase_config l m1) (erase_config l m2).
Proof.
  intros. inversion H0.
  Case "onestep".
  apply LIO_l_onestep.
  assumption. 
  apply lio_reduce_simulation_n.
  assumption. assumption. assumption. assumption. assumption. assumption. 
  Case "done".
  apply LIO_l_done.
  assumption. 
Qed.


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
   | t_VLIO _          => False
   | t_VLabeled _  _   => False
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

Lemma lio_reduce_l_refl : forall l n l1 c1 t1 l2 c2 t2,
   lio_reduce_l_multi l n (m_Config l1 c1 (t_VLIO t1))  (m_Config l2 c2 (t_VLIO t2)) ->
   l1 = l2 /\ c1 = c2 /\ t1 = t2.
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
Qed.



Lemma deterministic_lio_reduce_l_multi : forall lA l c t n l1 c1 t1 l2 c2 t2,
  is_l_of_t lA ->
  lio_reduce_l_multi lA n (m_Config l c t) (m_Config l1 c1 (t_VLIO t1)) ->
  lio_reduce_l_multi lA n (m_Config l c t) (m_Config l2 c2 (t_VLIO t2)) ->
  l1 = l2 /\ c1 = c2 /\ t1 = t2.
Proof.
  intros lA l c t n l1 c1 t1 l2 c2 t2 lA_is_l H H0.
  term_cases (induction t) Case.
  Case "term_LBot". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_LBot).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LA". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_LA).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LB". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_LB).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LTop". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_LTop).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VTrue". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VTrue).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VFalse". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VFalse).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VUnit". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VUnit).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VAbs". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_VAbs x t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VLIO". intros.
  assert (l = l1 /\ c = c1 /\ t = t1) as Hrwrt1.
  SCase "assertion". apply lio_reduce_l_refl with (l := lA) (n := n). assumption.
  assert (l = l2 /\ c = c2 /\ t = t2) as Hrwrt2.
  SCase "assertion". apply lio_reduce_l_refl with (l := lA) (n := n). assumption.
  inversion Hrwrt1. inversion Hrwrt2. inversion H2. inversion H4. subst. assumption.
  Case "term_VLabeled". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_VLabeled t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_VHole". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c t_VHole).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Var". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Var x)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_App". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_App t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Fix". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Fix t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_IfEl". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_IfEl t3 t4 t5)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Join". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Join t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Meet". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Meet t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_CanFlowTo". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_CanFlowTo t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Return". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Return t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Bind". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Bind t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_GetLabel". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_GetLabel)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_GetClearance". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_GetClearance)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_LabelOf". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_LabelOf t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_Label". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_Label t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_UnLabel". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_UnLabel t)).
  assumption. assumption.
  inversion H13. eauto.
  Case "term_ToLabeled". intros.
  inversion H. inversion H0.
  assert ((m_Config l1 c1 (t_VLIO t1)) = (m_Config l2 c2 (t_VLIO t2))).
  apply deterministic_lio_reduce_l with (l := lA) (n:=n) (x := m_Config l c (t_ToLabeled t3 t4)).
  assumption. assumption.
  inversion H13. eauto.
Qed.

Lemma deterministic_lio_reduce_l_multi0 : forall lA l c t n l1 c1 t1 l2 c2 t2,
  is_l_of_t lA ->
  l [/= lA ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l1 c1 (t_VLIO t1))) ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l2 c2 (t_VLIO t2))) ->
  (erase_config lA (m_Config l1 c1 (t_VLIO t1))) = (erase_config lA (m_Config l2 c2 (t_VLIO t2))).
Proof.
  intros.
  assert (l1 [/= lA). (* l [/= lA and l [= l1 from motonicity *) admit.
  assert (l2 [/= lA). (* l [/= lA and l [= l2 from motonicity *) admit.
  simpl.
  rewrite H3. rewrite H4.
  reflexivity.
Qed.

Lemma deterministic_lio_reduce_l_multi1 : forall lA l c t n l1 c1 t1 l2 c2 t2,
  is_l_of_t lA ->
  l [= lA ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l1 c1 (t_VLIO t1))) ->
  lio_reduce_l_multi lA n (erase_config lA (m_Config l c t)) (erase_config lA (m_Config l2 c2 (t_VLIO t2))) ->
  (erase_config lA (m_Config l1 c1 (t_VLIO t1))) = (erase_config lA (m_Config l2 c2 (t_VLIO t2))).
Proof.
  intros.
  simpl.
  simpl. remember (canFlowTo l1 lA === Some true). destruct b.
  Case "l1 [= lA". remember (canFlowTo l2 lA === Some true). destruct b.
  SCase "l2 [= lA".
  simpl in H1. rewrite <- Heqb in H1. rewrite H0 in H1.
  simpl in H2. rewrite  H0 in H2. rewrite <- Heqb0 in H2. 
  assert (l1 = l2 /\ c1 = c2 /\ erase_term lA t1 = erase_term lA t2).
  SSCase "assertion". apply deterministic_lio_reduce_l_multi with (lA := lA) (l := l) (c := c) (t0 := erase_term lA t) (n := n) .
  assumption. assumption. assumption.
  inversion H3. subst l1. inversion H5. subst c1. inversion H6. reflexivity.
  SCase "l2 [/= lA".
  simpl in H1. rewrite <- Heqb in H1. rewrite H0 in H1.
  simpl in H2. rewrite  H0 in H2. rewrite <- Heqb0 in H2. 
  assert (l1 = t_VHole /\ c1 = t_VHole /\ erase_term lA t1 = t_VHole).
  SSCase "assertion". apply deterministic_lio_reduce_l_multi with (lA := lA) (l := l) (c := c) (t0 := erase_term lA t) (n := n) .
  assumption. assumption. assumption.
  inversion H3. subst l1. inversion H5. subst c1. inversion H6. reflexivity.
  SCase "l2 [/= lA".
  simpl in H1. rewrite <- Heqb in H1. rewrite H0 in H1.
  Case "l1 [/= lA". remember (canFlowTo l2 lA === Some true). destruct b.
  SCase "l2 [= lA". admit.
  SCase "l2 [/= lA". reflexivity.
Qed.

Theorem non_interference : forall l n f t1 lv1 tv1 t2 lv2 tv2 T T' l1 c1 l1' c1' t1' l2' c2' t2',
    is_l_of_t l
 -> is_l_of_t lv1 -> is_l_of_t lv2
 -> is_l_of_t l1  -> is_l_of_t c1
 -> is_l_of_t l1' -> is_l_of_t c1'
 -> is_l_of_t l2' -> is_l_of_t c2'

 -> GtT G_nil f  (T_TArrow (T_TLabeled T) (T_TLIO T')) -> safe f
    (* 0 |- f : Labeled T -> T' /\ safe f*)
 -> GtT G_nil tv1 T -> safe tv1 -> t1 = t_VLabeled lv1 tv1
    (* 0 |- tv1 : T /\ safe tv1*)
 -> GtT G_nil tv2 T -> safe tv2 -> t2 = t_VLabeled lv2 tv2
    (* 0 |- tv2 : T /\ safe tv2*)
 -> l_equiv_term l t1 t2
    (* Lb lv1 tv1 =L Lb lv2 tv2 *)
 -> lio_reduce_multi (m_Config l1 c1 (t_App f t1)) n (m_Config l1' c1' (t_VLIO t1'))
    (*  <l1, c1, f t1> -->*n <l1' c1' t1'> *)
 -> lio_reduce_multi (m_Config l1 c1 (t_App f t2)) n (m_Config l2' c2' (t_VLIO t2'))
    (*  <l1, c1, f t2> -->*n <l2' c2' t2'> *)
 -> l_equiv_config l (m_Config l1' c1' (t_VLIO t1')) (m_Config l2' c2' (t_VLIO t2'))
    (* <l1' c1' t1'> =L <l2' c2' t2'> *)
 .
Proof.
  intros. subst.
  apply simulation_multi with (l := l) in H17.
  apply simulation_multi with (l := l) in H18.
  assert (
    (erase_config l (m_Config l1 c1 (t_App f (t_VLabeled lv1 tv1)))) =
    (erase_config l (m_Config l1 c1 (t_App f (t_VLabeled lv2 tv2))))) as Hrwrt.
  Case "assert". apply lequiv_config_replace_inner. unfold l_equiv_term. simpl.
  assert (erase_term l lv1 = lv1) as Hrwrt_lv1. rewrite erase_label_id. reflexivity. assumption. assumption. rewrite Hrwrt_lv1.
  assert (erase_term l lv2 = lv2) as Hrwrt_lv2. rewrite erase_label_id. reflexivity. assumption. assumption. rewrite Hrwrt_lv2.
  remember (canFlowTo lv1 l === Some true). destruct b.
  SCase "lv1 [= l". remember (canFlowTo lv2 l === Some true). destruct b.
  SSCase "lv2 [= l".  inversion H16.
  rewrite Hrwrt_lv1 in H19. rewrite <- Heqb in H19.
  rewrite H19.
  rewrite Hrwrt_lv1 in H15. rewrite Hrwrt_lv2 in H15. 
  rewrite H15. reflexivity.
  SSCase "lv2 [/= l". inversion H16.
  rewrite Hrwrt_lv1 in H19. rewrite <- Heqb in H19.
  rewrite Hrwrt_lv1 in H15. rewrite Hrwrt_lv2 in H15. 
  rewrite H15 in Heqb.
  rewrite <- Heqb in Heqb0.
  solve by inversion.
  SCase "lv1 [/= l". remember (canFlowTo lv2 l === Some true). destruct b. 
  SSCase "lv2 [= l". inversion H16.
  rewrite Hrwrt_lv1 in H19. rewrite <- Heqb in H19.
  rewrite Hrwrt_lv1 in H15. rewrite Hrwrt_lv2 in H15. 
  rewrite H15 in Heqb.
  rewrite <- Heqb in Heqb0.
  solve by inversion.
  SSCase "lv2 [/= l".  inversion H16.
  rewrite Hrwrt_lv1 in H15. rewrite Hrwrt_lv2 in H15. 
  rewrite H15. reflexivity.
  rewrite Hrwrt in H17.
  unfold l_equiv_config.
  apply deterministic_lio_reduce_l_multi with (n := n) (m0 := erase_config l (m_Config l1 c1 (t_App f (t_VLabeled lv2 tv2)))).
  assumption. assumption.
  assumption. assumption.
Qed.
