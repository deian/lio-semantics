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
  ~ (lio_reduce (m_Config l c v n) m).
Proof.
  intros l c v n m H1.
  unfold not.
  intro H2.
  induction v; repeat (solve by inversion).
Qed.

(* NO!
Lemma values_cannot_be_lio_reduced_multi : forall l c v n m,
  is_v_of_t v ->
  ~ (lio_reduce_multi (m_Config l c v n) m).
Proof.
  intros l c v n m H1.
  unfold not.
  intro H2.
  inversion H2.
  apply values_cannot_be_lio_reduced in H10. solve by inversion. assumption.
  subst.
  induction v; repeat (solve by inversion).
  inversion H2.
  subst.
  apply values_cannot_be_lio_reduced in H10. solve by inversion. assumption.
  subst.
  apply LIO_done in H2.
  induction v; repeat (solve by inversion).
Qed.
*)

Hint Resolve values_cannot_be_lio_reduced.

Corollary labels_cannot_be_lio_reduced : forall l c v n m, 
  is_l_of_t v ->
  ~ (lio_reduce (m_Config l c v n) m).
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

(*
Lemma deterministic_lio_reduce : forall l c t n v1 n1 v2 n2,
   is_l_of_t l ->
   is_l_of_t c ->
   is_v_of_t v1 ->
   is_v_of_t v2 ->
   lio_reduce (m_Config l c t n) (m_Config l c v1 n1) ->
   lio_reduce (m_Config l c t n) (m_Config l c v2 n2) ->
   v1 = v2 /\ n1 = n2.
Proof.
  intros.
  inversion H3.
  inversion H4.
  split.
  subst.
  inversion H16.
  reflexivity. subst. assumption.
  intros l c t n v1 n1 v2 n2 l_of_t_l l_of_t_c v_of_t_v1 v_of_t_v2 Hy1 Hy2.
  generalize dependent v2. 
  inversion Hy1.
  lio_reduce_cases (induction H12) Case; intros y2 Hy2.
  Case "LIO_return". 
    inversion Hy2. 
    apply H1 with (l := l) (c := c) (x := x) (n0 := n0).
    subst.
    
  Case "LIO_bindCtx". 
    inversion Hy2.
  Case "LIO_bind".
    inversion Hy2.
  Case "LIO_getLabel". admit.
  Case "LIO_getClearance". admit.
  Case "LIO_labelCtx".
    inversion Hy2.
    subst.
    rewrite H10.
    assert (t1' = t1'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. reflexivity.
    subst t1 c0 l_5 t2.
    apply labels_cannot_be_reduced in H1. solve by inversion. assumption.
  Case "LIO_label".
    inversion Hy2.
    subst. 
    apply labels_cannot_be_reduced in H12. solve by inversion. assumption.
    reflexivity.
  Case "LIO_unlabelCtx".
    inversion Hy2.
    subst. 
    assert (t' = t'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t5). assumption. assumption.
    subst t'0. reflexivity.
    subst. 
    apply values_cannot_be_reduced in H1. solve by inversion. simpl. trivial.
 Case "LIO_unlabel".
    inversion Hy2.
    subst.
    apply values_cannot_be_reduced in H12. solve by inversion. simpl. trivial.
    subst.
    assert (l2 = l3).
    SCase "assertion". apply deterministic_pure_reduce with (x := t_Join l_5 l1). assumption. assumption.
    subst l3. reflexivity.
  Case "LIO_toLabeled".
    inversion Hy2.
    subst.
    inversion H6.
    inversion H23.
    subst.
  Case "LIO_hole".
    inversion Hy2.
    reflexivity.
Qed.

*)


Lemma deterministic_lio_reduce_multi : forall l c t n l' c' t' n' t'' n'',
  lio_reduce_multi (m_Config l c t n) (m_Config l' c' (t_Return t') n')   ->
  lio_reduce_multi (m_Config l c t n) (m_Config l' c' (t_Return t'') n'') ->
  t' = t'' /\ n' = n''.
Admitted.
(*
Proof.
  
  intros l c t n l' c' t' n' t'' n'' H1 H2.
  generalize dependent t''.
  inversion H1.
  lio_reduce_cases (induction H12) Case; intros t'' Hy2; subst.
  Case "LIO_return".
    inversion Hy2. subst. reflexivity.
  subst.
*)



(* NOT THE CASE -->* needs to be deterministic;
   maybe want to show that
   t -->* return t'
   t -->* return t''
   then t' = t'' 
*)
Lemma deterministic_lio_reduce :
  deterministic lio_reduce.
Proof.
  unfold deterministic. intros x y1 y2 Hy1 Hy2.
  generalize dependent y2. 
  lio_reduce_cases (induction Hy1) Case; intros y2 Hy2.
  Case "LIO_return".
    inversion Hy2. reflexivity.
  Case "LIO_bindCtx".
    inversion Hy2.
    subst. apply IHHy1 in H14. inversion H14. reflexivity.
    subst.
    inversion Hy2.
    subst. inversion Hy1. 
  Case "LIO_bind".
    inversion Hy2.
    subst. inversion H11. reflexivity.
  Case "LIO_getLabel".
    inversion Hy2.
    subst. reflexivity.
  Case "LIO_getClearance".
    inversion Hy2.
    subst. reflexivity.
  Case "LIO_labelCtx".
    inversion Hy2.
    subst. 
    assert (t1' = t1'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t1). assumption. assumption.
    subst t1'0. reflexivity.
    subst t1 c0 l_5 t2.
    apply labels_cannot_be_reduced in H1. solve by inversion. assumption.
  Case "LIO_label".
    inversion Hy2.
    subst. 
    apply labels_cannot_be_reduced in H12. solve by inversion. assumption.
    reflexivity.
  Case "LIO_unlabelCtx".
    inversion Hy2.
    subst. 
    assert (t' = t'0).
    SCase "assertion". apply  deterministic_pure_reduce with (x := t5). assumption. assumption.
    subst t'0. reflexivity.
    subst. 
    apply values_cannot_be_reduced in H1. solve by inversion. simpl. trivial.
 Case "LIO_unlabel".
    inversion Hy2.
    subst.
    apply values_cannot_be_reduced in H12. solve by inversion. simpl. trivial.
    subst.
    assert (l2 = l3).
    SCase "assertion". apply deterministic_pure_reduce with (x := t_Join l_5 l1). assumption. assumption.
    subst l3. reflexivity.
  Case "LIO_toLabeled".
    inversion Hy2.
    subst.
  Case "LIO_hole".
    inversion Hy2.
    reflexivity.
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

Axiom canFlowToSyntaxRel : forall l1 l2,
  (canFlowTo l1 l2 === Some true) = true <->
  pure_reduce (t_CanFlowTo l1 l2) t_VTrue.

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
                                     (if canFlowTo l1 l === Some true
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
   | t_Label t5 t'     => t_Label (erase_term l t5) (erase_term l t')
   | t_UnLabel t5      => t_UnLabel (erase_term l t5)
   | t_ToLabeled t1 t2 => t_ToLabeled (erase_term l t1) (erase_term l t2)
   | t_MkToLabeledTCB l_5 c l1 t5 => t_MkToLabeledTCB (erase_term l l_5)
                                                      (erase_term l c)
                                                      (erase_term l l1)
                                                      (erase_term l t5)
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
   | m_Config l1 c1 t1 => if canFlowTo l1 l
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
  Case "term_Label". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_UnLabel". simpl. rewrite <- IHt1. reflexivity.
  Case "term_ToLabeled". simpl. rewrite <- IHt1_1. rewrite <- IHt1_2. reflexivity.
  Case "term_MkToLabeledTCB". simpl. rewrite <- IHt1_1.
   rewrite <- IHt1_2. rewrite <- IHt1_3. rewrite <- IHt1_4. reflexivity.
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

Lemma erase_term_homo_subst : forall l t1 x t2,
  is_l_of_t l ->
  erase_term l (tsubst_t t1 x t2) = tsubst_t (erase_term l t1) x (erase_term l t2).
Proof. 
  intros l t1 x t2 l_of_t.
  generalize dependent t1.
  term_cases (induction t2) Case; intros t1; eauto.
  Case "term_VAbs". simpl. rewrite IHt2. reflexivity.
  Case "term_VLIO". simpl. rewrite IHt2. reflexivity.
  Case "term_VLabeled". admit.
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
  Case "term_Label". simpl. rewrite IHt2_1. rewrite IHt2_2. reflexivity.
  Case "term_UnLabel". simpl. rewrite IHt2. reflexivity.
  Case "term_ToLabeled". simpl. rewrite IHt2_1. rewrite IHt2_2. reflexivity.
  Case "term_MkToLabeledTCB". simpl. rewrite IHt2_1. rewrite IHt2_2. rewrite IHt2_3. rewrite IHt2_4. reflexivity.
Qed.
Hint Resolve erase_term_homo_subst.

Lemma erase_hole_implies_anything: forall l l1 t1,
  is_l_of_t l ->
  is_l_of_t l1 ->
  canFlowTo l1 l = Some false ->
  erase_term l (t_VLabeled l1 t_VHole) = erase_term l (t_VLabeled l1 t1).
Proof.
  intros. simpl. rewrite H1. simpl. reflexivity.
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
    Case "term_MkToLabeledTCB". inversion H.
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
    Case "term_MkToLabeledTCB". inversion H.
Qed.

(* -->L *)
Inductive lio_reduce_l : t -> m -> m -> Prop :=
   | lio_reduce_l_step : forall l m1 m2,
     is_l_of_t l ->
     lio_reduce m1 m2 ->
     lio_reduce_l l m1 (erase_config l m2).

Lemma deterministic_lio_reduce_l : forall l x y1 y2,
  lio_reduce_l l x y1 ->
  lio_reduce_l l x y2 ->
  y1 = y2.
Proof.
  intros l x y1 y2 Hy1 Hy2. 
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  inversion Hy2.
  assert (m2 = m3).
  Case "assertion". apply deterministic_lio_reduce with (x := m1). assumption. assumption. 
  rewrite H6. reflexivity.
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
Admitted.

Lemma inv_erase_labeled : forall l l1 (t2 : t),
  is_l_of_t l ->
  is_l_of_t l1 ->
  (canFlowTo l1 l === Some true) = false ->
  t_VLabeled l1 t_VHole = erase_term l (t_VLabeled l1 t2).
Proof.
Admitted.

Lemma inv_erase_conf : forall l l1 c1 (t2 : t),
  is_l_of_t l ->
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  not (canFlowTo l1 l = Some true) ->
  m_Config t_VHole t_VHole t_VHole = erase_config l (m_Config l1 c1 t2).
Proof.
Admitted.


Lemma inv_erase_return : forall l l1 c1 (t2 : t),
  is_l_of_t l1 ->
  is_l_of_t c1 ->
  is_l_of_t l ->
  m_Config l1 c1 (t_Return (erase_term l t2)) = erase_config l (m_Config l1 c1 (t_Return t2)).
Proof. Admitted.

(*
Lemma lio_reduce_simulation_helper : forall l m1 m2,
  is_l_of_t l ->
  lio_reduce m1 m2 ->
  lio_reduce (erase_config l m1) (erase_config l m2).
Proof.
  intros l m1 m2 l_of_t H.
  generalize dependent m2.
  destruct m1.
  term_cases (induction t3) Case; intros m2 H.
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
    Case "term_Fix".  inversion H.
    Case "term_IfEl". inversion H.
    Case "term_Join". inversion H.
    Case "term_Meet". inversion H.
    Case "term_CanFlowTo". inversion H.
    Case "term_Return". inversion H.
      subst. simpl. destruct (canFlowTo t1 l).
      SCase "[= l". apply LIO_return. assumption. assumption.
      SCase "[/= l". apply LIO_hole.
    Case "term_Bind". inversion H.
    SCase "bindCtx". admit.
(*
    subst. apply IHt3_1 in H9.
    simpl. simpl in H9. simpl in IHt3_1. simpl in IHt3_2.
    destruct (canFlowTo t1 l).
      SSCase " t1 [= l". destruct (canFlowTo l' l). 
      SSSCase "l' [= l". apply LIO_bindCtx. assumption. assumption. assumption. assumption. assumption.
      SSSCase "l' [/= l". admit.
*)
    SCase "bind". subst. simpl.
    destruct (canFlowTo t1 l).
      SSCase " t1 [= l". apply LIO_bind. assumption. assumption.
      SSCase " t1 [/= l". apply LIO_hole.
    Case "term_GetLabel". inversion H.
      subst. simpl. destruct (canFlowTo t1 l).
      rewrite erase_label_id.
      SCase "[= l". apply LIO_getLabel. assumption. assumption. assumption. assumption.
      SCase "[/= l". apply LIO_hole.
    Case "term_GetClearance". inversion H.
      subst. simpl. destruct (canFlowTo t1 l).
      rewrite erase_label_id.
      SCase "[= l". apply LIO_getClearance. assumption. assumption. assumption. assumption.
      SCase "[/= l". apply LIO_hole.
    Case "term_LabelOf". inversion H.
    Case "term_Label". inversion H.
     SCase "labelCtx".
      subst. simpl. destruct (canFlowTo t1 l).
      SSCase "[= l". apply LIO_labelCtx. assumption. assumption. 
      apply pure_reduce_simulation_helper. assumption. assumption.
      SSCase "[/= l". apply LIO_hole.
     SCase "label".
      subst. simpl. destruct (canFlowTo t1 l).
      SSCase "[= l". destruct (canFlowTo t3_1 l === Some true).
      SSSCase "t3_1 [= l". rewrite erase_label_id. apply LIO_label. 
     assumption. assumption. assumption. assumption. assumption. assumption. assumption. 
      SSSCase "t3_1 [/= l". 
      SSCase "[/= l". apply LIO_hole.
    Case "term_UnLabel". inversion H.
     SCase "unlabelCtx".
      subst. simpl. destruct (canFlowTo t1 l).
      SSCase "t1 [= l". apply LIO_unlabelCtx. assumption. assumption. 
      apply pure_reduce_simulation_helper. assumption. assumption.
      SSCase "t1 [/= l". apply LIO_hole.
     SCase "unlabel".
      subst. simpl. destruct (canFlowTo t1 l).
      SSCase "t1 [= l". destruct (canFlowTo l2 l).
      SSSCase "l2 [= l". remember (canFlowTo l1 l === Some true).
      destruct b1.
      SSSSCase "l1 [= l". apply LIO_unlabel.
      assumption. assumption. rewrite erase_label_id. assumption. assumption.
      assumption. assumption. rewrite erase_label_id. assumption. assumption.
      assumption. assumption. 
      SSSSCase "l1 [/= l". admit.
      SSSCase "l2 [/= l". remember (canFlowTo l1 l === Some true).
      destruct b0.
      SSSSCase "l1 [= l". admit.
      SSSSCase "l1 [/= l". admit.
      SSCase "t1 [/= l". destruct (canFlowTo l2 l).
      SSSCase "l2 [= l". admit.
      SSSCase "l2 [/= l". apply LIO_hole.
    Case "term_ToLabeled". admit.
    Case "term_MkToLabeledTCB". admit.
Qed.
*)

Lemma lio_reduce_simulation : forall l m1 m2,
  is_l_of_t l ->
  lio_reduce m1 m2 ->
  lio_reduce_l l (erase_config l m1) (erase_config l m2).
Proof.
  intros l m1 m2 l_of_t H.
  generalize dependent m2.
  destruct m1.
  term_cases (induction t3) Case; intros m2 H.
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
      rewrite erase_config_idempotent with (m1 := m_Config t_VHole t_VHole t_VHole).
      apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
    Case "term_Var". inversion H.
    Case "term_App".  inversion H.
    Case "term_Fix". inversion H.
    Case "term_IfEl". inversion H.
    Case "term_Join". inversion H.
    Case "term_Meet". inversion H.
    Case "term_CanFlowTo". inversion H.
    Case "term_Return". inversion H. 
      subst. 
      rewrite erase_config_idempotent with (m1 := m_Config t1 t2 (t_VLIO t3)).
      simpl. destruct (canFlowTo t1 l).
      SCase "t1 [= l". 
      apply lio_reduce_l_step. assumption. apply LIO_return. assumption. assumption.
      SCase "t1 [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
    Case "term_Bind". (*inversion H. subst.
      SCase "bindCtx".
      rewrite erase_config_idempotent with (m1 := m_Config l' c' (t_Bind t1' t3_2)).
      simpl. remember (canFlowTo t1 l). destruct o.
      SSCase "t1 [= l". remember (canFlowTo l' l).
      destruct o.
      SSSCase "l' [= l". apply lio_reduce_l_step. assumption. apply LIO_bindCtx. assumption. 
      assumption. assumption. assumption. 
      admit.
      SSSCase "l' [/= l". 
      rewrite inv_erase_conf with (l := l) (l1 := t1) (c1 := t2) (t2 := t_Bind (erase_term l t1') (erase_term l t3_2)).
      rewrite <- erase_config_idempotent. apply lio_reduce_l_step. assumption. 
      apply LIO_bindCtx. assumption. assumption. assumption. assumption.
      admit. assumption. assumption. assumption. assumption. unfold not.
      SSCase "t1 [/= l". destruct (canFlowTo l' l).
      SSSCase "l' [= l". admit.
      SSSCase "l' [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole.
      SCase "bind".
      subst. simpl. destruct (canFlowTo t1 l).
      SSCase "t1 [= l". apply lio_reduce_l_step. assumption. apply LIO_bind.
      assumption. assumption.
      SSCase "t1 [= l". apply lio_reduce_l_step. assumption. apply LIO_hole.*)
      admit.
    Case "term_GetLabel". inversion H.
      subst. 
      rewrite erase_config_idempotent with (m1 := m_Config t1 t2 (t_Return t1)).
      simpl. destruct (canFlowTo t1 l).
      SCase "t1 [= l". apply lio_reduce_l_step. assumption. rewrite erase_label_id. apply LIO_getLabel. assumption. assumption. assumption. assumption.
      SCase "t1 [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
    Case "term_GetClearance". inversion H.
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config t1 t2 (t_Return t2)).
      simpl. destruct (canFlowTo t1 l).
      SCase "t1 [= l". apply lio_reduce_l_step. assumption. rewrite erase_label_id. apply LIO_getClearance. assumption. assumption. assumption. assumption.
      SCase "t1 [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
    Case "term_LabelOf". inversion H.
    Case "term_Label". inversion H.
      SCase "labelCtx".
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config t1 t2 (t_Label t1' t3_2)).
      simpl. 
      destruct (canFlowTo t1 l).
      SSCase "t1 [= l". apply lio_reduce_l_step. assumption. apply LIO_labelCtx. assumption. assumption. 
     apply pure_reduce_simulation_helper. assumption. assumption. 
      SSCase "t1 [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
      SCase "label". subst.
      rewrite erase_config_idempotent with (m1 := m_Config t1 t2 (t_Return (t_VLabeled t3_1 t3_2))).
      simpl. destruct (canFlowTo t1 l).
      SSCase "t1 [= l". remember (canFlowTo t3_1 l === Some true).
       destruct b0.
       SSSCase "t3_1 [= l". apply lio_reduce_l_step. assumption. apply LIO_label.
       assumption. assumption. rewrite erase_label_id. assumption. assumption.
       assumption. rewrite erase_label_id. assumption. assumption. assumption.
       rewrite erase_label_id. assumption. assumption. assumption.
       SSSCase "t3_1 [/= l". 
       assert (erase_term l t3_1  = t3_1) as Hrwrt3_1. rewrite erase_label_id. reflexivity. assumption. assumption. rewrite Hrwrt3_1.
       rewrite inv_erase_labeled with (l := l) (l1 := t3_1) (t2 := (erase_term l t3_2)).
       rewrite inv_erase_return.
       rewrite <- erase_config_idempotent.
       apply lio_reduce_l_step. assumption. 
       apply LIO_label. assumption. assumption. assumption. assumption. assumption.
       assumption. assumption. assumption. assumption. assumption. assumption.
       eauto.
      SSCase "t1 [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
    Case "term_UnLabel". inversion H.
      SCase "unlabelCtx".
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config t1 t2 (t_UnLabel t')).
      simpl. destruct (canFlowTo t1 l).
      SSCase "t1 [= l". apply lio_reduce_l_step. assumption. apply LIO_unlabelCtx. assumption. assumption. 
     apply pure_reduce_simulation_helper. assumption. assumption. 
      SSCase "t1 [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
      SCase "unlabel".
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config l2 t2 (t_Return t0)).
      simpl. destruct (canFlowTo t1 l).
      SSCase "t1 [= l".  remember (canFlowTo l2 l).
      destruct o.
      SSSCase "l2 [= l". remember (canFlowTo l1 l === Some true).
      destruct b1.
      SSSSCase "l1 [= l".
      apply lio_reduce_l_step. assumption. 
      apply LIO_unlabel. assumption. assumption. 
      rewrite erase_label_id. assumption. assumption. assumption. assumption. 
      rewrite erase_label_id. assumption. assumption. assumption. assumption. 
      SSSSCase "l1 [/= l".
       (* l1 [/= l
          l2 [= l
          t1 [= l
          l2 = t1 |_| l1
          => contradiction *) admit.
      SSSCase "l2 [/= l". remember (canFlowTo l1 l === Some true).
      destruct b0.
      SSSSCase "l1 [= l".
      rewrite inv_erase_conf with (l := l) (l1 := l2) (c1 := t2) (t2 := t_Return (erase_term l t0)).
      rewrite <- erase_config_idempotent.
      apply lio_reduce_l_step. assumption. 
      apply LIO_unlabel.
      assumption. assumption. 
      rewrite erase_label_id. assumption. 
      assumption. assumption. assumption. 
      rewrite erase_label_id. assumption. 
      assumption. assumption. assumption. assumption. assumption. assumption. assumption. 
      unfold not. intro. rewrite <- Heqo in H0. inversion H0.
      SSSSCase "l1 [/= l".
      rewrite inv_erase_conf with (l := l) (l1 := l2) (c1 := t2) (t2 := t_Return t_VHole).
      rewrite <- erase_config_idempotent.
      apply lio_reduce_l_step. assumption. 
      apply LIO_unlabel.
      assumption. assumption. 
      rewrite erase_label_id. assumption. 
      assumption. assumption. assumption. 
      rewrite erase_label_id. assumption. 
      assumption. assumption. assumption. assumption. assumption. assumption. assumption. 
      unfold not. intro. rewrite <- Heqo in H0. inversion H0.
      SSCase "t1 [/= l".  remember (canFlowTo l2 l).
      destruct o.
      SSSCase "l2 [= l". 
       (* l2 [= l
          t1 [/=l
          l2 = t1 |_| l1
          => contradiction *) admit.
      SSSCase "l2 [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
    Case "term_ToLabeled". inversion H.
      subst.
      rewrite erase_config_idempotent with (m1 := m_Config t1 t2 (t_Bind t3_2 (t_VAbs x (t_MkToLabeledTCB t1 t2 t3_1 (t_Var x))))).
      simpl. destruct (canFlowTo t1 l).
      SSCase "t1 [= l". apply lio_reduce_l_step. assumption.
       assert (erase_term l t1 = t1) as Hrwrt1.
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption. 
       assert (erase_term l t2 = t2) as Hrwrt2.
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption. 
       assert (erase_term l t3_1 = t3_1) as Hrwrt3_1.
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption. 
       rewrite Hrwrt1. rewrite Hrwrt2.  rewrite Hrwrt3_1. 
       apply LIO_toLabeled. assumption. assumption. assumption.
	     assumption. assumption.
      SSCase "t1 [/= l". apply lio_reduce_l_step. assumption. apply LIO_hole. assumption.
    Case "term_MkToLabeledTCB". inversion H.
      subst.
      rewrite erase_config_idempotent with (m1 := (m_Config t3_1 t3_2 (t_Label t3_3 t3_4))).
      simpl. remember (canFlowTo t1 l).
      destruct o.
      SSCase "t1 [= l". 
(* apply lio_reduce_l_step. assumption. *)
       assert (erase_term l t3_1 = t3_1) as Hrwrt3_1.
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption. 
       assert (erase_term l t3_2 = t3_2) as Hrwrt3_2.
       SSSCase "assertion". rewrite erase_label_id. reflexivity. assumption. assumption. 
       rewrite Hrwrt3_1.
       rewrite Hrwrt3_2.
      remember (canFlowTo t3_1 l).
      destruct o.
      SSSCase "t3_1 [= l". 
      apply lio_reduce_l_step. assumption.
      apply LIO_mkToLabeledTCB.
      assumption. assumption.
      assumption. assumption.
      rewrite erase_label_id. assumption.
      assumption. assumption.
      rewrite erase_label_id. assumption.
      assumption. assumption.
      SSSCase "t3_1 [/= l".
      rewrite inv_erase_conf with (l := l) (l1 := t3_1) (c1 := t3_2) (t2 := t_Label (erase_term l t3_3) (erase_term l t3_4)).
      rewrite <- erase_config_idempotent.
      apply lio_reduce_l_step. assumption.
      apply LIO_mkToLabeledTCB.
      assumption. assumption.
      assumption. assumption.
      rewrite erase_label_id. assumption.
      assumption. assumption.
      rewrite erase_label_id. assumption.
      assumption. assumption.
      assumption. assumption.
      assumption. assumption.
      unfold not. intro.
      rewrite <- Heqo0 in H0. inversion H0.
      SSCase "t1 [/= l". remember (canFlowTo t3_1 l).  destruct o.
      SSSCase "t3_1 [= l". 
      rewrite erase_config_idempotent.
      rewrite inv_erase_conf with (l := l) (l1 := t1) (c1 := t2) (t2 := t_MkToLabeledTCB t3_1 t3_2 (erase_term l t3_3) (erase_term l t3_4)).
      apply lio_reduce_l_step. assumption.
      admit.
      assumption.
      assumption.
      assumption.
      unfold not. intros. rewrite  <- Heqo in H0. inversion H0.
      assumption.
      SSSCase "t3_1 [/= l". 
      apply lio_reduce_l_step. assumption.
      apply LIO_hole. assumption.
Qed.
