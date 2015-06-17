Require Export Assignment12_05.

(* problem #06: 10 points *)

Lemma value_is_nf : forall t,
  value t -> normal_form step t.
Proof.
  intros. unfold normal_form. unfold not. 
  induction H; intros. inversion H. inversion H0.
  inversion H. inversion H0. inversion H1. inversion H2. subst. apply IHvalue1. exists t1'. auto.
  subst. apply IHvalue2. exists t2'. auto.
  inversion H. inversion H0.
  inversion H0. inversion H1. subst. apply IHvalue. exists t1'. auto.
  inversion H0. inversion H1. subst. apply IHvalue. exists t1'. auto.
  inversion H. inversion H0.
  inversion H1. inversion H2. subst. apply IHvalue1. exists t1'. auto.
  subst. apply IHvalue2. exists t2'. auto.
  inversion H0. inversion H1. subst. apply IHvalue. exists t1'. auto.
Qed.

Theorem determin_step :
  deterministic step.
Proof.
  unfold deterministic. intros. generalize dependent y2. 
  step_cases (induction H) Case; intros.
  inversion H0. auto. inversion H4. subst. apply ex_falso_quodlibet.
  apply value_is_nf in H. apply H. exists t2'. auto.
  inversion H0. subst. inversion H. subst. apply IHstep in H4. rewrite H4. auto. subst.
  apply value_is_nf in H3. apply ex_falso_quodlibet. apply H3. exists t1'. auto.
  subst. inversion H. subst. apply value_is_nf in H3. apply ex_falso_quodlibet. apply H3. exists t1'0. auto.
  inversion H1. subst. apply value_is_nf in H5. apply ex_falso_quodlibet. apply H5. exists t2'. auto.
  subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'. auto.
  subst. apply IHstep in H6. rewrite H6. reflexivity.
  subst. apply value_is_nf in H6. apply ex_falso_quodlibet. apply H6. exists t2'. auto.
  inversion H0. subst. apply IHstep in H2. rewrite H2. auto. subst. inversion H.
  inversion H0. subst. inversion H1. auto.
  inversion H0. subst. apply IHstep in H2. rewrite H2. auto. subst. inversion H. 
  inversion H0. subst. inversion H1. subst. auto.
  inversion H0. subst. apply IHstep in H4. rewrite H4. auto. subst.
  apply value_is_nf in H3. apply ex_falso_quodlibet. apply H3. exists t1'. auto.
  subst. inversion H. inversion H1. subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'. auto.
  subst. apply IHstep in H6. rewrite H6. auto. subst. inversion H0.
  inversion H0. subst. inversion H3. subst. inversion H4. subst. auto.
  inversion H0. subst. apply IHstep in H5. rewrite H5. auto. subst. inversion H.
  subst. inversion H. inversion H0. subst. inversion H4. subst. auto.
  inversion H0. subst. inversion H4. subst. auto.
  inversion H0. subst. apply IHstep in H4. rewrite H4. auto. subst.
  apply value_is_nf in H3. apply ex_falso_quodlibet. apply H3. exists t1'. auto.
  inversion H1. subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'. auto.
  subst. apply IHstep in H6. rewrite H6. auto.
  inversion H0. subst. apply IHstep in H2. rewrite H2. auto.
  subst. inversion H. subst. apply value_is_nf in H2. apply ex_falso_quodlibet. apply H2. exists t1'0. auto.
  subst. apply value_is_nf in H3. apply ex_falso_quodlibet. apply H3. exists t2'. auto.
  inversion H1. subst. inversion H3. subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'0. auto.
  subst. apply value_is_nf in H0. apply ex_falso_quodlibet. apply H0. exists t2'. auto.
  subst. auto. inversion H0. subst. apply IHstep in H2. rewrite H2. auto. subst.
  inversion H. subst. apply value_is_nf in H2. apply ex_falso_quodlibet. apply H2. exists t1'0. auto. subst.
  apply value_is_nf in H3. apply ex_falso_quodlibet. apply H3. exists t2'. auto.
  inversion H1. subst. inversion H3. subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'0. auto.
  subst. apply value_is_nf in H0. apply ex_falso_quodlibet. apply H0. exists t2'. auto.
  subst. auto. inversion H0. subst. apply IHstep in H5. rewrite H5. auto.
  subst. apply value_is_nf in H5. apply ex_falso_quodlibet. apply H5. exists t1'. auto.
  inversion H0. subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'. auto.
  subst. auto. inversion H0. subst. apply IHstep in H4. rewrite H4. auto.
  inversion H0. subst. apply IHstep in H4. rewrite H4. auto.
  inversion H0. subst. apply IHstep in H7. rewrite H7. auto.
  subst. inversion H. subst. apply value_is_nf in H7. apply ex_falso_quodlibet. apply H7. exists t1'. auto.
  subst. inversion H. subst. apply value_is_nf in H7. apply ex_falso_quodlibet. apply H7. exists t1'. auto.
  inversion H0. subst. inversion H7. subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'. auto.
  subst. auto. inversion H0. subst. inversion H7. subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'. auto.
  subst. auto. inversion H0. subst. apply IHstep in H4. rewrite H4. auto.
  subst. apply value_is_nf in H3. apply ex_falso_quodlibet. apply H3. exists t1'. auto.
  inversion H1. subst. apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'. auto.
  subst. apply IHstep in H6. rewrite H6. auto.
  inversion H0. subst. apply IHstep in H7. rewrite H7. auto.
  subst. inversion H. subst. inversion H0. subst. apply IHstep in H2. rewrite H2. auto.
  subst. inversion H. subst. apply value_is_nf in H7. apply ex_falso_quodlibet. apply H7. exists t1'0. auto.
  subst. apply value_is_nf in H8. apply ex_falso_quodlibet. apply H8. exists t2'. auto.
  inversion H0. subst. inversion H6. auto. 
  inversion H1. subst. inversion H8. subst. 
  apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'0. auto.
  subst. apply value_is_nf in H0. apply ex_falso_quodlibet. apply H0. exists t2'. auto.
  subst. auto. inversion H0. subst. apply IHstep in H2. rewrite H2. auto.
  inversion H1. subst. inversion H5. subst.
  apply value_is_nf in H. apply ex_falso_quodlibet. apply H. exists t1'0. auto.
  subst. apply value_is_nf in H0. apply ex_falso_quodlibet. apply H0. exists t2'. auto.
  subst. auto.
Qed.

Lemma wow : forall p q r t,
  p ==>* t -> p ==> q -> q ==> r -> r ==> p -> (t = p \/ t = q \/ t = r).
Proof.
  intros. inversion H. auto. subst. inversion H4. subst.
  right. left. eapply determin_step. apply H3. auto.
  subst. inversion H6. subst. assert (y = q). eapply determin_step. apply H3. auto.
  subst. right. right. eapply determin_step. apply H5. auto. subst.
Admitted.


Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
  unfold tloop. intros Hc. destruct Hc. destruct H.
  inversion H. clear H. subst. apply H0. eexists. apply ST_AppFix. auto. auto.
  subst.
  exact FILL_IN_HERE.
Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

