Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)

Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros.
  unfold update.
  destruct (eq_id_dec x1 x2).
  rewrite <- e. symmetry. assumption.
  reflexivity.
Qed.

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  intros.
  split; intros.
  unfold aequiv in H. simpl in H.
  inversion H0; subst.
  assert (st' = update st' X (aeval st' e)).
    apply functional_extensionality.
    intro. rewrite <- H. rewrite update_same; reflexivity.
    rewrite H1 at 2. apply E_Ass. reflexivity.
  unfold aequiv in H. simpl in H.
  inversion H0; subst.
  replace (update st X (aeval st e)) with st.
  constructor.
  apply functional_extensionality. intro.
  rewrite <- H. rewrite update_same; reflexivity.
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

