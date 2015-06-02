Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  induction n; intros. 
  exists st. destruct H. split. constructor. auto.

  assert (exists st' : state,
          par_loop / st ==>c* par_loop / st' /\ st' X = n /\ st' Y = 0).
  apply IHn. assumption. 
  destruct H0.
  rename x into st'.
  exists (update st' X (S n)).
  split. destruct H0.
  eapply multi_trans. apply H0.
  eapply par_body_n__Sn. assumption.
  split. unfold update. simpl. reflexivity.
  unfold update. simpl. destruct H0. destruct H1. assumption.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

