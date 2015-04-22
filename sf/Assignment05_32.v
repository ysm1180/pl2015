Require Export Assignment05_31.

(* problem #32: 10 points *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
<<<<<<< HEAD
  intros.
  generalize dependent n.
  induction m.
  intros. inversion H.
  apply le_n. inversion H2.
  intros. destruct n.
  apply le_S. apply O_le_n.
  inversion H.
  apply le_n.
  assert (S n <= m).
  apply IHm. apply H2.
  apply le_S. apply H3.
=======
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.

