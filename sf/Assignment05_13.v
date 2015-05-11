Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros.
  unfold not.
  generalize dependent m.
  induction n.
  intros. induction m.
  inversion H.
  inversion H0.
  intros. induction m.
  inversion H0.
  inversion H. apply IHn in H2. apply H2. inversion H0. reflexivity.  
Qed.
(** [] *)



