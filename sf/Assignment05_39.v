Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  unfold not.
  intros.
  generalize dependent n.
  induction m.
  intros. destruct n.
  inversion H.
  inversion H0.
  intros. destruct n.
  inversion H.
  inversion H.
  apply IHm in H2. inversion H2.
  apply Sn_le_Sm__n_le_m. apply H0.
Qed.
(** [] *)

