Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros.
  generalize dependent n.
  induction m.
  intros. destruct n.
  apply le_n. inversion H.
  intros. destruct n.
  apply O_le_n.
  inversion H.
  apply n_le_m__Sn_le_Sm.
  apply IHm.
  apply H1.
Qed.

