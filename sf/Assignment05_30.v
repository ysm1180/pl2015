Require Export Assignment05_29.

(* problem #30: 10 points *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n.
  apply le_n.
  apply le_S. apply IHn.
Qed.

