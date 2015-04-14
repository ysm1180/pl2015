Require Export Assignment05_32.

(* problem #33: 10 points *)

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction a.
  simpl. apply O_le_n.
  simpl. apply n_le_m__Sn_le_Sm. apply IHa.
Qed.

