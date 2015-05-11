Require Export Assignment05_26.

(* problem #27: 10 points *)


Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
  intros.
  apply even__ev_strong.
  apply H.
Qed.
(** [] *)


