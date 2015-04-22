Require Export Assignment05_14.

(* problem #15: 10 points *)



(** 1 star (double_even)  *)
Theorem double_even : forall n,
  ev (double n).
Proof.
<<<<<<< HEAD
  intros.
  induction n.
  simpl. apply ev_0.
  simpl. apply ev_SS. apply IHn.
=======
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.
(** [] *)




