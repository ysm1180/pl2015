Require Export Assignment05_09.

(* problem #10: 10 points *)




(** 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
<<<<<<< HEAD
Proof.
  intros.
  unfold not.
  intros.
  destruct H.
  apply H0. apply H.
=======
Proof. 
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.
(** [] *)



