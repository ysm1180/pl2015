Require Export Assignment05_08.

(* problem #09: 10 points *)



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
<<<<<<< HEAD
  intros.
  unfold not.
  unfold not in H0.
  intros. apply H0. apply H. apply H1.
=======
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.
(** [] *)



