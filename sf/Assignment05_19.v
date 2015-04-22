Require Export Assignment05_18.

(* problem #19: 10 points *)




(** 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
<<<<<<< HEAD
  intros.
  induction H.
  simpl. apply H0.
  apply g_plus3 with (n:=n+m). apply IHgorgeous.
  apply g_plus5 with (n:=n+m). apply IHgorgeous.
=======
 (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.
(** [] *)


