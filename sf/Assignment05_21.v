Require Export Assignment05_20.

(* problem #21: 10 points *)





(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
<<<<<<< HEAD
  intros.
  induction H.
  simpl. apply H0.
  simpl. apply ev_SS. apply IHev.
=======
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.
(** [] *)





