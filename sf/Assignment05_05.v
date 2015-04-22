Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
<<<<<<< HEAD
  intros.
  split. intros.
  destruct H as [HP | [HQ HR]].
  split. left. apply HP.
  left. apply HP.
  split. right. apply HQ.
  right. apply HR.
  intros.
  destruct H as [[HP | HQ] [HP2 | HR]].
  left. apply HP.
  left. apply HP.
  left. apply HP2.
  right. split.
  apply HQ.
  apply HR.
=======
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.
(** [] *)


