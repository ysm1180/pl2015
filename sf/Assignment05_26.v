Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  intros.
  induction n.
  split. simpl. intros. apply ev_0.
  intros. apply ev_0.
  destruct IHn. split. simpl. apply H0.
  intros.
  destruct n.
  inversion H1.
  apply ev_SS. simpl in H. apply H. inversion H1. apply H3.
Qed.
(** [] *)


