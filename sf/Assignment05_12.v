Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)

Lemma ex_falso : forall P : Prop,
  False -> P.
Proof.
  intros.
  inversion H.
Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  intros.
  unfold not in H.
  generalize dependent n.
  induction m.
  intros. destruct n. apply ex_falso. apply H. reflexivity.
  reflexivity.
  intros. destruct n. reflexivity.
  apply IHm. intros. apply H. rewrite -> H0. reflexivity.
Qed.
(** [] *)




