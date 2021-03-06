Require Export Assignment05_21.

(* problem #22: 10 points *)



(** 1 star (inversion_practice)  *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H as [| n' H'].
  inversion H' as [| n'' H''].
  apply H''.
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)


