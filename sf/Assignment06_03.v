Require Export Assignment06_02.

(* problem #03: 10 points *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  intros.
  inversion H as [m Hm].
  destruct Hm.
  left. exists m. apply H0.
  right. exists m. apply H0.
  intros.
  inversion H. inversion H0 as [m Hm].
  exists m. left. apply Hm.
  inversion H0 as [m Hm].
  exists m. right. apply Hm.
Qed.
(** [] *)


