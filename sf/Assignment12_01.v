Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Lemma arrow_neq_T :
  ~ (exists T T', TArrow T T' = T).
Proof.
  intros Hc. inversion Hc.
  induction x; try solve by inversion 2.
  inversion H. inversion H0. apply IHx1. exists x2. auto.
  (*
  inversion H. inversion H0.
  inversion H. inversion H0.
  inversion H. inversion H0.
  inversion H. inversion H0.
  inversion H. inversion H0.
  *)
Qed.

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  intros Hc. inversion Hc. inversion H. clear H.
  inversion H0. subst. clear H0.
  inversion H5. subst. clear H5.
  inversion H2. subst. clear H2.
  inversion H4. subst. clear H4.
  rewrite H1 in H2. inversion H2.
  apply arrow_neq_T. exists T1.  exists T12. auto.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

