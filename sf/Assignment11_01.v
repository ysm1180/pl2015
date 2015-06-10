Require Export Assignment11_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue). unfold stuck.
  split.
  unfold normal_form. unfold not. intros.
  destruct H. inversion H. subst. inversion H1.
  unfold not. intros. inversion H. inversion H0. inversion H0. subst. inversion H2.
Qed.

(*-- Check --*)
Check some_term_is_stuck :
  exists t, stuck t.

