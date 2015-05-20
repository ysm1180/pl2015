Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv, cequiv.
  intros.
  split; intros.
  inversion H2; subst.
  apply E_IfTrue. rewrite <- H. assumption.
  rewrite <- H0. assumption.
  subst. apply E_IfFalse. rewrite <- H. assumption.
  rewrite <- H1. assumption.
  inversion H2; subst.
  apply E_IfTrue. rewrite H. assumption.
  rewrite H0. assumption.
  apply E_IfFalse. rewrite H. assumption.
  rewrite H1. assumption.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

