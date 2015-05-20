Require Export Assignment08_17.

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  intros c.
  com_cases (induction c) Case; simpl.
  apply refl_cequiv.
  apply CAss_congruence. apply optimize_0plus_aexp_sound.
  apply CSeq_congruence. assumption. assumption.
  apply CIf_congruence. apply optimize_0plus_bexp_sound.
  assumption. assumption.
  apply CWhile_congruence. apply optimize_0plus_bexp_sound. assumption.
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.

