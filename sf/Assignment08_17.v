Require Export Assignment08_16.

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intros. unfold bequiv. intros.
  bexp_cases (induction b) Case;
  try reflexivity;
  try (rename a into a1; rename a0 into a2; simpl;
  remember (optimize_0plus_aexp a1) as a1';
  remember (optimize_0plus_aexp a2) as a2';
  replace (aeval st a1) with (aeval st a1') by
    (subst a1'; rewrite <- optimize_0plus_aexp_sound; reflexivity);
  replace (aeval st a2) with (aeval st a2') by
    (subst a2'; rewrite <- optimize_0plus_aexp_sound; reflexivity);
  reflexivity).
  simpl. rewrite IHb. reflexivity.
  simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

