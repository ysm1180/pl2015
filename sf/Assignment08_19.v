Require Export Assignment08_18.

(* problem #19: 10 points *)

Lemma constfold_0plus_sound:
  ctrans_sound constfold_0plus.
Proof.
  intros c.
  assert (cequiv c (fold_constants_com c)).
    apply fold_constants_com_sound.
  assert (cequiv (fold_constants_com c) (optimize_0plus_com (fold_constants_com c))).
    apply optimize_0plus_com_sound.
  unfold constfold_0plus.
  unfold cequiv. intros. split; intros.
  apply H0. apply H. assumption.
  apply H. apply H0. assumption.
Qed.

(*-- Check --*)
Check constfold_0plus_sound:
  ctrans_sound constfold_0plus.
