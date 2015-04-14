Require Export Assignment05_17.

(* problem #18: 10 points *)





(** 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  intros.
  apply g_plus5 with (n:=8+n).
  apply g_plus5 with (n:=3+n).
  apply g_plus3.
  apply H.
Qed.
(** [] *)




