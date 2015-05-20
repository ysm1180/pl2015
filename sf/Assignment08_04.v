Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros. 
  generalize dependent st.
  induction c; intros.
  exists st. apply E_Skip.
  exists (update st i (aeval st a)). apply E_Ass. reflexivity.
  simpl in NOWHL. apply andb_true_iff in NOWHL. destruct NOWHL.
  assert (exists st', c1 / st || st').
    apply IHc1. apply H.
  inversion H1.
  assert (exists st'', c2 / x || st'').
    apply IHc2. apply H0.
  inversion H3.
  exists x0. apply E_Seq with x. apply H2. apply H4.
  simpl in NOWHL. apply andb_true_iff in NOWHL. destruct NOWHL.
  assert (exists st', c1 / st || st').
    apply IHc1. apply H.
  inversion H1.
  assert (exists st', c2 / st || st').
    apply IHc2. apply H0.
  inversion H3.
  destruct (beval st b) eqn: Heval. exists x. apply E_IfTrue.
  apply Heval. apply H2. exists x0. apply E_IfFalse. apply Heval.
  apply H4.
  inversion NOWHL.
Qed.

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

