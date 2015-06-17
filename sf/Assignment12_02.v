Require Export Assignment12_01.

(* problem #02: 10 points *)

(** **** Exercise: 2 stars, optional (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
    intros t T H x H0. remember (@empty ty) as Gamma.
    assert (exists t', Gamma x = Some t').
      apply free_in_context with (t := t) (T := T).
      assumption. assumption.
    inversion H1. rewrite HeqGamma in H2. inversion H2.
Qed.

(*-- Check --*)
Check typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.

