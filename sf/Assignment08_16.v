Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound, aequiv. intros.
  aexp_cases (induction a) Case; simpl;
    try reflexivity.
    destruct a1; 
    destruct a2; try (destruct n; try (rewrite IHa1; simpl; omega));
    try (rewrite IHa1; try rewrite IHa2; simpl; omega).

    try (destruct n0; simpl; omega);  
    try (rewrite IHa1; rewrite IHa2; simpl; omega).

    omega. 
    rewrite IHa1. rewrite IHa2. reflexivity. 
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

