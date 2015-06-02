Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Hint Constructors aval.
Hint Constructors astep.

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
  intros. induction a; eauto; destruct IHa1 as [[n0 H1] | [a' H2]]; destruct IHa2 as [[n1 H3] | [a'' H4]]; right; eexists;
  try (try (rewrite H1; rewrite H3; auto);
  try (rewrite H1; inversion H4; auto);
  try (rewrite H3; inversion H2; auto);
  try (inversion H2; inversion H4; auto)).
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.

