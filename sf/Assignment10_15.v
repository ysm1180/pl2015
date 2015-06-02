Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Hint Constructors bstep.

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  intros. induction b. 
  left. left. reflexivity.
  left. right. reflexivity.
  
  right. induction a; induction a0; eauto;
  try (destruct IHa0_1; destruct IHa0_2; inversion H; inversion H0; subst; eauto);
  try (destruct IHa1; destruct IHa2; inversion H; inversion H0; subst; eauto);
  try (solve by inversion); try (inversion H4; inversion H10; eauto).

  right. induction a; induction a0; eauto;
  try (destruct IHa0_1; destruct IHa0_2; inversion H; inversion H0; subst; eauto);
  try (destruct IHa1; destruct IHa2; inversion H; inversion H0; subst; eauto);
  try (solve by inversion); try (inversion H4; inversion H10; eauto).

  right. induction b; eauto; try (destruct IHb; destruct H; inversion H; induction H; eauto). 
  
  right. induction IHb1; induction IHb2. destruct H; destruct H0; rewrite H; rewrite H0; eauto.
  destruct H; try (rewrite H; eauto). inversion H0. eauto.
  destruct H0. inversion H. eauto. rewrite H0. inversion H. eauto.
  inversion H. inversion H0. eauto.
Qed.
(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

