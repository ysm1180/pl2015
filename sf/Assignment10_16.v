Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Hint Constructors cstep.

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
  intros. induction c; eauto.
  right. induction a; eauto;
  try (destruct IHa1; destruct H; destruct IHa2; destruct H0;
  inversion H; subst; inversion H0; subst; eauto).

  right. destruct IHc1; destruct IHc2;
  try (try rewrite H; try rewrite H0; try (destruct H; destruct H);  try (destruct H0; destruct H0)); eauto.
  
  assert (HB := (bexp_strong_progress st b)). inversion HB. 
  inversion H; subst; eauto. inversion H as [witness].
  right. exists (IFB witness THEN c1 ELSE c2 FI). exists st. eauto.

  right. inversion IHc1; inversion IHc2; clear IHc1; clear IHc2; subst; eauto.
  inversion H0 as [wit [wit1]]. intros.
  exists (PAR SKIP WITH wit END). eauto.
  inversion H as [wit [wit1]]. intros.
  exists (PAR wit WITH SKIP END). eauto.
  inversion H. inversion H0. inversion H1. inversion H2. eauto. 
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.

