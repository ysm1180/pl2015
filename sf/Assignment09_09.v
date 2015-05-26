Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{ 1 * X! = m! }}
  Y ::= 1;;
    {{ Y * X! = m! }}
  WHILE X <> 0
  DO   {{ X <> 0 /\ Y * X! = m! }} ->>
       {{ (Y * X) * (X - 1)! = m! }}
     Y ::= Y * X;;
       {{ Y * (X - 1)! = m! }}
     X ::= X - 1
       {{ Y * X! = m! }}
  END
    {{ X = 0 /\ Y * X! = m! }} ->>
    {{ Y = m! }}
*)

Print fact.

Lemma fact_minus : forall n,
  n <> 0 -> n * fact (n - 1) = fact n.
Proof.
  intros. induction n.
  apply ex_falso_quodlibet. apply H. reflexivity.
  simpl. assert (n - 0 = n). omega.
  rewrite H0. reflexivity.
Qed.


Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros. apply hoare_consequence_pre with (P' := fun st : state => 1 * fact (st X) = fact m).
  apply hoare_seq with (Q := fun st : state => (st Y) * fact (st X) = fact m).
  eapply hoare_consequence_post. apply hoare_while.
  apply hoare_consequence_pre with (P' := fun st : state => (st Y) * (st X) * fact (st X - 1) = fact m).
  apply hoare_seq with (Q := fun st : state => (st Y) * fact (st X - 1) = fact m);
  try eapply hoare_consequence_pre; try apply hoare_asgn;
  try (unfold assn_sub, update, assert_implies; intros; simpl; assumption).
  unfold assert_implies. simpl. intros. destruct H. apply negb_true in H0. apply beq_nat_false in H0.
  assert (st X * fact (st X - 1) = fact (st X)).
    apply fact_minus. assumption.
  rewrite <- H1 in H. rewrite <- mult_assoc. assumption.
  unfold assert_implies. simpl. intros. destruct H. apply negb_false in H0. apply beq_nat_true in H0. rewrite H0 in H. simpl in H. omega.
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. simpl. intros. assumption.
  unfold assert_implies. intros. rewrite H. simpl. omega.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

