Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  {{ X = n /\ Y = m }} ->> {{ X + Y = n + m }}
  WHILE X <> 0 DO
    {{ X <> 0 /\ X + Y = n + m }} ->> {{ X - 1 + Y + 1 = n + m }}
     Y ::= Y + 1;;
     {{ X - 1 + Y = n + m }}
     X ::= X - 1
     {{ X + Y = n + m }}
  END
    {{ X = 0 /\ X + Y = n + m }} ->> {{ Y = n + m }}

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
  intros. apply hoare_consequence_pre with (P' := fun st : state => st X + st Y = n + m).
  eapply hoare_consequence_post. apply hoare_while; simpl.
  apply hoare_consequence_pre with (P' := fun st : state => st X - 1 + st Y + 1 = n + m).
  apply hoare_seq with (Q := fun st : state => st X - 1 + st Y = n + m);
  try eapply hoare_consequence_pre; try apply hoare_asgn;
  try (unfold assn_sub, update, assert_implies; intros; simpl; omega).
  unfold assert_implies. intros. destruct H. apply negb_true in H0. apply beq_nat_false in H0. omega.
  unfold assert_implies. simpl. intros. destruct H. apply negb_false in H0. apply beq_nat_true in H0. omega.
  unfold assert_implies. intros. omega.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

