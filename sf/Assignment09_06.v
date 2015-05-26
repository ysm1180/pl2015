Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
  intros. apply hoare_seq with (Q := fun st : state => st X + st Y = m).
  eapply hoare_consequence_post. apply hoare_while.
  simpl. apply hoare_consequence_pre with (P' := fun st : state => st X - 1 + st Y + 1 = m).
  apply hoare_seq with (Q := fun st : state => st X + st Y + 1 = m).
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. simpl. intros. omega. 
  unfold assert_implies. intros. destruct H. apply negb_true in H0. apply beq_nat_false in H0. omega.
  unfold assert_implies. simpl. intros. destruct H. apply negb_false in H0. apply beq_nat_true in H0. omega. 
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
Qed.


(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
