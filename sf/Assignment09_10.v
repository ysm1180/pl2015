Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{ c = 0 + 0 + c }}
  X ::= 0;;
    {{ c = X + 0 + c }}
  Y ::= 0;;
    {{ c = X + Y + c }}
  Z ::= c;;
    {{ Z = X + Y + c }}
  WHILE X <> a DO
      {{ X <> a /\ Z = X + Y + c }} ->>
      {{ Z + 1 = X + 1 + Y + c}}
    X ::= X + 1;;
      {{ Z + 1 = X + Y + c }}
    Z ::= Z + 1
      {{ Z = X + Y + c }}
  END;;
    {{ X = a /\ Z = X + Y + c }} ->>
    {{ Z = a + Y + c }}
  WHILE Y <> b DO
      {{ Y <> b /\ Z = a + Y + c }} ->>
      {{ Z + 1 = a + Y + 1 + c }}
    Y ::= Y + 1;;
      {{ Z + 1 = a + Y + c }}
    Z ::= Z + 1
      {{ Z = a + Y + c }}
  END
    {{ Y = b /\ Z = a + Y + c }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros. apply hoare_consequence_pre with (P' := fun st : state => c = 0 + 0 + c).
  apply hoare_seq with (Q := fun st : state => c = st X + 0 + c). 
  apply hoare_seq with (Q := fun st : state => c = st X + st Y + c).
  apply hoare_seq with (Q := fun st : state => st Z = st X + st Y + c). 
  apply hoare_seq with (Q := fun st : state => st Z = a + st Y + c).
  eapply hoare_consequence_post. apply hoare_while.
  apply hoare_consequence_pre with (P' := fun st : state => st Z + 1 = a + st Y + 1 + c).
  apply hoare_seq with (Q := fun st : state => st Z + 1 = a + st Y + c).
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
  unfold assert_implies. simpl. intros. destruct H. apply negb_true in H0. apply beq_nat_false in H0. omega.
  unfold assert_implies. simpl. intros. destruct H. apply negb_false in H0. apply beq_nat_true in H0. omega. 
  eapply hoare_consequence_post. apply hoare_while.
  apply hoare_consequence_pre with (P' := fun st : state => st Z + 1 = st X + 1 + st Y + c).
  apply hoare_seq with (Q := fun st : state => st Z + 1 = st X + st Y + c).
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
  unfold assert_implies. simpl. intros. destruct H. apply negb_true in H0. apply beq_nat_false in H0. omega.
  unfold assert_implies. simpl. intros. destruct H. apply negb_false in H0. apply beq_nat_true in H0. omega.  
  eapply hoare_consequence_pre. apply hoare_asgn. 
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
  eapply hoare_consequence_pre. apply hoare_asgn. 
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
  eapply hoare_consequence_pre. apply hoare_asgn. 
  unfold assn_sub, update, assert_implies. simpl. intros. omega.
  unfold assert_implies. intros. omega.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

