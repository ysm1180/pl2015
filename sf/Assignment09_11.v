Require Export Assignment09_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp. split.
  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub, update, assert_implies. intros. simpl. omega.
  unfold assert_implies. simpl. intros. unfold hoare_triple in H.
  remember (update st X (st Y + 1)) as st'.
  assert ((X ::= APlus (AId Y) (ANum 1)) / st || st').
    subst. constructor. reflexivity.
  apply H in H1. rewrite Heqst' in H1. unfold update in H1. simpl in H1. omega.
  assumption.
Qed.

(*-- Check --*)
Check is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).

