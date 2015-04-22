Require Export Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
<<<<<<< HEAD
  | pal_nil : pal []
  | pal_one : forall (x : X), pal [x]
  | pal_x : forall (l : list X) (x : X), pal l -> pal (x :: l ++ [x]).

Lemma app_assoc: forall (X: Type) (l1 l2 l3: list X),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros.
  induction l1.
  simpl. reflexivity.
  simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma snoc_app: forall (X: Type) (l : list X) (x : X),
  snoc l x = l ++ [x].
Proof.
  intros.
  induction l.
  simpl. reflexivity.
  simpl. rewrite -> IHl. reflexivity.
Qed.

Lemma snoc_app_2: forall (X: Type) (l : list X) (x : X),
  l ++ snoc (rev l) x = (l ++ (rev l)) ++ [x].
Proof.
  intros.
  induction l.
  simpl. reflexivity.
  simpl. rewrite -> snoc_app. rewrite -> app_assoc. reflexivity.
Qed.
=======
(* FILL IN HERE *)
.
>>>>>>> upstream/master

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
<<<<<<< HEAD
  intros.
  induction l.
  simpl. apply pal_nil.
  simpl. rewrite -> snoc_app_2. apply pal_x. apply IHl.
Qed.

Theorem rev_list: forall (X: Type) (l: list X) (x : X),
  rev (l ++ [x]) = x :: rev l.
Proof.
  intros.
  induction l.
  simpl. reflexivity.
  simpl. rewrite -> IHl. simpl. reflexivity.
=======
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
<<<<<<< HEAD
  intros.
  induction H.
  simpl. reflexivity.
  simpl. reflexivity.
  simpl. rewrite -> snoc_app. rewrite -> rev_list. simpl. rewrite <- IHpal.
  reflexivity.
=======
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.

(** [] *)




