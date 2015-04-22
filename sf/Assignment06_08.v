Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros.
  induction l1.
  simpl. reflexivity.
  simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  exists nil. simpl. exists l. reflexivity.
  destruct IHappears_in. destruct proof.
  exists (b :: witness). exists witness0.
  simpl. rewrite proof. reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeat_ex : forall (x : X) (l : list X), repeats l -> repeats (x :: l)
  | repeat_app : forall (x : X) (l : list X), appears_in x l -> repeats (x :: l).

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
  intros X l1. induction l1 as [|x l1'].
  intros.
  inversion H1.
  unfold excluded_middle. unfold not.
  intros. 
  destruct (H (appears_in x l1')). 
  apply repeat_app. apply H2.
  apply repeat_ex. destruct (appears_in_app_split X x l2 (H0 x (ai_here x l1'))) as [l3 [l4]].
  apply IHl1' with (l2 := l3 ++ l4).
  unfold excluded_middle. apply H. intros.
  assert (H3' := H3). apply ai_later with (b := x) in H3. 
  apply H0 in H3. rewrite -> proof in H3. apply appears_in_app in H3.
  destruct H3. apply app_appears_in. left. apply H3.
  apply app_appears_in. right. inversion H3.
  rewrite -> H5 in H3'. apply contradiction_implies_anything with (P:= appears_in x l1').
  split. apply H3'. unfold not. apply H2.
  apply H5.
  rewrite -> proof in H1. rewrite -> app_length in H1. simpl in H1. 
  rewrite <- plus_n_Sm in H1. apply Sn_le_Sm__n_le_m in H1. rewrite <- app_length in H1.
  apply H1.
Qed.

