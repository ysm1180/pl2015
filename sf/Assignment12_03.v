Require Export Assignment12_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof.
  induction t; intros; inversion TYPED; inversion TYPED'; subst; auto.
  rewrite H1 in H5. inversion H5. reflexivity.
  assert (TArrow T1 T = TArrow T0 T').
    eapply IHt1. apply H2. assumption.
  inversion H. auto.
  
  f_equal. eapply IHt. apply H4. auto.
  eapply IHt2. apply H5. auto.
  f_equal. eapply IHt1. apply H2. auto. eapply IHt2. apply H4. auto.
  assert (TProd T T2 = TProd T' T3).
    eapply IHt. apply H1. auto.
  inversion H. auto.
  assert (TProd T1 T = TProd T0 T').
    eapply IHt. apply H1. auto.
  inversion H. auto.
  assert (T1 = T0). eapply IHt1. apply H4. auto.
  rewrite H in H5. eapply IHt2. apply H5. auto.
  f_equal. eapply IHt. apply H3. auto.
  f_equal. eapply IHt. apply H3. auto.
  assert (TSum T1 T2 = TSum T3 T4). eapply IHt1. apply H6. auto.
  inversion H. subst. eapply IHt2. apply H7. auto.
  eapply IHt2. apply H4. auto.
  eapply IHt2. apply H7. auto.
  assert (TArrow (TArrow T1 T2) (TArrow T1 T2) = TArrow (TArrow T0 T3) (TArrow T0 T3)).
    eapply IHt. apply H1. auto.
  inversion H. subst. auto.
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.

