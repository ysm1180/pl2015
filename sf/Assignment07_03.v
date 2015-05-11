Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : BTrue || true
  | E_BFalse : BFalse || false
  | E_BEq : forall a1 a2 n1 n2, aevalR a1 n1 -> aevalR a2 n2 -> BEq a1 a2 || beq_nat n1 n2
  | E_BLe : forall a1 a2 n1 n2, aevalR a1 n1 -> aevalR a2 n2 -> BLe a1 a2 || ble_nat n1 n2
  | E_BNot : forall b p, b || p -> BNot b || negb p
  | E_BAnd : forall b1 b2 p1 p2, b1 || p1 -> b2 || p2 -> BAnd b1 b2 || andb p1 p2
  where "e '||' n" := (bevalR e n) : type_scope.


Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  intros.
  induction H; try (simpl; reflexivity).

  simpl. assert (aeval a1 = n1).
  induction H; try (simpl; try (rewrite IHaevalR1; rewrite IHaevalR2); reflexivity).
  assert (aeval a2 = n2).
  induction H0; try (simpl; try (rewrite IHaevalR1; rewrite IHaevalR2); reflexivity).
  rewrite H1. rewrite H2. reflexivity.
  
  simpl. assert (aeval a1 = n1).
  induction H; try (simpl; try (rewrite IHaevalR1; rewrite IHaevalR2); reflexivity).
  assert (aeval a2 = n2).
  induction H0; try (simpl; try (rewrite IHaevalR1; rewrite IHaevalR2); reflexivity).
  rewrite H1. rewrite H2. reflexivity.

  simpl. rewrite IHbevalR. reflexivity.

  simpl. rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.

  intros.
  induction H.
  induction b.
  simpl. apply E_BTrue.
  simpl. apply E_BFalse.
  simpl. apply E_BEq; rewrite aeval_iff_aevalR; reflexivity.
  simpl. apply E_BLe; rewrite aeval_iff_aevalR; reflexivity.
  simpl. apply E_BNot. apply IHb.
  simpl. apply E_BAnd. apply IHb1. apply IHb2.
Qed.

(** [] *)

