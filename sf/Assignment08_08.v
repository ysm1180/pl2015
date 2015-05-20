Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros.
  split; intros.
  inversion H; subst. 
  apply E_IfFalse. simpl. rewrite H5. reflexivity.
  assumption.
  apply E_IfTrue. simpl. rewrite H5. reflexivity.
  assumption.
  inversion H; subst.
  apply E_IfFalse. simpl in H5. unfold negb in H5. 
  destruct (beval st b). inversion H5. reflexivity. assumption.
  subst. apply E_IfTrue. simpl in H5. unfold negb in H5.
  destruct (beval st b). reflexivity. inversion H5. assumption.
Qed.

(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).

