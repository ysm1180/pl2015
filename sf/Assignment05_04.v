Require Export Assignment05_03.

(* problem #04: 10 points *)



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
<<<<<<< HEAD
  intros.
  destruct H as [HPQ HQP].
  destruct H0 as [HQR HRQ].
  split.
  intros. apply HQR. apply HPQ. apply H.
  intros. apply HQP. apply HRQ. apply H.
=======
  (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.


