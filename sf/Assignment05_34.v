Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
<<<<<<< HEAD
 unfold lt.
 intros.
 inversion H.
 split.
 apply n_le_m__Sn_le_Sm. apply le_plus_l.
 apply n_le_m__Sn_le_Sm. rewrite -> plus_comm. apply le_plus_l.
 split.
 apply n_le_m__Sn_le_Sm.
 assert (n1 <= S (n1 + n2)).
 apply le_S. apply le_plus_l.
 apply le_trans with (m:=n1) (n:=S(n1 + n2)) (o:=m0).
 apply H3. apply H0.
 apply n_le_m__Sn_le_Sm.
 assert (n2 <= S (n1 + n2)).
 apply le_S. rewrite -> plus_comm. apply le_plus_l.
 apply le_trans with (m:=n2) (n:=S(n1+n2)) (o:=m0).
 apply H3. apply H0.
=======
 unfold lt. 
 (* FILL IN HERE *) admit.
>>>>>>> upstream/master
Qed.

