Check list.

Definition natlist : Type := list nat.
Check natlist.

Theorem obvious_fact : 1 + 1 = 2.
Proof.
    reflexivity.
Qed.

Check obvious_fact.

Print obvious_fact.

Print eq_refl.

Check nat.

Check Set.

Check 1 + 2 = 2.

Check Prop.

Locate "=".

Check @eq.

Check @eq nat 42 43.

Check @eq (nat -> nat) (fun x => x + 1) (fun x => 1 + x).

Check and.

Check or.

Check not.

(*
Implication
*)

Theorem p_implies_p : forall P:Prop, P -> P.
Proof.
    intros. apply H.
Qed.

Check p_implies_p.

Theorem syllogism : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
    intros.
    apply H. apply H0.
Qed.

Print syllogism.

Theorem imp_trans : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
    intros.
    apply H0. apply H. apply H1.
Qed.

Print imp_trans.

(*
Conjunction
*)

Theorem and_fst : forall P Q, P /\ Q -> P.
Proof.
    intros.
    destruct H. apply H.
Qed.

Print and_fst.

Theorem and_snd : forall P Q, P /\ Q -> Q.
Proof.
    intros.
    destruct H. apply H0.
Qed.

Print and_snd.

Locate "/\".

Check and.

Print and.

Theorem and_comm : forall P Q, P /\ Q -> Q /\ P.
Proof.
    intros.
    destruct H.
    split.
    apply H0.
    apply H.
Qed.

Print and_comm.

Theorem and_to_imp : forall P Q R : Prop, (P /\ Q -> R) -> (P -> (Q -> R)).
Proof.
    intros.
    apply H.
    split.
    apply H0.
    apply H1.
Qed.

(*
Disjunction
*)

Theorem or_left : forall (P Q : Prop), P -> P \/ Q.
Proof.
    intros.
    left. apply H.
Qed.

Print or_left.

Locate "\/".

Print or.

Print or_introl.

Theorem or_right : forall (P Q : Prop), Q -> P \/ Q.
Proof.
    intros.
    right. apply H.
Qed.

Theorem or_comm : forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
    intros.
    destruct H.
    right. apply H.
    left. apply H.
Qed.

Print or_comm.

Theorem or_distr_and : forall P Q R, P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
    intros.
    destruct H.
    split.
    left. assumption.
    left. assumption.
    destruct H.
    split.
    right. assumption.
    right. assumption.
Qed.

Theorem explosion : forall (P : Prop), False -> P.
Proof.
    intros.
    contradiction.
Qed.

Theorem proof_false : forall (P : Prop), P -> P /\ False.
Proof.
    intros.
    split.
    assumption.
Abort.

Theorem p_imp_p_or_false : forall (P : Prop), P -> P \/ False.
Proof.
    intros.
    left. assumption.
Qed.

Print False.
Print True.

Theorem p_imp_p_and_true : forall (P : Prop), P -> P /\ True.
Proof.
    intros.
    split.
    assumption.
    exact I.
Qed.

Theorem p_imp_p_or_true : forall (P : Prop), P -> P \/ True.
Proof.
    intros.
    left.
    assumption.
Qed.

(*
Negation
*)

Locate "~".

Check not.

Print not.

Theorem notFalse : ~False -> True.
Proof.
    unfold not.
    intros.
    exact I.
Qed.

Theorem notTrue : ~True -> False.
Proof.
    unfold not.
    intros.
    apply H.
    exact I.
Qed.

Theorem contra_implies_anything : forall (P Q : Prop), P /\ ~P -> Q.
Proof.
    intros.
    destruct H.
    contradiction.
Qed.

Theorem deMorgan : forall (P Q : Prop), ~(P \/ Q) -> ~P /\ ~Q.
Proof.
    intros.
    split.
    unfold not.
    unfold not in H.
    intros.
    apply H.
    left. assumption.
    unfold not.
    unfold not in H.
    intros.
    apply H.
    right. assumption.
Qed.

Theorem deMorgan2 : forall P Q : Prop, ~(P /\ Q) -> ~P \/ ~Q.
Proof.
    intros.
    unfold not.
Abort.
