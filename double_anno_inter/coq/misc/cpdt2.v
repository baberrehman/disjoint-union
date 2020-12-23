

(*
Inductive Predicates
*)

Print unit.

Print True.

Section Propositional.
Variables P Q R : Prop.

Theorem obvious : True.
Proof.
  apply I.
Qed.

Theorem obvious': True.
Proof.
  constructor.
Qed.

Print False.

Theorem False_imp : False -> 2 + 2 = 5.
Proof.
  intros.
  destruct H.
Qed.

Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
Proof.
  intros.
  elimtype False.
  inversion H.
Qed.

Print not.

Theorem aith_neq' : ~ (2 + 2 = 5).
Proof.
  intros.
  unfold not. intros.
  inversion H.
Qed.

Print and.

Theorem and_comm : P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H.
  split.
  assumption.
  assumption.
Qed.

Print or.

Theorem or_comm : P \/ Q -> Q \/ P.
Proof.
  intros.
  destruct H.
  right. assumption.
  left. assumption.
Qed.

Theorem or_comm' : P \/ Q -> Q \/ P.
Proof.
  intros.
  intuition.
Qed.

Print ex.

Theorem exists1 : exists x, x + 1 = 2.
Proof.
  exists 1. simpl. reflexivity.
Qed.

Theorem exist2 : forall (n m : nat), (exists x : nat , n + x = m) -> n <= m.
Proof.
  destruct 1.
  induction x.
  rewrite <- H.
  rewrite <- plus_n_O.
  auto.
  apply IHx.
Admitted.


(*
Predicates with Implicit Equality
*)

Inductive isZero : nat -> Prop :=
 | IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
Proof.
  apply IsZero.
Qed.

Print eq.

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
Proof.
  intros.
  destruct H.
  rewrite plus_n_O.
  reflexivity.
Qed.

Theorem isZero_contra : isZero 1 -> False.
Proof.
  destruct 1.
  Restart.
  inversion 1.
Qed.

Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
Proof.
  destruct 1.
  Undo.
  inversion 1.
Qed.

(*
Recursive Predicates
*)

Inductive even : nat -> Prop :=
 | Even0 : even 0
 | EvenSS : forall n, even n -> even (S (S n)).

Theorem even_0 : even 0.
Proof.
  apply Even0.
Qed.

Theorem even_4 : even 4.
Proof.
  apply EvenSS. apply EvenSS. apply Even0.
Qed.

Hint Constructors even : core.

Theorem even_1_contra : even 1 -> False.
Proof.
  inversion 1.
Qed.

Theorem even_3_contra : even 3 -> False.
Proof.
  inversion 1.
  inversion H1.
Qed.

Theorem  even_plus: forall n m, even n -> even m -> even (n + m).
Proof.
  induction n; auto.
  intros.
  simpl.
  inversion H.
  simpl.
  apply EvenSS.
  (* restarting proof from begining *)
  Restart.
  induction 1.
  auto.
  intro.
  simpl.
  apply EvenSS.
  apply IHeven.
  apply H0.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
Proof.
  induction 1.
Abort.

Lemma even_contra' : forall n', even n' -> forall n, n' = S (n + n) -> False.
Proof.
  induction 1; eauto.
  intros.
  inversion H.
  intros.
  destruct n; destruct n0; eauto.
  inversion H0.
  inversion H0.
  admit.
Admitted.
  
