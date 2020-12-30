(*
Infinite Data and Proofs

Library Cpdt.Coinductive
*)

Section stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
  End stream.

CoFixpoint zeroes : stream nat := Cons nat 0 zeroes.

CoFixpoint trues_falses : stream bool := Cons bool true falses_trues
with falses_trues : stream bool := Cons bool false trues_falses.

Fixpoint approx A (s : stream A) (n : nat) : list A :=
    match n with
    | O => nil
    | S n' =>
      match s with
        | Cons _ h t => h :: approx A t n'
      end
    end.

Eval simpl in approx nat zeroes 10.

Eval simpl in approx bool trues_falses 10.

Section map.
  Variables A B : Type.
  Variable f : A -> B.
  
  CoFixpoint map (s : stream A) : stream B :=
    match s with
    | Cons _ h t => Cons B (f h) (map t)
    end.
End map.

Section interleave.
  Variable A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
    | Cons _ h1 t1, Cons _ h2 t2 => Cons A h1 ( Cons A h2 (interleave t1 t2) )
    end.
End interleave.

Section map'.
  Variables A B : Type.
  Variable f : A -> B.
  
(*  CoFixpoint map' (s : stream A) : stream B :=
    match s with
    | Cons _ h t => interleave B (Cons B (f h) (map' t)) (Cons B (f h) (map' t))
    end.

*)
End map'.

Definition tl A (s : stream A) : stream A :=
    match s with
    | Cons _ _ s' => s'
    end.

(*CoFixpoint bad : stream nat := bad.*)

(*
Infinite Proofs
*)

CoFixpoint ones : stream nat := Cons nat 1 ones.

Definition ones' := map nat nat S zeroes.

Section stream_eq.
  Variable A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
    stream_eq t1 t2 ->
    stream_eq (Cons A h t1) (Cons A h t2).

End stream_eq.

Theorem ones_eq : stream_eq nat ones ones'.
cofix ones_eq.
assumption.
Undo.
simpl.
Abort.

Definition frob A (s : stream A) : stream A :=
    match s with
    | Cons _ h t => Cons A h t
    end.

Theorem  frob_eq : forall A (s : stream A), s = frob A s.
Proof.
    destruct s. reflexivity.
Qed.

Theorem ones_eq : stream_eq nat ones ones'.
Proof.
    cofix ones_eq.
    rewrite (frob_eq nat ones).
    rewrite (frob_eq nat ones').
    simpl.
    constructor.
    assumption.
Guarded.
Qed.

Theorem ones_eq' : stream_eq nat ones ones'.
Proof.
    cofix one_eq'; auto.
Abort.

Definition hd A (s : stream A) : A :=
    match s with
    | Cons _ x _ => x
    end.

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.

Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd A s1 = hd A s2.
Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl A s1) (tl A s2).


Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq A s1 s2.
cofix stream_eq_coind; destruct s1; destruct s2; intro.
Admitted.
End stream_eq_coind.

Require Import Arith.

(*
Simple Modeling of Non-Terminating Programs
*)

Definition var := nat.

Definition vars := var -> nat.
Definition set (vs : vars) (v : var) (n : nat) : vars :=
    fun v' => if beq_nat v v' then n else vs v'.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs : vars) (e : exp) : nat :=
    match e with
    | Const n => n
    | Var v => vs v
    | Plus e1 e2 => evalExp vs e1 + evalExp vs e2
    end.

Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.

CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e, evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2, evalCmd vs1 c1 vs2
  -> evalCmd vs2 c2 vs3
  -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c, evalExp vs e = 0
  -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c, evalExp vs1 e <> 0
  -> evalCmd vs1 c vs2
  -> evalCmd vs2 (While e c) vs3
  -> evalCmd vs1 (While e c) vs3.

  Section evalCmd_coind.
  Variable R : vars -> cmd -> vars -> Prop.

  Hypothesis AssignCase : forall vs1 vs2 v e, R vs1 (Assign v e) vs2
    -> vs2 = set vs1 v (evalExp vs1 e).

  Hypothesis SeqCase : forall vs1 vs3 c1 c2, R vs1 (Seq c1 c2) vs3
    -> exists vs2, R vs1 c1 vs2 /\ R vs2 c2 vs3.

  Hypothesis WhileCase : forall vs1 vs3 e c, R vs1 (While e c) vs3
    -> (evalExp vs1 e = 0 /\ vs3 = vs1)
    \/ exists vs2, evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3.

End evalCmd_coind.