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

CoFixpoint bad : stream nat := tl nat (Cons nat 0 bad).
