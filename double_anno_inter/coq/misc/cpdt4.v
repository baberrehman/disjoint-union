(*
Library Cpdt.Subset

Subset Types and Variations
*)

Print Nat.pred.

Lemma zgtz : 0 > 0 -> False.
Proof.
    intros.
    inversion H.
Qed.

Definition pred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
  end.

Theorem two_gt0 : 2 > 0.
Proof.
    auto.
Qed.

Eval compute in pred_strong1 2 two_gt0.

Definition pred_strong1' (n : nat) : n > 0 -> nat :=
    match n return n > 0 -> nat with
    | O => fun pf : 0 > 0 => match zgtz pf with end
    | S n' => fun _ => n'
    end.

Print sig.

(*
Decidable Proposition Types
*)

Print sumbool.

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Definition eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
  refine (fix f (n m : nat) : {n = m} + {n <> m} :=
    match n, m with
    | 0, 0 => Yes
    | S n' , S m' => Reduce (f n' m')
    | _, _ => No
    end); congruence.
Defined. 

Eval compute in eq_nat_dec 2 2.

Eval compute in eq_nat_dec 2 3.

Definition eq_nat_dec' (n m : nat) : {n = m} + {n <> m}.
  decide equality.
Defined.

Notation "x || y" := (if x then Yes else Reduce y).

Section In_dec.
  Variable A : Set.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  (*Definition In_dec : forall (x : A) (ls : list A), { In x ls} + {~ In x ls}.*)

End In_dec.

(*
Partial Subset Types
*)

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe A P
| Found : forall x : A, P x -> maybe A P.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

(*
Monadic Notations
*)

Notation "x <- e1 ; e2" := (match e1 with
                            | Unknown _ _ => ??
                            | Found _ _ _ _ => e2
                            end)
(right associativity, at level 60).

(*
A Type-Checking Example
*)

Inductive exp : Set :=
| Nat : nat -> exp
| Plus : exp -> exp -> exp
| Bool : bool -> exp
| And : exp -> exp -> exp.

Inductive type : Set := TNat | TBool.

Inductive hasType : exp -> type -> Prop :=
| HtNat : forall n,
          hasType (Nat n) TNat
| HtPlus : forall e1 e2,
          hasType e1 TNat ->
          hasType e2 TNat ->
          hasType (Plus e1 e2) TNat
| HtBool : forall b,
          hasType (Bool b) TBool
| HtAnd : forall e1 e2,
          hasType e1 TBool ->
          hasType e2 TBool ->
          hasType (And e1 e2) TBool.

Definition eq_type_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60).