(* Library Cpdt.InductiveTypes *)


Inductive unit : Set :=
 | tt.

Check unit.

Check tt.

Theorem unit_singleton : forall x : unit, x = tt.
Proof.
  intros.
  induction x. reflexivity.
Qed.

Check unit_ind.

Inductive Empty_set : Set := .

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
Proof.
  destruct 1.
Qed.

Check Empty_set_ind. 


Inductive bool : Set :=
| true
| false.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition negb' (b : bool) : bool :=
    if b then false else true.

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
Proof.
  intros. destruct b. simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
Proof.
  intros. destruct b. simpl. discriminate.
  discriminate.
Qed.

Check bool_ind.


(*
Simple Recursive Types
*)


Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Definition isZero (n : nat) : bool :=
    match n with
    | O => true
    | S _ => false
    end.

Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Theorem O_plus_n : forall n : nat, plus O n = n.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem n_plus_0 : forall n : nat, plus n O = n.
Proof.
  induction n. simpl. reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Check nat_ind.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
Proof.
  injection 1. trivial.
Qed.

Inductive nat_list : Set :=
 | NNil : nat_list
 | NCons : nat -> nat_list -> nat_list.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls1' => NCons n (napp ls1' ls2)
  end. 

Theorem nlength_napp : forall ls1 ls2 : nat_list, nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
Proof.
  intros. induction ls1. simpl. reflexivity.
  simpl. rewrite IHls1. reflexivity.
Qed.

Check nat_list_ind.

Inductive nat_btree : Set :=
 | NLeaf : nat_btree
 | NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
  | NLeaf => S O
  | NNode tr1 _ tr2 => plus (nsize tr1 ) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
  | NLeaf => NNode tr2 O NLeaf
  | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
Proof.
  intros.
  induction n1.
  simpl. reflexivity.
  simpl. rewrite IHn1. reflexivity.
Qed.

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1).
Proof.
  intros.
  induction tr1.
  simpl. reflexivity.
  simpl.
  rewrite IHtr1_1.
  apply plus_assoc.
Qed.

Check nat_btree_ind.

(*
Parameterized Types
*)

Inductive list (T : Set) : Set :=
 | Nil : list T
 | Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
  match ls with
  | Nil _ => O
  | Cons _ _ ls' => S (length T ls')
  end.  

Fixpoint app T (ls1 ls2 : list T) : (list T) := 
  match ls1 with
  | Nil _ => ls2
  | Cons _ x ls1' => Cons _ x (app T ls1' ls2)
  end.

Theorem length_app : forall T (ls1 ls2 : list T), length T (app T ls1 ls2) = plus (length T ls1) (length T ls2).
Proof.
  intros.
  induction ls1.
  simpl. reflexivity.
  simpl. rewrite IHls1. reflexivity.
Qed.
  

(*
Mutually Inductive Types
*)

Inductive even_list : Set :=
  | ENil : even_list
  | ECons : nat -> odd_list -> even_list

with odd_list : Set :=
  | OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
    match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
    end

with olength (ol : odd_list) : nat :=
    match ol with
    | OCons _ el => S (elength el)
    end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
    match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
    end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
    match ol with
    | OCons n el' => OCons n (eapp el' el)
    end.

Check even_list_ind.

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

Check even_list_mut.

Theorem elength_eapp : forall el1 el2 : even_list, elength (eapp el1 el2) = plus (elength el1) (elength el2).
Proof.
  intros.
  apply (even_list_mut
  (fun el1 : even_list => forall el2: even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2))
  (fun ol : odd_list => forall el : even_list,
  olength (oapp ol el) = plus (olength ol) (elength el))); auto.
  intros.
  simpl. specialize (H el0). rewrite H. reflexivity.
  intros. simpl. specialize (H el). rewrite H. reflexivity.
Qed.
