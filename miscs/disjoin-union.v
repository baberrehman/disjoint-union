(* Simply Typed Lambda Calculus with Subtyping, Union, and Intersection *)

Set Implicit Arguments.
Require Import TLC.LibLN.
Implicit Types x : var.

(* ***********************************************************************)
(** * Description of the Language *)

(** Representation of pre-types *)

Inductive typ : Set :=
  | typ_top   : typ
  | typ_int   : typ
  | typ_arrow : typ -> typ -> typ
  | typ_and       : typ -> typ -> typ
  | typ_or        : typ -> typ -> typ.

Inductive Ordinary : typ -> Prop :=
  | ATop : Ordinary typ_top
  | AInt : Ordinary typ_int
  | AFun : forall t1 t2, Ordinary (typ_arrow t1 t2).

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x     => trm_fvar x
  | trm_abs V e1  => trm_abs V (open_ee_rec (S k) f e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L V e1,
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs V e1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2).

(** Binding are mapping to term variables. 
 [x ~: T] is a typing assumption *)

Inductive bind : Set :=
  | bind_typ : typ -> bind.

(*Notation "X <: T" := (X ~ T)
  (at level 23, left associativity) : env_scope.*)

Notation "x ~: T" := (x ~ T)
  (at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. *)

Definition env := LibEnv.env typ.

(** A environment E is well-formed if it contains no duplicate bindings *)

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_typ : forall E x T,
      okt E-> x # E -> okt (E & x ~: T).

(** Subtyping relation *)

Inductive sub : typ -> typ -> Prop :=
  | sub_top   : forall S, sub S typ_top
  | sub_int   : sub typ_int typ_int
  | sub_arrow : forall S1 S2 T1 T2, sub T1 S1 -> sub S2 T2 ->
      sub (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_and1  : forall t t1 t2, sub t t1 -> sub t t2 -> sub t (typ_and  t1 t2) 
  | sub_and2  : forall t t1 t2 , sub t1 t -> sub (typ_and t1 t2) t 
  | sub_and3  : forall t t1 t2, sub t2 t -> sub (typ_and t1 t2) t 
  | sub_or1   : forall t t1 t2, sub t t2 -> sub t1 t2 -> sub (typ_or t t1) t2
  | sub_or2   : forall t t1 t2, sub t t1 -> sub t (typ_or t1 t2)
  | sub_or3   : forall t t1 t2, sub t t2 -> sub t (typ_or t1 t2).

(* Traditional definition of disjointness is:

Definition Disjoint A B := forall C, sub A C -> sub B C -> TopLike C.

But this does not work with union types because there is always 
a type that is not toplike and it is a supertype:

A | B

So, we can try to define a weaker notion, called weak disjointness:

*)

Definition WeakDisjointness A B := 
  forall C, sub A C -> sub B C -> 
  sub (typ_or A B) C /\ 
  not (sub A B) /\
  not (sub B A).

Lemma intint : not (WeakDisjointness typ_int typ_int).
unfold not; intros.
unfold WeakDisjointness in H.
destruct (H typ_int); try constructor.
destruct H1.
destruct H1.
constructor.
Defined.

Require Import Program.Equality.

Lemma intfint : WeakDisjointness typ_int (typ_arrow typ_int typ_int).
unfold WeakDisjointness.
intros.
split.
constructor; eauto.
split.
unfold not; intros.
dependent destruction H1.
unfold not; intros.
dependent destruction H1.
Defined.

Lemma inters : 
not (WeakDisjointness (typ_and typ_int (typ_arrow typ_int typ_int)) 
  (typ_and typ_int (typ_arrow typ_int (typ_arrow typ_int typ_int)))).
unfold not; intros.
unfold WeakDisjointness in H.
destruct (H (typ_and typ_int (typ_arrow typ_int typ_int)));
try constructor. apply sub_and2. constructor.
apply sub_and3. constructor. constructor. constructor.
constructor. constructor.
apply sub_and3. apply sub_arrow. constructor. admit.
destruct H1.
destruct H2.
apply sub_and2. apply sub_and1. constructor. admit.
Admitted.


Definition WeakDisjointness1 A B := 
  forall C, sub A C -> sub B C ->  
  not (sub A B) /\
  not (sub B A).


Lemma intint1 : not (WeakDisjointness1 typ_int typ_int).
unfold not; intros.
unfold WeakDisjointness1 in H.
destruct (H typ_int); try constructor.
destruct H1.
constructor.
Defined.

Require Import Program.Equality.

Lemma intfint1 : WeakDisjointness1 typ_int (typ_arrow typ_int typ_int).
unfold WeakDisjointness1.
intros.
split.
unfold not; intros.
dependent destruction H1.
unfold not; intros.
dependent destruction H1.
Defined.

Lemma inters1 : 
not (WeakDisjointness1 (typ_and typ_int (typ_arrow typ_int typ_int)) 
  (typ_and typ_int (typ_arrow typ_int (typ_arrow typ_int typ_int)))).
unfold not; intros.
unfold WeakDisjointness1 in H.
destruct (H (typ_and typ_int (typ_arrow typ_int typ_int)));
try constructor. apply sub_and2. constructor.
apply sub_and3. constructor. constructor. constructor.
constructor. constructor.
apply sub_and3. apply sub_arrow. constructor. admit.
destruct H1.
apply sub_and2. apply sub_and1. constructor. admit.
Admitted.

(* Disjointness: Specification *)

Inductive TopLike : typ -> Prop :=
  | TLTop  : TopLike typ_top 
  | TLAnd  : forall A B, TopLike A -> TopLike B -> TopLike (typ_and A B)
  | TLFun  : forall A B, TopLike B -> TopLike (typ_arrow A B).

(*
TLFunAnd states that output of two functions must be same and different input.
*)

Hint Resolve TLTop TLAnd TLFun.


Definition OrthoS (A B: typ) := forall C, sub A C -> sub B C -> TopLike C.

(* Next step: Define algorithmic weak disjointness and prove soundness and 
completness with respect to the specification *)


(* Disjointness: Implementation *)

(*Set Guard Checking.
Print Typing Flags.*)

Inductive Ortho : typ -> typ -> Prop :=
  | OTop : forall t1, Ortho t1 typ_top
  | OTop1 : forall t1, Ortho typ_top t1
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (typ_and t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (typ_and t2 t3)
  | OIntFun : forall t1 t2, Ortho typ_int (typ_arrow t1 t2)
  | OFunInt : forall t1 t2, Ortho (typ_arrow t1 t2) typ_int
  | OFun1   : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (typ_arrow t1 t2) (typ_arrow t3 t4)
  | OFun2  : forall t1 t2 t3 t4, Ortho t1 t3 -> Ortho (typ_arrow t1 t2) (typ_arrow t3 t4).

Hint Resolve OTop OTop1 OAnd1 OAnd2 OIntFun OFunInt OFun1 OFun2.

Hint Resolve 
  sub_top sub_int sub_arrow sub_and1 sub_and2 sub_and3 sub_or1 sub_or2 sub_or3.


Inductive wft : typ -> Prop :=
  | wft_top : wft typ_top
  | wft_int : wft typ_int
  | wft_fun : forall t1 t2, wft t1 -> wft t2 -> wft (typ_arrow t1 t2)
  | wft_and : forall t1 t2, wft t1 -> wft t2 -> OrthoS t1 t2-> wft (typ_and t1 t2)
  | wft_or : forall t1 t2, wft t1 -> wft t2 -> wft (typ_or t1 t2).




Lemma sub_reflexivity : forall E T,
  okt E -> 
  sub T T .
Proof.
  introv Ok.
  induction T; eauto. 
Qed.
 
(* ********************************************************************** *)
(** Narrowing and transitivity (3) *)

Section NarrowTrans.

(*Definition transitivity_on Q := forall S T,
  sub S Q -> sub Q T -> sub S T.

Hint Unfold transitivity_on.*)

Require Import Program.Equality.

Lemma invAndS1 : forall t t1 t2, sub t (typ_and t1 t2) -> sub t t1 /\ sub t t2.
Proof.
  intros. dependent induction H. split; auto.
  - destruct (IHsub _ _ eq_refl).
    split; constructor; auto.
  - destruct (IHsub _ _ eq_refl).
    split; apply sub_and3; auto.
  - destruct (IHsub1 _ _ eq_refl).
    destruct (IHsub2 _ _ eq_refl).
    split; constructor; auto.
Defined.

Lemma invOrS1 : forall t t1 t2, sub (typ_or t1 t2) t -> sub t1 t /\ sub t2 t.
Proof.
  intros. dependent induction H. split; eauto.
  - destruct (IHsub1 _ _ eq_refl);
    split; apply sub_and1; auto;
    destruct (IHsub2 _ _ eq_refl); auto.
  - split; auto.
  - destruct (IHsub _ _ eq_refl).
    split; constructor; auto.
  - destruct (IHsub _ _ eq_refl).
    split; apply sub_or3; auto.
Defined.

Lemma sub_transitivity : forall B A C, sub A B -> sub B C -> sub A C.
Proof.
  induction B; intros;
  generalize H0 H; clear H0; clear H; generalize A; clear A.
  - induction C; intro; intro; try (inversion H0); auto.
  - induction C; intro; intro; try (inversion H0); auto.
  - induction C; intro; intro; try (inversion H0); auto.
    induction A; intro; try (inversion H6); eauto.
  - intros; apply invAndS1 in H; destruct H;
    dependent induction H0; eauto.
  - intros; apply invOrS1 in H0; destruct H0;
    dependent induction H; eauto.
Qed.

Definition transitivity_on Q := forall S T,
  sub S Q -> sub Q T -> sub S T.

Lemma sub_transitivity1 : forall Q,
  transitivity_on Q.
Proof.
  induction Q; unfold transitivity_on; intros;
  generalize H0 H; clear H0; clear H; generalize S; clear S.
  - induction T; intro; intro; try (inversion H0); auto.
  - induction T; intro; intro; try (inversion H0); auto.
  - induction T; intro; intro; try (inversion H0); auto.
    induction S; intro; try (inversion H6); eauto.
  - intros. apply invAndS1 in H. destruct H.
    dependent induction H0; eauto.
  - intros. apply invOrS1 in H0. destruct H0.
    dependent induction H; eauto.
Defined.


Lemma ortho_completness : forall t1, WFTyp t1 -> forall t2, WFTyp t2 -> OrthoS t1 t2 -> Ortho t1 t2.
Proof.


(** Typing relation *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      okt E ->
      binds x T E ->
      typing E (trm_fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~: V) (e1 open_ee_var x) T1) ->
      typing E (trm_abs V e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (trm_app e1 e2) T2
  | typing_sub : forall S E e T,
      typing E e S ->
      sub S T ->
      typing E e T.

(** Values *)

Inductive value : trm -> Prop :=
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1).

(** One-step reduction *)

Inductive red : trm -> trm -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      term e2 ->
      red e1 e1' ->
      red (trm_app e1 e2) (trm_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (trm_app e1 e2) (trm_app e1 e2')
  | red_abs : forall V e1 v2,
      term (trm_abs V e1) ->
      value v2 ->
      red (trm_app (trm_abs V e1) v2) (open_ee e1 v2).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall E e e' T,
  typing E e T -> 
  red e e' -> 
  typing E e' T.

Definition progress := forall e T,
  typing empty e T -> 
     value e 
  \/ exists e', red e e'.

(** Computing free term variables in terms *)

Fixpoint fv_ee (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs V e1  => (fv_ee e1)
  | trm_app e1 e2 => (fv_ee e1) \u (fv_ee e2)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint subst_ee (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs V e1  => trm_abs V (subst_ee z u e1)
  | trm_app e1 e2 => trm_app (subst_ee z u e1) (subst_ee z u e2)
  end.

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors term ok okt value red.

Hint Resolve 
  sub_top sub_int sub_arrow sub_and1 sub_and2 sub_and3 sub_or1 sub_or2 sub_or3
  typing_var typing_app typing_sub.

(** Gathering free names already used in the proofs *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let D := gather_vars_with (fun x : trm => fv_ee x) in
  let F := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u D \u F).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)    

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

Ltac get_env :=
  match goal with
  | |- sub ?E _ _  => E
  | |- typing ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; autos*.

(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.


Lemma open_ee_rec_term : forall u e,
  term e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_ee. pick_fresh x. 
   apply* (@open_ee_rec_term_core e1 0 (trm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_ee e -> subst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, term u ->
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> term u ->
  (subst_ee x u e) open_ee_var y = subst_ee x u (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e, 
  x \notin fv_ee e -> term u ->
  open_ee e u = subst_ee x u (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_ee_term : forall e1 Z e2,
  term e1 -> term e2 -> term (subst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
Qed.

Hint Resolve subst_ee_term.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> ok E.
Proof.
  induction 1; auto. 
Qed.

Hint Extern 1 (ok _) => apply ok_from_okt.


(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Inversion lemma *)

Lemma okt_push_inv : forall E x T,
  okt (E & x ~: T) -> okt E /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. autos.
Qed.

(** Through strengthening *)

Lemma okt_strengthen : forall x T (E F:env),
  okt (E & x ~: T & F) ->
  okt (E & F).
Proof.
  introv O. induction F using env_ind.
  rewrite concat_empty_r in *. lets*: (okt_push_inv O).
  rewrite concat_assoc in *.
  apply okt_push_inv in O.
  destruct O. apply IHF in H.
  apply okt_typ; autos*.  
Qed.

(** Automation *)

Hint Immediate okt_strengthen.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ term e.
Proof.

  induction 1; try splits*.
   pick_fresh y. specializes H0 y. destructs~ H0.
  apply okt_push_inv in H0. destruct H0. auto. 
   apply_fresh* term_abs as y. 
      specializes H0 y. destructs~ H0.
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; autos*.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

Lemma red_regular : forall t t',
  red t t' -> term t /\ term t'.
Proof.
  induction 1; split; autos* value_regular.
  inversions H. pick_fresh y. rewrite* (@subst_ee_intro y).
Qed.

(** Automation *)

Hint Extern 1 (okt ?E) =>
  match goal with
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj32 (typing_regular H))
  | H: red ?e _ |- _ => apply (proj1 (red_regular H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular H))
  end.

(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  okt E -> 
  sub T T .
Proof.
  introv Ok.
  induction T; eauto. 
Qed.
 
(* ********************************************************************** *)
(** Narrowing and transitivity (3) *)

Section NarrowTrans.

(*Definition transitivity_on Q := forall S T,
  sub S Q -> sub Q T -> sub S T.

Hint Unfold transitivity_on.*)

Require Import Program.Equality.

Lemma invAndS1 : forall t t1 t2, sub t (typ_and t1 t2) -> sub t t1 /\ sub t t2.
Proof.
  intros. dependent induction H. split; auto.
  - destruct (IHsub _ _ eq_refl).
    split; constructor; auto.
  - destruct (IHsub _ _ eq_refl).
    split; apply sub_and3; auto.
  - destruct (IHsub1 _ _ eq_refl).
    destruct (IHsub2 _ _ eq_refl).
    split; constructor; auto.
Defined.

Lemma invOrS1 : forall t t1 t2, sub (typ_or t1 t2) t -> sub t1 t /\ sub t2 t.
Proof.
  intros. dependent induction H. split; eauto.
  - destruct (IHsub1 _ _ eq_refl);
    split; apply sub_and1; auto;
    destruct (IHsub2 _ _ eq_refl); auto.
  - split; auto.
  - destruct (IHsub _ _ eq_refl).
    split; constructor; auto.
  - destruct (IHsub _ _ eq_refl).
    split; apply sub_or3; auto.
Defined.

Lemma sub_transitivity : forall B A C, sub A B -> sub B C -> sub A C.
Proof.
  induction B; intros;
  generalize H0 H; clear H0; clear H; generalize A; clear A.
  - induction C; intro; intro; try (inversion H0); auto.
  - induction C; intro; intro; try (inversion H0); auto.
  - induction C; intro; intro; try (inversion H0); auto.
    induction A; intro; try (inversion H6); eauto.
  - intros; apply invAndS1 in H; destruct H;
    dependent induction H0; eauto.

  - intros; apply invOrS1 in H0; destruct H0;
    dependent induction H; eauto.
Qed.

Definition transitivity_on Q := forall S T,
  sub S Q -> sub Q T -> sub S T.

Lemma sub_transitivity1 : forall Q,
  transitivity_on Q.
Proof.
  induction Q; unfold transitivity_on; intros;
  generalize H0 H; clear H0; clear H; generalize S; clear S.
  - induction T; intro; intro; try (inversion H0); auto.
  - induction T; intro; intro; try (inversion H0); auto.
  - induction T; intro; intro; try (inversion H0); auto.
    induction S; intro; try (inversion H6); eauto.
  - intros. apply invAndS1 in H. destruct H.
    dependent induction H0; eauto.
  - intros. apply invOrS1 in H0. destruct H0.
    dependent induction H; eauto.
Defined.


(* ********************************************************************** *)
(** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T -> 
   okt (E & F & G) ->
   typing (E & F & G) e T.
Proof. 
  introv Typ. gen F. inductions Typ; introv Ok.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as x. forwards~ K: (H x).
   apply_ih_bind (H0 x); eauto.
  apply* typing_app.
  apply* typing_sub. 
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (E & x ~: U & F) e T ->
  typing E u U ->
  typing (E & F) (subst_ee x u e) T.
Proof.
   introv TypT TypU. inductions TypT; introv; simpl.
  case_var.
    binds_get H0. apply_empty* typing_weakening.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0.
  apply typing_regular in TypU. destruct TypU. auto.
  apply* typing_app.
  apply* typing_sub.
Qed.

(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (trm_abs S1 e1) T -> 
  forall U1 U2, sub T (typ_arrow U1 U2) ->
     sub U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (E & x ~: S1) (e1 open_ee_var x) S2 /\ sub S2 U2.
Proof.
  introv Typ. gen_eq e: (trm_abs S1 e1). gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversions EQ.
  inversions* Sub.
  apply IHTyp. auto.
  eapply sub_transitivity. apply H. auto.
Qed.

(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma preservation_result : preservation.
Proof.
  unfold preservation.
  introv Typ. gen e'. induction Typ; introv Red; 
   try solve [ inversion Red ].
  (* case: app *) 
  inversions Red; try solve [ apply* typing_app ].
  destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* sub_reflexivity.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_ee_intro X).
     apply_empty (@typing_through_subst_ee V).
       apply* (@typing_sub S2).
       autos*.
    apply* value_regular.
  (* case sub *)
  apply* typing_sub.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_arrow U1 U2) -> 
  exists V, exists e1, t = trm_abs V e1.
Proof.
  introv Val Typ. 
  gen_eq T: (typ_arrow U1 U2). intro st.
   assert (sub T (typ_arrow U1 U2)). 
{ rewrite st. 
    apply sub_reflexivity with (E:=empty); auto. }
  clear st. gen_eq E: (@empty typ).  gen U1 U2.
  induction Typ; introv EQT EQE; 
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. assert (sub S (typ_arrow U1 U2)). { 
    eapply sub_transitivity. apply H. apply EQT. }
   eapply IHTyp. apply Val. apply H0. reflexivity.
Qed.

(* ********************************************************************** *)
(** Progress Result (16) *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
  induction Typ; intros EQ; subst.
  (* case: var *)
  false* binds_empty_inv.
  (* case: abs *)
  left*. apply value_abs. apply* typing_regular.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        subst. exists* (open_ee e3 e2).  apply red_abs.
        apply* typing_regular. auto.
        exists (trm_app e1' e2). apply red_app_1. apply* typing_regular.
        auto.
  (* case: sub *)
  autos*.
Qed.

