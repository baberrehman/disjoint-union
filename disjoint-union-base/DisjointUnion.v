(* Simply Typed Lambda with Disjoint Union Types *)

Set Implicit Arguments.
Require Import TLC.LibLN.
Implicit Types x : var.

(* ***********************************************************************)
(** * Description of the Language *)

(** Representation of pre-types *)

Inductive typ : Set :=
(*| typ_top   : typ*)
| typ_bot   : typ
| typ_int   : typ
| typ_arrow : typ -> typ -> typ
(*  | typ_and       : typ -> typ -> typ *)
| typ_or    : typ -> typ -> typ.

(** Subtyping relation *)

Inductive sub : typ -> typ -> Prop :=
(*| sub_top   : forall S, sub S typ_top*)
| sub_bot   : forall A, sub typ_bot A
| sub_int   : sub typ_int typ_int
| sub_arrow : forall S1 S2 T1 T2, sub T1 S1 -> sub S2 T2 ->
                                  sub (typ_arrow S1 S2) (typ_arrow T1 T2)
(*  | sub_and1  : forall t t1 t2, sub t t1 -> sub t t2 -> sub t (typ_and  t1 t2) 
  | sub_and2  : forall t t1 t2 , sub t1 t -> sub (typ_and t1 t2) t 
  | sub_and3  : forall t t1 t2, sub t2 t -> sub (typ_and t1 t2) t *)
  | sub_or1   : forall t t1 t2, sub t t2 -> sub t1 t2 -> sub (typ_or t t1) t2
  | sub_or2   : forall t t1 t2, sub t t1 -> sub t (typ_or t1 t2)
  | sub_or3   : forall t t1 t2, sub t t2 -> sub t (typ_or t1 t2).



(* Intuition with disjoint intersection types:

x ,, y    The types of x and y cannot have a common supertype. 
          If they do then then overlap and we can choose different values

Similarly lets consider disjoint union types. We have a construct
like:

match e with
   (x : A) -> e1
   (x : B) -> e2

Like with merges, overlapping types can also be problematic. 
Consider:

match 'c' with       -- bad because they have a common subtype (Char)
  (x : Int | Char)          -> true 
  (x : Char | String)       -> false

When we try to write the above expression we get ambiguity, because 
the two patterns overlap. Thus we could choose the first or second 
clause, leading to two different outputs. 

In this case the problem is that the two types have a 
*common subtype*. This is the dual problem than with merges.

Rules for 

typeof e is 
   (x : A) -> e1
   (x : B) -> e2

Typing:

T |- e : A | B     T, x : A |- e1 : C    T, x : B |- e2 : C   A * B
--------------------------------------------------------------------
T |- typeof e is {(x : A) -> e1; (x : B) -> e2} : C

T |- e <= A | B     T, x : A |- e1 => C    T, x : B |- e2 => C   A * B
----------------------------------------------------------------------
T |- typeof e is {(x : A) -> e1; (x : B) -> e2} => C

The bi-directional rule above is a little odd!

Alternatively:

T |- e <= A | B     T, x : A |- e1 <= C    T, x : B |- e2 <= C   A * B
----------------------------------------------------------------------
T |- typeof e is {(x : A) -> e1; (x : B) -> e2} <= C

Reduction:

                       v -->A v'
--------------------------------------------------------
typeof v is {(x : A) -> e1; (x : B) -> e2} --> [v'/x] e1

                       v -->B v'
--------------------------------------------------------
typeof v is {(x : A) -> e1; (x : B) -> e2} --> [v'/x] e2


v -->A v'
---------------
v -->(A | B) v'

v -->B v'
---------------
v -->(A | B) v'

*)

Inductive BotLike : typ -> Prop :=
| BL_bot : BotLike typ_bot
| BL_or  : forall A B, BotLike A -> BotLike B -> BotLike (typ_or A B).

Hint Constructors sub BotLike.

Require Import Program.Equality.

Lemma BL_soundness : forall A, BotLike A -> forall C, sub A C.
Proof.
  induction 1; intros; eauto.
Defined.

Lemma sub_or : forall A B C, sub (typ_or A B) C -> sub A C /\ sub B C.
  intros.
  dependent induction H; split; eauto; destruct (IHsub A B); eauto.
Defined.

Lemma BL_completeness : forall A, (forall C, sub A C) -> BotLike A.
Proof.
  induction A; intros; eauto.
  - specialize (H typ_bot).
    dependent destruction H.
  - specialize (H typ_bot).
    dependent destruction H.
  - constructor.
    + apply IHA1. intros.
      specialize (H C).
      apply sub_or in H. destruct H. eauto.
    + apply IHA2. intros.
      specialize (H C).
      apply sub_or in H. destruct H. eauto.
Defined.

(* Disjointness *)

Definition DisjSpec A B := forall C, sub C A /\ sub C B -> BotLike C.

Inductive DisjAxiom : typ -> typ -> Prop :=
| DA1 : forall A, DisjAxiom A typ_bot
| DA2 : forall A B, DisjAxiom typ_int (typ_arrow A B).

Inductive Disj : typ -> typ -> Prop :=
| Disj_or1 : forall A B C, Disj A C -> Disj B C -> Disj (typ_or A B) C
| Disj_or2 : forall A B C, Disj C A -> Disj C B -> Disj C (typ_or A B)
| Disj_axiom : forall A B, DisjAxiom A B -> Disj A B
| Disj_axiom_sym : forall A B, DisjAxiom A B -> Disj B A.

Hint Constructors Disj DisjAxiom.
                                                       
(* | Disj_axiom1  : forall A B, Disj typ_int (typ_arrow A B) *)

Lemma DisjAxiom_soundness : forall A B, DisjAxiom A B -> DisjSpec A B.
  intros. dependent destruction H; unfold DisjSpec; intros.
  - destruct H.
    dependent induction H0; eauto.
    apply sub_or in H. destruct H; eauto.
  - destruct H.
    induction C; try (dependent destruction H); eauto.
    + dependent destruction H0.
    + apply sub_or in H1. destruct H1; eauto.
Defined.

Lemma Disj_soundness : forall A B, Disj A B -> DisjSpec A B.
  induction 1; unfold DisjSpec; intros; eauto.
  - destruct H1.
    dependent induction H1; eauto.
    apply sub_or in H2. destruct H2; eauto.
  - destruct H1.
    dependent induction H2; eauto.
    apply sub_or in H1. destruct H1; eauto.
  - destruct H0. apply DisjAxiom_soundness in H.
    unfold DisjSpec in *. eauto.
  - destruct H0. apply DisjAxiom_soundness in H.
    unfold DisjSpec in *. eauto.
Defined.

Lemma sub_refl : forall A, sub A A.
  induction A; eauto.
Defined.

Hint Resolve sub_refl.

Lemma BL_disj : forall A, BotLike A -> forall B, Disj A B. 
  induction 1; intros; eauto.
Defined.

Lemma Disj_sym : forall A B, Disj A B -> Disj B A.
  induction 1; eauto.
Defined.
   
Lemma Disj_completeness : forall A B, DisjSpec A B -> Disj A B.
  induction A; unfold DisjSpec; intros; eauto.
  - induction B; eauto.
    + specialize (H typ_int).
      destruct H; eauto.
      constructor.
      apply BL_disj; eauto.
      apply BL_disj; eauto.
    + constructor.
      apply IHB1; intros; eauto.
      destruct H0.
      apply H; eauto.
      apply IHB2; intros; eauto.
      destruct H0.
      apply H; eauto.
  - induction B; eauto.
      apply BL_disj; eauto.
    + specialize (H (typ_arrow (typ_or A1 B1) typ_bot)).  (* IMPORTANT: common subtype, which is not bottom-like *)
      assert (BotLike (typ_arrow (typ_or A1 B1) typ_bot)).
      apply H; eauto. split; eauto.
      dependent destruction H0.
    + constructor.
      apply IHB1; intros; eauto.
      destruct H0.
      apply H; eauto.
      apply IHB2; intros; eauto.
      destruct H0.
      apply H; eauto.
  - constructor.
    apply IHA1. unfold DisjSpec. intros.
    destruct H0.
    apply H; eauto.
    apply IHA2. unfold DisjSpec. intros.
    destruct H0.
    apply H; eauto.
Defined.

Lemma invOrS1 : forall t t1 t2, sub (typ_or t1 t2) t -> sub t1 t /\ sub t2 t.
Proof.
  intros.
  dependent induction H; eauto. 
  assert (sub t1 t0 /\ sub t2 t0). auto.
  destruct H0.
  split.
  apply sub_or2; auto.
  apply sub_or2; auto.
  assert (sub t1 t3 /\ sub t2 t3). auto.
  destruct H0.
  split.
  apply sub_or3; auto.
  apply sub_or3; auto.
Defined.

Lemma sub_transitivity : forall B A C, sub A B -> sub B C -> sub A C.
Proof.
  induction B; intros;
  generalize H0 H; clear H0; clear H; generalize A; clear A.
  - intros; dependent induction H; eauto.
  - intros; dependent induction H0; eauto.
  - induction C; intros; inversion H0; eauto.
    induction A; try (inversion H); eauto.
  - intros. apply invOrS1 in H0. destruct H0.
    dependent induction H; eauto.
Defined.

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_bvar  : nat -> trm
  | trm_fvar  : var -> trm
  | trm_abs   : typ -> trm -> typ -> trm
  | trm_app   : trm -> trm -> trm
  | trm_nat   : nat -> trm
  | trm_typof : trm -> typ -> trm -> typ -> trm -> trm
  | trm_anno   : trm -> typ -> trm.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x     => trm_fvar x
  | trm_abs V e1 V1  => trm_abs V (open_ee_rec (S k) f e1) V1
  | trm_app e1 e2 => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | trm_nat i     => trm_nat i
  | trm_typof e t1 e1 t2 e2    =>  trm_typof (open_ee_rec k f e) t1 
                                    (open_ee_rec (S k) f e1) t2 (open_ee_rec (S k) f e2)
  | trm_anno e1 t1   => trm_anno (open_ee_rec k f e1) t1
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L V e1 V1,
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs V e1 V1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2)
  | term_nat : forall i,
      term (trm_nat i)
  | term_typeof : forall L e t1 e1 t2 e2,
       term e ->
       (forall x, x \notin L -> term (e1 open_ee_var x)) ->
       (forall x, x \notin L -> term (e2 open_ee_var x)) ->
       term (trm_typof e t1 e1 t2 e2)
  | term_anno : forall e t,
      term e ->
      term (trm_anno e t).

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


Inductive flag : Set :=
  | inf : flag
  | chk : flag.

(* Int -> Char * Bool -> String *)

(** Typing relation *)

Inductive typing : env -> trm -> flag -> typ -> Prop :=
  | typing_var : forall E x T,
      okt E ->
      binds x T E ->
      typing E (trm_fvar x) inf T
  | typing_abs : forall L E V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~: V) (e1 open_ee_var x) chk T1) ->
      typing E (trm_abs V e1 T1) inf (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 inf (typ_arrow T1 T2) ->
      typing E e2 chk T1 ->
      typing E (trm_app e1 e2) inf T2
  | typing_nat : forall E i,
      okt E ->
      typing E (trm_nat i) inf typ_int
  | typing_sub : forall S E e T,
      typing E e inf S ->
      sub S T ->
      typing E e chk T
  | typing_anno : forall E e1 T,
      typing E e1 chk T ->
      typing E (trm_anno e1 T) inf T
  | typing_typeof : forall L E e e1 e2 T1 T2 T3,
      typing E e chk (typ_or T1 T2) ->
      (forall x, x \notin L ->
      typing (E & x ~: T1) (e1 open_ee_var x) chk T3) ->
      (forall x, x \notin L ->
      typing (E & x ~: T2) (e2 open_ee_var x) chk T3 ) ->
      DisjSpec T1 T2 ->
      typing E (trm_typof e T1 e1 T2 e2) chk T3.

(** Values *)

Inductive value : trm -> Prop :=
  | value_abs  : forall V e1 V1,
                 term (trm_abs V e1 V1) ->
                 value (trm_abs V e1 V1)
  | value_nat : forall i,
                 value (trm_nat i).

Definition checkType (v : trm) : typ :=
  match v with
  | (trm_nat i) => typ_int
  | (trm_abs V e1 V1) => typ_arrow V V1
  | _                 => typ_bot
  end.


(* Type reduction *)

Inductive typ_red : trm -> typ -> trm -> Prop :=
| tred_nat : forall i,
    typ_red (trm_nat i) typ_int (trm_nat i)
| tred_arrow : forall e A1 A2 B1 B2,
    term (trm_abs B1 e B2) ->
    sub A1 B1 ->
    sub B2 A2 ->
    typ_red (trm_abs B1 e B2) (typ_arrow A1 A2) (trm_abs B1 e A2)
| tred_or1 : forall v v' A B,
    value v ->
    typ_red v A v' ->
    typ_red v (typ_or A B) v'
| tred_or2 : forall v v' A B,
    value v ->
    typ_red v B v' ->
    typ_red v (typ_or A B) v'.

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
  | red_abs : forall A e v v' B,
      term (trm_abs A e B) ->
      value v ->
      typ_red v A v' ->
      red (trm_app (trm_abs A e B) v) (open_ee e v')
  | red_anno : forall e T e',
      red e e' ->
      red (trm_anno e T) (trm_anno e' T)
  | red_annov : forall v A v',
      value v ->
      typ_red v A v' ->
      red (trm_anno v A) v'
  | red_typeoft : forall e e' e1 e2 T1 T2,
      term (trm_typof e T1 e1 T2 e2) ->
      red e e' ->
      red (trm_typof e T1 e1 T2 e2) (trm_typof e' T1 e1 T2 e2)
  | red_typeofv1 : forall v v' e1 e2 T1 T2,
      term (trm_typof v T1 e1 T2 e2) ->
      value v ->
      typ_red v T1 v' ->
      (*sub (checkType v) T1 ->*)
      red (trm_typof v T1 e1 T2 e2) (open_ee e1 v')
  | red_typeofv2 : forall v v' e1 e2 T1 T2,
      term (trm_typof v T1 e1 T2 e2) ->
      value v ->
      typ_red v T2 v' ->
      (*sub (checkType v) T2 ->*)
      red (trm_typof v T1 e1 T2 e2) (open_ee e2 v').

(** Our goal is to prove preservation and progress *)

(*Definition preservation_result dir : Prop := match dir with
| chk => ...
| inf => ...
end.*)


(*Definition preservation := forall E e e' dir T,
  typing E e dir T -> 
  red e e' -> 
  (dir = chk /\ typing E e' chk T) \/
  (dir = inf /\ exists T', typing E e' inf T' /\ sub T' T).*)

  Definition preservation := forall E e e' dir T,
  typing E e dir T -> 
  red e e' -> 
  typing E e' chk T.


Definition progress := forall e dir T,
  typing empty e dir T -> 
     value e 
  \/ exists e', red e e'.

(** Computing free term variables in terms *)

Fixpoint fv_ee (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i      => \{}
  | trm_fvar x      => \{x}
  | trm_abs V e1 V2 => (fv_ee e1)
  | trm_app e1 e2   => (fv_ee e1) \u (fv_ee e2)
  | trm_nat i       => \{}
  | trm_typof e1 T1 e2 T2 e3 => (fv_ee e1) \u (fv_ee e2) \u (fv_ee e3)
  | trm_anno e T    => (fv_ee e)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint subst_ee (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs V e1 V1  => trm_abs V (subst_ee z u e1) V1
  | trm_app e1 e2 => trm_app (subst_ee z u e1) (subst_ee z u e2)
  | trm_nat i     => trm_nat i
  | trm_typof e1 T1 e2 T2 e3   => trm_typof (subst_ee z u e1) T1 (subst_ee z u e2) T2 (subst_ee z u e3)
  | trm_anno e T   => trm_anno (subst_ee z u e) T 
  end.

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors term ok okt value red typ_red.

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
  unfolds open_ee. pick_fresh x.
   apply* (@open_ee_rec_term_core e1 0 (trm_fvar x)).
   unfolds open_ee. pick_fresh x.
   apply* (@open_ee_rec_term_core e2 0 (trm_fvar x)).
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
 - apply_fresh* term_abs as y.
   rewrite* subst_ee_open_ee_var.
 - apply_fresh* term_typeof as y.
   rewrite* subst_ee_open_ee_var.
   rewrite* subst_ee_open_ee_var.
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

Lemma typing_regular : forall E e dir T,
  typing E e dir T -> okt E /\ term e.
Proof.
  induction 1; try splits*.
 - pick_fresh y. specializes H0 y. destructs~ H0.
  apply okt_push_inv in H0. destruct H0. auto.
 - apply term_abs with (L:=L). intros.
  specializes H0 x. destructs~ H0.
 - apply term_typeof with (L:=L); intros.
  destruct IHtyping. auto.
  specializes H1 x. destructs~ H1.
  specializes H3 x. destructs~ H3.
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; autos*.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

Lemma typ_red_val : forall v v' A, 
                 value v -> typ_red v A v' -> value v'.
Proof.
  intros.
  induction H0; auto.
  apply value_abs.
  inverts H0; eauto.
Qed.


Lemma red_regular : forall t t',
  red t t' -> term t /\ term t'.
Proof.
  induction 1; split; autos* value_regular.
  inversions H. pick_fresh y. rewrite (@subst_ee_intro y).
  eapply (@typ_red_val v v' A) in H0. auto. auto. auto.
  apply value_regular.
  eapply (@typ_red_val v v' A) in H0; auto.
  eapply (@typ_red_val v v' A) in H0; auto.
  dependent destruction H.
  apply term_typeof with (L:=L); auto.
  destruct~ IHred.
  dependent destruction H.
  pick_fresh y.
  rewrite (@subst_ee_intro y); auto.
  eapply (@typ_red_val v v' T1) in H2; eauto.
  eapply (@typ_red_val v v' T1) in H2; eauto.
  dependent destruction H.
  pick_fresh y.
  rewrite (@subst_ee_intro y); auto.
  eapply (@typ_red_val v v' T2) in H2; eauto.
  eapply (@typ_red_val v v' T2) in H2; eauto.
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

Definition transitivity_on Q := forall S T,
  sub S Q -> sub Q T -> sub S T.

Lemma sub_transitivity1 : forall Q,
  transitivity_on Q.
Proof.
  induction Q; unfold transitivity_on; intros;
  generalize H0 H; clear H0; clear H; generalize S; clear S.
  - intros; dependent induction H; eauto.
  - intros; induction T; dependent induction H0; eauto.
  - induction T; intros; try (inversion H0); eauto.
    induction S; try (inversion H); eauto.
  - intros. apply invOrS1 in H0. destruct H0.
    dependent induction H; eauto.
Defined.

(* ********************************************************************** *)
(** Weakening (5) *)

Lemma typing_weakening : forall E F G e dir T,
   typing (E & G) e dir T -> 
   okt (E & F & G) ->
   typing (E & F & G) e dir T.
Proof. 
  introv Typ. gen F. inductions Typ; introv Ok.
  apply* typing_var. apply binds_weaken. apply H0.
  apply ok_from_okt. apply Ok.
  apply_fresh* typing_abs as x. forwards~ K: (H x).
   apply_ih_bind (H0 x); eauto.
  apply* typing_app.
  apply typing_nat. apply Ok.
  eapply typing_sub with (S:=S). apply IHTyp.
  reflexivity. apply Ok. apply H.
  apply typing_anno. apply IHTyp. reflexivity.
  apply Ok.
  apply_fresh* typing_typeof as x.
  forwards~ K: (H x).
  apply_ih_bind (H0 x); eauto.
  forwards~ K: (H1 x).
  apply_ih_bind (H2 x); eauto.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma typing_chk_sub: forall E e A B,
    typing E e chk A -> sub A B -> typing E e chk B.
Proof.
  intros.
  inductions H.
  apply (@typing_sub S). auto.
  apply (@sub_transitivity T S B); auto.
  apply typing_typeof with (L:=L); auto.
Qed.


(*Lemma typing_through_subst_ee1 : forall U E F x T e u dir,
  typing (E & x ~: U & F) e dir T ->
  typing E u chk U ->
  value u ->
  (dir = inf /\ exists T', typing (E & F) (subst_ee x u e) inf T' /\ sub T' T)
  \/
  (dir = chk /\ typing (E & F) (subst_ee x u e) chk T).
Proof.
introv TypT TypU. inductions TypT; introv; simpl.

case_var.
binds_get H0.
  lets M: (@typing_weakening E F empty u inf U).
  do 2 rewrite concat_empty_r in M.
  left. split*.
left.
split*.
exists T. split*.
binds_cases H0; apply* typing_var.
left. split*.
exists (typ_arrow V T1). split*.
apply_fresh* typing_abs as y.
rewrite* subst_ee_open_ee_var.
admit.
apply typing_regular in TypU. destruct TypU. auto.
left.
split*.
exists T2.
split*.
eapply typing_app; eauto.
admit. admit. admit.
right.
split*.
forwards * : IHTypT.
destruct H0.
destruct H0.
destruct H1.
destruct H1.
apply sub_transitivity with (A:=x0) (B:=S) (C:=T) in H2; eauto.
eapply typing_sub; eauto.
destruct H0.
inversion H0.
Admitted.*)


Lemma typing_through_subst_ee : forall U E F x T e u dir,
  typing (E & x ~: U & F) e dir T ->
  typing E u chk U ->
  typing (E & F) (subst_ee x u e) dir T.
Proof.
   introv TypT TypU. inductions TypT; introv; simpl.
  case_var.
    binds_get H0.
      lets M: (@typing_weakening E F empty u inf U).
      do 2 rewrite concat_empty_r in M.
      apply* M. admit.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0.
  apply typing_regular in TypU. destruct TypU. auto.
  apply* typing_app.
  apply* typing_nat.
  eapply typing_sub; eauto.
  apply* typing_anno.
  apply_fresh* typing_typeof as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0.
  apply typing_regular in TypU. destruct TypU. auto.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H2.
  apply typing_regular in TypU. destruct TypU. auto.
Admitted.


(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing (13) *)

Lemma typing_inv_abs : forall E S1 S2 e1 T,
  typing E (trm_abs S1 e1 S2) inf T -> 
  forall U1 U2, sub T (typ_arrow U1 U2) ->
     sub U1 S1
  /\ exists L, forall x, x \notin L ->
     typing (E & x ~: S1) (e1 open_ee_var x) chk S2 /\ sub S2 U2.
Proof.
  introv Typ. gen_eq e: (trm_abs S1 e1 S2). gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversions EQ.
  inversions* Sub.
  apply IHTyp. auto.
  eapply sub_transitivity. apply H. auto.
Qed.

Lemma inv_typing_sub : forall E e A, value e -> typing E e chk A -> exists B,
                                           typing E e inf B /\ sub B A.
Proof.
  intros.
  dependent induction H0; eauto.
  dependent destruction H.
Qed.

(*Lemma inv_or_disj : forall S A B, sub S (typ_or A B) -> DisjSpec A B ->
                     sub S A \/ sub S B.
Proof.
intros.
inductions H; auto.
specialize (IHsub1 A B).
specialize (IHsub2 A B).
destruct IHsub1. auto. auto.
destruct IHsub2. auto. auto.
left.
apply sub_or1; auto.
left.
apply sub_or1; auto.
admit.
destruct IHsub2. auto. auto.
admit.
right.
apply sub_or1; auto.
Admitted.*)

(*Lemma check_or_sub_disj : forall E e S A B, value e -> DisjSpec A B ->
           typing E e chk S -> sub S (typ_or A B) ->
           typing E e chk A \/ typing E e chk B.
Proof.
intros.
inductions H1.
eapply typing_sub in H1; eauto.*)

Lemma check_or_typ : forall E e A B,  
   value e ->
   DisjSpec A B ->
   typing E e chk (typ_or A B) ->
   typing E e chk A \/ typing E e chk B.
Proof.
  intros.
  inductions H1.
  inversions H1; try solve [dependent destruction H].
  dependent destruction H2.
  left.
  eapply typing_sub.
  eapply typing_abs. intros. eauto. auto.
  right.
  eapply typing_sub.
  eapply typing_abs. intros. eauto. auto.
  dependent destruction H2.
  left.
  eapply typing_sub.
  eapply typing_nat; eauto. auto.
  right.
  eapply typing_sub.
  eapply typing_nat; eauto. auto.
  dependent destruction H.
Qed.


(*Lemma value_red_eq : forall v A v', value v -> typ_red v A v' -> v = v'.
Proof.
intros.
inductions H0; eauto.
inverts* H0.
Admitted.

Lemma typ_red_red : forall v v' A, value v -> typ_red v A v' -> red v v'.
Proof.
intros.
inductions H0; eauto.
eapply value_red_eq in H; eauto.
Admitted.*)


Lemma typ_red_chk : forall E v v' A B,
                    value v ->
                    okt E ->
                    typing E v chk B ->
                    typ_red v A v' ->
                    typing E v' chk A.
Proof.
intros.
generalize B.
inductions H2; intros.
eapply typing_sub; eauto.
apply typing_nat; auto.
eapply typing_sub with (S:=(typ_arrow B1 A2)).
inversion H1.
inversion H5. subst.
eapply typing_abs.
intros.
eapply typing_chk_sub; eauto.
apply sub_arrow; auto.
eapply typing_chk_sub; eauto.
eapply typing_chk_sub; eauto.
Qed.


(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma preservation_result : preservation.
Proof.
  unfold preservation.
  introv Typ. gen e'. induction Typ; introv Red; 
   try solve [ inversion Red ].
  - inductions Red.
   + eapply typing_sub; eauto.
     eapply typing_app; eauto. admit. 
   + eapply typing_sub; eauto.
     eapply typing_app with (T1:=T1). auto. auto.
   + destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [L P2]].
       pick_fresh X. forwards~ K: (P2 X). destruct K.
       rewrite* (@subst_ee_intro X).
       assert (E = E&empty).
       rewrite concat_empty_r. reflexivity.
       rewrite H4.
       apply typing_through_subst_ee with (U:=A).
       rewrite concat_empty_r.
       apply typing_chk_sub with (B:=T2) in H2. auto. auto.
       eapply typ_red_chk with (v:=e2); eauto.
       apply typing_regular in Typ1. destruct Typ1. auto. auto.
       apply value_regular.
       apply typ_red_val with (v:=e2) (A:=A). auto. auto.
  - apply typing_chk_sub with (A:=S). auto. auto.
  - dependent destruction Red.
    eapply typing_sub; eauto.
    apply typing_anno. apply IHTyp. auto.
    eapply typ_red_chk with (v:=e1); eauto.
    apply typing_regular in Typ. destruct Typ. auto.
  - dependent destruction Red.
   + apply typing_typeof with (L:=L); eauto.
   + pick_fresh X.
     rewrite* (@subst_ee_intro X).
     assert (E = E&empty).
     rewrite concat_empty_r. reflexivity.
     rewrite H7.
     apply (@typing_through_subst_ee T1).
     rewrite concat_empty_r. auto.
     eapply typ_red_chk with (v:=e); eauto.
     apply typing_regular in Typ. destruct Typ. auto.
     apply value_regular.
     apply typ_red_val with (v:=e) (A:=T1). auto. auto.
     + pick_fresh X.
     rewrite* (@subst_ee_intro X).
     assert (E = E&empty).
     rewrite concat_empty_r. reflexivity.
     rewrite H7.
     apply (@typing_through_subst_ee T2).
     rewrite concat_empty_r. auto.
     eapply typ_red_chk with (v:=e); eauto.
     apply typing_regular in Typ. destruct Typ. auto.
     apply value_regular.
     apply typ_red_val with (v:=e) (A:=T2). auto. auto.
Admitted.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t inf (typ_arrow U1 U2) -> 
  exists V, exists e1, exists V1, t = trm_abs V e1 V1.
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


Lemma typ_red_sub : forall v v' A B, 
                     value v ->
                     value v' ->
                     typ_red v A v' -> 
                     sub A B -> 
                     exists v'', typ_red v B v''.
Proof.
intros.
induction* H2.
- dependent destruction H1.
- dependent destruction H1. 
  exists (trm_abs B1 e T2).
  apply tred_arrow; auto.
  eapply sub_transitivity; eauto.
  eapply sub_transitivity; eauto.
- dependent destruction H1; auto.
- destruct~ IHsub.
  exists x.
  apply* tred_or1.
- destruct~ IHsub.
  exists x.
  apply* tred_or2.
Qed.


Lemma typ_red_val_dir : forall E v A dir,
       value v ->
       typing E v dir A ->
       exists v', typ_red v A v'.
Proof.
intros.
inductions H0; eauto.
- dependent destruction H.
- exists (trm_abs V e1 T1).
  apply tred_arrow; auto.
  inversion H. auto.
- dependent destruction H.
-  destruct IHtyping; auto.
  eapply typ_red_sub in H2; eauto.
  eapply typ_red_val; eauto.
- dependent destruction H.
- dependent destruction H.
Qed.


(*Lemma typ_red_val_chk : forall E v A dir,
       value v ->
       typing E v dir A ->
       typ_red v A v.
Proof.
intros.
inductions H0; eauto.
- dependent destruction H.
- apply tred_arrow; eauto.
  apply value_regular. auto.
- dependent destruction H.
- admit.
- dependent destruction H.
- dependent destruction H.
Admitted.*)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
  induction Typ; intros EQ; subst.
  (* case: var *)
   - false* binds_empty_inv.
  (* case: abs *)
   - left*. apply value_abs. apply* typing_regular.
  (* case: app *)
   - right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    + destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 H]].
      destruct H as [V1].
      subst. apply typ_red_val_dir in Typ2; auto.
      destruct  Typ2.
      exists* (open_ee e3 x). apply* red_abs.
      apply* typing_regular.
      dependent destruction Typ1; auto.
    + exists* (trm_app e1' e2).
      apply red_app_1. apply* typing_regular. auto.
  - left. apply value_nat.
  - autos*.
  - right. destruct* IHTyp.
    + apply typ_red_val_dir in Typ; auto.
      destruct Typ.
      exists x. apply* red_annov.
    + destruct H as [e1']. exists (trm_anno e1' T).
      apply red_anno. auto.
  - destruct* IHTyp.
    + right*.
      apply check_or_typ in Typ; auto.
      destruct Typ.
      * apply typ_red_val_dir in H5; auto.
        destruct H5.
        exists (open_ee e1 x).
        apply red_typeofv1; eauto.
        apply typing_regular in Typ'.
        destruct~ Typ'.
      * apply typ_red_val_dir in H5; auto.
        destruct H5.
        exists (open_ee e2 x).
        apply red_typeofv2; eauto.
        apply typing_regular in Typ'.
        destruct~ Typ'.
    + right. destruct H4 as [e'].
      exists (trm_typof e' T1 e1 T2 e2).
      apply* red_typeoft.
      apply typing_regular in Typ'.
      destruct~ Typ'.
Qed.