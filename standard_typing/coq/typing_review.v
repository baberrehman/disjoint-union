(*
This file is created on June 17, 2021

syntax_unit.v is the syntax file for this semantics

June 17, 2021:
---------------
-> Intersection introduction rule

e : A     e : B
---------------
   e : A & B

*)

Require Import TLC.LibLN.
Require Import syntax_unit.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.

(** definitions *)

(* defns value *)
Inductive value : exp -> Prop :=    (* defn value *)
 | val_int : forall i5,
     value (e_lit i5)
 | val_abs : forall e,
     lc_exp (e_abs e) ->
     value (e_abs e)
 | val_null :
     value e_null.

(* defns FindType *)
Inductive findtype : exp -> typ -> Prop :=    (* defn findtype *)
 | findtype_int : forall i5,
     findtype (e_lit i5) t_int
 | findtype_arrow : forall (e:exp),
     lc_exp (e_abs e) ->
     findtype  (e_abs e) (t_arrow t_top t_bot)
 | findtype_null :
     findtype e_null t_unit.

#[export]
Hint Constructors value findtype : core.

(* defns Typing *)
Inductive typing : env -> exp -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:env) i5,
      okt  G  ->
     typing G (e_lit i5) t_int
 | typ_null : forall G,
      okt G ->
      typing G e_null t_unit
 | typ_var : forall (G:env) (x:var) (A:typ),
      okt  G  ->
      binds  x A G  ->
     typing G (e_var_f x) A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     typing G e1 (t_arrow A B) ->
     typing G e2 A ->
     typing G (e_app e1 e2) B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing G e B ->
     B <: A ->
     typing G e A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      ( forall x , x \notin  L  -> typing  (G & x ~: A )   ( open_exp_wrt_exp e (e_var_f x) ) B )  ->
     typing G (e_abs e) (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing G e (t_union A B) ->
     ( forall x , x \notin  L  -> typing  (G & x ~: A )   ( open_exp_wrt_exp e1 (e_var_f x) ) C ) ->
     ( forall x , x \notin  L  -> typing  (G & x ~: B )   ( open_exp_wrt_exp e2 (e_var_f x) ) C ) ->
     A *s B ->
     typing G (e_typeof e A e1 B e2) C
 | typ_inter : forall G e A B,
     typing G e A ->
     typing G e B ->
     typing G e (t_and A B).

(* defns Reduction *)
Reserved Notation "e --> e'" (at level 80).
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     e1 --> e1' ->
     (e_app e1 e2) --> (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     e --> e' ->
     (e_app v e) --> (e_app v e')
 | step_beta : forall (e:exp) (v:exp),
     lc_exp (e_abs e) ->
     value v ->
     e_app  (e_abs e) v --> (open_exp_wrt_exp e v)
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     e --> e' ->
     (e_typeof e A e1 B e2) --> (e_typeof e' A e1 B e2)
 | step_typeofl : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     C <: A ->
     (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp e1 v)
 | step_typeofr : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
    lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     C <: B ->
     (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp  e2 v )
where "e --> e'" := (step e e') : env_scope.

#[export]
Hint Constructors typing step : core.


(** Gathering free names already used in the proofs *)


Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let D := gather_vars_with (fun x : exp => fv_exp x) in
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
  | |- subtyping ?E _ _  => E
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
open_exp_wrt_exp_rec j v e = open_exp_wrt_exp_rec i u (open_exp_wrt_exp_rec j v e) ->
  e = open_exp_wrt_exp_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_ee_rec_term : forall u e,
  lc_exp e -> forall k, e = open_exp_wrt_exp_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e 0 (e_var_f x)).
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e1 0 (e_var_f x)).
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e2 0 (e_var_f x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_exp e -> subst_exp u x e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, lc_exp u ->
subst_exp u x (open_exp_wrt_exp t1 t2) =
open_exp_wrt_exp (subst_exp u x t1) (subst_exp u x t2).
Proof.
  intros. unfold open_exp_wrt_exp. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> lc_exp u ->
  (subst_exp u x e) open_ee_var y = subst_exp u x (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_exp e -> lc_exp u ->
  open_exp_wrt_exp e u = subst_exp u x (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_ee_term : forall e1 Z e2,
lc_exp e1 -> lc_exp e2 -> lc_exp (subst_exp e2 Z e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
 - apply_fresh* lc_e_abs as y.
   rewrite* subst_ee_open_ee_var.
 - apply_fresh* lc_e_typeof as y.
   rewrite* subst_ee_open_ee_var.
   rewrite* subst_ee_open_ee_var.
Qed.

#[export]
Hint Resolve subst_ee_term : core.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> ok E.
Proof.
  induction 1; auto.
Qed.

#[export]
Hint Extern 1 (ok _) => apply ok_from_okt : core.


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
  rewrite concat_empty_r in *. apply okt_push_inv in O. destruct~ O.
  rewrite concat_assoc in *.
  apply okt_push_inv in O.
  destruct O. apply IHF in H.
  apply okt_typ; autos*.
Qed.

(** Automation *)

#[export]
Hint Immediate okt_strengthen : core.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ lc_exp e.
Proof.
  induction 1; try splits*.
 - pick_fresh y. specializes H0 y. destructs~ H0.
  apply okt_push_inv in H0. destruct H0. auto.
 - apply lc_e_abs with (L:=L). intros.
  specializes H0 x. destructs~ H0.
 - apply lc_e_typeof with (L:=L); intros. destruct~ IHtyping.
   specialize (H1 x H5). destruct~ H1.
   specialize (H3 x H5). destruct~ H3.
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> lc_exp t.
Proof.
  induction 1; autos*.
Qed.

#[export]
Hint Immediate value_regular : core.

(* ********************************************************************** *)
(** Weakening (5) *)


Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T ->
   okt (E & F & G) ->
   typing (E & F & G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
  - apply* typ_null.
  - apply* typ_var. apply* binds_weaken.
  - apply* typ_app.
  - apply* typ_sub.
  - apply_fresh* typ_abs as x.
    forwards~: (H x).
    apply_ih_bind (H0 x); eauto.
  - apply_fresh* typ_typeof as x.
    forwards*: H x. apply_ih_bind (H0 x); eauto.
    forwards*: H1 x. apply_ih_bind (H2 x); eauto.
  - apply* typ_inter.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Require Import Program.Equality.

Lemma typing_through_subst_ee : forall E F x T e u U,
   typing (E & x ~: U & F) e T ->
   typing E u U ->
   typing (E & F) (subst_exp u x e) T.
Proof.
introv TypT TypU.
lets TypT': TypT.
inductions TypT; introv; simpl.
(*case int*)
 - apply* typ_lit.
 - (*case null*)
   apply* typ_null.
(*case var*)
 - case_var.
  + binds_get H0.
    lets M: (typing_weakening E F empty u U).
    do 2 rewrite concat_empty_r in M.
    apply* M.
  + binds_cases H0; apply* typ_var.
(*case app*)
 - eapply typ_app; eauto.
(*case sub*)
 - eapply typ_sub; eauto.
(*case abs*)
 - apply_fresh* typ_abs as y.
   assert (y \notin L) by auto.
   specialize (H y H1).
   rewrite* subst_ee_open_ee_var.
   lets : H0 y H1 E (F & y ~: A) x.
   lets : H2 U.
   forwards* : H3.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destruct~ TypU.
(*case typeof*)
 - apply_fresh* typ_typeof as y.
 + assert (y \notin L) by auto.
   rewrite* subst_ee_open_ee_var.
   lets: H y H4.
   lets: H0 y H4 E (F & y ~: A) x.
   lets: H6 U.
   forwards*: H7.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destruct~ TypU.
+ assert (y \notin L) by auto.
   rewrite* subst_ee_open_ee_var.
   lets: H1 y H4.
   lets: H2 y H4 E (F & y ~: B) x.
   lets: H6 U.
   forwards*: H7.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destruct~ TypU.
- apply* typ_inter.
Qed.


(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma inv_int : forall E A i5,
typing E (e_lit i5) A -> typing E (e_lit i5) t_int /\ t_int <: A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - specialize (IHTyp i5).
  forwards*: IHTyp. destruct H0.
  split*.
  eapply sub_transitivity; eauto.
  - forwards*: IHTyp1. destruct H.
    forwards*: IHTyp2.
Qed.

Lemma abs_typ_arrow_sub : forall G e A,
typing G (e_abs e) A ->
exists A1 B1, (t_arrow A1 B1) <: A.
Proof.
    introv Typ.
    inductions Typ.
    - forwards*: IHTyp. destruct H0 as [x1[x2 H3]].
      exists x1 x2. eapply sub_transitivity; eauto.
    - exists* A B.
    - forwards*: IHTyp1.
      forwards*: IHTyp2.
      destruct H as [x1 [x2 H3]].
      destruct H0 as [x3 [x4 H4]].
      exists t_top t_bot.
      apply s_anda.
      assert (t_arrow t_top t_bot <: t_arrow x1 x2); eauto.
      eapply sub_transitivity; eauto.
      assert (t_arrow t_top t_bot <: t_arrow x3 x4); eauto.
      eapply sub_transitivity; eauto.
Qed.

Lemma inv_and_arrow : forall G e A1 A2 B1 B2,
  typing G (e_abs e) (t_and A1 A2) ->
  t_and A1 A2 <: t_arrow B1 B2 ->
  A1 <: t_arrow B1 B2 \/ A2 <: t_arrow B1 B2.
Proof.
  introv Typ Sub.
  inverts Sub; eauto.
  apply abs_typ_arrow_sub in Typ.
  destruct Typ as [A3 [A4]].
  apply (findsubtypes_empty_not_ord (t_and A1 A2) (t_arrow A3 A4)) in H; auto.
  false. apply H. auto.
Qed.

Lemma inv_abs_sub : forall G e A B1 B2,
    typing G (e_abs e) A ->
    A <: (t_arrow B1 B2) ->
         exists C1 C2,
           (exists L, forall x , x \notin  L -> typing (G & x ~: C1) (e open_ee_var x) C2)
           /\ (t_arrow C1 C2) <: (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: B <: t_arrow B1 B2) by applys sub_transitivity H Sub.
    forwards* (?&?&?&?): IHTyp HS.
  - forwards* [HS|HS]: inv_and_arrow Sub.
Qed.

Lemma inv_arrow : forall G e A1 A2,
    typing G (e_abs e) (t_arrow A1 A2) ->
    exists B1 B2, (exists L, forall x , x \notin  L -> typing (G & x ~: B1) (e open_ee_var x) B2)
                  /\ (t_arrow B1 B2) <: (t_arrow A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards*: inv_abs_sub H.
  - exists* A1 A2.
Qed.

(*
inv_and_union is false

Counter example:

A1 = Int -> Int
A2 = Bool -> Bool

B1 = A1 & A2
B2 = A1 & A2

A1 & A2 <: B1 | B2 --- True

But:

A1 <: B1 | B2  ----- False

A2 <: B1 | B2  ----- False

*)

(*

Lemma inv_and_union : forall G e A1 A2 B1 B2,
  typing G (e_abs e) (t_and A1 A2) ->
  t_and A1 A2 <: t_union B1 B2 ->
  A1 <: t_union B1 B2 \/ A2 <: t_union B1 B2.
Proof.
  introv Typ Sub.
  lets SubArr: abs_typ_arrow_sub Typ.
  destruct SubArr as [C1[C2]].
  admit.
Admitted.

Lemma inv_abs_union : forall G e A B1 B2,
    typing G (e_abs e) A ->
    A <: (t_union B1 B2) ->
         exists C1 C2,
           (exists L, forall x , x \notin  L -> typing (G & x ~: C1) (e open_ee_var x) C2)
           /\ (t_arrow C1 C2) <: (t_union B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: B <: t_union B1 B2) by applys sub_transitivity H Sub.
    forwards* (?&?&?&?): IHTyp HS.
  - forwards* [HS|HS]: inv_and_union Sub.
Qed.

*)

(*

\x.e : A1 | A2
A1 = (Int -> Int) & (Bool -> Bool)
A2 = (Int -> Int) & (Bool -> Bool)

Int | Bool -> Int & Bool <: (Int -> Int) & (Bool -> Bool)

*)

(*

Lemma inv_arrow_union : forall G e A1 A2,
    typing G (e_abs e) (t_union A1 A2) ->
    exists B1 B2, (exists L, forall x , x \notin  L -> typing (G & x ~: B1) (e open_ee_var x) B2)
                  /\ (t_arrow B1 B2) <: (t_union A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards*: inv_abs_union H H0.
Qed.

Lemma inv_abs_union1 : forall G e A B1 B2,
    typing G (e_abs e) A ->
    A <: (t_union B1 B2) ->
         exists C1 C2, typing G (e_abs e) (t_arrow C1 C2)
           /\ (t_arrow C1 C2) <: (t_union B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: B <: t_union B1 B2) by applys sub_transitivity H Sub.
    forwards* (?&?&?&?): IHTyp HS.
  - forwards* [HS|HS]: inv_and_union Sub.
Qed.

Lemma inv_arrow_union1 : forall G e A1 A2,
    typing G (e_abs e) (t_union A1 A2) ->
    exists B1 B2, typing G (e_abs e) (t_arrow B1 B2)
                  /\ (t_arrow B1 B2) <: (t_union A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards*: inv_abs_union H H0.
Qed.

*)

Lemma inv_abs_union : forall G e A A1 A2,
    typing G (e_abs e) A ->
    A <: (t_union A1 A2) ->
    typing G (e_abs e) A1 \/ typing G (e_abs e) A2.
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - eapply sub_transitivity in Sub; eauto.
  - inverts* Sub.
  - inverts* Sub.
Qed.

(*

Lemma inv_arrow : forall G e A,
typing G (e_abs e) A ->
exists A1 B1, (exists L, forall x , x \notin  L ->
typing (G & x ~: A1) (e open_ee_var x) B1) /\ (t_arrow A1 B1) <: A.
Proof.
  introv Typ.
  inductions Typ; eauto.
 - forwards*: IHTyp.
  destruct H0 as [y [z]].
  exists y z . destruct H0.
  split*.
  eapply sub_transitivity; eauto.
 - forwards*: IHTyp1. destruct H as [x1 [x2]]. destruct H.
   forwards*: IHTyp2. destruct H1 as [x3 [x4]]. destruct H1.
   exists x1 x2. split*.
Admitted.

Lemma inv_and_arrow : forall A1 A2 B1 B2,
  t_and A1 A2 <: t_arrow B1 B2 ->
  A1 <: t_arrow B1 B2 \/ A2 <: t_arrow B1 B2.
Proof.
  intros.
  dependent induction H; eauto.
  apply (s_disj (t_and A1 A2) (t_arrow B1 B2)) in H.
  inverts* H.
Admitted.

Lemma inv_arrow' : forall G e A,
typing G (e_abs e) A ->
exists A1 B1, (exists L, forall x , x \notin  L ->
typing (G & x ~: A1) (e open_ee_var x) B1) /\ (t_arrow A1 B1) <: A.
Proof.
  introv Typ.
  inductions Typ; eauto.
 - forwards*: IHTyp.
  destruct H0 as [y [z]].
  exists y z . destruct H0.
  split*.
  eapply sub_transitivity; eauto.
 - lets*: typ_inter Typ1 Typ2.
   lets* [A3 [A4]]: inv_arrow2 H.
   apply sub_and in H0. destruct H0.
Admitted.

Lemma inv_arrow'' : forall G e A1 A2,
typing G (e_abs e) (t_arrow A1 A2) ->
exists B1 B2, (exists L, forall x , x \notin  L ->
typing (G & x ~: B1) (e open_ee_var x) B2) /\ (t_arrow B1 B2) <: (t_arrow A1 A2).
Proof.
  introv Typ.
  inductions Typ; eauto.
  clear IHTyp.
  inductions B; eauto.
  admit. admit. admit. admit. admit.
  admit.
Admitted.

Lemma inv_arrow1 : forall G e A,
typing G (e_abs e) A ->
exists A1 B1, typing G (e_abs e) (t_arrow A1 B1) /\ (t_arrow A1 B1) <: A.
Proof.
    introv Typ.
    inductions Typ.
    - forwards*: IHTyp.
      admit.
    - exists* A B.
    - forwards*: IHTyp1.
      forwards*: IHTyp2.
Admitted.

Lemma inv_arrow3 : forall G e A B,
typing G (e_abs e) (t_arrow A B) ->
exists A1 B1, (t_arrow A1 B1) <: (t_arrow A B) /\ typing G (e_abs e)  (t_arrow A1 B1).
Proof.
  introv Typ.
  exists* A B.
Qed.

Lemma inv_arrow31 : forall G e A,
typing G (e_abs e) A ->
exists A1 B1, (exists L, forall x , x \notin  L ->
typing (G & x ~: A1) (e open_ee_var x) B1).
Proof.
  introv Typ.
  inductions Typ; eauto.
Qed.

Lemma inv_arrow4 : forall G e A B,
typing G (e_abs e) (t_arrow A B) ->
exists A1 B1, (exists L, forall x , x \notin  L ->
typing (G & x ~: A1) (e open_ee_var x) B1).
Proof.
  introv Typ.
  lets*: inv_arrow31 Typ.
Qed.

Lemma inv_arrow5 : forall G e A B,
typing G (e_abs e) (t_union A B) ->
exists A1 B1, (t_arrow A1 B1) <: (t_union A B) /\ typing G (e_abs e)  (t_arrow A1 B1).
Proof.
  introv Typ.
  lets Typ': Typ.
  inductions Typ.
Admitted.

Lemma inv_arrow6 : forall G e A B,
typing G (e_abs e) (t_arrow A B) ->
(exists L, forall x , x \notin  L ->
typing (G & x ~: A) (e open_ee_var x) B).
Proof.
  introv Typ.
  inductions Typ; eauto.
  clear IHTyp.
  induction B0; try solve [inverts H; inverts H0].
  lets*[A3[A4]]: inv_arrow2 Typ. inverts H0. inverts H1.
  clear IHB0_1 IHB0_2.
  admit.
  admit.
  lets*: inv_and_arrow' Typ H.
Admitted.

Lemma inv_arrow7 : forall G e A1 A2,
forall B1 B2, t_arrow A1 A2 <: t_arrow B1 B2 ->
(exists L, forall x , x \notin  L ->
typing (G & x ~: A1) (e open_ee_var x) A2) ->
(exists L, forall x , x \notin  L ->
typing (G & x ~: B1) (e open_ee_var x) B2).
Proof.
  introv Sub. inverts Sub. intros.
  inductions Sub; eauto.
  intros. destruct H as [L].
  exists L. intros.
  inverts* H2.
Admitted.

Lemma inv_arrow8 : forall G e A1 A2,
typing G (e_abs e) (t_arrow A1 A2) ->
forall B1 B2, t_arrow A1 A2 <: t_arrow B1 B2 ->
typing G (e_abs e) (t_arrow B1 B2).
Proof.
  introv Typ.
  inductions Typ; eauto.
Qed.

Lemma inv_arrow9 : forall G e A1 A2,
typing G (e_abs e) (t_arrow A1 A2) ->
exists B1 B2, t_arrow A1 A2 <: t_arrow B1 B2 /\
(exists L, forall x , x \notin  L ->
typing (G & x ~: B1) (e open_ee_var x) B2).
Proof.
  introv Typ.
  inductions Typ; eauto. admit.
  intros. inverts H1. admit.
  inverts* H2.
Admitted.

*)

Lemma inv_null : forall E A,
typing E e_null A -> typing E e_null t_unit /\ t_unit <: A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - forwards*: IHTyp. destruct H0.
   split*.
   eapply sub_transitivity; eauto.
 - forwards*: IHTyp1.
Qed.


(*

e = \x.x
\x.x : (Int -> Int) /\ (Bool -> Bool) | (Int -> Int) /\ (Bool -> Bool)

\x.x : (Int -> Int) /\ (Bool -> Bool)
\x.x : (Int -> Int) /\ (Bool -> Bool)

*)

Lemma check_or_typ : forall E e A B,
   value e ->
   typing E e (t_union A B) ->
   typing E e A \/ typing E e B.
Proof.
  introv Val Typ.
  inverts Val.
  (*subsumption again*)
 - apply inv_int in Typ. destruct Typ.
   inverts* H0.
 - inverts Typ.
   eapply inv_abs_union in H0; eauto.
 - apply inv_null in Typ. destruct Typ.
   inverts* H0.
Qed.


Lemma val_check_disjoint_types : forall E v A B,
A *s B ->
value v ->
typing E v A ->
typing E v B -> False.
Proof.
  introv Disj Val Typ1 Typ2.
  unfold DisjSpec in Disj. unfold not in Disj.
  inverts Val.
  - apply inv_int in Typ1. destruct Typ1.
    apply inv_int in Typ2. destruct Typ2.
    forwards*: Disj t_int.
  - apply abs_typ_arrow_sub in Typ1.
    destruct Typ1 as [A1 [B1]].
    assert ((t_arrow t_top t_bot) <: (t_arrow A1 B1)). auto.
    apply abs_typ_arrow_sub in Typ2.
    destruct Typ2 as [A2 [B2]].
    assert ((t_arrow t_top t_bot) <: (t_arrow A2 B2)). auto.
    eapply sub_transitivity with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A1 B1)) (C:=A) in H1; auto.
    eapply sub_transitivity with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A2 B2)) (C:=B) in H3; auto.
    forwards*: Disj (t_arrow t_top t_bot).
  - apply inv_null in Typ1. destruct Typ1.
    apply inv_null in Typ2. destruct Typ2.
    forwards*: Disj t_unit.
Qed.

Lemma check_find_type : forall E e A B,
typing E e A ->
findtype e B ->
B <: A.
Proof.
  introv Typ Find.
  inductions Find.
  - apply inv_int in Typ.
    destruct~ Typ.
  - apply abs_typ_arrow_sub in Typ.
    destruct Typ as [A1 [B1]].
    assert ((t_arrow t_top t_bot) <: (t_arrow A1 B1)) by auto.
    eapply sub_transitivity; eauto.
  - apply inv_null in Typ. destruct~ Typ.
Qed.

(*******************************)
(****  Preservation Lemma  *****)
(*******************************)

Lemma preservation : forall E e e' T,
  typing E e T ->
  e --> e' ->
  typing E e' T.
Proof.
  introv Typ. gen e'.
  induction Typ; introv Red; try solve [ inverts* Red ].
  - (* app *)
    inverts* Red.
    (* beta *)
        forwards* : inv_arrow Typ1.
        destruct H as [A1[B1 [H H']]]. 
        destruct H as [L].
        pick_fresh x.
        assert (x \notin L) by auto.
        lets: H x H0.
        assert (G & x ~: A1 = G & x ~: A1 & empty).
        rewrite* concat_empty_r.
        rewrite H4 in H2.
        assert (G = G & empty).
        rewrite* concat_empty_r. rewrite H5.
        lets: typing_through_subst_ee.
        inverts H'.
        forwards*: H6 H2.
        rewrite* (@subst_ee_intro x).
        inverts H7.
  - (* typeof *)
    inverts* Red.
    
    + (* value checks against disjoint types *)
      lets temp: check_or_typ G e A B H11.
      lets DisjOr: temp Typ.
      destruct DisjOr.
     * (*true goal*)
       pick_fresh y. assert (y \notin L) by auto.
       forwards*: H H5.
       assert  (G & y ~: A = G & y ~: A & empty).
       rewrite* concat_empty_r. rewrite H7 in H6.
       assert (G = G & empty).
       rewrite* concat_empty_r.
       rewrite H8.
       forwards*: typing_through_subst_ee.
       rewrite* (@subst_ee_intro y).
     * (*false goal, value e checks against disjoint types A and B*)
       lets temp1: check_find_type G e B C0 H4.
       lets SubB: temp1 H12.
       unfold DisjSpec in H3. unfold not in H3.
       destruct H12.
       forwards*: H3 t_int.
       forwards*: H3 (t_arrow t_top t_bot).
       forwards*: H3 t_unit.
    +  (* value checks against disjoint types *)
      lets temp: check_or_typ G e A B H11.
      lets DisjOr: temp Typ.
      destruct DisjOr.
     * (*false goal, value e checks against disjoint types A and B*)
        lets temp1: check_find_type G e A C0 H4.
        lets SubA: temp1 H12.
        unfold DisjSpec in H3. unfold not in H3.
        destruct H12.
        forwards*: H3 t_int.
        forwards*: H3 (t_arrow t_top t_bot).
        forwards*: H3 t_unit.
     * (*true goal*)
        pick_fresh y. assert (y \notin L) by auto.
        forwards*: H1 H5.
        assert  (G & y ~: B = G & y ~: B & empty).
        rewrite* concat_empty_r. rewrite H7 in H6.
        assert (G = G & empty).
        rewrite* concat_empty_r.
        rewrite H8.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
    - forwards*: IHTyp1.
Qed.


(*******************************)
(******  Progress Lemma  *******)
(*******************************)

Lemma progress : forall e T,
typing empty e T -> (value e) \/ (exists e', e --> e').
Proof.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
(*case int*)
 - left*.
 (*case null*)
 - left*.
 (*case var*)
 - apply binds_empty_inv in H0. inversion H0.
 (*case typ-app*)
 - right. destruct* IHTyp1.
  + destruct* IHTyp2.
   * inverts* H.
     (*i infers arrow*)
     apply inv_int in Typ1.
     destruct Typ1.
     inverts H1. inverts H2.
     apply inv_null in Typ1.
     destruct Typ1.
     inverts H1. inverts H2.
     (*case step-appl*)
   * destruct H0.
     exists* (e_app e1 x).
   (*case step-appr*)
  + destruct H.
    exists (e_app x e2). apply* step_appl.
    forwards*: typing_regular Typ2.
(*case typ-sub*)
 - destruct~ IHTyp.
(*case typ-abs*)
 - left. forwards*: typing_regular Typ'.
(*case typ-typeof*)
 - right. destruct* IHTyp.
  + apply check_or_typ in Typ; auto.
    destruct Typ.
    (*case typeofl*)
   * destruct H4.
     { (*case e = int*)
      apply inv_int in H5. destruct H5.
      exists (open_exp_wrt_exp e1 (e_lit i5)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H y H6.
      eapply step_typeofl with (C:=t_int); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply abs_typ_arrow_sub in H5.
      destruct H5 as [A1 [B1]].
      assert ((t_arrow t_top t_bot) <: (t_arrow A1 B1)) by auto.
      eapply sub_transitivity in H5; eauto.
      exists (open_exp_wrt_exp e1 (e_abs e)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H y H7.
      eapply step_typeofl with (C:=(t_arrow t_top t_bot)); eauto.
      forwards*: typing_regular Typ'.
     }
     {
       (*case e = null*)
       apply inv_null in H5. destruct H5.
       exists (open_exp_wrt_exp e1 e_null).
       pick_fresh y.
       assert (y \notin L) by auto.
       lets: H y H6.
       eapply step_typeofl with (C:=t_unit); eauto.
       forwards*: typing_regular Typ'.
     }
   * (*case typeofr*)
     destruct H4.
     apply inv_int in H5. destruct H5.
     { (*case e = int*)
      exists (open_exp_wrt_exp e2 (e_lit i5)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H1 y H6.
      eapply step_typeofr with (C:=t_int); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply abs_typ_arrow_sub in H5.
      destruct H5 as [A1 [B1]].
      assert ((t_arrow t_top t_bot) <: (t_arrow A1 B1)) by auto.
      eapply sub_transitivity in H5; eauto.
      exists (open_exp_wrt_exp e2 (e_abs e)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H1 y H7.
      eapply step_typeofr with (C:=(t_arrow t_top t_bot)); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = null*)
       apply inv_null in H5. destruct H5.
       exists (open_exp_wrt_exp e2 e_null).
       pick_fresh y.
       assert (y \notin L) by auto.
       lets: H y H6.
       eapply step_typeofr with (C:=t_unit); eauto.
       forwards*: typing_regular Typ'.
     }
  + (*case typeof*)
    destruct H4.
    exists (e_typeof x A e1 B e2).
    apply step_typeof; auto.
    forwards*: typing_regular Typ'.
  - destruct~ IHTyp1.
Qed.

(*******************************)
(*****  Determinism Lemma  *****)
(*******************************)

Lemma inv_app : forall E e1 e2 A,
typing E (e_app e1 e2) A ->
exists A1 B1, typing E e1 (t_arrow A1 B1) /\ typing E e2 A1.
Proof.
  introv Typ.
  inductions Typ.
 - exists* A B.
 - specialize (IHTyp e1 e2).
  forwards*: IHTyp.
 - forwards*: IHTyp1.
Qed.

Lemma inv_typeof : forall E e e1 e2 A B C,
typing E (e_typeof e A e1 B e2) C ->
exists D, typing E e D /\ A *s B.
Proof.
  introv Typ.
  inductions Typ.
  - specialize (IHTyp e e1 e2 A B).
    forwards*: IHTyp.
  - exists* (t_union A B).
  - forwards*: IHTyp1.
Qed.

Lemma determinism_dir : forall E e e1 e2 A, typing E e A ->
e --> e1 -> e --> e2 -> e1 = e2.
Proof.
  introv Typ He1. gen e2 A.
  induction He1; introv Typ He2.
  (*case step-appl*)
  - inverts* He2.
   + apply inv_app in Typ.
     destruct Typ as [A1 [B1]]. destruct H0.
     forwards*: IHHe1. rewrite* H3.
   + inverts* H2; inverts He1.
   + inverts* He1.
(*case step-appr*)
  - inverts* He2.
   + inverts* H; inverts* H4.
   + apply inv_app in Typ.
     destruct Typ as [A1 [B1]]. destruct H0.
     forwards*: IHHe1 H1. rewrite* H3.
   + inverts H4; inverts He1.
(*case step-beta*)
  - inverts* He2.
   + inverts* H5.
   + inverts H0; inverts H5.
(*case step-typeof*)
 - inverts* He2.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H0.
    forwards*: IHHe1. rewrite* H2.
  + inverts H8; inverts He1.
  + inverts H8; inverts He1.
(*case step-typeofl*)
 - inverts* He2.
  + inverts H0. inverts H10. inverts H10. inverts H10.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [H3 Disj].
    inverts H0.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj t_int.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj (t_arrow t_top t_bot).
    * inverts H1. inverts H11.
      forwards*: Disj t_unit.
      assert (t_unit <: (t_and A B)) by auto.
      contradiction.
(*case step-typeofr*)
- inverts* He2.
  + inverts H0; inverts H10.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [H3 Disj].
    inverts H0.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj t_int.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj (t_arrow t_top t_bot).
    * inverts H1. inverts H11.
      forwards*: Disj t_unit.
      assert (t_unit <: (t_and A B)) by auto.
      contradiction.
Qed.