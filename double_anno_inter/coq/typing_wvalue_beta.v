Require Import TLC.LibLN.
Require Import syntax_wvalue.

(*
This file is created on April 09, 2021

This is the main semantics file for disjoint union types
with intersection types.

syntax.v is the syntax file for this semantics

This file contains type safety and deterministic lemmas
associated with syntax_wvalue.v

Bool and String primitive type

Removed top from ordinary types

April 06, 2021:
--------------
-> extended from typing_no_top_findsubtypes.v
-> wexpr added

April 09, 2020:
---------------
-> extended from typing_wvalue.v
-> step-beta updated
-> changeanno inductive changed to changeanno definition
*)

(* defns changeanno *)
Definition changeanno (v:exp) (A:typ) (B:typ) :=    (* defn changeanno *)
 match v with
   | (e_ann p C) => (e_ann p B)
   | (e_abs e)   => (e_ann (e_ann (e_abs e) A) B)
   | _           => v
 end.


(* defns Typing *)
Inductive typing : env -> exp -> dirflag -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:env) i5,
      okt  G  ->
     typing G (e_lit i5) infer t_int
 | typ_bool : forall (G:env) b,
      okt  G  ->
     typing G (e_bool b) infer t_bool
 | typ_str : forall (G:env) s,
      okt G ->
      typing G (e_str s) infer t_str
 | typ_var : forall (G:env) (x:var) (A:typ),
      okt  G  ->
      binds  x A G  ->
     typing G (e_var_f x) infer A
 | typ_ann : forall (G:env) (e:exp) (A:typ),
     typing G e check A ->
     typing G (e_ann e A) infer A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     typing G e1 infer (t_arrow A B) ->
     typing G e2 check A ->
     typing G (e_app e1 e2) infer B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing G e infer B ->
     subtyping B A ->
     typing G e check A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      ( forall x , x \notin  L  -> typing  (G & x ~: A )   ( open_exp_wrt_exp e (e_var_f x) )  check B )  ->
     typing G (e_abs e) check (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing G e check (t_union A B) ->
     ( forall x , x \notin  L  -> typing  (G & x ~: A )   ( open_exp_wrt_exp e1 (e_var_f x) )  check C ) ->
     ( forall x , x \notin  L  -> typing  (G & x ~: B )   ( open_exp_wrt_exp e2 (e_var_f x) )  check C ) ->
     A *s B ->
     typing G (e_typeof e A e1 B e2) check C.

(* defns Reduction *)
Reserved Notation "e --> e'" (at level 80).
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_int : forall i5,
     step (e_lit i5) (e_ann (e_lit i5) t_int)
 | step_bool : forall b,
     step (e_bool b) (e_ann (e_bool b) t_bool)
 | step_str : forall s,
     step (e_str s) (e_ann (e_str s) t_str)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_app e1 e2) (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     wexpr v ->
     step e e' ->
     step (e_app v e) (e_app v e')
 | step_beta : forall (e:exp) (A1 B1 A2 B2:typ) (v:exp) (C:typ),
     lc_exp (e_abs e) ->
     value v ->
     (e_app  ( (e_ann (e_ann  ( (e_abs e) )  (t_arrow A1 B1)) (t_arrow A2 B2)) ) ( v ) ) --> (e_ann (e_ann  (  (open_exp_wrt_exp  e (changeanno v A2 A1) )  )  B1) B2)
 | step_ann : forall (e:exp) (A:typ) (e':exp),
     not ( wexpr (e_ann e A) )  ->
     step e e' ->
     step (e_ann e A) (e_ann e' A)
 | step_rm_ann : forall (p:exp) (A B:typ),
     pexpr p ->
     step (e_ann (e_ann p A) B) (e_ann p B)
 | step_lam_ann : forall (e:exp) (A B:typ),
     lc_exp (e_abs e) ->
     step (e_ann  ( (e_abs e) )  (t_arrow A B)) (e_ann (e_ann  ( (e_abs e) )  (t_arrow A B)) (t_arrow A B))
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     step e e' ->
     step (e_typeof e A e1 B e2) (e_typeof e' A e1 B e2)
 | step_typeofl : forall (p:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (x:var) (C:typ) (D:typ),
     lc_exp (e_typeof (e_ann p D) A e1 B e2) ->
     pexpr p ->
     findtype p C ->
     subtyping C A ->
     step (e_typeof (e_ann p D) A e1 B e2)  (open_exp_wrt_exp e1 (e_ann p A) )
 | step_typeofr : forall (p:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (x:var) (C:typ) (D:typ),
    lc_exp (e_typeof (e_ann p D) A e1 B e2) ->
     pexpr p ->
     findtype p C ->
     subtyping C B ->
     step (e_typeof (e_ann p D) A e1 B e2)  (open_exp_wrt_exp  e2 (e_ann p B) )
where "e --> e'" := (step e e') : env_scope.

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

Hint Immediate okt_strengthen : core.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e dir T,
  typing E e dir T -> okt E /\ lc_exp e.
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
  inverts* H.
  inverts* H0.
Qed.

Lemma prevalue_regular : forall t,
  pexpr t -> lc_exp t.
Proof.
  induction 1; autos*.
Qed.

Lemma wvalue_regular : forall t,
  wexpr t -> lc_exp t.
Proof.
  induction 1; autos*.
  inverts* H.
Qed.

Hint Immediate value_regular prevalue_regular wvalue_regular : core.

(* ********************************************************************** *)
(** Weakening (5) *)


Lemma typing_weakening : forall E F G e dir T,
   typing (E & G) e dir T ->
   okt (E & F & G) ->
   typing (E & F & G) e dir T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
  - apply* typ_bool.
  - apply* typ_str.
  - apply* typ_var. apply* binds_weaken.
  - apply* typ_ann.
  - apply* typ_app.
  - apply* typ_sub.
  - apply_fresh* typ_abs as x.
    forwards~: (H x).
    apply_ih_bind (H0 x); eauto.
  - apply_fresh* typ_typeof as x.
    forwards*: H x. apply_ih_bind (H0 x); eauto.
    forwards*: H1 x. apply_ih_bind (H2 x); eauto.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Require Import Program.Equality.

Lemma typing_through_subst_ee : forall E F x T e u dir U,
   typing (E & x ~: U & F) e dir T ->
   typing E u infer U ->
   typing (E & F) (subst_exp u x e) dir T.
Proof.
introv TypT TypU.
lets TypT': TypT.
inductions TypT; introv; simpl.
 - apply* typ_lit.
 - apply* typ_bool.
 - apply* typ_str.
 - case_var.
  + binds_get H0.
    lets M: (typing_weakening E F empty u infer U).
    do 2 rewrite concat_empty_r in M.
    apply* M.
  + binds_cases H0; apply* typ_var.
 - forwards* : IHTypT.
 - eapply typ_app; eauto.
 - eapply typ_sub; eauto.
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
Qed.

Lemma chk_inf : forall G e A,
    typing G (e_ann e A) check A <-> typing G (e_ann e A) infer A.
Proof.
intros. split. intros.
inverts H. inverts H0. eauto.
intros. eapply typ_sub; eauto.
Qed.


Lemma check_or_typ : forall E e A B,
   pexpr e ->
   A *s B ->
   typing E e check (t_union A B) ->
   typing E e check A \/ typing E e check B.
Proof.
  intros.
  inductions H1; try solve [ inverts* H | inverts* H0 | inverts* H1].
  inverts H;
  inverts* H1; inverts* H2.
Qed.

Lemma check_pexpr_ann : forall E p A C,
   pexpr p ->
   typing E (e_ann p C) check A ->
   typing E p check A.
Proof.
intros E p A C Prev Typ.
inductions Prev.
- inverts Typ. inverts H. inverts H3. inverts H.
  assert (typing E (e_lit i5) infer t_int). eauto.
  eapply typ_sub; eauto.
  eapply sub_transitivity; eauto.
- inverts Typ. inverts H. inverts H3. inverts H.
  assert (typing E (e_bool b) infer t_bool). eauto.
  eapply typ_sub; eauto.
  eapply sub_transitivity; eauto.
- inverts Typ. inverts H. inverts H3. inverts H.
  assert (typing E (e_str s) infer t_str). eauto.
  eapply typ_sub; eauto.
  eapply sub_transitivity; eauto.
- inverts Typ. inverts H0. inverts H4. inverts H0.
  assert (typing E (e_ann (e_abs e) (t_arrow A0 B)) infer (t_arrow A0 B)). eauto.
  eapply typ_sub; eauto. eapply sub_transitivity; eauto.
Qed.

Lemma pexpr_chk_sub : forall G e A, pexpr e -> typing G e check A -> 
forall B, A <: B -> typing G e check B.
Proof.
intros G e A Prev Typ1 B Sub.
inductions Typ1.
 - assert (B <: B0).
   eapply sub_transitivity; eauto.
   clear H Sub.
   eapply typ_sub; eauto.
 - inversion Prev.
 - inversion Prev.
Qed.

Hint Resolve chk_inf : core.

Lemma pexpr_inf_typ : forall G p A, pexpr p ->
typing G p check A -> exists B, typing G p infer B /\ B <: A.
Proof.
intros G p A Prev Typ.
inductions Prev.
- exists t_int. constructor. constructor.
  apply typing_regular in Typ. destruct~ Typ.
  dependent destruction Typ. dependent destruction Typ. auto.
- exists t_bool. constructor. constructor.
  apply typing_regular in Typ. destruct~ Typ.
  dependent destruction Typ. dependent destruction Typ. auto.
- exists t_str. constructor. constructor.
  apply typing_regular in Typ. destruct~ Typ.
  dependent destruction Typ. dependent destruction Typ. auto.
- dependent destruction Typ.
  dependent destruction Typ.
  exists (t_arrow A0 B). constructor. auto. auto.
Qed.

(* ********************************************************************** *)
(** Preservation Result (20) *)


Lemma preservation : forall E e e' dir T,
  typing E e dir T ->
  e --> e' ->
  typing E e' dir T.
Proof.
  introv Typ. gen e'.
  induction Typ; introv Red; try solve [ inverts* Red ].
  - (* rm anno *)
    inverts* Red.
    + (* p *)
      forwards*: check_pexpr_ann Typ.
    (*+ (* lam *)
      econstructor. applys* chk_inf.*)
  - (* app *)
    inverts* Red.
    + (* beta *)
     inverts H3.
     * inverts Typ1.
      do 3 dependent destruction H5.
      { (* infer lam *)
        dependent destruction H5.
      }
      {  
        dependent destruction H2.
        constructor.
        pick_fresh x.
        assert (x \notin L) by auto.
        lets: H0 x H2.
        assert (G & x ~: A1 = G & x ~: A1 & empty).
        rewrite* concat_empty_r.
        rewrite H4 in H3.
        assert (G = G & empty).
        rewrite* concat_empty_r.
        rewrite H5.
      (* prove p:A1 checks *)
        inverts Typ2. inverts H. inverts H6.
        assert (typing G (e_ann p A1) infer A1).
        assert (B0 <: A1).
        eapply sub_transitivity; eauto.
        forwards*: pexpr_chk_sub H10 H.
        lets*: typing_through_subst_ee.
        forwards*: H6 H3.
        unfold changeanno.
        rewrite* (@subst_ee_intro x).
        inversion H. inversion H.
      }
    * inverts Typ1.
      dependent destruction H5. dependent destruction H5.
      dependent destruction H5. dependent destruction H5.
      constructor.
      inverts H2.
      pick_fresh y. assert (y \notin L0) by auto.
      forwards*: H0 H2.
      assert (G & y ~: A1 = G & y ~: A1 & empty).
      rewrite* concat_empty_r.
      rewrite H4 in H3.
      assert (G = G & empty). rewrite* concat_empty_r.
      rewrite H5.
      inverts Typ2. inverts H7.
      assert (typing G ((e_ann (e_ann (e_abs e0) (t_arrow A0 B0)) A1)) infer A1). eauto.
      forwards*: typing_through_subst_ee.
      rewrite* (@subst_ee_intro y).
      unfold changeanno. forwards*: typing_regular.
      inversion H3.
  - (* typeof *)
    inverts* Red.
    + pick_fresh y. assert (y \notin L) by auto.
      forwards*: H H4.
      assert  (G & y ~: A = G & y ~: A & empty).
      rewrite* concat_empty_r. rewrite H6 in H5.
      assert (G = G & empty).
      rewrite* concat_empty_r.
      rewrite H7.
      dependent destruction H12.
      * assert (typing G (e_lit i5) infer t_int). apply typ_lit.
        forwards*: typing_regular Typ.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
      * assert (typing G (e_bool b) infer t_bool). apply typ_bool.
        forwards*: typing_regular Typ.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
      * assert (typing G (e_str s) infer t_str). apply typ_str.
        forwards*: typing_regular Typ.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
      * assert (typing G (e_ann (e_abs e) (t_arrow A0 B0)) infer (t_arrow A0 B0)). apply typ_ann.
        do 3 dependent destruction Typ.
        dependent destruction Typ. auto.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
    + pick_fresh y. assert (y \notin L) by auto.
      forwards*: H1 H4.
      assert  (G & y ~: B = G & y ~: B & empty).
      rewrite* concat_empty_r. rewrite H6 in H5.
      assert (G = G & empty).
      rewrite* concat_empty_r.
      rewrite H7.
      dependent destruction H12.
      * assert (typing G (e_lit i5) infer t_int). apply typ_lit.
        forwards*: typing_regular Typ.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
      * assert (typing G (e_bool b) infer t_bool). apply typ_bool.
        forwards*: typing_regular Typ.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
      * assert (typing G (e_str s) infer t_str). apply typ_str.
        forwards*: typing_regular Typ.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
      * assert (typing G (e_ann (e_abs e) (t_arrow A0 B0)) infer (t_arrow A0 B0)). apply typ_ann.
        do 4 dependent destruction Typ. auto.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
Qed.

Lemma canonical_form_abs_prevalue : forall t U1 U2,
  pexpr t -> typing empty t infer (t_arrow U1 U2) ->
  exists V, exists e1, exists V1, t = e_ann (e_abs e1) (t_arrow V V1).
Proof.
  introv Val Typ.
  gen_eq T: (t_arrow U1 U2). intro st.
   assert (T <: (t_arrow U1 U2)).
{ rewrite st; apply sub_refl. }
  clear st. gen_eq E: (@empty typ).  gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inverts* Val | inversion EQT | eauto ].
  - inverts EQT. inverts H0.
  - inverts EQT. inverts H0.
  - inverts EQT. inverts H0.
  - subst. assert (B <: (t_arrow U1 U2)). {
    eapply sub_transitivity. apply H. apply EQT. }
    eapply IHTyp. apply Val. apply H0. auto.
Qed.

Lemma check_both_disj_false : forall E e A B,
   pexpr e ->
   A *s B ->
   typing E e check A -> typing E e check B -> False.
Proof.
  intros.
  inductions H; try solve [ inverts* H | inverts* H0 | inverts* H2].
 - inverts H1. inverts H. inverts H2. inverts H.
   unfold DisjSpec in H0. specialize (H0 t_int).
   forwards*: H0.
 - inverts H1. inverts H. inverts H2. inverts H.
   unfold DisjSpec in H0. specialize (H0 t_bool).
   forwards*: H0.
 - inverts H1. inverts H. inverts H2. inverts H.
   unfold DisjSpec in H0. specialize (H0 t_str).
   forwards*: H0.
 - inverts H1. inverts H3. inverts H2. inverts H1.
   unfold DisjSpec in H0.
   specialize (H0 (t_arrow A0 B0)).
   forwards*: H0.
Qed.

Lemma not_expr : forall e t, ~ value (e_ann e t) -> ~ pexpr e.
Proof.
intros.
unfold not. intros.
unfold not in H. apply* H.
Qed.

Lemma val_pexpr : forall e, lc_exp e -> ~ wexpr e -> pexpr e \/ ~ pexpr e.
Proof.
introv lc. intros.
inductions e; try solve [right; unfold not; intros; inversion H0].
- left*.
- left*.
- left*.
- inductions e; try solve [right; unfold not; intros; inverts H0].
  destruct~ IHe0. inversion lc. subst. auto. unfold not. intros. inversion H0.
  inductions t; try solve [ right; unfold not; intros; inversion H1].
  left. apply pexpr_abs. inversion lc; subst. auto.
Qed.

Lemma value_not_value : forall e, lc_exp e -> (wexpr e) \/ (~ (wexpr e)).
Proof.
introv lc.
intros.
inductions e;
try solve [right; unfold not; intros; inversion H].
destruct~ IHe. inverts* lc.
- inverts* H. inverts* H0.
 + right. unfold not. intros. inversion H. subst. inversion H1.
 + right. unfold not. intros. inversion H. subst. inversion H1.
 + right. unfold not. intros. inversion H. subst. inversion H1.
 + right. unfold not. intros. inverts H0. inversion H2.
- apply val_pexpr in H.
  destruct~ H. right. unfold not. intros.
  inverts* H0. inverts* lc. 
Qed.

(* need to be strengthened *)
Lemma progress : forall e dir T,
typing empty e dir T -> (value e) \/ (exists e', e --> e').
Proof.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
(*case int*)
 - right*.
 (*case bool*)
 - right*.
 (*case string*)
 - right*.
 (*case var*)
 - apply binds_empty_inv in H0. inversion H0.
 (*case anno*)
 - destruct* IHTyp.
  + inverts H.
  (*case step-rm-anno*)
   * inverts H0.
     right. exists (e_ann p A). apply* step_rm_ann.
   (*case step-lam-ann*)
   * inverts Typ. inverts H.
     right. exists (e_ann (e_ann (e_abs e0)(t_arrow A0 B))(t_arrow A0 B) ).
     apply* step_lam_ann.
  + destruct H.
    dependent destruction Typ.
     { inverts* Typ.
       { apply binds_empty_inv in H2. inversion H2. }
       { 
         inverts* H0.
         destruct (value_not_value (e_ann (e_ann e0 B) A)).
         forwards*: typing_regular Typ'.
         left*.
         right. exists*.
         destruct (value_not_value ((e_ann (e_ann (e_ann p A0) B) A))).
         forwards*: typing_regular Typ'.
         left*.
         right.  exists*.
       }
       { right. exists (e_ann x A). apply* step_ann.
         unfold not. intros. inversion H3. inversion H5. 
       } 
     }
     { inversion H0. }
     { right. exists (e_ann x C). apply* step_ann.
       unfold not. intros. inversion H3. inversion H5. }
(*case typ-app*)
 - right. destruct* IHTyp1.
  + destruct* IHTyp2.
   * inverts* H.
    inverts* H1. inverts Typ1. inverts H.
    (*i infers arrow*)
    inverts H3. inverts H. inverts H1. inverts H.
    (*b infers arrow*)
    inverts H3. inverts H. inverts H1. inverts H.
    (*s infers arrow*)
    inverts H3. inverts H. inverts H1. inverts H.
    (*step-beta*)
    exists* (e_ann (e_ann (open_exp_wrt_exp e (changeanno e2 A A0)) B0) B).
    inverts Typ1.
    (*case step-appr*)
   * destruct H0.
     destruct H.
   { exists* (e_app e x). }
   { inverts Typ1. }
   (*case step-appl*)
  + destruct H. 
    exists (e_app x e2). apply* step_appl.
    forwards*: typing_regular Typ2.
(*case typ-sub*)
 - destruct~ IHTyp.
(*case typ-abs*)
 - left. forwards*: typing_regular Typ'.
   destruct~ H1. inverts* H2.
(*case typ-typeof*)
 - right. destruct* IHTyp.
  + inverts H4. inverts H5. 
    apply check_pexpr_ann in Typ; auto.
    eapply check_or_typ in Typ; eauto.
    destruct Typ.
   * forwards*: pexpr_inf_typ H4.
     destruct H6 as [S [H41 H51]].
     exists (open_exp_wrt_exp e1 (e_ann p A)).
     pick_fresh y.
     assert (y \notin L) by auto.
     lets: H y H6.
     eapply step_typeofl with (C:=S); eauto.
     forwards*: typing_regular Typ'.
     inverts H5; inverts* H41.
     inversion H4. 
     inverts H4. eauto. inversion H4.
   * forwards*: pexpr_inf_typ H4.
     destruct H6 as [S [H41 H51]].
     exists (open_exp_wrt_exp e2 (e_ann p B)).
     pick_fresh y.
     assert (y \notin L) by auto.
     lets: H1 y H6.
     eapply step_typeofr with (C:=S); eauto.
     forwards*: typing_regular Typ'.
     inverts H5; inverts* H41.
     inversion H4.
     inverts H4. eauto.
     inversion H4.
   * inverts Typ. inversion H4.
  + destruct H4.
     exists (e_typeof x A e1 B e2).
     apply step_typeof; auto.
     forwards*: typing_regular Typ'.
Qed.

Lemma determinism_dir : forall E e e1 e2 A dir, typing E e dir A -> 
e --> e1 -> e --> e2 -> e1 = e2.
Proof.
  introv Typ He1. gen e2 A dir.
  induction He1; introv Typ He2.
  (*case step-int*)
  - inverts* He2.
  (*case step-bool*)
  - inverts* He2.
  (*case step-str*) 
  - inverts* He2.
  (*case step-appl*)
  - inverts* He2.
   + inverts Typ.
     forwards*: IHHe1. rewrite* H0.
     inverts H0. eapply typ_sub with (A:=(t_arrow A0 B)) in H7; eauto.
     forwards*: IHHe1. rewrite* H0.
   + inverts* H2. inverts* H0. 
    * inverts He1. assert (value (e_ann (e_lit i5) A0)) by auto. 
      inverts H0. contradiction.
    * inverts He1. assert (value (e_ann (e_bool b) A0)) by auto. 
      inverts H0. contradiction.
    * inverts He1. assert (value (e_ann (e_str s) A0)) by auto. 
      inverts H0. contradiction.
    * inverts He1.
      assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B)) A0)). eauto.
      inverts H0. contradiction.
      inverts* H6.
   + inverts* He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))). eauto.
     inverts H0. contradiction.
     inverts H6.
(*case step-appr*)
  - inverts* He2.
   + inverts* H. inverts* H0. 
    * inverts* H4. assert (wexpr (e_ann (e_lit i5) A0)) by auto. 
      contradiction.
    * inverts H4. assert (wexpr (e_ann (e_bool b) A0)) by auto. contradiction.
    * inverts H4. assert (wexpr (e_ann (e_str s) A0)) by auto. contradiction.
    * inverts* H4. assert (wexpr (e_ann (e_ann (e_abs e0) (t_arrow A1 B)) A0)) by auto.
     contradiction.
     inversion H6.
   + inverts Typ.
     forwards*: IHHe1 H8. rewrite* H0.
     inverts H0. forwards*: IHHe1 H8. rewrite* H0.
   + inverts H4. inverts H0. inverts H1. 
    * inverts He1.
     assert (wexpr (e_ann (e_lit i5) A0)) by auto. contradiction.
    * inverts He1. assert (wexpr (e_ann (e_bool b) A0)) by auto. contradiction.
    * inverts He1. assert (wexpr (e_ann (e_str s) A0)) by auto. contradiction.
    * inverts He1. assert (wexpr (e_ann (e_ann (e_abs e) (t_arrow A3 B)) A0)) by auto.
      contradiction.
      inversion H6.
    * inversion He1.
(*case step-beta*)
  - inverts* He2.
   + inverts* H5. 
     assert (wexpr (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))) by auto.
     contradiction.
     inversion H7.
   + inverts H0. inverts H1. inverts H0. 
    * inverts H5.
     assert (wexpr (e_ann (e_lit i5) A0)) by auto. contradiction.
    * inverts H5. assert (wexpr (e_ann (e_bool b) A0)) by auto. contradiction.
    * inverts H5. assert (wexpr (e_ann (e_str s) A0)) by auto. contradiction.
    * inverts H5. assert (wexpr (e_ann (e_ann (e_abs e0) (t_arrow A3 B)) A0)) by auto.
      contradiction.
      inversion H7.
    * inversion H5.
(*case step-ann*)
  - inverts* He2. 
    inverts Typ. forwards*: IHHe1 H7. rewrite* H0.
    inverts H0. forwards*: IHHe1 H6. rewrite* H0.
    inverts H3.
   + inverts He1. assert (wexpr (e_ann (e_lit i5) A1)) by auto. contradiction.
   + inverts He1. assert (wexpr (e_ann (e_bool b) A1)) by auto. contradiction.
   + inverts He1. assert (wexpr (e_ann (e_str s) A1)) by auto. contradiction.
   + inverts He1. assert (wexpr (e_ann (e_ann (e_abs e) (t_arrow A2 B)) A1)) by auto.
     contradiction.
     inversion H5.
   + inversion He1.
(*case step-rm-ann*)
  - inverts* He2. inverts H.
   + inverts H4. assert (wexpr (e_ann (e_lit i5) A)) by auto. contradiction.
   + inverts H4. assert (wexpr (e_ann (e_bool b) A)) by auto. contradiction.
   + inverts H4. assert (wexpr (e_ann (e_str s) A)) by auto. contradiction.
   + inverts H4. assert (wexpr (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) A)) by auto. contradiction.
     inversion H6.
(*case step-lam-ann*)
  - inverts* He2. inversion H4.
(*case step-typeof*)
 - inverts* He2.
  + inverts Typ. inverts H0.
    forwards*: IHHe1 H10. rewrite* H0.
  + inverts H8.
   * inverts He1. assert (wexpr (e_ann (e_lit i5) D)) by auto. contradiction.
   * inverts He1. assert (wexpr (e_ann (e_bool b) D)) by auto. contradiction.
   * inverts He1. assert (wexpr (e_ann (e_str s) D)) by auto. contradiction.
   * inverts He1. assert (wexpr (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
     contradiction.
    inversion H5.
  + inverts H8.
   * inverts He1. assert (wexpr (e_ann (e_lit i5) D)) by auto. contradiction.
   * inverts He1. assert (wexpr (e_ann (e_bool b) D)) by auto. contradiction.
   * inverts He1. assert (wexpr (e_ann (e_str s) D)) by auto. contradiction.
   * inverts He1. assert (wexpr (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
     contradiction.
    inversion H5.
(*case step-typeofl*)
 - inverts* He2.
  + inverts H1. 
   * inverts H10. assert (wexpr (e_ann (e_lit i5) D)) by auto. contradiction.
   * inverts H10. assert (wexpr (e_ann (e_bool b) D)) by auto. contradiction.
   * inverts H10. assert (wexpr (e_ann (e_str s) D)) by auto. contradiction.
   * inverts H10. assert (wexpr (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
     contradiction.
    inversion H7.
  + inverts Typ. inverts H3.
    forwards*: typing_regular. destruct H3.
    inverts* H1. 
   * inverts H12.
     unfold DisjSpec in H18. specialize (H18 t_int).
     forwards*: H18.
     unfold not in H1.
     forwards*: H1.
    * inverts H12.
      unfold DisjSpec in H18. specialize (H18 t_bool).
      forwards*: H18.
      unfold not in H1.
      forwards*: H1.
    * inverts H12.
      unfold DisjSpec in H18. specialize (H18 t_str).
      forwards*: H18.
      unfold not in H1.
      forwards*: H1.
   * inverts H12.
     unfold DisjSpec in H18. specialize (H18 (t_arrow A1 B0)).
     forwards*: H18.
     unfold not in H1.
     forwards*: H1.
(*case step-typeofr*) 
- inverts* He2.
     + inverts H1. 
      * inverts H10. assert (wexpr (e_ann (e_lit i5) D)) by auto. contradiction.
      * inverts H10. assert (wexpr (e_ann (e_bool b) D)) by auto. contradiction.
      * inverts H10. assert (wexpr (e_ann (e_str s) D)) by auto. contradiction.
      * inverts H10. assert (wexpr (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
        contradiction.
       inversion H7.
     + inverts Typ. inverts H3.
       forwards*: typing_regular. destruct H3.
       inverts* H1. 
      * inverts H12.
        unfold DisjSpec in H18. specialize (H18 t_int).
        forwards*: H18.
        unfold not in H1.
        forwards*: H1.
       * inverts H12.
         unfold DisjSpec in H18. specialize (H18 t_bool).
         forwards*: H18.
         unfold not in H1.
         forwards*: H1.
       * inverts H12.
         unfold DisjSpec in H18. specialize (H18 t_str).
         forwards*: H18.
         unfold not in H1.
         forwards*: H1.
      * inverts H12.
        unfold DisjSpec in H18. specialize (H18 (t_arrow A1 B0)).
        forwards*: H18.
        unfold not in H1.
        forwards*: H1.
Qed.