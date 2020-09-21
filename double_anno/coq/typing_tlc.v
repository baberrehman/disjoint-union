Require Import TLC.LibLN.
Require Import syntaxtlc.

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
  rewrite concat_empty_r in *. apply okt_push_inv in O. destruct~ O.
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
Qed.

(* ********************************************************************** *)
(** Weakening (5) *)


Lemma typing_weakening : forall E F G e dir T,
   typing (E & G) e dir T -> 
   okt (E & F & G) ->
   typing (E & F & G) e dir T.
Proof. 
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
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

Lemma chk_sub : forall G e A, typing G e check A -> forall B, A <: B -> typing G e check B.
Proof.
intros.
inductions H.
assert (B <: B0).
eapply sub_transitivity; eauto.
clear H0 H1.
eapply typ_sub; eauto.
pick_fresh x.
assert (x \notin L) by auto.
lets: H x H2.
inductions H1; try solve [inversion H1].
clear IHsubtyping1 IHsubtyping2.
Admitted.

Lemma pexpr_inf_typ : forall G p A, pexpr p ->
typing G p check A -> exists B, typing G p infer B /\ B <: A.
Proof.
intros.
inductions H.
exists t_int. constructor. constructor.
apply typing_regular in H0. destruct~ H0.
dependent destruction H0. dependent destruction H0. auto.
dependent destruction H0.
dependent destruction H0.
exists (t_arrow A0 B). constructor. auto. auto.
Qed.

(*Lemma pexpr_inf_typ_ann : forall G p A C, pexpr p ->
typing G p check A -> exists B, typing G p infer B.
Proof.
intros.
inductions H.
exists t_int. constructor.
apply typing_regular in H0. destruct~ H0.
dependent destruction H0.
dependent destruction H0.
exists (t_arrow A0 B). constructor. auto.
Qed.*)


(* ********************************************************************** *)
(** Preservation Result (20) *)
                    

Lemma preservation : forall E e e' dir T,
  typing E e dir T -> 
  e --> e' -> 
  typing E e' dir T.
Proof.
  introv Typ. gen e'.
  lets Typ': Typ.
  induction Typ; introv Red; try solve [ inversion Red ].
  - inverts* Red.
  - inverts* Red.
   + inverts* Typ. inverts* H.
    apply typ_ann.
    eapply chk_sub; eauto.
  + constructor.
    eapply typ_sub; eauto. apply sub_refl.
 - inverts* Red.
  + inverts Typ1.
    do 3 dependent destruction H5.
    dependent destruction H5.
    dependent destruction H0.
    constructor.
    pick_fresh x.
    assert (x \notin L) by auto.
    lets: H x H0.
    assert (G & x ~: A1 = G & x ~: A1 & empty).
    rewrite* concat_empty_r.
    rewrite H4 in H2.
    assert (G = G & empty).
    rewrite* concat_empty_r.
    rewrite H5.
    dependent destruction H3.
   * assert (typing G (e_ann (e_lit i5) A1) infer A1).
     constructor.
     eapply chk_sub; eauto.
     forwards*: typing_through_subst_ee.
     rewrite* (@subst_ee_intro x).
     eapply chk_sub; eauto.
   * assert (typing G (e_ann (e_ann (e_abs e0) (t_arrow A0 B0)) A1) infer A1).
    constructor.
    eapply chk_sub; eauto.
    forwards*: typing_through_subst_ee.
    rewrite* (@subst_ee_intro x).
    eapply chk_sub; eauto.
  + eapply typ_app; eauto.
    inverts Typ2. inverts H.
    eapply chk_sub; eauto. 
 - forwards*: IHTyp.
 - inverts* Red.
  + pick_fresh y.
    assert (y \notin L) by auto.
    lets: H y H4.
    assert (G & y ~: A = G & y ~: A & empty).
    rewrite* concat_empty_r.
    rewrite H6 in H5.
    assert (G = G & empty).
    rewrite* concat_empty_r.
    rewrite H7.
    dependent destruction H13.
   * assert (typing G (e_lit i5) infer t_int). apply typ_lit.
    forwards*: typing_regular.
    forwards*: typing_through_subst_ee .
    rewrite* (@subst_ee_intro y).
   * assert (typing G (e_ann (e_abs e) (t_arrow A0 B0)) infer (t_arrow A0 B0)). apply typ_ann.
    do 3 dependent destruction Typ.
    dependent destruction Typ.
    eapply typ_abs; eauto.
    forwards*: typing_through_subst_ee .
    rewrite* (@subst_ee_intro y).
  + pick_fresh y.
    assert (y \notin L) by auto.
    lets: H1 y H4.
    assert (G & y ~: B = G & y ~: B & empty).
    rewrite* concat_empty_r.
    rewrite H6 in H5.
    assert (G = G & empty).
    rewrite* concat_empty_r.
    rewrite H7.
    dependent destruction H13.
   * assert (typing G (e_lit i5) infer t_int). apply typ_lit.
    forwards*: typing_regular.
    forwards*: typing_through_subst_ee.
    rewrite* (@subst_ee_intro y).
   * assert (typing G (e_ann (e_abs e) (t_arrow A0 B0)) infer (t_arrow A0 B0)).
    constructor.
    do 3 dependent destruction Typ.
    dependent destruction Typ.
    eapply typ_abs; eauto.
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
    subst. assert (B <: (t_arrow U1 U2)). { 
    eapply sub_transitivity. apply H. apply EQT. }
   eapply IHTyp. apply Val. apply H0. reflexivity.
Qed.

Lemma canonical_form_abs_value : forall t U1 U2,
  value t -> typing empty t infer (t_arrow U1 U2) -> 
  exists V, exists e1, exists V1, exists V2, t = (e_ann (e_ann (e_abs e1) (t_arrow V V1)) V2).
Proof.
  introv Val Typ. 
  gen_eq T: (t_arrow U1 U2). intro st.
   assert (T <: (t_arrow U1 U2)). 
{ rewrite st; apply sub_refl. }
  clear st. gen_eq E: (@empty typ).  gen U1 U2.
  induction Typ; introv EQT EQE;
   try solve [ inverts* Val | inverts* EQT ].
   inverts* Val. inverts* H0.
   inverts* Typ. inverts* H.
   eapply sub_transitivity in EQT; eauto. inversion EQT.
    subst. assert (B <: (t_arrow U1 U2)). { 
    eapply sub_transitivity. apply H. apply EQT. }
   eapply IHTyp. apply Val. apply H0. reflexivity.
Qed.

Lemma check_or_typ : forall E e A B dir,  
   value e ->
   A *s B ->
   typing E e check (t_union A B) ->
   typing E e dir A \/ typing E e dir B.
Proof.
  intros.
  inductions H1.
  inductions H1; try solve [ inverts* H | inverts* H0 | inverts* H1].
  inverts* H. inverts* H4.
Admitted.

Lemma progress : forall e dir T,
typing empty e dir T -> value e \/ exists e', e --> e'.
Proof.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
 - right*.
 - apply binds_empty_inv in H0. inversion H0.
 - forwards*: IHTyp. destruct H.
  + inverts* H.
  + destruct H as [e']. right.
    exists (e_ann e' A). apply* step_ann. admit.
 - right.  destruct* IHTyp1 as [Val1 | [e1' Rede1']].
  + destruct* IHTyp2 as [Val2 | [e2' Rede2']].
    dependent destruction Val1.
    dependent destruction H. inverts* Typ1. inverts* H1. inverts* H. inversion H0.
    inverts Typ1.

    (*lets: canonical_form_abs_value e1 A B Val1 Typ1.
    destruct H as [V [e [V1 [V2]]]].
    subst. inverts* Typ1.*)
    exists (e_ann (open_exp_wrt_exp e (e_ann e2 A1)) B). 
    eapply step_beta; eauto.
    inductions Val2. inverts* H0. admit. admit.
    exists (e_app e1 e2'). eapply step_appr; eauto. admit.
  + exists (e_app e1' e2). apply* step_appl.
    forwards*: typing_regular Typ2.
 - destruct~ IHTyp.
 - pick_fresh y. assert (y \notin L) by auto.
   lets: H y H1. admit.
 - right. destruct* IHTyp.
  + eapply check_or_typ with (dir:=check) in Typ; eauto.
    destruct Typ.
   * inverts* H4.
     inverts* H5. inverts* H4.
     forwards*: pexpr_inf_typ H9.
     destruct H4 as [S [H4 H5]].
     exists (open_exp_wrt_exp e1 (e_ann (e_ann p B0) A)).
     assert (S <: A). eapply sub_transitivity; eauto.
     clear H5 H7.
     pick_fresh y.
     assert (y \notin L) by auto.
     lets: H y H5.
     eapply step_typeofl; eauto.
     admit. admit. admit.
     inverts* H6. inverts* H4. admit. admit.
   * admit.
  + admit.
Admitted.

Ltac solve_by_inverts_step :=
  auto;
  match goal with
  | Hstp : (e_ann (e_abs ?e) ?T) --> ?E |- _ =>
      solve [inverts Hstp]
  | Hstp : ?e --> ?e',
    Hv : value ?e |- _ => solve [inverts Hv; inverts Hstp;
      solve_by_inverts_step]
  | Hpv : pexpr (e_ann ?e ?T) |- _ => solve [inverts Hpv]
  | Hpv : pexpr (e_app ?e1 ?e2) |- _ => solve [inverts Hpv]
  end.

Lemma pexpr_rexpr_false : forall e, rexpr e -> pexpr e -> False.
Proof.
intros.
dependent destruction e; try solve [inversion H | inversion H0 | inversion H1].
Qed.

Lemma value_rexpr_false : forall e, value e -> rexpr e -> False.
Proof.
intros.
dependent destruction e; try solve [inversion H | inversion H0].
Qed.

Lemma determinism : forall e e1 e2,
e --> e1 -> e --> e2 -> e1 = e2.
Proof.
  introv He1. gen e2.
  induction He1; introv He2.
  - inverts* He2.
  - inverts* He2.
   + forwards*: IHHe1. rewrite* H0. 
   + inverts* H2. inverts* H0. inverts* He1. inversion H2. inverts* He1. inversion H4. inverts* H7; inversion H0. 
   + inverts* He1. inversion H3. inverts* H6; inversion H0.
   + inverts* H2. inverts* H0. inverts* He1. inversion H2. inverts* He1. inversion H3. inverts* H6; inversion H0. 
  - inverts* He2.
   + inverts* H. inverts* H5.
     lets: pexpr_rexpr_false p H4 H1; inversion H.
     inverts* H1. inversion H6; inversion H.
     inversion H1.
   + forwards*: IHHe1. rewrite* H1.
   + lets: pexpr_rexpr_false r H0 H5. inversion H1.
   + inversion H0.
  - inverts* He2. 
   + inverts* H5. inverts* H4. inverts* H7; inversion H1.
   + inverts* H6; try solve [inversion H0 | inversion H4].
   + inverts* H0. inverts* H5; inversion H0. 
  - inverts* He2.
   + forwards*: IHHe1. rewrite* H0.
   + inversion H.
   + inversion H.
 - inverts* He2.
   + inverts* H. inverts* H5.
     lets: pexpr_rexpr_false p H4 H1. inversion H.
     inverts* H1. inversion H6; inversion H.
     inversion H1.
   + inversion H4.
   + inverts* H5. inverts H0; inversion H1. 
 - inverts* He2. inversion H2.
 - inverts* He2. inversion H2.
 - inverts* He2.
  + forwards*: IHHe1 H9. rewrite* H1.
  + admit.
  + admit.
Admitted.              
     

     
