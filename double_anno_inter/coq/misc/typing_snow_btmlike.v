Require Import TLC.LibLN.
Require Import syntax_snow_btmlike1.

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

Lemma prevalue_regular : forall t,
  pexpr t -> lc_exp t.
Proof.
  induction 1; autos*.
Qed.

Hint Immediate value_regular prevalue_regular : core.

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
  inverts* H. inverts* H1. inverts* H2. inverts* H1. inverts* H2.
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

(*Lemma chk_sub : forall G e A, typing G e check A -> forall B, A <: B -> typing G e check B.
Proof.
intros G e A Typ1 B Sub.
inductions Typ1.
 - assert (B <: B0).
   eapply sub_transitivity; eauto.
   clear H Sub.
   eapply typ_sub; eauto.
 - assert (typing G (e_abs e) check (t_arrow A B)) by eauto.
   admit.
 - inverts* Typ1.
Admitted.*)

Hint Resolve chk_inf : core.

Lemma pexpr_inf_typ : forall G p A, pexpr p ->
typing G p check A -> exists B, typing G p infer B /\ B <: A.
Proof.
intros G p A Prev Typ.
inductions Prev.
- exists t_int. constructor. constructor.
  apply typing_regular in Typ. destruct~ Typ.
  dependent destruction Typ. dependent destruction Typ. auto.
- dependent destruction Typ.
  dependent destruction Typ.
  exists (t_arrow A0 B). constructor. auto. auto.
Qed.

(*Lemma expr_inf_typ : forall G e dir A e',
typing G e dir A -> e --> e' ->
exists B, typing G e infer B /\ B <: A.
Proof.
intros. lets Typ: H.
inductions H.
- exists* t_int. 
- exists* A. split*. apply sub_refl.
- exists* A. split*. apply sub_refl.
- exists* B. split*. apply sub_refl.
- exists* B.
- inversion H1.
- inverts Typ. exists* B0. admit.
Admitted.*)

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
      inverts Typ1.
      do 3 dependent destruction H5.
      * (* infer lam *)
        dependent destruction H5.
      *
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
      (* prove p:A1 checks *)
        inverts Typ2. inverts H6.
        assert (typing G (e_ann p A1) infer A1).
        assert (B0 <: A1).
        eapply sub_transitivity; eauto.
        forwards*: pexpr_chk_sub H10 H6.
        lets*: typing_through_subst_ee.
        forwards*: H8 H2.
        rewrite* (@subst_ee_intro x).
    + inverts Typ1.
      dependent destruction H4. dependent destruction H4.
      dependent destruction H4. dependent destruction H4.
      constructor.
      inverts H0.
      pick_fresh y. assert (y \notin L) by auto.
      forwards*: H H0.
      assert (G & y ~: A1 = G & y ~: A1 & empty).
      rewrite* concat_empty_r.
      rewrite H3 in H2.
      assert (G = G & empty). rewrite* concat_empty_r.
      rewrite H4.
      inverts Typ2. inverts H6.
      assert (typing G ((e_ann (e_ann (e_abs x) (t_arrow A0 B0)) A1)) infer A1). eauto.
      forwards*: typing_through_subst_ee.
      rewrite* (@subst_ee_intro y).
      forwards*: typing_regular H6.
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

Lemma check_both_disj_false : forall E e A B,
   pexpr e ->
   A *s B ->
   typing E e check A -> typing E e check B -> False.
Proof.
  intros.
  inductions H; try solve [ inverts* H | inverts* H0 | inverts* H2].
  inverts H1. inverts H. inverts H2. inverts H.
  unfold DisjSpec in H0. specialize (H0 t_int).
  forwards*: H0.
  unfold btmLikeSpec in H. unfold not in H.
  inverts H1. inverts H3. inverts H2. inverts H1.
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


Lemma val_pexpr : forall e, lc_exp e -> ~ value e -> pexpr e \/ ~ pexpr e.
Proof.
introv lc. intros.
inductions e; try solve [right; unfold not; intros; inversion H0].
- left*.
- inductions e; try solve [right; unfold not; intros; inverts H0].
  destruct~ IHe0. inversion lc. subst. auto. unfold not. intros. inversion H0.
  inductions t; try solve [ right; unfold not; intros; inversion H1].
  left. apply pexpr_abs. inversion lc; subst. auto.
Qed.


Lemma value_not_value : forall e, lc_exp e -> (value e) \/ (~ (value e)).
Proof.
introv lc.
intros.
inductions e;
try solve [right; unfold not; intros; inversion H].
destruct~ IHe. inverts* lc.
- inverts* H. inverts* H0.
 + right. unfold not. intros. inversion H. subst. inversion H1.
 + right. unfold not. intros. inverts H0. inversion H2.
- apply val_pexpr in H.
  destruct~ H. right. unfold not. intros.
  inverts* H0. inverts* lc. 
Qed.

(* need to be strengthened *)
Lemma progress : forall e dir T,
typing empty e dir T -> (value e) \/ (exists e', e --> e') \/ 
(exists e', e = e_abs e' /\ dir = check).
Proof.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
 - right*.
 - apply binds_empty_inv in H0. inversion H0.
 - destruct* IHTyp.
  + inverts H.
    right. left. exists (e_ann p A). apply* step_rm_ann.
  + destruct H.
   * destruct H.
     dependent destruction Typ. 
     { inverts* Typ.
       { apply binds_empty_inv in H2. inversion H2. }
       { 
         inverts* H0.
         destruct (value_not_value (e_ann (e_ann e0 B) A)).
         forwards*: typing_regular Typ'.
         left*.
         right. left. exists*.
         destruct (value_not_value ((e_ann (e_ann (e_ann p A0) B) A))).
         forwards*: typing_regular Typ'.
         left*.
         right. left.  exists*.
       }
       { right. left. exists (e_ann x A). apply* step_ann.
         unfold not. intros. inversion H3. inversion H5. 
       } 
     }
     { inversion H0. }
     { right. left. exists (e_ann x C). apply* step_ann.
       unfold not. intros. inversion H3. inversion H5. }
   * destruct H. destruct H. subst.
    right. left.
    lets Typ'': Typ.
    inverts Typ. inverts H.
    exists (e_ann (e_ann (e_abs x) (t_arrow A0 B)) (t_arrow A0 B)).
    apply step_lam_ann.
    forwards*: typing_regular Typ''.
 - destruct* IHTyp1.
  + destruct* IHTyp2.
   * inverts* H.
    inverts* H1. inverts Typ1. inverts H2. inverts H. inversion H1.
    inverts Typ1.
    inverts* H0.
   * destruct H0.
   { destruct H0. right. left. exists* (e_app e1 x). }
   { destruct H0. destruct H0.
     inverts H0.
     inverts* Typ1; try solve [inversion H].
     lets H': H.
     inverts H.
     lets H3': H3.
     inverts H0; try solve [inversion H3].
     inverts H; try solve [inversion H3 | inversion H2].
     inverts H3.
     right. left.
     exists* (e_ann (e_ann (open_exp_wrt_exp e (e_ann (e_ann (e_abs x) A) A0)) B1) B). }
  + destruct H. 
    { destruct H.
    right. left. exists (e_app x e2). apply* step_appl.
    forwards*: typing_regular Typ2. }
    { destruct H. destruct H. inversion H0. }
 - destruct~ IHTyp. destruct~ H0. destruct H0. destruct H0. inversion H1.
 - right. right. exists* e.
 - right. destruct* IHTyp.
  + inverts H4. apply check_pexpr_ann in Typ; auto.
    eapply check_or_typ in Typ; eauto.
    destruct Typ.
   * forwards*: pexpr_inf_typ H4.
     destruct H6 as [S [H41 H51]]. left.
     exists (open_exp_wrt_exp e1 (e_ann p A)).
     pick_fresh y.
     assert (y \notin L) by auto.
     lets: H y H6.
     eapply step_typeofl with (C:=S); eauto.
     forwards*: typing_regular Typ'.
     inverts H5; inverts* H41.
   * forwards*: pexpr_inf_typ H4.
     destruct H6 as [S [H41 H51]]. left.
     exists (open_exp_wrt_exp e2 (e_ann p B)).
     pick_fresh y.
     assert (y \notin L) by auto.
     lets: H1 y H6.
     eapply step_typeofr with (C:=S); eauto.
     forwards*: typing_regular Typ'.
     inverts H5; inverts* H41.
  + destruct H4.
   * destruct H4. left.
     exists (e_typeof x A e1 B e2).
     apply step_typeof; auto.
     forwards*: typing_regular Typ'.
   * destruct H4. destruct H4. 
     inverts Typ. inverts H6; try solve [inversion TEMP]. inversion TEMP.
Qed.


Lemma determinism : forall E e e1 e2 A, typing E e check A -> 
e --> e1 -> e --> e2 -> e1 = e2.
Proof.
  introv Typ He1. gen e2 A.
  induction He1; introv Typ He2.
  - inverts* He2.
  - inverts* He2.
   + inverts Typ. inverts H0. eapply typ_sub with (A:=(t_arrow A0 B)) in H7; eauto.
     forwards*: IHHe1. rewrite* H0.
   + inverts* H2. inverts* H0. 
    * inverts* He1. unfold not in H2. 
      assert (value (e_ann (e_lit i5) A0)). eauto.
      apply H2 in H0. inversion H0.
    * inverts* He1. unfold not in H3.
      assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B)) A0)). eauto.
      apply H3 in H0. inversion H0.
      inverts* H6.
   + inverts* He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))). eauto.
     unfold not in H3. apply H3 in H0. inversion H0.
     inverts* H6.
   + inverts* He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))). auto.
     unfold not in H3. apply H3 in H0. inversion H0.
     inversion H5. 
  - inverts* He2.
   + inverts* H. inverts* H0. inverts* H4.
     assert (value (e_ann (e_lit i5) A0)). eauto.
     unfold not in H1. apply H1 in H. inversion H.
     inverts* H4. assert (value (e_ann (e_ann (e_abs e0) (t_arrow A1 B)) A0)) by auto.
     unfold not in H3.
     apply H3 in H0. inversion H0.
     inversion H6.
   + inverts Typ. inverts H0. forwards*: IHHe1 H8. rewrite* H0.
   + inverts H4. inverts He1.
     assert (value (e_ann (e_lit i5) C)) by auto.
     unfold not in H3. apply H3 in H0. inversion H0.
     inverts He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A0 B)) C)) by auto.
     unfold not in H4. apply H4 in H1. inversion H1.
     inversion H6.
   + inverts He1.     
  - inverts* He2.
   + inverts* H5. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))) by auto.
     unfold not in H4. apply H4 in H1. inversion H1.
     inversion H7.
   + inverts* H0. inverts* H5.
     assert (value (e_ann (e_lit i5) C)) by auto.
     unfold not in H2. apply H2 in H0. inversion H0.
     inverts* H5. assert (value (e_ann (e_ann (e_abs e0) (t_arrow A0 B)) C)) by auto.
     unfold not in H4. apply H4 in H0. inversion H0.
     inversion H7.
   + inversion H9.
  - inverts* He2.
   + inverts H5.
     assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))) by auto.
     unfold not in H4. apply H4 in H1. inversion H1. inversion H7.
   + subst. inversion H5.
   + inversion TEMP.    
  - inverts* He2.
   + inverts Typ. inverts H0.
     forwards*: IHHe1. rewrite* H0.
   + inverts* H3. inverts* He1.
     assert (value (e_ann (e_lit i5) A1)) by auto.
     unfold not in H2. apply H2 in H0. inversion H0.
     inverts He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A2 B)) A1)) by auto.
     unfold not in H3. apply H3 in H1. inversion H1.
     inversion H5.
   + inverts* He1. 
  - inverts* He2. inverts H. inverts H4.
    assert (value (e_ann (e_lit i5) A)) by auto.
    unfold not in H1. apply H1 in H. inversion H.
    inverts H4. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) A)) by auto.
    unfold not in H3. apply H3 in H. inversion H.
    inversion H6.
  - inverts* He2. inversion H4.  
  - inverts* He2.
  + inverts Typ. inverts H0.
    forwards*: IHHe1 H5. rewrite* H0.
  + inverts* H8. inverts He1.
    assert (value (e_ann (e_lit i5) D)) by auto.
    unfold not in H2.
    apply H2 in H0. inversion H0.
    inverts He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
    unfold not in H3. apply H3 in H1. inversion H1.
    inversion H5.
  + inverts H8. inverts He1.
    assert (value (e_ann (e_lit i5) D)) by auto.
    unfold not in H2. apply H2 in H0. inversion H0.
    inverts He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
    unfold not in H3. apply H3 in H1. inversion H1.
    inversion H5.
 - inverts* He2.
  + inverts H0. inverts H10. assert (value (e_ann (e_lit i5) D)) by auto.
    unfold not in H4. apply H4 in H0. inversion H0.
    inverts H10. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
    unfold not in H5. apply H5 in H0. inversion H0.
    inversion H7.
  + inverts Typ. inverts H3.
    forwards*: typing_regular. destruct H3.
    inverts* H1. inverts H12.
    assert (typing E (e_lit i5) check A); eauto.
    assert (typing E (e_lit i5) check B); eauto.
    forwards*: check_both_disj_false H1 H5.
    inverts H12.
    unfold DisjSpec in H17. specialize (H17 (t_arrow A1 B0)).
    forwards*: H17.
 - inverts* He2.
  + inverts H1. inverts H10. assert (value (e_ann (e_lit i5) D)) by auto.
    unfold not in H4. apply H4 in H1. inversion H1.
    inverts H10. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
    unfold not in H5. apply H5 in H1. inversion H1.
    inversion H7.
  + inverts Typ. inverts H3.
    forwards*: typing_regular. destruct H3.
    inverts* H1. inverts H12.
    unfold DisjSpec in H17. specialize (H17 t_int).
    forwards*: H17.
    inverts H12.
    unfold DisjSpec in H17. specialize (H17 (t_arrow A1 B0)).
    forwards*: H17.
Qed.


Lemma determinism_dir : forall E e e1 e2 A dir, typing E e dir A -> 
e --> e1 -> e --> e2 -> e1 = e2.
Proof.
  introv Typ He1. gen e2 A dir.
  induction He1; introv Typ He2.
  - inverts* He2.
  - inverts* He2.
   + inverts Typ.
     forwards*: IHHe1. rewrite* H0.
     inverts H0. eapply typ_sub with (A:=(t_arrow A0 B)) in H7; eauto.
     forwards*: IHHe1. rewrite* H0.
   + inverts* H2. inverts* H0. 
    * inverts* He1. unfold not in H2. 
      assert (value (e_ann (e_lit i5) A0)). eauto.
      apply H2 in H0. inversion H0.
    * inverts* He1. unfold not in H3.
      assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B)) A0)). eauto.
      apply H3 in H0. inversion H0.
      inverts* H6.
   + inverts* He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))). eauto.
     unfold not in H3. apply H3 in H0. inversion H0.
     inverts* H6.
   + inverts* He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))). eauto.
     unfold not in H3. apply H3 in H0. inversion H0.
     inversion H5.  
  - inverts* He2.
   + inverts* H. inverts* H0. inverts* H4.
     assert (value (e_ann (e_lit i5) A0)). eauto.
     unfold not in H1. apply H1 in H. inversion H.
     inverts* H4. assert (value (e_ann (e_ann (e_abs e0) (t_arrow A1 B)) A0)) by auto.
     unfold not in H3.
     apply H3 in H0. inversion H0.
     inversion H6.
   + inverts Typ.
     forwards*: IHHe1 H8. rewrite* H0.
     inverts H0. forwards*: IHHe1 H8. rewrite* H0.
   + inverts H4. inverts He1.
     assert (value (e_ann (e_lit i5) C)) by auto.
     unfold not in H3. apply H3 in H0. inversion H0.
     inverts He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A0 B)) C)) by auto.
     unfold not in H4. apply H4 in H1. inversion H1.
     inversion H6.
   + inversion He1.    
  - inverts* He2.
   + inverts* H5. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))) by auto.
     unfold not in H4. apply H4 in H1. inversion H1.
     inversion H7.
   + inverts* H0. inverts* H5.
     assert (value (e_ann (e_lit i5) C)) by auto.
     unfold not in H2. apply H2 in H0. inversion H0.
     inverts* H5. assert (value (e_ann (e_ann (e_abs e0) (t_arrow A0 B)) C)) by auto.
     unfold not in H4. apply H4 in H0. inversion H0.
     inversion H7.
   + inversion H9.
  - inverts* He2.
   + inverts H5. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B1)) (t_arrow A2 B2))) by auto.
     unfold not in H4. apply H4 in H1. inversion H1.
     inversion H7.
   + subst. inversion H5.
   + inversion TEMP.
  - inverts* He2.
   + inverts Typ.
     forwards*: IHHe1. rewrite* H0.
     inverts H0.
     forwards*: IHHe1. rewrite* H0.
   + inverts* H3. inverts* He1.
     assert (value (e_ann (e_lit i5) A1)) by auto.
     unfold not in H2. apply H2 in H0. inversion H0.
     inverts He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A2 B)) A1)) by auto.
     unfold not in H3. apply H3 in H1. inversion H1.
     inversion H5.
   + inverts* He1. 
  - inverts* He2. inverts H. inverts H4.
    assert (value (e_ann (e_lit i5) A)) by auto.
    unfold not in H1. apply H1 in H. inversion H.
    inverts H4. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) A)) by auto.
    unfold not in H3. apply H3 in H. inversion H.
    inversion H6.
  - inverts* He2. inversion H4.  
  - inverts* He2.
  + inverts Typ. inverts H0.
    forwards*: IHHe1 H10. rewrite* H0.
  + inverts* H8. inverts He1.
    assert (value (e_ann (e_lit i5) D)) by auto.
    unfold not in H2.
    apply H2 in H0. inversion H0.
    inverts He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
    unfold not in H3. apply H3 in H1. inversion H1.
    inversion H5.
  + inverts H8. inverts He1.
    assert (value (e_ann (e_lit i5) D)) by auto.
    unfold not in H2. apply H2 in H0. inversion H0.
    inverts He1. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
    unfold not in H3. apply H3 in H1. inversion H1.
    inversion H5.
 - inverts* He2.
  + inverts H0. inverts H10. assert (value (e_ann (e_lit i5) D)) by auto.
    unfold not in H4. apply H4 in H0. inversion H0.
    inverts H10. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
    unfold not in H5. apply H5 in H0. inversion H0.
    inversion H7.
  + inverts Typ. inverts H3.
    forwards*: typing_regular. destruct H3.
    inverts* H1. inverts H12.
    assert (typing E (e_lit i5) check A); eauto.
    assert (typing E (e_lit i5) check B); eauto.
    forwards*: check_both_disj_false H1 H5.
    inverts H12.
    unfold DisjSpec in H18. specialize (H18 (t_arrow A1 B0)).
    forwards*: H18.
 - inverts* He2.
  + inverts H1. inverts H10. assert (value (e_ann (e_lit i5) D)) by auto.
    unfold not in H4. apply H4 in H1. inversion H1.
    inverts H10. assert (value (e_ann (e_ann (e_abs e) (t_arrow A1 B0)) D)) by auto.
    unfold not in H5. apply H5 in H1. inversion H1.
    inversion H7.
  + inverts Typ. inverts H3.
    forwards*: typing_regular. destruct H3.
    inverts* H1. inverts H12.
    unfold DisjSpec in H18. specialize (H18 t_int).
    forwards*: H18.
    inverts H12.
    unfold DisjSpec in H18. specialize (H18 (t_arrow A1 B0)).
    forwards*: H18.
Qed.