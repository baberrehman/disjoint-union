(*
This file contains the updates suggested by Bruno.

Algorithmic disjointnes tomlike depends 
upon the bottom-like-Specs in this approach.
*)

Require Import TLC.LibLN.
Require Import Program.Equality.
(*Implicit Types x : var.*)
(** syntax *)

Inductive typ : Set :=  (*r type *)
 | typ_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and : typ -> typ -> typ.

Inductive exp : Set :=  (*r expression *)
 | e_var_b  : nat -> exp
 | e_var_f  : var -> exp
 | e_lit    : nat -> exp
 | e_ann    : exp -> typ -> exp
 | e_abs    : exp -> exp
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp.

Inductive dirflag : Set :=  (*r typing direction *)
 | infer : dirflag
 | check : dirflag.

(** Binding are mapping to term variables.
 [x ~: T] is a typing assumption *)

 Inductive bind : Set :=
 | bind_typ : typ -> bind.

Notation "x ~: T" := (x ~ T)
 (at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. *)


 Definition env := LibEnv.env typ.

Inductive okt : env -> Prop :=
| okt_empty :
     okt empty
| okt_typ : forall E x T,
     okt E-> x # E -> okt (E & x ~: T).


(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => If (k = nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_ann e A) => e_ann (open_exp_wrt_exp_rec k e_5 e) A
  | (e_abs e) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_exp_wrt_exp_rec k e_5 e) A (open_exp_wrt_exp_rec (S k) e_5 e1) B (open_exp_wrt_exp_rec (S k) e_5 e2)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_exp_wrt_exp t (e_var_f x)) (at level 67).


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall i5,
     (lc_exp (e_lit i5))
 | lc_e_ann : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_ann e A))
 | lc_e_abs : forall (L:vars) (e:exp),
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     (lc_exp e) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e1 (e_var_f x) )  ) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (e_var_f x) )  ) ->
     (lc_exp (e_typeof e A e1 B e2)).
(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => \{}
  | (e_var_f x) => \{x}
  | (e_lit i5) => \{}
  | (e_ann e A) => (fv_exp e)
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_typeof e A e1 B e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (If x = x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_ann e A) => e_ann (subst_exp e_5 x5 e) A
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
end.


(** definitions *)

(* defns PreValue *)
Inductive pexpr : exp -> Prop :=    (* defn pexpr *)
 | pexpr_int : forall i5,
     pexpr (e_lit i5)
 | pexpr_abs : forall (e:exp) (A B:typ),
     lc_exp (e_abs e) ->
     pexpr (e_ann  ( (e_abs e) )  (t_arrow A B)).

(* defns RExpr *)
Inductive rexpr : exp -> Prop :=    (* defn rexpr *)
 | rexpr_app : forall (e1 e2:exp),
     lc_exp e1 ->
     lc_exp e2 ->
     rexpr  ( (e_app e1 e2) )
 | rexpr_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     lc_exp e ->
     lc_exp e1 ->
     lc_exp e2 ->
     rexpr (e_typeof e A e1 B e2).

(* defns Value *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_val : forall (p:exp) (A:typ),
     pexpr p ->
     value (e_ann p A).

(* defns UExpr *)
Inductive uexpr : exp -> Prop :=    (* defn uexpr *)
 | uexpr_rexpr : forall (r:exp),
     rexpr r ->
     uexpr r
 | uexpr_pexpr : forall (p:exp),
     pexpr p ->
     uexpr p
 | uexpr_anno : forall (u:exp) (A:typ),
     uexpr u ->
     uexpr (e_ann u A).

(* defns FindType *)
Inductive findtype : exp -> typ -> Prop :=    (* defn findtype *)
 | findtype_int : forall i5,
     findtype (e_lit i5) t_int
 | findtype_arrow : forall (e:exp) (A B:typ),
     lc_exp (e_abs e) ->
     findtype  ( (e_ann  ( (e_abs e) )  (t_arrow A B)) )   (t_arrow A B).


(* defns Subtyping *)
Reserved Notation "A <: B" (at level 80).
Inductive subtyping : typ -> typ -> Prop :=    (* defn subtyping *)
 | s_top : forall A, A <: typ_top
 | s_btm : forall (A:typ),
     t_bot <: A
 | s_int :
     subtyping t_int t_int
 | s_arrow : forall (A1 A2 B1 B2:typ),
     B1 <: A1 ->
     A2 <: B2 ->
     (t_arrow A1 A2) <: (t_arrow B1 B2)
 | s_ora : forall (A1 A2 A:typ),
     A1 <: A ->
     A2 <: A ->
     (t_union A1 A2) <: A
 | s_orb : forall (A A1 A2:typ),
     A <: A1 ->
     A <: (t_union A1 A2)
 | s_orc : forall (A A1 A2:typ),
     A <: A2 ->
     A <: (t_union A1 A2)
 | s_anda : forall A A1 A2,
     A <: A1 ->
     A <: A2 ->
     A <: (t_and A1 A2)
 | s_andb : forall A1 A2 A,
     A1 <: A ->
     (t_and A1 A2) <: A
 | s_andc : forall A1 A2 A,
     A2 <: A ->
     (t_and A1 A2) <: A
where "A <: B" := (subtyping A B) : env_scope.

Hint Constructors pexpr rexpr value uexpr findtype subtyping lc_exp ok okt.

(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)

Lemma sub_or : forall A B C, (t_union A B) <: C -> A <: C /\ B <: C.
Proof.
intros; inductions H; try solve [split*].
specialize (IHsubtyping A B).
forwards* : IHsubtyping.
specialize (IHsubtyping A B).
forwards* : IHsubtyping.
specialize (IHsubtyping1 A B).
specialize (IHsubtyping2 A B).
forwards*: IHsubtyping1.
Qed.

Lemma sub_and : forall A B C, A <: (t_and B C) -> A <: B /\ A <: C.
Proof.
intros; inductions H; try solve [split*].
specialize (IHsubtyping1 B C).
specialize (IHsubtyping2 B C).
forwards*: IHsubtyping1.
specialize (IHsubtyping B C).
forwards*: IHsubtyping.
specialize (IHsubtyping B C).
forwards*: IHsubtyping.
Qed.

Lemma sub_refl : forall A, A <: A.
  induction A; eauto.
Qed.

Hint Resolve sub_refl.


Lemma sub_transitivity : forall B A C, A <: B -> B <: C -> A <: C.
Proof.
induction B; intros;
generalize H0 H; clear H0; clear H; generalize A; clear A.
- intros; inductions H0; eauto. 
- intros; inductions H; eauto.
- intros; inductions H; eauto.
- induction C; intros; inverts* H0.
  induction A; inverts* H.
- intros. apply sub_or in H0. destruct H0.
  inductions H; eauto.
- intros. apply sub_and in H. destruct H.
  inductions H0; eauto.
Qed.


(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
| o_top : Ord typ_top
| o_int : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2).
(*| o_union : forall t1 t2, Ord t1 -> Ord t2 -> Ord (t_union t1 t2).*)

Hint Constructors Ord.

(* Isomorphic Definition *)

Definition  Isomorphic A B := A <: B /\ B <: A.

(****************************************)
(*********  Bottom-Like Specs   *********)
(****************************************)

 (*Definition btmLikeSpec C := (exists A B, 
 Isomorphic (t_and A B) C -> (not (A <: B) /\ not (B <: A))) \/
C <: t_bot.*)

Definition btmLikeSpec C := forall A, Ord A -> not (A <: C).

(*Definition btmLikeSpec C := (forall A B,  Isomorphic (t_and A B) C -> 
btmLikeSpec A \/ btmLikeSpec B \/ (not (A <: B) /\ not (B <: A))) \/ C <: t_bot.*)

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec A B := forall C, C <: A /\ C <: B -> btmLikeSpec C.

Notation "A *s B" := (DisjSpec A B) (at level 80).

(* defns BottomLike *)
Inductive bottomlike : typ -> Prop :=    (* defn bottomlike *)
 | bl_bot :
     bottomlike t_bot
 | bl_or : forall (A B:typ),
     bottomlike A ->
     bottomlike B ->
     bottomlike (t_union A B)
 | bl_anda : forall A B,
     bottomlike A ->
     bottomlike (t_and A B)
 | bl_andb : forall A B,
     bottomlike B ->
     bottomlike (t_and A B)
 | bl_andsub : forall A B,
     A *s B ->
     bottomlike (t_and A B).

Hint Constructors bottomlike.

(**********************************)
(****  Bottom-Like Properties  ****)
(**********************************)


Lemma btm_sub_btmlike : forall A, A <: t_bot -> bottomlike A.
Proof.
intros. inductions H; eauto.
Qed.

Lemma btm_like_and : forall A B, bottomlike (t_and A B) ->
bottomlike A \/ bottomlike B \/ A *s B.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

Lemma BL_soundness : forall A, bottomlike A -> btmLikeSpec A.
Proof.
intros. inductions H; unfold btmLikeSpec in *; eauto; intros.
- unfold not. intros.
  inductions H; try solve [inversion H0].
- specialize (IHbottomlike1 A0).
  specialize (IHbottomlike2 A0).
  forwards*: IHbottomlike1.
  forwards*: IHbottomlike2.
  clear IHbottomlike1 IHbottomlike2.
  unfold not. intros.
  dependent induction H4; eauto.
  inversion H1. inversion H1. inversion H1.
- specialize (IHbottomlike A0).
  forwards*: IHbottomlike.
  unfold not in *. intros.
  apply H1.
  apply sub_and in H2. destruct H2. auto.
- specialize (IHbottomlike A0).
  forwards*: IHbottomlike.
  unfold not in *. intros.
  apply H1.
  apply sub_and in H2. destruct H2. auto.
- unfold DisjSpec in H.
  unfold btmLikeSpec in H.
  unfold not in *.
  intros.
  dependent induction H1; eauto.
  inversion H0. inversion H0. inversion H0.
Qed.

Lemma top_and_isomorphic : Isomorphic (t_and typ_top typ_top) typ_top.
Proof.
unfold Isomorphic.
split.
constructor.
constructor; auto.
Qed.

Lemma int_and_isomorphic : Isomorphic (t_and t_int t_int) t_int.
Proof.
unfold Isomorphic.
split.
constructor; auto.
constructor; auto.
Qed.

Lemma arrow_and_isomorphic : forall A B, 
Isomorphic (t_and (t_arrow A B) (t_arrow A B)) (t_arrow A B).
Proof.
unfold Isomorphic.
split.
constructor; auto.
constructor; auto.
Qed.

Lemma ord_sub_bot_false : forall A, Ord A -> A <: t_bot -> False.
Proof.
  intros.
  dependent induction H; inversion H0.
Qed.


(*Lemma not_sub_and : forall A1 A2, forall A, Ord A ->
not (A <: (t_and A1 A2)) -> not((A <: A1) /\ (A <: A2)).
Proof.
  intros.
  unfold not in *. intros.
  apply H0; destruct~ H1.
Qed.

Lemma btm_like_spec_and : forall A1 A2, btmLikeSpec (t_and A1 A2) ->
  btmLikeSpec A1 \/ btmLikeSpec A2 \/
  not (A1 <: A2) /\ not (A2 <: A1).
intros.
unfold btmLikeSpec in *.
unfold not in *.
eapply not_sub_and in H; eauto.*)


Lemma not_sub_and : forall A1 A2, forall A, Ord A ->
not (A <: (t_and A1 A2)) -> not((A <: A1) /\ (A <: A2)).
Proof.
  intros.
  unfold not in *. intros.
  apply H0; destruct~ H1.
Qed.

Lemma btm_like_spec_and : forall A1 A2, btmLikeSpec (t_and A1 A2) ->
  A1 *s A2.
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold DisjSpec.
  intros.
  destruct H0.
  unfold btmLikeSpec.
  intros.
  unfold not in *.
  intros.
  eapply H; eauto.
  assert (C <: (t_and A1 A2)) by auto.
  eapply sub_transitivity in H4; eauto.
Qed.

Lemma BL_completeness : forall A, btmLikeSpec A -> bottomlike A.
Proof.
inductions A; unfold btmLikeSpec; intro; eauto.
 - specialize (H typ_top).
   forwards*: H.
   unfold not in H0.
   forwards*: H0.
 - specialize (H t_int).
   forwards*: H.
   unfold not in H0.
   forwards*: H0.
 - specialize (H (t_arrow A1 A2)).
   forwards*: H.
   unfold not in H0.
   forwards*: H0.
 - constructor.
  + apply IHA1. unfold btmLikeSpec.
   intros.
   unfold not in *. intros.
   specialize (H A).
   assert (A <: (t_union A1 A2)). eauto.
   apply* H.
  + apply IHA2. unfold btmLikeSpec.
   intros.
   unfold not in *. intros.
   specialize (H A).
   assert (A <: (t_union A1 A2)). eauto.
   apply* H.
 - assert (btmLikeSpec (t_and A1 A2)) by auto.
   apply btm_like_spec_and in H0.
   apply bl_andsub; auto.
Qed.


(*************************************)
(*****  Disjointness Properties  *****)
(*************************************)


(* defns Disjointness *)
Reserved Notation "A *a B" (at level 80).
Inductive disjointness : typ -> typ -> Prop :=    (* defn disjointness *)
 | ad_btmr : forall (A:typ),
      A *a t_bot
 | ad_btml : forall (A:typ),
     t_bot *a A
 | ad_intl : forall (A B:typ),
     t_int *a (t_arrow A B)
 | ad_intr : forall (A B:typ),
     (t_arrow A B) *a t_int
 | ad_orl : forall (A B C:typ),
     A *a C ->
     B *a C ->
     (t_union A B) *a C
 | ad_orr : forall (C A B:typ),
     A *a C ->
     B *a C ->
     C *a (t_union A B)
 | ad_andl1 : forall A B C,
     A *a C ->
     (*B *a C ->*)
     (t_and A B) *a C
 | ad_andl2 : forall A B C,
     (*A *a C ->*)
     B *a C ->
     (t_and A B) *a C
 | ad_andr1 : forall A B C,
     A *a C ->
     (*B *a C ->*)
     C *a (t_and A B)
 | ad_andr2 : forall A B C,
     (*A *a C ->*)
     B *a C ->
     C *a (t_and A B)
 | ad_dis_specl : forall A B,
     btmLikeSpec A ->
     A *a B
 | ad_dis_specr : forall A B,
     btmLikeSpec B ->
     A *a B

where "A *a B" := (disjointness A B).

Hint Constructors disjointness.

(* defns Typing *)
Inductive typing : env -> exp -> dirflag -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:env) i5,
      okt  G  ->
     typing G (e_lit i5) infer t_int
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

Hint Constructors typing.

(* defns Reduction *)
Reserved Notation "e --> e'" (at level 80).
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_int : forall i5,
     step (e_lit i5) (e_ann (e_lit i5) t_int)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_app e1 e2) (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     step e e' ->
     step (e_app v e) (e_app v e')
 | step_beta : forall (e:exp) (A1 B1 A2 B2:typ) (p:exp) (C:typ),
     lc_exp (e_abs e) ->
     pexpr p ->
     (e_app  ( (e_ann (e_ann  ( (e_abs e) )  (t_arrow A1 B1)) (t_arrow A2 B2)) ) ( (e_ann p C) ) ) --> (e_ann (e_ann  (  (open_exp_wrt_exp  e (e_ann p A1) )  )  B1) B2)
 | step_beta_abs : forall (e:exp) (A1 B1 A2 B2:typ) (p:exp) (C:typ) x,
     lc_exp (e_abs e) ->
     p = (e_abs x) ->
     (e_app  ( (e_ann (e_ann  ( (e_abs e) )  (t_arrow A1 B1)) (t_arrow A2 B2)) ) ( p ) ) --> (e_ann (e_ann  (  (open_exp_wrt_exp  e (e_ann (e_ann p A2) A1) )  )  B1) B2)
 | step_ann : forall (e:exp) (A:typ) (e':exp),
      not ( value (e_ann e A) )  ->
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

Hint Constructors step.

(** infrastructure *)

Lemma not_sub_or_inv : forall A A1 A2, Ord A -> not (A <: A1) -> not (A <: A2) -> not (A <: (t_union A1 A2)).
Proof.
  intros.
  unfold not in *.
  intros. inductions H; inverts* H2.
Qed.

Lemma btm_like_spec_union_inv : forall A B, btmLikeSpec A -> btmLikeSpec B -> btmLikeSpec (t_union A B).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros.
  lets: H A0 H1.
  lets: H0 A0 H1.
  apply* not_sub_or_inv.
Qed.

Lemma btm_sub : forall A, t_bot <: A.
Proof.
  intros; auto.
Qed.

Lemma not_sub_and1_inv : forall A A1 A2, Ord A -> not (A <: A1) -> not (A <: (t_and A1 A2)).
Proof.
  intros.
  unfold not in *.
  intros. inductions H; inverts* H1.
Qed.

Lemma not_sub_and2_inv : forall A A1 A2, Ord A -> not (A <: A2) -> not (A <: (t_and A1 A2)).
Proof.
  intros.
  unfold not in *.
  intros. inductions H; inverts* H1.
Qed.

Lemma btm_like_spec_and1_inv : forall A B, btmLikeSpec A -> btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros.
  lets: H A0 H0.
  apply* not_sub_and1_inv.
Qed.

Lemma btm_like_spec_and2_inv : forall A B, btmLikeSpec B -> btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros.
  lets: H A0 H0.
  apply* not_sub_and2_inv.
Qed.

Lemma btm_spec : btmLikeSpec t_bot.
Proof.
  unfold btmLikeSpec.
  intros.
  unfold not.
  intros.
  inductions H; inverts* H0.
Qed.

Lemma ord_sub_union : forall A, Ord A -> forall A1 A2, A <: t_union A1 A2 -> A <: A1 \/ A <: A2.
Proof.
  intros A H.
  dependent induction H; intros.
  inverts* H.
  inverts* H.
  inverts* H.
Qed.

Lemma btm_like_spec_btm_inter : forall A, btmLikeSpec (t_and A t_bot).
Proof.
  intros.
  unfold btmLikeSpec. intros.
  unfold not. intros.
  apply sub_and in H0.
  destruct H0.
  apply ord_sub_bot_false in H1; auto.
Qed.


Lemma sub_int_arrow : forall A B, A <: t_int -> forall A1 A2, B <: (t_arrow A1 A2) -> btmLikeSpec (t_and A B).
Proof.
  intros.
  inductions H.
  - apply* btm_like_spec_and1_inv. apply btm_spec.
  - inductions H0.
   + apply btm_like_spec_btm_inter.
   + unfold btmLikeSpec. intros.
     unfold not. intros.
     inverts* H; inverts* H0. inversion H3. inversion H4. inversion H3.
   + forwards*: IHsubtyping1 A1 A2.
     forwards*: IHsubtyping2 A1 A2.
     unfold btmLikeSpec in *.
     intros.
     clear IHsubtyping1 IHsubtyping2.
     unfold not. intros.
     forwards*: H H1.
     forwards*: H0 H1.
     unfold not in *.
     apply sub_and in H2.
     destruct H2.
     apply ord_sub_union in H5; auto.
     destruct H5.
     apply H3. apply s_anda; auto.
     apply H4. apply s_anda; auto.
   + forwards*: IHsubtyping A1 A2.
     unfold btmLikeSpec in *.
     intros.
     unfold not in *. intros.
     lets: H A H1.
     apply sub_and in H2.
     destruct H2.
     apply sub_and in H4.
     destruct H4.
     apply H3.
     apply s_anda; auto.
   + forwards*: IHsubtyping A1 A2.
     unfold btmLikeSpec in *. intros.
     unfold not in *. intros.
     eapply H; eauto.
     apply sub_and in H2.
     destruct H2.
     apply sub_and in H3.
     destruct H3.
     apply s_anda; auto.
  - forwards*: IHsubtyping1 A0 A3.
    forwards*: IHsubtyping2 A0 A3.
    unfold btmLikeSpec in *.
    intros.
    unfold not in *.
    intros.
    apply sub_and in H5.
    destruct H5.
    apply ord_sub_union in H5; auto.
    destruct H5.
    eapply H2; eauto.
    eapply H3; eauto.
  - forwards*: IHsubtyping A0 A3.
    unfold btmLikeSpec in *.
    unfold not in *.
    intros.
    eapply H1; eauto.
    apply sub_and in H3.
    destruct H3.
    apply sub_and in H3. destruct H3.
    apply s_anda; auto.
  - forwards*: IHsubtyping A0 A3.
    unfold btmLikeSpec in *.
    unfold not in *.
    intros.
    eapply H1; eauto.
    apply sub_and in H3. destruct H3.
    eapply sub_and in H3. destruct H3.
    apply s_anda; auto.
Qed.

Lemma sym_btm_like : forall A B, btmLikeSpec (t_and A B) -> btmLikeSpec (t_and B A).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros.
  unfold not in *.
  intros.
  eapply H; eauto.
  apply sub_and in H1.
  destruct H1.
  apply s_anda; auto.
Qed.


Lemma disj_btm_like_spec : forall A B, A *s B ->
  forall C, C <: A -> C <: B -> btmLikeSpec C.
Proof.
 intros.
 unfold DisjSpec in H.
 apply H; eauto.
Qed.

Lemma disj_sub_union : forall A B C, A *s C -> B *s C -> t_union A B *s C.
Proof.
  intros.
  unfold DisjSpec in *. intros.
  unfold btmLikeSpec in *. intros.
  destruct H1.
  unfold not. intros.
  specialize (H A0).
  eapply sub_transitivity in H3; eauto.
  eapply sub_transitivity in H1; eauto.
  lets: ord_sub_union A0 H2 A B H1.
  destruct H5.
  unfold not in *.
  assert (A0 <: A /\ A0 <: C) by auto.
  lets: H H6.
  forwards*: H7 H2.
  specialize (H0 A0).
  assert (A0 <: B /\ A0 <: C) by auto.
  lets: H0 H6.
  unfold not in H7.
  forwards*: H7 H2.
Qed.


Lemma Disj_soundness : forall A B, A *a B -> A *s B.
intros. dependent induction H; unfold DisjSpec; intros; eauto.
- destruct H. dependent induction H0; eauto.
  apply btm_spec.
  apply sub_or in H. destruct H.
  forwards*: IHsubtyping1.
  forwards*: IHsubtyping2.
  apply* btm_like_spec_union_inv.
  forwards*: IHsubtyping.
  assert (t_bot <: A) by auto.
  eapply sub_transitivity in H1; eauto.
  apply* btm_like_spec_and1_inv.
  forwards*: IHsubtyping.
  assert (t_bot <: A) by auto.
  eapply sub_transitivity in H1; eauto.
  apply* btm_like_spec_and2_inv.
- destruct H. dependent induction H; eauto.
  apply btm_spec.
  apply sub_or in H1. destruct H1.
  forwards*: IHsubtyping1.
  forwards*: IHsubtyping2.
  apply* btm_like_spec_union_inv.
  forwards*: IHsubtyping.
  assert (t_bot <: A) by auto.
  eapply sub_transitivity in H1; eauto.
  apply* btm_like_spec_and1_inv.
  forwards*: IHsubtyping.
  assert (t_bot <: A) by auto.
  eapply sub_transitivity in H1; eauto.
  apply* btm_like_spec_and2_inv.
- destruct H. induction C; try (dependent destruction H); eauto.
  + inversion H0.
  + apply btm_spec.
  + inverts* H1.
    forwards*: IHC1.
    forwards*: IHC2.
    apply* btm_like_spec_union_inv.
  + inverts* H0.
    forwards*: IHC1.
    apply* btm_like_spec_and1_inv.
    eapply sub_int_arrow; eauto.
  + inverts* H0.
    apply sym_btm_like.
    eapply sub_int_arrow; eauto.
    forwards*: IHC2.
    apply* btm_like_spec_and2_inv.
- destruct H. induction C; try (dependent destruction H0); eauto.
  + inversion H.
  + apply btm_spec.
  + inverts* H.
    forwards*: IHC1.
    forwards*: IHC2.
    apply* btm_like_spec_union_inv.
  + inverts* H.
    forwards*: IHC1.
    apply* btm_like_spec_and1_inv.
    eapply sub_int_arrow; eauto.
  + inverts* H.
    apply sym_btm_like.
    eapply sub_int_arrow; eauto.
    forwards*: IHC2.
    apply* btm_like_spec_and2_inv.
    (* difficult case -- union with intersection *)
- destruct H1. inductions C0; try solve [inverts* H1].
 + apply sub_or in H1.
   destruct H1.
   apply sub_or in H2. destruct H2.
   lets: IHC0_1 H1 H2.
   lets: IHC0_2 H3 H4.
   apply* btm_like_spec_union_inv.
 + lets: disj_sub_union A B C IHdisjointness1 IHdisjointness2.
   lets: disj_btm_like_spec (t_union A B) C H3 (t_and C0_1 C0_2).
   lets: H4 H1 H2. auto.
    (* difficult case -- union with intersection *)
- destruct H1. inductions C0; try solve [inverts* H2].
  + apply sub_or in H2. destruct H2.
    apply sub_or in H1. destruct H1.
    lets: IHC0_1 H1 H2.
    lets: IHC0_2 H4 H3.
    apply* btm_like_spec_union_inv.
  + lets: disj_sub_union A B C IHdisjointness1 IHdisjointness2.
    lets: disj_btm_like_spec (t_union A B) C H3 (t_and C0_1 C0_2).
    lets: H4 H2 H1. auto.
- destruct H0.
  unfold DisjSpec in IHdisjointness.
  apply IHdisjointness.
  split; auto.
  apply sub_and in H0. destruct H0; auto.
- destruct H0.
  unfold DisjSpec in IHdisjointness.
  apply IHdisjointness.
  split; auto.
  apply sub_and in H0.
  destruct H0; auto.
- destruct H0.
  apply sub_and in H1.
  destruct H1.
  unfold DisjSpec in IHdisjointness.
  apply IHdisjointness; auto.
- destruct H0.
  apply sub_and in H1.
  destruct H1.
  unfold DisjSpec in IHdisjointness.
  apply IHdisjointness; auto.
- destruct H0.
  unfold btmLikeSpec in *. unfold not in *.
  intros.
  assert (A0 <: A). eapply sub_transitivity; eauto.
  forwards*: H H2.
- destruct H0.
  unfold btmLikeSpec in *. unfold not in *.
  intros.
  assert (A0 <: B). eapply sub_transitivity; eauto.
  forwards*: H H2.
Qed.

Lemma BL_disj_spec : forall A, btmLikeSpec A -> forall B, A *s B.
  intros.
  unfold btmLikeSpec in H.
  unfold not in H.
  unfold DisjSpec. intros.
  unfold btmLikeSpec. intros.
  unfold not. intros.
  eapply H; eauto.
  destruct H0.
  eapply sub_transitivity; eauto.
Qed.

Lemma disj_btm_spec : forall A B, A *s B -> btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold DisjSpec in H.
  apply H; eauto.
Qed.

Lemma Disj_sym : forall A B, A *a B -> B *a A.
  induction 1; eauto.
Defined.

Lemma test : forall A B, A *s B -> btmLikeSpec (t_and A B).
Proof.
  intros. unfold DisjSpec in H.
  unfold btmLikeSpec in *. unfold not in *.
  intros.
  specialize (H (t_and A B)).
  eapply H; eauto.
Qed.


Lemma BL_disj : forall A, bottomlike A -> forall B, A *a B.
Proof.
  intros A H1.
  inductions H1; intros; eauto.
  apply ad_dis_specl. eauto.
Qed.

Lemma disj_union_inv : forall A B C, A *a (t_union B C) ->
  A *a B /\ A *a C.
Proof.
intros.
inductions H; eauto.
specialize (IHdisjointness1 B C).
destruct IHdisjointness1; auto.
specialize (IHdisjointness2 B C).
destruct IHdisjointness2; auto.
split; apply* Disj_sym.
specialize (IHdisjointness B C).
destruct IHdisjointness; auto.
specialize (IHdisjointness B C).
destruct IHdisjointness; auto.
apply BL_completeness in H. inverts* H.
split; apply Disj_sym; apply BL_disj; auto.
Qed.


Lemma ord_sub_int_arrow_false : forall A B A1 A2, Ord A -> A <: B -> B <: t_int -> B <: t_arrow A1 A2 -> False.
Proof.
  intros.
  lets: sub_int_arrow B B H1 A1 A2.
  forwards*: H3.
  unfold btmLikeSpec in H4.
  unfold not in H4.
  eapply H4; eauto.
Qed.

(***************************)
(*

Important lemma for completeness.

\/ A B, botlike((A & B) & Int) -> botlike (A & Int) \/ botlike (B & Int)

Below is the proof of this lemma.

Difficult to prove.

*)
(***************************)

Lemma btm_like_spec_int_and : forall A B, btmLikeSpec (t_and (t_and A B) t_int) -> 
  btmLikeSpec (t_and A t_int) \/ btmLikeSpec (t_and B t_int).
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
  inductions A; eauto.
  - right. intros.
    apply sub_and in H1. destruct H1.
    forwards*: H A H0.
  - right. intros.
    apply sub_and in H1. destruct H1.
    forwards*: H A H0.
  - left. intros.
    apply sub_and in H1. destruct H1.
    forwards*: ord_sub_bot_false A H0.
  - clear IHA1 IHA2.
    left. intros. apply sub_and in H1.
    destruct H1.
    lets: sub_int_arrow A A H2 H1.
    unfold btmLikeSpec in H3. unfold not in H3.
    lets: H3 A H0.
    apply H4; eauto.
  - specialize (IHA1 B).
    destruct IHA1. intros. apply sub_and in H1. destruct H1.
    apply sub_and in H1. destruct H1.
    eapply H; eauto.
    specialize (IHA2 B).
    destruct IHA2. intros.
    apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H; eauto.
    left. intros.
    apply sub_and in H3. destruct H3.
    lets: ord_sub_union A H2 A1 A2 H3.
    destruct H5.
    eapply H0; eauto.
    eapply H1; eauto.
    right. auto.
    specialize (IHA2 B). destruct IHA2.
    intros. apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H; eauto.
    right. auto. right. auto.
  - specialize (IHA1 (t_and A2 B)). destruct IHA1.
    specialize (IHA2 (t_and A1 B)). destruct IHA2.
    intros. apply sub_and in H1. destruct H1.
    apply sub_and in H1. destruct H1.
    apply sub_and in H3. destruct H3.
    eapply H; eauto.
    intros. apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    apply sub_and in H4. destruct H4.
    eapply H0; eauto.
    intros. apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    apply sub_and in H4. destruct H4.
    eapply H0; eauto.
    specialize (IHA2 A1). destruct IHA2.
    intros.
    apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H0; eauto.
    left. intros.
    apply sub_and in H3. destruct H3.
    apply sub_and in H3. destruct H3.
    eapply H0; eauto.
    left. intros.
    apply sub_and in H3. destruct H3.
    apply sub_and in H3. destruct H3.
    eapply H0; eauto.
    specialize (IHA2 B). destruct IHA2.
    intros.
    apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H0; eauto.
    left. intros.
    apply sub_and in H3. destruct H3.
    apply sub_and in H3. destruct H3.
    eapply H1; eauto.
    right. auto.
Qed.


(***************************)
(*

Important lemma for completeness.

\/ A B, botlike((A & B) & (A1 -> B1)) -> botlike (A & (A1 -> B1)) \/ botlike (B & (A1 -> B1))

Below is the proof of this lemma.

Difficult to prove.

*)
(***************************)

Lemma btm_like_spec_arrow_and : forall A B A1 B1, btmLikeSpec (t_and (t_and A B) (t_arrow A1 B1)) -> 
  btmLikeSpec (t_and A (t_arrow A1 B1)) \/ btmLikeSpec (t_and B (t_arrow A1 B1)).
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
  inductions A; eauto.
  - right. intros.
    apply sub_and in H1. destruct H1.
    forwards*: H A H0.
  - left. intros.
    apply sub_and in H1. destruct H1.
    lets: sub_int_arrow A A H1 A1 B1.
    lets: H3 H2.
    unfold btmLikeSpec in H4. unfold not in H4.
    forwards*: H4 H0.
  - left. intros.
    apply sub_and in H1. destruct H1.
    forwards*: ord_sub_bot_false A H0.
  - specialize (IHA1 B (t_union A1 A0) t_bot). destruct IHA1.
    intros. apply sub_and in H1. destruct H1.
    apply sub_and in H1. destruct H1.
    eapply H; eauto.
    apply s_anda. apply s_anda; auto.
    assert ( t_arrow (t_union A1 A0) t_bot <: (t_arrow A1 A2)). eauto.
    eapply sub_transitivity; eauto.
    assert ( t_arrow (t_union A1 A0) t_bot <: (t_arrow A0 B1)). eauto.
    eapply sub_transitivity; eauto.
    specialize (IHA2 A1 (t_union A1 A0) t_bot). destruct IHA2.
    intros.
    apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H0; eauto.
    admit.
    admit.
    admit.
  - specialize (IHA1 B A0 B1).
    destruct IHA1. intros. apply sub_and in H1. destruct H1.
    apply sub_and in H1. destruct H1.
    eapply H; eauto.
    specialize (IHA2 B A0 B1).
    destruct IHA2. intros.
    apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H; eauto.
    left. intros.
    apply sub_and in H3. destruct H3.
    lets: ord_sub_union A H2 A1 A2 H3.
    destruct H5.
    eapply H0; eauto.
    eapply H1; eauto.
    right. auto.
    specialize (IHA2 B A0 B1). destruct IHA2.
    intros. apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H; eauto.
    right. auto. right. auto.
  - specialize (IHA1 (t_and A2 B) A0 B1). destruct IHA1.
    specialize (IHA2 (t_and A1 B) A0 B1). destruct IHA2.
    intros. apply sub_and in H1. destruct H1.
    apply sub_and in H1. destruct H1.
    apply sub_and in H3. destruct H3.
    eapply H; eauto.
    intros. apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    apply sub_and in H4. destruct H4.
    eapply H0; eauto.
    intros. apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    apply sub_and in H4. destruct H4.
    eapply H0; eauto.
    specialize (IHA2 A1 A0 B1). destruct IHA2.
    intros.
    apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H0; eauto.
    left. intros.
    apply sub_and in H3. destruct H3.
    apply sub_and in H3. destruct H3.
    eapply H0; eauto.
    left. intros.
    apply sub_and in H3. destruct H3.
    apply sub_and in H3. destruct H3.
    eapply H0; eauto.
    specialize (IHA2 B A0 B1). destruct IHA2.
    intros.
    apply sub_and in H2. destruct H2.
    apply sub_and in H2. destruct H2.
    eapply H0; eauto.
    left. intros.
    apply sub_and in H3. destruct H3.
    apply sub_and in H3. destruct H3.
    eapply H1; eauto.
    right. auto. 
Admitted.



Lemma disj_spec_int : forall A1 A2, (t_and A1 A2) *s t_int -> A1 *s t_int \/ A2 *s t_int.
Proof.
  intros.
  unfold DisjSpec in *.
  unfold btmLikeSpec in *.
  unfold not in *.
  specialize (H (t_and (t_and A1 A2) t_int)).
  assert ((t_and (t_and A1 A2) t_int <: t_and A1 A2)) by auto.
  assert (t_and (t_and A1 A2) t_int <: t_int) by auto.
  assert ((t_and (t_and A1 A2) t_int <: t_and A1 A2) /\ (t_and (t_and A1 A2) t_int <: t_int)) by auto.
  lets: H H2.
  clear H H0 H1 H2.
  inductions A1; eauto.
  - inductions A2; eauto.
    + right. intros.
      destruct H.
      assert (A <: t_bot).
      eapply sub_transitivity; eauto.
      lets: ord_sub_bot_false A H0 H4. auto.
    + clear IHA2_1 IHA2_2.
      right. intros. destruct H.
      forwards*: ord_sub_int_arrow_false H1.
    + clear IHA2_1 IHA2_2.
      right. intros. destruct H.
      lets H2': H2. 
      inverts* H2; eauto.
      lets: ord_sub_bot_false A H0 H1. auto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
    + clear IHA2_1 IHA2_2.
      right. intros. destruct H.
      lets H2': H2.
      inverts* H2; eauto.
      lets: ord_sub_bot_false A H0 H1. auto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
  - inductions A2; eauto.
    + right. intros.
      destruct H.
      assert (A <: t_bot).
      eapply sub_transitivity; eauto.
      lets: ord_sub_bot_false A H0 H4. auto.
    + right. intros.
      destruct H.
      lets: ord_sub_int_arrow_false A C A2_1 A2_2 H0.
      lets: H4 H1 H2 H. auto.
    + right. intros. destruct H.
      lets H2': H2.
      dependent destruction H2; eauto.
      forwards*: ord_sub_bot_false A H0 H1.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
    + right. intros. destruct H.
      lets H2': H2.
      dependent destruction H2; eauto.
      forwards*: ord_sub_bot_false A H0 H1.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
  - left. intros. destruct H.
    assert (A <: t_bot ).
    eapply sub_transitivity; eauto.
    forwards*: ord_sub_bot_false A H0 H4.
  - clear IHA1_1 IHA1_2.
    left. intros.
    destruct H.
    lets: ord_sub_int_arrow_false A C A1_1 A1_2 H0.
    lets: H4 H1 H2 H. auto.
  - clear IHA1_1 IHA1_2. inductions A2; eauto.
    + left. intros.
      destruct H.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
    + left. intros.
      destruct H.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H; eauto.
    + right. intros. destruct H.
      assert (A <: t_bot).
      eapply sub_transitivity; eauto.
      forwards*: ord_sub_bot_false A H0 H4.
    + clear IHA2_1 IHA2_2. right. intros.
      destruct H.
      lets: ord_sub_int_arrow_false A C A2_1 A2_2 H0.
      lets: H4 H1 H2 H. auto.
    + clear IHA2_1 IHA2_2.
      apply btm_like_spec_int_and in H3.
      destruct H3.
      left. intros.
      unfold btmLikeSpec in H.
      unfold not in H.
      destruct H0.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H0; eauto.
      right. intros. destruct H0.
      unfold btmLikeSpec in H.
      unfold not in H.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H0; eauto.
    + clear IHA2_1 IHA2_2.
      apply btm_like_spec_int_and in H3.
      destruct H3.
      unfold btmLikeSpec in H.
      unfold not in H.
      left. intros. destruct H0.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H0; eauto.
      unfold btmLikeSpec in H.
      unfold not in H.
      right. intros. destruct H0.
      assert (A <: t_int).
      eapply sub_transitivity; eauto.
      eapply sub_transitivity in H0; eauto.
  - clear IHA1_1 IHA1_2.
    apply btm_like_spec_int_and in H3.
    destruct H3.
    unfold btmLikeSpec in H.
    unfold not in H.
    left. intros. destruct H0.
    assert (A <: t_int).
    eapply sub_transitivity; eauto.
    eapply sub_transitivity in H0; eauto.
    unfold btmLikeSpec in H.
    unfold not in H.
    right. intros. destruct H0.
    assert (A <: t_int).
    eapply sub_transitivity; eauto.
    eapply sub_transitivity in H0; eauto.
Qed.


Lemma disj_spec_arrow : forall A1 A2 B1 B2, (t_and A1 A2) *s (t_arrow B1 B2) -> 
A1 *s (t_arrow B1 B2) \/ A2 *s (t_arrow B1 B2).
Proof.
  intros.
  unfold DisjSpec in *.
  unfold btmLikeSpec in *.
  unfold not in *.
  specialize (H (t_and (t_and A1 A2) (t_arrow B1 B2))).
  assert ((t_and (t_and A1 A2) (t_arrow B1 B2) <: t_and A1 A2)) by auto.
  assert (t_and (t_and A1 A2) (t_arrow B1 B2) <: (t_arrow B1 B2)) by auto.
  assert ((t_and (t_and A1 A2) (t_arrow B1 B2) <: t_and A1 A2) /\ (t_and (t_and A1 A2) (t_arrow B1 B2) <: (t_arrow B1 B2))) by auto.
  lets: H H2.
  clear H H0 H1 H2.
  apply btm_like_spec_arrow_and in H3.
  destruct H3.
 - unfold btmLikeSpec in H.
   unfold not in H.
   left. intros.
   destruct H0.
   assert (A <: A1). eapply sub_transitivity; eauto.
   eapply sub_transitivity in H3; eauto.
 - unfold btmLikeSpec in H. unfold not in H.
   right. intros.
   destruct H0.
   assert (A <: A2). eapply sub_transitivity; eauto.
   eapply sub_transitivity in H3; eauto.
Qed.

Lemma disj_spec_int_extra : forall A1 A2, (t_and A1 A2) *s t_int -> A1 *s t_int \/ A2 *s t_int.
Proof.
  intros.
  unfold DisjSpec in *.
  unfold btmLikeSpec in *.
  unfold not in *.
  specialize (H (t_and (t_and A1 A2) t_int)).
  assert ((t_and (t_and A1 A2) t_int <: t_and A1 A2)) by auto.
  assert (t_and (t_and A1 A2) t_int <: t_int) by auto.
  assert ((t_and (t_and A1 A2) t_int <: t_and A1 A2) /\ (t_and (t_and A1 A2) t_int <: t_int)) by auto.
  lets: H H2.
  clear H H0 H1 H2.
  apply btm_like_spec_int_and in H3.
  destruct H3.
  - unfold btmLikeSpec in H.
    unfold not in H.
    left. intros.
    destruct H0.
    assert (A <: t_int). eapply sub_transitivity; eauto.
    eapply sub_transitivity in H0; eauto.
  - unfold btmLikeSpec in H.
    unfold not in H.
    right. intros.
    destruct H0.
    assert (A <: t_int). eapply sub_transitivity; eauto.
    eapply sub_transitivity in H0; eauto.
Qed.


Lemma disj_spec_and_top : forall A1 A2, (t_and A1 A2) *s typ_top -> A1 *s A2.
Proof.
  intros.
  unfold DisjSpec in *.
  intros.
  destruct H0.
  eapply H; eauto.
Qed.


Lemma btm_like_spec_union_inter : forall A1 A2 B1 B2, btmLikeSpec (t_and (t_and A1 A2) (t_union B1 B2)) ->
btmLikeSpec (t_and (t_and A1 A2) B1) /\ btmLikeSpec (t_and (t_and A1 A2) B2).
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
  split.
  - intros.
    apply sub_and in H1. destruct H1.
    eapply H; eauto.
  - intros.
    apply sub_and in H1. destruct H1.
    eapply H; eauto.
Qed.


Lemma disj_spec_union_inter_or : forall A1 A2 B1 B2, t_and A1 A2 *s t_union B1 B2 ->
t_and A1 A2 *s B1 /\ t_and A1 A2 *s B2.
Proof.
  intros.
  unfold DisjSpec in *.
  eapply btm_like_spec_union_inter in H; eauto.
  destruct H. split.
 - intros. destruct H1.
  unfold btmLikeSpec in *. unfold not in *.
  intros.
  assert (A <: B1). eapply sub_transitivity; eauto.
  eapply sub_transitivity in H1; eauto.
 - intros. destruct H1.
   unfold btmLikeSpec in *. unfold not in *.
   intros.
   assert (A <: B2). eapply sub_transitivity; eauto.
   eapply sub_transitivity in H1; eauto.
Qed.


Lemma test5 : forall A B, A *s B -> btmLikeSpec A \/ btmLikeSpec B \/ btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold DisjSpec in H.
  unfold btmLikeSpec in *.
  unfold not in *.
  right. right. intros.
  apply sub_and in H1. destruct H1.
  specialize (H (t_and A B)).
  eapply H; eauto.
Qed.

(* 

Following two lemmas seem true but can't figure our how to prove

test51 depends upon test6

Did not find any counter example and can't prove the lemma

God help this poor PhD student! Please!

*)

Lemma test62 : forall A B C, Ord A -> not (A <: (t_and B C)) -> not (A <: B /\ A <: C).
Proof.
  intros.
  unfold not in *.
  intros.
  destruct H1.
  eapply H0; eauto.
Qed.

Lemma bottomLike_not_or1 : forall A1, not (bottomlike A1) ->
forall A2, not (bottomlike (t_union A1 A2)).
Proof.
  intros.
  unfold not in *. intros.
  inverts* H0.
Qed.

Lemma bottomLike_not_or2 : forall A2, not (bottomlike A2) ->
forall A1, not (bottomlike (t_union A1 A2)).
Proof.
  intros.
  unfold not in *. intros.
  inverts* H0.
Qed.

Lemma disjoint_decidable : forall A B, A *a B \/ not(A *a B).
Proof.
  induction A; eauto.
  - induction B; eauto.
   * right. unfold not. intros. inverts* H.
     admit. admit.
   * admit.
   * admit.
   * admit.
   * destruct IHB1; destruct IHB2.
     admit. admit. admit.
Admitted.

Lemma bottomLike_decidable : forall A, bottomlike A \/ not (bottomlike A).
Proof.
  dependent induction A; eauto;
  try solve [right; unfold not; intros; inversion H].
  - destruct IHA1; destruct IHA2.
    * left. apply bl_or; auto.
    * right. apply*  bottomLike_not_or2.
    * right. apply* bottomLike_not_or1.
    * right. apply* bottomLike_not_or1.
  - destruct IHA1; destruct IHA2.
   * left*.
   * left*.
   * left*.
   * admit.
Admitted.

Lemma test12 : forall A A1, Ord A -> A <: A1 -> forall A2, A <: A2 ->
(A <: (t_and A1 A2)).
Proof.
  intros.
  apply s_anda; auto.
Qed.


Lemma bottomLike_spec_decidable : forall A, btmLikeSpec A \/ not (btmLikeSpec A).
Proof.
  dependent induction A; eauto;
  try solve [right; unfold not; intros; inversion H].
  admit. admit. admit. admit.
  - destruct IHA1; destruct IHA2.
    * left. admit.
    * right. admit.
    * right. admit.
    * right. admit.
  - destruct IHA1; destruct IHA2.
   * left*. admit.
   * left*. admit.
   * left*. admit.
   * unfold btmLikeSpec in H.
     unfold not in H.
Admitted.

Lemma DeMorgan1 : forall A B, not (A \/ B) -> not A /\ not B.
Proof.
  unfold not. intros. split.
  intros. apply H. auto.
  intros. apply H. auto.
Qed.

(*Module LetsDoClassicalReasoning.*)

Require Import Coq.Logic.Classical.

Theorem excluded_middle : forall P, P \/ ~P.
Proof.
  apply classic.
Qed.

Lemma DeMorgan2 : forall A B, not (A /\ B) -> not A \/ not B.
Proof.
  apply not_and_or.
Qed.

(*End LetsDoClassicalReasoning.*)

Lemma not_sub_and1 : forall A1 A2 A,
not (A <: (t_and A1 A2)) -> not((A <: A1) /\ (A <: A2)).
Proof.
  intros.
  unfold not in *. intros.
  destruct H0.
  apply H; eauto.
Qed.

Lemma not_sub_and2 : forall A1 A2, btmLikeSpec (t_and A1 A2) -> forall A, Ord A -> not((A <: A1) /\ (A <: A2)).
Proof.
  intros.
  unfold not in *. intros.
  unfold btmLikeSpec in H. unfold not in H.
  destruct H1.
  eapply H; eauto.
Qed.

Lemma not_sub_and3 : forall A1 A2 A, not (A <: A1 /\ A <: A2) -> 
not (A <: A1) \/ not (A <: A2).
Proof.
  intros A1 A2 A.
  apply not_and_or.
Qed.

Lemma not_sub_and4 : forall A1 A2 A, Ord A -> 
not (A <: A1 /\ A <: A2) -> not (A <: A1) \/ not (A <: A2).
Proof.
  intros A1 A2 A H.
  apply not_and_or.
Qed.

(*

From the below lemma:

A1, A2, B: typ
H: btmLikeSpec (t_and (t_and A1 A2) B)
H0: forall A : typ, Ord A -> ~ ((A <: t_and A1 A2) /\ A <: B)
---------------------------------------------------------------1/1
btmLikeSpec (t_and A1 B) \/
btmLikeSpec (t_and A2 B) \/ btmLikeSpec (t_and A1 A2)

If we destruct H0 using Demorgan's law:

~ ((A <: t_and A1 A2) /\ A <: B) = ~(A <: t_and A1 A2) \/ ~(A <: B)

we can prove our lemma test6

*)

Lemma test6 : forall A1 A2 B, btmLikeSpec (t_and (t_and A1 A2) B) ->
btmLikeSpec (t_and A1 B) \/ btmLikeSpec (t_and A2 B) \/ btmLikeSpec (t_and A1 A2).
Proof.
  intros.
  lets: not_sub_and2 (t_and A1 A2) B H.
  lets: not_sub_and4 (t_and A1 A2) B.
  assert (forall A, Ord A -> ~ (A <: t_and A1 A2) \/ ~ (A <: B)). eauto.
  unfold btmLikeSpec.
Admitted.


Lemma test61 : forall B A1 A2, (t_and A1 A2) *s B ->
A1 *s B \/ A2 *s B \/ A1 *s A2.
Proof.
  intros.
  assert (btmLikeSpec (t_and(t_and A1 A2) B)). eauto.
  apply test6 in H0.
  destruct H0.
  left.
  unfold DisjSpec.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
  intros.
  destruct H1.
  assert (A <: B). eapply sub_transitivity; eauto.
  eapply sub_transitivity in H1; eauto.
  destruct H0.
  right. left.
  unfold DisjSpec. intros.
  unfold btmLikeSpec in *. unfold not in *. intros.
  destruct H1.
  assert (A <: B). eapply sub_transitivity; eauto.
  eapply sub_transitivity in H1; eauto.
  right. right.
  unfold DisjSpec. intros.
  unfold btmLikeSpec in *. unfold not in *. intros.
  destruct H1.
  assert (A <: A2). eapply sub_transitivity; eauto.
  eapply sub_transitivity in H1; eauto.
Qed.

Lemma tes13 : forall A1 A2 B, btmLikeSpec (t_and (t_and A1 A2) B) -> 
not (btmLikeSpec B) -> not (btmLikeSpec (t_and A1 A2)) ->
btmLikeSpec (t_and A1 B) \/ btmLikeSpec (t_and A2 B).
Proof.
intros.
unfold btmLikeSpec in *.
unfold not in *.
left. intros.
apply H0. intros.
Admitted.

Lemma test15 : forall B, not(btmLikeSpec B) -> forall A, Ord A -> A <: B.
intros.
dependent induction H0; eauto.
Admitted.

Lemma test16 : forall A1 A2, not(bottomlike (t_and A1 A2)) ->
forall B, bottomlike (t_and (t_and A1 A2) B) -> A1 *a B \/ A2 *a B.
Proof.
intros.
inductions H0. admit. admit.
unfold not in H. unfold DisjSpec in H0.
Admitted.

Lemma test611 : forall B A1 A2, (t_and A1 A2) *s B ->
                               A1 *s B \/ A2 *s B \/ A1 *s A2.
Proof.
  intros. unfold DisjSpec in *.
  (*assert (exists C, (C <: A1 /\ C <: B) \/ (C <: A2 /\ C <: B) \/ (C <: A1 /\ C <: B)).*)
  assert (exists C, (C <: A1 /\ C <: B /\ C <: A2)) by eauto.
    destruct H0.
    destruct H0.
    destruct H1.
    right. left.
    intros. destruct H3.
    unfold btmLikeSpec. intros. unfold not. intros.
    specialize (H (t_and x C)).
    assert ((t_and x C) <: (t_and A1 A2)) by eauto.
    assert (t_and x C <: B) by eauto.
    unfold not in *.
    assert ((t_and x C <: t_and A1 A2) /\ (t_and x C <: B)) by auto.
    lets: H H9.
    unfold btmLikeSpec in H10. unfold not in *.
    specialize (H10 A H5). clear H9.
    apply sub_and in H7. destruct H7.
    assert ((t_and A x) <: C) by auto.
    assert ((t_and A x) <: A) by auto.
    dependent induction H12; eauto.
Admitted.

Lemma Disj_completeness : forall A B, A *s B -> A *a B.
Proof.
induction A; unfold DisjSpec; intros; eauto.
- induction B; eauto.
  + constructor; apply Disj_sym. 
    apply IHB1; intros; destruct H0; apply H; eauto.
    apply IHB2; intros; destruct H0; apply H; eauto.
  + (* Intersection and Int case - requires hard helping lemma *) 
    specialize (H (t_and t_int (t_and B1 B2))).
    forwards*: H.
    apply sym_btm_like in H0.
    apply btm_like_spec_and in H0.
    (* Intersection and Int case - or lemma *)
    apply disj_spec_int in H0.
    destruct H0.
    apply ad_andr1.
    forwards*: IHB1.
    apply Disj_sym in H1. auto.
    apply ad_andr2.
    forwards*: IHB2.
    apply Disj_sym in H1. auto.
- induction B; eauto.
  + specialize (H (t_arrow (t_union A1 B1) t_bot)).
    forwards*: H. apply BL_completeness in H0. inversion H0.
  + constructor; apply Disj_sym.
    apply IHB1; intros; destruct H0; apply H; eauto.
    apply IHB2; intros; destruct H0; apply H; eauto.
  + specialize (H (t_and (t_arrow A1 A2) (t_and B1 B2))).
    forwards*: H.
    apply sym_btm_like in H0.
    apply btm_like_spec_and in H0.
    apply disj_spec_arrow in H0.
    destruct H0.
    apply ad_andr1.
    forwards*: IHB1.
    apply Disj_sym in H1. auto.
    apply ad_andr2.
    forwards*: IHB2.
    apply Disj_sym in H1. auto.
- constructor.
  apply IHA1; unfold DisjSpec; intros; destruct H0; apply H; eauto.
  apply IHA2; unfold DisjSpec; intros; destruct H0; apply H; eauto.
- assert (DisjSpec (t_and A1 A2) B) by auto.
  assert (btmLikeSpec (t_and(t_and A1 A2) B)); auto.
  apply test6 in H1.

  (*  lets: bottomLike_spec_decidable B.
  destruct H2. admit.
  lets: bottomLike_spec_decidable (t_and A1 A2).
  destruct H3. admit.
  apply BL_completeness in H1.
  assert (not (bottomlike B)). admit.
  assert (not (bottomlike (t_and A1 A2))). admit.
  dependent destruction H1. admit. admit.
  unfold not in *.

  apply BL_soundness in H1.
  apply ad_dis_specl.
  lets: bottomLike_decidable B.
  destruct H1; destruct H2; destruct H3.
  admit. admit. admit. admit. admit. admit. admit.
  assert (btmLikeSpec (t_and (t_and A1 A2) B)) by auto.
  apply BL_completeness in H4.
  dependent induction H4. admit. admit.
  apply test61 in H0.
  destruct H0.
  apply ad_andl1.
  eapply IHA1; auto.
  destruct H0.
  apply ad_andl2.
  eapply IHA2; auto.
  apply ad_dis_specl; auto.*)
(*  dependent induction B; eauto.
 + apply disj_spec_and_top in H0.
  apply ad_and_disl.
  eapply IHA1; auto.
 + apply disj_spec_int in H0. destruct H0.
   apply ad_andl1. eapply IHA1; auto.
   apply ad_andl2. eapply IHA2; auto.
 + apply disj_spec_arrow in H0.
   destruct H0.
   apply ad_andl1. eapply IHA1; auto.
   apply ad_andl2. eapply IHA2; auto.
 + apply disj_spec_union_inter_or in H0.
   destruct H0.
   apply ad_orr.
   apply Disj_sym. eapply IHB1; eauto.
   apply Disj_sym. eapply IHB2; eauto.
 + admit.*)
Qed.