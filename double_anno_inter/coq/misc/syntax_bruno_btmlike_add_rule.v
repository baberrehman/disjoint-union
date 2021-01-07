
(*
This file contains the updates suggested by Bruno.
Algorithmic bottomlike depends upon the algorithmic disjointnes
in this approach.
*)

Require Import TLC.LibLN.
Require Import Program.Equality.

(* Require Import LibTactics. *)
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

Reserved Notation "A *a B" (at level 80).

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
     A *a B ->
     bottomlike (t_and A B)
(* | bl_top : forall A,
     bottomlike (t_and typ_top A) ->
     bottomlike A *)

(* defns Disjointness *)
with disjointness : typ -> typ -> Prop :=    (* defn disjointness *)
 | ad_btml : forall (A:typ),
      t_bot *a A
 | ad_btmr : forall (A:typ),
     A *a t_bot
 | ad_intl : forall (A B:typ),
     t_int *a (t_arrow A B)
 | ad_intr : forall (A B:typ),
     (t_arrow A B) *a t_int
 | ad_orl : forall (A B C:typ),
     A *a C ->
     B *a C ->
     (t_union A B) *a C
 | ad_orr : forall (A B C:typ),
     A *a B ->
     A *a C ->
     A *a (t_union B C)
 | ad_andl1 : forall A B C,
     A *a C ->
     (t_and A B) *a C
 | ad_andl2 : forall A B C,
     B *a C ->
     (t_and A B) *a C
 | ad_andr1 : forall A B C,
     A *a B ->
     A *a (t_and B C)
 | ad_andr2 : forall A B C,
     (*A *a C ->*)
     A *a C ->
     A *a (t_and B C)
 | ad_disl: forall A B C,
    A *a B ->
    (t_and A B) *a C
 | ad_disr: forall A B C,
    B *a C ->
    A *a (t_and B C)
 | ad_and_and : forall A1 A2 B1 B2,
    bottomlike (t_and (t_and A1 A2) (t_and B1 B2)) ->
    (t_and A1 A2) *a (t_and B1 B2)

where "A *a B" := (disjointness A B).

Hint Constructors disjointness.

Hint Constructors bottomlike.


(**********************************)
(****  Bottom-Like Properties  ****)
(**********************************)

Lemma ord_sub_bot_false : forall A, Ord A -> A <: t_bot -> False.
Proof.
  intros.
  dependent induction H; inversion H0.
Qed.


Lemma btm_sub_btmlike : forall A, A <: t_bot -> bottomlike A.
Proof.
intros. inductions H; eauto.
Qed.

Lemma btm_sub_btmlikeSpec : forall A, A <: t_bot -> btmLikeSpec A.
Proof.
intros. unfold btmLikeSpec. unfold not. intros.
eapply sub_transitivity in H; eauto.
forwards*: ord_sub_bot_false H0.
Qed.


Lemma btm_like_and : forall A B, bottomlike (t_and A B) ->
bottomlike A \/ bottomlike B \/ A *a B.
Proof.
  intros.
  dependent induction H; eauto.
Qed.

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

Lemma ord_sub_and_or : forall B C, forall A, Ord A ->
not (A <: (t_and B C)) -> not(A <: B) \/ not(A <: C) \/ not (A <: (t_and B C)).
Proof.
  intros.
  unfold not in *. auto.
Qed.


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

(*************************************)
(*****  Disjointness Properties  *****)
(*************************************)

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

Lemma disj_spec_union : forall A B C, t_union A B *s C -> A *s C /\ B *s C.
Proof.
  unfold DisjSpec; unfold btmLikeSpec; unfold not; intros.
  split.
  - intros. destruct H0.
    specialize (H C0).
    apply H with (A:=A0); auto.
  - intros. destruct H0.
    specialize (H C0).
    apply H with (A:=A0); auto.
Defined.

Lemma disj_spec_union1 : forall A B C, A *s t_union B C -> A *s B /\ A *s C.
Proof.
  unfold DisjSpec; unfold btmLikeSpec; unfold not; intros.
  split.
  - intros. destruct H0.
    specialize (H C0).
    apply H with (A:=A0); auto.
  - intros. destruct H0.
    specialize (H C0).
    apply H with (A:=A0); auto.
Defined.


Lemma ord_sub_disj_spec_false : forall A, Ord A -> 
forall B C, B *s C -> A <: (t_and B C) -> False.
Proof.
 intros.
 unfold DisjSpec in H0.
 unfold btmLikeSpec in H0. unfold not in H0.
 apply sub_and in H1. destruct H1.
 specialize (H0 (t_and B C)).
 forwards*: H0 H.
Defined.

Lemma BL_disj : forall A, bottomlike A -> forall B, A *a B.
Proof.
  intros A H1.
  inductions H1; intros; eauto.
Defined.

Lemma BL_disj_sym : forall A, bottomlike A -> forall B, B *a A.
Proof.
  intros A H1.
  inductions H1; intros; eauto.
Defined.

Lemma Disj_sym_spec : forall A B, A *s B -> B *s A.
Proof.
  unfold DisjSpec. intros.
  destruct H0.
  apply* H.
Defined.

Lemma BL_soundness : forall A, bottomlike A -> btmLikeSpec A
with Disj_soundness : forall A B, A *a B -> A *s B.
Proof.
(* BL_soundness Soundness Proof *)
- clear BL_soundness. intros. inductions H; unfold btmLikeSpec in *; intros.
 + unfold not. intros.
  inductions H; try solve [inversion H0].
 + specialize (IHbottomlike1 A0).
  specialize (IHbottomlike2 A0).
  forwards: IHbottomlike1. auto.
  forwards: IHbottomlike2. auto.
  clear IHbottomlike1 IHbottomlike2.
  unfold not. intros.
  dependent induction H4; auto.
  inversion H1. inversion H1. inversion H1.
 + specialize (IHbottomlike A0).
  forwards: IHbottomlike. auto.
  unfold not in *. intros.
  apply H1.
  apply sub_and in H2. destruct H2. auto.
 + specialize (IHbottomlike A0).
  forwards: IHbottomlike. auto.
  unfold not in *. intros.
  apply H1.
  apply sub_and in H2. destruct H2. auto.
 + unfold not in *.
  intros.
  apply Disj_soundness in H.
  lets: ord_sub_disj_spec_false A0 H0 A B H.
  forwards: H2 H1. auto.
 (*+ unfold not in *.
   intros.
   specialize (IHbottomlike A0).
   apply IHbottomlike; auto.*)

(* Disj_soundness Soundness Proof *)
- clear Disj_soundness. intros. dependent induction H; unfold DisjSpec; intros.
 + destruct H.
   unfold btmLikeSpec in *. unfold not in *. intros.
   assert (A0 <: t_bot).
   apply sub_transitivity with (A := A0) (B := C) (C := t_bot); auto.
   apply ord_sub_bot_false in H3. false. apply H1.
+ destruct H.
   unfold btmLikeSpec in *. unfold not in *. intros.
   assert (A0 <: t_bot).
   apply sub_transitivity with (A := A0) (B := C) (C := t_bot); auto.
   apply ord_sub_bot_false in H3. false. apply H1.
 + destruct H. induction C; try (dependent destruction H).
  * inversion H0.
  * apply btm_spec.
  * inverts* H1.
    forwards*: IHC1.
    forwards*: IHC2.
    apply* btm_like_spec_union_inv.
  * inverts* H0.
    forwards*: IHC1.
    apply* btm_like_spec_and1_inv.
    eapply sub_int_arrow; eauto.
  * inverts* H0.
    apply sym_btm_like.
    eapply sub_int_arrow; eauto.
    forwards*: IHC2.
    apply* btm_like_spec_and2_inv.
+ destruct H. induction C; try (dependent destruction H0).
  * inversion H.
  * apply btm_spec.
  * inverts* H.
    forwards*: IHC1.
    forwards*: IHC2.
    apply* btm_like_spec_union_inv.
  * inverts* H.
    forwards*: IHC1.
    apply* btm_like_spec_and1_inv.
    eapply sub_int_arrow; eauto.
  * inverts* H.
    apply sym_btm_like.
    eapply sub_int_arrow; eauto.
    forwards*: IHC2.
    apply* btm_like_spec_and2_inv.
    (* difficult case -- union with intersection *)
+ destruct H1.
  lets: disj_sub_union A B C IHdisjointness1 IHdisjointness2.
  unfold DisjSpec in H3.
  apply H3. split. auto. auto.
    (* difficult case -- union with intersection *)
+ destruct H1.
  apply Disj_sym_spec in IHdisjointness1.
  apply Disj_sym_spec in IHdisjointness2.
  lets: disj_sub_union B C A IHdisjointness1 IHdisjointness2.
  unfold DisjSpec in H3.
  apply H3. split. auto. auto.
 + destruct H0.
  unfold DisjSpec in IHdisjointness.
  apply IHdisjointness.
  split; auto.
  apply sub_and in H0. destruct H0; auto.
 + destruct H0.
  unfold DisjSpec in IHdisjointness.
  apply IHdisjointness.
  split; auto.
  apply sub_and in H0.
  destruct H0; auto.
 + destruct H0.
  apply sub_and in H1.
  destruct H1.
  unfold DisjSpec in IHdisjointness.
  apply IHdisjointness; auto.
 + destruct H0.
  apply sub_and in H1.
  destruct H1.
  unfold DisjSpec in IHdisjointness.
  apply IHdisjointness; auto.
 + destruct H0.
   apply sub_and in H0. destruct H0.
   apply IHdisjointness. split; auto.
 + destruct H0.
   apply sub_and in H1. destruct H1.
   apply IHdisjointness. split; auto.
 + destruct H0.
   apply BL_soundness in H.
   unfold btmLikeSpec in *.
   unfold not in *.
   intros.
   specialize (H A).
   apply H; auto.
   apply s_anda.
   apply sub_transitivity with (A:=A) (B:=C) (C:= (t_and A1 A2)); auto.
   apply sub_transitivity with (A:=A) (B:=C) (C:= (t_and B1 B2)); auto.
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
Defined.

Lemma disj_btm_spec : forall A B, A *s B -> btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold DisjSpec in H.
  apply H; eauto.
Defined.

Lemma Disj_sym : forall A B, A *a B -> B *a A.
  induction 1; eauto.
  admit.
Admitted.

Lemma bl_union_inv : forall A B, bottomlike (t_union A B) -> 
bottomlike A /\ bottomlike B.
Proof.
intros. inverts* H.
Defined.

Lemma disj_union_inv : forall A B C, A *a (t_union B C) ->
  A *a B /\ A *a C.
Proof.
intros.
inductions H; eauto.
(*- apply bl_union_inv in H.
  destruct H. split*.*)
- specialize (IHdisjointness1 B C).
  destruct IHdisjointness1; auto.
  specialize (IHdisjointness2 B C).
  destruct IHdisjointness2; auto.
- specialize (IHdisjointness B C).
  destruct IHdisjointness; auto.
- specialize (IHdisjointness B C).
  destruct IHdisjointness; auto.
Defined.


Lemma ord_sub_int_arrow_false : forall A B A1 A2, Ord A -> A <: B -> B <: t_int -> B <: t_arrow A1 A2 -> False.
Proof.
  intros.
  lets: sub_int_arrow B B H1 A1 A2.
  forwards*: H3.
  unfold btmLikeSpec in H4.
  unfold not in H4.
  eapply H4; eauto.
Defined.

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
Defined.


(***************************)
(*

Important lemma for completeness.

\/ A B, botlike((A & B) & (A1 -> B1)) -> botlike (A & (A1 -> B1)) \/ botlike (B & (A1 -> B1))

Below is the proof of this lemma.

Difficult to prove.

*)
(***************************)

Lemma ord_sub_arrow_and_B : forall A, Ord A -> forall B, A <: B -> 
forall A1 A2, A <: (t_arrow A1 A2) -> exists A3 A4, A = (t_arrow A3 A4).
Proof.
  intros.
  dependent induction H1; eauto; try solve [inversion H].
Defined.

Lemma btm_like_spec_arrow_and : forall A B A1 B1, btmLikeSpec (t_and (t_and A B) (t_arrow A1 B1)) -> 
  btmLikeSpec (t_and A (t_arrow A1 B1)) \/ btmLikeSpec (t_and B (t_arrow A1 B1)).
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
  inductions A; eauto.
    (* Top Case *)
  - right. intros.
    apply sub_and in H1. destruct H1.
    forwards*: H A H0.
    (* Int Case *)
  - left. intros.
    apply sub_and in H1. destruct H1.
    lets: sub_int_arrow A A H1 A1 B1.
    lets: H3 H2.
    unfold btmLikeSpec in H4. unfold not in H4.
    forwards*: H4 H0.
    (* Bottom Case *)
  - left. intros.
    apply sub_and in H1. destruct H1.
    forwards*: ord_sub_bot_false A H0.
    (* Arrow Case *)
  - right. intros.
    apply sub_and in H1.
    destruct H1.
    lets: ord_sub_arrow_and_B A H0 B H1.
    lets: H3 A0 B1 H2.
    destruct H4 as [A3 [A4]].
    clear H3.
    subst.
    specialize (H (t_arrow typ_top t_bot)).
    forwards*: H.
    apply* s_anda.
    apply* s_anda.
    assert ((t_arrow typ_top t_bot) <: (t_arrow A3 A4)) by eauto.
    eapply sub_transitivity; eauto.
    
    (* Below is old and inefficient approach to prove this case *)
    (* By induction on the subtyping relation of Ord type and arrow type *)

    (*inductions H2; eauto; try solve [inversion H0];
    clear IHsubtyping1 IHsubtyping2 IHA1 IHA2.
    specialize (H (t_arrow typ_top t_bot)).
    forwards*: H.
    apply* s_anda.
    apply* s_anda.
    assert ((t_arrow typ_top t_bot) <: (t_arrow A4 A3)) by eauto.
    eapply sub_transitivity; eauto.*)
    (* union Case *)
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
    (* Intersection case *)
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
Defined.

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
Defined.


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
Defined.

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
Defined.

Lemma top_btmlike : forall A, btmLikeSpec (t_and typ_top A) -> btmLikeSpec A.
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
  intros.
  forwards*: H H0.
Defined.

Lemma top_disj : forall A, typ_top *s A -> btmLikeSpec A.
Proof.
  intros.
  apply disj_btm_spec in H.
  apply top_btmlike in H.
  apply H.
Defined.

Lemma disj_spec_and_top : forall A1 A2, (t_and A1 A2) *s typ_top -> A1 *s A2.
Proof.
  intros.
  unfold DisjSpec in *.
  intros.
  destruct H0.
  eapply H; eauto.
Defined.


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
Defined.


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
Defined.

(* 

Following two lemmas seem true but can't figure our how to prove

test61 depends upon test6

Did not find any counter example and can't prove the lemma

God help this poor PhD student! Please!

*)

Lemma test62 : forall A B C, Ord A -> not (A <: B) -> not (A <: (t_and B C)).
Proof.
  intros.
  unfold not in *.
  intros.
  apply sub_and in H1. destruct H1.
  apply H0; auto.
Qed.

Lemma test6 : forall A1 A2 B, btmLikeSpec (t_and (t_and A1 A2) B) ->
btmLikeSpec (t_and A1 B) \/ btmLikeSpec (t_and A2 B) \/ btmLikeSpec (t_and A1 A2).
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
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

Lemma disj_spec_or_top : forall A1 A2, (t_union A1 A2) *s typ_top -> A1 *s A2.
Proof.
  intros.
  unfold DisjSpec in *. intros.
  destruct H0.
  eapply H; auto.
Defined.

Lemma disj_spec_or_top1 : forall A1 A2, btmLikeSpec(t_and (t_union A1 A2) typ_top) -> btmLikeSpec (t_union A1 A2).
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
  intros.
  forwards*: H1.
Defined.

Lemma btm_like_and_disjoint : forall A B, bottomlike (t_and A B) -> A *a B.
Proof.
  intros. inductions H; eauto.
  apply BL_disj. apply H.
  apply Disj_sym. apply BL_disj. apply H.
Defined.

Lemma disjoint_implies_btm_like : forall A B, A *a B -> bottomlike (t_and A B).
Proof.
  intros. apply bl_andsub. auto.
Defined.

Lemma btm_like_and_disjoint1 : forall A B, bottomlike (t_and A B) -> 
bottomlike A \/ bottomlike B \/ A *a B.
Proof.
  intros. inductions H.
  left. auto.
  right. left. auto.
  right. right. apply H.
Defined.

Lemma btm_like_and_disjoint_and : forall A1 A2 B1 B2, 
bottomlike (t_and (t_and A1 A2) (t_and B1 B2)) -> (t_and A1 A2) *a (t_and B1 B2).
Proof.
  intros. inductions H; eauto.
  (*apply BL_disj. apply H.
  apply Disj_sym. apply BL_disj. apply H.*)
Defined.


Lemma btm_like_and_3 : forall A1 A2 A3, bottomlike (t_and (t_and A1 A2) A3) ->
bottomlike (t_and A1 A2) \/ bottomlike (t_and A2 A3) \/ bottomlike (t_and A1 A3)
with
disj_and_3 : forall A1 A2 A3, (t_and A1 A2) *a A3 ->
A1 *a A2 \/ A2 *a A3 \/ A1 *a A3.
Proof.
 - clear btm_like_and_3. intros.
   dependent induction H; auto.
   apply disj_and_3 in H.
   destruct H.
   left. apply bl_andsub in H. apply H.
   destruct H.
   right. left. apply bl_andsub in H. apply H.
   right. right. apply bl_andsub in H. apply H.
 - clear disj_and_3. intros.
   dependent induction H; auto.
   (* Union Case*)
   lets: ad_orr (t_and A1 A2) B C H H0.
   specialize (IHdisjointness1 A1 A2).
   forwards: IHdisjointness1. congruence.
   specialize (IHdisjointness2 A1 A2).
   forwards: IHdisjointness2. congruence.   
   destruct H2.
   left. apply H2.
   destruct H3.
   left. apply H3.
   destruct H2.
   destruct H3.
   right. left. apply ad_orr. apply H2. apply H3.
   right. left. apply ad_orr. apply H2.
    admit.
   destruct H3. admit.
   right. right.
   apply ad_orr. apply H2. apply H3.
   (* And Case 1 *)
   specialize (IHdisjointness A1 A2).
   forwards: IHdisjointness. congruence.
   destruct H0.
   left. apply H0.
   destruct H0. right. left. apply ad_andr1. apply H0.
   right. right. apply ad_andr1. apply H0.
   (* And Case 2*)
   specialize (IHdisjointness A1 A2).
   forwards: IHdisjointness. congruence.
   destruct H0.
   left. apply H0.
   destruct H0. right. left. apply ad_andr2. apply H0.
   right. right. apply ad_andr2. apply H0.
Admitted.

Lemma disj_spec_arrow_false : forall A1 A2 B1 B2, t_arrow A1 A2 *s t_arrow B1 B2 -> False.
Proof.
  unfold DisjSpec; unfold btmLikeSpec; unfold not; intros.
  specialize (H (t_arrow typ_top t_bot)).
  forwards: H; auto.
Defined.

Lemma bl_test : forall A B, bottomlike (t_and A B) ->
bottomlike A \/ bottomlike B \/ A *a B.
Proof.
  intros.
  inversion H; subst; auto.
Defined.

(*
Fool Lemmas
*)

Lemma top1 : forall A, typ_top *a A.
Admitted.

Lemma int1 : forall A, t_int *a A.
Admitted.

Lemma arrow1 : forall A1 A2 A, (t_arrow A1 A2) *a A.
Admitted.

Lemma btm1 : forall A, t_bot *a A.
Admitted.

Lemma union1 : forall A1 A2 A, (t_union A1 A2) *a A.
Admitted.

Lemma inter1 : forall A1 A2 A, (t_and A1 A2) *a A.
Admitted.

Lemma bl1 : forall A, bottomlike A.
Admitted.

Lemma identity : forall A : Prop, A -> A.
Proof.
 auto.
Defined.


(*
Fool Lemmas End Here
*)

Lemma BL_completeness : forall A, btmLikeSpec A -> bottomlike A
with Disj_completeness : forall A B, A *s B -> A *a B.
Proof.
  (* Bottom Like completeness proof *)
- clear BL_completeness. induction A; unfold btmLikeSpec; intro.
 + specialize (H typ_top).
  unfold not in H.
  assert (Ord typ_top) by auto.
  assert (typ_top <: typ_top) by auto.
  lets: H H0 H1. false.
 + specialize (H t_int).
  unfold not in H.
  assert (Ord t_int) by auto.
  assert (t_int <: t_int) by auto.
  lets: H H0 H1. false.
 + apply bl_bot.
 + specialize (H (t_arrow A1 A2)).
  unfold not in H.
  assert (Ord (t_arrow A1 A2)) by auto.
  assert ((t_arrow A1 A2) <: (t_arrow A1 A2)) by auto.
  lets: H H0 H1. false.
 + apply bl_or.
  * apply IHA1. unfold btmLikeSpec.
  intros.
  unfold not in *. intros.
  specialize (H A).
  assert (A <: (t_union A1 A2)) by auto.
  apply H. auto. auto.
  * apply IHA2. unfold btmLikeSpec.
  intros.
  unfold not in *. intros.
  specialize (H A).
  assert (A <: (t_union A1 A2)) by auto.
  apply H. auto. auto.
 + clear IHA1. clear IHA2.
  apply bl_andsub.
  assert (btmLikeSpec (t_and A1 A2)) by auto.
  lets: btm_like_spec_and A1 A2 H0.
  specialize (Disj_completeness A1 A2).
  apply Disj_completeness in H1. apply H1.

  (*
  Below is an alternate way to prove the
  intersection case in btm-like completeness
  *)

  (*apply Disj_completeness.
  unfold DisjSpec. intros.
  unfold btmLikeSpec. unfold not in *. intros.
  specialize (H A).
  apply H. apply H1.
  destruct H0.
  apply s_anda.
  apply sub_transitivity with (A := A) (B := C) (C := A1) in H0. auto. auto.
  apply sub_transitivity with (A := A) (B := C) (C := A2) in H3. auto. auto.*)

  (* Dijointness completeness proof *)
- clear Disj_completeness.
  (*intros.
  apply disj_btm_spec in H.
  apply BL_completeness in H.
  apply btm_like_and_disjoint in H.
  apply H.*)

  (*************************** 
  Below is New Proof Technique
  ****************************)

(*  induction A; induction B; intro; auto.
  + apply disj_spec_union1 in H. destruct H.
    apply ad_orr. apply IHB1. apply H.
    apply IHB2. apply H0.
  + apply Disj_sym_spec in H.
    apply disj_spec_int_extra in H. destruct H.
    apply ad_andr1. apply IHB1. apply Disj_sym_spec. apply H.
    apply ad_andr2. apply IHB2. apply Disj_sym_spec. apply H.
  + apply disj_spec_arrow_false in H. false.
  + apply disj_spec_union1 in H. destruct H.
    apply ad_orr. apply IHB1. apply H.
    apply IHB2. apply H0.
  + apply Disj_sym_spec in H.
    apply disj_spec_arrow in H. destruct H.
    apply ad_andr1. apply IHB1. apply Disj_sym_spec. apply H.
    apply ad_andr2. apply IHB2. apply Disj_sym_spec. apply H.
  + apply disj_spec_union in H. destruct H.
    apply ad_orl. apply IHA1. apply H.
    apply IHA2. apply H0.
  + apply disj_spec_union in H. destruct H.
    apply ad_orl. apply IHA1. apply H.
    apply IHA2. apply H0.
  + apply disj_spec_union1 in H. destruct H.
    apply ad_orr. apply IHB1. apply H.
    apply IHB2. apply H0.
  + apply disj_spec_union in H. destruct H.
    apply ad_orl. apply IHA1. apply H.
    apply IHA2. apply H0.
  + apply disj_spec_int_extra in H. destruct H.
    apply ad_andl1. apply IHA1. apply H.
    apply ad_andl2. apply IHA2. apply H.
  + apply disj_spec_arrow in H. destruct H.
    apply ad_andl1. apply IHA1. apply H.
    apply ad_andl2. apply IHA2. apply H.
  + apply disj_spec_union1 in H. destruct H.
    apply ad_orr. apply IHB1. apply H.
    apply IHB2. apply H0.
  + apply disj_btm_spec in H.
    specialize (BL_completeness (t_and (t_and A1 A2) (t_and B1 B2))).
    apply BL_completeness in H.
    apply btm_like_and_disjoint in H.
    apply H.
Guarded.
Abort.*)

  (*************************** 
  Below is Old Proof Technique
  ****************************)
  
 induction A; intros.
  (* Top Case *)
 + (*apply BL_disj_sym.
   apply top_disj in H.
   specialize (BL_completeness B).
   apply BL_completeness in H.
   apply bl1.*)

 induction B; intros.
  * specialize (H typ_top).
    assert (typ_top <: typ_top /\ typ_top <: typ_top) by auto.
    lets: H H0.
    specialize (H1 typ_top). unfold not in H1.
    destruct H0.
    assert (Ord typ_top) by auto. lets: H1 H3 H0. false.
  * specialize (H t_int).
    assert (t_int <: typ_top /\ t_int <: t_int) by auto.
    lets: H H0.
    specialize (H1 t_int). unfold not in H1.
    assert (Ord t_int) by auto.
    destruct H0.
    lets: H1 H2 H3. false.
  * apply ad_btmr.
  * clear IHB1 IHB2. specialize (H (t_arrow B1 B2)).
    assert ((t_arrow B1 B2) <: typ_top /\ (t_arrow B1 B2) <: (t_arrow B1 B2)) by auto.
    lets: H H0.
    specialize (H1 (t_arrow B1 B2)). unfold not in H1.
    assert (Ord (t_arrow B1 B2)) by auto.
    destruct H0. lets: H1 H2 H3. false.
  * apply disj_spec_union1 in H. destruct H.
    apply ad_orr. apply IHB1. apply H.
    apply IHB2. apply H0.
  * (* Todo: Problamatic Case - To be proved *) 
    clear IHB1 IHB2. apply BL_disj_sym.
    apply top_disj in H.
    specialize (BL_completeness (t_and B1 B2)).
    apply BL_completeness in H.
    apply bl1.

   (* Int Case *)
 + induction B.
  * specialize (H t_int).
    assert (t_int <: t_int /\ t_int <: typ_top) by auto.
    lets: H H0.
    unfold btmLikeSpec in H1. unfold not in H1.
    specialize (H1 t_int).
    assert (Ord t_int) by auto.
    assert (t_int <: t_int) by auto.
    lets: H1 H2 H3. false.
  * specialize (H t_int).
    assert (t_int <: t_int /\ t_int <: t_int) by auto.
    lets: H H0.
    unfold btmLikeSpec in H1. unfold not in H1.
    specialize (H1 t_int).
    assert (Ord t_int) by auto.
    assert (t_int <: t_int) by auto.
    lets: H1 H2 H3. inversion H4.
  * apply ad_btmr.
  * apply ad_intl.
  * apply disj_spec_union1 in H. destruct H.
    apply ad_orr.
    apply IHB1. apply H.
    apply IHB2. apply H0.
  * (* Intersection and Int case - requires hard helping lemma *)
    apply Disj_sym_spec in H.
    apply disj_spec_int_extra in H. destruct H.
    apply ad_andr1. apply IHB1. apply Disj_sym_spec. apply H.
    apply ad_andr2. apply IHB2. apply Disj_sym_spec. apply H.
   (* Bottom Case *)
 + apply ad_btml.
    (* Arrow Case *)
 + clear IHA1 IHA2.
   induction B.
  * specialize (H (t_arrow A1 A2)).
    assert (t_arrow A1 A2 <: t_arrow A1 A2 /\ t_arrow A1 A2 <: typ_top) by auto.
    lets: H H0.
    unfold btmLikeSpec in H1. unfold not in H1.
    specialize (H1 (t_arrow A1 A2)).
    assert (Ord (t_arrow A1 A2)) by auto.
    assert ( (t_arrow A1 A2) <: (t_arrow A1 A2)) by auto.
    lets: H1 H2 H3. false.
  * apply ad_intr.
  * apply ad_btmr.
  * apply disj_spec_arrow_false in H. false.
  * apply disj_spec_union1 in H. destruct H.
    apply ad_orr.
    apply IHB1. apply H.
    apply IHB2. apply H0.
  * apply Disj_sym_spec in H. apply disj_spec_arrow in H. destruct H.
    apply ad_andr1. apply IHB1. apply Disj_sym_spec. apply H.
    apply ad_andr2. apply IHB2. apply Disj_sym_spec. apply H.
    (* Union Case *)
 + apply disj_spec_union in H. destruct H.
   apply ad_orl.
   apply IHA1. apply H.
   apply IHA2. apply H0.
  (* Intersection Case *)
 + (*clear IHA1 IHA2.
   apply disj_btm_spec in H.
   apply BL_completeness in H.
   apply btm_like_and_disjoint in H.
   apply inter1.*)

   induction B.
   * apply disj_spec_and_top in H.
     apply BL_disj.
     apply disjoint_implies_btm_like.
     apply IHA1. apply H.
   * apply disj_spec_int_extra in H.
     destruct H. apply ad_andl1. apply IHA1. apply H.
     apply ad_andl2. apply IHA2. apply H.
   * apply ad_btmr.
   * clear IHB1 IHB2. apply disj_spec_arrow in H. destruct H.
     apply ad_andl1. apply IHA1. apply H.
     apply ad_andl2. apply IHA2. apply H.
   * clear IHA1 IHA2. apply disj_spec_union1 in H. destruct H.
     apply ad_orr. apply IHB1. apply H.
     apply IHB2. apply H0.
    (* Todo: Problamatic Case - To Be Proved *)

   * (*clear IHA1 IHA2 IHB1 IHB2.*) 
     apply disj_btm_spec in H.
     apply BL_completeness in H.
     apply ad_and_and in H.
     apply H.
Qed.
 
 (*apply btm_like_and_disjoint.
   apply BL_completeness. unfold btmLikeSpec. intros. unfold not. intros.
   specialize (H (t_and (t_and A1 A2) B)).
   assert ((t_and (t_and A1 A2) B) <: (t_and A1 A2) /\ (t_and (t_and A1 A2) B) <: B) by auto.
   lets: H H2.
   specialize (H3 A).
   lets: H3 H0 H1. false.*)
Admitted.


(* Following Disj_completeness1 is just for test *)
Lemma Disj_completeness1 : forall A B, A *s B -> A *a B.
Proof.
  (* Dijointness completeness proof *)
induction A; unfold DisjSpec; unfold btmLikeSpec; unfold not; intros.
  (* Top Case *)
 + specialize (H B).
   assert (B <: typ_top /\ B <: B) by auto.
   lets: H H0.
   apply BL_completeness in H1.
   apply Disj_sym.
   apply BL_disj. apply H1.
   (* Int Case *)
 + induction B.
  * specialize (H t_int).
    assert (t_int <: t_int /\ t_int <: typ_top) by auto.
    lets: H H0.
    unfold btmLikeSpec in H1. unfold not in H1.
    specialize (H1 t_int).
    assert (Ord t_int) by auto.
    assert (t_int <: t_int) by auto.
    lets: H1 H2 H3. inversion H4.
  * specialize (H t_int).
    assert (t_int <: t_int /\ t_int <: t_int) by auto.
    lets: H H0.
    unfold btmLikeSpec in H1. unfold not in H1.
    specialize (H1 t_int).
    assert (Ord t_int) by auto.
    assert (t_int <: t_int) by auto.
    lets: H1 H2 H3. inversion H4.
  * apply ad_btmr. apply bl_bot.
  * apply ad_intl.
  * apply ad_orr.
    apply IHB1. intros. apply H with (C:=C) (A:=A). destruct H0. 
    split. apply H0. auto. auto. auto.
    apply IHB2. intros. apply H with (C:=C) (A:=A). destruct H0. split.
     apply H0. auto. auto. auto.
  * (* Intersection and Int case - requires hard helping lemma *) 
    specialize (H (t_and t_int (t_and B1 B2))).
    assert (H': (t_and t_int (t_and B1 B2) <: t_int) /\ t_and t_int (t_and B1 B2) <: t_and B1 B2).
    auto.
    lets: H H'.
    apply sym_btm_like in H0.
    apply btm_like_spec_and in H0.
    (* Intersection and Int case - or lemma *)
    apply disj_spec_int in H0.
    destruct H0.
    apply ad_andr1.
    unfold DisjSpec in H0.
    forwards: IHB1.
    intros. unfold btmLikeSpec in H0. unfold not in H0.
    apply H0 with (C:=C) (A:=A).
    destruct H1.
    split. auto. auto. auto. auto. auto.
    apply ad_andr2.
    forwards: IHB2.
    unfold DisjSpec in H0. intros.
    unfold btmLikeSpec in H0. unfold not in H0.
    apply H0 with (C:=C) (A:=A). destruct H1.
    split. auto. auto. auto. auto. auto.
    (* Bottom Case *)
 + apply ad_btml. apply bl_bot.
    (* Arrow Case *)
 + clear IHA1 IHA2.
   induction B.
  * specialize (H (t_arrow A1 A2)).
    assert (t_arrow A1 A2 <: t_arrow A1 A2 /\ t_arrow A1 A2 <: typ_top) by auto.
    lets: H H0.
    unfold btmLikeSpec in H1. unfold not in H1.
    specialize (H1 (t_arrow A1 A2)).
    assert (Ord (t_arrow A1 A2)) by auto.
    assert ( (t_arrow A1 A2) <: (t_arrow A1 A2)) by auto.
    lets: H1 H2 H3. false.
  * apply ad_intr.
  * apply ad_btmr. apply bl_bot.
  * specialize (H (t_arrow typ_top t_bot)).
    assert ((t_arrow typ_top t_bot) <: (t_arrow A1 A2) /\ (t_arrow typ_top t_bot) <: (t_arrow B1 B2)) by auto.
    lets: H H0.
    unfold btmLikeSpec in H1. unfold not in H1.
    specialize (H1 (t_arrow typ_top t_bot)).
    assert (Ord (t_arrow typ_top t_bot)) by auto.
    assert ((t_arrow typ_top t_bot) <: (t_arrow typ_top t_bot)) by auto.
    lets: H1 H2 H3. false.
  * apply ad_orr.
    apply IHB1. intros. destruct H0. apply H with (C:=C) (A:=A).
    split. auto. auto. auto. auto.
    apply IHB2. intros. destruct H0. apply H with (C:=C) (A:=A).
    split. auto. auto. auto. auto.
  * specialize (H (t_and (t_arrow A1 A2) (t_and B1 B2))).
    assert (t_and (t_arrow A1 A2) (t_and B1 B2) <: (t_arrow A1 A2) /\ t_and (t_arrow A1 A2) (t_and B1 B2) <: (t_and B1 B2)).
    auto.
    lets: H H0.
    apply sym_btm_like in H1.
    apply btm_like_spec_and in H1.
    apply disj_spec_arrow in H1.
    destruct H1.
    apply ad_andr1.
    apply IHB1. unfold DisjSpec in H1.
    intros. 
    apply H1 with (C:=C) (A:=A). destruct H2.
    split. auto. auto. auto. auto.
    apply ad_andr2.
    apply IHB2. unfold DisjSpec in H1.
    intros. 
    apply H1 with (C:=C) (A:=A). destruct H2.
    split. auto. auto. auto. auto.
    (* Union Case *)
 + apply ad_orl.
   apply IHA1. unfold DisjSpec. unfold btmLikeSpec. unfold not. intros. destruct H0. 
   apply H with (C:=C) (A:=A). split. auto. auto. auto. auto.
   apply IHA2. unfold DisjSpec. unfold btmLikeSpec. unfold not. intros.
   destruct H0. apply H with (C:=C) (A:=A). split. auto. auto. auto. auto.
  (* Intersection Case *)
 + assert ((t_and A1 A2) *s B) by auto.
   apply disj_btm_spec in H0.
   apply BL_completeness in H0.
   apply btm_like_and_disjoint in H0.
   apply H0.
 
 (*apply btm_like_and_disjoint.
   apply BL_completeness. unfold btmLikeSpec. intros. unfold not. intros.
   specialize (H (t_and (t_and A1 A2) B)).
   assert ((t_and (t_and A1 A2) B) <: (t_and A1 A2) /\ (t_and (t_and A1 A2) B) <: B) by auto.
   lets: H H2.
   specialize (H3 A).
   lets: H3 H0 H1. false.*)
Qed.



(* Following BL_completeness1 lemma is just for test *)
Lemma BL_completeness1 : forall A, btmLikeSpec A -> bottomlike A.
Proof.
  (* Bottom Like completeness proof *)
induction A; unfold btmLikeSpec; intro.
 + specialize (H typ_top).
  unfold not in H.
  assert (Ord typ_top) by auto.
  assert (typ_top <: typ_top) by auto.
  lets: H H0 H1. false.
 + specialize (H t_int).
  unfold not in H.
  assert (Ord t_int) by auto.
  assert (t_int <: t_int) by auto.
  lets: H H0 H1. false.
 + apply bl_bot.
 + specialize (H (t_arrow A1 A2)).
  unfold not in H.
  assert (Ord (t_arrow A1 A2)) by auto.
  assert ((t_arrow A1 A2) <: (t_arrow A1 A2)) by auto.
  lets: H H0 H1. false.
 + apply bl_or.
  * apply IHA1. unfold btmLikeSpec.
  intros.
  unfold not in *. intros.
  specialize (H A).
  assert (A <: (t_union A1 A2)) by auto.
  apply H. auto. auto.
  * apply IHA2. unfold btmLikeSpec.
  intros.
  unfold not in *. intros.
  specialize (H A).
  assert (A <: (t_union A1 A2)) by auto.
  apply H. auto. auto.
 + clear IHA1. clear IHA2. 
  apply bl_andsub.
  assert (btmLikeSpec (t_and A1 A2)) by auto.
  lets: btm_like_spec_and A1 A2 H0.
  apply Disj_completeness in H1. apply H1.
Qed.



(* Following Disjoint Completeness lemma is not mutually dependent *)
Lemma Disj_completeness1 : forall A B, A *s B -> A *a B.
Proof.
induction A; unfold DisjSpec; intros; eauto.
- induction B; eauto.
  admit.
  admit.
  admit.
  assert (typ_top *s (t_union B1 B2)). eauto.
  assert (btmLikeSpec (t_and typ_top (t_union B1 B2))). eauto.
  apply top_btmlike in H1.
 (* apply humbty in H1. destruct H1.
  assert (btmLikeSpec (t_and typ_top B1)). eauto.
  assert (btmLikeSpec (t_and typ_top B2)). eauto.
  apply ad_orr.
  apply Disj_sym.
  forwards*: IHB1.
  apply Disj_sym.
  forwards*: IHB2.*)
  admit.
  assert (typ_top *s (t_and B1 B2)). eauto.
  assert (btmLikeSpec (t_and typ_top (t_and B1 B2))). eauto.
  apply top_btmlike in H1.

(*
We have a circular dependency in the following case.
This case depends upon BL-completeness,
and BL-completeness depends upon Dis-completeness

H0: typ_top *s t_and B1 B2
H1: btmLikeSpec (t_and B1 B2)
-----------------------------1/1
typ_top *a t_and B1 B2
*)
 
  admit.

(*  specialize (H B).
  forwards*: H.
  apply BL_completeness in H0.
  apply Disj_sym.
  (*TODO: Prove BL_disj*)
  apply BL_disj. auto.*)
- induction B; eauto.
  + specialize (H t_int).
    forwards*: H.
    unfold btmLikeSpec in H0. unfold not in H0.
    specialize (H0 t_int).
    forwards*: H0.
  + specialize (H t_int).
    forwards*: H.
    unfold btmLikeSpec in H0. unfold not in H0.
    specialize (H0 t_int).
    forwards*: H0.
  + apply ad_orr. 
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
    forwards*: IHB2.
- induction B; eauto.
  + specialize (H (t_arrow A1 A2)).
    forwards*: H.
    unfold btmLikeSpec in H0. unfold not in H0.
    specialize (H0 (t_arrow A1 A2)).
    forwards*: H0.
  + specialize (H (t_arrow (t_union A1 B1) t_bot)).
    forwards*: H.
    unfold btmLikeSpec in H0. unfold not in H0.
    specialize (H0 (t_arrow (t_union A1 B1) t_bot)).
    forwards*: H0.
  + apply ad_orr.
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
    forwards*: IHB2.
- apply ad_orl.
  apply IHA1; unfold DisjSpec; intros; destruct H0; apply H; eauto.
  apply IHA2; unfold DisjSpec; intros; destruct H0; apply H; eauto.
- assert (DisjSpec (t_and A1 A2) B) by auto.
(*apply test61 in H0.
  destruct H0.
  apply ad_andl1.
  eapply IHA1; eauto.
  destruct H0.
  apply ad_andl2.
  eapply IHA2; eauto.
  apply ad_and_disl.
  eapply IHA1; eauto.*)
  dependent induction B; eauto.
 + apply disj_spec_and_top in H0.
  admit.
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
   eapply IHB1; eauto.
   eapply IHB2; eauto.
 + admit.
Admitted.