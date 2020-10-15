(* generated by Ott 0.28, locally-nameless from: ../spec/rules.ott *)
Require Import TLC.LibLN.
(*Implicit Types x : var.*)
(** syntax *)

Inductive typ : Set :=  (*r type *)
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ.

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
     findtype  ( (e_ann  ( (e_abs e) )  (t_arrow A B)) )   (t_arrow A B) .

(* defns BottomLike *)
Inductive bottomlike : typ -> Prop :=    (* defn bottomlike *)
 | bl_bot :
     bottomlike t_bot
 | bl_or : forall (A B:typ),
     bottomlike A ->
     bottomlike B ->
     bottomlike (t_union A B).

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
     A *a C ->
     (t_union A B) *a C
 | ad_orr : forall (C A B:typ),
     A *a C ->
     A *a C ->
     C *a (t_union A B)
where "A *a B" := (disjointness A B).

(* defns Subtyping *)
Reserved Notation "A <: B" (at level 80).
Inductive subtyping : typ -> typ -> Prop :=    (* defn subtyping *)
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
where "A <: B" := (subtyping A B) : env_scope.


(****************************************)
(****  Dijoint Specs    ****)
(****************************************)

Definition DisjSpec A B := forall C, C <: A /\ C <: B -> bottomlike C.

Notation "A *s B" := (DisjSpec A B) (at level 80).

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

(** infrastructure *)
Hint Constructors pexpr rexpr value uexpr findtype bottomlike disjointness subtyping typing step lc_exp ok okt.

(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)

Lemma BL_soundness : forall A, bottomlike A -> forall C, A <: C.
Proof.
intros. inductions H. auto. eauto.
Qed.

Lemma sub_or : forall A B C, (t_union A B) <: C -> A <: C /\ B <: C.
Proof.
intros; inductions H; try solve [split*];
specialize (IHsubtyping A B);
forwards* : IHsubtyping.
Qed.

Lemma BL_completeness : forall A, (forall C, A <: C) -> bottomlike A.
Proof.
inductions A; intro; eauto.
 - specialize (H t_bot).
   inversion H.
 - specialize (H t_bot).
   inversion H.
 - constructor.
   apply IHA1. intros.
   specialize (H C).
   apply sub_or in H. destruct~ H.
   apply IHA2. intros.
   specialize (H C).
   apply sub_or in H. destruct~ H.
Qed.

Lemma sub_refl : forall A, A <: A.
  induction A; eauto.
Qed.

Lemma sub_transitivity : forall B A C, A <: B -> B <: C -> A <: C.
Proof.
induction B; intros;
generalize H0 H; clear H0; clear H; generalize A; clear A.
- intros; inductions H; eauto.
- intros; inductions H; eauto.
- induction C; intros; inverts* H0.
  induction A; inverts* H.
- intros. apply sub_or in H0. destruct H0.
  inductions H; eauto.
Qed.