Require Import TLC.LibLN.

(*

This file contains Coq code for syntax 
and disjointness associated with union calculus,
section 3 in paper Union Types with Disjoint Switches.

*)

(** syntax *)

Inductive typ : Set :=  (*r type *)
 | typ_top : typ
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

(* defns wexpr *)
Inductive wexpr : exp -> Prop :=    (* defn wexpr *)
 | wexpr_pexpr : forall (p:exp) (A:typ),
     pexpr p ->
     wexpr (e_ann p A).

(* defns value *)
Inductive value : exp -> Prop :=    (* defn value *)
 | val_wexpr : forall (e:exp),
     wexpr e ->
     value e
 | val_abs : forall (L:vars) e,
    (forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     value (e_abs e).

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
     B *a C ->
     (t_union A B) *a C
 | ad_orr : forall (C A B:typ),
     A *a C ->
     B *a C ->
     C *a (t_union A B)
where "A *a B" := (disjointness A B).

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
where "A <: B" := (subtyping A B) : env_scope.


(****************************************)
(****  Dijoint Specs    ****)
(****************************************)

Definition DisjSpec A B := forall C, C <: A /\ C <: B -> bottomlike C.

Notation "A *s B" := (DisjSpec A B) (at level 80).


Hint Constructors pexpr value wexpr findtype bottomlike disjointness subtyping lc_exp ok okt : core.

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

Require Import Program.Equality.

Lemma Disj_soundness : forall A B, A *a B -> A *s B.
intros. dependent induction H; unfold DisjSpec; intros; eauto.
- destruct H. dependent induction H0; eauto.
  apply sub_or in H. destruct H; eauto.
- destruct H. dependent induction H; eauto.
  apply sub_or in H1. destruct H1; eauto.
- destruct H. induction C; try (dependent destruction H); eauto.
  + inversion H0.
  + apply sub_or in H1. destruct H1; eauto. 
- destruct H. induction C; try (dependent destruction H0); eauto.
  + inversion H.
  + apply sub_or in H. destruct H; eauto.
- destruct H1. dependent induction H1; eauto.
  apply sub_or in H2. destruct H2; eauto.
- destruct H1. dependent induction H2; eauto.
  apply sub_or in H1. destruct H1; eauto.
Qed.

Lemma sub_refl : forall A, A <: A.
  induction A; eauto.
Qed.

Hint Resolve sub_refl : core.

Lemma BL_disj : forall A, bottomlike A -> forall B, A *a B. 
  induction 1; intros; eauto.
Defined.

Lemma Disj_sym : forall A B, A *a B -> B *a A.
  induction 1; eauto.
Defined.

Lemma Disj_completeness : forall A B, A *s B -> A *a B.
induction A; unfold DisjSpec; intros; eauto.
- specialize (H B). destruct H. split; eauto.
  constructor.
  apply ad_orr;
  apply BL_disj; eauto.
- induction B; eauto.
  + specialize (H t_int).
    destruct H; eauto.
    constructor;
    apply BL_disj; eauto.
  + specialize (H t_int).
    forwards*: H. inversion H0.
  + constructor; apply Disj_sym. 
    apply IHB1; intros; destruct H0; apply H; eauto.
    apply IHB2; intros; destruct H0; apply H; eauto.
- induction B; eauto.
  + specialize (H (t_arrow A1 A2)).
    forwards*: H. inversion H0.
  + specialize (H (t_arrow (t_union A1 B1) t_bot)).
    forwards*: H. inversion H0.
  + constructor; apply Disj_sym.
    apply IHB1; intros; destruct H0; apply H; eauto.
    apply IHB2; intros; destruct H0; apply H; eauto.
- constructor.
  apply IHA1; unfold DisjSpec; intros; destruct H0; apply H; eauto.
  apply IHA2; unfold DisjSpec; intros; destruct H0; apply H; eauto.
Qed.

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
Qed.

(*
Equivalance of Disjointness
*)

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
| o_int : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2).

Hint Constructors Ord : core.

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

(*

A *s B = not (exists C, Ord C -> C <: A /\ C <: B)

*)

Definition DisjSpec1 A B := forall C, Ord C -> not (C <: A /\ C <: B).
Notation "A *s1 B" := (DisjSpec1 A B) (at level 80).

Lemma disj_disj1 : forall A B, A *s B -> A *s1 B.
Proof.
  intros.
  unfold DisjSpec in H.
  unfold DisjSpec1. unfold not. intros.
  specialize (H C).
  forwards*: H.
  inductions H2.
  inversion H0.
  inversion H0.
Qed.

Lemma disj1_disj : forall A B, A *s1 B -> A *s B.
Proof.
  intros.
  unfold DisjSpec1 in H.
  unfold DisjSpec. intros.
  inductions C; eauto.
  - assert (Ord t_int) by auto.
    unfold not in H.
    assert (t_int <: typ_top) by auto.
    destruct H0.
    eapply sub_transitivity in H0; eauto.
    eapply sub_transitivity in H3; eauto.
    forwards*: H t_int H1.
  - specialize (H t_int).
    assert (Ord t_int) by auto.
    forwards*: H.
  - specialize (H (t_arrow C1 C2)).
    assert (Ord (t_arrow C1 C2)) by auto.
    forwards*: H.
  - destruct H0.
    apply sub_or in H0. destruct H0.
    apply sub_or in H1. destruct H1.
    constructor; auto.
Qed.