
(*
Update started on February 12, 2021
*)

(*
This file contains the updates suggested by Bruno.

Subtying algorithm with Coq definition added in this version

A *a B = findsubtypes A `inter` findsubtypes B == []

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.

(* Require Import LibTactics. *)
(*Implicit Types x : var.*)
(** syntax *)

Inductive typ : Set :=  (*r type *)
 | t_top : typ
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
 | s_top : forall A, A <: t_top
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
Defined.

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
Defined.

Lemma sub_refl : forall A, A <: A.
  induction A; eauto.
Defined.

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
Defined.


(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
| o_top : Ord t_top
| o_int : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2).
(*| o_union : forall t1 t2, Ord t1 -> Ord t2 -> Ord (t_union t1 t2).*)

Hint Constructors Ord : core.

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec A B := forall C, Ord C -> not (C <:  (t_and A B)).
Notation "A *s B" := (DisjSpec A B) (at level 80).

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

Lemma eq_dec : forall x y:typ, {x = y} + {x <> y}.
Proof.
 decide equality; auto.
Defined.

Notation "l1 `union` l2" := (set_union eq_dec l1 l2) (at level 80).
Notation "l1 `inter` l2" := (set_inter eq_dec l1 l2) (at level 80).

Fixpoint FindSubtypes (A: typ) :=
    match A with
    | t_top         => [t_int; t_arrow t_top t_bot; t_top]
    | t_bot         => []
    | t_int         => [t_int]
    | t_arrow A1 B1 => [t_arrow t_top t_bot]
    | t_union A1 B1 => (FindSubtypes A1) `union` (FindSubtypes B1)
    | t_and A1 B1   => (FindSubtypes A1) `inter` (FindSubtypes B1)
    end.

Eval compute in (FindSubtypes t_int).
Eval compute in (FindSubtypes (t_and t_int t_bot)).
Eval compute in (FindSubtypes (t_and t_int t_top)).
Eval compute in (FindSubtypes (t_and t_top t_int)).
Eval compute in (FindSubtypes (t_and (t_arrow t_int t_int) t_int)).
Eval compute in (FindSubtypes (t_and(t_and (t_arrow t_int t_int) t_int)t_top)).
Eval compute in (FindSubtypes (t_and t_top(t_and (t_arrow t_int t_int) t_int))).
Eval compute in (FindSubtypes (t_union (t_and t_top(t_and (t_arrow t_int t_int) t_int)) (t_and t_top(t_and (t_arrow t_int t_int) t_int)))).
Eval compute in (FindSubtypes (t_and (t_union t_top(t_union (t_arrow t_int t_int) t_int)) (t_union t_top(t_union (t_arrow t_int t_int) t_int)))).
Eval compute in (FindSubtypes (t_and t_top t_bot)).
Eval compute in (FindSubtypes (t_and (t_arrow t_int t_int) (t_arrow (t_arrow t_int t_int) t_int))).
Eval compute in (FindSubtypes (t_union t_int t_bot)).
Eval compute in (FindSubtypes (t_and (t_union t_int (t_arrow t_int t_int)) t_int)).
Eval compute in (FindSubtypes (t_union t_int (t_arrow t_int t_int))).
Eval compute in (FindSubtypes (t_and (t_arrow t_int t_int) t_top)).
Eval simpl in (FindSubtypes (t_and t_top (t_arrow t_int t_int))).

Definition DisjAlgo A B := ((FindSubtypes A) `inter` (FindSubtypes B)) = [].
Notation "A *a B" := (DisjAlgo A B) (at level 80).

(**********************************)
(****  DisjSpec Properties  ****)
(**********************************)

Lemma ord_sub_bot_false : forall A, Ord A -> A <: t_bot -> False.
Proof.
  intros.
  dependent induction H; inversion H0.
Defined.

Lemma not_sub_and : forall A1 A2, forall A, Ord A ->
not (A <: (t_and A1 A2)) -> not((A <: A1) /\ (A <: A2)).
Proof.
  intros.
  unfold not in *. intros.
  apply H0; destruct~ H1.
Defined.

Lemma ord_sub_and_or : forall B C, forall A, Ord A ->
not (A <: (t_and B C)) -> not(A <: B) \/ not(A <: C) \/ not (A <: (t_and B C)).
Proof.
  intros.
  unfold not in *. auto.
Defined.

Lemma not_sub_or_inv : forall A A1 A2, Ord A -> not (A <: A1) -> not (A <: A2) -> not (A <: (t_union A1 A2)).
Proof.
  intros.
  unfold not in *.
  intros. inductions H; inverts* H2.
Defined.

Lemma btm_sub : forall A, t_bot <: A.
Proof.
  intros; auto.
Defined.

Lemma ord_sub_union : forall A, Ord A -> forall A1 A2, A <: t_union A1 A2 -> A <: A1 \/ A <: A2.
Proof.
  intros A H.
  dependent induction H; intros.
  inverts* H.
  inverts* H.
  inverts* H.
Defined.

Lemma not_sub_and1_inv : forall A A1 A2, Ord A -> not (A <: A1) -> not (A <: (t_and A1 A2)).
Proof.
  intros.
  unfold not in *.
  intros. inductions H; inverts* H1.
Defined.

Lemma not_sub_and2_inv : forall A A1 A2, Ord A -> not (A <: A2) -> not (A <: (t_and A1 A2)).
Proof.
  intros.
  unfold not in *.
  intros. inductions H; inverts* H1.
Defined.

Lemma disj_union_intro : forall A B C, A *s C -> B *s C -> t_union A B *s C.
Proof.
  intros.
  unfold DisjSpec in *. intros.
  unfold not in *. intros.
  specialize (H C0).
  apply H; auto.
  apply sub_and in H2.
  destruct H2.
  lets: ord_sub_union C0 H1 A B H2.
  destruct H4.
  apply s_anda; auto.
  specialize (H0 C0).
  forwards*: H0.
Defined.

Lemma disj_union_elim : forall A B C, A *s t_union B C -> A *s B /\ A *s C.
Proof.
  unfold DisjSpec; unfold not; intros.
  split.
  - intros. apply sub_and in H1. destruct H1.
    specialize (H C0).
    apply H; auto.
  - intros. apply sub_and in H1. destruct H1.
    specialize (H C0).
    apply H; auto.
Defined.

Lemma ord_sub_disj_spec_false : forall A, Ord A -> 
forall B C, B *s C -> A <: (t_and B C) -> False.
Proof.
 unfold DisjSpec; unfold not; intros.
 apply sub_and in H1. destruct H1.
 specialize (H0 A).
 forwards*: H0 H.
Defined.

Lemma Disj_sym_spec : forall A B, A *s B -> B *s A.
Proof.
  unfold DisjSpec; unfold not; intros.
  intros.
  forwards*: H H0.
  apply sub_and in H1. destruct H1.
  apply s_anda; auto.
Defined.

Lemma ord_bot : Ord t_bot -> False.
Proof.
  inversion 1.
Defined.

Lemma ord_and : forall A B, Ord (t_and A B) -> False.
Proof.
  inversion 1.
Defined.

Lemma ord_union : forall A B, Ord (t_union A B) -> False.
Proof.
  inversion 1.
Defined.

(*
Below lemma states that all the elements of FindSubtypes are ordinary.
*)

Lemma elem_in_findsubtypes_ord : forall A B,
(set_In B (FindSubtypes A)) -> Ord B.
Proof.
  intros.
  inductions A.
  - simpl in H.
    destruct H. rewrite <- H. auto.
    destruct H. rewrite <- H. auto.
    destruct H. rewrite <- H. auto.
    inversion H.
  - simpl in H.
    destruct H. rewrite <- H. auto.
    inversion H.
  - simpl in H. inversion H.
  - simpl in H.
    destruct H. rewrite <- H. auto.
    inversion H.
  - simpl in H.
    apply set_union_elim in H. destruct H. 
    apply IHA1; auto. 
    apply IHA2; auto.
  - simpl in H.
    apply set_inter_elim1 in H.
    apply IHA1; auto.
Defined.

Lemma ord_in_findsubtypes : forall A B,
Ord A -> A <: B -> set_In A (FindSubtypes B).
Proof.
  induction 1; intros.
  - induction B; simpl; auto.
    inversion H.
    inverts H.
    inversion H.
    apply set_union_intro.
    inverts* H.
    apply set_inter_intro.
    inverts* H. inverts* H.
  - induction B; simpl; auto.
    inversion H.
    inversion H.
    apply set_union_intro.
    inverts* H.
    apply set_inter_intro.
    inverts* H. inverts* H.
  - induction B; simpl; auto.
    admit.
    inversion H.
    inversion H.
    admit.
    apply set_union_intro.
    inverts* H.
    apply set_inter_intro.
    inverts* H.
    inverts* H.
Admitted.

Lemma ord_in_findsubtypes1 : forall A B,
Ord A -> A <: B -> exists C, C <: A /\ set_In C (FindSubtypes B).
Proof.
  induction 1; intros.
  - induction B; simpl; auto.
    exists* t_top.
    inversion H.
    inversion H.
    inversion H.
    inverts* H.
    destruct IHB1. auto.
    destruct H.
    exists x. split*.
    apply set_union_intro. left*.
    destruct IHB2; auto. destruct H.
    exists x. split*.
    apply set_union_intro. right*.
    apply sub_and in H. destruct H.
    destruct IHB1; auto. destruct H1.
    destruct IHB2; auto. destruct H3.
    admit.
  - induction B; simpl; auto.
    exists* t_int.
    exists* t_int.
    inversion H.
    inversion H.
    inverts* H.
    destruct IHB1; auto. destruct H.
    exists x. split*.
    apply set_union_intro. left*.
    destruct IHB2; auto. destruct H.
    exists x. split*.
    apply set_union_intro. right*.
    apply sub_and in H. destruct H.
    destruct IHB1; auto. destruct H1.
    destruct IHB2; auto. destruct H3.
    exists x. split*.
    apply set_inter_intro. auto.
    admit.
  - induction B; simpl; auto.
    exists* (t_arrow t_top t_bot).
    inversion H.
    inversion H.
    exists* (t_arrow t_top t_bot).
    admit.
Admitted.

Lemma arrow_in_top_bot : forall A B C, 
set_In (t_arrow A B) (FindSubtypes C) ->
t_arrow A B = t_arrow t_top t_bot.
Proof.
  intros. inductions C.
  simpl in H; destruct H; inversion H.
  inversion H0. auto.
  destruct H0. inversion H0. inversion H0.
  simpl in H. destruct H. inversion H. inversion H.
  simpl in H. inversion H.
  simpl in H. destruct H. inversion H. auto. inversion H.
  simpl in H.
  apply set_union_elim in H. destruct H.
  apply IHC1; auto.
  apply IHC2; auto.
  simpl in H.
  apply set_inter_elim1 in H.
  apply IHC1; auto.
Defined.

Lemma ord_in_findsubtypes2 : forall A B,
Ord A -> A <: B -> set_In A (FindSubtypes B) \/ 
(exists t1 t2, A = t_arrow t1 t2 /\ set_In (t_arrow t_top t_bot) (FindSubtypes B)).
Proof.
  induction 1; intros.
  - induction B; simpl; auto.
   + inversion H.
   + inversion H.
   + inversion H.
   + inverts* H.
    * destruct IHB1; auto.
      left. apply set_union_intro. left*.
      destruct H as [x1 [x2]]. destruct H. inversion H.
    * destruct IHB2; auto.
      left. apply set_union_intro. right*.
      destruct H as [x1 [x2]]. destruct H. inversion H.
   + apply sub_and in H. destruct H.
     destruct IHB1; auto.
    * destruct IHB2; auto.
      left. apply set_inter_intro; auto.
      destruct H2 as [x1 [x2]]. destruct H2. inversion H2.
    * destruct H1 as [x1 [x2]]. destruct H1. inversion H1.
  - induction B; simpl; auto.
   + inversion H.
   + inversion H.
   + inverts* H.
    * destruct IHB1; auto.
      left. apply set_union_intro. left*.
      destruct H as [x1 [x2]]. destruct H. inversion H.
    * destruct IHB2; auto.
      left. apply set_union_intro. right*.
      destruct H as [x1 [x2]]. destruct H. inversion H.
   + apply sub_and in H. destruct H.
     destruct IHB1; auto.
    * destruct IHB2; auto.
      left. apply set_inter_intro; auto.
      destruct H2 as [x1 [x2]]. destruct H2. inversion H2.
    * destruct H1 as [x1 [x2]]. destruct H1. inversion H1.
  - induction B; simpl; auto.
   + right. exists* t1 t2.
   + inversion H.
   + inversion H.
   + right. exists* t1 t2.
   + inverts* H.
    * destruct IHB1; auto.
      left. apply set_union_intro. left*.
      destruct H as [x1 [x2]]. destruct H.
      right. exists x1 x2. split*.
      apply set_union_intro. left*.
    * destruct IHB2; auto.
      left. apply set_union_intro. right*.
      destruct H as [x1 [x2]]. destruct H.
      right. exists x1 x2. split*.
      apply set_union_intro. right*.
   + apply sub_and in H. destruct H.
     destruct IHB1; auto.
    * destruct IHB2; auto.
      { left. apply set_inter_intro; auto. }
      { destruct H2 as [x1 [x2]]. destruct H2.
        lets H1': H1.
        apply arrow_in_top_bot in H1'.
        rewrite <- H1' in H3.
        left. apply set_inter_intro; auto. }
    * destruct IHB2; auto.
      { destruct H1 as [x1 [x2]]. destruct H1.
        lets H2': H2.
        apply arrow_in_top_bot in H2'.
        rewrite <- H2' in H3.
        left. apply set_inter_intro; auto. }
      { destruct H1 as [x1 [x2]]. destruct H1.
        destruct H2 as [x3 [x4]]. destruct H2.
        right. exists x1 x2. split*.
        apply set_inter_intro; auto. }
Defined.

Lemma ord_sub_and_int_arrow : forall A B C,
Ord A -> A <: t_and B C ->
(t_int <: B /\ t_int <: C) \/ (t_arrow t_top t_bot <: B /\ t_arrow t_top t_bot <: C).
Proof.
  introv H. gen B C.
  dependent induction A; intros; try solve [inversion H].
  - left. inverts* H0. split.
    apply sub_transitivity with (A:=t_int) (B:=t_top) (C:=B); auto.
    apply sub_transitivity with (A:=t_int) (B:=t_top) (C:=C); auto.
  - left. inverts* H0.
  - right. inverts* H0. split.
    apply sub_transitivity with (A:=t_arrow t_top t_bot) (B:=t_arrow A1 A2) (C:=B); auto.
    apply sub_transitivity with (A:=t_arrow t_top t_bot) (B:=t_arrow A1 A2) (C:=C); auto. 
Defined.

Lemma ord_findsubtypes_not_empty : forall A,
Ord A -> (FindSubtypes A) <> [].
Proof.
  intros A H.
  induction A; unfold not; intros; 
  try solve [simpl in H0; inversion H0; inversion H].
Defined.

Lemma union_findsubtypes_empty_intro : forall A B,
(FindSubtypes A = []) -> (FindSubtypes B = []) ->
((FindSubtypes A) `union` (FindSubtypes B)) = [].
Proof.
  intros.
  induction (FindSubtypes A).
  - rewrite H0. simpl. auto.
  - inversion H.
Defined.

Lemma union_findsubtypes_empty_l : forall A,
([] `union` (FindSubtypes A)) = FindSubtypes A.
Proof.
  intros.
  induction (FindSubtypes A).
  - simpl. auto.
  - admit.
Admitted.

Lemma union_findsubtypes_empty_elim : forall A B,
((FindSubtypes A) `union` (FindSubtypes B)) = [] ->
(FindSubtypes A = []) /\ (FindSubtypes B = []).
Proof.
  intros.
  induction (FindSubtypes A).
  - split*. rewrite union_findsubtypes_empty_l in H. auto.
  - admit.
Admitted.

Lemma ord_sub_findsubtypes_not_empty : forall A B, 
Ord A -> A <: B ->
(FindSubtypes B) <> [].
Proof.
  intros A B H. gen B.
  induction B; unfold not; intros H1 H2; 
  try solve [simpl in H2; inversion H2].
  - apply ord_sub_bot_false in H1; auto.
  - apply union_findsubtypes_empty_elim in H2. destruct H2.
    apply ord_sub_union in H1; auto. destruct H1.
    unfold not in IHB1; apply IHB1; auto.
    unfold not in IHB2; apply IHB2; auto.
  - apply ord_in_findsubtypes2 in H1; auto.
    destruct H1.
    rewrite H2 in H0. inversion H0.
    destruct H0 as [x1 [x2]]. destruct H0.
    rewrite H2 in H1. inversion H1.
Defined.

Lemma Disj_soundness : forall A B, A *a B -> A *s B.
Proof.
(* Disj_soundness Soundness Proof *)
intros.
unfold DisjAlgo in H.
unfold DisjSpec. unfold not. intros.
apply ord_sub_findsubtypes_not_empty in H1; auto.
Qed.

Lemma union_inter_empty : forall A B C,
((FindSubtypes A) `inter` (FindSubtypes B)) = [] ->
((FindSubtypes A) `inter` (FindSubtypes C)) = [] ->
((FindSubtypes A) `inter` (FindSubtypes (t_union B C))) = [].
Admitted.

Lemma inter_sym : forall A B,
((FindSubtypes A) `inter` (FindSubtypes B)) =
((FindSubtypes B) `inter` (FindSubtypes A)).
Admitted.

Lemma top_disj : forall A, t_top *s A ->
(FindSubtypes A) = [].
Admitted.

Lemma int_disj : forall A, t_int *s A ->
((t_arrow t_top t_bot) <: A) \/ (FindSubtypes A) = [].
Admitted.

Lemma Disj_completeness : forall A B,  A *s B -> A *a B.
Proof.
  unfold DisjAlgo. intros.
  inductions A.
 - apply top_disj in H. rewrite H. simpl. auto.
 - simpl (FindSubtypes t_int).
   inductions B.
   admit.
   admit.
   simpl. auto.
   simpl. auto.
   admit.
   simpl (FindSubtypes (t_and B1 B2)).
   admit.
 - simpl. auto.
 - inductions B.
  + admit.
  + compute. auto.
  + simpl. auto.
  + admit.
  + apply disj_union_elim in H. destruct H.
    apply union_inter_empty.
    apply IHB1; auto.
    apply IHB2; auto.
  + admit.
  - apply Disj_sym_spec in H.
    apply disj_union_elim in H. destruct H. 
    apply Disj_sym_spec in H.
    apply Disj_sym_spec in H0.
    rewrite inter_sym.
    apply union_inter_empty.
    rewrite inter_sym.
    apply IHA1; auto.
    rewrite inter_sym.
    apply IHA2; auto.
  - admit.
Admitted. 

