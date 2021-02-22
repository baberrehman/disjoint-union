
(*
Update started on February 19, 2021
*)

(*
This file contains the updates suggested by Bruno.

Subtying algorithm with Coq definition added in this version

A *a B = findsubtypes A `inter` findsubtypes B == []

FindSubtypes B = []
-------------------
     B <: A

Transitivity Proved

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

(****************************************)
(**********  FindSubtypes    ************)
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
 | s_disj : forall A B,
     FindSubtypes A = [] ->
     A <: B
where "A <: B" := (subtyping A B) : env_scope.

Hint Constructors pexpr rexpr value uexpr findtype subtyping lc_exp ok okt.

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
| o_top : Ord t_top
| o_int : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2).
(*| o_union : forall t1 t2, Ord t1 -> Ord t2 -> Ord (t_union t1 t2).*)

Hint Constructors Ord : core.


(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)

Lemma list_empty_decide : forall l : list typ, (l = []) \/ (l <> []).
Proof.
  intros. induction l. auto.
  destruct IHl. right. 
  unfold not. intros. inversion H0.
  unfold not in *.
  right. intros.
  inversion H0.
Defined.

Lemma elem_append_in_list : forall (a : typ) (l : list typ), set_In a (a :: l).
Proof.
  intros. simpl. auto.
Defined.

Lemma a3 : forall (a1 a2 : typ) (l1 l2 : list typ), 
set_In a1 (a1 :: l1 `union` a2 :: l2).
Proof.
  intros.
  lets: elem_append_in_list a1 l1.
  apply set_union_intro1. auto.
Defined.

Lemma a4 : forall (a1 : typ) (l1 : list typ), 
set_In a1 ([] `union` a1 :: l1).
Proof.
  intros.
  lets: elem_append_in_list a1 l1.
  apply set_union_intro2. auto.
Defined.

Lemma union_findsubtypes_empty_elim : forall l1 A B l2 l3, 
l1 = FindSubtypes (t_union A B) /\ 
l2 = FindSubtypes A /\ l3 = FindSubtypes B ->
l1 = [] -> l2 = [] /\ l3 = [].
Proof.
    intros.
    destructs H.
    simpl in H.
    destruct l2.
    destruct l3.
    auto.
    rewrite <- H2 in H.
    rewrite H0 in H.
    rewrite <- H1 in H.
    lets: a4 t l3.
    rewrite <- H in H3.
    inverts H3.
    rewrite H0 in H.
    rewrite <- H1 in H.
    destruct (FindSubtypes B).
    simpl in H. inverts H.
    lets: a3 t t0 l2 l.
    rewrite <- H in H3.
    inverts H3.
Defined.

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
lets: union_findsubtypes_empty_elim  (FindSubtypes (t_union A B)) A B.
lets: H0 (FindSubtypes A) (FindSubtypes B).
forwards*: H1.
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
   + inversion H. simpl in H0; inversion H0.
   + inversion H. simpl in H0; inversion H0.
   + inversion H. simpl in H0; inversion H0.
   + inverts* H.
    * destruct IHB1; auto.
      left. apply set_union_intro. left*.
      destruct H as [x1 [x2]]. destruct H. inversion H.
    * destruct IHB2; auto.
      left. apply set_union_intro. right*.
      destruct H as [x1 [x2]]. destruct H. inversion H.
    * simpl in H0; inversion H0. 
   + apply sub_and in H. destruct H.
     destruct IHB1; auto.
    * destruct IHB2; auto.
      left. apply set_inter_intro; auto.
      destruct H2 as [x1 [x2]]. destruct H2. inversion H2.
    * destruct H1 as [x1 [x2]]. destruct H1. inversion H1.
  - induction B; simpl; auto.
   + inversion H. simpl in H0; inversion H0.
   + inversion H. simpl in H0; inversion H0.
   + inverts* H.
    * destruct IHB1; auto.
      left. apply set_union_intro. left*.
      destruct H as [x1 [x2]]. destruct H. inversion H.
    * destruct IHB2; auto.
      left. apply set_union_intro. right*.
      destruct H as [x1 [x2]]. destruct H. inversion H.
    * simpl in H0; inversion H0. 
   + apply sub_and in H. destruct H.
     destruct IHB1; auto.
    * destruct IHB2; auto.
      left. apply set_inter_intro; auto.
      destruct H2 as [x1 [x2]]. destruct H2. inversion H2.
    * destruct H1 as [x1 [x2]]. destruct H1. inversion H1.
  - induction B; simpl; auto.
   + right. exists* t1 t2.
   + inversion H. simpl in H0; inversion H0.
   + inversion H. simpl in H0; inversion H0.
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
    * simpl in H0; inversion H0.
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

Lemma ord_sub_findsubtypes_not_empty : forall A B, 
Ord A -> A <: B ->
(FindSubtypes B) <> [].
Proof.
  unfold not. intros.
  apply ord_in_findsubtypes2 in H0; auto.
  destruct H0.
  - rewrite H1 in H0. inversion H0.
  - destruct H0 as [x1 [x2]]. destruct H0.
    rewrite H1 in H2. inversion H2.
Defined.

Lemma list_append_findsubtypes_in : forall t l A, (t :: l) = FindSubtypes A ->
set_In t (FindSubtypes A).
Proof.
  intros.
  rewrite <- H.
  apply elem_append_in_list.
Defined.

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


Lemma inter_not_empty_elim : forall A l,
l = FindSubtypes A ->
l <> [] ->
set_In t_top l \/
set_In t_int l \/ 
set_In (t_arrow t_top t_bot) l.
Proof.
  intros.
  destruct l.
  contradiction.
  lets: elem_append_in_list t l.
  rewrite H in H1.
  lets: elem_in_findsubtypes_ord A t. 
  lets H1': H1.
  apply H2 in H1.
  induction H1.
  left. apply elem_append_in_list.
  right. left. apply elem_append_in_list.
  apply arrow_in_top_bot in H1'. inverts H1'.
  right. right. apply elem_append_in_list.
Defined.


Lemma not_in5 : forall A B,
not (set_In t_int (FindSubtypes (t_and A B))) /\
not (set_In (t_arrow t_top t_bot) (FindSubtypes (t_and A B))) /\
not (set_In t_top (FindSubtypes (t_and A B))) ->
(FindSubtypes (t_and A B)) = [].
Proof.
  intros.
  lets: list_empty_decide (FindSubtypes (t_and A B)).
  destruct H0. 
  - rewrite H0. auto.
  - apply inter_not_empty_elim with (A:=(t_and A B)) in H0.
    destruct H. destruct H1.
    destruct H0.
    contradiction.
    destruct H0.
    contradiction.
    contradiction.
    auto.
Defined.

Lemma demorgan1 : forall P Q : Prop, ~ P /\ ~ Q -> ~ (P \/ Q).
Proof.
  intros.
  destruct H.
  unfold not in *.
  intros.
  destruct H1.
  apply H; auto.
  apply H0; auto.
Defined.

Lemma demorgan2 : forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  intros.
  unfold not in *.
  split.
  intros. apply H. auto.
  intros. apply H. auto.
Defined.

Lemma demorgan3 : forall P Q R : Prop, ~ (P \/ Q \/ R) -> ~ P /\ ~ Q /\ ~ R.
Proof.
  intros.
  unfold not in *.
  split.
  intros. apply H. auto.
  split.
  intros. apply H. auto.
  intros. apply H. auto.
Defined.

Lemma elem_in_findsubtypes_sub : forall A B,
(set_In B (FindSubtypes A)) -> B <: A.
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
    apply s_orb. apply IHA1; auto. 
    apply s_orc. apply IHA2; auto.
  - simpl in H.
    apply s_anda.
    apply set_inter_elim1 in H. 
    apply IHA1; auto.
    apply set_inter_elim2 in H. 
    apply IHA2; auto.
Defined.


Lemma a1 : forall A B,
FindSubtypes A = [] -> B <: A -> not (Ord B).
Proof.
    intros.
    unfold not. intros.
    lets: ord_in_findsubtypes2 B A.
    inverts H1.
    - destruct H2; auto.
      rewrite H in H1. inverts H1.
      destruct H1 as [x1 [x2]].
      destruct H1. inversion H1.
    - destruct H2; auto.
      rewrite H in H1. inverts H1.
      destruct H1 as [x1 [x2]].
      destruct H1. inversion H1.
    - destruct H2; auto.
      rewrite H in H1. inverts H1.
      destruct H1 as [x1 [x2]].
      destruct H1. rewrite H in H2.
      inverts H2.
Defined.

Lemma a6 : forall A1 A2,
FindSubtypes (t_and A1 A2) = [] -> 
not (exists B, Ord B /\ B <: (t_and A1 A2)).
Proof.
  unfold not. intros.
  destruct H0. destruct H0.
  lets: ord_sub_findsubtypes_not_empty x (t_and A1 A2) H0 H1.
  contradiction.
Defined.

Lemma a7 : forall A1 A2,
FindSubtypes (t_and A1 A2) = [] -> 
forall B, Ord B -> not(B <: (t_and A1 A2)).
Proof.
  unfold not. intros.
  lets: ord_sub_findsubtypes_not_empty B (t_and A1 A2) H1. auto.
  contradiction.
Defined.

Lemma a9 : forall A1 A2,
forall B, Ord B -> not(B <: (t_and A1 A2)) ->
not (set_In B (FindSubtypes (t_and A1 A2))).
Proof.
  intros. unfold not. intros.
  apply elem_in_findsubtypes_sub in H1.
  contradiction.
Defined.

Lemma a10 : forall A,
FindSubtypes A <> [] -> exists B, set_In B (FindSubtypes A).
Proof.
  intros.
  destruct (FindSubtypes A).
  contradiction.
  lets: elem_append_in_list t l.
  exists t. auto.
Defined.

Lemma a11 : forall A, not (Ord A) ->
forall B, Ord B -> not (B <: A) -> not (set_In B (FindSubtypes A)).
Proof.
intros.
unfold not in *. intros.
lets: elem_in_findsubtypes_sub A B H2.
contradiction.
Defined.

Lemma a12 : forall A x, set_In x (FindSubtypes A) ->
forall B, A <: B -> set_In x (FindSubtypes B).
Proof.
  intros.
  inductions H0; eauto.
  - lets H': H.
    apply elem_in_findsubtypes_ord in H'.
    simpl. destruct H'. auto. auto.
    apply arrow_in_top_bot in H.
    rewrite H. auto.
  - simpl in H. inversion H.
  - simpl in H. apply set_union_elim in H.
    destruct H. 
    apply IHsubtyping1; auto.
    apply IHsubtyping2; auto.
  - simpl. apply set_union_intro1. apply IHsubtyping; auto.
  - simpl. apply set_union_intro2. apply IHsubtyping; auto.
  - simpl. apply set_inter_intro.
    apply IHsubtyping1; auto.
    apply IHsubtyping2; auto.
  - simpl in H. apply set_inter_elim1 in H.
    apply IHsubtyping; auto.
  - simpl in H. apply set_inter_elim2 in H.
    apply IHsubtyping; auto.
  - rewrite H0 in H.
    inverts H.
Defined.

Lemma a5 : forall A1 A2 B,
FindSubtypes (t_and A1 A2) = [] -> 
B <: (t_and A1 A2) -> FindSubtypes B = [].
Proof.
    intros.
    lets: list_empty_decide (FindSubtypes B).
    destruct H1. auto.
    lets: a10 B H1.
    destruct H2.
    lets: a12 B x H2 (t_and A1 A2) H0.
    rewrite H in H3. inverts H3.
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
- induction C; intros; try solve [inverts* H0].
  inverts* H0. inverts* H1.
  inverts* H0. inverts* H1.
  induction A; try solve[inverts* H].
  inverts* H0. inverts* H. 
- intros. apply sub_or in H0. destruct H0.
  inductions H; eauto.
- intros. apply sub_and in H. destruct H.
  inductions H0; eauto.
  assert (A <: t_and B1 B2) by auto.
  apply s_disj.
  apply a5 with (A1:=B1) (A2:=B2). auto. auto.
Defined.

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

(*

A *s B = not (exists C, Ord C -> C <: A /\ C <: B)

*)

Definition DisjSpec A B := forall C, Ord C -> not (C <:  (t_and A B)).
Notation "A *s B" := (DisjSpec A B) (at level 80).

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

(*
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
*)

Definition DisjAlgo A B := ((FindSubtypes A) `inter` (FindSubtypes B)) = [].
Notation "A *a B" := (DisjAlgo A B) (at level 80).

(**********************************)
(****  DisjSpec Properties  ****)
(**********************************)

Lemma ord_sub_bot_false : forall A, Ord A -> A <: t_bot -> False.
Proof.
  intros.
  dependent induction H; inversion H0.
  simpl in H; inversion H.
  simpl in H; inversion H.
  simpl in H; inversion H.
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

Lemma ord_sub_and_int_arrow : forall A B C,
Ord A -> A <: t_and B C ->
(t_int <: B /\ t_int <: C) \/ (t_arrow t_top t_bot <: B /\ t_arrow t_top t_bot <: C).
Proof.
  introv H. gen B C.
  dependent induction A; intros; try solve [inversion H].
  - left. inverts* H0. split.
    apply sub_transitivity with (A:=t_int) (B:=t_top) (C:=B); auto.
    apply sub_transitivity with (A:=t_int) (B:=t_top) (C:=C); auto.
    simpl in H1; inversion H1.
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

(*  
**************************************************************
Another approach to prove ord_sub_findsubtypes_not_empty lemma
**************************************************************

  intros A B H. gen B.
  induction B; unfold not; intros H1 H2; 
  try solve [simpl in H2; inversion H2].
  - apply ord_sub_bot_false in H1; auto.
  - (*apply union_findsubtypes_empty_elim in H2. destruct H2.
    apply ord_sub_union in H1; auto. destruct H1.
    unfold not in IHB1; apply IHB1; auto.
    unfold not in IHB2; apply IHB2; auto.*)
    apply ord_in_findsubtypes2 in H1; auto.
    destruct H1.
    rewrite H2 in H0. inversion H0.
    destruct H0 as [x1 [x2]]. destruct H0.
    rewrite H2 in H1. inversion H1.
  - apply ord_in_findsubtypes2 in H1; auto.
    destruct H1.
    rewrite H2 in H0. inversion H0.
    destruct H0 as [x1 [x2]]. destruct H0.
    rewrite H2 in H1. inversion H1.
Defined.
*)

Lemma Disj_soundness : forall A B, A *a B -> A *s B.
Proof.
(* Disj_soundness Soundness Proof *)
intros.
unfold DisjAlgo in H.
unfold DisjSpec. unfold not. intros.
apply ord_sub_findsubtypes_not_empty in H1; auto.
Qed.

Definition DisjSpec1 A B := not (exists C, Ord C /\ C <: (t_and A B)).
Notation "A *s1 B" := (DisjSpec1 A B) (at level 80).

Lemma disj_disj1 : forall A B, A *s B -> A *s1 B.
Proof.
  unfold DisjSpec. unfold DisjSpec1. unfold not. intros.
  destruct H0. destruct H0.
  specialize (H x).
  apply H; auto.
Defined.

Lemma disj1_disj : forall A B, A *s1 B -> A *s B.
Proof.
  unfold DisjSpec. unfold DisjSpec1. unfold not. intros.
  apply H. exists* C.
Defined.

Lemma exists_inter_empty : exists B C,
(FindSubtypes B `inter` FindSubtypes C) = [].
Proof.
  exists t_int (t_arrow t_top t_bot).
  simpl. auto.
Defined.

Lemma decidability: forall A B, Ord A -> 
(set_In A (FindSubtypes B)) \/ ~(set_In A (FindSubtypes B)) \/
(exists t1 t2, A = t_arrow t1 t2 /\ set_In (t_arrow t_top t_bot) (FindSubtypes B)).
Proof.
  induction A; try solve [intros; inversion H].
  - intros. induction B; auto.
   + left. simpl. auto.
   + right. left. simpl. unfold not. 
     intros. inverts* H0. inverts* H1.
   + right. left. simpl. unfold not. 
     intros. inverts* H0. inverts* H1.
   + destruct IHB1. 
     left. simpl. apply set_union_intro1. auto.
     destruct IHB2. 
     left. simpl. apply set_union_intro2. auto.
     destruct H0. destruct H1. 
     right. left. unfold not in *. intros.
     simpl in H2. apply set_union_elim in H2.
     destruct H2. apply H0; auto. apply H1; auto.
     destruct H1 as [x1 [x2]]. destruct H1. inversion H1.
     destruct H0 as [x1 [x2]]. destruct H0. inversion H0.
   + destruct IHB1. destruct IHB2.
     left. simpl. apply set_inter_intro; auto.
     destruct H1. 
     right. left. unfold not in *.
     intros. simpl in H2. apply H1.
     apply set_inter_elim2 in H2. auto.
     destruct H1 as [x1 [x2]]. destruct H1. inversion H1.
     destruct H0. 
     right. left. unfold not in *. 
     intros. simpl in H1. apply H0.
     apply set_inter_elim1 in H1. auto.
     destruct H0 as [x1 [x2]]. destruct H0. inversion H0.
  - intros. induction B; auto.
   + left. simpl. auto.
   + left. simpl. auto.
   + right. left. simpl. unfold not. 
     intros. inverts* H0. inverts* H1.
   + destruct IHB1. 
     left. simpl. apply set_union_intro1. auto.
     destruct IHB2. 
     left. simpl. apply set_union_intro2. auto.
     destruct H0. destruct H1. 
     right. left. unfold not in *. intros.
     simpl in H2. apply set_union_elim in H2.
     destruct H2. apply H0; auto. apply H1; auto.
     destruct H1 as [x1 [x2]]. destruct H1. inversion H1.
     destruct H0 as [x1 [x2]]. destruct H0. inversion H0.
   + destruct IHB1. destruct IHB2.
     left. simpl. apply set_inter_intro; auto.
     destruct H1. 
     right. left. unfold not in *.
     intros. simpl in H2. apply H1.
     apply set_inter_elim2 in H2. auto.
     destruct H1 as [x1 [x2]]. destruct H1. inversion H1.
     destruct H0. 
     right. left. unfold not in *. 
     intros. simpl in H1. apply H0.
     apply set_inter_elim1 in H1. auto.
     destruct H0 as [x1 [x2]]. destruct H0. inversion H0.
  - intros. induction B; auto.
   + right. right. exists A1 A2. split*.
     simpl. auto.
   + right. left. simpl. unfold not. 
     intros. inverts* H0. inverts* H1.
   + right. right. simpl. exists A1 A2. split*.
   + destruct IHB1. 
     left. simpl. apply set_union_intro1. auto.
     destruct IHB2. 
     left. simpl. apply set_union_intro2. auto.
     destruct H0. destruct H1. 
     right. left. unfold not in *. intros.
     simpl in H2. apply set_union_elim in H2.
     destruct H2. apply H0; auto. apply H1; auto.
     destruct H1 as [x1 [x2]]. destruct H1.
     right. right. exists A1 A2. split*.
     simpl. apply set_union_intro. right*.
     destruct H0 as [x1 [x2]]. destruct H0.
     right. right. exists A1 A2. split*.
     simpl. apply set_union_intro. left*.
   + destruct IHB1. destruct IHB2.
     left. simpl. apply set_inter_intro; auto.
     destruct H1. 
     right. left. unfold not in *.
     intros. simpl in H2. apply H1.
     apply set_inter_elim2 in H2. auto.
     destruct H1 as [x1 [x2]]. destruct H1.
     right. right. exists A1 A2. split*.
     lets H0': H0.
     apply arrow_in_top_bot in H0'. inverts H0'.
     simpl. apply set_inter_intro; auto.
     destruct H0. 
     right. left. unfold not in *. 
     intros. simpl in H1. apply H0.
     apply set_inter_elim1 in H1. auto.
     destruct H0 as [x1 [x2]]. destruct H0.
     destruct IHB2.
     lets H2': H2. apply arrow_in_top_bot in H2'. inverts H2'.
     left. simpl. apply set_inter_intro; auto.
     destruct H2.
     right. left. unfold not in *. intros.
     apply H2. simpl in H3. apply set_inter_elim2 in H3. auto.
     destruct H2 as [x3 [x4]]. destruct H2.
     right. right. exists A1 A2. split*.
     simpl. apply set_inter_intro; auto.
Defined.

Lemma not_in_inter_intro1 : forall A B, not (set_In A (FindSubtypes B)) ->
forall C, not (set_In A (FindSubtypes B `inter` FindSubtypes C)).
Proof.
  unfold not in *. intros.
  apply set_inter_elim1 in H0; apply H; auto.
Defined.

Lemma not_in_inter_intro2 : forall A C, not (set_In A (FindSubtypes C)) ->
forall B, not (set_In A (FindSubtypes B `inter` FindSubtypes C)).
Proof.
  unfold not in *. intros.
  apply set_inter_elim2 in H0; apply H; auto.
Defined.

Lemma not_in_union_elim : forall A B C, 
not (set_In A (FindSubtypes (t_union B C))) ->
not (set_In A (FindSubtypes B)) /\ not (set_In A (FindSubtypes C)).
Proof.
  unfold not in *. intros.
  split; intros.
  apply H. simpl. apply set_union_intro1. auto.
  apply H. simpl. apply set_union_intro2. auto.
Defined.

Definition DisjAlgo1 A B := (FindSubtypes (t_and A B)) = [].
Notation "A *a1 B" := (DisjAlgo1 A B) (at level 80).

Lemma disja_disja1 : forall A B, DisjAlgo A B -> DisjAlgo1 A B.
Proof.
  unfold DisjAlgo.
  unfold DisjAlgo1.
  intros. simpl. auto.
Defined.

Lemma disja1_disja : forall A B, DisjAlgo1 A B -> DisjAlgo A B.
Proof.
  unfold DisjAlgo.
  unfold DisjAlgo1.
  intros. simpl in H. auto.
Defined.

Lemma Disj_completeness2 : forall A B,  A *s B -> A *a1 B.
Proof.
  intros.
  apply disj_disj1 in H.
  unfold DisjSpec1 in H. unfold not in H.
  unfold DisjAlgo1.
  eapply not_in5.
  apply demorgan3. unfold not. intros.
  destruct H0.
  lets H0': H0.
  apply elem_in_findsubtypes_sub in H0'.
  lets H0'': H0.
  apply elem_in_findsubtypes_ord in H0''.
  apply H. exists t_int. split*.
  destruct H0.
  lets H0': H0.
  apply elem_in_findsubtypes_sub in H0'.
  lets H0'': H0.
  apply elem_in_findsubtypes_ord in H0''.
  apply H. exists (t_arrow t_top t_bot). split*.
  lets H0': H0.
  apply elem_in_findsubtypes_sub in H0'.
  lets H0'': H0.
  apply elem_in_findsubtypes_ord in H0''.
  apply H. exists t_top. split*.
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