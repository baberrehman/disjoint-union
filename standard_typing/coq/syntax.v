
(*
Update started on April 22, 2021
*)

(*

April 22, 2021:
---------------
-> Bidirectional to standard typing judgement

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.
Require Import Coq.Strings.String.

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
 | e_abs    : exp -> exp
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp.

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
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
end.

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
    | t_top         => [t_int; t_arrow t_top t_bot]
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
 | s_int :
     t_int <: t_int
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

Hint Constructors subtyping lc_exp ok okt : core.

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
| o_int   : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2).
(*| o_union : forall t1 t2, Ord t1 -> Ord t2 -> Ord (t_union t1 t2).*)

Hint Constructors Ord : core.

(***********************************)
(****  FindSubtypes Properties  ****)
(***********************************)

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

Lemma elem_append_in_union1 : forall (a1 a2 : typ) (l1 l2 : list typ), 
set_In a1 (a1 :: l1 `union` a2 :: l2).
Proof.
  intros.
  lets: elem_append_in_list a1 l1.
  apply set_union_intro1. auto.
Defined.

Lemma elem_append_in_union2 : forall (a1 : typ) (l1 : list typ), 
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
    lets: elem_append_in_union2 t l3.
    rewrite <- H in H3.
    inverts H3.
    rewrite H0 in H.
    rewrite <- H1 in H.
    destruct (FindSubtypes B).
    simpl in H. inverts H.
    lets: elem_append_in_union1 t t0 l2 l.
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
  intros. inductions C; try solve [simpl in H; destruct H; inversion H].
 - simpl in H. destruct H. inversion H.
   destruct H. inversion H. auto.
   inversion H.
 - simpl in H. destruct H. inversion H. auto. inversion H.
 - simpl in H.
   apply set_union_elim in H. destruct H.
   apply IHC1; auto.
   apply IHC2; auto.
 - simpl in H.
   apply set_inter_elim1 in H.
   apply IHC1; auto.
Defined.

Lemma ord_in_findsubtypes : forall A B,
Ord A -> A <: B -> set_In A (FindSubtypes B) \/ 
(exists t1 t2, A = t_arrow t1 t2 /\ set_In (t_arrow t_top t_bot) (FindSubtypes B)).
Proof.
  induction 1; intros.
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
  apply ord_in_findsubtypes in H0; auto.
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
 - left. apply elem_append_in_list.
 - apply arrow_in_top_bot in H1'. inverts H1'.
   right. apply elem_append_in_list.
Defined.

Lemma not_in : forall A B,
not (set_In t_int (FindSubtypes (t_and A B))) /\
not (set_In (t_arrow t_top t_bot) (FindSubtypes (t_and A B))) ->
(FindSubtypes (t_and A B)) = [].
Proof.
  intros.
  lets: list_empty_decide (FindSubtypes (t_and A B)).
  destruct H0. 
  - rewrite H0. auto.
  - destructs H. 
    apply inter_not_empty_elim with (A:=(t_and A B)) in H0.
    destruct H0 as [H5 | H5 ].
    contradiction.
    contradiction.
    auto.
Defined.

Lemma demorgan : forall P Q : Prop, 
~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  intros.
  unfold not in *.
  splits; intros; apply H; auto.
Defined.

Lemma elem_in_findsubtypes_sub : forall A B,
(set_In B (FindSubtypes A)) -> B <: A.
Proof.
  intros.
  inductions A.
  - simpl in H.
    destruct H as [H | [H | H ] ]; 
    try solve [rewrite <- H; auto].
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

(*
findsubtypes_empty_not_ord is an interesting property
but is not used in any theorem.
*)
Lemma findsubtypes_empty_not_ord : forall A B,
FindSubtypes A = [] -> B <: A -> not (Ord B).
Proof.
    intros.
    unfold not. intros.
    lets: ord_in_findsubtypes B A.
    inverts H1.
    - destruct H2; auto.
      rewrite H in H1. inverts H1.
      destruct H1 as [x1 [x2]].
      destruct H1. inversion H1.
    - destruct H2; auto.
      rewrite H in H1. simpl in H1. inversion H1.
      destruct H1 as [x1 [x2]]. destruct H1.
      rewrite H in H2. simpl in H2. inversion H2.
Defined.

Lemma findsubtypes_not_empty : forall A,
FindSubtypes A <> [] -> exists B, set_In B (FindSubtypes A).
Proof.
  intros.
  destruct (FindSubtypes A).
  contradiction.
  lets: elem_append_in_list t l.
  exists t. auto.
Defined.

Lemma set_in_sub : forall A x, set_In x (FindSubtypes A) ->
forall B, A <: B -> set_In x (FindSubtypes B).
Proof.
  intros.
  inductions H0; eauto.
  - lets H': H.
    apply elem_in_findsubtypes_ord in H'.
    simpl. destruct H'; auto.
    apply arrow_in_top_bot in H.
    rewrite H. auto.
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

Lemma findsubtypes_sub_empty : forall A1 A2 B,
FindSubtypes (t_and A1 A2) = [] -> 
B <: (t_and A1 A2) -> FindSubtypes B = [].
Proof.
    intros.
    lets: list_empty_decide (FindSubtypes B).
    destruct H1. auto.
    lets: findsubtypes_not_empty B H1.
    destruct H2.
    lets: set_in_sub B x H2 (t_and A1 A2) H0.
    rewrite H in H3. inverts H3.
Defined.

(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)

Lemma sub_refl : forall A, A <: A.
  induction A; eauto.
Defined.

Hint Resolve sub_refl : core.

Lemma sub_transitivity : forall B A C, A <: B -> B <: C -> A <: C.
Proof.
induction B; intros;
generalize H0 H; clear H0; clear H; generalize A; clear A.
- intros; inductions H0; eauto. 
- intros; inductions H; eauto.
- intros; inductions H; eauto.
- induction C; intros; try solve [inverts* H0].
  inverts H0. inverts H1.
  inverts H0. inverts H1.
  induction A; try solve[inverts* H].
  inverts* H0. inverts* H. 
- intros. apply sub_or in H0. destruct H0.
  inductions H; eauto.
- intros. apply sub_and in H. destruct H.
  inductions H0; eauto.
  assert (A <: t_and B1 B2) by auto.
  apply s_disj.
  apply findsubtypes_sub_empty with (A1:=B1) (A2:=B2). auto. auto.
Defined.

Lemma bot_sub_all : forall A, t_bot <: A.
Proof.
  intros.
  dependent induction A; eauto.
Qed.

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec A B := forall C, Ord C -> not (C <:  (t_and A B)).
Notation "A *s B" := (DisjSpec A B) (at level 80).

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

Definition DisjAlgo A B := ((FindSubtypes A) `inter` (FindSubtypes B)) = [].
Notation "A *a B" := (DisjAlgo A B) (at level 80).


Lemma Disj_soundness : forall A B, A *a B -> A *s B.
Proof.
intros.
unfold DisjAlgo in H.
unfold DisjSpec. unfold not. intros.
apply ord_sub_findsubtypes_not_empty in H1; auto.
Qed.

Lemma Disj_completeness : forall A B,  A *s B -> A *a B.
Proof.
  intros.
  unfold DisjSpec in H. unfold not in H.
  unfold DisjAlgo.
  eapply not_in.
  apply demorgan. unfold not. intros.
  destruct H0 as [H1 | H1];
  lets H1': H1;
  apply elem_in_findsubtypes_sub in H1';
  lets H1'': H1;
  apply elem_in_findsubtypes_ord in H1''.
  eapply H; eauto.
  eapply H; eauto.
Qed.

Lemma disj_bot_like : forall A B, A *a B -> t_and A B <: t_bot.
Proof.
  intros.
  unfold DisjAlgo in H.
  apply s_disj. simpl. auto.
Qed.