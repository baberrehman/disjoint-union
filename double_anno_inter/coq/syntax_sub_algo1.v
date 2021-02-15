
(*
Update started on February 08, 2021
*)

(*
This file contains the updates suggested by Bruno.
Mutual dependency of algorithmic bottom-like and
algorithmic disjointness.

Subtying algorithm added in this version.

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
| o_top : Ord typ_top
| o_int : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2).
(*| o_union : forall t1 t2, Ord t1 -> Ord t2 -> Ord (t_union t1 t2).*)

Hint Constructors Ord.

Require Import List.

Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.

Fixpoint typ_eq (A B : typ) : (bool * typ) :=
    match A, B with
    | typ_top, typ_top             => (true, B)
    | typ_top, t_int               => (true, B)
    | typ_top, t_arrow _ _         => (true, B)
    | t_int, typ_top               => (true, A)
    | t_arrow _ _, typ_top         => (true, A)
    | t_int, t_int                 => (true, A)
    | (t_arrow _ _), (t_arrow _ _) => (true, A)
    | _, _                         => (false, A)
    end.

Fixpoint IsElem (a : typ) (l : list typ) : (bool * typ) :=
    match l with
    | []            => (false, a) 
    | h :: tl       => match (typ_eq a h) with
                       | (true, A) => (true, A)
                       | _         => IsElem a tl
                       end
    end.

Fixpoint Intersect (l1 l2: list typ) : list typ :=
    match l1, l2 with
    | [], _      => []
    | _, []      => []
    | h :: tl, _ => match IsElem h l2 with
                    | (true, A) => [A] ++ Intersect tl l2
                    | _         => Intersect tl l2
                    end
    end.

Fixpoint Union (l1 l2: list typ) : list typ := l1 ++ l2.

Fixpoint FindSubtypes (A: typ) :=
    match A with
    | typ_top       => [typ_top]
    | t_bot         => []
    | t_int         => [t_int]
    | t_arrow A1 B1 => [t_arrow typ_top t_bot]
    | t_union A1 B1 => Union (FindSubtypes A1) (FindSubtypes B1)
    | t_and A1 B1   => Intersect (FindSubtypes A1) (FindSubtypes B1)
    end.

(*Eval compute in (FindSubtypes t_int).
Eval compute in (FindSubtypes (t_and t_int t_bot)).
Eval compute in (FindSubtypes (t_and t_int typ_top)).
Eval compute in (FindSubtypes (t_and typ_top t_int)).
Eval compute in (FindSubtypes (t_and (t_arrow t_int t_int) t_int)).
Eval compute in (FindSubtypes (t_and(t_and (t_arrow t_int t_int) t_int)typ_top)).
Eval compute in (FindSubtypes (t_and typ_top(t_and (t_arrow t_int t_int) t_int))).
Eval compute in (FindSubtypes (t_union (t_and typ_top(t_and (t_arrow t_int t_int) t_int)) (t_and typ_top(t_and (t_arrow t_int t_int) t_int)))).
Eval compute in (FindSubtypes (t_and (t_union typ_top(t_union (t_arrow t_int t_int) t_int)) (t_union typ_top(t_union (t_arrow t_int t_int) t_int)))).
Eval compute in (FindSubtypes (t_and typ_top t_bot)).
Eval compute in (FindSubtypes (t_and (t_arrow t_int t_int) (t_arrow (t_arrow t_int t_int) t_int))).
Eval compute in (FindSubtypes (t_union t_int t_bot)).
Eval compute in (FindSubtypes (t_and (t_union t_int (t_arrow t_int t_int)) t_int)).
Eval compute in (FindSubtypes (t_union t_int (t_arrow t_int t_int))).
Eval compute in (FindSubtypes (t_and (t_arrow t_int t_int) typ_top)).
Eval compute in (FindSubtypes (t_and typ_top (t_arrow t_int t_int))).*)

(*
New disjointness
*)


(****************************************)
(*********  Bottom-Like Specs   *********)
(****************************************)

Definition btmLikeSpec C := forall A, Ord A -> not (A <: C).

(*Definition btmLikeSpec C := (forall A B,  Isomorphic (t_and A B) C -> 
btmLikeSpec A \/ btmLikeSpec B \/ (not (A <: B) /\ not (B <: A))) \/ C <: t_bot.*)

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec A B := btmLikeSpec (t_and A B).

Notation "A *s B" := (DisjSpec A B) (at level 80).

(* defns Disjointness *)

Reserved Notation "A *a B" (at level 80).

Inductive disjointness : typ -> typ -> Prop :=    (* defn disjointness *)
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
     A *a C ->
     A *a (t_and B C)
 | disjl : forall A B, 
     Intersect (FindSubtypes A) (FindSubtypes B) = [] ->
     A *a B
 | disjr : forall A B, 
     Intersect (FindSubtypes B) (FindSubtypes A) = [] ->
     A *a B
where "A *a B" := (disjointness A B).

Hint Constructors disjointness.

(**********************************)
(****  Bottom-Like Properties  ****)
(**********************************)

Lemma ord_sub_bot_false : forall A, Ord A -> A <: t_bot -> False.
Proof.
  intros.
  dependent induction H; inversion H0.
Defined.

Lemma btm_sub_btmlikeSpec : forall A, A <: t_bot -> btmLikeSpec A.
Proof.
intros. unfold btmLikeSpec. unfold not. intros.
eapply sub_transitivity in H; eauto.
forwards*: ord_sub_bot_false H0.
Defined.

Lemma not_sub_and : forall A1 A2, forall A, Ord A ->
not (A <: (t_and A1 A2)) -> not((A <: A1) /\ (A <: A2)).
Proof.
  intros.
  unfold not in *. intros.
  apply H0; destruct~ H1.
Defined.

Lemma btm_like_spec_and : forall A1 A2, btmLikeSpec (t_and A1 A2) ->
  A1 *s A2.
Proof.
  intros.  unfold DisjSpec.
  auto.
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

Lemma btm_like_spec_union_inv : forall A B, btmLikeSpec A -> btmLikeSpec B -> btmLikeSpec (t_union A B).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros.
  lets: H A0 H1.
  lets: H0 A0 H1.
  apply* not_sub_or_inv.
Defined.

Lemma btm_like_spec_union : forall A B, btmLikeSpec (t_union A B) ->
btmLikeSpec A /\ btmLikeSpec B.
Proof.
intros. unfold btmLikeSpec in *. unfold not in *.
split*.
Defined.

Lemma ord_sub_union : forall A, Ord A -> forall A1 A2, A <: t_union A1 A2 -> A <: A1 \/ A <: A2.
Proof.
  intros A H.
  dependent induction H; intros.
  inverts* H.
  inverts* H.
  inverts* H.
Defined.

(***********************
Find Subtypes Properties
************************)

Lemma union_find_sub_types : forall A B, 
(FindSubtypes A = []) -> (FindSubtypes B = []) ->
Union (FindSubtypes A) (FindSubtypes B) = [].
Proof.
intros.
induction (FindSubtypes A). simpl. auto. inversion H.
Defined.

Lemma union_find_sub_types1 : forall A B,
Union (FindSubtypes A) (FindSubtypes B) = [] ->
(FindSubtypes A = []) /\ (FindSubtypes B = []).
Proof.
intros.
induction (FindSubtypes A). simpl in H. auto. inversion H.
Defined.

Lemma inter_find_subtypes_l : forall A B,
(FindSubtypes A) = [] ->
Intersect (FindSubtypes A) (FindSubtypes B) = [].
Proof.
  intros. rewrite H. simpl. auto.
Defined.

Lemma inter_find_subtypes_r : forall A B,
(FindSubtypes B) = [] ->
Intersect (FindSubtypes A) (FindSubtypes B) = [].
Proof.
  intros.
  induction Intersect; eauto.
  admit.
Admitted.

Lemma elem_in_find_subtypes_ord : forall A B,
fst(IsElem B (FindSubtypes A)) = true -> Ord B.
Proof.
  intros.
  induction FindSubtypes.
  simpl in H. discriminate.
  inductions B; eauto.
Defined.

Lemma union_inv1 : forall A B C,
fst(IsElem A (FindSubtypes B)) = true ->
fst(IsElem A (Union(FindSubtypes B) (FindSubtypes C))) = true.
Proof.
  intros.
  induction FindSubtypes. simpl in H. discriminate.
  induction FindSubtypes. admit.
  - induction Union; simpl in IHl.
Admitted. 

Lemma test_not_empty : forall A B, Ord A -> A <: B ->
FindSubtypes B <> [].
Proof.
  intros.
  inductions H; eauto.
 - induction B; unfold not; simpl; intros; eauto.
   inversion H. inversion H. inversion H0. inversion H.
  + apply union_find_sub_types1 in H. destruct H.
    apply ord_sub_union in H0; auto.
    destruct H0.
    * unfold not in IHB1. apply IHB1; auto.
    * unfold not in IHB2. apply IHB2; auto.    
  + apply sub_and in H0. destruct H0.
    unfold not in *. admit.
 - induction B; unfold not; simpl; intros; eauto.
   inversion H. inversion H.
   inversion H0. inversion H0.
   admit. admit.
 - induction B; unfold not; simpl; intros; eauto.
   inversion H. inversion H. inversion H0. inversion H.
   admit. admit.
Admitted.

Lemma intersect_sym : forall A B,
Intersect (FindSubtypes A) (FindSubtypes B) = [] ->
Intersect (FindSubtypes B) (FindSubtypes A) = [].
Proof.
Admitted.

Lemma btm_sub_complete : forall A, btmLikeSpec A -> FindSubtypes A = [].
Proof.
intros. induction A.
- simpl. unfold btmLikeSpec in H.
  unfold not in H.
  specialize (H typ_top). forwards*: H.
- simpl. unfold btmLikeSpec in H.
  unfold not in H.
  specialize (H t_int). forwards*: H.
- simpl. auto.
- simpl. unfold btmLikeSpec in H.
  specialize (H (t_arrow A1 A2)).
  unfold not in H. forwards*: H.
- simpl. apply btm_like_spec_union in H. destruct H.
  apply union_find_sub_types.
  apply IHA1; auto.
  apply IHA2; auto.
- simpl. induction FindSubtypes. simpl. auto.
  induction FindSubtypes. simpl. auto.
  induction (a :: l). simpl. auto.
Admitted.

Lemma btm_sub_sound : forall A, FindSubtypes A = [] -> 
btmLikeSpec A.
Proof.
intros. induction A.
- simpl in H. inversion H.
- simpl in H. inversion H.
- unfold btmLikeSpec. unfold not.
  intros. eapply ord_sub_bot_false; eauto.
- simpl in H. inversion H.
- simpl in H. apply union_find_sub_types1 in H.
  destruct H.
  apply btm_like_spec_union_inv; auto.
- unfold btmLikeSpec. unfold not. intros.
  lets: test_not_empty A (t_and A1 A2) H0 H1.
  contradiction.
Defined.

Lemma disj_inetersect_complete : forall A B,
A *s B -> Intersect (FindSubtypes A) (FindSubtypes B) = [].
Proof.
intros.
  induction A; eauto.
  admit.
  admit.
  admit.
  simpl.
  admit.
  simpl.
Admitted.


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

Lemma btm_like_spec_and1_inv : forall A B, btmLikeSpec A -> btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros.
  lets: H A0 H0.
  apply* not_sub_and1_inv.
Defined.

Lemma btm_like_spec_and2_inv : forall A B, btmLikeSpec B -> btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros.
  lets: H A0 H0.
  apply* not_sub_and2_inv.
Defined.

Lemma btm_spec : btmLikeSpec t_bot.
Proof.
  unfold btmLikeSpec.
  intros.
  unfold not.
  intros.
  inductions H; inverts* H0.
Defined.

Lemma btm_like_spec_btm_inter : forall A, btmLikeSpec (t_and A t_bot).
Proof.
  intros.
  unfold btmLikeSpec. intros.
  unfold not. intros.
  apply sub_and in H0.
  destruct H0.
  apply ord_sub_bot_false in H1; auto.
Defined.


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
Defined.

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
Defined.

Lemma disj_sub_union : forall A B C, A *s C -> B *s C -> t_union A B *s C.
Proof.
  intros.
  unfold DisjSpec in *. intros.
  unfold btmLikeSpec in *. intros.
  unfold not. intros.
  specialize (H A0).
  unfold not in H.
  apply H; auto.
  apply sub_and in H2.
  destruct H2.
  lets: ord_sub_union A0 H1 A B H2.
  destruct H4.
  apply s_anda; auto.
  specialize (H0 A0). unfold not in H0.
  assert (A0 <: t_and B C); auto.
  forwards*: H0.
Defined.

Lemma disj_spec_union : forall A B C, t_union A B *s C -> A *s C /\ B *s C.
Proof.
  unfold DisjSpec; unfold btmLikeSpec; unfold not; intros.
  split.
  - intros. apply sub_and in H1. destruct H1.
    specialize (H A0).
    apply H; auto.
  - intros. apply sub_and in H1. destruct H1.
    specialize (H A0).
    apply H; auto.
Defined.

Lemma disj_spec_union1 : forall A B C, A *s t_union B C -> A *s B /\ A *s C.
Proof.
  unfold DisjSpec; unfold btmLikeSpec; unfold not; intros.
  split.
  - intros. apply sub_and in H1. destruct H1.
    specialize (H A0).
    apply H; auto.
  - intros. apply sub_and in H1. destruct H1.
    specialize (H A0).
    apply H; auto.
Defined.


Lemma ord_sub_disj_spec_false : forall A, Ord A -> 
forall B C, B *s C -> A <: (t_and B C) -> False.
Proof.
 intros.
 unfold DisjSpec in H0.
 unfold btmLikeSpec in H0. unfold not in H0.
 apply sub_and in H1. destruct H1.
 specialize (H0 A).
 forwards*: H0 H.
Defined.

Lemma BL_disj : forall A, t_bot *a A.
Proof.
  intros; auto.
Defined.

Lemma Disj_sym_spec : forall A B, A *s B -> B *s A.
Proof.
  unfold DisjSpec. intros.
  unfold btmLikeSpec in *. unfold not in *.
  intros.
  forwards*: H H0.
  apply sub_and in H1. destruct H1.
  apply s_anda; auto.
Defined.    

Lemma Disj_soundness : forall A B, A *a B -> A *s B.
Proof.
(* Disj_soundness Soundness Proof *)
- intros. dependent induction H; unfold DisjSpec; intros.
 + unfold btmLikeSpec. unfold not. intros.
   apply sub_and in H0. destruct H0.
   lets: ord_sub_bot_false A0 H H0. false.
 + unfold btmLikeSpec. unfold not. intros.
   apply sub_and in H0. destruct H0.
   lets: ord_sub_bot_false A0 H H1. false.
 + unfold btmLikeSpec. unfold not. intros.
   apply sub_and in H0. destruct H0.
   lets: sub_int_arrow A0 A0 H0 A B.
   forwards*: H2. unfold btmLikeSpec in H3. unfold not in H3.
   lets: H3 A0 H. forwards*: H4.
 + unfold btmLikeSpec. unfold not. intros.
   apply sub_and in H0. destruct H0.
   lets: sub_int_arrow A0 A0 H1 A B.
   forwards*: H2. unfold btmLikeSpec in H3. unfold not in H3.
   lets: H3 A0 H. forwards*: H4.
    (* difficult case -- union with intersection *)
+ lets: disj_sub_union A B C IHdisjointness1 IHdisjointness2.
  unfold DisjSpec in H1. auto.
    (* difficult case -- union with intersection *)
+ apply Disj_sym_spec in IHdisjointness1.
  apply Disj_sym_spec in IHdisjointness2.
  lets: disj_sub_union B C A IHdisjointness1 IHdisjointness2.
  unfold DisjSpec in H1.
  apply sym_btm_like. auto.
 + unfold DisjSpec in IHdisjointness.
   unfold btmLikeSpec in *. unfold not in *. intros.
   apply sub_and in H1. destruct H1.
   apply sub_and in H1. destruct H1.
   eapply IHdisjointness; eauto.
 + unfold DisjSpec in IHdisjointness.
   unfold btmLikeSpec in *. unfold not in *. intros.
   apply sub_and in H1. destruct H1.
   apply sub_and in H1. destruct H1.
   eapply IHdisjointness; eauto.
 + unfold DisjSpec in IHdisjointness.
   unfold btmLikeSpec in *. unfold not in *. intros.
   apply sub_and in H1. destruct H1.
   apply sub_and in H2. destruct H2.
   eapply IHdisjointness; eauto.
+ unfold DisjSpec in IHdisjointness.
   unfold btmLikeSpec in *. unfold not in *. intros.
   apply sub_and in H1. destruct H1.
   apply sub_and in H2. destruct H2.
   eapply IHdisjointness; eauto.
 + unfold btmLikeSpec. unfold not. intros.
   apply test_not_empty in H1; auto.
 + unfold btmLikeSpec. unfold not. intros.
   apply test_not_empty in H1; auto.
   simpl in *.
   apply intersect_sym in H. auto.
Qed.

Lemma BL_disj_spec : forall A, btmLikeSpec A -> forall B, A *s B.
  intros.
  unfold btmLikeSpec in H.
  unfold not in H.
  unfold DisjSpec. intros.
  unfold btmLikeSpec. intros.
  unfold not. intros.
  eapply H; eauto.
  apply sub_and in H1; destruct H1; auto.
Defined.

Lemma disj_btm_spec : forall A B, A *s B -> btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold DisjSpec in H. auto.
Defined.

Lemma Disj_sym : forall A B, A *a B -> B *a A.
  induction 1; eauto.
Defined.

Lemma dist_inter_union : forall l1 l2 l3,
Intersect l1 (Union l2 l3) = [] ->
Intersect l1 l2 = [] /\ Intersect l1 l3 = [].
Proof.
  intros.
  induction l1; auto.
Admitted.

Lemma disj_union_inv : forall A B C, A *a (t_union B C) ->
  A *a B /\ A *a C.
Proof.
intros.
inductions H; eauto.
- specialize (IHdisjointness1 B C).
  destruct IHdisjointness1; auto.
  specialize (IHdisjointness2 B C).
  destruct IHdisjointness2; auto.
- specialize (IHdisjointness B C).
  destruct IHdisjointness; auto.
- specialize (IHdisjointness B C).
  destruct IHdisjointness; auto.
- simpl in H.
  apply dist_inter_union in H.
  destruct H.
  split*.
- admit.
Admitted.

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
  inductions A1; eauto.
  - inductions A2; eauto.
    + right. intros.
      assert (A <: t_bot).
      eapply sub_transitivity; eauto.
      lets: ord_sub_bot_false A H0 H2. auto.
    + clear IHA2_1 IHA2_2.
      right. intros.
      forwards*: ord_sub_int_arrow_false H1.
    + clear IHA2_1 IHA2_2.
      right. intros.
      inverts* H1; eauto.
      inversion H0. inversion H0. inversion H0.
    + clear IHA2_1 IHA2_2.
      right. intros.
      inverts* H1; eauto.
      inversion H0. inversion H0. inversion H0.
  - inductions A2; eauto.
    + right. intros.
      assert (A <: t_bot).
      eapply sub_transitivity; eauto.
      lets: ord_sub_bot_false A H0 H2. auto.
    + right. intros.
      apply sub_and in H1. destruct H1.
      lets: ord_sub_int_arrow_false A A A2_1 A2_2 H0.
      assert (A <: A); auto.
    + right. intros.
      dependent destruction H1; eauto.
      inversion H0. inversion H0. inversion H0.
    + right. intros.
      dependent destruction H1; eauto.
      inversion H0. inversion H0. inversion H0.
  - left. intros.
    assert (A <: t_bot ).
    eapply sub_transitivity; eauto.
    forwards*: ord_sub_bot_false A H0 H2.
  - clear IHA1_1 IHA1_2.
    left. intros.
    apply sub_and in H1. destruct H1.
    lets: ord_sub_int_arrow_false A A A1_1 A1_2 H0.
    assert (A <: A); auto.
  - clear IHA1_1 IHA1_2. inductions A2; eauto.
    + left. intros.
      eapply H; eauto.
      apply sub_and in H1. destruct H1.
      apply s_anda; auto.
    + left. intros.
      apply sub_and in H1. destruct H1.
      specialize (H A).
      apply H; auto. 
    + right. intros. 
      apply sub_and in H1. destruct H1.
      forwards*: ord_sub_bot_false A H0 H1.
    + clear IHA2_1 IHA2_2. right. intros.
      apply sub_and in H1. destruct H1.
      lets: ord_sub_int_arrow_false A A A2_1 A2_2 H0.
      auto.
    + clear IHA2_1 IHA2_2.
      apply btm_like_spec_int_and in H.
      destruct H.
      left. intros.
      unfold btmLikeSpec in H.
      unfold not in H.
      apply sub_and in H1. destruct H1.
      specialize (H A); auto.
      right. intros. 
      apply sub_and in H1. destruct H1.
      unfold btmLikeSpec in H.
      unfold not in H.
      specialize (H A); auto.
    + clear IHA2_1 IHA2_2.
      apply btm_like_spec_int_and in H.
      destruct H.
      unfold btmLikeSpec in H.
      unfold not in H.
      left. intros. 
      apply sub_and in H1. destruct H1.
      specialize (H A); auto.
      right. intros. apply sub_and in H1. destruct H1.
      unfold btmLikeSpec in H. unfold not in H.
      specialize (H A); auto.
  - clear IHA1_1 IHA1_2.
    apply btm_like_spec_int_and in H.
    destruct H.
    unfold btmLikeSpec in H.
    unfold not in H.
    left. intros. apply sub_and in H1. destruct H1.
    specialize (H A); auto.
    right. intros. unfold btmLikeSpec in H. unfold not in H.
    specialize (H A); auto.
Defined.


Lemma disj_spec_arrow : forall A1 A2 B1 B2, (t_and A1 A2) *s (t_arrow B1 B2) -> 
A1 *s (t_arrow B1 B2) \/ A2 *s (t_arrow B1 B2).
Proof.
  intros.
  unfold DisjSpec in *.
  unfold btmLikeSpec in *.
  unfold not in *.
  apply btm_like_spec_arrow_and in H.
  destruct H.
 - unfold btmLikeSpec in H.
   unfold not in H.
   left. intros.
   specialize (H A); auto.
 - unfold btmLikeSpec in H. unfold not in H.
   right. intros.
   specialize (H A); auto.
Defined.

Lemma disj_spec_int_extra : forall A1 A2, (t_and A1 A2) *s t_int -> A1 *s t_int \/ A2 *s t_int.
Proof.
  intros.
  unfold DisjSpec in *.
  unfold btmLikeSpec in *.
  unfold not in *.
  apply btm_like_spec_int_and in H.
  destruct H.
  - unfold btmLikeSpec in H.
    unfold not in H.
    left. intros.
    specialize (H A); auto.
  - unfold btmLikeSpec in H.
    unfold not in H.
    right. intros.
    specialize (H A); auto.
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
  unfold DisjSpec in *. unfold btmLikeSpec in *.
  unfold not in *.
  intros.
  specialize (H A); auto.
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

Lemma disj_spec_or_top : forall A, A *s typ_top -> btmLikeSpec A.
Proof.
  intros.
  unfold DisjSpec in *. unfold btmLikeSpec in *. unfold not in *. 
  intros.
  specialize (H A0); auto.
Defined.

Fixpoint size_of_type (A : typ) : nat :=
  match A with 
  | t_bot         => 1
  | t_int         => 1
  | typ_top       => 1
  | t_arrow A1 B1 => 1 + (size_of_type A1) + (size_of_type B1)
  | t_union A1 B1 => 1 + (size_of_type A1) + (size_of_type B1)
  | t_and A1 B1   => 1 + (size_of_type A1) + (size_of_type B1)
  end.

Require Import Omega.

Lemma ord_top_disj_false : forall A,
Ord A -> A *s typ_top -> False.
Proof.
  intros. unfold DisjSpec in H0.
  unfold btmLikeSpec in H0. unfold not in H0.
  specialize (H0 A). auto.
Defined.

Lemma int_int_disj_false :
t_int *s t_int -> False.
Proof.
  intros. unfold DisjSpec in H.
  unfold btmLikeSpec in H. unfold not in H.
  specialize (H t_int). auto.
Defined.

Lemma disj_spec_arrow_false : forall A1 A2 B1 B2, t_arrow A1 A2 *s t_arrow B1 B2 -> False.
Proof.
  unfold DisjSpec; unfold btmLikeSpec; unfold not; intros.
  specialize (H (t_arrow typ_top t_bot)).
  forwards: H; auto.
Defined.

Lemma Disj_completeness : forall A B, A *s B -> A *a B.
Proof.
  (* Dijointness completeness proof *)
 induction A; intros.
  (* Top Case *)
 + admit.
   (* Int Case *)
 + induction B; eauto.
  * apply ord_top_disj_false in H; auto. false.
  * apply int_int_disj_false in H; auto. false.
  * apply disj_spec_union1 in H. destruct H.
    apply ad_orr.
    apply IHB1; apply H.
    apply IHB2; apply H0.
  * (* Intersection and Int case - requires hard helping lemma *)
    apply Disj_sym_spec in H.
    apply disj_spec_int_extra in H. destruct H.
    apply ad_andr1. apply IHB1.
    apply Disj_sym_spec. apply H.
    apply ad_andr2. apply IHB2. 
    apply Disj_sym_spec. apply H.
   (* Bottom Case *)
 + apply ad_btml.
    (* Arrow Case *)
 + clear IHA1 IHA2.
   induction B; eauto.
  * apply ord_top_disj_false in H; auto. false.
  * apply disj_spec_arrow_false in H. false.
  * apply disj_spec_union1 in H. destruct H.
    apply ad_orr.
    apply IHB1; apply H.
    apply IHB2; apply H0.
  * apply Disj_sym_spec in H. apply disj_spec_arrow in H. destruct H.
    apply ad_andr1. apply IHB1.
    apply Disj_sym_spec. apply H.
    apply ad_andr2. apply IHB2.
    apply Disj_sym_spec. apply H.
    (* Union Case *)
 + apply disj_spec_union in H. destruct H.
   apply ad_orl.
   apply IHA1; apply H.
   apply IHA2; apply H0.
  (* Intersection Case *)
 + apply disjl.
   apply inetersect_and_empty in H. auto.
Admitted.