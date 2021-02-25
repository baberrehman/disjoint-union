(*
This file contains the updates suggested by Snow.
Mod of syntax_bruno_btmlike
Try to eliminate the dependency of disjointness and bottomlike
A * B ::= bot-like A&B
*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import LibTactics.
(*Implicit Types x : var.*)
(** syntax *)

Inductive typ : Set :=  (*r type *)
 | typ_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and : typ -> typ -> typ.

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

Hint Constructors subtyping : core.

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

Definition btmLikeSpec C := forall A, Ord A -> A <: C -> False.

(*Definition btmLikeSpec C := (forall A B,  Isomorphic (t_and A B) C ->
btmLikeSpec A \/ btmLikeSpec B \/ (not (A <: B) /\ not (B <: A))) \/ C <: t_bot.*)

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec A B := btmLikeSpec (t_and A B).

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
 | bl_intl : forall A B,
     bottomlike (t_and t_int (t_arrow A B))
 | bl_intr : forall A B,
     bottomlike (t_and (t_arrow A B) t_int)
 | bl_orl : forall A B C,
     bottomlike (t_and A C) ->
     bottomlike (t_and B C) ->
     bottomlike (t_and (t_union A B) C)
 | bl_orr : forall A B C,
     (* does the order matter? A&C or C&A? *)
     bottomlike (t_and A C) ->
     bottomlike (t_and B C) ->
     bottomlike (t_and C (t_union A B))
 | bl_andl1 : forall A B C,
     bottomlike (t_and A C) ->
     bottomlike (t_and (t_and A B) C)
 | bl_andl2 : forall A B C,
     bottomlike (t_and B C) ->
     bottomlike (t_and (t_and A B) C)
 | bl_andr1 : forall A B C,
     bottomlike (t_and A C) ->
     bottomlike (t_and C (t_and A B))
 | bl_andr2 : forall A B C,
     bottomlike (t_and B C) ->
     bottomlike (t_and C (t_and A B)).

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


Lemma not_sub_and : forall A1 A2, forall A, Ord A ->
not (A <: (t_and A1 A2)) -> not((A <: A1) /\ (A <: A2)).
Proof.
  intros.
  unfold not in *. intros.
  apply H0; destruct~ H1.
Qed.

(*************************************)
(*****  Disjointness Properties  *****)
(*************************************)

(** infrastructure *)

Lemma btm_like_spec_union_inv : forall A B, btmLikeSpec A -> btmLikeSpec B -> btmLikeSpec (t_union A B).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros.
  induction H1; inverts* H2.
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

Lemma btm_like_spec_and2_inv : forall A B, btmLikeSpec B -> btmLikeSpec (t_and A B).
Proof.
  intros.
  unfold btmLikeSpec in *.
  intros. inductions H0; inverts* H1.
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
  unfolds. intros.
  assert (A0 <: (t_and t_int (t_arrow A1 A2))). {
    applys sub_transitivity H2.
    applys s_anda. eauto. eauto.
  }
  forwards (HS1&HS2): sub_and H3.
  induction H1; try solve [inverts HS1]; try solve [inverts HS2].
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
 unfold btmLikeSpec in *. intros.
 eapply H; eauto.
 applys sub_transitivity H3. eauto.
Qed.

Lemma disj_sub_union : forall A B C, A *s C -> B *s C -> t_union A B *s C.
Proof.
  intros.
  unfold DisjSpec in *. intros.
  unfold btmLikeSpec in *. intros.
  destruct H1.
  unfold not. intros.
Abort.

(**************************************)
(******* Bottom Like Soundness ********)
(**************************************)

(*

no algorithmic disjointness now

*)

Lemma BL_soundness : forall A, bottomlike A -> btmLikeSpec A.
Proof.
  intros. inductions H; unfold btmLikeSpec in *; eauto; intros.
  - induction H; inverts H0.
  - forwards* [HS1|HS2]: ord_sub_union H2.
  - apply sub_and in H1. jauto.
  - apply sub_and in H1. jauto.
  - forwards (HS1&HS2): sub_and H0.
    induction H; try solve [inverts HS1]; try solve [inverts HS2].
  - forwards (HS1&HS2): sub_and H0.
    induction H; try solve [inverts HS1]; try solve [inverts HS2].
  - forwards (HS1&HS2): sub_and H2.
    forwards* [HS3|HS4]: ord_sub_union HS1.
  - forwards (HS1&HS2): sub_and H2.
    forwards* [HS3|HS4]: ord_sub_union HS2.
  - forwards (HS1&HS2): sub_and H1.
    forwards (HS3&HS4): sub_and HS1.
    eauto.
  - forwards (HS1&HS2): sub_and H1.
    forwards (HS3&HS4): sub_and HS1.
    eauto.
  - forwards (HS1&HS2): sub_and H1.
    forwards (HS3&HS4): sub_and HS2.
    eauto.
  - forwards (HS1&HS2): sub_and H1.
    forwards (HS3&HS4): sub_and HS2.
    eauto.
Qed.

Lemma bl_union_inv : forall A B, bottomlike (t_union A B) ->
bottomlike A /\ bottomlike B.
Proof.
intros. inverts* H.
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

(*

Following two lemmas seem true but can't figure our how to prove

test61 depends upon test6

Did not find any counter example and can't prove the lemma

God help this poor PhD student! Please!

*)
Theorem deMorgan : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q PorQ_imp_false.
  split.
  - intros P_holds. apply PorQ_imp_false. left. assumption.
  - intros Q_holds. apply PorQ_imp_false. right. assumption.
Qed.

Theorem excluded_middle : forall A, btmLikeSpec A \/ ~btmLikeSpec A.
Proof.
  intros.
  induction A; eauto.
  - left. applys ord_sub_bot_false.
  - (* union *) admit.
  - destruct IHA1.
    + left*. unfolds. intros.
      unfolds in H. applys H H0.
      applys* sub_transitivity H1.
    + destruct IHA2.
      * left*. unfolds. intros.
        unfolds in H0. applys H0 H1.
        applys* sub_transitivity H2.
      * right*. unfolds. intros.
        Abort.


Lemma test6_aux : forall Ta Tb Tc A B C,
    Ord Ta -> Ord Tb -> Ord Tc
    -> Ta <: (t_and B C)
    -> Tb <: (t_and A C)
    -> Tc <: (t_and A B)
             -> exists T, Ord T /\ T <: (t_and (t_and A B) C).
Proof.
Abort.


Lemma test6 : forall A1 A2 B, btmLikeSpec (t_and (t_and A1 A2) B) ->
btmLikeSpec (t_and A1 B) \/ btmLikeSpec (t_and A2 B) \/ btmLikeSpec (t_and A1 A2).
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
Abort.

Lemma top_btmlike : forall A, btmLikeSpec (t_and typ_top A) -> btmLikeSpec A.
Proof.
  intros.
  unfold btmLikeSpec in *.
  unfold not in *.
  intros.
  forwards*: H H0.
Qed.

Lemma BL_completeness : forall A, btmLikeSpec A -> bottomlike A.
Proof.
  intros.
  unfold btmLikeSpec in H.
  induction A.
  - exfalso. applys* H typ_top.
  - exfalso. applys* H t_int.
  - eauto.
  - exfalso. applys* H (t_arrow A1 A2).
  - constructor.
    + apply IHA1. intros.
      applys* H H0.
    + apply IHA2. intros.
      applys* H H0.
  - Abort.


Definition btmLikeSpec2 C := C <: t_bot \/ exists A B, C <: (t_and t_int (t_arrow A B)).

Lemma btmLikeSpec2_sound : forall C,
    btmLikeSpec2 C -> btmLikeSpec C.
Proof.
  intros. unfolds in H.
  - destruct H.
    + unfolds. intros.
      lets Hs: sub_transitivity H1 H.
      induction H0; try solve [inverts Hs].
    + destruct H. destruct H.
      assert (C <: t_int) by applys* sub_transitivity H.
      assert (C <: (t_arrow x x0)) by applys* sub_transitivity H.
      unfolds. intros.
      lets Hs1: sub_transitivity H3 H0.
      lets Hs2: sub_transitivity H3 H1.
      induction H2; try solve [inverts Hs1]; try solve [inverts Hs2].
Qed.

Lemma bottomlike_symm : forall A B,
    bottomlike (t_and A B) -> bottomlike (t_and B A).
Proof.
  intros.
  inductions H; eauto.
Qed.

Lemma bottomlike_disjoit_sub : forall A B T1 T2,
    A <: t_int -> B <: (t_arrow T1 T2) -> bottomlike (t_and A B).
Proof.
  introv HSa HSb.
  inductions HSa; eauto.
  inductions HSb; eauto.
  - forwards*: IHHSb1.
    forwards*: IHHSb2.
    apply bottomlike_symm in H.
    apply bottomlike_symm in H0.
    eauto.
  - forwards*: IHHSb.
    apply bottomlike_symm in H.
    eauto.
  - forwards*: IHHSb.
    apply bottomlike_symm in H.
    eauto.
Qed.

Lemma bottomlike_sub : forall A B,
    bottomlike A -> B <: A -> bottomlike B.
Proof.
  introv Hb Hs.
  induction* Hs; try solve [inverts Hb].
  - apply bl_union_inv in Hb. jauto.
  - apply bl_union_inv in Hb. jauto.
  - inverts* Hb.
    + inverts* Hs1; try solve [inverts Hs2].
Abort.

Lemma BL_completeness2 : forall A, btmLikeSpec2 A -> bottomlike A.
Proof.
  intros.
  unfold btmLikeSpec2 in H.
  induction A.
  - exfalso. destruct H as [H|(?&?&H)]; try solve [inverts H].
    assert (Hs: typ_top <: t_int) by applys* sub_transitivity H.
    inverts Hs.
  - exfalso. destruct H as [H|(?&?&H)]; try solve [inverts H].
    assert (Hs: t_int <: (t_arrow x x0)) by applys* sub_transitivity H.
    inverts Hs.
  - eauto.
  - exfalso. destruct H as [H|(?&?&H)]; try solve [inverts H].
    assert (Hs:  t_arrow A1 A2 <: t_int) by applys* sub_transitivity H.
    inverts Hs.
  - constructor.
    + apply IHA1. destruct H as [H|(?&?&H)].
      * left*. applys* sub_transitivity H.
      * right*. exists. applys* sub_transitivity H.
    + apply IHA2. destruct H as [H|(?&?&H)].
      * left*. applys* sub_transitivity H.
      * right*. exists. applys* sub_transitivity H.
  - destruct H as [H|(?&?&H)].
    + inverts* H.
    + forwards (HS1&HS2): sub_and H.
      inverts HS1; inverts HS2.
      * apply bl_anda. assert (A1 <: (t_and t_int (t_arrow x x0))) by eauto.
        eauto.
      * applys* bottomlike_disjoit_sub.
      * apply bottomlike_symm. applys* bottomlike_disjoit_sub.
      * apply bl_andb. assert (A2 <: (t_and t_int (t_arrow x x0))) by eauto.
        eauto.
Qed.

Lemma and_sub_int_arrow : forall A B T1 T2,
    t_and A B <: t_and t_int (t_arrow T1 T2) ->
                 A  <: t_and t_int (t_arrow T1 T2) \/
                 (A <: t_int /\ B <: (t_arrow T1 T2)) \/
                 (B <: t_int /\ A <: (t_arrow T1 T2)) \/
                 B  <: t_and t_int (t_arrow T1 T2).
Proof.
  intros.
  inverts* H.
  - inverts H3; inverts H4; eauto.
Qed.

Definition btmLikeSpec2_simple C := C <: (t_and t_int (t_arrow t_bot typ_top)).

Lemma BL_soundness2 : forall A, bottomlike A -> btmLikeSpec2_simple A.
Proof.
  intros. inductions H; unfold btmLikeSpec2_simple in *; jauto; intros.
  - forwards [?|[(?&?)|[(?&?)|?]]]: and_sub_int_arrow IHbottomlike1;
      forwards [?|[(?&?)|[(?&?)|?]]]: and_sub_int_arrow IHbottomlike2;
      eauto.
    + applys* sub_transitivity (t_and t_int C).
      assert (A <: t_int) by applys* sub_transitivity H1.
      eauto.
    + applys* sub_transitivity (t_and (t_arrow t_bot typ_top) C).
      assert (A <: (t_arrow t_bot typ_top) ) by applys* sub_transitivity H1.
      eauto.
    + applys* sub_transitivity (t_and t_int C).
      assert (B <: t_int) by applys* sub_transitivity H3.
      eauto.
    + applys* sub_transitivity (t_and (t_arrow t_bot typ_top) C).
      assert (B <: (t_arrow t_bot typ_top) ) by applys* sub_transitivity H3.
      eauto.
  - forwards [?|[(?&?)|[(?&?)|?]]]: and_sub_int_arrow IHbottomlike1;
      forwards [?|[(?&?)|[(?&?)|?]]]: and_sub_int_arrow IHbottomlike2;
      eauto.
    + applys* sub_transitivity (t_and t_int C).
      assert (A <: t_int) by applys* sub_transitivity H1.
      eauto.
    + applys* sub_transitivity (t_and (t_arrow t_bot typ_top) C).
      assert (A <: (t_arrow t_bot typ_top) ) by applys* sub_transitivity H1.
      eauto.
    + applys* sub_transitivity (t_and t_int C).
      assert (B <: t_int) by applys* sub_transitivity H3.
      eauto.
    + applys* sub_transitivity (t_and (t_arrow t_bot typ_top) C).
      assert (B <: (t_arrow t_bot typ_top) ) by applys* sub_transitivity H3.
      eauto.
  -  applys* sub_transitivity IHbottomlike.
  -  applys* sub_transitivity IHbottomlike.
  -  applys* sub_transitivity IHbottomlike.
  -  applys* sub_transitivity IHbottomlike.
Qed.

(*

Typing and Terms Part

*)

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

Hint Constructors pexpr rexpr value uexpr findtype subtyping lc_exp ok okt.

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

