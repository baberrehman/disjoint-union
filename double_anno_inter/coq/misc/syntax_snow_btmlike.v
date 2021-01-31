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

(* new spec is sound to the old spec *)
Lemma BL_new_sound_old : forall A,
    btmLikeSpec2_simple A -> btmLikeSpec A.
Proof.
  intros. unfolds in H. 
  unfolds. intros B HOrd HSub.
  induction HOrd.
  - assert (HS2: t_and t_int (t_arrow t_bot typ_top) <: t_int) by eauto.
    forwards* HS3: sub_transitivity H HS2.
    forwards* HS: sub_transitivity HSub HS3.
    inverts HS.
  - assert (HS2: t_and t_int (t_arrow t_bot typ_top) <: t_arrow t_bot typ_top) by eauto.
    forwards* HS3: sub_transitivity H HS2.
    forwards* HS: sub_transitivity HSub HS3.
    inverts HS.
  - assert (HS2: t_and t_int (t_arrow t_bot typ_top) <: t_int) by eauto.
    forwards* HS3: sub_transitivity H HS2.
    forwards* HS: sub_transitivity HSub HS3.
    inverts HS.
Qed.

Lemma BL_and : forall A B,
    btmLikeSpec (t_and A B) -> btmLikeSpec A \/ btmLikeSpec B \/ A <: t_int /\ B <: t_arrow t_bot typ_top \/ B <: t_int /\ A <: t_arrow t_bot typ_top.
Proof.
  intros.
  induction A.
  - right. left. unfolds in H. unfolds. intros H1 H2 H3.
    applys H H2. eauto.
  - induction B.
    + exfalso. applys* H t_int.
    + exfalso. applys* H t_int.
    + right. left. intros H1 H2 H3. applys* H H1. applys* s_anda. applys* sub_transitivity H3.
    + right. right. left*.
    + (* union *)
      unfolds in H.
      assert (btmLikeSpec (t_and t_int B1)). {
        intros H1 H2 H3. applys H H2.
        applys* s_anda; applys* sub_transitivity H3. }
      assert (btmLikeSpec (t_and t_int B2)). {
        intros H1 H2 H3. applys H H2.
        applys* s_anda; applys* sub_transitivity H3. }
      forwards~ [?|[?|[?|?]]] : IHB1 H0;
                                               forwards~ [?|[?|[?|?]]] : IHB2 H1.
      * forwards*: btm_like_spec_union_inv H2 H3.
      * right. right. left.
        (*  problem: Int /\ ( Int/\Char \/ Int->Int) is not bottom-like in new spec *)
      
      
Lemma BL_new_complete_old : forall A,
    btmLikeSpec A -> btmLikeSpec2_simple A.
Proof.
  intros. unfolds in H. unfolds.
  induction A.
  - exfalso. applys* H typ_top.
  - exfalso. applys* H t_int.
  - eauto.
  - exfalso. applys* H (t_arrow A1 A2).
  - applys s_ora;
      [applys IHA1 | applys IHA2]; intros T HT1 HT2; applys* H HT1.
  -
