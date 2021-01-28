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
 | t_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_or : typ -> typ -> typ
 | t_and : typ -> typ -> typ.

(* defns Ordinary *)
Inductive ord : typ -> Prop :=    (* defn ord *)
 | SO_top : 
     ord t_top
 | SO_bot : 
     ord t_bot
 | SO_int : 
     ord t_int
 | SO_arrow : forall (A B:typ),
     ordu A ->
     ord B ->
     ord (t_arrow A B)
 | SO_or : forall (A B:typ),
     ord A ->
     ord B ->
     ord (t_or A B)
with ordu : typ -> Prop :=    (* defn ordu *)
 | OU_top : 
     ordu t_top
 | OU_bot : 
     ordu t_bot
 | OU_int : 
     ordu t_int
 | OU_arrow : forall (A B:typ),
     ordu (t_arrow A B)
 | OU_and : forall (A B:typ),
     ordu A ->
     ordu B ->
     ordu (t_and A B).

(* split and split union*)
Inductive spl : typ -> typ -> typ -> Prop :=    (* defn spl *)
 | SSp_and : forall (A B:typ),
     spl (t_and A B) A B
 | SSp_arrow : forall (A B C D:typ),
     spl B C D ->
     spl (t_arrow A B) (t_arrow A C) (t_arrow A D)
 | SSp_arrowUnion : forall (A D B C:typ),
     ord D ->
     splu A B C ->
     spl (t_arrow A D) (t_arrow B D) (t_arrow C D)
 | SSp_orl : forall (A B A1 A2:typ),
     spl A A1 A2 ->
     spl (t_or A B) (t_or A1 B) (t_or A2 B)
 | SSp_orr : forall (A B B1 B2:typ),
     ord A ->
     spl B B1 B2 ->
     spl (t_or A B) (t_or A B1) (t_or A B2)
with splu : typ -> typ -> typ -> Prop :=    (* defn splu *)
 | SpU_or : forall (A B:typ),
     splu (t_or A B) A B
 | SpU_andl : forall (A B A1 A2:typ),
     splu A A1 A2 ->
     splu (t_and A B) (t_and A1 B) (t_and A2 B)
 | SpU_andr : forall (A B B1 B2:typ),
     ordu A ->
     splu B B1 B2 ->
     splu (t_and A B) (t_and A B1) (t_and A B2).

(* defns Subtyping *)
Reserved Notation "A <: B" (at level 80).
Inductive subtyping : typ -> typ -> Prop :=    (* defn subtyping *)
 | s_top : forall A, A <: t_top
 | s_btm : forall A, t_bot <: A
 | s_int : t_int <: t_int
 | s_arrow : forall (A1 A2 B1 B2:typ),
     ord (t_arrow A1 A2) ->
     ord (t_arrow B1 B2) ->
     B1 <: A1 ->
     A2 <: B2 ->
     (t_arrow A1 A2) <: (t_arrow B1 B2)
 | s_or : forall (A A1 A2 B:typ),
     splu A A1 A2 ->  
     A1 <: B ->
     A2 <: B ->
     A <: B
 | s_orl : forall (A B B1 B2:typ),
     splu B B1 B2 -> 
     A <: B1 ->
     A <: B
 | s_orr : forall (A B B1 B2:typ),
     splu B B1 B2 -> 
     A <: B2 ->
     A <: B
 | s_and : forall (A B B1 B2:typ),
     spl B B1 B2 ->  
     A <: B1 ->
     A <: B2 ->
     A <: B
 | s_andl : forall (A A1 A2 B:typ),
     spl A A1 A2 ->   
     A1 <: B ->
     A <: B
 | s_andr : forall (A A1 A2 B:typ),
     spl A A1 A2 ->   
     A2 <: B ->
     A <: B
where "A <: B" := (subtyping A B) : env_scope.

Hint Constructors subtyping : core.

(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)


(*************************)
(***** Ordinary Types ****)
(*************************)


(****************************************)
(**********  Disjoint Axioms  ***********)
(****************************************)


(****************************************)
(*********   Bottom-Like Spec   *********)
(****************************************)


Definition btmLikeSpec C := C <: (t_and t_int (t_arrow t_bot t_top)).


(****************************************)
(**********    Dijoint Spec   ***********)
(****************************************)

Definition DisjSpec A B := btmLikeSpec (t_and A B).

Notation "A *s B" := (DisjSpec A B) (at level 80).



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

Lemma btm_like_spec_union_inv : forall A B, btmLikeSpec A -> btmLikeSpec B -> btmLikeSpec (t_or A B).
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

Lemma ord_sub_union : forall A, Ord A -> forall A1 A2, A <: t_or A1 A2 -> A <: A1 \/ A <: A2.
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

Lemma disj_sub_union : forall A B C, A *s C -> B *s C -> t_or A B *s C.
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

Lemma bl_union_inv : forall A B, bottomlike (t_or A B) ->
bottomlike A /\ bottomlike B.
Proof.
intros. inverts* H.
Qed.

Lemma btm_like_spec_union_inter : forall A1 A2 B1 B2, btmLikeSpec (t_and (t_and A1 A2) (t_or B1 B2)) ->
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

Lemma top_btmlike : forall A, btmLikeSpec (t_and t_top A) -> btmLikeSpec A.
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
  - exfalso. applys* H t_top.
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
    assert (Hs: t_top <: t_int) by applys* sub_transitivity H.
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

Definition btmLikeSpec2_simple C := C <: (t_and t_int (t_arrow t_bot t_top)).

Lemma BL_soundness2 : forall A, bottomlike A -> btmLikeSpec2_simple A.
Proof.
  intros. inductions H; unfold btmLikeSpec2_simple in *; jauto; intros.
  - forwards [?|[(?&?)|[(?&?)|?]]]: and_sub_int_arrow IHbottomlike1;
      forwards [?|[(?&?)|[(?&?)|?]]]: and_sub_int_arrow IHbottomlike2;
      eauto.
    + applys* sub_transitivity (t_and t_int C).
      assert (A <: t_int) by applys* sub_transitivity H1.
      eauto.
    + applys* sub_transitivity (t_and (t_arrow t_bot t_top) C).
      assert (A <: (t_arrow t_bot t_top) ) by applys* sub_transitivity H1.
      eauto.
    + applys* sub_transitivity (t_and t_int C).
      assert (B <: t_int) by applys* sub_transitivity H3.
      eauto.
    + applys* sub_transitivity (t_and (t_arrow t_bot t_top) C).
      assert (B <: (t_arrow t_bot t_top) ) by applys* sub_transitivity H3.
      eauto.
  - forwards [?|[(?&?)|[(?&?)|?]]]: and_sub_int_arrow IHbottomlike1;
      forwards [?|[(?&?)|[(?&?)|?]]]: and_sub_int_arrow IHbottomlike2;
      eauto.
    + applys* sub_transitivity (t_and t_int C).
      assert (A <: t_int) by applys* sub_transitivity H1.
      eauto.
    + applys* sub_transitivity (t_and (t_arrow t_bot t_top) C).
      assert (A <: (t_arrow t_bot t_top) ) by applys* sub_transitivity H1.
      eauto.
    + applys* sub_transitivity (t_and t_int C).
      assert (B <: t_int) by applys* sub_transitivity H3.
      eauto.
    + applys* sub_transitivity (t_and (t_arrow t_bot t_top) C).
      assert (B <: (t_arrow t_bot t_top) ) by applys* sub_transitivity H3.
      eauto.
  -  applys* sub_transitivity IHbottomlike.
  -  applys* sub_transitivity IHbottomlike.
  -  applys* sub_transitivity IHbottomlike.
  -  applys* sub_transitivity IHbottomlike.
Qed.
