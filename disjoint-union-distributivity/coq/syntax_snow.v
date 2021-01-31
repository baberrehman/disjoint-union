(*
This file contains the updates suggested by Snow.
Mod of syntax_bruno_btmlike
Try to eliminate the dependency of disjointness and bottomlike
A * B ::= bot-like A&B

and try to capture disjointness on functions with the help of distributivity
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
 | O_top : 
     ord t_top
 | O_int : 
     ord t_int
 | O_arrow : forall (A B:typ),
     ord (t_arrow A B).


(****************************************)
(**********  Disjoint Axioms  ***********)
(****************************************)
Inductive disjoint : typ -> typ -> Prop :=
| D_intArr : disjoint t_int (t_arrow t_bot t_top)
| D_CharBool : disjoint (t_arrow t_int t_int) (t_arrow t_int (t_arrow t_int t_int)).


(****************************************)
(*************  Subtyping ***************)
(****************************************)
Reserved Notation "A <: B" (at level 80).
Inductive subtyping : typ -> typ -> Prop :=    (* defn subtyping *)
 | S_top : forall A, A <: t_top
 | S_btm : forall A, t_bot <: A
 | S_refl : forall A, A <: A
 | S_trans: forall A B C,
    A <: B -> B <: C -> A <: C
 | S_arrow : forall (A1 A2 B1 B2:typ),
     B1 <: A1 ->
     A2 <: B2 ->
     (t_arrow A1 A2) <: (t_arrow B1 B2)
 | S_or : forall (A1 A2 B:typ),
     A1 <: B ->
     A2 <: B ->
     (t_or A1 A2) <: B
 | S_orl : forall (B1 B2:typ),
     B1 <: (t_or B1 B2)
 | S_orr : forall (B1 B2:typ),
     B2 <: (t_or B1 B2)
 | S_and : forall (A B1 B2:typ),
     A <: B1 ->
     A <: B2 ->
     A <: (t_and B1 B2)
 | S_andl : forall (A1 A2:typ),
     (t_and A1 A2) <: A1
 | S_andr : forall (A1 A2:typ),
     (t_and A1 A2) <: A2
 | S_distOr : forall A B C,
     t_or (t_and A B) C <: t_and (t_or A C) (t_or B C)
 | S_distAnd : forall A B C,
     t_and (t_or A B) C <: t_or (t_and A C) (t_and B C)
 | S_disjoint : forall A1 A2,
     disjoint A1 A2 ->
     t_and A1 A2 <: t_bot
where "A <: B" := (subtyping A B) : env_scope.

Hint Constructors ord disjoint subtyping : core.

Lemma sub_distOr_alt : forall A B C,
    t_or A (t_and B C) <: t_and (t_or A B) (t_or A C).
Admitted.

Lemma sub_distAnd_alt : forall A B C,
    t_and A (t_or B C) <: t_or (t_and A B) (t_and A C).
Admitted.

(****************************************)
(*********   Bottom-Like Spec   *********)
(****************************************)

(*
Definition btmLikeSpec C := C <: (t_and t_int (t_arrow t_bot t_top)). *)

Definition btmLikeSpec C := C <: t_bot.


(****************************************)
(***********  Disjoint Spec *************)
(****************************************)

Definition DisjSpec A B := btmLikeSpec (t_and A B).

Notation "A *s B" := (DisjSpec A B) (at level 80).



(**********************************)
(****  Examples  ****)
(**********************************)

Example two_arrows : forall A1 A2 A3,
    (t_arrow t_int t_int) *s (t_arrow A1 (t_arrow A2 A3)).
Proof.
Abort. (* does not hold *)


Lemma sub_union : forall A1 A2 B1 B2,
    t_and (t_or A1 A2) (t_or B1 B2) <: t_or (t_or (t_and A1 B1) (t_and A1 B2)) (t_or (t_and A2 B1) (t_and A2 B2)).
Proof.
  intros.
  applys S_trans. applys S_distAnd.
  applys S_or; applys S_trans.
  - applys sub_distAnd_alt.
  - applys S_trans. applys S_orl. apply S_refl.
  - applys sub_distAnd_alt.
  - applys S_trans. applys S_orr. apply S_refl.
Qed.

(* 			• A1 = Int \/ Char (I->I)
			• A2 = Char \/ Bool (I->I->I)
			• B = Bool \/ Int                 
                        A1&A2 * B                                 *)
Example three_unions :
    t_and (t_or t_int (t_arrow t_int t_int)) (t_or (t_arrow t_int t_int) (t_arrow t_int (t_arrow t_int t_int))) *s t_or (t_arrow t_int (t_arrow t_int t_int)) t_int.
Proof.
  intros. repeat unfolds.
  applys S_trans. applys S_and.
  - applys S_trans. applys S_andl. applys sub_union.
  - applys S_trans. applys S_andr. applys S_refl.
  - applys S_trans. applys sub_union.
    repeat applys S_or; applys S_trans; try applys S_distAnd;
      repeat applys S_or.
    + applys S_trans (t_and t_int (t_arrow t_bot t_top)). applys S_trans. applys S_andl.
      eauto. applys* S_disjoint. 
    + applys S_trans (t_and t_int (t_arrow t_bot t_top)). applys S_trans. applys S_andl.
      eauto. applys* S_disjoint. 
    + applys S_trans (t_and t_int (t_arrow t_bot t_top)). applys S_trans. applys S_andl.
      eauto. applys* S_disjoint. 
    + applys S_trans (t_and t_int (t_arrow t_bot t_top)). applys S_trans. applys S_andl.
      eauto. applys* S_disjoint. 
    + applys S_trans (t_and (t_arrow t_int t_int) (t_arrow t_int (t_arrow t_int t_int))).
      eauto. applys* S_disjoint.
    + applys S_trans (t_and (t_arrow t_int t_int) (t_arrow t_int (t_arrow t_int t_int))).
      eauto. applys* S_disjoint.
    + applys S_trans (t_and t_int (t_arrow t_bot t_top)).
      eauto. applys* S_disjoint. 
    + applys S_trans (t_and t_int (t_arrow t_bot t_top)).
      eauto. applys* S_disjoint.
Qed.

(**********************************)
(****  Compare with old spec   ****)
(**********************************)

Definition btmLikeSpec_old C := forall A, ord A -> A <: C -> False.

(* new spec is sound to the old spec *)
Lemma BL_new_sound_old : forall A,
    btmLikeSpec A -> btmLikeSpec_old A.
Proof.
  intros. unfolds in H. 
  unfolds. intros B HOrd HSub.
  induction HOrd.
  - forwards: S_trans HSub H.
    (* T <: Bot *)
    admit.
  - (* Int <: Bot *)
    admit.
  - (* arrow <: Bot *)
    admit.
Qed.

Lemma btm_like_spec_union_inv : forall A B, btmLikeSpec_old A -> btmLikeSpec_old B -> btmLikeSpec_old (t_or A B).
Proof.
  intros.
  unfold btmLikeSpec_old in *.
  intros.
  assert (HU: forall A B C, A <: (t_or B C) -> A <: B \/ A <: C) by admit.
  forwards* [?|?]: HU H2.
Qed.

Lemma BL_and : forall A B,
    btmLikeSpec_old (t_and A B) -> btmLikeSpec_old A \/ btmLikeSpec_old B \/ exists A' B', A <: A' /\ B <: B' /\ disjoint A' B'.
Proof.
  intros.
  induction A.
  - right. left. unfolds in H. unfolds. intros H1 H2 H3. applys* H H2.
  - induction B.
    + exfalso. applys* H t_int.
    + exfalso. applys* H t_int.
    + right. left. intros H1 H2 H3. applys* H H1.
    + right. right. exists; repeat split; try applys D_intArr; eauto.
    + (* union *)
      unfolds in H.
      assert (btmLikeSpec_old (t_and t_int B1)). {
        intros H1 H2 H3. applys H H2. applys S_trans H3. eauto. }
      assert (btmLikeSpec_old (t_and t_int B2)). {
        intros H1 H2 H3. applys H H2. eauto. }
      forwards~ [?|[?|?]] : IHB1 H0; forwards~ [?|[?|?]] : IHB2 H1.
      * forwards*: btm_like_spec_union_inv H2 H3.
      * right. right. lets (?&(?&(?&(?&?)))): H3.
        exists~ x x0. repeat split~.
        (* depends on BL_complete *)
        admit.
      * (* similar *) admit.
      * right. right. lets (?&(?&(?&(?&?)))): H2. lets (?&(?&(?&(?&?)))): H3.
        (*  counter example: Int /\ ( Char \/ String ) is not bottom-like in new spec *)
      
      
Lemma BL_new_complete_old : forall A,
    btmLikeSpec_old A -> btmLikeSpec A.
Proof.
  intros. unfolds in H. unfolds.
  induction A.
  - exfalso. applys* H t_top.
  - exfalso. applys* H t_int.
  - eauto.
  - exfalso. applys* H (t_arrow A1 A2).
  - applys S_or;
      [applys IHA1 | applys IHA2]; intros T HT1 HT2; applys* H HT1.
  -


    
(**********************************)
(****  Bottom-Like Properties  ****)
(**********************************)
    
(*************************************)
(*****  Disjointness Properties  *****)
(*************************************)



(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)


(*************************)
(***** Ordinary Types ****)
(*************************)

(** infrastructure *)

Lemma ord_sub_union : forall A, ord A -> forall A1 A2, A <: t_or A1 A2 -> A <: A1 \/ A <: A2.
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
    applys S_anda. eauto. eauto.
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
  apply S_anda; auto.
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
    ord Ta -> ord Tb -> ord Tc
    -> Ta <: (t_and B C)
    -> Tb <: (t_and A C)
    -> Tc <: (t_and A B)
             -> exists T, ord T /\ T <: (t_and (t_and A B) C).
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
