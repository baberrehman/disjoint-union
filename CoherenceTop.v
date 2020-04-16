Require Import String.
Require Import STLC.
Require Import Coq.Structures.Equalities.
Require Import Coq.MSets.MSetInterface.
Require Import Arith.
Require Import Setoid.
Require Import Program.Equality.
Require Import TypingFlags.Loader.

Module CoherenceTop
       (Import VarTyp : BooleanDecidableType')
       (Import set : MSetInterface.S).

  
Module ST := TLC(VarTyp)(set).
Import ST.


(* Types *)

Inductive typ : Type :=
  | TopT : typ
  | IntT : typ
  | FunT : typ -> typ -> typ
  | AndT : typ -> typ -> typ
  | OrT  : typ -> typ -> typ.

Inductive Atomic : typ -> Prop :=
  | ATop : Atomic TopT
  | AInt : Atomic IntT
  | AFun : forall t1 t2, Atomic (FunT t1 t2).

Hint Resolve TopT IntT FunT AndT OrT ATop AInt AFun.

(* Subtyping relation *)

Inductive sub : typ -> typ -> Prop :=
  | STop : forall t, sub t TopT
  | SInt : sub IntT IntT
  | SFun : forall o1 o2 o3 o4, sub o3 o1 -> sub o2 o4 -> 
     sub (FunT o1 o2) (FunT  o3 o4)
  | SAnd1 : forall t t1 t2, sub t t1 -> sub t t2 -> 
     sub t (AndT t1 t2)
  | SAnd2 : forall t t1 t2, sub t1 t -> Atomic t ->
     sub (AndT t1 t2) t
  | SAnd3 : forall t t1 t2, sub t2 t -> Atomic t ->
     sub (AndT t1 t2) t
  | SOr1 : forall t t1 t2, sub t t2 -> sub t1 t2 -> 
     sub (OrT t t1) t2
  | SOr2 : forall t t1 t2, sub t t1 -> Atomic t ->
     sub t (OrT t1 t2)
  | SOr3 : forall t t1 t2, sub t t2 -> Atomic t ->
     sub t (OrT t1 t2).

Lemma sand2_atomic : forall t1 t2 t3, sub t1 t3 -> Atomic t3 -> sub (AndT t1 t2) t3.
Proof.
intros.
eapply SAnd2 in H; eauto.
Qed.

Lemma sand3_atomic : forall t1 t2 t3, sub t2 t3 -> Atomic t3 -> sub (AndT t1 t2) t3.
Proof.
intros.
eapply SAnd3 in H; eauto.
Qed.

Lemma sor2_atomic : forall t1 t2 t3, sub t1 t2 -> Atomic t1 -> sub t1 (OrT t2 t3).
Proof.
intros.
eapply SOr2 in H; eauto.
Qed.

Lemma sor3_atomic : forall t1 t2 t3, sub t1 t3 -> Atomic t1 -> sub t1 (OrT t2 t3).
Proof.
intros.
eapply SOr3 in H; eauto.
Qed.

Hint Resolve STop SInt SFun SAnd1 SAnd2 SAnd3 SOr1 SOr2 SOr3
             sand2_atomic sand3_atomic sor2_atomic sor3_atomic.

Lemma inv_ands1 : forall t t1 t2, sub t (AndT t1 t2) -> sub t t1 /\ sub t t2.
Proof.
  intro t; induction t; intros.
  - inversion H. auto.
  - inversion H. auto.
  - inversion H. auto.
(* Case AndT *)
  - inversion H. auto.
    assert (sub t1 t0 /\ sub t1 t3).
    auto.
    split.
    destruct H5; apply SAnd2; auto; inversion H4.
    destruct H5; apply SAnd3; auto; inversion H4.
    assert (sub t2 t0 /\ sub t2 t3).
    auto.
    split.
    destruct H5; apply SAnd2; auto; inversion H4.
    destruct H5; apply SAnd3; auto; inversion H4.
(* Case OrT *)
  - inversion H. auto.
    assert (sub t1 t0 /\ sub t1 t3).
    auto.
    assert (sub t2 t0 /\ sub t2 t3).
    auto.
    split.
    apply SOr1.
    destruct H5. auto.
    destruct H6. auto.
    apply SOr1.
    destruct H5. auto.
    destruct H6. auto.
Qed.

Lemma inv_ors1 : forall t t2 t3, sub (OrT t2 t3) t -> sub t2 t /\ sub t3 t.
Proof.
  intro t; induction t; intros.
  - inversion H; auto.
  - inversion H; auto.
  - inversion H; auto.
(* Case AndT *)
  - inversion H; auto.
    assert (sub t0 t1 /\ sub t3 t1).
    auto.
    assert (sub t0 t2 /\ sub t3 t2).
    auto.
    split.
    apply SAnd1.
    destruct H5. auto.
    destruct H6. auto.
    apply SAnd1.
    destruct H5. auto.
    destruct H6. auto.
(* Case OrT *)
  - inversion H; auto.
    assert (sub t0 t1 /\ sub t3 t1).
    auto.
    split.
    apply SOr2.
    destruct H5. auto.
    inversion H4.
    apply SOr2.
    destruct H5. auto.
    inversion H4.
    assert (sub t0 t2 /\ sub t3 t2).
    auto.
    split.
    apply SOr3.
    destruct H5. auto.
    inversion H4.
    apply SOr3.
    destruct H5. auto.
    inversion H4.
Qed.

Lemma sub_refl: forall A, sub A A.
Proof.
  intros.
  induction A; eauto.
  apply SAnd1.
  apply SAnd2; eauto. admit.
  apply SAnd3; eauto. admit.
  apply SOr1. apply SOr2; auto. admit.
  apply SOr3; eauto. admit.
Admitted.

Hint Resolve sub_refl.

Inductive TopLike : typ -> Prop :=
  | TLTop  : TopLike TopT
  | TLAnd  : forall A B, TopLike A -> TopLike B -> TopLike (AndT A B)
  | TLOr1  : forall A B, TopLike A -> TopLike (OrT A B)
  | TLOr2  : forall A B, TopLike B -> TopLike (OrT A B).


Hint Resolve TLTop TLAnd TLOr1 TLOr2.


(* Disjointness: Specification *)

Definition OrthoS (A B: typ) := forall C, sub A C -> sub B C -> 
                                  sub (AndT A B) C -> TopLike C.

Definition TopLikeS (A: typ) := sub TopT A.

Lemma completeTopLike : forall A, TopLikeS A -> TopLike A.
Proof.
intros.
unfold TopLikeS in H.
dependent induction H; eauto.
Defined.

Lemma soundTopLike : forall A, TopLike A -> TopLikeS A.
Proof.
intros.
dependent induction H; eauto.
 - unfold TopLikeS; auto.
 - unfold TopLikeS; auto.
 - unfold TopLikeS; auto.
 - unfold TopLikeS; auto.
Defined.

(* Disjointness: Implementation *)

(*Set Guard Checking.
Print Typing Flags.*)

Inductive Ortho : typ -> typ -> Prop :=
  | OTop1 : forall t1, Ortho t1 TopT
  | OTop2 : forall t1, Ortho TopT t1
  | OAnd1 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t2 t3 -> Ortho (AndT t1 t2) t3
  | OAnd2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (AndT t2 t3)
  | OIntFunT : forall t1 t2, Ortho IntT (FunT t1 t2)
  | OFunTInt : forall t1 t2, Ortho (FunT t1 t2) IntT
  | OFun1   : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (FunT t1 t2) (FunT t3 t4)
(*  | OFun2  : forall t1 t2 t3 t4, Ortho t1 t3 -> Ortho (FunT t1 t2) (FunT t3 t4) *)
  | Or1 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 (OrT t2 t3)
  | Or2 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t1 (OrT t2 t3)
  | Or3 : forall t1 t2 t3, Ortho t1 t3 -> Ortho (OrT t1 t2) t3
  | Or4 : forall t1 t2 t3, Ortho t2 t3 -> Ortho (OrT t1 t2) t3.

Hint Resolve OTop1 OTop2 OAnd1 OAnd2 OIntFunT OFunTInt Or1 OFun1 Or2 Or3 Or4.

Lemma applyOrthoS : forall A B, OrthoS A B -> forall C, sub A C -> sub B C ->
                      sub (AndT A B) C -> TopLike C.
Proof.
intros. destruct H with (C:=C); auto.
Defined.

Lemma applyOrtho : forall A B, Ortho A B -> forall C, sub A C -> sub B C -> 
                    sub (AndT A B) C -> TopLike C.
Proof.
intros.
dependent induction C; eauto.
Admitted.


(* Well-formed types *)

Inductive WFTyp : typ -> Prop :=
  | WFTop : WFTyp TopT
  | WFInt : WFTyp IntT
  | WFFun : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (FunT t1 t2)
  | WFAnd : forall t1 t2, WFTyp t1 -> WFTyp t2 -> OrthoS t1 t2 -> WFTyp (AndT t1 t2)
  | WOr   : forall t1 t2, WFTyp t1 -> WFTyp t2 -> WFTyp (OrT t1 t2).

Lemma sym_orthos : forall t1 t2, OrthoS t1 t2 -> OrthoS t2 t1.
Proof.
intros.
unfold OrthoS in *; intros.
dependent induction C; eauto.
(* Case And *)
- apply TLAnd.
  apply IHC1.
  apply inv_ands1 in H0; destruct H0; auto.
  apply inv_ands1 in H1; destruct H1; auto.
  apply inv_ands1 in H2; destruct H2; eauto.
  apply IHC2.
  apply inv_ands1 in H0; destruct H0; auto.
  apply inv_ands1 in H1; destruct H1; auto.
  apply inv_ands1 in H2; destruct H2; eauto.
(* Case Or *)
- dependent destruction H2; inversion H3.
Defined.

Lemma sym_ortho : forall t1 t2, Ortho t1 t2 -> Ortho t2 t1.
Proof.
intros.
- dependent induction H; eauto.
Qed.

Lemma inv_orthos_and: forall t1 t2 t3, OrthoS t1 (AndT t2 t3) -> OrthoS t1 t2 /\ OrthoS t1 t3.
Proof.
intros.
split.
 - unfold OrthoS; intros.
   dependent induction C; eauto.
  + apply TLAnd.
    apply IHC1.
    apply inv_ands1 in H0; destruct H0; auto.
    apply inv_ands1 in H1; destruct H1; auto.
    apply inv_ands1 in H2; destruct H2; auto.
    apply IHC2.
    apply inv_ands1 in H0; destruct H0; auto.
    apply inv_ands1 in H1; destruct H1; auto.
    apply inv_ands1 in H2; destruct H2; auto.
  + dependent destruction H2; inversion H3.
 - unfold OrthoS; intros.
   dependent induction C; eauto.
  + apply TLAnd.
    apply IHC1.
    apply inv_ands1 in H0; destruct H0; auto.
    apply inv_ands1 in H1; destruct H1; auto.
    apply inv_ands1 in H2; destruct H2; auto.
    apply IHC2.
    apply inv_ands1 in H0; destruct H0; auto.
    apply inv_ands1 in H1; destruct H1; auto.
    apply inv_ands1 in H2; destruct H2; auto.
  + dependent destruction H2; inversion H3.
Defined.

Lemma inv_orthos_or : forall t1 t2, OrthoS t1 (OrT t1 t2) -> OrthoS t1 t2.
Proof.
intros.
unfold OrthoS in H.
unfold OrthoS. intros.
dependent induction C; eauto.
 - apply TLAnd.
   apply IHC1.
   apply inv_ands1 in H0; destruct H0; auto.
   apply inv_ands1 in H1; destruct H1; auto.
   apply inv_ands1 in H2; destruct H2; auto.
   apply IHC2.
   apply inv_ands1 in H0; destruct H0; auto.
   apply inv_ands1 in H1; destruct H1; auto.
   apply inv_ands1 in H2; destruct H2; auto.
 - dependent destruction H2; inversion H3.
Defined.

Lemma inv_orthos_or2 : forall t1 t2 t3, OrthoS t1 (OrT t2 t3) -> OrthoS t1 t2 \/ OrthoS t1 t3.
Proof.
intros.
left.
unfold OrthoS; intros.
unfold OrthoS in H.
dependent induction C; auto.
inversion H2.
apply H; auto.
apply SOr1; auto. admit.
apply H; auto.
apply SOr1; auto. admit.
Admitted.

Lemma ortho_fun : forall t1 t2 t3 t4, Ortho (FunT t1 t2) (FunT t3 t4) 
                          -> Ortho t2 t4. 
Proof.
intros.
inversion H. auto.
Defined.

(* Soundness lemma of the disjointness algorithm *)

Lemma ortho_completness : forall t1, WFTyp t1 -> forall t2, WFTyp t2 -> OrthoS t1 t2 -> Ortho t1 t2.
Proof.
intros t1 wft1.
induction wft1; intros.
apply OTop2.
(* Case IntT *)
induction H; intros; eauto.
unfold OrthoS in H0; eauto.
assert (t0: TopLike IntT); auto. inversion t0.
apply OAnd2. apply IHWFTyp1.
apply inv_orthos_and in H0.
destruct H0; auto. 
apply inv_orthos_and in H0.
destruct H0; auto.
apply inv_orthos_or2 in H0.
destruct H0.
apply Or1.
apply IHWFTyp1. auto.
apply Or2.
apply IHWFTyp2. auto.
(* Case FunT t1 t2 *)
induction H; eauto.
(* Case FunT t1 t2 | FunT t0 t3 *)
apply OFun1.
apply IHwft1_2; eauto.
unfold OrthoS in H0.
unfold OrthoS. intros.
assert (TopLike (FunT (AndT t1 t0) C)).
apply H0.
apply SFun. apply SAnd2. auto. admit. auto.
apply SFun. apply SAnd3. auto. admit. auto.
admit. admit.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2. apply IHWFTyp1.
apply inv_orthos_and in H0.
destruct H0; auto.
apply IHWFTyp2.
apply inv_orthos_and in H0.
destruct H0; auto.
(* Case t11 -> t12 _|_ t21 | t22 *)
apply inv_orthos_or2 in H0.
destruct H0.
apply Or1.
apply IHWFTyp1. auto.
apply Or2.
apply IHWFTyp2. auto.
(* Case (t11 & t12) _|_ t2 *)
apply OAnd1.
apply IHwft1_1; auto.
apply sym_orthos in H1.
apply inv_orthos_and in H1.
apply sym_orthos.
destruct H1; auto.
apply IHwft1_2; auto.
apply sym_orthos in H1.
apply inv_orthos_and in H1.
apply sym_orthos.
destruct H1; auto.
(* Case (t11 | t12) _|_ t2 *)
apply sym_orthos in H0.
apply inv_orthos_or2 in H0.
destruct H0.
apply Or3.
apply IHwft1_1. auto.
apply sym_orthos. auto.
apply Or4.
apply IHwft1_2. auto.
apply sym_orthos. auto.
Admitted.

Lemma ortho_and : forall {A B C}, OrthoS A C -> OrthoS B C -> OrthoS (AndT A B) C.
Proof.
intros.
unfold OrthoS. intros.
unfold OrthoS in H.
unfold OrthoS in H0.
dependent induction C0; eauto.
 - inversion H1.
   apply H; auto.
   apply H0; auto.
 - inversion H1.
   apply H; auto.
   apply H0; auto.
 - apply TLAnd.
   + apply IHC0_1.
     apply inv_ands1 in H1. destruct H1. auto.
     apply inv_ands1 in H2. destruct H2. auto.
     apply inv_ands1 in H3. destruct H3. auto.
   + apply IHC0_2.
     apply inv_ands1 in H1. destruct H1. auto.
     apply inv_ands1 in H2. destruct H2. auto.
     apply inv_ands1 in H3. destruct H3. auto.
 - dependent destruction H3; inversion H4.
Defined.

Lemma orthos_or1 : forall {A B C}, OrthoS A C -> OrthoS (OrT A B) C.
Proof.
intros.
unfold OrthoS in *.
intros.
induction C0; eauto.
 - apply inv_ors1 in H0; destruct H0; auto.
 - apply inv_ors1 in H0; destruct H0; auto.
 - apply TLAnd.
  + apply IHC0_1.
    apply inv_ands1 in H0; destruct H0; auto.
    apply inv_ands1 in H1; destruct H1; auto.
    apply inv_ands1 in H2; destruct H2; auto.
  + apply IHC0_2.
    apply inv_ands1 in H0; destruct H0; auto.
    apply inv_ands1 in H1; destruct H1; auto.
    apply inv_ands1 in H2; destruct H2; auto.
 - dependent destruction H2; inversion H3.
Defined.

Lemma orthos_or2 : forall {A B C}, OrthoS B C -> OrthoS (OrT A B) C.
Proof.
intros.
unfold OrthoS in *.
intros.
induction C0; eauto.
 - apply inv_ors1 in H0; destruct H0; auto.
 - apply inv_ors1 in H0; destruct H0; auto.
 - apply TLAnd.
  + apply IHC0_1.
    apply inv_ands1 in H0; destruct H0; auto.
    apply inv_ands1 in H1; destruct H1; auto.
    apply inv_ands1 in H2; destruct H2; auto.
  + apply IHC0_2.
    apply inv_ands1 in H0; destruct H0; auto.
    apply inv_ands1 in H1; destruct H1; auto.
    apply inv_ands1 in H2; destruct H2; auto.
 - dependent destruction H2; inversion H3.
Defined.

Lemma orthos_or3 : forall {A B C}, OrthoS A C \/ OrthoS B C -> OrthoS (OrT A B) C.
Proof.
intros.
unfold OrthoS. intros.
unfold OrthoS in H.
induction C0; eauto.
 - destruct H.
  + apply inv_ors1 in H0; destruct H0; auto.
  + apply inv_ors1 in H0; destruct H0; auto.
 - destruct H.
  + apply inv_ors1 in H0; destruct H0; auto.
  + apply inv_ors1 in H0; destruct H0; auto.
 - apply TLAnd.
  + apply IHC0_1.
    apply inv_ands1 in H0. destruct H0. auto.
    apply inv_ands1 in H1. destruct H1. auto.
    apply inv_ands1 in H2. destruct H2. auto.
  + apply IHC0_2.
    apply inv_ands1 in H0. destruct H0. auto.
    apply inv_ands1 in H1. destruct H1. auto.
    apply inv_ands1 in H2. destruct H2. auto.
 - dependent destruction H2; inversion H3.
Defined.

(* Soundness of the disjointness algorithm: Theorem 7 *)

Lemma ortho_soundness : forall (t1 t2 : typ), WFTyp t1 -> WFTyp t2 -> Ortho t1 t2 -> OrthoS t1 t2.
intros.
induction H1.
(*Case t1 TopT*)
unfold OrthoS; intros.
induction C; eauto. inversion H2. inversion H2.
apply TLAnd. apply IHC1.
apply inv_ands1 in H1. destruct H1. auto.
apply inv_ands1 in H2. destruct H2. auto.
apply inv_ands1 in H3. destruct H3. auto.
apply IHC2.
apply inv_ands1 in H1. destruct H1. auto.
apply inv_ands1 in H2. destruct H2. auto.
apply inv_ands1 in H3. destruct H3. auto.
dependent destruction H3; inversion H4.
(*Case TopT t1*)
unfold OrthoS. intros.
induction C.
apply TLTop.
inversion H1. inversion H1.
apply TLAnd. apply IHC1.
apply inv_ands1 in H1. destruct H1. auto.
apply inv_ands1 in H2. destruct H2. auto.
apply inv_ands1 in H3. destruct H3. auto.
apply IHC2.
apply inv_ands1 in H1. destruct H1. auto.
apply inv_ands1 in H2. destruct H2. auto.
apply inv_ands1 in H3. destruct H3. auto.
dependent destruction H3; inversion H4.
(* Hard case: (AndT t1 t2) t3 *)
apply ortho_and.
apply IHOrtho1; eauto. inversion H. auto.
apply IHOrtho2; eauto. inversion H. auto.
apply sym_orthos.
apply ortho_and.
apply sym_orthos.
apply IHOrtho1; eauto. inversion H0. auto.
apply sym_orthos.
apply IHOrtho2; eauto. inversion H0. auto.
(* Case IntFunT *)
unfold OrthoS.
induction C; intros. apply TLTop. inversion H2. inversion H1.
apply TLAnd. apply IHC1. inversion H1. auto. inversion H2. auto.
apply inv_ands1 in H3. destruct H3. auto.
apply IHC2. inversion H1. auto. inversion H2. auto.
apply inv_ands1 in H3. destruct H3. auto.
dependent destruction H3; inversion H4.
(* Case FunTInt *)
unfold OrthoS.
induction C; intros. apply TLTop. inversion H1. inversion H2.
apply TLAnd.
apply IHC1. inversion H1. auto. inversion H2. auto.
apply inv_ands1 in H3. destruct H3. auto.
apply IHC2. inversion H1. auto. inversion H2. auto.
apply inv_ands1 in H3. destruct H3. auto.
dependent destruction H3; inversion H4.
(* FunTFunT *)
unfold OrthoS.
intros.
induction C. apply TLTop. inversion H2.
assert (Ortho (FunT t1 t2) (FunT t3 t4)).
apply OFun1. auto.
eapply applyOrtho with (A:=(FunT t1 t2)) (B:=(FunT t3 t4)); eauto.
apply TLAnd. apply IHC1. inversion H2. auto. inversion H3. auto.
apply inv_ands1 in H4. destruct H4. auto.
apply IHC2. inversion H2. auto. inversion H3. auto.
apply inv_ands1 in H4. destruct H4. auto.
dependent destruction H4; inversion H5.
(* Case OrT *)
apply sym_orthos.
apply orthos_or1.
apply sym_orthos.
apply IHOrtho; auto. inversion H0. auto.
apply sym_orthos.
apply orthos_or2.
apply sym_orthos.
apply IHOrtho; auto. inversion H0. auto.
apply orthos_or1.
apply IHOrtho; auto. inversion H. auto.
apply orthos_or2.
apply IHOrtho; auto. inversion H. auto.
Defined.
