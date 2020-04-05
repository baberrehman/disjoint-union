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


Hint Resolve STop SInt SFun SAnd1 SAnd2 SAnd3 SOr1 SOr2 SOr3.

Lemma sub_refl: forall A, sub A A.
Proof.
  intros.
  induction A; eauto.
  apply SAnd1. apply SAnd2; eauto. admit.
  apply SAnd3; eauto. admit.
  apply SOr1. apply SOr2; auto. admit.
  apply SOr3; eauto. admit.
Admitted.

Hint Resolve sub_refl.

Inductive TopLike : typ -> Prop :=
  | TLTop  : TopLike TopT
  | TLAnd  : forall A B, TopLike A -> TopLike B -> TopLike (AndT A B)
  | TLFun  : forall A B, TopLike B -> TopLike (FunT A B).


Hint Resolve TLTop TLAnd TLFun.


(* Disjointness: Specification *)

Definition OrthoS (A B: typ) := forall C, sub A C -> sub B C -> 
                                  sub (AndT A B) C -> TopLike C.

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
  | Or1 : forall t1 t2 t3, Ortho (OrT t1 t2) t3 -> Ortho t1 t3
  | Or2 : forall t1 t2 t3, Ortho (OrT t1 t2) t3 -> Ortho t2 t3
  | Or3 : forall t1 t2 t3, Ortho t1 (OrT t2 t3) -> Ortho t1 t2
  | Or4 : forall t1 t2 t3, Ortho t1 (OrT t2 t3) -> Ortho t1 t3.

Hint Resolve OTop1 OTop2 OAnd1 OAnd2 OIntFunT OFunTInt OFun1 Or1 Or2 Or3 Or4.

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
apply H; auto.
apply SAnd2. auto.
Admitted.

Lemma sym_ortho : forall t1 t2, Ortho t1 t2 -> Ortho t2 t1.
Proof.
intros.
dependent induction H; eauto.
Qed.

Lemma inv_orthos_and: forall t1 t2 t3, OrthoS t1 (AndT t2 t3) -> OrthoS t1 t2 /\ OrthoS t1 t3.
Proof.
Admitted.

Lemma inv_ortho_or : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 t3 -> Ortho t1 (OrT t2 t3).
Proof.
Admitted.

Lemma inv_orthos_or : forall t1 t2 t3, OrthoS t1 (OrT t2 t3) -> OrthoS t1 t2 /\ OrthoS t1 t3.
Proof.
Admitted.

Lemma inv_orthos_fun : forall t1 t2 t3 t4, OrthoS (FunT t1 t2) (FunT t3 t4) -> OrthoS t2 t4.
Proof.
Admitted.

(* Soundness lemma of the disjointness algorithm *)

Lemma ortho_completness : forall t1, WFTyp t1 -> forall t2, WFTyp t2 -> OrthoS t1 t2 -> Ortho t1 t2.
Proof.
intros t1 wft1.
induction wft1; intros.
apply OTop2.
(* Case IntT *)
generalize H0. clear H0. induction H; intros; eauto.
unfold OrthoS in H0; eauto.
assert (t0: TopLike IntT); auto. inversion t0.
apply OAnd2. apply IHWFTyp1.
apply inv_orthos_and in H2.
destruct H2; auto. 
apply inv_orthos_and in H2.
destruct H2; auto.
apply inv_ortho_or.
apply IHWFTyp1.
apply inv_orthos_or in H1.
destruct H1; auto.
apply IHWFTyp2.
apply inv_orthos_or in H1.
destruct H1; auto.
(* Case FunT t1 t2 *)
induction H; eauto.
(* Case FunT t1 t2 | FunT t0 t3 *)
apply OFun1.
apply IHwft1_2; eauto.
apply inv_orthos_fun in H0. auto.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2. apply IHWFTyp1.
apply inv_orthos_and in H0.
destruct H0; auto.
apply IHWFTyp2.
apply inv_orthos_and in H0.
destruct H0; auto.
(* Case t11 -> t12 _|_ t21 | t22 *)
apply inv_ortho_or.
apply IHWFTyp1.
apply inv_orthos_or in H0.
destruct H0; auto.
apply IHWFTyp2.
apply inv_orthos_or in H0.
destruct H0; auto.
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
apply sym_ortho.
apply inv_ortho_or.
apply sym_ortho.
apply IHwft1_1; auto.
apply sym_orthos in H0.
apply inv_orthos_or in H0.
destruct H0.
apply sym_orthos; auto.
apply sym_ortho.
apply IHwft1_2; auto.
apply sym_orthos in H0.
apply inv_orthos_or in H0.
destruct H0.
apply sym_orthos; auto.
Qed.

(* Soundness of the disjointness algorithm: Theorem 7 *)

Lemma ortho_soundness : forall (t1 t2 : typ), WFTyp t1 -> WFTyp t2 -> Ortho t1 t2 -> OrthoS t1 t2.
intros.
induction H.
(*Case t1 TopT*)
unfold OrthoS. intros.
induction C; eauto. inversion H.
apply TLFun. apply IHC2; auto.
apply TLAnd. apply IHC1
apply invAndS1 in H. destruct H. auto.
apply invAndS1 in H0. destruct H0. auto.
apply IHC2.
apply invAndS1 in H. destruct H. auto.
apply invAndS1 in H0. destruct H0. auto.
apply TLTop.
(*Case TopT t1*)
unfold OrthoS. intros.
induction C. inversion H. inversion H.
apply TLAnd. apply IHC1.
apply invAndS1 in H. destruct H. auto.
apply invAndS1 in H0. destruct H0. auto.
apply IHC2.
apply invAndS1 in H. destruct H. auto.
apply invAndS1 in H0. destruct H0. auto.
apply TLTop.
(* Hard case *)
apply ortho_and; auto.
assert (OrthoS t2 t1). apply ortho_sym. apply IHOrtho1; auto.
assert (OrthoS t3 t1). apply ortho_sym. apply IHOrtho2; auto.
apply ortho_sym.
apply ortho_and; auto.
(* Case IntFunT *)
unfold OrthoS.
induction C; intros. inversion H0. inversion H.
apply TLAnd. apply IHC1. inversion H. auto. inversion H0. auto.
apply IHC2. inversion H. auto. inversion H0. auto.
(* TopT *)
apply TLTop.
(* Case FunTInt *)
unfold OrthoS.
induction C; intros. inversion H. inversion H0.
apply TLAnd.
apply IHC1.
inversion H. auto.
inversion H0. auto.
apply IHC2.
inversion H. auto.
inversion H0. auto.
(* TopT *)
apply TLTop.
(* FunTFunT *)
unfold OrthoS.
intros.
induction C. inversion H0.
assert (Ortho (FunT t1 t2) (FunT t3 t4)).
apply OFunT. auto.
apply applyOrtho. auto. auto. auto.
apply TLAnd. apply IHC1. inversion H0. auto. inversion H1. auto.
apply IHC2. inversion H0. auto. inversion H1. auto.
apply TLTop.
(* FunTFunTA *)
unfold OrthoS.
intros.
induction C. inversion H0.
assert (Ortho (FunT t1 t2) (FunT t3 t4)).
apply OFunTA. auto.
apply applyOrtho. auto. auto. auto. auto.
apply TLAnd. apply IHC1. inversion H0. auto. inversion H1. auto.
apply IHC2. inversion H0. auto. inversion H1. auto.
apply TLTop.
Defined.