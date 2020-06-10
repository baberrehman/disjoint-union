Require Import STLC.
Require Import Program.Equality.

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
  | SAnd4 : forall t t1 t2, sub t1 t -> sub t t1 ->
     sub (AndT t1 t2) t
  | SAnd5 : forall t t1 t2, sub t2 t -> sub t t2 ->
     sub (AndT t1 t2) t 
  | SOr1 : forall t t1 t2, sub t t2 -> sub t1 t2 -> 
     sub (OrT t t1) t2
  | SOr2 : forall t t1 t2, sub t t1 -> Atomic t ->
     sub t (OrT t1 t2)
  | SOr3 : forall t t1 t2, sub t t2 -> Atomic t ->
     sub t (OrT t1 t2)
  | SOr4 : forall t t1 t2, sub t t1 -> sub t1 t ->
     sub t (OrT t1 t2)
  | SOr5 : forall t t1 t2, sub t t2 -> sub t2 t ->
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

Hint Resolve STop SInt SFun SAnd1 SAnd2 SAnd3 SAnd4 SAnd5 SOr1 SOr2 SOr3 SOr4 SOr5
             sand2_atomic sand3_atomic sor2_atomic sor3_atomic.

Lemma inv_ands1 : forall t t1 t2, sub t (AndT t1 t2) -> sub t t1 /\ sub t t2.
Proof.
  intro t; induction t; intros.
  - inversion H. auto.
  - inversion H. auto.
  - inversion H. auto.
(* Case AndT *)
  - inversion H; auto.
    inversion H4. inversion H4.
    assert (sub t1 t0 /\ sub t1 t3). auto.
    destruct H5.
    split.
    apply SAnd4. auto. admit.
    apply SAnd4. auto. admit.
    assert (sub t2 t0 /\ sub t2 t3). auto.
    destruct H5.
    split.
    apply SAnd5. auto. admit.
    apply SAnd5. auto. admit.
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
Admitted.

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
    inversion H4. inversion H4.
    assert (sub t0 t1 /\ sub t3 t1). auto.
    destruct H5.
    split.
    apply SOr4. auto. admit.
    apply SOr4. auto. admit.
    assert (sub t0 t2 /\ sub t3 t2). auto.
    destruct H5.
    split.
    apply SOr5. auto. admit.
    apply SOr5. auto. admit.
Admitted.

Lemma sub_refl: forall A, sub A A.
Proof.
  intros.
  induction A; eauto.
Defined.

Hint Resolve sub_refl.

Definition sub_iso (A B : typ) := sub A B /\ sub B A.

Lemma iso_types : forall A B C D, sub (AndT A B) (OrT C D) -> sub_iso A (OrT C D) \/
    sub_iso B (OrT C D) \/ sub_iso C (AndT A B) \/ sub_iso D (AndT A B).
Proof.
intros.
unfold sub_iso.
dependent induction H; eauto; inversion H0.
Defined.

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
(*  | OFun1   : forall t1 t2 t3 t4, Ortho t2 t4 -> Ortho (FunT t1 t2) (FunT t3 t4) *)
(*  | OFun2  : forall t1 t2 t3 t4, Ortho t1 t3 -> Ortho (FunT t1 t2) (FunT t3 t4) *)
  | Or1 : forall t1 t2 t3, Ortho t1 t2 -> Ortho t1 (OrT t2 t3)
  | Or2 : forall t1 t2 t3, Ortho t1 t2 -> Ortho (OrT t2 t3) t1
  | Or3 : forall t1 t2 t3, Ortho t1 t3 -> Ortho t1 (OrT t2 t3)
  | Or4 : forall t1 t2 t3, Ortho t1 t3 -> Ortho (OrT t2 t3) t1.

Hint Resolve OTop1 OTop2 OAnd1 OAnd2 OIntFunT OFunTInt Or1 Or2 Or3 Or4.

Lemma applyOrthoS : forall A B, OrthoS A B -> forall C, sub A C -> sub B C ->
                      sub (AndT A B) C -> TopLike C.
Proof.
intros. destruct H with (C:=C); auto.
Defined.

Lemma sym_and1 : forall t1 t2 t3, sub (AndT t1 t2) t3 -> sub (AndT t2 t1) t3.
Proof.
intros.
dependent induction H; eauto.
inversion H0.
inversion H0.
apply SOr4.
eapply IHsub1; eauto.
apply inv_ands1 in H0.
destruct H0.
apply SAnd1.
auto. auto.
apply SOr5.
eapply IHsub1; eauto.
apply inv_ands1 in H0.
destruct H0.
apply SAnd1.
auto. auto.
Defined.

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
- dependent destruction H2. inversion H3. inversion H3.
  apply H; auto.
  apply H; auto.
  inversion H3.
  inversion H3.
  apply H; eauto.
  apply SOr4.
  apply sym_and1 in H2_. auto.
  apply inv_ands1 in H2_0.
  destruct H2_0.
  apply SAnd1; auto.
  apply H; eauto.
  apply SOr5.
  apply sym_and1 in H2_. auto.
  apply inv_ands1 in H2_0.
  destruct H2_0.
  apply SAnd1; auto.
Defined.

Lemma sym_ortho : forall t1 t2, Ortho t1 t2 -> Ortho t2 t1.
Proof.
intros.
- dependent induction H; eauto.
Qed.

Lemma inv_orthos_and: forall t1 t2 t3, OrthoS t1 (AndT t2 t3) -> OrthoS t1 t2 /\ OrthoS t1 t3.
Proof.
intros.
unfold OrthoS in H.
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
  + dependent destruction H2; eauto.
    apply H; eauto.
    apply SAnd4. auto.
    admit. admit.
    inversion H3.
    inversion H3.
    admit. admit.
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
  + 
    assert (sub t1 (OrT C1 C2) /\ sub (OrT C1 C2) t1) by admit.
    destruct H3.
    (*assert (sub t3 t1) by admit.*)
    eapply H; eauto.
    assert (TopLike (OrT t1 t3)).
    eapply H; eauto. 
    dependent destruction H2.
    inversion H3.
    inversion H3.
    admit. admit.
    inversion H3.
    inversion H3.
    admit. admit.
Admitted.

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
 - dependent destruction H2.
   inversion H3.
   inversion H3.
   apply H; eauto.
   apply H; eauto.
    inversion H3.
    inversion H3.
   apply TLOr1.
   apply IHC1; eauto. admit. admit.
Admitted.

Lemma inv_orthos_or2 : forall t1 t2 t3,
                    OrthoS t1 (OrT t2 t3) -> OrthoS t1 t2 \/ OrthoS t1 t3.
Proof.
intros.
left.
unfold OrthoS in *. intros.
dependent induction C; eauto.
apply H; eauto.
apply SOr1. auto.
admit.
apply H; eauto.
apply SOr1. auto.
admit.
apply TLAnd.
apply IHC1.
apply inv_ands1 in H0; destruct H0; auto.
apply inv_ands1 in H1; destruct H1; auto.
apply inv_ands1 in H2; destruct H2; auto.
apply IHC2.
apply inv_ands1 in H0; destruct H0; auto.
apply inv_ands1 in H1; destruct H1; auto.
apply inv_ands1 in H2; destruct H2; auto.
dependent destruction H2.
inversion H3.
inversion H3.
apply TLOr1.
apply IHC1.
Admitted.

Lemma orthos_fun : forall t1 t2 t3 t4, OrthoS (FunT t1 t2) (FunT t3 t4) -> OrthoS t2 t4.
Proof.
intros.
unfold OrthoS in H.
unfold OrthoS.
intros.
dependent induction C; auto.
assert (TopLike (FunT (AndT t1 t3) TopT)).
apply H; eauto.
inversion H3.
assert (TopLike (FunT (AndT t1 t3) TopT)).
apply H; eauto.
inversion H3.
apply TLAnd.
apply IHC1.
apply inv_ands1 in H0; destruct H0; auto.
apply inv_ands1 in H1; destruct H1; auto.
apply inv_ands1 in H2; destruct H2; auto.
apply IHC2.
apply inv_ands1 in H0; destruct H0; auto.
apply inv_ands1 in H1; destruct H1; auto.
apply inv_ands1 in H2; destruct H2; auto.
assert (TopLike (FunT (AndT t1 t3) TopT)).
apply H; eauto.
inversion H3.
Defined.

Lemma ortho_fun : forall t1 t2 t3 t4, Ortho (FunT t1 t2) (FunT t3 t4) 
                          -> False.
Proof.
intros.
inversion H.
Defined.

Lemma toplike_fun_false : forall t1 t2, TopLike (FunT t1 t2) -> False.
Proof.
intros.
inversion H.
Defined.

Lemma orthos_fun_false : forall t1 t2 t3 t4, OrthoS (FunT t1 t2) (FunT t3 t4) -> False.
Proof.
intros.
unfold OrthoS in H.
assert (TopLike (FunT (AndT t1 t3) TopT)).
apply H; eauto.
inversion H0.
Defined.

(* completeness lemma of the disjointness algorithm *)

Lemma ortho_completness : forall t1 t2, OrthoS t1 t2 -> Ortho t1 t2.
Proof.
intros t1.
induction t1; intros.
apply OTop2.
(* Case IntT *)
induction t2; intros; eauto.
unfold OrthoS in H; eauto.
assert (t0: TopLike IntT); auto. inversion t0.
apply OAnd2. apply IHt2_1.
apply inv_orthos_and in H.
destruct H; auto. 
apply inv_orthos_and in H.
destruct H; auto.
apply inv_orthos_or2 in H.
destruct H.
apply Or1.
apply IHt2_1. auto.
apply Or3.
apply IHt2_2. auto.
(* Case FunT t1 t2 *)
dependent induction t2; eauto.
(* Case FunT t1 t2 | FunT t0 t3 *)
apply orthos_fun_false in H.
contradiction.
(* Case t11 -> t12 _|_ t21 & t22 *)
apply OAnd2. apply IHt2_1.
apply inv_orthos_and in H.
destruct H; auto.
apply IHt2_2.
apply inv_orthos_and in H.
destruct H; auto.
(* Case t11 -> t12 _|_ t21 | t22 *)
apply inv_orthos_or2 in H.
destruct H.
apply Or1.
apply IHt2_1. auto.
apply Or3.
apply IHt2_2. auto.
(* Case (t11 & t12) _|_ t2 *)
apply OAnd1.
apply IHt1_1; auto.
apply sym_orthos in H.
apply inv_orthos_and in H.
apply sym_orthos.
destruct H; auto.
apply IHt1_2; auto.
apply sym_orthos in H.
apply inv_orthos_and in H.
apply sym_orthos.
destruct H; auto.
(* Case (t11 | t12) _|_ t2 *)
apply sym_orthos in H.
apply inv_orthos_or2 in H.
destruct H.
apply Or2.
apply sym_ortho.
apply IHt1_1.
apply sym_orthos. auto.
apply Or4.
apply sym_ortho.
apply IHt1_2.
apply sym_orthos. auto.
Defined.

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
   apply H; auto.
   apply H0; auto.
 - inversion H1.
   apply H; auto.
   apply H0; auto.
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
 - inversion H1.
   apply H; auto.
   apply H0; auto.
   apply H; auto.
   apply H0; auto.
   inversion H8.
   inversion H8.
   apply TLOr1.
   apply IHC0_1; eauto. admit.
   apply TLOr2.
   apply IHC0_2; eauto. admit.
Admitted.

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
 - dependent destruction H2; admit.
Admitted.

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
 - dependent destruction H2; admit.
Admitted.

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
 - dependent destruction H2; admit.
Admitted.

(* Soundness of the disjointness algorithm: Theorem 7 *)

Lemma ortho_soundness : forall (t1 t2 : typ), Ortho t1 t2 -> OrthoS t1 t2.
intros.
induction H.
(*Case t1 TopT*)
unfold OrthoS; intros.
induction C; eauto. inversion H0. inversion H0.
apply TLAnd. apply IHC1.
apply inv_ands1 in H. destruct H. auto.
apply inv_ands1 in H0. destruct H0. auto.
apply inv_ands1 in H1. destruct H1. auto.
apply IHC2.
apply inv_ands1 in H. destruct H. auto.
apply inv_ands1 in H0. destruct H0. auto.
apply inv_ands1 in H1. destruct H1. auto.
dependent destruction H1; admit.
(*Case TopT t1*)
unfold OrthoS. intros.
induction C.
apply TLTop.
inversion H. inversion H.
apply TLAnd. apply IHC1.
apply inv_ands1 in H. destruct H. auto.
apply inv_ands1 in H0. destruct H0. auto.
apply inv_ands1 in H1. destruct H1. auto.
apply IHC2.
apply inv_ands1 in H. destruct H. auto.
apply inv_ands1 in H0. destruct H0. auto.
apply inv_ands1 in H1. destruct H1. auto.
dependent destruction H1; admit.
(* Hard case: (AndT t1 t2) t3 *)
apply ortho_and.
apply IHOrtho1. auto.
apply sym_orthos.
apply ortho_and.
apply sym_orthos.
auto.
apply sym_orthos.
auto.
(* Case IntFunT *)
unfold OrthoS.
induction C; intros. apply TLTop. inversion H0. inversion H.
apply TLAnd. apply IHC1. inversion H. auto. inversion H0. auto.
apply inv_ands1 in H1. destruct H1. auto.
apply IHC2. inversion H. auto. inversion H0. auto.
apply inv_ands1 in H1. destruct H1. auto.
dependent destruction H1; admit.
(* Case FunTInt *)
unfold OrthoS.
induction C; intros. apply TLTop. inversion H. inversion H0.
apply TLAnd.
apply IHC1. inversion H. auto. inversion H0. auto.
apply inv_ands1 in H1. destruct H1. auto.
apply IHC2. inversion H. auto. inversion H0. auto.
apply inv_ands1 in H1. destruct H1. auto.
dependent destruction H1.
inversion H2.
inversion H2. admit. admit. admit. admit. admit. admit.
(* FunTFunT *)
(*unfold OrthoS.
intros.
induction C. apply TLTop. inversion H2.
assert (Ortho (FunT t1 t2) (FunT t3 t4)).
apply OFun1. auto.
eapply applyOrtho with (A:=(FunT t1 t2)) (B:=(FunT t3 t4)); eauto.
apply TLAnd. apply IHC1. inversion H2. auto. inversion H3. auto.
apply inv_ands1 in H4. destruct H4. auto.
apply IHC2. inversion H2. auto. inversion H3. auto.
apply inv_ands1 in H4. destruct H4. auto.
dependent destruction H4; inversion H5.*)
(* Case OrT *)
apply sym_orthos.
apply orthos_or1.
apply sym_orthos.
auto.
apply orthos_or1.
apply sym_orthos.
auto.
apply sym_orthos.
apply orthos_or2.
apply sym_orthos.
auto.
apply orthos_or2.
apply sym_orthos.
auto.
Admitted.