(*
This file contains the updates suggested by Snow.
Mod of syntax_bruno_btmlike
Try to eliminate the dependency of disjointness and bottomlike
A * B ::= bot-like A&B

and try to capture disjointness on functions with the help of distributivity
*)

Require Import TLC.LibLN.
Require Import Program.Equality.
(*Require Import LibTactics.*)
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
     ord (t_arrow A B)
 | SO_or : forall (A B:typ),
     ord A ->
     ord B ->
     ord (t_or A B).

Inductive ordu : typ -> Prop :=    (* defn ordu *)
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
 | Spl_and : forall (A B:typ),
     spl (t_and A B) A B
 | Spl_orl : forall (A B A1 A2:typ),
     spl A A1 A2 ->
     spl (t_or A B) (t_or A1 B) (t_or A2 B)
 | Spl_orr : forall (A B B1 B2:typ),
     ord A ->
     spl B B1 B2 ->
     spl (t_or A B) (t_or A B1) (t_or A B2).

Inductive splu : typ -> typ -> typ -> Prop :=    (* defn splu *)
 | SpU_or : forall (A B:typ),
     splu (t_or A B) A B
 | SpU_andl : forall (A B A1 A2:typ),
     splu A A1 A2 ->
     splu (t_and A B) (t_and A1 B) (t_and A2 B)
 | SpU_andr : forall (A B B1 B2:typ),
     ordu A ->
     splu B B1 B2 ->
     splu (t_and A B) (t_and A B1) (t_and A B2).

(****************************************)
(**********  Disjoint Axioms  ***********)
(****************************************)
Inductive disjoint : typ -> typ -> Prop :=
| D_intArr : disjoint t_int (t_arrow t_bot t_top).


(****************************************)
(*************  Subtyping ***************)
(****************************************)
Reserved Notation "A <: B" (at level 80).
Inductive subtyping : typ -> typ -> Prop :=    (* defn subtyping *)
 | S_top : forall A, A <: t_top
 | S_btm : forall A, t_bot <: A
 | S_int : t_int <: t_int
 | S_arrow : forall (A1 A2 B1 B2:typ),
     B1 <: A1 ->
     A2 <: B2 ->
     (t_arrow A1 A2) <: (t_arrow B1 B2)
 | S_or : forall (A A1 A2 B:typ),
     splu A A1 A2 ->  
     A1 <: B ->
     A2 <: B ->
     A <: B
 | S_orl : forall (A B B1 B2:typ),
     splu B B1 B2 -> 
     A <: B1 ->
     A <: B
 | S_orr : forall (A B B1 B2:typ),
     splu B B1 B2 -> 
     A <: B2 ->
     A <: B
 | S_and : forall (A B B1 B2:typ),
     spl B B1 B2 ->  
     A <: B1 ->
     A <: B2 ->
     A <: B
 | S_andl : forall (A A1 A2 B:typ),
     spl A A1 A2 ->   
     A1 <: B ->
     A <: B
 | S_andr : forall (A A1 A2 B:typ),
     spl A A1 A2 ->   
     A2 <: B ->
     A <: B
 | S_disjoint : forall A B1 B2 C,
     disjoint B1 B2 ->
     A <: t_and B1 B2 ->
     A <: C
where "A <: B" := (subtyping A B) : env_scope.

Hint Constructors spl splu subtyping : core.

Theorem refl : forall A,
    A <: A.
Proof.
  intros; induction A; eauto.
Qed.

Lemma sub_or : forall A B C, (t_or A B) <: C -> A <: C /\ B <: C.
Proof.
  intros. inductions H; eauto.
  admit. admit. admit. admit. admit. admit. admit.
Admitted.

Lemma sub_and : forall A B C, A <: (t_and B C) -> A <: B /\ A <: C.
Proof.
intros; inductions H; try solve [split*].
specialize (IHsubtyping1 B C).
specialize (IHsubtyping2 B C).
forwards*: IHsubtyping1.
admit.
admit.
admit.
specialize (IHsubtyping B C).
forwards*: IHsubtyping.
specialize (IHsubtyping B C).
forwards*: IHsubtyping.
Admitted.

Theorem trans : forall B A C,
    A <: B -> B <: C -> A <: C.
Proof.
intros B A C H. gen C.
dependent induction H; intros; eauto.
- dependent induction H; eauto.
  inversion H. inversion H. inversion H.
- dependent induction H1; eauto.
  apply S_arrow; auto. admit.
  inversion H1. inversion H2. inversion H2.
- dependent induction H1; eauto.
  inversion H. inversion H.
  admit.
  admit.
  admit.
- apply IHsubtyping.
Admitted.

Theorem trans1 : forall B A C,
    A <: B -> B <: C -> A <: C.
Proof.
  inductions B; intros;
  generalize H0 H; clear H0; clear H; generalize A; clear A.
  - intros. inductions H0; eauto.
    inversion H. inversion H. inversion H.
  - intros. inductions H; eauto.
    inversion H. inversion H. inversion H.
  - intros. inductions H; eauto.
    inversion H. inversion H. inversion H.
  - induction C; intros. inverts* H0. 
    inversion H0; subst; try solve[inversion H1]. 
    apply S_disjoint with (C:=t_bot) in H2; auto.
    inversion H2; subst; try solve [inversion H3].
    admit.
    inverts* H0; try solve [inversion H1].
    admit.
    induction A; eauto.
    inverts* H; try solve [inversion H1].
    inverts* H; try solve [inversion H1].
    inverts* H; try solve [inversion H1].
    inverts* H0; try solve [inversion H].
    admit. admit. admit. admit. admit.
  - intros. apply sub_or in H0. destruct H0.
    inductions H; eauto. inverts* H. inverts* H.
    inverts keep H.
    apply IHB1; auto.
    admit. admit.
  - intros. apply sub_and in H. destruct H.
    inductions H0; eauto. inverts* H.
    eapply IHsubtyping1; eauto.
Admitted.

Theorem arrow : forall A B C D,
    C <: A -> B <: D -> (t_arrow A B) <: (t_arrow C D).
Admitted.

Hint Resolve refl arrow : core.
Hint Immediate trans : core.



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
(****  Bottom-Like Properties  ****)
(**********************************)

Example two_arrows : forall A1 A2 A3,
    (t_arrow t_int t_int) *s (t_arrow A1 (t_arrow A2 A3)).
Proof.
  intros. repeat unfolds.
  applys trans (t_arrow t_bot t_bot).
  applys trans (t_and (t_arrow t_bot t_int) (t_arrow t_bot (t_arrow A2 A3))).
  applys* S_and.
  applys trans (t_arrow t_bot (t_and t_int (t_arrow A2 A3))).
  applys S_and. applys* Spl_arrow.
  applys* S_andl. 
  applys* S_andr.
  applys~ arrow.
  applys S_disjoint. constructor.
  applys* S_and.
  (* need  bot -> bot <: bot *)
Abort.


(*************************************)
(*****  Disjointness Properties  *****)
(*************************************)



(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)


(*************************)
(***** Ordinary Types ****)
(*************************)
