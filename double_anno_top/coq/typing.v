Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import rules.
Require Import String.
Require Import Coq.Program.Equality.

(* ------- inversion lemmas for subtyping ------- *)
(*Lemma top_not_int : t_top <> t_int.
Proof. introv H. inversion H. Qed.

Lemma top_not_arrow : forall A B,
  t_top <> t_arrow A B.
Proof. introv H. inversion H. Qed.

Lemma sub_int : forall A,
  A <: t_int -> A = t_int.
Proof.
  introv H. remember (t_int) as B.
  gen HeqB. induction H; intros Heq.
  - reflexivity.
  - lets HT : Heq. apply IHsubtype2 in Heq.
    subst T. auto.
  - inversion Heq.
  - inversion Heq.
Qed.

Lemma sub_arrow : forall U A B,
  U <: t_arrow A B ->
  exists A' B', U = t_arrow A' B' /\ A <: A' /\ B' <: B.
Proof.
  introv H. remember (t_arrow A B) as T.
  gen HeqT. gen A B. induction H; introv Heq.
  - eauto.
  - apply IHsubtype2 in Heq as [A' [B' [HU [HU1 HU2]]]].
    apply IHsubtype1 in HU as [A'' [B'' [HS [HS1 HS2]]]].
    exists* A'' B''.
  - inversion Heq.
  - inverts* Heq.
Qed.

Lemma sup_top : forall T,
  t_top <: T -> T = t_top.
Proof with auto.
  introv H. remember t_top as U.
  induction H...
  - destruct* IHsubtype1.
  - inversion HeqU.
Qed.

Lemma sup_int : forall A,
  t_int <: A -> A = t_top \/ A = t_int.
Proof.
  induction A; auto.
  - intros H. apply sub_arrow in H
      as [A [B [Heq [HA HB]]]]. inversion Heq.
Qed.

Lemma sup_arrow : forall A B C,
  t_arrow A B <: C ->
  C = t_top \/ (exists A' B', C = t_arrow A' B' /\
    A' <: A /\ B <: B').
Proof.
  induction C; intros Heq; auto.
  - apply sub_int in Heq. inversion Heq.
  - apply sub_arrow in Heq
      as [A' [B' [H [H1 H2]]]]. inverts* H.
Qed.*)

(* ------- subtyping for lemmas inversion ------- *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  constr:(A `union` B `union` C `union` D).

(*Notation "[ z ~> u ] e" := (subst_exp z u e) (at level 68).
Notation "{ k ~> u } t" := (open_rec k u t) (at level 67). 

Lemma open_rec_lc_core : forall e j v i u,
  i <> j ->
  {j ~> v} e = {i ~> u} ({j ~> v} e) ->
  e = {i ~> u} e.
Proof.
  induction e; intros j v i u Neq H;
    simpl in *; try apply H;
    try (f_equal; inversion H; eauto).
  - (* e_var_b *)
    destruct (j == n) eqn:Ej;
      destruct (i == n) eqn:Ei.
    + subst n. destruct Neq. assumption.
    + reflexivity.
    + simpl in *.
      destruct (i == n).
      apply H.
      destruct n1. auto.
    + reflexivity.
Qed.

Lemma open_rec_lc_c : forall k u e,
  lc_exp e ->
  e = {k ~> u} e.
Proof.
  intros k u e H.
  generalize dependent k.
  induction H; simpl; try reflexivity;
    intros k.
  - (* e_ann *)
    f_equal. auto.
  - (* e_abs *)
    f_equal. pick fresh x.
    apply open_rec_lc_core
      with (j:=0) (v:=x); eauto.
  - (* e_app *)
    f_equal; auto.
Qed.

Lemma subst_open_rec_c : forall e1 e2 u (x : atom) k,
  lc_exp u ->
  [x ~> u] ({k ~> e2} e1) = {k ~> [x ~> u] e2} ([x ~> u] e1).
Proof.
  induction e1;
    intros e2 u y k H; simpl in *;
    try (f_equal; auto).
  - (* e_var_b *)
    destruct (k == n); auto.
  - (* e_var_f *)
    destruct (x == y);
      apply open_rec_lc_c; auto.
Qed.

Lemma subst_open_var_c : forall (x y : atom) u e,
  y <> x ->
  lc_exp u ->
  open ([x ~> u] e) y = [x ~> u] (open e y).
Proof.
  intros x y e u neq H.
  unfold open.
  rewrite subst_open_rec_c.
  simpl. destruct (y == x). destruct neq. apply e0.
  reflexivity.
  apply H.
Qed.

Lemma subst_intro : forall (x : atom) u e,
  x `notin` (fv_exp e) ->
  open e u = [x ~> u] (open e x).
Proof.
  intros x u e H.
  unfold open.
  generalize 0.
  induction e; intros n0; simpl in *;
    try (f_equal; auto).
  - (* e_var_b *)
    destruct (n0 == n).
    + simpl. destruct (x == x).
      reflexivity. destruct n1. reflexivity.
    + simpl. reflexivity.
  - destruct (x0 == x).
    subst. fsetdec. 
    reflexivity.
Qed.

Lemma subst_lc_c : forall (x : atom) u e,
  lc_exp e ->
  lc_exp u ->
  lc_exp ([x ~> u] e).
Proof.
  intros x u e le lu.
  induction le; simpl; auto.
  - (* lc_var_f *)
    destruct (x0 == x); auto.
  - (* lc_abs *)
    pick fresh y and apply lc_abs.
    rewrite subst_open_var_c; auto.
Qed.*)

Lemma typing_weakening_strengthen : forall (E F G : ctx) e dir T,
  typing (G ++ E) e dir T ->
  uniq (G ++ F ++ E) ->
  typing (G ++ F ++ E) e dir T.
Proof.
  intros E F G e dir T H.
  remember ( G ++ E ) as E'.
  generalize dependent G.
  dependent induction H;
    intros G1 Eq Uniq; subst; eauto.
  - Case "typ_abs".
    pick fresh x and apply typ_abs.
    rewrite_env (((x ~ A) ++ G1) ++ F ++ E).
    admit.
  - Case "typ_typeof".
    eapply typ_typeof; eauto.
Admitted.

Lemma notin_fv_open : forall (x y : atom) e,
  x `notin` fv_exp (open e y) ->
  x `notin` fv_exp e.
Proof.
   intros x y e. unfold open.
   generalize 0.
   induction e; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_open_neq : forall (x x' : atom) e,
  x `notin` fv_exp e ->
  x <> x' ->
  x `notin` fv_exp (open e x').
Proof.
  intros x y e. unfold open.
  generalize 0.
  induction e; simpl; intros k Fr; eauto.
  - destruct (k == n); eauto.
Qed.

Lemma typing_weakening : forall (E F : ctx) e dir T,
    typing E e dir T ->
    uniq (F ++ E) ->
    typing (F ++ E) e dir T.
Proof.
   intros.
   rewrite_env (nil ++ F ++ E).
   apply typing_weakening_strengthen.
   apply H. auto.
Qed.

Lemma typing_subst_var_case : forall (E F : ctx) u S T (z x : atom),
  binds x T (F ++ [(z,S)] ++ E) ->
  uniq (F ++ [(z,S)] ++ E) ->
  typing E u Inf S ->
  typing (F ++ E) ([z ~> u] x) Inf T.
Proof.
  intros E F u S T z x H J K.
  simpl. destruct (x == z).
  - Case "x = z".
    subst. assert (T = S).
    { eapply binds_mid_eq. apply H. apply J. }
    subst. apply typing_weakening.
    + apply K.
    + eapply uniq_remove_mid. apply J.
  - Case "x <> z".
    apply typ_var.
    eapply uniq_remove_mid. apply J.
    eapply binds_remove_mid. apply H. apply n.
Qed.

Lemma value_c_to_lc_c : forall e,
  value e -> lc_exp e.
Proof.
  intros e H. induction H; inverts H; eauto.
Qed.

Lemma typing_c_to_lc_c : forall E e dir T,
  typing E e dir T -> lc_exp e.
Proof.
  intros E e dir T H.
  induction H; eauto.
Qed.

Hint Resolve typing_c_to_lc_c : core.

Lemma typing_uniq : forall E e  dir T,
  typing E e dir T -> uniq E.
Proof.
  intros E e dir T H.
  induction H; auto.
  - pick fresh x.
    assert (uniq ((x ~ A)++ E)); auto.
    solve_uniq.
Qed.

Hint Resolve typing_uniq : core.

Lemma typing_c_subst : forall (E F : ctx) e u S dir T (z : atom),
  typing (F ++ (z ~ S) ++ E) e dir T ->
  typing E u Inf S ->
  typing (F ++ E) ([z ~> u] e) dir T.
Proof with auto.
  intros E F e u S dir T z H1 H2.
  remember (F ++ (z ~ S) ++ E) as E'.
  generalize dependent F.
  induction H1; intros F Heq;
    simpl; subst; eauto.
  - (* typ_var *)
    eapply typing_subst_var_case; eauto.
  - (* typ_abs *)
    pick fresh x and apply typ_abs.
    assert (Hex: e_abs ([z ~> u] e) = [z ~> u] (e_abs e))...
    rewrite Hex. apply typing_c_to_lc_c in H2.
    apply subst_lc_c...
    rewrite subst_open_var_c.
    rewrite_env (((x ~ A) ++ F) ++ E).
    auto. fsetdec.
    eapply typing_c_to_lc_c. apply H2.
  - (* typ_abs_top *)
    apply typ_abs_top. eauto.
    apply typing_c_to_lc_c in H2.
    assert (Hex: e_abs ([z ~> u] e)
        = [z ~> u] (e_abs e)). { auto. }
      rewrite Hex. apply* subst_lc_c.
Qed.

Lemma typing_c_subst_simple : forall (E : ctx)
  e u S dir T (z : atom),
  typing ((z ~ S) ++ E) e dir T ->
  typing E u Inf S ->
  typing E ([z ~> u] e) dir T.
Proof.
  intros E e u S dir T z H1 H2.
  rewrite_env (nil ++ E).
  eapply typing_c_subst.
    simpl_env. apply H1.
    apply H2.
Qed.

Lemma typing_notint : forall E F e x S T dir,
  typing (F ++ [(x, S)] ++ E) e dir T ->
  x `notin` fv_exp e ->
  typing (F ++ E) e dir T.
Proof.
  introv Htyp. remember (F ++ (x ~ S) ++ E) as G.
  gen HeqG. gen E F x S. induction Htyp; introv HE Hnotin;
    subst; simpl in Hnotin; eauto.
  - apply typ_var. solve_uniq.
    apply binds_app_1 in H0 as [HF | HxE]; auto.
    apply binds_app_1 in HxE as [Hx | HE]; auto.
    inversion Hx; inverts H0. solve_notin.
  - apply typ_abs with (L `union` singleton x); auto.
    introv HLx. assert (HL: x0 `notin` L) by auto.
    apply H1 with (E:=E0) (F0:=(x0~A) ++ F) (x1:=x) (S0:=S)
      in HL; auto. destruct_notin.
    apply notin_fv_open_neq; auto.
Qed.

Lemma lc_inversion_ann : forall e A,
  lc_exp (e_ann e A) -> lc_exp e.
Proof.
  introv H. inverts H. auto.
Qed.

Hint Resolve lc_inversion_ann : core.

Lemma inf_not_abs : forall e A,
  typing nil e Inf A -> ~ (exists e', e = e_abs e').
Proof.
  introv H [e' Heq]. subst. inversion H.
Qed.

Lemma lit_not_arrow : forall E i5 A B dir,
  ~ (typing E (e_lit i5) dir (t_arrow A B)).
Proof.
  introv H. inverts H. inverts H1.
  apply sub_arrow in H2 as [A' [B' [Hc [_ _]]]].
  inversion Hc.
Qed.

Theorem progress_strengthen : forall e T dir,
    typing nil e dir T ->
    ~ (exists e', e = e_abs e' /\ dir = Chk) ->
    value e \/ (exists e', step e e').
Proof with eauto 6.
  introv Htyp. remember nil as E. 
  gen HeqE. induction Htyp;
    intros HE Hextra; subst...
  - (* typ_var *)
    inversion H0.
  - (* typ_ann *)
    clear Hextra. lets Hlc : Htyp.
    apply typing_c_to_lc_c in Hlc.
    inverts Htyp... lets Hnabs : H0.
    apply inf_not_abs in Hnabs.
    lets [Val | [e' Red]] : IHHtyp. reflexivity.
    intros [e' [Habs _]]. destruct Hnabs...
    + inverts Val...
    + inverts Red; inverts Hlc...
  - (* typ_app *)
    clear Hextra. lets [Val1 | [e1' Red1]] : IHHtyp1;
    clear IHHtyp1... intros [_ [_ Hdir]]. inversion Hdir.
    inverts Htyp2.
    + (* typ_chk *)
      apply inf_not_abs in H0 as Hnabs.
      lets [Val | [e' Red]] : IHHtyp2; clear IHHtyp2...
      intros [e' [Habs _]]. destruct Hnabs...
      * (* e2 is value *)
        inverts Val...
      * (* e2 can step *)
        inverts* Red. inverts Val1. inverts Htyp1.
        inverts* H3. exfalso. eapply lit_not_arrow...
    + (* typ_abs *)
      inverts Val1. inverts Htyp1. inverts* H1.
      exfalso. eapply lit_not_arrow...
    + (* typ_abs_top *)
      inverts Val1. inverts Htyp1. inverts* H1.
      exfalso. eapply lit_not_arrow...
  - (* typ_chk *)
    lets [Val | [e' Red]] : IHHtyp. reflexivity.
    intros [_ [_ Hdir]]. inversion Hdir.
    auto. eauto.
  - (* typ_abs *)
    destruct Hextra...
  - (* typ_abs_top *)
    destruct Hextra...
Qed.

Theorem progress : forall e T,
    typing nil e Inf T ->
    value e \/ (exists e', step e e').
Proof.
  introv H. eapply progress_strengthen. apply H.
  introv Hc. destruct Hc as [_ [_ Hdir]]. inversion Hdir.
Qed.

Lemma subenv_dom : forall E F,
  E <:: F -> dom E = dom F.
Proof.
  introv H. induction H.
  - reflexivity.
  - simpl. rewrite IHsubenv. reflexivity.
Qed.

Lemma subenv_uniq : forall E F,
  E <:: F -> uniq E <-> uniq F.
Proof.
  introv H. induction H.
  - split; auto.
  - split; intros Hxuniq; apply subenv_dom in H0;
    apply uniq_cons_iff in Hxuniq as [HEu HEd];
    apply uniq_cons_iff; apply IHsubenv in HEu.
    + rewrite <- H0. auto.
    + rewrite H0. auto.
Qed.

Lemma subenv_binds : forall E F x T,
  E <:: F ->
  binds x T F ->
  exists S, S <: T /\ binds x S E.
Proof.
  introv H. gen x T. induction H; introv Hb.
  - exists T. auto.
  - analyze_binds Hb.
    + exists S. auto.
    + apply IHsubenv in BindsTac as [R [HRsub HRb]].
      exists R. auto.
Qed.

Lemma typing_aux : forall E E' e T dir,
  typing E e dir T ->
  E' <:: E ->
  ((dir = Chk) /\ forall U, T <: U -> typing E' e Chk U) \/
  ((dir = Inf) /\ exists S, S <: T /\ typing E' e Inf S).
Proof with auto.
  introv Htyp. gen E'. lets Htyp' : Htyp.
  induction Htyp; introv HEsub.
  - (* typ_lit *)
    right. split~. exists t_int.
    rewrite <- (subenv_uniq _ _ HEsub) in H. split~.
  - (* typ_var *)
    right. split~. rewrite <- (subenv_uniq _ _ HEsub) in H.
    apply (subenv_binds E' E x A) in HEsub...
    destruct HEsub as [S [HSsub HSb]]. exists~ S.
  - (* typ_ann *)
    right. split~. exists A. split~. apply typ_ann.
    apply IHHtyp in HEsub as [[Hdir H] | [Hdir H]]... inverts Hdir.
  - (* typ_app *)
    right. split~. lets HEsub2 : HEsub.
    apply IHHtyp1 in HEsub as [[Hdir H1] | [Hdir H1]];
    try inverts Hdir... apply IHHtyp2 in HEsub2 as [[Hdir H2]
      | [Hdir H2]]; try inverts Hdir... clear IHHtyp1 IHHtyp2.
    destruct H1 as [S [HSsub HStyp]]. apply sub_arrow in
      HSsub as [Ar [Br [Hr [Har Hbr]]]]. subst S. eauto.
  - (* typ_chk *)
    left. split~. rewrite <- (subenv_uniq _ _ HEsub) in H.
    apply IHHtyp in HEsub as [[Hdir He] | [Hdir He]];
    try inverts Hdir...
    destruct He as [S [HSsub HStyp]]. eauto.
  - (* tpy_abs *)
    left. split~. apply typing_uniq in Htyp'.
    rewrite <- (subenv_uniq _ _ HEsub) in Htyp'.
    introv HU. apply sup_arrow in HU as [HU | [A' [B' [HU [HA'
      HB']]]]]; subst~. apply typ_abs with L... introv HL.
    apply H1 with x ((x ~ A') ++ E') in HL as
      [[Hdir Ho] | [Hdir Ho]]; try inverts Hdir...
  - (* typ_abs_top *)
    left. split~. apply typing_uniq in Htyp'.
    rewrite <- (subenv_uniq _ _ HEsub) in Htyp'. introv HU.
    apply sup_top in HU. subst~.
Qed.

Corollary typing_chk : forall E e T dir,
  typing E e dir T ->
  forall U, T <: U -> typing E e Chk U.
Proof.
  introv Htyp.
  eapply typing_aux in Htyp.
  destruct Htyp as [[_ Hchk] | [_ [S [HS Hinf]]]];
    eauto. auto.
Qed.

Corollary typing_inf : forall E e T dir,
  typing E e dir T ->
  ~ (exists e', e = e_abs e') ->
  exists S, S <: T /\ typing E e Inf S.
Proof.
  introv Htyp Hnabs.
  eapply typing_aux in Htyp; auto.
  destruct Htyp as [[_ Hchk] | [_ [S [HS Hinf]]]].
  - (* Chk *)
    assert (T <: T) by auto. apply Hchk in H.
    inverts* H; destruct Hnabs; eauto.
  - (* Inf *)
    eauto.
Qed.

Corollary typing_narrowing : forall E E' e T dir,
  typing E e dir T ->
  E' <:: E ->
  typing E' e Chk T.
Proof.
  introv Htyp Hsub.
  eapply typing_aux in Htyp.
  destruct Htyp as [[_ Hchk] | [_ [S [HS Hinf]]]];
    eauto. auto.
Qed.

Lemma open_chk_open_e : forall L e e' A B,
  (forall x, x `notin` L ->
    typing ((x ~ A) ++ nil) (open e x) Chk B) ->
  typing nil e' Chk A ->
  typing nil (open e (e_ann e' A)) Chk B.
Proof.
  introv H Hchk.
  pick fresh x. rewrite subst_intro with x _ _.
  rewrite_env (@nil (atom * typ) ++ nil).
  apply typing_c_subst with A.
  assert (x `notin` L) as Hx. fsetdec.
  apply H in Hx. apply Hx. auto. fsetdec.
Qed.

Theorem preservation : forall e e' T dir,
  typing nil e dir T ->
  step e e' ->
  typing nil e' dir T.
Proof with eauto.
  introv HT. gen e'.
  remember nil as E. gen HeqE.
  induction HT; introv HE J;
    try solve [inverts* J]; subst E.
  - (* typ_ann *)
    inverts J.
    + (* step_ann_ann *)
      inverts HT. inverts H0. eapply typing_chk in H4...
    + (* step_ann_app *)
      eauto.
  - (* typ_app *)
    inverts* J.
    + (* step_beta *)
      inverts HT1. apply typ_ann. inverts H5. inverts H0.
      apply open_chk_open_e with L; assumption.
    + (* step_appr_ann *)
      inverts HT2. inverts H0. eapply typing_chk in H6...
Qed.

Ltac solve_by_inverts_step :=
  auto;
  match goal with
  | Hstp : step (e_ann (e_abs ?e) ?T) ?E |- _ =>
      solve [inverts Hstp]
  | Hstp : step ?e ?e',
    Hv : value ?e |- _ => solve [inverts Hv; inverts Hstp;
      solve_by_inverts_step]
  | Hpv : pvalue (e_ann ?e ?T) |- _ => solve [inverts Hpv]
  | Hpv : pvalue (e_app ?e1 ?e2) |- _ => solve [inverts Hpv]
  end.

Theorem determinism : forall e e1 e2,
  step e e1 ->
  step e e2 ->
  e1 = e2.
Proof.
  introv He1. gen e2.
  induction He1; introv He2;
    inverts He2; try solve_by_inverts_step;
    f_equal; auto.
Qed.