From Coq Require Import Lists.List.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Program.Equality.

Import ListNotations.

Set Implicit Arguments.

Module ReflectiveComputationM42.

Inductive Term : Type :=
| TVar : nat -> Term
| TUsr : nat -> list Term -> Term
| TEquiv : Term -> Term -> Term
| TRewrite : Term -> Term -> Term
| TTuple : list Term -> Term.

Fixpoint term_eq_dec (s t : Term) : {s = t} + {s <> t}.
Proof.
  decide equality;
    try apply Nat.eq_dec;
    try (apply list_eq_dec; exact term_eq_dec).
Defined.

Inductive FV : nat -> Term -> Prop :=
| fv_var : forall x, FV x (TVar x)
| fv_usr : forall x f args t, In t args -> FV x t -> FV x (TUsr f args)
| fv_equiv_l : forall x s t, FV x s -> FV x (TEquiv s t)
| fv_equiv_r : forall x s t, FV x t -> FV x (TEquiv s t)
| fv_rewrite_l : forall x l r, FV x l -> FV x (TRewrite l r)
| fv_rewrite_r : forall x l r, FV x r -> FV x (TRewrite l r)
| fv_tuple : forall x args t, In t args -> FV x t -> FV x (TTuple args).

Definition Ground (t : Term) : Prop := forall x, ~ FV x t.

Inductive SubstRel (sigma : nat -> option Term) : Term -> Term -> Prop :=
| sub_var_hit :
    forall x g, sigma x = Some g -> Ground g -> SubstRel sigma (TVar x) g
| sub_var_miss :
    forall x, sigma x = None -> SubstRel sigma (TVar x) (TVar x)
| sub_usr :
    forall f args args',
      Forall2 (SubstRel sigma) args args' ->
      SubstRel sigma (TUsr f args) (TUsr f args')
| sub_equiv :
    forall s s' t t',
      SubstRel sigma s s' ->
      SubstRel sigma t t' ->
      SubstRel sigma (TEquiv s t) (TEquiv s' t')
| sub_rewrite :
    forall l l' r r',
      SubstRel sigma l l' ->
      SubstRel sigma r r' ->
      SubstRel sigma (TRewrite l r) (TRewrite l' r')
| sub_tuple :
    forall args args',
      Forall2 (SubstRel sigma) args args' ->
      SubstRel sigma (TTuple args) (TTuple args')
| sub_ground_none :
    forall t,
      Ground t ->
      (forall x, sigma x = None) ->
      SubstRel sigma t t.

Definition alpha_equiv (s t : Term) : Prop := s = t.

Inductive TermArityOK (usr_arity : nat -> nat) : Term -> Prop :=
| arity_var :
    forall x, TermArityOK usr_arity (TVar x)
| arity_usr :
    forall f args,
      length args = usr_arity f ->
      TermsArityOK usr_arity args ->
      TermArityOK usr_arity (TUsr f args)
| arity_equiv :
    forall s t,
      TermArityOK usr_arity s ->
      TermArityOK usr_arity t ->
      TermArityOK usr_arity (TEquiv s t)
| arity_rewrite :
    forall l r,
      TermArityOK usr_arity l ->
      TermArityOK usr_arity r ->
      TermArityOK usr_arity (TRewrite l r)
| arity_tuple :
    forall args,
      TermsArityOK usr_arity args ->
      TermArityOK usr_arity (TTuple args)
with TermsArityOK (usr_arity : nat -> nat) : list Term -> Prop :=
| arity_nil :
    TermsArityOK usr_arity []
| arity_cons :
    forall t rest,
      TermArityOK usr_arity t ->
      TermsArityOK usr_arity rest ->
      TermsArityOK usr_arity (t :: rest).

Inductive Prefix : list nat -> list nat -> Prop :=
| prefix_nil : forall p, Prefix [] p
| prefix_cons : forall i p q, Prefix p q -> Prefix (i :: p) (i :: q).

Inductive SubAt : Term -> list nat -> Term -> Prop :=
| sub_here : forall t, SubAt t [] t
| sub_usr_child :
    forall f args i child p u,
      nth_error args i = Some child ->
      SubAt child p u ->
      SubAt (TUsr f args) (i :: p) u
| sub_equiv_l :
    forall s t p u, SubAt s p u -> SubAt (TEquiv s t) (0 :: p) u
| sub_equiv_r :
    forall s t p u, SubAt t p u -> SubAt (TEquiv s t) (1 :: p) u
| sub_rewrite_l :
    forall l r p u, SubAt l p u -> SubAt (TRewrite l r) (0 :: p) u
| sub_rewrite_r :
    forall l r p u, SubAt r p u -> SubAt (TRewrite l r) (1 :: p) u
| sub_tuple_child :
    forall args i child p u,
      nth_error args i = Some child ->
      SubAt child p u ->
      SubAt (TTuple args) (i :: p) u.

Inductive ReplaceAt : Term -> list nat -> Term -> Term -> Prop :=
| replace_here : forall t s, ReplaceAt t [] s s
| replace_usr_child :
    forall f args args' i child child' p s,
      nth_error args i = Some child ->
      ReplaceAt child p s child' ->
      replace_nth args i child' (Some args') ->
      ReplaceAt (TUsr f args) (i :: p) s (TUsr f args')
| replace_equiv_l :
    forall a b p s a', ReplaceAt a p s a' -> ReplaceAt (TEquiv a b) (0 :: p) s (TEquiv a' b)
| replace_equiv_r :
    forall a b p s b', ReplaceAt b p s b' -> ReplaceAt (TEquiv a b) (1 :: p) s (TEquiv a b')
| replace_rewrite_l :
    forall l r p s l', ReplaceAt l p s l' -> ReplaceAt (TRewrite l r) (0 :: p) s (TRewrite l' r)
| replace_rewrite_r :
    forall l r p s r', ReplaceAt r p s r' -> ReplaceAt (TRewrite l r) (1 :: p) s (TRewrite l r')
| replace_tuple_child :
    forall args args' i child child' p s,
      nth_error args i = Some child ->
      ReplaceAt child p s child' ->
      replace_nth args i child' (Some args') ->
      ReplaceAt (TTuple args) (i :: p) s (TTuple args')
with replace_nth : list Term -> nat -> Term -> option (list Term) -> Prop :=
| replace_nth_here :
    forall old rest new, replace_nth (old :: rest) 0 new (Some (new :: rest))
| replace_nth_next :
    forall old rest i new rest',
      replace_nth rest i new (Some rest') ->
      replace_nth (old :: rest) (S i) new (Some (old :: rest'))
| replace_nth_fail :
    forall i new, replace_nth [] i new None.

Scheme ReplaceAt_ind' := Induction for ReplaceAt Sort Prop
with replace_nth_ind' := Induction for replace_nth Sort Prop.

Definition Subterm (T u : Term) : Prop := exists p, SubAt T p u.
Definition GroundSub (T u : Term) : Prop := Subterm T u /\ Ground u.

Definition FV_subset (r l : Term) : Prop :=
  forall x, FV x r -> FV x l.

Definition variable_scope_ok (T : Term) : Prop :=
  forall x p,
    SubAt T p (TVar x) ->
    exists q j l r,
      (j = 0 \/ j = 1) /\
      Prefix (q ++ [j]) p /\
      SubAt T q (TRewrite l r).

Definition rules_safe (T : Term) : Prop :=
  forall q l r, SubAt T q (TRewrite l r) -> FV_subset r l.

Record Spec (T : Term) : Prop := {
  spec_scope : variable_scope_ok T;
  spec_rules_safe : rules_safe T
}.

Lemma nth_error_in_term :
  forall (args : list Term) i child, nth_error args i = Some child -> In child args.
Proof.
  induction args as [|a args IH]; intros [|i] child H; simpl in H.
  - discriminate.
  - discriminate.
  - inversion H; subst; left; reflexivity.
  - right; exact (IH i child H).
Qed.

Lemma in_term_nth_error :
  forall (args : list Term) t, In t args -> exists i, nth_error args i = Some t.
Proof.
  induction args as [|a args IH]; intros t Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Ht | Hin].
    + subst t. exists 0. reflexivity.
    + destruct (IH t Hin) as [i Hi].
      exists (S i). exact Hi.
Qed.

Lemma subat_fv_lift :
  forall T p u x, SubAt T p u -> FV x u -> FV x T.
Proof.
  intros T p u x Hsub.
  induction Hsub; intros Hfv.
  - exact Hfv.
  - eapply fv_usr.
    + exact (@nth_error_in_term args i child H).
    + exact (IHHsub Hfv).
  - eapply fv_equiv_l; eauto.
  - eapply fv_equiv_r; eauto.
  - eapply fv_rewrite_l; eauto.
  - eapply fv_rewrite_r; eauto.
  - eapply fv_tuple.
    + exact (@nth_error_in_term args i child H).
    + exact (IHHsub Hfv).
Qed.

Lemma subat_append :
  forall T p u q v,
    SubAt T p u ->
    SubAt u q v ->
    SubAt T (p ++ q) v.
Proof.
  intros T p u q v Hsub.
  induction Hsub; intros Hinner; simpl.
  - exact Hinner.
  - eapply sub_usr_child; eauto.
  - apply sub_equiv_l. exact (IHHsub Hinner).
  - apply sub_equiv_r. exact (IHHsub Hinner).
  - apply sub_rewrite_l. exact (IHHsub Hinner).
  - apply sub_rewrite_r. exact (IHHsub Hinner).
  - eapply sub_tuple_child; eauto.
Qed.

Lemma subat_usr_rewrite_inv :
  forall f args q l r,
    SubAt (TUsr f args) q (TRewrite l r) ->
    exists i child p,
      q = i :: p /\
      nth_error args i = Some child /\
      SubAt child p (TRewrite l r).
Proof.
  intros f args q l r Hsub.
  dependent destruction Hsub.
  exists i, child, p.
  repeat split; reflexivity || assumption.
Qed.

Lemma subat_tuple_rewrite_inv :
  forall args q l r,
    SubAt (TTuple args) q (TRewrite l r) ->
    exists i child p,
      q = i :: p /\
      nth_error args i = Some child /\
      SubAt child p (TRewrite l r).
Proof.
  intros args q l r Hsub.
  dependent destruction Hsub.
  exists i, child, p.
  repeat split; reflexivity || assumption.
Qed.

Lemma subat_equiv_rewrite_inv :
  forall a b q l r,
    SubAt (TEquiv a b) q (TRewrite l r) ->
    (exists p, q = 0 :: p /\ SubAt a p (TRewrite l r)) \/
    (exists p, q = 1 :: p /\ SubAt b p (TRewrite l r)).
Proof.
  intros a b q l r Hsub.
  dependent destruction Hsub.
  - left. exists p. split; reflexivity || assumption.
  - right. exists p. split; reflexivity || assumption.
Qed.

Lemma subat_rewrite_rewrite_inv :
  forall l r q l0 r0,
    SubAt (TRewrite l r) q (TRewrite l0 r0) ->
    (q = [] /\ l0 = l /\ r0 = r) \/
    (exists p, q = 0 :: p /\ SubAt l p (TRewrite l0 r0)) \/
    (exists p, q = 1 :: p /\ SubAt r p (TRewrite l0 r0)).
Proof.
  intros l r q l0 r0 Hsub.
  dependent destruction Hsub.
  - left. repeat split.
  - right. left. exists p. split; reflexivity || assumption.
  - right. right. exists p. split; reflexivity || assumption.
Qed.

Lemma subat_usr_var_inv :
  forall f args q x,
    SubAt (TUsr f args) q (TVar x) ->
    exists i child p,
      q = i :: p /\
      nth_error args i = Some child /\
      SubAt child p (TVar x).
Proof.
  intros f args q x Hsub.
  dependent destruction Hsub.
  exists i, child, p.
  repeat split; reflexivity || assumption.
Qed.

Lemma subat_tuple_var_inv :
  forall args q x,
    SubAt (TTuple args) q (TVar x) ->
    exists i child p,
      q = i :: p /\
      nth_error args i = Some child /\
      SubAt child p (TVar x).
Proof.
  intros args q x Hsub.
  dependent destruction Hsub.
  exists i, child, p.
  repeat split; reflexivity || assumption.
Qed.

Lemma subat_equiv_var_inv :
  forall a b q x,
    SubAt (TEquiv a b) q (TVar x) ->
    (exists p, q = 0 :: p /\ SubAt a p (TVar x)) \/
    (exists p, q = 1 :: p /\ SubAt b p (TVar x)).
Proof.
  intros a b q x Hsub.
  dependent destruction Hsub.
  - left. exists p. split; reflexivity || assumption.
  - right. exists p. split; reflexivity || assumption.
Qed.

Lemma subat_rewrite_var_inv :
  forall l r q x,
    SubAt (TRewrite l r) q (TVar x) ->
    (exists p, q = 0 :: p /\ SubAt l p (TVar x)) \/
    (exists p, q = 1 :: p /\ SubAt r p (TVar x)).
Proof.
  intros l r q x Hsub.
  dependent destruction Hsub.
  - left. exists p. split; reflexivity || assumption.
  - right. exists p. split; reflexivity || assumption.
Qed.

Lemma prefix_cons_inv :
  forall i j p q,
    Prefix (i :: p) (j :: q) ->
    i = j /\ Prefix p q.
Proof.
  intros i j p q Hpre.
  inversion Hpre; subst.
  split; reflexivity || assumption.
Qed.

Lemma variable_scope_usr_child :
  forall f args i child,
    variable_scope_ok (TUsr f args) ->
    nth_error args i = Some child ->
    variable_scope_ok child.
Proof.
  unfold variable_scope_ok.
  intros f args i child Hscope Hnth x p Hvar.
  assert (Hwhole_var : SubAt (TUsr f args) (i :: p) (TVar x)).
  {
    eapply sub_usr_child; eauto.
  }
  destruct (Hscope x (i :: p) Hwhole_var)
    as [q [j [l [r [Hj [Hpre Hrule]]]]]].
  destruct (subat_usr_rewrite_inv Hrule) as
      [k [rule_child [q0 [Hq [Hnth_rule Hrule_child]]]]].
  subst q.
  simpl in Hpre.
  destruct (prefix_cons_inv Hpre) as [Hki Hpre_tail].
  subst k.
  rewrite Hnth in Hnth_rule.
  inversion Hnth_rule; subst rule_child.
  exists q0, j, l, r.
  repeat split; try assumption.
Qed.

Lemma variable_scope_tuple_child :
  forall args i child,
    variable_scope_ok (TTuple args) ->
    nth_error args i = Some child ->
    variable_scope_ok child.
Proof.
  unfold variable_scope_ok.
  intros args i child Hscope Hnth x p Hvar.
  assert (Hwhole_var : SubAt (TTuple args) (i :: p) (TVar x)).
  {
    eapply sub_tuple_child; eauto.
  }
  destruct (Hscope x (i :: p) Hwhole_var)
    as [q [j [l [r [Hj [Hpre Hrule]]]]]].
  destruct (subat_tuple_rewrite_inv Hrule) as
      [k [rule_child [q0 [Hq [Hnth_rule Hrule_child]]]]].
  subst q.
  simpl in Hpre.
  destruct (prefix_cons_inv Hpre) as [Hki Hpre_tail].
  subst k.
  rewrite Hnth in Hnth_rule.
  inversion Hnth_rule; subst rule_child.
  exists q0, j, l, r.
  repeat split; try assumption.
Qed.

Lemma variable_scope_equiv_l_child :
  forall a b,
    variable_scope_ok (TEquiv a b) ->
    variable_scope_ok a.
Proof.
  unfold variable_scope_ok.
  intros a b Hscope x p Hvar.
  assert (Hwhole_var : SubAt (TEquiv a b) (0 :: p) (TVar x)).
  {
    apply sub_equiv_l. exact Hvar.
  }
  destruct (Hscope x (0 :: p) Hwhole_var)
    as [q [j [l [r [Hj [Hpre Hrule]]]]]].
  destruct (subat_equiv_rewrite_inv Hrule) as
      [[q0 [Hq Hleft]] | [q0 [Hq Hright]]]; subst q; simpl in Hpre.
  - destruct (prefix_cons_inv Hpre) as [_ Hpre_tail].
    exists q0, j, l, r. repeat split; try assumption.
  - destruct (prefix_cons_inv Hpre) as [Hbad _]. discriminate Hbad.
Qed.

Lemma variable_scope_equiv_r_child :
  forall a b,
    variable_scope_ok (TEquiv a b) ->
    variable_scope_ok b.
Proof.
  unfold variable_scope_ok.
  intros a b Hscope x p Hvar.
  assert (Hwhole_var : SubAt (TEquiv a b) (1 :: p) (TVar x)).
  {
    apply sub_equiv_r. exact Hvar.
  }
  destruct (Hscope x (1 :: p) Hwhole_var)
    as [q [j [l [r [Hj [Hpre Hrule]]]]]].
  destruct (subat_equiv_rewrite_inv Hrule) as
      [[q0 [Hq Hleft]] | [q0 [Hq Hright]]]; subst q; simpl in Hpre.
  - destruct (prefix_cons_inv Hpre) as [Hbad _]. discriminate Hbad.
  - destruct (prefix_cons_inv Hpre) as [_ Hpre_tail].
    exists q0, j, l, r. repeat split; try assumption.
Qed.

Lemma rules_safe_subterm :
  forall T p u,
    rules_safe T ->
    SubAt T p u ->
    rules_safe u.
Proof.
  unfold rules_safe.
  intros T p u Hsafe Hsub q l r Hrw.
  exact (Hsafe (p ++ q) l r (subat_append Hsub Hrw)).
Qed.

Lemma replace_nth_in_new_or_old :
  forall args i new out,
    replace_nth args i new (Some out) ->
    forall t, In t out -> t = new \/ In t args.
Proof.
  intros args i new out Hrep.
  remember (Some out) as result eqn:Hresult.
  generalize dependent out.
  induction Hrep; intros out Hresult t Hin; inversion Hresult; subst; simpl in Hin.
  - destruct Hin as [Ht | Hin].
    + left; symmetry; exact Ht.
    + right; right; exact Hin.
  - destruct Hin as [Ht | Hin].
    + right; left; exact Ht.
    + destruct (IHHrep rest' eq_refl t Hin) as [Htnew | Hinold].
      * left; exact Htnew.
      * right; right; exact Hinold.
Qed.

Lemma replaceat_fv_source_or_insert :
  forall T p s T' x,
    ReplaceAt T p s T' ->
    FV x T' ->
    FV x T \/ FV x s.
Proof.
  intros T p s T' x Hrep.
  induction Hrep; intros Hfv.
  - right; exact Hfv.
  - inversion Hfv; subst.
    match goal with
    | Hnth : replace_nth args i child' (Some args'),
      Hin : In ?t args',
      Hsub : FV x ?t,
      IH : FV x child' -> FV x child \/ FV x s |- _ =>
        destruct (replace_nth_in_new_or_old Hnth t Hin) as [Ht | Hinold]
    end.
    + subst.
      match goal with
      | Hsub : FV x child',
        IH : FV x child' -> FV x child \/ FV x s |- _ =>
          destruct (IH Hsub) as [Hold | Hs]
      end.
      * left. eapply fv_usr.
        -- eapply nth_error_in_term; eauto.
        -- exact Hold.
      * right; exact Hs.
    + left. eapply fv_usr.
      * exact Hinold.
      * assumption.
  - inversion Hfv; subst.
    + destruct (IHHrep H1) as [Ha | Hs].
      * left; apply fv_equiv_l; exact Ha.
      * right; exact Hs.
    + left; apply fv_equiv_r; assumption.
  - inversion Hfv; subst.
    + left; apply fv_equiv_l; assumption.
    + destruct (IHHrep H1) as [Hb | Hs].
      * left; apply fv_equiv_r; exact Hb.
      * right; exact Hs.
  - inversion Hfv; subst.
    + destruct (IHHrep H1) as [Hl | Hs].
      * left; apply fv_rewrite_l; exact Hl.
      * right; exact Hs.
    + left; apply fv_rewrite_r; assumption.
  - inversion Hfv; subst.
    + left; apply fv_rewrite_l; assumption.
    + destruct (IHHrep H1) as [Hr | Hs].
      * left; apply fv_rewrite_r; exact Hr.
      * right; exact Hs.
  - inversion Hfv; subst.
    match goal with
    | Hnth : replace_nth args i child' (Some args'),
      Hin : In ?t args',
      Hsub : FV x ?t,
      IH : FV x child' -> FV x child \/ FV x s |- _ =>
        destruct (replace_nth_in_new_or_old Hnth t Hin) as [Ht | Hinold]
    end.
    + subst.
      match goal with
      | Hsub : FV x child',
        IH : FV x child' -> FV x child \/ FV x s |- _ =>
          destruct (IH Hsub) as [Hold | Hs]
      end.
      * left. eapply fv_tuple.
        -- eapply nth_error_in_term; eauto.
        -- exact Hold.
      * right; exact Hs.
    + left. eapply fv_tuple.
      * exact Hinold.
      * assumption.
Qed.

Corollary replaceat_ground_insert_no_new_fv :
  forall T p s T' x,
    ReplaceAt T p s T' ->
    Ground s ->
    FV x T' ->
    FV x T.
Proof.
  intros T p s T' x Hrep Hs Hfv.
  destruct (replaceat_fv_source_or_insert Hrep Hfv) as [HT | Hinsert].
  - exact HT.
  - exfalso. exact (Hs x Hinsert).
Qed.

Lemma replace_nth_symmetric :
  forall args i new out,
    replace_nth args i new (Some out) ->
    forall old,
      nth_error args i = Some old ->
      replace_nth out i old (Some args).
Proof.
  intros args i new out Hrep.
  remember (Some out) as result eqn:Hresult.
  generalize dependent out.
  induction Hrep; intros out Hresult replaced Hnth; inversion Hresult; subst; simpl in Hnth.
  - inversion Hnth; subst replaced.
    apply replace_nth_here.
  - apply replace_nth_next.
    apply IHHrep with (out := rest').
    + reflexivity.
    + exact Hnth.
Qed.

Lemma replace_nth_new_at :
  forall args i new out,
    replace_nth args i new (Some out) ->
    nth_error out i = Some new.
Proof.
  intros args i new out Hrep.
  remember (Some out) as result eqn:Hresult.
  generalize dependent out.
  induction Hrep; intros out Hresult; inversion Hresult; subst; simpl.
  - reflexivity.
  - apply IHHrep with (out := rest'); reflexivity.
Qed.

Lemma replaceat_symmetric :
  forall T p old new T',
    SubAt T p old ->
    ReplaceAt T p new T' ->
    ReplaceAt T' p old T.
Proof.
  intros T p old new T' Hsub Hrep.
  generalize dependent old.
  induction Hrep; intros old0 Hsub.
  - inversion Hsub; subst.
    apply replace_here.
  - inversion Hsub; subst.
    match goal with
    | H1 : nth_error args i = Some child,
      H2 : nth_error args i = Some child0 |- _ =>
        rewrite H1 in H2; inversion H2; subst child0
    end.
    eapply replace_usr_child.
    + eapply replace_nth_new_at; eauto.
    + match goal with
      | Hchild : SubAt child p old0 |- _ => exact (IHHrep old0 Hchild)
      end.
    + eapply replace_nth_symmetric; eauto.
  - inversion Hsub; subst.
    apply replace_equiv_l.
    match goal with
    | Hchild : SubAt a p old0 |- _ => exact (IHHrep old0 Hchild)
    end.
  - inversion Hsub; subst.
    apply replace_equiv_r.
    match goal with
    | Hchild : SubAt b p old0 |- _ => exact (IHHrep old0 Hchild)
    end.
  - inversion Hsub; subst.
    apply replace_rewrite_l.
    match goal with
    | Hchild : SubAt l p old0 |- _ => exact (IHHrep old0 Hchild)
    end.
  - inversion Hsub; subst.
    apply replace_rewrite_r.
    match goal with
    | Hchild : SubAt r p old0 |- _ => exact (IHHrep old0 Hchild)
    end.
  - inversion Hsub; subst.
    match goal with
    | H1 : nth_error args i = Some child,
      H2 : nth_error args i = Some child0 |- _ =>
        rewrite H1 in H2; inversion H2; subst child0
    end.
    eapply replace_tuple_child.
    + eapply replace_nth_new_at; eauto.
    + match goal with
      | Hchild : SubAt child p old0 |- _ => exact (IHHrep old0 Hchild)
      end.
    + eapply replace_nth_symmetric; eauto.
Qed.

Lemma replaceat_ground_to_ground_fv_iff :
  forall T p old new T' x,
    SubAt T p old ->
    Ground old ->
    Ground new ->
    ReplaceAt T p new T' ->
    (FV x T <-> FV x T').
Proof.
  intros T p old new T' x Hsub Hold Hnew Hrep.
  split.
  - intros Hfv.
    pose proof (replaceat_symmetric Hsub Hrep) as Hsym.
    eapply replaceat_ground_insert_no_new_fv; eauto.
  - intros Hfv.
    eapply replaceat_ground_insert_no_new_fv; eauto.
Qed.

Theorem replaceat_ground_to_ground_preserves_rules_safe :
  forall T p old new T',
    SubAt T p old ->
    Ground old ->
    Ground new ->
    ReplaceAt T p new T' ->
    rules_safe T ->
    rules_safe T'.
Proof.
  intros T p old new T' Hsite Hold Hnew Hrep.
  generalize dependent old.
  induction Hrep; intros old0 Hsite Hold Hsafe.
  - unfold rules_safe.
    intros q l r Hrw x Hfv.
    exfalso.
    apply (Hnew x).
    eapply subat_fv_lift; [exact Hrw |].
    apply fv_rewrite_r. exact Hfv.
  - inversion Hsite; subst.
    match goal with
    | H1 : nth_error args i = Some child,
      H2 : nth_error args i = Some child0 |- _ =>
        rewrite H1 in H2; inversion H2; subst child0
    end.
    assert (Hchild_safe : rules_safe child).
    {
      eapply rules_safe_subterm.
      - exact Hsafe.
      - eapply sub_usr_child.
        + exact H.
        + apply sub_here.
    }
    pose proof (IHHrep Hnew old0 ltac:(match goal with Hs : SubAt child p old0 |- _ => exact Hs end) Hold Hchild_safe)
      as Hchild'_safe.
    unfold rules_safe.
    intros q l r Hrw x Hfv.
    destruct (subat_usr_rewrite_inv Hrw) as
        [k [child_at [q0 [_ [Hnth_out Hrw_child]]]]].
    destruct (replace_nth_in_new_or_old H0 child_at (@nth_error_in_term args' k child_at Hnth_out)) as [Hnew_child | Hold_child].
    + subst child_at.
      exact (Hchild'_safe q0 l r Hrw_child x Hfv).
    + destruct (in_term_nth_error args child_at Hold_child) as [k0 Hk0].
      assert (Hrw_old : SubAt (TUsr f args) (k0 :: q0) (TRewrite l r)).
      {
        eapply sub_usr_child; eauto.
      }
      exact (Hsafe (k0 :: q0) l r Hrw_old x Hfv).
  - inversion Hsite; subst.
    assert (Ha_safe : rules_safe a).
    {
      eapply rules_safe_subterm.
      - exact Hsafe.
      - apply sub_equiv_l. apply sub_here.
    }
    pose proof (IHHrep Hnew old0 ltac:(match goal with Hs : SubAt a p old0 |- _ => exact Hs end) Hold Ha_safe)
      as Ha'_safe.
    unfold rules_safe.
    intros q l r Hrw x Hfv.
    destruct (subat_equiv_rewrite_inv Hrw) as [[q0 [Hq Hleft]] | [q0 [Hq Hright]]]; subst q.
    + exact (Ha'_safe q0 l r Hleft x Hfv).
    + assert (Hrw_old : SubAt (TEquiv a b) (1 :: q0) (TRewrite l r)).
      {
        apply sub_equiv_r. exact Hright.
      }
      exact (Hsafe (1 :: q0) l r Hrw_old x Hfv).
  - inversion Hsite; subst.
    assert (Hb_safe : rules_safe b).
    {
      eapply rules_safe_subterm.
      - exact Hsafe.
      - apply sub_equiv_r. apply sub_here.
    }
    pose proof (IHHrep Hnew old0 ltac:(match goal with Hs : SubAt b p old0 |- _ => exact Hs end) Hold Hb_safe)
      as Hb'_safe.
    unfold rules_safe.
    intros q l r Hrw x Hfv.
    destruct (subat_equiv_rewrite_inv Hrw) as [[q0 [Hq Hleft]] | [q0 [Hq Hright]]]; subst q.
    + assert (Hrw_old : SubAt (TEquiv a b) (0 :: q0) (TRewrite l r)).
      {
        apply sub_equiv_l. exact Hleft.
      }
      exact (Hsafe (0 :: q0) l r Hrw_old x Hfv).
    + exact (Hb'_safe q0 l r Hright x Hfv).
  - inversion Hsite; subst.
    assert (Hl_safe : rules_safe l).
    {
      eapply rules_safe_subterm.
      - exact Hsafe.
      - apply sub_rewrite_l. apply sub_here.
    }
    pose proof (IHHrep Hnew old0 ltac:(match goal with Hs : SubAt l p old0 |- _ => exact Hs end) Hold Hl_safe)
      as Hl'_safe.
    unfold rules_safe.
    intros q l0 r0 Hrw x Hfv.
    destruct (subat_rewrite_rewrite_inv Hrw) as
        [[Hq [Hl0 Hr0]] | [[q0 [Hq Hleft]] | [q0 [Hq Hright]]]]; subst.
    + apply (proj1 (@replaceat_ground_to_ground_fv_iff l p old0 s l' x H3 Hold Hnew Hrep)).
      exact (Hsafe [] l r (sub_here _) x Hfv).
    + exact (Hl'_safe q0 l0 r0 Hleft x Hfv).
    + assert (Hrw_old : SubAt (TRewrite l r) (1 :: q0) (TRewrite l0 r0)).
      {
        apply sub_rewrite_r. exact Hright.
      }
      exact (Hsafe (1 :: q0) l0 r0 Hrw_old x Hfv).
  - inversion Hsite; subst.
    assert (Hr_safe : rules_safe r).
    {
      eapply rules_safe_subterm.
      - exact Hsafe.
      - apply sub_rewrite_r. apply sub_here.
    }
    pose proof (IHHrep Hnew old0 ltac:(match goal with Hs : SubAt r p old0 |- _ => exact Hs end) Hold Hr_safe)
      as Hr'_safe.
    unfold rules_safe.
    intros q l0 r0 Hrw x Hfv.
    destruct (subat_rewrite_rewrite_inv Hrw) as
        [[Hq [Hl0 Hr0]] | [[q0 [Hq Hleft]] | [q0 [Hq Hright]]]]; subst.
    + exact (Hsafe [] l r (sub_here _) x
        ((proj2 (@replaceat_ground_to_ground_fv_iff r p old0 s r' x H3 Hold Hnew Hrep)) Hfv)).
    + assert (Hrw_old : SubAt (TRewrite l r) (0 :: q0) (TRewrite l0 r0)).
      {
        apply sub_rewrite_l. exact Hleft.
      }
      exact (Hsafe (0 :: q0) l0 r0 Hrw_old x Hfv).
    + exact (Hr'_safe q0 l0 r0 Hright x Hfv).
  - inversion Hsite; subst.
    match goal with
    | H1 : nth_error args i = Some child,
      H2 : nth_error args i = Some child0 |- _ =>
        rewrite H1 in H2; inversion H2; subst child0
    end.
    assert (Hchild_safe : rules_safe child).
    {
      eapply rules_safe_subterm.
      - exact Hsafe.
      - eapply sub_tuple_child.
        + exact H.
        + apply sub_here.
    }
    pose proof (IHHrep Hnew old0 ltac:(match goal with Hs : SubAt child p old0 |- _ => exact Hs end) Hold Hchild_safe)
      as Hchild'_safe.
    unfold rules_safe.
    intros q l r Hrw x Hfv.
    destruct (subat_tuple_rewrite_inv Hrw) as
        [k [child_at [q0 [_ [Hnth_out Hrw_child]]]]].
    destruct (replace_nth_in_new_or_old H0 child_at (@nth_error_in_term args' k child_at Hnth_out)) as [Hnew_child | Hold_child].
    + subst child_at.
      exact (Hchild'_safe q0 l r Hrw_child x Hfv).
    + destruct (in_term_nth_error args child_at Hold_child) as [k0 Hk0].
      assert (Hrw_old : SubAt (TTuple args) (k0 :: q0) (TRewrite l r)).
      {
        eapply sub_tuple_child; eauto.
      }
      exact (Hsafe (k0 :: q0) l r Hrw_old x Hfv).
Qed.

Theorem replaceat_ground_insert_preserves_variable_scope :
  forall T p new T',
    Ground new ->
    ReplaceAt T p new T' ->
    variable_scope_ok T ->
    variable_scope_ok T'.
Proof.
  intros T p new T' Hnew Hrep.
  induction Hrep; intros Hscope.
  - unfold variable_scope_ok.
    intros x p Hvar.
    exfalso.
    exact (Hnew x (subat_fv_lift Hvar (fv_var x))).
  - assert (Hchild_scope : variable_scope_ok child).
    {
      eapply variable_scope_usr_child; eauto.
    }
    pose proof (IHHrep Hnew Hchild_scope) as Hchild'_scope.
    unfold variable_scope_ok.
    intros x q Hvar.
    destruct (subat_usr_var_inv Hvar) as
        [k [child_at [pvar [Hq [Hnth_out Hvar_child]]]]].
    subst q.
    destruct (replace_nth_in_new_or_old H0 child_at (@nth_error_in_term args' k child_at Hnth_out)) as
        [Hnew_child | Hold_child].
    + subst child_at.
      destruct (Hchild'_scope x pvar Hvar_child) as
          [q0 [j [l [r [Hj [Hpre Hrule]]]]]].
      exists (k :: q0), j, l, r.
      split; [exact Hj |].
      split.
      * simpl. apply prefix_cons. exact Hpre.
      * eapply sub_usr_child; eauto.
    + destruct (in_term_nth_error args child_at Hold_child) as [k0 Hk0].
      pose proof (@variable_scope_usr_child f args k0 child_at Hscope Hk0) as Hchild_at_scope.
      destruct (Hchild_at_scope x pvar Hvar_child) as
          [q0 [j [l [r [Hj [Hpre Hrule]]]]]].
      exists (k :: q0), j, l, r.
      split; [exact Hj |].
      split.
      * simpl. apply prefix_cons. exact Hpre.
      * eapply sub_usr_child; eauto.
  - assert (Ha_scope : variable_scope_ok a).
    {
      apply (variable_scope_equiv_l_child Hscope).
    }
    pose proof (IHHrep Hnew Ha_scope) as Ha'_scope.
    pose proof (variable_scope_equiv_r_child Hscope) as Hb_scope.
    unfold variable_scope_ok.
    intros x q Hvar.
    destruct (subat_equiv_var_inv Hvar) as [[pvar [Hq Hvar_left]] | [pvar [Hq Hvar_right]]]; subst q.
    + destruct (Ha'_scope x pvar Hvar_left) as
          [q0 [j [l [r [Hj [Hpre Hrule]]]]]].
      exists (0 :: q0), j, l, r.
      split; [exact Hj |].
      split.
      * simpl. apply prefix_cons. exact Hpre.
      * apply sub_equiv_l. exact Hrule.
    + destruct (Hb_scope x pvar Hvar_right) as
          [q0 [j [l [r [Hj [Hpre Hrule]]]]]].
      exists (1 :: q0), j, l, r.
      split; [exact Hj |].
      split.
      * simpl. apply prefix_cons. exact Hpre.
      * apply sub_equiv_r. exact Hrule.
  - assert (Hb_scope : variable_scope_ok b).
    {
      apply (variable_scope_equiv_r_child Hscope).
    }
    pose proof (IHHrep Hnew Hb_scope) as Hb'_scope.
    pose proof (variable_scope_equiv_l_child Hscope) as Ha_scope.
    unfold variable_scope_ok.
    intros x q Hvar.
    destruct (subat_equiv_var_inv Hvar) as [[pvar [Hq Hvar_left]] | [pvar [Hq Hvar_right]]]; subst q.
    + destruct (Ha_scope x pvar Hvar_left) as
          [q0 [j [l [r [Hj [Hpre Hrule]]]]]].
      exists (0 :: q0), j, l, r.
      split; [exact Hj |].
      split.
      * simpl. apply prefix_cons. exact Hpre.
      * apply sub_equiv_l. exact Hrule.
    + destruct (Hb'_scope x pvar Hvar_right) as
          [q0 [j [l [r [Hj [Hpre Hrule]]]]]].
      exists (1 :: q0), j, l, r.
      split; [exact Hj |].
      split.
      * simpl. apply prefix_cons. exact Hpre.
      * apply sub_equiv_r. exact Hrule.
  - unfold variable_scope_ok.
    intros x q Hvar.
    destruct (subat_rewrite_var_inv Hvar) as [[pvar [Hq Hvar_left]] | [pvar [Hq Hvar_right]]]; subst q.
    + exists [], 0, l', r.
      split; [left; reflexivity |].
      split.
      * simpl. apply prefix_cons. apply prefix_nil.
      * apply sub_here.
    + exists [], 1, l', r.
      split; [right; reflexivity |].
      split.
      * simpl. apply prefix_cons. apply prefix_nil.
      * apply sub_here.
  - unfold variable_scope_ok.
    intros x q Hvar.
    destruct (subat_rewrite_var_inv Hvar) as [[pvar [Hq Hvar_left]] | [pvar [Hq Hvar_right]]]; subst q.
    + exists [], 0, l, r'.
      split; [left; reflexivity |].
      split.
      * simpl. apply prefix_cons. apply prefix_nil.
      * apply sub_here.
    + exists [], 1, l, r'.
      split; [right; reflexivity |].
      split.
      * simpl. apply prefix_cons. apply prefix_nil.
      * apply sub_here.
  - assert (Hchild_scope : variable_scope_ok child).
    {
      eapply variable_scope_tuple_child; eauto.
    }
    pose proof (IHHrep Hnew Hchild_scope) as Hchild'_scope.
    unfold variable_scope_ok.
    intros x q Hvar.
    destruct (subat_tuple_var_inv Hvar) as
        [k [child_at [pvar [Hq [Hnth_out Hvar_child]]]]].
    subst q.
    destruct (replace_nth_in_new_or_old H0 child_at (@nth_error_in_term args' k child_at Hnth_out)) as
        [Hnew_child | Hold_child].
    + subst child_at.
      destruct (Hchild'_scope x pvar Hvar_child) as
          [q0 [j [l [r [Hj [Hpre Hrule]]]]]].
      exists (k :: q0), j, l, r.
      split; [exact Hj |].
      split.
      * simpl. apply prefix_cons. exact Hpre.
      * eapply sub_tuple_child; eauto.
    + destruct (in_term_nth_error args child_at Hold_child) as [k0 Hk0].
      pose proof (@variable_scope_tuple_child args k0 child_at Hscope Hk0) as Hchild_at_scope.
      destruct (Hchild_at_scope x pvar Hvar_child) as
          [q0 [j [l [r [Hj [Hpre Hrule]]]]]].
      exists (k :: q0), j, l, r.
      split; [exact Hj |].
      split.
      * simpl. apply prefix_cons. exact Hpre.
      * eapply sub_tuple_child; eauto.
Qed.

Theorem replaceat_ground_to_ground_preserves_spec :
  forall T p old new T',
    SubAt T p old ->
    Ground old ->
    Ground new ->
    ReplaceAt T p new T' ->
    Spec T ->
    Spec T'.
Proof.
  intros T p old new T' Hsite Hold Hnew Hrep Hspec.
  constructor.
  - eapply replaceat_ground_insert_preserves_variable_scope.
    + exact Hnew.
    + exact Hrep.
    + exact (spec_scope Hspec).
  - eapply replaceat_ground_to_ground_preserves_rules_safe.
    + exact Hsite.
    + exact Hold.
    + exact Hnew.
    + exact Hrep.
    + exact (spec_rules_safe Hspec).
Qed.

Lemma ground_spec : forall T, Ground T -> Spec T.
Proof.
  intros T HT.
  constructor.
  - intros x p Hvar.
    exfalso.
    exact (HT x (subat_fv_lift Hvar (fv_var x))).
  - intros q l r Hrw x Hfv.
    exfalso.
    apply (HT x).
    eapply subat_fv_lift; [exact Hrw |].
    eapply fv_rewrite_r; exact Hfv.
Qed.

Definition RuleOf (T : Term) (q : list nat) (l r : Term) : Prop :=
  SubAt T q (TRewrite l r).

Definition BaseEq (T s t : Term) : Prop :=
  Subterm T (TEquiv s t) /\ Ground s /\ Ground t.

Definition U (T a : Term) : Prop := GroundSub T a.

Record CongProps (T : Term) (C : Term -> Term -> Prop) : Prop := {
  cp_base : forall s t, BaseEq T s t -> C s t;
  cp_refl : forall a, U T a -> C a a;
  cp_sym : forall a b, C a b -> C b a;
  cp_trans : forall a b c, C a b -> C b c -> C a c;
  cp_usr :
    forall f xs ys,
      U T (TUsr f xs) ->
      U T (TUsr f ys) ->
      Forall2 C xs ys ->
      C (TUsr f xs) (TUsr f ys);
  cp_equiv :
    forall a a' b b',
      U T (TEquiv a b) ->
      U T (TEquiv a' b') ->
      C a a' ->
      C b b' ->
      C (TEquiv a b) (TEquiv a' b');
  cp_rewrite :
    forall l l' r r',
      U T (TRewrite l r) ->
      U T (TRewrite l' r') ->
      C l l' ->
      C r r' ->
      C (TRewrite l r) (TRewrite l' r');
  cp_tuple :
    forall xs ys,
      U T (TTuple xs) ->
      U T (TTuple ys) ->
      Forall2 C xs ys ->
      C (TTuple xs) (TTuple ys)
}.

Definition DynCong (T a b : Term) : Prop :=
  U T a /\ U T b /\ forall C, CongProps T C -> C a b.

Lemma dyn_refl : forall T a, U T a -> DynCong T a a.
Proof.
  intros T a Ha.
  split; [exact Ha |].
  split; [exact Ha |].
  intros C HC; exact (@cp_refl T C HC a Ha).
Qed.

Lemma dyn_sym : forall T a b, DynCong T a b -> DynCong T b a.
Proof.
  intros T a b [Ha [Hb Hab]].
  split; [exact Hb |].
  split; [exact Ha |].
  intros C HC; exact (@cp_sym T C HC a b (Hab C HC)).
Qed.

Lemma dyn_trans : forall T a b c, DynCong T a b -> DynCong T b c -> DynCong T a c.
Proof.
  intros T a b c [Ha [_ Hab]] [_ [Hc Hbc]].
  split; [exact Ha |].
  split; [exact Hc |].
  intros C HC; exact (@cp_trans T C HC a b c (Hab C HC) (Hbc C HC)).
Qed.

Definition Decidable (P : Prop) : Prop := P \/ ~ P.

Theorem dynamic_congruence_decidable :
  forall T a b, Spec T -> U T a -> U T b -> Decidable (DynCong T a b).
Proof.
  intros; unfold Decidable; apply classic.
Qed.

Record DynCongFiniteDecider (T : Term) : Type := {
  dyn_finite_decide :
    forall a b,
      U T a ->
      U T b ->
      {DynCong T a b} + {~ DynCong T a b}
}.

Theorem dynamic_congruence_decidable_from_finite_decider :
  forall T a b,
    Spec T ->
    U T a ->
    U T b ->
    DynCongFiniteDecider T ->
    Decidable (DynCong T a b).
Proof.
  intros T a b _ Ha Hb D.
  unfold Decidable.
  destruct (@dyn_finite_decide T D a b Ha Hb) as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

Record DynCongClosureCertificate (T : Term) : Type := {
  dyn_closure_domain : list Term;
  dyn_closure_domain_exact :
    forall a, In a dyn_closure_domain <-> U T a;
  dyn_closure_relation : list (Term * Term);
  dyn_closure_relation_exact :
    forall a b, In (a, b) dyn_closure_relation <-> DynCong T a b;
  dyn_closure_pair_decide :
    forall a b, {In (a, b) dyn_closure_relation} + {~ In (a, b) dyn_closure_relation}
}.

Theorem dynamic_congruence_decidable_from_closure_certificate :
  forall T a b,
    Spec T ->
    U T a ->
    U T b ->
    DynCongClosureCertificate T ->
    Decidable (DynCong T a b).
Proof.
  intros T a b _ _ _ C.
  unfold Decidable.
  destruct (@dyn_closure_pair_decide T C a b) as [Hin | Hnin].
  - left. apply (proj1 (@dyn_closure_relation_exact T C a b)); exact Hin.
  - right. intros Hcong.
    apply Hnin.
    apply (proj2 (@dyn_closure_relation_exact T C a b)); exact Hcong.
Qed.

Record GroundSubst (T : Term) (sigma : nat -> option Term) : Prop := {
  gs_ground : forall x g, sigma x = Some g -> Ground g;
  gs_codomain : forall x g, sigma x = Some g -> U T g
}.

Definition subst_domain_exact (sigma : nat -> option Term) (l : Term) : Prop :=
  forall x, FV x l <-> exists g, sigma x = Some g.

Record DRMatch (T l a : Term) (sigma : nat -> option Term) (sl : Term) : Prop := {
  drm_ground_subst : GroundSubst T sigma;
  drm_domain : subst_domain_exact sigma l;
  drm_subst : SubstRel sigma l sl;
  drm_image_in_U : U T sl;
  drm_cong : DynCong T sl a
}.

Theorem drmatch_decidable :
  forall T l a, Spec T -> U T a -> Decidable (exists sigma sl, DRMatch T l a sigma sl).
Proof.
  intros; unfold Decidable; apply classic.
Qed.

Record DRMatchFiniteDecider (T l a : Term) : Type := {
  drmatch_finite_decide :
    {exists sigma sl, DRMatch T l a sigma sl} +
    {~ exists sigma sl, DRMatch T l a sigma sl}
}.

Theorem drmatch_decidable_from_finite_decider :
  forall T l a,
    Spec T ->
    U T a ->
    DRMatchFiniteDecider T l a ->
    Decidable (exists sigma sl, DRMatch T l a sigma sl).
Proof.
  intros T l a _ _ D.
  unfold Decidable.
  destruct (@drmatch_finite_decide T l a D) as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

Record DRMatchEnumerationCertificate (T l a : Term) : Type := {
  drmatch_candidate_list : list ((nat -> option Term) * Term);
  drmatch_candidate_exact :
    forall sigma sl,
      In (sigma, sl) drmatch_candidate_list <-> DRMatch T l a sigma sl;
  drmatch_candidate_exists_decide :
    {exists sigma sl, In (sigma, sl) drmatch_candidate_list} +
    {~ exists sigma sl, In (sigma, sl) drmatch_candidate_list}
}.

Theorem drmatch_decidable_from_enumeration_certificate :
  forall T l a,
    Spec T ->
    U T a ->
    DRMatchEnumerationCertificate T l a ->
    Decidable (exists sigma sl, DRMatch T l a sigma sl).
Proof.
  intros T l a _ _ C.
  unfold Decidable.
  destruct (@drmatch_candidate_exists_decide T l a C) as [Hex | Hnone].
  - left.
    destruct Hex as [sigma [sl Hin]].
    exists sigma, sl.
    apply (proj1 (@drmatch_candidate_exact T l a C sigma sl)); exact Hin.
  - right. intros Hex.
    apply Hnone.
    destruct Hex as [sigma [sl Hmatch]].
    exists sigma, sl.
    apply (proj2 (@drmatch_candidate_exact T l a C sigma sl)); exact Hmatch.
Qed.

Inductive RawStep (T T' : Term) : Prop :=
| raw_step_intro :
  forall (rule_pos app_pos : list nat)
      (lhs rhs target : Term)
      (sigma : nat -> option Term)
      (lhs_image rhs_image : Term),
      RuleOf T rule_pos lhs rhs ->
      SubAt T app_pos target ->
      U T target ->
      DRMatch T lhs target sigma lhs_image ->
      SubstRel sigma rhs rhs_image ->
      Ground rhs_image ->
      ReplaceAt T app_pos rhs_image T' ->
      RawStep T T'.

Inductive Step (T T' : Term) : Prop :=
| step_intro :
    Spec T ->
    RawStep T T' ->
    Spec T' ->
    Step T T'.

Inductive StepM (T T' : Term) : Prop :=
| step_m_intro :
    Spec T ->
    RawStep T T' ->
    StepM T T'.

Theorem certified_step_is_stepM :
  forall T T', Step T T' -> StepM T T'.
Proof.
  intros T T' H.
  inversion H; subst.
  exact (step_m_intro H0 H1).
Qed.

Definition NF (T : Term) : Prop :=
  forall T', StepM T T' -> T' = T.

Theorem normal_form_decidable :
  forall T, Spec T -> Decidable (NF T).
Proof.
  intros; unfold Decidable; apply classic.
Qed.

Record StepMCandidateDecider (T : Term) : Type := {
  stepM_candidates : list Term;
  stepM_candidates_complete :
    forall T', StepM T T' -> In T' stepM_candidates;
  stepM_candidate_decide :
    forall T',
      In T' stepM_candidates ->
      {StepM T T'} + {~ StepM T T'}
}.

Theorem normal_form_decidable_from_finite_candidates :
  forall T,
    Spec T ->
    StepMCandidateDecider T ->
    Decidable (NF T).
Proof.
  intros T _ D.
  unfold Decidable, NF.
  assert (Hscan_list :
    forall cs,
      (forall T', In T' cs -> In T' (@stepM_candidates T D)) ->
      {forall T', In T' cs -> StepM T T' -> T' = T} +
      {exists T', In T' cs /\ StepM T T' /\ T' <> T}).
  {
    induction cs as [|c cs IH]; intros Hsub.
    {
      left. intros T' Hin _; contradiction.
    }
    destruct (@stepM_candidate_decide T D c (Hsub c (or_introl eq_refl))) as [Hcstep | Hcnostep].
    {
      destruct (term_eq_dec c T) as [Heq | Hneq].
      {
        destruct (IH (fun T' Hin => Hsub T' (or_intror Hin))) as [Hgood | Hbad].
        {
          left. intros T' Hin Hstep.
          destruct Hin as [HT' | Hin].
          {
            subst T'. exact Heq.
          }
          {
            exact (Hgood T' Hin Hstep).
          }
        }
        {
          right.
          destruct Hbad as [T' [Hin [Hstep Hneq']]].
          exists T'. split.
          {
            right; exact Hin.
          }
          split; assumption.
        }
      }
      {
        right.
        exists c. split.
        {
          left; reflexivity.
        }
        split; assumption.
      }
    }
    {
      destruct (IH (fun T' Hin => Hsub T' (or_intror Hin))) as [Hgood | Hbad].
      {
        left. intros T' Hin Hstep.
        destruct Hin as [HT' | Hin].
        {
          subst T'. exfalso. exact (Hcnostep Hstep).
        }
        {
          exact (Hgood T' Hin Hstep).
        }
      }
      {
        right.
        destruct Hbad as [T' [Hin [Hstep Hneq']]].
        exists T'. split.
        {
          right; exact Hin.
        }
        split; assumption.
      }
    }
  }
  destruct (Hscan_list (@stepM_candidates T D) (fun T' Hin => Hin)) as [Hgood | Hbad].
  - left. intros T' Hstep.
    exact (Hgood T' (@stepM_candidates_complete T D T' Hstep) Hstep).
  - right. intros Hnf.
    destruct Hbad as [T' [_ [Hstep Hneq]]].
    exact (Hneq (Hnf T' Hstep)).
Qed.

Record StepMEnumerationCertificate (T : Term) : Type := {
  stepM_candidate_list : list Term;
  stepM_candidate_exact :
    forall T', In T' stepM_candidate_list <-> StepM T T';
  stepM_nontrivial_exists_decide :
    {exists T', In T' stepM_candidate_list /\ T' <> T} +
    {~ exists T', In T' stepM_candidate_list /\ T' <> T}
}.

Theorem normal_form_decidable_from_enumeration_certificate :
  forall T,
    Spec T ->
    StepMEnumerationCertificate T ->
    Decidable (NF T).
Proof.
  intros T _ C.
  unfold Decidable, NF.
  destruct (@stepM_nontrivial_exists_decide T C) as [Hex | Hnone].
  - right. intros Hnf.
    destruct Hex as [T' [Hin Hneq]].
    apply Hneq.
    apply Hnf.
    apply (proj1 (@stepM_candidate_exact T C T')); exact Hin.
  - left. intros T' Hstep.
    destruct (term_eq_dec T' T) as [Heq | Hneq].
    + exact Heq.
    + exfalso. apply Hnone.
      exists T'. split.
      * apply (proj2 (@stepM_candidate_exact T C T')); exact Hstep.
      * exact Hneq.
Qed.

Theorem step_preserves_spec :
  forall T T', Step T T' -> Spec T'.
Proof.
  intros T T' H.
  inversion H; subst; assumption.
Qed.

Theorem raw_step_preserves_spec :
  forall T T',
    Spec T ->
    RawStep T T' ->
    Spec T'.
Proof.
  intros T T' Hspec Hstep.
  inversion Hstep; subst.
  destruct H1 as [_ Htarget_ground].
  eapply replaceat_ground_to_ground_preserves_spec.
  - exact H0.
  - exact Htarget_ground.
  - exact H4.
  - exact H5.
  - exact Hspec.
Qed.

Theorem stepM_preserves_spec :
  forall T T',
    StepM T T' ->
    Spec T'.
Proof.
  intros T T' Hstep.
  inversion Hstep; subst.
  eapply raw_step_preserves_spec; eauto.
Qed.

Theorem raw_step_no_new_fv :
  forall T T' x,
    RawStep T T' ->
    FV x T' ->
    FV x T.
Proof.
  intros T T' x Hstep Hfv.
  inversion Hstep; subst.
  eapply replaceat_ground_insert_no_new_fv; eauto.
Qed.

Theorem stepM_no_new_fv :
  forall T T' x,
    StepM T T' ->
    FV x T' ->
    FV x T.
Proof.
  intros T T' x Hstep Hfv.
  inversion Hstep; subst.
  eapply raw_step_no_new_fv; eauto.
Qed.

Inductive Label : Type := L : nat -> Label.

Inductive CounterInstr : Type :=
| Inc1 : Label -> Label -> CounterInstr
| Inc2 : Label -> Label -> CounterInstr
| DecJump1 : Label -> Label -> Label -> CounterInstr
| DecJump2 : Label -> Label -> Label -> CounterInstr.

Record CounterMachine : Type := {
  cm_instr : CounterInstr -> Prop
}.

Record Config : Type := {
  cfg_label : Label;
  cfg_c1 : nat;
  cfg_c2 : nat
}.

Inductive CM_step (M : CounterMachine) : Config -> Config -> Prop :=
| cm_inc1 :
    forall l l' m n,
      cm_instr M (Inc1 l l') ->
      CM_step M {| cfg_label := l; cfg_c1 := m; cfg_c2 := n |}
                {| cfg_label := l'; cfg_c1 := S m; cfg_c2 := n |}
| cm_inc2 :
    forall l l' m n,
      cm_instr M (Inc2 l l') ->
      CM_step M {| cfg_label := l; cfg_c1 := m; cfg_c2 := n |}
                {| cfg_label := l'; cfg_c1 := m; cfg_c2 := S n |}
| cm_dec1_zero :
    forall l l0 ls n,
      cm_instr M (DecJump1 l l0 ls) ->
      CM_step M {| cfg_label := l; cfg_c1 := 0; cfg_c2 := n |}
                {| cfg_label := l0; cfg_c1 := 0; cfg_c2 := n |}
| cm_dec1_succ :
    forall l l0 ls m n,
      cm_instr M (DecJump1 l l0 ls) ->
      CM_step M {| cfg_label := l; cfg_c1 := S m; cfg_c2 := n |}
                {| cfg_label := ls; cfg_c1 := m; cfg_c2 := n |}
| cm_dec2_zero :
    forall l l0 ls m,
      cm_instr M (DecJump2 l l0 ls) ->
      CM_step M {| cfg_label := l; cfg_c1 := m; cfg_c2 := 0 |}
                {| cfg_label := l0; cfg_c1 := m; cfg_c2 := 0 |}
| cm_dec2_succ :
    forall l l0 ls m n,
      cm_instr M (DecJump2 l l0 ls) ->
      CM_step M {| cfg_label := l; cfg_c1 := m; cfg_c2 := S n |}
                {| cfg_label := ls; cfg_c1 := m; cfg_c2 := n |}.

Definition c_zero : nat := 0.
Definition c_succ : nat := 1.
Definition c_state : nat := 2.
Definition c_label (l : Label) : nat :=
  match l with L n => 100 + n end.

Fixpoint numeral (n : nat) : Term :=
  match n with
  | O => TUsr c_zero []
  | S k => TUsr c_succ [numeral k]
  end.

Definition label_term (l : Label) : Term := TUsr (c_label l) [].

Definition config_term (c : Config) : Term :=
  TUsr c_state [label_term (cfg_label c); numeral (cfg_c1 c); numeral (cfg_c2 c)].

Lemma ground_usr :
  forall f args, Forall Ground args -> Ground (TUsr f args).
Proof.
  intros f args Hargs x Hfv.
  inversion Hfv; subst.
  rewrite Forall_forall in Hargs.
  match goal with
  | Hin : In ?t args, Hsub : FV x ?t |- _ =>
      exact (Hargs t Hin x Hsub)
  end.
Qed.

Lemma ground_tuple :
  forall args, Forall Ground args -> Ground (TTuple args).
Proof.
  intros args Hargs x Hfv.
  inversion Hfv; subst.
  rewrite Forall_forall in Hargs.
  match goal with
  | Hin : In ?t args, Hsub : FV x ?t |- _ =>
      exact (Hargs t Hin x Hsub)
  end.
Qed.

Lemma ground_rewrite :
  forall l r, Ground l -> Ground r -> Ground (TRewrite l r).
Proof.
  intros l r Hl Hr x Hfv.
  inversion Hfv; subst.
  - exact (Hl x H1).
  - exact (Hr x H1).
Qed.

Lemma ground_label : forall l, Ground (label_term l).
Proof.
  intros l.
  apply ground_usr.
  constructor.
Qed.

Lemma ground_numeral : forall n, Ground (numeral n).
Proof.
  induction n as [|n IH].
  - apply ground_usr; constructor.
  - apply ground_usr; constructor; [exact IH | constructor].
Qed.

Lemma ground_config : forall c, Ground (config_term c).
Proof.
  intros [l m n].
  apply ground_usr.
  repeat constructor.
  - apply ground_label.
  - apply ground_numeral.
  - apply ground_numeral.
Qed.

Definition machine_rule_term (c c' : Config) : Term :=
  TRewrite (config_term c) (config_term c').

Definition machine_step_term (c c' : Config) : Term :=
  TTuple [machine_rule_term c c'; config_term c].

Definition machine_step_term_next (c c' : Config) : Term :=
  TTuple [machine_rule_term c c'; config_term c'].

Lemma ground_machine_rule : forall c c', Ground (machine_rule_term c c').
Proof.
  intros c c'; unfold machine_rule_term.
  apply ground_rewrite; apply ground_config.
Qed.

Lemma ground_machine_step_term : forall c c', Ground (machine_step_term c c').
Proof.
  intros c c'; unfold machine_step_term.
  apply ground_tuple.
  repeat constructor.
  - apply ground_machine_rule.
  - apply ground_config.
Qed.

Lemma ground_machine_step_term_next : forall c c', Ground (machine_step_term_next c c').
Proof.
  intros c c'; unfold machine_step_term_next.
  apply ground_tuple.
  repeat constructor.
  - apply ground_machine_rule.
  - apply ground_config.
Qed.

Definition c_comm_add : nat := 200.
Definition c_comm_one : nat := 201.
Definition c_comm_two : nat := 202.
Definition c_comm_simp : nat := 203.
Definition c_comm_declare : nat := 204.

Definition comm_one : Term := TUsr c_comm_one [].
Definition comm_two : Term := TUsr c_comm_two [].
Definition comm_simp : Term := TUsr c_comm_simp [].
Definition comm_declare : Term := TUsr c_comm_declare [].
Definition comm_add (a b : Term) : Term := TUsr c_comm_add [a; b].

Definition comm_Rgen_lhs : Term :=
  TTuple [comm_declare; comm_add (TVar 0) (TVar 1)].

Definition comm_Rgen_rhs : Term :=
  TTuple [
    comm_declare;
    comm_add (TVar 0) (TVar 1);
    TEquiv (comm_add (TVar 0) (TVar 1)) (comm_add (TVar 1) (TVar 0))
  ].

Definition comm_Rsimp_lhs : Term := comm_add comm_two comm_one.
Definition comm_Rsimp_rhs : Term := comm_simp.
Definition comm_Rgen : Term := TRewrite comm_Rgen_lhs comm_Rgen_rhs.
Definition comm_Rsimp : Term := TRewrite comm_Rsimp_lhs comm_Rsimp_rhs.

Definition comm_data0 : Term :=
  TTuple [comm_declare; comm_add comm_one comm_two].

Definition comm_data1 : Term :=
  TTuple [
    comm_declare;
    comm_add comm_one comm_two;
    TEquiv (comm_add comm_one comm_two) (comm_add comm_two comm_one)
  ].

Definition comm_data2 : Term :=
  TTuple [
    comm_declare;
    comm_simp;
    TEquiv (comm_add comm_one comm_two) (comm_add comm_two comm_one)
  ].

Definition comm_T0 : Term := TTuple [comm_Rgen; comm_Rsimp; comm_data0].
Definition comm_T1 : Term := TTuple [comm_Rgen; comm_Rsimp; comm_data1].
Definition comm_T2 : Term := TTuple [comm_Rgen; comm_Rsimp; comm_data2].

Definition comm_sigma_gen (x : nat) : option Term :=
  match x with
  | 0 => Some comm_one
  | 1 => Some comm_two
  | _ => None
  end.

Definition comm_sigma_empty (_ : nat) : option Term := None.

Lemma ground_equiv :
  forall s t, Ground s -> Ground t -> Ground (TEquiv s t).
Proof.
  intros s t Hs Ht x Hfv.
  inversion Hfv; subst.
  - exact (Hs x H1).
  - exact (Ht x H1).
Qed.

Lemma ground_comm_one : Ground comm_one.
Proof. unfold comm_one. apply ground_usr. constructor. Qed.

Lemma ground_comm_two : Ground comm_two.
Proof. unfold comm_two. apply ground_usr. constructor. Qed.

Lemma ground_comm_simp : Ground comm_simp.
Proof. unfold comm_simp. apply ground_usr. constructor. Qed.

Lemma ground_comm_declare : Ground comm_declare.
Proof. unfold comm_declare. apply ground_usr. constructor. Qed.

Lemma ground_comm_add :
  forall a b, Ground a -> Ground b -> Ground (comm_add a b).
Proof.
  intros a b Ha Hb.
  unfold comm_add.
  apply ground_usr.
  repeat constructor; assumption.
Qed.

Lemma ground_comm_data0 : Ground comm_data0.
Proof.
  unfold comm_data0.
  apply ground_tuple.
  repeat constructor.
  - apply ground_comm_declare.
  - apply ground_comm_add; [apply ground_comm_one | apply ground_comm_two].
Qed.

Lemma ground_comm_data1 : Ground comm_data1.
Proof.
  unfold comm_data1.
  apply ground_tuple.
  repeat constructor.
  - apply ground_comm_declare.
  - apply ground_comm_add; [apply ground_comm_one | apply ground_comm_two].
  - apply ground_equiv; apply ground_comm_add; [apply ground_comm_one | apply ground_comm_two | apply ground_comm_two | apply ground_comm_one].
Qed.

Lemma ground_comm_data2 : Ground comm_data2.
Proof.
  unfold comm_data2.
  apply ground_tuple.
  repeat constructor.
  - apply ground_comm_declare.
  - apply ground_comm_simp.
  - apply ground_equiv; apply ground_comm_add; [apply ground_comm_one | apply ground_comm_two | apply ground_comm_two | apply ground_comm_one].
Qed.

Lemma U_comm_T0_data0 : U comm_T0 comm_data0.
Proof.
  split.
  - exists [2].
    unfold comm_T0.
    eapply sub_tuple_child; [reflexivity | constructor].
  - apply ground_comm_data0.
Qed.

Lemma U_comm_T0_one : U comm_T0 comm_one.
Proof.
  split.
  - exists [2; 1; 0].
    unfold comm_T0, comm_data0, comm_add.
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_usr_child; [reflexivity | constructor].
  - apply ground_comm_one.
Qed.

Lemma U_comm_T0_two : U comm_T0 comm_two.
Proof.
  split.
  - exists [2; 1; 1].
    unfold comm_T0, comm_data0, comm_add.
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_usr_child; [reflexivity | constructor].
  - apply ground_comm_two.
Qed.

Lemma U_comm_T1_add_one_two : U comm_T1 (comm_add comm_one comm_two).
Proof.
  split.
  - exists [2; 1].
    unfold comm_T1, comm_data1.
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_tuple_child; [reflexivity | constructor].
  - apply ground_comm_add; [apply ground_comm_one | apply ground_comm_two].
Qed.

Lemma U_comm_T1_add_two_one : U comm_T1 (comm_add comm_two comm_one).
Proof.
  split.
  - exists [2; 2; 1].
    unfold comm_T1, comm_data1.
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_equiv_r; constructor.
  - apply ground_comm_add; [apply ground_comm_two | apply ground_comm_one].
Qed.

Lemma U_comm_T1_simp : U comm_T1 comm_simp.
Proof.
  split.
  - exists [1; 1].
    unfold comm_T1, comm_Rsimp, comm_Rsimp_rhs.
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_rewrite_r; constructor.
  - apply ground_comm_simp.
Qed.

Lemma comm_Rgen_rule_in_T0 :
  RuleOf comm_T0 [0] comm_Rgen_lhs comm_Rgen_rhs.
Proof.
  unfold RuleOf, comm_T0, comm_Rgen.
  eapply sub_tuple_child; [reflexivity | constructor].
Qed.

Lemma comm_Rsimp_rule_in_T1 :
  RuleOf comm_T1 [1] comm_Rsimp_lhs comm_Rsimp_rhs.
Proof.
  unfold RuleOf, comm_T1, comm_Rsimp.
  eapply sub_tuple_child; [reflexivity | constructor].
Qed.

Lemma comm_data0_at_T0 :
  SubAt comm_T0 [2] comm_data0.
Proof.
  unfold comm_T0.
  eapply sub_tuple_child; [reflexivity | constructor].
Qed.

Lemma comm_add_one_two_at_T1 :
  SubAt comm_T1 [2; 1] (comm_add comm_one comm_two).
Proof.
  unfold comm_T1, comm_data1.
  eapply sub_tuple_child; [reflexivity |].
  eapply sub_tuple_child; [reflexivity | constructor].
Qed.

Lemma comm_sigma_gen_ground_subst :
  GroundSubst comm_T0 comm_sigma_gen.
Proof.
  constructor.
  - intros [|[|x]] g H; simpl in H; inversion H; subst.
    + apply ground_comm_one.
    + apply ground_comm_two.
  - intros [|[|x]] g H; simpl in H; inversion H; subst.
    + apply U_comm_T0_one.
    + apply U_comm_T0_two.
Qed.

Lemma comm_Rgen_lhs_fv_cases :
  forall x, FV x comm_Rgen_lhs -> x = 0 \/ x = 1.
Proof.
  intros x Hfv.
  unfold comm_Rgen_lhs in Hfv.
  inversion Hfv as
    [x0
    | x0 f args t Hin Ht
    | x0 s t Hs
    | x0 s t Ht
    | x0 l r Hl
    | x0 l r Hr
    | x0 args t Hin Ht]; subst; clear Hfv.
  simpl in Hin.
  destruct Hin as [Ht_eq | [Ht_eq | []]]; subst.
  - exfalso.
    exact (ground_comm_declare Ht).
  - unfold comm_add in *.
    inversion Ht as
      [y
      | y f args0 t0 Hin0 Ht0
      | y s u Hs
      | y s u Hu
      | y l r Hl
      | y l r Hr
      | y args0 t0 Hin0 Ht0]; subst; clear Ht.
    simpl in Hin0.
    destruct Hin0 as [Ht_eq | [Ht_eq | []]]; subst.
    + inversion Ht0; subst. left; reflexivity.
    + inversion Ht0; subst. right; reflexivity.
Qed.

Lemma comm_sigma_gen_domain :
  subst_domain_exact comm_sigma_gen comm_Rgen_lhs.
Proof.
  unfold subst_domain_exact.
  intro x; split.
  - intro Hfv.
    unfold comm_sigma_gen.
    destruct (comm_Rgen_lhs_fv_cases Hfv) as [Hx | Hx]; subst.
    + exists comm_one. reflexivity.
    + exists comm_two. reflexivity.
  - intros [g Hg].
    unfold comm_sigma_gen in Hg.
    destruct x as [|[|x]]; simpl in Hg.
    + inversion Hg; subst.
      unfold comm_Rgen_lhs.
      eapply fv_tuple.
      * simpl; right; left; reflexivity.
      * unfold comm_add. eapply fv_usr.
        -- simpl; left; reflexivity.
        -- apply fv_var.
    + inversion Hg; subst.
      unfold comm_Rgen_lhs.
      eapply fv_tuple.
      * simpl; right; left; reflexivity.
      * unfold comm_add. eapply fv_usr.
        -- simpl; right; left; reflexivity.
        -- apply fv_var.
    + discriminate Hg.
Qed.

Lemma comm_subst_Rgen_lhs :
  SubstRel comm_sigma_gen comm_Rgen_lhs comm_data0.
Proof.
  unfold comm_Rgen_lhs, comm_data0, comm_add.
  apply sub_tuple.
  constructor.
  - unfold comm_declare. apply sub_usr. constructor.
  - constructor.
    + apply sub_usr.
      constructor.
      * apply sub_var_hit; [reflexivity | apply ground_comm_one].
      * constructor.
        -- apply sub_var_hit; [reflexivity | apply ground_comm_two].
        -- constructor.
    + constructor.
Qed.

Lemma comm_subst_Rgen_rhs :
  SubstRel comm_sigma_gen comm_Rgen_rhs comm_data1.
Proof.
  unfold comm_Rgen_rhs, comm_data1, comm_add.
  apply sub_tuple.
  constructor.
  - unfold comm_declare. apply sub_usr. constructor.
  - constructor.
    + apply sub_usr.
      constructor.
      * apply sub_var_hit; [reflexivity | apply ground_comm_one].
      * constructor.
        -- apply sub_var_hit; [reflexivity | apply ground_comm_two].
        -- constructor.
    + constructor.
      * apply sub_equiv.
        -- apply sub_usr.
           constructor.
           ++ apply sub_var_hit; [reflexivity | apply ground_comm_one].
           ++ constructor.
              ** apply sub_var_hit; [reflexivity | apply ground_comm_two].
              ** constructor.
        -- apply sub_usr.
           constructor.
           ++ apply sub_var_hit; [reflexivity | apply ground_comm_two].
           ++ constructor.
              ** apply sub_var_hit; [reflexivity | apply ground_comm_one].
              ** constructor.
      * constructor.
Qed.

Lemma comm_DRMatch_gen :
  DRMatch comm_T0 comm_Rgen_lhs comm_data0 comm_sigma_gen comm_data0.
Proof.
  refine {| drm_ground_subst := comm_sigma_gen_ground_subst;
            drm_domain := comm_sigma_gen_domain;
            drm_subst := comm_subst_Rgen_lhs;
            drm_image_in_U := U_comm_T0_data0;
            drm_cong := dyn_refl U_comm_T0_data0 |}.
Qed.

Lemma comm_replace_T0_data :
  ReplaceAt comm_T0 [2] comm_data1 comm_T1.
Proof.
  unfold comm_T0, comm_T1.
  eapply replace_tuple_child.
  - reflexivity.
  - constructor.
  - apply replace_nth_next.
    apply replace_nth_next.
    apply replace_nth_here.
Qed.

Theorem comm_first_raw_step :
  RawStep comm_T0 comm_T1.
Proof.
  eapply raw_step_intro
    with (rule_pos := [0])
         (app_pos := [2])
         (lhs := comm_Rgen_lhs)
         (rhs := comm_Rgen_rhs)
         (target := comm_data0)
         (sigma := comm_sigma_gen)
         (lhs_image := comm_data0)
         (rhs_image := comm_data1).
  - apply comm_Rgen_rule_in_T0.
  - apply comm_data0_at_T0.
  - apply U_comm_T0_data0.
  - apply comm_DRMatch_gen.
  - apply comm_subst_Rgen_rhs.
  - apply ground_comm_data1.
  - apply comm_replace_T0_data.
Qed.

Lemma comm_sigma_empty_ground_subst :
  GroundSubst comm_T1 comm_sigma_empty.
Proof.
  constructor; intros x g H; inversion H.
Qed.

Lemma comm_Rsimp_lhs_ground : Ground comm_Rsimp_lhs.
Proof.
  unfold comm_Rsimp_lhs.
  apply ground_comm_add; [apply ground_comm_two | apply ground_comm_one].
Qed.

Lemma comm_sigma_empty_domain :
  subst_domain_exact comm_sigma_empty comm_Rsimp_lhs.
Proof.
  unfold subst_domain_exact, comm_sigma_empty.
  intros x; split.
  - intros Hfv. exfalso. exact (comm_Rsimp_lhs_ground Hfv).
  - intros [g Hg]. discriminate Hg.
Qed.

Lemma comm_subst_Rsimp_lhs :
  SubstRel comm_sigma_empty comm_Rsimp_lhs comm_Rsimp_lhs.
Proof.
  apply sub_ground_none.
  - apply comm_Rsimp_lhs_ground.
  - reflexivity.
Qed.

Lemma comm_subst_Rsimp_rhs :
  SubstRel comm_sigma_empty comm_Rsimp_rhs comm_simp.
Proof.
  unfold comm_Rsimp_rhs.
  apply sub_ground_none.
  - apply ground_comm_simp.
  - reflexivity.
Qed.

Lemma comm_base_equiv_T1 :
  BaseEq comm_T1 (comm_add comm_one comm_two) (comm_add comm_two comm_one).
Proof.
  split.
  - exists [2; 2].
    unfold comm_T1, comm_data1.
    eapply sub_tuple_child; [reflexivity |].
    eapply sub_tuple_child; [reflexivity | constructor].
  - split.
    + apply ground_comm_add; [apply ground_comm_one | apply ground_comm_two].
    + apply ground_comm_add; [apply ground_comm_two | apply ground_comm_one].
Qed.

Lemma comm_dyn_cong_for_simp :
  DynCong comm_T1 (comm_add comm_two comm_one) (comm_add comm_one comm_two).
Proof.
  split; [apply U_comm_T1_add_two_one |].
  split; [apply U_comm_T1_add_one_two |].
  intros C HC.
  apply (@cp_sym comm_T1 C HC).
  apply (@cp_base comm_T1 C HC).
  apply comm_base_equiv_T1.
Qed.

Lemma comm_DRMatch_simp :
  DRMatch comm_T1 comm_Rsimp_lhs (comm_add comm_one comm_two)
    comm_sigma_empty comm_Rsimp_lhs.
Proof.
  refine {| drm_ground_subst := comm_sigma_empty_ground_subst;
            drm_domain := comm_sigma_empty_domain;
            drm_subst := comm_subst_Rsimp_lhs;
            drm_image_in_U := U_comm_T1_add_two_one;
            drm_cong := comm_dyn_cong_for_simp |}.
Qed.

Lemma comm_replace_T1_add :
  ReplaceAt comm_T1 [2; 1] comm_simp comm_T2.
Proof.
  unfold comm_T1, comm_T2, comm_data1, comm_data2.
  eapply replace_tuple_child.
  - reflexivity.
  - eapply replace_tuple_child.
    + reflexivity.
    + constructor.
    + apply replace_nth_next.
      apply replace_nth_here.
  - apply replace_nth_next.
    apply replace_nth_next.
    apply replace_nth_here.
Qed.

Theorem comm_second_raw_step :
  RawStep comm_T1 comm_T2.
Proof.
  eapply raw_step_intro
    with (rule_pos := [1])
         (app_pos := [2; 1])
         (lhs := comm_Rsimp_lhs)
         (rhs := comm_Rsimp_rhs)
         (target := comm_add comm_one comm_two)
         (sigma := comm_sigma_empty)
         (lhs_image := comm_Rsimp_lhs)
         (rhs_image := comm_simp).
  - apply comm_Rsimp_rule_in_T1.
  - apply comm_add_one_two_at_T1.
  - apply U_comm_T1_add_one_two.
  - apply comm_DRMatch_simp.
  - apply comm_subst_Rsimp_rhs.
  - apply ground_comm_simp.
  - apply comm_replace_T1_add.
Qed.

Definition NoRewrite (t : Term) : Prop :=
  forall p l r, SubAt t p (TRewrite l r) -> False.

Lemma no_rewrite_usr :
  forall f args, Forall NoRewrite args -> NoRewrite (TUsr f args).
Proof.
  unfold NoRewrite.
  intros f args Hargs p l r Hsub.
  inversion Hsub; subst; try discriminate.
  rewrite Forall_forall in Hargs.
  eapply Hargs.
  - eapply nth_error_in_term; eauto.
  - eauto.
Qed.

Lemma no_rewrite_equiv :
  forall s t, NoRewrite s -> NoRewrite t -> NoRewrite (TEquiv s t).
Proof.
  unfold NoRewrite.
  intros s t Hs Ht p l r Hsub.
  inversion Hsub; subst; try discriminate; eauto.
Qed.

Lemma no_rewrite_tuple :
  forall args, Forall NoRewrite args -> NoRewrite (TTuple args).
Proof.
  unfold NoRewrite.
  intros args Hargs p l r Hsub.
  inversion Hsub; subst; try discriminate.
  rewrite Forall_forall in Hargs.
  eapply Hargs.
  - eapply nth_error_in_term; eauto.
  - eauto.
Qed.

Lemma no_rewrite_comm_one : NoRewrite comm_one.
Proof. unfold comm_one; apply no_rewrite_usr; constructor. Qed.

Lemma no_rewrite_comm_two : NoRewrite comm_two.
Proof. unfold comm_two; apply no_rewrite_usr; constructor. Qed.

Lemma no_rewrite_comm_simp : NoRewrite comm_simp.
Proof. unfold comm_simp; apply no_rewrite_usr; constructor. Qed.

Lemma no_rewrite_comm_declare : NoRewrite comm_declare.
Proof. unfold comm_declare; apply no_rewrite_usr; constructor. Qed.

Lemma no_rewrite_comm_add :
  forall a b, NoRewrite a -> NoRewrite b -> NoRewrite (comm_add a b).
Proof.
  intros a b Ha Hb.
  unfold comm_add.
  apply no_rewrite_usr.
  repeat constructor; assumption.
Qed.

Lemma no_rewrite_comm_Rgen_lhs : NoRewrite comm_Rgen_lhs.
Proof.
  unfold comm_Rgen_lhs.
  apply no_rewrite_tuple.
  repeat constructor.
  - apply no_rewrite_comm_declare.
  - apply no_rewrite_comm_add; unfold NoRewrite; intros p l r H; inversion H.
Qed.

Lemma no_rewrite_comm_Rgen_rhs : NoRewrite comm_Rgen_rhs.
Proof.
  unfold comm_Rgen_rhs.
  apply no_rewrite_tuple.
  repeat constructor.
  - apply no_rewrite_comm_declare.
  - apply no_rewrite_comm_add; unfold NoRewrite; intros p l r H; inversion H.
  - apply no_rewrite_equiv;
      apply no_rewrite_comm_add; unfold NoRewrite; intros p l r H; inversion H.
Qed.

Lemma no_rewrite_comm_Rsimp_lhs : NoRewrite comm_Rsimp_lhs.
Proof.
  unfold comm_Rsimp_lhs.
  apply no_rewrite_comm_add; [apply no_rewrite_comm_two | apply no_rewrite_comm_one].
Qed.

Lemma no_rewrite_comm_Rsimp_rhs : NoRewrite comm_Rsimp_rhs.
Proof. unfold comm_Rsimp_rhs; apply no_rewrite_comm_simp. Qed.

Lemma no_rewrite_comm_data0 : NoRewrite comm_data0.
Proof.
  unfold comm_data0.
  apply no_rewrite_tuple.
  repeat constructor.
  - apply no_rewrite_comm_declare.
  - apply no_rewrite_comm_add; [apply no_rewrite_comm_one | apply no_rewrite_comm_two].
Qed.

Lemma no_rewrite_comm_data1 : NoRewrite comm_data1.
Proof.
  unfold comm_data1.
  apply no_rewrite_tuple.
  repeat constructor.
  - apply no_rewrite_comm_declare.
  - apply no_rewrite_comm_add; [apply no_rewrite_comm_one | apply no_rewrite_comm_two].
  - apply no_rewrite_equiv;
      apply no_rewrite_comm_add;
      [apply no_rewrite_comm_one | apply no_rewrite_comm_two
      | apply no_rewrite_comm_two | apply no_rewrite_comm_one].
Qed.

Lemma ground_comm_Rsimp : Ground comm_Rsimp.
Proof.
  unfold comm_Rsimp.
  apply ground_rewrite.
  - apply comm_Rsimp_lhs_ground.
  - unfold comm_Rsimp_rhs; apply ground_comm_simp.
Qed.

Lemma subat_rewrite_var_prefix :
  forall l r p x,
    SubAt (TRewrite l r) p (TVar x) ->
    exists j, (j = 0 \/ j = 1) /\ Prefix [j] p.
Proof.
  intros l r p x Hsub.
  inversion Hsub; subst; try discriminate.
  - exists 0. split; [left; reflexivity | constructor; constructor].
  - exists 1. split; [right; reflexivity | constructor; constructor].
Qed.

Lemma comm_tuple_scope_ok :
  forall data,
    Ground data ->
    variable_scope_ok (TTuple [comm_Rgen; comm_Rsimp; data]).
Proof.
  unfold variable_scope_ok.
  intros data Hdata x p Hvar.
  remember (TTuple [comm_Rgen; comm_Rsimp; data]) as Whole eqn:Hwhole.
  change (SubAt Whole p (TVar x)) in Hvar.
  inversion Hvar as
    [t0
    | f args i child p0 u Hnth Hchild
    | s t p0 u Hchild
    | s t p0 u Hchild
    | l r p0 u Hchild
    | l r p0 u Hchild
    | args i child p0 u Hnth Hchild]; subst; try discriminate.
  match goal with
  | Htuple : TTuple args = TTuple [comm_Rgen; comm_Rsimp; data] |- _ =>
      inversion Htuple; subst args; clear Htuple
  end.
  destruct i as [|i].
  - simpl in *.
    match goal with
    | Hnth : Some comm_Rgen = Some child |- _ =>
        inversion Hnth; subst child; clear Hnth
    end.
    unfold comm_Rgen in Hchild.
    destruct (subat_rewrite_var_prefix Hchild) as [j [Hj Hpre]].
    exists [0], j, comm_Rgen_lhs, comm_Rgen_rhs.
    split; [exact Hj |].
    split.
    + simpl. constructor. exact Hpre.
    + unfold comm_Rgen.
      eapply sub_tuple_child; [reflexivity | constructor].
  - destruct i as [|i].
    + simpl in *.
      match goal with
      | Hnth : Some comm_Rsimp = Some child |- _ =>
          inversion Hnth; subst child; clear Hnth
      end.
      exfalso.
      exact (ground_comm_Rsimp
        (subat_fv_lift Hchild (fv_var x))).
    + destruct i as [|i].
      * simpl in *.
        match goal with
        | Hnth : Some data = Some child |- _ =>
            inversion Hnth; subst child; clear Hnth
        end.
        exfalso.
        exact (Hdata x (subat_fv_lift Hchild (fv_var x))).
      * simpl in *.
        destruct i; discriminate Hnth.
Qed.

Lemma fv_comm_add_vars :
  forall x m n,
    FV x (comm_add (TVar m) (TVar n)) ->
    x = m \/ x = n.
Proof.
  intros x m n Hfv.
  unfold comm_add in Hfv.
  inversion Hfv as
    [y
    | y f args t Hin Ht
    | y s t Hs
    | y s t Ht'
    | y l r Hl
    | y l r Hr
    | y args t Hin Ht]; subst.
  simpl in Hin.
  destruct Hin as [Ht_eq | [Ht_eq | []]]; subst.
  - inversion Ht; subst. left; reflexivity.
  - inversion Ht; subst. right; reflexivity.
Qed.

Lemma comm_Rgen_lhs_has_var :
  forall x, x = 0 \/ x = 1 -> FV x comm_Rgen_lhs.
Proof.
  intros x Hx.
  destruct Hx as [Hx | Hx]; subst.
  - unfold comm_Rgen_lhs, comm_add.
    eapply fv_tuple.
    + simpl; right; left; reflexivity.
    + eapply fv_usr.
      * simpl; left; reflexivity.
      * apply fv_var.
  - unfold comm_Rgen_lhs, comm_add.
    eapply fv_tuple.
    + simpl; right; left; reflexivity.
    + eapply fv_usr.
      * simpl; right; left; reflexivity.
      * apply fv_var.
Qed.

Lemma comm_Rgen_rhs_fv_subset :
  FV_subset comm_Rgen_rhs comm_Rgen_lhs.
Proof.
  unfold FV_subset.
  intros x Hfv.
  unfold comm_Rgen_rhs in Hfv.
  inversion Hfv as
    [y
    | y f args t Hin Ht
    | y s t Hs
    | y s t Ht'
    | y l r Hl
    | y l r Hr
    | y args t Hin Ht]; subst.
  simpl in Hin.
  destruct Hin as [Ht_eq | [Ht_eq | [Ht_eq | []]]]; subst.
  - exfalso. exact (ground_comm_declare Ht).
  - apply comm_Rgen_lhs_has_var.
    apply fv_comm_add_vars in Ht.
    exact Ht.
  - inversion Ht as
      [y
      | y f args0 t0 Hin0 Ht0
      | y s u Hleft
      | y s u Hright
      | y l r Hl
      | y l r Hr
      | y args0 t0 Hin0 Ht0]; subst.
    + apply comm_Rgen_lhs_has_var.
      apply fv_comm_add_vars in Hleft.
      exact Hleft.
    + apply comm_Rgen_lhs_has_var.
      apply fv_comm_add_vars in Hright.
      destruct Hright as [Hright | Hright]; subst;
        [right | left]; reflexivity.
Qed.

Lemma comm_Rsimp_rhs_fv_subset :
  FV_subset comm_Rsimp_rhs comm_Rsimp_lhs.
Proof.
  unfold FV_subset.
  intros x Hfv.
  exfalso.
  unfold comm_Rsimp_rhs in Hfv.
  exact (ground_comm_simp Hfv).
Qed.

Lemma comm_Rgen_rewrite_subterm :
  forall p l r,
    SubAt comm_Rgen p (TRewrite l r) ->
    p = [] /\ l = comm_Rgen_lhs /\ r = comm_Rgen_rhs.
Proof.
  intros p l r Hsub.
  unfold comm_Rgen in Hsub.
  inversion Hsub; subst; try discriminate.
  - repeat split; reflexivity.
  - exfalso.
    match goal with
    | H : SubAt comm_Rgen_lhs _ (TRewrite _ _) |- _ =>
        exact (no_rewrite_comm_Rgen_lhs H)
    end.
  - exfalso.
    match goal with
    | H : SubAt comm_Rgen_rhs _ (TRewrite _ _) |- _ =>
        exact (no_rewrite_comm_Rgen_rhs H)
    end.
Qed.

Lemma comm_Rsimp_rewrite_subterm :
  forall p l r,
    SubAt comm_Rsimp p (TRewrite l r) ->
    p = [] /\ l = comm_Rsimp_lhs /\ r = comm_Rsimp_rhs.
Proof.
  intros p l r Hsub.
  unfold comm_Rsimp in Hsub.
  inversion Hsub; subst; try discriminate.
  - repeat split; reflexivity.
  - exfalso.
    match goal with
    | H : SubAt comm_Rsimp_lhs _ (TRewrite _ _) |- _ =>
        exact (no_rewrite_comm_Rsimp_lhs H)
    end.
  - exfalso.
    match goal with
    | H : SubAt comm_Rsimp_rhs _ (TRewrite _ _) |- _ =>
        exact (no_rewrite_comm_Rsimp_rhs H)
    end.
Qed.

Lemma comm_tuple_rules_safe :
  forall data,
    NoRewrite data ->
    rules_safe (TTuple [comm_Rgen; comm_Rsimp; data]).
Proof.
  unfold rules_safe.
  intros data Hdata q l r Hrw.
  remember (TTuple [comm_Rgen; comm_Rsimp; data]) as Whole eqn:Hwhole.
  change (SubAt Whole q (TRewrite l r)) in Hrw.
  inversion Hrw as
    [t0
    | f args i child p0 u Hnth Hchild
    | s t p0 u Hchild
    | s t p0 u Hchild
    | l0 r0 p0 u Hchild
    | l0 r0 p0 u Hchild
    | args i child p0 u Hnth Hchild]; subst; try discriminate.
  match goal with
  | Htuple : TTuple args = TTuple [comm_Rgen; comm_Rsimp; data] |- _ =>
      inversion Htuple; subst args; clear Htuple
  end.
  destruct i as [|i].
  - simpl in *.
    match goal with
    | Hnth : Some comm_Rgen = Some child |- _ =>
        inversion Hnth; subst child; clear Hnth
    end.
    destruct (comm_Rgen_rewrite_subterm Hchild) as [_ [Hl Hr]].
    subst. apply comm_Rgen_rhs_fv_subset.
  - destruct i as [|i].
    + simpl in *.
      match goal with
      | Hnth : Some comm_Rsimp = Some child |- _ =>
          inversion Hnth; subst child; clear Hnth
      end.
      destruct (comm_Rsimp_rewrite_subterm Hchild) as [_ [Hl Hr]].
      subst. apply comm_Rsimp_rhs_fv_subset.
    + destruct i as [|i].
      * simpl in *.
        match goal with
        | Hnth : Some data = Some child |- _ =>
            inversion Hnth; subst child; clear Hnth
        end.
        exfalso. exact (Hdata p0 l r Hchild).
      * simpl in *.
        destruct i; discriminate Hnth.
Qed.

Lemma spec_comm_T0 : Spec comm_T0.
Proof.
  constructor.
  - unfold comm_T0.
    apply comm_tuple_scope_ok.
    apply ground_comm_data0.
  - unfold comm_T0.
    apply comm_tuple_rules_safe.
    apply no_rewrite_comm_data0.
Qed.

Lemma spec_comm_T1 : Spec comm_T1.
Proof.
  constructor.
  - unfold comm_T1.
    apply comm_tuple_scope_ok.
    apply ground_comm_data1.
  - unfold comm_T1.
    apply comm_tuple_rules_safe.
    apply no_rewrite_comm_data1.
Qed.

Theorem comm_first_stepM :
  StepM comm_T0 comm_T1.
Proof.
  exact (step_m_intro spec_comm_T0 comm_first_raw_step).
Qed.

Theorem comm_second_stepM :
  StepM comm_T1 comm_T2.
Proof.
  exact (step_m_intro spec_comm_T1 comm_second_raw_step).
Qed.

Record dynamic_commutativity_witness : Type := {
  comm_witness_T0 : Term;
  comm_witness_T1 : Term;
  comm_witness_T2 : Term;
  comm_witness_first : RawStep comm_witness_T0 comm_witness_T1;
  comm_witness_second : RawStep comm_witness_T1 comm_witness_T2
}.

Theorem dynamic_commutativity_raw_witness :
  dynamic_commutativity_witness.
Proof.
  refine {| comm_witness_T0 := comm_T0;
            comm_witness_T1 := comm_T1;
            comm_witness_T2 := comm_T2;
            comm_witness_first := comm_first_raw_step;
            comm_witness_second := comm_second_raw_step |}.
Qed.

Record dynamic_commutativity_stepM_witness : Type := {
  comm_stepM_witness_T0 : Term;
  comm_stepM_witness_T1 : Term;
  comm_stepM_witness_T2 : Term;
  comm_stepM_witness_first : StepM comm_stepM_witness_T0 comm_stepM_witness_T1;
  comm_stepM_witness_second : StepM comm_stepM_witness_T1 comm_stepM_witness_T2
}.

Theorem dynamic_commutativity_stepM_witness_exists :
  dynamic_commutativity_stepM_witness.
Proof.
  refine {| comm_stepM_witness_T0 := comm_T0;
            comm_stepM_witness_T1 := comm_T1;
            comm_stepM_witness_T2 := comm_T2;
            comm_stepM_witness_first := comm_first_stepM;
            comm_stepM_witness_second := comm_second_stepM |}.
Qed.

Definition HasOneStepSimulation : Prop :=
  forall M c c',
    CM_step M c c' ->
    exists T T', Step T T'.

Theorem counter_machine_one_step_simulation : HasOneStepSimulation.
Proof.
  intros M c c' H.
  exists (machine_step_term c c'), (machine_step_term_next c c').
  eapply step_intro.
  - apply ground_spec.
    apply ground_machine_step_term.
  - eapply raw_step_intro
      with (rule_pos := [0])
           (app_pos := [1])
           (lhs := config_term c)
           (rhs := config_term c')
           (target := config_term c)
           (sigma := fun _ => None)
           (lhs_image := config_term c)
           (rhs_image := config_term c').
    + unfold RuleOf, machine_step_term, machine_rule_term.
      eapply sub_tuple_child.
      * reflexivity.
      * constructor.
    + unfold machine_step_term.
      eapply sub_tuple_child.
      * reflexivity.
      * constructor.
    + split.
      * unfold machine_step_term.
        exists [1].
        eapply sub_tuple_child; [reflexivity | constructor].
      * apply ground_config.
    + refine {| drm_ground_subst := _;
                drm_domain := _;
                drm_subst := _;
                drm_image_in_U := _;
                drm_cong := _ |}.
      * constructor; intros x g Hnone; discriminate Hnone.
      * intros x; split.
        -- intros Hfv. exfalso. exact (@ground_config c x Hfv).
        -- intros [g Hg]; discriminate Hg.
      * apply sub_ground_none.
        -- apply ground_config.
        -- reflexivity.
      * split.
        -- unfold machine_step_term.
           exists [1].
           eapply sub_tuple_child; [reflexivity | constructor].
        -- apply ground_config.
      * apply dyn_refl.
        split.
        -- unfold machine_step_term.
           exists [1].
           eapply sub_tuple_child; [reflexivity | constructor].
        -- apply ground_config.
    + apply sub_ground_none.
      * apply ground_config.
      * reflexivity.
    + apply ground_config.
    + unfold machine_step_term, machine_step_term_next.
      eapply replace_tuple_child.
      * reflexivity.
      * constructor.
      * apply replace_nth_next.
        apply replace_nth_here.
  - apply ground_spec.
    apply ground_machine_step_term_next.
Qed.

Definition HasOneStepSimulationM : Prop :=
  forall M c c',
    CM_step M c c' ->
    exists T T', StepM T T'.

Theorem counter_machine_one_step_simulation_source : HasOneStepSimulationM.
Proof.
  intros M c c' Hstep.
  destruct (@counter_machine_one_step_simulation M c c' Hstep) as [T [T' Hcert]].
  exists T, T'.
  exact (certified_step_is_stepM Hcert).
Qed.

Definition TuringCompleteCapacity : Prop := HasOneStepSimulation.

Theorem turing_complete_capacity : TuringCompleteCapacity.
Proof.
  exact counter_machine_one_step_simulation.
Qed.

Definition TuringCompleteCapacityM : Prop := HasOneStepSimulationM.

Theorem turing_complete_capacity_source : TuringCompleteCapacityM.
Proof.
  exact counter_machine_one_step_simulation_source.
Qed.

Record MSystem : Type := {
  ms_system_marker : unit;
  ms_var : Type := nat;
  ms_user_symbol : Type := nat;
  ms_user_arity : nat -> nat;
  ms_term : Type := Term;
  ms_term_arity_ok : Term -> Prop := TermArityOK ms_user_arity;
  ms_ground : Term -> Prop := Ground;
  ms_fv : nat -> Term -> Prop := FV;
  ms_substitution : (nat -> option Term) -> Term -> Term -> Prop := SubstRel;
  ms_alpha_equiv : Term -> Term -> Prop := alpha_equiv;
  ms_position : Type := list nat;
  ms_subat : Term -> list nat -> Term -> Prop := SubAt;
  ms_replace_at : Term -> list nat -> Term -> Term -> Prop := ReplaceAt;
  ms_subterm : Term -> Term -> Prop := Subterm;
  ms_ground_subterm : Term -> Term -> Prop := GroundSub;
  ms_spec : Term -> Prop := Spec;
  ms_rule_set : Term -> list nat -> Term -> Term -> Prop := RuleOf;
  ms_base_eq : Term -> Term -> Term -> Prop := BaseEq;
  ms_domain : Term -> Term -> Prop := U;
  ms_dyn_cong : Term -> Term -> Term -> Prop := DynCong;
  ms_dyn_cong_decidable :
    forall T a b, Spec T -> U T a -> U T b -> Decidable (DynCong T a b)
    := dynamic_congruence_decidable;
  ms_match :
    Term -> Term -> Term -> (nat -> option Term) -> Term -> Prop := DRMatch;
  ms_match_decidable :
    forall T l a, Spec T -> U T a ->
      Decidable (exists sigma sl, DRMatch T l a sigma sl)
    := drmatch_decidable;
  ms_raw_step : Term -> Term -> Prop := RawStep;
  ms_step : Term -> Term -> Prop := StepM;
  ms_certified_step : Term -> Term -> Prop := Step;
  ms_step_preserves_spec :
    forall T T', StepM T T' -> Spec T'
    := stepM_preserves_spec;
  ms_nf : Term -> Prop := NF;
  ms_nf_decidable : forall T, Spec T -> Decidable (NF T)
    := normal_form_decidable;
  ms_dynamic_commutativity_witness : dynamic_commutativity_stepM_witness
    := dynamic_commutativity_stepM_witness_exists;
  ms_counter_machine_one_step_simulation : HasOneStepSimulationM
    := counter_machine_one_step_simulation_source;
  ms_turing_complete_capacity : TuringCompleteCapacityM
    := turing_complete_capacity_source
}.

End ReflectiveComputationM42.
