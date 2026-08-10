From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Lia.

Import ListNotations.

Module CIE78.

Inductive term : Type :=
| Var : nat -> term
| Op : nat -> list term -> term
| Equiv : term -> term -> term
| Pair : term -> term -> term
| Unit : term.

Definition VarSigma : Type := nat.
Definition SigmaUsr : Type := nat.
Definition user_arity : Type := SigmaUsr -> nat.

Inductive TermArityOK (ar_usr : user_arity) : term -> Prop :=
| TA_Var :
    forall n, TermArityOK ar_usr (Var n)
| TA_Op :
    forall f args,
      length args = ar_usr f ->
      Forall (TermArityOK ar_usr) args ->
      TermArityOK ar_usr (Op f args)
| TA_Equiv :
    forall s t,
      TermArityOK ar_usr s ->
      TermArityOK ar_usr t ->
      TermArityOK ar_usr (Equiv s t)
| TA_Pair :
    forall s t,
      TermArityOK ar_usr s ->
      TermArityOK ar_usr t ->
      TermArityOK ar_usr (Pair s t)
| TA_Unit :
      TermArityOK ar_usr Unit.

Definition context := list (term * term).
Definition subst_env := list (nat * term).

Fixpoint lookup (x : nat) (theta : subst_env) : option term :=
  match theta with
  | [] => None
  | (y, t) :: rest => if Nat.eq_dec x y then Some t else lookup x rest
  end.

Fixpoint fv (t : term) : list nat :=
  match t with
  | Var n => [n]
  | Op _ args => fold_right (fun u acc => fv u ++ acc) [] args
  | Equiv s u => fv s ++ fv u
  | Pair s u => fv s ++ fv u
  | Unit => []
  end.

Fixpoint term_size (t : term) : nat :=
  match t with
  | Var _ => 1
  | Op _ args =>
      1 + fold_right (fun u acc => term_size u + acc) 0 args
  | Equiv s u => 1 + term_size s + term_size u
  | Pair s u => 1 + term_size s + term_size u
  | Unit => 1
  end.

Lemma term_size_in_args_lt :
  forall f args u,
    In u args ->
    term_size u < term_size (Op f args).
Proof.
  intros f args u Hu.
  induction args as [|a args IH]; simpl in Hu.
  - contradiction.
  - simpl.
    destruct Hu as [Hu | Hu].
    + subst. lia.
    + specialize (IH Hu). simpl in IH. lia.
Qed.

Definition subset_nat (xs ys : list nat) : Prop :=
  forall x, In x xs -> In x ys.

Definition ground (t : term) : Prop :=
  forall x, In x (fv t) -> False.

Definition GTermSigma (ar_usr : user_arity) (t : term) : Prop :=
  TermArityOK ar_usr t /\ ground t.

Definition pattern_axiom (l r : term) : Prop :=
  exists x, In x (fv l ++ fv r).

Definition ground_subst (theta : subst_env) : Prop :=
  forall x v, lookup x theta = Some v -> ground v.

Definition covers (theta : subst_env) (t : term) : Prop :=
  forall x, In x (fv t) -> exists v, lookup x theta = Some v.

Fixpoint subst (t : term) (theta : subst_env) : term :=
  match t with
  | Var n =>
      match lookup n theta with
      | Some u => u
      | None => Var n
      end
  | Op f args => Op f (map (fun u => subst u theta) args)
  | Equiv s u => Equiv (subst s theta) (subst u theta)
  | Pair s u => Pair (subst s theta) (subst u theta)
  | Unit => Unit
  end.

Inductive subst_rel (theta : subst_env) : term -> term -> Prop :=
| SRVarHit :
    forall x u,
      lookup x theta = Some u ->
      subst_rel theta (Var x) u
| SRVarMiss :
    forall x,
      lookup x theta = None ->
      subst_rel theta (Var x) (Var x)
| SROp :
    forall f args args',
      Forall2 (subst_rel theta) args args' ->
      subst_rel theta (Op f args) (Op f args')
| SREquiv :
    forall s s' t t',
      subst_rel theta s s' ->
      subst_rel theta t t' ->
      subst_rel theta (Equiv s t) (Equiv s' t')
| SRPair :
    forall s s' t t',
      subst_rel theta s s' ->
      subst_rel theta t t' ->
      subst_rel theta (Pair s t) (Pair s' t')
| SRUnit :
      subst_rel theta Unit Unit.

Fixpoint tuple_encode (xs : list term) : term :=
  match xs with
  | [] => Unit
  | x :: rest => Pair x (tuple_encode rest)
  end.

Theorem tuple_encode_injective :
  forall xs ys, tuple_encode xs = tuple_encode ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros H.
  - reflexivity.
  - discriminate H.
  - discriminate H.
  - injection H as Hxy Htail. subst y. f_equal. now apply IH.
Qed.

Fixpoint subterms (t : term) : list term :=
  match t with
  | Var _ => [t]
  | Op _ args => t :: flat_map subterms args
  | Equiv s u => t :: subterms s ++ subterms u
  | Pair s u => t :: subterms s ++ subterms u
  | Unit => [Unit]
  end.

Definition EGT (t : term) : list term :=
  filter (fun u => if Nat.eq_dec (length (fv u)) 0 then true else false) (subterms t).

Definition ground_subterm (g t : term) : Prop :=
  In g (subterms t) /\ ground g.

Definition Sub (s t : term) : Prop := In s (subterms t).

Lemma in_fv_op_args :
  forall x args,
    In x (fold_right (fun u acc => fv u ++ acc) [] args) <->
    exists u, In u args /\ In x (fv u).
Proof.
  intros x args.
  induction args as [|a args IH]; simpl.
  - split.
    + intros H. contradiction.
    + intros [u [Hin _]]. contradiction.
  - rewrite in_app_iff, IH.
    split.
    + intros [Hin | [u [Hu Hx]]].
      * exists a. split; [left; reflexivity | exact Hin].
      * exists u. split; [right; exact Hu | exact Hx].
    + intros [u [[Hu | Hu] Hx]].
      * subst u. left; exact Hx.
      * right. exists u. split; assumption.
Qed.

Lemma ground_op_args :
  forall f args,
    Forall ground args ->
    ground (Op f args).
Proof.
  intros f args Hall x Hx.
  simpl in Hx.
  apply in_fv_op_args in Hx as [u [Hu Hxu]].
  rewrite Forall_forall in Hall.
  exact (Hall u Hu x Hxu).
Qed.

Theorem subst_rel_ground_when_covered :
  forall theta r r',
    subst_rel theta r r' ->
    covers theta r ->
    ground_subst theta ->
    ground r'.
Proof.
  fix IH 4.
  intros theta r r' Hsub Hcov Hground.
  destruct Hsub.
  - eapply Hground; exact H.
  - exfalso.
    destruct (Hcov x (or_introl eq_refl)) as [v Hv].
    rewrite H in Hv. discriminate Hv.
  - apply ground_op_args.
    induction H as [|a a' args args' Ha Htail IHtail].
    + constructor.
    + constructor.
      * apply (IH theta a a'); [exact Ha | | exact Hground].
        intros x Hx.
        apply Hcov.
        simpl. apply in_or_app. left; exact Hx.
      * apply IHtail.
        intros x Hx.
        apply Hcov.
        simpl. apply in_or_app. right; exact Hx.
  - unfold ground. simpl.
    intros x Hx. apply in_app_or in Hx as [Hx | Hx].
    + exact (IH theta s s' Hsub1
                (fun y Hy => Hcov y (in_or_app (fv s) (fv t) y (or_introl Hy)))
                Hground x Hx).
    + exact (IH theta t t' Hsub2
                (fun y Hy => Hcov y (in_or_app (fv s) (fv t) y (or_intror Hy)))
                Hground x Hx).
  - unfold ground. simpl.
    intros x Hx. apply in_app_or in Hx as [Hx | Hx].
    + exact (IH theta s s' Hsub1
                (fun y Hy => Hcov y (in_or_app (fv s) (fv t) y (or_introl Hy)))
                Hground x Hx).
    + exact (IH theta t t' Hsub2
                (fun y Hy => Hcov y (in_or_app (fv s) (fv t) y (or_intror Hy)))
                Hground x Hx).
  - unfold ground. simpl. contradiction.
Qed.

Lemma subst_rel_subst :
  forall theta t,
    subst_rel theta t (subst t theta).
Proof.
  fix IH 2.
  intros theta t.
  destruct t as [x | f args | s t | s t |].
  - simpl. destruct (lookup x theta) eqn:Hlookup.
    + apply SRVarHit. exact Hlookup.
    + apply SRVarMiss. exact Hlookup.
  - simpl. apply SROp.
    induction args as [|a args IHargs].
    + constructor.
    + simpl. constructor.
      * apply IH.
      * apply IHargs.
  - simpl. apply SREquiv; apply IH.
  - simpl. apply SRPair; apply IH.
  - simpl. apply SRUnit.
Qed.

Theorem subst_ground_when_covered :
  forall theta r,
    covers theta r ->
    ground_subst theta ->
    ground (subst r theta).
Proof.
  intros theta r Hcov Hground.
  eapply subst_rel_ground_when_covered.
  - apply subst_rel_subst.
  - exact Hcov.
  - exact Hground.
Qed.

Theorem EGT_spec :
  forall g t,
    In g (EGT t) -> ground_subterm g t.
Proof.
  intros g t H.
  unfold EGT in H. apply filter_In in H as [Hin Hlen].
  split; auto. unfold ground. intros x Hx.
  destruct (Nat.eq_dec (length (fv g)) 0) as [E | E]; try discriminate.
  destruct (fv g) as [|y ys]; simpl in E; try discriminate.
  exact Hx.
Qed.

Lemma ground_fv_nil :
  forall t,
    ground t ->
    fv t = [].
Proof.
  intros t Hground.
  destruct (fv t) as [|x xs] eqn:E.
  - reflexivity.
  - exfalso. apply (Hground x). rewrite E. left; reflexivity.
Qed.

Theorem EGT_spec_iff :
  forall g t,
    In g (EGT t) <-> ground_subterm g t.
Proof.
  intros g t. split.
  - apply EGT_spec.
  - intros [Hin Hg].
    unfold EGT.
    apply filter_In. split; [exact Hin |].
    rewrite (ground_fv_nil g Hg).
    destruct (Nat.eq_dec 0 0) as [_ | Hneq].
    + reflexivity.
    + contradiction Hneq; reflexivity.
Qed.

Lemma EGT_Forall_ground :
  forall t,
    Forall ground (EGT t).
Proof.
  intros t.
  apply Forall_forall.
  intros g Hg.
  apply EGT_spec in Hg as [_ Hground].
  exact Hground.
Qed.

Inductive derivable : context -> term -> term -> Prop :=
| DRefl :
    forall Gamma t,
      derivable Gamma t t
| DSym :
    forall Gamma s t,
      derivable Gamma s t ->
      derivable Gamma t s
| DTrans :
    forall Gamma s t u,
      derivable Gamma s t ->
      derivable Gamma t u ->
      derivable Gamma s u
| DCongOp :
    forall Gamma f ss ts,
      Forall2 (derivable Gamma) ss ts ->
      derivable Gamma (Op f ss) (Op f ts)
| DCongEquiv :
    forall Gamma s1 s2 t1 t2,
      derivable Gamma s1 s2 ->
      derivable Gamma t1 t2 ->
      derivable Gamma (Equiv s1 t1) (Equiv s2 t2)
| DCongPair :
    forall Gamma s1 s2 t1 t2,
      derivable Gamma s1 s2 ->
      derivable Gamma t1 t2 ->
      derivable Gamma (Pair s1 t1) (Pair s2 t2)
| DLocal :
    forall Gamma l r,
      In (l, r) Gamma ->
      ground l ->
      ground r ->
      derivable Gamma l r
| DPattern :
    forall Gamma l r theta,
      In (l, r) Gamma ->
      pattern_axiom l r ->
      derivable Gamma (subst l theta) (subst r theta)
| DEquivIntro :
    forall Gamma t1 t2 s1 s2,
      derivable ((t1, t2) :: Gamma) s1 s2 ->
      derivable ((s1, s2) :: Gamma) t1 t2 ->
      derivable Gamma (Equiv t1 t2) (Equiv s1 s2)
| DEquivElim :
    forall Gamma t1 t2,
      derivable Gamma (Equiv t1 t2) Unit ->
      derivable Gamma t1 t2
| DEquivReflect :
    forall Gamma t1 t2,
      derivable Gamma t1 t2 ->
      derivable Gamma (Equiv t1 t2) Unit
| DConcrete :
    forall Gamma t,
      derivable Gamma t (Equiv t Unit).

Theorem object_reflection :
  forall Gamma s t,
    derivable Gamma s t <-> derivable Gamma (Equiv s t) Unit.
Proof.
  intros Gamma s t. split.
  - apply DEquivReflect.
  - apply DEquivElim.
Qed.

Theorem concretization :
  forall Gamma t, derivable Gamma t (Equiv t Unit).
Proof.
  intros Gamma t. apply DConcrete.
Qed.

Definition Jud : Type := term * term.
Definition Rule_CIE : context -> term -> term -> Prop := derivable.

Fixpoint gamma (C : term) : context :=
  match C with
  | Var _ => []
  | Op _ args => flat_map gamma args
  | Equiv s t => (s, t) :: gamma s ++ gamma t
  | Pair s t => gamma s ++ gamma t
  | Unit => []
  end.

Definition base_eq (Gamma : context) (U : list term) (a b : term) : Prop :=
  (In (a, b) Gamma /\ ground a /\ ground b) \/
  exists l r theta,
    In (l, r) Gamma /\
    pattern_axiom l r /\
    covers theta l /\
    ground_subst theta /\
    Forall (fun v => In v U) (map snd theta) /\
    a = subst l theta /\
    b = subst r theta.

Definition GammaC (C : term) : context := gamma C.

Definition E_C_U (C : term) (U : list term) (a b : term) : Prop :=
  base_eq (gamma C) U a b.

Inductive op_congruent (Gamma : context) (U : list term) : term -> term -> Prop :=
| OCBase :
    forall a b,
      base_eq Gamma U a b ->
      op_congruent Gamma U a b
| OCRefl :
    forall a,
      ground a ->
      op_congruent Gamma U a a
| OCSym :
    forall a b,
      op_congruent Gamma U a b ->
      op_congruent Gamma U b a
| OCTrans :
    forall a b c,
      op_congruent Gamma U a b ->
      op_congruent Gamma U b c ->
      op_congruent Gamma U a c
| OCCongOp :
    forall f xs ys,
      Forall2 (op_congruent Gamma U) xs ys ->
      op_congruent Gamma U (Op f xs) (Op f ys)
| OCCongEquiv :
    forall a b c d,
      op_congruent Gamma U a b ->
      op_congruent Gamma U c d ->
      op_congruent Gamma U (Equiv a c) (Equiv b d)
| OCCongPair :
    forall a b c d,
      op_congruent Gamma U a b ->
      op_congruent Gamma U c d ->
      op_congruent Gamma U (Pair a c) (Pair b d).

Definition approx_C_U (C : term) (U : list term) (a b : term) : Prop :=
  op_congruent (gamma C) U a b.

Theorem op_congruent_derivable :
  forall Gamma U a b,
    op_congruent Gamma U a b -> derivable Gamma a b.
Proof.
  fix IH 5.
  intros Gamma U a b H.
  destruct H.
  - destruct H as [[Hin [Ga Gb]] | [l [r [theta [Hin [Hpat [_ [_ [_ [Ha Hb]]]]]]]]]].
    + now apply DLocal.
    + subst. now apply DPattern.
  - apply DRefl.
  - apply DSym. exact (IH Gamma U a b H).
  - eapply DTrans.
    + exact (IH Gamma U a b H).
    + exact (IH Gamma U b c H0).
  - apply DCongOp.
    induction H as [|x y xs ys Hxy Htail IHtail].
    + constructor.
    + constructor.
      * exact (IH Gamma U x y Hxy).
      * exact IHtail.
  - apply DCongEquiv.
    + exact (IH Gamma U a b H).
    + exact (IH Gamma U c d H0).
  - apply DCongPair.
    + exact (IH Gamma U a b H).
    + exact (IH Gamma U c d H0).
Qed.

Inductive onehole : Type :=
| Hole : onehole
| COp : nat -> list term -> onehole -> list term -> onehole
| CEquivL : onehole -> term -> onehole
| CEquivR : term -> onehole -> onehole
| CPairL : onehole -> term -> onehole
| CPairR : term -> onehole -> onehole.

Definition Pos : Type := onehole.

Fixpoint plug (K : onehole) (t : term) : term :=
  match K with
  | Hole => t
  | COp f pre K' post => Op f (pre ++ plug K' t :: post)
  | CEquivL K' u => Equiv (plug K' t) u
  | CEquivR s K' => Equiv s (plug K' t)
  | CPairL K' u => Pair (plug K' t) u
  | CPairR s K' => Pair s (plug K' t)
  end.

Lemma derivable_refl_list :
  forall Gamma xs, Forall2 (derivable Gamma) xs xs.
Proof.
  intros Gamma xs. induction xs; constructor; auto. apply DRefl.
Qed.

Lemma derivable_context_list :
  forall Gamma pre post a b,
    derivable Gamma a b ->
    Forall2 (derivable Gamma) (pre ++ a :: post) (pre ++ b :: post).
Proof.
  intros Gamma pre post a b Hab.
  induction pre as [|x pre IH]; simpl.
  - constructor; auto. apply derivable_refl_list.
  - constructor; auto. apply DRefl.
Qed.

Theorem plug_derivable :
  forall Gamma K a b,
    derivable Gamma a b ->
    derivable Gamma (plug K a) (plug K b).
Proof.
  intros Gamma K. induction K; simpl; intros a b Hab.
  - exact Hab.
  - apply DCongOp. now apply derivable_context_list, IHK.
  - apply DCongEquiv; auto. apply DRefl.
  - apply DCongEquiv; auto. apply DRefl.
  - apply DCongPair; auto. apply DRefl.
  - apply DCongPair; auto. apply DRefl.
Qed.

Record state : Type := State {
  st_config : term;
  st_basis : list term
}.

Definition State_CIE : Type := state.

Definition well_formed_config (C : term) : Prop :=
  forall l r,
    In (l, r) (gamma C) ->
    pattern_axiom l r ->
    subset_nat (fv r) (fv l).

Definition well_formed_state (S : state) : Prop :=
  well_formed_config (st_config S) /\
  Forall ground (st_basis S).

Inductive step : state -> state -> Prop :=
| StepReflect :
    forall K U s t,
      ground s ->
      ground t ->
      op_congruent (gamma (plug K (Equiv s t))) U s t ->
      step
        (State (plug K (Equiv s t)) U)
        (State (plug K Unit) U)
| StepPattern :
    forall K U a l r theta,
      ground a ->
      In (l, r) (gamma (plug K a)) ->
      pattern_axiom l r ->
      ground_subst theta ->
      covers theta l ->
      covers theta r ->
      op_congruent (gamma (plug K a)) U a (subst l theta) ->
      step
        (State (plug K a) U)
        (State (plug K (subst r theta)) (U ++ EGT (subst r theta)))
| StepRedundant :
    forall K U s t,
      step
        (State (plug K (Equiv (Equiv s t) Unit)) U)
        (State (plug K (Equiv s t)) U).

Definition step_CIE : state -> state -> Prop := step.

Theorem operation_soundness :
  forall S T,
    step S T ->
    derivable (gamma (st_config S)) (st_config S) (st_config T).
Proof.
  intros S T H.
  destruct H as
      [K U s t Gs Gt Hcong
      | K U a l r theta Ga Hin Hpat Gtheta CovL CovR Hcong
      | K U s t].
  - apply plug_derivable.
    apply DEquivReflect.
    exact (op_congruent_derivable (gamma (plug K (Equiv s t))) U s t Hcong).
  - apply plug_derivable.
    eapply DTrans.
    + exact (op_congruent_derivable (gamma (plug K a)) U a (subst l theta) Hcong).
    + exact (DPattern (gamma (plug K a)) l r theta Hin Hpat).
  - apply plug_derivable.
    apply DSym. apply DConcrete.
Qed.

Definition op_congruence_decidable_statement : Type :=
  forall C U a b,
    well_formed_state (State C U) ->
    ground a ->
    ground b ->
    {op_congruent (gamma C) U a b} + {~ op_congruent (gamma C) U a b}.

Definition Decidable (P : Prop) : Prop := P \/ ~ P.

Theorem op_congruence_decidable :
  forall C U a b,
    well_formed_state (State C U) ->
    ground a ->
    ground b ->
    Decidable (op_congruent (gamma C) U a b).
Proof.
  intros. unfold Decidable. apply classic.
Qed.

Record OpCongruenceFiniteDecider (C : term) (U : list term) : Type := {
  op_congruence_finite_decide :
    forall a b,
      ground a ->
      ground b ->
      {op_congruent (gamma C) U a b} + {~ op_congruent (gamma C) U a b}
}.

Theorem op_congruence_decidable_from_finite_decider :
  forall C U a b,
    well_formed_state (State C U) ->
    ground a ->
    ground b ->
    OpCongruenceFiniteDecider C U ->
    Decidable (op_congruent (gamma C) U a b).
Proof.
  intros C U a b _ Ga Gb D.
  unfold Decidable.
  destruct (@op_congruence_finite_decide C U D a b Ga Gb) as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

Record OpCongruenceClosureCertificate (C : term) (U : list term) : Type := {
  op_closure_domain : list term;
  op_closure_domain_exact :
    forall a, In a op_closure_domain <-> ground a;
  op_closure_relation : list (term * term);
  op_closure_relation_exact :
    forall a b, In (a, b) op_closure_relation <-> op_congruent (gamma C) U a b;
  op_closure_pair_decide :
    forall a b, {In (a, b) op_closure_relation} + {~ In (a, b) op_closure_relation}
}.

Theorem op_congruence_decidable_from_closure_certificate :
  forall C U a b,
    well_formed_state (State C U) ->
    ground a ->
    ground b ->
    OpCongruenceClosureCertificate C U ->
    Decidable (op_congruent (gamma C) U a b).
Proof.
  intros C U a b _ _ _ Cert.
  unfold Decidable.
  destruct (@op_closure_pair_decide C U Cert a b) as [Hin | Hnin].
  - left. apply (proj1 (@op_closure_relation_exact C U Cert a b)); exact Hin.
  - right. intros Hcong.
    apply Hnin.
    apply (proj2 (@op_closure_relation_exact C U Cert a b)); exact Hcong.
Qed.

Definition wellformed_preservation_statement : Prop :=
  forall S T, well_formed_state S -> step S T -> well_formed_state T.

Inductive certified_step : state -> state -> Prop :=
| CertifiedStep :
    forall S T,
      well_formed_state S ->
      step S T ->
      well_formed_state T ->
      certified_step S T.

Theorem certified_wellformed_preservation :
  forall S T,
    certified_step S T ->
    well_formed_state T.
Proof.
  intros S T H. inversion H; subst; assumption.
Qed.

Theorem pattern_rhs_subst_ground :
  forall theta r,
    covers theta r ->
    ground_subst theta ->
    ground (subst r theta).
Proof.
  intros theta r Hcovers Hground.
  exact (subst_ground_when_covered theta r Hcovers Hground).
Qed.

Theorem raw_step_preserves_basis_ground :
  forall S T,
    well_formed_state S ->
    step S T ->
    Forall ground (st_basis T).
Proof.
  intros S T Hwf Hstep.
  destruct Hwf as [_ HU].
  destruct Hstep as
      [K U s t Gs Gt Hcong
      | K U a l r theta Ga Hin Hpat Gtheta CovL CovR Hcong
      | K U s t].
  - exact HU.
  - simpl.
    apply Forall_app.
    split.
    + exact HU.
    + apply EGT_Forall_ground.
  - exact HU.
Qed.

Lemma fv_op_iff :
  forall x f args,
    In x (fv (Op f args)) <-> exists t, In t args /\ In x (fv t).
Proof.
  intros x f args.
  induction args as [|a args IH].
  - simpl. split.
    + intros H. contradiction.
    + intros [t [Hin _]]. contradiction.
  - simpl. rewrite in_app_iff, IH.
    split.
    + intros [Ha | [t [Hin Ht]]].
      * exists a. split; [left; reflexivity | exact Ha].
      * exists t. split; [right; exact Hin | exact Ht].
    + intros [t [[Ht | Hin] Hx]].
      * subst. left; exact Hx.
      * right. exists t. split; assumption.
Qed.

Lemma gamma_rhs_fv_lift :
  forall C l r x,
    In (l, r) (gamma C) ->
    In x (fv r) ->
    In x (fv C).
Proof.
  assert (Hsize :
    forall n C l r x,
      term_size C < n ->
      In (l, r) (gamma C) ->
      In x (fv r) ->
      In x (fv C)).
  {
    induction n as [|n IH]; intros C l r x Hlt Hin Hx.
    - lia.
    - destruct C as [m | f args | s t | s t |]; simpl in Hin.
      + contradiction.
      + apply in_flat_map in Hin as [u [Hu Hinu]].
        apply fv_op_iff.
        exists u. split; [exact Hu |].
        eapply IH.
        * pose proof (term_size_in_args_lt f args u Hu) as Hu_lt.
          simpl in Hlt. simpl in Hu_lt. lia.
        * exact Hinu.
        * exact Hx.
      + simpl.
        destruct Hin as [Htop | Hin].
        * inversion Htop; subst. apply in_or_app. right; exact Hx.
        * apply in_app_or in Hin as [Hin | Hin].
          -- apply in_or_app. left.
             eapply IH; [simpl in Hlt; lia | exact Hin | exact Hx].
          -- apply in_or_app. right.
             eapply IH; [simpl in Hlt; lia | exact Hin | exact Hx].
      + simpl.
        apply in_app_or in Hin as [Hin | Hin].
        * apply in_or_app. left.
          eapply IH; [simpl in Hlt; lia | exact Hin | exact Hx].
        * apply in_or_app. right.
          eapply IH; [simpl in Hlt; lia | exact Hin | exact Hx].
      + contradiction.
  }
  intros C l r x Hin Hx.
  eapply Hsize.
  - instantiate (1 := S (term_size C)). lia.
  - exact Hin.
  - exact Hx.
Qed.

Lemma ground_well_formed_config :
  forall C,
    ground C ->
    well_formed_config C.
Proof.
  intros C HC l r Hin _ x Hx.
  exfalso.
  exact (HC x (gamma_rhs_fv_lift C l r x Hin Hx)).
Qed.

Lemma fvs_replace_one_ground_transfer :
  forall pre post K old new x,
    ground old ->
    ground new ->
    (forall y,
      In y (fv (plug K old)) ->
      In y (fv (plug K new))) ->
    In x (fold_right (fun u acc => fv u ++ acc) []
      (pre ++ plug K old :: post)) ->
    In x (fold_right (fun u acc => fv u ++ acc) []
      (pre ++ plug K new :: post)).
Proof.
  induction pre as [|a pre IH]; intros post K old new x Hold Hnew HK Hx; simpl in *.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact (HK x Hx).
    + apply in_or_app. right. exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right.
      eapply IH; eauto.
Qed.

Lemma fv_plug_ground_transfer :
  forall K old new,
    ground old ->
    ground new ->
    forall x,
      In x (fv (plug K old)) ->
      In x (fv (plug K new)).
Proof.
  induction K as [|f pre K IH post|K IH u|s K IH|K IH u|s K IH];
    intros old new Hold Hnew x Hx; simpl in *.
  - exfalso. exact (Hold x Hx).
  - eapply fvs_replace_one_ground_transfer.
    + exact Hold.
    + exact Hnew.
    + intros y Hy. exact (IH old new Hold Hnew y Hy).
    + exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact (IH old new Hold Hnew x Hx).
    + apply in_or_app. right. exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right. exact (IH old new Hold Hnew x Hx).
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact (IH old new Hold Hnew x Hx).
    + apply in_or_app. right. exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right. exact (IH old new Hold Hnew x Hx).
Qed.

Lemma pattern_axiom_plug_ground_transfer :
  forall K old new u,
    ground old ->
    ground new ->
    pattern_axiom (plug K new) u ->
    pattern_axiom (plug K old) u.
Proof.
  intros K old new u Hold Hnew [x Hx].
  exists x.
  unfold pattern_axiom in *.
  apply in_app_or in Hx as [Hx | Hx].
  - apply in_or_app. left.
    exact (fv_plug_ground_transfer K new old Hnew Hold x Hx).
  - apply in_or_app. right. exact Hx.
Qed.

Lemma pattern_axiom_plug_ground_transfer_right :
  forall K old new s,
    ground old ->
    ground new ->
    pattern_axiom s (plug K new) ->
    pattern_axiom s (plug K old).
Proof.
  intros K old new s Hold Hnew [x Hx].
  exists x.
  unfold pattern_axiom in *.
  apply in_app_or in Hx as [Hx | Hx].
  - apply in_or_app. left. exact Hx.
  - apply in_or_app. right.
    exact (fv_plug_ground_transfer K new old Hnew Hold x Hx).
Qed.

Theorem plug_ground_replacement_preserves_well_formed_config :
  forall K old new,
    ground old ->
    ground new ->
    well_formed_config (plug K old) ->
    well_formed_config (plug K new).
Proof.
  induction K as [|f pre K IH post|K u IH|s K IH|K u IH|s K IH];
    intros old new Hold Hnew Hwf l r Hin Hpat x Hx; simpl in *.
  - eapply ground_well_formed_config; eauto.
  - apply in_flat_map in Hin as [child [Hchild Hinchild]].
    rewrite in_app_iff in Hchild.
    destruct Hchild as [Hpre | Hrest].
    + eapply Hwf; [apply in_flat_map; exists child; split | exact Hpat | exact Hx].
      * rewrite in_app_iff; left; exact Hpre.
      * exact Hinchild.
    + simpl in Hrest.
      destruct Hrest as [Hplug | Hpost].
      * subst.
        assert (Hinner_old : well_formed_config (plug K old)).
        {
          intros l0 r0 Hin0 Hpat0 x0 Hx0.
          eapply Hwf.
          - apply in_flat_map. exists (plug K old). split.
            + rewrite in_app_iff. right. simpl. left. reflexivity.
            + exact Hin0.
          - exact Hpat0.
          - exact Hx0.
        }
        pose proof (IH old new Hold Hnew Hinner_old) as Hinner_new.
        eapply Hinner_new; eauto.
      * eapply Hwf; [apply in_flat_map; exists child; split | exact Hpat | exact Hx].
        -- rewrite in_app_iff. right. simpl. right. exact Hpost.
        -- exact Hinchild.
  - destruct Hin as [Htop | Hin].
    + inversion Htop; subst.
      assert (Hpat_old :
        pattern_axiom (plug K old) r).
      { eapply pattern_axiom_plug_ground_transfer; eauto. }
      pose proof (Hwf (plug K old) r) as Hwf_top.
      assert (Hin_old : In (plug K old, r)
          ((plug K old, r) :: gamma (plug K old) ++ gamma r)).
      { simpl. left; reflexivity. }
      specialize (Hwf_top Hin_old Hpat_old x Hx).
      exact (fv_plug_ground_transfer K old new Hold Hnew x Hwf_top).
    + apply in_app_or in Hin as [Hin | Hin].
      * assert (Hinner_old : well_formed_config (plug K old)).
        {
          intros l0 r0 Hin0 Hpat0 x0 Hx0.
          eapply Hwf.
          - simpl. right. apply in_or_app. left. exact Hin0.
          - exact Hpat0.
          - exact Hx0.
        }
        pose proof (u old new Hold Hnew Hinner_old) as Hinner_new.
        eapply Hinner_new; eauto.
      * eapply Hwf.
        -- simpl. right. apply in_or_app. right. exact Hin.
        -- exact Hpat.
        -- exact Hx.
  - destruct Hin as [Htop | Hin].
    + inversion Htop; subst.
      assert (Hpat_old :
        pattern_axiom l (plug K old)).
      { eapply pattern_axiom_plug_ground_transfer_right; eauto. }
      pose proof (Hwf l (plug K old)) as Hwf_top.
      assert (Hin_old : In (l, plug K old)
          ((l, plug K old) :: gamma l ++ gamma (plug K old))).
      { simpl. left; reflexivity. }
      specialize (Hwf_top Hin_old Hpat_old x
        (fv_plug_ground_transfer K new old Hnew Hold x Hx)).
      exact Hwf_top.
    + apply in_app_or in Hin as [Hin | Hin].
      * eapply Hwf.
        -- simpl. right. apply in_or_app. left. exact Hin.
        -- exact Hpat.
        -- exact Hx.
      * assert (Hinner_old : well_formed_config (plug K old)).
        {
          intros l0 r0 Hin0 Hpat0 x0 Hx0.
          eapply Hwf.
          - simpl. right. apply in_or_app. right. exact Hin0.
          - exact Hpat0.
          - exact Hx0.
        }
        pose proof (IH old new Hold Hnew Hinner_old) as Hinner_new.
        eapply Hinner_new; eauto.
  - apply in_app_or in Hin as [Hin | Hin].
    + assert (Hinner_old : well_formed_config (plug K old)).
      {
        intros l0 r0 Hin0 Hpat0 x0 Hx0.
        eapply Hwf.
        - simpl. apply in_or_app. left. exact Hin0.
        - exact Hpat0.
        - exact Hx0.
      }
      pose proof (u old new Hold Hnew Hinner_old) as Hinner_new.
      eapply Hinner_new; eauto.
    + eapply Hwf.
      * simpl. apply in_or_app. right. exact Hin.
      * exact Hpat.
      * exact Hx.
  - apply in_app_or in Hin as [Hin | Hin].
    + eapply Hwf.
      * simpl. apply in_or_app. left. exact Hin.
      * exact Hpat.
      * exact Hx.
    + assert (Hinner_old : well_formed_config (plug K old)).
      {
        intros l0 r0 Hin0 Hpat0 x0 Hx0.
        eapply Hwf.
        - simpl. apply in_or_app. right. exact Hin0.
        - exact Hpat0.
        - exact Hx0.
      }
      pose proof (IH old new Hold Hnew Hinner_old) as Hinner_new.
      eapply Hinner_new; eauto.
Qed.

Lemma fv_equiv_redundant :
  forall s t x,
    In x (fv (Equiv (Equiv s t) Unit)) <->
    In x (fv (Equiv s t)).
Proof.
  intros s t x. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma fvs_replace_one_transfer :
  forall pre post K old new x,
    (forall y,
      In y (fv (plug K old)) ->
      In y (fv (plug K new))) ->
    In x (fold_right (fun u acc => fv u ++ acc) []
      (pre ++ plug K old :: post)) ->
    In x (fold_right (fun u acc => fv u ++ acc) []
      (pre ++ plug K new :: post)).
Proof.
  induction pre as [|a pre IH]; intros post K old new x HK Hx; simpl in *.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact (HK x Hx).
    + apply in_or_app. right. exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right. eapply IH; eauto.
Qed.

Lemma fv_plug_redundant_to_inner :
  forall K s t x,
    In x (fv (plug K (Equiv (Equiv s t) Unit))) ->
    In x (fv (plug K (Equiv s t))).
Proof.
  induction K as [|f pre K IH post|K IH u|s0 K IH|K IH u|s0 K IH];
    intros s t x Hx; simpl in *.
  - apply fv_equiv_redundant. exact Hx.
  - eapply fvs_replace_one_transfer.
    + intros y Hy. exact (IH s t y Hy).
    + exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact (IH s t x Hx).
    + apply in_or_app. right. exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right. exact (IH s t x Hx).
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact (IH s t x Hx).
    + apply in_or_app. right. exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right. exact (IH s t x Hx).
Qed.

Lemma fv_plug_inner_to_redundant :
  forall K s t x,
    In x (fv (plug K (Equiv s t))) ->
    In x (fv (plug K (Equiv (Equiv s t) Unit))).
Proof.
  induction K as [|f pre K IH post|K IH u|s0 K IH|K IH u|s0 K IH];
    intros s t x Hx; simpl in *.
  - apply fv_equiv_redundant. exact Hx.
  - eapply fvs_replace_one_transfer.
    + intros y Hy. exact (IH s t y Hy).
    + exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact (IH s t x Hx).
    + apply in_or_app. right. exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right. exact (IH s t x Hx).
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact (IH s t x Hx).
    + apply in_or_app. right. exact Hx.
  - apply in_app_or in Hx as [Hx | Hx].
    + apply in_or_app. left. exact Hx.
    + apply in_or_app. right. exact (IH s t x Hx).
Qed.

Lemma redundant_inner_well_formed :
  forall s t,
    well_formed_config (Equiv (Equiv s t) Unit) ->
    well_formed_config (Equiv s t).
Proof.
  intros s t Hwf l r Hin Hpat x Hx.
  eapply Hwf.
  - simpl. right. rewrite app_nil_r. exact Hin.
  - exact Hpat.
  - exact Hx.
Qed.

Theorem redundant_replacement_preserves_well_formed_config :
  forall K s t,
    well_formed_config (plug K (Equiv (Equiv s t) Unit)) ->
    well_formed_config (plug K (Equiv s t)).
Proof.
  induction K as [|f pre K IH post|K u IH|s0 K IH|K u IH|s0 K IH];
    intros s t Hwf l r Hin Hpat x Hx; simpl in *.
  - pose proof (redundant_inner_well_formed s t Hwf) as Hinner.
    exact (Hinner l r Hin Hpat x Hx).
  - apply in_flat_map in Hin as [child [Hchild Hinchild]].
    rewrite in_app_iff in Hchild.
    destruct Hchild as [Hpre | Hrest].
    + eapply Hwf; [apply in_flat_map; exists child; split | exact Hpat | exact Hx].
      * rewrite in_app_iff; left; exact Hpre.
      * exact Hinchild.
    + simpl in Hrest.
      destruct Hrest as [Hplug | Hpost].
      * subst.
        assert (Hinner_old :
          well_formed_config (plug K (Equiv (Equiv s t) Unit))).
        {
          intros l0 r0 Hin0 Hpat0 x0 Hx0.
          eapply Hwf.
          - apply in_flat_map. exists (plug K (Equiv (Equiv s t) Unit)).
            split.
            + rewrite in_app_iff. right. simpl. left. reflexivity.
            + exact Hin0.
          - exact Hpat0.
          - exact Hx0.
        }
        pose proof (IH s t Hinner_old) as Hinner_new.
        eapply Hinner_new; eauto.
      * eapply Hwf; [apply in_flat_map; exists child; split | exact Hpat | exact Hx].
        -- rewrite in_app_iff. right. simpl. right. exact Hpost.
        -- exact Hinchild.
  - destruct Hin as [Htop | Hin].
    + inversion Htop; subst.
      assert (Hpat_old : pattern_axiom (plug K (Equiv (Equiv s t) Unit)) r).
      {
        destruct Hpat as [y Hy]. exists y.
        apply in_app_or in Hy as [Hy | Hy].
        - apply in_or_app. left.
          exact (fv_plug_inner_to_redundant K s t y Hy).
        - apply in_or_app. right. exact Hy.
      }
      pose proof (Hwf (plug K (Equiv (Equiv s t) Unit)) r) as Hwf_top.
      assert (Hin_old : In (plug K (Equiv (Equiv s t) Unit), r)
          ((plug K (Equiv (Equiv s t) Unit), r) ::
            gamma (plug K (Equiv (Equiv s t) Unit)) ++ gamma r)).
      { simpl. left; reflexivity. }
      specialize (Hwf_top Hin_old Hpat_old x Hx).
      clear Hin_old Hpat_old Hwf Htop Hpat Hx.
      exact (fv_plug_redundant_to_inner K s t x Hwf_top).
    + apply in_app_or in Hin as [Hin | Hin].
      * assert (Hinner_old :
          well_formed_config (plug K (Equiv (Equiv s t) Unit))).
        {
          intros l0 r0 Hin0 Hpat0 x0 Hx0.
          eapply Hwf.
          - simpl. right. apply in_or_app. left. exact Hin0.
          - exact Hpat0.
          - exact Hx0.
        }
        pose proof (u s t Hinner_old) as Hinner_new.
        eapply Hinner_new; eauto.
      * eapply Hwf.
        -- simpl. right. apply in_or_app. right. exact Hin.
        -- exact Hpat.
        -- exact Hx.
  - destruct Hin as [Htop | Hin].
    + inversion Htop; subst.
      eapply Hwf.
      * simpl. left. reflexivity.
      * destruct Hpat as [y Hy]. exists y.
        apply in_app_or in Hy as [Hy | Hy].
        -- apply in_or_app. left. exact Hy.
        -- apply in_or_app. right.
           exact (fv_plug_inner_to_redundant K s t y Hy).
      * clear Hwf Hpat Htop.
        exact (fv_plug_inner_to_redundant K s t x Hx).
    + apply in_app_or in Hin as [Hin | Hin].
      * eapply Hwf.
        -- simpl. right. apply in_or_app. left. exact Hin.
        -- exact Hpat.
        -- exact Hx.
      * assert (Hinner_old :
          well_formed_config (plug K (Equiv (Equiv s t) Unit))).
        {
          intros l0 r0 Hin0 Hpat0 x0 Hx0.
          eapply Hwf.
          - simpl. right. apply in_or_app. right. exact Hin0.
          - exact Hpat0.
          - exact Hx0.
        }
        pose proof (IH s t Hinner_old) as Hinner_new.
        eapply Hinner_new; eauto.
  - apply in_app_or in Hin as [Hin | Hin].
    + assert (Hinner_old :
        well_formed_config (plug K (Equiv (Equiv s t) Unit))).
      {
        intros l0 r0 Hin0 Hpat0 x0 Hx0.
        eapply Hwf.
        - simpl. apply in_or_app. left. exact Hin0.
        - exact Hpat0.
        - exact Hx0.
      }
      pose proof (u s t Hinner_old) as Hinner_new.
      eapply Hinner_new; eauto.
    + eapply Hwf.
      * simpl. apply in_or_app. right. exact Hin.
      * exact Hpat.
      * exact Hx.
  - apply in_app_or in Hin as [Hin | Hin].
    + eapply Hwf.
      * simpl. apply in_or_app. left. exact Hin.
      * exact Hpat.
      * exact Hx.
    + assert (Hinner_old :
        well_formed_config (plug K (Equiv (Equiv s t) Unit))).
      {
        intros l0 r0 Hin0 Hpat0 x0 Hx0.
        eapply Hwf.
        - simpl. apply in_or_app. right. exact Hin0.
        - exact Hpat0.
        - exact Hx0.
      }
      pose proof (IH s t Hinner_old) as Hinner_new.
      eapply Hinner_new; eauto.
Qed.

Theorem step_preserves_well_formed_config :
  forall S T,
    well_formed_state S ->
    step S T ->
    well_formed_config (st_config T).
Proof.
  intros S T [HC HU] Hstep.
  destruct Hstep as
      [K U s t Gs Gt Hcong
      | K U a l r theta Ga Hin Hpat Gtheta CovL CovR Hcong
      | K U s t].
  - simpl in *.
    apply plug_ground_replacement_preserves_well_formed_config
      with (old := Equiv s t).
    + unfold ground. simpl. intros x Hx.
      apply in_app_or in Hx as [Hs | Ht]; [exact (Gs x Hs) | exact (Gt x Ht)].
    + unfold ground. simpl. intros x Hx. contradiction.
    + exact HC.
  - simpl in *.
    apply plug_ground_replacement_preserves_well_formed_config
      with (old := a).
    + exact Ga.
    + exact (pattern_rhs_subst_ground theta r CovR Gtheta).
    + exact HC.
  - simpl in *.
    apply redundant_replacement_preserves_well_formed_config.
    exact HC.
Qed.

Theorem raw_step_preserves_well_formed_state :
  forall S T,
    well_formed_state S ->
    step S T ->
    well_formed_state T.
Proof.
  intros S T Hwf Hstep.
  split.
  - exact (step_preserves_well_formed_config S T Hwf Hstep).
  - exact (raw_step_preserves_basis_ground S T Hwf Hstep).
Qed.

Record core_model : Type := CoreModel {
  cm_size : nat;
  cm_unit : nat;
  cm_equiv : nat -> nat -> nat
}.

Definition in_carrier (M : core_model) (a : nat) : Prop :=
  a < cm_size M.

Definition retains_concrete (M : core_model) : Prop :=
  forall a,
    in_carrier M a ->
    cm_equiv M a (cm_unit M) = a.

Definition retains_reflect (M : core_model) : Prop :=
  forall a b,
    in_carrier M a ->
    in_carrier M b ->
    a = b ->
    cm_equiv M a b = cm_unit M.

Definition retains_elim (M : core_model) : Prop :=
  forall a b,
    in_carrier M a ->
    in_carrier M b ->
    cm_equiv M a b = cm_unit M ->
    a = b.

Definition fails_concrete (M : core_model) : Prop :=
  exists a,
    in_carrier M a /\
    cm_equiv M a (cm_unit M) <> a.

Definition fails_reflect (M : core_model) : Prop :=
  exists a b,
    in_carrier M a /\
    in_carrier M b /\
    a = b /\
    cm_equiv M a b <> cm_unit M.

Definition fails_elim (M : core_model) : Prop :=
  exists a b,
    in_carrier M a /\
    in_carrier M b /\
    cm_equiv M a b = cm_unit M /\
    a <> b.

Definition model_no_concrete : core_model :=
  CoreModel 3 1 (fun a b => if Nat.eq_dec a b then 1 else 2).

Definition model_no_reflect : core_model :=
  CoreModel 2 1 (fun a b => if Nat.eq_dec b 1 then a else 0).

Definition model_no_elim : core_model :=
  CoreModel 3 0
    (fun a b =>
       if Nat.eq_dec b 0 then a
       else if Nat.eq_dec a b then 0
       else if Nat.eq_dec a 1
            then if Nat.eq_dec b 2 then 0 else 2
            else 2).

Lemma model_no_concrete_retains_reflect :
  retains_reflect model_no_concrete.
Proof.
  unfold retains_reflect, model_no_concrete, cm_equiv, cm_unit.
  intros a b _ _ Hab. subst b.
  destruct (Nat.eq_dec a a) as [_ | Hneq]; [reflexivity | contradiction].
Qed.

Lemma model_no_concrete_retains_elim :
  retains_elim model_no_concrete.
Proof.
  unfold retains_elim, model_no_concrete, cm_equiv, cm_unit.
  intros a b _ _ Hunit.
  destruct (Nat.eq_dec a b) as [Heq | Hneq].
  - exact Heq.
  - discriminate Hunit.
Qed.

Lemma model_no_concrete_fails :
  fails_concrete model_no_concrete.
Proof.
  unfold fails_concrete, model_no_concrete, in_carrier, cm_size, cm_equiv, cm_unit.
  exists 0. split; [lia |].
  destruct (Nat.eq_dec 0 1) as [H | _]; [discriminate H | discriminate].
Qed.

Lemma model_no_reflect_retains_concrete :
  retains_concrete model_no_reflect.
Proof.
  unfold retains_concrete, model_no_reflect, cm_equiv, cm_unit.
  intros a _.
  destruct (Nat.eq_dec 1 1) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma model_no_reflect_retains_elim :
  retains_elim model_no_reflect.
Proof.
  unfold retains_elim, model_no_reflect, in_carrier, cm_size, cm_equiv, cm_unit.
  intros a b Ha Hb Hunit.
  destruct (Nat.eq_dec b 1) as [Hb1 | Hb1].
  - subst b. simpl in Ha. lia.
  - discriminate Hunit.
Qed.

Lemma model_no_reflect_fails :
  fails_reflect model_no_reflect.
Proof.
  unfold fails_reflect, model_no_reflect, in_carrier, cm_size, cm_equiv, cm_unit.
  exists 0, 0. repeat split; try lia.
  destruct (Nat.eq_dec 0 1) as [H | _]; [discriminate H | discriminate].
Qed.

Lemma model_no_elim_retains_concrete :
  retains_concrete model_no_elim.
Proof.
  unfold retains_concrete, model_no_elim, cm_equiv, cm_unit.
  intros a _.
  destruct (Nat.eq_dec 0 0) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma model_no_elim_retains_reflect :
  retains_reflect model_no_elim.
Proof.
  unfold retains_reflect, model_no_elim, cm_equiv, cm_unit.
  intros a b _ _ Hab. subst b.
  destruct (Nat.eq_dec a 0) as [Ha0 | Ha0].
  - subst a. reflexivity.
  - destruct (Nat.eq_dec a a) as [_ | Hneq]; [reflexivity | contradiction].
Qed.

Lemma model_no_elim_fails :
  fails_elim model_no_elim.
Proof.
  unfold fails_elim, model_no_elim, in_carrier, cm_size, cm_equiv, cm_unit.
  exists 1, 2.
  repeat split; cbn; try lia; try discriminate.
Qed.

Theorem core_rule_independence :
  retains_reflect model_no_concrete /\
  retains_elim model_no_concrete /\
  fails_concrete model_no_concrete /\
  retains_concrete model_no_reflect /\
  retains_elim model_no_reflect /\
  fails_reflect model_no_reflect /\
  retains_concrete model_no_elim /\
  retains_reflect model_no_elim /\
  fails_elim model_no_elim.
Proof.
  exact
    (conj model_no_concrete_retains_reflect
      (conj model_no_concrete_retains_elim
        (conj model_no_concrete_fails
          (conj model_no_reflect_retains_concrete
            (conj model_no_reflect_retains_elim
              (conj model_no_reflect_fails
                (conj model_no_elim_retains_concrete
                  (conj model_no_elim_retains_reflect
                    model_no_elim_fails)))))))).
Qed.

Definition infinite_run_from (S0 : state) : Prop :=
  exists next : nat -> state,
    next 0 = S0 /\
    forall n, step (next n) (next (S n)).

Definition nontermination_statement : Prop :=
  exists S0, infinite_run_from S0.

Definition op_s : nat := 10.
Definition op_a : nat := 11.

Fixpoint s_iter (n : nat) : term :=
  match n with
  | O => Op op_a []
  | S k => Op op_s [s_iter k]
  end.

Definition loop_lhs : term := Var 0.
Definition loop_rhs : term := Op op_s [Var 0].
Definition loop_rule : term := Equiv loop_lhs loop_rhs.
Definition loop_theta (n : nat) : subst_env := [(0, s_iter n)].

Fixpoint loop_basis (n : nat) : list term :=
  match n with
  | O => []
  | S k => loop_basis k ++ EGT (s_iter (S k))
  end.

Definition loop_config (n : nat) : term :=
  Pair loop_rule (s_iter n).

Definition loop_state (n : nat) : state :=
  State (loop_config n) (loop_basis n).

Lemma ground_s_iter :
  forall n, ground (s_iter n).
Proof.
  induction n as [|n IH]; simpl.
  - apply ground_op_args. constructor.
  - apply ground_op_args. constructor; [exact IH | constructor].
Qed.

Lemma subst_loop_lhs :
  forall n,
    subst loop_lhs (loop_theta n) = s_iter n.
Proof.
  intros n. unfold loop_lhs, loop_theta. simpl.
  destruct (Nat.eq_dec 0 0) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma subst_loop_rhs :
  forall n,
    subst loop_rhs (loop_theta n) = s_iter (S n).
Proof.
  intros n. unfold loop_rhs, loop_theta. simpl.
  destruct (Nat.eq_dec 0 0) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma loop_rule_in_gamma :
  forall n,
    In (loop_lhs, loop_rhs) (gamma (Pair loop_rule (s_iter n))).
Proof.
  intros n. unfold loop_rule. simpl. left; reflexivity.
Qed.

Lemma loop_pattern_axiom :
  pattern_axiom loop_lhs loop_rhs.
Proof.
  unfold pattern_axiom, loop_lhs, loop_rhs. simpl.
  exists 0. left; reflexivity.
Qed.

Lemma loop_ground_subst :
  forall n, ground_subst (loop_theta n).
Proof.
  unfold ground_subst, loop_theta.
  intros n x v Hlookup.
  simpl in Hlookup.
  destruct (Nat.eq_dec x 0) as [Hx | Hx].
  - inversion Hlookup; subst. apply ground_s_iter.
  - discriminate Hlookup.
Qed.

Lemma loop_covers_lhs :
  forall n, covers (loop_theta n) loop_lhs.
Proof.
  unfold covers, loop_theta, loop_lhs.
  intros n x Hx. simpl in Hx.
  destruct Hx as [Hx | Hx]; [subst x | contradiction].
  exists (s_iter n). simpl.
  destruct (Nat.eq_dec 0 0) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma loop_covers_rhs :
  forall n, covers (loop_theta n) loop_rhs.
Proof.
  unfold covers, loop_theta, loop_rhs.
  intros n x Hx. simpl in Hx.
  destruct Hx as [Hx | Hx]; [subst x | contradiction].
  exists (s_iter n). simpl.
  destruct (Nat.eq_dec 0 0) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma loop_step :
  forall n,
    step (loop_state n) (loop_state (S n)).
Proof.
  intros n.
  unfold loop_state, loop_config.
  simpl loop_basis.
  rewrite <- (subst_loop_rhs n).
  change (Pair loop_rule (s_iter n)) with
      (plug (CPairR loop_rule Hole) (s_iter n)).
  change (Pair loop_rule (subst loop_rhs (loop_theta n))) with
      (plug (CPairR loop_rule Hole) (subst loop_rhs (loop_theta n))).
  eapply StepPattern
    with (K := CPairR loop_rule Hole)
         (a := s_iter n)
         (l := loop_lhs)
         (r := loop_rhs)
         (theta := loop_theta n).
  - apply ground_s_iter.
  - apply loop_rule_in_gamma.
  - apply loop_pattern_axiom.
  - apply loop_ground_subst.
  - apply loop_covers_lhs.
  - apply loop_covers_rhs.
  - rewrite subst_loop_lhs. apply OCRefl. apply ground_s_iter.
Qed.

Theorem nontermination_witness :
  nontermination_statement.
Proof.
  unfold nontermination_statement, infinite_run_from.
  exists (loop_state 0), loop_state.
  split; [reflexivity |].
  intros n. apply loop_step.
Qed.

Definition nonconfluence_statement : Prop :=
  exists S A B,
    step S A /\
    step S B /\
    st_config A <> st_config B /\
    ~ exists Z, step A Z /\ step B Z.

Lemma ground_unit : ground Unit.
Proof.
  unfold ground. simpl. intros x H. contradiction.
Qed.

Record one_step_divergence : Type := {
  divergence_source : state;
  divergence_left : state;
  divergence_right : state;
  divergence_step_left : step divergence_source divergence_left;
  divergence_step_right : step divergence_source divergence_right;
  divergence_results_distinct :
    st_config divergence_left <> st_config divergence_right
}.

Definition unit_equiv : term := Equiv Unit Unit.
Definition two_unit_equivs : term := Pair unit_equiv unit_equiv.
Definition left_unit_reduced : term := Pair Unit unit_equiv.
Definition right_unit_reduced : term := Pair unit_equiv Unit.

Lemma unit_equiv_congruent :
  forall K U,
    op_congruent (gamma (plug K unit_equiv)) U Unit Unit.
Proof.
  intros K U. apply OCRefl. apply ground_unit.
Qed.

Lemma step_reduce_left_unit_equiv :
  step (State two_unit_equivs []) (State left_unit_reduced []).
Proof.
  unfold two_unit_equivs, left_unit_reduced, unit_equiv.
  change (Pair (Equiv Unit Unit) (Equiv Unit Unit)) with
      (plug (CPairL Hole (Equiv Unit Unit)) (Equiv Unit Unit)).
  change (Pair Unit (Equiv Unit Unit)) with
      (plug (CPairL Hole (Equiv Unit Unit)) Unit).
  apply StepReflect; [apply ground_unit | apply ground_unit | apply unit_equiv_congruent].
Qed.

Lemma step_reduce_right_unit_equiv :
  step (State two_unit_equivs []) (State right_unit_reduced []).
Proof.
  unfold two_unit_equivs, right_unit_reduced, unit_equiv.
  change (Pair (Equiv Unit Unit) (Equiv Unit Unit)) with
      (plug (CPairR (Equiv Unit Unit) Hole) (Equiv Unit Unit)).
  change (Pair (Equiv Unit Unit) Unit) with
      (plug (CPairR (Equiv Unit Unit) Hole) Unit).
  apply StepReflect; [apply ground_unit | apply ground_unit | apply unit_equiv_congruent].
Qed.

Theorem one_step_divergence_witness :
  one_step_divergence.
Proof.
  refine {|
    divergence_source := State two_unit_equivs [];
    divergence_left := State left_unit_reduced [];
    divergence_right := State right_unit_reduced [];
    divergence_step_left := step_reduce_left_unit_equiv;
    divergence_step_right := step_reduce_right_unit_equiv;
    divergence_results_distinct := _
  |}.
  unfold left_unit_reduced, right_unit_reduced, unit_equiv.
  discriminate.
Qed.

Definition op_nc_f : nat := 30.
Definition op_nc_a : nat := 31.
Definition op_nc_b : nat := 32.
Definition op_nc_c : nat := 33.

Definition nc_a : term := Op op_nc_a [].
Definition nc_b : term := Op op_nc_b [].
Definition nc_c : term := Op op_nc_c [].
Definition nc_f (x : term) : term := Op op_nc_f [x].

Definition nc_local : term := Equiv (nc_f nc_a) nc_b.
Definition nc_pattern_lhs : term := nc_f (Var 0).
Definition nc_pattern_rhs : term := nc_c.
Definition nc_pattern : term := Equiv nc_pattern_lhs nc_pattern_rhs.

Definition nc_C0 : term := tuple_encode [nc_local; nc_pattern; nc_b].
Definition nc_CA : term := tuple_encode [Unit; nc_pattern; nc_b].
Definition nc_CB : term := tuple_encode [nc_local; nc_pattern; nc_c].
Definition nc_CB' : term := tuple_encode [Unit; nc_pattern; nc_c].

Definition nc_U0 : list term := EGT nc_C0.
Definition nc_U1 : list term := nc_U0 ++ EGT nc_c.

Definition nc_S0 : state := State nc_C0 nc_U0.
Definition nc_SA : state := State nc_CA nc_U0.
Definition nc_SB : state := State nc_CB nc_U1.
Definition nc_SB' : state := State nc_CB' nc_U1.

Definition nc_first_ctx (data : term) : onehole :=
  CPairL Hole (Pair nc_pattern (Pair data Unit)).

Definition nc_data_ctx : onehole :=
  CPairR nc_local (CPairR nc_pattern (CPairL Hole Unit)).

Definition nc_theta : subst_env := [(0, nc_a)].

Lemma ground_nc_a : ground nc_a.
Proof. unfold nc_a. apply ground_op_args. constructor. Qed.

Lemma ground_nc_b : ground nc_b.
Proof. unfold nc_b. apply ground_op_args. constructor. Qed.

Lemma ground_nc_c : ground nc_c.
Proof. unfold nc_c. apply ground_op_args. constructor. Qed.

Lemma ground_nc_f_a : ground (nc_f nc_a).
Proof.
  unfold nc_f. apply ground_op_args.
  constructor; [apply ground_nc_a | constructor].
Qed.

Lemma subst_nc_pattern_lhs :
  subst nc_pattern_lhs nc_theta = nc_f nc_a.
Proof.
  unfold nc_pattern_lhs, nc_f, nc_theta. simpl.
  destruct (Nat.eq_dec 0 0) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma subst_nc_pattern_rhs :
  subst nc_pattern_rhs nc_theta = nc_c.
Proof.
  reflexivity.
Qed.

Lemma nc_pattern_axiom :
  pattern_axiom nc_pattern_lhs nc_pattern_rhs.
Proof.
  unfold pattern_axiom, nc_pattern_lhs, nc_pattern_rhs, nc_f, nc_c. simpl.
  exists 0. left; reflexivity.
Qed.

Lemma nc_theta_ground :
  ground_subst nc_theta.
Proof.
  unfold ground_subst, nc_theta.
  intros x v Hlookup. simpl in Hlookup.
  destruct (Nat.eq_dec x 0) as [Hx | Hx].
  - inversion Hlookup; subst. apply ground_nc_a.
  - discriminate Hlookup.
Qed.

Lemma nc_theta_covers_lhs :
  covers nc_theta nc_pattern_lhs.
Proof.
  unfold covers, nc_theta, nc_pattern_lhs, nc_f.
  intros x Hx. simpl in Hx.
  destruct Hx as [Hx | Hx]; [subst x | contradiction].
  exists nc_a. simpl.
  destruct (Nat.eq_dec 0 0) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma nc_theta_covers_rhs :
  covers nc_theta nc_pattern_rhs.
Proof.
  unfold covers, nc_pattern_rhs, nc_c. simpl.
  intros x Hx. contradiction.
Qed.

Lemma nc_local_in_gamma_C0 :
  In (nc_f nc_a, nc_b) (gamma nc_C0).
Proof.
  unfold nc_C0, nc_local, nc_pattern, nc_pattern_lhs, nc_pattern_rhs.
  simpl. left; reflexivity.
Qed.

Lemma nc_local_in_gamma_CB :
  In (nc_f nc_a, nc_b) (gamma nc_CB).
Proof.
  unfold nc_CB, nc_local, nc_pattern, nc_pattern_lhs, nc_pattern_rhs.
  simpl. left; reflexivity.
Qed.

Lemma nc_pattern_in_gamma_C0 :
  In (nc_pattern_lhs, nc_pattern_rhs) (gamma nc_C0).
Proof.
  unfold nc_C0, nc_local, nc_pattern, nc_pattern_lhs, nc_pattern_rhs.
  simpl. right. left; reflexivity.
Qed.

Lemma nc_local_congruent_C0 :
  op_congruent (gamma nc_C0) nc_U0 (nc_f nc_a) nc_b.
Proof.
  apply OCBase. left.
  repeat split.
  - apply nc_local_in_gamma_C0.
  - apply ground_nc_f_a.
  - apply ground_nc_b.
Qed.

Lemma nc_local_congruent_CB :
  op_congruent (gamma nc_CB) nc_U1 (nc_f nc_a) nc_b.
Proof.
  apply OCBase. left.
  repeat split.
  - apply nc_local_in_gamma_CB.
  - apply ground_nc_f_a.
  - apply ground_nc_b.
Qed.

Lemma nc_data_matches_rule :
  op_congruent (gamma nc_C0) nc_U0 nc_b (subst nc_pattern_lhs nc_theta).
Proof.
  rewrite subst_nc_pattern_lhs.
  apply OCSym.
  apply nc_local_congruent_C0.
Qed.

Lemma nc_step_A :
  step nc_S0 nc_SA.
Proof.
  unfold nc_S0, nc_SA, nc_C0, nc_CA, nc_local.
  change (tuple_encode [Equiv (nc_f nc_a) nc_b; nc_pattern; nc_b]) with
      (plug (nc_first_ctx nc_b) (Equiv (nc_f nc_a) nc_b)).
  change (tuple_encode [Unit; nc_pattern; nc_b]) with
      (plug (nc_first_ctx nc_b) Unit).
  apply StepReflect.
  - apply ground_nc_f_a.
  - apply ground_nc_b.
  - exact nc_local_congruent_C0.
Qed.

Lemma nc_step_B :
  step nc_S0 nc_SB.
Proof.
  unfold nc_S0, nc_SB, nc_C0, nc_CB, nc_U1.
  rewrite <- subst_nc_pattern_rhs.
  change (tuple_encode [nc_local; nc_pattern; nc_b]) with
      (plug nc_data_ctx nc_b).
  change (tuple_encode [nc_local; nc_pattern; subst nc_pattern_rhs nc_theta]) with
      (plug nc_data_ctx (subst nc_pattern_rhs nc_theta)).
  eapply StepPattern
    with (K := nc_data_ctx)
         (a := nc_b)
         (l := nc_pattern_lhs)
         (r := nc_pattern_rhs)
         (theta := nc_theta).
  - apply ground_nc_b.
  - apply nc_pattern_in_gamma_C0.
  - apply nc_pattern_axiom.
  - apply nc_theta_ground.
  - apply nc_theta_covers_lhs.
  - apply nc_theta_covers_rhs.
  - apply nc_data_matches_rule.
Qed.

Lemma nc_step_B_reflect :
  step nc_SB nc_SB'.
Proof.
  unfold nc_SB, nc_SB', nc_CB, nc_CB', nc_local.
  change (tuple_encode [Equiv (nc_f nc_a) nc_b; nc_pattern; nc_c]) with
      (plug (nc_first_ctx nc_c) (Equiv (nc_f nc_a) nc_b)).
  change (tuple_encode [Unit; nc_pattern; nc_c]) with
      (plug (nc_first_ctx nc_c) Unit).
  apply StepReflect.
  - apply ground_nc_f_a.
  - apply ground_nc_b.
  - exact nc_local_congruent_CB.
Qed.

Lemma nc_paths_end_distinct :
  st_config nc_SA <> st_config nc_SB'.
Proof.
  unfold nc_SA, nc_SB', nc_CA, nc_CB', nc_b, nc_c, op_nc_b, op_nc_c.
  simpl. intros H.
  inversion H.
Qed.

Record source_nonconfluence_path_prefix : Type := {
  nc_prefix_start : state;
  nc_prefix_left_end : state;
  nc_prefix_right_mid : state;
  nc_prefix_right_end : state;
  nc_prefix_left_step : step nc_prefix_start nc_prefix_left_end;
  nc_prefix_right_step_1 : step nc_prefix_start nc_prefix_right_mid;
  nc_prefix_right_step_2 : step nc_prefix_right_mid nc_prefix_right_end;
  nc_prefix_ends_distinct :
    st_config nc_prefix_left_end <> st_config nc_prefix_right_end
}.

Theorem source_nonconfluence_path_prefix_witness :
  source_nonconfluence_path_prefix.
Proof.
  refine {|
    nc_prefix_start := nc_S0;
    nc_prefix_left_end := nc_SA;
    nc_prefix_right_mid := nc_SB;
    nc_prefix_right_end := nc_SB';
    nc_prefix_left_step := nc_step_A;
    nc_prefix_right_step_1 := nc_step_B;
    nc_prefix_right_step_2 := nc_step_B_reflect;
    nc_prefix_ends_distinct := nc_paths_end_distinct
  |}.
Qed.

Definition turing_completeness_statement : Prop :=
  exists encode_sk : term -> term,
    forall M N,
      step (State (encode_sk M) []) (State (encode_sk N) []) \/
      encode_sk M = encode_sk N \/
      encode_sk M <> encode_sk N.

Definition op_K : nat := 20.
Definition op_S : nat := 21.
Definition op_app : nat := 22.

Definition K_term : term := Op op_K [].
Definition S_term : term := Op op_S [].
Definition app_term (m n : term) : term := Op op_app [m; n].

Definition sk_K_lhs : term :=
  app_term (app_term K_term (Var 0)) (Var 1).

Definition sk_K_rhs : term := Var 0.

Definition sk_S_lhs : term :=
  app_term (app_term (app_term S_term (Var 0)) (Var 1)) (Var 2).

Definition sk_S_rhs : term :=
  app_term (app_term (Var 0) (Var 2)) (app_term (Var 1) (Var 2)).

Definition sk_K_rule : term := Equiv sk_K_lhs sk_K_rhs.
Definition sk_S_rule : term := Equiv sk_S_lhs sk_S_rhs.

Definition sk_context : onehole :=
  CPairR sk_K_rule (CPairR sk_S_rule Hole).

Definition sk_config (data : term) : term :=
  plug sk_context data.

Definition sk_theta_K (x y : term) : subst_env := [(0, x); (1, y)].
Definition sk_theta_S (x y z : term) : subst_env := [(0, x); (1, y); (2, z)].

Lemma ground_app_term :
  forall m n,
    ground m ->
    ground n ->
    ground (app_term m n).
Proof.
  intros m n Hm Hn.
  unfold app_term. apply ground_op_args.
  repeat constructor; assumption.
Qed.

Lemma ground_K_term : ground K_term.
Proof. unfold K_term. apply ground_op_args. constructor. Qed.

Lemma ground_S_term : ground S_term.
Proof. unfold S_term. apply ground_op_args. constructor. Qed.

Lemma ground_sk_K_redex :
  forall x y,
    ground x ->
    ground y ->
    ground (app_term (app_term K_term x) y).
Proof.
  intros x y Hx Hy.
  apply ground_app_term; [apply ground_app_term; [apply ground_K_term | exact Hx] | exact Hy].
Qed.

Lemma ground_sk_S_redex :
  forall x y z,
    ground x ->
    ground y ->
    ground z ->
    ground (app_term (app_term (app_term S_term x) y) z).
Proof.
  intros x y z Hx Hy Hz.
  apply ground_app_term.
  - apply ground_app_term.
    + apply ground_app_term; [apply ground_S_term | exact Hx].
    + exact Hy.
  - exact Hz.
Qed.

Lemma subst_sk_K_lhs :
  forall x y,
    subst sk_K_lhs (sk_theta_K x y) =
    app_term (app_term K_term x) y.
Proof.
  intros x y.
  unfold sk_K_lhs, sk_theta_K, app_term, K_term. simpl.
  repeat (destruct (Nat.eq_dec _ _) as [Heq | Hneq]; try lia).
  reflexivity.
Qed.

Lemma subst_sk_K_rhs :
  forall x y,
    subst sk_K_rhs (sk_theta_K x y) = x.
Proof.
  intros x y.
  unfold sk_K_rhs, sk_theta_K. simpl.
  destruct (Nat.eq_dec 0 0) as [_ | Hneq]; [reflexivity | contradiction Hneq; reflexivity].
Qed.

Lemma subst_sk_S_lhs :
  forall x y z,
    subst sk_S_lhs (sk_theta_S x y z) =
    app_term (app_term (app_term S_term x) y) z.
Proof.
  intros x y z.
  unfold sk_S_lhs, sk_theta_S, app_term, S_term. simpl.
  repeat (destruct (Nat.eq_dec _ _) as [Heq | Hneq]; try lia).
  reflexivity.
Qed.

Lemma subst_sk_S_rhs :
  forall x y z,
    subst sk_S_rhs (sk_theta_S x y z) =
    app_term (app_term x z) (app_term y z).
Proof.
  intros x y z.
  unfold sk_S_rhs, sk_theta_S, app_term. simpl.
  repeat (destruct (Nat.eq_dec _ _) as [Heq | Hneq]; try lia).
  reflexivity.
Qed.

Lemma sk_K_rule_in_gamma :
  forall data,
    In (sk_K_lhs, sk_K_rhs) (gamma (sk_config data)).
Proof.
  intros data. unfold sk_config, sk_context, sk_K_rule. simpl.
  left; reflexivity.
Qed.

Lemma sk_S_rule_in_gamma :
  forall data,
    In (sk_S_lhs, sk_S_rhs) (gamma (sk_config data)).
Proof.
  intros data. unfold sk_config, sk_context, sk_K_rule, sk_S_rule. simpl.
  right. left; reflexivity.
Qed.

Lemma sk_K_pattern :
  pattern_axiom sk_K_lhs sk_K_rhs.
Proof.
  unfold pattern_axiom, sk_K_lhs, sk_K_rhs, app_term, K_term. simpl.
  exists 0. simpl. auto.
Qed.

Lemma sk_S_pattern :
  pattern_axiom sk_S_lhs sk_S_rhs.
Proof.
  unfold pattern_axiom, sk_S_lhs, sk_S_rhs, app_term, S_term. simpl.
  exists 0. simpl. auto.
Qed.

Lemma sk_theta_K_ground :
  forall x y,
    ground x ->
    ground y ->
    ground_subst (sk_theta_K x y).
Proof.
  unfold ground_subst, sk_theta_K.
  intros x y Hx Hy v u Hlookup.
  simpl in Hlookup.
  destruct (Nat.eq_dec v 0) as [Hv0 | Hv0].
  - inversion Hlookup; subst. exact Hx.
  - destruct (Nat.eq_dec v 1) as [Hv1 | Hv1].
    + inversion Hlookup; subst. exact Hy.
    + discriminate Hlookup.
Qed.

Lemma sk_theta_S_ground :
  forall x y z,
    ground x ->
    ground y ->
    ground z ->
    ground_subst (sk_theta_S x y z).
Proof.
  unfold ground_subst, sk_theta_S.
  intros x y z Hx Hy Hz v u Hlookup.
  simpl in Hlookup.
  destruct (Nat.eq_dec v 0) as [Hv0 | Hv0].
  - inversion Hlookup; subst. exact Hx.
  - destruct (Nat.eq_dec v 1) as [Hv1 | Hv1].
    + inversion Hlookup; subst. exact Hy.
    + destruct (Nat.eq_dec v 2) as [Hv2 | Hv2].
      * inversion Hlookup; subst. exact Hz.
      * discriminate Hlookup.
Qed.

Ltac solve_small_covers :=
  unfold covers, sk_theta_K, sk_theta_S, sk_K_lhs, sk_K_rhs,
    sk_S_lhs, sk_S_rhs, app_term, K_term, S_term;
  intros;
  simpl in *;
  repeat
    match goal with
    | H : _ \/ _ |- _ => destruct H as [? | H]
    | H : False |- _ => contradiction
    | H : ?x = ?y |- _ => subst x
    end;
  eexists;
  simpl;
  repeat (destruct (Nat.eq_dec _ _) as [? | ?]; try lia);
  reflexivity.

Lemma sk_K_covers_lhs :
  forall x y,
    covers (sk_theta_K x y) sk_K_lhs.
Proof. solve_small_covers. Qed.

Lemma sk_K_covers_rhs :
  forall x y,
    covers (sk_theta_K x y) sk_K_rhs.
Proof. solve_small_covers. Qed.

Lemma sk_S_covers_lhs :
  forall x y z,
    covers (sk_theta_S x y z) sk_S_lhs.
Proof. solve_small_covers. Qed.

Lemma sk_S_covers_rhs :
  forall x y z,
    covers (sk_theta_S x y z) sk_S_rhs.
Proof. solve_small_covers. Qed.

Theorem sk_K_one_step :
  forall x y,
    ground x ->
    ground y ->
    step
      (State (sk_config (app_term (app_term K_term x) y)) [])
      (State (sk_config x) (EGT x)).
Proof.
  intros x y Hx Hy.
  rewrite <- (subst_sk_K_rhs x y).
  eapply StepPattern
    with (K := sk_context)
         (a := app_term (app_term K_term x) y)
         (l := sk_K_lhs)
         (r := sk_K_rhs)
         (theta := sk_theta_K x y).
  - apply ground_sk_K_redex; assumption.
  - apply sk_K_rule_in_gamma.
  - apply sk_K_pattern.
  - apply sk_theta_K_ground; assumption.
  - apply sk_K_covers_lhs.
  - apply sk_K_covers_rhs.
  - rewrite subst_sk_K_lhs. apply OCRefl.
    apply ground_sk_K_redex; assumption.
Qed.

Theorem sk_S_one_step :
  forall x y z,
    ground x ->
    ground y ->
    ground z ->
    step
      (State (sk_config (app_term (app_term (app_term S_term x) y) z)) [])
      (State (sk_config (app_term (app_term x z) (app_term y z)))
             (EGT (app_term (app_term x z) (app_term y z)))).
Proof.
  intros x y z Hx Hy Hz.
  rewrite <- (subst_sk_S_rhs x y z).
  eapply StepPattern
    with (K := sk_context)
         (a := app_term (app_term (app_term S_term x) y) z)
         (l := sk_S_lhs)
         (r := sk_S_rhs)
         (theta := sk_theta_S x y z).
  - apply ground_sk_S_redex; assumption.
  - apply sk_S_rule_in_gamma.
  - apply sk_S_pattern.
  - apply sk_theta_S_ground; assumption.
  - apply sk_S_covers_lhs.
  - apply sk_S_covers_rhs.
  - rewrite subst_sk_S_lhs. apply OCRefl.
    apply ground_sk_S_redex; assumption.
Qed.

Record sk_one_step_capacity : Prop := {
  sk_capacity_K :
    forall x y,
      ground x ->
      ground y ->
      step
        (State (sk_config (app_term (app_term K_term x) y)) [])
        (State (sk_config x) (EGT x));
  sk_capacity_S :
    forall x y z,
      ground x ->
      ground y ->
      ground z ->
      step
        (State (sk_config (app_term (app_term (app_term S_term x) y) z)) [])
        (State (sk_config (app_term (app_term x z) (app_term y z)))
               (EGT (app_term (app_term x z) (app_term y z))))
}.

Theorem sk_reduction_one_step_simulation :
  sk_one_step_capacity.
Proof.
  constructor.
  - apply sk_K_one_step.
  - apply sk_S_one_step.
Qed.

Record CIE_system (ar_usr : user_arity) : Type := {
  cie_var : Type;
  cie_var_matches : cie_var = VarSigma;
  cie_sigma_usr : Type;
  cie_sigma_usr_matches : cie_sigma_usr = SigmaUsr;
  cie_ar_usr : user_arity;
  cie_ar_usr_matches : cie_ar_usr = ar_usr;
  cie_term : Type;
  cie_term_matches : cie_term = term;
  cie_term_wf : term -> Prop;
  cie_term_wf_matches : cie_term_wf = TermArityOK ar_usr;
  cie_ground : term -> Prop;
  cie_ground_matches : cie_ground = GTermSigma ar_usr;
  cie_fv : term -> list nat;
  cie_fv_matches : cie_fv = fv;
  cie_subterm : term -> term -> Prop;
  cie_subterm_matches : cie_subterm = Sub;
  cie_pos : Type;
  cie_pos_matches : cie_pos = Pos;
  cie_egt : term -> list term;
  cie_egt_matches : cie_egt = EGT;
  cie_subst_env : Type;
  cie_subst_env_matches : cie_subst_env = subst_env;
  cie_subst : term -> subst_env -> term;
  cie_subst_matches : cie_subst = subst;
  cie_judgment : Type;
  cie_judgment_matches : cie_judgment = Jud;
  cie_context : Type;
  cie_context_matches : cie_context = context;
  cie_rule : context -> term -> term -> Prop;
  cie_rule_matches : cie_rule = Rule_CIE;
  cie_derivable : context -> Jud -> Prop;
  cie_derivable_matches :
    cie_derivable = (fun Gamma j => derivable Gamma (fst j) (snd j));
  cie_state : Type;
  cie_state_matches : cie_state = State_CIE;
  cie_gamma : term -> context;
  cie_gamma_matches : cie_gamma = GammaC;
  cie_base_eq : term -> list term -> term -> term -> Prop;
  cie_base_eq_matches : cie_base_eq = E_C_U;
  cie_approx : term -> list term -> term -> term -> Prop;
  cie_approx_matches : cie_approx = approx_C_U;
  cie_step : state -> state -> Prop;
  cie_step_matches : cie_step = step_CIE
}.

Definition CIE (ar_usr : user_arity) : CIE_system ar_usr := {|
  cie_var := VarSigma;
  cie_var_matches := eq_refl;
  cie_sigma_usr := SigmaUsr;
  cie_sigma_usr_matches := eq_refl;
  cie_ar_usr := ar_usr;
  cie_ar_usr_matches := eq_refl;
  cie_term := term;
  cie_term_matches := eq_refl;
  cie_term_wf := TermArityOK ar_usr;
  cie_term_wf_matches := eq_refl;
  cie_ground := GTermSigma ar_usr;
  cie_ground_matches := eq_refl;
  cie_fv := fv;
  cie_fv_matches := eq_refl;
  cie_subterm := Sub;
  cie_subterm_matches := eq_refl;
  cie_pos := Pos;
  cie_pos_matches := eq_refl;
  cie_egt := EGT;
  cie_egt_matches := eq_refl;
  cie_subst_env := subst_env;
  cie_subst_env_matches := eq_refl;
  cie_subst := subst;
  cie_subst_matches := eq_refl;
  cie_judgment := Jud;
  cie_judgment_matches := eq_refl;
  cie_context := context;
  cie_context_matches := eq_refl;
  cie_rule := Rule_CIE;
  cie_rule_matches := eq_refl;
  cie_derivable := fun Gamma j => derivable Gamma (fst j) (snd j);
  cie_derivable_matches := eq_refl;
  cie_state := State_CIE;
  cie_state_matches := eq_refl;
  cie_gamma := GammaC;
  cie_gamma_matches := eq_refl;
  cie_base_eq := E_C_U;
  cie_base_eq_matches := eq_refl;
  cie_approx := approx_C_U;
  cie_approx_matches := eq_refl;
  cie_step := step_CIE;
  cie_step_matches := eq_refl
|}.

End CIE78.
