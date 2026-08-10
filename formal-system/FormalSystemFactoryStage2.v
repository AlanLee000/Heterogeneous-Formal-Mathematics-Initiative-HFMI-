From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryKernel.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.

Module FormalSystemFactoryStage2.

Inductive raw_term : Type :=
| RVar : nat -> raw_term
| RConst : nat -> raw_term
| RApp : raw_term -> raw_term -> raw_term
| RBind : raw_term -> raw_term.

Definition renaming : Type := nat -> nat.
Definition substitution : Type := nat -> raw_term.

Definition id_ren : renaming := fun x => x.
Definition id_subst : substitution := fun x => RVar x.

Definition up_ren (rho : renaming) : renaming :=
  fun x =>
    match x with
    | 0 => 0
    | S y => S (rho y)
    end.

Fixpoint rename (rho : renaming) (t : raw_term) : raw_term :=
  match t with
  | RVar x => RVar (rho x)
  | RConst c => RConst c
  | RApp l r => RApp (rename rho l) (rename rho r)
  | RBind body => RBind (rename (up_ren rho) body)
  end.

Definition shift (t : raw_term) : raw_term := rename S t.

Definition up_subst (sigma : substitution) : substitution :=
  fun x =>
    match x with
    | 0 => RVar 0
    | S y => shift (sigma y)
    end.

Fixpoint subst (sigma : substitution) (t : raw_term) : raw_term :=
  match t with
  | RVar x => sigma x
  | RConst c => RConst c
  | RApp l r => RApp (subst sigma l) (subst sigma r)
  | RBind body => RBind (subst (up_subst sigma) body)
  end.

Definition compose_ren (rho sigma : renaming) : renaming :=
  fun x => rho (sigma x).

Definition raw_syntax_signature : K.Signature :=
  {|
    K.sort_count := 1;
    K.constructor_count := 3;
    K.constructor_arity :=
      fun c =>
        match c with
        | 0 => 0
        | 1 => 2
        | 2 => 1
        | _ => 0
        end;
    K.constructor_result := fun _ => 0
  |}.

Lemma raw_syntax_signature_valid :
  K.ValidSignature raw_syntax_signature.
Proof.
  unfold K.ValidSignature, raw_syntax_signature; simpl.
  split.
  - lia.
  - intros c Hc.
    destruct c as [|[|[|c]]]; simpl; lia.
Qed.

Lemma up_ren_ext :
  forall rho sigma,
    (forall x, rho x = sigma x) ->
    forall x, up_ren rho x = up_ren sigma x.
Proof.
  intros rho sigma H x.
  destruct x as [|x]; simpl.
  - reflexivity.
  - rewrite H; reflexivity.
Qed.

Lemma rename_ext :
  forall t rho sigma,
    (forall x, rho x = sigma x) ->
    rename rho t = rename sigma t.
Proof.
  induction t as [x | c | l IHl r IHr | body IH]; intros rho sigma H; simpl.
  - rewrite H; reflexivity.
  - reflexivity.
  - rewrite (IHl rho sigma H), (IHr rho sigma H); reflexivity.
  - rewrite (IH (up_ren rho) (up_ren sigma)).
    + reflexivity.
    + apply up_ren_ext; exact H.
Qed.

Lemma rename_id :
  forall t, rename id_ren t = t.
Proof.
  induction t as [x | c | l IHl r IHr | body IH]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHl, IHr; reflexivity.
  - f_equal.
    transitivity (rename id_ren body).
    + apply rename_ext.
      intros [|x]; reflexivity.
    + exact IH.
Qed.

Lemma rename_comp :
  forall t rho sigma,
    rename rho (rename sigma t) = rename (compose_ren rho sigma) t.
Proof.
  induction t as [x | c | l IHl r IHr | body IH]; intros rho sigma; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHl, IHr; reflexivity.
  - f_equal.
    rewrite IH.
    apply rename_ext.
    intros [|x]; reflexivity.
Qed.

Lemma up_subst_ext :
  forall sigma tau,
    (forall x, sigma x = tau x) ->
    forall x, up_subst sigma x = up_subst tau x.
Proof.
  intros sigma tau H x.
  destruct x as [|x]; simpl.
  - reflexivity.
  - rewrite H; reflexivity.
Qed.

Lemma subst_ext :
  forall t sigma tau,
    (forall x, sigma x = tau x) ->
    subst sigma t = subst tau t.
Proof.
  induction t as [x | c | l IHl r IHr | body IH]; intros sigma tau H; simpl.
  - apply H.
  - reflexivity.
  - rewrite (IHl sigma tau H), (IHr sigma tau H); reflexivity.
  - rewrite (IH (up_subst sigma) (up_subst tau)).
    + reflexivity.
    + apply up_subst_ext; exact H.
Qed.

Lemma subst_id :
  forall t, subst id_subst t = t.
Proof.
  induction t as [x | c | l IHl r IHr | body IH]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHl, IHr; reflexivity.
  - f_equal.
    transitivity (subst id_subst body).
    + apply subst_ext.
      intros [|x]; simpl.
      * reflexivity.
      * unfold shift.
        reflexivity.
    + exact IH.
Qed.

Lemma rename_as_subst :
  forall t rho,
    rename rho t = subst (fun x => RVar (rho x)) t.
Proof.
  induction t as [x | c | l IHl r IHr | body IH]; intros rho; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHl, IHr; reflexivity.
  - f_equal.
    rewrite IH.
    apply subst_ext.
    intros [|x]; reflexivity.
Qed.

Fixpoint well_scoped (depth : nat) (t : raw_term) : bool :=
  match t with
  | RVar x => Nat.ltb x depth
  | RConst _ => true
  | RApp l r => andb (well_scoped depth l) (well_scoped depth r)
  | RBind body => well_scoped (S depth) body
  end.

Definition closed_term (t : raw_term) : Prop :=
  well_scoped 0 t = true.

Lemma well_scoped_rename :
  forall t depth target rho,
    (forall x, x < depth -> rho x < target) ->
    well_scoped depth t = true ->
    well_scoped target (rename rho t) = true.
Proof.
  induction t as [x | c | l IHl r IHr | body IH]; intros depth target rho Hrho Hwf; simpl in *.
  - apply Nat.ltb_lt in Hwf.
    apply Nat.ltb_lt.
    apply Hrho; exact Hwf.
  - reflexivity.
  - apply andb_true_iff in Hwf as [Hl Hr].
    apply andb_true_iff.
    split.
    + apply IHl with (depth := depth); assumption.
    + apply IHr with (depth := depth); assumption.
  - apply IH with (depth := S depth).
    + intros [|x] Hx; simpl.
      * lia.
      * specialize (Hrho x ltac:(lia)); lia.
    + exact Hwf.
Qed.

Lemma well_scoped_shift :
  forall t depth,
    well_scoped depth t = true ->
    well_scoped (S depth) (shift t) = true.
Proof.
  intros t depth Hwf.
  unfold shift.
  apply well_scoped_rename with (depth := depth).
  - intros x Hx; lia.
  - exact Hwf.
Qed.

Lemma well_scoped_subst :
  forall t depth target sigma,
    (forall x, x < depth -> well_scoped target (sigma x) = true) ->
    well_scoped depth t = true ->
    well_scoped target (subst sigma t) = true.
Proof.
  induction t as [x | c | l IHl r IHr | body IH]; intros depth target sigma Hsigma Hwf; simpl in *.
  - apply Nat.ltb_lt in Hwf.
    apply Hsigma; exact Hwf.
  - reflexivity.
  - apply andb_true_iff in Hwf as [Hl Hr].
    apply andb_true_iff.
    split.
    + apply IHl with (depth := depth); assumption.
    + apply IHr with (depth := depth); assumption.
  - apply IH with (depth := S depth).
    + intros [|x] Hx; simpl.
      * apply Nat.ltb_lt; lia.
      * apply well_scoped_shift.
        apply Hsigma; lia.
    + exact Hwf.
Qed.

Theorem closed_rename :
  forall t rho,
    closed_term t ->
    closed_term (rename rho t).
Proof.
  intros t rho Hclosed.
  unfold closed_term in *.
  apply well_scoped_rename with (depth := 0).
  - intros x Hx; lia.
  - exact Hclosed.
Qed.

Theorem closed_subst :
  forall t sigma,
    closed_term t ->
    closed_term (subst sigma t).
Proof.
  intros t sigma Hclosed.
  unfold closed_term in *.
  apply well_scoped_subst with (depth := 0).
  - intros x Hx; lia.
  - exact Hclosed.
Qed.

Definition example_identity_body : raw_term :=
  RBind (RVar 0).

Lemma example_identity_body_closed :
  closed_term example_identity_body.
Proof.
  unfold closed_term, example_identity_body; simpl.
  reflexivity.
Qed.

Definition example_constant_application : raw_term :=
  RApp (RConst 0) example_identity_body.

Lemma example_constant_application_closed :
  closed_term example_constant_application.
Proof.
  unfold closed_term, example_constant_application; simpl.
  exact example_identity_body_closed.
Qed.

End FormalSystemFactoryStage2.
