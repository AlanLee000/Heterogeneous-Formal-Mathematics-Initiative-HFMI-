From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryStage2.

Import ListNotations.

Module S2 := FormalSystemFactoryStage2.FormalSystemFactoryStage2.

Module FormalSystemFactoryBindingAPI.

Definition term : Type := S2.raw_term.

Definition mk_var : nat -> term := S2.RVar.
Definition mk_const : nat -> term := S2.RConst.
Definition mk_app : term -> term -> term := S2.RApp.
Definition mk_bind : term -> term := S2.RBind.

Definition rename : S2.renaming -> term -> term := S2.rename.
Definition subst : S2.substitution -> term -> term := S2.subst.
Definition shift : term -> term := S2.shift.
Definition well_scoped : nat -> term -> bool := S2.well_scoped.
Definition closed : term -> Prop := S2.closed_term.

Definition replace_free (x : nat) (u : term) : S2.substitution :=
  fun y => if Nat.eqb y x then u else mk_var y.

Definition substitute_free (x : nat) (u t : term) : term :=
  subst (replace_free x u) t.

Definition instantiate_bound_subst (u : term) : S2.substitution :=
  fun y =>
    match y with
    | 0 => u
    | S z => mk_var z
    end.

Definition instantiate_bound (u body : term) : term :=
  subst (instantiate_bound_subst u) body.

Definition open_bind (u binder : term) : option term :=
  match binder with
  | S2.RBind body => Some (instantiate_bound u body)
  | _ => None
  end.

Definition beta_contract (operator argument : term) : option term :=
  match operator with
  | S2.RBind body => Some (instantiate_bound argument body)
  | _ => None
  end.

Record BindingAPI : Type := {
  api_term : Type;
  api_var : nat -> api_term;
  api_const : nat -> api_term;
  api_app : api_term -> api_term -> api_term;
  api_bind : api_term -> api_term;
  api_rename : S2.renaming -> api_term -> api_term;
  api_subst : S2.substitution -> api_term -> api_term;
  api_replace_free : nat -> api_term -> S2.substitution;
  api_substitute_free : nat -> api_term -> api_term -> api_term;
  api_instantiate_bound : api_term -> api_term -> api_term;
  api_open_bind : api_term -> api_term -> option api_term;
  api_beta_contract : api_term -> api_term -> option api_term;
  api_well_scoped : nat -> api_term -> bool;
  api_closed : api_term -> Prop
}.

Definition raw_binding_api : BindingAPI :=
  {|
    api_term := term;
    api_var := mk_var;
    api_const := mk_const;
    api_app := mk_app;
    api_bind := mk_bind;
    api_rename := rename;
    api_subst := subst;
    api_replace_free := replace_free;
    api_substitute_free := substitute_free;
    api_instantiate_bound := instantiate_bound;
    api_open_bind := open_bind;
    api_beta_contract := beta_contract;
    api_well_scoped := well_scoped;
    api_closed := closed
  |}.

Lemma replace_free_same :
  forall x u, replace_free x u x = u.
Proof.
  intros x u.
  unfold replace_free.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma replace_free_other :
  forall x y u,
    x <> y ->
    replace_free x u y = mk_var y.
Proof.
  intros x y u Hneq.
  unfold replace_free.
  destruct (Nat.eqb y x) eqn:Heq.
  - apply Nat.eqb_eq in Heq; subst; contradiction.
  - reflexivity.
Qed.

Lemma substitute_free_var_same :
  forall x u,
    substitute_free x u (mk_var x) = u.
Proof.
  intros x u.
  unfold substitute_free.
  simpl.
  apply replace_free_same.
Qed.

Lemma substitute_free_var_other :
  forall x y u,
    x <> y ->
    substitute_free x u (mk_var y) = mk_var y.
Proof.
  intros x y u Hneq.
  unfold substitute_free.
  simpl.
  apply replace_free_other.
  exact Hneq.
Qed.

Lemma instantiate_bound_var_zero :
  forall u,
    instantiate_bound u (mk_var 0) = u.
Proof.
  intros u; reflexivity.
Qed.

Lemma instantiate_bound_var_succ :
  forall u x,
    instantiate_bound u (mk_var (S x)) = mk_var x.
Proof.
  intros u x; reflexivity.
Qed.

Lemma open_bind_mk_bind :
  forall u body,
    open_bind u (mk_bind body) = Some (instantiate_bound u body).
Proof.
  intros u body; reflexivity.
Qed.

Lemma beta_contract_mk_bind :
  forall argument body,
    beta_contract (mk_bind body) argument =
    Some (instantiate_bound argument body).
Proof.
  intros argument body; reflexivity.
Qed.

Theorem api_rename_id :
  forall t,
    rename S2.id_ren t = t.
Proof.
  apply S2.rename_id.
Qed.

Theorem api_subst_id :
  forall t,
    subst S2.id_subst t = t.
Proof.
  apply S2.subst_id.
Qed.

Theorem api_closed_rename :
  forall t rho,
    closed t ->
    closed (rename rho t).
Proof.
  apply S2.closed_rename.
Qed.

Theorem api_closed_subst :
  forall t sigma,
    closed t ->
    closed (subst sigma t).
Proof.
  apply S2.closed_subst.
Qed.

Lemma instantiate_bound_closed :
  forall u body,
    closed u ->
    well_scoped 1 body = true ->
    closed (instantiate_bound u body).
Proof.
  intros u body Hu Hbody.
  unfold closed, instantiate_bound.
  apply S2.well_scoped_subst with (depth := 1).
  - intros [|x] Hx; simpl.
    + exact Hu.
    + lia.
  - exact Hbody.
Qed.

Theorem beta_contract_closed :
  forall operator argument result body,
    operator = mk_bind body ->
    beta_contract operator argument = Some result ->
    closed argument ->
    well_scoped 1 body = true ->
    closed result.
Proof.
  intros operator argument result body Hop Hbeta Harg Hbody.
  subst operator.
  simpl in Hbeta.
  inversion Hbeta; subst result.
  apply instantiate_bound_closed; assumption.
Qed.

Definition identity_operator : term :=
  mk_bind (mk_var 0).

Definition beta_identity_example : option term :=
  beta_contract identity_operator (mk_const 7).

Lemma beta_identity_example_value :
  beta_identity_example = Some (mk_const 7).
Proof.
  reflexivity.
Qed.

Lemma beta_identity_example_closed :
  beta_contract identity_operator (mk_const 7) = Some (mk_const 7) /\
  closed (mk_const 7).
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

End FormalSystemFactoryBindingAPI.
