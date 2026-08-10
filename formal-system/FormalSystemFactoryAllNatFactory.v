From Stdlib Require Import Lists.List.

Require Import FormalSystemFactoryRuleAPI.
Require Import FormalSystemFactoryStructuralCodec.
Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryMRBackend.
Require Import FormalSystemFactoryEndToEnd.
Require Import FormalSystemFactoryTheoryCodec.

Import ListNotations.

Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.
Module SC := FormalSystemFactoryStructuralCodec.FormalSystemFactoryStructuralCodec.
Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module MRB := FormalSystemFactoryMRBackend.FormalSystemFactoryMRBackend.
Module E2E := FormalSystemFactoryEndToEnd.FormalSystemFactoryEndToEnd.
Module TC := FormalSystemFactoryTheoryCodec.FormalSystemFactoryTheoryCodec.

Module FormalSystemFactoryAllNatFactory.

Record AllNatFormalSystemFactory : Type := {
  all_nat_factory_rule_api : R.RuleAPI;
  all_nat_factory_backend : MRB.MRDecoderBackend
}.

Definition all_nat_factory_check_with_fuel
           (factory : AllNatFormalSystemFactory)
           (theory_fuel proof_fuel goal_fuel
                        theory_nat proof_nat goal_nat : nat) : bool :=
  TC.backend_decoded_all_nat_check_proof_with_fuel
    (all_nat_factory_backend factory)
    theory_fuel proof_fuel goal_fuel
    theory_nat proof_nat goal_nat.

Definition theory_fuel_for (spec : R.TheorySpec) : nat :=
  S (NC.code_depth (TC.encode_theory_spec spec)).

Definition proof_fuel_for (p : R.proof_object) : nat :=
  E2E.proof_fuel_for p.

Definition goal_fuel_for (goal : R.judgment) : nat :=
  E2E.goal_fuel_for goal.

Definition encode_theory_for_all_nat_factory
           (spec : R.TheorySpec) : nat :=
  TC.encode_theory_spec_nat spec.

Definition encode_proof_for_all_nat_factory
           (p : R.proof_object) : nat :=
  E2E.encode_proof_for_factory p.

Definition encode_goal_for_all_nat_factory
           (goal : R.judgment) : nat :=
  E2E.encode_goal_for_factory goal.

Theorem all_nat_factory_check_encoded_agrees :
  forall factory spec p goal,
    all_nat_factory_check_with_fuel
      factory
      (theory_fuel_for spec)
      (proof_fuel_for p)
      (goal_fuel_for goal)
      (encode_theory_for_all_nat_factory spec)
      (encode_proof_for_all_nat_factory p)
      (encode_goal_for_all_nat_factory goal) =
    R.check_proof spec p goal.
Proof.
  intros factory spec p goal.
  unfold all_nat_factory_check_with_fuel,
         theory_fuel_for, proof_fuel_for, goal_fuel_for,
         encode_theory_for_all_nat_factory,
         encode_proof_for_all_nat_factory,
         encode_goal_for_all_nat_factory,
         E2E.proof_fuel_for, E2E.goal_fuel_for,
         E2E.encode_proof_for_factory,
         E2E.encode_goal_for_factory.
  apply TC.backend_decoded_all_nat_check_proof_agrees.
Qed.

Definition all_nat_factory_accepts
           (factory : AllNatFormalSystemFactory)
           (theory_fuel proof_fuel goal_fuel
                        theory_nat proof_nat goal_nat : nat) : Prop :=
  all_nat_factory_check_with_fuel
    factory theory_fuel proof_fuel goal_fuel
    theory_nat proof_nat goal_nat = true.

Theorem all_nat_factory_accepts_iff_checked :
  forall factory spec p goal,
    all_nat_factory_accepts
      factory
      (theory_fuel_for spec)
      (proof_fuel_for p)
      (goal_fuel_for goal)
      (encode_theory_for_all_nat_factory spec)
      (encode_proof_for_all_nat_factory p)
      (encode_goal_for_all_nat_factory goal) <->
    R.Prf spec p goal.
Proof.
  intros factory spec p goal.
  unfold all_nat_factory_accepts, R.Prf.
  rewrite all_nat_factory_check_encoded_agrees.
  split; intro H; exact H.
Qed.

Definition instantiate_fixed_factory
           (factory : AllNatFormalSystemFactory)
           (spec : R.TheorySpec) : E2E.FormalSystemFactory :=
  E2E.make_formal_system_factory
    (all_nat_factory_backend factory)
    spec.

Theorem all_nat_factory_refines_fixed_factory :
  forall factory spec p goal,
    all_nat_factory_check_with_fuel
      factory
      (theory_fuel_for spec)
      (proof_fuel_for p)
      (goal_fuel_for goal)
      (encode_theory_for_all_nat_factory spec)
      (encode_proof_for_all_nat_factory p)
      (encode_goal_for_all_nat_factory goal) =
    E2E.factory_check_nat_with_fuel
      (instantiate_fixed_factory factory spec)
      (proof_fuel_for p)
      (goal_fuel_for goal)
      (encode_proof_for_all_nat_factory p)
      (encode_goal_for_all_nat_factory goal).
Proof.
  intros factory spec p goal.
  rewrite all_nat_factory_check_encoded_agrees.
  unfold instantiate_fixed_factory,
         proof_fuel_for, goal_fuel_for,
         encode_proof_for_all_nat_factory,
         encode_goal_for_all_nat_factory.
  rewrite E2E.factory_check_encoded_agrees.
  reflexivity.
Qed.

Record AllNatFactoryCorrectnessCertificate
       (factory : AllNatFormalSystemFactory) : Prop := {
  all_nat_certificate_encoded_agrees :
    forall spec p goal,
      all_nat_factory_check_with_fuel
        factory
        (theory_fuel_for spec)
        (proof_fuel_for p)
        (goal_fuel_for goal)
        (encode_theory_for_all_nat_factory spec)
        (encode_proof_for_all_nat_factory p)
        (encode_goal_for_all_nat_factory goal) =
      R.check_proof spec p goal;
  all_nat_certificate_refines_fixed :
    forall spec p goal,
      all_nat_factory_check_with_fuel
        factory
        (theory_fuel_for spec)
        (proof_fuel_for p)
        (goal_fuel_for goal)
        (encode_theory_for_all_nat_factory spec)
        (encode_proof_for_all_nat_factory p)
        (encode_goal_for_all_nat_factory goal) =
      E2E.factory_check_nat_with_fuel
        (instantiate_fixed_factory factory spec)
        (proof_fuel_for p)
        (goal_fuel_for goal)
        (encode_proof_for_all_nat_factory p)
        (encode_goal_for_all_nat_factory goal)
}.

Definition make_all_nat_factory_certificate
           (factory : AllNatFormalSystemFactory)
  : AllNatFactoryCorrectnessCertificate factory :=
  {|
    all_nat_certificate_encoded_agrees :=
      all_nat_factory_check_encoded_agrees factory;
    all_nat_certificate_refines_fixed :=
      all_nat_factory_refines_fixed_factory factory
  |}.

Definition make_all_nat_formal_system_factory
           (backend : MRB.MRDecoderBackend)
  : AllNatFormalSystemFactory :=
  {|
    all_nat_factory_rule_api := R.raw_rule_api;
    all_nat_factory_backend := backend
  |}.

Definition default_all_nat_factory : AllNatFormalSystemFactory :=
  make_all_nat_formal_system_factory MRB.default_mr_decoder_backend.

Definition default_all_nat_factory_certificate
  : AllNatFactoryCorrectnessCertificate default_all_nat_factory :=
  make_all_nat_factory_certificate default_all_nat_factory.

Theorem default_all_nat_factory_checks_rule :
  all_nat_factory_check_with_fuel
    default_all_nat_factory
    (theory_fuel_for R.example_rule_theory)
    (proof_fuel_for R.example_rule_proof)
    (goal_fuel_for (R.rule_conclusion R.example_rule))
    (encode_theory_for_all_nat_factory R.example_rule_theory)
    (encode_proof_for_all_nat_factory R.example_rule_proof)
    (encode_goal_for_all_nat_factory
       (R.rule_conclusion R.example_rule)) = true.
Proof.
  rewrite all_nat_factory_check_encoded_agrees.
  exact R.example_rule_checked.
Qed.

Theorem default_all_nat_factory_accepts_rule :
  all_nat_factory_accepts
    default_all_nat_factory
    (theory_fuel_for R.example_rule_theory)
    (proof_fuel_for R.example_rule_proof)
    (goal_fuel_for (R.rule_conclusion R.example_rule))
    (encode_theory_for_all_nat_factory R.example_rule_theory)
    (encode_proof_for_all_nat_factory R.example_rule_proof)
    (encode_goal_for_all_nat_factory
       (R.rule_conclusion R.example_rule)).
Proof.
  exact default_all_nat_factory_checks_rule.
Qed.

End FormalSystemFactoryAllNatFactory.
