From Stdlib Require Import Lists.List.

Require Import FormalSystemFactoryRuleAPI.
Require Import FormalSystemFactoryStructuralCodec.
Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryMRBackend.
Require Import FormalSystemFactoryMRStructuralDecoder.

Import ListNotations.

Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.
Module SC := FormalSystemFactoryStructuralCodec.FormalSystemFactoryStructuralCodec.
Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module MRB := FormalSystemFactoryMRBackend.FormalSystemFactoryMRBackend.
Module MSD := FormalSystemFactoryMRStructuralDecoder.FormalSystemFactoryMRStructuralDecoder.

Module FormalSystemFactoryEndToEnd.

Record FormalSystemFactory : Type := {
  factory_rule_api : R.RuleAPI;
  factory_backend : MRB.MRDecoderBackend;
  factory_theory : R.TheorySpec
}.

Definition factory_check_nat_with_fuel
           (factory : FormalSystemFactory)
           (proof_fuel goal_fuel proof_nat goal_nat : nat) : bool :=
  MSD.backend_decoded_nat_check_proof_with_fuel
    (factory_backend factory)
    (factory_theory factory)
    proof_fuel goal_fuel proof_nat goal_nat.

Definition proof_fuel_for (p : R.proof_object) : nat :=
  S (NC.code_depth (SC.encode_proof_object p)).

Definition goal_fuel_for (goal : R.judgment) : nat :=
  S (NC.code_depth (SC.encode_judgment goal)).

Definition encode_proof_for_factory (p : R.proof_object) : nat :=
  NC.encode_proof_object_nat p.

Definition encode_goal_for_factory (goal : R.judgment) : nat :=
  NC.encode_judgment_nat goal.

Theorem factory_check_nat_with_fuel_agrees_with_nat :
  forall factory proof_fuel goal_fuel proof_nat goal_nat,
    factory_check_nat_with_fuel
      factory proof_fuel goal_fuel proof_nat goal_nat =
    NC.decoded_nat_check_proof_with_fuel
      (factory_theory factory)
      proof_fuel goal_fuel proof_nat goal_nat.
Proof.
  intros factory proof_fuel goal_fuel proof_nat goal_nat.
  unfold factory_check_nat_with_fuel.
  apply MSD.backend_decoded_nat_check_proof_agrees_with_nat.
Qed.

Theorem factory_check_encoded_agrees :
  forall factory p goal,
    factory_check_nat_with_fuel
      factory
      (proof_fuel_for p)
      (goal_fuel_for goal)
      (encode_proof_for_factory p)
      (encode_goal_for_factory goal) =
    R.check_proof (factory_theory factory) p goal.
Proof.
  intros factory p goal.
  unfold factory_check_nat_with_fuel, proof_fuel_for, goal_fuel_for,
         encode_proof_for_factory, encode_goal_for_factory.
  apply MSD.backend_decoded_nat_check_proof_agrees.
Qed.

Definition factory_accepts_encoded
           (factory : FormalSystemFactory)
           (proof_fuel goal_fuel proof_nat goal_nat : nat) : Prop :=
  factory_check_nat_with_fuel
    factory proof_fuel goal_fuel proof_nat goal_nat = true.

Theorem factory_accepts_encoded_iff_checked :
  forall factory p goal,
    factory_accepts_encoded
      factory
      (proof_fuel_for p)
      (goal_fuel_for goal)
      (encode_proof_for_factory p)
      (encode_goal_for_factory goal) <->
    R.Prf (factory_theory factory) p goal.
Proof.
  intros factory p goal.
  unfold factory_accepts_encoded, R.Prf.
  rewrite factory_check_encoded_agrees.
  split; intro H; exact H.
Qed.

Record FactoryCorrectnessCertificate
       (factory : FormalSystemFactory) : Prop := {
  certificate_backend_agrees :
    forall proof_fuel goal_fuel proof_nat goal_nat,
      factory_check_nat_with_fuel
        factory proof_fuel goal_fuel proof_nat goal_nat =
      NC.decoded_nat_check_proof_with_fuel
        (factory_theory factory)
        proof_fuel goal_fuel proof_nat goal_nat;
  certificate_encoded_agrees :
    forall p goal,
      factory_check_nat_with_fuel
        factory
        (proof_fuel_for p)
        (goal_fuel_for goal)
        (encode_proof_for_factory p)
        (encode_goal_for_factory goal) =
      R.check_proof (factory_theory factory) p goal
}.

Definition make_factory_certificate
           (factory : FormalSystemFactory)
  : FactoryCorrectnessCertificate factory :=
  {|
    certificate_backend_agrees :=
      factory_check_nat_with_fuel_agrees_with_nat factory;
    certificate_encoded_agrees :=
      factory_check_encoded_agrees factory
  |}.

Definition make_formal_system_factory
           (backend : MRB.MRDecoderBackend)
           (spec : R.TheorySpec) : FormalSystemFactory :=
  {|
    factory_rule_api := R.raw_rule_api;
    factory_backend := backend;
    factory_theory := spec
  |}.

Definition default_example_factory : FormalSystemFactory :=
  make_formal_system_factory
    MRB.default_mr_decoder_backend
    R.example_rule_theory.

Definition default_example_factory_certificate
  : FactoryCorrectnessCertificate default_example_factory :=
  make_factory_certificate default_example_factory.

Theorem default_example_factory_checks_rule :
  factory_check_nat_with_fuel
    default_example_factory
    (proof_fuel_for R.example_rule_proof)
    (goal_fuel_for (R.rule_conclusion R.example_rule))
    (encode_proof_for_factory R.example_rule_proof)
    (encode_goal_for_factory (R.rule_conclusion R.example_rule)) = true.
Proof.
  rewrite factory_check_encoded_agrees.
  exact R.example_rule_checked.
Qed.

Theorem default_example_factory_accepts_rule :
  factory_accepts_encoded
    default_example_factory
    (proof_fuel_for R.example_rule_proof)
    (goal_fuel_for (R.rule_conclusion R.example_rule))
    (encode_proof_for_factory R.example_rule_proof)
    (encode_goal_for_factory (R.rule_conclusion R.example_rule)).
Proof.
  exact default_example_factory_checks_rule.
Qed.

End FormalSystemFactoryEndToEnd.
