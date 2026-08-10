From Stdlib Require Import Lists.List.

Require Import FormalSystemFactoryRuleAPI.
Require Import FormalSystemFactoryPrimitiveRecursion.
Require Import FormalSystemFactoryAllNatFactory.

Import ListNotations.

Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.
Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.
Module ANF := FormalSystemFactoryAllNatFactory.FormalSystemFactoryAllNatFactory.

Module FormalSystemFactoryAllNatRepresentation.

Definition all_nat_checker_function
           (factory : ANF.AllNatFormalSystemFactory)
           (theory_fuel proof_fuel goal_fuel
                        theory_nat proof_nat goal_nat : nat) : bool :=
  ANF.all_nat_factory_check_with_fuel
    factory
    theory_fuel proof_fuel goal_fuel
    theory_nat proof_nat goal_nat.

Definition ERepresentsAllNatChecker
           (factory : ANF.AllNatFormalSystemFactory)
           (code : EPR.EPRCode) : Prop :=
  forall theory_fuel proof_fuel goal_fuel
         theory_nat proof_nat goal_nat,
    all_nat_checker_function
      factory
      theory_fuel proof_fuel goal_fuel
      theory_nat proof_nat goal_nat =
    EPR.eval_EPR_bool
      code
      [ theory_fuel; proof_fuel; goal_fuel;
        theory_nat; proof_nat; goal_nat ].

Record EPRAllNatCheckerCertificate
       (factory : ANF.AllNatFormalSystemFactory) : Type := {
  epr_all_nat_checker_code : EPR.EPRCode;
  epr_all_nat_checker_correct :
    ERepresentsAllNatChecker factory epr_all_nat_checker_code
}.

Definition EPRAllNatFactoryRepresentable
           (factory : ANF.AllNatFormalSystemFactory) : Prop :=
  inhabited (EPRAllNatCheckerCertificate factory).

Inductive AllNatFactoryRepresentationStatus
          (factory : ANF.AllNatFormalSystemFactory) : Type :=
| AllNatFactoryRepresented :
    EPRAllNatCheckerCertificate factory ->
    AllNatFactoryRepresentationStatus factory
| AllNatFactoryNotYetCertified :
    AllNatFactoryRepresentationStatus factory.

Definition default_all_nat_factory_representation_status
  : AllNatFactoryRepresentationStatus ANF.default_all_nat_factory :=
  AllNatFactoryNotYetCertified ANF.default_all_nat_factory.

Theorem represented_all_nat_checker_agrees :
  forall factory
         (cert : EPRAllNatCheckerCertificate factory)
         theory_fuel proof_fuel goal_fuel
         theory_nat proof_nat goal_nat,
    all_nat_checker_function
      factory
      theory_fuel proof_fuel goal_fuel
      theory_nat proof_nat goal_nat =
    EPR.eval_EPR_bool
      (epr_all_nat_checker_code factory cert)
      [ theory_fuel; proof_fuel; goal_fuel;
        theory_nat; proof_nat; goal_nat ].
Proof.
  intros factory cert.
  apply epr_all_nat_checker_correct.
Qed.

Theorem represented_all_nat_accepts_iff_epr_true :
  forall factory
         (cert : EPRAllNatCheckerCertificate factory)
         theory_fuel proof_fuel goal_fuel
         theory_nat proof_nat goal_nat,
    ANF.all_nat_factory_accepts
      factory
      theory_fuel proof_fuel goal_fuel
      theory_nat proof_nat goal_nat <->
    EPR.eval_EPR_bool
      (epr_all_nat_checker_code factory cert)
      [ theory_fuel; proof_fuel; goal_fuel;
        theory_nat; proof_nat; goal_nat ] = true.
Proof.
  intros factory cert theory_fuel proof_fuel goal_fuel
         theory_nat proof_nat goal_nat.
  unfold ANF.all_nat_factory_accepts.
  change
    (all_nat_checker_function
       factory
       theory_fuel proof_fuel goal_fuel
       theory_nat proof_nat goal_nat = true <->
     EPR.eval_EPR_bool
       (epr_all_nat_checker_code factory cert)
       [ theory_fuel; proof_fuel; goal_fuel;
         theory_nat; proof_nat; goal_nat ] = true).
  rewrite
    (epr_all_nat_checker_correct
       factory cert
       theory_fuel proof_fuel goal_fuel
       theory_nat proof_nat goal_nat).
  split; intro H; exact H.
Qed.

Theorem represented_all_nat_checker_on_encoded_inputs :
  forall factory
         (cert : EPRAllNatCheckerCertificate factory)
         spec p goal,
    EPR.eval_EPR_bool
      (epr_all_nat_checker_code factory cert)
      [ ANF.theory_fuel_for spec;
        ANF.proof_fuel_for p;
        ANF.goal_fuel_for goal;
        ANF.encode_theory_for_all_nat_factory spec;
        ANF.encode_proof_for_all_nat_factory p;
        ANF.encode_goal_for_all_nat_factory goal ] =
    R.check_proof spec p goal.
Proof.
  intros factory cert spec p goal.
  rewrite <-
    (epr_all_nat_checker_correct
       factory cert
       (ANF.theory_fuel_for spec)
       (ANF.proof_fuel_for p)
       (ANF.goal_fuel_for goal)
       (ANF.encode_theory_for_all_nat_factory spec)
       (ANF.encode_proof_for_all_nat_factory p)
       (ANF.encode_goal_for_all_nat_factory goal)).
  unfold all_nat_checker_function.
  apply ANF.all_nat_factory_check_encoded_agrees.
Qed.

Theorem represented_all_nat_accepts_encoded_iff_checked :
  forall factory
         (cert : EPRAllNatCheckerCertificate factory)
         spec p goal,
    EPR.eval_EPR_bool
      (epr_all_nat_checker_code factory cert)
      [ ANF.theory_fuel_for spec;
        ANF.proof_fuel_for p;
        ANF.goal_fuel_for goal;
        ANF.encode_theory_for_all_nat_factory spec;
        ANF.encode_proof_for_all_nat_factory p;
        ANF.encode_goal_for_all_nat_factory goal ] = true <->
    R.Prf spec p goal.
Proof.
  intros factory cert spec p goal.
  rewrite represented_all_nat_checker_on_encoded_inputs.
  unfold R.Prf.
  split; intro H; exact H.
Qed.

Record CertifiedEPRAllNatFactory : Type := {
  certified_all_nat_factory : ANF.AllNatFormalSystemFactory;
  certified_all_nat_checker :
    EPRAllNatCheckerCertificate certified_all_nat_factory
}.

Definition certified_all_nat_checker_code
           (certified : CertifiedEPRAllNatFactory) : EPR.EPRCode :=
  epr_all_nat_checker_code
    (certified_all_nat_factory certified)
    (certified_all_nat_checker certified).

Definition certified_all_nat_check
           (certified : CertifiedEPRAllNatFactory)
           (theory_fuel proof_fuel goal_fuel
                        theory_nat proof_nat goal_nat : nat) : bool :=
  EPR.eval_EPR_bool
    (certified_all_nat_checker_code certified)
    [ theory_fuel; proof_fuel; goal_fuel;
      theory_nat; proof_nat; goal_nat ].

Theorem certified_all_nat_check_agrees :
  forall certified
         theory_fuel proof_fuel goal_fuel
         theory_nat proof_nat goal_nat,
    certified_all_nat_check
      certified
      theory_fuel proof_fuel goal_fuel
      theory_nat proof_nat goal_nat =
    ANF.all_nat_factory_check_with_fuel
      (certified_all_nat_factory certified)
      theory_fuel proof_fuel goal_fuel
      theory_nat proof_nat goal_nat.
Proof.
  intros certified theory_fuel proof_fuel goal_fuel
         theory_nat proof_nat goal_nat.
  unfold certified_all_nat_check, certified_all_nat_checker_code.
  symmetry.
  apply epr_all_nat_checker_correct.
Qed.

End FormalSystemFactoryAllNatRepresentation.
