From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.

Require Import FormalSystemFactoryKernel.
Require Import FormalSystemFactoryRuleAPI.
Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryCanonicalFuel.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.
Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.
Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module CF := FormalSystemFactoryCanonicalFuel.FormalSystemFactoryCanonicalFuel.

Module FormalSystemFactoryPRRepresentation.

Definition RepresentsBinaryBool
           (f : nat -> nat -> bool)
           (code : K.PRCode) : Prop :=
  forall x y, f x y = K.eval_PR_bool code [x; y].

Definition checker_function (spec : R.TheorySpec) : nat -> nat -> bool :=
  fun proof_nat goal_nat => CF.check_proof_nat spec proof_nat goal_nat.

Definition RepresentsChecker
           (spec : R.TheorySpec)
           (code : K.PRCode) : Prop :=
  RepresentsBinaryBool (checker_function spec) code.

Record PRCheckerCertificate (spec : R.TheorySpec) : Type := {
  pr_checker_code : K.PRCode;
  pr_checker_correct : RepresentsChecker spec pr_checker_code
}.

Definition PRRepresentableChecker (spec : R.TheorySpec) : Prop :=
  inhabited (PRCheckerCertificate spec).

Inductive CheckerRepresentationStatus (spec : R.TheorySpec) : Type :=
| CheckerRepresented : PRCheckerCertificate spec -> CheckerRepresentationStatus spec
| CheckerNotYetCertified : CheckerRepresentationStatus spec.

Definition canonical_checker_status
           (spec : R.TheorySpec) : CheckerRepresentationStatus spec :=
  CheckerNotYetCertified spec.

Record CertifiedPRTheory : Type := {
  certified_rule_spec : R.TheorySpec;
  certified_signature : K.Signature;
  certified_contradiction_code : nat;
  certified_checker : PRCheckerCertificate certified_rule_spec
}.

Definition certified_checker_code (ct : CertifiedPRTheory) : K.PRCode :=
  pr_checker_code (certified_rule_spec ct) (certified_checker ct).

Definition certified_kernel_theory (ct : CertifiedPRTheory) : K.Theory :=
  {|
    K.theory_signature := certified_signature ct;
    K.theory_rules := [];
    K.proof_check_code := certified_checker_code ct;
    K.contradiction_code := certified_contradiction_code ct
  |}.

Theorem certified_kernel_theory_agrees :
  forall ct proof_nat goal_nat,
    K.proof_check (certified_kernel_theory ct) proof_nat goal_nat =
    CF.check_proof_nat (certified_rule_spec ct) proof_nat goal_nat.
Proof.
  intros ct proof_nat goal_nat.
  unfold K.proof_check, certified_kernel_theory, certified_checker_code.
  simpl.
  symmetry.
  apply pr_checker_correct.
Qed.

Theorem certified_kernel_theory_acceptable :
  forall ct, K.Acceptable (certified_kernel_theory ct).
Proof.
  intro ct.
  unfold K.Acceptable, K.PR_relation_2, K.proof_check.
  exists (certified_checker_code ct).
  intros proof_nat goal_nat.
  unfold certified_kernel_theory.
  reflexivity.
Qed.

Lemma blocked_rule_checker_rejects_all :
  forall p goal,
    R.check_proof R.example_blocked_theory p goal = false.
Proof.
  intros p goal.
  destruct p as [j | rule_index subproofs].
  - simpl.
    destruct (R.judgment_eqb j goal); reflexivity.
  - destruct rule_index as [|rule_index].
    + simpl.
      reflexivity.
    + simpl.
      destruct rule_index; reflexivity.
Qed.

Lemma blocked_nat_checker_rejects_all :
  forall proof_nat goal_nat,
    CF.check_proof_nat R.example_blocked_theory proof_nat goal_nat = false.
Proof.
  intros proof_nat goal_nat.
  unfold CF.check_proof_nat.
  destruct (CF.decode_proof_object_nat proof_nat) as [p |].
  - destruct (CF.decode_judgment_nat goal_nat) as [goal |].
    + apply blocked_rule_checker_rejects_all.
    + reflexivity.
  - destruct (CF.decode_judgment_nat goal_nat); reflexivity.
Qed.

Definition false_checker_code : K.PRCode := K.PRConst 0.

Lemma false_checker_code_evaluates_false :
  forall proof_nat goal_nat,
    K.eval_PR_bool false_checker_code [proof_nat; goal_nat] = false.
Proof.
  intros proof_nat goal_nat.
  reflexivity.
Qed.

Definition blocked_checker_certificate :
  PRCheckerCertificate R.example_blocked_theory.
Proof.
  refine
    {|
      pr_checker_code := false_checker_code;
      pr_checker_correct := _
    |}.
  intros proof_nat goal_nat.
  rewrite blocked_nat_checker_rejects_all.
  rewrite false_checker_code_evaluates_false.
  reflexivity.
Defined.

Definition one_sort_empty_signature : K.Signature :=
  {|
    K.sort_count := 1;
    K.constructor_count := 0;
    K.constructor_arity := fun _ => 0;
    K.constructor_result := fun _ => 0
  |}.

Definition blocked_certified_pr_theory : CertifiedPRTheory :=
  {|
    certified_rule_spec := R.example_blocked_theory;
    certified_signature := one_sort_empty_signature;
    certified_contradiction_code :=
      NC.encode_judgment_nat (R.theory_contradiction R.example_blocked_theory);
    certified_checker := blocked_checker_certificate
  |}.

Lemma blocked_certified_kernel_rejects_all :
  forall proof_nat goal_nat,
    K.proof_check
      (certified_kernel_theory blocked_certified_pr_theory)
      proof_nat goal_nat = false.
Proof.
  intros proof_nat goal_nat.
  rewrite certified_kernel_theory_agrees.
  apply blocked_nat_checker_rejects_all.
Qed.

Lemma blocked_certified_kernel_acceptable :
  K.Acceptable (certified_kernel_theory blocked_certified_pr_theory).
Proof.
  apply certified_kernel_theory_acceptable.
Qed.

End FormalSystemFactoryPRRepresentation.
