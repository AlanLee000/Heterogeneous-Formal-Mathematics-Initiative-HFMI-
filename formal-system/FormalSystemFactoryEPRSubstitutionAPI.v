From Stdlib Require Import Lists.List.

Require Import FormalSystemFactoryKernel.
Require Import FormalSystemFactoryPrimitiveRecursion.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.
Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.

Module FormalSystemFactoryEPRSubstitutionAPI.

Fixpoint eval_EPR_codes
         (codes : list EPR.EPRCode) (env : list nat) : list nat :=
  match codes with
  | [] => []
  | code :: rest => EPR.eval_EPR code env :: eval_EPR_codes rest env
  end.

Record EPRSubstitutionCertificate
       (source : EPR.EPRCode) (subst : list EPR.EPRCode) : Type := {
  substituted_epr_code : EPR.EPRCode;
  substituted_epr_code_correct :
    forall env,
      EPR.eval_EPR substituted_epr_code env =
      EPR.eval_EPR source (eval_EPR_codes subst env)
}.

Lemma nth_default_eval_EPR_codes_nth_error :
  forall subst i code env,
    nth_error subst i = Some code ->
    K.nth_default (eval_EPR_codes subst env) i =
    EPR.eval_EPR code env.
Proof.
  induction subst as [|head rest IH]; intros i code env Hnth.
  - destruct i; discriminate.
  - destruct i as [|i].
    + inversion Hnth; subst.
      reflexivity.
    + simpl.
      apply IH.
      exact Hnth.
Qed.

Definition substitute_const_certificate
           (n : nat) (subst : list EPR.EPRCode)
  : EPRSubstitutionCertificate (EPR.EPRConst n) subst.
Proof.
  refine {| substituted_epr_code := EPR.EPRConst n |}.
  intro env.
  reflexivity.
Defined.

Definition substitute_arg_certificate
           (subst : list EPR.EPRCode)
           (i : nat) (code : EPR.EPRCode)
           (Hnth : nth_error subst i = Some code)
  : EPRSubstitutionCertificate (EPR.EPRArg i) subst.
Proof.
  refine {| substituted_epr_code := code |}.
  intro env.
  symmetry.
  apply nth_default_eval_EPR_codes_nth_error.
  exact Hnth.
Defined.

Definition substitute_succ_certificate
           (source : EPR.EPRCode) (subst : list EPR.EPRCode)
           (cert : EPRSubstitutionCertificate source subst)
  : EPRSubstitutionCertificate (EPR.EPRSucc source) subst.
Proof.
  refine
    {|
      substituted_epr_code :=
        EPR.EPRSucc (substituted_epr_code source subst cert)
    |}.
  intro env.
  simpl.
  rewrite (substituted_epr_code_correct source subst cert env).
  reflexivity.
Defined.

Definition substitute_pred_certificate
           (source : EPR.EPRCode) (subst : list EPR.EPRCode)
           (cert : EPRSubstitutionCertificate source subst)
  : EPRSubstitutionCertificate (EPR.EPRPred source) subst.
Proof.
  refine
    {|
      substituted_epr_code :=
        EPR.EPRPred (substituted_epr_code source subst cert)
    |}.
  intro env.
  simpl.
  rewrite (substituted_epr_code_correct source subst cert env).
  reflexivity.
Defined.

Definition substitute_binary_certificate
           (constructor : EPR.EPRCode -> EPR.EPRCode -> EPR.EPRCode)
           (semantic : nat -> nat -> nat)
           (source_left source_right : EPR.EPRCode)
           (subst : list EPR.EPRCode)
           (left_cert : EPRSubstitutionCertificate source_left subst)
           (right_cert : EPRSubstitutionCertificate source_right subst)
           (Hconstructor :
              forall left right env,
                EPR.eval_EPR (constructor left right) env =
                semantic
                  (EPR.eval_EPR left env)
                  (EPR.eval_EPR right env))
  : EPRSubstitutionCertificate
      (constructor source_left source_right) subst :=
  {|
    substituted_epr_code :=
      constructor
        (substituted_epr_code source_left subst left_cert)
        (substituted_epr_code source_right subst right_cert);
    substituted_epr_code_correct :=
      fun env =>
        eq_trans
          (Hconstructor
             (substituted_epr_code source_left subst left_cert)
             (substituted_epr_code source_right subst right_cert)
             env)
          (eq_trans
             (f_equal2 semantic
                (substituted_epr_code_correct
                   source_left subst left_cert env)
                (substituted_epr_code_correct
                   source_right subst right_cert env))
             (eq_sym
                (Hconstructor source_left source_right
                   (eval_EPR_codes subst env))))
  |}.

Definition substitute_add_certificate
           (left right : EPR.EPRCode) (subst : list EPR.EPRCode)
           (left_cert : EPRSubstitutionCertificate left subst)
           (right_cert : EPRSubstitutionCertificate right subst)
  : EPRSubstitutionCertificate (EPR.EPRAdd left right) subst :=
  substitute_binary_certificate
    EPR.EPRAdd Nat.add left right subst left_cert right_cert
    (fun _ _ _ => eq_refl).

Definition substitute_mul_certificate
           (left right : EPR.EPRCode) (subst : list EPR.EPRCode)
           (left_cert : EPRSubstitutionCertificate left subst)
           (right_cert : EPRSubstitutionCertificate right subst)
  : EPRSubstitutionCertificate (EPR.EPRMul left right) subst :=
  substitute_binary_certificate
    EPR.EPRMul Nat.mul left right subst left_cert right_cert
    (fun _ _ _ => eq_refl).

Definition substitute_eq_certificate
           (left right : EPR.EPRCode) (subst : list EPR.EPRCode)
           (left_cert : EPRSubstitutionCertificate left subst)
           (right_cert : EPRSubstitutionCertificate right subst)
  : EPRSubstitutionCertificate (EPR.EPREq left right) subst :=
  substitute_binary_certificate
    EPR.EPREq
    (fun x y => K.bool_to_nat (Nat.eqb x y))
    left right subst left_cert right_cert
    (fun _ _ _ => eq_refl).

Definition substitute_le_certificate
           (left right : EPR.EPRCode) (subst : list EPR.EPRCode)
           (left_cert : EPRSubstitutionCertificate left subst)
           (right_cert : EPRSubstitutionCertificate right subst)
  : EPRSubstitutionCertificate (EPR.EPRLe left right) subst :=
  substitute_binary_certificate
    EPR.EPRLe
    (fun x y => K.bool_to_nat (Nat.leb x y))
    left right subst left_cert right_cert
    (fun _ _ _ => eq_refl).

Definition substitute_not_certificate
           (source : EPR.EPRCode) (subst : list EPR.EPRCode)
           (cert : EPRSubstitutionCertificate source subst)
  : EPRSubstitutionCertificate (EPR.EPRNot source) subst.
Proof.
  refine
    {|
      substituted_epr_code :=
        EPR.EPRNot (substituted_epr_code source subst cert)
    |}.
  intro env.
  simpl.
  rewrite (substituted_epr_code_correct source subst cert env).
  reflexivity.
Defined.

Definition substitute_and_certificate
           (left right : EPR.EPRCode) (subst : list EPR.EPRCode)
           (left_cert : EPRSubstitutionCertificate left subst)
           (right_cert : EPRSubstitutionCertificate right subst)
  : EPRSubstitutionCertificate (EPR.EPRAnd left right) subst :=
  substitute_binary_certificate
    EPR.EPRAnd
    (fun x y =>
       K.bool_to_nat (andb (K.nat_to_bool x) (K.nat_to_bool y)))
    left right subst left_cert right_cert
    (fun _ _ _ => eq_refl).

Definition substitute_or_certificate
           (left right : EPR.EPRCode) (subst : list EPR.EPRCode)
           (left_cert : EPRSubstitutionCertificate left subst)
           (right_cert : EPRSubstitutionCertificate right subst)
  : EPRSubstitutionCertificate (EPR.EPROr left right) subst :=
  substitute_binary_certificate
    EPR.EPROr
    (fun x y =>
       K.bool_to_nat (orb (K.nat_to_bool x) (K.nat_to_bool y)))
    left right subst left_cert right_cert
    (fun _ _ _ => eq_refl).

Definition substitute_if_certificate
           (guard then_code else_code : EPR.EPRCode)
           (subst : list EPR.EPRCode)
           (guard_cert : EPRSubstitutionCertificate guard subst)
           (then_cert : EPRSubstitutionCertificate then_code subst)
           (else_cert : EPRSubstitutionCertificate else_code subst)
  : EPRSubstitutionCertificate
      (EPR.EPRIf guard then_code else_code) subst.
Proof.
  refine
    {|
      substituted_epr_code :=
        EPR.EPRIf
          (substituted_epr_code guard subst guard_cert)
          (substituted_epr_code then_code subst then_cert)
          (substituted_epr_code else_code subst else_cert);
      substituted_epr_code_correct := _
    |}.
  intro env.
  simpl.
  rewrite (substituted_epr_code_correct guard subst guard_cert env).
  destruct
    (K.nat_to_bool
       (EPR.eval_EPR guard (eval_EPR_codes subst env))).
  - apply substituted_epr_code_correct.
  - apply substituted_epr_code_correct.
Defined.

Definition EPRStepSubstitutionAgrees
           (subst step_subst : list EPR.EPRCode) : Prop :=
  forall acc counter env,
    eval_EPR_codes step_subst (acc :: counter :: env) =
    acc :: counter :: eval_EPR_codes subst env.

Record EPRRecSubstitutionBoundary
       (bound base step : EPR.EPRCode)
       (subst step_subst : list EPR.EPRCode) : Type := {
  epr_rec_bound_certificate :
    EPRSubstitutionCertificate bound subst;
  epr_rec_base_certificate :
    EPRSubstitutionCertificate base subst;
  epr_rec_step_certificate :
    EPRSubstitutionCertificate step step_subst;
  epr_rec_step_subst_agrees :
    EPRStepSubstitutionAgrees subst step_subst;
  epr_rec_substitution_certificate :
    EPRSubstitutionCertificate (EPR.EPRRec bound base step) subst
}.

Definition substitute_pair
           (source : EPR.EPRCode) (subst : list EPR.EPRCode)
  : Type :=
  EPRSubstitutionCertificate source subst.

End FormalSystemFactoryEPRSubstitutionAPI.
