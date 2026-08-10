From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryKernel.
Require Import FormalSystemFactoryRuleAPI.
Require Import FormalSystemFactoryCanonicalFuel.
Require Import FormalSystemFactoryPRRepresentation.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.
Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.
Module CF := FormalSystemFactoryCanonicalFuel.FormalSystemFactoryCanonicalFuel.
Module PRR := FormalSystemFactoryPRRepresentation.FormalSystemFactoryPRRepresentation.

Module FormalSystemFactoryPrimitiveRecursion.

Inductive EPRCode : Type :=
| EPRConst : nat -> EPRCode
| EPRArg : nat -> EPRCode
| EPRSucc : EPRCode -> EPRCode
| EPRPred : EPRCode -> EPRCode
| EPRAdd : EPRCode -> EPRCode -> EPRCode
| EPRMul : EPRCode -> EPRCode -> EPRCode
| EPREq : EPRCode -> EPRCode -> EPRCode
| EPRLe : EPRCode -> EPRCode -> EPRCode
| EPRNot : EPRCode -> EPRCode
| EPRAnd : EPRCode -> EPRCode -> EPRCode
| EPROr : EPRCode -> EPRCode -> EPRCode
| EPRIf : EPRCode -> EPRCode -> EPRCode -> EPRCode
| EPRRec : EPRCode -> EPRCode -> EPRCode -> EPRCode.

Fixpoint eval_EPR (c : EPRCode) : list nat -> nat :=
  match c with
  | EPRConst n => fun _ => n
  | EPRArg i => fun env => K.nth_default env i
  | EPRSucc a => fun env => S (eval_EPR a env)
  | EPRPred a => fun env => Nat.pred (eval_EPR a env)
  | EPRAdd a b => fun env => eval_EPR a env + eval_EPR b env
  | EPRMul a b => fun env => eval_EPR a env * eval_EPR b env
  | EPREq a b =>
      fun env => K.bool_to_nat (Nat.eqb (eval_EPR a env) (eval_EPR b env))
  | EPRLe a b =>
      fun env => K.bool_to_nat (Nat.leb (eval_EPR a env) (eval_EPR b env))
  | EPRNot a =>
      fun env => K.bool_to_nat (negb (K.nat_to_bool (eval_EPR a env)))
  | EPRAnd a b =>
      fun env =>
        K.bool_to_nat
          (andb (K.nat_to_bool (eval_EPR a env))
                (K.nat_to_bool (eval_EPR b env)))
  | EPROr a b =>
      fun env =>
        K.bool_to_nat
          (orb (K.nat_to_bool (eval_EPR a env))
               (K.nat_to_bool (eval_EPR b env)))
  | EPRIf guard then_code else_code =>
      fun env =>
        if K.nat_to_bool (eval_EPR guard env)
        then eval_EPR then_code env
        else eval_EPR else_code env
  | EPRRec bound base step =>
      fun env =>
        let n := eval_EPR bound env in
        let base_value := eval_EPR base env in
        let step_eval := eval_EPR step in
        let fix loop (k acc : nat) : nat :=
            match k with
            | 0 => acc
            | S k' => loop k' (step_eval (acc :: k' :: env))
            end in
        loop n base_value
  end.

Definition eval_EPR_bool (c : EPRCode) (env : list nat) : bool :=
  K.nat_to_bool (eval_EPR c env).

Fixpoint embed_PRCode (c : K.PRCode) : EPRCode :=
  match c with
  | K.PRConst n => EPRConst n
  | K.PRArg i => EPRArg i
  | K.PRSucc a => EPRSucc (embed_PRCode a)
  | K.PRPred a => EPRPred (embed_PRCode a)
  | K.PRAdd a b => EPRAdd (embed_PRCode a) (embed_PRCode b)
  | K.PRMul a b => EPRMul (embed_PRCode a) (embed_PRCode b)
  | K.PREq a b => EPREq (embed_PRCode a) (embed_PRCode b)
  | K.PRLe a b => EPRLe (embed_PRCode a) (embed_PRCode b)
  | K.PRNot a => EPRNot (embed_PRCode a)
  | K.PRAnd a b => EPRAnd (embed_PRCode a) (embed_PRCode b)
  | K.PROr a b => EPROr (embed_PRCode a) (embed_PRCode b)
  | K.PRIf guard then_code else_code =>
      EPRIf (embed_PRCode guard) (embed_PRCode then_code)
            (embed_PRCode else_code)
  end.

Lemma eval_embed_PRCode :
  forall c env,
    eval_EPR (embed_PRCode c) env = K.eval_PR c env.
Proof.
  induction c; intros env; simpl;
    try rewrite IHc;
    try rewrite IHc1;
    try rewrite IHc2;
    try rewrite IHc3;
    reflexivity.
Qed.

Lemma eval_embed_PRCode_bool :
  forall c env,
    eval_EPR_bool (embed_PRCode c) env = K.eval_PR_bool c env.
Proof.
  intros c env.
  unfold eval_EPR_bool, K.eval_PR_bool.
  rewrite eval_embed_PRCode.
  reflexivity.
Qed.

Definition EPR_relation_2 (f : nat -> nat -> bool) : Prop :=
  exists c : EPRCode, forall x y, f x y = eval_EPR_bool c [x; y].

Definition ERepresentsBinaryBool
           (f : nat -> nat -> bool)
           (code : EPRCode) : Prop :=
  forall x y, f x y = eval_EPR_bool code [x; y].

Definition ERepresentsChecker
           (spec : R.TheorySpec)
           (code : EPRCode) : Prop :=
  ERepresentsBinaryBool
    (fun proof_nat goal_nat => CF.check_proof_nat spec proof_nat goal_nat)
    code.

Record EPRCheckerCertificate (spec : R.TheorySpec) : Type := {
  epr_checker_code : EPRCode;
  epr_checker_correct : ERepresentsChecker spec epr_checker_code
}.

Definition embed_checker_certificate
           (spec : R.TheorySpec)
           (cert : PRR.PRCheckerCertificate spec)
  : EPRCheckerCertificate spec.
Proof.
  refine
    {|
      epr_checker_code := embed_PRCode (PRR.pr_checker_code spec cert);
      epr_checker_correct := _
    |}.
  unfold ERepresentsChecker, ERepresentsBinaryBool.
  intros proof_nat goal_nat.
  pose proof (PRR.pr_checker_correct spec cert proof_nat goal_nat) as Hcorrect.
  unfold PRR.RepresentsChecker, PRR.RepresentsBinaryBool in Hcorrect.
  unfold PRR.checker_function in Hcorrect.
  rewrite Hcorrect.
  symmetry.
  apply eval_embed_PRCode_bool.
Defined.

Record ETheory : Type := {
  etheory_signature : K.Signature;
  etheory_rules : list K.RuleSchema;
  eproof_check_code : EPRCode;
  econtradiction_code : nat
}.

Definition eproof_check (T : ETheory) (p j : nat) : bool :=
  eval_EPR_bool (eproof_check_code T) [p; j].

Definition EAcceptable (T : ETheory) : Prop :=
  EPR_relation_2 (eproof_check T).

Record CertifiedEPRTheory : Type := {
  certified_epr_rule_spec : R.TheorySpec;
  certified_epr_signature : K.Signature;
  certified_epr_contradiction_code : nat;
  certified_epr_checker : EPRCheckerCertificate certified_epr_rule_spec
}.

Definition certified_epr_theory (ct : CertifiedEPRTheory) : ETheory :=
  {|
    etheory_signature := certified_epr_signature ct;
    etheory_rules := [];
    eproof_check_code :=
      epr_checker_code
        (certified_epr_rule_spec ct)
        (certified_epr_checker ct);
    econtradiction_code := certified_epr_contradiction_code ct
  |}.

Theorem certified_epr_theory_agrees :
  forall ct proof_nat goal_nat,
    eproof_check (certified_epr_theory ct) proof_nat goal_nat =
    CF.check_proof_nat (certified_epr_rule_spec ct) proof_nat goal_nat.
Proof.
  intros ct proof_nat goal_nat.
  unfold eproof_check, certified_epr_theory.
  simpl.
  symmetry.
  apply epr_checker_correct.
Qed.

Theorem certified_epr_theory_acceptable :
  forall ct, EAcceptable (certified_epr_theory ct).
Proof.
  intro ct.
  unfold EAcceptable, EPR_relation_2, eproof_check.
  exists (eproof_check_code (certified_epr_theory ct)).
  intros proof_nat goal_nat.
  reflexivity.
Qed.

Definition add_by_rec_code : EPRCode :=
  EPRRec (EPRArg 0) (EPRArg 1) (EPRSucc (EPRArg 0)).

Fixpoint iter_succ (k acc : nat) : nat :=
  match k with
  | 0 => acc
  | S k' => iter_succ k' (S acc)
  end.

Lemma iter_succ_correct :
  forall x y, iter_succ x y = x + y.
Proof.
  induction x as [|x IH]; intros y; simpl.
  - reflexivity.
  - rewrite IH.
    lia.
Qed.

Lemma add_by_rec_loop :
  forall x y env,
    (let step_eval := eval_EPR (EPRSucc (EPRArg 0)) in
     let fix loop (k acc : nat) : nat :=
         match k with
         | 0 => acc
         | S k' => loop k' (step_eval (acc :: k' :: env))
         end in
     loop x y) = x + y.
Proof.
  intros x y env.
  change (iter_succ x y = x + y).
  apply iter_succ_correct.
Qed.

Lemma add_by_rec_code_correct :
  forall x y,
    eval_EPR add_by_rec_code [x; y] = x + y.
Proof.
  intros x y.
  unfold add_by_rec_code.
  simpl.
  apply (add_by_rec_loop x y [x; y]).
Qed.

Definition blocked_epr_checker_certificate :
  EPRCheckerCertificate R.example_blocked_theory :=
  embed_checker_certificate
    R.example_blocked_theory
    PRR.blocked_checker_certificate.

Definition blocked_certified_epr_theory : CertifiedEPRTheory :=
  {|
    certified_epr_rule_spec := R.example_blocked_theory;
    certified_epr_signature := PRR.one_sort_empty_signature;
    certified_epr_contradiction_code :=
      PRR.certified_contradiction_code PRR.blocked_certified_pr_theory;
    certified_epr_checker := blocked_epr_checker_certificate
  |}.

Lemma blocked_certified_epr_theory_rejects_all :
  forall proof_nat goal_nat,
    eproof_check
      (certified_epr_theory blocked_certified_epr_theory)
      proof_nat goal_nat = false.
Proof.
  intros proof_nat goal_nat.
  rewrite certified_epr_theory_agrees.
  apply PRR.blocked_nat_checker_rejects_all.
Qed.

End FormalSystemFactoryPrimitiveRecursion.
