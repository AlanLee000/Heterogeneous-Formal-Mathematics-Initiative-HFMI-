From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryKernel.
Require Import FormalSystemFactoryPrimitiveRecursion.
Require Import FormalSystemFactoryEPRSubstitutionAPI.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.
Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.
Module SUB := FormalSystemFactoryEPRSubstitutionAPI.FormalSystemFactoryEPRSubstitutionAPI.

Module FormalSystemFactoryEPRRecSubstitution.

Fixpoint insert_at (cutoff : nat) (prefix env : list nat) : list nat :=
  match cutoff, env with
  | 0, _ => prefix ++ env
  | S cutoff', [] => prefix
  | S cutoff', x :: xs => x :: insert_at cutoff' prefix xs
  end.

Lemma nth_default_app_right :
  forall xs ys i,
    K.nth_default (xs ++ ys) (length xs + i) =
    K.nth_default ys i.
Proof.
  induction xs as [|x xs IH]; intros ys i.
  - reflexivity.
  - simpl.
    apply IH.
Qed.

Lemma nth_default_insert_left :
  forall cutoff prefix env i,
    cutoff <= length env ->
    i < cutoff ->
    K.nth_default (insert_at cutoff prefix env) i =
    K.nth_default env i.
Proof.
  induction cutoff as [|cutoff IH]; intros prefix env i Hcut Hlt.
  - lia.
  - destruct env as [|x xs]; simpl in Hcut; [lia |].
    destruct i as [|i].
    + reflexivity.
    + simpl in Hlt.
      simpl.
      apply IH; lia.
Qed.

Lemma nth_default_insert_right :
  forall cutoff prefix env i,
    cutoff <= length env ->
    cutoff <= i ->
    K.nth_default
      (insert_at cutoff prefix env)
      (length prefix + i) =
    K.nth_default env i.
Proof.
  induction cutoff as [|cutoff IH]; intros prefix env i Hcut Hle.
  - simpl.
    apply nth_default_app_right.
  - destruct env as [|x xs]; simpl in Hcut; [lia |].
    destruct i as [|i]; [lia |].
    simpl.
    replace (length prefix + S i) with (S (length prefix + i)) by lia.
    simpl.
    apply IH; lia.
Qed.

Fixpoint shift_EPR_above
         (amount cutoff : nat) (code : EPR.EPRCode) : EPR.EPRCode :=
  match code with
  | EPR.EPRConst n => EPR.EPRConst n
  | EPR.EPRArg i =>
      if Nat.ltb i cutoff
      then EPR.EPRArg i
      else EPR.EPRArg (amount + i)
  | EPR.EPRSucc a => EPR.EPRSucc (shift_EPR_above amount cutoff a)
  | EPR.EPRPred a => EPR.EPRPred (shift_EPR_above amount cutoff a)
  | EPR.EPRAdd a b =>
      EPR.EPRAdd
        (shift_EPR_above amount cutoff a)
        (shift_EPR_above amount cutoff b)
  | EPR.EPRMul a b =>
      EPR.EPRMul
        (shift_EPR_above amount cutoff a)
        (shift_EPR_above amount cutoff b)
  | EPR.EPREq a b =>
      EPR.EPREq
        (shift_EPR_above amount cutoff a)
        (shift_EPR_above amount cutoff b)
  | EPR.EPRLe a b =>
      EPR.EPRLe
        (shift_EPR_above amount cutoff a)
        (shift_EPR_above amount cutoff b)
  | EPR.EPRNot a => EPR.EPRNot (shift_EPR_above amount cutoff a)
  | EPR.EPRAnd a b =>
      EPR.EPRAnd
        (shift_EPR_above amount cutoff a)
        (shift_EPR_above amount cutoff b)
  | EPR.EPROr a b =>
      EPR.EPROr
        (shift_EPR_above amount cutoff a)
        (shift_EPR_above amount cutoff b)
  | EPR.EPRIf guard then_code else_code =>
      EPR.EPRIf
        (shift_EPR_above amount cutoff guard)
        (shift_EPR_above amount cutoff then_code)
        (shift_EPR_above amount cutoff else_code)
  | EPR.EPRRec bound base step =>
      EPR.EPRRec
        (shift_EPR_above amount cutoff bound)
        (shift_EPR_above amount cutoff base)
        (shift_EPR_above amount (S (S cutoff)) step)
  end.

Theorem eval_shift_EPR_above :
  forall code amount cutoff prefix env,
    length prefix = amount ->
    cutoff <= length env ->
    EPR.eval_EPR
      (shift_EPR_above amount cutoff code)
      (insert_at cutoff prefix env) =
    EPR.eval_EPR code env.
Proof.
  induction code; intros amount cutoff prefix env Hlen Hcut; simpl.
  - reflexivity.
  - destruct (Nat.ltb_spec n cutoff).
    + apply nth_default_insert_left; assumption.
    + subst amount.
      apply nth_default_insert_right; lia.
  - rewrite IHcode by assumption.
    reflexivity.
  - rewrite IHcode by assumption.
    reflexivity.
  - rewrite IHcode1 by assumption.
    rewrite IHcode2 by assumption.
    reflexivity.
  - rewrite IHcode1 by assumption.
    rewrite IHcode2 by assumption.
    reflexivity.
  - rewrite IHcode1 by assumption.
    rewrite IHcode2 by assumption.
    reflexivity.
  - rewrite IHcode1 by assumption.
    rewrite IHcode2 by assumption.
    reflexivity.
  - rewrite IHcode by assumption.
    reflexivity.
  - rewrite IHcode1 by assumption.
    rewrite IHcode2 by assumption.
    reflexivity.
  - rewrite IHcode1 by assumption.
    rewrite IHcode2 by assumption.
    reflexivity.
  - rewrite IHcode1 by assumption.
    destruct (K.nat_to_bool (EPR.eval_EPR code1 env)).
    + rewrite IHcode2 by assumption.
      reflexivity.
    + rewrite IHcode3 by assumption.
      reflexivity.
  - rewrite IHcode1 by assumption.
    rewrite IHcode2 by assumption.
    set (fuel := EPR.eval_EPR code1 env).
    clearbody fuel.
    set (base_value := EPR.eval_EPR code2 env).
    clearbody base_value.
    revert base_value.
    induction fuel as [|fuel IHfuel]; intro acc.
    + reflexivity.
    + simpl.
      change (acc :: fuel :: insert_at cutoff prefix env)
        with (insert_at (S (S cutoff)) prefix (acc :: fuel :: env)).
      rewrite IHcode3 by (try exact Hlen; simpl; lia).
      apply IHfuel.
Qed.

Definition shift_EPR (amount : nat) (code : EPR.EPRCode) : EPR.EPRCode :=
  shift_EPR_above amount 0 code.

Lemma eval_shift_EPR_prefix :
  forall code prefix env,
    EPR.eval_EPR (shift_EPR (length prefix) code) (prefix ++ env) =
    EPR.eval_EPR code env.
Proof.
  intros code prefix env.
  unfold shift_EPR.
  change (prefix ++ env) with (insert_at 0 prefix env).
  apply eval_shift_EPR_above.
  - reflexivity.
  - lia.
Qed.

Definition lift_subst_under_rec
           (subst : list EPR.EPRCode) : list EPR.EPRCode :=
  [EPR.EPRArg 0; EPR.EPRArg 1] ++ map (shift_EPR 2) subst.

Lemma eval_EPR_codes_map_shift2 :
  forall subst acc counter env,
    SUB.eval_EPR_codes (map (shift_EPR 2) subst)
      (acc :: counter :: env) =
    SUB.eval_EPR_codes subst env.
Proof.
  induction subst as [|code rest IH]; intros acc counter env.
  - reflexivity.
  - simpl.
    change (acc :: counter :: env) with ([acc; counter] ++ env).
    replace (EPR.eval_EPR (shift_EPR 2 code) ([acc; counter] ++ env))
      with (EPR.eval_EPR code env).
    change ([acc; counter] ++ env) with (acc :: counter :: env).
    rewrite IH.
    reflexivity.
    symmetry.
    change 2 with (length [acc; counter]).
    apply eval_shift_EPR_prefix.
Qed.

Lemma lift_subst_under_rec_agrees :
  forall subst,
    SUB.EPRStepSubstitutionAgrees subst (lift_subst_under_rec subst).
Proof.
  intros subst acc counter env.
  unfold lift_subst_under_rec.
  simpl.
  rewrite eval_EPR_codes_map_shift2.
  reflexivity.
Qed.

Definition substitute_rec_certificate
           (bound base step : EPR.EPRCode)
           (subst : list EPR.EPRCode)
           (bound_cert : SUB.EPRSubstitutionCertificate bound subst)
           (base_cert : SUB.EPRSubstitutionCertificate base subst)
           (step_cert :
              SUB.EPRSubstitutionCertificate
                step (lift_subst_under_rec subst))
  : SUB.EPRSubstitutionCertificate (EPR.EPRRec bound base step) subst.
Proof.
  refine
    {|
      SUB.substituted_epr_code :=
        EPR.EPRRec
          (SUB.substituted_epr_code bound subst bound_cert)
          (SUB.substituted_epr_code base subst base_cert)
          (SUB.substituted_epr_code
             step (lift_subst_under_rec subst) step_cert);
      SUB.substituted_epr_code_correct := _
    |}.
  intro env.
  simpl.
  rewrite (SUB.substituted_epr_code_correct bound subst bound_cert env).
  rewrite (SUB.substituted_epr_code_correct base subst base_cert env).
  set (fuel := EPR.eval_EPR bound (SUB.eval_EPR_codes subst env)).
  clearbody fuel.
  set (base_value := EPR.eval_EPR base (SUB.eval_EPR_codes subst env)).
  clearbody base_value.
  revert base_value.
  induction fuel as [|fuel IH]; intro acc.
  - reflexivity.
  - simpl.
    rewrite
      (SUB.substituted_epr_code_correct
         step (lift_subst_under_rec subst) step_cert
         (acc :: fuel :: env)).
    rewrite lift_subst_under_rec_agrees.
    apply IH.
Defined.

End FormalSystemFactoryEPRRecSubstitution.
