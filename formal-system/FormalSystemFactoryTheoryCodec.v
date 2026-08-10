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

Module FormalSystemFactoryTheoryCodec.

Definition encode_judgment_list (js : list R.judgment) : SC.code :=
  SC.encode_code_list SC.encode_judgment js.

Definition decode_judgment_list (c : SC.code) : option (list R.judgment) :=
  SC.decode_code_list_node SC.decode_judgment c.

Lemma decode_encode_judgment_list :
  forall js,
    decode_judgment_list (encode_judgment_list js) = Some js.
Proof.
  intros js.
  apply SC.decode_code_list_node_encode.
  exact SC.decode_encode_judgment.
Qed.

Definition encode_rule_schema (r : R.RuleSchema) : SC.code :=
  SC.CNode 60
    [ SC.CAtom (R.rule_name r);
      SC.encode_context (R.rule_parameters r);
      encode_judgment_list (R.rule_premises r);
      SC.encode_judgment (R.rule_conclusion r);
      SC.encode_prcode (R.rule_side_condition_code r);
      SC.encode_nat_list (R.rule_side_condition_env r)
    ].

Definition decode_rule_schema (c : SC.code) : option R.RuleSchema :=
  match c with
  | SC.CNode 60
      [ SC.CAtom name;
        parameters_code;
        premises_code;
        conclusion_code;
        side_condition_code;
        side_condition_env_code
      ] =>
      match SC.decode_context parameters_code,
            decode_judgment_list premises_code,
            SC.decode_judgment conclusion_code,
            SC.decode_prcode side_condition_code,
            SC.decode_nat_list side_condition_env_code with
      | Some parameters,
        Some premises,
        Some conclusion,
        Some side_code,
        Some side_env =>
          Some
            {|
              R.rule_name := name;
              R.rule_parameters := parameters;
              R.rule_premises := premises;
              R.rule_conclusion := conclusion;
              R.rule_side_condition_code := side_code;
              R.rule_side_condition_env := side_env
            |}
      | _, _, _, _, _ => None
      end
  | _ => None
  end.

Lemma decode_encode_rule_schema :
  forall r,
    decode_rule_schema (encode_rule_schema r) = Some r.
Proof.
  intros
    [name parameters premises conclusion side_code side_env].
  unfold encode_rule_schema, decode_rule_schema.
  rewrite SC.decode_encode_context.
  rewrite decode_encode_judgment_list.
  rewrite SC.decode_encode_judgment.
  rewrite SC.decode_encode_prcode.
  rewrite SC.decode_nat_list_encode.
  reflexivity.
Qed.

Definition rule_schema_structural_codec : SC.StructuralCodec R.RuleSchema.
Proof.
  refine
    {|
      SC.encode_code := encode_rule_schema;
      SC.decode_code := decode_rule_schema
    |}.
  exact decode_encode_rule_schema.
Defined.

Definition encode_rule_schema_list
           (rules : list R.RuleSchema) : SC.code :=
  SC.encode_code_list encode_rule_schema rules.

Definition decode_rule_schema_list
           (c : SC.code) : option (list R.RuleSchema) :=
  SC.decode_code_list_node decode_rule_schema c.

Lemma decode_encode_rule_schema_list :
  forall rules,
    decode_rule_schema_list (encode_rule_schema_list rules) =
    Some rules.
Proof.
  intros rules.
  apply SC.decode_code_list_node_encode.
  exact decode_encode_rule_schema.
Qed.

Definition encode_theory_spec (spec : R.TheorySpec) : SC.code :=
  SC.CNode 61
    [ encode_judgment_list (R.theory_axioms spec);
      encode_rule_schema_list (R.theory_rules spec);
      SC.encode_judgment (R.theory_contradiction spec)
    ].

Definition decode_theory_spec (c : SC.code) : option R.TheorySpec :=
  match c with
  | SC.CNode 61 [axioms_code; rules_code; contradiction_code] =>
      match decode_judgment_list axioms_code,
            decode_rule_schema_list rules_code,
            SC.decode_judgment contradiction_code with
      | Some axioms, Some rules, Some contradiction =>
          Some
            {|
              R.theory_axioms := axioms;
              R.theory_rules := rules;
              R.theory_contradiction := contradiction
            |}
      | _, _, _ => None
      end
  | _ => None
  end.

Lemma decode_encode_theory_spec :
  forall spec,
    decode_theory_spec (encode_theory_spec spec) = Some spec.
Proof.
  intros [axioms rules contradiction].
  unfold encode_theory_spec, decode_theory_spec.
  rewrite decode_encode_judgment_list.
  rewrite decode_encode_rule_schema_list.
  rewrite SC.decode_encode_judgment.
  reflexivity.
Qed.

Definition theory_spec_structural_codec : SC.StructuralCodec R.TheorySpec.
Proof.
  refine
    {|
      SC.encode_code := encode_theory_spec;
      SC.decode_code := decode_theory_spec
    |}.
  exact decode_encode_theory_spec.
Defined.

Definition encode_rule_schema_nat (r : R.RuleSchema) : nat :=
  NC.encode_code_nat (encode_rule_schema r).

Definition encode_theory_spec_nat (spec : R.TheorySpec) : nat :=
  NC.encode_code_nat (encode_theory_spec spec).

Definition decode_rule_schema_nat
           (fuel n : nat) : option R.RuleSchema :=
  match NC.decode_code_nat_fuel fuel n with
  | Some c => decode_rule_schema c
  | None => None
  end.

Definition decode_theory_spec_nat
           (fuel n : nat) : option R.TheorySpec :=
  match NC.decode_code_nat_fuel fuel n with
  | Some c => decode_theory_spec c
  | None => None
  end.

Lemma decode_encode_rule_schema_nat :
  forall r,
    decode_rule_schema_nat
      (S (NC.code_depth (encode_rule_schema r)))
      (encode_rule_schema_nat r) = Some r.
Proof.
  intro r.
  unfold decode_rule_schema_nat, encode_rule_schema_nat.
  rewrite NC.decode_encode_code_nat_fuel.
  apply decode_encode_rule_schema.
Qed.

Lemma decode_encode_theory_spec_nat :
  forall spec,
    decode_theory_spec_nat
      (S (NC.code_depth (encode_theory_spec spec)))
      (encode_theory_spec_nat spec) = Some spec.
Proof.
  intro spec.
  unfold decode_theory_spec_nat, encode_theory_spec_nat.
  rewrite NC.decode_encode_code_nat_fuel.
  apply decode_encode_theory_spec.
Qed.

Definition backend_decode_rule_schema_nat
           (backend : MRB.MRDecoderBackend)
           (fuel n : nat) : option R.RuleSchema :=
  match MSD.backend_decode_code_nat_fuel backend fuel n with
  | Some c => decode_rule_schema c
  | None => None
  end.

Definition backend_decode_theory_spec_nat
           (backend : MRB.MRDecoderBackend)
           (fuel n : nat) : option R.TheorySpec :=
  match MSD.backend_decode_code_nat_fuel backend fuel n with
  | Some c => decode_theory_spec c
  | None => None
  end.

Theorem backend_decode_rule_schema_nat_correct :
  forall backend fuel n,
    backend_decode_rule_schema_nat backend fuel n =
    decode_rule_schema_nat fuel n.
Proof.
  intros backend fuel n.
  unfold backend_decode_rule_schema_nat, decode_rule_schema_nat.
  rewrite MSD.backend_decode_code_nat_fuel_correct.
  reflexivity.
Qed.

Theorem backend_decode_theory_spec_nat_correct :
  forall backend fuel n,
    backend_decode_theory_spec_nat backend fuel n =
    decode_theory_spec_nat fuel n.
Proof.
  intros backend fuel n.
  unfold backend_decode_theory_spec_nat, decode_theory_spec_nat.
  rewrite MSD.backend_decode_code_nat_fuel_correct.
  reflexivity.
Qed.

Theorem backend_decode_encode_rule_schema_nat :
  forall backend r,
    backend_decode_rule_schema_nat
      backend
      (S (NC.code_depth (encode_rule_schema r)))
      (encode_rule_schema_nat r) = Some r.
Proof.
  intros backend r.
  rewrite backend_decode_rule_schema_nat_correct.
  apply decode_encode_rule_schema_nat.
Qed.

Theorem backend_decode_encode_theory_spec_nat :
  forall backend spec,
    backend_decode_theory_spec_nat
      backend
      (S (NC.code_depth (encode_theory_spec spec)))
      (encode_theory_spec_nat spec) = Some spec.
Proof.
  intros backend spec.
  rewrite backend_decode_theory_spec_nat_correct.
  apply decode_encode_theory_spec_nat.
Qed.

Definition backend_decoded_all_nat_check_proof_with_fuel
           (backend : MRB.MRDecoderBackend)
           (theory_fuel proof_fuel goal_fuel
                        theory_nat proof_nat goal_nat : nat) : bool :=
  match backend_decode_theory_spec_nat backend theory_fuel theory_nat,
        MSD.backend_decode_proof_object_nat backend proof_fuel proof_nat,
        MSD.backend_decode_judgment_nat backend goal_fuel goal_nat with
  | Some spec, Some p, Some goal => R.check_proof spec p goal
  | _, _, _ => false
  end.

Theorem backend_decoded_all_nat_check_proof_agrees :
  forall backend spec p goal,
    backend_decoded_all_nat_check_proof_with_fuel
      backend
      (S (NC.code_depth (encode_theory_spec spec)))
      (S (NC.code_depth (SC.encode_proof_object p)))
      (S (NC.code_depth (SC.encode_judgment goal)))
      (encode_theory_spec_nat spec)
      (NC.encode_proof_object_nat p)
      (NC.encode_judgment_nat goal) =
    R.check_proof spec p goal.
Proof.
  intros backend spec p goal.
  unfold backend_decoded_all_nat_check_proof_with_fuel.
  rewrite backend_decode_encode_theory_spec_nat.
  rewrite MSD.backend_decode_encode_proof_object_nat.
  rewrite MSD.backend_decode_encode_judgment_nat.
  reflexivity.
Qed.

Theorem default_backend_all_nat_example_rule_checked :
  backend_decoded_all_nat_check_proof_with_fuel
    MRB.default_mr_decoder_backend
    (S (NC.code_depth (encode_theory_spec R.example_rule_theory)))
    (S (NC.code_depth (SC.encode_proof_object R.example_rule_proof)))
    (S (NC.code_depth (SC.encode_judgment (R.rule_conclusion R.example_rule))))
    (encode_theory_spec_nat R.example_rule_theory)
    (NC.encode_proof_object_nat R.example_rule_proof)
    (NC.encode_judgment_nat (R.rule_conclusion R.example_rule)) = true.
Proof.
  rewrite backend_decoded_all_nat_check_proof_agrees.
  exact R.example_rule_checked.
Qed.

End FormalSystemFactoryTheoryCodec.
