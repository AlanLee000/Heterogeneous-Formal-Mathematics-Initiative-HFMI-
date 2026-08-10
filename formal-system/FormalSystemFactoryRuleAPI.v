From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.

Require Import FormalSystemFactoryKernel.
Require Import FormalSystemFactoryStage2.
Require Import FormalSystemFactoryBindingAPI.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.
Module S2 := FormalSystemFactoryStage2.FormalSystemFactoryStage2.
Module B := FormalSystemFactoryBindingAPI.FormalSystemFactoryBindingAPI.

Module FormalSystemFactoryRuleAPI.

Definition term : Type := B.term.
Definition context : Type := list term.

Definition term_eq_dec : forall a b : term, {a = b} + {a <> b}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition term_eqb (a b : term) : bool :=
  if term_eq_dec a b then true else false.

Lemma term_eqb_eq :
  forall a b, term_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold term_eqb.
  destruct (term_eq_dec a b) as [H | H]; split; congruence.
Qed.

Lemma term_eqb_refl :
  forall a, term_eqb a a = true.
Proof.
  intros a; apply term_eqb_eq; reflexivity.
Qed.

Definition context_eq_dec : forall a b : context, {a = b} + {a <> b} :=
  list_eq_dec term_eq_dec.

Inductive judgment : Type :=
| JFormula : term -> judgment
| JSequent : context -> term -> judgment.

Definition judgment_eq_dec :
  forall a b : judgment, {a = b} + {a <> b}.
Proof.
  intros a b.
  destruct a as [ta | ca ta]; destruct b as [tb | cb tb].
  - destruct (term_eq_dec ta tb) as [H | H].
    + subst; left; reflexivity.
    + right; intro Heq; inversion Heq; contradiction.
  - right; discriminate.
  - right; discriminate.
  - destruct (context_eq_dec ca cb) as [Hc | Hc].
    + destruct (term_eq_dec ta tb) as [Ht | Ht].
      * subst; left; reflexivity.
      * right; intro Heq; inversion Heq; contradiction.
    + right; intro Heq; inversion Heq; contradiction.
Defined.

Definition judgment_eqb (a b : judgment) : bool :=
  if judgment_eq_dec a b then true else false.

Lemma judgment_eqb_eq :
  forall a b, judgment_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold judgment_eqb.
  destruct (judgment_eq_dec a b) as [H | H]; split; congruence.
Qed.

Lemma judgment_eqb_refl :
  forall a, judgment_eqb a a = true.
Proof.
  intros a; apply judgment_eqb_eq; reflexivity.
Qed.

Fixpoint in_judgmentb (j : judgment) (js : list judgment) : bool :=
  match js with
  | [] => false
  | k :: rest =>
      if judgment_eqb j k then true else in_judgmentb j rest
  end.

Lemma in_judgmentb_complete :
  forall j js,
    In j js ->
    in_judgmentb j js = true.
Proof.
  intros j js Hin.
  induction js as [|k rest IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hjk | Hrest].
    + subst k.
      rewrite judgment_eqb_refl.
      reflexivity.
    + destruct (judgment_eqb j k); auto.
Qed.

Record RuleSchema : Type := {
  rule_name : nat;
  rule_parameters : list term;
  rule_premises : list judgment;
  rule_conclusion : judgment;
  rule_side_condition_code : K.PRCode;
  rule_side_condition_env : list nat
}.

Definition rule_side_condition (r : RuleSchema) : bool :=
  K.eval_PR_bool (rule_side_condition_code r) (rule_side_condition_env r).

Record TheorySpec : Type := {
  theory_axioms : list judgment;
  theory_rules : list RuleSchema;
  theory_contradiction : judgment
}.

Inductive proof_object : Type :=
| PAxiom : judgment -> proof_object
| PRule : nat -> list proof_object -> proof_object.

Fixpoint check_proof (spec : TheorySpec) (p : proof_object)
         (goal : judgment) {struct p} : bool :=
  match p with
  | PAxiom j =>
      andb (judgment_eqb j goal)
           (in_judgmentb j (theory_axioms spec))
  | PRule rule_index subproofs =>
      let fix check_premises (ps : list proof_object)
              (goals : list judgment) : bool :=
          match ps, goals with
          | [], [] => true
          | p' :: ps', g :: goals' =>
              andb (check_proof spec p' g)
                   (check_premises ps' goals')
          | _, _ => false
          end in
      match nth_error (theory_rules spec) rule_index with
      | None => false
      | Some r =>
          andb (rule_side_condition r)
               (andb (judgment_eqb (rule_conclusion r) goal)
                     (check_premises subproofs (rule_premises r)))
      end
  end.

Definition Prf (spec : TheorySpec) (p : proof_object)
           (goal : judgment) : Prop :=
  check_proof spec p goal = true.

Definition Derivable (spec : TheorySpec) (goal : judgment) : Prop :=
  exists p, Prf spec p goal.

Lemma axiom_checked :
  forall spec j,
    In j (theory_axioms spec) ->
    check_proof spec (PAxiom j) j = true.
Proof.
  intros spec j Hin.
  simpl.
  rewrite judgment_eqb_refl.
  simpl.
  apply in_judgmentb_complete.
  exact Hin.
Qed.

Record RuleAPI : Type := {
  api_judgment : Type;
  api_formula_judgment : term -> api_judgment;
  api_sequent_judgment : context -> term -> api_judgment;
  api_rule_schema : Type;
  api_theory_spec : Type;
  api_proof_object : Type;
  api_check_proof : api_theory_spec -> api_proof_object -> api_judgment -> bool;
  api_derivable : api_theory_spec -> api_judgment -> Prop
}.

Definition raw_rule_api : RuleAPI :=
  {|
    api_judgment := judgment;
    api_formula_judgment := JFormula;
    api_sequent_judgment := JSequent;
    api_rule_schema := RuleSchema;
    api_theory_spec := TheorySpec;
    api_proof_object := proof_object;
    api_check_proof := check_proof;
    api_derivable := Derivable
  |}.

Definition pr_true : K.PRCode := K.PRConst 1.
Definition pr_false : K.PRCode := K.PRConst 0.

Definition example_formula : term := B.mk_const 10.
Definition example_judgment : judgment := JFormula example_formula.

Definition example_axiom_theory : TheorySpec :=
  {|
    theory_axioms := [example_judgment];
    theory_rules := [];
    theory_contradiction := JFormula (B.mk_const 0)
  |}.

Lemma example_axiom_checked :
  check_proof example_axiom_theory
              (PAxiom example_judgment)
              example_judgment = true.
Proof.
  apply axiom_checked.
  simpl; left; reflexivity.
Qed.

Definition example_rule : RuleSchema :=
  {|
    rule_name := 0;
    rule_parameters := [example_formula];
    rule_premises := [example_judgment];
    rule_conclusion := JSequent [example_formula] example_formula;
    rule_side_condition_code := pr_true;
    rule_side_condition_env := []
  |}.

Definition example_rule_theory : TheorySpec :=
  {|
    theory_axioms := [example_judgment];
    theory_rules := [example_rule];
    theory_contradiction := JFormula (B.mk_const 0)
  |}.

Definition example_rule_proof : proof_object :=
  PRule 0 [PAxiom example_judgment].

Lemma example_rule_checked :
  check_proof example_rule_theory
              example_rule_proof
              (rule_conclusion example_rule) = true.
Proof.
  reflexivity.
Qed.

Definition example_blocked_rule : RuleSchema :=
  {|
    rule_name := 1;
    rule_parameters := [];
    rule_premises := [];
    rule_conclusion := example_judgment;
    rule_side_condition_code := pr_false;
    rule_side_condition_env := []
  |}.

Definition example_blocked_theory : TheorySpec :=
  {|
    theory_axioms := [];
    theory_rules := [example_blocked_rule];
    theory_contradiction := JFormula (B.mk_const 0)
  |}.

Lemma example_blocked_rule_rejected :
  check_proof example_blocked_theory
              (PRule 0 [])
              example_judgment = false.
Proof.
  reflexivity.
Qed.

End FormalSystemFactoryRuleAPI.
