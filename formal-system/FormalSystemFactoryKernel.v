From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Module FormalSystemFactoryKernel.

Record Codec (A : Type) := {
  encode : A -> nat;
  decode : nat -> option A;
  decode_encode : forall a, decode (encode a) = Some a
}.

Definition nat_codec : Codec nat.
Proof.
  refine {| encode := fun n => n; decode := fun n => Some n |}.
  intros n; reflexivity.
Defined.

Definition bool_encode (b : bool) : nat :=
  if b then 1 else 0.

Definition bool_decode (n : nat) : option bool :=
  match n with
  | 0 => Some false
  | 1 => Some true
  | _ => None
  end.

Lemma bool_decode_encode :
  forall b, bool_decode (bool_encode b) = Some b.
Proof.
  destruct b; reflexivity.
Qed.

Definition bool_codec : Codec bool.
Proof.
  refine {| encode := bool_encode; decode := bool_decode |}.
  exact bool_decode_encode.
Defined.

Inductive PRCode : Type :=
| PRConst : nat -> PRCode
| PRArg : nat -> PRCode
| PRSucc : PRCode -> PRCode
| PRPred : PRCode -> PRCode
| PRAdd : PRCode -> PRCode -> PRCode
| PRMul : PRCode -> PRCode -> PRCode
| PREq : PRCode -> PRCode -> PRCode
| PRLe : PRCode -> PRCode -> PRCode
| PRNot : PRCode -> PRCode
| PRAnd : PRCode -> PRCode -> PRCode
| PROr : PRCode -> PRCode -> PRCode
| PRIf : PRCode -> PRCode -> PRCode -> PRCode.

Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Definition nat_to_bool (n : nat) : bool :=
  negb (Nat.eqb n 0).

Fixpoint nth_default (xs : list nat) (i : nat) : nat :=
  match xs, i with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: rest, S j => nth_default rest j
  end.

Fixpoint eval_PR (c : PRCode) (env : list nat) : nat :=
  match c with
  | PRConst n => n
  | PRArg i => nth_default env i
  | PRSucc a => S (eval_PR a env)
  | PRPred a => Nat.pred (eval_PR a env)
  | PRAdd a b => eval_PR a env + eval_PR b env
  | PRMul a b => eval_PR a env * eval_PR b env
  | PREq a b => bool_to_nat (Nat.eqb (eval_PR a env) (eval_PR b env))
  | PRLe a b => bool_to_nat (Nat.leb (eval_PR a env) (eval_PR b env))
  | PRNot a => bool_to_nat (negb (nat_to_bool (eval_PR a env)))
  | PRAnd a b => bool_to_nat (andb (nat_to_bool (eval_PR a env))
                                    (nat_to_bool (eval_PR b env)))
  | PROr a b => bool_to_nat (orb (nat_to_bool (eval_PR a env))
                                  (nat_to_bool (eval_PR b env)))
  | PRIf guard then_code else_code =>
      if nat_to_bool (eval_PR guard env)
      then eval_PR then_code env
      else eval_PR else_code env
  end.

Definition eval_PR_bool (c : PRCode) (env : list nat) : bool :=
  nat_to_bool (eval_PR c env).

Lemma eval_PR_total :
  forall c env, exists n, eval_PR c env = n.
Proof.
  intros c env; exists (eval_PR c env); reflexivity.
Qed.

Definition PR_relation_2 (R : nat -> nat -> bool) : Prop :=
  exists c : PRCode, forall x y, R x y = eval_PR_bool c [x; y].

Record Signature : Type := {
  sort_count : nat;
  constructor_count : nat;
  constructor_arity : nat -> nat;
  constructor_result : nat -> nat
}.

Definition constructor_valid (Sg : Signature) (c : nat) : Prop :=
  c < constructor_count Sg /\
  constructor_result Sg c < sort_count Sg.

Definition ValidSignature (Sg : Signature) : Prop :=
  sort_count Sg > 0 /\
  forall c, c < constructor_count Sg ->
    constructor_result Sg c < sort_count Sg.

Record RuleSchema : Type := {
  rule_name_code : nat;
  rule_checker_code : PRCode
}.

Record TheorySpec : Type := {
  spec_signature : Signature;
  spec_rules : list RuleSchema;
  spec_checker_code : PRCode;
  spec_contradiction_code : nat
}.

Definition ValidSpec (spec : TheorySpec) : Prop :=
  ValidSignature (spec_signature spec).

Record Theory : Type := {
  theory_signature : Signature;
  theory_rules : list RuleSchema;
  proof_check_code : PRCode;
  contradiction_code : nat
}.

Definition compile_theory (spec : TheorySpec) : Theory :=
  {|
    theory_signature := spec_signature spec;
    theory_rules := spec_rules spec;
    proof_check_code := spec_checker_code spec;
    contradiction_code := spec_contradiction_code spec
  |}.

Definition proof_check (T : Theory) (p j : nat) : bool :=
  eval_PR_bool (proof_check_code T) [p; j].

Definition Prf (T : Theory) (p j : nat) : Prop :=
  proof_check T p j = true.

Definition Acceptable (T : Theory) : Prop :=
  PR_relation_2 (proof_check T).

Theorem compile_preserves_acceptability :
  forall spec,
    ValidSpec spec ->
    Acceptable (compile_theory spec).
Proof.
  intros spec _.
  unfold Acceptable, PR_relation_2, proof_check, compile_theory.
  exists (spec_checker_code spec).
  intros p j; reflexivity.
Qed.

Definition Inconsistent (T : Theory) : Prop :=
  exists p, Prf T p (contradiction_code T).

Definition Nontrivial (T : Theory) : Prop :=
  ~ Inconsistent T.

Record Interpretation (T S : Theory) : Type := {
  translate_judgment : nat -> nat;
  translate_proof : nat -> nat;
  preserves_proof :
    forall p j,
      Prf T p j ->
      Prf S (translate_proof p) (translate_judgment j);
  preserves_contradiction :
    translate_judgment (contradiction_code T) = contradiction_code S
}.

Theorem interpretation_preserves_nontriviality :
  forall T S,
    Interpretation T S ->
    Nontrivial S ->
    Nontrivial T.
Proof.
  intros T S I HnonS [p Hp].
  apply HnonS.
  exists (translate_proof T S I p).
  pose proof (preserves_proof T S I p (contradiction_code T) Hp) as HS.
  rewrite (preserves_contradiction T S I) in HS.
  exact HS.
Qed.

Record ContradictionRefutationCertificate (T : Theory) : Type := {
  certificate_rejects_contradiction :
    forall p, proof_check T p (contradiction_code T) = false
}.

Theorem contradiction_refutation_nontrivial :
  forall T,
    ContradictionRefutationCertificate T ->
    Nontrivial T.
Proof.
  intros T C [p Hp].
  unfold Prf in Hp.
  rewrite (certificate_rejects_contradiction T C p) in Hp.
  discriminate Hp.
Qed.

Record JudgmentModel (T : Theory) : Type := {
  model_holds : nat -> Prop;
  model_truth_nonempty : exists j, model_holds j;
  model_proof_sound :
    forall p j, Prf T p j -> model_holds j;
  model_contradiction_false : ~ model_holds (contradiction_code T)
}.

Theorem judgment_model_nontrivial :
  forall T, JudgmentModel T -> Nontrivial T.
Proof.
  intros T M [p Hp].
  exact (model_contradiction_false T M
    (model_proof_sound T M p (contradiction_code T) Hp)).
Qed.

Inductive TrustBase : Type :=
| PRA_checked
| KP_checked
| ZFC_checked
| HoTT_checked
| Assumed.

Record CertifiedStatement : Type := {
  statement_code : nat;
  trust_base : TrustBase;
  certificate_code : nat
}.

Definition certified_by_PRA (c : CertifiedStatement) : Prop :=
  trust_base c = PRA_checked.

Definition checked_in_stronger_backend (c : CertifiedStatement) : Prop :=
  trust_base c = KP_checked \/
  trust_base c = ZFC_checked \/
  trust_base c = HoTT_checked.

Definition one_sort_signature : Signature :=
  {|
    sort_count := 1;
    constructor_count := 0;
    constructor_arity := fun _ => 0;
    constructor_result := fun _ => 0
  |}.

Lemma one_sort_signature_valid :
  ValidSignature one_sort_signature.
Proof.
  split.
  - simpl; lia.
  - intros c Hc; simpl in Hc; lia.
Qed.

Definition reject_all_checker : PRCode := PRConst 0.

Definition empty_spec : TheorySpec :=
  {|
    spec_signature := one_sort_signature;
    spec_rules := [];
    spec_checker_code := reject_all_checker;
    spec_contradiction_code := 0
  |}.

Definition empty_theory : Theory := compile_theory empty_spec.

Theorem empty_theory_acceptable :
  Acceptable empty_theory.
Proof.
  apply compile_preserves_acceptability.
  exact one_sort_signature_valid.
Qed.

Definition empty_theory_model : JudgmentModel empty_theory.
Proof.
  refine {|
    model_holds := fun j => j = 1
  |}.
  - exists 1. reflexivity.
  - intros p j Hp.
    unfold Prf, proof_check, empty_theory, compile_theory in Hp.
    simpl in Hp. discriminate Hp.
  - simpl. discriminate.
Defined.

Theorem empty_theory_nontrivial :
  Nontrivial empty_theory.
Proof.
  exact (judgment_model_nontrivial empty_theory empty_theory_model).
Qed.

Theorem empty_theory_semantic_separation :
  model_holds empty_theory empty_theory_model 1 /\
  ~ model_holds empty_theory empty_theory_model
      (contradiction_code empty_theory).
Proof.
  split; simpl; [reflexivity | discriminate].
Qed.

Definition identity_interpretation (T : Theory) : Interpretation T T.
Proof.
  refine
    {|
      translate_judgment := fun j => j;
      translate_proof := fun p => p
    |}.
  - intros p j Hp; exact Hp.
  - reflexivity.
Defined.

Theorem identity_interpretation_keeps_nontriviality :
  forall T,
    Nontrivial T ->
    Nontrivial T.
Proof.
  intros T H.
  exact (interpretation_preserves_nontriviality
           T T (identity_interpretation T) H).
Qed.

End FormalSystemFactoryKernel.
