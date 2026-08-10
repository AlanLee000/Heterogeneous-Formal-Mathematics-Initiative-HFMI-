From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.

Import ListNotations.

Module BoundedStringFixedPoint.

Definition Str : Type := list bool.

Definition size : Str -> nat := @length bool.

Definition epsilon : Str := [].
Definition bit_zero : Str := [false].
Definition bit_one : Str := [true].

Definition concat (x y : Str) : Str := x ++ y.

Definition num (m : nat) : Str := repeat true m ++ [false].

Definition pair_code (x y : Str) : Str :=
  repeat true (size x) ++ [false] ++ x ++ y.

Fixpoint seq_code (xs : list Str) : Str :=
  match xs with
  | [] => epsilon
  | x :: rest => pair_code x (seq_code rest)
  end.

Definition tag_eval : Str := num 0.
Definition tag_thm : Str := num 1.
Definition tag_syn : Str := num 2.
Definition tag_term : Str := num 3.
Definition tag_form : Str := num 4.
Definition tag_assign : Str := num 5.
Definition tag_val : Str := num 6.
Definition tag_proof : Str := num 7.
Definition tag_claim : Str := num 8.
Definition tag_rule : Str := num 9.
Definition tag_zero : Str := num 10.
Definition tag_one : Str := num 11.

Section Core.

Definition bool_num (b : bool) : nat := if b then 1 else 0.

Definition EvalCl (b : bool) (n : nat) (phi alpha : Str) : Str :=
  seq_code [tag_eval; num (bool_num b); num n; phi; alpha].

Definition ThmCl (n : nat) (phi : Str) : Str :=
  seq_code [tag_thm; num n; phi].

Definition SynCl (n j : nat) (x : Str) : Str :=
  seq_code [tag_syn; num n; num j; x].

Definition TermCl (n : nat) (t : Str) : Str :=
  seq_code [tag_term; num n; t].

Definition FormCl (n : nat) (phi : Str) : Str :=
  seq_code [tag_form; num n; phi].

Definition AssignCl (n : nat) (phi alpha : Str) : Str :=
  seq_code [tag_assign; num n; phi; alpha].

Definition ValCl (n : nat) (t alpha y : Str) : Str :=
  seq_code [tag_val; num n; t; alpha; y].

Record bound_class : Type := {
  bound_fun : nat -> Type;
  bound_apply : forall k, bound_fun k -> list nat -> nat;
  bound_zero : bound_fun 0;
  bound_one : bound_fun 0;
  bound_proj : forall k, nat -> bound_fun k;
  bound_add : bound_fun 2;
  bound_mul : bound_fun 2;
  bound_comp :
    forall k l, bound_fun l -> list (bound_fun k) -> bound_fun k
}.

Inductive delta0_atom : Type :=
| AtomEq
| AtomLtLen
| AtomBitZero
| AtomBitOne
| AtomConcat
| AtomPair.

Inductive delta0_formula : Type :=
| DAtom : delta0_atom -> list Str -> delta0_formula
| DNeg : delta0_formula -> delta0_formula
| DAnd : delta0_formula -> delta0_formula -> delta0_formula
| DOr : delta0_formula -> delta0_formula -> delta0_formula
| DExistsBounded : nat -> delta0_formula -> delta0_formula
| DForallBounded : nat -> delta0_formula -> delta0_formula.

Inductive positive_formula : Type :=
| PDeltaAtom : delta0_atom -> list Str -> positive_formula
| PNegDeltaAtom : delta0_atom -> list Str -> positive_formula
| PRelVar : nat -> list Str -> positive_formula
| PAnd : positive_formula -> positive_formula -> positive_formula
| POr : positive_formula -> positive_formula -> positive_formula
| PExistsBounded : nat -> positive_formula -> positive_formula
| PForallBounded : nat -> positive_formula -> positive_formula.

Record candidate : Type := {
  cand_term : nat -> Str -> Prop;
  cand_form : nat -> Str -> Prop;
  cand_assign : nat -> Str -> Str -> Prop;
  cand_val : nat -> Str -> Str -> Str -> Prop;
  cand_claim : nat -> Str -> Prop;
  cand_proof : nat -> Str -> Str -> Prop;
  cand_prv : nat -> Str -> Prop;
  cand_eval0 : nat -> Str -> Str -> Prop;
  cand_eval1 : nat -> Str -> Str -> Prop
}.

Record le_candidate (X Y : candidate) : Prop := {
  le_term : forall n t, cand_term X n t -> cand_term Y n t;
  le_form : forall n phi, cand_form X n phi -> cand_form Y n phi;
  le_assign :
    forall n phi alpha,
      cand_assign X n phi alpha -> cand_assign Y n phi alpha;
  le_val :
    forall n t alpha y,
      cand_val X n t alpha y -> cand_val Y n t alpha y;
  le_claim : forall n c, cand_claim X n c -> cand_claim Y n c;
  le_proof :
    forall n p c, cand_proof X n p c -> cand_proof Y n p c;
  le_prv : forall n c, cand_prv X n c -> cand_prv Y n c;
  le_eval0 :
    forall n phi alpha,
      cand_eval0 X n phi alpha -> cand_eval0 Y n phi alpha;
  le_eval1 :
    forall n phi alpha,
      cand_eval1 X n phi alpha -> cand_eval1 Y n phi alpha
}.

Lemma le_candidate_refl : forall X, le_candidate X X.
Proof. intros X; constructor; auto. Qed.

Lemma le_candidate_trans :
  forall X Y Z,
    le_candidate X Y -> le_candidate Y Z -> le_candidate X Z.
Proof.
  intros X Y Z HXY HYZ.
  constructor; eauto using le_term, le_form, le_assign, le_val,
    le_claim, le_proof, le_prv, le_eval0, le_eval1.
Qed.

Record hierarchy_spec : Type := {
  spec_bound : nat -> nat -> nat;
  theta_term : candidate -> nat -> Str -> Prop;
  theta_form : candidate -> nat -> Str -> Prop;
  theta_assign : candidate -> nat -> Str -> Str -> Prop;
  theta_val : candidate -> nat -> Str -> Str -> Str -> Prop;
  theta_claim : candidate -> nat -> Str -> Prop;
  theta_proof : candidate -> nat -> Str -> Str -> Prop;
  theta_term_mono :
    forall X Y, le_candidate X Y ->
      forall n t, theta_term X n t -> theta_term Y n t;
  theta_form_mono :
    forall X Y, le_candidate X Y ->
      forall n phi, theta_form X n phi -> theta_form Y n phi;
  theta_assign_mono :
    forall X Y, le_candidate X Y ->
      forall n phi alpha,
        theta_assign X n phi alpha -> theta_assign Y n phi alpha;
  theta_val_mono :
    forall X Y, le_candidate X Y ->
      forall n t alpha y, theta_val X n t alpha y -> theta_val Y n t alpha y;
  theta_claim_mono :
    forall X Y, le_candidate X Y ->
      forall n c, theta_claim X n c -> theta_claim Y n c;
  theta_proof_mono :
    forall X Y, le_candidate X Y ->
      forall n p c, theta_proof X n p c -> theta_proof Y n p c;
  fragment_G : nat -> Str -> Prop;
  embed_I : nat -> Str -> Str -> Prop;
  embed_I_functional :
    forall n t u v, embed_I n t u -> embed_I n t v -> u = v;
  embed_I_total :
    forall n t, exists u, embed_I n t u;
  syn_frag : nat -> nat -> Str -> Prop;
  assign_term : nat -> Str -> Str -> Prop
}.

Definition Phi (S : hierarchy_spec) (X : candidate) : candidate := {|
  cand_term := theta_term S X;
  cand_form := theta_form S X;
  cand_assign := theta_assign S X;
  cand_val := theta_val S X;
  cand_claim := theta_claim S X;
  cand_proof := theta_proof S X;
  cand_prv :=
    fun n c =>
      exists p, size p <= spec_bound S n (size c) /\ theta_proof S X n p c;
  cand_eval0 :=
    fun n phi alpha => cand_prv X (Datatypes.S n) (EvalCl false n phi alpha);
  cand_eval1 :=
    fun n phi alpha => cand_prv X (Datatypes.S n) (EvalCl true n phi alpha)
|}.

Definition prefixed (S : hierarchy_spec) (X : candidate) : Prop :=
  le_candidate (Phi S X) X.

Lemma Phi_monotone :
  forall S X Y, le_candidate X Y -> le_candidate (Phi S X) (Phi S Y).
Proof.
  intros S X Y HXY.
  constructor; simpl.
  - apply theta_term_mono; exact HXY.
  - apply theta_form_mono; exact HXY.
  - apply theta_assign_mono; exact HXY.
  - apply theta_val_mono; exact HXY.
  - apply theta_claim_mono; exact HXY.
  - apply theta_proof_mono; exact HXY.
  - intros n c [p [Hb Hp]].
    exists p; split; [exact Hb|].
    eapply theta_proof_mono; eauto.
  - intros n phi alpha H.
    eapply le_prv; eauto.
  - intros n phi alpha H.
    eapply le_prv; eauto.
Qed.

Definition Hstar (S : hierarchy_spec) : candidate := {|
  cand_term := fun n t => forall X, prefixed S X -> cand_term X n t;
  cand_form := fun n phi => forall X, prefixed S X -> cand_form X n phi;
  cand_assign :=
    fun n phi alpha => forall X, prefixed S X -> cand_assign X n phi alpha;
  cand_val :=
    fun n t alpha y => forall X, prefixed S X -> cand_val X n t alpha y;
  cand_claim := fun n c => forall X, prefixed S X -> cand_claim X n c;
  cand_proof := fun n p c => forall X, prefixed S X -> cand_proof X n p c;
  cand_prv := fun n c => forall X, prefixed S X -> cand_prv X n c;
  cand_eval0 :=
    fun n phi alpha => forall X, prefixed S X -> cand_eval0 X n phi alpha;
  cand_eval1 :=
    fun n phi alpha => forall X, prefixed S X -> cand_eval1 X n phi alpha
|}.

Lemma Hstar_least :
  forall S X, prefixed S X -> le_candidate (Hstar S) X.
Proof.
  intros S X HX.
  constructor; simpl; intros; eauto.
Qed.

Lemma Hstar_prefixed :
  forall S, prefixed S (Hstar S).
Proof.
  intros S.
  constructor; simpl.
  - intros n t H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_term _ _ HX).
    apply (le_term _ _ HM); exact H.
  - intros n phi H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_form _ _ HX).
    apply (le_form _ _ HM); exact H.
  - intros n phi alpha H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_assign _ _ HX).
    apply (le_assign _ _ HM); exact H.
  - intros n t alpha y H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_val _ _ HX).
    apply (le_val _ _ HM); exact H.
  - intros n c H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_claim _ _ HX).
    apply (le_claim _ _ HM); exact H.
  - intros n p c H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_proof _ _ HX).
    apply (le_proof _ _ HM); exact H.
  - intros n c H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_prv _ _ HX).
    apply (le_prv _ _ HM); exact H.
  - intros n phi alpha H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_eval0 _ _ HX).
    apply (le_eval0 _ _ HM); exact H.
  - intros n phi alpha H X HX.
    pose proof (Phi_monotone S (Hstar S) X (Hstar_least S X HX)) as HM.
    apply (le_eval1 _ _ HX).
    apply (le_eval1 _ _ HM); exact H.
Qed.

Lemma Phi_Hstar_prefixed :
  forall S, prefixed S (Phi S (Hstar S)).
Proof.
  intros S.
  unfold prefixed.
  apply Phi_monotone.
  apply Hstar_prefixed.
Qed.

Theorem Hstar_fixed :
  forall S,
    le_candidate (Phi S (Hstar S)) (Hstar S) /\
    le_candidate (Hstar S) (Phi S (Hstar S)).
Proof.
  intro S.
  split.
  - apply Hstar_prefixed.
  - apply Hstar_least.
    apply Phi_Hstar_prefixed.
Qed.

Definition Sat (S : hierarchy_spec) (n : nat) (phi alpha : Str) : Prop :=
  cand_eval1 (Hstar S) n phi alpha.

Definition Unsat (S : hierarchy_spec) (n : nat) (phi alpha : Str) : Prop :=
  cand_eval0 (Hstar S) n phi alpha.

Theorem Sat_unfold :
  forall S n phi alpha,
    Sat S n phi alpha <->
    cand_prv (Hstar S) (Datatypes.S n) (EvalCl true n phi alpha).
Proof.
  intros S n phi alpha.
  destruct (Hstar_fixed S) as [Hpre Hpost].
  split; intro H.
  - exact (le_eval1 _ _ Hpost n phi alpha H).
  - exact (le_eval1 _ _ Hpre n phi alpha H).
Qed.

Theorem Unsat_unfold :
  forall S n phi alpha,
    Unsat S n phi alpha <->
    cand_prv (Hstar S) (Datatypes.S n) (EvalCl false n phi alpha).
Proof.
  intros S n phi alpha.
  destruct (Hstar_fixed S) as [Hpre Hpost].
  split; intro H.
  - exact (le_eval0 _ _ Hpost n phi alpha H).
  - exact (le_eval0 _ _ Hpre n phi alpha H).
Qed.

Variable FreeOcc : nat -> Str -> Str -> Prop.

Definition EvalConsistent (S : hierarchy_spec) : Prop :=
  forall n phi alpha,
    cand_form (Hstar S) n phi ->
    cand_assign (Hstar S) n phi alpha ->
    ~ (Sat S n phi alpha /\ Unsat S n phi alpha).

Record object_language (S : hierarchy_spec) (n : nat) : Prop := {
  obj_term : Str -> Prop := cand_term (Hstar S) n;
  obj_form : Str -> Prop := cand_form (Hstar S) n;
  obj_assign : Str -> Str -> Prop := cand_assign (Hstar S) n;
  obj_val : Str -> Str -> Str -> Prop := cand_val (Hstar S) n;
  obj_prv : Str -> Prop := cand_prv (Hstar S) n
}.

Definition Sent (S : hierarchy_spec) (n : nat) (phi : Str) : Prop :=
  cand_form (Hstar S) n phi /\
  forall v, size v <= size phi -> ~ FreeOcc n v phi.

Definition Theory (S : hierarchy_spec) (n : nat) (phi : Str) : Prop :=
  Sent S n phi /\ cand_prv (Hstar S) n (ThmCl n phi).

Definition ValFunctional (S : hierarchy_spec) : Prop :=
  forall n t alpha y z,
    cand_val (Hstar S) n t alpha y ->
    cand_val (Hstar S) n t alpha z ->
    y = z.

Definition ValTotalOnAssignedTerms (S : hierarchy_spec) : Prop :=
  forall n t alpha,
    cand_term (Hstar S) n t ->
    assign_term S n t alpha ->
    exists y, cand_val (Hstar S) n t alpha y.

Definition CurrentEvalClaimBlocked (S : hierarchy_spec) : Prop :=
  forall n b phi alpha, ~ cand_claim (Hstar S) n (EvalCl b n phi alpha).

Definition LowerEvalClaimAllowed (S : hierarchy_spec) : Prop :=
  forall m n b phi alpha,
    m < n ->
    cand_form (Hstar S) m phi ->
    cand_assign (Hstar S) m phi alpha ->
    cand_claim (Hstar S) n (EvalCl b m phi alpha).

Definition SynFragmentExact (S : hierarchy_spec) : Prop :=
  forall n j x,
    cand_claim (Hstar S) n (SynCl n j x) <-> syn_frag S n j x.

Definition NoFullInternalSyntax (S : hierarchy_spec) : Prop :=
  forall n j,
    ~ forall x, syn_frag S n j x <-> cand_form (Hstar S) n x.

Definition EmbeddingPreservesTermsAndForms (S : hierarchy_spec) : Prop :=
  forall n x y,
    embed_I S n x y ->
    (cand_term (Hstar S) n x -> cand_term (Hstar S) (Datatypes.S n) y) /\
    (cand_form (Hstar S) n x -> cand_form (Hstar S) (Datatypes.S n) y).

Definition EmbeddingFunctional (S : hierarchy_spec) : Prop :=
  forall n t u v, embed_I S n t u -> embed_I S n t v -> u = v.

Definition EmbeddingTotal (S : hierarchy_spec) : Prop :=
  forall n t, exists u, embed_I S n t u.

Theorem spec_embedding_functional :
  forall S, EmbeddingFunctional S.
Proof.
  intros S n t u v Hu Hv.
  exact (embed_I_functional S n t u v Hu Hv).
Qed.

Theorem spec_embedding_total :
  forall S, EmbeddingTotal S.
Proof.
  intros S n t.
  exact (embed_I_total S n t).
Qed.

Definition FragmentConservative (S : hierarchy_spec) (n : nat) : Prop :=
  forall phi psi,
    fragment_G S n phi ->
    embed_I S n phi psi ->
    Theory S (Datatypes.S n) psi ->
    Theory S n phi.

Definition ForwardTheoryInclusion (S : hierarchy_spec) (n : nat) : Prop :=
  forall phi psi,
    embed_I S n phi psi ->
    Theory S n phi ->
    Theory S (Datatypes.S n) psi.

Definition ProofCert (S : hierarchy_spec) (n : nat) (p c : Str) : Prop :=
  cand_proof (Hstar S) n p c.

Definition proves_bounded (S : hierarchy_spec) (n : nat) (c : Str) : Prop :=
  exists p, size p <= spec_bound S n (size c) /\ ProofCert S n p c.

Definition EvalCert
    (S : hierarchy_spec) (n : nat) (b : bool)
    (phi alpha p : Str) : Prop :=
  size p <= spec_bound S (Datatypes.S n) (size (EvalCl b n phi alpha)) /\
  ProofCert S (Datatypes.S n) p (EvalCl b n phi alpha).

Definition EvalJudgment
    (S : hierarchy_spec) (n : nat) (alpha phi : Str) (b : bool) : Prop :=
  exists p, EvalCert S n b phi alpha p.

Definition ConsCert
    (S : hierarchy_spec) (n : nat) (phi psi p q : Str) : Prop :=
  fragment_G S n phi /\
  embed_I S n phi psi /\
  size p <= spec_bound S (Datatypes.S n) (size (ThmCl (Datatypes.S n) psi)) /\
  ProofCert S (Datatypes.S n) p (ThmCl (Datatypes.S n) psi) /\
  size q <= spec_bound S n (size (ThmCl n phi)) /\
  ProofCert S n q (ThmCl n phi).

Definition ConservativeJudgment
    (S : hierarchy_spec) (n : nat) (phi psi : Str) : Prop :=
  exists p q, ConsCert S n phi psi p q.

Record formal_system (S : hierarchy_spec) : Type := {
  fs_bound_class : bound_class;
  fs_candidate_operator : candidate -> candidate := Phi S;
  fs_fixed_hierarchy : candidate := Hstar S;
  fs_fixed_point : le_candidate (Phi S (Hstar S)) (Hstar S) /\
                   le_candidate (Hstar S) (Phi S (Hstar S));
  fs_sat : nat -> Str -> Str -> Prop := Sat S;
  fs_unsat : nat -> Str -> Str -> Prop := Unsat S;
  fs_theory : nat -> Str -> Prop := Theory S;
  fs_proof_cert : nat -> Str -> Str -> Prop := ProofCert S;
  fs_eval_cert : nat -> bool -> Str -> Str -> Str -> Prop := EvalCert S;
  fs_cons_cert : nat -> Str -> Str -> Str -> Str -> Prop := ConsCert S;
  fs_eval_judgment : nat -> Str -> Str -> bool -> Prop := EvalJudgment S;
  fs_conservative_judgment : nat -> Str -> Str -> Prop := ConservativeJudgment S;
  fs_embedding_functional : EmbeddingFunctional S;
  fs_embedding_total : EmbeddingTotal S
}.

Definition build_formal_system (S : hierarchy_spec) (B : bound_class)
    : formal_system S := {|
  fs_bound_class := B;
  fs_fixed_point := Hstar_fixed S;
  fs_embedding_functional := spec_embedding_functional S;
  fs_embedding_total := spec_embedding_total S
|}.

End Core.

End BoundedStringFixedPoint.
