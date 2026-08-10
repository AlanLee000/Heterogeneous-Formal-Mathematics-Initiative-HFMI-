(** The complete forward package of HRISS v3.2, Sections 12.2--14. *)

From Stdlib Require Import Lists.List Logic.ClassicalDescription
  Logic.ProofIrrelevance.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics HRISS_v3_2_Stability
  HRISS_v3_2_Theory HRISS_v3_2_Clauses HRISS_v3_2_Eval
  HRISS_v3_2_Certificates HRISS_v3_2_FiniteTrees
  HRISS_v3_2_CertCompleteness HRISS_v3_2_Identity
  HRISS_v3_2_Structural HRISS_v3_2_EvalEquivariance.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(** The relational branch lists the judgment families themselves.  The
    constructors of these inductive families are exactly the rule families
    displayed in Sections 4 and 5. *)
Record RelationalTransformData (Sig : Signature) : Type := {
  relational_Sub : nat -> tm Sig -> expr Sig -> expr Sig -> Prop;
  relational_BRren : nat -> nat -> expr Sig -> expr Sig -> Prop;
  relational_RootAlpha : fm Sig -> fm Sig -> Prop;
  relational_Alpha : fm Sig -> fm Sig -> Prop;
  relational_AStar : expr Sig -> expr Sig -> Prop;
  relational_CSub : nat -> tm Sig -> expr Sig -> expr Sig -> Prop;
  relational_Path : forall i s z z',
      relational_CSub i s z z' -> Perm3 -> Perm3 -> Prop
}.

Definition relational_transform_data (Sig : Signature) :
    RelationalTransformData Sig :=
  {| relational_Sub := @SubExpr Sig;
     relational_BRren := @BRenExpr Sig;
     relational_RootAlpha := @RootAlpha Sig;
     relational_Alpha := @Alpha Sig;
     relational_AStar := @AStar Sig;
     relational_CSub := @CSub Sig;
     relational_Path := @PathEq Sig |}.

(** This sum is the literal case distinction [Trans(H)] of Section 12.2.
    Equality with the trivial subgroup is carried by the first constructor;
    its negation is carried by the second. *)
Inductive TransformData (Sig : Signature) (H : Subgroup) : Type :=
| TransformIdentity : H = trivial_subgroup -> IdentityTransformData Sig ->
    TransformData Sig H
| TransformRelational : H <> trivial_subgroup ->
    RelationalTransformData Sig -> TransformData Sig H.

Arguments TransformIdentity {Sig H} _ _.
Arguments TransformRelational {Sig H} _ _.

Definition transform_data (Sig : Signature) (H : Subgroup) :
    TransformData Sig H :=
  match excluded_middle_informative (H = trivial_subgroup) with
  | left Heq => TransformIdentity Heq (identity_transform_data Sig)
  | right Hneq => TransformRelational Hneq (relational_transform_data Sig)
  end.

Lemma transform_data_trivial : forall Sig,
    exists Heq : trivial_subgroup = trivial_subgroup,
      transform_data Sig trivial_subgroup =
        TransformIdentity Heq (identity_transform_data Sig).
Proof.
  intro Sig. unfold transform_data.
  destruct excluded_middle_informative as [Heq|Hneq].
  - exists Heq. reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma transform_data_nontrivial : forall Sig H,
    H <> trivial_subgroup ->
    exists Hneq : H <> trivial_subgroup,
      transform_data Sig H =
        TransformRelational Hneq (relational_transform_data Sig).
Proof.
  intros Sig H Hnot. unfold transform_data.
  destruct excluded_middle_informative as [Heq|Hneq].
  - contradiction.
  - exists Hneq. reflexivity.
Qed.

(** One-step rule applicability, kept separate from explicit finite trees. *)
Definition EvalRuleRel {Sig H} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) (z : SyntaxCarrier Sig H)
    (v : E_car Sig H) : Prop :=
  match proj1_sig z with
  | ETerm t => EvalTmCert C e t v
  | EForm p => EvalFmCert C e p v
  end.

Definition SatPair {Sig H} (C : SyntaxCoding Sig H)
    (evp : E_car Sig H * { p : fm Sig | wf_fm H p }) : Prop :=
  Satisfies C (fst evp) (snd evp).

(** This record follows the coordinate order of Section 14.  [Sig], [H], and
    [C] are parameters because the paper fixes these data before forming the
    tuple.  Every field below is a previously constructed coordinate. *)
Record HRISSSystem (Sig : Signature) (H : Subgroup)
    (C : SyntaxCoding Sig H) : Type := {
  hs_H : Subgroup;
  hs_Sigma : Signature;
  hs_A : Type;
  hs_r : hs_A -> nat;
  hs_Tm : Type;
  hs_Fm : Type;
  hs_S : Type;
  hs_sort : hs_S -> sort;
  hs_height : hs_S -> nat;
  hs_Fresh : nat -> NameSet -> Prop;
  hs_FreshWit : NameSet -> Type;
  hs_FV : hs_S -> NameSet;
  hs_BV : hs_S -> NameSet;
  hs_Supp : hs_S -> NameSet;
  hs_AN : hs_S -> NameSet;
  hs_syntax_action : forall g, hmem H g ->
      SyntaxCarrier Sig H -> SyntaxCarrier Sig H;
  hs_transform : TransformData Sig H;
  hs_path_compatibility : NameSet -> Perm3 -> Perm3 -> Prop;
  hs_holonomy : Perm3 -> Perm3 -> nat -> Prop;
  hs_F : PDCPO -> PDCPO;
  hs_D : nat -> PDCPO;
  hs_iota : forall m, SCMap (hs_D m) (hs_D (S m));
  hs_rho : forall m, SCMap (hs_D (S m)) (hs_D m);
  hs_stage_action : forall m g, hmem H g ->
      SCMap (hs_D m) (hs_D m);
  hs_E : PDCPO;
  hs_Theta : SCMap hs_E (hs_F hs_E);
  hs_Omega : SCMap (hs_F hs_E) hs_E;
  hs_interpreter_action : forall g, hmem H g -> SCMap hs_E hs_E;
  hs_code_type : Type;
  hs_encode_syntax : SyntaxCarrier Sig H -> hs_code_type;
  hs_decode_syntax : hs_code_type -> SyntaxCarrier Sig H;
  hs_quote : SyntaxCarrier Sig H -> dcar hs_E;
  hs_delta : dcar hs_E -> SyntaxCarrier Sig H -> Prop;
  hs_enc : forall n, SCMap (power_dcpo hs_E n) hs_E -> dcar hs_E;
  hs_dec : forall n, dcar hs_E -> SCMap (power_dcpo hs_E n) hs_E;
  hs_update : nat -> dcar hs_E -> dcar hs_E -> dcar hs_E;
  hs_Val : dcar hs_E -> SyntaxCarrier Sig H -> dcar hs_E;
  hs_Run_minus_one : SCMap (power_dcpo hs_E 2) hs_E;
  hs_Run_stage : nat -> SCMap (power_dcpo hs_E 2) hs_E;
  hs_Run : SCMap (power_dcpo hs_E 2) hs_E;
  hs_eval_rule : dcar hs_E -> SyntaxCarrier Sig H -> dcar hs_E -> Prop;
  hs_eval_derivation : dcar hs_E -> SyntaxCarrier Sig H -> dcar hs_E -> Prop;
  hs_truth_family : dcar hs_E -> dcar hs_E -> Prop;
  hs_context : Type;
  hs_sat_set : (dcar hs_E * { p : fm Sig | wf_fm H p }) -> Prop;
  hs_satisfies : dcar hs_E -> { p : fm Sig | wf_fm H p } -> Prop;
  hs_local_consequence : dcar hs_E -> Context Sig H ->
      { p : fm Sig | wf_fm H p } -> Prop;
  hs_global_consequence : Context Sig H ->
      { p : fm Sig | wf_fm H p } -> Prop
}.

Definition HRISS_system (Sig : Signature) (H : Subgroup)
    (C : SyntaxCoding Sig H) : @HRISSSystem Sig H C :=
  {| hs_H := H;
     hs_Sigma := Sig;
     hs_A := AIndex Sig;
     hs_r := @arity Sig;
     hs_Tm := { t : tm Sig | wf_tm H t };
     hs_Fm := { p : fm Sig | wf_fm H p };
     hs_S := SyntaxCarrier Sig H;
     hs_sort := fun z => expr_sort (proj1_sig z);
     hs_height := fun z => expr_height (proj1_sig z);
     hs_Fresh := Fresh;
     hs_FreshWit := FreshWit;
     hs_FV := fun z => FV (proj1_sig z);
     hs_BV := fun z => BV (proj1_sig z);
     hs_Supp := fun z => Supp (proj1_sig z);
     hs_AN := fun z => AN (proj1_sig z);
     hs_syntax_action := fun g Hg z => syntax_act g Hg z;
     hs_transform := transform_data Sig H;
     hs_path_compatibility := path_compatible;
     hs_holonomy := Hol;
     hs_F := F_dcpo Sig;
     hs_D := D_level Sig;
     hs_iota := chain_iota Sig H;
     hs_rho := chain_rho Sig H;
     hs_stage_action := fun m g Hg => B_level_map C m g Hg;
     hs_E := E_dcpo Sig H;
     hs_Theta := theta_map Sig H;
     hs_Omega := omega_map Sig H;
     hs_interpreter_action := fun g Hg => transport_map C g Hg;
     hs_code_type := CodeNat;
     hs_encode_syntax := syntax_encode C;
     hs_decode_syntax := syntax_decode C;
     hs_quote := quote_value C;
     hs_delta := decode_rel C;
     hs_enc := enc Sig H;
     hs_dec := dec Sig H;
     hs_update := upd Sig H;
     hs_Val := Val C;
     hs_Run_minus_one := run_bottom Sig H;
     hs_Run_stage := Run_n C;
     hs_Run := Run C;
     hs_eval_rule := EvalRuleRel C;
     hs_eval_derivation := EvalDerives C;
     hs_truth_family := TruthRegion;
     hs_context := Context Sig H;
     hs_sat_set := SatPair C;
     hs_satisfies := Satisfies C;
     hs_local_consequence := LocalConsequence C;
     hs_global_consequence := GlobalConsequence C |}.

Arguments HRISS_system Sig H C : clear implicits.

(** The internal baseline of Section 12.2 is literally the trivial instance,
    with no reference to any external document. *)
Definition local_RISS20 (Sig : Signature)
    (C : SyntaxCoding Sig trivial_subgroup) :
    @HRISSSystem Sig trivial_subgroup C :=
  HRISS_system Sig trivial_subgroup C.

Arguments local_RISS20 Sig C : clear implicits.

Definition HRISS_identity_restriction (Sig : Signature)
    (C : SyntaxCoding Sig trivial_subgroup) :
    @HRISSSystem Sig trivial_subgroup C :=
  HRISS_system Sig trivial_subgroup C.

Arguments HRISS_identity_restriction Sig C : clear implicits.

Theorem exact_identity_degeneration : forall Sig
    (C : SyntaxCoding Sig trivial_subgroup),
    HRISS_identity_restriction Sig C = local_RISS20 Sig C.
Proof. reflexivity. Qed.

Definition HRISS_main (Sig : Signature)
    (C : SyntaxCoding Sig full_subgroup) :
    @HRISSSystem Sig full_subgroup C :=
  HRISS_system Sig full_subgroup C.

Arguments HRISS_main Sig C : clear implicits.

Theorem main_branch_is_full : forall Sig
    (C : SyntaxCoding Sig full_subgroup),
    hs_H (HRISS_main Sig C) = full_subgroup.
Proof. reflexivity. Qed.

(** The packaged coordinates retain the already proved inverse equations,
    runner equation, and certificate completeness. *)
Theorem packaged_recursive_inverse : forall Sig H (C : SyntaxCoding Sig H) e,
    @hs_Omega Sig H C (HRISS_system Sig H C)
      (@hs_Theta Sig H C (HRISS_system Sig H C) e) = e.
Proof. intros; apply omega_theta. Qed.

Theorem packaged_Run_quote : forall Sig H (C : SyntaxCoding Sig H) e z,
    @hs_Run Sig H C (HRISS_system Sig H C)
      (@pair_power (E_dcpo Sig H) e (quote_value C z)) =
    @hs_Val Sig H C (HRISS_system Sig H C) e z.
Proof. intros; apply Run_quote. Qed.

Theorem packaged_certificate_complete : forall Sig H
    (C : SyntaxCoding Sig H) e z v,
    @hs_eval_derivation Sig H C (HRISS_system Sig H C) e z v <->
    v = @hs_Val Sig H C (HRISS_system Sig H C) e z.
Proof. intros; apply EvalDerives_iff_Val. Qed.

Theorem packaged_Val_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) e z,
    @hs_Val Sig H C (HRISS_system Sig H C)
      (@hs_interpreter_action Sig H C (HRISS_system Sig H C) g Hg e)
      (@hs_syntax_action Sig H C (HRISS_system Sig H C) g Hg z) =
    @hs_interpreter_action Sig H C (HRISS_system Sig H C) g Hg
      (@hs_Val Sig H C (HRISS_system Sig H C) e z).
Proof. intros. apply Val_equivariant. Qed.

Theorem packaged_Run_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) e u,
    @hs_Run Sig H C (HRISS_system Sig H C)
      (@pair_power (E_dcpo Sig H)
        (@hs_interpreter_action Sig H C (HRISS_system Sig H C) g Hg e)
        (@hs_interpreter_action Sig H C (HRISS_system Sig H C) g Hg u)) =
    @hs_interpreter_action Sig H C (HRISS_system Sig H C) g Hg
      (@hs_Run Sig H C (HRISS_system Sig H C)
        (@pair_power (E_dcpo Sig H) e u)).
Proof. intros. apply Run_equivariant. Qed.

Theorem packaged_Satisfies_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) e p,
    @hs_satisfies Sig H C (HRISS_system Sig H C)
      (@hs_interpreter_action Sig H C (HRISS_system Sig H C) g Hg e)
      (@formula_act Sig H g Hg p) <->
    @hs_satisfies Sig H C (HRISS_system Sig H C) e p.
Proof. intros. apply Satisfies_equivariant. Qed.
