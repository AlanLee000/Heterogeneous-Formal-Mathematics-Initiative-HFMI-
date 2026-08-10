(** Mechanized structural theorems for HRISS v3.2, Section 13. *)

From Stdlib Require Import Arith.PeanoNat Logic.ClassicalDescription
  Logic.FunctionalExtensionality Logic.ProofIrrelevance.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics HRISS_v3_2_Theory
  HRISS_v3_2_Eval HRISS_v3_2_CertCompleteness HRISS_v3_2_Identity.
Set Implicit Arguments.
Unset Strict Implicit.

(** 13.1: the two maps already constructed from the bilimit are a genuine
    isomorphism, not a postulated domain equation. *)
Record RecursiveStructureIso (Sig : Signature) (H : Subgroup) : Type := {
  rsi_theta : E_car Sig H -> dcar (F_dcpo Sig (E_dcpo Sig H));
  rsi_omega : dcar (F_dcpo Sig (E_dcpo Sig H)) -> E_car Sig H;
  rsi_omega_theta : forall e, rsi_omega (rsi_theta e) = e;
  rsi_theta_omega : forall M, rsi_theta (rsi_omega M) = M
}.

Definition recursive_structure_iso (Sig : Signature) (H : Subgroup) :
    RecursiveStructureIso Sig H :=
  {| rsi_theta := theta_map Sig H;
     rsi_omega := omega_map Sig H;
     rsi_omega_theta := @omega_theta Sig H;
     rsi_theta_omega := @theta_omega Sig H |}.

Definition variable_carrier (Sig : Signature) (H : Subgroup) (i : nat) :
    SyntaxCarrier Sig H := exist _ (ETerm (TVar i)) I.

Theorem E_is_nontrivial : forall Sig H (C : SyntaxCoding Sig H),
    exists x y : E_car Sig H, x <> y.
Proof.
  intros Sig H C.
  exists (quote_value C (variable_carrier Sig H 0)),
    (quote_value C (variable_carrier Sig H 1)).
  intro Heq. apply quote_value_injective in Heq.
  pose proof (f_equal (@proj1_sig _ _) Heq) as Hraw.
  inversion Hraw.
Qed.

(** 13.4 and 13.5 are the exact theorems proved in the core module. *)
Theorem main_nonzero_holonomy : Hol p_path q_path 0.
Proof. apply nonzero_reflection_holonomy. Qed.

Theorem main_path_substitution_separation : forall Sig (s : tm Sig) z z'
    (Csub : CSub 0 s z z'), ~ PathEq Csub p_path q_path.
Proof. apply path_CSub_separation. Qed.

(** 13.6: a typed endpoint-flat comparison target. *)
Record EndpointFlatTarget (Sig : Signature) : Type := {
  eft_car : Type;
  eft_quote : SyntaxCarrier Sig full_subgroup -> eft_car;
  eft_transport : Perm3 -> eft_car -> eft_car;
  eft_val : eft_car -> SyntaxCarrier Sig full_subgroup -> eft_car;
  eft_run : eft_car -> eft_car -> eft_car;
  eft_path : forall i (s : tm Sig) z z' (D : CSub i s z z'),
      Perm3 -> Perm3 -> Prop;
  eft_flat : forall g h, eft_transport g = eft_transport h
}.

Arguments eft_car {Sig} _.

Inductive RAppExpression {Sig} : expr Sig -> Prop :=
| RAE_T : forall t u, RAppExpression (ETerm (TRApp t u))
| RAE_F : forall t p, RAppExpression (EForm (FRApp t p)).

Record PreservesRRP {Sig} (C : SyntaxCoding Sig full_subgroup)
    (T : EndpointFlatTarget Sig) (F : E_car Sig full_subgroup -> eft_car T) :
    Prop := {
  pres_run : forall e u, F (Run C (@pair_power (E_dcpo Sig full_subgroup) e u)) =
      @eft_run Sig T (F e) (F u);
  pres_rapp : forall e (z : SyntaxCarrier Sig full_subgroup),
      RAppExpression (proj1_sig z) ->
      F (Val C e z) = @eft_val Sig T (F e) z;
  pres_path_rule : forall i (s : tm Sig) z z' (D : CSub i s z z') g h,
      PathEq D g h -> @eft_path Sig T i s z z' D g h
}.

Definition QuoteImageInjective {Sig}
    (C : SyntaxCoding Sig full_subgroup) {X}
    (F : E_car Sig full_subgroup -> X) : Prop :=
  forall z w, F (quote_value C z) = F (quote_value C w) -> z = w.

Definition PreservesQuote {Sig} (C : SyntaxCoding Sig full_subgroup)
    (T : EndpointFlatTarget Sig) (F : E_car Sig full_subgroup -> eft_car T) : Prop :=
  forall z, F (quote_value C z) = @eft_quote Sig T z.

Definition PreservesTransport {Sig} (C : SyntaxCoding Sig full_subgroup)
    (T : EndpointFlatTarget Sig) (F : E_car Sig full_subgroup -> eft_car T) : Prop :=
  forall g (Hg : hmem full_subgroup g) e,
    F (transport_map C g Hg e) = @eft_transport Sig T g (F e).

Lemma syntax_act_p_var0 : forall Sig,
    @syntax_act Sig full_subgroup p_path I
      (variable_carrier Sig full_subgroup 0) =
      variable_carrier Sig full_subgroup 1.
Proof. intro Sig. apply sig_prop_ext. reflexivity. Qed.

Lemma syntax_act_q_var0 : forall Sig,
    @syntax_act Sig full_subgroup q_path I
      (variable_carrier Sig full_subgroup 0) =
      variable_carrier Sig full_subgroup 2.
Proof. intro Sig. apply sig_prop_ext. reflexivity. Qed.

Theorem endpoint_flat_no_go : forall Sig
    (C : SyntaxCoding Sig full_subgroup) (T : EndpointFlatTarget Sig)
    (F : E_car Sig full_subgroup -> eft_car T),
    @QuoteImageInjective Sig C (eft_car T) F ->
    @PreservesQuote Sig C T F ->
    @PreservesTransport Sig C T F ->
    @PreservesRRP Sig C T F -> False.
Proof.
  intros Sig C T F Hinj Hquote Htransport Hrrp.
  set (z0 := variable_carrier Sig full_subgroup 0).
  set (z1 := variable_carrier Sig full_subgroup 1).
  set (z2 := variable_carrier Sig full_subgroup 2).
  pose proof (@quote_equivariant Sig full_subgroup C p_path I z0) as Hqp.
  pose proof (@quote_equivariant Sig full_subgroup C q_path I z0) as Hqq.
  assert (Hazp : @syntax_act Sig full_subgroup p_path I z0 = z1).
  { subst z0 z1. apply syntax_act_p_var0. }
  assert (Hazq : @syntax_act Sig full_subgroup q_path I z0 = z2).
  { subst z0 z2. apply syntax_act_q_var0. }
  rewrite Hazp in Hqp. rewrite Hazq in Hqq.
  pose proof (Htransport p_path I (quote_value C z0)) as Htp.
  pose proof (Htransport q_path I (quote_value C z0)) as Htq.
  rewrite Hqp in Htp. rewrite Hqq in Htq.
  pose proof (f_equal (fun R => R (F (quote_value C z0)))
    (@eft_flat Sig T p_path q_path)) as Hflat.
  assert (Heq : F (quote_value C z1) = F (quote_value C z2)).
  { rewrite Htp, Htq. exact Hflat. }
  apply Hinj in Heq.
  pose proof (f_equal (@proj1_sig _ _) Heq) as Hraw.
  inversion Hraw.
Qed.

(** 13.8: Cantor's obstruction for the unrestricted function space. *)
Theorem cantor_no_surjection_to_full_function_space : forall
    (A : Type) (zero one : A), zero <> one ->
    forall code : A -> (A -> A),
      ~ (forall f : A -> A, exists a, code a = f).
Proof.
  intros A zero one Hne code Hsurj.
  set (diag := fun x : A =>
    if excluded_middle_informative (code x x = zero) then one else zero).
  destruct (Hsurj diag) as [a Ha].
  pose proof (f_equal (fun f : A -> A => f a) Ha) as Haa.
  unfold diag in Haa.
  destruct (excluded_middle_informative (code a a = zero)) as [Hz|Hnz].
  - apply Hne. now rewrite <- Haa.
  - apply Hnz. exact Haa.
Qed.

Corollary no_bijection_with_full_endofunction_space : forall
    (A : Type) (zero one : A), zero <> one ->
    ~ exists (enc : A -> (A -> A)) (dec : (A -> A) -> A),
        forall f, enc (dec f) = f.
Proof.
  intros A zero one Hne (enc & dec & Hright).
  eapply (@cantor_no_surjection_to_full_function_space A zero one Hne enc).
  intro f. exists (dec f). apply Hright.
Qed.

Print Assumptions endpoint_flat_no_go.
Print Assumptions no_bijection_with_full_endofunction_space.
