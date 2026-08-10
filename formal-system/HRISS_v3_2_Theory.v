(** Consequences of height stability: stage correctness and satisfaction. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics HRISS_v3_2_Stability.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma run_history_extend : forall Sig H (C : SyntaxCoding Sig H) n d,
    exists tail,
      run_history C (n + d) = run_history C n ++ tail.
Proof.
  intros Sig H C n d. induction d as [|d IH].
  - exists []. rewrite Nat.add_0_r, app_nil_r. reflexivity.
  - destruct IH as [tail IH].
    rewrite Nat.add_succ_r, run_history_succ, IH.
    exists (tail ++ [make_run C (run_history C n ++ tail) (n + d)]).
    now rewrite app_assoc.
Qed.

Lemma run_history_prefix : forall Sig H (C : SyntaxCoding Sig H) n m,
    n <= m -> exists tail,
      run_history C m = run_history C n ++ tail.
Proof.
  intros Sig H C n m Hnm.
  destruct (@run_history_extend Sig H C n (m - n)) as [tail Htail].
  exists tail. replace (n + (m - n)) with m in Htail by lia. exact Htail.
Qed.

Lemma run_history_agree_prefix : forall Sig H (C : SyntaxCoding Sig H) n m,
    n <= m -> history_agree n (run_history C n) (run_history C m).
Proof.
  intros Sig H C n m Hnm j Hj.
  destruct (run_history_prefix C Hnm) as [tail Htail].
  rewrite Htail, app_nth1; [reflexivity|].
  rewrite run_history_length. exact Hj.
Qed.

Lemma val_history_stage : forall Sig H (C : SyntaxCoding Sig H) z n,
    expr_height z <= n ->
    val_expr_hist C (run_history C (expr_height z)) z =
      val_expr_hist C (run_history C n) z.
Proof.
  intros. apply val_expr_history_agree.
  now apply run_history_agree_prefix.
Qed.

Theorem Run_n_quote_Val : forall Sig H (C : SyntaxCoding Sig H) n
    (z : SyntaxCarrier Sig H) (e : E_car Sig H),
    expr_height (proj1_sig z) <= n ->
    Run_n C n (@pair_power (E_dcpo Sig H) e (quote_value C z)) = Val C e z.
Proof.
  intros Sig H C n z e Hz.
  rewrite Run_n_quote by exact Hz.
  unfold Val, Val_map.
  pose proof (@val_history_stage Sig H C (proj1_sig z) n Hz) as Hstage.
  now rewrite Hstage.
Qed.

(** The total runner agrees with every sufficiently high finite stage on a
    syntax quotation. *)
Theorem Run_stage_total_on_quote : forall Sig H (C : SyntaxCoding Sig H) n
    (z : SyntaxCarrier Sig H) (e : E_car Sig H),
    expr_height (proj1_sig z) <= n ->
    Run_n C n (@pair_power (E_dcpo Sig H) e (quote_value C z)) =
      Run C (@pair_power (E_dcpo Sig H) e (quote_value C z)).
Proof. intros; rewrite Run_n_quote_Val by assumption; symmetry; apply Run_quote. Qed.

(** ** Section 11: truth region, relative satisfaction, and consequence *)

Definition TruthOpen {Sig H} (u : E_car Sig H) : Prop :=
  pi_map Sig H 0 u = Some 1.

Definition assert_operation {Sig H} (e : E_car Sig H) :
    SCMap (E_dcpo Sig H) (E_dcpo Sig H) :=
  @sc_comp (E_dcpo Sig H) (power_dcpo (E_dcpo Sig H) 1) (E_dcpo Sig H)
    (theta_map Sig H e ai_assert)
    (@singleton_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H)
      (sc_id (E_dcpo Sig H))).

Definition TruthRegion {Sig H} (e v : E_car Sig H) : Prop :=
  TruthOpen (assert_operation e v).

Definition Satisfies {Sig H} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) (p : { q : fm Sig | wf_fm H q }) : Prop :=
  TruthRegion e (Val C e (exist _ (EForm (proj1_sig p)) (proj2_sig p))).

Definition Context (Sig : Signature) (H : Subgroup) : Type :=
  list { p : fm Sig | wf_fm H p }.

Fixpoint ContextFV {Sig H} (Gamma : Context Sig H) : NameSet :=
  match Gamma with
  | [] => []
  | p :: Gamma' => FV_fm (proj1_sig p) ++ ContextFV Gamma'
  end.

Definition LocalConsequence {Sig H} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) (Gamma : Context Sig H)
    (p : { q : fm Sig | wf_fm H q }) : Prop :=
  (forall q, In q Gamma -> Satisfies C e q) -> Satisfies C e p.

Definition GlobalConsequence {Sig H} (C : SyntaxCoding Sig H)
    (Gamma : Context Sig H) (p : { q : fm Sig | wf_fm H q }) : Prop :=
  forall e : E_car Sig H, LocalConsequence C e Gamma p.

Lemma local_consequence_empty : forall Sig H (C : SyntaxCoding Sig H) e p,
    LocalConsequence C e [] p <-> Satisfies C e p.
Proof.
  intros Sig H C e p. unfold LocalConsequence. split.
  - intro Hlocal. apply Hlocal. intros q Hin. inversion Hin.
  - intros Hp _. exact Hp.
Qed.

Lemma global_consequence_empty : forall Sig H (C : SyntaxCoding Sig H) p,
    GlobalConsequence C [] p <-> forall e, Satisfies C e p.
Proof.
  intros Sig H C p. unfold GlobalConsequence. split.
  - intros Hglobal e. apply Hglobal. intros q Hin. inversion Hin.
  - intros Hall e _. apply Hall.
Qed.

Print Assumptions Run_n_quote_Val.
Print Assumptions Run_stage_total_on_quote.
Print Assumptions global_consequence_empty.
