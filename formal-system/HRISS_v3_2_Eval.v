(** RApp equations and finite evaluation certificates for HRISS v3.2. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Logic.ProofIrrelevance
  Logic.ClassicalDescription Logic.FunctionalExtensionality Program.Equality.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics HRISS_v3_2_Stability
  HRISS_v3_2_Theory HRISS_v3_2_Clauses.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma finite_caseS_zero : forall n (P : Finite (S n) -> Type)
    (hz : P (fzero n)) (hs : forall j : Finite n, P (fsucc j)),
    @finite_caseS n (fzero n) P hz hs = hz.
Proof.
  intros. unfold finite_caseS. cbn.
  unfold Equality.simplification_heq, Equality.solution_left,
    Equality.solution_right, Equality.block. cbn.
  replace (JMeq_eq JMeq_refl) with
    (@eq_refl (Finite (S n)) (fzero n)) by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma finite_caseS_succ : forall n (j : Finite n)
    (P : Finite (S n) -> Type) (hz : P (fzero n))
    (hs : forall j : Finite n, P (fsucc j)),
    @finite_caseS n (fsucc j) P hz hs = hs j.
Proof.
  intros. unfold finite_caseS. cbn.
  unfold Equality.simplification_heq, Equality.solution_left,
    Equality.solution_right, Equality.block. cbn.
  replace (JMeq_eq JMeq_refl) with
    (@eq_refl (Finite (S n)) (fsucc j)) by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma pair_maps_apply : forall X D (f g : SCMap X D) x,
    @pair_maps X D f g x = @pair_power D (f x) (g x).
Proof.
  intros X D f g x. apply functional_extensionality_dep. intro i.
  dependent destruction i.
  - change ((@finite_caseS 1 (fzero 1) (fun _ => SCMap X D) f
        (fun j => @sc_comp X (power_dcpo D 1) D
          (power_projection_sc D 1 j) (@singleton_tuple_sc X D g))) x = f x).
    rewrite finite_caseS_zero. reflexivity.
  - change ((@finite_caseS 1 (fsucc i) (fun _ => SCMap X D) f
        (fun j => @sc_comp X (power_dcpo D 1) D
          (power_projection_sc D 1 j) (@singleton_tuple_sc X D g))) x = g x).
    rewrite finite_caseS_succ.
    dependent destruction i.
    + change ((@finite_caseS 0 (fzero 0) (fun _ => SCMap X D) g
          (fun j => @sc_comp X (power_dcpo D 0) D
            (power_projection_sc D 0 j) (@empty_tuple_sc X D))) x = g x).
      rewrite finite_caseS_zero. reflexivity.
    + dependent destruction i.
Qed.

Lemma quote_tm_raw_eq : forall Sig H (C : SyntaxCoding Sig H) t
    (Ht : wf_tm H t),
    quote_tm_raw C t = quote_value C (@TmCarrier Sig H t Ht).
Proof.
  intros. unfold quote_tm_raw.
  destruct (excluded_middle_informative (wf_tm H t)) as [Ht'|Hn].
  - f_equal. apply sig_prop_ext. reflexivity.
  - contradiction.
Qed.

Lemma quote_fm_raw_eq : forall Sig H (C : SyntaxCoding Sig H) p
    (Hp : wf_fm H p),
    quote_fm_raw C p = quote_value C (@FmCarrier Sig H p Hp).
Proof.
  intros. unfold quote_fm_raw.
  destruct (excluded_middle_informative (wf_fm H p)) as [Hp'|Hn].
  - f_equal. apply sig_prop_ext. reflexivity.
  - contradiction.
Qed.

Theorem Val_RAppT : forall Sig H (C : SyntaxCoding Sig H) e t u
    (Ht : wf_tm H t) (Hu : wf_tm H u),
    @ValTm Sig H C e (TRApp t u) (conj Ht Hu) =
      Run C (@pair_power (E_dcpo Sig H)
        (@ValTm Sig H C e t Ht)
        (quote_value C (@TmCarrier Sig H u Hu))).
Proof.
  intros Sig H C e t u Ht Hu.
  unfold ValTm, Val, TmCarrier, Val_map.
  set (m := Nat.max (tm_height t) (tm_height u)).
  change ((nth m (run_history C (S m)) (run_bottom Sig H))
      (@pair_maps (E_dcpo Sig H) (E_dcpo Sig H)
        (val_tm_hist H C (run_history C (S m)) t)
        (@sc_const (E_dcpo Sig H) (E_dcpo Sig H) (quote_tm_raw C u)) e) =
    Run C (@pair_power (E_dcpo Sig H)
      (val_tm_hist H C (run_history C (tm_height t)) t e)
      (quote_value C (@TmCarrier Sig H u Hu)))).
  rewrite pair_maps_apply, (@quote_tm_raw_eq Sig H C u Hu).
  rewrite val_tm_later_stage with (k := S m) by (unfold m; lia).
  change (Run_n C m
      (@pair_power (E_dcpo Sig H)
        (val_tm_hist H C (run_history C (tm_height t)) t e)
        (quote_value C (@TmCarrier Sig H u Hu))) =
    Run C
      (@pair_power (E_dcpo Sig H)
        (val_tm_hist H C (run_history C (tm_height t)) t e)
        (quote_value C (@TmCarrier Sig H u Hu)))).
  apply (@Run_stage_total_on_quote Sig H C m
    (@TmCarrier Sig H u Hu)
    (val_tm_hist H C (run_history C (tm_height t)) t e)).
  cbn. unfold m. apply Nat.le_max_r.
Qed.

Theorem Val_RAppF : forall Sig H (C : SyntaxCoding Sig H) e t p
    (Ht : wf_tm H t) (Hp : wf_fm H p),
    @ValFm Sig H C e (FRApp t p) (conj Ht Hp) =
      Run C (@pair_power (E_dcpo Sig H)
        (@ValTm Sig H C e t Ht)
        (quote_value C (@FmCarrier Sig H p Hp))).
Proof.
  intros Sig H C e t p Ht Hp.
  unfold ValFm, ValTm, Val, FmCarrier, TmCarrier, Val_map.
  set (m := Nat.max (tm_height t) (fm_height p)).
  change ((nth m (run_history C (S m)) (run_bottom Sig H))
      (@pair_maps (E_dcpo Sig H) (E_dcpo Sig H)
        (val_tm_hist H C (run_history C (S m)) t)
        (@sc_const (E_dcpo Sig H) (E_dcpo Sig H) (quote_fm_raw C p)) e) =
    Run C (@pair_power (E_dcpo Sig H)
      (val_tm_hist H C (run_history C (tm_height t)) t e)
      (quote_value C (@FmCarrier Sig H p Hp)))).
  rewrite pair_maps_apply, (@quote_fm_raw_eq Sig H C p Hp).
  rewrite val_tm_later_stage with (k := S m) by (unfold m; lia).
  change (Run_n C m
      (@pair_power (E_dcpo Sig H)
        (val_tm_hist H C (run_history C (tm_height t)) t e)
        (quote_value C (@FmCarrier Sig H p Hp))) =
    Run C
      (@pair_power (E_dcpo Sig H)
        (val_tm_hist H C (run_history C (tm_height t)) t e)
        (quote_value C (@FmCarrier Sig H p Hp)))).
  apply (@Run_stage_total_on_quote Sig H C m
    (@FmCarrier Sig H p Hp)
    (val_tm_hist H C (run_history C (tm_height t)) t e)).
  cbn. unfold m. apply Nat.le_max_r.
Qed.

Print Assumptions Val_RAppT.
Print Assumptions Val_RAppF.
