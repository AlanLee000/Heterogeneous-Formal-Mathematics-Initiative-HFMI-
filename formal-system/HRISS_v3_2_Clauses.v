(** Constructor equations for the total HRISS valuation. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Logic.ProofIrrelevance
  Logic.ClassicalDescription.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics HRISS_v3_2_Stability
  HRISS_v3_2_Theory.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Definition TmCarrier {Sig} (H : Subgroup) (t : tm Sig) (Ht : wf_tm H t) :
    SyntaxCarrier Sig H := exist _ (ETerm t) Ht.

Definition FmCarrier {Sig} (H : Subgroup) (p : fm Sig) (Hp : wf_fm H p) :
    SyntaxCarrier Sig H := exist _ (EForm p) Hp.

Definition ValTm {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    (t : tm Sig) (Ht : wf_tm H t) : E_car Sig H :=
  Val C e (@TmCarrier Sig H t Ht).

Definition ValFm {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    (p : fm Sig) (Hp : wf_fm H p) : E_car Sig H :=
  Val C e (@FmCarrier Sig H p Hp).

Definition ValTmlMap {Sig H} (C : SyntaxCoding Sig H) {n} (xs : tml Sig n) :
    SCMap (E_dcpo Sig H) (power_dcpo (E_dcpo Sig H) n) :=
  val_tml_hist H C (run_history C (tml_height xs)) xs.

Definition ValFmlMap {Sig H} (C : SyntaxCoding Sig H) {n} (ps : fml Sig n) :
    SCMap (E_dcpo Sig H) (power_dcpo (E_dcpo Sig H) n) :=
  val_fml_hist H C (run_history C (fml_height ps)) ps.

Lemma val_tml_later_stage : forall Sig H (C : SyntaxCoding Sig H) n
    (xs : tml Sig n) k,
    tml_height xs <= k ->
    val_tml_hist H C (run_history C k) xs = ValTmlMap C xs.
Proof.
  intros. symmetry. apply val_tml_history_agree.
  now apply run_history_agree_prefix.
Qed.

Lemma val_fml_later_stage : forall Sig H (C : SyntaxCoding Sig H) n
    (ps : fml Sig n) k,
    fml_height ps <= k ->
    val_fml_hist H C (run_history C k) ps = ValFmlMap C ps.
Proof.
  intros. symmetry. apply val_fml_history_agree.
  now apply run_history_agree_prefix.
Qed.

Lemma val_tm_later_stage : forall Sig H (C : SyntaxCoding Sig H)
    (t : tm Sig) k,
    tm_height t <= k ->
    val_tm_hist H C (run_history C k) t =
      val_tm_hist H C (run_history C (tm_height t)) t.
Proof.
  intros. symmetry. apply val_tm_history_agree.
  now apply run_history_agree_prefix.
Qed.

Theorem Val_Var : forall Sig H (C : SyntaxCoding Sig H) e i,
    @ValTm Sig H C e (TVar i) I =
      @operation_family_map Sig H (ai_var i) e (empty_power (E_dcpo Sig H)).
Proof. reflexivity. Qed.

Theorem Val_Fun : forall Sig H (C : SyntaxCoding Sig H) e n
    (f : TSym Sig n) xs (Hxs : wf_tml H xs),
    @ValTm Sig H C e (TFun f xs) Hxs =
      @operation_family_map Sig H (ai_T f) e (ValTmlMap C xs e).
Proof.
  intros Sig H C e n f xs Hxs.
  unfold ValTm, Val, TmCarrier, Val_map.
  destruct xs as [|n x xs].
  - reflexivity.
  - change (@operation_family_map Sig H (ai_T f) e
      (val_tml_hist H C (run_history C (S (tml_height (TCons x xs))))
        (TCons x xs) e) =
      @operation_family_map Sig H (ai_T f) e (ValTmlMap C (TCons x xs) e)).
    rewrite val_tml_later_stage with (k := S (tml_height (TCons x xs)));
      [reflexivity|lia].
Qed.

Theorem Val_Pred : forall Sig H (C : SyntaxCoding Sig H) e n
    (P : PSym Sig n) xs (Hxs : wf_tml H xs),
    @ValFm Sig H C e (FPred P xs) Hxs =
      @operation_family_map Sig H (ai_P P) e (ValTmlMap C xs e).
Proof.
  intros Sig H C e n P xs Hxs.
  unfold ValFm, Val, FmCarrier, Val_map.
  destruct xs as [|n x xs].
  - reflexivity.
  - change (@operation_family_map Sig H (ai_P P) e
      (val_tml_hist H C (run_history C (S (tml_height (TCons x xs))))
        (TCons x xs) e) =
      @operation_family_map Sig H (ai_P P) e (ValTmlMap C (TCons x xs) e)).
    rewrite val_tml_later_stage with (k := S (tml_height (TCons x xs)));
      [reflexivity|lia].
Qed.

Theorem Val_Conn : forall Sig H (C : SyntaxCoding Sig H) e n
    (L : LSym Sig n) ps (Hps : wf_fml H ps),
    @ValFm Sig H C e (FConn L ps) Hps =
      @operation_family_map Sig H (ai_L L) e (ValFmlMap C ps e).
Proof.
  intros Sig H C e n L ps Hps.
  unfold ValFm, Val, FmCarrier, Val_map.
  destruct ps as [|n p ps].
  - reflexivity.
  - change (@operation_family_map Sig H (ai_L L) e
      (val_fml_hist H C (run_history C (S (fml_height (FCons p ps))))
        (FCons p ps) e) =
      @operation_family_map Sig H (ai_L L) e (ValFmlMap C (FCons p ps) e)).
    rewrite val_fml_later_stage with (k := S (fml_height (FCons p ps)));
      [reflexivity|lia].
Qed.

Theorem Val_QuoteT : forall Sig H (C : SyntaxCoding Sig H) e t
    (Ht : wf_tm H t),
    @ValTm Sig H C e (TQuoteT t) Ht = quote_value C (@TmCarrier Sig H t Ht).
Proof.
  intros. unfold ValTm, Val, TmCarrier, Val_map.
  change (quote_tm_raw C t = quote_value C (@TmCarrier Sig H t Ht)).
  unfold quote_tm_raw.
  destruct (excluded_middle_informative (wf_tm H t)) as [Ht'|Hn].
  - assert (Heq : exist (fun z : expr Sig => wf_expr H z) (ETerm t) Ht' =
        @TmCarrier Sig H t Ht).
    { apply sig_prop_ext. reflexivity. }
    now rewrite Heq.
  - contradiction.
Qed.

Theorem Val_QuoteF : forall Sig H (C : SyntaxCoding Sig H) e p
    (Hp : wf_fm H p),
    @ValTm Sig H C e (TQuoteF p) Hp = quote_value C (@FmCarrier Sig H p Hp).
Proof.
  intros. unfold ValTm, Val, FmCarrier, Val_map.
  change (quote_fm_raw C p = quote_value C (@FmCarrier Sig H p Hp)).
  unfold quote_fm_raw.
  destruct (excluded_middle_informative (wf_fm H p)) as [Hp'|Hn].
  - assert (Heq : exist (fun z : expr Sig => wf_expr H z) (EForm p) Hp' =
        @FmCarrier Sig H p Hp).
    { apply sig_prop_ext. reflexivity. }
    now rewrite Heq.
  - contradiction.
Qed.

Theorem Val_Move : forall Sig H (C : SyntaxCoding Sig H) e g
    (Hg : Hminus H g),
    @ValTm Sig H C e (TMove g) Hg = transport_map C g (proj1 Hg) e.
Proof.
  intros. unfold ValTm, Val, TmCarrier, Val_map.
  change (val_tm_hist H C (run_history C 0) (TMove g) e =
    transport_map C g (proj1 Hg) e).
  rewrite (val_move_clause C (run_history C 0) Hg). reflexivity.
Qed.

Definition QuantBody {Sig H} (C : SyntaxCoding Sig H) i
    (p : fm Sig) (Hp : wf_fm H p) :
    SCMap (E_dcpo Sig H) (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H)) :=
  @abstraction_map Sig H i (Val_map C (EForm p)).

Theorem Val_Quant : forall Sig H (C : SyntaxCoding Sig H) e Q i p
    (Hp : wf_fm H p),
    @ValFm Sig H C e (FQuant Q i p) Hp =
      @operation_family_map Sig H (ai_Q Q) e
        ((@singleton_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H)
          (@sc_comp (E_dcpo Sig H)
            (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H))
            (E_dcpo Sig H) (@enc_unary_family Sig H)
            (@QuantBody Sig H C i p Hp))) e).
Proof.
  intros Sig H C e Q i p Hp.
  unfold ValFm, Val, FmCarrier, QuantBody.
  change (val_fm_hist H C (run_history C (S (fm_height p)))
      (FQuant Q i p) e =
    @operation_family_map Sig H (ai_Q Q) e
      ((@singleton_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H)
        (@sc_comp (E_dcpo Sig H)
          (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H))
          (E_dcpo Sig H) (@enc_unary_family Sig H)
          (@abstraction_map Sig H i (Val_map C (EForm p))))) e)).
  rewrite val_quant_clause.
  assert (Hbody : val_fm_hist H C (run_history C (S (fm_height p))) p =
      Val_map C (EForm p)).
  { unfold Val_map; cbn [expr_height].
    symmetry. apply val_fm_history_agree.
    apply run_history_agree_prefix. lia. }
  now rewrite Hbody.
Qed.

Print Assumptions Val_QuoteT.
Print Assumptions Val_Quant.
