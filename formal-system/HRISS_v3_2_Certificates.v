(** Finite ordered evaluation trees for HRISS v3.2, Section 10. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Logic.ProofIrrelevance
  Logic.FunctionalExtensionality Program.Equality.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics HRISS_v3_2_Stability
  HRISS_v3_2_Theory HRISS_v3_2_Clauses HRISS_v3_2_Eval.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(** The head followed by an ordered [n]-tuple.  This is the value-level
    counterpart of [power_cons_sc]. *)
Definition tuple_cons_value {D : PDCPO} {n}
    (v : dcar D) (vs : dcar (power_dcpo D n)) :
    dcar (power_dcpo D (S n)) :=
  fun i => @finite_caseS n i (fun _ => dcar D) v (fun j => vs j).

Definition quant_rule_value {Sig H} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) (Q : QSym Sig) i p (Hp : wf_fm H p) : E_car Sig H :=
  @operation_family_map Sig H (ai_Q Q) e
    ((@singleton_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H)
      (@sc_comp (E_dcpo Sig H)
        (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H))
        (E_dcpo Sig H) (@enc_unary_family Sig H)
        (@QuantBody Sig H C i p Hp))) e).

(** Each constructor is one rule node.  The two tuple families encode the
    finite ordered lists of premises of ordinary constructors. *)
Inductive EvalTmCert {Sig} {H : Subgroup} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) : tm Sig -> E_car Sig H -> Prop :=
| Cert_Var : forall i,
    EvalTmCert C e (TVar i)
      (@operation_family_map Sig H (ai_var i) e (empty_power (E_dcpo Sig H)))
| Cert_Fun : forall n (f : TSym Sig n) (xs : tml Sig n) vals,
    EvalTmlCert C e xs vals ->
    EvalTmCert C e (TFun f xs)
      (@operation_family_map Sig H (ai_T f) e vals)
| Cert_QuoteT : forall t (Ht : wf_tm H t),
    EvalTmCert C e (TQuoteT t) (quote_value C (@TmCarrier Sig H t Ht))
| Cert_QuoteF : forall p (Hp : wf_fm H p),
    EvalTmCert C e (TQuoteF p) (quote_value C (@FmCarrier Sig H p Hp))
| Cert_RAppT : forall t u vt q,
    EvalTmCert C e t vt ->
    EvalTmCert C e (TQuoteT u) q ->
    EvalTmCert C e (TRApp t u)
      (Run C (@pair_power (E_dcpo Sig H) vt q))
| Cert_Move : forall g (Hg : Hminus H g),
    EvalTmCert C e (TMove g) (transport_map C g (proj1 Hg) e)
with EvalFmCert {Sig} {H : Subgroup} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) : fm Sig -> E_car Sig H -> Prop :=
| Cert_Pred : forall n (P : PSym Sig n) (xs : tml Sig n) vals,
    EvalTmlCert C e xs vals ->
    EvalFmCert C e (FPred P xs)
      (@operation_family_map Sig H (ai_P P) e vals)
| Cert_Conn : forall n (L : LSym Sig n) (ps : fml Sig n) vals,
    EvalFmlCert C e ps vals ->
    EvalFmCert C e (FConn L ps)
      (@operation_family_map Sig H (ai_L L) e vals)
| Cert_RAppF : forall t p vt q,
    EvalTmCert C e t vt ->
    EvalTmCert C e (TQuoteF p) q ->
    EvalFmCert C e (FRApp t p)
      (Run C (@pair_power (E_dcpo Sig H) vt q))
| Cert_Quant : forall Q i p (Hp : wf_fm H p),
    EvalFmCert C e (FQuant Q i p)
      (@quant_rule_value Sig H C e Q i p Hp)
with EvalTmlCert {Sig} {H : Subgroup} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) : forall n, tml Sig n ->
      dcar (power_dcpo (E_dcpo Sig H) n) -> Prop :=
| Cert_TNil : EvalTmlCert C e TNil (empty_power (E_dcpo Sig H))
| Cert_TCons : forall n t (xs : tml Sig n) v vs,
    EvalTmCert C e t v -> EvalTmlCert C e xs vs ->
    EvalTmlCert C e (TCons t xs)
      (@tuple_cons_value (E_dcpo Sig H) n v vs)
with EvalFmlCert {Sig} {H : Subgroup} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) : forall n, fml Sig n ->
      dcar (power_dcpo (E_dcpo Sig H) n) -> Prop :=
| Cert_FNil : EvalFmlCert C e FNil (empty_power (E_dcpo Sig H))
| Cert_FCons : forall n p (ps : fml Sig n) v vs,
    EvalFmCert C e p v -> EvalFmlCert C e ps vs ->
    EvalFmlCert C e (FCons p ps)
      (@tuple_cons_value (E_dcpo Sig H) n v vs).

Scheme EvalTmCert_ind' := Induction for EvalTmCert Sort Prop
with EvalFmCert_ind' := Induction for EvalFmCert Sort Prop
with EvalTmlCert_ind' := Induction for EvalTmlCert Sort Prop
with EvalFmlCert_ind' := Induction for EvalFmlCert Sort Prop.
Combined Scheme EvalCert_mutind from EvalTmCert_ind', EvalFmCert_ind',
  EvalTmlCert_ind', EvalFmlCert_ind'.

Lemma power_cons_sc_apply : forall X D n (f : SCMap X D)
    (fs : SCMap X (power_dcpo D n)) x,
    @power_cons_sc X D n f fs x =
      @tuple_cons_value D n (f x) (fs x).
Proof.
  intros X D n f fs x. apply functional_extensionality_dep. intro i.
  dependent destruction i.
  - change ((@finite_caseS n (fzero n) (fun _ => SCMap X D) f
        (fun j => @sc_comp X (power_dcpo D n) D
          (power_projection_sc D n j) fs)) x =
      @finite_caseS n (fzero n) (fun _ => dcar D)
        (f x) (fun j => fs x j)).
    now rewrite !finite_caseS_zero.
  - change ((@finite_caseS n (fsucc i) (fun _ => SCMap X D) f
        (fun j => @sc_comp X (power_dcpo D n) D
          (power_projection_sc D n j) fs)) x =
      @finite_caseS n (fsucc i) (fun _ => dcar D)
        (f x) (fun j => fs x j)).
    rewrite !finite_caseS_succ. reflexivity.
Qed.

Lemma ValTmlMap_cons : forall Sig H (C : SyntaxCoding Sig H) e n t
    (xs : tml Sig n) (Ht : wf_tm H t),
    ValTmlMap C (TCons t xs) e =
      @tuple_cons_value (E_dcpo Sig H) n
        (@ValTm Sig H C e t Ht) (ValTmlMap C xs e).
Proof.
  intros Sig H C e n t xs Ht.
  unfold ValTmlMap, ValTm, Val, TmCarrier, Val_map.
  change (@power_cons_sc (E_dcpo Sig H) (E_dcpo Sig H) n
      (val_tm_hist H C (run_history C (tml_height (TCons t xs))) t)
      (val_tml_hist H C (run_history C (tml_height (TCons t xs))) xs) e =
    @tuple_cons_value (E_dcpo Sig H) n
      (val_tm_hist H C (run_history C (tm_height t)) t e)
      (val_tml_hist H C (run_history C (tml_height xs)) xs e)).
  rewrite power_cons_sc_apply.
  rewrite val_tm_later_stage with
    (k := tml_height (TCons t xs)) by apply tm_head_le_tml.
  rewrite val_tml_later_stage with
    (k := tml_height (TCons t xs)) by apply tml_tail_le_tml.
  reflexivity.
Qed.

Lemma ValFmlMap_cons : forall Sig H (C : SyntaxCoding Sig H) e n p
    (ps : fml Sig n) (Hp : wf_fm H p),
    ValFmlMap C (FCons p ps) e =
      @tuple_cons_value (E_dcpo Sig H) n
        (@ValFm Sig H C e p Hp) (ValFmlMap C ps e).
Proof.
  intros Sig H C e n p ps Hp.
  unfold ValFmlMap, ValFm, Val, FmCarrier, Val_map.
  change (@power_cons_sc (E_dcpo Sig H) (E_dcpo Sig H) n
      (val_fm_hist H C (run_history C (fml_height (FCons p ps))) p)
      (val_fml_hist H C (run_history C (fml_height (FCons p ps))) ps) e =
    @tuple_cons_value (E_dcpo Sig H) n
      (val_fm_hist H C (run_history C (fm_height p)) p e)
      (val_fml_hist H C (run_history C (fml_height ps)) ps e)).
  rewrite power_cons_sc_apply.
  assert (Hhead : val_fm_hist H C (run_history C (fml_height (FCons p ps))) p =
      val_fm_hist H C (run_history C (fm_height p)) p).
  { symmetry. apply val_fm_history_agree.
    apply run_history_agree_prefix. apply fm_head_le_fml. }
  rewrite Hhead.
  rewrite val_fml_later_stage with
    (k := fml_height (FCons p ps)) by apply fml_tail_le_fml.
  reflexivity.
Qed.

(** Direct structural recursion keeps the proof terms small while exposing
    that every certificate root is well formed. *)
Fixpoint EvalTmCert_wf {Sig H} (C : SyntaxCoding Sig H) e t v
    (D : @EvalTmCert Sig H C e t v) {struct D} : wf_tm H t
with EvalFmCert_wf {Sig H} (C : SyntaxCoding Sig H) e p v
    (D : @EvalFmCert Sig H C e p v) {struct D} : wf_fm H p
with EvalTmlCert_wf {Sig H} (C : SyntaxCoding Sig H) e n xs vals
    (D : @EvalTmlCert Sig H C e n xs vals) {struct D} : wf_tml H xs
with EvalFmlCert_wf {Sig H} (C : SyntaxCoding Sig H) e n ps vals
    (D : @EvalFmlCert Sig H C e n ps vals) {struct D} : wf_fml H ps.
Proof.
  - destruct D.
    + exact I.
    + exact (@EvalTmlCert_wf Sig H C e n xs vals H0).
    + exact Ht.
    + exact Hp.
    + split; [exact (@EvalTmCert_wf Sig H C e t vt D1)|
        exact (@EvalTmCert_wf Sig H C e (TQuoteT u) q D2)].
    + exact Hg.
  - destruct D.
    + exact (@EvalTmlCert_wf Sig H C e n xs vals H0).
    + exact (@EvalFmlCert_wf Sig H C e n ps vals H0).
    + split.
      * match goal with D0 : EvalTmCert C e t vt |- _ =>
          exact (@EvalTmCert_wf Sig H C e t vt D0) end.
      * match goal with D0 : EvalTmCert C e (TQuoteF p) q |- _ =>
          exact (@EvalTmCert_wf Sig H C e (TQuoteF p) q D0) end.
    + exact Hp.
  - destruct D.
    + exact I.
    + split.
      * match goal with D0 : EvalTmCert C e t v |- _ =>
          exact (@EvalTmCert_wf Sig H C e t v D0) end.
      * match goal with D0 : EvalTmlCert C e xs vs |- _ =>
          exact (@EvalTmlCert_wf Sig H C e n xs vs D0) end.
  - destruct D.
    + exact I.
    + split.
      * match goal with D0 : EvalFmCert C e p v |- _ =>
          exact (@EvalFmCert_wf Sig H C e p v D0) end.
      * match goal with D0 : EvalFmlCert C e ps vs |- _ =>
          exact (@EvalFmlCert_wf Sig H C e n ps vs D0) end.
Defined.
