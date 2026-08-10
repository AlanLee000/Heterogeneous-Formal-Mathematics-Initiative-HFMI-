(** Strict evaluator and runner equivariance, Section 9.6. *)

From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lists.List Lia Logic.ProofIrrelevance
  Logic.FunctionalExtensionality Program.Equality.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics
  HRISS_v3_2_Equivariance HRISS_v3_2_Eval HRISS_v3_2_Certificates
  HRISS_v3_2_Theory.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Lemma enc_unary_abstraction_transport : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) i
    (body body' : SCMap (E_dcpo Sig H) (E_dcpo Sig H)),
    (forall r, body' (transport_map C g Hg r) =
      transport_map C g Hg (body r)) ->
    forall e,
    @enc_unary_family Sig H
      (@abstraction_map Sig H (pact g i) body'
        (transport_map C g Hg e)) =
    transport_map C g Hg
      (@enc_unary_family Sig H (@abstraction_map Sig H i body e)).
Proof.
  intros Sig H C g Hg i body body' Hbody e.
  pose (K := @unary_power_lift (E_dcpo Sig H)
    (@abstraction_map Sig H i body e)).
  pose (K' := @unary_power_lift (E_dcpo Sig H)
    (@abstraction_map Sig H (pact g i) body'
      (transport_map C g Hg e))).
  pose proof (@enc_unary_family_apply Sig H
    (@abstraction_map Sig H (pact g i) body'
      (transport_map C g Hg e))) as Hleft.
  pose proof (@enc_unary_family_apply Sig H
    (@abstraction_map Sig H i body e)) as Hright.
  assert (Hconj :
    conjugate_operation (E_dcpo Sig H) 1
      (transport_map C g Hg) (transport_inverse_map C g Hg) K = K').
  { subst K K'. apply unary_abstraction_conjugate. exact Hbody. }
  pose proof (@enc_transport Sig H C g Hg 1 K) as Henc.
  exact (eq_trans Hleft
    (eq_trans
      (eq_sym (eq_trans Henc (f_equal (enc Sig H 1) Hconj)))
      (f_equal (transport_map C g Hg) (eq_sym Hright)))).
Qed.

(** The name action changes neither tree shape nor height. *)
Fixpoint act_tm_height {Sig} g (t : tm Sig) {struct t} :
    tm_height (act_tm g t) = tm_height t
with act_fm_height {Sig} g (p : fm Sig) {struct p} :
    fm_height (act_fm g p) = fm_height p
with act_tml_height {Sig n} g (xs : tml Sig n) {struct xs} :
    tml_height (act_tml g xs) = tml_height xs
with act_fml_height {Sig n} g (ps : fml Sig n) {struct ps} :
    fml_height (act_fml g ps) = fml_height ps.
Proof.
  - destruct t as [i|n f xs|u|p|u v|a]; cbn.
    + reflexivity.
    + pose proof (@act_tml_height Sig n g xs) as Hxs.
      destruct xs; cbn in Hxs |- *; [reflexivity|exact (f_equal S Hxs)].
    + now rewrite act_tm_height.
    + now rewrite act_fm_height.
    + now rewrite act_tm_height, act_tm_height.
    + reflexivity.
  - destruct p as [n P xs|n L ps|t q|Q i q]; cbn.
    + pose proof (@act_tml_height Sig n g xs) as Hxs.
      destruct xs; cbn in Hxs |- *; [reflexivity|exact (f_equal S Hxs)].
    + pose proof (@act_fml_height Sig n g ps) as Hps.
      destruct ps; cbn in Hps |- *; [reflexivity|exact (f_equal S Hps)].
    + now rewrite act_tm_height, act_fm_height.
    + now rewrite act_fm_height.
  - destruct xs as [|n t xs]; cbn; [reflexivity|].
    pose proof (@act_tm_height Sig g t) as Ht.
    pose proof (@act_tml_height Sig n g xs) as Hxs.
    destruct xs; cbn in Ht, Hxs |- *; [exact Ht|now rewrite Ht, Hxs].
  - destruct ps as [|n p ps]; cbn; [reflexivity|].
    pose proof (@act_fm_height Sig g p) as Hp.
    pose proof (@act_fml_height Sig n g ps) as Hps.
    destruct ps; cbn in Hp, Hps |- *; [exact Hp|now rewrite Hp, Hps].
Defined.

Definition RunEquivariant {Sig H} (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) (R : RunMap Sig H) : Prop :=
  forall e u,
    R (@pair_power (E_dcpo Sig H)
      (transport_map C g Hg e) (transport_map C g Hg u)) =
    transport_map C g Hg (R (@pair_power (E_dcpo Sig H) e u)).

Lemma run_bottom_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g),
    @RunEquivariant Sig H C g Hg (run_bottom Sig H).
Proof.
  intros Sig H C g Hg e u. cbn [run_bottom]. symmetry.
  apply transport_bottom.
Qed.

Lemma nth_run_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) rs,
    Forall (@RunEquivariant Sig H C g Hg) rs ->
    forall k, @RunEquivariant Sig H C g Hg
      (nth k rs (run_bottom Sig H)).
Proof.
  intros Sig H C g Hg rs Hrs. induction Hrs; intro k.
  - destruct k; apply run_bottom_equivariant.
  - destruct k; cbn; [exact H0|apply IHHrs].
Qed.

Lemma power_map_apply : forall D E n (f : SCMap D E)
    (xs : dcar (power_dcpo D n)) i,
    @power_map D E n f xs i = f (xs i).
Proof. reflexivity. Qed.

Lemma power_map_tuple_cons : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) n v
    (vs : dcar (power_dcpo (E_dcpo Sig H) n)),
    @power_map (E_dcpo Sig H) (E_dcpo Sig H) (S n)
      (transport_map C g Hg) (@tuple_cons_value (E_dcpo Sig H) n v vs) =
    @tuple_cons_value (E_dcpo Sig H) n (transport_map C g Hg v)
      (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
        (transport_map C g Hg) vs).
Proof.
  intros. apply functional_extensionality_dep. intro j.
  dependent destruction j.
  - rewrite power_map_apply. unfold tuple_cons_value.
    now rewrite !finite_caseS_zero.
  - rewrite power_map_apply. unfold tuple_cons_value.
    now rewrite !finite_caseS_succ, power_map_apply.
Qed.

Lemma singleton_tuple_sc_apply : forall X D (f : SCMap X D) x,
    @singleton_tuple_sc X D f x = @power_one D (f x).
Proof.
  intros. unfold singleton_tuple_sc. rewrite power_cons_sc_apply.
  apply functional_extensionality_dep. intro j.
  refine (@finite_caseS 0 j
    (fun k => @tuple_cons_value D 0 (f x) (empty_tuple_sc X D x) k =
      @power_one D (f x) k) _ _).
  - unfold tuple_cons_value, power_one. now rewrite finite_caseS_zero.
  - intros impossible. inversion impossible.
Qed.

Lemma power_map_power_one : forall D E (f : SCMap D E) x,
    @power_map D E 1 f (@power_one D x) = @power_one E (f x).
Proof.
  intros. apply functional_extensionality_dep. intro j.
  refine (@finite_caseS 0 j
    (fun k => @power_map D E 1 f (@power_one D x) k =
      @power_one E (f x) k) _ _).
  - rewrite power_map_apply. reflexivity.
  - intros impossible. inversion impossible.
Qed.

(** Small, opaque computation interfaces used below.  Keeping these clauses
    separate prevents the mutual induction proof from embedding the complete
    definitions of Scott composition and of the evaluator in every branch. *)
Lemma sc_comp_apply : forall X Y Z (f : SCMap Y Z) (h : SCMap X Y) x,
    @sc_comp X Y Z f h x = f (h x).
Proof. reflexivity. Qed.

Lemma sc_const_apply : forall X D (d : dcar D) x,
    @sc_const X D d x = d.
Proof. reflexivity. Qed.

Lemma val_quote_tm_apply : forall Sig H (C : SyntaxCoding Sig H) rs u e,
    val_tm_hist H C rs (TQuoteT u) e = quote_tm_raw C u.
Proof. reflexivity. Qed.

Lemma val_quote_fm_apply : forall Sig H (C : SyntaxCoding Sig H) rs p e,
    val_tm_hist H C rs (TQuoteF p) e = quote_fm_raw C p.
Proof. reflexivity. Qed.

Lemma val_rapp_tm_apply : forall Sig H (C : SyntaxCoding Sig H) rs u v e,
    val_tm_hist H C rs (TRApp u v) e =
      (nth (Nat.pred (tm_height (TRApp u v))) rs (run_bottom Sig H))
        (@pair_maps (E_dcpo Sig H) (E_dcpo Sig H)
          (val_tm_hist H C rs u)
          (@sc_const (E_dcpo Sig H) (E_dcpo Sig H) (quote_tm_raw C v)) e).
Proof. reflexivity. Qed.

Lemma val_rapp_fm_apply : forall Sig H (C : SyntaxCoding Sig H) rs t q e,
    val_fm_hist H C rs (FRApp t q) e =
      (nth (Nat.pred (fm_height (FRApp t q))) rs (run_bottom Sig H))
        (@pair_maps (E_dcpo Sig H) (E_dcpo Sig H)
          (val_tm_hist H C rs t)
          (@sc_const (E_dcpo Sig H) (E_dcpo Sig H) (quote_fm_raw C q)) e).
Proof. reflexivity. Qed.

Lemma val_tml_cons_apply : forall Sig H (C : SyntaxCoding Sig H) rs n
    (t : tm Sig) (xs : tml Sig n) e,
    val_tml_hist H C rs (TCons t xs) e =
      @power_cons_sc (E_dcpo Sig H) (E_dcpo Sig H) n
        (val_tm_hist H C rs t) (val_tml_hist H C rs xs) e.
Proof. reflexivity. Qed.

Lemma val_tml_nil_apply : forall Sig H (C : SyntaxCoding Sig H) rs e,
    val_tml_hist H C rs (@TNil Sig) e = empty_power (E_dcpo Sig H).
Proof. reflexivity. Qed.

Lemma val_fml_cons_apply : forall Sig H (C : SyntaxCoding Sig H) rs n
    (p : fm Sig) (ps : fml Sig n) e,
    val_fml_hist H C rs (FCons p ps) e =
      @power_cons_sc (E_dcpo Sig H) (E_dcpo Sig H) n
        (val_fm_hist H C rs p) (val_fml_hist H C rs ps) e.
Proof. reflexivity. Qed.

Lemma val_fml_nil_apply : forall Sig H (C : SyntaxCoding Sig H) rs e,
    val_fml_hist H C rs (@FNil Sig) e = empty_power (E_dcpo Sig H).
Proof. reflexivity. Qed.

Set Warnings "-non-full-mutual".

Scheme tm_equiv_ind := Induction for tm Sort Prop
with fm_equiv_ind := Induction for fm Sort Prop
with tml_equiv_ind := Induction for tml Sort Prop
with fml_equiv_ind := Induction for fml Sort Prop.

Combined Scheme syntax_equiv_mutind
  from tm_equiv_ind, fm_equiv_ind, tml_equiv_ind, fml_equiv_ind.

Theorem val_hist_equivariant_mut {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (rs : list (RunMap Sig H))
    (Hrs : Forall (@RunEquivariant Sig H C g Hg) rs) :
    (forall t : tm Sig,
      wf_tm H t -> forall e,
        val_tm_hist H C rs (act_tm g t) (transport_map C g Hg e) =
        transport_map C g Hg (val_tm_hist H C rs t e)) /\
    (forall p : fm Sig,
      wf_fm H p -> forall e,
        val_fm_hist H C rs (act_fm g p) (transport_map C g Hg e) =
        transport_map C g Hg (val_fm_hist H C rs p e)) /\
    (forall n (xs : tml Sig n),
      wf_tml H xs -> forall e,
        val_tml_hist H C rs (act_tml g xs) (transport_map C g Hg e) =
        @power_map (E_dcpo Sig H) (E_dcpo Sig H) n
          (transport_map C g Hg) (val_tml_hist H C rs xs e)) /\
    (forall n (ps : fml Sig n),
      wf_fml H ps -> forall e,
        val_fml_hist H C rs (act_fml g ps) (transport_map C g Hg e) =
        @power_map (E_dcpo Sig H) (E_dcpo Sig H) n
          (transport_map C g Hg) (val_fml_hist H C rs ps e)).
Proof.
  apply syntax_equiv_mutind.
  - abstract (
      intros i _ e; cbn [act_tm]; rewrite !val_var_clause;
      apply operation_var_transport).
  - abstract (
      intros n f xs IHxs Hxs e; cbn [act_tm] in *;
      rewrite !val_fun_clause;
      rewrite (IHxs Hxs e); apply operation_T_transport).
  - abstract (
      intros u IHu Hu e; cbn [act_tm]; rewrite !val_quote_tm_apply;
      symmetry; now apply quote_tm_raw_equivariant).
  - abstract (
      intros p IHp Hp e; cbn [act_tm]; rewrite !val_quote_fm_apply;
      symmetry; now apply quote_fm_raw_equivariant).
  - abstract (
      intros u IHu v IHv HuHv e;
      destruct HuHv as [Hu Hv]; cbn [act_tm];
      rewrite !val_rapp_tm_apply;
      cbn [tm_height]; rewrite !act_tm_height;
      rewrite !pair_maps_apply, !sc_const_apply;
      rewrite (IHu Hu e);
      rewrite <- (@quote_tm_raw_equivariant Sig H C g Hg v Hv);
      apply (@nth_run_equivariant Sig H C g Hg rs Hrs
        (Nat.pred (S (Nat.max (tm_height u) (tm_height v)))))).
  - abstract (
      intros a Ha e;
      assert (Hpa : Hminus H (pconj g a)) by
        (split;
          [exact (@pconj_mem H g a Hg (proj1 Ha))
          |exact (@pconj_nonid g a (proj2 Ha))]);
      cbn [act_tm];
      rewrite (val_move_clause C rs Hpa), (val_move_clause C rs Ha);
      replace (proj1 Hpa) with
        (@pconj_mem H g a Hg (proj1 Ha)) by apply proof_irrelevance;
      apply transport_conjugate_apply).
  - abstract (
      intros n P xs IHxs Hxs e; cbn [act_fm] in *;
      rewrite !val_pred_clause;
      rewrite (IHxs Hxs e); apply operation_P_transport).
  - abstract (
      intros n L ps IHps Hps e; cbn [act_fm] in *;
      rewrite !val_conn_clause;
      rewrite (IHps Hps e); apply operation_L_transport).
  - abstract (
      intros t IHt q IHq Htq e;
      destruct Htq as [Ht Hq]; cbn [act_fm];
      rewrite !val_rapp_fm_apply;
      cbn [fm_height]; rewrite act_tm_height, act_fm_height;
      rewrite !pair_maps_apply, !sc_const_apply;
      rewrite (IHt Ht e);
      rewrite <- (@quote_fm_raw_equivariant Sig H C g Hg q Hq);
      apply (@nth_run_equivariant Sig H C g Hg rs Hrs
        (Nat.pred (S (Nat.max (tm_height t) (fm_height q)))))).
  - abstract (
      intros Q i q IHq Hq e; cbn [act_fm];
      rewrite !val_quant_clause;
      rewrite !singleton_tuple_sc_apply;
      rewrite !sc_comp_apply;
      rewrite (@enc_unary_abstraction_transport Sig H C g Hg i
        (val_fm_hist H C rs q) (val_fm_hist H C rs (act_fm g q))
        (IHq Hq) e);
      rewrite <- power_map_power_one;
      apply operation_Q_transport).
  - abstract (
      intros _ e; cbn [act_tml]; rewrite !val_tml_nil_apply;
      symmetry; apply empty_power_unique).
  - abstract (
      intros n t IHt xs IHxs Htxs e;
      destruct Htxs as [Ht Hxs]; cbn [act_tml];
      rewrite !val_tml_cons_apply;
      rewrite !power_cons_sc_apply;
      rewrite (IHt Ht e), (IHxs Hxs e);
      symmetry; apply power_map_tuple_cons).
  - abstract (
      intros _ e; cbn [act_fml]; rewrite !val_fml_nil_apply;
      symmetry; apply empty_power_unique).
  - abstract (
      intros n p IHp ps IHps Hpps e;
      destruct Hpps as [Hp Hps]; cbn [act_fml];
      rewrite !val_fml_cons_apply;
      rewrite !power_cons_sc_apply;
      rewrite (IHp Hp e), (IHps Hps e);
      symmetry; apply power_map_tuple_cons).
Qed.

Theorem val_tm_hist_equivariant {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (rs : list (RunMap Sig H))
    (Hrs : Forall (@RunEquivariant Sig H C g Hg) rs)
    (t : tm Sig) (Ht : wf_tm H t) : forall e,
    val_tm_hist H C rs (act_tm g t) (transport_map C g Hg e) =
    transport_map C g Hg (val_tm_hist H C rs t e).
Proof.
  exact (proj1 (@val_hist_equivariant_mut Sig H C g Hg rs Hrs) t Ht).
Qed.

Theorem val_fm_hist_equivariant {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (rs : list (RunMap Sig H))
    (Hrs : Forall (@RunEquivariant Sig H C g Hg) rs)
    (p : fm Sig) (Hp : wf_fm H p) : forall e,
    val_fm_hist H C rs (act_fm g p) (transport_map C g Hg e) =
    transport_map C g Hg (val_fm_hist H C rs p e).
Proof.
  exact (proj1 (proj2
    (@val_hist_equivariant_mut Sig H C g Hg rs Hrs)) p Hp).
Qed.

Theorem val_tml_hist_equivariant {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (rs : list (RunMap Sig H))
    (Hrs : Forall (@RunEquivariant Sig H C g Hg) rs)
    {n} (xs : tml Sig n) (Hxs : wf_tml H xs) : forall e,
    val_tml_hist H C rs (act_tml g xs) (transport_map C g Hg e) =
    @power_map (E_dcpo Sig H) (E_dcpo Sig H) n
      (transport_map C g Hg) (val_tml_hist H C rs xs e).
Proof.
  exact (proj1 (proj2 (proj2
    (@val_hist_equivariant_mut Sig H C g Hg rs Hrs))) n xs Hxs).
Qed.

Theorem val_fml_hist_equivariant {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (rs : list (RunMap Sig H))
    (Hrs : Forall (@RunEquivariant Sig H C g Hg) rs)
    {n} (ps : fml Sig n) (Hps : wf_fml H ps) : forall e,
    val_fml_hist H C rs (act_fml g ps) (transport_map C g Hg e) =
    @power_map (E_dcpo Sig H) (E_dcpo Sig H) n
      (transport_map C g Hg) (val_fml_hist H C rs ps e).
Proof.
  exact (proj2 (proj2 (proj2
    (@val_hist_equivariant_mut Sig H C g Hg rs Hrs))) n ps Hps).
Qed.

Set Warnings "+non-full-mutual".

Lemma act_expr_height : forall Sig g (z : expr Sig),
    expr_height (act_expr g z) = expr_height z.
Proof.
  intros Sig g [t|p]; cbn [act_expr expr_height].
  - apply act_tm_height.
  - apply act_fm_height.
Qed.

Lemma syntax_act_height : forall Sig H g (Hg : hmem H g)
    (z : SyntaxCarrier Sig H),
    expr_height (proj1_sig (syntax_act g Hg z)) =
    expr_height (proj1_sig z).
Proof.
  intros Sig H g Hg [z Hz]. cbn [syntax_act]. apply act_expr_height.
Qed.

Theorem val_expr_hist_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (rs : list (RunMap Sig H)),
    Forall (@RunEquivariant Sig H C g Hg) rs ->
    forall z, wf_expr H z -> forall e,
      val_expr_hist C rs (act_expr g z) (transport_map C g Hg e) =
      transport_map C g Hg (val_expr_hist C rs z e).
Proof.
  intros Sig H C g Hg rs Hrs [t|p] Hz e; cbn [act_expr val_expr_hist].
  - exact (@val_tm_hist_equivariant Sig H C g Hg rs Hrs t Hz e).
  - exact (@val_fm_hist_equivariant Sig H C g Hg rs Hrs p Hz e).
Qed.

Lemma code_nat_action_preserves_nonreserved : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) n,
    nonreserved n -> nonreserved (code_nat_action C g Hg n).
Proof.
  intros Sig H C g Hg n [H0 H1].
  rewrite (code_nat_action_nonreserved C g Hg n H0 H1).
  exact (proj2_sig (syntax_encode C
    (syntax_act g Hg (syntax_decode C (exist _ n (conj H0 H1)))))).
Qed.

Lemma syntax_decode_code_nat_action : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) n
    (Hn : nonreserved n)
    (Hgn : nonreserved (code_nat_action C g Hg n)),
    syntax_decode C (exist _ (code_nat_action C g Hg n) Hgn) =
    syntax_act g Hg (syntax_decode C (exist _ n Hn)).
Proof.
  intros Sig H C g Hg n [H0 H1] Hgn.
  set (z := syntax_act g Hg
    (syntax_decode C (exist _ n (conj H0 H1)))).
  assert (Hcode :
      exist nonreserved (code_nat_action C g Hg n) Hgn =
      syntax_encode C z).
  { apply sig_prop_ext. cbn. unfold z.
    apply code_nat_action_nonreserved. }
  rewrite Hcode. apply syntax_decode_encode.
Qed.

Lemma first2_pair_power : forall D (x y : dcar D),
    first2 D (@pair_power D x y) = x.
Proof. reflexivity. Qed.

Lemma second2_pair_power : forall D (x y : dcar D),
    second2 D (@pair_power D x y) = y.
Proof. reflexivity. Qed.

Lemma runner_tag_pair_power : forall Sig H (e u : E_car Sig H),
    runner_tag Sig H (@pair_power (E_dcpo Sig H) e u) =
    pi_map Sig H 0 u.
Proof. reflexivity. Qed.

Lemma B0_map_none : forall Sig H (C : SyntaxCoding Sig H) g Hg,
    B0_map C g Hg None = None.
Proof. reflexivity. Qed.

Lemma B0_map_some : forall Sig H (C : SyntaxCoding Sig H) g Hg n,
    B0_map C g Hg (Some n) = Some (code_nat_action C g Hg n).
Proof. reflexivity. Qed.

Lemma runner_tag_transport_pair : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) e u,
    runner_tag Sig H
      (@pair_power (E_dcpo Sig H)
        (transport_map C g Hg e) (transport_map C g Hg u)) =
    B0_map C g Hg
      (runner_tag Sig H (@pair_power (E_dcpo Sig H) e u)).
Proof.
  intros. rewrite !runner_tag_pair_power, transport_pi. reflexivity.
Qed.

Theorem runner_branch_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (rs : list (RunMap Sig H)),
    Forall (@RunEquivariant Sig H C g Hg) rs ->
    forall stage code e u,
      runner_branch C rs stage (code_nat_action C g Hg code)
        (@pair_power (E_dcpo Sig H)
          (transport_map C g Hg e) (transport_map C g Hg u)) =
      transport_map C g Hg
        (runner_branch C rs stage code
          (@pair_power (E_dcpo Sig H) e u)).
Proof.
  intros Sig H C g Hg rs Hrs stage code e u.
  destruct (Nat.eq_dec code 0) as [H0|H0].
  - subst code. rewrite code_nat_action_zero.
    unfold runner_branch.
    destruct (Nat.eq_dec 0 0); [|contradiction].
    cbn [run_bottom]. symmetry. apply transport_bottom.
  - destruct (Nat.eq_dec code 1) as [H1|H1].
    + subst code. rewrite code_nat_action_one.
      unfold runner_branch.
      destruct (Nat.eq_dec 1 0) as [H10|H10]; [discriminate|].
      destruct (Nat.eq_dec 1 1); [|contradiction].
      cbn [run_bottom]. symmetry. apply transport_bottom.
    + pose proof (@code_nat_action_preserves_nonreserved Sig H C g Hg code
        (conj H0 H1)) as Hgn.
      destruct Hgn as [Hg0 Hg1].
      unfold runner_branch.
      destruct (Nat.eq_dec (code_nat_action C g Hg code) 0)
        as [Hbad0|Hgood0]; [contradiction|].
      destruct (Nat.eq_dec (code_nat_action C g Hg code) 1)
        as [Hbad1|Hgood1]; [contradiction|].
      destruct (Nat.eq_dec code 0) as [Hbad0|Hgood0']; [contradiction|].
      destruct (Nat.eq_dec code 1) as [Hbad1|Hgood1']; [contradiction|].
      set (z := syntax_decode C
        (exist nonreserved code (conj Hgood0' Hgood1'))) in *.
      assert (Hzg : forall Hact :
          nonreserved (code_nat_action C g Hg code),
        syntax_decode C
          (exist nonreserved (code_nat_action C g Hg code)
            Hact) =
        syntax_act g Hg z).
      { intro Hact. unfold z. apply syntax_decode_code_nat_action. }
      rewrite (Hzg _).
      assert (Hz : forall Horig : nonreserved code,
        syntax_decode C (exist nonreserved code Horig) = z).
      { intro Horig. unfold z. apply (f_equal (syntax_decode C)).
        apply sig_prop_ext. reflexivity. }
      repeat rewrite (Hz _).
      destruct (le_dec
        (expr_height (proj1_sig (syntax_act g Hg z))) stage)
        as [Hleg|Hnleg];
      destruct (le_dec (expr_height (proj1_sig z)) stage)
        as [Hle|Hnle].
      * rewrite !sc_comp_apply, !first2_pair_power.
        apply (@val_expr_hist_equivariant Sig H C g Hg rs Hrs
          (proj1_sig z) (proj2_sig z) e).
      * exfalso. apply Hnle.
        rewrite <- (@syntax_act_height Sig H g Hg z). exact Hleg.
      * exfalso. apply Hnleg.
        rewrite (@syntax_act_height Sig H g Hg z). exact Hle.
      * cbn [run_bottom]. symmetry. apply transport_bottom.
Qed.

Theorem make_run_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (rs : list (RunMap Sig H)),
    Forall (@RunEquivariant Sig H C g Hg) rs ->
    forall stage,
      @RunEquivariant Sig H C g Hg (make_run C rs stage).
Proof.
  intros Sig H C g Hg rs Hrs stage e u.
  unfold make_run, flat_dispatch.
  change
    ((match runner_tag Sig H
        (@pair_power (E_dcpo Sig H)
          (transport_map C g Hg e) (transport_map C g Hg u)) with
      | None => dbot (E_dcpo Sig H)
      | Some code => runner_branch C rs stage code
          (@pair_power (E_dcpo Sig H)
            (transport_map C g Hg e) (transport_map C g Hg u))
      end) =
     transport_map C g Hg
       (match runner_tag Sig H (@pair_power (E_dcpo Sig H) e u) with
        | None => dbot (E_dcpo Sig H)
        | Some code => runner_branch C rs stage code
            (@pair_power (E_dcpo Sig H) e u)
        end)).
  rewrite runner_tag_transport_pair, runner_tag_pair_power.
  destruct (pi_map Sig H 0 u) as [code|] eqn:Htag.
  - rewrite B0_map_some.
    apply (@runner_branch_equivariant Sig H C g Hg rs Hrs
      stage code e u).
  - rewrite B0_map_none. symmetry. apply transport_bottom.
Qed.

Theorem run_history_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) n,
    Forall (@RunEquivariant Sig H C g Hg) (run_history C n).
Proof.
  intros Sig H C g Hg n. induction n as [|n IH].
  - constructor.
  - rewrite run_history_succ. apply Forall_app. split.
    + exact IH.
    + constructor.
      * apply (@make_run_equivariant Sig H C g Hg
          (run_history C n) IH n).
      * constructor.
Qed.

Theorem Run_n_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) n,
    @RunEquivariant Sig H C g Hg (Run_n C n).
Proof.
  intros Sig H C g Hg n. unfold Run_n.
  apply (@nth_run_equivariant Sig H C g Hg
    (run_history C (S n))
    (@run_history_equivariant Sig H C g Hg (S n)) n).
Qed.

Theorem Val_map_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) z,
    wf_expr H z -> forall e,
      Val_map C (act_expr g z) (transport_map C g Hg e) =
      transport_map C g Hg (Val_map C z e).
Proof.
  intros Sig H C g Hg z Hz e. unfold Val_map.
  rewrite act_expr_height.
  apply (@val_expr_hist_equivariant Sig H C g Hg
    (run_history C (expr_height z))
    (@run_history_equivariant Sig H C g Hg (expr_height z)) z Hz e).
Qed.

Theorem Val_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g)
    (z : SyntaxCarrier Sig H) e,
    Val C (transport_map C g Hg e) (syntax_act g Hg z) =
    transport_map C g Hg (Val C e z).
Proof.
  intros Sig H C g Hg [z Hz] e. unfold Val. cbn [syntax_act].
  apply (@Val_map_equivariant Sig H C g Hg z Hz e).
Qed.

Theorem total_runner_branch_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) code e u,
    total_runner_branch C (code_nat_action C g Hg code)
      (@pair_power (E_dcpo Sig H)
        (transport_map C g Hg e) (transport_map C g Hg u)) =
    transport_map C g Hg
      (total_runner_branch C code (@pair_power (E_dcpo Sig H) e u)).
Proof.
  intros Sig H C g Hg code e u.
  destruct (Nat.eq_dec code 0) as [H0|H0].
  - subst code. rewrite code_nat_action_zero.
    unfold total_runner_branch.
    destruct (Nat.eq_dec 0 0); [|contradiction].
    cbn [run_bottom]. symmetry. apply transport_bottom.
  - destruct (Nat.eq_dec code 1) as [H1|H1].
    + subst code. rewrite code_nat_action_one.
      unfold total_runner_branch.
      destruct (Nat.eq_dec 1 0) as [H10|H10]; [discriminate|].
      destruct (Nat.eq_dec 1 1); [|contradiction].
      cbn [run_bottom]. symmetry. apply transport_bottom.
    + pose proof (@code_nat_action_preserves_nonreserved Sig H C g Hg code
        (conj H0 H1)) as Hgn.
      destruct Hgn as [Hg0 Hg1].
      unfold total_runner_branch.
      destruct (Nat.eq_dec (code_nat_action C g Hg code) 0)
        as [Hbad0|Hgood0]; [contradiction|].
      destruct (Nat.eq_dec (code_nat_action C g Hg code) 1)
        as [Hbad1|Hgood1]; [contradiction|].
      destruct (Nat.eq_dec code 0) as [Hbad0|Hgood0']; [contradiction|].
      destruct (Nat.eq_dec code 1) as [Hbad1|Hgood1']; [contradiction|].
      set (z := syntax_decode C
        (exist nonreserved code (conj Hgood0' Hgood1'))) in *.
      assert (Hzg : forall Hact :
          nonreserved (code_nat_action C g Hg code),
        syntax_decode C
          (exist nonreserved (code_nat_action C g Hg code) Hact) =
        syntax_act g Hg z).
      { intro Hact. unfold z. apply syntax_decode_code_nat_action. }
      rewrite (Hzg _).
      assert (Hz : forall Horig : nonreserved code,
        syntax_decode C (exist nonreserved code Horig) = z).
      { intro Horig. unfold z. apply (f_equal (syntax_decode C)).
        apply sig_prop_ext. reflexivity. }
      repeat rewrite (Hz _).
      rewrite !sc_comp_apply, !first2_pair_power.
      apply (@Val_map_equivariant Sig H C g Hg
        (proj1_sig z) (proj2_sig z) e).
Qed.

Theorem Run_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g),
    @RunEquivariant Sig H C g Hg (Run C).
Proof.
  intros Sig H C g Hg e u. unfold Run, flat_dispatch.
  change
    ((match runner_tag Sig H
        (@pair_power (E_dcpo Sig H)
          (transport_map C g Hg e) (transport_map C g Hg u)) with
      | None => dbot (E_dcpo Sig H)
      | Some code => total_runner_branch C code
          (@pair_power (E_dcpo Sig H)
            (transport_map C g Hg e) (transport_map C g Hg u))
      end) =
     transport_map C g Hg
       (match runner_tag Sig H (@pair_power (E_dcpo Sig H) e u) with
        | None => dbot (E_dcpo Sig H)
        | Some code => total_runner_branch C code
            (@pair_power (E_dcpo Sig H) e u)
        end)).
  rewrite runner_tag_transport_pair, runner_tag_pair_power.
  destruct (pi_map Sig H 0 u) as [code|] eqn:Htag.
  - rewrite B0_map_some.
    apply (@total_runner_branch_equivariant Sig H C g Hg code e u).
  - rewrite B0_map_none. symmetry. apply transport_bottom.
Qed.

Lemma assert_operation_apply : forall Sig H (e v : E_car Sig H),
    assert_operation e v =
    @operation_family_map Sig H ai_assert e (@power_one (E_dcpo Sig H) v).
Proof.
  intros. unfold assert_operation, operation_family_map.
  rewrite !sc_comp_apply, singleton_tuple_sc_apply. reflexivity.
Qed.

Theorem assert_operation_transport : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) e v,
    assert_operation (transport_map C g Hg e)
      (transport_map C g Hg v) =
    transport_map C g Hg (assert_operation e v).
Proof.
  intros. rewrite !assert_operation_apply.
  rewrite <- (@power_map_power_one (E_dcpo Sig H) (E_dcpo Sig H)
    (transport_map C g Hg) v).
  apply operation_assert_transport.
Qed.

Theorem TruthOpen_transport : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) u,
    TruthOpen (transport_map C g Hg u) <-> TruthOpen u.
Proof.
  intros Sig H C g Hg u. unfold TruthOpen.
  rewrite transport_pi.
  change
    (B0_map C g Hg (pi_map Sig H 0 u) = Some 1 <->
     pi_map Sig H 0 u = Some 1).
  destruct (pi_map Sig H 0 u) as [n|] eqn:Hpi.
  - rewrite B0_map_some.
    destruct (Nat.eq_dec n 0) as [H0|H0].
    + subst n. rewrite code_nat_action_zero.
      split; intro Hx; discriminate.
    + destruct (Nat.eq_dec n 1) as [H1|H1].
      * subst n. rewrite code_nat_action_one.
        split; intro; reflexivity.
      * pose proof (@code_nat_action_preserves_nonreserved Sig H C g Hg n
          (conj H0 H1)) as [_ Hgn1].
        split; intro Hx.
        -- exfalso. apply Hgn1. now injection Hx.
        -- exfalso. apply H1. now injection Hx.
  - rewrite B0_map_none. split; intro Hx; discriminate.
Qed.

Theorem TruthRegion_transport : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) e v,
    TruthRegion (transport_map C g Hg e) (transport_map C g Hg v) <->
    TruthRegion e v.
Proof.
  intros. unfold TruthRegion.
  rewrite assert_operation_transport.
  apply TruthOpen_transport.
Qed.

Definition formula_act {Sig H} g (Hg : hmem H g)
    (p : { q : fm Sig | wf_fm H q }) : { q : fm Sig | wf_fm H q } :=
  exist _ (act_fm g (proj1_sig p))
    (@wf_act_fm H Sig g Hg (proj1_sig p) (proj2_sig p)).

Theorem Satisfies_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) e
    (p : { q : fm Sig | wf_fm H q }),
    Satisfies C (transport_map C g Hg e) (@formula_act Sig H g Hg p) <->
    Satisfies C e p.
Proof.
  intros Sig H C g Hg e [p Hp]. unfold Satisfies, formula_act.
  cbv beta iota zeta.
  lazymatch goal with
  | |- TruthRegion _ (Val _ _ ?za) <-> _ =>
      replace za with
        (syntax_act g Hg (exist (wf_expr H) (EForm p) Hp)) by
        (apply sig_prop_ext; reflexivity)
  end.
  rewrite Val_equivariant.
  apply TruthRegion_transport.
Qed.
