(**
  Sections 9--11 of HRISS v3.2: continuous evaluation, runner,
  finite evaluation certificates, and relative satisfaction.

  This module imports the checked domain/syntax core.  No semantic clause is
  postulated: every evaluator below is assembled from Scott-continuous maps.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lists.List Lia Logic.ProofIrrelevance
  Logic.ClassicalDescription.
Require Import HRISS_v3_2.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Definition RunMap (Sig : Signature) (H : Subgroup) : Type :=
  SCMap (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H).

Definition run_bottom (Sig : Signature) (H : Subgroup) : RunMap Sig H :=
  @sc_const (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H)
    (dbot (E_dcpo Sig H)).

Definition quote_tm_raw {Sig H} (C : SyntaxCoding Sig H) (t : tm Sig) :
    E_car Sig H :=
  match excluded_middle_informative (wf_tm H t) with
  | left Ht => quote_value C (exist _ (ETerm t) Ht)
  | right _ => dbot (E_dcpo Sig H)
  end.

Definition quote_fm_raw {Sig H} (C : SyntaxCoding Sig H) (p : fm Sig) :
    E_car Sig H :=
  match excluded_middle_informative (wf_fm H p) with
  | left Hp => quote_value C (exist _ (EForm p) Hp)
  | right _ => dbot (E_dcpo Sig H)
  end.

Definition pair_maps (X D : PDCPO) (f g : SCMap X D) :
    SCMap X (power_dcpo D 2) :=
  @power_cons_sc X D 1 f (@singleton_tuple_sc X D g).

(** The source writes [E^1] and [E] interchangeably.  This is the explicit
    Scott-continuous precomposition along the unique projection [E^1 -> E]. *)
Definition unary_power_lift (D : PDCPO) :
    SCMap (@scmap_dcpo D D) (@scmap_dcpo (power_dcpo D 1) D) :=
  @prepost_map (power_dcpo D 1) D D D
    (power_projection_sc D 1 (fzero 0)) (sc_id D).

Definition enc_unary_family (Sig : Signature) (H : Subgroup) :
    SCMap (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H)) (E_dcpo Sig H) :=
  @sc_comp (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H))
    (@scmap_dcpo (power_dcpo (E_dcpo Sig H) 1) (E_dcpo Sig H))
    (E_dcpo Sig H) (enc_map Sig H 1) (unary_power_lift (E_dcpo Sig H)).

Fixpoint val_tm_hist {Sig} (H : Subgroup) (C : SyntaxCoding Sig H)
    (rs : list (RunMap Sig H)) (t : tm Sig) {struct t} :
    SCMap (E_dcpo Sig H) (E_dcpo Sig H) :=
  match t with
  | TVar i =>
      @semantic_node Sig H (ai_var i)
        (@empty_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H))
  | @TFun _ n f xs =>
      @semantic_node Sig H (ai_T f) (@val_tml_hist Sig H C rs n xs)
  | TQuoteT u =>
      @sc_const (E_dcpo Sig H) (E_dcpo Sig H) (quote_tm_raw C u)
  | TQuoteF p =>
      @sc_const (E_dcpo Sig H) (E_dcpo Sig H) (quote_fm_raw C p)
  | TRApp u v =>
      @sc_comp (E_dcpo Sig H) (power_dcpo (E_dcpo Sig H) 2)
        (E_dcpo Sig H)
        (nth (Nat.pred (tm_height (TRApp u v))) rs (run_bottom Sig H))
        (@pair_maps (E_dcpo Sig H) (E_dcpo Sig H)
          (@val_tm_hist Sig H C rs u)
          (@sc_const (E_dcpo Sig H) (E_dcpo Sig H) (quote_tm_raw C v)))
  | TMove g =>
      match excluded_middle_informative (Hminus H g) with
      | left Hg => transport_map C g (proj1 Hg)
      | right _ => @sc_const (E_dcpo Sig H) (E_dcpo Sig H)
          (dbot (E_dcpo Sig H))
      end
  end
with val_fm_hist {Sig} (H : Subgroup) (C : SyntaxCoding Sig H)
    (rs : list (RunMap Sig H)) (p : fm Sig) {struct p} :
    SCMap (E_dcpo Sig H) (E_dcpo Sig H) :=
  match p with
  | @FPred _ n P xs =>
      @semantic_node Sig H (ai_P P) (@val_tml_hist Sig H C rs n xs)
  | @FConn _ n L ps =>
      @semantic_node Sig H (ai_L L) (@val_fml_hist Sig H C rs n ps)
  | FRApp t q =>
      @sc_comp (E_dcpo Sig H) (power_dcpo (E_dcpo Sig H) 2)
        (E_dcpo Sig H)
        (nth (Nat.pred (fm_height (FRApp t q))) rs (run_bottom Sig H))
        (@pair_maps (E_dcpo Sig H) (E_dcpo Sig H)
          (@val_tm_hist Sig H C rs t)
          (@sc_const (E_dcpo Sig H) (E_dcpo Sig H) (quote_fm_raw C q)))
  | FQuant Q i q =>
      @semantic_node Sig H (ai_Q Q)
        (@singleton_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H)
          (@sc_comp (E_dcpo Sig H)
            (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H))
            (E_dcpo Sig H) (@enc_unary_family Sig H)
            (@abstraction_map Sig H i (@val_fm_hist Sig H C rs q))))
  end
with val_tml_hist {Sig} (H : Subgroup) (C : SyntaxCoding Sig H)
    (rs : list (RunMap Sig H)) {n} (xs : tml Sig n) {struct xs} :
    SCMap (E_dcpo Sig H) (power_dcpo (E_dcpo Sig H) n) :=
  match xs with
  | TNil => @empty_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H)
  | @TCons _ n x xs' =>
      @power_cons_sc (E_dcpo Sig H) (E_dcpo Sig H) n
        (@val_tm_hist Sig H C rs x) (@val_tml_hist Sig H C rs n xs')
  end
with val_fml_hist {Sig} (H : Subgroup) (C : SyntaxCoding Sig H)
    (rs : list (RunMap Sig H)) {n} (ps : fml Sig n) {struct ps} :
    SCMap (E_dcpo Sig H) (power_dcpo (E_dcpo Sig H) n) :=
  match ps with
  | FNil => @empty_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H)
  | @FCons _ n p ps' =>
      @power_cons_sc (E_dcpo Sig H) (E_dcpo Sig H) n
        (@val_fm_hist Sig H C rs p) (@val_fml_hist Sig H C rs n ps')
  end.

Arguments val_tm_hist {Sig} H C rs t.
Arguments val_fm_hist {Sig} H C rs p.
Arguments val_tml_hist {Sig} H C rs {n} xs.
Arguments val_fml_hist {Sig} H C rs {n} ps.

Definition val_expr_hist {Sig H} (C : SyntaxCoding Sig H)
    (rs : list (RunMap Sig H)) (z : expr Sig) :
    SCMap (E_dcpo Sig H) (E_dcpo Sig H) :=
  match z with
  | ETerm t => val_tm_hist H C rs t
  | EForm p => val_fm_hist H C rs p
  end.

(** Direct computation facts for the continuous evaluator skeleton. *)
Lemma quote_tm_raw_wf : forall Sig H (C : SyntaxCoding Sig H) t,
    wf_tm H t -> exists Ht,
      quote_tm_raw C t = quote_value C (exist _ (ETerm t) Ht).
Proof.
  intros Sig H C t Hwf. unfold quote_tm_raw.
  destruct excluded_middle_informative as [Ht|Hn]; [eauto|contradiction].
Qed.

Lemma quote_fm_raw_wf : forall Sig H (C : SyntaxCoding Sig H) p,
    wf_fm H p -> exists Hp,
      quote_fm_raw C p = quote_value C (exist _ (EForm p) Hp).
Proof.
  intros Sig H C p Hwf. unfold quote_fm_raw.
  destruct excluded_middle_informative as [Hp|Hn]; [eauto|contradiction].
Qed.

Lemma val_move_clause : forall Sig H (C : SyntaxCoding Sig H) rs g
    (Hg : Hminus H g),
    val_tm_hist H C rs (TMove g) = transport_map C g (proj1 Hg).
Proof.
  intros. cbn [val_tm_hist].
  destruct excluded_middle_informative as [Hg'|Hn]; [|contradiction].
  f_equal. apply proof_irrelevance.
Qed.

Lemma val_var_clause : forall Sig H (C : SyntaxCoding Sig H) rs i e,
    val_tm_hist H C rs (TVar i) e =
      @operation_family_map Sig H (ai_var i) e (empty_power (E_dcpo Sig H)).
Proof. reflexivity. Qed.

Lemma val_fun_clause : forall Sig H (C : SyntaxCoding Sig H) rs n
    (f : TSym Sig n) xs e,
    val_tm_hist H C rs (TFun f xs) e =
      @operation_family_map Sig H (ai_T f) e (val_tml_hist H C rs xs e).
Proof. reflexivity. Qed.

Lemma val_pred_clause : forall Sig H (C : SyntaxCoding Sig H) rs n
    (P : PSym Sig n) xs e,
    val_fm_hist H C rs (FPred P xs) e =
      @operation_family_map Sig H (ai_P P) e (val_tml_hist H C rs xs e).
Proof. reflexivity. Qed.

Lemma val_conn_clause : forall Sig H (C : SyntaxCoding Sig H) rs n
    (L : LSym Sig n) ps e,
    val_fm_hist H C rs (FConn L ps) e =
      @operation_family_map Sig H (ai_L L) e (val_fml_hist H C rs ps e).
Proof. reflexivity. Qed.

Lemma val_quant_clause : forall Sig H (C : SyntaxCoding Sig H) rs Q i p e,
    val_fm_hist H C rs (FQuant Q i p) e =
      @operation_family_map Sig H (ai_Q Q) e
        (@singleton_tuple_sc (E_dcpo Sig H) (E_dcpo Sig H)
          (@sc_comp (E_dcpo Sig H)
            (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H))
            (E_dcpo Sig H) (@enc_unary_family Sig H)
            (@abstraction_map Sig H i (val_fm_hist H C rs p))) e).
Proof. reflexivity. Qed.

Print Assumptions val_move_clause.
Print Assumptions val_quant_clause.

(** ** Flat-label dispatch

    This is the continuity argument used by every finite runner stage.  A
    non-bottom flat tag is compact/attained; directedness then makes the
    corresponding branch cofinal. *)
Definition flat_dispatch (X E : PDCPO)
    (tag : SCMap X flat_nat_dcpo) (branch : nat -> SCMap X E) : SCMap X E.
Proof.
  refine (@Build_SCMap X E
    (fun x => match tag x with
      | None => dbot E
      | Some n => branch n x
      end) _ _).
  - intros x y Hxy.
    pose proof (@sc_monotone X flat_nat_dcpo tag x y Hxy) as Htag.
    destruct (tag x) as [n|] eqn:Hx;
      destruct (tag y) as [m|] eqn:Hy; cbn in Htag |- *.
    + subst m. now apply sc_monotone.
    + contradiction.
    + apply dbot_least.
    + apply dle_refl.
  - intros A HA.
    pose proof (@sc_pres_lub X flat_nat_dcpo tag A HA) as Htag_lub.
    pose proof (image_directed (sc_monotone tag) HA) as Htag_dir.
    set (s := dsup X A HA).
    assert (Htag_sup : tag s =
        dsup flat_nat_dcpo (image_pred tag A) Htag_dir).
    { apply (@lub_unique flat_nat_dcpo (image_pred tag A)).
      - exact Htag_lub.
      - apply dsup_lub. }
    destruct (tag s) as [n|] eqn:Hs.
    + assert (Hatt : image_pred tag A (Some n)).
      { apply (@flat_lub_some_attained (image_pred tag A) Htag_dir n).
        now rewrite <- Htag_sup. }
      destruct Hatt as (x0 & Hx0 & Htag0).
      split.
      * intros y (x & Hx & ->).
        pose proof (proj1 (dsup_lub X A HA) x Hx) as Hxs.
        pose proof (@sc_monotone X flat_nat_dcpo tag x s Hxs) as Hle.
        destruct (tag x) as [m|] eqn:Htx; cbn in |- *.
        -- rewrite Hs in Hle. unfold flat_nat_dcpo in Hle.
           assert (Hmn : m = n).
           { eapply (@flat_common_some m n (Some n));
               [exact Hle|apply flat_le_refl]. }
           subst m.
           apply sc_monotone. exact Hxs.
        -- apply dbot_least.
      * intros v Hv.
        apply (proj2 (@sc_pres_lub X E (branch n) A HA)).
        intros y (x & Hx & ->).
        pose proof (proj2 HA) as Hdir.
        destruct (Hdir x x0 Hx Hx0) as (z & Hz & Hxz & Hx0z).
        assert (Htz : tag z = Some n).
        { pose proof (@sc_monotone X flat_nat_dcpo tag x0 z Hx0z) as Hle.
          destruct (tag z) as [k|] eqn:Hz'.
          - rewrite <- Htag0 in Hle. unfold flat_nat_dcpo in Hle.
            assert (Hnk : n = k).
            { eapply (@flat_common_some n k (Some k));
                [exact Hle|apply flat_le_refl]. }
            now subst k.
          - rewrite <- Htag0 in Hle. unfold flat_nat_dcpo in Hle.
            cbn in Hle. contradiction. }
        eapply dle_trans.
        -- apply sc_monotone. exact Hxz.
        -- apply Hv. exists z. split; [exact Hz|].
           cbn. now rewrite Htz.
    + split.
      * intros y (x & Hx & ->).
        pose proof (proj1 (dsup_lub X A HA) x Hx) as Hxs.
        pose proof (@sc_monotone X flat_nat_dcpo tag x s Hxs) as Hle.
        destruct (tag x) as [m|] eqn:Htx; cbn in |- *.
        -- rewrite Hs in Hle. unfold flat_nat_dcpo in Hle.
           cbn in Hle. contradiction.
        -- apply dle_refl.
      * intros v _. apply dbot_least.
Defined.

Arguments flat_dispatch X E tag branch : clear implicits.

Print Assumptions flat_dispatch.

(** ** Height-stratified runners *)

Definition runner_tag (Sig : Signature) (H : Subgroup) :
    SCMap (power_dcpo (E_dcpo Sig H) 2) flat_nat_dcpo :=
  @sc_comp (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H)
    flat_nat_dcpo (pi_map Sig H 0) (second2 (E_dcpo Sig H)).

Definition runner_branch {Sig H} (C : SyntaxCoding Sig H)
    (rs : list (RunMap Sig H)) (stage code : nat) : RunMap Sig H.
Proof.
  destruct (Nat.eq_dec code 0) as [H0|H0].
  - exact (run_bottom Sig H).
  - destruct (Nat.eq_dec code 1) as [H1|H1].
    + exact (run_bottom Sig H).
    + pose (z := syntax_decode C (exist _ code (conj H0 H1))).
      destruct (le_dec (expr_height (proj1_sig z)) stage) as [Hz|Hz].
      * exact (@sc_comp (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H)
          (E_dcpo Sig H) (val_expr_hist C rs (proj1_sig z))
          (first2 (E_dcpo Sig H))).
      * exact (run_bottom Sig H).
Defined.

Definition make_run {Sig H} (C : SyntaxCoding Sig H)
    (rs : list (RunMap Sig H)) (stage : nat) : RunMap Sig H :=
  @flat_dispatch (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H)
    (runner_tag Sig H) (runner_branch C rs stage).

Fixpoint run_history {Sig H} (C : SyntaxCoding Sig H) (count : nat) :
    list (RunMap Sig H) :=
  match count with
  | 0 => []
  | S k =>
      let prev := run_history C k in
      prev ++ [make_run C prev k]
  end.

Definition Run_minus1 {Sig H} : RunMap Sig H := run_bottom Sig H.

Definition Run_n {Sig H} (C : SyntaxCoding Sig H) (n : nat) : RunMap Sig H :=
  nth n (run_history C (S n)) (run_bottom Sig H).

Lemma run_history_length : forall Sig H (C : SyntaxCoding Sig H) n,
    length (run_history C n) = n.
Proof.
  intros Sig H C n. induction n as [|n IH]; cbn; [reflexivity|].
  rewrite length_app, IH. cbn. lia.
Qed.

Lemma run_history_succ : forall Sig H (C : SyntaxCoding Sig H) n,
    run_history C (S n) =
      run_history C n ++ [make_run C (run_history C n) n].
Proof. reflexivity. Qed.

Lemma Run_n_unfold : forall Sig H (C : SyntaxCoding Sig H) n,
    Run_n C n = make_run C (run_history C n) n.
Proof.
  intros Sig H C n. unfold Run_n. rewrite run_history_succ.
  rewrite app_nth2.
  - rewrite run_history_length. replace (n - n) with 0 by lia. reflexivity.
  - rewrite run_history_length. lia.
Qed.

Definition Val_map {Sig H} (C : SyntaxCoding Sig H) (z : expr Sig) :
    SCMap (E_dcpo Sig H) (E_dcpo Sig H) :=
  val_expr_hist C (run_history C (expr_height z)) z.

Definition Val {Sig H} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) (z : SyntaxCarrier Sig H) : E_car Sig H :=
  Val_map C (proj1_sig z) e.

Lemma make_run_quote : forall Sig H (C : SyntaxCoding Sig H) rs stage
    (z : SyntaxCarrier Sig H) (e : E_car Sig H),
    expr_height (proj1_sig z) <= stage ->
    make_run C rs stage
      (@pair_power (E_dcpo Sig H) e (quote_value C z)) =
    val_expr_hist C rs (proj1_sig z) e.
Proof.
  intros Sig H C rs stage z e Hz.
  unfold make_run, flat_dispatch.
  change ((match pi_map Sig H 0 (quote_value C z) with
    | None => dbot (E_dcpo Sig H)
    | Some code => runner_branch C rs stage code
        (@pair_power (E_dcpo Sig H) e (quote_value C z))
    end) = val_expr_hist C rs (proj1_sig z) e).
  rewrite pi_quote.
  destruct (syntax_encode C z) as [code [H0 H1]] eqn:Hcode; cbn.
  unfold runner_branch.
  destruct (Nat.eq_dec code 0); [contradiction|].
  destruct (Nat.eq_dec code 1); [contradiction|].
  cbn.
  assert (Hdecode : forall pf : nonreserved code,
      syntax_decode C (exist nonreserved code pf) = z).
  { intro pf.
    assert (Hcode' : exist nonreserved code pf = syntax_encode C z).
    { apply sig_prop_ext. cbn. now rewrite Hcode. }
    rewrite Hcode'. apply syntax_decode_encode. }
  rewrite (Hdecode _).
  destruct (le_dec (expr_height (proj1_sig z)) stage); [|lia].
  reflexivity.
Qed.

Theorem Run_n_quote : forall Sig H (C : SyntaxCoding Sig H) n
    (z : SyntaxCarrier Sig H) (e : E_car Sig H),
    expr_height (proj1_sig z) <= n ->
    Run_n C n (@pair_power (E_dcpo Sig H) e (quote_value C z)) =
      val_expr_hist C (run_history C n) (proj1_sig z) e.
Proof.
  intros. rewrite Run_n_unfold. now apply make_run_quote.
Qed.

Print Assumptions Run_n_quote.

(** The total runner, presented extensionally by all flat syntax-code fibres.
    The subsequent stability theorem identifies it with the height chain. *)
Definition total_runner_branch {Sig H} (C : SyntaxCoding Sig H)
    (code : nat) : RunMap Sig H.
Proof.
  destruct (Nat.eq_dec code 0) as [H0|H0].
  - exact (run_bottom Sig H).
  - destruct (Nat.eq_dec code 1) as [H1|H1].
    + exact (run_bottom Sig H).
    + pose (z := syntax_decode C (exist _ code (conj H0 H1))).
      exact (@sc_comp (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H)
        (E_dcpo Sig H) (Val_map C (proj1_sig z)) (first2 (E_dcpo Sig H))).
Defined.

Definition Run {Sig H} (C : SyntaxCoding Sig H) : RunMap Sig H :=
  @flat_dispatch (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H)
    (runner_tag Sig H) (total_runner_branch C).

Lemma Run_quote : forall Sig H (C : SyntaxCoding Sig H)
    (z : SyntaxCarrier Sig H) (e : E_car Sig H),
    Run C (@pair_power (E_dcpo Sig H) e (quote_value C z)) = Val C e z.
Proof.
  intros Sig H C z e. unfold Run, flat_dispatch.
  change ((match pi_map Sig H 0 (quote_value C z) with
    | None => dbot (E_dcpo Sig H)
    | Some code => total_runner_branch C code
        (@pair_power (E_dcpo Sig H) e (quote_value C z))
    end) = Val C e z).
  rewrite pi_quote.
  destruct (syntax_encode C z) as [code [H0 H1]] eqn:Hcode; cbn.
  unfold total_runner_branch.
  destruct (Nat.eq_dec code 0); [contradiction|].
  destruct (Nat.eq_dec code 1); [contradiction|]. cbn.
  assert (Hdecode : forall pf : nonreserved code,
      syntax_decode C (exist nonreserved code pf) = z).
  { intro pf.
    assert (Hcode' : exist nonreserved code pf = syntax_encode C z).
    { apply sig_prop_ext. cbn. now rewrite Hcode. }
    rewrite Hcode'. apply syntax_decode_encode. }
  rewrite (Hdecode _). reflexivity.
Qed.

Definition resident_runner {Sig H} (C : SyntaxCoding Sig H) : E_car Sig H :=
  enc_map Sig H 2 (Run C).

Theorem resident_runner_decodes : forall Sig H (C : SyntaxCoding Sig H),
    theta_map Sig H (resident_runner C) = @resident_structure Sig H 2 (Run C).
Proof.
  intros. unfold resident_runner.
  rewrite enc_map_apply. unfold enc. apply theta_omega.
Qed.

Print Assumptions Run_quote.
Print Assumptions resident_runner_decodes.
