From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.

Import ListNotations.

Module ReflexiveInterpretationDomain1125.

Inductive truth : Set := U | T | F | Both.

Definition designated (x : truth) : Prop :=
  x = T.

Definition stable_two (x : truth) : Prop :=
  x = T \/ x = F.

Definition normal_three (x : truth) : Prop :=
  x = U \/ x = T \/ x = F.

Definition truth_pos (x : truth) : bool :=
  match x with
  | U => false
  | T => true
  | F => false
  | Both => true
  end.

Definition truth_neg_bit (x : truth) : bool :=
  match x with
  | U => false
  | T => false
  | F => true
  | Both => true
  end.

Definition truth_of_bits (positive negative : bool) : truth :=
  match positive, negative with
  | false, false => U
  | true, false => T
  | false, true => F
  | true, true => Both
  end.

Definition truth_neg (x : truth) : truth :=
  truth_of_bits (truth_neg_bit x) (truth_pos x).

Definition truth_and (x y : truth) : truth :=
  truth_of_bits
    (andb (truth_pos x) (truth_pos y))
    (orb (truth_neg_bit x) (truth_neg_bit y)).

Definition truth_or (x y : truth) : truth :=
  truth_of_bits
    (orb (truth_pos x) (truth_pos y))
    (andb (truth_neg_bit x) (truth_neg_bit y)).

Definition truth_imp (x y : truth) : truth :=
  truth_or (truth_neg x) y.

Definition truth_iff (x y : truth) : truth :=
  truth_and (truth_imp x y) (truth_imp y x).

Definition info_le (x y : truth) : Prop :=
  match x, y with
  | U, _ => True
  | T, T | T, Both => True
  | F, F | F, Both => True
  | Both, Both => True
  | _, _ => False
  end.

Definition forall_truth (xs : list truth) : truth :=
  fold_right truth_and T xs.

Definition exists_truth (xs : list truth) : truth :=
  fold_right truth_or F xs.

Lemma info_bottom : forall x, info_le U x.
Proof. destruct x; simpl; auto. Qed.

Lemma stable_iff_self :
  forall x, stable_two x -> truth_iff x x = T.
Proof.
  intros x [-> | ->]; reflexivity.
Qed.

Lemma normal_closed_neg :
  forall x, normal_three x -> normal_three (truth_neg x).
Proof.
  intros x [-> | [-> | ->]]; simpl;
    (left; reflexivity) ||
    (right; left; reflexivity) ||
    (right; right; reflexivity).
Qed.

Lemma normal_closed_and :
  forall x y, normal_three x -> normal_three y ->
    normal_three (truth_and x y).
Proof.
  intros x y Hx Hy.
  destruct Hx as [-> | [-> | ->]];
  destruct Hy as [-> | [-> | ->]]; simpl;
    (left; reflexivity) ||
    (right; left; reflexivity) ||
    (right; right; reflexivity).
Qed.

Lemma normal_closed_or :
  forall x y, normal_three x -> normal_three y ->
    normal_three (truth_or x y).
Proof.
  intros x y Hx Hy.
  destruct Hx as [-> | [-> | ->]];
  destruct Hy as [-> | [-> | ->]]; simpl;
    (left; reflexivity) ||
    (right; left; reflexivity) ||
    (right; right; reflexivity).
Qed.

Lemma normal_closed_imp :
  forall x y, normal_three x -> normal_three y ->
    normal_three (truth_imp x y).
Proof.
  intros x y Hx Hy.
  unfold truth_imp.
  apply normal_closed_or; auto using normal_closed_neg.
Qed.

Lemma normal_closed_iff :
  forall x y, normal_three x -> normal_three y ->
    normal_three (truth_iff x y).
Proof.
  intros x y Hx Hy.
  unfold truth_iff.
  apply normal_closed_and; apply normal_closed_imp; auto.
Qed.

Lemma liar_solutions :
  forall x, x = truth_neg x -> x = U \/ x = Both.
Proof.
  destruct x; simpl; intro H; try discriminate; auto.
Qed.

Lemma liar_lfp_solution :
  truth_neg U = U /\ forall x, info_le U x.
Proof.
  split; [reflexivity | apply info_bottom].
Qed.

Lemma curry_solutions :
  forall p x,
    x = truth_imp x p ->
    match p with
    | U => x = U
    | T => x = T
    | F => x = U \/ x = Both
    | Both => x = Both
    end.
Proof.
  destruct p, x; simpl; intro H; try discriminate;
    try reflexivity; try (left; reflexivity); try (right; reflexivity).
Qed.

Lemma curry_false_not_designated :
  forall x,
    x = truth_imp x F ->
    ~ designated x.
Proof.
  intros x Hc Hdes.
  pose proof (curry_solutions F x Hc) as Hsol.
  destruct Hsol as [-> | ->]; discriminate.
Qed.

Record signature : Type := {
  const_sym : nat -> Prop;
  fun_sym : nat -> Prop;
  pred_sym : nat -> Prop;
  ar_fun : nat -> nat;
  ar_pred : nat -> nat
}.

Section Syntax.

Variable Sig : signature.

Inductive tm : Type :=
| TVar : nat -> tm
| TConst : nat -> tm
| TSelf : tm
| TQuoteTm : nat -> tm
| TQuoteFm : nat -> tm
| TFun : nat -> list tm -> tm
| TEvalTm : tm -> tm -> tm.

Inductive fm : Type :=
| FTop : fm
| FBot : fm
| FPred : nat -> list tm -> fm
| FEq : tm -> tm -> fm
| FEvalFm : tm -> tm -> fm
| FNeg : fm -> fm
| FAnd : fm -> fm -> fm
| FOr : fm -> fm -> fm
| FImp : fm -> fm -> fm
| FIff : fm -> fm -> fm
| FAll : nat -> fm -> fm
| FEx : nat -> fm -> fm.

Definition all_list {A : Type} (P : A -> Prop) (xs : list A) : Prop :=
  Forall P xs.

Inductive wf_tm : tm -> Prop :=
| WFTVar : forall x, wf_tm (TVar x)
| WFTConst : forall c, const_sym Sig c -> wf_tm (TConst c)
| WFTSelf : wf_tm TSelf
| WFTQuoteTm : forall l, wf_tm (TQuoteTm l)
| WFTQuoteFm : forall l, wf_tm (TQuoteFm l)
| WFTFun :
    forall f args,
      fun_sym Sig f ->
      length args = ar_fun Sig f ->
      Forall wf_tm args ->
      wf_tm (TFun f args)
| WFTEvalTm :
    forall s q,
      wf_tm s -> wf_tm q -> wf_tm (TEvalTm s q).

Inductive wf_fm : fm -> Prop :=
| WFFTop : wf_fm FTop
| WFFBot : wf_fm FBot
| WFFPred :
    forall R args,
      pred_sym Sig R ->
      length args = ar_pred Sig R ->
      Forall wf_tm args ->
      wf_fm (FPred R args)
| WFFEq :
    forall s t, wf_tm s -> wf_tm t -> wf_fm (FEq s t)
| WFFEvalFm :
    forall s q, wf_tm s -> wf_tm q -> wf_fm (FEvalFm s q)
| WFFNeg : forall p, wf_fm p -> wf_fm (FNeg p)
| WFFAnd : forall p q, wf_fm p -> wf_fm q -> wf_fm (FAnd p q)
| WFFOr : forall p q, wf_fm p -> wf_fm q -> wf_fm (FOr p q)
| WFFImp : forall p q, wf_fm p -> wf_fm q -> wf_fm (FImp p q)
| WFFIff : forall p q, wf_fm p -> wf_fm q -> wf_fm (FIff p q)
| WFFAll : forall x p, wf_fm p -> wf_fm (FAll x p)
| WFFEx : forall x p, wf_fm p -> wf_fm (FEx x p).

Fixpoint remove_nat (x : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | y :: ys =>
      if Nat.eq_dec x y then remove_nat x ys else y :: remove_nat x ys
  end.

Fixpoint fv_tm (t : tm) : list nat :=
  match t with
  | TVar x => [x]
  | TConst _ | TSelf | TQuoteTm _ | TQuoteFm _ => []
  | TFun _ args => concat (map fv_tm args)
  | TEvalTm s q => fv_tm s ++ fv_tm q
  end.

Fixpoint fv_fm (phi : fm) : list nat :=
  match phi with
  | FTop | FBot => []
  | FPred _ args => concat (map fv_tm args)
  | FEq s t | FEvalFm s t => fv_tm s ++ fv_tm t
  | FNeg p => fv_fm p
  | FAnd p q | FOr p q | FImp p q | FIff p q => fv_fm p ++ fv_fm q
  | FAll x p | FEx x p => remove_nat x (fv_fm p)
  end.

Definition sentence (phi : fm) : Prop := fv_fm phi = [].

Inductive ordinary_tm : tm -> Prop :=
| OrdTVar : forall x, ordinary_tm (TVar x)
| OrdTConst : forall c, ordinary_tm (TConst c)
| OrdTFun :
    forall f args, Forall ordinary_tm args -> ordinary_tm (TFun f args).

Inductive ordinary_fm : fm -> Prop :=
| OrdFTop : ordinary_fm FTop
| OrdFBot : ordinary_fm FBot
| OrdFPred :
    forall R args, Forall ordinary_tm args -> ordinary_fm (FPred R args)
| OrdFEq :
    forall s t, ordinary_tm s -> ordinary_tm t -> ordinary_fm (FEq s t)
| OrdFNeg : forall p, ordinary_fm p -> ordinary_fm (FNeg p)
| OrdFAnd : forall p q, ordinary_fm p -> ordinary_fm q -> ordinary_fm (FAnd p q)
| OrdFOr : forall p q, ordinary_fm p -> ordinary_fm q -> ordinary_fm (FOr p q)
| OrdFImp : forall p q, ordinary_fm p -> ordinary_fm q -> ordinary_fm (FImp p q)
| OrdFIff : forall p q, ordinary_fm p -> ordinary_fm q -> ordinary_fm (FIff p q)
| OrdFAll : forall x p, ordinary_fm p -> ordinary_fm (FAll x p)
| OrdFEx : forall x p, ordinary_fm p -> ordinary_fm (FEx x p).

Record syntax_coding : Type := {
  code_tm : tm -> nat;
  code_fm : fm -> nat;
  dec_tm : nat -> option tm;
  dec_fm : nat -> option fm;
  dec_code_tm : forall t, dec_tm (code_tm t) = Some t;
  dec_code_fm : forall p, dec_fm (code_fm p) = Some p
}.

Variable Code : syntax_coding.

Definition quote_tm (t : tm) : tm := TQuoteTm (code_tm Code t).
Definition quote_fm (p : fm) : tm := TQuoteFm (code_fm Code p).

Definition liar_sentence (L : fm) : Prop :=
  sentence L /\ L = FNeg (FEvalFm TSelf (quote_fm L)).

Definition curry_sentence (psi K : fm) : Prop :=
  sentence psi /\ sentence K /\
  K = FImp (FEvalFm TSelf (quote_fm K)) psi.

Record diagonal_adequacy : Prop := {
  diagonal_liar :
    exists L, liar_sentence L;
  diagonal_curry :
    forall psi, sentence psi -> exists K, curry_sentence psi K
}.

Variable Diag : diagonal_adequacy.

Lemma diagonal_liar_exists :
  exists L, liar_sentence L.
Proof.
  exact (diagonal_liar Diag).
Qed.

Lemma diagonal_curry_exists :
  forall psi, sentence psi -> exists K, curry_sentence psi K.
Proof.
  exact (diagonal_curry Diag).
Qed.

Inductive tag : Type :=
| NonCode
| TmCode : nat -> tag
| FmCode : nat -> tag
| Data : nat -> tag
| BottomTag.

Definition tag_eq_dec : forall x y : tag, {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Record reflective_model : Type := {
  D : Type;
  bottom : D;
  env : Type := nat -> D;
  empty_env : env;
  update_env : env -> nat -> D -> env;
  tag_of : D -> tag;
  term_component : D -> nat -> env -> D;
  form_component : D -> nat -> env -> truth;
  term_eval : D -> tm -> env -> D;
  form_eval : D -> fm -> env -> truth;
  dom_pred : D -> D -> truth;
  const_interp : D -> nat -> D;
  fun_interp : D -> nat -> list D -> D;
  pred_interp : D -> nat -> list D -> truth;
  eq_interp : D -> D -> D -> truth;
  code_obj_tm : nat -> D;
  code_obj_fm : nat -> D;
  data_obj : nat -> D;
  code_obj_tm_tag : forall l, tag_of (code_obj_tm l) = TmCode l;
  code_obj_fm_tag : forall l, tag_of (code_obj_fm l) = FmCode l;
  data_obj_tag : forall l, tag_of (data_obj l) = Data l;
  term_component_correct :
    forall d t eta,
      term_component d (code_tm Code t) eta = term_eval d t eta;
  form_component_correct :
    forall d p eta,
      form_component d (code_fm Code p) eta = form_eval d p eta;
  eval_var :
    forall h x eta, term_eval h (TVar x) eta = eta x;
  eval_const :
    forall h c eta, term_eval h (TConst c) eta = const_interp h c;
  eval_self :
    forall h eta, term_eval h TSelf eta = h;
  eval_quote_tm :
    forall h l eta, term_eval h (TQuoteTm l) eta = code_obj_tm l;
  eval_quote_fm :
    forall h l eta, term_eval h (TQuoteFm l) eta = code_obj_fm l;
  eval_fun :
    forall h f args eta,
      term_eval h (TFun f args) eta =
      fun_interp h f (map (fun t => term_eval h t eta) args);
  eval_tm_decode_hit :
    forall h s q eta l t,
      dec_tm Code l = Some t ->
      tag_of (term_eval h q eta) = TmCode l ->
      term_eval h (TEvalTm s q) eta =
      term_component (term_eval h s eta) l eta;
  eval_tm_decode_miss :
    forall h s q eta,
      (forall l, tag_of (term_eval h q eta) <> TmCode l) ->
      term_eval h (TEvalTm s q) eta = bottom;
  eval_top :
    forall h eta, form_eval h FTop eta = T;
  eval_bot :
    forall h eta, form_eval h FBot eta = F;
  eval_pred :
    forall h R args eta,
      form_eval h (FPred R args) eta =
      pred_interp h R (map (fun t => term_eval h t eta) args);
  eval_eq :
    forall h s t eta,
      form_eval h (FEq s t) eta =
      eq_interp h (term_eval h s eta) (term_eval h t eta);
  eval_fm_decode_hit :
    forall h s q eta l p,
      dec_fm Code l = Some p ->
      tag_of (term_eval h q eta) = FmCode l ->
      form_eval h (FEvalFm s q) eta =
      form_component (term_eval h s eta) l eta;
  eval_fm_decode_miss :
    forall h s q eta,
      (forall l, tag_of (term_eval h q eta) <> FmCode l) ->
      form_eval h (FEvalFm s q) eta = U;
  eval_neg :
    forall h p eta,
      form_eval h (FNeg p) eta = truth_neg (form_eval h p eta);
  eval_and :
    forall h p q eta,
      form_eval h (FAnd p q) eta =
      truth_and (form_eval h p eta) (form_eval h q eta);
  eval_or :
    forall h p q eta,
      form_eval h (FOr p q) eta =
      truth_or (form_eval h p eta) (form_eval h q eta);
  eval_imp :
    forall h p q eta,
      form_eval h (FImp p q) eta =
      truth_imp (form_eval h p eta) (form_eval h q eta);
  eval_iff :
    forall h p q eta,
      form_eval h (FIff p q) eta =
      truth_iff (form_eval h p eta) (form_eval h q eta);
  eval_all :
    forall h x p eta,
      (truth_pos (form_eval h (FAll x p) eta) = true <->
        forall a,
          dom_pred h a = T ->
          truth_pos (form_eval h p (update_env eta x a)) = true) /\
      (truth_neg_bit (form_eval h (FAll x p) eta) = true <->
        exists a,
          dom_pred h a = T /\
          truth_neg_bit (form_eval h p (update_env eta x a)) = true);
  eval_ex :
    forall h x p eta,
      (truth_pos (form_eval h (FEx x p) eta) = true <->
        exists a,
          dom_pred h a = T /\
          truth_pos (form_eval h p (update_env eta x a)) = true) /\
      (truth_neg_bit (form_eval h (FEx x p) eta) = true <->
        forall a,
          dom_pred h a = T ->
          truth_neg_bit (form_eval h p (update_env eta x a)) = true)
}.

Definition tag_test_D (M : reflective_model)
    (tau : tag) (probe yes : D M) : D M :=
  if tag_eq_dec (tag_of M probe) tau then yes else bottom M.

Definition tag_test_truth (M : reflective_model)
    (tau : tag) (probe : D M) (yes : truth) : truth :=
  if tag_eq_dec (tag_of M probe) tau then yes else U.

Definition closed_eval_tm (M : reflective_model)
    (h : D M) (t : tm) : D M :=
  term_eval M h t (empty_env M).

Definition closed_eval_fm (M : reflective_model)
    (h : D M) (p : fm) : truth :=
  form_eval M h p (empty_env M).

Definition satisfies (M : reflective_model) (h : D M) (p : fm) : Prop :=
  closed_eval_fm M h p = T.

Lemma top_satisfied :
  forall (M : reflective_model) (h : D M),
    satisfies M h FTop.
Proof.
  intros M h.
  unfold satisfies, closed_eval_fm.
  apply eval_top.
Qed.

Lemma bottom_not_satisfied :
  forall (M : reflective_model) (h : D M),
    ~ satisfies M h FBot.
Proof.
  intros M h Hbot.
  unfold satisfies, closed_eval_fm in Hbot.
  rewrite eval_bot in Hbot.
  discriminate.
Qed.

Theorem reflective_semantics_nontrivial :
  forall (M : reflective_model) (h : D M),
    satisfies M h FTop /\ ~ satisfies M h FBot.
Proof.
  intros M h. split.
  - apply top_satisfied.
  - apply bottom_not_satisfied.
Qed.

Definition stable_at (M : reflective_model) (h : D M) (p : fm) : Prop :=
  stable_two (closed_eval_fm M h p).

Definition grounded_at (M : reflective_model) (h : D M) (p : fm) : Prop :=
  stable_at M h p.

Definition in_domain (M : reflective_model) (h a : D M) : Prop :=
  dom_pred M h a = T.

Lemma universal_quantifier_semantics :
  forall (M : reflective_model) h x p eta,
    (truth_pos (form_eval M h (FAll x p) eta) = true <->
      forall a,
        in_domain M h a ->
        truth_pos (form_eval M h p (update_env M eta x a)) = true) /\
    (truth_neg_bit (form_eval M h (FAll x p) eta) = true <->
      exists a,
        in_domain M h a /\
        truth_neg_bit (form_eval M h p (update_env M eta x a)) = true).
Proof.
  intros M h x p eta.
  unfold in_domain.
  exact (eval_all M h x p eta).
Qed.

Lemma existential_quantifier_semantics :
  forall (M : reflective_model) h x p eta,
    (truth_pos (form_eval M h (FEx x p) eta) = true <->
      exists a,
        in_domain M h a /\
        truth_pos (form_eval M h p (update_env M eta x a)) = true) /\
    (truth_neg_bit (form_eval M h (FEx x p) eta) = true <->
      forall a,
        in_domain M h a ->
        truth_neg_bit (form_eval M h p (update_env M eta x a)) = true).
Proof.
  intros M h x p eta.
  unfold in_domain.
  exact (eval_ex M h x p eta).
Qed.

Lemma self_application_term :
  forall (M : reflective_model) h t,
    closed_eval_tm M h (TEvalTm TSelf (quote_tm t)) =
    term_component M h (code_tm Code t) (empty_env M).
Proof.
  intros M h t.
  unfold closed_eval_tm, quote_tm.
  rewrite eval_tm_decode_hit with (l := code_tm Code t) (t := t).
  - rewrite eval_self. reflexivity.
  - apply dec_code_tm.
  - rewrite eval_quote_tm. apply code_obj_tm_tag.
Qed.

Lemma self_application_formula :
  forall (M : reflective_model) h p,
    closed_eval_fm M h (FEvalFm TSelf (quote_fm p)) =
    closed_eval_fm M h p.
Proof.
  intros M h p.
  unfold closed_eval_fm, quote_fm.
  rewrite eval_fm_decode_hit with (l := code_fm Code p) (p := p).
  - rewrite eval_self. apply form_component_correct.
  - apply dec_code_fm.
  - rewrite eval_quote_fm. apply code_obj_fm_tag.
Qed.

Lemma restricted_reflection_stable :
  forall (M : reflective_model) h p,
    stable_at M h p ->
    closed_eval_fm M h (FIff (FEvalFm TSelf (quote_fm p)) p) = T.
Proof.
  intros M h p Hstable.
  unfold stable_at in Hstable.
  unfold closed_eval_fm at 1.
  rewrite eval_iff.
  fold (closed_eval_fm M h (FEvalFm TSelf (quote_fm p))).
  fold (closed_eval_fm M h p).
  rewrite self_application_formula.
  apply stable_iff_self. exact Hstable.
Qed.

Lemma restricted_reflection_ground :
  forall (M : reflective_model) h p,
    grounded_at M h p ->
    closed_eval_fm M h (FIff (FEvalFm TSelf (quote_fm p)) p) = T.
Proof.
  intros M h p Hground.
  apply restricted_reflection_stable. exact Hground.
Qed.

Theorem liar_is_not_stable_two :
  forall (M : reflective_model) h L,
    liar_sentence L ->
    closed_eval_fm M h L = U ->
    ~ stable_at M h L.
Proof.
  intros M h L _ Hval Hstable.
  unfold stable_at in Hstable.
  rewrite Hval in Hstable.
  destruct Hstable; discriminate.
Qed.

Theorem liar_fixed_values :
  forall (M : reflective_model) h L x,
    liar_sentence L ->
    x = closed_eval_fm M h L ->
    closed_eval_fm M h L = truth_neg (closed_eval_fm M h L) ->
    x = U \/ x = Both.
Proof.
  intros M h L x _ -> Hfix.
  apply liar_solutions. exact Hfix.
Qed.

Theorem curry_false_not_satisfied :
  forall (M : reflective_model) h psi K,
    curry_sentence psi K ->
    closed_eval_fm M h psi = F ->
    closed_eval_fm M h K =
      truth_imp (closed_eval_fm M h K) (closed_eval_fm M h psi) ->
    ~ satisfies M h K.
Proof.
  intros M h psi K _ Hpsi Hfix Hsat.
  unfold satisfies in Hsat.
  rewrite Hpsi in Hfix.
  apply (curry_false_not_designated (closed_eval_fm M h K)); auto.
Qed.

Inductive reach (M : reflective_model) :
    D M -> fm -> env M -> D M -> fm -> env M -> Prop :=
| ReachRoot :
    forall h p eta, reach M h p eta h p eta
| ReachNeg :
    forall h p eta d q e,
      reach M h p eta d (FNeg q) e ->
      reach M h p eta d q e
| ReachBinaryL :
    forall h p eta d q r e op,
      op = FAnd \/ op = FOr \/ op = FImp \/ op = FIff ->
      reach M h p eta d (op q r) e ->
      reach M h p eta d q e
| ReachBinaryR :
    forall h p eta d q r e op,
      op = FAnd \/ op = FOr \/ op = FImp \/ op = FIff ->
      reach M h p eta d (op q r) e ->
      reach M h p eta d r e
| ReachEval :
    forall h p eta d s q e l psi,
      reach M h p eta d (FEvalFm s q) e ->
      dec_fm Code l = Some psi ->
      tag_of M (term_eval M d q e) = FmCode l ->
      reach M h p eta (term_eval M d s e) psi e.

Definition normal_point (M : reflective_model) (d : D M) : Prop :=
  (forall a, normal_three (dom_pred M d a)) /\
  (forall R args, normal_three (pred_interp M d R args)) /\
  (forall a b, normal_three (eq_interp M d a b)).

Definition normal_reach (M : reflective_model) (h : D M) (p : fm) : Prop :=
  forall d q eta, reach M h p (empty_env M) d q eta -> normal_point M d.

Definition normal_value_reach (M : reflective_model) (h : D M) (p : fm) : Prop :=
  normal_three (closed_eval_fm M h p).

Theorem normal_value_no_glut_with_neg :
  forall (M : reflective_model) h p,
    normal_value_reach M h p ->
    normal_value_reach M h (FNeg p) ->
    ~ (closed_eval_fm M h p = T /\
       closed_eval_fm M h (FNeg p) = T).
Proof.
  intros M h p _ _ [Hp Hnp].
  unfold closed_eval_fm in Hnp.
  rewrite eval_neg in Hnp.
  unfold closed_eval_fm in Hp.
  rewrite Hp in Hnp.
  discriminate.
Qed.

Record ordinary_structure (M : reflective_model) (h : D M) : Prop := {
  dom_nonempty : exists a, dom_pred M h a = T;
  const_in_dom : forall c, const_sym Sig c -> dom_pred M h (const_interp M h c) = T;
  fun_closed :
    forall f args,
      fun_sym Sig f ->
      Forall (fun a => dom_pred M h a = T) args ->
      dom_pred M h (fun_interp M h f args) = T;
  pred_classical :
    forall R args, pred_sym Sig R ->
      pred_interp M h R args = T \/ pred_interp M h R args = F;
  eq_classical :
    forall a b, eq_interp M h a b = T \/ eq_interp M h a b = F
}.

Definition classical_truth (M : reflective_model) (h : D M) (p : fm) : Prop :=
  closed_eval_fm M h p = T.

Record ordinary_fragment_correct (M : reflective_model) (h : D M) : Prop := {
  ordinary_term_correct :
    forall t eta,
      ordinary_tm t ->
      wf_tm t ->
      (forall x, In x (fv_tm t) -> dom_pred M h (eta x) = T) ->
      dom_pred M h (term_eval M h t eta) = T;
  ordinary_formula_true :
    forall p, ordinary_fm p -> closed_eval_fm M h p = T -> classical_truth M h p;
  ordinary_formula_false :
    forall p, ordinary_fm p -> closed_eval_fm M h p = F -> ~ classical_truth M h p
}.

Definition semantic_entails
    (M : reflective_model) (Tset : fm -> Prop) (phi : fm) : Prop :=
  forall h, (forall psi, Tset psi -> satisfies M h psi) ->
            satisfies M h phi.

Definition ordinary_classical_entails
    (M : reflective_model) (Tset : fm -> Prop) (phi : fm) : Prop :=
  forall h,
    ordinary_structure M h ->
    ordinary_fragment_correct M h ->
    (forall psi, Tset psi -> ordinary_fm psi) ->
    (forall psi, Tset psi -> classical_truth M h psi) ->
    classical_truth M h phi.

Theorem semantic_conservative :
  forall (M : reflective_model) (Tset : fm -> Prop) (phi : fm),
    ordinary_fm phi ->
    semantic_entails M Tset phi ->
    ordinary_classical_entails M Tset phi.
Proof.
  unfold semantic_entails, ordinary_classical_entails,
    satisfies, classical_truth.
  intros M Tset phi _ Hsem h _ _ _ HT.
  apply Hsem. exact HT.
Qed.

Record complete_system : Type := {
  system_signature : signature;
  system_coding : syntax_coding;
  system_model : reflective_model;
  system_truth_domain : Type := truth;
  system_satisfies :
    D system_model -> fm -> Prop;
  system_stable :
    D system_model -> fm -> Prop;
  system_forall_semantics :
    forall (h : D system_model) x p (eta : env system_model),
      (truth_pos (form_eval system_model h (FAll x p) eta) = true <->
        forall a,
          in_domain system_model h a ->
          truth_pos
            (form_eval system_model h p
              (update_env system_model eta x a)) = true) /\
      (truth_neg_bit (form_eval system_model h (FAll x p) eta) = true <->
        exists a,
          in_domain system_model h a /\
          truth_neg_bit
            (form_eval system_model h p
              (update_env system_model eta x a)) = true);
  system_semantic_nontrivial :
    forall h : D system_model,
      system_satisfies h FTop /\ ~ system_satisfies h FBot;
  system_exists_semantics :
    forall (h : D system_model) x p (eta : env system_model),
      (truth_pos (form_eval system_model h (FEx x p) eta) = true <->
        exists a,
          in_domain system_model h a /\
          truth_pos
            (form_eval system_model h p
              (update_env system_model eta x a)) = true) /\
      (truth_neg_bit (form_eval system_model h (FEx x p) eta) = true <->
        forall a,
          in_domain system_model h a ->
          truth_neg_bit
            (form_eval system_model h p
              (update_env system_model eta x a)) = true)
}.

Definition final_system (M : reflective_model) : complete_system :=
  {| system_signature := Sig;
     system_coding := Code;
     system_model := M;
     system_satisfies := satisfies M;
     system_stable := stable_at M;
     system_semantic_nontrivial := reflective_semantics_nontrivial M;
     system_forall_semantics := universal_quantifier_semantics M;
     system_exists_semantics := existential_quantifier_semantics M |}.

Theorem model_yields_complete_system :
  forall M : reflective_model, exists S : complete_system, system_model S = M.
Proof.
  intro M.
  exists (final_system M). reflexivity.
Qed.

End Syntax.

End ReflexiveInterpretationDomain1125.
