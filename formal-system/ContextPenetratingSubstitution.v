From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Lia.

Import ListNotations.

Module ContextPenetratingSubstitution.

Definition Var := nat.
Definition FSym := nat.
Definition PSym := nat.

Definition Epred : PSym := 0.

Definition var_lt (x y : Var) : Prop := x < y.

Definition remove_var (x : Var) (xs : list Var) : list Var :=
  filter (fun y => negb (Nat.eqb x y)) xs.

Definition union_vars (xs ys : list Var) : list Var := xs ++ ys.

Fixpoint fresh_from (fuel : nat) (used : list Var) : Var :=
  match fuel with
  | 0 => 0
  | S k => if existsb (Nat.eqb k) used then fresh_from k used else k
  end.

Definition fresh (used : list Var) : Var :=
  fresh_from (S (fold_right Nat.max 0 used)) used.

Inductive tm : Type :=
| TVar : Var -> tm
| TFun : FSym -> list tm -> tm
| TQuote : fm -> tm
with fm : Type :=
| FRel : PSym -> list tm -> fm
| FNeg : fm -> fm
| FAnd : fm -> fm -> fm
| FAll : Var -> fm -> fm.

Scheme tm_ind' := Induction for tm Sort Prop
with fm_ind' := Induction for fm Sort Prop.
Combined Scheme syntax_ind from tm_ind', fm_ind'.

Fixpoint var_occ_t (t : tm) : list Var :=
  match t with
  | TVar x => [x]
  | TFun _ args => concat (map var_occ_t args)
  | TQuote a => var_occ_f a
  end
with var_occ_f (a : fm) : list Var :=
  match a with
  | FRel _ args => concat (map var_occ_t args)
  | FNeg b => var_occ_f b
  | FAnd b c => var_occ_f b ++ var_occ_f c
  | FAll x b => x :: var_occ_f b
  end.

Fixpoint fv_t (t : tm) : list Var :=
  match t with
  | TVar x => [x]
  | TFun _ args => concat (map fv_t args)
  | TQuote a => fv_f a
  end
with fv_f (a : fm) : list Var :=
  match a with
  | FRel _ args => concat (map fv_t args)
  | FNeg b => fv_f b
  | FAnd b c => fv_f b ++ fv_f c
  | FAll x b => remove_var x (fv_f b)
  end.

Definition FImp (a b : fm) : fm := FNeg (FAnd a (FNeg b)).
Definition FIff (a b : fm) : fm := FAnd (FImp a b) (FImp b a).

Definition E_ctx (x y : Var) (a : fm) : fm :=
  FRel Epred [TVar x; TVar y; TQuote a].

Inductive SubT : tm -> Var -> Var -> tm -> Prop :=
| SubTVarSame :
    forall x y, SubT (TVar x) x y (TVar y)
| SubTVarDiff :
    forall x y z, z <> x -> SubT (TVar z) x y (TVar z)
| SubTFun :
    forall f xs ys x y,
      Forall2 (fun s t => SubT s x y t) xs ys ->
      SubT (TFun f xs) x y (TFun f ys)
| SubTQuote :
    forall a b x y,
      SubF a x y b ->
      SubT (TQuote a) x y (TQuote b)
with SubF : fm -> Var -> Var -> fm -> Prop :=
| SubFRel :
    forall p xs ys x y,
      Forall2 (fun s t => SubT s x y t) xs ys ->
      SubF (FRel p xs) x y (FRel p ys)
| SubFNeg :
    forall a b x y,
      SubF a x y b ->
      SubF (FNeg a) x y (FNeg b)
| SubFAnd :
    forall a b c d x y,
      SubF a x y b ->
      SubF c x y d ->
      SubF (FAnd a c) x y (FAnd b d)
| SubFAllShadow :
    forall z b y,
      SubF (FAll z b) z y (FAll z b)
| SubFAllSafe :
    forall z b c x y,
      z <> x ->
      (z <> y \/ ~ In x (fv_f b)) ->
      SubF b x y c ->
      SubF (FAll z b) x y (FAll z c)
| SubFAllRename :
    forall z b c d x y w,
      z <> x ->
      z = y ->
      In x (fv_f b) ->
      ~ In w (var_occ_f b ++ [x; y]) ->
      SubF b z w c ->
      SubF c x y d ->
      SubF (FAll z b) x y (FAll w d).

Scheme SubT_ind' := Induction for SubT Sort Prop
with SubF_ind' := Induction for SubF Sort Prop.
Combined Scheme subst_ind from SubT_ind', SubF_ind'.

Inductive AlphaT : tm -> tm -> Prop :=
| AlphaTRefl : forall t, AlphaT t t
| AlphaTFun :
    forall f xs ys,
      Forall2 AlphaT xs ys ->
      AlphaT (TFun f xs) (TFun f ys)
| AlphaTQuote :
    forall a b, AlphaF a b -> AlphaT (TQuote a) (TQuote b)
with AlphaF : fm -> fm -> Prop :=
| AlphaFRefl : forall a, AlphaF a a
| AlphaFRel :
    forall p xs ys,
      Forall2 AlphaT xs ys ->
      AlphaF (FRel p xs) (FRel p ys)
| AlphaFNeg :
    forall a b, AlphaF a b -> AlphaF (FNeg a) (FNeg b)
| AlphaFAnd :
    forall a b c d,
      AlphaF a b -> AlphaF c d -> AlphaF (FAnd a c) (FAnd b d)
| AlphaFAll :
    forall x a b,
      AlphaF a b -> AlphaF (FAll x a) (FAll x b)
| AlphaFRename :
    forall x w a b,
      ~ In w (var_occ_f a) ->
      SubF a x w b ->
      AlphaF (FAll x a) (FAll w b).

Scheme AlphaT_ind' := Induction for AlphaT Sort Prop
with AlphaF_ind' := Induction for AlphaF Sort Prop.
Combined Scheme alpha_ind from AlphaT_ind', AlphaF_ind'.

Inductive Ax : fm -> Prop :=
| AxP1 : forall a b, Ax (FImp a (FImp b a))
| AxP2 : forall a b c,
    Ax (FImp (FImp a (FImp b c))
        (FImp (FImp a b) (FImp a c)))
| AxP3 : forall a b, Ax (FImp (FAnd a b) a)
| AxP4 : forall a b, Ax (FImp (FAnd a b) b)
| AxP5 : forall a b, Ax (FImp a (FImp b (FAnd a b)))
| AxP6 : forall a b,
    Ax (FImp (FImp a b) (FImp (FImp a (FNeg b)) (FNeg a)))
| AxP7 : forall a, Ax (FImp (FNeg (FNeg a)) a)
| AxQ1 : forall x a b,
    Ax (FImp (FAll x (FImp a b)) (FImp (FAll x a) (FAll x b)))
| AxQ2 : forall x y a b,
    SubF a x y b ->
    Ax (FImp (FAll x a) b)
| AxE : forall x y a b,
    SubF a x y b ->
    Ax (FImp (E_ctx x y a) (FIff a b)).

Inductive Rule : list fm -> fm -> Prop :=
| RuleMP : forall a b, Rule [a; FImp a b] b
| RuleGen : forall x a, Rule [a] (FAll x a)
| RuleAlpha : forall a b, AlphaF a b -> Rule [a] b.

Inductive ProofLine : list fm -> fm -> Prop :=
| FromAx : forall past a, Ax a -> ProofLine past a
| FromRule :
    forall past premises a,
      Rule premises a ->
      Forall (fun p => In p past) premises ->
      ProofLine past a.

Inductive Proof : list fm -> Prop :=
| ProofOne : forall a, ProofLine [] a -> Proof [a]
| ProofSnoc :
    forall past a,
      Proof past ->
      ProofLine past a ->
      Proof (past ++ [a]).

Definition last_is (a : fm) (pi : list fm) : Prop :=
  exists past, pi = past ++ [a].

Definition Provable (a : fm) : Prop :=
  exists pi, Proof pi /\ last_is a pi.

Record CtxModel : Type := {
  state : Type;
  satisfies : state -> fm -> Prop;
  E_holds : state -> Var -> Var -> fm -> Prop;
  legal_E :
      forall g x y a b,
        E_holds g x y a ->
        SubF a x y b ->
        (satisfies g a <-> satisfies g b)
}.

Definition Valid (m : CtxModel) (a : fm) : Prop :=
  forall g : state m, satisfies m g a.

Record SoundCtxModel : Type := {
  sound_base :> CtxModel;
  sound_ax : forall a, Ax a -> Valid sound_base a;
  sound_rule :
    forall premises a,
      Rule premises a ->
      Forall (Valid sound_base) premises ->
      Valid sound_base a
}.

Lemma proofline_valid :
  forall (sm : SoundCtxModel) past a,
    Forall (Valid (sound_base sm)) past ->
    ProofLine past a ->
    Valid (sound_base sm) a.
Proof.
  intros sm past a hpast hline.
  destruct hline as [past0 a0 hax | past0 premises a0 hrule hprem].
  - exact (sound_ax sm a0 hax).
  - apply (sound_rule sm premises a0 hrule).
    apply Forall_forall.
    intros p hp_in.
    rewrite Forall_forall in hpast.
    apply hpast.
    rewrite Forall_forall in hprem.
    exact (hprem p hp_in).
Qed.

Lemma proof_valid_all :
  forall (m : CtxModel) (sm : SoundCtxModel) pi,
    m = sound_base sm ->
    Proof pi ->
    Forall (Valid m) pi.
Proof.
  intros m sm pi hm hproof.
  subst m.
  induction hproof as [a hline | past a hproof IH hline].
  - constructor.
    + apply (proofline_valid sm [] a).
      * constructor.
      * exact hline.
    + constructor.
  - apply Forall_app.
    split.
    + exact IH.
    + constructor.
      * apply (proofline_valid sm past a IH hline).
      * constructor.
Qed.

Theorem abstract_soundness :
  forall (sm : SoundCtxModel) a,
    Provable a ->
    Valid sm a.
Proof.
  intros sm a [pi [hproof [past hlast]]].
  pose proof (proof_valid_all (sound_base sm) sm pi eq_refl hproof) as hall.
  subst pi.
  rewrite Forall_app in hall.
  destruct hall as [_ htail].
  inversion htail as [|x xs hx hxs]; subst.
  exact hx.
Qed.

Record TarskiModel : Type := {
  carrier : Type;
  func_interp : FSym -> list carrier -> carrier;
  pred_interp : PSym -> list carrier -> Prop;
  quote_interp : fm -> (Var -> carrier) -> carrier
}.

Definition Assignment (m : TarskiModel) : Type := Var -> carrier m.

Definition update_assignment
    (m : TarskiModel) (rho : Assignment m) (x : Var) (d : carrier m)
    : Assignment m :=
  fun z => if Nat.eq_dec z x then d else rho z.

Fixpoint eval_t (m : TarskiModel) (rho : Assignment m) (t : tm)
    : carrier m :=
  match t with
  | TVar x => rho x
  | TFun f args => func_interp m f (map (eval_t m rho) args)
  | TQuote a => quote_interp m a rho
  end.

Fixpoint forces (m : TarskiModel) (rho : Assignment m) (a : fm) : Prop :=
  match a with
  | FRel p args => pred_interp m p (map (eval_t m rho) args)
  | FNeg b => ~ forces m rho b
  | FAnd b c => forces m rho b /\ forces m rho c
  | FAll x b => forall d : carrier m,
      forces m (update_assignment m rho x d) b
  end.

Record TarskiLegal (m : TarskiModel) : Prop := {
  tarski_subst_term_sound :
    forall rho x y s t,
      SubT s x y t ->
      eval_t m rho t =
      eval_t m (update_assignment m rho x (rho y)) s;
  tarski_subst_formula_sound :
    forall rho x y a b,
      SubF a x y b ->
      (forces m rho b <->
       forces m (update_assignment m rho x (rho y)) a);
  tarski_alpha_term_sound :
    forall rho s t,
      AlphaT s t ->
      eval_t m rho s = eval_t m rho t;
  tarski_alpha_formula_sound :
    forall rho a b,
      AlphaF a b ->
      (forces m rho a <-> forces m rho b);
  tarski_legal_E :
    forall rho x y a b,
      pred_interp m Epred [rho x; rho y; quote_interp m a rho] ->
      SubF a x y b ->
      (forces m rho a <-> forces m rho b)
}.

Definition unit_tarski_model : TarskiModel := {|
  carrier := unit;
  func_interp := fun _ _ => tt;
  pred_interp := fun _ _ => False;
  quote_interp := fun _ _ => tt
|}.

Fixpoint unit_truth (a : fm) : Prop :=
  match a with
  | FRel _ _ => False
  | FNeg b => ~ unit_truth b
  | FAnd b c => unit_truth b /\ unit_truth c
  | FAll _ b => unit_truth b
  end.

Lemma unit_forces_iff :
  forall (rho : Assignment unit_tarski_model) a,
    forces unit_tarski_model rho a <-> unit_truth a.
Proof.
  intros rho a. revert rho.
  induction a as [p args | b IHb | b IHb c IHc | x b IHb];
    intro rho; cbn.
  - tauto.
  - rewrite IHb. tauto.
  - rewrite IHb, IHc. tauto.
  - split.
    + intro Hall. specialize (Hall tt).
      exact (proj1 (IHb (update_assignment unit_tarski_model rho x tt)) Hall).
    + intros Hb d. destruct d.
      exact (proj2 (IHb (update_assignment unit_tarski_model rho x tt)) Hb).
Qed.

Lemma unit_truth_substitution :
  forall a x y b,
    SubF a x y b ->
    (unit_truth b <-> unit_truth a).
Proof.
  intros a x y b Hsub.
  induction Hsub; cbn in *; try tauto.
Qed.

Lemma unit_truth_alpha :
  forall a b,
    AlphaF a b ->
    (unit_truth a <-> unit_truth b).
Proof.
  intros a b Halpha.
  induction Halpha; cbn in *; try tauto.
  now rewrite (unit_truth_substitution _ _ _ _ H0).
Qed.

Definition unit_tarski_legal : TarskiLegal unit_tarski_model.
Proof.
  refine {|
    tarski_subst_term_sound := _;
    tarski_subst_formula_sound := _;
    tarski_alpha_term_sound := _;
    tarski_alpha_formula_sound := _;
    tarski_legal_E := _
  |}.
  - intros rho x y s t Hsub.
    destruct (eval_t unit_tarski_model rho t).
    destruct (eval_t unit_tarski_model
      (update_assignment unit_tarski_model rho x (rho y)) s).
    reflexivity.
  - intros rho x y a b Hsub.
    rewrite !unit_forces_iff.
    exact (unit_truth_substitution a x y b Hsub).
  - intros rho s t Halpha.
    destruct (eval_t unit_tarski_model rho s).
    destruct (eval_t unit_tarski_model rho t).
    reflexivity.
  - intros rho a b Halpha.
    rewrite !unit_forces_iff.
    exact (unit_truth_alpha a b Halpha).
  - intros rho x y a b _ Hsub.
    rewrite !unit_forces_iff.
    symmetry.
    exact (unit_truth_substitution a x y b Hsub).
Defined.

Record AdmModel : Type := {
  adm_base :> TarskiModel;
  adm_legal : TarskiLegal adm_base
}.

Definition unit_admissible_model : AdmModel := {|
  adm_base := unit_tarski_model;
  adm_legal := unit_tarski_legal
|}.

Definition unit_false_atom : fm := FRel 1 [].
Definition unit_tautology : fm := FImp unit_false_atom unit_false_atom.

Lemma unit_model_tautology_holds :
  forall rho : Assignment unit_admissible_model,
    forces unit_admissible_model rho unit_tautology.
Proof.
  intro rho. cbn [unit_tautology FImp unit_false_atom forces].
  tauto.
Qed.

Lemma unit_model_negated_tautology_refuted :
  forall rho : Assignment unit_admissible_model,
    ~ forces unit_admissible_model rho (FNeg unit_tautology).
Proof.
  intros rho Hneg.
  cbn [unit_tautology FImp unit_false_atom forces] in Hneg.
  tauto.
Qed.

Definition AdmValid (a : fm) : Prop :=
  forall m : AdmModel, forall rho : Assignment m, forces m rho a.

Definition LocallyValid (m : AdmModel) (a : fm) : Prop :=
  forall rho : Assignment m, forces m rho a.

Lemma forces_imp_intro :
  forall (m : TarskiModel) (rho : Assignment m) a b,
    (forces m rho a -> forces m rho b) ->
    forces m rho (FImp a b).
Proof.
  intros m rho a b hab.
  simpl.
  intros [ha hnb].
  exact (hnb (hab ha)).
Qed.

Lemma forces_imp_elim :
  forall (m : TarskiModel) (rho : Assignment m) a b,
    forces m rho (FImp a b) ->
    forces m rho a ->
    forces m rho b.
Proof.
  intros m rho a b hab ha.
  apply NNPP.
  intro hnb.
  exact (hab (conj ha hnb)).
Qed.

Lemma forces_iff_intro :
  forall (m : TarskiModel) (rho : Assignment m) a b,
    (forces m rho a <-> forces m rho b) ->
    forces m rho (FIff a b).
Proof.
  intros m rho a b hab.
  split.
  - apply forces_imp_intro.
    exact (proj1 hab).
  - apply forces_imp_intro.
    exact (proj2 hab).
Qed.

Theorem adm_valid_context_identity_axiom :
  forall x y a b,
    SubF a x y b ->
    AdmValid (FImp (E_ctx x y a) (FIff a b)).
Proof.
  intros x y a b hsub m rho.
  apply forces_imp_intro.
  intro hE.
  apply forces_iff_intro.
  exact (tarski_legal_E m (adm_legal m) rho x y a b hE hsub).
Qed.

Theorem substitution_lemma_term :
  forall (m : AdmModel) rho x y s t,
    SubT s x y t ->
    eval_t m rho t =
    eval_t m (update_assignment m rho x (rho y)) s.
Proof.
  intros m rho x y s t hsub.
  exact (tarski_subst_term_sound m (adm_legal m) rho x y s t hsub).
Qed.

Theorem substitution_lemma_formula :
  forall (m : AdmModel) rho x y a b,
    SubF a x y b ->
    (forces m rho b <->
     forces m (update_assignment m rho x (rho y)) a).
Proof.
  intros m rho x y a b hsub.
  exact (tarski_subst_formula_sound m (adm_legal m) rho x y a b hsub).
Qed.

Theorem alpha_soundness_formula :
  forall (m : AdmModel) rho a b,
    AlphaF a b ->
    (forces m rho a <-> forces m rho b).
Proof.
  intros m rho a b halpha.
  exact (tarski_alpha_formula_sound m (adm_legal m) rho a b halpha).
Qed.

Theorem adm_axiom_valid_in :
  forall (m : AdmModel) a,
    Ax a ->
    LocallyValid m a.
Proof.
  intros m a hax rho.
  destruct hax as
    [a b
    |a b c
    |a b
    |a b
    |a b
    |a b
    |a
    |x a b
    |x y a b hsub
    |x y a b hsub].
  - apply forces_imp_intro. intro ha.
    apply forces_imp_intro. intro hb.
    exact ha.
  - apply forces_imp_intro. intro ha_bc.
    apply forces_imp_intro. intro ha_b.
    apply forces_imp_intro. intro ha.
    apply (forces_imp_elim m rho b c).
    + apply (forces_imp_elim m rho a (FImp b c)); assumption.
    + apply (forces_imp_elim m rho a b); assumption.
  - apply forces_imp_intro. intros [ha _].
    exact ha.
  - apply forces_imp_intro. intros [_ hb].
    exact hb.
  - apply forces_imp_intro. intro ha.
    apply forces_imp_intro. intro hb.
    split; assumption.
  - apply forces_imp_intro. intro ha_b.
    apply forces_imp_intro. intro ha_notb.
    simpl. intro ha.
    pose proof (forces_imp_elim m rho a b ha_b ha) as hb.
    pose proof (forces_imp_elim m rho a (FNeg b) ha_notb ha) as hnb.
    exact (hnb hb).
  - apply forces_imp_intro. intro hnna.
    simpl in hnna.
    exact (NNPP (forces m rho a) hnna).
  - apply forces_imp_intro. intro hforall_imp.
    apply forces_imp_intro. intro hforall_a.
    simpl. intro d.
    apply (forces_imp_elim m (update_assignment m rho x d) a b).
    + exact (hforall_imp d).
    + exact (hforall_a d).
  - apply forces_imp_intro. intro hforall.
    apply (proj2 (substitution_lemma_formula m rho x y a b hsub)).
    exact (hforall (rho y)).
  - exact (adm_valid_context_identity_axiom x y a b hsub m rho).
Qed.

Theorem adm_axiom_valid :
  forall a,
    Ax a ->
    AdmValid a.
Proof.
  intros a hax m.
  exact (adm_axiom_valid_in m a hax).
Qed.

Theorem adm_rule_valid_in :
  forall (m : AdmModel) premises a,
    Rule premises a ->
    Forall (LocallyValid m) premises ->
    LocallyValid m a.
Proof.
  intros m premises a hrule hprem rho.
  destruct hrule as [a b | x a | a b halpha].
  - inversion hprem as [|p ps hp_a hp_tail]; subst.
    inversion hp_tail as [|q qs hp_imp hp_nil]; subst.
    exact (forces_imp_elim m rho a b (hp_imp rho) (hp_a rho)).
  - inversion hprem as [|p ps hp_a hp_nil]; subst.
    simpl. intro d.
    exact (hp_a (update_assignment m rho x d)).
  - inversion hprem as [|p ps hp_a hp_nil]; subst.
    apply (proj1 (alpha_soundness_formula m rho a b halpha)).
    exact (hp_a rho).
Qed.

Theorem adm_rule_valid :
  forall premises a,
    Rule premises a ->
    Forall AdmValid premises ->
    AdmValid a.
Proof.
  intros premises a hrule hprem m rho.
  apply (adm_rule_valid_in m premises a hrule).
  rewrite Forall_forall in *.
  intros p hp rho'.
  exact (hprem p hp m rho').
Qed.

Definition adm_ctx_model (m : AdmModel) : CtxModel.
Proof.
  refine {|
    state := Assignment m;
    satisfies := forces m;
    E_holds := fun rho x y a =>
      pred_interp m Epred [rho x; rho y; quote_interp m a rho];
    legal_E := _
  |}.
  intros rho x y a b hE hsub.
  exact (tarski_legal_E m (adm_legal m) rho x y a b hE hsub).
Defined.

Definition adm_sound_ctx_model (m : AdmModel) : SoundCtxModel.
Proof.
  refine {|
    sound_base := adm_ctx_model m;
    sound_ax := _;
    sound_rule := _
  |}.
  - intros a hax rho.
    exact (adm_axiom_valid_in m a hax rho).
  - intros premises a hrule hprem rho.
    apply (adm_rule_valid_in m premises a hrule).
    rewrite Forall_forall in *.
    intros p hp rho'.
    exact (hprem p hp rho').
Defined.

Theorem soundness :
  forall a,
    Provable a ->
    AdmValid a.
Proof.
  intros a hprov m rho.
  exact (abstract_soundness (adm_sound_ctx_model m) a hprov rho).
Qed.

Record ContextPenetratingSubstitutionSystem : Type := {
  cps_var_order : Var -> Var -> Prop;
  cps_term : Type;
  cps_formula : Type;
  cps_var_occ_t : tm -> list Var;
  cps_var_occ_f : fm -> list Var;
  cps_fv_t : tm -> list Var;
  cps_fv_f : fm -> list Var;
  cps_sub_t : tm -> Var -> Var -> tm -> Prop;
  cps_sub_f : fm -> Var -> Var -> fm -> Prop;
  cps_alpha_t : tm -> tm -> Prop;
  cps_alpha_f : fm -> fm -> Prop;
  cps_axiom : fm -> Prop;
  cps_rule : list fm -> fm -> Prop;
  cps_provable : fm -> Prop;
  cps_model : Type;
  cps_legal : cps_model -> Prop;
  cps_eval_t : forall m : TarskiModel, Assignment m -> tm -> carrier m;
  cps_forces : forall m : TarskiModel, Assignment m -> fm -> Prop;
  cps_valid : fm -> Prop;
  cps_concrete_model : AdmModel;
  cps_semantic_nontrivial :
    forall rho : Assignment cps_concrete_model,
      cps_forces cps_concrete_model rho unit_tautology /\
      ~ cps_forces cps_concrete_model rho (FNeg unit_tautology);
  cps_substitution_lemma :
    forall (m : AdmModel) rho x y a b,
      cps_sub_f a x y b ->
      (cps_forces m rho b <->
       cps_forces m (update_assignment m rho x (rho y)) a);
  cps_alpha_sound :
    forall (m : AdmModel) rho a b,
      cps_alpha_f a b ->
      (cps_forces m rho a <-> cps_forces m rho b);
  cps_context_identity_sound :
    forall x y a b,
      cps_sub_f a x y b ->
      cps_valid (FImp (E_ctx x y a) (FIff a b));
  cps_soundness :
    forall a,
      cps_provable a ->
      cps_valid a
}.

Definition L_Ctx : ContextPenetratingSubstitutionSystem := {|
  cps_var_order := var_lt;
  cps_term := tm;
  cps_formula := fm;
  cps_var_occ_t := var_occ_t;
  cps_var_occ_f := var_occ_f;
  cps_fv_t := fv_t;
  cps_fv_f := fv_f;
  cps_sub_t := SubT;
  cps_sub_f := SubF;
  cps_alpha_t := AlphaT;
  cps_alpha_f := AlphaF;
  cps_axiom := Ax;
  cps_rule := Rule;
  cps_provable := Provable;
  cps_model := TarskiModel;
  cps_legal := TarskiLegal;
  cps_eval_t := eval_t;
  cps_forces := forces;
  cps_valid := AdmValid;
  cps_concrete_model := unit_admissible_model;
  cps_semantic_nontrivial := fun rho =>
    conj (unit_model_tautology_holds rho)
      (unit_model_negated_tautology_refuted rho);
  cps_substitution_lemma := substitution_lemma_formula;
  cps_alpha_sound := alpha_soundness_formula;
  cps_context_identity_sound := adm_valid_context_identity_axiom;
  cps_soundness := soundness
|}.

End ContextPenetratingSubstitution.
