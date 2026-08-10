From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Program.Equality.

Import ListNotations.

Unset Implicit Arguments.

Module RuleSetEnumerationBindingCalculus.

Inductive sort_name : Type :=
| SBase : nat -> nat -> sort_name
| SFormulaCode : nat -> sort_name
| SEnvironmentCode : nat -> sort_name
| SRuleSetCode : nat -> sort_name
| SBindingCode : nat -> sort_name.

Definition object_sort (k : nat) : sort_name := SBase k 0.

Definition sort_eq_dec : forall a b : sort_name, {a = b} + {a <> b}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition sort_eqb (a b : sort_name) : bool :=
  if sort_eq_dec a b then true else false.

Lemma sort_eqb_eq : forall a b, sort_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold sort_eqb.
  destruct (sort_eq_dec a b) as [H | H]; split; congruence.
Qed.

Definition sort_at (k : nat) (s : sort_name) : Prop :=
  match s with
  | SBase j _ => j = k
  | SFormulaCode i => i < k
  | SEnvironmentCode i => i < k
  | SRuleSetCode i => i < k
  | SBindingCode i => i < k
  end.

Lemma object_sort_at : forall k, sort_at k (object_sort k).
Proof. intros k; reflexivity. Qed.

Lemma formula_code_at_succ : forall k, sort_at (S k) (SFormulaCode k).
Proof. intros k; simpl; lia. Qed.

Lemma environment_code_at_succ : forall k, sort_at (S k) (SEnvironmentCode k).
Proof. intros k; simpl; lia. Qed.

Lemma ruleset_code_at_succ : forall k, sort_at (S k) (SRuleSetCode k).
Proof. intros k; simpl; lia. Qed.

Lemma binding_code_at_succ : forall k, sort_at (S k) (SBindingCode k).
Proof. intros k; simpl; lia. Qed.

Lemma current_formula_code_not_sort : forall k, ~ sort_at k (SFormulaCode k).
Proof. intros k H; simpl in H; lia. Qed.

Lemma current_environment_code_not_sort : forall k, ~ sort_at k (SEnvironmentCode k).
Proof. intros k H; simpl in H; lia. Qed.

Lemma current_ruleset_code_not_sort : forall k, ~ sort_at k (SRuleSetCode k).
Proof. intros k H; simpl in H; lia. Qed.

Lemma current_binding_code_not_sort : forall k, ~ sort_at k (SBindingCode k).
Proof. intros k H; simpl in H; lia. Qed.

Lemma ruleset_code_ne_object : forall k, SRuleSetCode k <> object_sort k.
Proof. intros k H; discriminate H. Qed.

Lemma binding_code_ne_object : forall k, SBindingCode k <> object_sort k.
Proof. intros k H; discriminate H. Qed.

Definition var_id : Type := (sort_name * nat)%type.

Definition var_eq_dec : forall a b : var_id, {a = b} + {a <> b}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply sort_eq_dec.
Defined.

Definition var_eqb (a b : var_id) : bool :=
  if var_eq_dec a b then true else false.

Lemma var_eqb_eq : forall a b, var_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold var_eqb.
  destruct (var_eq_dec a b) as [H | H]; split; congruence.
Qed.

Fixpoint in_varb (x : var_id) (xs : list var_id) : bool :=
  match xs with
  | [] => false
  | y :: ys => if var_eqb x y then true else in_varb x ys
  end.

Fixpoint remove_var (x : var_id) (xs : list var_id) : list var_id :=
  match xs with
  | [] => []
  | y :: ys =>
      if var_eqb x y then remove_var x ys else y :: remove_var x ys
  end.

Fixpoint max_index_for_sort (s : sort_name) (xs : list var_id) : nat :=
  match xs with
  | [] => 0
  | (s', i) :: ys =>
      let m := max_index_for_sort s ys in
      if sort_eqb s s' then Nat.max i m else m
  end.

Definition fresh_index (s : sort_name) (avoid : list var_id) : nat :=
  S (max_index_for_sort s avoid).

Lemma max_index_for_sort_ge :
  forall s i avoid,
    In (s, i) avoid -> i <= max_index_for_sort s avoid.
Proof.
  intros s i avoid.
  induction avoid as [| [s' j] rest IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst.
      unfold sort_eqb.
      destruct (sort_eq_dec s s) as [_ | Hneq]; [lia | contradiction].
    + specialize (IH Hin).
      destruct (sort_eqb s s'); lia.
Qed.

Lemma fresh_index_avoids_var :
  forall s i avoid,
    In (s, i) avoid -> fresh_index s avoid <> i.
Proof.
  intros s i avoid Hin Heq.
  unfold fresh_index in Heq.
  pose proof (max_index_for_sort_ge s i avoid Hin).
  lia.
Qed.

Section Calculus.

Variable FunctionSymbol : nat -> Type.
Variable fun_dom : forall k, FunctionSymbol k -> list sort_name.
Variable fun_cod : forall k, FunctionSymbol k -> sort_name.

Variable PredicateSymbol : nat -> Type.
Variable pred_dom : forall k, PredicateSymbol k -> list sort_name.

Variable Rule : nat -> Type.
Variable n_rules : nat -> nat.
Variable rule_name : forall k, nat -> Rule k.

Hypothesis rule_name_injective_on_space :
  forall k i j,
    i < n_rules k ->
    j < n_rules k ->
    rule_name k i = rule_name k j ->
    i = j.

Inductive term : nat -> sort_name -> Type :=
| TVar :
    forall k s, sort_at k s -> nat -> term k s
| TFun :
    forall k (F : FunctionSymbol k),
      term_tuple k (@fun_dom k F) -> term k (@fun_cod k F)
| TQuoteFormula :
    forall k i, i < k -> formula i -> term k (SFormulaCode i)
| TQuoteEnvironment :
    forall k i, i < k -> environment i -> term k (SEnvironmentCode i)
| TQuoteRuleSet :
    forall k i, i < k -> finite_ruleset i -> term k (SRuleSetCode i)
| TBinding :
    forall k i,
      i < k ->
      term k (SFormulaCode i) ->
      term k (SEnvironmentCode i) ->
      term k (SRuleSetCode i) ->
      term k (SBindingCode i)
with term_tuple : nat -> list sort_name -> Type :=
| TTnil : forall k, term_tuple k []
| TTcons :
    forall k s ss,
      term k s -> term_tuple k ss -> term_tuple k (s :: ss)
with formula : nat -> Type :=
| FPred :
    forall k (P : PredicateSymbol k),
      term_tuple k (@pred_dom k P) -> formula k
| FEq :
    forall k s, term k s -> term k s -> formula k
| FNeg : forall k, formula k -> formula k
| FAnd : forall k, formula k -> formula k -> formula k
| FForall :
    forall k s, sort_at k s -> nat -> formula k -> formula k
with environment : nat -> Type :=
| Env : forall k, list (env_entry k) -> environment k
with env_entry : nat -> Type :=
| EnvEntry :
    forall k s, sort_at k s -> nat -> term k s -> env_entry k
with finite_ruleset : nat -> Type :=
| RuleSet : forall k, list (Rule k) -> finite_ruleset k.

Fixpoint free_term (k : nat) (s : sort_name) (t : term k s) {struct t}
  : list var_id :=
  match t with
  | TVar _ s _ i => [(s, i)]
  | TFun _ _ ts => free_tuple _ _ ts
  | TQuoteFormula _ _ _ _ => []
  | TQuoteEnvironment _ _ _ _ => []
  | TQuoteRuleSet _ _ _ _ => []
  | TBinding _ _ _ u v w =>
      free_term _ _ u ++ free_term _ _ v ++ free_term _ _ w
  end
with free_tuple (k : nat) (ss : list sort_name) (ts : term_tuple k ss)
  {struct ts} : list var_id :=
  match ts with
  | TTnil _ => []
  | TTcons _ _ _ t rest => free_term _ _ t ++ free_tuple _ _ rest
  end.

Fixpoint free_formula (k : nat) (A : formula k) {struct A} : list var_id :=
  match A with
  | FPred _ _ ts => free_tuple _ _ ts
  | FEq _ _ t u => free_term _ _ t ++ free_term _ _ u
  | FNeg _ B => free_formula _ B
  | FAnd _ B C => free_formula _ B ++ free_formula _ C
  | FForall _ s _ i B => remove_var (s, i) (free_formula _ B)
  end.

Definition entry_var (k : nat) (e : env_entry k) : var_id :=
  match e with
  | EnvEntry _ s _ i _ => (s, i)
  end.

Definition entry_closed (k : nat) (e : env_entry k) : Prop :=
  match e with
  | EnvEntry _ _ _ _ t => free_term _ _ t = []
  end.

Definition environment_entries (k : nat) (rho : environment k)
  : list (env_entry k) :=
  match rho with
  | Env _ entries => entries
  end.

Definition environment_ok (k : nat) (rho : environment k) : Prop :=
  Forall (entry_closed k) (environment_entries k rho).

Definition env_domain (k : nat) (rho : environment k) : list var_id :=
  map (entry_var k) (environment_entries k rho).

Definition open_variables (k : nat) (rho : environment k) (A : formula k)
  : list var_id :=
  filter (fun v => negb (in_varb v (env_domain k rho))) (free_formula k A).

Definition object_var (k x : nat) : var_id := (object_sort k, x).

Definition open_subset_object
    (k x : nat) (A : formula k) (rho : environment k) : bool :=
  forallb (fun v => var_eqb v (object_var k x)) (open_variables k rho A).

Definition cast_term
    (k : nat) {s t : sort_name} (H : s = t) (u : term k s)
  : term k t :=
  match H in _ = t' return term k t' with
  | eq_refl => u
  end.

Inductive subst_entry : Type :=
| SubstEntry :
    forall k s, sort_at k s -> nat -> term k s -> subst_entry.

Definition cast_term2
    {k1 k2 : nat} {s1 s2 : sort_name}
    (Hk : k1 = k2) (Hs : s1 = s2) (u : term k1 s1)
  : term k2 s2 :=
  match Hk in _ = k' return term k' s2 with
  | eq_refl => cast_term k1 Hs u
  end.

Definition subst_entry_var (e : subst_entry) : var_id :=
  match e with
  | SubstEntry _ s _ i _ => (s, i)
  end.

Fixpoint subst_domain (sigma : list subst_entry) : list var_id :=
  match sigma with
  | [] => []
  | e :: rest => subst_entry_var e :: subst_domain rest
  end.

Definition subst_entry_free (e : subst_entry) : list var_id :=
  match e with
  | SubstEntry _ _ _ _ t => free_term _ _ t
  end.

Fixpoint lookup_subst
    (k : nat) (s : sort_name) (i : nat) (sigma : list subst_entry)
  : option (term k s) :=
  match sigma with
  | [] => None
  | SubstEntry k' s' _ j t :: rest =>
      match Nat.eq_dec k' k with
      | left Hk =>
          match sort_eq_dec s' s with
          | left Hs =>
              if Nat.eqb i j
              then Some (cast_term2 Hk Hs t)
              else lookup_subst k s i rest
          | right _ => lookup_subst k s i rest
          end
      | right _ => lookup_subst k s i rest
      end
  end.

Fixpoint remove_subst_var
    (x : var_id) (sigma : list subst_entry)
  : list subst_entry :=
  match sigma with
  | [] => []
  | e :: rest =>
      if var_eqb x (subst_entry_var e)
      then remove_subst_var x rest
      else e :: remove_subst_var x rest
  end.

Fixpoint free_subst_terms (sigma : list subst_entry)
  : list var_id :=
  match sigma with
  | [] => []
  | e :: rest => subst_entry_free e ++ free_subst_terms rest
  end.

Definition subst_terms_contain
    (x : var_id) (sigma : list subst_entry) : bool :=
  in_varb x (free_subst_terms sigma).

Fixpoint subst_term_env
    (k : nat) (s : sort_name) (t : term k s)
    (sigma : list subst_entry) {struct t} : term k s :=
  match t with
  | TVar k s hs i =>
      match lookup_subst k s i sigma with
      | Some u => u
      | None => TVar k s hs i
      end
  | TFun k F ts => TFun k F (subst_tuple_env k (@fun_dom k F) ts sigma)
  | TQuoteFormula k i h A => TQuoteFormula k i h A
  | TQuoteEnvironment k i h rho => TQuoteEnvironment k i h rho
  | TQuoteRuleSet k i h R => TQuoteRuleSet k i h R
  | TBinding k i h u v w =>
      TBinding k i h
        (subst_term_env k (SFormulaCode i) u sigma)
        (subst_term_env k (SEnvironmentCode i) v sigma)
        (subst_term_env k (SRuleSetCode i) w sigma)
  end
with subst_tuple_env
    (k : nat) (ss : list sort_name) (ts : term_tuple k ss)
    (sigma : list subst_entry) {struct ts} : term_tuple k ss :=
  match ts with
  | TTnil k => TTnil k
  | TTcons k s ss t rest =>
      TTcons k s ss
        (subst_term_env k s t sigma)
        (subst_tuple_env k ss rest sigma)
  end.

Fixpoint subst_formula_env
    (k : nat) (A : formula k) (sigma : list subst_entry)
    {struct A} : formula k :=
  match A with
  | FPred k P ts => FPred k P (subst_tuple_env k (@pred_dom k P) ts sigma)
  | FEq k s t u =>
      FEq k s (subst_term_env k s t sigma) (subst_term_env k s u sigma)
  | FNeg k B => FNeg k (subst_formula_env k B sigma)
  | FAnd k B C =>
      FAnd k (subst_formula_env k B sigma) (subst_formula_env k C sigma)
  | FForall k s hs i B =>
      let x := (s, i) in
      let sigma' := remove_subst_var x sigma in
      if subst_terms_contain x sigma'
      then
        let z :=
          fresh_index s
            (free_formula k B ++ free_subst_terms sigma' ++
             subst_domain sigma' ++ [x]) in
        FForall k s hs z
          (subst_formula_env k B
            (SubstEntry k s hs i (TVar k s hs z) :: sigma'))
      else FForall k s hs i (subst_formula_env k B sigma')
  end.

Definition subst_term
    (k : nat) (s xsort : sort_name)
    (t : term k s) (x : nat) (u : term k xsort)
    (hx : sort_at k xsort) : term k s :=
  subst_term_env k s t [SubstEntry k xsort hx x u].

Definition subst_formula
    (k : nat) (xsort : sort_name)
    (A : formula k) (x : nat) (u : term k xsort)
    (hx : sort_at k xsort) : formula k :=
  subst_formula_env k A [SubstEntry k xsort hx x u].

Definition finite_rule_space (k : nat) : list (Rule k) :=
  map (rule_name k) (seq 0 (n_rules k)).

Variable Applicable :
  forall k, Rule k -> nat -> formula k -> environment k -> bool.

Definition fit_bool
    (k x : nat) (A : formula k) (rho : environment k) (r : Rule k)
  : bool :=
  open_subset_object k x A rho && Applicable k r x A rho.

Definition Fit
    (k x : nat) (A : formula k) (rho : environment k) (r : Rule k)
  : Prop :=
  In r (finite_rule_space k) /\
  open_subset_object k x A rho = true /\
  Applicable k r x A rho = true.

Definition enumerated_ruleset
    (k x : nat) (A : formula k) (rho : environment k)
  : finite_ruleset k :=
  RuleSet k (filter (fit_bool k x A rho) (finite_rule_space k)).

Definition empty_ruleset (k : nat) : finite_ruleset k := RuleSet k [].

Definition quote_formula (k : nat) (A : formula k)
  : term (S k) (SFormulaCode k) :=
  TQuoteFormula (S k) k (Nat.lt_succ_diag_r k) A.

Definition quote_environment (k : nat) (rho : environment k)
  : term (S k) (SEnvironmentCode k) :=
  TQuoteEnvironment (S k) k (Nat.lt_succ_diag_r k) rho.

Definition quote_ruleset (k : nat) (R : finite_ruleset k)
  : term (S k) (SRuleSetCode k) :=
  TQuoteRuleSet (S k) k (Nat.lt_succ_diag_r k) R.

Definition decode_formula
    (i k : nat) (h : i < k) (u : term k (SFormulaCode i))
  : option (formula i).
Proof.
  dependent destruction u; try (exact (Some f)); exact None.
Defined.

Definition decode_environment
    (i k : nat) (h : i < k) (u : term k (SEnvironmentCode i))
  : option (environment i).
Proof.
  dependent destruction u; try (exact (Some e)); exact None.
Defined.

Definition decode_ruleset
    (i k : nat) (h : i < k) (u : term k (SRuleSetCode i))
  : option (finite_ruleset i).
Proof.
  dependent destruction u; try (exact (Some f)); exact None.
Defined.

Definition enumerate
    (k x : nat)
    (u : term (S k) (SFormulaCode k))
    (v : term (S k) (SEnvironmentCode k))
  : term (S k) (SRuleSetCode k) :=
  match
    decode_formula k (S k) (Nat.lt_succ_diag_r k) u,
    decode_environment k (S k) (Nat.lt_succ_diag_r k) v
  with
  | Some A, Some rho => quote_ruleset k (enumerated_ruleset k x A rho)
  | _, _ => quote_ruleset k (empty_ruleset k)
  end.

Variable beta : forall k, nat -> formula k -> nat.

Hypothesis beta_injective :
  forall k x y (A B : formula k),
    beta k x A = beta k y B -> x = y /\ A = B.

Definition bullet_var (k x : nat) (A : formula k) : nat :=
  beta k x A.

Definition rho_bullet
    (k x : nat) (A : formula k) (rho : environment k)
  : environment (S k) :=
  Env (S k)
    [EnvEntry (S k) (SRuleSetCode k) (ruleset_code_at_succ k)
      (bullet_var k x A)
      (enumerate k x (quote_formula k A) (quote_environment k rho))].

Definition bound_state
    (k x : nat) (A : formula k) (rho : environment k)
  : term (S k) (SBindingCode k) :=
  TBinding (S k) k (Nat.lt_succ_diag_r k)
    (quote_formula k A)
    (quote_environment k rho)
    (enumerate k x (quote_formula k A) (quote_environment k rho)).

Definition enum_cert
    (k x : nat) (A : formula k) (rho : environment k)
    (sigma : list bool) : Prop :=
  length sigma = n_rules k /\
  forall i,
    i < n_rules k ->
    nth_error sigma i = Some true <->
    Fit k x A rho (rule_name k i).

Definition canonical_sigma
    (k x : nat) (A : formula k) (rho : environment k) : list bool :=
  map (fun i => fit_bool k x A rho (rule_name k i)) (seq 0 (n_rules k)).

Definition BindCert
    (k x : nat) (A : formula k) (rho : environment k)
    (B : term (S k) (SBindingCode k)) : Prop :=
  open_subset_object k x A rho = true /\
  exists sigma, enum_cert k x A rho sigma /\ B = bound_state k x A rho.

Definition derives_E
    (k x : nat) (A : formula k) (rho : environment k)
    (B : term (S k) (SBindingCode k)) : Prop :=
  BindCert k x A rho B.

Definition Bound_E (k : nat) : Type :=
  { xb : nat * formula k * environment k * term (S k) (SBindingCode k) |
    match xb with
    | (x, A, rho, B) => derives_E k x A rho B
    end }.

Lemma free_quote_formula_nil :
  forall k (A : formula k),
    free_term (S k) (SFormulaCode k) (quote_formula k A) = [].
Proof. reflexivity. Qed.

Lemma free_quote_environment_nil :
  forall k (rho : environment k),
    free_term (S k) (SEnvironmentCode k) (quote_environment k rho) = [].
Proof. reflexivity. Qed.

Lemma free_quote_ruleset_nil :
  forall k (R : finite_ruleset k),
    free_term (S k) (SRuleSetCode k) (quote_ruleset k R) = [].
Proof. reflexivity. Qed.

Lemma free_enumerate_nil :
  forall k x u v,
    free_term (S k) (SRuleSetCode k) (enumerate k x u v) = [].
Proof.
  intros k x u v.
  unfold enumerate.
  destruct (decode_formula k (S k) (Nat.lt_succ_diag_r k) u);
  destruct (decode_environment k (S k) (Nat.lt_succ_diag_r k) v);
  reflexivity.
Qed.

Theorem rho_bullet_is_environment_ok :
  forall k x A rho, environment_ok (S k) (rho_bullet k x A rho).
Proof.
  intros k x A rho.
  unfold environment_ok, rho_bullet, environment_entries.
  constructor.
  - reflexivity.
  - constructor.
Qed.

Theorem bound_state_has_binding_sort :
  forall k x A rho,
    exists B : term (S k) (SBindingCode k),
      B = bound_state k x A rho.
Proof.
  intros; eexists; reflexivity.
Qed.

Theorem binding_state_not_current_layer_object :
  forall k,
    sort_at (S k) (SBindingCode k) /\
    ~ sort_at k (SBindingCode k) /\
    SBindingCode k <> object_sort k.
Proof.
  intros k; split.
  - apply binding_code_at_succ.
  - split.
    + apply current_binding_code_not_sort.
    + apply binding_code_ne_object.
Qed.

Theorem ruleset_code_not_substitutable_for_object :
  forall k,
    sort_at (S k) (SRuleSetCode k) /\
    ~ sort_at k (SRuleSetCode k) /\
    SRuleSetCode k <> object_sort k.
Proof.
  intros k; split.
  - apply ruleset_code_at_succ.
  - split.
    + apply current_ruleset_code_not_sort.
    + apply ruleset_code_ne_object.
Qed.

Lemma canonical_sigma_length :
  forall k x A rho,
    length (canonical_sigma k x A rho) = n_rules k.
Proof.
  intros; unfold canonical_sigma; rewrite length_map, length_seq; reflexivity.
Qed.

Lemma finite_rule_space_contains_named_rule :
  forall k i,
    i < n_rules k -> In (rule_name k i) (finite_rule_space k).
Proof.
  intros k i Hi.
  unfold finite_rule_space.
  apply in_map.
  apply in_seq.
  lia.
Qed.

Lemma canonical_sigma_is_enum_cert :
  forall k x A rho,
    enum_cert k x A rho (canonical_sigma k x A rho).
Proof.
  intros k x A rho.
  split.
  - apply canonical_sigma_length.
  - intros i Hi.
    unfold canonical_sigma.
    rewrite nth_error_map.
    rewrite nth_error_seq by lia.
    replace (i <? n_rules k) with true by
      (symmetry; apply Nat.ltb_lt; exact Hi).
    simpl.
    unfold Fit, fit_bool.
    split; intros H.
    + injection H as Hfit.
      apply andb_true_iff in Hfit as [Hopen Happ].
      repeat split.
      * apply finite_rule_space_contains_named_rule. exact Hi.
      * exact Hopen.
      * exact Happ.
    + destruct H as [_ [Hopen Happ]].
      rewrite Hopen, Happ.
      reflexivity.
Qed.

Theorem bind_cert_iff_bound_state :
  forall k x A rho B,
    BindCert k x A rho B <->
    open_subset_object k x A rho = true /\ B = bound_state k x A rho.
Proof.
  intros k x A rho B.
  split.
  - intros [Hopen [_ [_ HB]]].
    split; assumption.
  - intros [Hopen HB].
    split.
    + exact Hopen.
    + exists (canonical_sigma k x A rho).
      split.
      * apply canonical_sigma_is_enum_cert.
      * exact HB.
Qed.

Lemma filter_rule_fit :
  forall k x A rho r,
    In r (filter (fit_bool k x A rho) (finite_rule_space k)) <->
    Fit k x A rho r.
Proof.
  intros k x A rho r.
  unfold Fit, finite_rule_space.
  rewrite filter_In.
  unfold fit_bool.
  rewrite andb_true_iff.
  tauto.
Qed.

Definition rejected_binding_variable (k : nat) :
    term (S k) (SBindingCode k) :=
  TVar (S k) (SBindingCode k) (binding_code_at_succ k) 0.

Theorem binding_semantics_nontrivial :
  forall k x (A : formula k) (rho : environment k),
    open_subset_object k x A rho = true ->
    derives_E k x A rho (bound_state k x A rho) /\
    ~ derives_E k x A rho (rejected_binding_variable k).
Proof.
  intros k x A rho Hopen.
  split.
  - apply (proj2 (bind_cert_iff_bound_state
      k x A rho (bound_state k x A rho))).
    split; [exact Hopen | reflexivity].
  - intro Hbad.
    apply (proj1 (bind_cert_iff_bound_state
      k x A rho (rejected_binding_variable k))) in Hbad.
    destruct Hbad as [_ Heq].
    unfold rejected_binding_variable, bound_state in Heq.
    discriminate Heq.
Qed.
Record formal_system : Type := {
  fs_Bound_E : forall k : nat, Type;
  fs_derives_E :
    forall (k x : nat) (A : formula k) (rho : environment k)
      (B : term (S k) (SBindingCode k)), Prop;
  fs_derives_is_bindcert :
    forall (k x : nat) A rho B,
      fs_derives_E k x A rho B <-> BindCert k x A rho B;
  fs_bindcert_characterization :
    forall (k x : nat) A rho B,
      BindCert k x A rho B <->
      open_subset_object k x A rho = true /\ B = bound_state k x A rho;
  fs_ruleset_code_separation :
    forall k : nat,
      sort_at (S k) (SRuleSetCode k) /\
      ~ sort_at k (SRuleSetCode k) /\
      SRuleSetCode k <> object_sort k;
  fs_semantic_nontriviality :
    forall k x (A : formula k) (rho : environment k),
      open_subset_object k x A rho = true ->
      fs_derives_E k x A rho (bound_state k x A rho) /\
      ~ fs_derives_E k x A rho (rejected_binding_variable k);
  fs_binding_code_separation :
    forall k : nat,
      sort_at (S k) (SBindingCode k) /\
      ~ sort_at k (SBindingCode k) /\
      SBindingCode k <> object_sort k
}.

Definition canonical_formal_system : formal_system := {|
  fs_Bound_E := Bound_E;
  fs_derives_E := derives_E;
  fs_derives_is_bindcert := fun k x A rho B => iff_refl _;
  fs_bindcert_characterization := bind_cert_iff_bound_state;
  fs_ruleset_code_separation := ruleset_code_not_substitutable_for_object;
  fs_semantic_nontriviality := binding_semantics_nontrivial;
  fs_binding_code_separation := binding_state_not_current_layer_object
|}.

End Calculus.

End RuleSetEnumerationBindingCalculus.
