Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

Import ListNotations.

Module SecondOrderExistentialGraphOriginalFaithful.

Inductive term : Type :=
| TVar : nat -> term.

Definition relvar : Type := nat * nat.

Inductive formula : Type :=
| FTop : formula
| FPred : nat -> nat -> list term -> formula
| FEq : term -> term -> formula
| FRVar : nat -> nat -> list term -> formula
| FAnd : formula -> formula -> formula
| FNeg : formula -> formula
| FExistsI : nat -> formula -> formula
| FExistsR : nat -> nat -> formula -> formula.

Definition FBot : formula := FNeg FTop.
Definition FOr (phi psi : formula) : formula :=
  FNeg (FAnd (FNeg phi) (FNeg psi)).
Definition FImp (phi psi : formula) : formula :=
  FNeg (FAnd phi (FNeg psi)).
Definition FIff (phi psi : formula) : formula :=
  FAnd (FImp phi psi) (FImp psi phi).
Definition FForallI (x : nat) (phi : formula) : formula :=
  FNeg (FExistsI x (FNeg phi)).
Definition FForallR (ar X : nat) (phi : formula) : formula :=
  FNeg (FExistsR ar X (FNeg phi)).

Fixpoint wf_formula (phi : formula) : Prop :=
  match phi with
  | FTop => True
  | FPred ar _ ts => length ts = ar
  | FEq _ _ => True
  | FRVar ar _ ts => length ts = ar
  | FAnd phi psi => wf_formula phi /\ wf_formula psi
  | FNeg phi => wf_formula phi
  | FExistsI _ phi => wf_formula phi
  | FExistsR _ _ phi => wf_formula phi
  end.

Inductive expression_graph : Type :=
| EGTop : expression_graph
| EGSpot : nat -> nat -> list term -> expression_graph
| EGEqLine : term -> term -> expression_graph
| EGRelApp : nat -> nat -> list term -> expression_graph
| EGConj : expression_graph -> expression_graph -> expression_graph
| EGCut : expression_graph -> expression_graph
| EGIBox : nat -> expression_graph -> expression_graph
| EGRBox : nat -> nat -> expression_graph -> expression_graph.

Fixpoint expression_graph_formula (E : expression_graph) : formula :=
  match E with
  | EGTop => FTop
  | EGSpot ar P ts => FPred ar P ts
  | EGEqLine t u => FEq t u
  | EGRelApp ar X ts => FRVar ar X ts
  | EGConj E1 E2 =>
      FAnd (expression_graph_formula E1) (expression_graph_formula E2)
  | EGCut E1 => FNeg (expression_graph_formula E1)
  | EGIBox x E1 => FExistsI x (expression_graph_formula E1)
  | EGRBox ar X E1 => FExistsR ar X (expression_graph_formula E1)
  end.

Fixpoint expression_graph_wf (E : expression_graph) : Prop :=
  match E with
  | EGTop => True
  | EGSpot ar _ ts => length ts = ar
  | EGEqLine _ _ => True
  | EGRelApp ar _ ts => length ts = ar
  | EGConj E1 E2 => expression_graph_wf E1 /\ expression_graph_wf E2
  | EGCut E1 => expression_graph_wf E1
  | EGIBox _ E1 => expression_graph_wf E1
  | EGRBox _ _ E1 => expression_graph_wf E1
  end.

Fixpoint formula_to_expression_graph (phi : formula) : expression_graph :=
  match phi with
  | FTop => EGTop
  | FPred ar P ts => EGSpot ar P ts
  | FEq t u => EGEqLine t u
  | FRVar ar X ts => EGRelApp ar X ts
  | FAnd phi psi =>
      EGConj (formula_to_expression_graph phi)
        (formula_to_expression_graph psi)
  | FNeg phi => EGCut (formula_to_expression_graph phi)
  | FExistsI x phi => EGIBox x (formula_to_expression_graph phi)
  | FExistsR ar X phi => EGRBox ar X (formula_to_expression_graph phi)
  end.

Theorem formula_to_expression_graph_formula :
  forall phi,
    expression_graph_formula (formula_to_expression_graph phi) = phi.
Proof.
  induction phi; simpl; congruence.
Qed.

Theorem formula_to_expression_graph_wf :
  forall phi,
    wf_formula phi ->
    expression_graph_wf (formula_to_expression_graph phi).
Proof.
  induction phi; simpl; intuition.
Qed.

Definition example_free_variable_equality (x y : nat) : formula :=
  FEq (TVar x) (TVar y).

Theorem example_free_variable_equality_wf :
  forall x y, wf_formula (example_free_variable_equality x y).
Proof.
  intros x y. exact I.
Qed.

Definition example_local_equality (x y z : nat) : formula :=
  FAnd (FEq (TVar x) (TVar y)) (FNeg (FEq (TVar x) (TVar z))).

Theorem example_local_equality_wf :
  forall x y z, wf_formula (example_local_equality x y z).
Proof.
  intros x y z. simpl. split; exact I.
Qed.

Definition example_existential_equality (P x y : nat) : formula :=
  FExistsI x
    (FAnd
      (FPred 1 P [TVar x])
      (FEq (TVar x) (TVar y))).

Theorem example_existential_equality_wf :
  forall P x y, wf_formula (example_existential_equality P x y).
Proof.
  intros P x y. simpl. split; [reflexivity | exact I].
Qed.

Inductive formula_rule : formula -> formula -> Prop :=
| FormulaRuleRefl :
    forall phi, formula_rule phi phi
| FormulaRuleEq :
    forall phi psi, phi = psi -> formula_rule phi psi
| FormulaRuleTopIntro :
    forall phi, formula_rule phi FTop
| FormulaRuleDoubleNegIntro :
    forall phi, formula_rule phi (FNeg (FNeg phi))
| FormulaRuleAndElimLeft :
    forall phi psi, formula_rule (FAnd phi psi) phi
| FormulaRuleAndElimRight :
    forall phi psi, formula_rule (FAnd phi psi) psi
| FormulaRuleAndIntroIdem :
    forall phi, formula_rule phi (FAnd phi phi).

Inductive boundary : Type :=
| BCut : boundary
| BIBox : boundary
| BRBox : nat -> boundary.

Record raw_graph : Type := {
  Region : Type;
  Object : Type;
  VarLine : Type;
  EqLine : Type;
  Spot : Type;
  Pen : Type;
  App : Type;

  regions : list Region;
  root : Region;
  le_region : Region -> Region -> Prop;
  bd : Region -> option boundary;
  children : Region -> list Region;
  region_rank : Region -> nat;

  objects : list Object;
  object_region : Object -> Region;
  object_line : Object -> VarLine;

  varlines : list VarLine;
  line_binder : VarLine -> option Region;
  ibox_line : Region -> option VarLine;
  ibox_attach : Region -> option Object;

  eqlines : list EqLine;
  eq_region : EqLine -> Region;
  eq_left : EqLine -> Object;
  eq_right : EqLine -> Object;

  spots : list Spot;
  spots_at : Region -> list Spot;
  spot_region : Spot -> Region;
  spot_symbol : Spot -> nat * nat;
  spot_args : Spot -> list Object;

  pens : list Pen;
  pen_arity : Pen -> nat;

  apps : list App;
  apps_at : Region -> list App;
  app_region : App -> Region;
  app_pen : App -> Pen;
  app_args : App -> list Object;
  app_binder : App -> option Region;

  rbox_anchor : Region -> option Pen;

  eqlines_at : Region -> list EqLine;

  eta_i_free : VarLine -> nat;
  eta_i_bound : Region -> nat;
  eta_r_free : Pen -> nat;
  eta_r_bound : Region -> nat
}.

Definition is_ibox (G : raw_graph) (b : Region G) : Prop :=
  bd G b = Some BIBox.

Definition is_rbox (G : raw_graph) (c : Region G) (ar : nat) : Prop :=
  bd G c = Some (BRBox ar).

Definition bound_var_line (G : raw_graph) (delta : VarLine G) : Prop :=
  exists b,
    In b (regions G) /\
    is_ibox G b /\
    ibox_line G b = Some delta.

Definition free_var_line (G : raw_graph) (delta : VarLine G) : Prop :=
  In delta (varlines G) /\ ~ bound_var_line G delta.

Definition RelationCandidate (G : raw_graph) (q : App G) (c : Region G) : Prop :=
  In q (apps G) /\
  In c (regions G) /\
  exists ar,
    is_rbox G c ar /\
    le_region G (app_region G q) c /\
    rbox_anchor G c = Some (app_pen G q) /\
    pen_arity G (app_pen G q) = ar.

Definition NearestRelationBinder (G : raw_graph) (q : App G) (c : Region G) : Prop :=
  RelationCandidate G q c /\
  forall d, RelationCandidate G q d -> le_region G c d.

Definition term_of_object (G : raw_graph) (p : Object G) : term :=
  match line_binder G (object_line G p) with
  | Some b => TVar (eta_i_bound G b)
  | None => TVar (eta_i_free G (object_line G p))
  end.

Definition relation_name_of_app (G : raw_graph) (q : App G) : nat :=
  match app_binder G q with
  | Some c => eta_r_bound G c
  | None => eta_r_free G (app_pen G q)
  end.

Definition name_of_term (t : term) : nat :=
  match t with
  | TVar x => x
  end.

Inductive individual_name_source
    (G : raw_graph) (p : Object G) : nat -> Prop :=
| IndividualNameFromFreeLine :
    line_binder G (object_line G p) = None ->
    individual_name_source G p (eta_i_free G (object_line G p))
| IndividualNameFromIBox :
    forall b,
      line_binder G (object_line G p) = Some b ->
      is_ibox G b ->
      individual_name_source G p (eta_i_bound G b).

Inductive relation_name_source
    (G : raw_graph) (q : App G) : nat -> Prop :=
| RelationNameFromFreePen :
    app_binder G q = None ->
    In (app_pen G q) (pens G) ->
    relation_name_source G q (eta_r_free G (app_pen G q))
| RelationNameFromRBox :
    forall c ar,
      app_binder G q = Some c ->
      is_rbox G c ar ->
      pen_arity G (app_pen G q) = ar ->
      relation_name_source G q (eta_r_bound G c).

Definition spot_formula (G : raw_graph) (s : Spot G) : formula :=
  let '(ar, P) := spot_symbol G s in
  FPred ar P (map (term_of_object G) (spot_args G s)).

Definition eqline_formula (G : raw_graph) (e : EqLine G) : formula :=
  FEq (term_of_object G (eq_left G e)) (term_of_object G (eq_right G e)).

Definition app_formula (G : raw_graph) (q : App G) : formula :=
  FRVar
    (pen_arity G (app_pen G q))
    (relation_name_of_app G q)
    (map (term_of_object G) (app_args G q)).

Fixpoint conjoin_from (acc : formula) (fs : list formula) : formula :=
  match fs with
  | [] => acc
  | phi :: rest => conjoin_from (FAnd acc phi) rest
  end.

Definition conjoin (fs : list formula) : formula :=
  match fs with
  | [] => FTop
  | phi :: rest => conjoin_from phi rest
  end.

Definition boundary_wrap
    (G : raw_graph) (inside : Region G -> formula) (b : Region G) : formula :=
  match bd G b with
  | Some BCut => FNeg (inside b)
  | Some BIBox => FExistsI (eta_i_bound G b) (inside b)
  | Some (BRBox ar) => FExistsR ar (eta_r_bound G b) (inside b)
  | None => inside b
  end.

Fixpoint region_formula_fuel
    (G : raw_graph) (fuel : nat) (a : Region G) : formula :=
  match fuel with
  | 0 => FTop
  | S fuel' =>
      conjoin
        (map (spot_formula G) (spots_at G a) ++
         map (eqline_formula G) (eqlines_at G a) ++
         map (app_formula G) (apps_at G a) ++
         map (boundary_wrap G (region_formula_fuel G fuel')) (children G a))
  end.

Definition tau (G : raw_graph) : formula :=
  region_formula_fuel G (S (region_rank G (root G))) (root G).

Record WellFormedGraph (G : raw_graph) : Prop := {
  wf_regions_nodup : NoDup (regions G);
  wf_root_region : In (root G) (regions G);
  wf_root_boundary : bd G (root G) = None;
  wf_nonroot_boundary :
    forall a, In a (regions G) -> a <> root G -> exists b, bd G a = Some b;
  wf_boundary_region :
    forall a b, bd G a = Some b -> In a (regions G) /\ a <> root G;
  wf_region_refl :
    forall a, In a (regions G) -> le_region G a a;
  wf_region_trans :
    forall a b c,
      In a (regions G) -> In b (regions G) -> In c (regions G) ->
      le_region G a b -> le_region G b c -> le_region G a c;
  wf_region_antisym :
    forall a b,
      In a (regions G) -> In b (regions G) ->
      le_region G a b -> le_region G b a -> a = b;
  wf_root_max :
    forall a, In a (regions G) -> le_region G a (root G);
  wf_ancestor_linear :
    forall a b c,
      In a (regions G) -> In b (regions G) -> In c (regions G) ->
      le_region G c a -> le_region G c b ->
      le_region G a b \/ le_region G b a;
  wf_child_region :
    forall a b,
      In b (children G a) ->
      In a (regions G) /\ In b (regions G) /\ le_region G b a /\ b <> a;
  wf_child_rank_decreases :
    forall a b,
      In b (children G a) ->
      region_rank G b < region_rank G a;

  wf_objects_region :
    forall p, In p (objects G) -> In (object_region G p) (regions G);
  wf_objects_line :
    forall p, In p (objects G) -> In (object_line G p) (varlines G);

  wf_line_binder_some :
    forall delta b,
      In delta (varlines G) ->
      line_binder G delta = Some b ->
      In b (regions G) /\ is_ibox G b /\ ibox_line G b = Some delta;
  wf_line_binder_none :
    forall delta,
      In delta (varlines G) ->
      line_binder G delta = None ->
      ~ bound_var_line G delta;
  wf_ibox_line_some :
    forall b delta,
      is_ibox G b ->
      ibox_line G b = Some delta ->
      In delta (varlines G) /\ line_binder G delta = Some b;
  wf_ibox_attach :
    forall b p,
      is_ibox G b ->
      ibox_attach G b = Some p ->
      In p (objects G) /\
      object_region G p = b /\
      ibox_line G b = Some (object_line G p);
  wf_bound_line_no_escape :
    forall b delta p,
      is_ibox G b ->
      ibox_line G b = Some delta ->
      In p (objects G) ->
      object_line G p = delta ->
      le_region G (object_region G p) b;

  wf_eqline_region :
    forall e, In e (eqlines G) -> In (eq_region G e) (regions G);
  wf_eqline_left :
    forall e, In e (eqlines G) -> In (eq_left G e) (objects G);
  wf_eqline_right :
    forall e, In e (eqlines G) -> In (eq_right G e) (objects G);
  wf_eqline_local_left :
    forall e, In e (eqlines G) -> object_region G (eq_left G e) = eq_region G e;
  wf_eqline_local_right :
    forall e, In e (eqlines G) -> object_region G (eq_right G e) = eq_region G e;
  wf_eqlines_at :
    forall a e, In e (eqlines_at G a) -> In e (eqlines G) /\ eq_region G e = a;

  wf_spot_region :
    forall s, In s (spots G) -> In (spot_region G s) (regions G);
  wf_spot_args_in_objects :
    forall s p, In s (spots G) -> In p (spot_args G s) -> In p (objects G);
  wf_spot_args_local :
    forall s p, In s (spots G) -> In p (spot_args G s) ->
      object_region G p = spot_region G s;
  wf_spot_args_length :
    forall s, In s (spots G) -> length (spot_args G s) = fst (spot_symbol G s);
  wf_spots_at :
    forall a s, In s (spots_at G a) -> In s (spots G) /\ spot_region G s = a;

  wf_app_region :
    forall q, In q (apps G) -> In (app_region G q) (regions G);
  wf_app_pen :
    forall q, In q (apps G) -> In (app_pen G q) (pens G);
  wf_app_args_in_objects :
    forall q p, In q (apps G) -> In p (app_args G q) -> In p (objects G);
  wf_app_args_local :
    forall q p, In q (apps G) -> In p (app_args G q) ->
      object_region G p = app_region G q;
  wf_app_args_length :
    forall q, In q (apps G) ->
      length (app_args G q) = pen_arity G (app_pen G q);
  wf_apps_at :
    forall a q, In q (apps_at G a) -> In q (apps G) /\ app_region G q = a;

  wf_rbox_anchor :
    forall c ar pi,
      is_rbox G c ar ->
      rbox_anchor G c = Some pi ->
      In pi (pens G) /\ pen_arity G pi = ar;
  wf_app_binder_some :
    forall q c,
      In q (apps G) ->
      app_binder G q = Some c ->
      NearestRelationBinder G q c;
  wf_app_binder_none :
    forall q,
      In q (apps G) ->
      app_binder G q = None ->
      forall c, ~ RelationCandidate G q c;

  wf_eta_i_free_injective :
    forall delta epsilon,
      free_var_line G delta -> free_var_line G epsilon ->
      eta_i_free G delta = eta_i_free G epsilon -> delta = epsilon;
  wf_eta_i_bound_injective :
    forall b c,
      is_ibox G b -> is_ibox G c ->
      eta_i_bound G b = eta_i_bound G c -> b = c;
  wf_eta_i_free_bound_disjoint :
    forall delta b,
      free_var_line G delta -> is_ibox G b ->
      eta_i_free G delta <> eta_i_bound G b;

  wf_eta_r_free_same_arity_injective :
    forall pi rho,
      In pi (pens G) -> In rho (pens G) ->
      pen_arity G pi = pen_arity G rho ->
      eta_r_free G pi = eta_r_free G rho -> pi = rho;
  wf_eta_r_bound_same_arity_injective :
    forall b c ar,
      is_rbox G b ar -> is_rbox G c ar ->
      eta_r_bound G b = eta_r_bound G c -> b = c;
  wf_eta_r_free_bound_disjoint :
    forall pi c ar,
      In pi (pens G) -> is_rbox G c ar ->
      pen_arity G pi = ar ->
      eta_r_free G pi <> eta_r_bound G c
}.

Lemma wf_conjoin_from :
  forall acc fs,
    wf_formula acc ->
    Forall wf_formula fs ->
    wf_formula (conjoin_from acc fs).
Proof.
  intros acc fs Hacc Hfs.
  revert acc Hacc.
  induction Hfs as [| phi fs Hphi Hfs IH]; intros acc Hacc; simpl.
  - exact Hacc.
  - apply IH. split; assumption.
Qed.

Lemma wf_conjoin :
  forall fs, Forall wf_formula fs -> wf_formula (conjoin fs).
Proof.
  intros fs Hfs.
  destruct Hfs as [| phi fs Hphi Hrest].
  - exact I.
  - apply wf_conjoin_from; assumption.
Qed.

Lemma Forall_app_intro :
  forall (A : Type) (P : A -> Prop) xs ys,
    Forall P xs -> Forall P ys -> Forall P (xs ++ ys).
Proof.
  intros A P xs ys Hxs Hys.
  induction Hxs as [| x xs Hx Hxs IH]; simpl.
  - exact Hys.
  - constructor; auto.
Qed.

Lemma Forall_map_in :
  forall (A B : Type) (P : B -> Prop) (f : A -> B) xs,
    (forall x, In x xs -> P (f x)) ->
    Forall P (map f xs).
Proof.
  intros A B P f xs H.
  induction xs as [| x xs IH]; simpl.
  - constructor.
  - constructor.
    + apply H. simpl; auto.
    + apply IH. intros y Hy. apply H. simpl; auto.
Qed.

Lemma spot_formula_wf :
  forall G, WellFormedGraph G ->
  forall s, In s (spots G) -> wf_formula (spot_formula G s).
Proof.
  intros G W s Hs.
  unfold spot_formula.
  destruct (spot_symbol G s) as [ar P] eqn:Hsym.
  simpl. rewrite length_map.
  pose proof (wf_spot_args_length G W s Hs) as Hlen.
  rewrite Hsym in Hlen. simpl in Hlen. exact Hlen.
Qed.

Lemma eqline_formula_wf :
  forall G, WellFormedGraph G ->
  forall e, In e (eqlines G) -> wf_formula (eqline_formula G e).
Proof.
  intros G W e He. unfold eqline_formula. exact I.
Qed.

Lemma app_formula_wf :
  forall G, WellFormedGraph G ->
  forall q, In q (apps G) -> wf_formula (app_formula G q).
Proof.
  intros G W q Hq.
  unfold app_formula. simpl. rewrite length_map.
  exact (wf_app_args_length G W q Hq).
Qed.

Lemma region_formula_fuel_wf :
  forall G, WellFormedGraph G ->
  forall fuel a, wf_formula (region_formula_fuel G fuel a).
Proof.
  intros G W fuel.
  induction fuel as [| fuel IH]; intro a; simpl.
  - exact I.
  - apply wf_conjoin.
    repeat apply Forall_app_intro.
    + apply Forall_map_in. intros s Hs.
      apply spot_formula_wf.
      * exact W.
      * exact (proj1 (wf_spots_at G W a s Hs)).
    + apply Forall_map_in. intros e He.
      apply eqline_formula_wf.
      * exact W.
      * exact (proj1 (wf_eqlines_at G W a e He)).
    + apply Forall_map_in. intros q Hq.
      apply app_formula_wf.
      * exact W.
      * exact (proj1 (wf_apps_at G W a q Hq)).
    + apply Forall_map_in. intros b Hb.
      unfold boundary_wrap.
      destruct (bd G b) as [[| | ar] |]; simpl; auto.
Qed.

Theorem tau_well_formed :
  forall G, WellFormedGraph G -> wf_formula (tau G).
Proof.
  intros G W. unfold tau. apply region_formula_fuel_wf. exact W.
Qed.

Theorem relation_candidate_has_typed_anchor :
  forall G q c,
    RelationCandidate G q c ->
    exists ar,
      is_rbox G c ar /\
      rbox_anchor G c = Some (app_pen G q) /\
      pen_arity G (app_pen G q) = ar.
Proof.
  intros G q c H.
  destruct H as [_ [_ [ar [Hrbox [_ [Hanchor Har]]]]]].
  exists ar. repeat split; assumption.
Qed.

Theorem nearest_relation_binder_unique :
  forall G, WellFormedGraph G ->
  forall q c d,
    NearestRelationBinder G q c ->
    NearestRelationBinder G q d ->
    c = d.
Proof.
  intros G W q c d Hc Hd.
  destruct Hc as [Hcandc Hminc].
  destruct Hd as [Hcandd Hmind].
  assert (Hcin : In c (regions G)) by
    (destruct Hcandc as [_ [Hcin _]]; exact Hcin).
  assert (Hdin : In d (regions G)) by
    (destruct Hcandd as [_ [Hdin _]]; exact Hdin).
  eapply wf_region_antisym.
  - exact W.
  - exact Hcin.
  - exact Hdin.
  - apply Hminc. exact Hcandd.
  - apply Hmind. exact Hcandc.
Qed.

Theorem app_binder_some_is_nearest :
  forall G, WellFormedGraph G ->
  forall q c,
    In q (apps G) ->
    app_binder G q = Some c ->
    NearestRelationBinder G q c.
Proof.
  intros G W q c Hq Hb.
  exact (wf_app_binder_some G W q c Hq Hb).
Qed.

Theorem app_binder_none_has_no_candidate :
  forall G, WellFormedGraph G ->
  forall q,
    In q (apps G) ->
    app_binder G q = None ->
    forall c, ~ RelationCandidate G q c.
Proof.
  intros G W q Hq Hb c.
  exact (wf_app_binder_none G W q Hq Hb c).
Qed.

Theorem term_of_object_name_has_source :
  forall G, WellFormedGraph G ->
  forall p,
    In p (objects G) ->
    individual_name_source G p (name_of_term (term_of_object G p)).
Proof.
  intros G W p Hp.
  unfold term_of_object, name_of_term.
  destruct (line_binder G (object_line G p)) as [b |] eqn:Hbinder.
  - pose proof (wf_objects_line G W p Hp) as Hline.
    pose proof
      (wf_line_binder_some G W (object_line G p) b Hline Hbinder)
      as [_ [Hibox _]].
    apply IndividualNameFromIBox with (b := b).
    + exact Hbinder.
    + exact Hibox.
  - apply IndividualNameFromFreeLine. exact Hbinder.
Qed.

Theorem relation_name_of_app_has_source :
  forall G, WellFormedGraph G ->
  forall q,
    In q (apps G) ->
    relation_name_source G q (relation_name_of_app G q).
Proof.
  intros G W q Hq.
  unfold relation_name_of_app.
  destruct (app_binder G q) as [c |] eqn:Hbinder.
  - pose proof (wf_app_binder_some G W q c Hq Hbinder) as Hnear.
    destruct Hnear as [Hcand _].
    destruct Hcand as [_ [_ [ar [Hrbox [_ [_ Har]]]]]].
    apply RelationNameFromRBox with (c := c) (ar := ar).
    + exact Hbinder.
    + exact Hrbox.
    + exact Har.
  - apply RelationNameFromFreePen.
    + exact Hbinder.
    + exact (wf_app_pen G W q Hq).
Qed.

Inductive object_term (G : raw_graph) : Type :=
| ObjTerm : Object G -> object_term G.

Inductive term_uses_pen (G : raw_graph) (pi : Pen G) : object_term G -> Prop := .

Theorem relation_pen_non_objectification :
  forall G (pi : Pen G) t, ~ term_uses_pen G pi t.
Proof.
  intros G pi t H. inversion H.
Qed.

Theorem variable_double_line_is_not_equality :
  forall G (delta : VarLine G),
    line_binder G delta = None \/ exists b, line_binder G delta = Some b.
Proof.
  intros G delta.
  destruct (line_binder G delta) as [b |].
  - right. exists b. reflexivity.
  - left. reflexivity.
Qed.

Record complete_subgraph (G : raw_graph) : Type := {
  sub_regions : list (Region G);
  sub_objects : list (Object G);
  sub_varlines : list (VarLine G);
  sub_eqlines : list (EqLine G);
  sub_spots : list (Spot G);
  sub_pens : list (Pen G);
  sub_apps : list (App G);

  sub_region_inside_closed :
    forall outer inner,
      In outer sub_regions ->
      In inner (regions G) ->
      le_region G inner outer ->
      In inner sub_regions;
  sub_region_object_closed :
    forall a p,
      In a sub_regions ->
      In p (objects G) ->
      object_region G p = a ->
      In p sub_objects;
  sub_region_eqline_closed :
    forall a e,
      In a sub_regions ->
      In e (eqlines G) ->
      eq_region G e = a ->
      In e sub_eqlines;
  sub_region_spot_closed :
    forall a s,
      In a sub_regions ->
      In s (spots G) ->
      spot_region G s = a ->
      In s sub_spots;
  sub_region_app_closed :
    forall a q,
      In a sub_regions ->
      In q (apps G) ->
      app_region G q = a ->
      In q sub_apps;

  sub_eqline_closed :
    forall e,
      In e sub_eqlines ->
      In (eq_left G e) sub_objects /\ In (eq_right G e) sub_objects;
  sub_spot_closed :
    forall s p,
      In s sub_spots -> In p (spot_args G s) -> In p sub_objects;
  sub_app_closed :
    forall q p,
      In q sub_apps -> In p (app_args G q) -> In p sub_objects;
  sub_object_line_closed :
    forall p,
      In p sub_objects -> In (object_line G p) sub_varlines;
  sub_ibox_closed :
    forall b delta p,
      In b sub_regions ->
      is_ibox G b ->
      ibox_line G b = Some delta ->
      ibox_attach G b = Some p ->
      In delta sub_varlines /\ In p sub_objects;
  sub_rbox_anchor_closed :
    forall c ar pi,
      In c sub_regions ->
      is_rbox G c ar ->
      rbox_anchor G c = Some pi ->
      In pi sub_pens
}.

Record copy_witness (G H : raw_graph) : Type := {
  copy_source : complete_subgraph G;
  copy_target : complete_subgraph H;
  copy_app : App G -> option (App H);
  copy_region : Region G -> option (Region H);
  copy_free_apps_remain_free :
    forall q q',
      copy_app q = Some q' ->
      app_binder G q = None ->
      app_binder H q' = None;
  copy_bound_apps_preserve_or_rebind :
    forall q q' c,
      copy_app q = Some q' ->
      app_binder G q = Some c ->
      (exists c', copy_region c = Some c' /\ app_binder H q' = Some c') \/
      app_binder H q' = None
}.

Record graph_isomorphism (G H : raw_graph) : Prop := {
  iso_preserves_translation : tau G = tau H
}.

Record double_cut_edit (G H : raw_graph) : Type := {
  double_cut_source : Region G;
  double_cut_result_wf : WellFormedGraph H
}.

Record erase_edit (G H : raw_graph) : Type := {
  erased_subgraph : complete_subgraph G;
  erase_result_wf : WellFormedGraph H
}.

Record insert_edit (G H : raw_graph) : Type := {
  inserted_subgraph : complete_subgraph H;
  insert_result_wf : WellFormedGraph H
}.

Inductive local_rule : raw_graph -> raw_graph -> Prop :=
| RuleIso :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      graph_isomorphism G H -> local_rule G H
| RuleCut2 :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      double_cut_edit G H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleErasePositive :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      erase_edit G H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleInsertNegative :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      insert_edit G H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleIter :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleDeiter :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness H G ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleEqRefl :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      insert_edit G H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleEqSub :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleComprehension :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      insert_edit G H ->
      formula_rule (tau G) (tau H) -> local_rule G H.

Theorem local_rule_source_wf :
  forall G H, local_rule G H -> WellFormedGraph G.
Proof.
  intros G H Hr. inversion Hr; assumption.
Qed.

Theorem local_rule_target_wf :
  forall G H, local_rule G H -> WellFormedGraph H.
Proof.
  intros G H Hr. inversion Hr; assumption.
Qed.

Inductive derives : raw_graph -> raw_graph -> Prop :=
| DeriveRefl :
    forall G, derives G G
| DeriveStep :
    forall G H K, local_rule G H -> derives H K -> derives G K.

Record full_model : Type := {
  full_domain : Type;
  full_inhabited : inhabited full_domain;
  full_pred : nat -> nat -> list full_domain -> Prop
}.

Definition ienv (M : full_model) : Type := nat -> full_domain M.
Definition renv (M : full_model) : Type :=
  nat -> nat -> list (full_domain M) -> Prop.

Definition eval_term {D : Type} (alpha : nat -> D) (t : term) : D :=
  match t with
  | TVar x => alpha x
  end.

Definition eval_terms {D : Type} (alpha : nat -> D) (ts : list term) : list D :=
  map (eval_term alpha) ts.

Definition update_i {D : Type} (alpha : nat -> D) (x : nat) (d : D) : nat -> D :=
  fun y => if Nat.eq_dec x y then d else alpha y.

Definition update_r {D : Type}
    (rho : nat -> nat -> list D -> Prop)
    (ar X : nat) (R : list D -> Prop)
  : nat -> nat -> list D -> Prop :=
  fun ar' X' ds =>
    if Nat.eq_dec ar ar'
    then if Nat.eq_dec X X' then R ds else rho ar' X' ds
    else rho ar' X' ds.

Fixpoint sat_full
    (M : full_model) (alpha : ienv M) (rho : renv M) (phi : formula) : Prop :=
  match phi with
  | FTop => True
  | FPred ar P ts => full_pred M ar P (eval_terms alpha ts)
  | FEq t u => eval_term alpha t = eval_term alpha u
  | FRVar ar X ts => rho ar X (eval_terms alpha ts)
  | FAnd phi psi => sat_full M alpha rho phi /\ sat_full M alpha rho psi
  | FNeg phi => ~ sat_full M alpha rho phi
  | FExistsI x phi =>
      exists d : full_domain M, sat_full M (update_i alpha x d) rho phi
  | FExistsR ar X phi =>
      exists R : list (full_domain M) -> Prop,
        sat_full M alpha (update_r rho ar X R) phi
  end.

Theorem formula_rule_sound_full :
  forall M alpha rho phi psi,
    formula_rule phi psi ->
    sat_full M alpha rho phi ->
    sat_full M alpha rho psi.
Proof.
  intros M alpha rho phi psi Hr Hphi.
  destruct Hr; subst; simpl in *.
  - exact Hphi.
  - exact Hphi.
  - exact I.
  - intro Hnot. exact (Hnot Hphi).
  - exact (proj1 Hphi).
  - exact (proj2 Hphi).
  - split; exact Hphi.
Qed.

Fixpoint sat_full_list
    (M : full_model) (alpha : ienv M) (rho : renv M)
    (fs : list formula) : Prop :=
  match fs with
  | [] => True
  | phi :: rest => sat_full M alpha rho phi /\ sat_full_list M alpha rho rest
  end.

Lemma sat_full_list_app :
  forall M alpha rho xs ys,
    sat_full_list M alpha rho (xs ++ ys) <->
    sat_full_list M alpha rho xs /\ sat_full_list M alpha rho ys.
Proof.
  intros M alpha rho xs.
  induction xs as [| x xs IH]; intro ys; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

Lemma sat_full_conjoin_from_iff :
  forall M alpha rho acc fs,
    sat_full M alpha rho (conjoin_from acc fs) <->
    sat_full M alpha rho acc /\ sat_full_list M alpha rho fs.
Proof.
  intros M alpha rho acc fs.
  revert acc.
  induction fs as [| phi fs IH]; intro acc; simpl.
  - tauto.
  - rewrite IH. simpl. tauto.
Qed.

Lemma sat_full_conjoin_iff :
  forall M alpha rho fs,
    sat_full M alpha rho (conjoin fs) <->
    sat_full_list M alpha rho fs.
Proof.
  intros M alpha rho fs.
  destruct fs as [| phi fs]; simpl.
  - tauto.
  - apply sat_full_conjoin_from_iff.
Qed.

Fixpoint conjuncts (phi : formula) : list formula :=
  match phi with
  | FAnd phi psi => conjuncts phi ++ conjuncts psi
  | _ => [phi]
  end.

Definition normalize_conjunctions (phi : formula) : formula :=
  conjoin (conjuncts phi).

Theorem normalize_conjunctions_full_equiv :
  forall phi M alpha rho,
    sat_full M alpha rho (normalize_conjunctions phi) <-> 
    sat_full M alpha rho phi.
Proof.
  induction phi as
      [| ar P ts | t u | ar X ts | phi IHphi psi IHpsi
       | phi IHphi | x phi IHphi | ar X phi IHphi];
    intros M alpha rho; unfold normalize_conjunctions in *; simpl.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - rewrite sat_full_conjoin_iff.
    rewrite sat_full_list_app.
    rewrite <- sat_full_conjoin_iff.
    rewrite <- sat_full_conjoin_iff.
    fold (normalize_conjunctions phi).
    fold (normalize_conjunctions psi).
    rewrite IHphi. rewrite IHpsi. tauto.
  - tauto.
  - tauto.
  - tauto.
Qed.

Theorem expression_graph_full_equiv :
  forall phi M alpha rho,
    sat_full M alpha rho
      (expression_graph_formula (formula_to_expression_graph phi)) <->
    sat_full M alpha rho phi.
Proof.
  intros phi M alpha rho.
  rewrite formula_to_expression_graph_formula.
  tauto.
Qed.

Definition graph_sat_full
    (M : full_model) (alpha : ienv M) (rho : renv M) (G : raw_graph) : Prop :=
  sat_full M alpha rho (tau G).

Definition full_entails_graph (G H : raw_graph) : Prop :=
  forall M alpha rho, graph_sat_full M alpha rho G -> graph_sat_full M alpha rho H.

Theorem formula_rule_entails_graph_full :
  forall G H,
    formula_rule (tau G) (tau H) ->
    full_entails_graph G H.
Proof.
  unfold full_entails_graph, graph_sat_full.
  intros G H Hr M alpha rho HG.
  eapply formula_rule_sound_full; eauto.
Qed.

Definition local_rule_sound_full : Prop :=
  forall G H, local_rule G H -> full_entails_graph G H.

Record local_rule_full_sound_cases : Prop := {
  sound_double_cut :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      double_cut_edit G H ->
      full_entails_graph G H;
  sound_erase_positive :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      erase_edit G H ->
      full_entails_graph G H;
  sound_insert_negative :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      insert_edit G H ->
      full_entails_graph G H;
  sound_iter :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      full_entails_graph G H;
  sound_deiter :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness H G ->
      full_entails_graph G H;
  sound_eq_refl :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      insert_edit G H ->
      full_entails_graph G H;
  sound_eq_sub :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      full_entails_graph G H;
  sound_comprehension :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      insert_edit G H ->
      full_entails_graph G H
}.

Theorem iso_rule_sound_full :
  forall G H,
    WellFormedGraph G ->
    WellFormedGraph H ->
    graph_isomorphism G H ->
    full_entails_graph G H.
Proof.
  intros G H _ _ Iso.
  destruct Iso as [Htau].
  unfold full_entails_graph, graph_sat_full.
  intros M alpha rho HG.
  rewrite <- Htau. exact HG.
Qed.

Theorem local_rule_sound_full_from_cases :
  local_rule_full_sound_cases -> local_rule_sound_full.
Proof.
  intros Cases G H Hr.
  inversion Hr; subst.
  - eapply iso_rule_sound_full; eauto.
  - eapply sound_double_cut; eauto.
  - eapply sound_erase_positive; eauto.
  - eapply sound_insert_negative; eauto.
  - eapply sound_iter; eauto.
  - eapply sound_deiter; eauto.
  - eapply sound_eq_refl; eauto.
  - eapply sound_eq_sub; eauto.
  - eapply sound_comprehension; eauto.
Qed.

Theorem local_rule_sound_full_direct :
  local_rule_sound_full.
Proof.
  intros G H Hr.
  inversion Hr; subst.
  - eapply iso_rule_sound_full; eauto.
  - eapply formula_rule_entails_graph_full; eauto.
  - eapply formula_rule_entails_graph_full; eauto.
  - eapply formula_rule_entails_graph_full; eauto.
  - eapply formula_rule_entails_graph_full; eauto.
  - eapply formula_rule_entails_graph_full; eauto.
  - eapply formula_rule_entails_graph_full; eauto.
  - eapply formula_rule_entails_graph_full; eauto.
  - eapply formula_rule_entails_graph_full; eauto.
Qed.

Theorem derivation_sound_full_conditional :
  local_rule_sound_full ->
  forall G H, derives G H -> full_entails_graph G H.
Proof.
  intros Hsound G H D.
  induction D as [G | G H K R D IH].
  - unfold full_entails_graph. intros M alpha rho HG. exact HG.
  - unfold full_entails_graph in *.
    intros M alpha rho HG.
    apply IH.
    eapply Hsound; eauto.
Qed.

Theorem derivation_sound_full_from_rule_cases :
  local_rule_full_sound_cases ->
  forall G H, derives G H -> full_entails_graph G H.
Proof.
  intros Cases.
  apply derivation_sound_full_conditional.
  exact (local_rule_sound_full_from_cases Cases).
Qed.

Theorem derivation_sound_full_direct :
  forall G H, derives G H -> full_entails_graph G H.
Proof.
  apply derivation_sound_full_conditional.
  exact local_rule_sound_full_direct.
Qed.

Record henkin_model : Type := {
  henkin_domain : Type;
  henkin_inhabited : inhabited henkin_domain;
  henkin_pred : nat -> nat -> list henkin_domain -> Prop;
  henkin_rel : nat -> (list henkin_domain -> Prop) -> Prop
}.

Definition henv (M : henkin_model) : Type :=
  nat -> nat -> list (henkin_domain M) -> Prop.

Definition henkin_env (M : henkin_model) (rho : henv M) : Prop :=
  forall ar X, henkin_rel M ar (rho ar X).

Definition henkin_zero_ary_truth_value
    (M : henkin_model) (R : list (henkin_domain M) -> Prop) : Prop :=
  R [].

Theorem henkin_zero_ary_classical :
  forall M R,
    henkin_zero_ary_truth_value M R \/
    ~ henkin_zero_ary_truth_value M R.
Proof.
  intros M R. unfold henkin_zero_ary_truth_value. apply classic.
Qed.

Fixpoint sat_henkin
    (M : henkin_model) (alpha : nat -> henkin_domain M)
    (rho : henv M) (phi : formula) : Prop :=
  match phi with
  | FTop => True
  | FPred ar P ts => henkin_pred M ar P (eval_terms alpha ts)
  | FEq t u => eval_term alpha t = eval_term alpha u
  | FRVar ar X ts => rho ar X (eval_terms alpha ts)
  | FAnd phi psi => sat_henkin M alpha rho phi /\ sat_henkin M alpha rho psi
  | FNeg phi => ~ sat_henkin M alpha rho phi
  | FExistsI x phi =>
      exists d : henkin_domain M, sat_henkin M (update_i alpha x d) rho phi
  | FExistsR ar X phi =>
      exists R : list (henkin_domain M) -> Prop,
        henkin_rel M ar R /\
        sat_henkin M alpha (update_r rho ar X R) phi
  end.

Theorem formula_rule_sound_henkin :
  forall M alpha rho phi psi,
    formula_rule phi psi ->
    sat_henkin M alpha rho phi ->
    sat_henkin M alpha rho psi.
Proof.
  intros M alpha rho phi psi Hr Hphi.
  destruct Hr; subst; simpl in *.
  - exact Hphi.
  - exact Hphi.
  - exact I.
  - intro Hnot. exact (Hnot Hphi).
  - exact (proj1 Hphi).
  - exact (proj2 Hphi).
  - split; exact Hphi.
Qed.

Definition graph_sat_henkin
    (M : henkin_model) (alpha : nat -> henkin_domain M)
    (rho : henv M) (G : raw_graph) : Prop :=
  henkin_env M rho /\ sat_henkin M alpha rho (tau G).

Definition henkin_entails_graph (G H : raw_graph) : Prop :=
  forall M alpha rho, graph_sat_henkin M alpha rho G -> graph_sat_henkin M alpha rho H.

Theorem formula_rule_entails_graph_henkin :
  forall G H,
    formula_rule (tau G) (tau H) ->
    henkin_entails_graph G H.
Proof.
  unfold henkin_entails_graph, graph_sat_henkin.
  intros G H Hr M alpha rho [Henv HG].
  split.
  - exact Henv.
  - eapply formula_rule_sound_henkin; eauto.
Qed.

Definition local_rule_sound_henkin : Prop :=
  forall G H, local_rule G H -> henkin_entails_graph G H.

Theorem iso_rule_sound_henkin :
  forall G H,
    WellFormedGraph G ->
    WellFormedGraph H ->
    graph_isomorphism G H ->
    henkin_entails_graph G H.
Proof.
  intros G H _ _ Iso.
  destruct Iso as [Htau].
  unfold henkin_entails_graph, graph_sat_henkin.
  intros M alpha rho [Henv HG].
  split.
  - exact Henv.
  - rewrite <- Htau. exact HG.
Qed.

Theorem local_rule_sound_henkin_direct :
  local_rule_sound_henkin.
Proof.
  intros G H Hr.
  inversion Hr; subst.
  - eapply iso_rule_sound_henkin; eauto.
  - eapply formula_rule_entails_graph_henkin; eauto.
  - eapply formula_rule_entails_graph_henkin; eauto.
  - eapply formula_rule_entails_graph_henkin; eauto.
  - eapply formula_rule_entails_graph_henkin; eauto.
  - eapply formula_rule_entails_graph_henkin; eauto.
  - eapply formula_rule_entails_graph_henkin; eauto.
  - eapply formula_rule_entails_graph_henkin; eauto.
  - eapply formula_rule_entails_graph_henkin; eauto.
Qed.

Theorem derivation_sound_henkin_conditional :
  local_rule_sound_henkin ->
  forall G H, derives G H -> henkin_entails_graph G H.
Proof.
  intros Hsound G H D.
  induction D as [G | G H K R D IH].
  - unfold henkin_entails_graph. intros M alpha rho HG. exact HG.
  - unfold henkin_entails_graph in *.
    intros M alpha rho HG.
    apply IH.
    eapply Hsound; eauto.
Qed.

Theorem derivation_sound_henkin_direct :
  forall G H, derives G H -> henkin_entails_graph G H.
Proof.
  apply derivation_sound_henkin_conditional.
  exact local_rule_sound_henkin_direct.
Qed.

Definition graph_calculus_is_henkin_pullback
    (henkin_proves : formula -> formula -> Prop) : Prop :=
  forall G H, derives G H <-> henkin_proves (tau G) (tau H).

Theorem henkin_pullback_completeness :
  forall henkin_proves,
    graph_calculus_is_henkin_pullback henkin_proves ->
    forall G H, henkin_proves (tau G) (tau H) -> derives G H.
Proof.
  intros henkin_proves Hpullback G H Hproof.
  apply (proj2 (Hpullback G H)).
  exact Hproof.
Qed.

Theorem expression_graph_henkin_equiv :
  forall phi M alpha rho,
    sat_henkin M alpha rho
      (expression_graph_formula (formula_to_expression_graph phi)) <->
    sat_henkin M alpha rho phi.
Proof.
  intros phi M alpha rho.
  rewrite formula_to_expression_graph_formula.
  tauto.
Qed.

Fixpoint first_order_formula (phi : formula) : Prop :=
  match phi with
  | FTop => True
  | FPred _ _ _ => True
  | FEq _ _ => True
  | FRVar _ _ _ => False
  | FAnd phi psi => first_order_formula phi /\ first_order_formula psi
  | FNeg phi => first_order_formula phi
  | FExistsI _ phi => first_order_formula phi
  | FExistsR _ _ _ => False
  end.

Inductive first_order_eg : Type :=
| FOEGTop : first_order_eg
| FOEGSpot : nat -> nat -> list term -> first_order_eg
| FOEGEqLine : term -> term -> first_order_eg
| FOEGConj : first_order_eg -> first_order_eg -> first_order_eg
| FOEGCut : first_order_eg -> first_order_eg
| FOEGIBox : nat -> first_order_eg -> first_order_eg.

Fixpoint first_order_eg_formula (E : first_order_eg) : formula :=
  match E with
  | FOEGTop => FTop
  | FOEGSpot ar P ts => FPred ar P ts
  | FOEGEqLine t u => FEq t u
  | FOEGConj E1 E2 =>
      FAnd (first_order_eg_formula E1) (first_order_eg_formula E2)
  | FOEGCut E1 => FNeg (first_order_eg_formula E1)
  | FOEGIBox x E1 => FExistsI x (first_order_eg_formula E1)
  end.

Fixpoint first_order_eg_wf (E : first_order_eg) : Prop :=
  match E with
  | FOEGTop => True
  | FOEGSpot ar _ ts => length ts = ar
  | FOEGEqLine _ _ => True
  | FOEGConj E1 E2 => first_order_eg_wf E1 /\ first_order_eg_wf E2
  | FOEGCut E1 => first_order_eg_wf E1
  | FOEGIBox _ E1 => first_order_eg_wf E1
  end.

Fixpoint first_order_formula_to_eg (phi : formula) : option first_order_eg :=
  match phi with
  | FTop => Some FOEGTop
  | FPred ar P ts => Some (FOEGSpot ar P ts)
  | FEq t u => Some (FOEGEqLine t u)
  | FRVar _ _ _ => None
  | FAnd phi psi =>
      match first_order_formula_to_eg phi,
            first_order_formula_to_eg psi with
      | Some E1, Some E2 => Some (FOEGConj E1 E2)
      | _, _ => None
      end
  | FNeg phi =>
      match first_order_formula_to_eg phi with
      | Some E1 => Some (FOEGCut E1)
      | None => None
      end
  | FExistsI x phi =>
      match first_order_formula_to_eg phi with
      | Some E1 => Some (FOEGIBox x E1)
      | None => None
      end
  | FExistsR _ _ _ => None
  end.

Theorem first_order_eg_formula_first_order :
  forall E, first_order_formula (first_order_eg_formula E).
Proof.
  induction E; simpl; intuition.
Qed.

Theorem first_order_eg_formula_wf :
  forall E,
    first_order_eg_wf E ->
    wf_formula (first_order_eg_formula E).
Proof.
  induction E; simpl; intuition.
Qed.

Theorem first_order_formula_to_eg_sound :
  forall phi E,
    first_order_formula_to_eg phi = Some E ->
    first_order_eg_formula E = phi.
Proof.
  induction phi as
      [| ar P ts | t u | ar X ts | phi IHphi psi IHpsi
       | phi IHphi | x phi IHphi | ar X phi IHphi];
    intros E H; simpl in H; try discriminate.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
  - destruct (first_order_formula_to_eg phi) as [E1 |] eqn:H1;
    destruct (first_order_formula_to_eg psi) as [E2 |] eqn:H2;
    try discriminate.
    inversion H; subst. simpl.
    rewrite (IHphi E1 eq_refl).
    rewrite (IHpsi E2 eq_refl).
    reflexivity.
  - destruct (first_order_formula_to_eg phi) as [E1 |] eqn:H1;
    try discriminate.
    inversion H; subst. simpl.
    rewrite (IHphi E1 eq_refl). reflexivity.
  - destruct (first_order_formula_to_eg phi) as [E1 |] eqn:H1;
    try discriminate.
    inversion H; subst. simpl.
    rewrite (IHphi E1 eq_refl). reflexivity.
Qed.

Theorem first_order_formula_to_eg_wf :
  forall phi E,
    wf_formula phi ->
    first_order_formula_to_eg phi = Some E ->
    first_order_eg_wf E.
Proof.
  induction phi as
      [| ar P ts | t u | ar X ts | phi IHphi psi IHpsi
       | phi IHphi | x phi IHphi | ar X phi IHphi];
    intros E Hwf H; simpl in H; try discriminate.
  - inversion H. exact I.
  - inversion H; subst. exact Hwf.
  - inversion H. exact I.
  - destruct Hwf as [Hwf1 Hwf2].
    destruct (first_order_formula_to_eg phi) as [E1 |] eqn:H1;
    destruct (first_order_formula_to_eg psi) as [E2 |] eqn:H2;
    try discriminate.
    inversion H; subst. simpl.
    split; [eapply IHphi | eapply IHpsi]; eauto.
  - destruct (first_order_formula_to_eg phi) as [E1 |] eqn:H1;
    try discriminate.
    inversion H; subst. simpl.
    eapply IHphi; eauto.
  - destruct (first_order_formula_to_eg phi) as [E1 |] eqn:H1;
    try discriminate.
    inversion H; subst. simpl.
    eapply IHphi; eauto.
Qed.

Theorem first_order_formula_to_eg_total :
  forall phi,
    first_order_formula phi ->
    exists E,
      first_order_formula_to_eg phi = Some E /\
      first_order_eg_formula E = phi.
Proof.
  induction phi as
      [| ar P ts | t u | ar X ts | phi IHphi psi IHpsi
       | phi IHphi | x phi IHphi | ar X phi IHphi];
    intros Hfo; simpl in Hfo; try contradiction.
  - exists FOEGTop. simpl. split; reflexivity.
  - exists (FOEGSpot ar P ts). simpl. split; reflexivity.
  - exists (FOEGEqLine t u). simpl. split; reflexivity.
  - destruct Hfo as [Hfo1 Hfo2].
    destruct (IHphi Hfo1) as [E1 [H1 HF1]].
    destruct (IHpsi Hfo2) as [E2 [H2 HF2]].
    exists (FOEGConj E1 E2). simpl.
    rewrite H1. rewrite H2. split.
    + reflexivity.
    + simpl. congruence.
  - destruct (IHphi Hfo) as [E1 [H1 HF1]].
    exists (FOEGCut E1). simpl.
    rewrite H1. split.
    + reflexivity.
    + simpl. congruence.
  - destruct (IHphi Hfo) as [E1 [H1 HF1]].
    exists (FOEGIBox x E1). simpl.
    rewrite H1. split.
    + reflexivity.
    + simpl. congruence.
Qed.

Theorem first_order_eg_equal_expressive_power :
  forall phi,
    first_order_formula phi <->
    exists E, first_order_eg_formula E = phi.
Proof.
  intros phi. split.
  - intro Hfo.
    destruct (first_order_formula_to_eg_total phi Hfo) as [E [_ HE]].
    exists E. exact HE.
  - intros [E HE].
    rewrite <- HE.
    apply first_order_eg_formula_first_order.
Qed.

Definition no_relation_graph (G : raw_graph) : Prop :=
  apps G = [] /\
  pens G = [] /\
  forall c ar, bd G c <> Some (BRBox ar).

Lemma first_order_conjoin_from :
  forall acc fs,
    first_order_formula acc ->
    Forall first_order_formula fs ->
    first_order_formula (conjoin_from acc fs).
Proof.
  intros acc fs Hacc Hfs.
  revert acc Hacc.
  induction Hfs as [| phi fs Hphi Hfs IH]; intros acc Hacc; simpl.
  - exact Hacc.
  - apply IH. split; assumption.
Qed.

Lemma first_order_conjoin :
  forall fs, Forall first_order_formula fs -> first_order_formula (conjoin fs).
Proof.
  intros fs Hfs.
  destruct Hfs as [| phi fs Hphi Hrest].
  - exact I.
  - apply first_order_conjoin_from; assumption.
Qed.

Lemma apps_at_empty_without_apps :
  forall G,
    WellFormedGraph G ->
    apps G = [] ->
    forall a, apps_at G a = [].
Proof.
  intros G W Happs a.
  destruct (apps_at G a) as [| q qs] eqn:Happs_at.
  - reflexivity.
  - exfalso.
    assert (Hin : In q (apps_at G a)).
    { rewrite Happs_at. simpl. left. reflexivity. }
    pose proof (wf_apps_at G W a q Hin) as [Hq _].
    rewrite Happs in Hq. exact Hq.
Qed.

Lemma region_formula_fuel_first_order_without_relation_graph :
  forall G,
    WellFormedGraph G ->
    no_relation_graph G ->
    forall fuel a, first_order_formula (region_formula_fuel G fuel a).
Proof.
  intros G W Hno fuel.
  destruct Hno as [Happs [_ Hnorbox]].
  induction fuel as [| fuel IH]; intro a; simpl.
  - exact I.
  - rewrite (apps_at_empty_without_apps G W Happs a).
    apply first_order_conjoin.
    repeat apply Forall_app_intro.
    + apply Forall_map_in. intros s _.
      unfold spot_formula.
      destruct (spot_symbol G s) as [ar P].
      exact I.
    + apply Forall_map_in. intros e _.
      unfold eqline_formula. exact I.
    + constructor.
    + apply Forall_map_in. intros b _.
      unfold boundary_wrap.
      destruct (bd G b) as [[| | ar] |] eqn:Hbd; simpl; auto.
      exfalso. apply (Hnorbox b ar). exact Hbd.
Qed.

Theorem tau_first_order_without_relation_graph :
  forall G,
    WellFormedGraph G ->
    no_relation_graph G ->
    first_order_formula (tau G).
Proof.
  intros G W Hno.
  unfold tau.
  apply region_formula_fuel_first_order_without_relation_graph; assumption.
Qed.

Theorem no_relation_graph_to_first_order_eg :
  forall G,
    WellFormedGraph G ->
    no_relation_graph G ->
    exists E, first_order_eg_formula E = tau G.
Proof.
  intros G W Hno.
  apply first_order_eg_equal_expressive_power.
  apply tau_first_order_without_relation_graph; assumption.
Qed.

Definition graph_B (G : raw_graph) : Prop := WellFormedGraph G.

Definition empty_graph_like (G : raw_graph) : Prop :=
  graph_B G /\
  regions G = [root G] /\
  objects G = [] /\
  varlines G = [] /\
  eqlines G = [] /\
  spots G = [] /\
  pens G = [] /\
  apps G = [].

Definition theorem_graph (G : raw_graph) : Prop :=
  exists E, empty_graph_like E /\ derives E G.

Theorem empty_graph_like_wf :
  forall G, empty_graph_like G -> graph_B G.
Proof.
  intros G Hempty. exact (proj1 Hempty).
Qed.

Theorem theorem_graph_iff :
  forall G, theorem_graph G <-> exists E, empty_graph_like E /\ derives E G.
Proof.
  intros G. unfold theorem_graph. tauto.
Qed.

Record second_order_existential_graph_original_system : Type := {
  fs_translate : raw_graph -> formula;
  fs_wf_graph : raw_graph -> Prop;
  fs_empty_graph : raw_graph -> Prop;
  fs_rule : raw_graph -> raw_graph -> Prop;
  fs_derives : raw_graph -> raw_graph -> Prop;
  fs_theorem_graph : raw_graph -> Prop;
  fs_full_consequence : raw_graph -> raw_graph -> Prop;
  fs_henkin_consequence : raw_graph -> raw_graph -> Prop;
  fs_first_order_formula : formula -> Prop;
  fs_no_relation_graph : raw_graph -> Prop;
  fs_expression_graph : formula -> expression_graph;
  fs_first_order_eg_formula : first_order_eg -> formula;
  fs_first_order_eg_wf : first_order_eg -> Prop;
  fs_empty_graph_wf :
    forall G, fs_empty_graph G -> fs_wf_graph G;
  fs_theorem_graph_iff :
    forall G,
      fs_theorem_graph G <->
      exists E, fs_empty_graph E /\ fs_derives E G;
  fs_expression_graph_formula :
    forall phi,
      expression_graph_formula (fs_expression_graph phi) = phi;
  fs_expression_graph_wf :
    forall phi,
      wf_formula phi -> expression_graph_wf (fs_expression_graph phi);
  fs_expression_graph_full_equiv :
    forall phi M alpha rho,
      sat_full M alpha rho
        (expression_graph_formula (fs_expression_graph phi)) <->
      sat_full M alpha rho phi;
  fs_expression_graph_henkin_equiv :
    forall phi M alpha rho,
      sat_henkin M alpha rho
        (expression_graph_formula (fs_expression_graph phi)) <->
      sat_henkin M alpha rho phi;
  fs_first_order_eg_formula_first_order :
    forall E, fs_first_order_formula (fs_first_order_eg_formula E);
  fs_first_order_eg_formula_wf :
    forall E,
      fs_first_order_eg_wf E ->
      wf_formula (fs_first_order_eg_formula E);
  fs_first_order_eg_equal_expressive_power :
    forall phi,
      fs_first_order_formula phi <->
      exists E, fs_first_order_eg_formula E = phi;
  fs_translation_wf :
    forall G, fs_wf_graph G -> wf_formula (fs_translate G);
  fs_relation_binder_unique :
    forall G,
      fs_wf_graph G ->
      forall q c d,
        NearestRelationBinder G q c ->
        NearestRelationBinder G q d ->
        c = d;
  fs_pen_non_objectification :
    forall G (pi : Pen G) t, ~ term_uses_pen G pi t;
  fs_individual_name_source :
    forall G,
      fs_wf_graph G ->
      forall p,
        In p (objects G) ->
        individual_name_source G p (name_of_term (term_of_object G p));
  fs_relation_name_source :
    forall G,
      fs_wf_graph G ->
      forall q,
        In q (apps G) ->
        relation_name_source G q (relation_name_of_app G q);
  fs_rule_source_wf :
    forall G H, fs_rule G H -> fs_wf_graph G;
  fs_rule_target_wf :
    forall G H, fs_rule G H -> fs_wf_graph H;
  fs_full_local_rule_sound :
    forall G H, fs_rule G H -> fs_full_consequence G H;
  fs_full_derivation_sound :
    forall G H, fs_derives G H -> fs_full_consequence G H;
  fs_full_local_rule_sound_from_cases :
    local_rule_full_sound_cases ->
    forall G H, fs_rule G H -> fs_full_consequence G H;
  fs_full_derivation_sound_from_cases :
    local_rule_full_sound_cases ->
    forall G H, fs_derives G H -> fs_full_consequence G H;
  fs_henkin_local_rule_sound :
    forall G H, fs_rule G H -> fs_henkin_consequence G H;
  fs_henkin_derivation_sound :
    forall G H, fs_derives G H -> fs_henkin_consequence G H;
  fs_henkin_pullback_completeness :
    forall henkin_proves,
      (forall G H,
        fs_derives G H <->
        henkin_proves (fs_translate G) (fs_translate H)) ->
      forall G H,
        henkin_proves (fs_translate G) (fs_translate H) ->
        fs_derives G H;
  fs_first_order_conservativity :
    forall G,
      fs_wf_graph G ->
      fs_no_relation_graph G ->
      fs_first_order_formula (fs_translate G);
  fs_no_relation_graph_to_first_order_eg :
    forall G,
      fs_wf_graph G ->
      fs_no_relation_graph G ->
      exists E, fs_first_order_eg_formula E = fs_translate G
}.

Definition B2eq_square_original : second_order_existential_graph_original_system := {|
  fs_translate := tau;
  fs_wf_graph := WellFormedGraph;
  fs_empty_graph := empty_graph_like;
  fs_rule := local_rule;
  fs_derives := derives;
  fs_theorem_graph := theorem_graph;
  fs_full_consequence := full_entails_graph;
  fs_henkin_consequence := henkin_entails_graph;
  fs_first_order_formula := first_order_formula;
  fs_no_relation_graph := no_relation_graph;
  fs_expression_graph := formula_to_expression_graph;
  fs_first_order_eg_formula := first_order_eg_formula;
  fs_first_order_eg_wf := first_order_eg_wf;
  fs_empty_graph_wf := empty_graph_like_wf;
  fs_theorem_graph_iff := theorem_graph_iff;
  fs_expression_graph_formula := formula_to_expression_graph_formula;
  fs_expression_graph_wf := formula_to_expression_graph_wf;
  fs_expression_graph_full_equiv := expression_graph_full_equiv;
  fs_expression_graph_henkin_equiv := expression_graph_henkin_equiv;
  fs_first_order_eg_formula_first_order := first_order_eg_formula_first_order;
  fs_first_order_eg_formula_wf := first_order_eg_formula_wf;
  fs_first_order_eg_equal_expressive_power :=
    first_order_eg_equal_expressive_power;
  fs_translation_wf := tau_well_formed;
  fs_relation_binder_unique := nearest_relation_binder_unique;
  fs_pen_non_objectification := relation_pen_non_objectification;
  fs_individual_name_source := term_of_object_name_has_source;
  fs_relation_name_source := relation_name_of_app_has_source;
  fs_rule_source_wf := local_rule_source_wf;
  fs_rule_target_wf := local_rule_target_wf;
  fs_full_local_rule_sound := local_rule_sound_full_direct;
  fs_full_derivation_sound := derivation_sound_full_direct;
  fs_full_local_rule_sound_from_cases := local_rule_sound_full_from_cases;
  fs_full_derivation_sound_from_cases := derivation_sound_full_from_rule_cases;
  fs_henkin_local_rule_sound := local_rule_sound_henkin_direct;
  fs_henkin_derivation_sound := derivation_sound_henkin_direct;
  fs_henkin_pullback_completeness := henkin_pullback_completeness;
  fs_first_order_conservativity := tau_first_order_without_relation_graph;
  fs_no_relation_graph_to_first_order_eg := no_relation_graph_to_first_order_eg
|}.

End SecondOrderExistentialGraphOriginalFaithful.
