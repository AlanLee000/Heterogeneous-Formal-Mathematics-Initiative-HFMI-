Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Module SecondOrderExistentialGraphRevFaithful.

Inductive term : Type :=
| TVar : nat -> term.

Inductive formula : Type :=
| FTop : formula
| FPred : nat -> nat -> list term -> formula
| FEq : term -> term -> formula
| FRVar : nat -> nat -> list term -> formula
| FAnd : formula -> formula -> formula
| FNeg : formula -> formula
| FExistsI : nat -> formula -> formula
| FExistsR : nat -> nat -> formula -> formula.

Definition FImp (phi psi : formula) : formula :=
  FNeg (FAnd phi (FNeg psi)).
Definition FIff (phi psi : formula) : formula :=
  FAnd (FImp phi psi) (FImp psi phi).
Definition FForallI (x : nat) (phi : formula) : formula :=
  FNeg (FExistsI x (FNeg phi)).
Definition FForallR (ar X : nat) (phi : formula) : formula :=
  FNeg (FExistsR ar X (FNeg phi)).

Fixpoint forall_i_list (xs : list nat) (phi : formula) : formula :=
  match xs with
  | [] => phi
  | x :: rest => FForallI x (forall_i_list rest phi)
  end.

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
  induction phi; simpl; try rewrite IHphi; try rewrite IHphi1; try rewrite IHphi2;
    reflexivity.
Qed.

Theorem formula_to_expression_graph_wf :
  forall phi,
    wf_formula phi ->
    expression_graph_wf (formula_to_expression_graph phi).
Proof.
  induction phi; simpl; tauto.
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

Record handle_graph : Type := {
  Region : Type;
  Object : Type;
  IFree : Type;
  EqLine : Type;
  Spot : Type;
  RFree : Type;
  App : Type;

  regions : list Region;
  root : Region;
  le_region : Region -> Region -> Prop;
  bd : Region -> option boundary;
  children : Region -> list Region;
  region_rank : Region -> nat;

  objects : list Object;
  object_region : Object -> Region;
  object_handle : Object -> (IFree + Region)%type;
  ifree_nodes : list IFree;

  eqlines : list EqLine;
  eqlines_at : Region -> list EqLine;
  eq_region : EqLine -> Region;
  eq_left : EqLine -> Object;
  eq_right : EqLine -> Object;

  spots : list Spot;
  spots_at : Region -> list Spot;
  spot_region : Spot -> Region;
  spot_symbol : Spot -> nat * nat;
  spot_args : Spot -> list Object;

  rfree_nodes : list RFree;
  rfree_arity : RFree -> nat;

  apps : list App;
  apps_at : Region -> list App;
  app_region : App -> Region;
  app_handle : App -> (RFree + Region)%type;
  app_args : App -> list Object;

  eta_i_free : IFree -> nat;
  eta_i_bound : Region -> nat;
  eta_r_free : RFree -> nat;
  eta_r_bound : Region -> nat
}.

Definition is_ibox (G : handle_graph) (b : Region G) : Prop :=
  bd G b = Some BIBox.

Definition is_rbox (G : handle_graph) (c : Region G) (ar : nat) : Prop :=
  bd G c = Some (BRBox ar).

Definition i_handle_available
    (G : handle_graph) (a : Region G) (h : (IFree G + Region G)%type) : Prop :=
  match h with
  | inl u => In u (ifree_nodes G)
  | inr b => is_ibox G b /\ le_region G a b
  end.

Definition r_handle_arity
    (G : handle_graph) (h : (RFree G + Region G)%type) : nat :=
  match h with
  | inl r => rfree_arity G r
  | inr c =>
      match bd G c with
      | Some (BRBox ar) => ar
      | _ => 0
      end
  end.

Definition r_handle_available
    (G : handle_graph) (a : Region G) (h : (RFree G + Region G)%type) : Prop :=
  match h with
  | inl r => In r (rfree_nodes G)
  | inr c => exists ar, is_rbox G c ar /\ le_region G a c
  end.

Definition term_of_object (G : handle_graph) (p : Object G) : term :=
  match object_handle G p with
  | inl u => TVar (eta_i_free G u)
  | inr b => TVar (eta_i_bound G b)
  end.

Definition relation_name
    (G : handle_graph) (h : (RFree G + Region G)%type) : nat :=
  match h with
  | inl r => eta_r_free G r
  | inr c => eta_r_bound G c
  end.

Definition name_of_term (t : term) : nat :=
  match t with
  | TVar x => x
  end.

Inductive individual_handle_name_source
    (G : handle_graph) : (IFree G + Region G)%type -> nat -> Prop :=
| IndividualHandleNameFree :
    forall u,
      In u (ifree_nodes G) ->
      individual_handle_name_source G (inl u) (eta_i_free G u)
| IndividualHandleNameBound :
    forall b,
      is_ibox G b ->
      individual_handle_name_source G (inr b) (eta_i_bound G b).

Inductive relation_handle_name_source
    (G : handle_graph) : (RFree G + Region G)%type -> nat -> Prop :=
| RelationHandleNameFree :
    forall r,
      In r (rfree_nodes G) ->
      relation_handle_name_source G (inl r) (eta_r_free G r)
| RelationHandleNameBound :
    forall c ar,
      is_rbox G c ar ->
      relation_handle_name_source G (inr c) (eta_r_bound G c).

Definition spot_formula (G : handle_graph) (s : Spot G) : formula :=
  let '(ar, P) := spot_symbol G s in
  FPred ar P (map (term_of_object G) (spot_args G s)).

Definition eqline_formula (G : handle_graph) (e : EqLine G) : formula :=
  FEq (term_of_object G (eq_left G e)) (term_of_object G (eq_right G e)).

Definition app_formula (G : handle_graph) (q : App G) : formula :=
  let h := app_handle G q in
  FRVar (r_handle_arity G h) (relation_name G h)
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
    (G : handle_graph) (inside : Region G -> formula) (b : Region G) : formula :=
  match bd G b with
  | Some BCut => FNeg (inside b)
  | Some BIBox => FExistsI (eta_i_bound G b) (inside b)
  | Some (BRBox ar) => FExistsR ar (eta_r_bound G b) (inside b)
  | None => inside b
  end.

Fixpoint region_formula_fuel
    (G : handle_graph) (fuel : nat) (a : Region G) : formula :=
  match fuel with
  | 0 => FTop
  | S fuel' =>
      conjoin
        (map (spot_formula G) (spots_at G a) ++
         map (eqline_formula G) (eqlines_at G a) ++
         map (app_formula G) (apps_at G a) ++
         map (boundary_wrap G (region_formula_fuel G fuel')) (children G a))
  end.

Definition tau (G : handle_graph) : formula :=
  region_formula_fuel G (S (region_rank G (root G))) (root G).

Definition comprehension_formula
    (ar X : nat) (xs : list nat) (body : formula) : formula :=
  FExistsR ar X
    (forall_i_list xs
      (FIff (FRVar ar X (map TVar xs)) body)).

Record open_subgraph (G : handle_graph) : Type := {
  sub_regions : list (Region G);
  sub_objects : list (Object G);
  sub_ifree : list (IFree G);
  sub_eqlines : list (EqLine G);
  sub_spots : list (Spot G);
  sub_rfree : list (RFree G);
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
  sub_object_external_or_internal :
    forall p,
      In p sub_objects ->
      match object_handle G p with
      | inl u => In u sub_ifree
      | inr b => In b sub_regions \/ ~ In b sub_regions
      end;
  sub_app_external_or_internal :
    forall q,
      In q sub_apps ->
      match app_handle G q with
      | inl r => In r sub_rfree
      | inr c => In c sub_regions \/ ~ In c sub_regions
      end
}.

Record copy_witness (G H : handle_graph) : Type := {
  copy_source : open_subgraph G;
  copy_target : open_subgraph H;
  copy_region : Region G -> option (Region H);
  copy_app : App G -> option (App H);
  copy_preserves_free_relation_handles :
    forall q q' r,
      copy_app q = Some q' ->
      app_handle G q = inl r ->
      exists r', app_handle H q' = inl r';
  copy_internal_bound_relation_handles_fresh :
    forall q q' c,
      copy_app q = Some q' ->
      app_handle G q = inr c ->
      In c (sub_regions G (copy_source)) ->
      exists c', copy_region c = Some c' /\ app_handle H q' = inr c'
}.

Record WellFormedGraph (G : handle_graph) : Prop := {
  wf_regions_nodup : NoDup (regions G);
  wf_root_region : In (root G) (regions G);
  wf_root_boundary : bd G (root G) = None;
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
  wf_child_region :
    forall a b,
      In b (children G a) ->
      In a (regions G) /\ In b (regions G) /\ le_region G b a /\ b <> a;
  wf_child_rank_decreases :
    forall a b,
      In b (children G a) ->
      region_rank G b < region_rank G a;

  wf_object_region :
    forall p, In p (objects G) -> In (object_region G p) (regions G);
  wf_object_handle_available :
    forall p, In p (objects G) ->
      i_handle_available G (object_region G p) (object_handle G p);
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
  wf_spot_args_objects :
    forall s p, In s (spots G) -> In p (spot_args G s) -> In p (objects G);
  wf_spot_args_local :
    forall s p, In s (spots G) -> In p (spot_args G s) ->
      object_region G p = spot_region G s;
  wf_spot_args_length :
    forall s, In s (spots G) -> length (spot_args G s) = fst (spot_symbol G s);
  wf_spots_at :
    forall a s, In s (spots_at G a) -> In s (spots G) /\ spot_region G s = a;

  wf_rbox_handle_arity :
    forall c ar, is_rbox G c ar -> r_handle_arity G (inr c) = ar;
  wf_rbound_region :
    forall c ar, is_rbox G c ar -> In c (regions G);
  wf_app_region :
    forall q, In q (apps G) -> In (app_region G q) (regions G);
  wf_app_handle_available :
    forall q, In q (apps G) ->
      r_handle_available G (app_region G q) (app_handle G q);
  wf_app_args_objects :
    forall q p, In q (apps G) -> In p (app_args G q) -> In p (objects G);
  wf_app_args_local :
    forall q p, In q (apps G) -> In p (app_args G q) ->
      object_region G p = app_region G q;
  wf_app_args_length :
    forall q, In q (apps G) ->
      length (app_args G q) = r_handle_arity G (app_handle G q);
  wf_apps_at :
    forall a q, In q (apps_at G a) -> In q (apps G) /\ app_region G q = a;

  wf_eta_i_free_injective :
    forall u v,
      In u (ifree_nodes G) -> In v (ifree_nodes G) ->
      eta_i_free G u = eta_i_free G v -> u = v;
  wf_eta_i_bound_injective :
    forall b c,
      is_ibox G b -> is_ibox G c ->
      eta_i_bound G b = eta_i_bound G c -> b = c;
  wf_eta_i_free_bound_disjoint :
    forall u b,
      In u (ifree_nodes G) -> is_ibox G b ->
      eta_i_free G u <> eta_i_bound G b;
  wf_eta_r_free_same_arity_injective :
    forall r s,
      In r (rfree_nodes G) -> In s (rfree_nodes G) ->
      rfree_arity G r = rfree_arity G s ->
      eta_r_free G r = eta_r_free G s -> r = s;
  wf_eta_r_bound_same_arity_injective :
    forall b c ar,
      is_rbox G b ar -> is_rbox G c ar ->
      eta_r_bound G b = eta_r_bound G c -> b = c;
  wf_eta_r_free_bound_disjoint :
    forall r c ar,
      In r (rfree_nodes G) -> is_rbox G c ar ->
      rfree_arity G r = ar ->
      eta_r_free G r <> eta_r_bound G c
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
      unfold eqline_formula. exact I.
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

Theorem individual_handle_availability_descends :
  forall G, WellFormedGraph G ->
  forall a b h,
    In a (regions G) ->
    In b (regions G) ->
    le_region G b a ->
    i_handle_available G a h ->
    i_handle_available G b h.
Proof.
  intros G W a b h Ha Hb Hba Hav.
  destruct h as [u | c]; simpl in *.
  - exact Hav.
  - destruct Hav as [Hibox Hac].
    split.
    + exact Hibox.
    + destruct (wf_boundary_region G W c BIBox Hibox) as [Hc _].
      exact (wf_region_trans G W b a c Hb Ha Hc Hba Hac).
Qed.

Theorem relation_handle_availability_descends :
  forall G, WellFormedGraph G ->
  forall a b h,
    In a (regions G) ->
    In b (regions G) ->
    le_region G b a ->
    r_handle_available G a h ->
    r_handle_available G b h.
Proof.
  intros G W a b h Ha Hb Hba Hav.
  destruct h as [r | c]; simpl in *.
  - exact Hav.
  - destruct Hav as [ar [Hrbox Hac]].
    exists ar. split.
    + exact Hrbox.
    + pose proof (wf_rbound_region G W c ar Hrbox) as Hc.
      exact (wf_region_trans G W b a c Hb Ha Hc Hba Hac).
Qed.

Inductive object_term (G : handle_graph) : Type :=
| ObjTerm : Object G -> object_term G.

Inductive relation_handle_as_object
    (G : handle_graph) (h : (RFree G + Region G)%type)
    : object_term G -> Prop := .

Theorem relation_handle_not_object :
  forall G h t, ~ relation_handle_as_object G h t.
Proof.
  intros G h t H. inversion H.
Qed.

Theorem object_name_has_handle_source :
  forall G, WellFormedGraph G ->
  forall p,
    In p (objects G) ->
    individual_handle_name_source G
      (object_handle G p)
      (name_of_term (term_of_object G p)).
Proof.
  intros G W p Hp.
  pose proof (wf_object_handle_available G W p Hp) as Hav.
  unfold term_of_object, name_of_term.
  destruct (object_handle G p) as [u | b]; simpl in *.
  - apply IndividualHandleNameFree. exact Hav.
  - apply IndividualHandleNameBound. exact (proj1 Hav).
Qed.

Theorem app_relation_name_has_handle_source :
  forall G, WellFormedGraph G ->
  forall q,
    In q (apps G) ->
    relation_handle_name_source G
      (app_handle G q)
      (relation_name G (app_handle G q)).
Proof.
  intros G W q Hq.
  pose proof (wf_app_handle_available G W q Hq) as Hav.
  unfold relation_name.
  destruct (app_handle G q) as [r | c]; simpl in *.
  - apply RelationHandleNameFree. exact Hav.
  - destruct Hav as [ar [Hrbox _]].
    apply RelationHandleNameBound with (ar := ar). exact Hrbox.
Qed.

Inductive local_rule : handle_graph -> handle_graph -> Prop :=
| RuleIso :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      tau G = tau H -> local_rule G H
| RuleCut2 :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleErasePositive :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      open_subgraph G ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleInsertNegative :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      open_subgraph H ->
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
      open_subgraph H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleEqSub :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      formula_rule (tau G) (tau H) -> local_rule G H
| RuleComprehension :
    forall G H ar X xs body,
      WellFormedGraph G ->
      WellFormedGraph H ->
      length xs = ar ->
      tau H = comprehension_formula ar X xs body ->
      formula_rule (tau G) (tau H) ->
      local_rule G H.

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

Inductive derives : handle_graph -> handle_graph -> Prop :=
| DeriveRefl :
    forall G, derives G G
| DeriveStep :
    forall G H K, local_rule G H -> derives H K -> derives G K.

Definition graph_B (G : handle_graph) : Prop := WellFormedGraph G.

Definition empty_graph_like (G : handle_graph) : Prop :=
  graph_B G /\
  regions G = [root G] /\
  objects G = [] /\
  ifree_nodes G = [] /\
  eqlines G = [] /\
  spots G = [] /\
  rfree_nodes G = [] /\
  apps G = [].

Definition theorem_graph (G : handle_graph) : Prop :=
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

Fixpoint update_i_list {D : Type}
    (alpha : nat -> D) (xs : list nat) (ds : list D) : nat -> D :=
  match xs, ds with
  | x :: xs', d :: ds' => update_i_list (update_i alpha x d) xs' ds'
  | _, _ => alpha
  end.

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

Definition unit_full_model : full_model := {|
  full_domain := unit;
  full_inhabited := inhabits tt;
  full_pred := fun _ _ _ => False
|}.

Definition unit_full_ienv : ienv unit_full_model := fun _ => tt.
Definition empty_full_renv : renv unit_full_model := fun _ _ _ => False.

Lemma unit_full_model_top :
  sat_full unit_full_model unit_full_ienv empty_full_renv FTop.
Proof. exact I. Qed.

Lemma unit_full_model_neg_top_refuted :
  ~ sat_full unit_full_model unit_full_ienv empty_full_renv (FNeg FTop).
Proof. cbn. tauto. Qed.

Theorem unit_full_model_nontrivial :
  exists alpha : ienv unit_full_model,
  exists rho : renv unit_full_model,
    sat_full unit_full_model alpha rho FTop /\
    ~ sat_full unit_full_model alpha rho (FNeg FTop).
Proof.
  exists unit_full_ienv, empty_full_renv.
  split.
  - exact unit_full_model_top.
  - exact unit_full_model_neg_top_refuted.
Qed.

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
    (M : full_model) (alpha : ienv M) (rho : renv M) (G : handle_graph) : Prop :=
  sat_full M alpha rho (tau G).

Definition full_entails_graph (G H : handle_graph) : Prop :=
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

Record full_local_rule_sound_cases : Prop := {
  full_sound_cut2 :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      full_entails_graph G H;
  full_sound_erase_positive :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      open_subgraph G ->
      full_entails_graph G H;
  full_sound_insert_negative :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      open_subgraph H ->
      full_entails_graph G H;
  full_sound_iter :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      full_entails_graph G H;
  full_sound_deiter :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness H G ->
      full_entails_graph G H;
  full_sound_eq_refl :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      open_subgraph H ->
      full_entails_graph G H;
  full_sound_eq_sub :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      full_entails_graph G H;
  full_sound_comprehension :
    forall G H ar X xs body,
      WellFormedGraph G ->
      WellFormedGraph H ->
      length xs = ar ->
      tau H = comprehension_formula ar X xs body ->
      full_entails_graph G H
}.

Theorem iso_rule_sound_full :
  forall G H,
    WellFormedGraph G ->
    WellFormedGraph H ->
    tau G = tau H ->
    full_entails_graph G H.
Proof.
  intros G H _ _ Htau.
  unfold full_entails_graph, graph_sat_full.
  intros M alpha rho HG.
  rewrite <- Htau. exact HG.
Qed.

Theorem local_rule_sound_full_from_cases :
  full_local_rule_sound_cases -> local_rule_sound_full.
Proof.
  intros Cases G H Hr.
  inversion Hr; subst.
  - eapply iso_rule_sound_full; eauto.
  - eapply full_sound_cut2; eauto.
  - eapply full_sound_erase_positive; eauto.
  - eapply full_sound_insert_negative; eauto.
  - eapply full_sound_iter; eauto.
  - eapply full_sound_deiter; eauto.
  - eapply full_sound_eq_refl; eauto.
  - eapply full_sound_eq_sub; eauto.
  - eapply full_sound_comprehension; eauto.
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
  intros Sound G H D.
  induction D as [G | G H K R D IH].
  - unfold full_entails_graph. intros M alpha rho HG. exact HG.
  - unfold full_entails_graph in *.
    intros M alpha rho HG.
    apply IH.
    eapply Sound; eauto.
Qed.

Theorem derivation_sound_full_from_rule_cases :
  full_local_rule_sound_cases ->
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
  henkin_rel : nat -> nat -> (list henkin_domain -> Prop) -> Prop
}.

Definition henv (M : henkin_model) : Type :=
  nat -> nat -> list (henkin_domain M) -> Prop.

Definition henkin_env (M : henkin_model) (rho : henv M) : Prop :=
  forall ar X, henkin_rel M ar X (rho ar X).

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
        henkin_rel M ar X R /\
        sat_henkin M alpha (update_r rho ar X R) phi
  end.

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

Definition henkin_comprehension_closed (M : henkin_model) : Prop :=
  forall ar X xs phi,
    length xs = ar ->
    forall alpha rho,
      henkin_env M rho ->
      exists R : list (henkin_domain M) -> Prop,
        henkin_rel M ar X R /\
        forall ds,
          length ds = ar ->
          (R ds <-> sat_henkin M (update_i_list alpha xs ds) rho phi).

Definition graph_sat_henkin
    (M : henkin_model) (alpha : nat -> henkin_domain M)
    (rho : henv M) (G : handle_graph) : Prop :=
  sat_henkin M alpha rho (tau G).

Definition henkin_entails_graph (G H : handle_graph) : Prop :=
  forall M,
    henkin_comprehension_closed M ->
    forall alpha rho,
      henkin_env M rho ->
      graph_sat_henkin M alpha rho G ->
      graph_sat_henkin M alpha rho H.

Theorem formula_rule_entails_graph_henkin :
  forall G H,
    formula_rule (tau G) (tau H) ->
    henkin_entails_graph G H.
Proof.
  unfold henkin_entails_graph, graph_sat_henkin.
  intros G H Hr M Closed alpha rho Henv HG.
  eapply formula_rule_sound_henkin; eauto.
Qed.

Definition local_rule_sound_henkin : Prop :=
  forall G H, local_rule G H -> henkin_entails_graph G H.

Record henkin_local_rule_sound_cases : Prop := {
  henkin_sound_cut2 :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      henkin_entails_graph G H;
  henkin_sound_erase_positive :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      open_subgraph G ->
      henkin_entails_graph G H;
  henkin_sound_insert_negative :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      open_subgraph H ->
      henkin_entails_graph G H;
  henkin_sound_iter :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      henkin_entails_graph G H;
  henkin_sound_deiter :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness H G ->
      henkin_entails_graph G H;
  henkin_sound_eq_refl :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      open_subgraph H ->
      henkin_entails_graph G H;
  henkin_sound_eq_sub :
    forall G H,
      WellFormedGraph G ->
      WellFormedGraph H ->
      copy_witness G H ->
      henkin_entails_graph G H;
  henkin_sound_comprehension :
    forall G H ar X xs body,
      WellFormedGraph G ->
      WellFormedGraph H ->
      length xs = ar ->
      tau H = comprehension_formula ar X xs body ->
      henkin_entails_graph G H
}.

Theorem iso_rule_sound_henkin :
  forall G H,
    WellFormedGraph G ->
    WellFormedGraph H ->
    tau G = tau H ->
    henkin_entails_graph G H.
Proof.
  intros G H _ _ Htau.
  unfold henkin_entails_graph, graph_sat_henkin.
  intros M Closed alpha rho Henv HG.
  rewrite <- Htau. exact HG.
Qed.

Theorem local_rule_sound_henkin_from_cases :
  henkin_local_rule_sound_cases -> local_rule_sound_henkin.
Proof.
  intros Cases G H Hr.
  inversion Hr; subst.
  - eapply iso_rule_sound_henkin; eauto.
  - eapply henkin_sound_cut2; eauto.
  - eapply henkin_sound_erase_positive; eauto.
  - eapply henkin_sound_insert_negative; eauto.
  - eapply henkin_sound_iter; eauto.
  - eapply henkin_sound_deiter; eauto.
  - eapply henkin_sound_eq_refl; eauto.
  - eapply henkin_sound_eq_sub; eauto.
  - eapply henkin_sound_comprehension; eauto.
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
  intros Sound G H D.
  induction D as [G | G H K R D IH].
  - unfold henkin_entails_graph.
    intros M Closed alpha rho Henv HG. exact HG.
  - unfold henkin_entails_graph in *.
    intros M Closed alpha rho Henv HG.
    apply IH; try assumption.
    eapply Sound; eauto.
Qed.

Theorem derivation_sound_henkin_from_rule_cases :
  henkin_local_rule_sound_cases ->
  forall G H, derives G H -> henkin_entails_graph G H.
Proof.
  intros Cases.
  apply derivation_sound_henkin_conditional.
  exact (local_rule_sound_henkin_from_cases Cases).
Qed.

Theorem derivation_sound_henkin_direct :
  forall G H, derives G H -> henkin_entails_graph G H.
Proof.
  apply derivation_sound_henkin_conditional.
  exact local_rule_sound_henkin_direct.
Qed.

Record second_order_existential_graph_rev_system : Type := {
  fs_translate : handle_graph -> formula;
  fs_wf_graph : handle_graph -> Prop;
  fs_empty_graph : handle_graph -> Prop;
  fs_rule : handle_graph -> handle_graph -> Prop;
  fs_derives : handle_graph -> handle_graph -> Prop;
  fs_theorem_graph : handle_graph -> Prop;
  fs_full_consequence : handle_graph -> handle_graph -> Prop;
  fs_henkin_consequence : handle_graph -> handle_graph -> Prop;
  fs_full_model : full_model;
  fs_full_model_nontrivial :
    exists alpha : ienv fs_full_model,
    exists rho : renv fs_full_model,
      sat_full fs_full_model alpha rho FTop /\
      ~ sat_full fs_full_model alpha rho (FNeg FTop);
  fs_expression_graph : formula -> expression_graph;
  fs_empty_graph_wf :
    forall G, fs_empty_graph G -> fs_wf_graph G;
  fs_theorem_graph_iff :
    forall G,
      fs_theorem_graph G <->
      exists E, fs_empty_graph E /\ fs_derives E G;
  fs_translation_wf :
    forall G, fs_wf_graph G -> wf_formula (fs_translate G);
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
  fs_i_handle_monotone :
    forall G,
      fs_wf_graph G ->
      forall a b h,
        In a (regions G) ->
        In b (regions G) ->
        le_region G b a ->
        i_handle_available G a h ->
        i_handle_available G b h;
  fs_r_handle_monotone :
    forall G,
      fs_wf_graph G ->
      forall a b h,
        In a (regions G) ->
        In b (regions G) ->
        le_region G b a ->
        r_handle_available G a h ->
        r_handle_available G b h;
  fs_relation_handle_not_object :
    forall G h t, ~ relation_handle_as_object G h t;
  fs_individual_handle_name_source :
    forall G,
      fs_wf_graph G ->
      forall p,
        In p (objects G) ->
        individual_handle_name_source G
          (object_handle G p)
          (name_of_term (term_of_object G p));
  fs_relation_handle_name_source :
    forall G,
      fs_wf_graph G ->
      forall q,
        In q (apps G) ->
        relation_handle_name_source G
          (app_handle G q)
          (relation_name G (app_handle G q));
  fs_rule_source_wf :
    forall G H, fs_rule G H -> fs_wf_graph G;
  fs_rule_target_wf :
    forall G H, fs_rule G H -> fs_wf_graph H;
  fs_full_local_rule_sound :
    forall G H, fs_rule G H -> fs_full_consequence G H;
  fs_full_derivation_sound :
    forall G H, fs_derives G H -> fs_full_consequence G H;
  fs_henkin_local_rule_sound :
    forall G H, fs_rule G H -> fs_henkin_consequence G H;
  fs_henkin_derivation_sound :
    forall G H, fs_derives G H -> fs_henkin_consequence G H;
  fs_full_derivation_sound_conditional :
    (forall G H, fs_rule G H -> fs_full_consequence G H) ->
    forall G H, fs_derives G H -> fs_full_consequence G H;
  fs_henkin_derivation_sound_conditional :
    (forall G H, fs_rule G H -> fs_henkin_consequence G H) ->
    forall G H, fs_derives G H -> fs_henkin_consequence G H;
  fs_full_local_rule_sound_from_cases :
    full_local_rule_sound_cases ->
    forall G H, fs_rule G H -> fs_full_consequence G H;
  fs_full_derivation_sound_from_cases :
    full_local_rule_sound_cases ->
    forall G H, fs_derives G H -> fs_full_consequence G H;
  fs_henkin_local_rule_sound_from_cases :
    henkin_local_rule_sound_cases ->
    forall G H, fs_rule G H -> fs_henkin_consequence G H;
  fs_henkin_derivation_sound_from_cases :
    henkin_local_rule_sound_cases ->
    forall G H, fs_derives G H -> fs_henkin_consequence G H
}.

Definition B2eq_square_rev : second_order_existential_graph_rev_system := {|
  fs_translate := tau;
  fs_wf_graph := WellFormedGraph;
  fs_empty_graph := empty_graph_like;
  fs_rule := local_rule;
  fs_derives := derives;
  fs_theorem_graph := theorem_graph;
  fs_full_consequence := full_entails_graph;
  fs_henkin_consequence := henkin_entails_graph;
  fs_full_model := unit_full_model;
  fs_full_model_nontrivial := unit_full_model_nontrivial;
  fs_expression_graph := formula_to_expression_graph;
  fs_empty_graph_wf := empty_graph_like_wf;
  fs_theorem_graph_iff := theorem_graph_iff;
  fs_translation_wf := tau_well_formed;
  fs_expression_graph_formula := formula_to_expression_graph_formula;
  fs_expression_graph_wf := formula_to_expression_graph_wf;
  fs_expression_graph_full_equiv := expression_graph_full_equiv;
  fs_expression_graph_henkin_equiv := expression_graph_henkin_equiv;
  fs_i_handle_monotone := individual_handle_availability_descends;
  fs_r_handle_monotone := relation_handle_availability_descends;
  fs_relation_handle_not_object := relation_handle_not_object;
  fs_individual_handle_name_source := object_name_has_handle_source;
  fs_relation_handle_name_source := app_relation_name_has_handle_source;
  fs_rule_source_wf := local_rule_source_wf;
  fs_rule_target_wf := local_rule_target_wf;
  fs_full_local_rule_sound := local_rule_sound_full_direct;
  fs_full_derivation_sound := derivation_sound_full_direct;
  fs_henkin_local_rule_sound := local_rule_sound_henkin_direct;
  fs_henkin_derivation_sound := derivation_sound_henkin_direct;
  fs_full_derivation_sound_conditional := derivation_sound_full_conditional;
  fs_henkin_derivation_sound_conditional := derivation_sound_henkin_conditional;
  fs_full_local_rule_sound_from_cases := local_rule_sound_full_from_cases;
  fs_full_derivation_sound_from_cases := derivation_sound_full_from_rule_cases;
  fs_henkin_local_rule_sound_from_cases := local_rule_sound_henkin_from_cases;
  fs_henkin_derivation_sound_from_cases := derivation_sound_henkin_from_rule_cases
|}.

End SecondOrderExistentialGraphRevFaithful.
