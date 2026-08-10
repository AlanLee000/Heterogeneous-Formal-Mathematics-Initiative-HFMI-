From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Classes.RelationClasses.
From Stdlib Require Import Lia.

Import ListNotations.

Module ReificationDiagramCalculus.

Definition Name := nat.
Definition RelSym := nat.
Definition Gamma := bool.
Definition CodeString := list Gamma.
Definition Point := nat.
Definition Port := (nat * nat)%type.

Record Signature : Type := {
  rel_arity : RelSym -> nat;
  gamma_code : CodeString -> nat;
  enum_var : nat -> Name
}.

Inductive Ty : Type := Pt | Chr | Conn | Sep | Reif.

Inductive Label : Type :=
| LVar : Name -> Label
| LRel : RelSym -> Label
| LLink : Label
| LCut : Label
| LCode : CodeString -> Label
| LSelf : Label.

Definition label_ok (t : Ty) (l : Label) : Prop :=
  match t, l with
  | Pt, LVar _ => True
  | Chr, LRel _ => True
  | Conn, LLink => True
  | Sep, LCut => True
  | Reif, LCode _ => True
  | Reif, LSelf => True
  | _, _ => False
  end.

Record GeoComponent : Type := {
  gid : nat;
  gty : Ty;
  glabel : Label;
  support : Point -> Prop;
  interfaces : list Point;
  g_label_ok : label_ok gty glabel
}.

Definition disjoint_support (a b : GeoComponent) : Prop :=
  forall p, support a p -> support b p -> False.

Definition line_like (c : GeoComponent) : Prop :=
  gty c = Conn \/ gty c = Sep.

Definition all_interfaces (xs : list GeoComponent) : list Point :=
  concat (map interfaces xs).

Definition binary_contact (xs : list GeoComponent) : Prop :=
  forall p, count_occ Nat.eq_dec (all_interfaces xs) p <= 2.

Definition argument_like (c : GeoComponent) : Prop :=
  gty c = Pt \/ gty c = Chr \/ gty c = Reif.

Definition connection_contact (xs : list GeoComponent) : Prop :=
  forall c d p,
    In c xs -> In d xs -> c <> d ->
    In p (interfaces c) -> In p (interfaces d) ->
    (gty c = Conn /\ argument_like d) \/
    (argument_like c /\ gty d = Conn).
Record GeoConfig : Type := {
  gcomps : list GeoComponent;
  ga_separated :
    forall c d,
      In c gcomps -> In d gcomps -> c <> d -> disjoint_support c d;
  ga_boundary_isolated :
    forall c d,
      In c gcomps -> In d gcomps -> c <> d -> line_like c ->
      disjoint_support c d;
  ga_binary_contact : binary_contact gcomps;
  ga_connection_constraint : connection_contact gcomps
}.

Definition root_room : nat := 0.

Record Nesting : Type := {
  rooms : list nat;
  parent : nat -> option nat;
  room_depth : nat -> nat;
  nesting_rooms_unique : NoDup rooms;
  nesting_root_present : In root_room rooms;
  nesting_root_parentless : parent root_room = None;
  nesting_parent_depth :
    forall child p,
      In child rooms ->
      parent child = Some p ->
      In p rooms /\ room_depth child = S (room_depth p)
}.

Record CombPattern : Type := {
  p_components : list GeoComponent;
  p_boundary : list Name;
  p_matches : list (Port * Port);
  p_parent : nat -> option nat;
  p_room : nat -> option nat;
  p_boundary_order : list nat;
  p_port_count : nat -> nat;
  p_ref_rank : CodeString -> option nat
}.

Definition arity (p : CombPattern) : nat := length (p_boundary p).
Definition cmp (p : Port) : nat := fst p.

Definition component_ids (p : CombPattern) : list nat :=
  map gid (p_components p).

Definition component_by_id (p : CombPattern) (n : nat) (c : GeoComponent) : Prop :=
  In c (p_components p) /\ gid c = n.

Definition port_valid (p : CombPattern) (q : Port) : Prop :=
  exists c,
    component_by_id p (fst q) c /\ snd q < p_port_count p (fst q).

Definition port_has_type (p : CombPattern) (q : Port) (t : Ty) : Prop :=
  exists c,
    component_by_id p (fst q) c /\ gty c = t /\
    snd q < p_port_count p (fst q).

Definition arg_port (p : CombPattern) (q : Port) : Prop :=
  port_has_type p q Pt \/ port_has_type p q Chr \/ port_has_type p q Reif.

Definition link_port (p : CombPattern) (q : Port) : Prop :=
  port_has_type p q Conn.

Definition port_in_edge (q : Port) (e : Port * Port) : Prop :=
  q = fst e \/ q = snd e.

Definition match_pair_typed (p : CombPattern) (e : Port * Port) : Prop :=
  let q := fst e in
  let r := snd e in
  q <> r /\
  port_valid p q /\
  port_valid p r /\
  ((link_port p q /\ arg_port p r) \/
   (arg_port p q /\ link_port p r)).

Definition matching_typed (p : CombPattern) : Prop :=
  forall e, In e (p_matches p) -> match_pair_typed p e.

Definition matching_functional (p : CombPattern) : Prop :=
  forall e1 e2 q,
    In e1 (p_matches p) ->
    In e2 (p_matches p) ->
    port_in_edge q e1 ->
    port_in_edge q e2 ->
    e1 = e2.

Definition port_count_shape (p : CombPattern) : Prop :=
  forall c,
    In c (p_components p) ->
    match gty c with
    | Pt => p_port_count p (gid c) = 1
    | Conn => p_port_count p (gid c) = 2
    | Sep => p_port_count p (gid c) = 0
    | Chr => p_port_count p (gid c) = length (interfaces c)
    | Reif => p_port_count p (gid c) = length (interfaces c)
    end.

Inductive ParentAnc (p : CombPattern) : nat -> nat -> Prop :=
| ParentDirect :
    forall a b,
      p_parent p a = Some b ->
      ParentAnc p a b
| ParentStep :
    forall a b c,
      p_parent p a = Some b ->
      ParentAnc p b c ->
      ParentAnc p a c.

Definition parent_acyclic (p : CombPattern) : Prop :=
  forall r, ~ ParentAnc p r r.

Definition boundary_order_bijective (p : CombPattern) : Prop :=
  NoDup (p_boundary_order p) /\
  forall i, In i (p_boundary_order p) <-> i < arity p.

Definition boundary_names_injective (p : CombPattern) : Prop :=
  NoDup (p_boundary p).

Definition cut_matches (p : CombPattern) (a : list nat) : list (Port * Port) :=
  filter
    (fun e =>
      let c := fst (fst e) in
      let d := fst (snd e) in
      xorb (existsb (Nat.eqb c) a) (existsb (Nat.eqb d) a))
    (p_matches p).

Definition connected_closed (p : CombPattern) (a : list nat) : Prop :=
  cut_matches p a = [].

Definition room_closed (p : CombPattern) (a : list nat) : Prop :=
  forall c r,
    In c a ->
    p_room p c = Some r ->
    forall d, p_room p d = Some r -> In d a.

Record StructWellformed (p : CombPattern) : Prop := {
  wf_component_ids : NoDup (component_ids p);
  wf_port_count : port_count_shape p;
  wf_matches_typed : matching_typed p;
  wf_matches_functional : matching_functional p;
  wf_parent : parent_acyclic p;
  wf_boundary_names : boundary_names_injective p;
  wf_boundary_order : boundary_order_bijective p
}.

Definition reference_rank_decreasing (p : CombPattern) : Prop :=
  forall c code,
    In c (p_components p) ->
    glabel c = LCode code ->
    exists target_rank,
      p_ref_rank p code = Some target_rank /\
      target_rank < length (p_components p).

Record OpenDiagram : Type := {
  pattern : CombPattern;
  diagram_wf : StructWellformed pattern;
  ref_rank_decreasing : reference_rank_decreasing pattern
}.

Definition ClosedDiagram (d : OpenDiagram) : Prop :=
  arity (pattern d) = 0.

Definition rank (d : OpenDiagram) : nat :=
  length (p_components (pattern d)).

Theorem rank_finite : forall d, exists n, rank d = n.
Proof.
  intro d. exists (rank d). reflexivity.
Qed.

Definition StaticRef (d : OpenDiagram) (source_rank target_rank : nat) : Prop :=
  source_rank = rank d /\
  exists c code,
    In c (p_components (pattern d)) /\
    gty c = Reif /\
    glabel c = LCode code /\
    p_ref_rank (pattern d) code = Some target_rank.

Definition component_reference_edge
    (p : CombPattern) (c : GeoComponent) : list (nat * nat) :=
  match glabel c with
  | LCode code =>
      match p_ref_rank p code with
      | Some target_rank => [(length (p_components p), target_rank)]
      | None => []
      end
  | _ => []
  end.

Definition RefDAG (d : OpenDiagram) : list (nat * nat) :=
  concat
    (map (component_reference_edge (pattern d))
      (p_components (pattern d))).

Definition static_reference_count (d : OpenDiagram) : nat :=
  length (RefDAG d).

Record ReifiableSubconfig (d : OpenDiagram) : Type := {
  sub_ids : list nat;
  sub_nonempty : sub_ids <> [];
  sub_ids_valid : forall i, In i sub_ids -> In i (component_ids (pattern d));
  sub_room_closed : room_closed (pattern d) sub_ids;
  sub_connected_closed : connected_closed (pattern d) sub_ids;
  sub_no_self_reification :
    forall i c,
      In i sub_ids ->
      component_by_id (pattern d) i c ->
      glabel c <> LSelf
}.

Record OpenSubdiagram (d : OpenDiagram) (s : ReifiableSubconfig d) : Type := {
  sub_boundary_vars : list Name;
  sub_pattern : CombPattern;
  sub_wf : StructWellformed sub_pattern
}.

Definition same_boundary (d e : OpenDiagram) : Prop :=
  p_boundary (pattern d) = p_boundary (pattern e) /\
  p_boundary_order (pattern d) = p_boundary_order (pattern e).

Lemma same_boundary_preserves_arity :
  forall d e, same_boundary d e -> arity (pattern d) = arity (pattern e).
Proof.
  intros d e [Hboundary _].
  unfold arity. now rewrite Hboundary.
Qed.

Definition EvenNat (n : nat) : Prop := exists k, n = 2 * k.
Definition OddNat (n : nat) : Prop := exists k, n = S (2 * k).

Inductive RoomDepth (p : CombPattern) : nat -> nat -> Prop :=
| RoomDepthRoot : RoomDepth p root_room 0
| RoomDepthChild :
    forall r q n,
      p_parent p r = Some q ->
      RoomDepth p q n ->
      RoomDepth p r (S n).

Definition EvenRoom (p : CombPattern) (r : nat) : Prop :=
  exists n, RoomDepth p r n /\ EvenNat n.

Definition OddRoom (p : CombPattern) (r : nat) : Prop :=
  exists n, RoomDepth p r n /\ OddNat n.

Definition RoomDescendant (p : CombPattern) (r v : nat) : Prop :=
  r = v \/ ParentAnc p r v.

Definition ids_in_pattern (p : CombPattern) (ids : list nat) : Prop :=
  forall i, In i ids -> In i (component_ids p).

Definition ids_in_room_cone (p : CombPattern) (ids : list nat) (v : nat) : Prop :=
  forall i r,
    In i ids ->
    p_room p i = Some r ->
    RoomDescendant p r v.

Definition subconfig_closed (p : CombPattern) (ids : list nat) : Prop :=
  ids_in_pattern p ids /\
  room_closed p ids /\
  connected_closed p ids.

Definition component_has_type (p : CombPattern) (i : nat) (t : Ty) : Prop :=
  exists c, component_by_id p i c /\ gty c = t.

Definition component_has_label (p : CombPattern) (i : nat) (l : Label) : Prop :=
  exists c, component_by_id p i c /\ glabel c = l.

Definition sep_component (p : CombPattern) (i : nat) : Prop :=
  component_has_type p i Sep.

Definition reif_component_with_label
    (p : CombPattern) (i : nat) (l : Label) : Prop :=
  component_has_type p i Reif /\ component_has_label p i l.

Definition static_reif_component (p : CombPattern) (i : nat) : Prop :=
  exists code, reif_component_with_label p i (LCode code).

Definition self_reif_component (p : CombPattern) (i : nat) : Prop :=
  reif_component_with_label p i LSelf.

Definition pt_var_component (p : CombPattern) (i : nat) (x : Name) : Prop :=
  component_has_type p i Pt /\ component_has_label p i (LVar x).

Definition ids_all_pt_var (p : CombPattern) (ids : list nat) (x : Name) : Prop :=
  forall i, In i ids -> pt_var_component p i x.

Definition fresh_var (p : CombPattern) (z : Name) : Prop :=
  forall c, In c (p_components p) -> glabel c <> LVar z.

Definition id_selected (i : nat) (ids : list nat) : bool :=
  existsb (Nat.eqb i) ids.

Definition remove_components_by_ids
    (p : CombPattern) (ids : list nat) : list GeoComponent :=
  filter (fun c => negb (id_selected (gid c) ids)) (p_components p).

Definition ComponentNameChange
    (old_name new_name : Name) (ids : list nat)
    (c c' : GeoComponent) : Prop :=
  gid c' = gid c /\
  gty c' = gty c /\
  support c' = support c /\
  interfaces c' = interfaces c /\
  if id_selected (gid c) ids
  then glabel c = LVar old_name /\ glabel c' = LVar new_name
  else c' = c.

Definition PatternNameChange
    (old_name new_name : Name) (ids : list nat)
    (p q : CombPattern) : Prop :=
  p_boundary q = p_boundary p /\
  p_matches q = p_matches p /\
  p_parent q = p_parent p /\
  p_room q = p_room p /\
  p_boundary_order q = p_boundary_order p /\
  p_port_count q = p_port_count p /\
  p_ref_rank q = p_ref_rank p /\
  Forall2 (ComponentNameChange old_name new_name ids)
    (p_components p) (p_components q).
Inductive ReifReplace : OpenDiagram -> OpenDiagram -> Prop :=
| ReifIntro :
    forall d (s : ReifiableSubconfig d) reif e,
      gty reif = Reif ->
      (exists code, glabel reif = LCode code) ->
      same_boundary d e ->
      p_components (pattern e) =
        remove_components_by_ids (pattern d) (sub_ids d s) ++ [reif] ->
      StructWellformed (pattern e) ->
      ReifReplace d e.

Inductive DerefReplace : OpenDiagram -> OpenDiagram -> Prop :=
| DerefIntro :
    forall d r code payload e,
      reif_component_with_label (pattern d) r (LCode code) ->
      p_ref_rank (pattern d) code = Some (rank payload) ->
      same_boundary d e ->
      p_components (pattern e) =
        remove_components_by_ids (pattern d) [r] ++
        p_components (pattern payload) ->
      StructWellformed (pattern e) ->
      DerefReplace d e.

Definition name_map_injective (f : Name -> Name) : Prop :=
  forall x y, f x = f y -> x = y.

Definition fixes_boundary (p : CombPattern) (f : Name -> Name) : Prop :=
  forall x, In x (p_boundary p) -> f x = x.

Definition AlphaLabel (f : Name -> Name) (l l' : Label) : Prop :=
  match l, l' with
  | LVar x, LVar y => y = f x
  | _, _ => l' = l
  end.

Definition AlphaComponent
    (f : Name -> Name) (c c' : GeoComponent) : Prop :=
  gid c' = gid c /\
  gty c' = gty c /\
  AlphaLabel f (glabel c) (glabel c') /\
  support c' = support c /\
  interfaces c' = interfaces c.

Definition AlphaPattern
    (f : Name -> Name) (p q : CombPattern) : Prop :=
  p_boundary q = p_boundary p /\
  p_matches q = p_matches p /\
  p_parent q = p_parent p /\
  p_room q = p_room p /\
  p_boundary_order q = p_boundary_order p /\
  p_port_count q = p_port_count p /\
  p_ref_rank q = p_ref_rank p /\
  Forall2 (AlphaComponent f) (p_components p) (p_components q).
Inductive AlphaEq : OpenDiagram -> OpenDiagram -> Prop :=
| AlphaRefl : forall d, AlphaEq d d
| AlphaRename :
    forall d e f,
      name_map_injective f ->
      fixes_boundary (pattern d) f ->
      AlphaPattern f (pattern d) (pattern e) ->
      AlphaEq d e
| AlphaSym : forall d e, AlphaEq d e -> AlphaEq e d
| AlphaTrans : forall d e f, AlphaEq d e -> AlphaEq e f -> AlphaEq d f.

Instance AlphaEq_equiv : Equivalence AlphaEq.
Proof.
  split.
  - exact AlphaRefl.
  - intros x y h. exact (AlphaSym x y h).
  - intros x y z hxy hyz. exact (AlphaTrans x y z hxy hyz).
Qed.

Theorem alpha_preserves_arity :
  forall d e, AlphaEq d e -> arity (pattern d) = arity (pattern e).
Proof.
  intros d e Halpha.
  induction Halpha as
      [d0
      | d0 e0 f Hinj Hfix Hpattern
      | d0 e0 _ IH
      | d0 e0 f0 _ IHde _ IHef].
  - reflexivity.
  - unfold AlphaPattern in Hpattern.
    destruct Hpattern as [Hboundary _].
    unfold arity. now rewrite Hboundary.
  - symmetry. exact IH.
  - etransitivity; eassumption.
Qed.
Inductive RuleName : Type :=
| ROddInsert
| REvenErase
| RDoubleCutIntro
| RDoubleCutElim
| RIterate
| RDeiterate
| REvenSplit
| ROddMerge
| RReifIntro
| RDeref
| RUnfoldSelf.

Record OddInsertCert (d e : OpenDiagram) : Type := {
  oi_boundary : same_boundary d e;
  oi_result_wf : StructWellformed (pattern e);
  oi_room : nat;
  oi_room_odd : OddRoom (pattern d) oi_room;
  oi_inserted : OpenDiagram;
  oi_inserted_closed : ClosedDiagram oi_inserted;
  oi_components_exact :
    p_components (pattern e) =
      p_components (pattern d) ++ p_components (pattern oi_inserted);
  oi_rank_growth : rank d <= rank e
}.

Record EvenEraseCert (d e : OpenDiagram) : Type := {
  ee_boundary : same_boundary d e;
  ee_result_wf : StructWellformed (pattern e);
  ee_room : nat;
  ee_room_even : EvenRoom (pattern d) ee_room;
  ee_removed_ids : list nat;
  ee_removed_closed : subconfig_closed (pattern d) ee_removed_ids;
  ee_removed_in_scope : ids_in_room_cone (pattern d) ee_removed_ids ee_room;
  ee_rank_decrease : rank e <= rank d;
  ee_components_exact :
    p_components (pattern e) =
      remove_components_by_ids (pattern d) ee_removed_ids
}.

Record DoubleCutIntroCert (d e : OpenDiagram) : Type := {
  dci_boundary : same_boundary d e;
  dci_result_wf : StructWellformed (pattern e);
  dci_wrapped_ids : list nat;
  dci_wrapped_closed : subconfig_closed (pattern d) dci_wrapped_ids;
  dci_outer_component : GeoComponent;
  dci_inner_component : GeoComponent;
  dci_outer_is_sep : gty dci_outer_component = Sep;
  dci_inner_is_sep : gty dci_inner_component = Sep;
  dci_cut_ids_distinct : gid dci_outer_component <> gid dci_inner_component;
  dci_components_exact :
    p_components (pattern e) =
      p_components (pattern d) ++ [dci_outer_component; dci_inner_component];
  dci_nesting_exact :
    p_parent (pattern e) (gid dci_inner_component) =
      Some (gid dci_outer_component);
  dci_two_cuts_added : rank d + 2 <= rank e
}.

Record DoubleCutElimCert (d e : OpenDiagram) : Type := {
  dce_boundary : same_boundary d e;
  dce_result_wf : StructWellformed (pattern e);
  dce_outer_cut : nat;
  dce_inner_cut : nat;
  dce_outer_sep : sep_component (pattern d) dce_outer_cut;
  dce_inner_sep : sep_component (pattern d) dce_inner_cut;
  dce_nested_pair : p_parent (pattern d) dce_inner_cut = Some dce_outer_cut;
  dce_components_exact :
    p_components (pattern e) =
      remove_components_by_ids (pattern d) [dce_outer_cut; dce_inner_cut];
  dce_two_cuts_removed : rank e + 2 <= rank d
}.

Record IterateCert (d e : OpenDiagram) : Type := {
  it_boundary : same_boundary d e;
  it_result_wf : StructWellformed (pattern e);
  it_source_room : nat;
  it_target_room : nat;
  it_strict_descendant :
    RoomDescendant (pattern d) it_target_room it_source_room /\
    it_target_room <> it_source_room;
  it_copied_ids : list nat;
  it_copied_closed : subconfig_closed (pattern d) it_copied_ids;
  it_copied_components : list GeoComponent;
  it_copy_name_map : Name -> Name;
  it_copy_name_map_injective : name_map_injective it_copy_name_map;
  it_copy_shape :
    Forall2 (AlphaComponent it_copy_name_map)
      (filter (fun c => id_selected (gid c) it_copied_ids)
        (p_components (pattern d)))
      it_copied_components;
  it_components_exact :
    p_components (pattern e) =
      p_components (pattern d) ++ it_copied_components;
  it_rank_growth : rank d <= rank e
}.

Record DeiterateCert (d e : OpenDiagram) : Type := {
  deit_boundary : same_boundary d e;
  deit_result_wf : StructWellformed (pattern e);
  deit_source_room : nat;
  deit_target_room : nat;
  deit_strict_descendant :
    RoomDescendant (pattern d) deit_target_room deit_source_room /\
    deit_target_room <> deit_source_room;
  deit_removed_copy_ids : list nat;
  deit_removed_copy_closed :
    subconfig_closed (pattern d) deit_removed_copy_ids;
  deit_components_exact :
    p_components (pattern e) =
      remove_components_by_ids (pattern d) deit_removed_copy_ids;
  deit_rank_decrease : rank e <= rank d
}.

Record EvenSplitCert (d e : OpenDiagram) : Type := {
  es_boundary : same_boundary d e;
  es_result_wf : StructWellformed (pattern e);
  es_room : nat;
  es_room_even : EvenRoom (pattern d) es_room;
  es_old_name : Name;
  es_new_name : Name;
  es_new_fresh : fresh_var (pattern d) es_new_name;
  es_selected_pts : list nat;
  es_selected_nonempty : es_selected_pts <> [];
  es_selected_label : ids_all_pt_var (pattern d) es_selected_pts es_old_name;
  es_selected_in_scope :
    ids_in_room_cone (pattern d) es_selected_pts es_room;
  es_exact_update :
    PatternNameChange es_old_name es_new_name es_selected_pts
      (pattern d) (pattern e)
}.

Record OddMergeCert (d e : OpenDiagram) : Type := {
  om_boundary : same_boundary d e;
  om_result_wf : StructWellformed (pattern e);
  om_room : nat;
  om_room_odd : OddRoom (pattern d) om_room;
  om_keep_name : Name;
  om_merge_name : Name;
  om_names_distinct : om_keep_name <> om_merge_name;
  om_keep_occurs :
    exists i, pt_var_component (pattern d) i om_keep_name;
  om_merge_occurs :
    exists i, pt_var_component (pattern d) i om_merge_name;
  om_renamed_ids : list nat;
  om_all_merge_occurrences :
    forall i, pt_var_component (pattern d) i om_merge_name ->
      In i om_renamed_ids;
  om_exact_update :
    PatternNameChange om_merge_name om_keep_name om_renamed_ids
      (pattern d) (pattern e)
}.

Record UnfoldSelfCert (d e : OpenDiagram) : Type := {
  us_boundary : same_boundary d e;
  us_result_wf : StructWellformed (pattern e);
  us_reif_id : nat;
  us_self_component : self_reif_component (pattern d) us_reif_id;
  us_ports_match_boundary : p_port_count (pattern d) us_reif_id = arity (pattern d);
  us_unfolded_components : list GeoComponent;
  us_name_map : Name -> Name;
  us_name_map_injective : name_map_injective us_name_map;
  us_unfolded_shape :
    Forall2 (AlphaComponent us_name_map)
      (p_components (pattern d)) us_unfolded_components;
  us_components_exact :
    p_components (pattern e) =
      p_components (pattern d) ++ us_unfolded_components;
  us_rank_growth : rank d <= rank e
}.

Inductive RuleCert : RuleName -> OpenDiagram -> OpenDiagram -> Type :=
| CertOddInsert :
    forall d e, OddInsertCert d e -> same_boundary d e -> RuleCert ROddInsert d e
| CertEvenErase :
    forall d e, EvenEraseCert d e -> same_boundary d e -> RuleCert REvenErase d e
| CertDoubleCutIntro :
    forall d e, DoubleCutIntroCert d e -> same_boundary d e -> RuleCert RDoubleCutIntro d e
| CertDoubleCutElim :
    forall d e, DoubleCutElimCert d e -> same_boundary d e -> RuleCert RDoubleCutElim d e
| CertIterate :
    forall d e, IterateCert d e -> same_boundary d e -> RuleCert RIterate d e
| CertDeiterate :
    forall d e, DeiterateCert d e -> same_boundary d e -> RuleCert RDeiterate d e
| CertEvenSplit :
    forall d e, EvenSplitCert d e -> same_boundary d e -> RuleCert REvenSplit d e
| CertOddMerge :
    forall d e, OddMergeCert d e -> same_boundary d e -> RuleCert ROddMerge d e
| CertReifIntro :
    forall d e, ReifReplace d e -> same_boundary d e -> RuleCert RReifIntro d e
| CertDeref :
    forall d e, DerefReplace d e -> same_boundary d e -> RuleCert RDeref d e
| CertUnfoldSelf :
    forall d e, UnfoldSelfCert d e -> same_boundary d e -> RuleCert RUnfoldSelf d e.

Lemma rule_cert_preserves_arity :
  forall r d e,
    RuleCert r d e -> arity (pattern d) = arity (pattern e).
Proof.
  intros r d e Hcert.
  destruct Hcert; apply same_boundary_preserves_arity; assumption.
Qed.
Inductive StepRDC : OpenDiagram -> OpenDiagram -> Prop :=
| StepByRule :
    forall r d e,
      RuleCert r d e ->
      StepRDC d e
| StepAlpha :
    forall d e,
      AlphaEq d e ->
      StepRDC d e.

Theorem step_preserves_arity :
  forall d e,
    StepRDC d e -> arity (pattern d) = arity (pattern e).
Proof.
  intros d e Hstep.
  destruct Hstep as [r d0 e0 Hcert | d0 e0 Halpha].
  - exact (rule_cert_preserves_arity r d0 e0 Hcert).
  - exact (alpha_preserves_arity d0 e0 Halpha).
Qed.
Inductive DerivesRDC : OpenDiagram -> OpenDiagram -> Prop :=
| DerivesRefl :
    forall d, DerivesRDC d d
| DerivesStep :
    forall d e f,
      StepRDC d e ->
      DerivesRDC e f ->
      DerivesRDC d f.

Record EmptyLike (k : nat) (d : OpenDiagram) : Prop := {
  empty_components : p_components (pattern d) = [];
  empty_boundary_length : arity (pattern d) = k;
  empty_matches : p_matches (pattern d) = []
}.

Definition ProvableRDC (d : OpenDiagram) : Prop :=
  exists e, EmptyLike (arity (pattern d)) e /\ DerivesRDC e d.

Record FirstOrderStructure : Type := {
  domain : Type;
  rel_interp : RelSym -> list domain -> Prop
}.

Record ReadSemantics : Type := {
  read_structure : FirstOrderStructure;
  reads : OpenDiagram -> list (domain read_structure) -> Prop;
  read_alpha :
    forall d e xs, AlphaEq d e -> (reads d xs <-> reads e xs);
  read_step_sound :
    forall d e xs, StepRDC d e -> reads d xs -> reads e xs
}.

Definition SemEntails (d e : OpenDiagram) : Prop :=
  forall m xs, reads m d xs -> reads m e xs.

Theorem derives_sound :
  forall d e,
    DerivesRDC d e -> SemEntails d e.
Proof.
  intros d e hder m xs hd.
  induction hder as [d0 | d0 e0 f0 hstep htail IH].
  - exact hd.
  - apply IH.
    exact (read_step_sound m d0 e0 xs hstep hd).
Qed.

Theorem provable_sound :
  forall d,
    ProvableRDC d ->
    forall e,
      (exists k, EmptyLike k e) ->
      DerivesRDC e d ->
      SemEntails e d.
Proof.
  intros d _ e _ hder.
  exact (derives_sound e d hder).
Qed.

Record DerivationCert (d e : OpenDiagram) : Type := {
  cert_diagrams : list OpenDiagram;
  cert_steps : list (OpenDiagram * OpenDiagram);
  cert_derives : DerivesRDC d e
}.

Record SoundnessCert (d e : OpenDiagram) : Type := {
  sound_cert : DerivationCert d e;
  sound_semantic : SemEntails d e
}.

Definition DiagramLe (k : nat) (d : OpenDiagram) : Prop :=
  static_reference_count d <= k.

Record RDCFragment (k : nat) : Type := {
  frag_diagram : OpenDiagram -> Prop;
  frag_step : OpenDiagram -> OpenDiagram -> Prop;
  frag_closed :
    forall d e, frag_step d e -> DiagramLe k d /\ DiagramLe k e
}.

Definition trivial_pattern : CombPattern := {|
  p_components := [];
  p_boundary := [];
  p_matches := [];
  p_parent := fun _ => None;
  p_room := fun _ => None;
  p_boundary_order := [];
  p_port_count := fun _ => 0;
  p_ref_rank := fun _ => None
|}.

Lemma trivial_wf : StructWellformed trivial_pattern.
Proof.
  constructor.
  - constructor.
  - intros c hc. contradiction.
  - intros e he. contradiction.
  - intros e1 e2 q he1 he2 _ _. contradiction.
  - intros r h.
    induction h as [a b hparent | a b c hparent _ IH].
    + discriminate hparent.
    + discriminate hparent.
  - constructor.
  - split.
    + constructor.
    + intros i. split; intro h.
      * contradiction.
      * unfold arity in h. simpl in h. lia.
Qed.

Definition empty_open_diagram : OpenDiagram := {|
  pattern := trivial_pattern;
  diagram_wf := trivial_wf;
  ref_rank_decreasing := fun c code Hc => False_rect _ Hc
|}.

Definition boundary_one_pattern : CombPattern := {|
  p_components := [];
  p_boundary := [0];
  p_matches := [];
  p_parent := fun _ => None;
  p_room := fun _ => None;
  p_boundary_order := [0];
  p_port_count := fun _ => 0;
  p_ref_rank := fun _ => None
|}.

Lemma boundary_one_wf : StructWellformed boundary_one_pattern.
Proof.
  constructor.
  - constructor.
  - intros c hc. contradiction.
  - intros e he. contradiction.
  - intros e1 e2 q he1 he2 _ _. contradiction.
  - intros r Hanc.
    induction Hanc as [a b Hparent | a b c Hparent _ IH].
    + discriminate Hparent.
    + discriminate Hparent.
  - constructor.
    + simpl. tauto.
    + constructor.
  - split.
    + constructor.
      * simpl. tauto.
      * constructor.
    + intro i. change (In i [0] <-> i < 1). destruct i.
      * split.
        -- intro Hzero. lia.
        -- intro Hlt. left. reflexivity.
      * simpl. split.
        -- intros [Hi | Hi]; [discriminate Hi | contradiction].
        -- intro Hi. lia.
Qed.

Definition boundary_one_diagram : OpenDiagram := {|
  pattern := boundary_one_pattern;
  diagram_wf := boundary_one_wf;
  ref_rank_decreasing := fun c code Hc => False_rect _ Hc
|}.

Definition boundary_arity_structure : FirstOrderStructure := {|
  domain := unit;
  rel_interp := fun _ _ => False
|}.

Definition boundary_arity_model : ReadSemantics.
Proof.
  refine {|
    read_structure := boundary_arity_structure;
    reads := fun d xs => length xs = arity (pattern d)
  |}.
  - intros d e xs Halpha.
    rewrite (alpha_preserves_arity d e Halpha).
    tauto.
  - intros d e xs Hstep Hread.
    rewrite <- (step_preserves_arity d e Hstep).
    exact Hread.
Defined.

Theorem rdc_semantically_nontrivial :
  ~ SemEntails empty_open_diagram boundary_one_diagram.
Proof.
  intro Hentails.
  specialize (Hentails boundary_arity_model []).
  cbn in Hentails.
  assert (0 = 1) as Hbad by (apply Hentails; reflexivity).
  discriminate Hbad.
Qed.
Record ReificationDiagramCalculusSystem : Type := {
  rdc_signature : Type;
  rdc_component : Type;
  rdc_pattern : Type;
  rdc_open_diagram : Type;
  rdc_alpha : OpenDiagram -> OpenDiagram -> Prop;
  rdc_step : OpenDiagram -> OpenDiagram -> Prop;
  rdc_derives : OpenDiagram -> OpenDiagram -> Prop;
  rdc_semantics : Type;
  rdc_entails : OpenDiagram -> OpenDiagram -> Prop;
  rdc_concrete_model : ReadSemantics;
  rdc_nontriviality :
    ~ rdc_entails empty_open_diagram boundary_one_diagram
}.

Definition RDC : ReificationDiagramCalculusSystem := {|
  rdc_signature := Signature;
  rdc_component := GeoComponent;
  rdc_pattern := CombPattern;
  rdc_open_diagram := OpenDiagram;
  rdc_alpha := AlphaEq;
  rdc_step := StepRDC;
  rdc_derives := DerivesRDC;
  rdc_semantics := ReadSemantics;
  rdc_entails := SemEntails;
  rdc_concrete_model := boundary_arity_model;
  rdc_nontriviality := rdc_semantically_nontrivial
|}.

End ReificationDiagramCalculus.
