From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Classes.RelationClasses.

Import ListNotations.

Module TopologicalSchematicLogic.

Definition Point := nat.
Definition String := list bool.
Definition Support := Point -> Prop.

Inductive Ty : Type :=
| Pt | Char | Conn | Sep | PtOn | Int | Grp | Reif.

Inductive Label : Type :=
| LString : String -> Label
| LBottom : Label.

Definition label_allowed (t : Ty) (l : Label) : Prop :=
  match t, l with
  | Char, LString _ => True
  | Reif, LString _ => True
  | Char, LBottom => False
  | Reif, LBottom => False
  | _, LBottom => True
  | _, LString _ => False
  end.

Definition subset_support (a b : Support) : Prop :=
  forall p, a p -> b p.

Definition support_disjoint (a b : Support) : Prop :=
  forall p, a p -> b p -> False.

Definition singleton_support (x : Point) : Support :=
  fun p => p = x.

Definition support_union (xs : list Support) : Support :=
  fun p => exists s, In s xs /\ s p.

Definition image_support (f : Point -> Point) (s : Support) : Support :=
  fun q => exists p, s p /\ q = f p.

Record TopologyFacts : Type := {
  bounded : Support -> Prop;
  connected : Support -> Prop;
  open_set : Support -> Prop;
  simple_arc_between : Support -> Support -> Support -> Prop;
  separator_support : Support -> Prop;
  separator_splits :
    Support -> Support -> Support -> Prop;
  support_image : (Point -> Point) -> Support -> Support;
  compact_supported_homeomorphism : (Point -> Point) -> Prop
}.

Record Component : Type := {
  cid : nat;
  cty : Ty;
  clabel : Label;
  csupport : Support;
  cdeps : list nat;
  crd : nat;
  c_label_ok : label_allowed cty clabel
}.

Inductive ConstructorTag : Type :=
| CPoint | CChar | CConn | CSep | CPtOn | CInt | CGrp | CReif.

Definition ids_of (xs : list Component) : list nat := map cid xs.

Definition components_by_ids (xs : list Component) (ids : list nat) : Prop :=
  forall n, In n ids -> exists c, In c xs /\ cid c = n.

Definition deps_closed_in (xs deps : list Component) : Prop :=
  forall c, In c deps -> In c xs.

Definition finite_dependency_closed (xs deps : list Component) : Prop :=
  deps_closed_in xs deps /\ NoDup (ids_of deps).

Inductive GeneratedByRule (geo : TopologyFacts)
    (xs : list Component) : ConstructorTag -> Component -> Prop :=
| GenC1Point :
    forall c x,
      cty c = Pt ->
      clabel c = LBottom ->
      csupport c = singleton_support x ->
      cdeps c = [] ->
      GeneratedByRule geo xs CPoint c
| GenC2Char :
    forall c s,
      cty c = Char ->
      clabel c = LString s ->
      open_set geo (csupport c) ->
      connected geo (csupport c) ->
      bounded geo (csupport c) ->
      cdeps c = [] ->
      GeneratedByRule geo xs CChar c
| GenC3Conn :
    forall c c1 c2,
      In c1 xs ->
      In c2 xs ->
      c1 <> c2 ->
      cty c = Conn ->
      clabel c = LBottom ->
      cdeps c = [cid c1; cid c2] ->
      simple_arc_between geo (csupport c) (csupport c1) (csupport c2) ->
      GeneratedByRule geo xs CConn c
| GenC4Sep :
    forall c c1 c2,
      In c1 xs ->
      In c2 xs ->
      c1 <> c2 ->
      cty c = Sep ->
      clabel c = LBottom ->
      cdeps c = [cid c1; cid c2] ->
      separator_support geo (csupport c) ->
      separator_splits geo (csupport c) (csupport c1) (csupport c2) ->
      GeneratedByRule geo xs CSep c
| GenC5PtOn :
    forall c cg x,
      In cg xs ->
      cty cg = Conn \/ cty cg = Sep ->
      csupport cg x ->
      cty c = PtOn ->
      clabel c = LBottom ->
      csupport c = singleton_support x ->
      cdeps c = [cid cg] ->
      GeneratedByRule geo xs CPtOn c
| GenC6Int :
    forall c ca cb x,
      In ca xs ->
      In cb xs ->
      cty ca = Conn \/ cty ca = Sep ->
      cty cb = Conn \/ cty cb = Sep ->
      csupport ca x ->
      csupport cb x ->
      cty c = Int ->
      clabel c = LBottom ->
      csupport c = singleton_support x ->
      cdeps c = [cid ca; cid cb] ->
      GeneratedByRule geo xs CInt c
| GenC7Grp :
    forall c deps,
      deps <> [] ->
      finite_dependency_closed xs deps ->
      cty c = Grp ->
      clabel c = LBottom ->
      csupport c = support_union (map csupport deps) ->
      cdeps c = ids_of deps ->
      GeneratedByRule geo xs CGrp c
| GenC8Reif :
    forall c deps,
      deps_closed_in xs deps ->
      NoDup (ids_of deps) ->
      cty c = Reif ->
      (exists code, clabel c = LString code) ->
      open_set geo (csupport c) ->
      connected geo (csupport c) ->
      bounded geo (csupport c) ->
      cdeps c = ids_of deps ->
      GeneratedByRule geo xs CReif c.

Inductive GeneratedComponent (geo : TopologyFacts) : Component -> Prop :=
| GeneratedIntro :
    forall xs tag c,
      Forall (GeneratedComponent geo) xs ->
      GeneratedByRule geo xs tag c ->
      GeneratedComponent geo c.

Definition DirectDep (xs : list Component) (a b : Component) : Prop :=
  In a xs /\ In b xs /\ In (cid a) (cdeps b).

Inductive Anc (xs : list Component) : Component -> Component -> Prop :=
| AncDirect :
    forall a b,
      DirectDep xs a b ->
      Anc xs a b
| AncStep :
    forall a b c,
      DirectDep xs a b ->
      Anc xs b c ->
      Anc xs a c.

Definition Core (xs : list Component) (c : Component) (p : Point) : Prop :=
  csupport c p /\ forall a, Anc xs a c -> ~ csupport a p.

Definition non_group (c : Component) : Prop := cty c <> Grp.

Definition incomparable (xs : list Component) (a b : Component) : Prop :=
  ~ Anc xs a b /\ ~ Anc xs b a.

Definition DepClosed (xs : list Component) : Prop :=
  forall b d,
    In b xs ->
    In d (cdeps b) ->
    exists a, In a xs /\ cid a = d.

Definition Acyclic (xs : list Component) : Prop :=
  forall c, In c xs -> ~ Anc xs c c.

Record Diagram : Type := {
  dcomps : list Component;
  d_closed : DepClosed dcomps;
  d_acyclic : Acyclic dcomps
}.

Definition component_ids (xs : list Component) : list nat := map cid xs.

Definition SpatialExclusive (xs : list Component) : Prop :=
  forall c d,
    In c xs ->
    In d xs ->
    c <> d ->
    non_group c ->
    non_group d ->
    incomparable xs c d ->
    support_disjoint (Core xs c) (Core xs d).

Definition LegalDiagram (d : Diagram) : Prop :=
  DepClosed (dcomps d) /\ Acyclic (dcomps d) /\
  NoDup (component_ids (dcomps d)) /\
  SpatialExclusive (dcomps d).

Definition SameComponentShape (c d : Component) : Prop :=
  cty d = cty c /\
  clabel d = clabel c /\
  cdeps d = cdeps c /\
  crd d = crd c.

Definition AbstractIso (xs ys : list Component) : Prop :=
  Forall2 SameComponentShape xs ys.

Record EncodedDag : Type := {
  dag_vertices : list nat;
  dag_edges : list (nat * nat);
  dag_labels : nat -> Ty * Label
}.

Definition induced_dag (xs : list Component) : EncodedDag := {|
  dag_vertices := map cid xs;
  dag_edges :=
    concat
      (map (fun b => map (fun a => (a, cid b)) (cdeps b)) xs);
  dag_labels := fun n =>
    match find (fun c => Nat.eqb (cid c) n) xs with
    | Some c => (cty c, clabel c)
    | None => (Pt, LBottom)
    end
|}.

Definition enc (g : EncodedDag) : String :=
  map Nat.odd (dag_vertices g).

Record EncodingFaithful : Type := {
  code_of : list Component -> String;
  code_abstract_iso :
    forall xs ys,
      DepClosed xs ->
      DepClosed ys ->
      Acyclic xs ->
      Acyclic ys ->
      code_of xs = code_of ys <-> AbstractIso xs ys
}.

Theorem abstract_iso_preserves_depth_multiset :
  forall xs ys,
    AbstractIso xs ys ->
    map crd xs = map crd ys.
Proof.
  intros xs ys h.
  induction h as [|x y xs ys hxy _ IH].
  - reflexivity.
  - simpl.
    destruct hxy as [_ [_ [_ hrd]]].
    rewrite hrd.
    now f_equal.
Qed.

Record TraceWitness (d e : Diagram) : Type := {
  trace_homeomorphism : Point -> Point;
  trace_pairs : list (nat * nat);
  trace_type_label :
    forall c n,
      In c (dcomps d) ->
      In (cid c, n) trace_pairs ->
      exists c',
        In c' (dcomps e) /\
        cid c' = n /\
        cty c' = cty c /\
        clabel c' = clabel c;
  trace_deps :
    forall c n,
      In c (dcomps d) ->
      In (cid c, n) trace_pairs ->
      exists c',
        In c' (dcomps e) /\
        cid c' = n /\
        cdeps c' = cdeps c;
  trace_support :
    forall c n,
      In c (dcomps d) ->
      In (cid c, n) trace_pairs ->
      exists c',
        In c' (dcomps e) /\
        cid c' = n /\
        csupport c' = image_support trace_homeomorphism (csupport c)
}.

Definition Homotopic (d e : Diagram) : Prop :=
  exists w : TraceWitness d e, True.

Inductive TraceEq : Diagram -> Diagram -> Prop :=
| TraceBase :
    forall d e, Homotopic d e -> TraceEq d e
| TraceRefl :
    forall d, TraceEq d d
| TraceSym :
    forall d e, TraceEq d e -> TraceEq e d
| TraceTrans :
    forall d e f, TraceEq d e -> TraceEq e f -> TraceEq d f.

Instance TraceEq_Equivalence : Equivalence TraceEq.
Proof.
  split.
  - intro x. apply TraceRefl.
  - intros x y h. exact (TraceSym x y h).
  - intros x y z hxy hyz. exact (TraceTrans x y z hxy hyz).
Qed.

Record RewriteRule : Type := {
  left_side : list Component;
  right_side : list Component;
  side_condition : Diagram -> Prop;
  rule_wellformed : DepClosed left_side /\ DepClosed right_side
}.

Record MatchCert (d : Diagram) (r : RewriteRule) : Type := {
  match_pairs : list (nat * nat);
  match_ok : Prop
}.

Record DangCert (d : Diagram) (r : RewriteRule) : Type := {
  dang_match : MatchCert d r;
  dangling_ok : Prop
}.

Record InstCert (d : Diagram) (r : RewriteRule) : Type := {
  inst_dang : DangCert d r;
  inst_added : list Component;
  inst_result : list Component;
  inst_ok : DepClosed inst_result /\ Acyclic inst_result
}.

Definition replace_result (d : Diagram) (r : RewriteRule) (i : InstCert d r)
    : Diagram := {|
  dcomps := inst_result d r i;
  d_closed := proj1 (inst_ok d r i);
  d_acyclic := proj2 (inst_ok d r i)
|}.

Definition StepTSL (d : Diagram) (r : RewriteRule) (e : Diagram) : Prop :=
  exists i : InstCert d r, dcomps e = dcomps (replace_result d r i).

Inductive Derives : Diagram -> Diagram -> Prop :=
| DerivesRefl :
    forall d, Derives d d
| DerivesStep :
    forall d e f r,
      StepTSL d r e ->
      Derives e f ->
      Derives d f.

Record DerivationCert (d e : Diagram) : Type := {
  cert_diagrams : list Diagram;
  cert_rules : list RewriteRule;
  cert_connects : Derives d e
}.

Definition HomClosedDerives (d e : Diagram) : Prop :=
  exists d' e',
    TraceEq d' d /\ TraceEq e' e /\ Derives d' e'.

Record HomClosedCert (d e : Diagram) : Type := {
  hcert_left : Diagram;
  hcert_right : Diagram;
  hcert_left_trace : TraceEq hcert_left d;
  hcert_right_trace : TraceEq hcert_right e;
  hcert_derivation : DerivationCert hcert_left hcert_right
}.

Theorem homotopy_closed_lifts_step :
  forall d d_star d' r,
    TraceEq d d_star ->
    StepTSL d r d' ->
    exists d_star',
      HomClosedDerives d_star d_star' /\ TraceEq d' d_star'.
Proof.
  intros d d_star d' r htrace hstep.
  exists d'.
  split.
  - unfold HomClosedDerives.
    exists d, d'.
    split; [exact htrace |].
    split; [apply TraceRefl |].
    apply DerivesStep with (e := d') (r := r).
    + exact hstep.
    + apply DerivesRefl.
  - apply TraceRefl.
Qed.

Record StructuralCopy (avoid : list nat) (a a' : Diagram) : Prop := {
  copy_trace : TraceEq a a';
  copy_avoids :
    forall c, In c (dcomps a') -> ~ In (cid c) avoid;
  copy_legal : LegalDiagram a'
}.

Record DereificationRule (c : Component) : Type := {
  dereif_is_reif : cty c = Reif;
  dereif_payload : Diagram;
  dereif_copy : Diagram;
  dereif_copy_cert :
    StructuralCopy (cid c :: cdeps c) dereif_payload dereif_copy;
  dereif_new_reif : Component;
  dereif_rule : RewriteRule;
  dereif_rule_left : left_side dereif_rule = [c];
  dereif_rule_right :
    right_side dereif_rule = dcomps dereif_copy ++ [dereif_new_reif]
}.

Definition CoreClassifies
    (geo : TopologyFacts) (xs : list Component)
    (tag : ConstructorTag) (c : Component) : Prop :=
  GeneratedByRule geo xs tag c /\
  match tag with
  | CPoint => forall p, Core (c :: xs) c p <-> csupport c p
  | CChar => forall p, Core (c :: xs) c p <-> csupport c p
  | CConn => forall p, Core (c :: xs) c p <->
      csupport c p /\
      forall a, Anc (c :: xs) a c -> ~ csupport a p
  | CSep => forall p, Core (c :: xs) c p <->
      csupport c p /\
      forall a, Anc (c :: xs) a c -> ~ csupport a p
  | CPtOn => forall p, ~ Core (c :: xs) c p
  | CInt => forall p, ~ Core (c :: xs) c p
  | CGrp => forall p, ~ Core (c :: xs) c p
  | CReif => forall p, Core (c :: xs) c p <->
      csupport c p /\
      forall a, Anc (c :: xs) a c -> ~ csupport a p
  end.

Definition rd_component (c : Component) : nat := crd c.

Definition DiagramLe (k : nat) (d : Diagram) : Prop :=
  Forall (fun c => rd_component c <= k) (dcomps d).

Record Fragment (k : nat) : Type := {
  fragment_diagram : Diagram -> Prop;
  fragment_step : Diagram -> RewriteRule -> Diagram -> Prop;
  fragment_closed :
    forall d r e,
      fragment_step d r e ->
      DiagramLe k d /\ DiagramLe k e
}.

Definition TSL_fragment (k : nat) : Fragment k := {|
  fragment_diagram := DiagramLe k;
  fragment_step := fun d r e =>
    DiagramLe k d /\ StepTSL d r e /\ DiagramLe k e;
  fragment_closed := fun d r e h =>
    match h with
    | conj hd (conj _ he) => conj hd he
    end
|}.

Definition component_at_depth (k id : nat) : Component := {|
  cid := id;
  cty := Reif;
  clabel := LString [];
  csupport := fun _ => False;
  cdeps := [];
  crd := k;
  c_label_ok := I
|}.

Lemma singleton_closed :
  forall c, cdeps c = [] -> DepClosed [c].
Proof.
  intros c hdeps b d hb hd.
  simpl in hb.
  destruct hb as [<- | []].
  rewrite hdeps in hd.
  contradiction.
Qed.

Lemma singleton_no_direct :
  forall c a b, cdeps c = [] -> ~ DirectDep [c] a b.
Proof.
  intros c a b hdeps h.
  destruct h as [ha [hb hin]].
  simpl in hb.
  destruct hb as [<- | []].
  rewrite hdeps in hin.
  contradiction.
Qed.

Lemma singleton_acyclic :
  forall c, cdeps c = [] -> Acyclic [c].
Proof.
  intros c hdeps x hx.
  simpl in hx.
  destruct hx as [<- | []].
  intro hanc.
  induction hanc as [a b hd | a b z hd _ IH].
  - exact (singleton_no_direct c a b hdeps hd).
  - exact (singleton_no_direct c a b hdeps hd).
Qed.

Definition singleton_diagram_at_depth (k : nat) : Diagram := {|
  dcomps := [component_at_depth k 0];
  d_closed := singleton_closed (component_at_depth k 0) eq_refl;
  d_acyclic := singleton_acyclic (component_at_depth k 0) eq_refl
|}.

Lemma singleton_depth_exact :
  forall k,
    DiagramLe k (singleton_diagram_at_depth k).
Proof.
  intro k.
  constructor; [simpl; lia | constructor].
Qed.

Lemma singleton_not_below :
  forall k,
    ~ DiagramLe k (singleton_diagram_at_depth (S k)).
Proof.
  intros k h.
  inversion h as [|c xs hc _]; subst.
  simpl in hc.
  lia.
Qed.

Theorem fragment_monotone :
  forall k d,
    DiagramLe k d -> DiagramLe (S k) d.
Proof.
  intros k d h.
  unfold DiagramLe in *.
  induction h as [|c xs hc hxs IH].
  - constructor.
  - constructor; [lia | exact IH].
Qed.

Theorem strict_hierarchy :
  forall k,
    exists d,
      DiagramLe (S k) d /\ ~ DiagramLe k d.
Proof.
  intro k.
  exists (singleton_diagram_at_depth (S k)).
  split.
  - apply singleton_depth_exact.
  - apply singleton_not_below.
Qed.

Record TopologicalSchematicLogicSystem : Type := {
  tsl_topology : Type;
  tsl_types : Type;
  tsl_components : Type;
  tsl_generated_rule :
    TopologyFacts -> list Component -> ConstructorTag -> Component -> Prop;
  tsl_generated_component :
    TopologyFacts -> Component -> Prop;
  tsl_encoding_faithful : Type;
  tsl_diagrams : Type;
  tsl_legal : Diagram -> Prop;
  tsl_trace_witness : Diagram -> Diagram -> Type;
  tsl_trace : Diagram -> Diagram -> Prop;
  tsl_rules : Type;
  tsl_step : Diagram -> RewriteRule -> Diagram -> Prop;
  tsl_derives : Diagram -> Diagram -> Prop;
  tsl_hom_closed_derives : Diagram -> Diagram -> Prop;
  tsl_structural_copy : list nat -> Diagram -> Diagram -> Prop;
  tsl_dereification_rule : Component -> Type;
  tsl_depth : Component -> nat;
  tsl_fragment : forall k : nat, Fragment k
}.

Definition TSL : TopologicalSchematicLogicSystem := {|
  tsl_topology := TopologyFacts;
  tsl_types := Ty;
  tsl_components := Component;
  tsl_generated_rule := GeneratedByRule;
  tsl_generated_component := GeneratedComponent;
  tsl_encoding_faithful := EncodingFaithful;
  tsl_diagrams := Diagram;
  tsl_legal := LegalDiagram;
  tsl_trace_witness := TraceWitness;
  tsl_trace := TraceEq;
  tsl_rules := RewriteRule;
  tsl_step := StepTSL;
  tsl_derives := Derives;
  tsl_hom_closed_derives := HomClosedDerives;
  tsl_structural_copy := StructuralCopy;
  tsl_dereification_rule := DereificationRule;
  tsl_depth := rd_component;
  tsl_fragment := TSL_fragment
|}.

End TopologicalSchematicLogic.
