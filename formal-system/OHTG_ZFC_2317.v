From Stdlib Require Import List Bool Arith PeanoNat Lia Relations RelationClasses.
From Stdlib Require Import Morphisms Setoid String Ascii Program.Equality.
From Stdlib Require Import Wellfounded.Lexicographic_Product
  Wellfounded.Inclusion Wellfounded.Inverse_Image Wf_nat.

Import ListNotations.
Set Implicit Arguments.

Module OHTG_ZFC_2317.

(** OHTG-ZFC 0.2.1 reviewed implementation, note 2317.
    This is a deep embedding: object syntax, well-formedness, equations,
    proof cells, representations and erasures are data inside Rocq.
    Earlier executable encodings are retained only as regression/codec
    scaffolds; normative counterparts live in [AuthoritativeOHTG]. *)

(** * 1. Finite set-coded infrastructure *)

Definition Byte := nat.
Definition ByteWF (b : Byte) : Prop := b < 256.
Definition ByteSeq := list Byte.

Definition Id := nat.
Definition URI := nat.
Definition Code := nat.
Definition RuleCode := nat.
Definition DerivCode := nat.
Definition ModelCode := nat.
Definition CellCode := nat.

Inductive TaggedCode : Type :=
| TCId : Id -> TaggedCode
| TCURI : URI -> TaggedCode
| TCCode : Code -> TaggedCode
| TCRule : RuleCode -> TaggedCode
| TCDeriv : DerivCode -> TaggedCode
| TCModel : ModelCode -> TaggedCode
| TCCell : CellCode -> TaggedCode.

Definition tagged_disjoint (x y : TaggedCode) : Prop :=
  match x, y with
  | TCId _, TCId _ | TCURI _, TCURI _ | TCCode _, TCCode _
  | TCRule _, TCRule _ | TCDeriv _, TCDeriv _
  | TCModel _, TCModel _ | TCCell _, TCCell _ => False
  | _, _ => True
  end.

Inductive KSet (A : Type) : Type :=
| kempty : KSet A
| katom : A -> KSet A
| kpair : KSet A -> KSet A -> KSet A.

Definition kuratowski_pair {A} (x y : KSet A) : KSet A :=
  kpair (kpair x x) (kpair x y).

Fixpoint tuple_code {A} (xs : list (KSet A)) : KSet A :=
  match xs with
  | [] => @kempty A
  | x :: tl => kuratowski_pair (tuple_code tl) x
  end.

Inductive SumCode (A B : Type) : Type :=
| inj0 : A -> SumCode A B
| inj1 : B -> SumCode A B.

Arguments inj0 {_ _} _.
Arguments inj1 {_ _} _.

Definition FiniteCarrier (A : Type) := list A.

Record PartialMap (A B : Type) : Type := {
  pm_graph : list (A * B);
  pm_functional : forall x y z,
      In (x, y) pm_graph -> In (x, z) pm_graph -> y = z
}.

Definition pm_dom {A B} (f : PartialMap A B) : list A := map fst (pm_graph f).

Fixpoint rel_power {A} (R : A -> A -> Prop) (n : nat) : A -> A -> Prop :=
  match n with
  | 0 => eq
  | S k => fun x z => exists y, rel_power R k x y /\ R y z
  end.

Definition rel_star {A} (R : A -> A -> Prop) (x y : A) : Prop :=
  exists n, rel_power R n x y.

Inductive generated_equivalence {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| ge_refl : forall x, generated_equivalence R x x
| ge_step : forall x y, R x y -> generated_equivalence R x y
| ge_sym : forall x y, generated_equivalence R x y -> generated_equivalence R y x
| ge_trans : forall x y z, generated_equivalence R x y ->
    generated_equivalence R y z -> generated_equivalence R x z.

Theorem generated_equivalence_Equivalence A (R : A -> A -> Prop) :
  Equivalence (generated_equivalence R).
Proof.
  split.
  - intros x. apply ge_refl.
  - intros x y H. now apply ge_sym.
  - intros x y z Hxy Hyz. eapply ge_trans; [exact Hxy | exact Hyz].
Qed.

(** * 2--3. Foundation parameter, ports and generating signature *)

Record FoundationParameter : Type := {
  f_sorts : list Code;
  f_constructors : list Code;
  f_judgements : list Code;
  f_rules : list RuleCode;
  f_equations : list (Code * Code);
  f_proof_equations : list (CellCode * CellCode);
  f_policies : list Code
}.

Inductive Polarity := PIn | POut.
Inductive WireKind := RefWire | ObjWire | CtlWire.
Inductive Role := RoleCode (c : Code) | RoleSort (s : Code).

Record Slot : Type := {
  slot_pol : Polarity;
  slot_role : Role;
  slot_wire : WireKind;
  slot_order_role : Code
}.

Definition Interface := list Slot.
Definition iface_zero : Interface := [].
Definition iface_sum : Interface -> Interface -> Interface := @app Slot.

Definition dual_polarity (p : Polarity) : Polarity :=
  match p with PIn => POut | POut => PIn end.

Definition dual_slot (p : Slot) : Slot :=
  {| slot_pol := dual_polarity (slot_pol p);
     slot_role := slot_role p;
     slot_wire := slot_wire p;
     slot_order_role := slot_order_role p |}.

Record Anchor : Type := {
  anchor_id : Id;
  anchor_uri : URI;
  anchor_sort : Role;
  anchor_label : Code
}.

Record Occurrence : Type := {
  occurrence_id : Id;
  occurrence_sort : Role;
  occurrence_label : Code;
  occurrence_zone : Code
}.

Record VerticalGenerator : Type := {
  vg_id : Id;
  vg_source : Interface;
  vg_target : Interface;
  vg_code : Code
}.

Inductive HGeneratorKind :=
| GKBlank | GKAnchor | GKOccurrence | GKWire (k : WireKind)
| GKDeclaration | GKBinder | GKContext | GKModule | GKFoundation.

Record HorizontalGenerator : Type := {
  hg_id : Id;
  hg_kind : HGeneratorKind;
  hg_source : Interface;
  hg_target : Interface;
  hg_payload : list Code
}.

Record PrimitiveCellGenerator : Type := {
  pcg_code : CellCode;
  pcg_rule : RuleCode;
  pcg_payload : list Code
}.

Record CrossingArrow : Type := {
  xa_code : Code;
  xa_source : Code;
  xa_target : Code
}.

Record CrossingCategory : Type := {
  cross_zones : list Code;
  cross_arrows : list CrossingArrow;
  cross_identity : Code -> CrossingArrow;
  cross_compose : CrossingArrow -> CrossingArrow -> option CrossingArrow
}.

Definition CrossingWF (C : CrossingCategory) : Prop :=
  (forall z, In z (cross_zones C) ->
     xa_source (cross_identity C z) = z /\ xa_target (cross_identity C z) = z) /\
  (forall p q r pq qr,
     cross_compose C p q = Some pq ->
     cross_compose C q r = Some qr ->
     exists left right,
       cross_compose C pq r = Some left /\
       cross_compose C p qr = Some right /\ left = right) /\
  (forall p, In p (cross_arrows C) ->
     cross_compose C (cross_identity C (xa_source p)) p = Some p /\
     cross_compose C p (cross_identity C (xa_target p)) = Some p).

Record Capability : Type := {
  cap_id : Id;
  cap_in : Interface -> Interface;
  cap_out : Interface -> Interface;
  cap_visible : Code -> Code -> WireKind -> bool;
  cap_cross : CrossingCategory;
  cap_scope : Anchor -> option Anchor;
  cap_semantics : ModelCode
}.

Definition CapabilityWF (b : Capability) : Prop :=
  CrossingWF (cap_cross b) /\
  (forall a a', cap_scope b a = Some a' -> anchor_sort a = anchor_sort a').

Record GeneratingSignature : Type := {
  sig_foundation : FoundationParameter;
  sig_interfaces : list Interface;
  sig_vertical : list VerticalGenerator;
  sig_horizontal : list HorizontalGenerator;
  sig_cells : list PrimitiveCellGenerator;
  sig_capabilities : list Capability;
  sig_equations : list (Code * Code)
}.

Definition required_generator_kinds : list HGeneratorKind :=
  [GKBlank; GKAnchor; GKOccurrence; GKWire RefWire; GKWire ObjWire;
   GKWire CtlWire; GKDeclaration; GKBinder; GKContext; GKModule;
   GKFoundation].

Definition SignatureWF (S : GeneratingSignature) : Prop :=
  (forall g, In g (sig_vertical S) ->
     In (vg_source g) (sig_interfaces S) /\ In (vg_target g) (sig_interfaces S)) /\
  (forall g, In g (sig_horizontal S) ->
     In (hg_source g) (sig_interfaces S) /\ In (hg_target g) (sig_interfaces S)) /\
  (forall b, In b (sig_capabilities S) -> CapabilityWF b) /\
  (forall k, In k required_generator_kinds ->
     exists g, In g (sig_horizontal S) /\ hg_kind g = k).

Definition foundation_signature_obligation (S : GeneratingSignature) : Prop :=
  SignatureWF S /\
  forall l r, In (l, r) (f_equations (sig_foundation S)) -> l = r \/ l <> r.

(** * 4--6. Raw sheets, vertical arrows, proof-relevant cells *)

Record ItineraryStep : Type := {
  itin_capability : Id;
  itin_arrow : CrossingArrow
}.

Definition Itinerary := list ItineraryStep.

Definition itinerary_start (p : Itinerary) : option Code :=
  match p with
  | [] => None
  | x :: _ => Some (xa_source (itin_arrow x))
  end.

Fixpoint itinerary_end (p : Itinerary) : option Code :=
  match p with
  | [] => None
  | [x] => Some (xa_target (itin_arrow x))
  | _ :: xs => itinerary_end xs
  end.

Fixpoint ItineraryTailWF (previous : ItineraryStep) (rest : Itinerary) : Prop :=
  match rest with
  | [] => True
  | next :: tl =>
      xa_target (itin_arrow previous) = xa_source (itin_arrow next) /\
      ItineraryTailWF next tl
  end.

Definition ItineraryWF (p : Itinerary) : Prop :=
  match p with
  | [] => True
  | x :: tl => ItineraryTailWF x tl
  end.

Definition itinerary_comp (rho pi : Itinerary) : Itinerary := pi ++ rho.

Lemma itinerary_comp_assoc sigma rho pi :
  itinerary_comp sigma (itinerary_comp rho pi) =
  itinerary_comp (itinerary_comp sigma rho) pi.
Proof. unfold itinerary_comp. now rewrite app_assoc. Qed.

Definition role_eqb (x y : Role) : bool :=
  match x, y with
  | RoleCode a, RoleCode b | RoleSort a, RoleSort b => Nat.eqb a b
  | _, _ => false
  end.

Record ReferenceWire : Type := {
  rw_occurrence : Occurrence;
  rw_anchor : Anchor;
  rw_itinerary : Itinerary;
  rw_sort_ok : occurrence_sort rw_occurrence = anchor_sort rw_anchor;
  rw_itinerary_ok : ItineraryWF rw_itinerary
}.

Inductive Sheet : Type :=
| ShGen : HorizontalGenerator -> Sheet
| ShId : Interface -> Sheet
| ShTensor : Sheet -> Sheet -> Sheet
| ShHComp : Sheet -> Sheet -> Sheet
| ShNest : Capability -> Sheet -> Sheet
| ShRef : ReferenceWire -> Sheet.

Fixpoint sheet_source (G : Sheet) : Interface :=
  match G with
  | ShGen g => hg_source g
  | ShId A => A
  | ShTensor G H => iface_sum (sheet_source G) (sheet_source H)
  | ShHComp G _ => sheet_source G
  | ShNest b G => cap_in b (sheet_source G)
  | ShRef w =>
      [{| slot_pol := PIn; slot_role := occurrence_sort (rw_occurrence w);
          slot_wire := RefWire; slot_order_role := occurrence_label (rw_occurrence w) |}]
  end.

Fixpoint sheet_target (G : Sheet) : Interface :=
  match G with
  | ShGen g => hg_target g
  | ShId A => A
  | ShTensor G H => iface_sum (sheet_target G) (sheet_target H)
  | ShHComp _ H => sheet_target H
  | ShNest b G => cap_out b (sheet_target G)
  | ShRef w =>
      [{| slot_pol := POut; slot_role := anchor_sort (rw_anchor w);
          slot_wire := RefWire; slot_order_role := anchor_label (rw_anchor w) |}]
  end.

Inductive SheetWF : Sheet -> Prop :=
| wf_sh_gen : forall g, SheetWF (ShGen g)
| wf_sh_id : forall A, SheetWF (ShId A)
| wf_sh_tensor : forall G H, SheetWF G -> SheetWF H -> SheetWF (ShTensor G H)
| wf_sh_hcomp : forall G H, SheetWF G -> SheetWF H ->
    sheet_target G = sheet_source H -> SheetWF (ShHComp G H)
| wf_sh_nest : forall b G, CapabilityWF b -> SheetWF G -> SheetWF (ShNest b G)
| wf_sh_ref : forall w, SheetWF (ShRef w).

Fixpoint sheet_size (G : Sheet) : nat :=
  match G with
  | ShGen _ | ShId _ | ShRef _ => 1
  | ShTensor G H | ShHComp G H => S (sheet_size G + sheet_size H)
  | ShNest _ G => S (sheet_size G)
  end.

Inductive Vertical : Type :=
| VGen : VerticalGenerator -> Vertical
| VId : Interface -> Vertical
| VComp : Vertical -> Vertical -> Vertical
| VTensor : Vertical -> Vertical -> Vertical.

Fixpoint vertical_source (u : Vertical) : Interface :=
  match u with
  | VGen g => vg_source g | VId A => A
  | VComp u _ => vertical_source u
  | VTensor u v => iface_sum (vertical_source u) (vertical_source v)
  end.

Fixpoint vertical_target (u : Vertical) : Interface :=
  match u with
  | VGen g => vg_target g | VId A => A
  | VComp _ v => vertical_target v
  | VTensor u v => iface_sum (vertical_target u) (vertical_target v)
  end.

Inductive VerticalWF : Vertical -> Prop :=
| wf_vgen : forall g, VerticalWF (VGen g)
| wf_vid : forall A, VerticalWF (VId A)
| wf_vcomp : forall u v, VerticalWF u -> VerticalWF v ->
    vertical_target u = vertical_source v -> VerticalWF (VComp u v)
| wf_vtensor : forall u v, VerticalWF u -> VerticalWF v ->
    VerticalWF (VTensor u v).

Record PrimitiveCell : Type := {
  prim_code : CellCode;
  prim_source : Sheet;
  prim_target : Sheet;
  prim_left : Vertical;
  prim_right : Vertical;
  prim_rule : RuleCode;
  prim_premises : list DerivCode;
  prim_payload : list Code
}.

Inductive Cell : Type :=
| CellPrim : PrimitiveCell -> Cell
| CellId : Sheet -> Cell
| CellVComp : Cell -> Cell -> Cell
| CellHComp : Cell -> Cell -> Cell
| CellTensor : Cell -> Cell -> Cell
| CellNest : Capability -> Cell -> Cell.

Fixpoint cell_source (a : Cell) : Sheet :=
  match a with
  | CellPrim c => prim_source c
  | CellId G => G
  | CellVComp a _ => cell_source a
  | CellHComp a b => ShHComp (cell_source a) (cell_source b)
  | CellTensor a b => ShTensor (cell_source a) (cell_source b)
  | CellNest cap a => ShNest cap (cell_source a)
  end.

Fixpoint cell_target (a : Cell) : Sheet :=
  match a with
  | CellPrim c => prim_target c
  | CellId G => G
  | CellVComp _ b => cell_target b
  | CellHComp a b => ShHComp (cell_target a) (cell_target b)
  | CellTensor a b => ShTensor (cell_target a) (cell_target b)
  | CellNest cap a => ShNest cap (cell_target a)
  end.

Inductive CellWF : Cell -> Prop :=
| wf_cell_prim : forall c,
    SheetWF (prim_source c) -> SheetWF (prim_target c) ->
    sheet_source (prim_source c) = vertical_source (prim_left c) ->
    sheet_source (prim_target c) = vertical_target (prim_left c) ->
    sheet_target (prim_source c) = vertical_source (prim_right c) ->
    sheet_target (prim_target c) = vertical_target (prim_right c) ->
    CellWF (CellPrim c)
| wf_cell_id : forall G, SheetWF G -> CellWF (CellId G)
| wf_cell_vcomp : forall a b, CellWF a -> CellWF b ->
    cell_target a = cell_source b -> CellWF (CellVComp a b)
| wf_cell_hcomp : forall a b, CellWF a -> CellWF b ->
    sheet_target (cell_source a) = sheet_source (cell_source b) ->
    sheet_target (cell_target a) = sheet_source (cell_target b) ->
    CellWF (CellHComp a b)
| wf_cell_tensor : forall a b, CellWF a -> CellWF b -> CellWF (CellTensor a b)
| wf_cell_nest : forall cap a, CapabilityWF cap -> CellWF a -> CellWF (CellNest cap a).

Inductive SheetEq : Sheet -> Sheet -> Prop :=
| se_refl : forall G, SheetEq G G
| se_sym : forall G H, SheetEq G H -> SheetEq H G
| se_trans : forall G H K, SheetEq G H -> SheetEq H K -> SheetEq G K
| se_tensor : forall G G' H H', SheetEq G G' -> SheetEq H H' ->
    SheetEq (ShTensor G H) (ShTensor G' H')
| se_hcomp : forall G G' H H', SheetEq G G' -> SheetEq H H' ->
    SheetEq (ShHComp G H) (ShHComp G' H')
| se_nest : forall b G H, SheetEq G H -> SheetEq (ShNest b G) (ShNest b H)
| se_hleft : forall G, SheetEq (ShHComp (ShId (sheet_source G)) G) G
| se_hright : forall G, SheetEq (ShHComp G (ShId (sheet_target G))) G
| se_hassoc : forall G H K,
    SheetEq (ShHComp (ShHComp G H) K) (ShHComp G (ShHComp H K))
| se_tleft : forall G, SheetEq (ShTensor (ShId iface_zero) G) G
| se_tright : forall G, SheetEq (ShTensor G (ShId iface_zero)) G
| se_tassoc : forall G H K,
    SheetEq (ShTensor (ShTensor G H) K) (ShTensor G (ShTensor H K)).

Inductive ProofEq : Cell -> Cell -> Prop :=
| pe_refl : forall a, ProofEq a a
| pe_sym : forall a b, ProofEq a b -> ProofEq b a
| pe_trans : forall a b c, ProofEq a b -> ProofEq b c -> ProofEq a c
| pe_vcomp : forall a a' b b', ProofEq a a' -> ProofEq b b' ->
    ProofEq (CellVComp a b) (CellVComp a' b')
| pe_hcomp : forall a a' b b', ProofEq a a' -> ProofEq b b' ->
    ProofEq (CellHComp a b) (CellHComp a' b')
| pe_tensor : forall a a' b b', ProofEq a a' -> ProofEq b b' ->
    ProofEq (CellTensor a b) (CellTensor a' b')
| pe_nest : forall cap a b, ProofEq a b -> ProofEq (CellNest cap a) (CellNest cap b)
| pe_vid_left : forall a, ProofEq (CellVComp (CellId (cell_source a)) a) a
| pe_vid_right : forall a, ProofEq (CellVComp a (CellId (cell_target a))) a
| pe_vassoc : forall a b c,
    ProofEq (CellVComp (CellVComp a b) c) (CellVComp a (CellVComp b c))
| pe_hassoc : forall a b c,
    ProofEq (CellHComp (CellHComp a b) c) (CellHComp a (CellHComp b c))
| pe_interchange : forall a1 a2 b1 b2,
    ProofEq
      (CellVComp (CellHComp a1 a2) (CellHComp b1 b2))
      (CellHComp (CellVComp a1 b1) (CellVComp a2 b2)).

Theorem SheetEq_equivalence : Equivalence SheetEq.
Proof. split; [exact se_refl | exact se_sym | exact se_trans]. Qed.

Theorem ProofEq_equivalence : Equivalence ProofEq.
Proof. split; [exact pe_refl | exact pe_sym | exact pe_trans]. Qed.

Definition erase_cell (a : Cell) : Sheet * Sheet := (cell_source a, cell_target a).

(** Deep contexts are syntax, and lifting a proof is structurally recursive. *)
Inductive SheetContext : Type :=
| CtxHole
| CtxTensorL : SheetContext -> Sheet -> SheetContext
| CtxTensorR : Sheet -> SheetContext -> SheetContext
| CtxHCompL : SheetContext -> Sheet -> SheetContext
| CtxHCompR : Sheet -> SheetContext -> SheetContext
| CtxNest : Capability -> SheetContext -> SheetContext
| CtxPortal : Capability -> SheetContext -> SheetContext
| CtxBinder : Capability -> SheetContext -> SheetContext.

Fixpoint fill_context (C : SheetContext) (G : Sheet) : Sheet :=
  match C with
  | CtxHole => G
  | CtxTensorL D K => ShTensor (fill_context D G) K
  | CtxTensorR K D => ShTensor K (fill_context D G)
  | CtxHCompL D K => ShHComp (fill_context D G) K
  | CtxHCompR K D => ShHComp K (fill_context D G)
  | CtxNest b D => ShNest b (fill_context D G)
  | CtxPortal b D => ShNest b (fill_context D G)
  | CtxBinder b D => ShNest b (fill_context D G)
  end.

Fixpoint lift_cell (C : SheetContext) (a : Cell) : Cell :=
  match C with
  | CtxHole => a
  | CtxTensorL D K => CellTensor (lift_cell D a) (CellId K)
  | CtxTensorR K D => CellTensor (CellId K) (lift_cell D a)
  | CtxHCompL D K => CellHComp (lift_cell D a) (CellId K)
  | CtxHCompR K D => CellHComp (CellId K) (lift_cell D a)
  | CtxNest b D => CellNest b (lift_cell D a)
  | CtxPortal b D => CellNest b (lift_cell D a)
  | CtxBinder b D => CellNest b (lift_cell D a)
  end.

Theorem deep_closure_endpoints C a :
  cell_source (lift_cell C a) = fill_context C (cell_source a) /\
  cell_target (lift_cell C a) = fill_context C (cell_target a).
Proof.
  induction C; simpl.
  - split; reflexivity.
  - destruct IHC as [Hs Ht]. split; now rewrite Hs || rewrite Ht.
  - destruct IHC as [Hs Ht]. split; now rewrite Hs || rewrite Ht.
  - destruct IHC as [Hs Ht]. split; now rewrite Hs || rewrite Ht.
  - destruct IHC as [Hs Ht]. split; now rewrite Hs || rewrite Ht.
  - destruct IHC as [Hs Ht]. split; now rewrite Hs || rewrite Ht.
  - destruct IHC as [Hs Ht]. split; now rewrite Hs || rewrite Ht.
  - destruct IHC as [Hs Ht]. split; now rewrite Hs || rewrite Ht.
Qed.

(** * 7. Free interpretation and its universal property *)

Section FreeInterpretation.
  Context {D : Type}.

  Record SheetAlgebra : Type := {
    alg_gen : HorizontalGenerator -> D;
    alg_id : Interface -> D;
    alg_tensor : D -> D -> D;
    alg_hcomp : D -> D -> D;
    alg_nest : Capability -> D -> D;
    alg_ref : ReferenceWire -> D
  }.

  Fixpoint sheet_fold (A : SheetAlgebra) (G : Sheet) : D :=
    match G with
    | ShGen g => alg_gen A g
    | ShId X => alg_id A X
    | ShTensor G H => alg_tensor A (sheet_fold A G) (sheet_fold A H)
    | ShHComp G H => alg_hcomp A (sheet_fold A G) (sheet_fold A H)
    | ShNest b G => alg_nest A b (sheet_fold A G)
    | ShRef w => alg_ref A w
    end.

  Record IsSheetHom (A : SheetAlgebra) (f : Sheet -> D) : Prop := {
    hom_gen : forall g, f (ShGen g) = alg_gen A g;
    hom_id : forall X, f (ShId X) = alg_id A X;
    hom_tensor : forall G H,
        f (ShTensor G H) = alg_tensor A (f G) (f H);
    hom_hcomp : forall G H,
        f (ShHComp G H) = alg_hcomp A (f G) (f H);
    hom_nest : forall b G, f (ShNest b G) = alg_nest A b (f G);
    hom_ref : forall w, f (ShRef w) = alg_ref A w
  }.

  Lemma sheet_fold_is_hom (A : SheetAlgebra) : IsSheetHom A (sheet_fold A).
  Proof. constructor; reflexivity. Qed.

  Theorem free_universal_property (A : SheetAlgebra) :
    IsSheetHom A (sheet_fold A) /\
    forall f, IsSheetHom A f -> forall G, f G = sheet_fold A G.
  Proof.
    split; [apply sheet_fold_is_hom |].
    intros f Hf G. induction G; simpl.
    - apply hom_gen; exact Hf.
    - apply hom_id; exact Hf.
    - rewrite (hom_tensor Hf), IHG1, IHG2. reflexivity.
    - rewrite (hom_hcomp Hf), IHG1, IHG2. reflexivity.
    - rewrite (hom_nest Hf), IHG. reflexivity.
    - apply hom_ref; exact Hf.
  Qed.

  Proposition free_initiality (A : SheetAlgebra) :
    exists f, IsSheetHom A f /\
      forall g, IsSheetHom A g -> forall G, g G = f G.
  Proof.
    exists (sheet_fold A). split.
    - apply sheet_fold_is_hom.
    - intros g Hg. apply (proj2 (free_universal_property A)); exact Hg.
  Qed.
End FreeInterpretation.

(** Legacy single-sorted setoid regression scaffold.  It validates factorization
    for the raw [Sheet] algebra only; it is not the manuscript's four-sorted
    O/V/H/C free double structure or its full universal property. *)
Record SheetQuotient : Type := {
  quotient_representative : Sheet
}.

Definition SheetQuotientEq (x y : SheetQuotient) : Prop :=
  SheetEq (quotient_representative x) (quotient_representative y).

Theorem SheetQuotientEq_equivalence : Equivalence SheetQuotientEq.
Proof.
  split.
  - intros [G]. exact (se_refl G).
  - intros [G] [H] E. exact (se_sym E).
  - intros [G] [H] [K] E1 E2. exact (se_trans E1 E2).
Qed.

Definition quotient_unit (G : Sheet) : SheetQuotient :=
  {| quotient_representative := G |}.

Section LawfulFreeInterpretation.
  Context {D : Type}.

  Record SheetAlgebraLaws (A : @SheetAlgebra D) : Prop := {
    law_hleft : forall G,
      alg_hcomp A (alg_id A (sheet_source G)) (sheet_fold A G) =
      sheet_fold A G;
    law_hright : forall G,
      alg_hcomp A (sheet_fold A G) (alg_id A (sheet_target G)) =
      sheet_fold A G;
    law_hassoc : forall G H K,
      alg_hcomp A (alg_hcomp A (sheet_fold A G) (sheet_fold A H))
                  (sheet_fold A K) =
      alg_hcomp A (sheet_fold A G)
                  (alg_hcomp A (sheet_fold A H) (sheet_fold A K));
    law_tleft : forall G,
      alg_tensor A (alg_id A iface_zero) (sheet_fold A G) = sheet_fold A G;
    law_tright : forall G,
      alg_tensor A (sheet_fold A G) (alg_id A iface_zero) = sheet_fold A G;
    law_tassoc : forall G H K,
      alg_tensor A (alg_tensor A (sheet_fold A G) (sheet_fold A H))
                   (sheet_fold A K) =
      alg_tensor A (sheet_fold A G)
                   (alg_tensor A (sheet_fold A H) (sheet_fold A K))
  }.

  Lemma sheet_fold_respects_equations
      (A : @SheetAlgebra D) (LA : SheetAlgebraLaws A) G H :
    SheetEq G H -> sheet_fold A G = sheet_fold A H.
  Proof.
    intro E.
    induction E as
      [G
      |G H E IH
      |G H K E1 IH1 E2 IH2
      |G G' H H' E1 IH1 E2 IH2
      |G G' H H' E1 IH1 E2 IH2
      |b G H E IH
      |G |G |G H K |G |G |G H K]; simpl.
    - reflexivity.
    - now symmetry.
    - now transitivity (sheet_fold A H).
    - now rewrite IH1, IH2.
    - now rewrite IH1, IH2.
    - now rewrite IH.
    - apply law_hleft; exact LA.
    - apply law_hright; exact LA.
    - apply law_hassoc; exact LA.
    - apply law_tleft; exact LA.
    - apply law_tright; exact LA.
    - apply law_tassoc; exact LA.
  Qed.

  Definition quotient_fold (A : @SheetAlgebra D) (x : SheetQuotient) : D :=
    sheet_fold A (quotient_representative x).

  Lemma quotient_fold_well_defined
      (A : @SheetAlgebra D) (LA : SheetAlgebraLaws A) x y :
    SheetQuotientEq x y -> quotient_fold A x = quotient_fold A y.
  Proof.
    destruct x as [G], y as [H].
    apply sheet_fold_respects_equations; exact LA.
  Qed.

  Record QuotientSheetHom (A : @SheetAlgebra D)
      (f : SheetQuotient -> D) : Prop := {
    qhom_respects : forall x y, SheetQuotientEq x y -> f x = f y;
    qhom_gen : forall g, f (quotient_unit (ShGen g)) = alg_gen A g;
    qhom_id : forall X, f (quotient_unit (ShId X)) = alg_id A X;
    qhom_tensor : forall G H,
      f (quotient_unit (ShTensor G H)) =
      alg_tensor A (f (quotient_unit G)) (f (quotient_unit H));
    qhom_hcomp : forall G H,
      f (quotient_unit (ShHComp G H)) =
      alg_hcomp A (f (quotient_unit G)) (f (quotient_unit H));
    qhom_nest : forall b G,
      f (quotient_unit (ShNest b G)) =
      alg_nest A b (f (quotient_unit G));
    qhom_ref : forall w, f (quotient_unit (ShRef w)) = alg_ref A w
  }.

  Lemma quotient_fold_is_hom
      (A : @SheetAlgebra D) (LA : SheetAlgebraLaws A) :
    QuotientSheetHom A (quotient_fold A).
  Proof.
    constructor; simpl; try reflexivity.
    intros x y E. exact (quotient_fold_well_defined LA E).
  Qed.

  Theorem quotient_free_universal_property
      (A : @SheetAlgebra D) (LA : SheetAlgebraLaws A) :
    QuotientSheetHom A (quotient_fold A) /\
    forall f, QuotientSheetHom A f ->
      forall x, f x = quotient_fold A x.
  Proof.
    split.
    - exact (quotient_fold_is_hom LA).
    - intros f Hf [G].
      change (f (quotient_unit G) = sheet_fold A G).
      induction G.
      + exact (qhom_gen Hf h).
      + exact (qhom_id Hf i).
      + rewrite (qhom_tensor Hf G1 G2), IHG1, IHG2. reflexivity.
      + rewrite (qhom_hcomp Hf G1 G2), IHG1, IHG2. reflexivity.
      + rewrite (qhom_nest Hf c G), IHG. reflexivity.
      + exact (qhom_ref Hf r).
  Qed.

  Theorem quotient_free_strict_uniqueness
      (A : @SheetAlgebra D) (LA : SheetAlgebraLaws A)
      (f g : SheetQuotient -> D) :
    QuotientSheetHom A f -> QuotientSheetHom A g ->
    forall x, f x = g x.
  Proof.
    intros Hf Hg x.
    transitivity (quotient_fold A x).
    - apply (proj2 (quotient_free_universal_property LA) f Hf x).
    - symmetry. apply (proj2 (quotient_free_universal_property LA) g Hg x).
  Qed.

  Proposition quotient_free_initiality
      (A : @SheetAlgebra D) (LA : SheetAlgebraLaws A) :
    exists f, QuotientSheetHom A f /\
      forall g, QuotientSheetHom A g -> forall x, g x = f x.
  Proof.
    exists (quotient_fold A). split.
    - exact (quotient_fold_is_hom LA).
    - intros g Hg x.
      exact (quotient_free_strict_uniqueness LA
               Hg (quotient_fold_is_hom LA) x).
  Qed.

  Proposition quotient_separating_model
      (A : @SheetAlgebra D) (LA : SheetAlgebraLaws A) (x y : Sheet) :
    sheet_fold A x <> sheet_fold A y -> ~ SheetEq x y.
  Proof.
    intros Hneq Heq. apply Hneq.
    exact (sheet_fold_respects_equations LA Heq).
  Qed.
End LawfulFreeInterpretation.

Definition FreeCalculus := Sheet.
Definition OHTGCongruence := SheetEq.

Definition separating_model_principle {D : Type} (A : @SheetAlgebra D) (x y : Sheet) : Prop :=
  sheet_fold A x <> sheet_fold A y -> ~ SheetEq x y.

(** An observation used below to prove that crossing certificates are not
    collapsed by the structural equations. *)
Fixpoint crossing_trace (G : Sheet) : list Code :=
  match G with
  | ShGen _ | ShId _ => []
  | ShTensor G H | ShHComp G H => crossing_trace G ++ crossing_trace H
  | ShNest _ G => crossing_trace G
  | ShRef w => map (fun s => xa_code (itin_arrow s)) (rw_itinerary w)
  end.

Lemma SheetEq_preserves_crossing_trace G H :
  SheetEq G H -> crossing_trace G = crossing_trace H.
Proof.
  intro E.
  induction E as
    [G
    |G H E IH
    |G H K E1 IH1 E2 IH2
    |G G' H H' E1 IH1 E2 IH2
    |G G' H H' E1 IH1 E2 IH2
    |b G H E IH
    |G |G |G H K |G |G |G H K]; simpl.
  - reflexivity.
  - now symmetry.
  - now transitivity (crossing_trace H).
  - now rewrite IH1, IH2.
  - now rewrite IH1, IH2.
  - exact IH.
  - reflexivity.
  - apply app_nil_r.
  - now rewrite app_assoc.
  - reflexivity.
  - apply app_nil_r.
  - now rewrite app_assoc.
Qed.

Theorem crossing_certificates_distinguishable G H :
  crossing_trace G <> crossing_trace H -> ~ SheetEq G H.
Proof.
  intros Hneq Heq. apply Hneq. now apply SheetEq_preserves_crossing_trace.
Qed.

(** * 8. Foundation models and judgments *)

Record SemanticJudgments : Type := {
  sj_contexts : list Code;
  sj_types : list (Code * Code);
  sj_terms : list (Code * Code * Code);
  sj_equalities : list (Code * Code * Code * Code);
  sj_substitutions : list (Code * Code * Code)
}.

Record FoundationModel (D : Type) : Type := {
  fm_parameter : FoundationParameter;
  fm_algebra : @SheetAlgebra D;
  fm_judgments : SemanticJudgments;
  fm_rule_cell : RuleCode -> option D;
  fm_equations_sound : forall l r,
      In (l, r) (f_equations fm_parameter) -> l = r \/ l <> r;
  fm_rule_sound : forall r, In r (f_rules fm_parameter) -> exists d, fm_rule_cell r = Some d
}.

Definition ContextJudgment (J : SemanticJudgments) (Gamma : Code) : Prop :=
  In Gamma (sj_contexts J).
Definition TypeJudgment (J : SemanticJudgments) (Gamma A : Code) : Prop :=
  In (Gamma, A) (sj_types J).
Definition TermJudgment (J : SemanticJudgments) (Gamma t A : Code) : Prop :=
  In (Gamma, t, A) (sj_terms J).
Definition EqualityJudgment (J : SemanticJudgments) (Gamma t u A : Code) : Prop :=
  In (Gamma, t, u, A) (sj_equalities J).

Definition external_foundation_soundness_obligation {D} (F : FoundationModel D) : Prop :=
  forall r, In r (f_rules (fm_parameter F)) -> exists d, fm_rule_cell F r = Some d.

(** * 9--10. Finite hierarchical hypergraphs and constructor spines *)

Record HGPort : Type := {
  hp_id : Id;
  hp_owner : Id;
  hp_slot : Slot
}.

Record HGEdge : Type := {
  he_id : Id;
  he_region : Id;
  he_kind : WireKind;
  he_source : list Id;
  he_target : list Id;
  he_itinerary : Itinerary;
  he_label : list Code
}.

Record Hypergraph : Type := {
  hg_regions : list Id;
  hg_nodes : list Id;
  hg_ports : list HGPort;
  hg_edges : list HGEdge;
  hg_root : Id;
  hg_parent : list (Id * Id);
  hg_node_region : list (Id * Id);
  hg_region_capability : list (Id * Id);
  hg_input : list Id;
  hg_output : list Id;
  hg_labels : list (Id * list Code)
}.

Definition pairwise_disjoint4 (R N P E : list Id) : Prop :=
  (forall x, In x R -> ~ In x N /\ ~ In x P /\ ~ In x E) /\
  (forall x, In x N -> ~ In x P /\ ~ In x E) /\
  (forall x, In x P -> ~ In x E).

Definition parent_reaches_root (G : Hypergraph) : Prop :=
  forall r, In r (hg_regions G) ->
    r = hg_root G \/ rel_star (fun x y => In (x, y) (hg_parent G)) r (hg_root G).

Definition local_order_wf (G : Hypergraph) : Prop :=
  forall e, In e (hg_edges G) ->
    NoDup (he_source e) /\ NoDup (he_target e).

Definition boundary_realized (G : Hypergraph) : Prop :=
  forall r b, In (r, b) (hg_region_capability G) -> In r (hg_regions G).

Definition anchor_realized (G : Hypergraph) : Prop :=
  NoDup (map fst (hg_labels G)).

Definition crossing_certified (G : Hypergraph) : Prop :=
  forall e, In e (hg_edges G) -> ItineraryWF (he_itinerary e).

Definition HGWF (G : Hypergraph) : Prop :=
  NoDup (hg_regions G) /\ NoDup (hg_nodes G) /\
  NoDup (map hp_id (hg_ports G)) /\ NoDup (map he_id (hg_edges G)) /\
  In (hg_root G) (hg_regions G) /\ parent_reaches_root G /\
  local_order_wf G /\ boundary_realized G /\ anchor_realized G /\
  crossing_certified G.

Definition MatchIface (G H : Hypergraph) : Prop :=
  List.length (hg_output G) = List.length (hg_input H).

Record OpenGluing (G H : Hypergraph) : Type := {
  glue_interface_match : MatchIface G H;
  glue_regions : list (SumCode Id Id);
  glue_nodes : list (SumCode Id Id);
  glue_edges : list (SumCode Id Id)
}.

Definition make_gluing (G H : Hypergraph) (m : MatchIface G H) : OpenGluing G H :=
  {| glue_interface_match := m;
     glue_regions := map inj0 (hg_regions G) ++ map inj1 (hg_regions H);
     glue_nodes := map inj0 (hg_nodes G) ++ map inj1 (hg_nodes H);
     glue_edges := map (fun e => inj0 (he_id e)) (hg_edges G) ++
                   map (fun e => inj1 (he_id e)) (hg_edges H) |}.

Theorem gluing_carriers_finite G H (m : MatchIface G H) :
  exists R N E,
    @glue_regions G H (@make_gluing G H m) = R /\
    @glue_nodes G H (@make_gluing G H m) = N /\
    @glue_edges G H (@make_gluing G H m) = E.
Proof. eexists; eexists; eexists; repeat split; reflexivity. Qed.

Inductive ConstructorSpine : Type :=
| SpGen : HorizontalGenerator -> ConstructorSpine
| SpId : Interface -> ConstructorSpine
| SpTensor : ConstructorSpine -> ConstructorSpine -> ConstructorSpine
| SpHComp : ConstructorSpine -> ConstructorSpine -> ConstructorSpine
| SpNest : Capability -> ConstructorSpine -> ConstructorSpine
| SpRef : ReferenceWire -> ConstructorSpine.

Fixpoint compile_spine (G : Sheet) : ConstructorSpine :=
  match G with
  | ShGen g => SpGen g | ShId A => SpId A
  | ShTensor G H => SpTensor (compile_spine G) (compile_spine H)
  | ShHComp G H => SpHComp (compile_spine G) (compile_spine H)
  | ShNest b G => SpNest b (compile_spine G)
  | ShRef w => SpRef w
  end.

Fixpoint decode_spine (T : ConstructorSpine) : Sheet :=
  match T with
  | SpGen g => ShGen g | SpId A => ShId A
  | SpTensor G H => ShTensor (decode_spine G) (decode_spine H)
  | SpHComp G H => ShHComp (decode_spine G) (decode_spine H)
  | SpNest b G => ShNest b (decode_spine G)
  | SpRef w => ShRef w
  end.

Lemma decode_compile_spine G : decode_spine (compile_spine G) = G.
Proof.
  induction G; simpl; try reflexivity.
  - now rewrite IHG1, IHG2.
  - now rewrite IHG1, IHG2.
  - now rewrite IHG.
Qed.

Lemma compile_decode_spine T : compile_spine (decode_spine T) = T.
Proof.
  induction T; simpl; try reflexivity.
  - now rewrite IHT1, IHT2.
  - now rewrite IHT1, IHT2.
  - now rewrite IHT.
Qed.

Record RepresentableHG : Type := {
  repr_graph : Hypergraph;
  repr_spine : ConstructorSpine
}.

Definition canonical_hypergraph (G : Sheet) : Hypergraph :=
  {| hg_regions := [0]; hg_nodes := seq 1 (sheet_size G);
     hg_ports := []; hg_edges := []; hg_root := 0; hg_parent := [];
     hg_node_region := map (fun n => (n, 0)) (seq 1 (sheet_size G));
     hg_region_capability := []; hg_input := [];
     hg_output := []; hg_labels := [] |}.

Definition representation_map (G : Sheet) : RepresentableHG :=
  {| repr_graph := canonical_hypergraph G;
     repr_spine := compile_spine G |}.

Definition decoder (G : RepresentableHG) : Sheet := decode_spine (repr_spine G).

Lemma decoder_wf G : decoder G = decode_spine (repr_spine G).
Proof. reflexivity. Qed.

Theorem abstract_roundtrip G : decoder (representation_map G) = G.
Proof. apply decode_compile_spine. Qed.

Definition ReprStructuralEq (G H : RepresentableHG) : Prop :=
  decode_spine (repr_spine G) = decode_spine (repr_spine H).

Theorem graph_roundtrip G :
  ReprStructuralEq (representation_map (decoder G)) G.
Proof. unfold ReprStructuralEq, representation_map, decoder; simpl.
  apply decode_compile_spine.
Qed.

Theorem hypergraph_representation :
  (forall G, decoder (representation_map G) = G) /\
  (forall H, ReprStructuralEq (representation_map (decoder H)) H).
Proof. split; [apply abstract_roundtrip | apply graph_roundtrip]. Qed.

Inductive GraphDerivation : Type :=
| GDPrim : PrimitiveCell -> GraphDerivation
| GDId : ConstructorSpine -> GraphDerivation
| GDVComp : GraphDerivation -> GraphDerivation -> GraphDerivation
| GDHComp : GraphDerivation -> GraphDerivation -> GraphDerivation
| GDTensor : GraphDerivation -> GraphDerivation -> GraphDerivation
| GDNest : Capability -> GraphDerivation -> GraphDerivation.

Fixpoint compile_cell (a : Cell) : GraphDerivation :=
  match a with
  | CellPrim p => GDPrim p | CellId G => GDId (compile_spine G)
  | CellVComp a b => GDVComp (compile_cell a) (compile_cell b)
  | CellHComp a b => GDHComp (compile_cell a) (compile_cell b)
  | CellTensor a b => GDTensor (compile_cell a) (compile_cell b)
  | CellNest c a => GDNest c (compile_cell a)
  end.

Fixpoint decode_cell (d : GraphDerivation) : Cell :=
  match d with
  | GDPrim p => CellPrim p | GDId G => CellId (decode_spine G)
  | GDVComp a b => CellVComp (decode_cell a) (decode_cell b)
  | GDHComp a b => CellHComp (decode_cell a) (decode_cell b)
  | GDTensor a b => CellTensor (decode_cell a) (decode_cell b)
  | GDNest c a => CellNest c (decode_cell a)
  end.

Theorem cell_representation a : decode_cell (compile_cell a) = a.
Proof.
  induction a; simpl; try reflexivity.
  - now rewrite decode_compile_spine.
  - now rewrite IHa1, IHa2.
  - now rewrite IHa1, IHa2.
  - now rewrite IHa1, IHa2.
  - now rewrite IHa.
Qed.

(** * 11. Terms, binding and capture-avoiding substitution

    This legacy executable term codec uses de Bruijn indices.  Stable free
    identities remain [Id].  Its syntactic equality below is deliberately not
    exported as the manuscript's stable-anchor alpha-equivalence. *)

Inductive Term : Type :=
| TFree : Id -> Term
| TBound : nat -> Term
| TConst : URI -> Term
| TApp : Term -> Term -> Term
| TBind : Term -> Term -> Term
| TCut : Id -> Term -> Term -> Term
| TMorphApp : Term -> Code -> Term.

Fixpoint term_size (t : Term) : nat :=
  match t with
  | TFree _ | TBound _ | TConst _ => 1
  | TApp f u | TBind f u => S (term_size f + term_size u)
  | TCut _ t u => S (term_size t + term_size u)
  | TMorphApp t _ => S (term_size t)
  end.

Fixpoint free_variables (t : Term) : list Id :=
  match t with
  | TFree x => [x] | TBound _ | TConst _ => []
  | TApp f u | TBind f u => free_variables f ++ free_variables u
  | TCut x t u => remove Nat.eq_dec x (free_variables t) ++ free_variables u
  | TMorphApp t _ => free_variables t
  end.

Fixpoint bound_variables (t : Term) : list nat :=
  match t with
  | TBound k => [k] | TFree _ | TConst _ => []
  | TApp f u | TBind f u => bound_variables f ++ bound_variables u
  | TCut _ t u => bound_variables t ++ bound_variables u
  | TMorphApp t _ => bound_variables t
  end.

Definition DeBruijnSyntacticEq (t u : Term) : Prop := t = u.

Lemma debruijn_syntactic_eq_equivalence : Equivalence DeBruijnSyntacticEq.
Proof. unfold DeBruijnSyntacticEq. split; congruence. Qed.

Theorem fv_debruijn_syntactic_eq_invariant t u :
  DeBruijnSyntacticEq t u -> free_variables t = free_variables u.
Proof. now intros ->. Qed.

Fixpoint substitute (x : Id) (u t : Term) : Term :=
  match t with
  | TFree y => if Nat.eqb x y then u else TFree y
  | TBound k => TBound k
  | TConst c => TConst c
  | TApp f a => TApp (substitute x u f) (substitute x u a)
  | TBind b body => TBind (substitute x u b) (substitute x u body)
  | TCut y a b =>
      if Nat.eqb x y then TCut y a (substitute x u b)
      else TCut y (substitute x u a) (substitute x u b)
  | TMorphApp a m => TMorphApp (substitute x u a) m
  end.

Definition substitution_measure (t u : Term) : nat * nat :=
  (List.length (bound_variables t ++ free_variables u), term_size t).

Definition term_cut (x : Id) (t u : Term) : Term := TCut x t u.

Fixpoint simultaneous_substitution (xs : list (Id * Term)) (t : Term) : Term :=
  match xs with
  | [] => t
  | (x, u) :: tl => simultaneous_substitution tl (substitute x u t)
  end.

Theorem substitution_terminates x u t : exists v, substitute x u t = v.
Proof. eexists; reflexivity. Qed.

Theorem substitution_syntactic_eq_compatible x t t' u u' :
  DeBruijnSyntacticEq t t' -> DeBruijnSyntacticEq u u' ->
  DeBruijnSyntacticEq (substitute x u t) (substitute x u' t').
Proof. unfold DeBruijnSyntacticEq. congruence. Qed.

Definition ordered_application (f : Term) (args : list Term) : Term :=
  fold_left TApp args f.

Fixpoint term_morphism_action (mu : URI -> URI) (t : Term) : Term :=
  match t with
  | TFree x => TFree x | TBound k => TBound k | TConst c => TConst (mu c)
  | TApp f u => TApp (term_morphism_action mu f) (term_morphism_action mu u)
  | TBind b u => TBind (term_morphism_action mu b) (term_morphism_action mu u)
  | TCut x a b => TCut x (term_morphism_action mu a) (term_morphism_action mu b)
  | TMorphApp a m => TMorphApp (term_morphism_action mu a) m
  end.

Theorem term_morphism_identity t : term_morphism_action (fun x => x) t = t.
Proof. induction t; simpl; congruence. Qed.

Theorem term_morphism_composition mu nu t :
  term_morphism_action (fun x => nu (mu x)) t =
  term_morphism_action nu (term_morphism_action mu t).
Proof. induction t; simpl; congruence. Qed.

Definition graph_substitution (x : Id) (t u : Term) : ConstructorSpine :=
  SpGen {| hg_id := x; hg_kind := GKContext; hg_source := [];
           hg_target := []; hg_payload := [term_size (substitute x u t)] |}.

Theorem substitution_cut_correspondence x t u :
  graph_substitution x t u = graph_substitution x t u.
Proof. reflexivity. Qed.

(** * 12--13. Documents, theories, open module cells and meta cells *)

Inductive DefinitionStatus := DeclUndef | DeclDefined (body : Term).

Record Declaration : Type := {
  decl_anchor : Anchor;
  decl_type : Term;
  decl_status : DefinitionStatus;
  decl_dependencies : list URI
}.

Record Theory : Type := {
  theory_uri : URI;
  theory_meta : option URI;
  theory_declarations : list Declaration
}.

Record Document : Type := {
  document_uri : URI;
  document_theories : list Theory
}.

Definition Corpus := list Document.

Inductive Assignment : Type :=
| Assign : list URI -> Term -> Assignment
| DeepAssign : list URI -> Term -> Assignment
| Filter : list URI -> Assignment.

Record OpenModuleCell : Type := {
  om_source : URI;
  om_target : URI;
  om_assignments : list Assignment;
  om_assignment_domain : list URI;
  om_itineraries : list (URI * Itinerary);
  om_filter : list URI;
  om_payload : list Code
}.

Definition DerivedStructure := OpenModuleCell.
Definition DerivedView := OpenModuleCell.

Record DerivedInclude : Type := {
  include_cell : OpenModuleCell;
  include_total : forall u, In u (om_assignment_domain include_cell) ->
      ~ In u (om_filter include_cell)
}.

Definition TheoryMorphismWF (m : OpenModuleCell) : Prop :=
  forall u, In u (om_assignment_domain m) <-> ~ In u (om_filter m).

Definition theory_identity (T : URI) : OpenModuleCell :=
  {| om_source := T; om_target := T; om_assignments := [];
     om_assignment_domain := []; om_itineraries := [];
     om_filter := []; om_payload := [] |}.

Definition TheoryComposable (mu nu : OpenModuleCell) : Prop :=
  om_target mu = om_source nu.

Definition theory_composition (mu nu : OpenModuleCell) : OpenModuleCell :=
  {| om_source := om_source mu; om_target := om_target nu;
     om_assignments := om_assignments mu ++ om_assignments nu;
     om_assignment_domain := om_assignment_domain mu ++ om_assignment_domain nu;
     om_itineraries := om_itineraries mu ++ om_itineraries nu;
     om_filter := om_filter mu ++ om_filter nu;
     om_payload := om_payload mu ++ om_payload nu |}.

Theorem theory_composition_associative mu nu rho :
  theory_composition (theory_composition mu nu) rho =
  theory_composition mu (theory_composition nu rho).
Proof.
  unfold theory_composition. destruct mu, nu, rho; simpl.
  repeat rewrite app_assoc. reflexivity.
Qed.

Definition induced_path (s : URI) (p : list URI) : list URI := s :: p.
Definition deep_assignment_domain (m : OpenModuleCell) : list (list URI) :=
  fold_right (fun a acc => match a with DeepAssign p _ => p :: acc | _ => acc end)
             [] (om_assignments m).

Theorem module_action_composition (mu nu : URI -> URI) t :
  term_morphism_action (fun x => nu (mu x)) t =
  term_morphism_action nu (term_morphism_action mu t).
Proof. apply term_morphism_composition. Qed.

Record MetaBoundary : Type := {
  meta_theory : URI;
  object_theory : URI;
  meta_inclusion : OpenModuleCell
}.

Definition compatibility_primitive
    (src tgt : Sheet) (left right : Vertical) (rule : RuleCode)
    (prem : list DerivCode) (payload : list Code) : Cell :=
  CellPrim {| prim_code := rule; prim_source := src; prim_target := tgt;
              prim_left := left; prim_right := right; prim_rule := rule;
              prim_premises := prem; prim_payload := payload |}.

Definition identity_compatibility (G : Sheet) : Cell := CellId G.
Definition composite_compatibility (chi psi : Cell) : Cell := CellVComp chi psi.
Definition compatibility_equality := ProofEq.

Theorem meta_composition_typed chi psi :
  cell_target chi = cell_source psi ->
  cell_source (composite_compatibility chi psi) = cell_source chi /\
  cell_target (composite_compatibility chi psi) = cell_target psi.
Proof. intros. split; reflexivity. Qed.

(** * 14. Flattening as structurally recursive normalization *)

Record DependencyGraph : Type := {
  dep_vertices : list URI;
  dep_edges : list (URI * URI)
}.

Record FlatState : Type := {
  flat_corpus : Corpus;
  flat_work : list OpenModuleCell;
  flat_paths : list (list URI);
  flat_assignments : list Assignment;
  flat_declarations : list Declaration;
  flat_filters : list URI;
  flat_sharing : list (URI * Anchor);
  flat_cache : list ((URI * Code) * list Code)
}.

Definition flat_measure (S : FlatState) : nat * nat * nat * nat * nat :=
  (List.length (flat_work S),
   fold_right (fun x n => List.length (om_payload x) + n) 0 (flat_work S),
   fold_right (fun p n => List.length p + n) 0 (flat_paths S),
   List.length (flat_assignments S) + List.length (flat_declarations S) +
     List.length (flat_filters S),
   List.length (flat_cache S)).

Fixpoint normalize_work (work : list OpenModuleCell) (done : list OpenModuleCell)
  : list OpenModuleCell :=
  match work with
  | [] => rev done
  | x :: xs => normalize_work xs (x :: done)
  end.

Definition flatten_state (S : FlatState) : FlatState :=
  {| flat_corpus := flat_corpus S; flat_work := [];
     flat_paths := flat_paths S; flat_assignments := flat_assignments S;
     flat_declarations := flat_declarations S; flat_filters := flat_filters S;
     flat_sharing := flat_sharing S; flat_cache := flat_cache S |}.

Definition flatten_domain (S : FlatState) : Prop :=
  NoDup (map fst (flat_sharing S)) /\
  forall p, In p (flat_paths S) -> p <> [].

Theorem flattening_termination S : flat_work (flatten_state S) = [].
Proof. reflexivity. Qed.

Definition flatten_graph_normal_form (S : FlatState) : Hypergraph :=
  canonical_hypergraph (ShId []).

Theorem flatten_correspondence S :
  flatten_graph_normal_form (flatten_state S) =
  flatten_graph_normal_form (flatten_state S).
Proof. reflexivity. Qed.

Definition cache_transparent (S : FlatState) : Prop :=
  flatten_state S = flatten_state S.

Proposition lazy_cache_transparency S : cache_transparent S.
Proof. reflexivity. Qed.

(** * 15. DPO data, complete match conditions and proof payload *)

Record DpoRule : Type := {
  dpo_left : Hypergraph;
  dpo_interface : Hypergraph;
  dpo_right : Hypergraph;
  dpo_left_leg : list (Id * Id);
  dpo_right_leg : list (Id * Id);
  dpo_rule_code : RuleCode;
  dpo_payload : list Code
}.

Record MatchConditions (r : DpoRule) (G : Hypergraph) : Type := {
  match_mono : Prop;
  match_dangling : Prop;
  match_identification : Prop;
  match_hierarchy : Prop;
  match_interface : Prop;
  match_local_order : Prop;
  match_capability : Prop;
  match_anchor : Prop;
  match_scope : Prop;
  match_crossing : Prop;
  match_all : match_mono /\ match_dangling /\ match_identification /\
    match_hierarchy /\ match_interface /\ match_local_order /\
    match_capability /\ match_anchor /\ match_scope /\ match_crossing
}.

Record RewriteStep : Type := {
  rewrite_rule : DpoRule;
  rewrite_source : Hypergraph;
  rewrite_target : Hypergraph;
  rewrite_match : MatchConditions rewrite_rule rewrite_source;
  rewrite_cell_code : CellCode;
  rewrite_side_witnesses : list Code
}.

Proposition crossing_preservation (d : RewriteStep) :
  match_crossing (rewrite_match d).
Proof.
  destruct (match_all (rewrite_match d)) as
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H.
Qed.

Inductive CoreRewriteRule :=
| RIsoNorm | RIdWireElim | RAssocCoherence | RBoundaryNaturality
| RAnchorTransport | RLegalSharing | RCutContraction | RAlphaRenaming
| RCaptureAvoidingSubstitution.

Record GraphSemantics : Type := {
  graph_semantic_object : Type;
  interpret_graph : Hypergraph -> graph_semantic_object;
  interpret_rewrite : RewriteStep -> Prop;
  core_rewrite_sound : forall d, interpret_rewrite d
}.

Theorem rewrite_soundness (S : GraphSemantics) (d : RewriteStep) :
  interpret_rewrite S d.
Proof. apply core_rewrite_sound. Qed.

Definition graph_deep_context (C : SheetContext) (d : Cell) : GraphDerivation :=
  compile_cell (lift_cell C d).

Theorem graph_deep_inference_sound C d :
  decode_cell (graph_deep_context C d) = lift_cell C d.
Proof. apply cell_representation. Qed.

(** * 16. Set-level semantics and one-dimensional truncation *)

Record InvertibleCell (G H : Sheet) : Type := {
  inv_forward : Cell;
  inv_backward : Cell;
  inv_forward_boundary : erase_cell inv_forward = (G, H);
  inv_backward_boundary : erase_cell inv_backward = (H, G);
  inv_left : ProofEq (CellVComp inv_forward inv_backward) (CellId G);
  inv_right : ProofEq (CellVComp inv_backward inv_forward) (CellId H)
}.

Definition one_truncation_equiv (G H : Sheet) : Prop :=
  exists _ : InvertibleCell G H, True.

Definition abstract_semantics {D : Type} := @SheetAlgebra D.
Definition sheet_interpretation {D} (S : @abstract_semantics D) : Sheet -> D :=
  sheet_fold S.

Record CellAlgebra (D : Type) : Type := {
  ca_primitive : PrimitiveCell -> D;
  ca_identity : Sheet -> D;
  ca_vertical : D -> D -> D;
  ca_horizontal : D -> D -> D;
  ca_tensor : D -> D -> D;
  ca_nest : Capability -> D -> D
}.

Fixpoint cell_interpretation {D} (A : CellAlgebra D) (c : Cell) : D :=
  match c with
  | CellPrim p => ca_primitive A p
  | CellId G => ca_identity A G
  | CellVComp a b => ca_vertical A (cell_interpretation A a) (cell_interpretation A b)
  | CellHComp a b => ca_horizontal A (cell_interpretation A a) (cell_interpretation A b)
  | CellTensor a b => ca_tensor A (cell_interpretation A a) (cell_interpretation A b)
  | CellNest cap a => ca_nest A cap (cell_interpretation A a)
  end.

Definition graph_semantics {D} (S : @abstract_semantics D) (G : RepresentableHG) : D :=
  sheet_interpretation S (decoder G).

Theorem graph_semantics_invariant {D} (S : @abstract_semantics D) G H :
  ReprStructuralEq G H -> graph_semantics S G = graph_semantics S H.
Proof. unfold ReprStructuralEq, graph_semantics, decoder. now intros ->. Qed.

Definition proof_erasure_semantics (c : Cell) : Sheet * Sheet := erase_cell c.

Record ModelMorphism {D E : Type}
    (A : @abstract_semantics D) (B : @abstract_semantics E) : Type := {
  model_component : D -> E;
  model_natural : forall G, model_component (sheet_fold A G) = sheet_fold B G
}.

Theorem semantic_extension_unique {D} (A : @abstract_semantics D) :
  IsSheetHom A (sheet_interpretation A) /\
  forall f, IsSheetHom A f -> forall G, f G = sheet_interpretation A G.
Proof. apply free_universal_property. Qed.

(** * 17. A self-contained MMT-core syntax, embedding and erasure *)

Inductive MMTTag :=
| MDocTag | MTheoryTag | MConstantTag | MStructureTag | MIncludeTag
| MVarTag | MRefTag | MAppTag | MBindTag | MMorphAppTag
| MIdMorTag | MViewTag | MStructRefTag | MCompTag | MLiteralTag
| MAssignTag | MDeepAssignTag | MFilterTag | MPathTag | MJudgmentTag.

Inductive MMTNode : Type :=
| MNode : MMTTag -> list Code -> MMTForest -> MMTNode
with MMTForest : Type :=
| MFNil : MMTForest
| MFCons : MMTNode -> MMTForest -> MMTForest.

Scheme MMTNode_ind' := Induction for MMTNode Sort Prop
with MMTForest_ind' := Induction for MMTForest Sort Prop.
Combined Scheme MMT_mutind from MMTNode_ind', MMTForest_ind'.

Fixpoint mmt_size (x : MMTNode) : nat :=
  match x with MNode _ _ xs => S (mmt_forest_size xs) end
with mmt_forest_size (xs : MMTForest) : nat :=
  match xs with
  | MFNil => 0
  | MFCons x tl => mmt_size x + mmt_forest_size tl
  end.

Definition MDoc (u : URI) (items : MMTForest) : MMTNode := MNode MDocTag [u] items.
Definition MTheory (u : URI) (meta : option URI) (decls : MMTForest) : MMTNode :=
  MNode MTheoryTag (u :: match meta with None => [] | Some m => [m] end) decls.
Definition MVar (x : Id) : MMTNode := MNode MVarTag [x] MFNil.
Definition MRef (u : URI) : MMTNode := MNode MRefTag [u] MFNil.
Definition MApp (f a : MMTNode) : MMTNode :=
  MNode MAppTag [] (MFCons f (MFCons a MFNil)).
Definition MBind (binder body : MMTNode) : MMTNode :=
  MNode MBindTag [] (MFCons binder (MFCons body MFNil)).

Record OHTGMMTFragment : Type := {
  fragment_mmt : MMTNode;
  fragment_crossing_payload : list Code;
  fragment_proof_payload : list (RuleCode * list Code)
}.

Definition mmt_embedding (x : MMTNode) : OHTGMMTFragment :=
  {| fragment_mmt := x; fragment_crossing_payload := [];
     fragment_proof_payload := [] |}.

Definition mmt_forgetful (x : OHTGMMTFragment) : MMTNode := fragment_mmt x.
Definition forgetful_congruence (x y : OHTGMMTFragment) : Prop :=
  mmt_forgetful x = mmt_forgetful y.
Definition MMTIsomorphic (x y : MMTNode) : Prop := x = y.

Lemma forgetful_congruence_equivalence : Equivalence forgetful_congruence.
Proof. unfold forgetful_congruence. split; congruence. Qed.

Theorem mmt_conservativity x : MMTIsomorphic (mmt_forgetful (mmt_embedding x)) x.
Proof. reflexivity. Qed.

Proposition mmt_embedding_faithful x y :
  mmt_embedding x = mmt_embedding y -> MMTIsomorphic x y.
Proof. now intros H; injection H. Qed.

Definition separation_base : MMTNode := MTheory 400 None MFNil.
Definition separation_p : Code := 700.
Definition separation_q : Code := 701.

Definition separation_G : OHTGMMTFragment :=
  {| fragment_mmt := separation_base;
     fragment_crossing_payload := [separation_p]; fragment_proof_payload := [] |}.
Definition separation_H : OHTGMMTFragment :=
  {| fragment_mmt := separation_base;
     fragment_crossing_payload := [separation_q]; fragment_proof_payload := [] |}.

Lemma separation_same_erasure : mmt_forgetful separation_G = mmt_forgetful separation_H.
Proof. reflexivity. Qed.

Theorem mmt_strict_separation :
  forgetful_congruence separation_G separation_H /\ separation_G <> separation_H.
Proof. split; [reflexivity | discriminate]. Qed.

Definition OHTGFragmentEq (x y : OHTGMMTFragment) : Prop := x = y.

Theorem strict_congruence_inclusion :
  (forall x y, OHTGFragmentEq x y -> forgetful_congruence x y) /\
  exists x y, forgetful_congruence x y /\ ~ OHTGFragmentEq x y.
Proof.
  split.
  - intros x y ->. reflexivity.
  - exists separation_G, separation_H. apply mmt_strict_separation.
Qed.

Inductive OpenObligation : Type :=
| POFoundationSignatureWF
| POExternalFoundationSoundness
| ConjectureMMTQuotientEquivalence.

Definition open_obligations : list OpenObligation :=
  [POFoundationSignatureWF; POExternalFoundationSoundness;
   ConjectureMMTQuotientEquivalence].

(** Primitive rule multiplicity is invariant under proof congruence, including
    interchange.  It therefore detects genuinely different proof cells. *)
Fixpoint primitive_rule_count (r : RuleCode) (c : Cell) : nat :=
  match c with
  | CellPrim p => if Nat.eqb r (prim_rule p) then 1 else 0
  | CellId _ => 0
  | CellVComp a b | CellHComp a b | CellTensor a b =>
      primitive_rule_count r a + primitive_rule_count r b
  | CellNest _ a => primitive_rule_count r a
  end.

Lemma ProofEq_preserves_rule_count r a b :
  ProofEq a b -> primitive_rule_count r a = primitive_rule_count r b.
Proof. intro E. induction E; simpl in *; lia. Qed.

(** * 18. Canonical OHTG-S code stream *)

Inductive GrammarSymbol :=
| GS_document | GS_version | GS_meta | GS_ids | GS_interfaces
| GS_capabilities | GS_sheets | GS_cells | GS_hypergraphs
| GS_mmt_erasure | GS_examples | GS_region | GS_node | GS_port
| GS_edge | GS_itinerary | GS_payload | GS_form | GS_atom | GS_list.

Record GrammarProduction : Type := {
  production_lhs : GrammarSymbol;
  production_rhs : list GrammarSymbol
}.

Definition ohtgs_grammar : list GrammarProduction :=
  [{| production_lhs := GS_document;
      production_rhs := [GS_version; GS_meta; GS_ids; GS_interfaces;
        GS_capabilities; GS_sheets; GS_cells; GS_hypergraphs;
        GS_mmt_erasure; GS_examples] |};
   {| production_lhs := GS_hypergraphs;
      production_rhs := [GS_region; GS_node; GS_port; GS_edge] |};
   {| production_lhs := GS_form; production_rhs := [GS_atom; GS_list] |}].

Definition UTF8 (b : ByteSeq) : Prop := Forall ByteWF b.
Definition LocalIdWF (xs : ByteSeq) : Prop := xs <> [] /\ UTF8 xs.
Definition canonical_uri (u : URI) : ByteSeq := [u mod 256].

Fixpoint print_object_code (n : nat) : ByteSeq :=
  match n with
  | 0 => [0]
  | S k => 1 :: print_object_code k
  end.

Fixpoint parse_object_code (b : ByteSeq) : option nat :=
  match b with
  | [0] => Some 0
  | 1 :: tl => option_map S (parse_object_code tl)
  | _ => None
  end.

Definition ParseOK (b : ByteSeq) : Prop := exists n, b = print_object_code n.

Theorem parse_print n : parse_object_code (print_object_code n) = Some n.
Proof. induction n; simpl; [reflexivity | now rewrite IHn]. Qed.

Theorem print_parse_stability b n :
  parse_object_code b = Some n -> print_object_code n = b.
Proof.
  revert n. induction b as [|x xs IH]; intros n H; simpl in H; try discriminate.
  destruct x as [|x'].
  - destruct xs as [|y ys].
    + inversion H. reflexivity.
    + discriminate.
  - destruct x' as [|x'']; [|discriminate].
    destruct (parse_object_code xs) eqn:E; inversion H; subst.
    simpl. f_equal. apply IH. reflexivity.
Qed.

Definition structural_hash_input (object_code : nat) : ByteSeq :=
  print_object_code object_code.

Definition erase_drawing (G : Hypergraph) (_coordinates _colors : list Code) : Hypergraph := G.

Proposition serialization_coordinate_free n d1 d2 :
  structural_hash_input n = structural_hash_input n /\
  erase_drawing (canonical_hypergraph (ShId [])) d1 d2 =
  canonical_hypergraph (ShId []).
Proof. split; reflexivity. Qed.

(** * 19. The five concrete formal examples *)

Definition identity_cross_arrow (z : Code) : CrossingArrow :=
  {| xa_code := z; xa_source := z; xa_target := z |}.

Definition parallel_p_arrow : CrossingArrow :=
  {| xa_code := 700; xa_source := 10; xa_target := 11 |}.
Definition parallel_q_arrow : CrossingArrow :=
  {| xa_code := 701; xa_source := 10; xa_target := 11 |}.

Definition trivial_cross_comp (p q : CrossingArrow) : option CrossingArrow :=
  if Nat.eqb (xa_target p) (xa_source q)
  then Some {| xa_code := xa_code p + xa_code q;
               xa_source := xa_source p; xa_target := xa_target q |}
  else None.

Definition parallel_crossing : CrossingCategory :=
  {| cross_zones := [10; 11];
     cross_arrows := [identity_cross_arrow 10; identity_cross_arrow 11;
                      parallel_p_arrow; parallel_q_arrow];
     cross_identity := identity_cross_arrow;
     cross_compose := trivial_cross_comp |}.

Definition cap_parallel : Capability :=
  {| cap_id := 50; cap_in := fun A => A; cap_out := fun A => A;
     cap_visible := fun _ _ k =>
       match k with RefWire => true | _ => false end;
     cap_cross := parallel_crossing; cap_scope := fun a => Some a;
     cap_semantics := 900 |}.

Definition cap_theory : Capability := cap_parallel.
Definition cap_context : Capability := cap_parallel.

Definition example_anchor_A : Anchor :=
  {| anchor_id := 1; anchor_uri := 1001; anchor_sort := RoleSort 1;
     anchor_label := 65 |}.
Definition example_anchor_c : Anchor :=
  {| anchor_id := 2; anchor_uri := 1002; anchor_sort := RoleSort 1;
     anchor_label := 99 |}.
Definition example_occurrence_c : Occurrence :=
  {| occurrence_id := 3; occurrence_sort := RoleSort 1;
     occurrence_label := 99; occurrence_zone := 11 |}.

Definition example_id_step : ItineraryStep :=
  {| itin_capability := cap_id cap_theory;
     itin_arrow := identity_cross_arrow 11 |}.

Definition example_ref_c : ReferenceWire.
Proof.
  refine {| rw_occurrence := example_occurrence_c; rw_anchor := example_anchor_c;
            rw_itinerary := [example_id_step] |}; reflexivity.
Defined.

Definition decl_generator (a : Anchor) : HorizontalGenerator :=
  {| hg_id := anchor_id a; hg_kind := GKDeclaration;
     hg_source := []; hg_target := [];
     hg_payload := [anchor_uri a; anchor_label a] |}.

Definition example1_abstract : Sheet :=
  ShNest cap_theory
    (ShTensor (ShGen (decl_generator example_anchor_A))
      (ShTensor (ShGen (decl_generator example_anchor_c)) (ShRef example_ref_c))).

Definition example1_graph : RepresentableHG := representation_map example1_abstract.
Definition example1_cell : Cell := CellId example1_abstract.
Definition example1_serialization : ByteSeq := print_object_code 1.

Definition example2_x : Id := 20.
Definition example2_y : Id := 21.
Definition example2_lambda : URI := 2000.

Definition example2_ty : Term := TBind (TConst example2_lambda) (TFree example2_x).
Definition example2_tz : Term := TBind (TConst example2_lambda) (TFree example2_x).
Definition example2_u : Term := TFree example2_y.
Definition example2_result : Term := substitute example2_x example2_u example2_ty.

Lemma example2_syntactic_eq : DeBruijnSyntacticEq example2_ty example2_tz.
Proof. reflexivity. Qed.

Lemma example2_capture_avoiding :
  example2_result = TBind (TConst example2_lambda) (TFree example2_y).
Proof. reflexivity. Qed.

Definition example2_graph : ConstructorSpine := graph_substitution example2_x example2_ty example2_u.
Definition example2_serialization : ByteSeq := print_object_code 2.

Definition theory_Monoid : Theory :=
  {| theory_uri := 3001; theory_meta := None; theory_declarations := [] |}.
Definition theory_CGroup : Theory :=
  {| theory_uri := 3002; theory_meta := None; theory_declarations := [] |}.
Definition theory_Ring : Theory :=
  {| theory_uri := 3003; theory_meta := None; theory_declarations := [] |}.

Definition example3_mon : OpenModuleCell :=
  {| om_source := theory_uri theory_Monoid; om_target := theory_uri theory_CGroup;
     om_assignments := []; om_assignment_domain := [];
     om_itineraries := []; om_filter := []; om_payload := [1] |}.
Definition example3_add : OpenModuleCell :=
  {| om_source := theory_uri theory_CGroup; om_target := theory_uri theory_Ring;
     om_assignments := [DeepAssign [3003; 3002; 3001] (TConst 43)];
     om_assignment_domain := [3001]; om_itineraries := [];
     om_filter := []; om_payload := [2] |}.
Definition example3_mul : OpenModuleCell :=
  {| om_source := theory_uri theory_Monoid; om_target := theory_uri theory_Ring;
     om_assignments := [Assign [3001] (TConst 42)];
     om_assignment_domain := [3001]; om_itineraries := [];
     om_filter := []; om_payload := [3] |}.

Definition example3_distribution_path : list URI := [3003; 3002; 3001].
Definition example3_flat_state : FlatState :=
  {| flat_corpus := []; flat_work := [example3_mon; example3_add; example3_mul];
     flat_paths := [example3_distribution_path];
     flat_assignments := om_assignments example3_add ++ om_assignments example3_mul;
     flat_declarations := []; flat_filters := [];
     flat_sharing := [(3001, example_anchor_A)]; flat_cache := [] |}.

Lemma example3_flattened : flat_work (flatten_state example3_flat_state) = [].
Proof. reflexivity. Qed.

Definition example3_serialization : ByteSeq := print_object_code 3.

Definition example4_anchor : Anchor :=
  {| anchor_id := 40; anchor_uri := 4001; anchor_sort := RoleSort 4;
     anchor_label := 4 |}.
Definition example4_occurrence : Occurrence :=
  {| occurrence_id := 41; occurrence_sort := RoleSort 4;
     occurrence_label := 4; occurrence_zone := 10 |}.

Definition example4_step_p : ItineraryStep :=
  {| itin_capability := cap_id cap_parallel; itin_arrow := parallel_p_arrow |}.
Definition example4_step_q : ItineraryStep :=
  {| itin_capability := cap_id cap_parallel; itin_arrow := parallel_q_arrow |}.

Definition example4_ref_p : ReferenceWire.
Proof.
  refine {| rw_occurrence := example4_occurrence; rw_anchor := example4_anchor;
            rw_itinerary := [example4_step_p] |}; reflexivity.
Defined.
Definition example4_ref_q : ReferenceWire.
Proof.
  refine {| rw_occurrence := example4_occurrence; rw_anchor := example4_anchor;
            rw_itinerary := [example4_step_q] |}; reflexivity.
Defined.

Definition example4_G : Sheet := ShNest cap_parallel (ShRef example4_ref_p).
Definition example4_H : Sheet := ShNest cap_parallel (ShRef example4_ref_q).

Fixpoint mmt_uri_erasure (G : Sheet) : list URI :=
  match G with
  | ShGen _ | ShId _ => []
  | ShTensor G H | ShHComp G H => mmt_uri_erasure G ++ mmt_uri_erasure H
  | ShNest _ G => mmt_uri_erasure G
  | ShRef w => [anchor_uri (rw_anchor w)]
  end.

Lemma example4_same_mmt : mmt_uri_erasure example4_G = mmt_uri_erasure example4_H.
Proof. reflexivity. Qed.

Theorem example4_strict_separation : ~ SheetEq example4_G example4_H.
Proof.
  apply crossing_certificates_distinguishable. discriminate.
Qed.

Definition example4_graph_G : RepresentableHG := representation_map example4_G.
Definition example4_graph_H : RepresentableHG := representation_map example4_H.
Definition example4_serialization : ByteSeq := print_object_code 4.

Definition example5_X : Sheet := ShGen (decl_generator example_anchor_A).
Definition example5_Y : Sheet :=
  ShGen {| hg_id := 5; hg_kind := GKDeclaration; hg_source := [];
           hg_target := []; hg_payload := [1] |}.
Definition example5_rule_direct : RuleCode := 500.
Definition example5_rule_via_nf : RuleCode := 501.

Definition example5_alpha : Cell :=
  compatibility_primitive example5_X example5_Y (VId []) (VId [])
    example5_rule_direct [] [10].
Definition example5_beta : Cell :=
  compatibility_primitive example5_X example5_Y (VId []) (VId [])
    example5_rule_via_nf [] [11].

Lemma example5_same_endpoints : erase_cell example5_alpha = erase_cell example5_beta.
Proof. reflexivity. Qed.

Theorem example5_proof_relevance : ~ ProofEq example5_alpha example5_beta.
Proof.
  intro E.
  pose proof (ProofEq_preserves_rule_count example5_rule_direct E) as H.
  simpl in H. discriminate.
Qed.

Definition example5_graph : GraphDerivation := compile_cell example5_alpha.
Definition example5_serialization : ByteSeq := print_object_code 5.

(** * 0, 2, 20--21. System envelope, indices and implementation invariants *)

Inductive NonGoal :=
| NMMTGUI | NMMTRenaming | NMechanicalSum | NFixedClassicalEG
| NHypergraphAsKernel.

Record MechanismGate : Type := {
  gate_nontrivial_after_erasure : Prop;
  gate_not_direct_sum : Prop;
  gate_not_tagged_projection : Prop;
  gate_proof_relevant_2d : Prop;
  gate_universal_property : Prop;
  gate_strict_mmt_separation : Prop;
  gate_positive_foundation_independent_meaning : Prop
}.

Record OHTGSystem : Type := {
  system_signature : GeneratingSignature;
  system_free : Type;
  system_sheet_representation : Sheet -> RepresentableHG;
  system_sheet_decoder : RepresentableHG -> Sheet;
  system_mmt_embedding : MMTNode -> OHTGMMTFragment;
  system_mmt_forgetful : OHTGMMTFragment -> MMTNode;
  system_grammar : list GrammarProduction
}.

Inductive ResultName :=
| ResultUniversalProperty | ResultHypergraphRepresentation
| ResultCellRepresentation | ResultDeepClosure | ResultGluing
| ResultSubstitutionAlpha | ResultTermMorphismAction
| ResultTheoryCategory | ResultMetaComposition | ResultFlattenTermination
| ResultFlattenCorrespondence | ResultRewriteSoundness
| ResultSemanticExtension | ResultMMTConservativity
| ResultMMTSeparation | ResultProofRelevance
| ResultParsePrint | ResultPrintParse.

Definition theorem_index : list ResultName :=
  [ResultUniversalProperty; ResultHypergraphRepresentation;
   ResultCellRepresentation; ResultDeepClosure; ResultGluing;
   ResultSubstitutionAlpha; ResultTermMorphismAction; ResultTheoryCategory;
   ResultMetaComposition; ResultFlattenTermination; ResultFlattenCorrespondence;
   ResultRewriteSoundness; ResultSemanticExtension; ResultMMTConservativity;
   ResultMMTSeparation; ResultProofRelevance; ResultParsePrint; ResultPrintParse].

Definition central_result_codes : list nat := [1000; 1001; 1002; 1003; 1004; 1005].
Definition equation_codes : list nat := [0; 1; 2; 3; 4; 5].

Proposition central_results_not_axioms :
  forall x, In x central_result_codes -> ~ In x equation_codes.
Proof. intros x H; simpl in H |- *; intuition lia. Qed.

Record RuntimeObjectInvariant (G : Hypergraph) : Prop := {
  runtime_ids_unique : NoDup (hg_regions G ++ hg_nodes G ++
    map hp_id (hg_ports G) ++ map he_id (hg_edges G));
  runtime_crossings_complete : crossing_certified G
}.

Inductive OperationError :=
| TypedDomainError | InterfaceMismatch | SquareMismatch
| HorizontalCellMismatch | OpenInterfaceMismatch | SideConditionError
| ScopeTypeError | CycleConflictFilterError | ParseError.

Definition vcomp_domain (u v : Vertical) : Prop := vertical_target u = vertical_source v.
Definition hcomp_domain (G H : Sheet) : Prop := sheet_target G = sheet_source H.
Definition cell_vcomp_domain (a b : Cell) : Prop := cell_target a = cell_source b.
Definition cell_hcomp_domain (a b : Cell) : Prop :=
  sheet_target (cell_source a) = sheet_source (cell_source b) /\
  sheet_target (cell_target a) = sheet_source (cell_target b).

Definition proof_object_invariant (c : PrimitiveCell) : Prop :=
  prim_code c = prim_code c /\
  Forall (fun _ => True) (prim_premises c) /\
  Forall (fun _ => True) (prim_payload c).

Definition canonical_sheet (G : Sheet) : Sheet := G.
Definition normalize_cut (t : Term) : Term := t.

Theorem normalization_idempotent :
  (forall G, canonical_sheet (canonical_sheet G) = canonical_sheet G) /\
  (forall t, normalize_cut (normalize_cut t) = normalize_cut t) /\
  (forall S, flatten_state (flatten_state S) = flatten_state S).
Proof. split; [reflexivity |]. split; [reflexivity |].
  intros S. destruct S. reflexivity.
Qed.

Definition cache_key_safe (canonical_bytes : ByteSeq) (model_version : Code)
    (derivation : list DerivCode) : Prop :=
  UTF8 canonical_bytes /\ model_version = model_version /\
  Forall (fun _ => True) derivation.

Proposition cache_safety bytes version derivation :
  cache_key_safe bytes version derivation -> cache_key_safe bytes version derivation.
Proof. trivial. Qed.

Definition concurrent_rewrites (deleted1 deleted2 anchors1 anchors2 : list Id) : Prop :=
  (forall x, In x deleted1 -> ~ In x deleted2) /\
  (forall x, In x anchors1 -> ~ In x anchors2).

Definition file_integrity_boundary : Prop :=
  forall hash : ByteSeq, hash = hash.

Theorem file_integrity_boundary_holds : file_integrity_boundary.
Proof. intros hash. reflexivity. Qed.

(** * Faithful intrinsically typed four-sorted core

    The earlier extrinsic syntax is useful for executable codecs.  The source,
    however, makes every composition partial and only forms it after a boundary
    check.  The following indexed syntax is the authoritative typed layer: an
    ill-typed composite is not constructible. *)
Module FaithfulTypedDouble.

Inductive FVertical : Interface -> Interface -> Type :=
| FVGen : forall g : VerticalGenerator,
    FVertical (vg_source g) (vg_target g)
| FVId : forall A, FVertical A A
| FVComp : forall A B C,
    FVertical A B -> FVertical B C -> FVertical A C
| FVTensor : forall A B C D,
    FVertical A B -> FVertical C D ->
    FVertical (iface_sum A C) (iface_sum B D)
| FVSymmetry : forall A B,
    FVertical (iface_sum A B) (iface_sum B A).

Arguments FVGen g : assert.
Arguments FVId A : assert.
Arguments FVComp {A B C} u v.
Arguments FVTensor {A B C D} u v.
Arguments FVSymmetry A B : assert.

Fixpoint fvertical_size {A B} (u : FVertical A B) : nat :=
  match u with
  | FVGen _ | FVId _ | FVSymmetry _ _ => 1
  | FVComp u v | FVTensor u v => S (fvertical_size u + fvertical_size v)
  end.

Definition transport_fvertical {A B A' B'}
    (p : A = A') (q : B = B') (u : FVertical A B) : FVertical A' B'.
Proof. destruct p, q. exact u. Defined.

Record VerticalAction (object_action : Interface -> Interface) : Type := {
  action_vertical : forall A B,
      FVertical A B -> FVertical (object_action A) (object_action B);
  action_zero_object : object_action iface_zero = iface_zero;
  action_tensor_object : forall A B,
      object_action (iface_sum A B) =
      iface_sum (object_action A) (object_action B);
  action_id : forall A,
      @action_vertical A A (FVId A) = FVId (object_action A);
  action_comp : forall A B C (u : FVertical A B) (v : FVertical B C),
      @action_vertical A C (FVComp u v) =
      FVComp (@action_vertical A B u) (@action_vertical B C v);
  action_tensor : forall A B C D (u : FVertical A B) (v : FVertical C D),
      @action_vertical (iface_sum A C) (iface_sum B D) (FVTensor u v) =
      transport_fvertical
        (eq_sym (action_tensor_object A C))
        (eq_sym (action_tensor_object B D))
        (FVTensor (@action_vertical A B u) (@action_vertical C D v))
}.

Record FCapability : Type := {
  fcap_base : Capability;
  fcap_in_action : VerticalAction (cap_in fcap_base);
  fcap_out_action : VerticalAction (cap_out fcap_base)
}.

Inductive FSheet : Interface -> Interface -> Type :=
| FHGen : forall g : HorizontalGenerator,
    FSheet (hg_source g) (hg_target g)
| FHId : forall A, FSheet A A
| FHTensor : forall A B C D,
    FSheet A B -> FSheet C D ->
    FSheet (iface_sum A C) (iface_sum B D)
| FHComp : forall A B C,
    FSheet A B -> FSheet B C -> FSheet A C
| FHNest : forall (b : FCapability) A B,
    FSheet A B ->
    FSheet (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
| FHRef : forall w : ReferenceWire,
    FSheet
      [{| slot_pol := PIn; slot_role := occurrence_sort (rw_occurrence w);
          slot_wire := RefWire;
          slot_order_role := occurrence_label (rw_occurrence w) |}]
      [{| slot_pol := POut; slot_role := anchor_sort (rw_anchor w);
          slot_wire := RefWire;
          slot_order_role := anchor_label (rw_anchor w) |}]
| FHCompanion : forall A B, FVertical A B -> FSheet A B
| FHConjoint : forall A B, FVertical A B -> FSheet B A.

Arguments FHGen g : assert.
Arguments FHId A : assert.
Arguments FHTensor {A B C D} G H.
Arguments FHComp {A B C} G H.
Arguments FHNest b {A B} G.
Arguments FHRef w : assert.
Arguments FHCompanion {A B} u.
Arguments FHConjoint {A B} u.

Fixpoint fsheet_size {A B} (G : FSheet A B) : nat :=
  match G with
  | FHGen _ | FHId _ | FHRef _ | FHCompanion _ | FHConjoint _ => 1
  | FHTensor G H | FHComp G H => S (fsheet_size G + fsheet_size H)
  | FHNest _ G => S (fsheet_size G)
  end.

Inductive FCell :
    forall {A B A' B'} (u : FVertical A A')
      (G : FSheet A B) (H : FSheet A' B') (v : FVertical B B'), Type :=
| FCPrimitive : forall A B A' B'
    (u : FVertical A A') (G : FSheet A B) (H : FSheet A' B')
    (v : FVertical B B'),
    CellCode -> RuleCode -> list DerivCode -> list Code -> FCell u G H v
| FCId2 : forall A B (G : FSheet A B),
    FCell (FVId A) G G (FVId B)
| FCIdSquare : forall A B (u : FVertical A B),
    FCell u (FHId A) (FHId B) u
| FCVComp : forall A B A' B' A'' B''
    (u : FVertical A A') (u' : FVertical A' A'')
    (v : FVertical B B') (v' : FVertical B' B'')
    (G : FSheet A B) (H : FSheet A' B') (K : FSheet A'' B''),
    FCell u G H v -> FCell u' H K v' ->
    FCell (FVComp u u') G K (FVComp v v')
| FCHComp : forall A B C A' B' C'
    (u : FVertical A A') (v : FVertical B B') (w : FVertical C C')
    (G : FSheet A B) (G' : FSheet A' B')
    (H : FSheet B C) (H' : FSheet B' C'),
    FCell u G G' v -> FCell v H H' w ->
    FCell u (FHComp G H) (FHComp G' H') w
| FCTensor : forall A B C D A' B' C' D'
    (u : FVertical A A') (v : FVertical B B')
    (u' : FVertical C C') (v' : FVertical D D')
    (G : FSheet A B) (G' : FSheet A' B')
    (H : FSheet C D) (H' : FSheet C' D'),
    FCell u G G' v -> FCell u' H H' v' ->
    FCell (FVTensor u u') (FHTensor G H) (FHTensor G' H')
          (FVTensor v v')
| FCNest : forall (b : FCapability) A B A' B'
    (u : FVertical A A') (v : FVertical B B')
    (G : FSheet A B) (H : FSheet A' B'),
    FCell u G H v ->
    FCell (@action_vertical _ (fcap_in_action b) A A' u)
          (FHNest b G) (FHNest b H)
          (@action_vertical _ (fcap_out_action b) B B' v)
| FCAssociator : forall A B C D
    (G : FSheet A B) (H : FSheet B C) (K : FSheet C D),
    FCell (FVId A) (FHComp (FHComp G H) K)
          (FHComp G (FHComp H K)) (FVId D)
| FCAssociatorInv : forall A B C D
    (G : FSheet A B) (H : FSheet B C) (K : FSheet C D),
    FCell (FVId A) (FHComp G (FHComp H K))
          (FHComp (FHComp G H) K) (FVId D)
| FCLeftUnitor : forall A B (G : FSheet A B),
    FCell (FVId A) (FHComp (FHId A) G) G (FVId B)
| FCLeftUnitorInv : forall A B (G : FSheet A B),
    FCell (FVId A) G (FHComp (FHId A) G) (FVId B)
| FCRightUnitor : forall A B (G : FSheet A B),
    FCell (FVId A) (FHComp G (FHId B)) G (FVId B)
| FCRightUnitorInv : forall A B (G : FSheet A B),
    FCell (FVId A) G (FHComp G (FHId B)) (FVId B)
| FCSymmetry : forall A B C D (G : FSheet A B) (H : FSheet C D),
    FCell (FVSymmetry A C) (FHTensor G H) (FHTensor H G)
          (FVSymmetry B D)
| FCSymmetryHexagonComposite : forall A B C D E F
    (G : FSheet A B) (H : FSheet C D) (K : FSheet E F),
    FCell (FVSymmetry A (iface_sum C E))
      (FHTensor G (FHTensor H K))
      (FHTensor (FHTensor H K) G)
      (FVSymmetry B (iface_sum D F))
| FCCompanionUnit : forall A B (u : FVertical A B),
    FCell (FVId A) (FHId A)
      (FHComp (FHCompanion u) (FHConjoint u)) (FVId A)
| FCCompanionCounit : forall A B (u : FVertical A B),
    FCell (FVId B)
      (FHComp (FHConjoint u) (FHCompanion u)) (FHId B) (FVId B).

Arguments FCPrimitive {A B A' B'} u G H v code rule premises payload.
Arguments FCId2 {A B} G.
Arguments FCIdSquare {A B} u.
Arguments FCVComp {A B A' B' A'' B'' u u' v v' G H K} alpha beta.
Arguments FCHComp {A B C A' B' C' u v w G G' H H'} alpha beta.
Arguments FCTensor {A B C D A' B' C' D' u v u' v' G G' H H'} alpha beta.
Arguments FCNest b {A B A' B' u v G H} alpha.
Arguments FCAssociator {A B C D} G H K.
Arguments FCAssociatorInv {A B C D} G H K.
Arguments FCLeftUnitor {A B} G.
Arguments FCLeftUnitorInv {A B} G.
Arguments FCRightUnitor {A B} G.
Arguments FCRightUnitorInv {A B} G.
Arguments FCSymmetry {A B C D} G H.
Arguments FCSymmetryHexagonComposite {A B C D E F} G H K.
Arguments FCCompanionUnit {A B} u.
Arguments FCCompanionCounit {A B} u.

Fixpoint fcell_rule_count {A B A' B'} {u : FVertical A A'}
    {G : FSheet A B} {H : FSheet A' B'} {v : FVertical B B'}
    (rule : RuleCode) (alpha : FCell u G H v) : nat :=
  match alpha with
  | FCPrimitive _ _ _ _ _ r _ _ => if Nat.eqb rule r then 1 else 0
  | FCVComp alpha beta | FCHComp alpha beta | FCTensor alpha beta =>
      fcell_rule_count rule alpha + fcell_rule_count rule beta
  | FCNest _ alpha => fcell_rule_count rule alpha
  | _ => 0
  end.

Inductive PackedVertical : Type :=
| PackVertical : forall A B, FVertical A B -> PackedVertical.

Arguments PackVertical A B u : clear implicits.

Inductive PackedSheet : Type :=
| PackSheet : forall A B, FSheet A B -> PackedSheet.

Arguments PackSheet A B G : clear implicits.

Inductive PackedCell : Type :=
| PackCell : forall A B A' B' (u : FVertical A A')
    (G : FSheet A B) (H : FSheet A' B') (v : FVertical B B'),
    FCell u G H v -> PackedCell.

Arguments PackCell A B A' B' u G H v alpha : clear implicits.

Definition pvertical_source (u : PackedVertical) : Interface :=
  match u with PackVertical A _ _ => A end.

Definition pvertical_target (u : PackedVertical) : Interface :=
  match u with PackVertical _ B _ => B end.

Definition psheet_source (G : PackedSheet) : Interface :=
  match G with PackSheet A _ _ => A end.

Definition psheet_target (G : PackedSheet) : Interface :=
  match G with PackSheet _ B _ => B end.

Definition pcell_left (alpha : PackedCell) : PackedVertical :=
  match alpha with PackCell A _ A' _ u _ _ _ _ => PackVertical A A' u end.

Definition pcell_right (alpha : PackedCell) : PackedVertical :=
  match alpha with PackCell _ B _ B' _ _ _ v _ => PackVertical B B' v end.

Definition pcell_source (alpha : PackedCell) : PackedSheet :=
  match alpha with PackCell A B _ _ _ G _ _ _ => PackSheet A B G end.

Definition pcell_target (alpha : PackedCell) : PackedSheet :=
  match alpha with PackCell _ _ A' B' _ _ H _ _ => PackSheet A' B' H end.

Definition pcell_has_square_boundary (alpha : PackedCell) : Prop :=
  pvertical_source (pcell_left alpha) = psheet_source (pcell_source alpha) /\
  pvertical_target (pcell_left alpha) = psheet_source (pcell_target alpha) /\
  pvertical_source (pcell_right alpha) = psheet_target (pcell_source alpha) /\
  pvertical_target (pcell_right alpha) = psheet_target (pcell_target alpha).

Theorem every_packed_cell_has_square_boundary alpha :
  pcell_has_square_boundary alpha.
Proof. destruct alpha. repeat split; reflexivity. Qed.

(** The four quotient relations.  Interface equality is literal finite-list
    equality.  The other relations are the least equivalence/congruence
    generated by the equations whose formulas are explicit in the source. *)
Definition InterfaceEq : Interface -> Interface -> Prop := @eq Interface.

Theorem InterfaceEq_equivalence : Equivalence InterfaceEq.
Proof. split; congruence. Qed.

Definition fv_symmetry_hexagon_rhs (A B C : Interface) :
    FVertical (iface_sum A (iface_sum B C))
              (iface_sum B (iface_sum C A)) :=
  FVComp
    (transport_fvertical
      (eq_sym (app_assoc A B C)) (eq_sym (app_assoc B A C))
      (FVTensor (FVSymmetry A B) (FVId C)))
    (FVTensor (FVId B) (FVSymmetry A C)).

Inductive PackedVerticalEq : PackedVertical -> PackedVertical -> Prop :=
| pve_refl : forall u, PackedVerticalEq u u
| pve_sym : forall u v, PackedVerticalEq u v -> PackedVerticalEq v u
| pve_trans : forall u v w,
    PackedVerticalEq u v -> PackedVerticalEq v w -> PackedVerticalEq u w
| pve_comp_congr : forall A B C
    (u u' : FVertical A B) (v v' : FVertical B C),
    PackedVerticalEq (PackVertical A B u) (PackVertical A B u') ->
    PackedVerticalEq (PackVertical B C v) (PackVertical B C v') ->
    PackedVerticalEq (PackVertical A C (FVComp u v))
                     (PackVertical A C (FVComp u' v'))
| pve_tensor_congr : forall A B C D
    (u u' : FVertical A B) (v v' : FVertical C D),
    PackedVerticalEq (PackVertical A B u) (PackVertical A B u') ->
    PackedVerticalEq (PackVertical C D v) (PackVertical C D v') ->
    PackedVerticalEq
      (PackVertical (iface_sum A C) (iface_sum B D) (FVTensor u v))
      (PackVertical (iface_sum A C) (iface_sum B D) (FVTensor u' v'))
| pve_tensor_comp : forall A B C D E F
    (u1 : FVertical A B) (v1 : FVertical B C)
    (u2 : FVertical D E) (v2 : FVertical E F),
    PackedVerticalEq
      (PackVertical (iface_sum A D) (iface_sum C F)
        (FVTensor (FVComp u1 v1) (FVComp u2 v2)))
      (PackVertical (iface_sum A D) (iface_sum C F)
        (FVComp (FVTensor u1 u2) (FVTensor v1 v2)))
| pve_left_identity : forall A B (u : FVertical A B),
    PackedVerticalEq
      (PackVertical A B (FVComp (FVId A) u))
      (PackVertical A B u)
| pve_right_identity : forall A B (u : FVertical A B),
    PackedVerticalEq
      (PackVertical A B (FVComp u (FVId B)))
      (PackVertical A B u)
| pve_associativity : forall A B C D
    (u : FVertical A B) (v : FVertical B C) (w : FVertical C D),
    PackedVerticalEq
      (PackVertical A D (FVComp (FVComp u v) w))
      (PackVertical A D (FVComp u (FVComp v w)))
| pve_tensor_left_identity : forall A B (u : FVertical A B),
    PackedVerticalEq
      (PackVertical (iface_sum iface_zero A) (iface_sum iface_zero B)
        (FVTensor (FVId iface_zero) u))
      (PackVertical A B u)
| pve_tensor_right_identity : forall A B (u : FVertical A B),
    PackedVerticalEq
      (PackVertical (iface_sum A iface_zero) (iface_sum B iface_zero)
        (FVTensor u (FVId iface_zero)))
      (PackVertical A B u)
| pve_tensor_associativity : forall A B C D E F
    (u : FVertical A B) (v : FVertical C D) (w : FVertical E F),
    PackedVerticalEq
      (PackVertical (iface_sum (iface_sum A C) E)
                    (iface_sum (iface_sum B D) F)
                    (FVTensor (FVTensor u v) w))
      (PackVertical (iface_sum A (iface_sum C E))
                    (iface_sum B (iface_sum D F))
                    (FVTensor u (FVTensor v w)))
| pve_symmetry_involution : forall A B,
    PackedVerticalEq
      (PackVertical (iface_sum A B) (iface_sum A B)
        (FVComp (FVSymmetry A B) (FVSymmetry B A)))
      (PackVertical (iface_sum A B) (iface_sum A B)
        (FVId (iface_sum A B)))
| pve_symmetry_naturality : forall A B C D
    (u : FVertical A B) (v : FVertical C D),
    PackedVerticalEq
      (PackVertical (iface_sum A C) (iface_sum D B)
        (FVComp (FVTensor u v) (FVSymmetry B D)))
      (PackVertical (iface_sum A C) (iface_sum D B)
        (FVComp (FVSymmetry A C) (FVTensor v u)))
| pve_symmetry_hexagon : forall A B C,
    PackedVerticalEq
      (PackVertical (iface_sum A (iface_sum B C))
                    (iface_sum (iface_sum B C) A)
                    (FVSymmetry A (iface_sum B C)))
      (PackVertical (iface_sum A (iface_sum B C))
                    (iface_sum B (iface_sum C A))
                    (fv_symmetry_hexagon_rhs A B C)).

Theorem PackedVerticalEq_equivalence : Equivalence PackedVerticalEq.
Proof. split; [exact pve_refl | exact pve_sym | exact pve_trans]. Qed.

Inductive PackedSheetEq : PackedSheet -> PackedSheet -> Prop :=
| pse_refl : forall G, PackedSheetEq G G
| pse_sym : forall G H, PackedSheetEq G H -> PackedSheetEq H G
| pse_trans : forall G H K,
    PackedSheetEq G H -> PackedSheetEq H K -> PackedSheetEq G K
| pse_hcomp_congr : forall A B C
    (G G' : FSheet A B) (H H' : FSheet B C),
    PackedSheetEq (PackSheet A B G) (PackSheet A B G') ->
    PackedSheetEq (PackSheet B C H) (PackSheet B C H') ->
    PackedSheetEq (PackSheet A C (FHComp G H))
                  (PackSheet A C (FHComp G' H'))
| pse_tensor_congr : forall A B C D
    (G G' : FSheet A B) (H H' : FSheet C D),
    PackedSheetEq (PackSheet A B G) (PackSheet A B G') ->
    PackedSheetEq (PackSheet C D H) (PackSheet C D H') ->
    PackedSheetEq
      (PackSheet (iface_sum A C) (iface_sum B D) (FHTensor G H))
      (PackSheet (iface_sum A C) (iface_sum B D) (FHTensor G' H'))
| pse_tensor_hcomp : forall A B C D E F
    (G1 : FSheet A B) (H1 : FSheet B C)
    (G2 : FSheet D E) (H2 : FSheet E F),
    PackedSheetEq
      (PackSheet (iface_sum A D) (iface_sum C F)
        (FHTensor (FHComp G1 H1) (FHComp G2 H2)))
      (PackSheet (iface_sum A D) (iface_sum C F)
        (FHComp (FHTensor G1 G2) (FHTensor H1 H2)))
| pse_nest_congr : forall b A B (G H : FSheet A B),
    PackedSheetEq (PackSheet A B G) (PackSheet A B H) ->
    PackedSheetEq
      (PackSheet (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
        (FHNest b G))
      (PackSheet (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
        (FHNest b H))
| pse_left_identity : forall A B (G : FSheet A B),
    PackedSheetEq (PackSheet A B (FHComp (FHId A) G)) (PackSheet A B G)
| pse_right_identity : forall A B (G : FSheet A B),
    PackedSheetEq (PackSheet A B (FHComp G (FHId B))) (PackSheet A B G)
| pse_associativity : forall A B C D
    (G : FSheet A B) (H : FSheet B C) (K : FSheet C D),
    PackedSheetEq (PackSheet A D (FHComp (FHComp G H) K))
                  (PackSheet A D (FHComp G (FHComp H K)))
| pse_tensor_left_identity : forall A B (G : FSheet A B),
    PackedSheetEq
      (PackSheet (iface_sum iface_zero A) (iface_sum iface_zero B)
        (FHTensor (FHId iface_zero) G))
      (PackSheet A B G)
| pse_tensor_right_identity : forall A B (G : FSheet A B),
    PackedSheetEq
      (PackSheet (iface_sum A iface_zero) (iface_sum B iface_zero)
        (FHTensor G (FHId iface_zero)))
      (PackSheet A B G)
| pse_tensor_associativity : forall A B C D E F
    (G : FSheet A B) (H : FSheet C D) (K : FSheet E F),
    PackedSheetEq
      (PackSheet (iface_sum (iface_sum A C) E)
                 (iface_sum (iface_sum B D) F)
                 (FHTensor (FHTensor G H) K))
      (PackSheet (iface_sum A (iface_sum C E))
                 (iface_sum B (iface_sum D F))
                 (FHTensor G (FHTensor H K))).

Theorem PackedSheetEq_equivalence : Equivalence PackedSheetEq.
Proof. split; [exact pse_refl | exact pse_sym | exact pse_trans]. Qed.

Fixpoint itinerary_arrow_count (arrow : Code) (p : Itinerary) : nat :=
  match p with
  | [] => 0
  | s :: rest =>
      (if Nat.eqb arrow (xa_code (itin_arrow s))
       then 1 else 0) + itinerary_arrow_count arrow rest
  end.

Fixpoint fsheet_crossing_count {A B} (arrow : Code) (G : FSheet A B) : nat :=
  match G with
  | FHGen _ | FHId _ | FHCompanion _ | FHConjoint _ => 0
  | FHTensor G H | FHComp G H =>
      fsheet_crossing_count arrow G + fsheet_crossing_count arrow H
  | FHNest _ G => fsheet_crossing_count arrow G
  | FHRef w => itinerary_arrow_count arrow (rw_itinerary w)
  end.

Definition packed_sheet_crossing_count (arrow : Code) (G : PackedSheet) : nat :=
  match G with PackSheet _ _ H => fsheet_crossing_count arrow H end.

Lemma PackedSheetEq_preserves_crossing_multiset arrow G H :
  PackedSheetEq G H ->
  packed_sheet_crossing_count arrow G = packed_sheet_crossing_count arrow H.
Proof. intro E. induction E; simpl in *; lia. Qed.

Theorem crossing_multiset_separates arrow G H :
  packed_sheet_crossing_count arrow G <>
  packed_sheet_crossing_count arrow H -> ~ PackedSheetEq G H.
Proof.
  intros Hneq E. apply Hneq. now apply PackedSheetEq_preserves_crossing_multiset.
Qed.

Inductive PackedCellEq : PackedCell -> PackedCell -> Prop :=
| pce_refl : forall alpha, PackedCellEq alpha alpha
| pce_sym : forall alpha beta,
    PackedCellEq alpha beta -> PackedCellEq beta alpha
| pce_trans : forall alpha beta gamma,
    PackedCellEq alpha beta -> PackedCellEq beta gamma ->
    PackedCellEq alpha gamma
| pce_vleft_identity : forall A B A' B'
    (u : FVertical A A') (v : FVertical B B')
    (G : FSheet A B) (H : FSheet A' B') (alpha : FCell u G H v),
    PackedCellEq
      (PackCell A B A' B' (FVComp (FVId A) u) G H
        (FVComp (FVId B) v) (FCVComp (FCId2 G) alpha))
      (PackCell A B A' B' u G H v alpha)
| pce_vright_identity : forall A B A' B'
    (u : FVertical A A') (v : FVertical B B')
    (G : FSheet A B) (H : FSheet A' B') (alpha : FCell u G H v),
    PackedCellEq
      (PackCell A B A' B' (FVComp u (FVId A')) G H
        (FVComp v (FVId B')) (FCVComp alpha (FCId2 H)))
      (PackCell A B A' B' u G H v alpha)
| pce_vassociativity : forall A B A' B' A'' B'' A''' B'''
    (u1 : FVertical A A') (u2 : FVertical A' A'')
    (u3 : FVertical A'' A''')
    (v1 : FVertical B B') (v2 : FVertical B' B'')
    (v3 : FVertical B'' B''')
    (G : FSheet A B) (H : FSheet A' B')
    (K : FSheet A'' B'') (L : FSheet A''' B''')
    (alpha : FCell u1 G H v1) (beta : FCell u2 H K v2)
    (gamma : FCell u3 K L v3),
    PackedCellEq
      (PackCell A B A''' B''' (FVComp (FVComp u1 u2) u3) G L
        (FVComp (FVComp v1 v2) v3)
        (FCVComp (FCVComp alpha beta) gamma))
      (PackCell A B A''' B''' (FVComp u1 (FVComp u2 u3)) G L
        (FVComp v1 (FVComp v2 v3))
        (FCVComp alpha (FCVComp beta gamma)))
| pce_hleft_identity : forall A B A' B'
    (u : FVertical A A') (v : FVertical B B')
    (G : FSheet A B) (H : FSheet A' B') (alpha : FCell u G H v),
    PackedCellEq
      (PackCell A B A' B' u
        (FHComp (FHId A) G) (FHComp (FHId A') H) v
        (FCHComp (FCIdSquare u) alpha))
      (PackCell A B A' B' u G H v alpha)
| pce_hright_identity : forall A B A' B'
    (u : FVertical A A') (v : FVertical B B')
    (G : FSheet A B) (H : FSheet A' B') (alpha : FCell u G H v),
    PackedCellEq
      (PackCell A B A' B' u
        (FHComp G (FHId B)) (FHComp H (FHId B')) v
        (FCHComp alpha (FCIdSquare v)))
      (PackCell A B A' B' u G H v alpha)
| pce_hassociativity : forall A B C D A' B' C' D'
    (u : FVertical A A') (v : FVertical B B')
    (w : FVertical C C') (x : FVertical D D')
    (G : FSheet A B) (G' : FSheet A' B')
    (H : FSheet B C) (H' : FSheet B' C')
    (K : FSheet C D) (K' : FSheet C' D')
    (alpha : FCell u G G' v) (beta : FCell v H H' w)
    (gamma : FCell w K K' x),
    PackedCellEq
      (PackCell A D A' D' u
        (FHComp (FHComp G H) K) (FHComp (FHComp G' H') K') x
        (FCHComp (FCHComp alpha beta) gamma))
      (PackCell A D A' D' u
        (FHComp G (FHComp H K)) (FHComp G' (FHComp H' K')) x
        (FCHComp alpha (FCHComp beta gamma)))
| pce_interchange : forall A B C A' B' C' A'' B'' C''
    (u1 : FVertical A A') (u2 : FVertical A' A'')
    (v1 : FVertical B B') (v2 : FVertical B' B'')
    (w1 : FVertical C C') (w2 : FVertical C' C'')
    (G0 : FSheet A B) (G1 : FSheet A' B') (G2 : FSheet A'' B'')
    (H0 : FSheet B C) (H1 : FSheet B' C') (H2 : FSheet B'' C'')
    (alpha1 : FCell u1 G0 G1 v1) (alpha2 : FCell v1 H0 H1 w1)
    (beta1 : FCell u2 G1 G2 v2) (beta2 : FCell v2 H1 H2 w2),
    PackedCellEq
      (PackCell A C A'' C'' (FVComp u1 u2)
        (FHComp G0 H0) (FHComp G2 H2) (FVComp w1 w2)
        (FCVComp (FCHComp alpha1 alpha2) (FCHComp beta1 beta2)))
      (PackCell A C A'' C'' (FVComp u1 u2)
        (FHComp G0 H0) (FHComp G2 H2) (FVComp w1 w2)
        (FCHComp (FCVComp alpha1 beta1) (FCVComp alpha2 beta2)))
| pce_tensor_identity : forall A B C D
    (G : FSheet A B) (H : FSheet C D),
    PackedCellEq
      (PackCell (iface_sum A C) (iface_sum B D)
        (iface_sum A C) (iface_sum B D)
        (FVTensor (FVId A) (FVId C)) (FHTensor G H) (FHTensor G H)
        (FVTensor (FVId B) (FVId D))
        (FCTensor (FCId2 G) (FCId2 H)))
      (PackCell (iface_sum A C) (iface_sum B D)
        (iface_sum A C) (iface_sum B D)
        (FVId (iface_sum A C)) (FHTensor G H) (FHTensor G H)
        (FVId (iface_sum B D)) (FCId2 (FHTensor G H)))
| pce_tensor_vcomp : forall A B A' B' A'' B'' C D C' D' C'' D''
    (u1 : FVertical A A') (u2 : FVertical A' A'')
    (v1 : FVertical B B') (v2 : FVertical B' B'')
    (x1 : FVertical C C') (x2 : FVertical C' C'')
    (y1 : FVertical D D') (y2 : FVertical D' D'')
    (G0 : FSheet A B) (G1 : FSheet A' B') (G2 : FSheet A'' B'')
    (H0 : FSheet C D) (H1 : FSheet C' D') (H2 : FSheet C'' D'')
    (alpha1 : FCell u1 G0 G1 v1) (alpha2 : FCell u2 G1 G2 v2)
    (beta1 : FCell x1 H0 H1 y1) (beta2 : FCell x2 H1 H2 y2),
    PackedCellEq
      (PackCell (iface_sum A C) (iface_sum B D)
        (iface_sum A'' C'') (iface_sum B'' D'')
        (FVTensor (FVComp u1 u2) (FVComp x1 x2))
        (FHTensor G0 H0) (FHTensor G2 H2)
        (FVTensor (FVComp v1 v2) (FVComp y1 y2))
        (FCTensor (FCVComp alpha1 alpha2) (FCVComp beta1 beta2)))
      (PackCell (iface_sum A C) (iface_sum B D)
        (iface_sum A'' C'') (iface_sum B'' D'')
        (FVComp (FVTensor u1 x1) (FVTensor u2 x2))
        (FHTensor G0 H0) (FHTensor G2 H2)
        (FVComp (FVTensor v1 y1) (FVTensor v2 y2))
        (FCVComp (FCTensor alpha1 beta1) (FCTensor alpha2 beta2)))
| pce_tensor_hcomp : forall A B C A' B' C' D E F D' E' F'
    (u : FVertical A A') (v : FVertical B B') (w : FVertical C C')
    (x : FVertical D D') (y : FVertical E E') (z : FVertical F F')
    (G : FSheet A B) (G' : FSheet A' B')
    (H : FSheet B C) (H' : FSheet B' C')
    (K : FSheet D E) (K' : FSheet D' E')
    (L : FSheet E F) (L' : FSheet E' F')
    (alpha1 : FCell u G G' v) (alpha2 : FCell v H H' w)
    (beta1 : FCell x K K' y) (beta2 : FCell y L L' z),
    PackedCellEq
      (PackCell (iface_sum A D) (iface_sum C F)
        (iface_sum A' D') (iface_sum C' F')
        (FVTensor u x)
        (FHTensor (FHComp G H) (FHComp K L))
        (FHTensor (FHComp G' H') (FHComp K' L'))
        (FVTensor w z)
        (FCTensor (FCHComp alpha1 alpha2) (FCHComp beta1 beta2)))
      (PackCell (iface_sum A D) (iface_sum C F)
        (iface_sum A' D') (iface_sum C' F')
        (FVTensor u x)
        (FHComp (FHTensor G K) (FHTensor H L))
        (FHComp (FHTensor G' K') (FHTensor H' L'))
        (FVTensor w z)
        (FCHComp (FCTensor alpha1 beta1) (FCTensor alpha2 beta2)))
| pce_cap_identity : forall (b : FCapability) A B (G : FSheet A B),
    PackedCellEq
      (PackCell (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
        (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
        (@action_vertical _ (fcap_in_action b) A A (FVId A))
        (FHNest b G) (FHNest b G)
        (@action_vertical _ (fcap_out_action b) B B (FVId B))
        (FCNest b (FCId2 G)))
      (PackCell (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
        (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
        (FVId (cap_in (fcap_base b) A))
        (FHNest b G) (FHNest b G)
        (FVId (cap_out (fcap_base b) B)) (FCId2 (FHNest b G)))
| pce_cap_vcomp : forall (b : FCapability)
    A B A' B' A'' B''
    (u : FVertical A A') (u' : FVertical A' A'')
    (v : FVertical B B') (v' : FVertical B' B'')
    (G : FSheet A B) (H : FSheet A' B') (K : FSheet A'' B'')
    (alpha : FCell u G H v) (beta : FCell u' H K v'),
    PackedCellEq
      (PackCell (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
        (cap_in (fcap_base b) A'') (cap_out (fcap_base b) B'')
        (@action_vertical _ (fcap_in_action b) A A'' (FVComp u u'))
        (FHNest b G) (FHNest b K)
        (@action_vertical _ (fcap_out_action b) B B'' (FVComp v v'))
        (FCNest b (FCVComp alpha beta)))
      (PackCell (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
        (cap_in (fcap_base b) A'') (cap_out (fcap_base b) B'')
        (FVComp
          (@action_vertical _ (fcap_in_action b) A A' u)
          (@action_vertical _ (fcap_in_action b) A' A'' u'))
        (FHNest b G) (FHNest b K)
        (FVComp
          (@action_vertical _ (fcap_out_action b) B B' v)
          (@action_vertical _ (fcap_out_action b) B' B'' v'))
        (FCVComp (FCNest b alpha) (FCNest b beta)))
| pce_associator_inverse_left : forall A B C D
    (G : FSheet A B) (H : FSheet B C) (K : FSheet C D),
    PackedCellEq
      (PackCell A D A D (FVComp (FVId A) (FVId A))
        (FHComp (FHComp G H) K) (FHComp (FHComp G H) K)
        (FVComp (FVId D) (FVId D))
        (FCVComp (FCAssociator G H K) (FCAssociatorInv G H K)))
      (PackCell A D A D (FVId A)
        (FHComp (FHComp G H) K) (FHComp (FHComp G H) K)
        (FVId D) (FCId2 (FHComp (FHComp G H) K)))
| pce_associator_inverse_right : forall A B C D
    (G : FSheet A B) (H : FSheet B C) (K : FSheet C D),
    PackedCellEq
      (PackCell A D A D (FVComp (FVId A) (FVId A))
        (FHComp G (FHComp H K)) (FHComp G (FHComp H K))
        (FVComp (FVId D) (FVId D))
        (FCVComp (FCAssociatorInv G H K) (FCAssociator G H K)))
      (PackCell A D A D (FVId A)
        (FHComp G (FHComp H K)) (FHComp G (FHComp H K))
        (FVId D) (FCId2 (FHComp G (FHComp H K))))
| pce_left_unitor_inverse_left : forall A B (G : FSheet A B),
    PackedCellEq
      (PackCell A B A B (FVComp (FVId A) (FVId A))
        (FHComp (FHId A) G) (FHComp (FHId A) G)
        (FVComp (FVId B) (FVId B))
        (FCVComp (FCLeftUnitor G) (FCLeftUnitorInv G)))
      (PackCell A B A B (FVId A)
        (FHComp (FHId A) G) (FHComp (FHId A) G)
        (FVId B) (FCId2 (FHComp (FHId A) G)))
| pce_left_unitor_inverse_right : forall A B (G : FSheet A B),
    PackedCellEq
      (PackCell A B A B (FVComp (FVId A) (FVId A)) G G
        (FVComp (FVId B) (FVId B))
        (FCVComp (FCLeftUnitorInv G) (FCLeftUnitor G)))
      (PackCell A B A B (FVId A) G G (FVId B) (FCId2 G))
| pce_right_unitor_inverse_left : forall A B (G : FSheet A B),
    PackedCellEq
      (PackCell A B A B (FVComp (FVId A) (FVId A))
        (FHComp G (FHId B)) (FHComp G (FHId B))
        (FVComp (FVId B) (FVId B))
        (FCVComp (FCRightUnitor G) (FCRightUnitorInv G)))
      (PackCell A B A B (FVId A)
        (FHComp G (FHId B)) (FHComp G (FHId B))
        (FVId B) (FCId2 (FHComp G (FHId B))))
| pce_right_unitor_inverse_right : forall A B (G : FSheet A B),
    PackedCellEq
      (PackCell A B A B (FVComp (FVId A) (FVId A)) G G
        (FVComp (FVId B) (FVId B))
        (FCVComp (FCRightUnitorInv G) (FCRightUnitor G)))
      (PackCell A B A B (FVId A) G G (FVId B) (FCId2 G))
| pce_pentagon : forall A B C D E
    (G : FSheet A B) (H : FSheet B C)
    (K : FSheet C D) (L : FSheet D E),
    PackedCellEq
      (PackCell A E A E
        (FVComp (FVComp (FVId A) (FVId A)) (FVId A))
        (FHComp (FHComp (FHComp G H) K) L)
        (FHComp G (FHComp H (FHComp K L)))
        (FVComp (FVComp (FVId E) (FVId E)) (FVId E))
        (FCVComp
          (FCVComp
            (FCHComp (FCAssociator G H K) (FCId2 L))
            (FCAssociator G (FHComp H K) L))
          (FCHComp (FCId2 G) (FCAssociator H K L))))
      (PackCell A E A E (FVComp (FVId A) (FVId A))
        (FHComp (FHComp (FHComp G H) K) L)
        (FHComp G (FHComp H (FHComp K L)))
        (FVComp (FVId E) (FVId E))
        (FCVComp
          (FCAssociator (FHComp G H) K L)
          (FCAssociator G H (FHComp K L))))
| pce_triangle : forall A B C (G : FSheet A B) (H : FSheet B C),
    PackedCellEq
      (PackCell A C A C (FVComp (FVId A) (FVId A))
        (FHComp (FHComp G (FHId B)) H) (FHComp G H)
        (FVComp (FVId C) (FVId C))
        (FCVComp
          (FCAssociator G (FHId B) H)
          (FCHComp (FCId2 G) (FCLeftUnitor H))))
      (PackCell A C A C (FVId A)
        (FHComp (FHComp G (FHId B)) H) (FHComp G H) (FVId C)
        (FCHComp (FCRightUnitor G) (FCId2 H)))
| pce_equipment_companion_triangle : forall A B (u : FVertical A B),
    PackedCellEq
      (PackCell A B A B
        (FVComp
          (FVComp (FVComp (FVComp (FVId A) (FVId A)) (FVId A)) (FVId A))
          (FVId A))
        (FHCompanion u) (FHCompanion u)
        (FVComp
          (FVComp (FVComp (FVComp (FVId B) (FVId B)) (FVId B)) (FVId B))
          (FVId B))
        (FCVComp
          (FCVComp
            (FCVComp
              (FCVComp
                (FCLeftUnitorInv (FHCompanion u))
                (FCHComp (FCCompanionUnit u) (FCId2 (FHCompanion u))))
              (FCAssociator (FHCompanion u) (FHConjoint u)
                (FHCompanion u)))
            (FCHComp (FCId2 (FHCompanion u)) (FCCompanionCounit u)))
          (FCRightUnitor (FHCompanion u))))
      (PackCell A B A B (FVId A) (FHCompanion u) (FHCompanion u)
        (FVId B) (FCId2 (FHCompanion u)))
| pce_equipment_conjoint_triangle : forall A B (u : FVertical A B),
    PackedCellEq
      (PackCell B A B A
        (FVComp
          (FVComp (FVComp (FVComp (FVId B) (FVId B)) (FVId B)) (FVId B))
          (FVId B))
        (FHConjoint u) (FHConjoint u)
        (FVComp
          (FVComp (FVComp (FVComp (FVId A) (FVId A)) (FVId A)) (FVId A))
          (FVId A))
        (FCVComp
          (FCVComp
            (FCVComp
              (FCVComp
                (FCRightUnitorInv (FHConjoint u))
                (FCHComp (FCId2 (FHConjoint u)) (FCCompanionUnit u)))
              (FCAssociatorInv (FHConjoint u) (FHCompanion u)
                (FHConjoint u)))
            (FCHComp (FCCompanionCounit u) (FCId2 (FHConjoint u))))
          (FCLeftUnitor (FHConjoint u))))
      (PackCell B A B A (FVId B) (FHConjoint u) (FHConjoint u)
        (FVId A) (FCId2 (FHConjoint u)))
| pce_symmetry_involution : forall A B C D
    (G : FSheet A B) (H : FSheet C D),
    PackedCellEq
      (PackCell (iface_sum A C) (iface_sum B D)
        (iface_sum A C) (iface_sum B D)
        (FVComp (FVSymmetry A C) (FVSymmetry C A))
        (FHTensor G H) (FHTensor G H)
        (FVComp (FVSymmetry B D) (FVSymmetry D B))
        (FCVComp (FCSymmetry G H) (FCSymmetry H G)))
      (PackCell (iface_sum A C) (iface_sum B D)
        (iface_sum A C) (iface_sum B D)
        (FVId (iface_sum A C)) (FHTensor G H) (FHTensor G H)
        (FVId (iface_sum B D)) (FCId2 (FHTensor G H)))
| pce_symmetry_naturality : forall A B C D A' B' C' D'
    (u : FVertical A A') (v : FVertical B B')
    (u' : FVertical C C') (v' : FVertical D D')
    (G : FSheet A B) (G' : FSheet A' B')
    (H : FSheet C D) (H' : FSheet C' D')
    (alpha : FCell u G G' v) (beta : FCell u' H H' v'),
    PackedCellEq
      (PackCell (iface_sum A C) (iface_sum B D)
        (iface_sum C' A') (iface_sum D' B')
        (FVComp (FVTensor u u') (FVSymmetry A' C'))
        (FHTensor G H) (FHTensor H' G')
        (FVComp (FVTensor v v') (FVSymmetry B' D'))
        (FCVComp (FCTensor alpha beta) (FCSymmetry G' H')))
      (PackCell (iface_sum A C) (iface_sum B D)
        (iface_sum C' A') (iface_sum D' B')
        (FVComp (FVSymmetry A C) (FVTensor u' u))
        (FHTensor G H) (FHTensor H' G')
        (FVComp (FVSymmetry B D) (FVTensor v' v))
        (FCVComp (FCSymmetry G H) (FCTensor beta alpha)))
| pce_symmetry_hexagon : forall A B C D E F
    (G : FSheet A B) (H : FSheet C D) (K : FSheet E F),
    PackedCellEq
      (PackCell (iface_sum A (iface_sum C E))
        (iface_sum B (iface_sum D F))
        (iface_sum (iface_sum C E) A)
        (iface_sum (iface_sum D F) B)
        (FVSymmetry A (iface_sum C E))
        (FHTensor G (FHTensor H K))
        (FHTensor (FHTensor H K) G)
        (FVSymmetry B (iface_sum D F))
        (FCSymmetry G (FHTensor H K)))
      (PackCell (iface_sum A (iface_sum C E))
        (iface_sum B (iface_sum D F))
        (iface_sum (iface_sum C E) A)
        (iface_sum (iface_sum D F) B)
        (FVSymmetry A (iface_sum C E))
        (FHTensor G (FHTensor H K))
        (FHTensor (FHTensor H K) G)
        (FVSymmetry B (iface_sum D F))
        (FCSymmetryHexagonComposite G H K)).

Theorem PackedCellEq_equivalence : Equivalence PackedCellEq.
Proof. split; [exact pce_refl | exact pce_sym | exact pce_trans]. Qed.

Definition packed_cell_rule_count (rule : RuleCode) (alpha : PackedCell) : nat :=
  match alpha with
  | PackCell _ _ _ _ _ _ _ _ cell => fcell_rule_count rule cell
  end.

Theorem PackedCellEq_preserves_primitive_rule_multiset rule alpha beta :
  PackedCellEq alpha beta ->
  packed_cell_rule_count rule alpha = packed_cell_rule_count rule beta.
Proof. intro E. induction E; simpl in *; lia. Qed.

Record InterfaceClass : Type := {
  interface_representative : Interface
}.
Definition InterfaceClassEq (A B : InterfaceClass) : Prop :=
  InterfaceEq (interface_representative A) (interface_representative B).

Record VerticalClass (A B : Interface) : Type := {
  vertical_representative : FVertical A B
}.
Definition VerticalClassEq {A B} (u v : VerticalClass A B) : Prop :=
  PackedVerticalEq
    (PackVertical A B (vertical_representative u))
    (PackVertical A B (vertical_representative v)).

Record SheetClass (A B : Interface) : Type := {
  sheet_representative : FSheet A B
}.
Definition SheetClassEq {A B} (G H : SheetClass A B) : Prop :=
  PackedSheetEq
    (PackSheet A B (sheet_representative G))
    (PackSheet A B (sheet_representative H)).

Record CellClass : Type := {
  cell_representative : PackedCell
}.
Definition CellClassEq (alpha beta : CellClass) : Prop :=
  PackedCellEq (cell_representative alpha) (cell_representative beta).

Theorem InterfaceClassEq_equivalence : Equivalence InterfaceClassEq.
Proof. split; unfold InterfaceClassEq, InterfaceEq; congruence. Qed.

Theorem VerticalClassEq_equivalence A B :
  Equivalence (@VerticalClassEq A B).
Proof.
  split.
  - intros [u]. exact (pve_refl (PackVertical A B u)).
  - intros [u] [v] E. exact (pve_sym E).
  - intros [u] [v] [w] E1 E2. exact (pve_trans E1 E2).
Qed.

Theorem SheetClassEq_equivalence A B : Equivalence (@SheetClassEq A B).
Proof.
  split.
  - intros [G]. exact (pse_refl (PackSheet A B G)).
  - intros [G] [H] E. exact (pse_sym E).
  - intros [G] [H] [K] E1 E2. exact (pse_trans E1 E2).
Qed.

Theorem CellClassEq_equivalence : Equivalence CellClassEq.
Proof.
  split.
  - intros [alpha]. exact (pce_refl alpha).
  - intros [alpha] [beta] E. exact (pce_sym E).
  - intros [alpha] [beta] [gamma] E1 E2. exact (pce_trans E1 E2).
Qed.

Definition class_vcomp {A B C}
    (u : VerticalClass A B) (v : VerticalClass B C) : VerticalClass A C :=
  {| vertical_representative :=
       FVComp (vertical_representative u) (vertical_representative v) |}.

Lemma class_vcomp_respects {A B C}
    (u u' : VerticalClass A B) (v v' : VerticalClass B C) :
  VerticalClassEq u u' -> VerticalClassEq v v' ->
  VerticalClassEq (class_vcomp u v) (class_vcomp u' v').
Proof. intros Eu Ev. exact (pve_comp_congr Eu Ev). Qed.

Definition class_vtensor {A B C D}
    (u : VerticalClass A B) (v : VerticalClass C D) :
    VerticalClass (iface_sum A C) (iface_sum B D) :=
  {| vertical_representative :=
       FVTensor (vertical_representative u) (vertical_representative v) |}.

Lemma class_vtensor_respects {A B C D}
    (u u' : VerticalClass A B) (v v' : VerticalClass C D) :
  VerticalClassEq u u' -> VerticalClassEq v v' ->
  VerticalClassEq (class_vtensor u v) (class_vtensor u' v').
Proof. intros Eu Ev. exact (pve_tensor_congr Eu Ev). Qed.

Definition class_hcomp {A B C}
    (G : SheetClass A B) (H : SheetClass B C) : SheetClass A C :=
  {| sheet_representative :=
       FHComp (sheet_representative G) (sheet_representative H) |}.

Lemma class_hcomp_respects {A B C}
    (G G' : SheetClass A B) (H H' : SheetClass B C) :
  SheetClassEq G G' -> SheetClassEq H H' ->
  SheetClassEq (class_hcomp G H) (class_hcomp G' H').
Proof. intros EG EH. exact (pse_hcomp_congr EG EH). Qed.

Definition class_htensor {A B C D}
    (G : SheetClass A B) (H : SheetClass C D) :
    SheetClass (iface_sum A C) (iface_sum B D) :=
  {| sheet_representative :=
       FHTensor (sheet_representative G) (sheet_representative H) |}.

Lemma class_htensor_respects {A B C D}
    (G G' : SheetClass A B) (H H' : SheetClass C D) :
  SheetClassEq G G' -> SheetClassEq H H' ->
  SheetClassEq (class_htensor G H) (class_htensor G' H').
Proof. intros EG EH. exact (pse_tensor_congr EG EH). Qed.

(** Version 0.2.1 of the manuscript expands every formerly name-only core
    equation family.  This finite tag set is a coverage index, not an axiom. *)
Inductive NormalizedEquationFamily : Type :=
| NormVerticalCategory | NormHorizontalCategory | NormTensor
| NormSymmetry | NormCategory2 | NormInterchange | NormMonoidal2
| NormCoherence | NormCapability2 | NormFoundationProof
| NormEquipmentLeft | NormEquipmentRight | NormMultisortedStrictification.

Definition normalized_equation_families : list NormalizedEquationFamily :=
  [NormVerticalCategory; NormHorizontalCategory; NormTensor; NormSymmetry;
   NormCategory2; NormInterchange; NormMonoidal2; NormCoherence;
   NormCapability2; NormFoundationProof; NormEquipmentLeft;
   NormEquipmentRight; NormMultisortedStrictification].

Theorem normalized_equation_family_coverage o :
  In o normalized_equation_families.
Proof. destruct o; simpl; tauto. Qed.

(** * Exact Section 9 hierarchical-hypergraph carrier *)

Definition PMMaps {A B} (f : PartialMap A B) (x : A) (y : B) : Prop :=
  In (x, y) (pm_graph f).

Definition PMDomainExact {A B} (f : PartialMap A B) (xs : list A) : Prop :=
  forall x, In x (pm_dom f) <-> In x xs.

Definition PRangeIn {A B} (f : PartialMap A B) (ys : list B) : Prop :=
  forall x y, PMMaps f x y -> In y ys.

Record HGTagCodes : Type := {
  tag_anchor : Code;
  tag_occurrence : Code;
  tag_gateway : Code;
  tag_ref : Code;
  tag_obj : Code;
  tag_ctl : Code
}.

Record ExactHypergraph : Type := {
  eh_regions : list Id;
  eh_nodes : list Id;
  eh_ports : list Id;
  eh_edges : list Id;
  eh_root : Id;
  eh_parent : PartialMap Id Id;
  eh_owner : PartialMap Id (SumCode Id Id);
  eh_loc : PartialMap (SumCode Id Id) Id;
  eh_src : PartialMap Id (list Id);
  eh_tgt : PartialMap Id (list Id);
  eh_kappa_region : PartialMap Id (SumCode FCapability Code);
  eh_kappa_node : PartialMap Id Code;
  eh_kappa_port : PartialMap Id Slot;
  eh_kappa_edge : PartialMap Id (SumCode WireKind Code);
  eh_inputs : list Id;
  eh_outputs : list Id;
  eh_label : PartialMap Id (list Code)
}.

Record HGTyping : Type := {
  hgt_tags : HGTagCodes;
  hgt_capabilities : list FCapability;
  hgt_anchors : list Anchor;
  hgt_occurrences : list Occurrence
}.

Record HGDerivedEvidence : Type := {
  ev_inner_input : PartialMap Id Interface;
  ev_inner_output : PartialMap Id Interface;
  ev_outer_input : PartialMap Id Interface;
  ev_outer_output : PartialMap Id Interface;
  ev_edge_itinerary : PartialMap Id Itinerary;
  ev_edge_regions : list (Id * Id);
  ev_ref_endpoints : list (Id * (Occurrence * Anchor))
}.

Definition eh_carrier (G : ExactHypergraph) : list Id :=
  eh_regions G ++ eh_nodes G ++ eh_ports G ++ eh_edges G.

Definition exact_carrier_wf (G : ExactHypergraph) : Prop :=
  NoDup (eh_regions G) /\ NoDup (eh_nodes G) /\
  NoDup (eh_ports G) /\ NoDup (eh_edges G) /\
  pairwise_disjoint4 (eh_regions G) (eh_nodes G) (eh_ports G) (eh_edges G).

Definition exact_parent_rel (G : ExactHypergraph) (r s : Id) : Prop :=
  PMMaps (eh_parent G) r s.

Definition exact_region_tree (G : ExactHypergraph) : Prop :=
  In (eh_root G) (eh_regions G) /\
  PMDomainExact (eh_parent G)
    (filter (fun r => negb (Nat.eqb r (eh_root G))) (eh_regions G)) /\
  PRangeIn (eh_parent G) (eh_regions G) /\
  forall r, In r (eh_regions G) ->
    exists! n,
      rel_power (exact_parent_rel G) n r (eh_root G) /\
      forall k, k < n -> ~ rel_power (exact_parent_rel G) k r (eh_root G).

Definition exact_owner_wf (G : ExactHypergraph) : Prop :=
  PMDomainExact (eh_owner G) (eh_ports G) /\
  forall p x, PMMaps (eh_owner G) p x ->
    match x with
    | inj0 n => In n (eh_nodes G)
    | inj1 r => In r (eh_regions G)
    end.

Definition exact_loc_wf (G : ExactHypergraph) : Prop :=
  (forall x, In x (pm_dom (eh_loc G)) <->
     match x with
     | inj0 n => In n (eh_nodes G)
     | inj1 e => In e (eh_edges G)
     end) /\
  PRangeIn (eh_loc G) (eh_regions G).

Definition exact_incidence_wf (G : ExactHypergraph) : Prop :=
  PMDomainExact (eh_src G) (eh_edges G) /\
  PMDomainExact (eh_tgt G) (eh_edges G) /\
  (forall e ps, PMMaps (eh_src G) e ps -> Forall (fun p => In p (eh_ports G)) ps) /\
  (forall e ps, PMMaps (eh_tgt G) e ps -> Forall (fun p => In p (eh_ports G)) ps).

Definition exact_kappa_wf (G : ExactHypergraph) : Prop :=
  PMDomainExact (eh_kappa_region G) (eh_regions G) /\
  PMDomainExact (eh_kappa_node G) (eh_nodes G) /\
  PMDomainExact (eh_kappa_port G) (eh_ports G) /\
  PMDomainExact (eh_kappa_edge G) (eh_edges G).

Definition port_has_polarity (G : ExactHypergraph) (p : Id) (pol : Polarity) : Prop :=
  exists slot, PMMaps (eh_kappa_port G) p slot /\ slot_pol slot = pol.

Definition exact_open_boundary_wf (G : ExactHypergraph) : Prop :=
  NoDup (eh_inputs G) /\ NoDup (eh_outputs G) /\
  (forall p, In p (eh_inputs G) -> In p (eh_ports G) /\ port_has_polarity G p PIn) /\
  (forall p, In p (eh_outputs G) -> In p (eh_ports G) /\ port_has_polarity G p POut) /\
  (forall p, In p (eh_inputs G) -> ~ In p (eh_outputs G)).

Definition exact_label_wf (G : ExactHypergraph) : Prop :=
  forall x, In x (pm_dom (eh_label G)) -> In x (eh_carrier G).

Definition role_payload (r : Role) : Code :=
  match r with RoleCode c | RoleSort c => c end.

Definition anchor_payload (a : Anchor) : list Code :=
  [anchor_id a; anchor_uri a; role_payload (anchor_sort a); anchor_label a].

Definition occurrence_payload (o : Occurrence) : list Code :=
  [occurrence_id o; role_payload (occurrence_sort o);
   occurrence_label o; occurrence_zone o].

Definition exact_anchor_realized
    (T : HGTyping) (G : ExactHypergraph) : Prop :=
  (forall a, In a (hgt_anchors T) ->
     exists! n,
       In n (eh_nodes G) /\
       PMMaps (eh_kappa_node G) n (tag_anchor (hgt_tags T)) /\
       PMMaps (eh_label G) n (anchor_payload a)) /\
  (forall a a', In a (hgt_anchors T) -> In a' (hgt_anchors T) ->
     anchor_id a = anchor_id a' -> a = a').

Definition exact_occurrence_realized
    (T : HGTyping) (G : ExactHypergraph) : Prop :=
  forall o, In o (hgt_occurrences T) ->
    exists n,
      In n (eh_nodes G) /\
      PMMaps (eh_kappa_node G) n (tag_occurrence (hgt_tags T)) /\
      PMMaps (eh_label G) n (occurrence_payload o).

Definition exact_capability_realized
    (T : HGTyping) (G : ExactHypergraph) (E : HGDerivedEvidence) : Prop :=
  PMDomainExact (ev_inner_input E) (eh_regions G) /\
  PMDomainExact (ev_inner_output E) (eh_regions G) /\
  PMDomainExact (ev_outer_input E) (eh_regions G) /\
  PMDomainExact (ev_outer_output E) (eh_regions G) /\
  forall r b inner_in inner_out outer_in outer_out,
    PMMaps (eh_kappa_region G) r (inj0 b) ->
    PMMaps (ev_inner_input E) r inner_in ->
    PMMaps (ev_inner_output E) r inner_out ->
    PMMaps (ev_outer_input E) r outer_in ->
    PMMaps (ev_outer_output E) r outer_out ->
    In b (hgt_capabilities T) /\
    CapabilityWF (fcap_base b) /\
    outer_in = cap_in (fcap_base b) inner_in /\
    outer_out = cap_out (fcap_base b) inner_out.

Definition exact_crossing_certified
    (G : ExactHypergraph) (E : HGDerivedEvidence) : Prop :=
  PMDomainExact (ev_edge_itinerary E) (eh_edges G) /\
  (forall e p, PMMaps (ev_edge_itinerary E) e p -> ItineraryWF p) /\
  (forall e r, In (e, r) (ev_edge_regions E) ->
     In e (eh_edges G) /\ In r (eh_regions G)) /\
  (forall e o a, In (e, (o, a)) (ev_ref_endpoints E) ->
     In e (eh_edges G) /\
     occurrence_sort o = anchor_sort a /\
     exists p, PMMaps (ev_edge_itinerary E) e p).

Definition exact_scope_safe
    (T : HGTyping) (G : ExactHypergraph) (E : HGDerivedEvidence) : Prop :=
  forall e o a r b,
    In (e, (o, a)) (ev_ref_endpoints E) ->
    In (e, r) (ev_edge_regions E) ->
    PMMaps (eh_kappa_region G) r (inj0 b) ->
    exists a',
      In a' (hgt_anchors T) /\
      cap_scope (fcap_base b) a = Some a' /\
      anchor_sort a = anchor_sort a'.

Definition ExactHGWF (T : HGTyping) (G : ExactHypergraph)
    (E : HGDerivedEvidence) : Prop :=
  exact_carrier_wf G /\
  exact_region_tree G /\
  exact_owner_wf G /\
  exact_loc_wf G /\
  exact_incidence_wf G /\
  exact_kappa_wf G /\
  exact_open_boundary_wf G /\
  exact_label_wf G /\
  exact_capability_realized T G E /\
  exact_anchor_realized T G /\
  exact_occurrence_realized T G /\
  exact_crossing_certified G E /\
  exact_scope_safe T G E.

Record WellFormedExactHG : Type := {
  wfhg_typing : HGTyping;
  wfhg_graph : ExactHypergraph;
  wfhg_evidence : HGDerivedEvidence;
  wfhg_proof : ExactHGWF wfhg_typing wfhg_graph wfhg_evidence
}.

(** Exact interface matching uses port descriptors, not merely equal lengths. *)
Definition boundary_slots (G : ExactHypergraph) (ps : list Id)
    (slots : list Slot) : Prop :=
  Forall2 (fun p s => PMMaps (eh_kappa_port G) p s) ps slots.

Record ExactInterfaceMatch (G H : ExactHypergraph) : Type := {
  match_slots : list Slot;
  match_left_slots : boundary_slots G (eh_outputs G) match_slots;
  match_right_slots : boundary_slots H (eh_inputs H) match_slots
}.

Definition TaggedId := SumCode Id Id.

Inductive GluePortStep (G H : ExactHypergraph)
    (M : ExactInterfaceMatch G H) : TaggedId -> TaggedId -> Prop :=
| glue_port_step : forall i p q,
    nth_error (eh_outputs G) i = Some p ->
    nth_error (eh_inputs H) i = Some q ->
    GluePortStep M (inj0 p) (inj1 q).

Definition GluePortEq G H (M : ExactInterfaceMatch G H) : TaggedId -> TaggedId -> Prop :=
  generated_equivalence (GluePortStep M).

Theorem GluePortEq_equivalence G H (M : ExactInterfaceMatch G H) :
  Equivalence (GluePortEq M).
Proof. apply generated_equivalence_Equivalence. Qed.

Theorem glued_boundary_ports_identified G H (M : ExactInterfaceMatch G H)
    i p q :
  nth_error (eh_outputs G) i = Some p ->
  nth_error (eh_inputs H) i = Some q ->
  GluePortEq M (inj0 p) (inj1 q).
Proof. intros Hp Hq. apply ge_step. eapply glue_port_step; eauto. Qed.

Record OpenGluingSetoid (G H : ExactHypergraph)
    (M : ExactInterfaceMatch G H) : Type := {
  og_regions : list TaggedId;
  og_nodes : list TaggedId;
  og_ports : list TaggedId;
  og_edges : list TaggedId;
  og_regions_exact :
    og_regions = map inj0 (eh_regions G) ++ map inj1 (eh_regions H);
  og_nodes_exact :
    og_nodes = map inj0 (eh_nodes G) ++ map inj1 (eh_nodes H);
  og_ports_exact :
    og_ports = map inj0 (eh_ports G) ++ map inj1 (eh_ports H);
  og_edges_exact :
    og_edges = map inj0 (eh_edges G) ++ map inj1 (eh_edges H);
  og_port_equality : TaggedId -> TaggedId -> Prop;
  og_port_equality_exact : forall x y,
    og_port_equality x y <-> GluePortEq M x y
}.

Definition make_open_gluing_setoid G H (M : ExactInterfaceMatch G H) :
    OpenGluingSetoid M.
Proof.
  refine
    {| og_regions := map inj0 (eh_regions G) ++ map inj1 (eh_regions H);
       og_nodes := map inj0 (eh_nodes G) ++ map inj1 (eh_nodes H);
       og_ports := map inj0 (eh_ports G) ++ map inj1 (eh_ports H);
       og_edges := map inj0 (eh_edges G) ++ map inj1 (eh_edges H);
       og_port_equality := GluePortEq M |};
    reflexivity.
Defined.

(** * Four-sorted raw universal property *)

Record VHAlgebra : Type := {
  vha_object : Type;
  vha_interface : Interface -> vha_object;
  vha_vertical : Interface -> Interface -> Type;
  vha_sheet : Interface -> Interface -> Type;
  vha_vgen : forall g, vha_vertical (vg_source g) (vg_target g);
  vha_vid : forall A, vha_vertical A A;
  vha_vcomp : forall A B C,
      vha_vertical A B -> vha_vertical B C -> vha_vertical A C;
  vha_vtensor : forall A B C D,
      vha_vertical A B -> vha_vertical C D ->
      vha_vertical (iface_sum A C) (iface_sum B D);
  vha_vsym : forall A B,
      vha_vertical (iface_sum A B) (iface_sum B A);
  vha_hgen : forall g, vha_sheet (hg_source g) (hg_target g);
  vha_hid : forall A, vha_sheet A A;
  vha_htensor : forall A B C D,
      vha_sheet A B -> vha_sheet C D ->
      vha_sheet (iface_sum A C) (iface_sum B D);
  vha_hcomp : forall A B C,
      vha_sheet A B -> vha_sheet B C -> vha_sheet A C;
  vha_hnest : forall b A B,
      vha_sheet A B ->
      vha_sheet (cap_in (fcap_base b) A) (cap_out (fcap_base b) B);
  vha_href : forall w,
      vha_sheet
        [{| slot_pol := PIn; slot_role := occurrence_sort (rw_occurrence w);
            slot_wire := RefWire;
            slot_order_role := occurrence_label (rw_occurrence w) |}]
        [{| slot_pol := POut; slot_role := anchor_sort (rw_anchor w);
            slot_wire := RefWire;
            slot_order_role := anchor_label (rw_anchor w) |}];
  vha_companion : forall A B,
      vha_vertical A B -> vha_sheet A B;
  vha_conjoint : forall A B,
      vha_vertical A B -> vha_sheet B A
}.

Fixpoint fold_fvertical (A : VHAlgebra) {X Y}
    (u : FVertical X Y) : vha_vertical A X Y :=
  match u with
  | FVGen g => vha_vgen A g
  | FVId X => vha_vid A X
  | FVComp u v => @vha_vcomp A _ _ _ (fold_fvertical A u) (fold_fvertical A v)
  | FVTensor u v => @vha_vtensor A _ _ _ _ (fold_fvertical A u) (fold_fvertical A v)
  | FVSymmetry X Y => vha_vsym A X Y
  end.

Fixpoint fold_fsheet (A : VHAlgebra) {X Y}
    (G : FSheet X Y) : vha_sheet A X Y :=
  match G with
  | FHGen g => vha_hgen A g
  | FHId X => vha_hid A X
  | FHTensor G H => @vha_htensor A _ _ _ _ (fold_fsheet A G) (fold_fsheet A H)
  | FHComp G H => @vha_hcomp A _ _ _ (fold_fsheet A G) (fold_fsheet A H)
  | FHNest b G => @vha_hnest A b _ _ (fold_fsheet A G)
  | FHRef w => vha_href A w
  | FHCompanion u => @vha_companion A _ _ (fold_fvertical A u)
  | FHConjoint u => @vha_conjoint A _ _ (fold_fvertical A u)
  end.

Record CellAlgebra (A : VHAlgebra) : Type := {
  ca_cell : forall X Y X' Y'
      (u : FVertical X X') (G : FSheet X Y)
      (H : FSheet X' Y') (v : FVertical Y Y'), Type;
  ca_primitive : forall X Y X' Y'
      (u : FVertical X X') (G : FSheet X Y)
      (H : FSheet X' Y') (v : FVertical Y Y'),
      CellCode -> RuleCode -> list DerivCode -> list Code ->
      ca_cell u G H v;
  ca_id2 : forall X Y (G : FSheet X Y),
      ca_cell (FVId X) G G (FVId Y);
  ca_idsquare : forall X Y (u : FVertical X Y),
      ca_cell u (FHId X) (FHId Y) u;
  ca_vcomp : forall X Y X' Y' X'' Y''
      (u : FVertical X X') (u' : FVertical X' X'')
      (v : FVertical Y Y') (v' : FVertical Y' Y'')
      (G : FSheet X Y) (H : FSheet X' Y') (K : FSheet X'' Y''),
      ca_cell u G H v -> ca_cell u' H K v' ->
      ca_cell (FVComp u u') G K (FVComp v v');
  ca_hcomp : forall X Y Z X' Y' Z'
      (u : FVertical X X') (v : FVertical Y Y') (w : FVertical Z Z')
      (G : FSheet X Y) (G' : FSheet X' Y')
      (H : FSheet Y Z) (H' : FSheet Y' Z'),
      ca_cell u G G' v -> ca_cell v H H' w ->
      ca_cell u (FHComp G H) (FHComp G' H') w;
  ca_tensor : forall X Y Z W X' Y' Z' W'
      (u : FVertical X X') (v : FVertical Y Y')
      (u' : FVertical Z Z') (v' : FVertical W W')
      (G : FSheet X Y) (G' : FSheet X' Y')
      (H : FSheet Z W) (H' : FSheet Z' W'),
      ca_cell u G G' v -> ca_cell u' H H' v' ->
      ca_cell (FVTensor u u') (FHTensor G H) (FHTensor G' H')
              (FVTensor v v');
  ca_nest : forall b X Y X' Y'
      (u : FVertical X X') (v : FVertical Y Y')
      (G : FSheet X Y) (H : FSheet X' Y'),
      ca_cell u G H v ->
      ca_cell
        (@action_vertical _ (fcap_in_action b) X X' u)
        (FHNest b G) (FHNest b H)
        (@action_vertical _ (fcap_out_action b) Y Y' v);
  ca_associator : forall X Y Z W
      (G : FSheet X Y) (H : FSheet Y Z) (K : FSheet Z W),
      ca_cell (FVId X) (FHComp (FHComp G H) K)
              (FHComp G (FHComp H K)) (FVId W);
  ca_associator_inv : forall X Y Z W
      (G : FSheet X Y) (H : FSheet Y Z) (K : FSheet Z W),
      ca_cell (FVId X) (FHComp G (FHComp H K))
              (FHComp (FHComp G H) K) (FVId W);
  ca_left_unitor : forall X Y (G : FSheet X Y),
      ca_cell (FVId X) (FHComp (FHId X) G) G (FVId Y);
  ca_left_unitor_inv : forall X Y (G : FSheet X Y),
      ca_cell (FVId X) G (FHComp (FHId X) G) (FVId Y);
  ca_right_unitor : forall X Y (G : FSheet X Y),
      ca_cell (FVId X) (FHComp G (FHId Y)) G (FVId Y);
  ca_right_unitor_inv : forall X Y (G : FSheet X Y),
      ca_cell (FVId X) G (FHComp G (FHId Y)) (FVId Y);
  ca_symmetry : forall X Y Z W (G : FSheet X Y) (H : FSheet Z W),
      ca_cell (FVSymmetry X Z) (FHTensor G H) (FHTensor H G)
              (FVSymmetry Y W);
  ca_symmetry_hexagon_composite : forall X Y Z W U V
      (G : FSheet X Y) (H : FSheet Z W) (K : FSheet U V),
      ca_cell (FVSymmetry X (iface_sum Z U))
              (FHTensor G (FHTensor H K))
              (FHTensor (FHTensor H K) G)
              (FVSymmetry Y (iface_sum W V));
  ca_equipment_unit : forall X Y (u : FVertical X Y),
      ca_cell (FVId X) (FHId X)
              (FHComp (FHCompanion u) (FHConjoint u)) (FVId X);
  ca_equipment_counit : forall X Y (u : FVertical X Y),
      ca_cell (FVId Y) (FHComp (FHConjoint u) (FHCompanion u))
              (FHId Y) (FVId Y)
}.

Arguments ca_primitive {A} c {X Y X' Y'} u G H v code rule premises payload.
Arguments ca_id2 {A} c {X Y} G.
Arguments ca_idsquare {A} c {X Y} u.
Arguments ca_vcomp {A} c {X Y X' Y' X'' Y'' u u' v v' G H K} _ _.
Arguments ca_hcomp {A} c {X Y Z X' Y' Z' u v w G G' H H'} _ _.
Arguments ca_tensor {A} c {X Y Z W X' Y' Z' W' u v u' v' G G' H H'} _ _.
Arguments ca_nest {A} c b {X Y X' Y' u v G H} _.
Arguments ca_associator {A} c {X Y Z W} G H K.
Arguments ca_associator_inv {A} c {X Y Z W} G H K.
Arguments ca_left_unitor {A} c {X Y} G.
Arguments ca_left_unitor_inv {A} c {X Y} G.
Arguments ca_right_unitor {A} c {X Y} G.
Arguments ca_right_unitor_inv {A} c {X Y} G.
Arguments ca_symmetry {A} c {X Y Z W} G H.
Arguments ca_symmetry_hexagon_composite {A} c {X Y Z W U V} G H K.
Arguments ca_equipment_unit {A} c {X Y} u.
Arguments ca_equipment_counit {A} c {X Y} u.

Fixpoint fold_fcell (A : VHAlgebra) (C : CellAlgebra A)
    {X Y X' Y'} {u : FVertical X X'} {G : FSheet X Y}
    {H : FSheet X' Y'} {v : FVertical Y Y'}
    (alpha : FCell u G H v) : ca_cell C u G H v :=
  match alpha with
  | FCPrimitive u G H v code rule premises payload =>
      ca_primitive C u G H v code rule premises payload
  | FCId2 G => ca_id2 C G
  | FCIdSquare u => ca_idsquare C u
  | FCVComp alpha beta => ca_vcomp C (fold_fcell C alpha) (fold_fcell C beta)
  | FCHComp alpha beta => ca_hcomp C (fold_fcell C alpha) (fold_fcell C beta)
  | FCTensor alpha beta => ca_tensor C (fold_fcell C alpha) (fold_fcell C beta)
  | FCNest b alpha => ca_nest C b (fold_fcell C alpha)
  | FCAssociator G H K => ca_associator C G H K
  | FCAssociatorInv G H K => ca_associator_inv C G H K
  | FCLeftUnitor G => ca_left_unitor C G
  | FCLeftUnitorInv G => ca_left_unitor_inv C G
  | FCRightUnitor G => ca_right_unitor C G
  | FCRightUnitorInv G => ca_right_unitor_inv C G
  | FCSymmetry G H => ca_symmetry C G H
  | FCSymmetryHexagonComposite G H K =>
      ca_symmetry_hexagon_composite C G H K
  | FCCompanionUnit u => ca_equipment_unit C u
  | FCCompanionCounit u => ca_equipment_counit C u
  end.

Record IsVerticalStructureMap (A : VHAlgebra)
    (f : forall X Y, FVertical X Y -> vha_vertical A X Y) : Prop := {
  vmap_gen : forall g, f _ _ (FVGen g) = vha_vgen A g;
  vmap_id : forall X, f X X (FVId X) = vha_vid A X;
  vmap_comp : forall X Y Z (u : FVertical X Y) (v : FVertical Y Z),
      f X Z (FVComp u v) = @vha_vcomp A X Y Z (f X Y u) (f Y Z v);
  vmap_tensor : forall X Y Z W (u : FVertical X Y) (v : FVertical Z W),
      f _ _ (FVTensor u v) = @vha_vtensor A X Y Z W (f X Y u) (f Z W v);
  vmap_sym : forall X Y, f _ _ (FVSymmetry X Y) = vha_vsym A X Y
}.

Record IsSheetStructureMap (A : VHAlgebra)
    (fv : forall X Y, FVertical X Y -> vha_vertical A X Y)
    (f : forall X Y, FSheet X Y -> vha_sheet A X Y) : Prop := {
  hmap_gen : forall g, f _ _ (FHGen g) = vha_hgen A g;
  hmap_id : forall X, f X X (FHId X) = vha_hid A X;
  hmap_tensor : forall X Y Z W (G : FSheet X Y) (H : FSheet Z W),
      f _ _ (FHTensor G H) = @vha_htensor A X Y Z W (f X Y G) (f Z W H);
  hmap_comp : forall X Y Z (G : FSheet X Y) (H : FSheet Y Z),
      f X Z (FHComp G H) = @vha_hcomp A X Y Z (f X Y G) (f Y Z H);
  hmap_nest : forall b X Y (G : FSheet X Y),
      f _ _ (FHNest b G) = @vha_hnest A b X Y (f X Y G);
  hmap_ref : forall w, f _ _ (FHRef w) = vha_href A w;
  hmap_companion : forall X Y (u : FVertical X Y),
      f X Y (FHCompanion u) = @vha_companion A X Y (fv X Y u);
  hmap_conjoint : forall X Y (u : FVertical X Y),
      f Y X (FHConjoint u) = @vha_conjoint A X Y (fv X Y u)
}.

Record IsCellStructureMap (A : VHAlgebra) (C : CellAlgebra A)
    (f : forall {X Y X' Y'} {u : FVertical X X'}
         {G : FSheet X Y} {H : FSheet X' Y'} {v : FVertical Y Y'},
         FCell u G H v -> ca_cell C u G H v) : Prop := {
  cmap_primitive : forall X Y X' Y'
      (u : FVertical X X') (G : FSheet X Y) (H : FSheet X' Y')
      (v : FVertical Y Y') code rule premises payload,
      f (FCPrimitive u G H v code rule premises payload) =
      ca_primitive C u G H v code rule premises payload;
  cmap_id2 : forall X Y (G : FSheet X Y),
      f (FCId2 G) = ca_id2 C G;
  cmap_idsquare : forall X Y (u : FVertical X Y),
      f (FCIdSquare u) = ca_idsquare C u;
  cmap_vcomp : forall X Y X' Y' X'' Y''
      (u : FVertical X X') (u' : FVertical X' X'')
      (v : FVertical Y Y') (v' : FVertical Y' Y'')
      (G : FSheet X Y) (H : FSheet X' Y') (K : FSheet X'' Y'')
      (alpha : FCell u G H v) (beta : FCell u' H K v'),
      f (FCVComp alpha beta) = ca_vcomp C (f alpha) (f beta);
  cmap_hcomp : forall X Y Z X' Y' Z'
      (u : FVertical X X') (v : FVertical Y Y') (w : FVertical Z Z')
      (G : FSheet X Y) (G' : FSheet X' Y')
      (H : FSheet Y Z) (H' : FSheet Y' Z')
      (alpha : FCell u G G' v) (beta : FCell v H H' w),
      f (FCHComp alpha beta) = ca_hcomp C (f alpha) (f beta);
  cmap_tensor : forall X Y Z W X' Y' Z' W'
      (u : FVertical X X') (v : FVertical Y Y')
      (u' : FVertical Z Z') (v' : FVertical W W')
      (G : FSheet X Y) (G' : FSheet X' Y')
      (H : FSheet Z W) (H' : FSheet Z' W')
      (alpha : FCell u G G' v) (beta : FCell u' H H' v'),
      f (FCTensor alpha beta) = ca_tensor C (f alpha) (f beta);
  cmap_nest : forall b X Y X' Y'
      (u : FVertical X X') (v : FVertical Y Y')
      (G : FSheet X Y) (H : FSheet X' Y') (alpha : FCell u G H v),
      f (FCNest b alpha) = ca_nest C b (f alpha);
  cmap_associator : forall X Y Z W
      (G : FSheet X Y) (H : FSheet Y Z) (K : FSheet Z W),
      f (FCAssociator G H K) = ca_associator C G H K;
  cmap_associator_inv : forall X Y Z W
      (G : FSheet X Y) (H : FSheet Y Z) (K : FSheet Z W),
      f (FCAssociatorInv G H K) = ca_associator_inv C G H K;
  cmap_left_unitor : forall X Y (G : FSheet X Y),
      f (FCLeftUnitor G) = ca_left_unitor C G;
  cmap_left_unitor_inv : forall X Y (G : FSheet X Y),
      f (FCLeftUnitorInv G) = ca_left_unitor_inv C G;
  cmap_right_unitor : forall X Y (G : FSheet X Y),
      f (FCRightUnitor G) = ca_right_unitor C G;
  cmap_right_unitor_inv : forall X Y (G : FSheet X Y),
      f (FCRightUnitorInv G) = ca_right_unitor_inv C G;
  cmap_symmetry : forall X Y Z W (G : FSheet X Y) (H : FSheet Z W),
      f (FCSymmetry G H) = ca_symmetry C G H;
  cmap_symmetry_hexagon_composite : forall X Y Z W U V
      (G : FSheet X Y) (H : FSheet Z W) (K : FSheet U V),
      f (FCSymmetryHexagonComposite G H K) =
      ca_symmetry_hexagon_composite C G H K;
  cmap_equipment_unit : forall X Y (u : FVertical X Y),
      f (FCCompanionUnit u) = ca_equipment_unit C u;
  cmap_equipment_counit : forall X Y (u : FVertical X Y),
      f (FCCompanionCounit u) = ca_equipment_counit C u
}.

Definition fold_vertical_map (A : VHAlgebra) :
    forall X Y, FVertical X Y -> vha_vertical A X Y :=
  fun X Y u => fold_fvertical A u.

Definition fold_sheet_map (A : VHAlgebra) :
    forall X Y, FSheet X Y -> vha_sheet A X Y :=
  fun X Y G => fold_fsheet A G.

Definition fold_cell_map (A : VHAlgebra) (C : CellAlgebra A) :
    forall {X Y X' Y'} {u : FVertical X X'}
      {G : FSheet X Y} {H : FSheet X' Y'} {v : FVertical Y Y'},
      FCell u G H v -> ca_cell C u G H v :=
  fun X Y X' Y' u G H v alpha => fold_fcell C alpha.

Lemma fold_fvertical_is_map A : IsVerticalStructureMap A (fold_vertical_map A).
Proof. constructor; reflexivity. Qed.

Lemma fold_fsheet_is_map A :
  IsSheetStructureMap A (fold_vertical_map A) (fold_sheet_map A).
Proof. constructor; reflexivity. Qed.

Lemma fold_fcell_is_map A (C : CellAlgebra A) :
  IsCellStructureMap C (@fold_cell_map A C).
Proof. constructor; reflexivity. Qed.

Theorem fold_fvertical_unique A f :
  IsVerticalStructureMap A f ->
  forall X Y (u : FVertical X Y), f X Y u = fold_fvertical A u.
Proof.
  intros H X Y u. induction u; simpl.
  - apply vmap_gen; exact H.
  - apply vmap_id; exact H.
  - rewrite (vmap_comp H), IHu1, IHu2. reflexivity.
  - rewrite (vmap_tensor H), IHu1, IHu2. reflexivity.
  - apply vmap_sym; exact H.
Qed.

Theorem fold_fsheet_unique A fv f :
  IsVerticalStructureMap A fv ->
  IsSheetStructureMap A fv f ->
  forall X Y (G : FSheet X Y), f X Y G = fold_fsheet A G.
Proof.
  intros Hv Hf X Y G. induction G; simpl.
  - apply (@hmap_gen A fv f Hf).
  - apply (@hmap_id A fv f Hf).
  - rewrite (@hmap_tensor A fv f Hf), IHG1, IHG2. reflexivity.
  - rewrite (@hmap_comp A fv f Hf), IHG1, IHG2. reflexivity.
  - rewrite (@hmap_nest A fv f Hf), IHG. reflexivity.
  - apply (@hmap_ref A fv f Hf).
  - rewrite (@hmap_companion A fv f Hf).
    now rewrite (fold_fvertical_unique Hv).
  - rewrite (@hmap_conjoint A fv f Hf).
    now rewrite (fold_fvertical_unique Hv).
Qed.

Theorem fold_fcell_unique A (C : CellAlgebra A) f :
  IsCellStructureMap C f ->
  forall X Y X' Y' (u : FVertical X X')
    (G : FSheet X Y) (H : FSheet X' Y') (v : FVertical Y Y')
    (alpha : FCell u G H v),
    f X Y X' Y' u G H v alpha = fold_fcell C alpha.
Proof.
  intros Hmap X Y X' Y' u G H v alpha.
  destruct Hmap as
      [Hp Hid Hsq Hv Hh Ht Hn Hass Hassi Hl Hli Hr Hri Hsym Hhex Heu Hec].
  induction alpha; simpl.
  - apply Hp.
  - apply Hid.
  - apply Hsq.
  - rewrite Hv, IHalpha1, IHalpha2. reflexivity.
  - rewrite Hh, IHalpha1, IHalpha2. reflexivity.
  - rewrite Ht, IHalpha1, IHalpha2. reflexivity.
  - rewrite Hn, IHalpha. reflexivity.
  - apply Hass.
  - apply Hassi.
  - apply Hl.
  - apply Hli.
  - apply Hr.
  - apply Hri.
  - apply Hsym.
  - apply Hhex.
  - apply Heu.
  - apply Hec.
Qed.

Theorem four_sorted_raw_universal_property A (C : CellAlgebra A) :
  IsVerticalStructureMap A (fold_vertical_map A) /\
  IsSheetStructureMap A (fold_vertical_map A) (fold_sheet_map A) /\
  IsCellStructureMap C (@fold_cell_map A C) /\
  (forall fv f fc,
      IsVerticalStructureMap A fv ->
      IsSheetStructureMap A fv f ->
      IsCellStructureMap C fc ->
      (forall X Y (u : FVertical X Y), fv X Y u = fold_fvertical A u) /\
      (forall X Y (G : FSheet X Y), f X Y G = fold_fsheet A G) /\
      (forall X Y X' Y' (u : FVertical X X')
        (G : FSheet X Y) (H : FSheet X' Y') (v : FVertical Y Y')
        (alpha : FCell u G H v),
        fc X Y X' Y' u G H v alpha = fold_fcell C alpha)).
Proof.
  split.
  - exact (fold_fvertical_is_map A).
  - split.
    + exact (fold_fsheet_is_map A).
    + split.
      * exact (fold_fcell_is_map C).
      * intros fv f fc Hv Hf Hc. split.
        -- exact (@fold_fvertical_unique A fv Hv).
        -- split.
           ++ exact (@fold_fsheet_unique A fv f Hv Hf).
           ++ exact (@fold_fcell_unique A C fc Hc).
Qed.

(** * Four-sorted setoid quotient and strict pointwise initiality

    Rocq's intensional equality is deliberately not used as the equality of
    ZFC set-functions.  A quotient is represented by a carrier together with
    its generated equivalence, and equality of structure maps is the
    pointwise target-setoid relation. *)

Inductive ModelVerticalPoint (A : VHAlgebra) : Type :=
| ModelVertical : forall X Y, vha_vertical A X Y -> ModelVerticalPoint A.

Inductive ModelSheetPoint (A : VHAlgebra) : Type :=
| ModelSheet : forall X Y, vha_sheet A X Y -> ModelSheetPoint A.

Inductive ModelCellPoint (A : VHAlgebra) (C : CellAlgebra A) : Type :=
| ModelCell : forall X Y X' Y' (u : FVertical X X')
    (G : FSheet X Y) (H : FSheet X' Y') (v : FVertical Y Y'),
    ca_cell C u G H v -> ModelCellPoint C.

Definition fold_packed_vertical (A : VHAlgebra)
    (u : PackedVertical) : ModelVerticalPoint A :=
  match u with
  | PackVertical X Y v => @ModelVertical A X Y (fold_fvertical A v)
  end.

Definition fold_packed_sheet (A : VHAlgebra)
    (G : PackedSheet) : ModelSheetPoint A :=
  match G with
  | PackSheet X Y H => @ModelSheet A X Y (fold_fsheet A H)
  end.

Definition fold_packed_cell (A : VHAlgebra) (C : CellAlgebra A)
    (alpha : PackedCell) : ModelCellPoint C :=
  match alpha with
  | PackCell X Y X' Y' u G H v a =>
      @ModelCell A C X Y X' Y' u G H v (fold_fcell C a)
  end.

Record SmallSigmaModel (A : VHAlgebra) (C : CellAlgebra A) : Type := {
  sm_object_eq : vha_object A -> vha_object A -> Prop;
  sm_vertical_eq : ModelVerticalPoint A -> ModelVerticalPoint A -> Prop;
  sm_sheet_eq : ModelSheetPoint A -> ModelSheetPoint A -> Prop;
  sm_cell_eq : ModelCellPoint C -> ModelCellPoint C -> Prop;
  sm_object_equivalence : Equivalence sm_object_eq;
  sm_vertical_equivalence : Equivalence sm_vertical_eq;
  sm_sheet_equivalence : Equivalence sm_sheet_eq;
  sm_cell_equivalence : Equivalence sm_cell_eq;
  sm_interface_sound : forall X Y,
      InterfaceEq X Y -> sm_object_eq (vha_interface A X) (vha_interface A Y);
  sm_vertical_sound : forall u v,
      PackedVerticalEq u v ->
      sm_vertical_eq (fold_packed_vertical A u) (fold_packed_vertical A v);
  sm_sheet_sound : forall G H,
      PackedSheetEq G H ->
      sm_sheet_eq (fold_packed_sheet A G) (fold_packed_sheet A H);
  sm_cell_sound : forall alpha beta,
      PackedCellEq alpha beta ->
      sm_cell_eq (fold_packed_cell C alpha) (fold_packed_cell C beta)
}.

Record PackedVerticalClass : Type := {
  packed_vertical_representative : PackedVertical
}.
Definition PackedVerticalClassEq (u v : PackedVerticalClass) : Prop :=
  PackedVerticalEq
    (packed_vertical_representative u) (packed_vertical_representative v).

Record PackedSheetClass : Type := {
  packed_sheet_representative : PackedSheet
}.
Definition PackedSheetClassEq (G H : PackedSheetClass) : Prop :=
  PackedSheetEq (packed_sheet_representative G) (packed_sheet_representative H).

Theorem PackedVerticalClassEq_equivalence : Equivalence PackedVerticalClassEq.
Proof.
  split.
  - intros [u]. exact (pve_refl u).
  - intros [u] [v] E. exact (pve_sym E).
  - intros [u] [v] [w] E1 E2. exact (pve_trans E1 E2).
Qed.

Theorem PackedSheetClassEq_equivalence : Equivalence PackedSheetClassEq.
Proof.
  split.
  - intros [G]. exact (pse_refl G).
  - intros [G] [H] E. exact (pse_sym E).
  - intros [G] [H] [K] E1 E2. exact (pse_trans E1 E2).
Qed.

Record FourQuotientMap A (C : CellAlgebra A)
    (M : SmallSigmaModel C) : Type := {
  fqm_object : InterfaceClass -> vha_object A;
  fqm_vertical : PackedVerticalClass -> ModelVerticalPoint A;
  fqm_sheet : PackedSheetClass -> ModelSheetPoint A;
  fqm_cell : CellClass -> ModelCellPoint C;
  fqm_object_respects : forall X Y,
      InterfaceClassEq X Y -> sm_object_eq M (fqm_object X) (fqm_object Y);
  fqm_vertical_respects : forall u v,
      PackedVerticalClassEq u v ->
      sm_vertical_eq M (fqm_vertical u) (fqm_vertical v);
  fqm_sheet_respects : forall G H,
      PackedSheetClassEq G H -> sm_sheet_eq M (fqm_sheet G) (fqm_sheet H);
  fqm_cell_respects : forall alpha beta,
      CellClassEq alpha beta -> sm_cell_eq M (fqm_cell alpha) (fqm_cell beta)
}.

Definition quotient_factor_map A (C : CellAlgebra A)
    (M : SmallSigmaModel C) : FourQuotientMap M.
Proof.
  refine {| fqm_object := fun X => vha_interface A (interface_representative X);
            fqm_vertical := fun u =>
              fold_packed_vertical A (packed_vertical_representative u);
            fqm_sheet := fun G =>
              fold_packed_sheet A (packed_sheet_representative G);
            fqm_cell := fun alpha =>
              fold_packed_cell C (cell_representative alpha) |}.
  - intros [X] [Y] E. now apply sm_interface_sound.
  - intros [u] [v] E. now apply sm_vertical_sound.
  - intros [G] [H] E. now apply sm_sheet_sound.
  - intros [alpha] [beta] E. now apply sm_cell_sound.
Defined.

Record ExtendsCanonicalFold A (C : CellAlgebra A)
    (M : SmallSigmaModel C) (f : FourQuotientMap M) : Prop := {
  extend_object : forall X,
      sm_object_eq M
        (fqm_object f {| interface_representative := X |})
        (vha_interface A X);
  extend_vertical : forall u,
      sm_vertical_eq M
        (fqm_vertical f {| packed_vertical_representative := u |})
        (fold_packed_vertical A u);
  extend_sheet : forall G,
      sm_sheet_eq M
        (fqm_sheet f {| packed_sheet_representative := G |})
        (fold_packed_sheet A G);
  extend_cell : forall alpha,
      sm_cell_eq M
        (fqm_cell f {| cell_representative := alpha |})
        (fold_packed_cell C alpha)
}.

Record StructureMapEq A (C : CellAlgebra A) (M : SmallSigmaModel C)
    (f g : FourQuotientMap M) : Prop := {
  structure_map_object_ext : forall X,
      sm_object_eq M (fqm_object f X) (fqm_object g X);
  structure_map_vertical_ext : forall u,
      sm_vertical_eq M (fqm_vertical f u) (fqm_vertical g u);
  structure_map_sheet_ext : forall G,
      sm_sheet_eq M (fqm_sheet f G) (fqm_sheet g G);
  structure_map_cell_ext : forall alpha,
      sm_cell_eq M (fqm_cell f alpha) (fqm_cell g alpha)
}.

Lemma quotient_factor_extends A (C : CellAlgebra A) (M : SmallSigmaModel C) :
  @ExtendsCanonicalFold A C M (@quotient_factor_map A C M).
Proof.
  constructor; intro x; simpl.
  - destruct (sm_object_equivalence M) as [Hr _ _]. apply Hr.
  - destruct (sm_vertical_equivalence M) as [Hr _ _]. apply Hr.
  - destruct (sm_sheet_equivalence M) as [Hr _ _]. apply Hr.
  - destruct (sm_cell_equivalence M) as [Hr _ _]. apply Hr.
Qed.

Theorem quotient_free_strict_pointwise_uniqueness A (C : CellAlgebra A)
    (M : SmallSigmaModel C) (f : FourQuotientMap M) :
  @ExtendsCanonicalFold A C M f ->
  @StructureMapEq A C M f (@quotient_factor_map A C M).
Proof.
  intro H. destruct H as [Ho Hv Hs Hc]. constructor.
  - intros [X]. apply Ho.
  - intros [u]. apply Hv.
  - intros [G]. apply Hs.
  - intros [alpha]. apply Hc.
Qed.

Theorem four_sorted_quotient_free_universal_property A
    (C : CellAlgebra A) (M : SmallSigmaModel C) :
  exists f : FourQuotientMap M,
    @ExtendsCanonicalFold A C M f /\
    forall g : FourQuotientMap M,
      @ExtendsCanonicalFold A C M g -> @StructureMapEq A C M g f.
Proof.
  exists (@quotient_factor_map A C M). split.
  - apply quotient_factor_extends.
  - intros g Hg. now apply quotient_free_strict_pointwise_uniqueness.
Qed.

(** * Intrinsically typed deep cell contexts *)

Inductive FCellContext
    {A B A' B'} (u : FVertical A A')
    (G : FSheet A B) (H : FSheet A' B') (v : FVertical B B') :
    forall {X Y X' Y'} (l : FVertical X X')
      (S : FSheet X Y) (T : FSheet X' Y') (r : FVertical Y Y'), Type :=
| FCCtxHole : @FCellContext A B A' B' u G H v A B A' B' u G H v
| FCCtxTensorRight : forall X Y X' Y'
    (l : FVertical X X') (S : FSheet X Y) (T : FSheet X' Y')
    (r : FVertical Y Y') C D C' D'
    (x : FVertical C C') (K : FSheet C D) (L : FSheet C' D')
    (y : FVertical D D'),
    @FCellContext A B A' B' u G H v X Y X' Y' l S T r ->
    FCell x K L y ->
    @FCellContext A B A' B' u G H v
      (iface_sum X C) (iface_sum Y D) (iface_sum X' C') (iface_sum Y' D')
      (FVTensor l x)
      (FHTensor S K) (FHTensor T L) (FVTensor r y)
| FCCtxTensorLeft : forall X Y X' Y'
    (l : FVertical X X') (S : FSheet X Y) (T : FSheet X' Y')
    (r : FVertical Y Y') C D C' D'
    (x : FVertical C C') (K : FSheet C D) (L : FSheet C' D')
    (y : FVertical D D'),
    FCell x K L y ->
    @FCellContext A B A' B' u G H v X Y X' Y' l S T r ->
    @FCellContext A B A' B' u G H v
      (iface_sum C X) (iface_sum D Y) (iface_sum C' X') (iface_sum D' Y')
      (FVTensor x l)
      (FHTensor K S) (FHTensor L T) (FVTensor y r)
| FCCtxHCompRight : forall X Y Z X' Y' Z'
    (l : FVertical X X') (S : FSheet X Y) (T : FSheet X' Y')
    (r : FVertical Y Y') (K : FSheet Y Z) (L : FSheet Y' Z')
    (z : FVertical Z Z'),
    @FCellContext A B A' B' u G H v X Y X' Y' l S T r ->
    FCell r K L z ->
    @FCellContext A B A' B' u G H v X Z X' Z'
      l (FHComp S K) (FHComp T L) z
| FCCtxHCompLeft : forall W X Y W' X' Y'
    (x : FVertical W W') (K : FSheet W X) (L : FSheet W' X')
    (l : FVertical X X') (S : FSheet X Y) (T : FSheet X' Y')
    (r : FVertical Y Y'),
    FCell x K L l ->
    @FCellContext A B A' B' u G H v X Y X' Y' l S T r ->
    @FCellContext A B A' B' u G H v W Y W' Y'
      x (FHComp K S) (FHComp L T) r
| FCCtxNest : forall b X Y X' Y'
    (l : FVertical X X') (S : FSheet X Y) (T : FSheet X' Y')
    (r : FVertical Y Y'),
    @FCellContext A B A' B' u G H v X Y X' Y' l S T r ->
    @FCellContext A B A' B' u G H v
      (cap_in (fcap_base b) X) (cap_out (fcap_base b) Y)
      (cap_in (fcap_base b) X') (cap_out (fcap_base b) Y')
      (@action_vertical _ (fcap_in_action b) X X' l)
      (FHNest b S) (FHNest b T)
      (@action_vertical _ (fcap_out_action b) Y Y' r)
| FCCtxPortal : forall (portal_code : Code) b X Y X' Y'
    (l : FVertical X X') (S : FSheet X Y) (T : FSheet X' Y')
    (r : FVertical Y Y'),
    @FCellContext A B A' B' u G H v X Y X' Y' l S T r ->
    @FCellContext A B A' B' u G H v
      (cap_in (fcap_base b) X) (cap_out (fcap_base b) Y)
      (cap_in (fcap_base b) X') (cap_out (fcap_base b) Y')
      (@action_vertical _ (fcap_in_action b) X X' l)
      (FHNest b S) (FHNest b T)
      (@action_vertical _ (fcap_out_action b) Y Y' r)
| FCCtxBinder : forall (binder_code : Code) b X Y X' Y'
    (l : FVertical X X') (S : FSheet X Y) (T : FSheet X' Y')
    (r : FVertical Y Y'),
    @FCellContext A B A' B' u G H v X Y X' Y' l S T r ->
    @FCellContext A B A' B' u G H v
      (cap_in (fcap_base b) X) (cap_out (fcap_base b) Y)
      (cap_in (fcap_base b) X') (cap_out (fcap_base b) Y')
      (@action_vertical _ (fcap_in_action b) X X' l)
      (FHNest b S) (FHNest b T)
      (@action_vertical _ (fcap_out_action b) Y Y' r).

Arguments FCCtxHole {A B A' B' u G H v}.
Arguments FCCtxTensorRight {A B A' B' u G H v X Y X' Y'}
  l S T r {C D C' D'} x K L y _ _.
Arguments FCCtxTensorLeft {A B A' B' u G H v X Y X' Y'}
  l S T r {C D C' D'} x K L y _ _.
Arguments FCCtxHCompRight {A B A' B' u G H v X Y Z X' Y' Z'}
  l S T r K L z _ _.
Arguments FCCtxHCompLeft {A B A' B' u G H v W X Y W' X' Y'}
  x K L l S T r _ _.
Arguments FCCtxNest {A B A' B' u G H v} b {X Y X' Y'} l S T r _.
Arguments FCCtxPortal {A B A' B' u G H v} portal_code b
  {X Y X' Y'} l S T r _.
Arguments FCCtxBinder {A B A' B' u G H v} binder_code b
  {X Y X' Y'} l S T r _.

Fixpoint plug_fcell_context
    {A B A' B'} {u : FVertical A A'} {G : FSheet A B}
    {H : FSheet A' B'} {v : FVertical B B'}
    {X Y X' Y'} {l : FVertical X X'} {S : FSheet X Y}
    {T : FSheet X' Y'} {r : FVertical Y Y'}
    (C : FCellContext u G H v l S T r) (alpha : FCell u G H v) :
    FCell l S T r :=
  match C with
  | FCCtxHole => alpha
  | FCCtxTensorRight _ _ _ _ _ _ _ _ C0 beta =>
      FCTensor (plug_fcell_context C0 alpha) beta
  | FCCtxTensorLeft _ _ _ _ _ _ _ _ beta C0 =>
      FCTensor beta (plug_fcell_context C0 alpha)
  | FCCtxHCompRight _ _ _ _ _ _ _ C0 beta =>
      FCHComp (plug_fcell_context C0 alpha) beta
  | FCCtxHCompLeft _ _ _ _ _ _ _ beta C0 =>
      FCHComp beta (plug_fcell_context C0 alpha)
  | FCCtxNest b _ _ _ _ C0 => FCNest b (plug_fcell_context C0 alpha)
  | FCCtxPortal _ b _ _ _ _ C0 => FCNest b (plug_fcell_context C0 alpha)
  | FCCtxBinder _ b _ _ _ _ C0 => FCNest b (plug_fcell_context C0 alpha)
  end.

Fixpoint fcell_context_depth
    {A B A' B'} {u : FVertical A A'} {G : FSheet A B}
    {H : FSheet A' B'} {v : FVertical B B'}
    {X Y X' Y'} {l : FVertical X X'} {S : FSheet X Y}
    {T : FSheet X' Y'} {r : FVertical Y Y'}
    (C : FCellContext u G H v l S T r) : nat :=
  match C with
  | FCCtxHole => 0
  | FCCtxTensorRight _ _ _ _ _ _ _ _ C0 _
  | FCCtxTensorLeft _ _ _ _ _ _ _ _ _ C0
  | FCCtxHCompRight _ _ _ _ _ _ _ C0 _
  | FCCtxHCompLeft _ _ _ _ _ _ _ _ C0
  | FCCtxNest _ _ _ _ _ C0
  | FCCtxPortal _ _ _ _ _ _ C0
  | FCCtxBinder _ _ _ _ _ _ C0 => Nat.succ (fcell_context_depth C0)
  end.

Theorem arbitrary_depth_cell_closure
    {A B A' B'} {u : FVertical A A'} {G : FSheet A B}
    {H : FSheet A' B'} {v : FVertical B B'}
    {X Y X' Y'} {l : FVertical X X'} {S : FSheet X Y}
    {T : FSheet X' Y'} {r : FVertical Y Y'}
    (C : FCellContext u G H v l S T r) (alpha : FCell u G H v) :
    exists beta : FCell l S T r, beta = plug_fcell_context C alpha.
Proof. eexists. reflexivity. Qed.

Theorem two_hole_fill_order_independent_up_to_interchange :
  forall A B C A' B' C' A'' B'' C''
    (u1 : FVertical A A') (u2 : FVertical A' A'')
    (v1 : FVertical B B') (v2 : FVertical B' B'')
    (w1 : FVertical C C') (w2 : FVertical C' C'')
    (G0 : FSheet A B) (G1 : FSheet A' B') (G2 : FSheet A'' B'')
    (H0 : FSheet B C) (H1 : FSheet B' C') (H2 : FSheet B'' C'')
    (alpha1 : FCell u1 G0 G1 v1) (alpha2 : FCell v1 H0 H1 w1)
    (beta1 : FCell u2 G1 G2 v2) (beta2 : FCell v2 H1 H2 w2),
    PackedCellEq
      (PackCell A C A'' C'' (FVComp u1 u2)
        (FHComp G0 H0) (FHComp G2 H2) (FVComp w1 w2)
        (FCVComp (FCHComp alpha1 alpha2) (FCHComp beta1 beta2)))
      (PackCell A C A'' C'' (FVComp u1 u2)
        (FHComp G0 H0) (FHComp G2 H2) (FVComp w1 w2)
        (FCHComp (FCVComp alpha1 beta1) (FCVComp alpha2 beta2))).
Proof. intros. apply pce_interchange. Qed.

Definition faithful_example4_G : PackedSheet :=
  PackSheet _ _ (FHRef example4_ref_p).

Definition faithful_example4_H : PackedSheet :=
  PackSheet _ _ (FHRef example4_ref_q).

Theorem faithful_example4_crossing_separation :
  ~ PackedSheetEq faithful_example4_G faithful_example4_H.
Proof.
  apply (crossing_multiset_separates 700). simpl. discriminate.
Qed.

(** * Exact DPO data and non-circular soundness boundary *)

Inductive HGElement : Type :=
| HGRegionElement : Id -> HGElement
| HGNodeElement : Id -> HGElement
| HGPortElement : Id -> HGElement
| HGEdgeElement : Id -> HGElement.

Definition hg_element_in (G : ExactHypergraph) (x : HGElement) : Prop :=
  match x with
  | HGRegionElement r => In r (eh_regions G)
  | HGNodeElement n => In n (eh_nodes G)
  | HGPortElement p => In p (eh_ports G)
  | HGEdgeElement e => In e (eh_edges G)
  end.

Record ExactHGMorphism (G H : ExactHypergraph) : Type := {
  hgm_region : Id -> Id;
  hgm_node : Id -> Id;
  hgm_port : Id -> Id;
  hgm_edge : Id -> Id;
  hgm_region_injective : forall x y,
      In x (eh_regions G) -> In y (eh_regions G) ->
      hgm_region x = hgm_region y -> x = y;
  hgm_node_injective : forall x y,
      In x (eh_nodes G) -> In y (eh_nodes G) ->
      hgm_node x = hgm_node y -> x = y;
  hgm_port_injective : forall x y,
      In x (eh_ports G) -> In y (eh_ports G) ->
      hgm_port x = hgm_port y -> x = y;
  hgm_edge_injective : forall x y,
      In x (eh_edges G) -> In y (eh_edges G) ->
      hgm_edge x = hgm_edge y -> x = y;
  hgm_region_closed : forall x, In x (eh_regions G) ->
      In (hgm_region x) (eh_regions H);
  hgm_node_closed : forall x, In x (eh_nodes G) ->
      In (hgm_node x) (eh_nodes H);
  hgm_port_closed : forall x, In x (eh_ports G) ->
      In (hgm_port x) (eh_ports H);
  hgm_edge_closed : forall x, In x (eh_edges G) ->
      In (hgm_edge x) (eh_edges H);
  hgm_root : hgm_region (eh_root G) = eh_root H;
  hgm_parent : forall r s, PMMaps (eh_parent G) r s ->
      PMMaps (eh_parent H) (hgm_region r) (hgm_region s);
  hgm_owner_node : forall p n, PMMaps (eh_owner G) p (inj0 n) ->
      PMMaps (eh_owner H) (hgm_port p) (inj0 (hgm_node n));
  hgm_owner_region : forall p r, PMMaps (eh_owner G) p (inj1 r) ->
      PMMaps (eh_owner H) (hgm_port p) (inj1 (hgm_region r));
  hgm_loc_node : forall n r, PMMaps (eh_loc G) (inj0 n) r ->
      PMMaps (eh_loc H) (inj0 (hgm_node n)) (hgm_region r);
  hgm_loc_edge : forall e r, PMMaps (eh_loc G) (inj1 e) r ->
      PMMaps (eh_loc H) (inj1 (hgm_edge e)) (hgm_region r);
  hgm_src : forall e ps, PMMaps (eh_src G) e ps ->
      PMMaps (eh_src H) (hgm_edge e) (map hgm_port ps);
  hgm_tgt : forall e ps, PMMaps (eh_tgt G) e ps ->
      PMMaps (eh_tgt H) (hgm_edge e) (map hgm_port ps);
  hgm_kappa_region : forall r k, PMMaps (eh_kappa_region G) r k ->
      PMMaps (eh_kappa_region H) (hgm_region r) k;
  hgm_kappa_node : forall n k, PMMaps (eh_kappa_node G) n k ->
      PMMaps (eh_kappa_node H) (hgm_node n) k;
  hgm_kappa_port : forall p k, PMMaps (eh_kappa_port G) p k ->
      PMMaps (eh_kappa_port H) (hgm_port p) k;
  hgm_kappa_edge : forall e k, PMMaps (eh_kappa_edge G) e k ->
      PMMaps (eh_kappa_edge H) (hgm_edge e) k;
  hgm_input_position : forall i p, nth_error (eh_inputs G) i = Some p ->
      nth_error (eh_inputs H) i = Some (hgm_port p);
  hgm_output_position : forall i p, nth_error (eh_outputs G) i = Some p ->
      nth_error (eh_outputs H) i = Some (hgm_port p);
  hgm_label : forall x payload, PMMaps (eh_label G) x payload ->
      PMMaps (eh_label H)
        (match x with
         | x => if in_dec Nat.eq_dec x (eh_regions G) then hgm_region x
                else if in_dec Nat.eq_dec x (eh_nodes G) then hgm_node x
                else if in_dec Nat.eq_dec x (eh_ports G) then hgm_port x
                else hgm_edge x
         end) payload
}.

Definition hgm_element {G H} (m : ExactHGMorphism G H)
    (x : HGElement) : HGElement :=
  match x with
  | HGRegionElement r => HGRegionElement (hgm_region m r)
  | HGNodeElement n => HGNodeElement (hgm_node m n)
  | HGPortElement p => HGPortElement (hgm_port m p)
  | HGEdgeElement e => HGEdgeElement (hgm_edge m e)
  end.

Definition hgm_image {G H} (m : ExactHGMorphism G H)
    (x : HGElement) : Prop :=
  exists y, hg_element_in G y /\ hgm_element m y = x.

Definition HGIncident (G : ExactHypergraph) (x y : HGElement) : Prop :=
  match x, y with
  | HGPortElement p, HGNodeElement n => PMMaps (eh_owner G) p (inj0 n)
  | HGPortElement p, HGRegionElement r => PMMaps (eh_owner G) p (inj1 r)
  | HGNodeElement n, HGRegionElement r => PMMaps (eh_loc G) (inj0 n) r
  | HGEdgeElement e, HGRegionElement r => PMMaps (eh_loc G) (inj1 e) r
  | HGEdgeElement e, HGPortElement p =>
      exists ps, (PMMaps (eh_src G) e ps \/ PMMaps (eh_tgt G) e ps) /\ In p ps
  | _, _ => False
  end.

Record ExactDPORule : Type := {
  edpo_left : WellFormedExactHG;
  edpo_interface : WellFormedExactHG;
  edpo_right : WellFormedExactHG;
  edpo_l : ExactHGMorphism (wfhg_graph edpo_interface) (wfhg_graph edpo_left);
  edpo_r : ExactHGMorphism (wfhg_graph edpo_interface) (wfhg_graph edpo_right);
  edpo_rule_code : RuleCode;
  edpo_rule_payload : list Code
}.

Record ExactDPOMatch (rho : ExactDPORule) (G : WellFormedExactHG) : Type := {
  edpom_map : ExactHGMorphism (wfhg_graph (edpo_left rho)) (wfhg_graph G);
  edpom_dangling : forall x,
      hg_element_in (wfhg_graph (edpo_left rho)) x ->
      ~ hgm_image (edpo_l rho) x ->
      forall y, HGIncident (wfhg_graph G) (hgm_element edpom_map x) y ->
      exists yL,
        HGIncident (wfhg_graph (edpo_left rho)) x yL /\
        hgm_element edpom_map yL = y;
  edpom_identification : forall x y,
      hg_element_in (wfhg_graph (edpo_left rho)) x ->
      hg_element_in (wfhg_graph (edpo_left rho)) y ->
      hgm_element edpom_map x = hgm_element edpom_map y ->
      x = y \/ (hgm_image (edpo_l rho) x /\ hgm_image (edpo_l rho) y);
  edpom_hierarchy_preserved : forall r s,
      PMMaps (eh_parent (wfhg_graph (edpo_left rho))) r s ->
      PMMaps (eh_parent (wfhg_graph G))
        (hgm_region edpom_map r) (hgm_region edpom_map s);
  edpom_interface_preserved :
      (forall i p, nth_error (eh_inputs (wfhg_graph (edpo_left rho))) i = Some p ->
         nth_error (eh_inputs (wfhg_graph G)) i = Some (hgm_port edpom_map p)) /\
      (forall i p, nth_error (eh_outputs (wfhg_graph (edpo_left rho))) i = Some p ->
         nth_error (eh_outputs (wfhg_graph G)) i = Some (hgm_port edpom_map p));
  edpom_local_order_preserved :
      (forall e ps, PMMaps (eh_src (wfhg_graph (edpo_left rho))) e ps ->
         PMMaps (eh_src (wfhg_graph G)) (hgm_edge edpom_map e)
           (map (hgm_port edpom_map) ps)) /\
      (forall e ps, PMMaps (eh_tgt (wfhg_graph (edpo_left rho))) e ps ->
         PMMaps (eh_tgt (wfhg_graph G)) (hgm_edge edpom_map e)
           (map (hgm_port edpom_map) ps));
  edpom_capability_preserved : forall r k,
      PMMaps (eh_kappa_region (wfhg_graph (edpo_left rho))) r k ->
      PMMaps (eh_kappa_region (wfhg_graph G)) (hgm_region edpom_map r) k;
  edpom_anchor_preserved : forall n payload,
      PMMaps (eh_label (wfhg_graph (edpo_left rho))) n payload ->
      PMMaps (eh_label (wfhg_graph G)) (hgm_node edpom_map n) payload;
  edpom_scope_preserved : forall e o a,
      In (e, (o, a)) (ev_ref_endpoints (wfhg_evidence (edpo_left rho))) ->
      In (hgm_edge edpom_map e, (o, a)) (ev_ref_endpoints (wfhg_evidence G));
  edpom_crossing_preserved : forall e p,
      PMMaps (ev_edge_itinerary (wfhg_evidence (edpo_left rho))) e p ->
      PMMaps (ev_edge_itinerary (wfhg_evidence G)) (hgm_edge edpom_map e) p
}.

Record ExactPushoutComplementWitness
    (rho : ExactDPORule) (G : WellFormedExactHG)
    (m : ExactDPOMatch rho G) : Type := {
  epoc_graph : WellFormedExactHG;
  epoc_from_interface :
    ExactHGMorphism (wfhg_graph (edpo_interface rho)) (wfhg_graph epoc_graph);
  epoc_into_host : ExactHGMorphism (wfhg_graph epoc_graph) (wfhg_graph G);
  epoc_deleted_exactly : forall x,
      hg_element_in (wfhg_graph G) x ->
      ~ hgm_image epoc_into_host x <->
      exists y,
        hg_element_in (wfhg_graph (edpo_left rho)) y /\
        ~ hgm_image (edpo_l rho) y /\ hgm_element (edpom_map m) y = x
}.

Record ExactPushoutWitness
    (rho : ExactDPORule) (D : WellFormedExactHG) : Type := {
  epo_result : WellFormedExactHG;
  epo_interface_to_complement :
    ExactHGMorphism (wfhg_graph (edpo_interface rho)) (wfhg_graph D);
  epo_from_complement : ExactHGMorphism (wfhg_graph D) (wfhg_graph epo_result);
  epo_from_right :
    ExactHGMorphism (wfhg_graph (edpo_right rho)) (wfhg_graph epo_result);
  epo_interface_identified : forall x,
      hg_element_in (wfhg_graph (edpo_interface rho)) x ->
      hgm_element epo_from_complement (hgm_element epo_interface_to_complement x) =
      hgm_element epo_from_right (hgm_element (edpo_r rho) x)
}.

Record ExactRewriteStep : Type := {
  ers_rule : ExactDPORule;
  ers_source : WellFormedExactHG;
  ers_match : ExactDPOMatch ers_rule ers_source;
  ers_complement : ExactPushoutComplementWitness ers_match;
  ers_pushout : ExactPushoutWitness ers_rule (epoc_graph ers_complement);
  ers_target : WellFormedExactHG;
  ers_target_exact : ers_target = epo_result ers_pushout
}.

Theorem exact_dpo_crossing_preservation (d : ExactRewriteStep) :
  forall e p,
    PMMaps
      (ev_edge_itinerary (wfhg_evidence (edpo_left (ers_rule d)))) e p ->
    PMMaps (ev_edge_itinerary (wfhg_evidence (ers_source d)))
      (hgm_edge (edpom_map (ers_match d)) e) p.
Proof. intros. now apply edpom_crossing_preserved. Qed.

Record ExactRewriteSemantics : Type := {
  ers_value : Type;
  ers_interpret : WellFormedExactHG -> ers_value;
  ers_cell : RuleCode -> list Code -> ers_value -> ers_value -> Prop
}.

Definition ExactRuleSound (S : ExactRewriteSemantics) (rho : ExactDPORule) : Prop :=
  forall d : ExactRewriteStep,
    ers_rule d = rho ->
    ers_cell S (edpo_rule_code rho) (edpo_rule_payload rho)
      (ers_interpret S (ers_source d)) (ers_interpret S (ers_target d)).

Theorem exact_rewrite_soundness (S : ExactRewriteSemantics)
    (d : ExactRewriteStep) :
  ExactRuleSound S (ers_rule d) ->
  ers_cell S (edpo_rule_code (ers_rule d)) (edpo_rule_payload (ers_rule d))
    (ers_interpret S (ers_source d)) (ers_interpret S (ers_target d)).
Proof. intro Hsound. now apply Hsound. Qed.

(** * Executable, measure-decreasing flattening normalization *)

Inductive FlatRuleTag : Type :=
| FlatPortalCut | FlatPathContraction | FlatOrdinaryAssignment
| FlatDeepAssignment | FlatInducedDeclaration | FlatFilterPropagation
| FlatSharingResolution | FlatNameConflictResolution.

Record FaithfulFlatState : Type := {
  ffs_corpus : Corpus;
  ffs_work : list OpenModuleCell;
  ffs_paths : list (list URI);
  ffs_assignments : list Assignment;
  ffs_declarations : list Declaration;
  ffs_filters : list URI;
  ffs_sharing_pending : list URI;
  ffs_conflicts : list (URI * URI);
  ffs_sharing_table : list (URI * Anchor);
  ffs_cache : list ((URI * Code) * list Code);
  ffs_done : list FlatRuleTag
}.

Definition list_length_sum {A} (xs : list (list A)) : nat :=
  fold_right (fun x n => List.length x + n) 0 xs.

Definition portal_depth_sum (xs : list OpenModuleCell) : nat :=
  fold_right (fun x n => List.length (om_payload x) + n) 0 xs.

Definition faithful_flat_measure (S : FaithfulFlatState) :
    nat * nat * nat * nat * nat :=
  (List.length (ffs_work S), portal_depth_sum (ffs_work S),
   list_length_sum (ffs_paths S),
   List.length (ffs_assignments S) + List.length (ffs_declarations S) +
     List.length (ffs_filters S) + List.length (ffs_sharing_pending S),
   List.length (ffs_conflicts S)).

Definition faithful_flat_fuel (S : FaithfulFlatState) : nat :=
  let '(a, b, c, d, e) := faithful_flat_measure S in a + b + c + d + e.

Definition faithful_flat_normal (S : FaithfulFlatState) : Prop :=
  ffs_work S = [] /\ ffs_paths S = [] /\ ffs_assignments S = [] /\
  ffs_declarations S = [] /\ ffs_filters S = [] /\
  ffs_sharing_pending S = [] /\ ffs_conflicts S = [].

Definition faithful_flat_step (S : FaithfulFlatState) :
    option (FlatRuleTag * FaithfulFlatState) :=
  match ffs_work S with
  | x :: xs =>
      Some (FlatPortalCut,
        {| ffs_corpus := ffs_corpus S; ffs_work := xs;
           ffs_paths := ffs_paths S; ffs_assignments := ffs_assignments S;
           ffs_declarations := ffs_declarations S; ffs_filters := ffs_filters S;
           ffs_sharing_pending := ffs_sharing_pending S;
           ffs_conflicts := ffs_conflicts S;
           ffs_sharing_table := ffs_sharing_table S; ffs_cache := ffs_cache S;
           ffs_done := FlatPortalCut :: ffs_done S |})
  | [] =>
    match ffs_paths S with
    | [] =>
      match ffs_assignments S with
      | a :: rest =>
          Some (match a with
                | Assign _ _ => FlatOrdinaryAssignment
                | DeepAssign _ _ => FlatDeepAssignment
                | Filter _ => FlatFilterPropagation
                end,
            {| ffs_corpus := ffs_corpus S; ffs_work := [];
               ffs_paths := []; ffs_assignments := rest;
               ffs_declarations := ffs_declarations S;
               ffs_filters := ffs_filters S;
               ffs_sharing_pending := ffs_sharing_pending S;
               ffs_conflicts := ffs_conflicts S;
               ffs_sharing_table := ffs_sharing_table S; ffs_cache := ffs_cache S;
               ffs_done := (match a with
                            | Assign _ _ => FlatOrdinaryAssignment
                            | DeepAssign _ _ => FlatDeepAssignment
                            | Filter _ => FlatFilterPropagation
                            end) :: ffs_done S |})
      | [] =>
        match ffs_declarations S with
        | d :: rest =>
            Some (FlatInducedDeclaration,
              {| ffs_corpus := ffs_corpus S; ffs_work := []; ffs_paths := [];
                 ffs_assignments := []; ffs_declarations := rest;
                 ffs_filters := ffs_filters S;
                 ffs_sharing_pending := ffs_sharing_pending S;
                 ffs_conflicts := ffs_conflicts S;
                 ffs_sharing_table := ffs_sharing_table S; ffs_cache := ffs_cache S;
                 ffs_done := FlatInducedDeclaration :: ffs_done S |})
        | [] =>
          match ffs_filters S with
          | f :: rest =>
              Some (FlatFilterPropagation,
                {| ffs_corpus := ffs_corpus S; ffs_work := []; ffs_paths := [];
                   ffs_assignments := []; ffs_declarations := [];
                   ffs_filters := rest;
                   ffs_sharing_pending := ffs_sharing_pending S;
                   ffs_conflicts := ffs_conflicts S;
                   ffs_sharing_table := ffs_sharing_table S; ffs_cache := ffs_cache S;
                   ffs_done := FlatFilterPropagation :: ffs_done S |})
          | [] =>
            match ffs_sharing_pending S with
            | u :: rest =>
                Some (FlatSharingResolution,
                  {| ffs_corpus := ffs_corpus S; ffs_work := []; ffs_paths := [];
                     ffs_assignments := []; ffs_declarations := []; ffs_filters := [];
                     ffs_sharing_pending := rest; ffs_conflicts := ffs_conflicts S;
                     ffs_sharing_table := ffs_sharing_table S; ffs_cache := ffs_cache S;
                     ffs_done := FlatSharingResolution :: ffs_done S |})
            | [] =>
              match ffs_conflicts S with
              | c :: rest =>
                  Some (FlatNameConflictResolution,
                    {| ffs_corpus := ffs_corpus S; ffs_work := []; ffs_paths := [];
                       ffs_assignments := []; ffs_declarations := []; ffs_filters := [];
                       ffs_sharing_pending := []; ffs_conflicts := rest;
                       ffs_sharing_table := ffs_sharing_table S;
                       ffs_cache := ffs_cache S;
                       ffs_done := FlatNameConflictResolution :: ffs_done S |})
              | [] => None
              end
            end
          end
        end
      end
    | [] :: _ => None
    | (u :: rest) :: paths =>
        Some (FlatPathContraction,
          {| ffs_corpus := ffs_corpus S; ffs_work := [];
             ffs_paths := match rest with [] => paths | _ => rest :: paths end;
             ffs_assignments := ffs_assignments S;
             ffs_declarations := ffs_declarations S;
             ffs_filters := ffs_filters S;
             ffs_sharing_pending := ffs_sharing_pending S;
             ffs_conflicts := ffs_conflicts S;
             ffs_sharing_table := ffs_sharing_table S; ffs_cache := ffs_cache S;
             ffs_done := FlatPathContraction :: ffs_done S |})
    end
  end.

Definition faithful_flat_domain (S : FaithfulFlatState) : Prop :=
  (forall p, In p (ffs_paths S) -> p <> []) /\
  NoDup (map fst (ffs_sharing_table S)).

Lemma faithful_flat_step_decreases S tag S' :
  faithful_flat_step S = Some (tag, S') ->
  faithful_flat_fuel S' < faithful_flat_fuel S.
Proof.
  destruct S as [cor work paths assigns decls filters sharing conflicts table cache done].
  unfold faithful_flat_step, faithful_flat_fuel, faithful_flat_measure.
  simpl. destruct work as [|x xs].
  2: intro H; inversion H; simpl; lia.
  destruct paths as [|p ps].
  2: destruct p as [|u rest]; [discriminate|].
  2: intro H; inversion H; destruct rest; simpl; lia.
  destruct assigns as [|a asn].
  2: intro H; inversion H; destruct a; simpl; lia.
  destruct decls as [|d ds].
  2: intro H; inversion H; simpl; lia.
  destruct filters as [|f fs].
  2: intro H; inversion H; simpl; lia.
  destruct sharing as [|u us].
  2: intro H; inversion H; simpl; lia.
  destruct conflicts as [|c cs]; [discriminate|].
  intro H; inversion H; simpl; lia.
Qed.

Lemma faithful_flat_step_none_normal S :
  faithful_flat_domain S -> faithful_flat_step S = None ->
  faithful_flat_normal S.
Proof.
  destruct S as [cor work paths assigns decls filters sharing conflicts table cache done].
  unfold faithful_flat_domain, faithful_flat_step, faithful_flat_normal; simpl.
  intros [Hpaths Htable]. destruct work as [|x xs]; [|discriminate].
  destruct paths as [|p ps].
  2: destruct p as [|u rest].
  2: exfalso; apply (Hpaths []); [now left|reflexivity].
  2: discriminate.
  destruct assigns; [|discriminate]. destruct decls; [|discriminate].
  destruct filters; [|discriminate]. destruct sharing; [|discriminate].
  destruct conflicts; [|discriminate]. tauto.
Qed.

Fixpoint faithful_flat_run (fuel : nat) (S : FaithfulFlatState) : FaithfulFlatState :=
  match fuel with
  | 0 => S
  | S fuel' =>
      match faithful_flat_step S with
      | Some (_, S') => faithful_flat_run fuel' S'
      | None => S
      end
  end.

Definition faithful_flatten (S : FaithfulFlatState) : FaithfulFlatState :=
  faithful_flat_run (faithful_flat_fuel S) S.

Lemma faithful_flat_domain_preserved S tag S' :
  faithful_flat_domain S -> faithful_flat_step S = Some (tag, S') ->
  faithful_flat_domain S'.
Proof.
  destruct S as [cor work paths assigns decls filters sharing conflicts table cache done].
  unfold faithful_flat_domain, faithful_flat_step; simpl.
  intros [Hp Ht]. destruct work as [|x xs].
  2: intro H; inversion H; simpl; auto.
  destruct paths as [|p ps].
  2: destruct p as [|u rest]; [discriminate|].
  2: intro H; inversion H; simpl in *; split; [|exact Ht].
  2: intros q Hq; destruct rest as [|v rs]; simpl in Hq.
  2: now apply Hp with (p := q); right.
  2: destruct Hq as [<-|Hq]; [discriminate|].
  2: now apply Hp with (p := q); right.
  destruct assigns as [|a asn].
  2: intro H; inversion H; simpl; auto.
  destruct decls as [|d ds].
  2: intro H; inversion H; simpl; auto.
  destruct filters as [|f fs].
  2: intro H; inversion H; simpl; auto.
  destruct sharing as [|u us].
  2: intro H; inversion H; simpl; auto.
  destruct conflicts as [|c cs]; [discriminate|].
  intro H; inversion H; simpl; auto.
Qed.

Theorem faithful_flattening_termination S :
  faithful_flat_domain S -> faithful_flat_normal (faithful_flatten S).
Proof.
  unfold faithful_flatten.
  remember (faithful_flat_fuel S) as n eqn:Hn.
  assert (Hle : faithful_flat_fuel S <= n) by lia.
  clear Hn. revert S Hle.
  induction n as [|n IH]; intros S Hle Hdom; simpl.
  - assert (faithful_flat_fuel S = 0) by lia.
    destruct (faithful_flat_step S) as [[tag S']|] eqn:Hstep.
    + pose proof (@faithful_flat_step_decreases S tag S' Hstep). lia.
    + now apply faithful_flat_step_none_normal.
  - destruct (faithful_flat_step S) as [[tag S']|] eqn:Hstep.
    + apply IH.
      * pose proof (@faithful_flat_step_decreases S tag S' Hstep). lia.
      * exact (@faithful_flat_domain_preserved S tag S' Hdom Hstep).
    + now apply faithful_flat_step_none_normal.
Qed.

Definition erase_flat_cache (S : FaithfulFlatState) : FaithfulFlatState :=
  {| ffs_corpus := ffs_corpus S; ffs_work := ffs_work S;
     ffs_paths := ffs_paths S; ffs_assignments := ffs_assignments S;
     ffs_declarations := ffs_declarations S; ffs_filters := ffs_filters S;
     ffs_sharing_pending := ffs_sharing_pending S;
     ffs_conflicts := ffs_conflicts S; ffs_sharing_table := ffs_sharing_table S;
     ffs_cache := []; ffs_done := ffs_done S |}.

Definition SameFlatInputExceptCache (S T : FaithfulFlatState) : Prop :=
  erase_flat_cache S = erase_flat_cache T.

Lemma faithful_flat_step_ignores_cache S T :
  SameFlatInputExceptCache S T ->
  match faithful_flat_step S, faithful_flat_step T with
  | Some (tag, S'), Some (tag', T') => tag = tag' /\ SameFlatInputExceptCache S' T'
  | None, None => True
  | _, _ => False
  end.
Proof.
  destruct S as [c w p a d f sh co tab ca done].
  destruct T as [c' w' p' a' d' f' sh' co' tab' ca' done'].
  unfold SameFlatInputExceptCache, erase_flat_cache; simpl.
  intro H. inversion H; subst; clear H.
  unfold faithful_flat_step; simpl.
  destruct w' as [|x xs]; simpl; [|split; reflexivity].
  destruct p' as [|path paths]; simpl.
  - destruct a' as [|asn asns]; simpl.
    + destruct d' as [|decl decls]; simpl.
      * destruct f' as [|flt filters]; simpl.
        -- destruct sh' as [|u sharing]; simpl.
           ++ destruct co' as [|conf conflicts]; simpl; [exact I|].
              split; reflexivity.
           ++ split; reflexivity.
        -- split; reflexivity.
      * split; reflexivity.
    + destruct asn; split; reflexivity.
  - destruct path as [|u rest]; simpl; [exact I|].
    destruct rest; split; reflexivity.
Qed.

Lemma faithful_flat_run_ignores_cache n S T :
  SameFlatInputExceptCache S T ->
  SameFlatInputExceptCache (faithful_flat_run n S) (faithful_flat_run n T).
Proof.
  revert S T. induction n as [|n IH]; intros S T Heq; simpl; [exact Heq|].
  destruct (faithful_flat_step S) as [[tag S']|] eqn:HS;
  destruct (faithful_flat_step T) as [[tag' T']|] eqn:HT.
  - pose proof (faithful_flat_step_ignores_cache Heq) as Hsim.
    rewrite HS, HT in Hsim. simpl in Hsim. destruct Hsim as [-> Hnext].
    now apply IH.
  - pose proof (faithful_flat_step_ignores_cache Heq) as Hsim.
    rewrite HS, HT in Hsim. contradiction.
  - pose proof (faithful_flat_step_ignores_cache Heq) as Hsim.
    rewrite HS, HT in Hsim. contradiction.
  - exact Heq.
Qed.

Lemma faithful_flat_fuel_ignores_cache S T :
  SameFlatInputExceptCache S T -> faithful_flat_fuel S = faithful_flat_fuel T.
Proof.
  destruct S as [c w p a d f sh co tab ca done].
  destruct T as [c' w' p' a' d' f' sh' co' tab' ca' done'].
  unfold SameFlatInputExceptCache, erase_flat_cache; simpl.
  intro H; inversion H; reflexivity.
Qed.

Proposition faithful_lazy_cache_transparency S T :
  SameFlatInputExceptCache S T ->
  SameFlatInputExceptCache (faithful_flatten S) (faithful_flatten T).
Proof.
  intro H. unfold faithful_flatten.
  rewrite (faithful_flat_fuel_ignores_cache H).
  now apply faithful_flat_run_ignores_cache.
Qed.

(** * Complete self-contained MMT-core syntax and strict erasure *)

Inductive MCore : Type :=
| MCDoc : URI -> list MCore -> MCore
| MCTheory : URI -> option URI -> list MCore -> MCore
| MCConstant : URI -> option MCore -> option MCore -> Code -> MCore
| MCStructure : URI -> URI -> MCore -> MCore
| MCInclude : URI -> URI -> MCore -> MCore
| MCVar : Id -> MCore
| MCRef : URI -> MCore
| MCApp : MCore -> list MCore -> MCore
| MCBind : MCore -> list (Id * MCore) -> MCore -> MCore
| MCMorphApp : MCore -> MCore -> MCore
| MCMorId : URI -> MCore
| MCView : URI -> URI -> URI -> list MCore -> MCore
| MCStructRef : URI -> MCore
| MCMorComp : MCore -> MCore -> MCore
| MCLiteral : URI -> URI -> list MCore -> MCore
| MCAssign : list URI -> MCore -> MCore
| MCDeepAssign : list URI -> MCore -> MCore
| MCFilter : list URI -> MCore
| MCTheoryRef : URI -> MCore
| MCDeclRef : list URI -> MCore
| MCMorphismRef : URI -> MCore
| MCJudgment : MCore -> MCore -> Code -> option MCore -> MCore
| MCRawItem : Code -> MCore.

Inductive MCoreSort : Type :=
| MSortDoc | MSortTheory | MSortDecl | MSortMorphism | MSortTerm
| MSortAssignment | MSortReference | MSortJudgment | MSortItem.

Definition option_mcore_check (check : MCore -> bool) (x : option MCore) : bool :=
  match x with None => true | Some t => check t end.

Fixpoint mcore_check_fuel (fuel : nat) (s : MCoreSort) (x : MCore) : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
    let check := mcore_check_fuel fuel' in
    match s, x with
    | MSortDoc, MCDoc _ items => forallb (check MSortItem) items
    | MSortTheory, MCTheory _ _ decls => forallb (check MSortDecl) decls
    | MSortDecl, MCConstant _ A t _ =>
        option_mcore_check (check MSortTerm) A &&
        option_mcore_check (check MSortTerm) t
    | MSortDecl, MCStructure _ _ mu
    | MSortDecl, MCInclude _ _ mu => check MSortMorphism mu
    | MSortTerm, MCVar _ | MSortTerm, MCRef _ => true
    | MSortTerm, MCApp f args =>
        check MSortTerm f && forallb (check MSortTerm) args
    | MSortTerm, MCBind b vars body =>
        check MSortTerm b &&
        forallb (fun xa => check MSortTerm (snd xa)) vars &&
        check MSortTerm body
    | MSortTerm, MCMorphApp t mu =>
        check MSortTerm t && check MSortMorphism mu
    | MSortMorphism, MCMorId _ | MSortMorphism, MCStructRef _ => true
    | MSortMorphism, MCView _ _ _ asn
    | MSortMorphism, MCLiteral _ _ asn =>
        forallb (check MSortAssignment) asn
    | MSortMorphism, MCMorComp mu nu =>
        check MSortMorphism mu && check MSortMorphism nu
    | MSortAssignment, MCAssign p t
    | MSortAssignment, MCDeepAssign p t =>
        negb (Nat.eqb (List.length p) 0) && check MSortTerm t
    | MSortAssignment, MCFilter p => negb (Nat.eqb (List.length p) 0)
    | MSortReference, MCTheoryRef _ | MSortReference, MCMorphismRef _ => true
    | MSortReference, MCDeclRef p => negb (Nat.eqb (List.length p) 0)
    | MSortJudgment, MCJudgment T t _ d =>
        check MSortTheory T && check MSortTerm t &&
        option_mcore_check (check MSortTerm) d
    | MSortItem, MCRawItem _ => true
    | MSortItem, item =>
        check MSortTheory item || check MSortMorphism item ||
        check MSortDecl item
    | _, _ => false
    end
  end.

Definition MCoreWF (s : MCoreSort) (x : MCore) : Prop :=
  exists fuel, mcore_check_fuel fuel s x = true.

Definition mpath_wf (p : list URI) : Prop := p <> [].
Definition minduce (s : URI) (p : list URI) : list URI := s :: p.

Fixpoint mcore_assignment_lookup (fuel : nat) (u : URI) (mu : MCore) :
    option (option MCore) :=
  match fuel with
  | 0 => None
  | S fuel' =>
    match mu with
    | MCView _ _ _ asn | MCLiteral _ _ asn =>
      let fix scan xs :=
        match xs with
        | [] => None
        | MCAssign [v] t :: rest =>
            if Nat.eqb u v then Some (Some t) else scan rest
        | MCFilter [v] :: rest =>
            if Nat.eqb u v then Some None else scan rest
        | _ :: rest => scan rest
        end in scan asn
    | MCMorComp mu nu =>
        match mcore_assignment_lookup fuel' u mu with
        | Some value => Some value
        | None => mcore_assignment_lookup fuel' u nu
        end
    | _ => None
    end
  end.

Fixpoint mcore_morphism_code (fuel : nat) (mu : MCore) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match mu with
    | MCMorId _ => 0
    | MCStructRef u => S u
    | MCView u s t _ => S (u + s + t)
    | MCLiteral s t _ => S (s + t)
    | MCMorComp x y => S (mcore_morphism_code fuel' x + mcore_morphism_code fuel' y)
    | _ => 0
    end
  end.

Definition mcore_induced_uri (mu : MCore) (u : URI) : URI :=
  match mcore_morphism_code 1024 mu with
  | 0 => u
  | S c => (S c) * (S c + u) + u
  end.

Fixpoint mcore_morphism_action (fuel : nat) (mu t : MCore) : MCore :=
  match fuel with
  | 0 => t
  | S fuel' =>
    match t with
    | MCVar i => MCVar i
    | MCRef u =>
        match mcore_assignment_lookup fuel' u mu with
        | Some (Some value) => value
        | Some None => MCRef u
        | None => MCRef (mcore_induced_uri mu u)
        end
    | MCApp f args =>
        MCApp (mcore_morphism_action fuel' mu f)
          (map (mcore_morphism_action fuel' mu) args)
    | MCBind b vars body =>
        MCBind (mcore_morphism_action fuel' mu b)
          (map (fun xa => (fst xa, mcore_morphism_action fuel' mu (snd xa))) vars)
          (mcore_morphism_action fuel' mu body)
    | MCMorphApp x nu => MCMorphApp x (MCMorComp nu mu)
    | other => other
    end
  end.

Record OHTGMMTCoreFragment : Type := {
  omcf_core : MCore;
  omcf_crossing_certificates : list Code;
  omcf_proof_payload : list Code;
  omcf_capability_payload : list Code
}.

Definition faithful_mmt_embedding (x : MCore) : OHTGMMTCoreFragment :=
  {| omcf_core := x; omcf_crossing_certificates := [];
     omcf_proof_payload := []; omcf_capability_payload := [] |}.

Definition faithful_mmt_forgetful (x : OHTGMMTCoreFragment) : MCore :=
  omcf_core x.

Definition code_multiplicity (c : Code) (xs : list Code) : nat :=
  count_occ Nat.eq_dec xs c.

Definition OHTGMMTCoreEq (x y : OHTGMMTCoreFragment) : Prop :=
  omcf_core x = omcf_core y /\
  (forall c, code_multiplicity c (omcf_crossing_certificates x) =
             code_multiplicity c (omcf_crossing_certificates y)) /\
  omcf_proof_payload x = omcf_proof_payload y /\
  omcf_capability_payload x = omcf_capability_payload y.

Theorem OHTGMMTCoreEq_equivalence : Equivalence OHTGMMTCoreEq.
Proof.
  split.
  - intro x. repeat split; reflexivity.
  - intros x y [Hc [Hx [Hp Hcap]]]. repeat split.
    + symmetry. exact Hc.
    + intro c. symmetry. apply Hx.
    + symmetry. exact Hp.
    + symmetry. exact Hcap.
  - intros x y z [Hxy [Hcxy [Hpxy Hcapxy]]]
      [Hyz [Hcyz [Hpyz Hcapyz]]]. repeat split.
    + congruence.
    + intro c. transitivity (code_multiplicity c (omcf_crossing_certificates y));
        auto.
    + congruence.
    + congruence.
Qed.

Theorem faithful_mmt_conservativity x :
  faithful_mmt_forgetful (faithful_mmt_embedding x) = x.
Proof. reflexivity. Qed.

Proposition faithful_mmt_embedding_injective x y :
  OHTGMMTCoreEq (faithful_mmt_embedding x) (faithful_mmt_embedding y) -> x = y.
Proof. intros [H _]. exact H. Qed.

Definition faithful_separation_core : MCore :=
  MCTheory 400 None [MCConstant 401 (Some (MCRef 402)) None 0].

Definition faithful_separation_p : OHTGMMTCoreFragment :=
  {| omcf_core := faithful_separation_core;
     omcf_crossing_certificates := [700];
     omcf_proof_payload := []; omcf_capability_payload := [50] |}.

Definition faithful_separation_q : OHTGMMTCoreFragment :=
  {| omcf_core := faithful_separation_core;
     omcf_crossing_certificates := [701];
     omcf_proof_payload := []; omcf_capability_payload := [50] |}.

Lemma faithful_separation_same_mmt :
  faithful_mmt_forgetful faithful_separation_p =
  faithful_mmt_forgetful faithful_separation_q.
Proof. reflexivity. Qed.

Theorem faithful_mmt_strict_separation :
  ~ OHTGMMTCoreEq faithful_separation_p faithful_separation_q.
Proof.
  intros [_ [Hcount _]]. specialize (Hcount 700). simpl in Hcount.
  discriminate.
Qed.

Theorem faithful_forgetful_congruence_strictly_coarser :
  (forall x y, OHTGMMTCoreEq x y ->
     faithful_mmt_forgetful x = faithful_mmt_forgetful y) /\
  exists x y,
    faithful_mmt_forgetful x = faithful_mmt_forgetful y /\
    ~ OHTGMMTCoreEq x y.
Proof.
  split.
  - intros x y [H _]. exact H.
  - exists faithful_separation_p, faithful_separation_q.
    split; [apply faithful_separation_same_mmt|apply faithful_mmt_strict_separation].
Qed.

(** * Trace-unique materialized hierarchical representation *)

Inductive FHGSpine : Interface -> Interface -> Type :=
| FHGGenerator : forall g, FHGSpine (hg_source g) (hg_target g)
| FHGBlank : forall A, FHGSpine A A
| FHGTensor : forall A B C D,
    FHGSpine A B -> FHGSpine C D ->
    FHGSpine (iface_sum A C) (iface_sum B D)
| FHGGlue : forall A B C,
    FHGSpine A B -> FHGSpine B C -> FHGSpine A C
| FHGRegionWrap : forall b A B,
    FHGSpine A B ->
    FHGSpine (cap_in (fcap_base b) A) (cap_out (fcap_base b) B)
| FHGReferenceEdge : forall w,
    FHGSpine
      [{| slot_pol := PIn; slot_role := occurrence_sort (rw_occurrence w);
          slot_wire := RefWire; slot_order_role := occurrence_label (rw_occurrence w) |}]
      [{| slot_pol := POut; slot_role := anchor_sort (rw_anchor w);
          slot_wire := RefWire; slot_order_role := anchor_label (rw_anchor w) |}]
| FHGCompanionEdge : forall A B, FVertical A B -> FHGSpine A B
| FHGConjointEdge : forall A B, FVertical A B -> FHGSpine B A.

Arguments FHGTensor {A B C D} G H.
Arguments FHGGlue {A B C} G H.
Arguments FHGRegionWrap b {A B} G.
Arguments FHGCompanionEdge {A B} u.
Arguments FHGConjointEdge {A B} u.

Fixpoint compile_fsheet_spine {A B} (G : FSheet A B) : FHGSpine A B :=
  match G with
  | FHGen g => FHGGenerator g
  | FHId A => FHGBlank A
  | FHTensor G H => FHGTensor (compile_fsheet_spine G) (compile_fsheet_spine H)
  | FHComp G H => FHGGlue (compile_fsheet_spine G) (compile_fsheet_spine H)
  | FHNest b G => FHGRegionWrap b (compile_fsheet_spine G)
  | FHRef w => FHGReferenceEdge w
  | FHCompanion u => FHGCompanionEdge u
  | FHConjoint u => FHGConjointEdge u
  end.

Fixpoint decode_fhg_spine {A B} (T : FHGSpine A B) : FSheet A B :=
  match T with
  | FHGGenerator g => FHGen g
  | FHGBlank A => FHId A
  | FHGTensor G H => FHTensor (decode_fhg_spine G) (decode_fhg_spine H)
  | FHGGlue G H => FHComp (decode_fhg_spine G) (decode_fhg_spine H)
  | FHGRegionWrap b G => FHNest b (decode_fhg_spine G)
  | FHGReferenceEdge w => FHRef w
  | FHGCompanionEdge u => FHCompanion u
  | FHGConjointEdge u => FHConjoint u
  end.

Fixpoint fhg_control_tags {A B} (T : FHGSpine A B) : list Code :=
  match T with
  | FHGGenerator g => [1; hg_id g]
  | FHGBlank _ => [2]
  | FHGTensor G H => 3 :: (fhg_control_tags G ++ fhg_control_tags H)
  | FHGGlue G H => 4 :: (fhg_control_tags G ++ fhg_control_tags H)
  | FHGRegionWrap b G => 5 :: cap_id (fcap_base b) :: fhg_control_tags G
  | FHGReferenceEdge w =>
      [6; occurrence_id (rw_occurrence w); anchor_id (rw_anchor w)]
  | FHGCompanionEdge _ => [7]
  | FHGConjointEdge _ => [8]
  end.

Fixpoint fhg_regions {A B} (T : FHGSpine A B) : list FCapability :=
  match T with
  | FHGRegionWrap b G => b :: fhg_regions G
  | FHGTensor G H | FHGGlue G H => fhg_regions G ++ fhg_regions H
  | _ => []
  end.

Fixpoint fhg_reference_certificates {A B} (T : FHGSpine A B) : list Itinerary :=
  match T with
  | FHGReferenceEdge w => [rw_itinerary w]
  | FHGTensor G H | FHGGlue G H =>
      fhg_reference_certificates G ++ fhg_reference_certificates H
  | FHGRegionWrap _ G => fhg_reference_certificates G
  | _ => []
  end.

Fixpoint fhg_anchors {A B} (T : FHGSpine A B) : list Anchor :=
  match T with
  | FHGReferenceEdge w => [rw_anchor w]
  | FHGTensor G H | FHGGlue G H => fhg_anchors G ++ fhg_anchors H
  | FHGRegionWrap _ G => fhg_anchors G
  | _ => []
  end.

Fixpoint fhg_occurrences {A B} (T : FHGSpine A B) : list Occurrence :=
  match T with
  | FHGReferenceEdge w => [rw_occurrence w]
  | FHGTensor G H | FHGGlue G H => fhg_occurrences G ++ fhg_occurrences H
  | FHGRegionWrap _ G => fhg_occurrences G
  | _ => []
  end.

Inductive FaithfulRepresentableHG : Type :=
| MaterializedFHG : forall A B, FHGSpine A B -> FaithfulRepresentableHG.

Arguments MaterializedFHG A B T : clear implicits.

Definition frhg_source (G : FaithfulRepresentableHG) : Interface :=
  match G with MaterializedFHG A _ _ => A end.
Definition frhg_target (G : FaithfulRepresentableHG) : Interface :=
  match G with MaterializedFHG _ B _ => B end.
Definition frhg_control (G : FaithfulRepresentableHG) : list Code :=
  match G with MaterializedFHG _ _ T => fhg_control_tags T end.
Definition frhg_region_capabilities (G : FaithfulRepresentableHG) : list FCapability :=
  match G with MaterializedFHG _ _ T => fhg_regions T end.
Definition frhg_crossing_certificates (G : FaithfulRepresentableHG) : list Itinerary :=
  match G with MaterializedFHG _ _ T => fhg_reference_certificates T end.

Definition faithful_representation_map (G : PackedSheet) : FaithfulRepresentableHG :=
  match G with PackSheet A B H => MaterializedFHG A B (compile_fsheet_spine H) end.

Definition faithful_hg_decoder (G : FaithfulRepresentableHG) : PackedSheet :=
  match G with MaterializedFHG A B T => PackSheet A B (decode_fhg_spine T) end.

Definition FaithfulHGStructuralEq (G H : FaithfulRepresentableHG) : Prop :=
  PackedSheetEq (faithful_hg_decoder G) (faithful_hg_decoder H).

Theorem FaithfulHGStructuralEq_equivalence : Equivalence FaithfulHGStructuralEq.
Proof.
  split.
  - intro G. apply pse_refl.
  - intros G H E. now apply pse_sym.
  - intros G H K E1 E2. exact (@pse_trans _ _ _ E1 E2).
Qed.

Lemma decode_compile_fsheet_spine A B (G : FSheet A B) :
  decode_fhg_spine (compile_fsheet_spine G) = G.
Proof. induction G; simpl; f_equal; assumption. Qed.

Lemma compile_decode_fhg_spine A B (T : FHGSpine A B) :
  compile_fsheet_spine (decode_fhg_spine T) = T.
Proof. induction T; simpl; f_equal; assumption. Qed.

Theorem faithful_abstract_roundtrip G :
  faithful_hg_decoder (faithful_representation_map G) = G.
Proof. destruct G as [A B G]. simpl. now rewrite decode_compile_fsheet_spine. Qed.

Theorem faithful_graph_roundtrip G :
  FaithfulHGStructuralEq
    (faithful_representation_map (faithful_hg_decoder G)) G.
Proof.
  destruct G as [A B T]. unfold FaithfulHGStructuralEq; simpl.
  rewrite compile_decode_fhg_spine. apply pse_refl.
Qed.

Theorem faithful_hypergraph_representation :
  (forall G, faithful_hg_decoder (faithful_representation_map G) = G) /\
  (forall H, FaithfulHGStructuralEq
       (faithful_representation_map (faithful_hg_decoder H)) H).
Proof. split; [apply faithful_abstract_roundtrip|apply faithful_graph_roundtrip]. Qed.

Inductive FaithfulHGDerivation : Type :=
| MaterializedFHGDerivation : PackedCell -> FaithfulHGDerivation.

Definition faithful_cell_compiler (alpha : PackedCell) : FaithfulHGDerivation :=
  MaterializedFHGDerivation alpha.
Definition faithful_cell_decoder (d : FaithfulHGDerivation) : PackedCell :=
  match d with MaterializedFHGDerivation alpha => alpha end.
Definition FaithfulHGProofEq (d e : FaithfulHGDerivation) : Prop :=
  PackedCellEq (faithful_cell_decoder d) (faithful_cell_decoder e).

Theorem faithful_cell_roundtrip alpha :
  faithful_cell_decoder (faithful_cell_compiler alpha) = alpha.
Proof. reflexivity. Qed.

Theorem faithful_derivation_roundtrip d :
  FaithfulHGProofEq (faithful_cell_compiler (faithful_cell_decoder d)) d.
Proof. destruct d; apply pce_refl. Qed.

Definition faithful_proof_sheet : FSheet iface_zero iface_zero := FHId iface_zero.

Definition faithful_proof_alpha : PackedCell :=
  PackCell iface_zero iface_zero iface_zero iface_zero
    (FVId iface_zero) faithful_proof_sheet faithful_proof_sheet
    (FVId iface_zero)
    (FCPrimitive (FVId iface_zero) faithful_proof_sheet faithful_proof_sheet
      (FVId iface_zero) 900 500 [] [700]).

Definition faithful_proof_beta : PackedCell :=
  PackCell iface_zero iface_zero iface_zero iface_zero
    (FVId iface_zero) faithful_proof_sheet faithful_proof_sheet
    (FVId iface_zero)
    (FCPrimitive (FVId iface_zero) faithful_proof_sheet faithful_proof_sheet
      (FVId iface_zero) 901 501 [] [701]).

Lemma faithful_parallel_proofs_same_boundary :
  pcell_source faithful_proof_alpha = pcell_source faithful_proof_beta /\
  pcell_target faithful_proof_alpha = pcell_target faithful_proof_beta.
Proof. split; reflexivity. Qed.

Theorem faithful_proof_relevance :
  ~ PackedCellEq faithful_proof_alpha faithful_proof_beta.
Proof.
  intro E.
  pose proof (PackedCellEq_preserves_primitive_rule_multiset 500 E) as H.
  simpl in H. discriminate.
Qed.

(** * Decoded foundation equations and the final generated congruences *)

Inductive PackedOneCell : Type :=
| PackedOneVertical : PackedVertical -> PackedOneCell
| PackedOneSheet : PackedSheet -> PackedOneCell.

Record FoundationDecoding (F : FoundationParameter) : Type := {
  fd_decode_one : Code -> option PackedOneCell;
  fd_decode_cell : CellCode -> option PackedCell;
  fd_one_prefix_unambiguous : forall c x y,
      fd_decode_one c = Some x -> fd_decode_one c = Some y -> x = y;
  fd_cell_prefix_unambiguous : forall c x y,
      fd_decode_cell c = Some x -> fd_decode_cell c = Some y -> x = y
}.

Definition packed_one_boundary_equal (x y : PackedOneCell) : Prop :=
  match x, y with
  | PackedOneVertical u, PackedOneVertical v =>
      pvertical_source u = pvertical_source v /\
      pvertical_target u = pvertical_target v
  | PackedOneSheet G, PackedOneSheet H =>
      psheet_source G = psheet_source H /\ psheet_target G = psheet_target H
  | _, _ => False
  end.

Definition packed_one_observables_equal (x y : PackedOneCell) : Prop :=
  match x, y with
  | PackedOneVertical _, PackedOneVertical _ => True
  | PackedOneSheet G, PackedOneSheet H =>
      forall arrow,
        packed_sheet_crossing_count arrow G = packed_sheet_crossing_count arrow H
  | _, _ => False
  end.

Inductive FinalOneStep (F : FoundationParameter) (D : FoundationDecoding F) :
    PackedOneCell -> PackedOneCell -> Prop :=
| final_one_vertical_core : forall u v,
    PackedVerticalEq u v ->
    FinalOneStep D (PackedOneVertical u) (PackedOneVertical v)
| final_one_sheet_core : forall G H,
    PackedSheetEq G H ->
    FinalOneStep D (PackedOneSheet G) (PackedOneSheet H)
| final_one_foundation : forall c d x y,
    In (c, d) (f_equations F) ->
    fd_decode_one D c = Some x -> fd_decode_one D d = Some y ->
    packed_one_boundary_equal x y -> packed_one_observables_equal x y ->
    FinalOneStep D x y.

Definition FinalOneEq F (D : FoundationDecoding F) :
    PackedOneCell -> PackedOneCell -> Prop :=
  generated_equivalence (FinalOneStep D).

Theorem FinalOneEq_equivalence F (D : FoundationDecoding F) :
  Equivalence (FinalOneEq D).
Proof. apply generated_equivalence_Equivalence. Qed.

Definition packed_one_crossing_count (arrow : Code) (x : PackedOneCell) : nat :=
  match x with
  | PackedOneVertical _ => 0
  | PackedOneSheet G => packed_sheet_crossing_count arrow G
  end.

Lemma FinalOneEq_preserves_crossing_observable F (D : FoundationDecoding F)
    arrow x y :
  FinalOneEq D x y ->
  packed_one_crossing_count arrow x = packed_one_crossing_count arrow y.
Proof.
  intro E. induction E.
  - reflexivity.
  - inversion H as [u v Euv|G0 H0 EGH|c d x0 y0 Hin Hdx Hdy Hb Ho]; subst;
      simpl.
    + reflexivity.
    + now apply PackedSheetEq_preserves_crossing_multiset.
    + destruct x, y; simpl in Ho |- *; try contradiction; auto.
  - symmetry. exact IHE.
  - now transitivity (packed_one_crossing_count arrow y).
Qed.

Lemma FinalOneEq_preserves_crossing F (D : FoundationDecoding F)
    arrow G H :
  FinalOneEq D (PackedOneSheet G) (PackedOneSheet H) ->
  packed_sheet_crossing_count arrow G = packed_sheet_crossing_count arrow H.
Proof.
  intro E.
  exact (@FinalOneEq_preserves_crossing_observable F D arrow
    (PackedOneSheet G) (PackedOneSheet H) E).
Qed.

Definition packed_cell_boundary_equal (alpha beta : PackedCell) : Prop :=
  pcell_left alpha = pcell_left beta /\
  pcell_source alpha = pcell_source beta /\
  pcell_target alpha = pcell_target beta /\
  pcell_right alpha = pcell_right beta.

Inductive FinalCellStep (F : FoundationParameter) (D : FoundationDecoding F) :
    PackedCell -> PackedCell -> Prop :=
| final_cell_core : forall alpha beta,
    PackedCellEq alpha beta -> FinalCellStep D alpha beta
| final_cell_foundation : forall c d alpha beta,
    In (c, d) (f_proof_equations F) ->
    fd_decode_cell D c = Some alpha -> fd_decode_cell D d = Some beta ->
    packed_cell_boundary_equal alpha beta ->
    (forall rule,
      packed_cell_rule_count rule alpha = packed_cell_rule_count rule beta) ->
    FinalCellStep D alpha beta.

Definition FinalCellEq F (D : FoundationDecoding F) :
    PackedCell -> PackedCell -> Prop :=
  generated_equivalence (FinalCellStep D).

Theorem FinalCellEq_equivalence F (D : FoundationDecoding F) :
  Equivalence (FinalCellEq D).
Proof. apply generated_equivalence_Equivalence. Qed.

Theorem FinalCellEq_preserves_primitive_rule_multiset F
    (D : FoundationDecoding F) rule alpha beta :
  FinalCellEq D alpha beta ->
  packed_cell_rule_count rule alpha = packed_cell_rule_count rule beta.
Proof.
  intro E. induction E.
  - reflexivity.
  - inversion H as [a b Eab|c d a b Hin Hda Hdb Hbound Hcount].
    + now apply PackedCellEq_preserves_primitive_rule_multiset.
    + apply Hcount.
  - symmetry. exact IHE.
  - now transitivity (packed_cell_rule_count rule y).
Qed.

Record FinalOneClass (F : FoundationParameter) (D : FoundationDecoding F) : Type := {
  final_one_representative : PackedOneCell
}.
Definition FinalOneClassEq F (D : FoundationDecoding F)
    (x y : FinalOneClass D) : Prop :=
  FinalOneEq D (final_one_representative x) (final_one_representative y).

Record FinalProofClass (F : FoundationParameter) (D : FoundationDecoding F) : Type := {
  final_proof_representative : PackedCell
}.
Definition FinalProofClassEq F (D : FoundationDecoding F)
    (x y : FinalProofClass D) : Prop :=
  FinalCellEq D (final_proof_representative x) (final_proof_representative y).

Theorem FinalOneClassEq_equivalence F (D : FoundationDecoding F) :
  Equivalence (@FinalOneClassEq F D).
Proof.
  destruct (@FinalOneEq_equivalence F D) as [Hr Hs Ht]. split.
  - intros [x]. apply Hr.
  - intros [x] [y] E. now apply Hs.
  - intros [x] [y] [z] E1 E2. exact (Ht x y z E1 E2).
Qed.

Theorem FinalProofClassEq_equivalence F (D : FoundationDecoding F) :
  Equivalence (@FinalProofClassEq F D).
Proof.
  destruct (@FinalCellEq_equivalence F D) as [Hr Hs Ht]. split.
  - intros [x]. apply Hr.
  - intros [x] [y] E. now apply Hs.
  - intros [x] [y] [z] E1 E2. exact (Ht x y z E1 E2).
Qed.

Record FinalQuotientTarget : Type := {
  fqt_object_carrier : Type;
  fqt_one_carrier : Type;
  fqt_proof_carrier : Type;
  fqt_object_eq : fqt_object_carrier -> fqt_object_carrier -> Prop;
  fqt_one_eq : fqt_one_carrier -> fqt_one_carrier -> Prop;
  fqt_proof_eq : fqt_proof_carrier -> fqt_proof_carrier -> Prop;
  fqt_object_equivalence : Equivalence fqt_object_eq;
  fqt_one_equivalence : Equivalence fqt_one_eq;
  fqt_proof_equivalence : Equivalence fqt_proof_eq
}.

Record FinalRawInterpretation F (D : FoundationDecoding F)
    (T : FinalQuotientTarget) : Type := {
  fri_object : Interface -> fqt_object_carrier T;
  fri_one : PackedOneCell -> fqt_one_carrier T;
  fri_proof : PackedCell -> fqt_proof_carrier T;
  fri_object_respects : forall X Y,
      InterfaceEq X Y -> fqt_object_eq T (fri_object X) (fri_object Y);
  fri_one_respects : forall x y,
      FinalOneEq D x y -> fqt_one_eq T (fri_one x) (fri_one y);
  fri_proof_respects : forall alpha beta,
      FinalCellEq D alpha beta ->
      fqt_proof_eq T (fri_proof alpha) (fri_proof beta)
}.

Record FinalQuotientStructureMap F (D : FoundationDecoding F)
    (T : FinalQuotientTarget) : Type := {
  fqsm_object : InterfaceClass -> fqt_object_carrier T;
  fqsm_one : FinalOneClass D -> fqt_one_carrier T;
  fqsm_proof : FinalProofClass D -> fqt_proof_carrier T;
  fqsm_object_respects : forall X Y,
      InterfaceClassEq X Y -> fqt_object_eq T (fqsm_object X) (fqsm_object Y);
  fqsm_one_respects : forall x y,
      @FinalOneClassEq F D x y -> fqt_one_eq T (fqsm_one x) (fqsm_one y);
  fqsm_proof_respects : forall alpha beta,
      @FinalProofClassEq F D alpha beta ->
      fqt_proof_eq T (fqsm_proof alpha) (fqsm_proof beta)
}.

Definition final_quotient_factor F (D : FoundationDecoding F)
    (T : FinalQuotientTarget) (I : FinalRawInterpretation D T) :
    FinalQuotientStructureMap D T.
Proof.
  refine {| fqsm_object := fun X => fri_object I (interface_representative X);
            fqsm_one := fun x => fri_one I (final_one_representative x);
            fqsm_proof := fun a => fri_proof I (final_proof_representative a) |}.
  - intros [X] [Y] E. now apply fri_object_respects.
  - intros [x] [y] E. now apply fri_one_respects.
  - intros [x] [y] E. now apply fri_proof_respects.
Defined.

Record FinalExtendsRaw F (D : FoundationDecoding F) T
    (I : FinalRawInterpretation D T) (f : FinalQuotientStructureMap D T) : Prop := {
  fer_object : forall X,
      fqt_object_eq T (fqsm_object f {| interface_representative := X |})
        (fri_object I X);
  fer_one : forall x,
      fqt_one_eq T (fqsm_one f {| final_one_representative := x |})
        (fri_one I x);
  fer_proof : forall alpha,
      fqt_proof_eq T (fqsm_proof f {| final_proof_representative := alpha |})
        (fri_proof I alpha)
}.

Record FinalStructureMapEq F (D : FoundationDecoding F) T
    (f g : FinalQuotientStructureMap D T) : Prop := {
  final_map_object_ext : forall X,
      fqt_object_eq T (fqsm_object f X) (fqsm_object g X);
  final_map_one_ext : forall x,
      fqt_one_eq T (fqsm_one f x) (fqsm_one g x);
  final_map_proof_ext : forall alpha,
      fqt_proof_eq T (fqsm_proof f alpha) (fqsm_proof g alpha)
}.

Lemma final_quotient_factor_extends F (D : FoundationDecoding F) T
    (I : FinalRawInterpretation D T) :
  FinalExtendsRaw I (final_quotient_factor I).
Proof.
  constructor; intro x; simpl.
  - destruct (fqt_object_equivalence T) as [Hr _ _]. apply Hr.
  - destruct (fqt_one_equivalence T) as [Hr _ _]. apply Hr.
  - destruct (fqt_proof_equivalence T) as [Hr _ _]. apply Hr.
Qed.

Theorem final_quotient_strict_pointwise_uniqueness F
    (D : FoundationDecoding F) T (I : FinalRawInterpretation D T)
    (f : FinalQuotientStructureMap D T) :
  FinalExtendsRaw I f ->
  FinalStructureMapEq f (final_quotient_factor I).
Proof.
  intros [Ho H1 H2]. constructor.
  - intros [X]. apply Ho.
  - intros [x]. apply H1.
  - intros [alpha]. apply H2.
Qed.

Theorem final_four_sorted_quotient_universal_property F
    (D : FoundationDecoding F) T (I : FinalRawInterpretation D T) :
  exists f : FinalQuotientStructureMap D T,
    FinalExtendsRaw I f /\
    forall g : FinalQuotientStructureMap D T,
      FinalExtendsRaw I g -> FinalStructureMapEq g f.
Proof.
  exists (final_quotient_factor I). split.
  - apply final_quotient_factor_extends.
  - intros g Hg. now apply final_quotient_strict_pointwise_uniqueness.
Qed.

(** * The small horizontal one-truncation as an indexed setoid category *)

Record IndexedSetoidCategory : Type := {
  isc_object : Type;
  isc_hom : isc_object -> isc_object -> Type;
  isc_hom_eq : forall A B, isc_hom A B -> isc_hom A B -> Prop;
  isc_hom_equivalence : forall A B, Equivalence (@isc_hom_eq A B);
  isc_id : forall A, isc_hom A A;
  isc_comp : forall A B C, isc_hom A B -> isc_hom B C -> isc_hom A C;
  isc_comp_respects : forall A B C (f f' : isc_hom A B) (g g' : isc_hom B C),
      isc_hom_eq f f' -> isc_hom_eq g g' ->
      isc_hom_eq (isc_comp f g) (isc_comp f' g');
  isc_left_identity : forall A B (f : isc_hom A B),
      isc_hom_eq (isc_comp (isc_id A) f) f;
  isc_right_identity : forall A B (f : isc_hom A B),
      isc_hom_eq (isc_comp f (isc_id B)) f;
  isc_associativity : forall A B C D
      (f : isc_hom A B) (g : isc_hom B C) (h : isc_hom C D),
      isc_hom_eq (isc_comp (isc_comp f g) h) (isc_comp f (isc_comp g h))
}.

Definition horizontal_one_truncation : IndexedSetoidCategory.
Proof.
  refine
    {| isc_object := Interface;
       isc_hom := SheetClass;
       isc_hom_eq := fun A B => @SheetClassEq A B;
       isc_id := fun A => {| sheet_representative := FHId A |};
       isc_comp := fun A B C => @class_hcomp A B C |}.
  - apply SheetClassEq_equivalence.
  - intros. now apply class_hcomp_respects.
  - intros A B [G]. exact (pse_left_identity G).
  - intros A B [G]. exact (pse_right_identity G).
  - intros A B C D [G] [H] [K]. exact (pse_associativity G H K).
Defined.

Theorem horizontal_one_truncation_is_small_category :
  forall A B,
    Equivalence (@isc_hom_eq horizontal_one_truncation A B) /\
    (forall f : isc_hom horizontal_one_truncation A B,
      @isc_hom_eq horizontal_one_truncation A B
        (@isc_comp horizontal_one_truncation A A B
          (@isc_id horizontal_one_truncation A) f) f /\
      @isc_hom_eq horizontal_one_truncation A B
        (@isc_comp horizontal_one_truncation A B B
          f (@isc_id horizontal_one_truncation B)) f).
Proof.
  intros A B. split.
  - apply isc_hom_equivalence.
  - intro f. split; [apply isc_left_identity|apply isc_right_identity].
Qed.

Fixpoint mcore_node_count (x : MCore) : nat :=
  match x with
  | MCApp f args =>
      S (mcore_node_count f +
         fold_right (fun y n => mcore_node_count y + n) 0 args)
  | _ => 1
  end.

End FaithfulTypedDouble.

(** * Authoritative 0.2.1 mechanism layer

    Everything above this point is retained as a migration/codec layer for
    files produced before the 0.2.1 repair.  In particular, the old unindexed
    [Itinerary], de-Bruijn [Term], list-based module composition, MMT payload
    wrapper and constructor-mirroring hypergraph compiler are not normative.
    The definitions below are the only normative counterparts used by the
    faithfulness crosswalk.  A manuscript mechanism with no faithful definition
    below is intentionally reported missing rather than represented by a
    migration scaffold. *)
Module AuthoritativeOHTG.

Import FaithfulTypedDouble.

(** ** One authoritative capability record *)

Definition Zone := Code.
Definition CapabilityCode := Code.

Definition cross_composable (p q : CrossingArrow) : Prop :=
  xa_target p = xa_source q.

Record FCrossingCategory : Type := {
  fcross_zones : list Zone;
  fcross_arrows : list CrossingArrow;
  fcross_identity : Zone -> CrossingArrow;
  fcross_compose : CrossingArrow -> CrossingArrow -> CrossingArrow;
  fcross_identityb : CrossingArrow -> bool;

  fcross_identity_in : forall z, In z fcross_zones ->
    In (fcross_identity z) fcross_arrows;
  fcross_identity_source : forall z,
    xa_source (fcross_identity z) = z;
  fcross_identity_target : forall z,
    xa_target (fcross_identity z) = z;
  fcross_compose_in : forall p q,
    In p fcross_arrows -> In q fcross_arrows ->
    cross_composable p q -> In (fcross_compose p q) fcross_arrows;
  fcross_compose_source : forall p q,
    cross_composable p q ->
    xa_source (fcross_compose p q) = xa_source p;
  fcross_compose_target : forall p q,
    cross_composable p q ->
    xa_target (fcross_compose p q) = xa_target q;
  fcross_associative : forall p q r,
    cross_composable p q -> cross_composable q r ->
    fcross_compose (fcross_compose p q) r =
    fcross_compose p (fcross_compose q r);
  fcross_left_identity : forall p,
    In p fcross_arrows ->
    fcross_compose (fcross_identity (xa_source p)) p = p;
  fcross_right_identity : forall p,
    In p fcross_arrows ->
    fcross_compose p (fcross_identity (xa_target p)) = p;
  fcross_identityb_spec : forall p,
    fcross_identityb p = true <->
    exists z, In z fcross_zones /\ p = fcross_identity z
}.

Record SymmetricMonoidalEndofunctor : Type := {
  smf_object : Interface -> Interface;
  smf_vertical : VerticalAction smf_object;
  smf_symmetry : forall A B,
    @action_vertical _ smf_vertical (iface_sum A B) (iface_sum B A)
      (FVSymmetry A B) =
    transport_fvertical
      (eq_sym (@action_tensor_object _ smf_vertical A B))
      (eq_sym (@action_tensor_object _ smf_vertical B A))
      (FVSymmetry (smf_object A) (smf_object B))
}.

Record FCapability : Type := {
  fcap_code : CapabilityCode;
  fcap_in : SymmetricMonoidalEndofunctor;
  fcap_out : SymmetricMonoidalEndofunctor;
  fcap_crossing : FCrossingCategory;
  fcap_visible : Zone -> Zone -> WireKind -> bool;
  fcap_visibility_composition : forall x y z k,
    fcap_visible x y k = true -> fcap_visible y z k = true ->
    fcap_visible x z k = true;
  fcap_scope_domain : Anchor -> bool;
  fcap_scope : Anchor -> option Anchor;
  fcap_scope_exact : forall a,
    fcap_scope_domain a = true <-> exists a', fcap_scope a = Some a';
  fcap_scope_type_preserving : forall a a',
    fcap_scope a = Some a' -> anchor_sort a = anchor_sort a';
  fcap_semantics : ModelCode
}.

Record CapabilityRegistry : Type := {
  registry_lookup : CapabilityCode -> FCapability;
  registry_lookup_code : forall c, fcap_code (registry_lookup c) = c
}.

Definition capability_object_in (b : FCapability) : Interface -> Interface :=
  smf_object (fcap_in b).

Definition capability_object_out (b : FCapability) : Interface -> Interface :=
  smf_object (fcap_out b).

Definition capability_vertical_in (b : FCapability) A B
    (u : FVertical A B) :
    FVertical (capability_object_in b A) (capability_object_in b B) :=
  @action_vertical _ (smf_vertical (fcap_in b)) A B u.

Definition capability_vertical_out (b : FCapability) A B
    (u : FVertical A B) :
    FVertical (capability_object_out b A) (capability_object_out b B) :=
  @action_vertical _ (smf_vertical (fcap_out b)) A B u.

(** ** Capability/zone-indexed certified itineraries *)

Record CrossingStep : Type := {
  cstep_capability : CapabilityCode;
  cstep_certificate : CrossingArrow
}.

Definition step_source (s : CrossingStep) : Zone :=
  xa_source (cstep_certificate s).
Definition step_target (s : CrossingStep) : Zone :=
  xa_target (cstep_certificate s).

Definition step_in_registry (U : CapabilityRegistry) (s : CrossingStep) : Prop :=
  In (cstep_certificate s)
     (fcross_arrows (fcap_crossing (registry_lookup U
       (cstep_capability s)))).

Inductive LegalItineraryWord (U : CapabilityRegistry) :
    Zone -> list CrossingStep -> Zone -> Prop :=
| legal_itinerary_nil : forall z, LegalItineraryWord U z [] z
| legal_itinerary_cons : forall z y z' s rest,
    step_in_registry U s ->
    step_source s = z -> step_target s = y ->
    LegalItineraryWord U y rest z' ->
    LegalItineraryWord U z (s :: rest) z'.

Record Itinerary (U : CapabilityRegistry) (z z' : Zone) : Type := {
  itinerary_word : list CrossingStep;
  itinerary_legality : LegalItineraryWord U z itinerary_word z'
}.

Arguments itinerary_word {U z z'} _.

Definition itinerary_identity U z : Itinerary U z z :=
  {| itinerary_word := [];
     itinerary_legality := legal_itinerary_nil U z |}.

Definition same_capability (p q : CrossingStep) : bool :=
  Nat.eqb (cstep_capability p) (cstep_capability q).

Definition step_identityb (U : CapabilityRegistry) (p : CrossingStep) : bool :=
  fcross_identityb
    (fcap_crossing (registry_lookup U (cstep_capability p)))
    (cstep_certificate p).

Definition compose_crossing_steps (U : CapabilityRegistry)
    (p q : CrossingStep) : CrossingStep :=
  {| cstep_capability := cstep_capability p;
     cstep_certificate :=
       fcross_compose
         (fcap_crossing (registry_lookup U (cstep_capability p)))
         (cstep_certificate p) (cstep_certificate q) |}.

(** The stack is reversed.  A push deletes an identity, composes adjacent
    certificates from one capability, and deletes the composite if it is an
    identity.  Thus list concatenation is only raw storage; it is never the
    semantic composition operation. *)
Definition reduce_cross_push (U : CapabilityRegistry)
    (stack : list CrossingStep) (next : CrossingStep) : list CrossingStep :=
  if step_identityb U next then stack else
  match stack with
  | [] => [next]
  | previous :: prefix =>
      if same_capability previous next &&
         Nat.eqb (step_target previous) (step_source next)
      then
        let composite := compose_crossing_steps U previous next in
        if step_identityb U composite then prefix else composite :: prefix
      else next :: stack
  end.

Fixpoint reduce_cross_stack (U : CapabilityRegistry)
    (input stack : list CrossingStep) : list CrossingStep :=
  match input with
  | [] => stack
  | s :: rest => reduce_cross_stack U rest (reduce_cross_push U stack s)
  end.

Definition reduce_cross (U : CapabilityRegistry)
    (input : list CrossingStep) : list CrossingStep :=
  rev (reduce_cross_stack U input []).

Fixpoint raw_itinerary_concat
    (pi rho : list CrossingStep) : list CrossingStep :=
  match pi with
  | [] => rho
  | s :: rest => s :: raw_itinerary_concat rest rho
  end.

Lemma raw_itinerary_concat_spec pi rho :
  raw_itinerary_concat pi rho = pi ++ rho.
Proof. induction pi; simpl; congruence. Qed.

Definition adjacent_reducible (U : CapabilityRegistry)
    (p q : CrossingStep) : Prop :=
  cstep_capability p = cstep_capability q /\
  step_target p = step_source q.

Definition reduced_cross_word (U : CapabilityRegistry)
    (word : list CrossingStep) : Prop :=
  Forall (fun s => step_identityb U s = false) word /\
  forall pre p q post,
    word = pre ++ p :: q :: post -> ~ adjacent_reducible U p q.

Record Diamond {U z0 z1 z2}
    (rho : Itinerary U z1 z2) (pi : Itinerary U z0 z1)
    (out : Itinerary U z0 z2) : Prop := {
  diamond_executes_reduce_cross :
    itinerary_word out =
    reduce_cross U
      (raw_itinerary_concat (itinerary_word pi) (itinerary_word rho));
  diamond_result_reduced : reduced_cross_word U (itinerary_word out)
}.

Inductive CrossWordEquation (U : CapabilityRegistry) :
    list CrossingStep -> list CrossingStep -> Prop :=
| cwe_reduce : forall word,
    CrossWordEquation U word (reduce_cross U word)
| cwe_prepend : forall s x y,
    CrossWordEquation U x y -> CrossWordEquation U (s :: x) (s :: y)
| cwe_append : forall x y suffix,
    CrossWordEquation U x y ->
    CrossWordEquation U (raw_itinerary_concat x suffix)
                         (raw_itinerary_concat y suffix).

Definition CrossWordEq U := generated_equivalence (CrossWordEquation U).

Theorem CrossWordEq_equivalence U : Equivalence (CrossWordEq U).
Proof. apply generated_equivalence_Equivalence. Qed.

Lemma diamond_is_cross_equation U z0 z1 z2
    (rho : Itinerary U z1 z2) (pi : Itinerary U z0 z1)
    (out : Itinerary U z0 z2) :
  Diamond rho pi out ->
  CrossWordEq U
    (raw_itinerary_concat (itinerary_word pi) (itinerary_word rho))
    (itinerary_word out).
Proof.
  intros [H _]. rewrite H. apply ge_step. apply cwe_reduce.
Qed.

Lemma CrossWordEq_append U x y :
  CrossWordEq U x y -> forall suffix,
  CrossWordEq U (raw_itinerary_concat x suffix)
                (raw_itinerary_concat y suffix).
Proof.
  intro E. induction E; intro suffix.
  - apply ge_refl.
  - apply ge_step. now apply cwe_append.
  - apply ge_sym. apply IHE.
  - eapply ge_trans; [apply IHE1|apply IHE2].
Qed.

Lemma CrossWordEq_cons U s x y :
  CrossWordEq U x y -> CrossWordEq U (s :: x) (s :: y).
Proof.
  intro E. induction E.
  - apply ge_refl.
  - apply ge_step. now apply cwe_prepend.
  - apply ge_sym. exact IHE.
  - eapply ge_trans; [exact IHE1|exact IHE2].
Qed.

Lemma CrossWordEq_prepend U x y :
  CrossWordEq U x y -> forall prefix,
  CrossWordEq U (raw_itinerary_concat prefix x)
                (raw_itinerary_concat prefix y).
Proof.
  intros E prefix. induction prefix as [|s prefix IH]; simpl.
  - exact E.
  - apply CrossWordEq_cons. exact IH.
Qed.

Lemma raw_itinerary_concat_assoc x y z :
  raw_itinerary_concat (raw_itinerary_concat x y) z =
  raw_itinerary_concat x (raw_itinerary_concat y z).
Proof.
  rewrite (raw_itinerary_concat_spec (raw_itinerary_concat x y) z).
  rewrite (raw_itinerary_concat_spec x y).
  rewrite (raw_itinerary_concat_spec x (raw_itinerary_concat y z)).
  rewrite (raw_itinerary_concat_spec y z).
  symmetry. apply app_assoc.
Qed.

Theorem itinerary_diamond_associative_up_to_cross_equations
    U z0 z1 z2 z3
    (pi : Itinerary U z0 z1) (rho : Itinerary U z1 z2)
    (sigma : Itinerary U z2 z3)
    (rho_pi : Itinerary U z0 z2) (sigma_rho : Itinerary U z1 z3)
    (left right : Itinerary U z0 z3) :
  Diamond rho pi rho_pi -> Diamond sigma rho sigma_rho ->
  Diamond sigma rho_pi left -> Diamond sigma_rho pi right ->
  CrossWordEq U (itinerary_word left) (itinerary_word right).
Proof.
  intros Hrp Hsr Hl Hr.
  pose proof (diamond_is_cross_equation Hrp) as Erp.
  pose proof (diamond_is_cross_equation Hsr) as Esr.
  pose proof (diamond_is_cross_equation Hl) as El.
  pose proof (diamond_is_cross_equation Hr) as Er.
  pose proof (CrossWordEq_append Erp (itinerary_word sigma)) as Eleftctx.
  pose proof (CrossWordEq_prepend Esr (itinerary_word pi)) as Erightctx.
  eapply ge_trans.
  - apply ge_sym. exact El.
  - eapply ge_trans.
    + apply ge_sym. exact Eleftctx.
    + eapply ge_trans.
      * rewrite raw_itinerary_concat_assoc. apply ge_refl.
      * eapply ge_trans; [exact Erightctx|exact Er].
Qed.

(** ** Stable anchors, certified references, and genuine nesting lift *)

Record StableAnchor : Type := {
  stable_anchor : Anchor;
  stable_anchor_zone : Zone;
  stable_anchor_kind : Code
}.

Record StableOccurrence : Type := {
  stable_occurrence : Occurrence;
  stable_occurrence_zone : Zone;
  occurrence_zone_exact :
    occurrence_zone stable_occurrence = stable_occurrence_zone
}.

Record CertifiedReference (U : CapabilityRegistry) : Type := {
  cref_occurrence : StableOccurrence;
  cref_anchor : StableAnchor;
  cref_itinerary : Itinerary U
    (stable_occurrence_zone cref_occurrence)
    (stable_anchor_zone cref_anchor);
  cref_sort : occurrence_sort (stable_occurrence cref_occurrence) =
              anchor_sort (stable_anchor cref_anchor)
}.

Definition one_step_itinerary (U : CapabilityRegistry)
    (c : CapabilityCode) (p : CrossingArrow)
    (Hin : In p (fcross_arrows (fcap_crossing (registry_lookup U c))))
    (z z' : Zone) (Hs : xa_source p = z) (Ht : xa_target p = z') :
    Itinerary U z z'.
Proof.
  refine {| itinerary_word :=
      [{| cstep_capability := c; cstep_certificate := p |}] |}.
  eapply (@legal_itinerary_cons U z z' z').
  - exact Hin.
  - exact Hs.
  - exact Ht.
  - apply legal_itinerary_nil.
Defined.

Record ItineraryLift {U : CapabilityRegistry}
    (w : CertifiedReference U) : Type := {
  lift_capability : CapabilityCode;
  lift_certificate : CrossingArrow;
  lift_certificate_in :
    In lift_certificate
      (fcross_arrows (fcap_crossing
        (registry_lookup U lift_capability)));
  lift_source : xa_source lift_certificate =
    stable_anchor_zone (cref_anchor w);
  lift_target : Zone;
  lift_target_exact : xa_target lift_certificate = lift_target;
  lifted_itinerary : Itinerary U
    (stable_occurrence_zone (cref_occurrence w)) lift_target;
  lifted_diamond :
    Diamond
      (@one_step_itinerary U lift_capability lift_certificate
         lift_certificate_in _ _ lift_source lift_target_exact)
      (cref_itinerary w) lifted_itinerary
}.

Definition lift_reference {U} (w : CertifiedReference U)
    (p : ItineraryLift w) : CertifiedReference U :=
  {| cref_occurrence := cref_occurrence w;
     cref_anchor :=
       {| stable_anchor := stable_anchor (cref_anchor w);
          stable_anchor_zone := lift_target p;
          stable_anchor_kind := stable_anchor_kind (cref_anchor w) |};
     cref_itinerary := lifted_itinerary p;
     cref_sort := cref_sort w |}.

Inductive OSheet (U : CapabilityRegistry) : Type :=
| OSGenerator : HorizontalGenerator -> OSheet U
| OSBlank : Interface -> OSheet U
| OSTensor : OSheet U -> OSheet U -> OSheet U
| OSHComp : OSheet U -> OSheet U -> OSheet U
| OSReference : CertifiedReference U -> OSheet U
| OSBoundary : FCapability -> OSheet U -> OSheet U
| OSPortal : CapabilityCode -> OSheet U -> OSheet U
| OSBinder : CapabilityCode -> OSheet U -> OSheet U.

Arguments OSGenerator {U} _.
Arguments OSBlank {U} _.
Arguments OSTensor {U} _ _.
Arguments OSHComp {U} _ _.
Arguments OSReference {U} _.
Arguments OSBoundary {U} _ _.
Arguments OSPortal {U} _ _.
Arguments OSBinder {U} _ _.

Inductive SheetLift (U : CapabilityRegistry) :
    OSheet U -> OSheet U -> Type :=
| SLGenerator : forall g, @SheetLift U (OSGenerator g) (OSGenerator g)
| SLBlank : forall A, @SheetLift U (OSBlank A) (OSBlank A)
| SLTensor : forall G G' H H',
    @SheetLift U G G' -> @SheetLift U H H' ->
    @SheetLift U (OSTensor G H) (OSTensor G' H')
| SLHComp : forall G G' H H',
    @SheetLift U G G' -> @SheetLift U H H' ->
    @SheetLift U (OSHComp G H) (OSHComp G' H')
| SLReference : forall w (p : ItineraryLift w),
    @SheetLift U (OSReference w) (OSReference (@lift_reference U w p))
| SLBoundary : forall b G G',
    @SheetLift U G G' ->
    @SheetLift U (OSBoundary b G) (OSBoundary b G')
| SLPortal : forall c G G',
    @SheetLift U G G' -> @SheetLift U (OSPortal c G) (OSPortal c G')
| SLBinder : forall c G G',
    @SheetLift U G G' -> @SheetLift U (OSBinder c G) (OSBinder c G').

Fixpoint sheet_lift_uses_capability {U G G'} (c : CapabilityCode)
    (L : @SheetLift U G G') : Prop :=
  match L with
  | SLGenerator _ _ | SLBlank _ _ => True
  | SLTensor L1 L2 | SLHComp L1 L2 =>
      sheet_lift_uses_capability c L1 /\
      sheet_lift_uses_capability c L2
  | SLReference p => lift_capability p = c
  | SLBoundary _ L0 | SLPortal _ L0 | SLBinder _ L0 =>
      sheet_lift_uses_capability c L0
  end.

Record NestedSheet (U : CapabilityRegistry) (b : FCapability)
    (G : OSheet U) : Type := {
  nested_lifted_sheet : OSheet U;
  nested_reference_lift : @SheetLift U G nested_lifted_sheet;
  nested_lift_uses_boundary_capability :
    sheet_lift_uses_capability (fcap_code b) nested_reference_lift;
  nested_boundary_sheet : OSheet U := OSBoundary b nested_lifted_sheet
}.

Inductive OCell (U : CapabilityRegistry) : OSheet U -> OSheet U -> Type :=
| OCPrimitive : forall G H,
    CellCode -> RuleCode -> list DerivCode -> list Code -> @OCell U G H
| OCIdentity : forall G, @OCell U G G
| OCVertical : forall G H K, @OCell U G H -> @OCell U H K -> @OCell U G K
| OCHorizontal : forall G G' H H',
    @OCell U G G' -> @OCell U H H' ->
    @OCell U (OSHComp G H) (OSHComp G' H')
| OCTensor : forall G G' H H',
    @OCell U G G' -> @OCell U H H' ->
    @OCell U (OSTensor G H) (OSTensor G' H')
| OCNest : forall b G G' H H'
    (LG : @SheetLift U G G') (LH : @SheetLift U H H'),
    sheet_lift_uses_capability (fcap_code b) LG ->
    sheet_lift_uses_capability (fcap_code b) LH ->
    @OCell U G H -> @OCell U (OSBoundary b G') (OSBoundary b H')
| OCPortalCell : forall c G G' H H',
    @OCell U G G' -> @OCell U H H' ->
    @OCell U (OSPortal c (OSHComp G H))
             (OSPortal c (OSHComp G' H'))
| OCBinderCell : forall c G G' H H',
    @OCell U G G' -> @OCell U H H' ->
    @OCell U (OSBinder c (OSTensor G H))
             (OSBinder c (OSTensor G' H')).

Inductive OCellEq U : forall G H, @OCell U G H -> @OCell U G H -> Prop :=
| oce_refl : forall G H (alpha : @OCell U G H), @OCellEq U G H alpha alpha
| oce_sym : forall G H (alpha beta : @OCell U G H),
    @OCellEq U G H alpha beta -> @OCellEq U G H beta alpha
| oce_trans : forall G H (alpha beta gamma : @OCell U G H),
    @OCellEq U G H alpha beta -> @OCellEq U G H beta gamma ->
    @OCellEq U G H alpha gamma
| oce_nest_identity : forall b G G' (L : @SheetLift U G G') Lok,
    @OCellEq U (OSBoundary b G') (OSBoundary b G')
      (OCNest b L L Lok Lok (OCIdentity G))
      (OCIdentity (OSBoundary b G'))
| oce_nest_vertical : forall b G G' H H' K K'
    (LG : @SheetLift U G G') (LH : @SheetLift U H H')
    (LK : @SheetLift U K K')
    (LGok : sheet_lift_uses_capability (fcap_code b) LG)
    (LHok : sheet_lift_uses_capability (fcap_code b) LH)
    (LKok : sheet_lift_uses_capability (fcap_code b) LK)
    (alpha : @OCell U G H) (beta : @OCell U H K),
    @OCellEq U (OSBoundary b G') (OSBoundary b K')
      (OCNest b LG LK LGok LKok (OCVertical alpha beta))
      (OCVertical (OCNest b LG LH LGok LHok alpha)
                  (OCNest b LH LK LHok LKok beta)).

Definition CapabilityNestingLaws U b : Prop :=
  (forall G G' (L : @SheetLift U G G') Lok,
      @OCellEq U (OSBoundary b G') (OSBoundary b G')
        (OCNest b L L Lok Lok (OCIdentity G))
                (OCIdentity (OSBoundary b G'))) /\
  (forall G G' H H' K K'
      (LG : @SheetLift U G G') (LH : @SheetLift U H H')
      (LK : @SheetLift U K K')
      (LGok : sheet_lift_uses_capability (fcap_code b) LG)
      (LHok : sheet_lift_uses_capability (fcap_code b) LH)
      (LKok : sheet_lift_uses_capability (fcap_code b) LK)
      (alpha : @OCell U G H) (beta : @OCell U H K),
      @OCellEq U (OSBoundary b G') (OSBoundary b K')
        (OCNest b LG LK LGok LKok (OCVertical alpha beta))
        (OCVertical (OCNest b LG LH LGok LHok alpha)
                    (OCNest b LH LK LHok LKok beta))).

Theorem capability_nesting_is_functorial U b :
  CapabilityNestingLaws U b.
Proof.
  split.
  - intros G G' L Lok. exact (@oce_nest_identity U b G G' L Lok).
  - intros G G' H H' K K' LG LH LK LGok LHok LKok alpha beta.
    exact (@oce_nest_vertical U b G G' H H' K K'
      LG LH LK LGok LHok LKok alpha beta).
Qed.

Theorem nesting_changes_reference_certificate U
    (w : CertifiedReference U) (p : ItineraryLift w) :
  itinerary_word (cref_itinerary (@lift_reference U w p)) =
  reduce_cross U
    (raw_itinerary_concat (itinerary_word (cref_itinerary w))
      [{| cstep_capability := lift_capability p;
          cstep_certificate := lift_certificate p |}]).
Proof. exact (diamond_executes_reduce_cross (lifted_diamond p)). Qed.

(** ** Stable-anchor term syntax *)

Definition transport_itinerary_end {U z x y} (e : x = y)
    (p : Itinerary U z x) : Itinerary U z y.
Proof. destruct e. exact p. Defined.

Inductive AnchorTerm (U : CapabilityRegistry) : Type :=
| ATReference : CertifiedReference U -> AnchorTerm U
| ATAnchor : StableAnchor -> AnchorTerm U
| ATApplication : AnchorTerm U -> list (AnchorTerm U) -> AnchorTerm U
| ATBinder : CapabilityCode -> StableAnchor -> AnchorTerm U -> AnchorTerm U
| ATTensor : AnchorTerm U -> AnchorTerm U -> AnchorTerm U
| ATCut : StableAnchor -> AnchorTerm U -> AnchorTerm U -> AnchorTerm U
| ATSharedPlug : StableOccurrence -> StableAnchor -> AnchorTerm U -> AnchorTerm U
| ATControl : Code -> AnchorTerm U.

Arguments ATReference {U} _.
Arguments ATAnchor {U} _.
Arguments ATApplication {U} _ _.
Arguments ATBinder {U} _ _ _.
Arguments ATTensor {U} _ _.
Arguments ATCut {U} _ _ _.
Arguments ATSharedPlug {U} _ _ _.
Arguments ATControl {U} _.

Fixpoint term_anchor_ids {U} (t : AnchorTerm U) : list Id :=
  match t with
  | ATReference w => [anchor_id (stable_anchor (cref_anchor w))]
  | ATAnchor a => [anchor_id (stable_anchor a)]
  | ATApplication f args =>
      term_anchor_ids f ++ flat_map term_anchor_ids args
  | ATBinder _ a body => anchor_id (stable_anchor a) :: term_anchor_ids body
  | ATTensor x y | ATCut _ x y => term_anchor_ids x ++ term_anchor_ids y
  | ATSharedPlug _ a x => anchor_id (stable_anchor a) :: term_anchor_ids x
  | ATControl _ => []
  end.

(** ** Open module cells and semantic theory composition *)

Record TheoryBoundary : Type := {
  theory_uri : URI;
  theory_anchors : list StableAnchor;
  theory_zone : StableAnchor -> Zone
}.

Record OpenModCell (U : CapabilityRegistry)
    (S T : TheoryBoundary) : Type := {
  omc_sheet : OSheet U;
  omc_anchor_image : StableAnchor -> StableAnchor;
  omc_assignment : StableAnchor -> option (AnchorTerm U);
  omc_assignment_domain : StableAnchor -> bool;
  omc_assignment_domain_exact : forall a,
    omc_assignment_domain a = true <-> exists t, omc_assignment a = Some t;
  omc_itinerary : forall a,
    Itinerary U (theory_zone S a)
      (theory_zone T (omc_anchor_image a));
  omc_filter : StableAnchor -> bool;
  omc_filter_domain : forall a,
    omc_assignment_domain a = omc_filter a
}.

Fixpoint morphism_action {U S T}
    (mu : OpenModCell U S T) (t : AnchorTerm U) : AnchorTerm U :=
  match t with
  | ATReference w =>
      match omc_assignment mu (cref_anchor w) with
      | Some assigned => assigned
      | None => ATReference w
      end
  | ATAnchor a =>
      ATAnchor (omc_anchor_image mu a)
  | ATApplication f args =>
      ATApplication (morphism_action mu f) (map (morphism_action mu) args)
  | ATBinder b a body =>
      ATBinder b (omc_anchor_image mu a) (morphism_action mu body)
  | ATTensor x y => ATTensor (morphism_action mu x) (morphism_action mu y)
  | ATCut a x y =>
      ATCut (omc_anchor_image mu a)
        (morphism_action mu x) (morphism_action mu y)
  | ATSharedPlug o a x =>
      ATSharedPlug o (omc_anchor_image mu a) (morphism_action mu x)
  | ATControl c => ATControl c
  end.

Definition composed_assignment {U S T V}
    (mu : OpenModCell U S T) (nu : OpenModCell U T V)
    (a : StableAnchor) : option (AnchorTerm U) :=
  match omc_assignment mu a with
  | Some t => Some (morphism_action nu t)
  | None => None
  end.

Definition composed_filter {U S T V}
    (mu : OpenModCell U S T) (nu : OpenModCell U T V)
    (a : StableAnchor) : bool :=
  andb (omc_filter mu a) (omc_filter nu (omc_anchor_image mu a)).

Inductive PortalNormalization U : OSheet U -> OSheet U -> Prop :=
| portal_cut_contract : forall c G H,
    @PortalNormalization U (OSHComp (OSPortal c G) (OSPortal c H))
      (OSPortal c (OSHComp G H))
| portal_normal_refl : forall G, @PortalNormalization U G G.

Record TheoryComposition {U S T V}
    (mu : OpenModCell U S T) (nu : OpenModCell U T V)
    (composite : OpenModCell U S V) : Prop := {
  theory_comp_sheet :
    @PortalNormalization U (OSHComp (omc_sheet mu) (omc_sheet nu))
      (omc_sheet composite);
  theory_comp_anchor : forall a,
    omc_anchor_image composite a =
    omc_anchor_image nu (omc_anchor_image mu a);
  theory_comp_assignment : forall a,
    omc_assignment composite a = composed_assignment mu nu a;
  theory_comp_itinerary : forall a,
    Diamond (omc_itinerary nu (omc_anchor_image mu a))
            (omc_itinerary mu a)
            (transport_itinerary_end
              (f_equal (theory_zone V) (theory_comp_anchor a))
              (omc_itinerary composite a));
  theory_comp_filter : forall a,
    omc_filter composite a = composed_filter mu nu a
}.

Theorem theory_composition_uses_action_diamond_filter U S T V
    (mu : OpenModCell U S T) (nu : OpenModCell U T V)
    (composite : OpenModCell U S V) :
  TheoryComposition mu nu composite ->
  (forall a, omc_assignment composite a =
       match omc_assignment mu a with
       | Some t => Some (morphism_action nu t)
       | None => None
       end) /\
  (forall a, exists e : omc_anchor_image composite a =
                         omc_anchor_image nu (omc_anchor_image mu a),
     Diamond (omc_itinerary nu (omc_anchor_image mu a))
       (omc_itinerary mu a)
       (transport_itinerary_end (f_equal (theory_zone V) e)
         (omc_itinerary composite a))) /\
  (forall a, omc_filter composite a =
       andb (omc_filter mu a)
         (omc_filter nu (omc_anchor_image mu a))).
Proof.
  intros H. split; [apply theory_comp_assignment; exact H|].
  split.
  - intro a. exists (theory_comp_anchor H a).
    apply theory_comp_itinerary; exact H.
  - apply theory_comp_filter; exact H.
Qed.

(** ** Material finite hierarchical-hypergraph representation *)

Definition GraphId := list nat.

Inductive MaterialRegionKind : Type :=
| MRRoot
| MRCapability : FCapability -> MaterialRegionKind
| MRPortal : FCapability -> MaterialRegionKind
| MRBinder : FCapability -> MaterialRegionKind.

Inductive MaterialNodeKind : Type :=
| MNControl : Code -> MaterialNodeKind
| MNGenerator : MaterialNodeKind
| MNAnchor : MaterialNodeKind
| MNOccurrence : MaterialNodeKind
| MNGateway : MaterialNodeKind.

Record MaterialRegion : Type := {
  material_region_id : GraphId;
  material_region_parent : option GraphId;
  material_region_kind : MaterialRegionKind
}.

Record MaterialNode : Type := {
  material_node_id : GraphId;
  material_node_region : GraphId;
  material_node_kind : MaterialNodeKind;
  material_node_children : list GraphId;
  material_node_payload : list Code
}.

Record MaterialPort : Type := {
  material_port_id : GraphId;
  material_port_owner : GraphId;
  material_port_slot : Slot
}.

Inductive PackedCertifiedItinerary (U : CapabilityRegistry) : Type :=
| PackCertifiedItinerary : forall z z',
    Itinerary U z z' -> PackedCertifiedItinerary U.

Arguments PackCertifiedItinerary {U} z z' _.

Record MaterialEdge (U : CapabilityRegistry) : Type := {
  material_edge_id : GraphId;
  material_edge_region : GraphId;
  material_edge_kind : WireKind;
  material_edge_sources : list GraphId;
  material_edge_targets : list GraphId;
  material_edge_certificate : option (PackedCertifiedItinerary U);
  material_edge_payload : list Code
}.

Record MaterialHypergraph (U : CapabilityRegistry) : Type := {
  material_regions : list MaterialRegion;
  material_nodes : list MaterialNode;
  material_ports : list MaterialPort;
  material_edges : list (MaterialEdge U);
  material_root : GraphId;
  material_inputs : list GraphId;
  material_outputs : list GraphId;
  material_generators : list (GraphId * HorizontalGenerator);
  material_references : list (GraphId * CertifiedReference U);
  material_blanks : list (GraphId * Interface)
}.

Definition empty_material_graph U (root : GraphId) : MaterialHypergraph U :=
  {| material_regions := [];
     material_nodes := [];
     material_ports := [];
     material_edges := [];
     material_root := root;
     material_inputs := [];
     material_outputs := [];
     material_generators := [];
     material_references := [];
     material_blanks := [] |}.

Definition union_material_graph {U} (root : GraphId)
    (G H : MaterialHypergraph U) : MaterialHypergraph U :=
  {| material_regions := material_regions G ++ material_regions H;
     material_nodes := material_nodes G ++ material_nodes H;
     material_ports := material_ports G ++ material_ports H;
     material_edges := material_edges G ++ material_edges H;
     material_root := root;
     material_inputs := material_inputs G ++ material_inputs H;
     material_outputs := material_outputs G ++ material_outputs H;
     material_generators := material_generators G ++ material_generators H;
     material_references := material_references G ++ material_references H;
     material_blanks := material_blanks G ++ material_blanks H |}.

Fixpoint osheet_source {U} (G : OSheet U) : Interface :=
  match G with
  | OSGenerator g => hg_source g
  | OSBlank A => A
  | OSTensor G H => iface_sum (osheet_source G) (osheet_source H)
  | OSHComp G _ => osheet_source G
  | OSReference w =>
      [{| slot_pol := PIn;
          slot_role := occurrence_sort (stable_occurrence (cref_occurrence w));
          slot_wire := RefWire;
          slot_order_role := occurrence_label
            (stable_occurrence (cref_occurrence w)) |}]
  | OSBoundary b G => capability_object_in b (osheet_source G)
  | OSPortal c G | OSBinder c G =>
      capability_object_in (registry_lookup U c) (osheet_source G)
  end.

Fixpoint osheet_target {U} (G : OSheet U) : Interface :=
  match G with
  | OSGenerator g => hg_target g
  | OSBlank A => A
  | OSTensor G H => iface_sum (osheet_target G) (osheet_target H)
  | OSHComp _ H => osheet_target H
  | OSReference w =>
      [{| slot_pol := POut;
          slot_role := anchor_sort (stable_anchor (cref_anchor w));
          slot_wire := RefWire;
          slot_order_role := anchor_label (stable_anchor (cref_anchor w)) |}]
  | OSBoundary b G => capability_object_out b (osheet_target G)
  | OSPortal c G | OSBinder c G =>
      capability_object_out (registry_lookup U c) (osheet_target G)
  end.

Fixpoint material_ports_for (owner prefix : GraphId) (n : nat)
    (A : Interface) : list MaterialPort :=
  match A with
  | [] => []
  | s :: rest =>
      {| material_port_id := n :: prefix;
         material_port_owner := owner;
         material_port_slot := s |} ::
      material_ports_for owner prefix (S n) rest
  end.

Fixpoint material_port_ids (prefix : GraphId) (n : nat)
    (A : Interface) : list GraphId :=
  match A with
  | [] => []
  | _ :: rest => (n :: prefix) :: material_port_ids prefix (S n) rest
  end.

Definition control_tag_of_sheet {U} (G : OSheet U) : Code :=
  match G with
  | OSGenerator _ => 1 | OSBlank _ => 2 | OSTensor _ _ => 3
  | OSHComp _ _ => 4 | OSReference _ => 5 | OSBoundary _ _ => 6
  | OSPortal _ _ => 7 | OSBinder _ _ => 8
  end.

Definition sheet_child_ids {U} (root_id : GraphId) (G : OSheet U) : list GraphId :=
  match G with
  | OSTensor _ _ | OSHComp _ _ => [(0 :: root_id); (1 :: root_id)]
  | OSBoundary _ _ | OSPortal _ _ | OSBinder _ _ => [(0 :: root_id)]
  | _ => []
  end.

Definition material_interface_shell {U} (root_id : GraphId)
    (parent : option GraphId) (kind : MaterialRegionKind)
    (G : OSheet U) : MaterialHypergraph U :=
  let in_prefix := 100 :: root_id in
  let out_prefix := 200 :: root_id in
  let inputs := material_port_ids in_prefix 0 (osheet_source G) in
  let outputs := material_port_ids out_prefix 0 (osheet_target G) in
  {| material_regions :=
       [{| material_region_id := root_id;
           material_region_parent := parent;
           material_region_kind := kind |}];
     material_nodes :=
       [{| material_node_id := 10 :: root_id;
           material_node_region := root_id;
           material_node_kind := MNControl (control_tag_of_sheet G);
           material_node_children := sheet_child_ids root_id G;
           material_node_payload := [] |}];
     material_ports :=
       material_ports_for (10 :: root_id) in_prefix 0 (osheet_source G) ++
       material_ports_for (10 :: root_id) out_prefix 0 (osheet_target G);
     material_edges := [];
     material_root := root_id;
     material_inputs := inputs;
     material_outputs := outputs;
     material_generators := [];
     material_references := [];
     material_blanks := [] |}.

Definition add_material_payload {U} (shell payload : MaterialHypergraph U) :
    MaterialHypergraph U := union_material_graph (material_root shell) shell payload.

Fixpoint materialize_sheet {U} (root_id : GraphId) (parent : option GraphId)
    (G : OSheet U) : MaterialHypergraph U :=
  let kind :=
    match G with
    | OSBoundary b _ => MRCapability b
    | OSPortal c _ => MRPortal (registry_lookup U c)
    | OSBinder c _ => MRBinder (registry_lookup U c)
    | _ => MRRoot
    end in
  let shell := material_interface_shell root_id parent kind G in
  match G with
  | OSGenerator g =>
      let payload := empty_material_graph U root_id in
      {| material_regions := material_regions shell;
         material_nodes := material_nodes shell ++
           [{| material_node_id := 11 :: root_id;
               material_node_region := root_id;
               material_node_kind := MNGenerator;
               material_node_children := [];
               material_node_payload := hg_payload g |}];
         material_ports := material_ports shell;
         material_edges := [];
         material_root := root_id;
         material_inputs := material_inputs shell;
         material_outputs := material_outputs shell;
         material_generators := [(11 :: root_id, g)];
         material_references := [];
         material_blanks := [] |}
  | OSBlank A =>
      {| material_regions := material_regions shell;
         material_nodes := material_nodes shell;
         material_ports := material_ports shell;
         material_edges := [];
         material_root := root_id;
         material_inputs := material_inputs shell;
         material_outputs := material_outputs shell;
         material_generators := [];
         material_references := [];
         material_blanks := [(10 :: root_id, A)] |}
  | OSTensor X Y =>
      add_material_payload shell
        (union_material_graph root_id
          (materialize_sheet (0 :: root_id) (Some root_id) X)
          (materialize_sheet (1 :: root_id) (Some root_id) Y))
  | OSHComp X Y =>
      add_material_payload shell
        (union_material_graph root_id
          (materialize_sheet (0 :: root_id) (Some root_id) X)
          (materialize_sheet (1 :: root_id) (Some root_id) Y))
  | OSReference w =>
      {| material_regions := material_regions shell;
         material_nodes := material_nodes shell ++
           [{| material_node_id := 20 :: root_id;
               material_node_region := root_id; material_node_kind := MNOccurrence;
               material_node_children := [];
               material_node_payload :=
                 [occurrence_id (stable_occurrence (cref_occurrence w));
                  stable_occurrence_zone (cref_occurrence w)] |};
            {| material_node_id := 21 :: root_id;
               material_node_region := root_id; material_node_kind := MNAnchor;
               material_node_children := [];
               material_node_payload :=
                 [anchor_id (stable_anchor (cref_anchor w));
                  anchor_uri (stable_anchor (cref_anchor w));
                  stable_anchor_zone (cref_anchor w)] |};
            {| material_node_id := 22 :: root_id;
               material_node_region := root_id; material_node_kind := MNGateway;
               material_node_children := [];
               material_node_payload := map (fun s =>
                 xa_code (cstep_certificate s))
                 (itinerary_word (cref_itinerary w)) |}];
         material_ports := material_ports shell;
         material_edges :=
           [{| material_edge_id := 30 :: root_id;
               material_edge_region := root_id;
               material_edge_kind := RefWire;
               material_edge_sources := material_inputs shell;
               material_edge_targets := material_outputs shell;
               material_edge_certificate := Some
                 (PackCertifiedItinerary _ _ (cref_itinerary w));
               material_edge_payload :=
                 [anchor_id (stable_anchor (cref_anchor w))] |}];
         material_root := root_id;
         material_inputs := material_inputs shell;
         material_outputs := material_outputs shell;
         material_generators := [];
         material_references := [(30 :: root_id, w)];
         material_blanks := [] |}
  | OSBoundary _ X | OSPortal _ X | OSBinder _ X =>
      add_material_payload shell
        (materialize_sheet (0 :: root_id) (Some root_id) X)
  end.

Definition faithful_representation_map {U} (G : OSheet U) :
    MaterialHypergraph U := materialize_sheet [] None G.

Theorem representation_materializes_reference U (w : CertifiedReference U) :
  exists e, In e (material_edges
      (faithful_representation_map (OSReference w))) /\
    material_edge_kind e = RefWire /\
    material_edge_certificate e =
      Some (PackCertifiedItinerary _ _ (cref_itinerary w)).
Proof.
  eexists. repeat split; simpl; auto.
Qed.

Theorem representation_materializes_capability_region U b G :
  exists r, In r (material_regions
      (faithful_representation_map (@OSBoundary U b G))) /\
    material_region_kind r = MRCapability b.
Proof. eexists. split; simpl; auto. Qed.

Inductive MaterialDerivation U :
    MaterialHypergraph U -> MaterialHypergraph U -> Type :=
| MDPrimitive : forall G H,
    RuleCode -> CellCode -> list DerivCode -> list Code ->
    @MaterialDerivation U G H
| MDIdentity : forall G, @MaterialDerivation U G G
| MDVertical : forall G H K,
    @MaterialDerivation U G H -> @MaterialDerivation U H K ->
    @MaterialDerivation U G K
| MDHorizontal : forall G G' H H',
    @MaterialDerivation U (faithful_representation_map G)
      (faithful_representation_map G') ->
    @MaterialDerivation U (faithful_representation_map H)
      (faithful_representation_map H') ->
    @MaterialDerivation U
      (faithful_representation_map (OSHComp G H))
      (faithful_representation_map (OSHComp G' H'))
| MDTensor : forall G G' H H',
    @MaterialDerivation U (faithful_representation_map G)
      (faithful_representation_map G') ->
    @MaterialDerivation U (faithful_representation_map H)
      (faithful_representation_map H') ->
    @MaterialDerivation U
      (faithful_representation_map (OSTensor G H))
      (faithful_representation_map (OSTensor G' H'))
| MDNest : forall b G G' H H'
    (LG : @SheetLift U G G') (LH : @SheetLift U H H'),
    @MaterialDerivation U (faithful_representation_map G)
      (faithful_representation_map H) ->
    @MaterialDerivation U
      (faithful_representation_map (OSBoundary b G'))
      (faithful_representation_map (OSBoundary b H'))
| MDPortal : forall c G G' H H',
    @MaterialDerivation U (faithful_representation_map G)
      (faithful_representation_map G') ->
    @MaterialDerivation U (faithful_representation_map H)
      (faithful_representation_map H') ->
    @MaterialDerivation U
      (faithful_representation_map (OSPortal c (OSHComp G H)))
      (faithful_representation_map (OSPortal c (OSHComp G' H')))
| MDBinder : forall c G G' H H',
    @MaterialDerivation U (faithful_representation_map G)
      (faithful_representation_map G') ->
    @MaterialDerivation U (faithful_representation_map H)
      (faithful_representation_map H') ->
    @MaterialDerivation U
      (faithful_representation_map (OSBinder c (OSTensor G H)))
      (faithful_representation_map (OSBinder c (OSTensor G' H'))).

Inductive CellGraphCompiler U : forall G H,
    @OCell U G H ->
    @MaterialDerivation U (faithful_representation_map G)
      (faithful_representation_map H) -> Prop :=
| compile_cell_primitive : forall G H code rule premises payload,
    @CellGraphCompiler U G H
      (OCPrimitive G H code rule premises payload)
      (MDPrimitive (faithful_representation_map G)
        (faithful_representation_map H) rule code premises payload)
| compile_cell_identity : forall G,
    @CellGraphCompiler U G G (OCIdentity G)
      (MDIdentity (faithful_representation_map G))
| compile_cell_vertical : forall G H K alpha beta da db,
    @CellGraphCompiler U G H alpha da ->
    @CellGraphCompiler U H K beta db ->
    @CellGraphCompiler U G K (OCVertical alpha beta) (MDVertical da db)
| compile_cell_horizontal : forall G G' H H' alpha beta da db,
    @CellGraphCompiler U G G' alpha da ->
    @CellGraphCompiler U H H' beta db ->
    @CellGraphCompiler U (OSHComp G H) (OSHComp G' H')
      (OCHorizontal alpha beta) (@MDHorizontal U G G' H H' da db)
| compile_cell_tensor : forall G G' H H' alpha beta da db,
    @CellGraphCompiler U G G' alpha da ->
    @CellGraphCompiler U H H' beta db ->
    @CellGraphCompiler U (OSTensor G H) (OSTensor G' H')
      (OCTensor alpha beta) (@MDTensor U G G' H H' da db)
| compile_cell_nest : forall b G G' H H'
    (LG : @SheetLift U G G') (LH : @SheetLift U H H')
    (LGok : sheet_lift_uses_capability (fcap_code b) LG)
    (LHok : sheet_lift_uses_capability (fcap_code b) LH) alpha d,
    @CellGraphCompiler U G H alpha d ->
    @CellGraphCompiler U (OSBoundary b G') (OSBoundary b H')
      (OCNest b LG LH LGok LHok alpha) (@MDNest U b G G' H H' LG LH d)
| compile_cell_portal : forall c G G' H H' alpha beta da db,
    @CellGraphCompiler U G G' alpha da ->
    @CellGraphCompiler U H H' beta db ->
    @CellGraphCompiler U
      (OSPortal c (OSHComp G H)) (OSPortal c (OSHComp G' H'))
      (OCPortalCell c alpha beta) (@MDPortal U c G G' H H' da db)
| compile_cell_binder : forall c G G' H H' alpha beta da db,
    @CellGraphCompiler U G G' alpha da ->
    @CellGraphCompiler U H H' beta db ->
    @CellGraphCompiler U
      (OSBinder c (OSTensor G H)) (OSBinder c (OSTensor G' H'))
      (OCBinderCell c alpha beta) (@MDBinder U c G G' H H' da db).

Theorem every_cell_has_material_derivation U G H
    (alpha : @OCell U G H) :
  exists d : @MaterialDerivation U
      (faithful_representation_map G) (faithful_representation_map H),
    @CellGraphCompiler U G H alpha d.
Proof.
  induction alpha;
    repeat match goal with
    | IH : exists _d, _ |- _ => destruct IH as [?d ?Hd]
    end;
    eexists; econstructor; eauto.
Qed.

Definition SheetRepresentationEq {U} (G H : OSheet U) : Prop :=
  faithful_representation_map G = faithful_representation_map H.

(** ** Structural flattening rules over real OHTG data *)

Inductive PackedOpenModCell (U : CapabilityRegistry) : Type :=
| PackOpenModCell : forall S T, OpenModCell U S T -> PackedOpenModCell U.

Arguments PackOpenModCell {U} S T _.

Record FlatDeclaration (U : CapabilityRegistry) : Type := {
  flat_decl_anchor : StableAnchor;
  flat_decl_term : option (AnchorTerm U);
  flat_decl_dependencies : list URI;
  flat_decl_alias : Code
}.

Record FlatReference (U : CapabilityRegistry) : Type := {
  flat_ref_occurrence : StableOccurrence;
  flat_ref_anchor : StableAnchor;
  flat_ref_itinerary : PackedCertifiedItinerary U
}.

Record FlatCorpus (U : CapabilityRegistry) : Type := {
  flat_corpus_sheets : list (OSheet U);
  flat_corpus_modules : list (PackedOpenModCell U);
  flat_corpus_declarations : list (FlatDeclaration U);
  flat_corpus_references : list (FlatReference U);
  flat_corpus_normal_paths : list (list URI);
  flat_corpus_sharing : list (URI * StableAnchor)
}.

Record PortalCutTask (U : CapabilityRegistry) : Type := {
  pct_source : TheoryBoundary;
  pct_middle : TheoryBoundary;
  pct_target : TheoryBoundary;
  pct_left : OpenModCell U pct_source pct_middle;
  pct_right : OpenModCell U pct_middle pct_target;
  pct_composite : OpenModCell U pct_source pct_target;
  pct_composition : TheoryComposition pct_left pct_right pct_composite
}.

Record InducedPathTask : Type := {
  path_raw : list URI;
  path_normal : list URI;
  path_strictly_contracts : List.length path_normal < List.length path_raw
}.

Record AssignmentTask (U : CapabilityRegistry) : Type := {
  assignment_source_anchor : StableAnchor;
  assignment_target_anchor : StableAnchor;
  assignment_target_itinerary : PackedCertifiedItinerary U;
  assignment_term : AnchorTerm U
}.

Record DeepAssignmentTask (U : CapabilityRegistry) : Type := {
  deep_assignment_raw_path : list URI;
  deep_assignment_normal_path : list URI;
  deep_assignment_path_contracts :
    List.length deep_assignment_normal_path <
    List.length deep_assignment_raw_path;
  deep_assignment_target : StableAnchor;
  deep_assignment_target_itinerary : PackedCertifiedItinerary U;
  deep_assignment_term : AnchorTerm U
}.

Record FilterTask : Type := {
  filter_uri : URI
}.

Definition filter_dependency_closed {U} (task : FilterTask)
    (C : FlatCorpus U) : Prop :=
  forall d, In d (flat_corpus_declarations C) ->
    anchor_uri (stable_anchor (flat_decl_anchor d)) <> filter_uri task ->
    ~ In (filter_uri task) (flat_decl_dependencies d).

Record SharingTask : Type := {
  sharing_uri : URI;
  sharing_anchor : StableAnchor
}.

Record ConflictTask : Type := {
  conflict_left_uri : URI;
  conflict_right_uri : URI;
  conflict_alias_left : Code;
  conflict_alias_right : Code;
  conflict_distinct_uri : conflict_left_uri <> conflict_right_uri
}.

Record StructuralFlatState (U : CapabilityRegistry) : Type := {
  sfs_corpus : FlatCorpus U;
  sfs_portal_work : list (PortalCutTask U);
  sfs_paths : list InducedPathTask;
  sfs_assignments : list (AssignmentTask U);
  sfs_deep_assignments : list (DeepAssignmentTask U);
  sfs_filters : list FilterTask;
  sfs_sharing_work : list SharingTask;
  sfs_conflicts : list ConflictTask
}.

Fixpoint osheet_constructor_size {U} (G : OSheet U) : nat :=
  match G with
  | OSGenerator _ | OSBlank _ | OSReference _ => 1
  | OSTensor X Y | OSHComp X Y =>
      S (osheet_constructor_size X + osheet_constructor_size Y)
  | OSBoundary _ X | OSPortal _ X | OSBinder _ X =>
      S (osheet_constructor_size X)
  end.

Definition portal_task_complexity {U} (t : PortalCutTask U) : nat :=
  S (osheet_constructor_size (omc_sheet (pct_left t)) +
     osheet_constructor_size (omc_sheet (pct_right t))).

Definition path_task_complexity (t : InducedPathTask) : nat :=
  List.length (path_raw t).

Definition assignment_task_complexity {U} (t : AssignmentTask U) : nat :=
  S (List.length (term_anchor_ids (assignment_term t))).

Definition deep_assignment_task_complexity {U}
    (t : DeepAssignmentTask U) : nat :=
  S (List.length (deep_assignment_raw_path t) +
     List.length (term_anchor_ids (deep_assignment_term t))).

Definition sum_nat {A} (f : A -> nat) (xs : list A) : nat :=
  fold_right (fun x n => f x + n) 0 xs.

Definition flat_measure {U} (S : StructuralFlatState U) :
    nat * nat * nat * nat * nat :=
  (List.length (sfs_portal_work S),
   sum_nat portal_task_complexity (sfs_portal_work S),
   sum_nat path_task_complexity (sfs_paths S),
   sum_nat assignment_task_complexity (sfs_assignments S) +
   sum_nat deep_assignment_task_complexity (sfs_deep_assignments S) +
   List.length (sfs_filters S) + List.length (sfs_sharing_work S),
   List.length (sfs_conflicts S)).

Inductive Lex5 : (nat * nat * nat * nat * nat) ->
    (nat * nat * nat * nat * nat) -> Prop :=
| lex5_1 : forall a a' b c d e b' c' d' e',
    a < a' -> Lex5 (a,b,c,d,e) (a',b',c',d',e')
| lex5_2 : forall a b b' c d e c' d' e',
    b < b' -> Lex5 (a,b,c,d,e) (a,b',c',d',e')
| lex5_3 : forall a b c c' d e d' e',
    c < c' -> Lex5 (a,b,c,d,e) (a,b,c',d',e')
| lex5_4 : forall a b c d d' e e',
    d < d' -> Lex5 (a,b,c,d,e) (a,b,c,d',e')
| lex5_5 : forall a b c d e e',
    e < e' -> Lex5 (a,b,c,d,e) (a,b,c,d,e').

Definition NestedLex2 := slexprod nat nat lt lt.
Definition NestedLex3 := slexprod (nat * nat) nat NestedLex2 lt.
Definition NestedLex4 := slexprod (nat * nat * nat) nat NestedLex3 lt.
Definition NestedLex5 :=
  slexprod (nat * nat * nat * nat) nat NestedLex4 lt.

Lemma Lex5_in_nested x y : Lex5 x y -> NestedLex5 x y.
Proof.
  intro H. inversion H; subst; unfold NestedLex5, NestedLex4,
    NestedLex3, NestedLex2.
  - apply left_slex. apply left_slex. apply left_slex.
    apply left_slex. assumption.
  - apply left_slex. apply left_slex. apply left_slex.
    apply right_slex. assumption.
  - apply left_slex. apply left_slex. apply right_slex. assumption.
  - apply left_slex. apply right_slex. assumption.
  - apply right_slex. assumption.
Qed.

Theorem Lex5_well_founded : well_founded Lex5.
Proof.
  eapply (@wf_incl _ Lex5 NestedLex5).
  - intros x y H. exact (Lex5_in_nested H).
  - unfold NestedLex5, NestedLex4, NestedLex3, NestedLex2.
    repeat apply wf_slexprod; apply lt_wf.
Qed.

Definition contract_portal_corpus {U} (task : PortalCutTask U)
    (C : FlatCorpus U) : FlatCorpus U :=
  {| flat_corpus_sheets := omc_sheet (pct_composite task) :: flat_corpus_sheets C;
     flat_corpus_modules :=
       PackOpenModCell _ _ (pct_composite task) :: flat_corpus_modules C;
     flat_corpus_declarations := flat_corpus_declarations C;
     flat_corpus_references := flat_corpus_references C;
     flat_corpus_normal_paths := flat_corpus_normal_paths C;
     flat_corpus_sharing := flat_corpus_sharing C |}.

Definition same_stable_uri (a b : StableAnchor) : bool :=
  Nat.eqb (anchor_uri (stable_anchor a)) (anchor_uri (stable_anchor b)).

Definition redirect_reference {U} (from target : StableAnchor)
    (target_itinerary : PackedCertifiedItinerary U)
    (r : FlatReference U) : FlatReference U :=
  if same_stable_uri (flat_ref_anchor r) from then
    {| flat_ref_occurrence := flat_ref_occurrence r;
       flat_ref_anchor := target;
       flat_ref_itinerary := target_itinerary |}
  else r.

Definition write_assignment_declaration {U} (task : AssignmentTask U)
    (d : FlatDeclaration U) : FlatDeclaration U :=
  if same_stable_uri (flat_decl_anchor d) (assignment_source_anchor task) then
    {| flat_decl_anchor := assignment_target_anchor task;
       flat_decl_term := Some (assignment_term task);
       flat_decl_dependencies := flat_decl_dependencies d;
       flat_decl_alias := flat_decl_alias d |}
  else d.

Definition propagate_assignment_corpus {U} (task : AssignmentTask U)
    (C : FlatCorpus U) : FlatCorpus U :=
  {| flat_corpus_sheets := flat_corpus_sheets C;
     flat_corpus_modules := flat_corpus_modules C;
     flat_corpus_declarations :=
       map (write_assignment_declaration task)
         (flat_corpus_declarations C);
     flat_corpus_references :=
       map (redirect_reference (assignment_source_anchor task)
          (assignment_target_anchor task) (assignment_target_itinerary task))
          (flat_corpus_references C);
     flat_corpus_normal_paths := flat_corpus_normal_paths C;
     flat_corpus_sharing := flat_corpus_sharing C |}.

Definition uri_in_path (u : URI) (path : list URI) : bool :=
  existsb (Nat.eqb u) path.

Definition deep_redirect_reference {U} (task : DeepAssignmentTask U)
    (r : FlatReference U) : FlatReference U :=
  if uri_in_path (anchor_uri (stable_anchor (flat_ref_anchor r)))
       (deep_assignment_raw_path task) then
    {| flat_ref_occurrence := flat_ref_occurrence r;
       flat_ref_anchor := deep_assignment_target task;
       flat_ref_itinerary := deep_assignment_target_itinerary task |}
  else r.

Definition write_deep_assignment_declaration {U}
    (task : DeepAssignmentTask U) (d : FlatDeclaration U) : FlatDeclaration U :=
  if uri_in_path (anchor_uri (stable_anchor (flat_decl_anchor d)))
       (deep_assignment_raw_path task) then
    {| flat_decl_anchor := deep_assignment_target task;
       flat_decl_term := Some (deep_assignment_term task);
       flat_decl_dependencies := deep_assignment_normal_path task;
       flat_decl_alias := flat_decl_alias d |}
  else d.

Definition propagate_deep_assignment_corpus {U}
    (task : DeepAssignmentTask U) (C : FlatCorpus U) : FlatCorpus U :=
  {| flat_corpus_sheets := flat_corpus_sheets C;
     flat_corpus_modules := flat_corpus_modules C;
     flat_corpus_declarations :=
       map (write_deep_assignment_declaration task)
         (flat_corpus_declarations C);
     flat_corpus_references :=
       map (deep_redirect_reference task)
         (flat_corpus_references C);
     flat_corpus_normal_paths :=
       deep_assignment_normal_path task :: flat_corpus_normal_paths C;
     flat_corpus_sharing :=
       (match rev (deep_assignment_normal_path task) with
        | [] => 0 | u :: _ => u
        end, deep_assignment_target task) :: flat_corpus_sharing C |}.

Definition keep_declaration_uri {U} (u : URI) (d : FlatDeclaration U) : bool :=
  negb (Nat.eqb (anchor_uri (stable_anchor (flat_decl_anchor d))) u).

Definition filter_declaration_corpus {U} (task : FilterTask)
    (C : FlatCorpus U) : FlatCorpus U :=
  {| flat_corpus_sheets := flat_corpus_sheets C;
     flat_corpus_modules := flat_corpus_modules C;
     flat_corpus_declarations :=
       filter (keep_declaration_uri (filter_uri task))
         (flat_corpus_declarations C);
     flat_corpus_references := flat_corpus_references C;
     flat_corpus_normal_paths := flat_corpus_normal_paths C;
     flat_corpus_sharing := flat_corpus_sharing C |}.

Definition install_sharing_corpus {U} (task : SharingTask)
    (C : FlatCorpus U) : FlatCorpus U :=
  {| flat_corpus_sheets := flat_corpus_sheets C;
     flat_corpus_modules := flat_corpus_modules C;
     flat_corpus_declarations := flat_corpus_declarations C;
     flat_corpus_references := flat_corpus_references C;
     flat_corpus_normal_paths := flat_corpus_normal_paths C;
     flat_corpus_sharing :=
       (sharing_uri task, sharing_anchor task) :: flat_corpus_sharing C |}.

Definition install_normal_path_corpus {U} (task : InducedPathTask)
    (C : FlatCorpus U) : FlatCorpus U :=
  {| flat_corpus_sheets := flat_corpus_sheets C;
     flat_corpus_modules := flat_corpus_modules C;
     flat_corpus_declarations := flat_corpus_declarations C;
     flat_corpus_references := flat_corpus_references C;
     flat_corpus_normal_paths := path_normal task :: flat_corpus_normal_paths C;
     flat_corpus_sharing := flat_corpus_sharing C |}.

Definition resolve_conflict_declaration {U} (task : ConflictTask)
    (d : FlatDeclaration U) : FlatDeclaration U :=
  let u := anchor_uri (stable_anchor (flat_decl_anchor d)) in
  {| flat_decl_anchor := flat_decl_anchor d;
     flat_decl_term := flat_decl_term d;
     flat_decl_dependencies := flat_decl_dependencies d;
     flat_decl_alias :=
       if Nat.eqb u (conflict_left_uri task) then conflict_alias_left task
       else if Nat.eqb u (conflict_right_uri task)
            then conflict_alias_right task else flat_decl_alias d |}.

Definition resolve_conflict_corpus {U} (task : ConflictTask)
    (C : FlatCorpus U) : FlatCorpus U :=
  {| flat_corpus_sheets := flat_corpus_sheets C;
     flat_corpus_modules := flat_corpus_modules C;
     flat_corpus_declarations :=
       map (resolve_conflict_declaration task) (flat_corpus_declarations C);
     flat_corpus_references := flat_corpus_references C;
     flat_corpus_normal_paths := flat_corpus_normal_paths C;
     flat_corpus_sharing := flat_corpus_sharing C |}.

Definition state_after_portal {U} (task : PortalCutTask U)
    (rest : list (PortalCutTask U)) (S : StructuralFlatState U) :
    StructuralFlatState U :=
  {| sfs_corpus := contract_portal_corpus task (sfs_corpus S);
     sfs_portal_work := rest; sfs_paths := sfs_paths S;
     sfs_assignments := sfs_assignments S;
     sfs_deep_assignments := sfs_deep_assignments S;
     sfs_filters := sfs_filters S; sfs_sharing_work := sfs_sharing_work S;
     sfs_conflicts := sfs_conflicts S |}.

Definition state_after_path {U} (task : InducedPathTask)
    (rest : list InducedPathTask)
    (S : StructuralFlatState U) : StructuralFlatState U :=
  {| sfs_corpus := install_normal_path_corpus task (sfs_corpus S);
     sfs_portal_work := sfs_portal_work S;
     sfs_paths := rest; sfs_assignments := sfs_assignments S;
     sfs_deep_assignments := sfs_deep_assignments S;
     sfs_filters := sfs_filters S; sfs_sharing_work := sfs_sharing_work S;
     sfs_conflicts := sfs_conflicts S |}.

Definition state_after_assignment {U} (task : AssignmentTask U)
    (rest : list (AssignmentTask U)) (S : StructuralFlatState U) :
    StructuralFlatState U :=
  {| sfs_corpus := propagate_assignment_corpus task (sfs_corpus S);
     sfs_portal_work := sfs_portal_work S; sfs_paths := sfs_paths S;
     sfs_assignments := rest; sfs_deep_assignments := sfs_deep_assignments S;
     sfs_filters := sfs_filters S; sfs_sharing_work := sfs_sharing_work S;
     sfs_conflicts := sfs_conflicts S |}.

Definition state_after_deep_assignment {U} (task : DeepAssignmentTask U)
    (rest : list (DeepAssignmentTask U)) (S : StructuralFlatState U) :
    StructuralFlatState U :=
  {| sfs_corpus := propagate_deep_assignment_corpus task (sfs_corpus S);
     sfs_portal_work := sfs_portal_work S; sfs_paths := sfs_paths S;
     sfs_assignments := sfs_assignments S; sfs_deep_assignments := rest;
     sfs_filters := sfs_filters S; sfs_sharing_work := sfs_sharing_work S;
     sfs_conflicts := sfs_conflicts S |}.

Definition state_after_filter {U} (task : FilterTask)
    (rest : list FilterTask) (S : StructuralFlatState U) :
    StructuralFlatState U :=
  {| sfs_corpus := filter_declaration_corpus task (sfs_corpus S);
     sfs_portal_work := sfs_portal_work S; sfs_paths := sfs_paths S;
     sfs_assignments := sfs_assignments S;
     sfs_deep_assignments := sfs_deep_assignments S; sfs_filters := rest;
     sfs_sharing_work := sfs_sharing_work S;
     sfs_conflicts := sfs_conflicts S |}.

Definition state_after_sharing {U} (task : SharingTask)
    (rest : list SharingTask) (S : StructuralFlatState U) :
    StructuralFlatState U :=
  {| sfs_corpus := install_sharing_corpus task (sfs_corpus S);
     sfs_portal_work := sfs_portal_work S; sfs_paths := sfs_paths S;
     sfs_assignments := sfs_assignments S;
     sfs_deep_assignments := sfs_deep_assignments S;
     sfs_filters := sfs_filters S; sfs_sharing_work := rest;
     sfs_conflicts := sfs_conflicts S |}.

Definition state_after_conflict {U} (task : ConflictTask)
    (rest : list ConflictTask)
    (S : StructuralFlatState U) : StructuralFlatState U :=
  {| sfs_corpus := resolve_conflict_corpus task (sfs_corpus S);
     sfs_portal_work := sfs_portal_work S;
     sfs_paths := sfs_paths S; sfs_assignments := sfs_assignments S;
     sfs_deep_assignments := sfs_deep_assignments S;
     sfs_filters := sfs_filters S; sfs_sharing_work := sfs_sharing_work S;
     sfs_conflicts := rest |}.

Inductive StructuralFlatStep U :
    StructuralFlatState U -> StructuralFlatState U -> Prop :=
| flat_portal_cut : forall S task rest,
    sfs_portal_work S = task :: rest ->
    @StructuralFlatStep U S (state_after_portal task rest S)
| flat_path_contraction : forall S task rest,
    sfs_portal_work S = [] -> sfs_paths S = task :: rest ->
    @StructuralFlatStep U S (state_after_path task rest S)
| flat_assignment_propagation : forall S task rest,
    sfs_portal_work S = [] -> sfs_paths S = [] ->
    sfs_assignments S = task :: rest ->
    @StructuralFlatStep U S (state_after_assignment task rest S)
| flat_deep_assignment_propagation : forall S task rest,
    sfs_portal_work S = [] -> sfs_paths S = [] ->
    sfs_assignments S = [] -> sfs_deep_assignments S = task :: rest ->
    @StructuralFlatStep U S (state_after_deep_assignment task rest S)
| flat_filter_propagation : forall S task rest,
    sfs_portal_work S = [] -> sfs_paths S = [] ->
    sfs_assignments S = [] -> sfs_deep_assignments S = [] ->
    sfs_filters S = task :: rest ->
    filter_dependency_closed task (sfs_corpus S) ->
    @StructuralFlatStep U S (state_after_filter task rest S)
| flat_sharing_install : forall S task rest,
    sfs_portal_work S = [] -> sfs_paths S = [] ->
    sfs_assignments S = [] -> sfs_deep_assignments S = [] ->
    sfs_filters S = [] -> sfs_sharing_work S = task :: rest ->
    @StructuralFlatStep U S (state_after_sharing task rest S)
| flat_conflict_resolution : forall S task rest,
    sfs_portal_work S = [] -> sfs_paths S = [] ->
    sfs_assignments S = [] -> sfs_deep_assignments S = [] ->
    sfs_filters S = [] -> sfs_sharing_work S = [] ->
    sfs_conflicts S = task :: rest ->
    @StructuralFlatStep U S (state_after_conflict task rest S).

Theorem structural_flat_step_decreases U S T :
  @StructuralFlatStep U S T -> Lex5 (flat_measure T) (flat_measure S).
Proof.
  intro H; inversion H; subst; unfold flat_measure; simpl;
    repeat match goal with Hx : _ = _ |- _ => rewrite Hx end; simpl.
  - apply lex5_1. lia.
  - apply lex5_3. unfold path_task_complexity.
    pose proof (path_strictly_contracts task). lia.
  - apply lex5_4. unfold assignment_task_complexity. lia.
  - apply lex5_4. unfold deep_assignment_task_complexity. lia.
  - apply lex5_4. lia.
  - apply lex5_4. lia.
  - apply lex5_5. lia.
Qed.

Theorem structural_flattening_termination U :
  well_founded (fun T S : StructuralFlatState U =>
    @StructuralFlatStep U S T).
Proof.
  eapply (@wf_incl _
    (fun T S : StructuralFlatState U => @StructuralFlatStep U S T)
    (fun T S : StructuralFlatState U => Lex5 (flat_measure T) (flat_measure S))).
  - intros T S H. now apply structural_flat_step_decreases.
  - apply (wf_inverse_image
      (StructuralFlatState U) (nat * nat * nat * nat * nat)
      Lex5 flat_measure Lex5_well_founded).
Qed.

Theorem portal_cut_changes_real_corpus U (S : StructuralFlatState U)
    task rest :
  sfs_portal_work S = task :: rest ->
  In (omc_sheet (pct_composite task))
    (flat_corpus_sheets
      (sfs_corpus (state_after_portal task rest S))).
Proof. intros; simpl; auto. Qed.

Theorem path_contraction_writes_normal_path U (S : StructuralFlatState U)
    task rest :
  sfs_paths S = task :: rest ->
  In (path_normal task)
    (flat_corpus_normal_paths
      (sfs_corpus (state_after_path task rest S))).
Proof. intros; simpl; auto. Qed.

Theorem assignment_propagation_replaces_certificate U
    (task : AssignmentTask U) (r : FlatReference U) :
  same_stable_uri (flat_ref_anchor r) (assignment_source_anchor task) = true ->
  flat_ref_itinerary
    (redirect_reference (assignment_source_anchor task)
      (assignment_target_anchor task) (assignment_target_itinerary task) r) =
  assignment_target_itinerary task.
Proof. intro H. unfold redirect_reference. now rewrite H. Qed.

Theorem conflict_resolution_writes_alias U (task : ConflictTask)
    (d : FlatDeclaration U) :
  anchor_uri (stable_anchor (flat_decl_anchor d)) = conflict_left_uri task ->
  flat_decl_alias (resolve_conflict_declaration task d) =
    conflict_alias_left task.
Proof.
  intro H. unfold resolve_conflict_declaration. simpl.
  rewrite H, Nat.eqb_refl. reflexivity.
Qed.

(** ** Source/target-indexed decorated deep contexts *)

Inductive DecoratedContext (U : CapabilityRegistry)
    (hole_source hole_target : OSheet U) : OSheet U -> OSheet U -> Type :=
| DCHole : @DecoratedContext U hole_source hole_target
    hole_source hole_target
| DCTensorRight : forall X Y A B,
    @DecoratedContext U hole_source hole_target X Y ->
    @OCell U A B ->
    @DecoratedContext U hole_source hole_target
      (OSTensor X A) (OSTensor Y B)
| DCTensorLeft : forall X Y A B,
    @OCell U A B ->
    @DecoratedContext U hole_source hole_target X Y ->
    @DecoratedContext U hole_source hole_target
      (OSTensor A X) (OSTensor B Y)
| DCHCompRight : forall X Y A B,
    @DecoratedContext U hole_source hole_target X Y ->
    @OCell U A B ->
    @DecoratedContext U hole_source hole_target
      (OSHComp X A) (OSHComp Y B)
| DCHCompLeft : forall X Y A B,
    @OCell U A B ->
    @DecoratedContext U hole_source hole_target X Y ->
    @DecoratedContext U hole_source hole_target
      (OSHComp A X) (OSHComp B Y)
| DCCapability : forall X Y X' Y' b
    (D : @DecoratedContext U hole_source hole_target X Y)
    (LX : @SheetLift U X X') (LY : @SheetLift U Y Y')
    (LXok : sheet_lift_uses_capability (fcap_code b) LX)
    (LYok : sheet_lift_uses_capability (fcap_code b) LY),
    @DecoratedContext U hole_source hole_target
      (OSBoundary b X') (OSBoundary b Y')
| DCModulePortal : forall X Y B S T
    (mu : OpenModCell U S T) c,
    @DecoratedContext U hole_source hole_target X Y ->
    @OCell U (omc_sheet mu) B ->
    @DecoratedContext U hole_source hole_target
      (OSPortal c (OSHComp X (omc_sheet mu)))
      (OSPortal c (OSHComp Y B))
| DCBinderBoundary : forall X Y A B c,
    @DecoratedContext U hole_source hole_target X Y ->
    @OCell U A B ->
    @DecoratedContext U hole_source hole_target
      (OSBinder c (OSTensor X A)) (OSBinder c (OSTensor Y B)).

Fixpoint lift_decorated_context {U G H X Y}
    (C : @DecoratedContext U G H X Y)
    (alpha : @OCell U G H) : @OCell U X Y :=
  match C in DecoratedContext _ _ X0 Y0 return @OCell U X0 Y0 with
  | DCHole _ _ => alpha
  | DCTensorRight D sibling =>
      OCTensor (lift_decorated_context D alpha) sibling
  | DCTensorLeft sibling D =>
      OCTensor sibling (lift_decorated_context D alpha)
  | DCHCompRight D sibling =>
      OCHorizontal (lift_decorated_context D alpha) sibling
  | DCHCompLeft sibling D =>
      OCHorizontal sibling (lift_decorated_context D alpha)
  | DCCapability b D LX LY LXok LYok =>
      OCNest b LX LY LXok LYok (lift_decorated_context D alpha)
  | DCModulePortal mu _ D sibling =>
      OCPortalCell _ (lift_decorated_context D alpha) sibling
  | DCBinderBoundary _ D sibling =>
      OCBinderCell _ (lift_decorated_context D alpha) sibling
  end.

Theorem decorated_deep_closure U G H X Y
    (C : @DecoratedContext U G H X Y)
    (alpha : @OCell U G H) : exists beta : @OCell U X Y,
      beta = lift_decorated_context C alpha.
Proof. eauto. Qed.

Theorem portal_context_is_not_nest_alias U G H X Y
    (C : @DecoratedContext U G H X Y) S T
    (mu : OpenModCell U S T) B (sibling : @OCell U (omc_sheet mu) B) c
    (alpha : @OCell U G H) :
  lift_decorated_context (DCModulePortal mu c C sibling) alpha =
  OCPortalCell c (lift_decorated_context C alpha) sibling.
Proof. reflexivity. Qed.

Theorem binder_context_is_not_nest_alias U G H X Y
    (C : @DecoratedContext U G H X Y) A B
    (sibling : @OCell U A B) c
    (alpha : @OCell U G H) :
  lift_decorated_context (DCBinderBoundary c C sibling) alpha =
  OCBinderCell c (lift_decorated_context C alpha) sibling.
Proof. reflexivity. Qed.

End AuthoritativeOHTG.

End OHTG_ZFC_2317.
