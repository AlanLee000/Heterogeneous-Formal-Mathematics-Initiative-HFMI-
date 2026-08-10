(*
  SRBE-065 / 1787 枚举反射 -- causal strong-mechanism reconstruction.

  SRBE1787.v and SRBE1787Codec.v are retained as the frozen literal/legacy
  layer.  This file repairs the architectural losses identified in the
  faithfulness audit: certificates are dynamically registered checked
  objects, histories generate the Low language, dependency occurrences carry
  the noncommutative transport path, obstacles retain complete rule identity,
  and the application checker consumes one integrated stage capability.
*)

From Stdlib Require Import List Bool Arith PeanoNat Lia.
Require Import SRBE1787 SRBE1787Codec.
Import ListNotations.
Set Implicit Arguments.

Module CausalSRBE.

(** * A. Dynamic certificates with intrinsic dependency transport *)

Record causal_dependency : Type := mkCausalDependency {
  dependency_handle : nat;
  dependency_transport : path_letter
}.

Definition causal_dependency_eqb (d e : causal_dependency) : bool :=
  Nat.eqb (dependency_handle d) (dependency_handle e) &&
  path_letter_eqb (dependency_transport d) (dependency_transport e).

Lemma causal_dependency_eqb_refl : forall d,
  causal_dependency_eqb d d = true.
Proof.
  intros [code transport]. unfold causal_dependency_eqb. cbn.
  rewrite Nat.eqb_refl. destruct transport; reflexivity.
Qed.

Definition causal_dependency_list_eqb := list_eqb causal_dependency_eqb.

Definition dependency_handle_memberb (handle : nat)
    (ds : list causal_dependency) : bool :=
  existsb (fun d => Nat.eqb handle (dependency_handle d)) ds.

Fixpoint dependency_handles_uniqueb (ds : list causal_dependency) : bool :=
  match ds with
  | [] => true
  | d :: rest =>
      negb (dependency_handle_memberb (dependency_handle d) rest) &&
      dependency_handles_uniqueb rest
  end.

Inductive causal_open_tree : Type :=
| CausalHole (index : nat) (label : sch_sequent)
| CausalQAxiom (axiom : formula) (label : sch_sequent)
| CausalGQ (rule : sch_gq_witness) (label : sch_sequent)
           (children : causal_open_forest)
| CausalDepApp (dependency : causal_dependency)
               (rho : sch_instantiation)
               (label : sch_sequent) (children : causal_open_forest)
| CausalPerm (exchanges : list sch_adjacent_exchange)
             (child : causal_open_tree) (label : sch_sequent)
with causal_open_forest : Type :=
| CausalNil
| CausalCons (head : causal_open_tree) (tail : causal_open_forest).

Definition causal_open_root (p : causal_open_tree) : sch_sequent :=
  match p with
  | CausalHole _ lbl | CausalQAxiom _ lbl | CausalGQ _ lbl _
  | CausalDepApp _ _ lbl _ | CausalPerm _ _ lbl => lbl
  end.

Fixpoint causal_forest_roots (ps : causal_open_forest)
    : list sch_sequent :=
  match ps with
  | CausalNil => []
  | CausalCons p qs => causal_open_root p :: causal_forest_roots qs
  end.

Fixpoint causal_open_dependencies (p : causal_open_tree)
    : list causal_dependency :=
  match p with
  | CausalHole _ _ | CausalQAxiom _ _ => []
  | CausalGQ _ _ ps => causal_forest_dependencies ps
  | CausalDepApp d _ _ ps => d :: causal_forest_dependencies ps
  | CausalPerm _ q _ => causal_open_dependencies q
  end
with causal_forest_dependencies (ps : causal_open_forest)
    : list causal_dependency :=
  match ps with
  | CausalNil => []
  | CausalCons p qs =>
      causal_open_dependencies p ++ causal_forest_dependencies qs
  end.

Definition causal_root_resolver := nat -> option rule_scheme.

Fixpoint causal_tree_check (resolve : causal_root_resolver)
    (q : rule_scheme) (p : causal_open_tree) : bool :=
  match p with
  | CausalHole i lbl =>
      match nth_error (scheme_premises q) i with
      | Some target => sch_sequent_eqb lbl target
      | None => false
      end
  | CausalQAxiom A lbl =>
      qaxiomb A &&
      sch_sequent_eqb lbl (mkSchSeq [] [SCFormula (quote_formula A)])
  | CausalGQ w lbl ps =>
      sch_gq_validb w &&
      sch_sequent_list_eqb (causal_forest_roots ps) (sch_gq_premises w) &&
      sch_sequent_eqb lbl (sch_gq_conclusion w) &&
      causal_forest_check resolve q ps
  | CausalDepApp d rho lbl ps =>
      match resolve (dependency_handle d) with
      | None => false
      | Some dependency_root =>
          match sch_instantiate_rule_scheme rho dependency_root with
          | None => false
          | Some instantiated =>
              sch_legal_instantiationb dependency_root rho &&
              sch_sequent_list_eqb (causal_forest_roots ps)
                (scheme_premises instantiated) &&
              sch_sequent_eqb lbl (scheme_conclusion instantiated) &&
              causal_forest_check resolve q ps
          end
      end
  | CausalPerm es child lbl =>
      causal_tree_check resolve q child &&
      match execute_sch_exchanges es (causal_open_root child) with
      | Some target => sch_sequent_eqb target lbl
      | None => false
      end
  end
with causal_forest_check (resolve : causal_root_resolver)
    (q : rule_scheme) (ps : causal_open_forest) : bool :=
  match ps with
  | CausalNil => true
  | CausalCons p qs =>
      causal_tree_check resolve q p && causal_forest_check resolve q qs
  end.

Record causal_certificate : Type := mkCausalCertificate {
  causal_certificate_root : rule_scheme;
  causal_certificate_skeleton : causal_open_tree;
  causal_certificate_dependencies : list causal_dependency
}.

Definition dependency_resolvedb (resolve : causal_root_resolver)
    (d : causal_dependency) : bool :=
  match resolve (dependency_handle d) with
  | Some _ => true
  | None => false
  end.

Definition CausalPCOK (resolve : causal_root_resolver)
    (c : causal_certificate) : bool :=
  let q := causal_certificate_root c in
  let p := causal_certificate_skeleton c in
  let ds := causal_certificate_dependencies c in
  forallb (sch_sequent_wtb 0)
    (scheme_premises q ++ [scheme_conclusion q]) &&
  forallb static_side_conditionb (scheme_conditions q) &&
  causal_tree_check resolve q p &&
  sch_sequent_eqb (causal_open_root p) (scheme_conclusion q) &&
  causal_dependency_list_eqb ds (causal_open_dependencies p) &&
  dependency_handles_uniqueb ds &&
  forallb (dependency_resolvedb resolve) ds.

(** The dependency itinerary is read from the checked skeleton itself.  It is
    not an independent four-letter permission input. *)
Definition certificate_dependency_path (c : causal_certificate)
    : list path_letter :=
  map dependency_transport
    (causal_open_dependencies (causal_certificate_skeleton c)).

Definition certificate_holonomy (c : causal_certificate) : permutation :=
  Hol (certificate_dependency_path c).

(** * B. Reversible structural and arithmetic codes *)

Definition encode_path_letter_code (a : path_letter) : SC.code :=
  match a with
  | LA => SC.CNode 0 []
  | LAMinus => SC.CNode 1 []
  | LB => SC.CNode 2 []
  | LBMinus => SC.CNode 3 []
  end.

Definition decode_path_letter_code (c : SC.code) : option path_letter :=
  match c with
  | SC.CNode 0 [] => Some LA
  | SC.CNode 1 [] => Some LAMinus
  | SC.CNode 2 [] => Some LB
  | SC.CNode 3 [] => Some LBMinus
  | _ => None
  end.

Lemma decode_encode_path_letter_code : forall a,
  decode_path_letter_code (encode_path_letter_code a) = Some a.
Proof. destruct a; reflexivity. Qed.

Definition encode_causal_dependency_code (d : causal_dependency) : SC.code :=
  SC.CNode 0 [SC.CAtom (dependency_handle d);
              encode_path_letter_code (dependency_transport d)].

Definition decode_causal_dependency_code (c : SC.code)
    : option causal_dependency :=
  match c with
  | SC.CNode 0 [SC.CAtom handle; transport] =>
      match decode_path_letter_code transport with
      | Some a => Some (mkCausalDependency handle a)
      | None => None
      end
  | _ => None
  end.

Lemma decode_encode_causal_dependency_code : forall d,
  decode_causal_dependency_code (encode_causal_dependency_code d) = Some d.
Proof.
  intros [code transport]. unfold encode_causal_dependency_code,
    decode_causal_dependency_code. cbn.
  rewrite decode_encode_path_letter_code. reflexivity.
Qed.

Definition encode_causal_dependency_list :=
  SC.encode_code_list encode_causal_dependency_code.
Definition decode_causal_dependency_list :=
  SC.decode_code_list_node decode_causal_dependency_code.

Lemma decode_encode_causal_dependency_list : forall ds,
  decode_causal_dependency_list (encode_causal_dependency_list ds) = Some ds.
Proof.
  apply SC.decode_code_list_node_encode.
  exact decode_encode_causal_dependency_code.
Qed.

Fixpoint encode_causal_open_tree_code (p : causal_open_tree) : SC.code :=
  match p with
  | CausalHole i lbl =>
      SC.CNode 0 [SC.CAtom i; encode_sch_sequent_code lbl]
  | CausalQAxiom A lbl =>
      SC.CNode 1 [encode_formula_code A; encode_sch_sequent_code lbl]
  | CausalGQ w lbl ps =>
      SC.CNode 2 [encode_sch_gq_witness_code w;
                  encode_sch_sequent_code lbl;
                  encode_causal_open_forest_code ps]
  | CausalDepApp d rho lbl ps =>
      SC.CNode 3 [encode_causal_dependency_code d;
                  encode_sch_instantiation_code rho;
                  encode_sch_sequent_code lbl;
                  encode_causal_open_forest_code ps]
  | CausalPerm es child lbl =>
      SC.CNode 4 [encode_exchange_list es;
                  encode_causal_open_tree_code child;
                  encode_sch_sequent_code lbl]
  end
with encode_causal_open_forest_code (ps : causal_open_forest) : SC.code :=
  match ps with
  | CausalNil => SC.CNode 0 []
  | CausalCons p qs =>
      SC.CNode 1 [encode_causal_open_tree_code p;
                  encode_causal_open_forest_code qs]
  end.

Fixpoint decode_causal_open_tree_code (c : SC.code)
    : option causal_open_tree :=
  match c with
  | SC.CNode 0 [SC.CAtom i; lbl] =>
      match decode_sch_sequent_code lbl with
      | Some seq0 => Some (CausalHole i seq0)
      | None => None
      end
  | SC.CNode 1 [A; lbl] =>
      omap2 CausalQAxiom (decode_formula_code A)
        (decode_sch_sequent_code lbl)
  | SC.CNode 2 [w; lbl; ps] =>
      omap3 CausalGQ (decode_sch_gq_witness_code w)
        (decode_sch_sequent_code lbl) (decode_causal_open_forest_code ps)
  | SC.CNode 3 [d; rho; lbl; ps] =>
      omap4 CausalDepApp (decode_causal_dependency_code d)
        (decode_sch_instantiation_code rho) (decode_sch_sequent_code lbl)
        (decode_causal_open_forest_code ps)
  | SC.CNode 4 [es; child; lbl] =>
      omap3 CausalPerm (decode_exchange_list es)
        (decode_causal_open_tree_code child) (decode_sch_sequent_code lbl)
  | _ => None
  end
with decode_causal_open_forest_code (c : SC.code)
    : option causal_open_forest :=
  match c with
  | SC.CNode 0 [] => Some CausalNil
  | SC.CNode 1 [p; ps] =>
      omap2 CausalCons (decode_causal_open_tree_code p)
        (decode_causal_open_forest_code ps)
  | _ => None
  end.

Lemma decode_encode_causal_open_tree_code : forall p,
  decode_causal_open_tree_code (encode_causal_open_tree_code p) = Some p
with decode_encode_causal_open_forest_code : forall ps,
  decode_causal_open_forest_code (encode_causal_open_forest_code ps) = Some ps.
Proof.
  - intro p. destruct p as
      [index label | axiom label | rule label children |
       dependency rho label children | exchanges child label].
    + change
        (match decode_sch_sequent_code (encode_sch_sequent_code label) with
         | Some seq0 => Some (CausalHole index seq0)
         | None => None
         end = Some (CausalHole index label)).
      rewrite decode_encode_sch_sequent_code. reflexivity.
    + change
        (omap2 CausalQAxiom
          (decode_formula_code (encode_formula_code axiom))
          (decode_sch_sequent_code (encode_sch_sequent_code label)) =
         Some (CausalQAxiom axiom label)).
      rewrite decode_encode_formula_code,
        decode_encode_sch_sequent_code. reflexivity.
    + change
        (omap3 CausalGQ
          (decode_sch_gq_witness_code (encode_sch_gq_witness_code rule))
          (decode_sch_sequent_code (encode_sch_sequent_code label))
          (decode_causal_open_forest_code
             (encode_causal_open_forest_code children)) =
         Some (CausalGQ rule label children)).
      rewrite decode_encode_sch_gq_witness_code,
        decode_encode_sch_sequent_code,
        decode_encode_causal_open_forest_code. reflexivity.
    + change
        (omap4 CausalDepApp
          (decode_causal_dependency_code
             (encode_causal_dependency_code dependency))
          (decode_sch_instantiation_code
             (encode_sch_instantiation_code rho))
          (decode_sch_sequent_code (encode_sch_sequent_code label))
          (decode_causal_open_forest_code
             (encode_causal_open_forest_code children)) =
         Some (CausalDepApp dependency rho label children)).
      rewrite decode_encode_causal_dependency_code,
        decode_encode_sch_instantiation_code,
        decode_encode_sch_sequent_code,
        decode_encode_causal_open_forest_code. reflexivity.
    + change
        (omap3 CausalPerm
          (decode_exchange_list (encode_exchange_list exchanges))
          (decode_causal_open_tree_code
             (encode_causal_open_tree_code child))
          (decode_sch_sequent_code (encode_sch_sequent_code label)) =
         Some (CausalPerm exchanges child label)).
      rewrite decode_encode_exchange_list,
        decode_encode_causal_open_tree_code,
        decode_encode_sch_sequent_code. reflexivity.
  - intro ps. destruct ps as [|head tail].
    + reflexivity.
    + change
        (omap2 CausalCons
          (decode_causal_open_tree_code
             (encode_causal_open_tree_code head))
          (decode_causal_open_forest_code
             (encode_causal_open_forest_code tail)) =
         Some (CausalCons head tail)).
      rewrite decode_encode_causal_open_tree_code,
        decode_encode_causal_open_forest_code. reflexivity.
Qed.

Definition encode_causal_certificate_code (c : causal_certificate) : SC.code :=
  SC.CNode 0 [encode_rule_scheme_code (causal_certificate_root c);
              encode_causal_open_tree_code (causal_certificate_skeleton c);
              encode_causal_dependency_list
                (causal_certificate_dependencies c)].

Definition decode_causal_certificate_code (c : SC.code)
    : option causal_certificate :=
  match c with
  | SC.CNode 0 [q; p; ds] =>
      omap3 mkCausalCertificate (decode_rule_scheme_code q)
        (decode_causal_open_tree_code p) (decode_causal_dependency_list ds)
  | _ => None
  end.

Lemma decode_encode_causal_certificate_code : forall c,
  decode_causal_certificate_code (encode_causal_certificate_code c) = Some c.
Proof.
  intros [q p ds]. unfold encode_causal_certificate_code,
    decode_causal_certificate_code.
  change
    (omap3 mkCausalCertificate
       (decode_rule_scheme_code (encode_rule_scheme_code q))
       (decode_causal_open_tree_code (encode_causal_open_tree_code p))
       (decode_causal_dependency_list
          (encode_causal_dependency_list ds)) =
     Some (mkCausalCertificate q p ds)).
  rewrite decode_encode_rule_scheme_code,
    decode_encode_causal_open_tree_code,
    decode_encode_causal_dependency_list. reflexivity.
Qed.

Definition encode_causal_certificate_nat (c : causal_certificate) : nat :=
  pack_code (encode_causal_certificate_code c).

Definition decode_causal_certificate_nat (n : nat)
    : option causal_certificate :=
  match unpack_code n with
  | Some c => decode_causal_certificate_code c
  | None => None
  end.

Lemma decode_encode_causal_certificate_nat : forall c,
  decode_causal_certificate_nat (encode_causal_certificate_nat c) = Some c.
Proof.
  intro c. unfold decode_causal_certificate_nat,
    encode_causal_certificate_nat. rewrite unpack_pack_code.
  apply decode_encode_causal_certificate_code.
Qed.

Lemma encode_causal_certificate_nat_injective : forall c d,
  encode_causal_certificate_nat c = encode_causal_certificate_nat d -> c = d.
Proof.
  intros c d H.
  pose proof (decode_encode_causal_certificate_nat c) as Hc.
  pose proof (decode_encode_causal_certificate_nat d) as Hd.
  rewrite H in Hc. rewrite Hd in Hc. inversion Hc. reflexivity.
Qed.

(** * C. Checker-caused dynamic registration history *)

Record registration_event : Type := mkRegistrationEvent {
  event_handle : nat;
  event_certificate : causal_certificate
}.

Definition causal_history := list registration_event.

Fixpoint history_lookup (H : causal_history) (handle : nat)
    : option registration_event :=
  match H with
  | [] => None
  | event :: rest =>
      if Nat.eqb (event_handle event) handle
      then Some event else history_lookup rest handle
  end.

Definition history_root (H : causal_history) : causal_root_resolver :=
  fun handle =>
    match history_lookup H handle with
    | Some event => Some (causal_certificate_root (event_certificate event))
    | None => None
    end.

Definition history_containsb (H : causal_history) (handle : nat) : bool :=
  match history_lookup H handle with Some _ => true | None => false end.

Definition causal_dependencies_availableb (H : causal_history)
    (c : causal_certificate) : bool :=
  forallb
    (fun d => history_containsb H (dependency_handle d))
    (causal_certificate_dependencies c).

Definition registerableb (H : causal_history) (event : registration_event) : bool :=
  let c := event_certificate event in
  negb (history_containsb H (event_handle event)) &&
  CausalPCOK (history_root H) c &&
  causal_dependencies_availableb H c.

Definition register_checked (H : causal_history) (event : registration_event)
    : option causal_history :=
  if registerableb H event then Some (H ++ [event]) else None.

Fixpoint history_valid_from (prefix pending : causal_history) : bool :=
  match pending with
  | [] => true
  | event :: rest =>
      registerableb prefix event &&
      history_valid_from (prefix ++ [event]) rest
  end.

Definition history_validb (H : causal_history) : bool :=
  history_valid_from [] H.

Theorem successful_registration_requires_full_checker : forall H event H',
  register_checked H event = Some H' ->
  CausalPCOK (history_root H) (event_certificate event) = true /\
  causal_dependencies_availableb H (event_certificate event) = true /\
  H' = H ++ [event].
Proof.
  intros H event H'. unfold register_checked.
  destruct (registerableb H event) eqn:Hreg; try discriminate.
  intro Hresult. inversion Hresult; subst H'.
  unfold registerableb in Hreg.
  repeat rewrite andb_true_iff in Hreg.
  tauto.
Qed.

(** * D. History-generated Low resources and language *)

Record low_resource : Type := mkLowResource {
  resource_source : nat;
  resource_handle : nat
}.

Definition resource_event (H : causal_history) (r : low_resource)
    : option registration_event := history_lookup H (resource_handle r).

Definition resource_rule (H : causal_history) (r : low_resource)
    : option rule_scheme :=
  match resource_event H r with
  | Some event => Some (causal_certificate_root (event_certificate event))
  | None => None
  end.

Definition resource_rule_code (H : causal_history) (r : low_resource)
    : option nat :=
  match resource_rule H r with
  | Some q => Some (encode_rule_scheme_nat q)
  | None => None
  end.

Definition resource_certificate_number (H : causal_history) (r : low_resource)
    : option nat :=
  match resource_event H r with
  | Some event =>
      Some (encode_causal_certificate_nat (event_certificate event))
  | None => None
  end.

Fixpoint indexed_resources_from (source : nat) (H : causal_history)
    : list low_resource :=
  match H with
  | [] => []
  | event :: rest =>
      mkLowResource source (event_handle event) ::
      indexed_resources_from (S source) rest
  end.

Definition stage_resources (H : causal_history) (k : nat)
    : list low_resource :=
  indexed_resources_from 0 (firstn k H).

Definition low_resource_eqb (r s : low_resource) : bool :=
  Nat.eqb (resource_source r) (resource_source s) &&
  Nat.eqb (resource_handle r) (resource_handle s).

Lemma low_resource_eqb_refl : forall r, low_resource_eqb r r = true.
Proof.
  intros [source handle]. unfold low_resource_eqb. cbn.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Definition low_resource_validb (H : causal_history) (k : nat)
    (r : low_resource) : bool :=
  existsb (low_resource_eqb r) (stage_resources H k).

Definition Low_semantics (H : causal_history) (k : nat)
    (r : low_resource) : Prop :=
  history_validb (firstn k H) = true /\
  In r (stage_resources H k).

Record stage_capability (H : causal_history) (k : nat) : Type :=
  mkStageCapability {
    capability_resource : low_resource;
    capability_history_checked : history_validb (firstn k H) = true;
    capability_registered : low_resource_validb H k capability_resource = true
  }.

Definition Low (H : causal_history) (k : nat) : Type := stage_capability H k.
Definition ListLow (H : causal_history) (k : nat) : Type := list (Low H k).

Definition causal_enum (H : causal_history) (k n : nat)
    : list low_resource :=
  firstn (S n) (stage_resources H k).

Lemma firstn_membership : forall (A : Type) n (xs : list A) x,
  In x (firstn n xs) -> In x xs.
Proof.
  intros A n. induction n as [|n IH]; intros xs x H.
  - cbn in H. contradiction.
  - destruct xs as [|y ys]; cbn in *.
    + contradiction.
    + destruct H as [->|H].
      * left. reflexivity.
      * right. apply IH with (xs := ys). exact H.
Qed.

Theorem causal_enum_is_object_level : forall H k n r,
  history_validb (firstn k H) = true ->
  In r (causal_enum H k n) -> Low_semantics H k r.
Proof.
  intros H k n r Hvalid Hin. split; [exact Hvalid|].
  unfold causal_enum in Hin. apply firstn_membership in Hin. exact Hin.
Qed.

Example a_handle_without_history_is_not_a_Low_resource :
  low_resource_validb [] 1 (mkLowResource 0 20) = false.
Proof. reflexivity. Qed.

(** An actual stage constant is generated by a checked Low carrier element;
    there is no constructor taking only a natural-number certificate code. *)
Inductive generated_low_constant (H : causal_history) (k : nat) : Type :=
| GeneratedLowConstant (capability : stage_capability H k).

Definition low_constant_authorizedb (H : causal_history) (k source root cert : nat)
    : bool :=
  existsb
    (fun r =>
       match resource_rule_code H r, resource_certificate_number H r with
       | Some rule_code, Some certificate_number =>
           Nat.eqb source (resource_source r) &&
           Nat.eqb root rule_code &&
           Nat.eqb cert certificate_number
       | _, _ => false
       end)
    (stage_resources H k).

Definition history_fsym_allowedb (H : causal_history) (k : nat)
    (f : fsym) : bool :=
  match f with
  | FLowConst j source root cert =>
      Nat.eqb j k && low_constant_authorizedb H k source root cert
  | _ => fsym_allowedb k f
  end.

Fixpoint history_term_closedb (H : causal_history) (k : nat) (t : term) : bool :=
  match t with
  | TVar _ _ => true
  | TFun f ts => history_fsym_allowedb H k f && history_terms_closedb H k ts
  end
with history_terms_closedb (H : causal_history) (k : nat) (ts : terms) : bool :=
  match ts with
  | TNil => true
  | TCons t us => history_term_closedb H k t && history_terms_closedb H k us
  end.

Fixpoint history_surface_closedb (H : causal_history) (k : nat)
    (A : sformula) : bool :=
  match A with
  | SFBot => true
  | SFEq _ t u => history_term_closedb H k t && history_term_closedb H k u
  | SFRel _ ts => history_terms_closedb H k ts
  | SFAnd B C | SFOr B C | SFImp B C =>
      history_surface_closedb H k B && history_surface_closedb H k C
  | SFAll _ B | SFEx _ B | OwnAll _ B => history_surface_closedb H k B
  end.

(** * E. Feedback barriers and adapters over complete rule identities *)

Record causal_obstacle : Type := mkCausalObstacle {
  obstacle_emitter : low_resource
}.

Definition obstacle_rule_identity (H : causal_history) (o : causal_obstacle)
    : option rule_scheme := resource_rule H (obstacle_emitter o).

Definition emitted_obstacles (H : causal_history) (k : nat)
    : list causal_obstacle :=
  map mkCausalObstacle (stage_resources H k).

Definition causal_barriers (tau : timing) (H : causal_history) (k : nat)
    : list causal_obstacle :=
  match tau with
  | Delayed => emitted_obstacles H (Nat.pred k)
  | Immediate => emitted_obstacles H k
  | Ablated => []
  end.

Definition adapter_coversb (o : causal_obstacle)
    (adapter : list low_resource) : bool :=
  existsb (low_resource_eqb (obstacle_emitter o)) adapter.

Definition causal_Adapt (H : causal_history) (k : nat)
    (B : list causal_obstacle) (q : rule_scheme)
    (adapter : list low_resource) : bool :=
  forallb (low_resource_validb H k) adapter &&
  forallb
    (fun o =>
       match obstacle_rule_identity H o with
       | Some obstacle_rule =>
           negb (rule_scheme_eqb q obstacle_rule) || adapter_coversb o adapter
       | None => false
       end)
    B.

(** * F. Dependency-derived one-beat ownership and formation *)

Definition causal_omega (H : causal_history) (k : nat) (r : low_resource)
    : option ownership :=
  match resource_event H r with
  | None => None
  | Some event =>
      if Nat.leb (S (S (resource_source r))) k
      then Some (ownership_action
        (certificate_holonomy (event_certificate event)) Omega0)
      else Some Omega0
  end.

Definition causal_formationb (H : causal_history) (k : nat)
    (r : low_resource) (Xi : assignment_context) (A : sformula) : bool :=
  history_validb (firstn k H) &&
  low_resource_validb H k r &&
  history_surface_closedb H k A &&
  match causal_omega H k r with
  | Some omega => FCHK_H k omega Xi A
  | None => false
  end.

(** * G. One combined obstacle-adapter-formation-application interface *)

Record causal_application : Type := mkCausalApplication {
  application_capability : low_resource;
  application_rule_identity : rule_scheme;
  application_instantiation : instantiation;
  application_adapter : list low_resource;
  application_surface : sformula;
  application_assignment : assignment_context;
  application_premises : list sequent;
  application_conclusion : sequent
}.

Definition formula_in_contextb (A : formula) (G : context) : bool :=
  existsb (formula_eqb A) G.

Definition conclusion_mentions_surfaceb (app : causal_application) : bool :=
  let A := UNDER (application_surface app) in
  formula_in_contextb A (antecedent (application_conclusion app)) ||
  formula_in_contextb A (succedent (application_conclusion app)).

Definition registration_authorityb (H : causal_history) (k : nat)
    (r : low_resource) : bool :=
  let prior := firstn (resource_source r) H in
  match resource_event H r with
  | None => false
  | Some event =>
      low_resource_validb H k r &&
      CausalPCOK (history_root prior) (event_certificate event) &&
      causal_dependencies_availableb prior (event_certificate event)
  end.

Definition instantiated_shape_matchesb (app : causal_application) : bool :=
  match instantiate_sequents (application_instantiation app)
          (scheme_premises (application_rule_identity app)),
        instantiate_sequent (application_instantiation app)
          (scheme_conclusion (application_rule_identity app)) with
  | Some premises, Some conclusion =>
      list_eqb sequent_eqb premises (application_premises app) &&
      sequent_eqb conclusion (application_conclusion app)
  | _, _ => false
  end.

Definition causal_application_guardb (H : causal_history) (k : nat)
    (tau : timing) (app : causal_application) : bool :=
  let r := application_capability app in
  let q := application_rule_identity app in
  history_validb (firstn k H) &&
  registration_authorityb H k r &&
  match resource_rule H r with
  | None => false
  | Some registered_rule =>
      rule_scheme_eqb q registered_rule &&
      legal_instantiationb k q (application_instantiation app) &&
      causal_Adapt H k (causal_barriers tau H k) q
        (application_adapter app) &&
      causal_formationb H k r (application_assignment app)
        (application_surface app) &&
      conclusion_mentions_surfaceb app
  end.

Definition causal_application_check (H : causal_history) (k : nat)
    (tau : timing) (app : causal_application) : bool :=
  causal_application_guardb H k tau app && instantiated_shape_matchesb app.

Definition execute_with_capabilityb {H : causal_history} {k : nat}
    (cap : stage_capability H k) (tau : timing)
    (q : rule_scheme) (sigma : instantiation)
    (adapter : list low_resource) (A : sformula)
    (Xi : assignment_context) (premises : list sequent) (conclusion : sequent)
    : bool :=
  causal_application_check H k tau
    (mkCausalApplication (capability_resource cap) q sigma adapter A Xi
       premises conclusion).

Theorem checked_application_uses_joint_authority : forall H k tau app,
  causal_application_check H k tau app = true ->
  history_validb (firstn k H) = true /\
  registration_authorityb H k (application_capability app) = true /\
  match resource_rule H (application_capability app) with
  | None => False
  | Some registered_rule =>
    rule_scheme_eqb (application_rule_identity app) registered_rule = true /\
  legal_instantiationb k (application_rule_identity app)
    (application_instantiation app) = true /\
  causal_Adapt H k (causal_barriers tau H k)
    (application_rule_identity app) (application_adapter app) = true /\
  causal_formationb H k (application_capability app)
    (application_assignment app) (application_surface app) = true /\
  conclusion_mentions_surfaceb app = true /\
  instantiated_shape_matchesb app = true
  end.
Proof.
  intros H k tau app Hcheck.
  unfold causal_application_check in Hcheck.
  apply andb_true_iff in Hcheck as [Hguard Hshape].
  unfold causal_application_guardb in Hguard.
  apply andb_true_iff in Hguard as [Hprefix Hguard].
  apply andb_true_iff in Hprefix as [Hhistory Hauthority].
  destruct (resource_rule H (application_capability app)) as [q|];
    try discriminate.
  repeat rewrite andb_true_iff in Hguard. tauto.
Qed.

(** * H. Dynamic noncommutative branches used as executable regression tests *)

Definition generator_tag (a : path_letter) : nat :=
  match a with LA => 100 | LAMinus => 101 | LB => 102 | LBMinus => 103 end.

Definition generator_certificate (a : path_letter) : causal_certificate :=
  mkCausalCertificate (identity_scheme (generator_tag a))
    (CausalHole 0 sch_H) [].

Definition generator_handle (a : path_letter) : nat :=
  match a with LA => 10 | LAMinus => 11 | LB => 12 | LBMinus => 13 end.

Definition generator_event (a : path_letter) : registration_event :=
  mkRegistrationEvent (generator_handle a) (generator_certificate a).

Definition dependency_of_letter (a : path_letter) : causal_dependency :=
  mkCausalDependency (generator_handle a) a.

Fixpoint install_dependency_chain (ds : list causal_dependency)
    (base : causal_open_tree) : causal_open_tree :=
  match ds with
  | [] => base
  | d :: rest =>
      CausalDepApp d qn_schematic_identity sch_H
        (CausalCons (install_dependency_chain rest base) CausalNil)
  end.

Definition path_certificate (p : list path_letter) : causal_certificate :=
  let ds := map dependency_of_letter p in
  mkCausalCertificate (identity_scheme 200)
    (install_dependency_chain ds (CausalHole 0 sch_H)) ds.

Lemma installed_dependencies : forall ds base,
  causal_open_dependencies (install_dependency_chain ds base) =
  ds ++ causal_open_dependencies base.
Proof.
  intro ds. induction ds as [|d ds IH]; intro base.
  - reflexivity.
  - cbn. rewrite IH, app_nil_r. reflexivity.
Qed.

Theorem path_certificate_retains_order : forall p,
  certificate_dependency_path (path_certificate p) = p.
Proof.
  intro p. unfold certificate_dependency_path, path_certificate.
  cbn [causal_certificate_skeleton].
  rewrite installed_dependencies, app_nil_r.
  induction p as [|a rest IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Definition generator_history : causal_history :=
  map generator_event [LA; LAMinus; LB; LBMinus].

Definition path_event (p : list path_letter) : registration_event :=
  mkRegistrationEvent 20 (path_certificate p).

Definition pi0_history : causal_history :=
  generator_history ++ [path_event pi_0].

Definition pih_history : causal_history :=
  generator_history ++ [path_event pi_h].

Definition pi0_resource : low_resource :=
  mkLowResource 4 20.

Definition pih_resource : low_resource :=
  mkLowResource 4 20.

Example generator_history_checks : history_validb generator_history = true.
Proof. vm_compute. reflexivity. Qed.

Example pi0_dynamic_registration_checks :
  register_checked generator_history (path_event pi_0) =
  Some pi0_history.
Proof. vm_compute. reflexivity. Qed.

Example pih_dynamic_registration_checks :
  register_checked generator_history (path_event pi_h) =
  Some pih_history.
Proof. vm_compute. reflexivity. Qed.

Example pi0_history_checks : history_validb pi0_history = true.
Proof. vm_compute. reflexivity. Qed.

Example pih_history_checks : history_validb pih_history = true.
Proof. vm_compute. reflexivity. Qed.

Theorem pi0_holonomy_is_intrinsic :
  certificate_holonomy (path_certificate pi_0) = Hol pi_0.
Proof. unfold certificate_holonomy. rewrite path_certificate_retains_order.
  reflexivity. Qed.

Theorem pih_holonomy_is_intrinsic :
  certificate_holonomy (path_certificate pi_h) = Hol pi_h.
Proof. unfold certificate_holonomy. rewrite path_certificate_retains_order.
  reflexivity. Qed.

Example causal_pi0_owner_x :
  exists omega,
    causal_omega pi0_history 6 pi0_resource = Some omega /\
    ownership_lookup omega VX = Owner0.
Proof. eexists. split; vm_compute; reflexivity. Qed.

Example causal_pih_owner_x :
  exists omega,
    causal_omega pih_history 6 pih_resource = Some omega /\
    ownership_lookup omega VX = Owner2.
Proof. eexists. split; vm_compute; reflexivity. Qed.

Definition qx_core : formula := UNDER Q_x.
Definition qx_sequent : sequent := mkSeq [qx_core] [qx_core].
Definition qx_instantiation : instantiation :=
  mkInst [] [] [(0, [qx_core]); (1, [qx_core])].

Definition pi0_application : causal_application :=
  mkCausalApplication pi0_resource (identity_scheme 200) qx_instantiation
    [pi0_resource] Q_x [] [qx_sequent] qx_sequent.

Definition pih_application : causal_application :=
  mkCausalApplication pih_resource (identity_scheme 200) qx_instantiation
    [pih_resource] Q_x [] [qx_sequent] qx_sequent.

Definition pi0_application_without_adapter : causal_application :=
  mkCausalApplication pi0_resource (identity_scheme 200) qx_instantiation
    [] Q_x [] [qx_sequent] qx_sequent.

Definition same_tag_wrong_rule : rule_scheme :=
  mkScheme 200 [] sch_H [].

Definition pi0_application_with_tag_only : causal_application :=
  mkCausalApplication pi0_resource same_tag_wrong_rule qx_instantiation
    [pi0_resource] Q_x [] [qx_sequent] qx_sequent.

Example integrated_pi0_application_accepts :
  causal_application_check pi0_history 6 Delayed pi0_application = true.
Proof. vm_compute. reflexivity. Qed.

Example intrinsic_holonomy_rejects_pih_formation :
  causal_application_check pih_history 6 Delayed pih_application = false.
Proof. vm_compute. reflexivity. Qed.

Example feedback_requires_registered_adapter :
  causal_application_check pi0_history 6 Delayed
    pi0_application_without_adapter = false.
Proof. vm_compute. reflexivity. Qed.

Example full_rule_identity_is_not_a_tag :
  scheme_tag same_tag_wrong_rule = scheme_tag (identity_scheme 200) /\
  causal_application_check pi0_history 6 Delayed
    pi0_application_with_tag_only = false.
Proof. split; vm_compute; reflexivity. Qed.

(** * I. Arithmetic representation is not execution authority *)

Definition causally_represented_certificate (n : nat) : Prop :=
  exists c, decode_causal_certificate_nat n = Some c.

Theorem every_causal_certificate_has_an_arithmetic_representation : forall c,
  causally_represented_certificate (encode_causal_certificate_nat c).
Proof.
  intro c. exists c. apply decode_encode_causal_certificate_nat.
Qed.

Theorem empty_stage_has_no_capability : stage_capability [] 0 -> False.
Proof.
  intros [r Hhistory Hregistered]. cbn in Hregistered. discriminate.
Qed.

Theorem no_uniform_code_to_execution_capability :
  ~ exists decode : forall (H : causal_history) (k : nat),
      nat -> stage_capability H k, True.
Proof.
  intros [decode _].
  exact (empty_stage_has_no_capability (decode [] 0 0)).
Qed.

Theorem representation_does_not_grant_empty_stage_authority : forall c,
  decode_causal_certificate_nat (encode_causal_certificate_nat c) = Some c /\
  ~ exists cap : stage_capability [] 0,
      resource_certificate_number [] (capability_resource cap) =
      Some (encode_causal_certificate_nat c).
Proof.
  intro c. split.
  - apply decode_encode_causal_certificate_nat.
  - intros [cap _]. exact (empty_stage_has_no_capability cap).
Qed.

Theorem causal_operational_semantics_nontrivial :
  causal_application_check pi0_history 6 Delayed pi0_application = true /\
  causal_application_check pih_history 6 Delayed pih_application = false.
Proof.
  split.
  - exact integrated_pi0_application_accepts.
  - exact intrinsic_holonomy_rejects_pih_formation.
Qed.

(** * J. Authoritative reconstructed package *)

Record causal_srbe_system : Type := mkCausalSRBESystem {
  causal_sys_certificate : Type;
  causal_sys_structural_code : causal_sys_certificate -> SC.code;
  causal_sys_arithmetic_code : causal_sys_certificate -> nat;
  causal_sys_pcok : causal_root_resolver -> causal_sys_certificate -> bool;
  causal_sys_event : Type;
  causal_sys_event_handle : causal_sys_event -> nat;
  causal_sys_event_certificate : causal_sys_event -> causal_sys_certificate;
  causal_sys_history : Type;
  causal_sys_register : causal_sys_history -> causal_sys_event ->
                        option causal_sys_history;
  causal_sys_history_valid : causal_sys_history -> bool;
  causal_sys_low_resource : Type;
  causal_sys_stage_resources : causal_sys_history -> nat ->
                               list causal_sys_low_resource;
  causal_sys_barriers : timing -> causal_sys_history -> nat ->
                        list causal_obstacle;
  causal_sys_dependency_path : causal_sys_certificate -> list path_letter;
  causal_sys_holonomy : causal_sys_certificate -> permutation;
  causal_sys_formation : causal_sys_history -> nat -> causal_sys_low_resource ->
                         assignment_context -> sformula -> bool;
  causal_sys_application : Type;
  causal_sys_execute : causal_sys_history -> nat -> timing ->
                       causal_sys_application -> bool;
  causal_sys_operational_nontrivial :
    causal_application_check pi0_history 6 Delayed pi0_application = true /\
    causal_application_check pih_history 6 Delayed pih_application = false
}.

Definition SRBE_065_Causal : causal_srbe_system :=
  {| causal_sys_certificate := causal_certificate;
     causal_sys_structural_code := encode_causal_certificate_code;
     causal_sys_arithmetic_code := encode_causal_certificate_nat;
     causal_sys_pcok := CausalPCOK;
     causal_sys_event := registration_event;
     causal_sys_event_handle := event_handle;
     causal_sys_event_certificate := event_certificate;
     causal_sys_history := causal_history;
     causal_sys_register := register_checked;
     causal_sys_history_valid := history_validb;
     causal_sys_low_resource := low_resource;
     causal_sys_stage_resources := stage_resources;
     causal_sys_barriers := causal_barriers;
     causal_sys_dependency_path := certificate_dependency_path;
     causal_sys_holonomy := certificate_holonomy;
     causal_sys_formation := causal_formationb;
     causal_sys_application := causal_application;
     causal_sys_execute := causal_application_check;
     causal_sys_operational_nontrivial :=
       causal_operational_semantics_nontrivial |}.

End CausalSRBE.
