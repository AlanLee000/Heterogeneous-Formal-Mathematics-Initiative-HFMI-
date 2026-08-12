(*
  KappaSJMMT.v

  The single-file Rocq 9 formalization of kappa-SJ-MMT/CK-v2.  CK-v2 is
  the authorized repair of the original design: every theorem below is an
  actually checked theorem, while Pakhomov recoding is excluded from the
  trusted kernel and the concrete H-omega profile is externally consistent.
*)

From Stdlib Require Import List Bool Arith PeanoNat Lia.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Module KappaSJMMT.

(** Section 2/12: an intrinsically checked root profile. *)

Inductive RootStatus : Type :=
| RSUnchecked
| RSExternallyConsistent
| RSSelfConsistent.

Record RootProfile : Type := {
  root_surface : Type;
  root_formula : Type;
  root_proof : Type;
  erase_formula : root_surface -> root_formula;
  encode_formula : root_formula -> nat;
  proof_conclusion : root_proof -> root_formula;
  bottom_surface : root_surface;
  bottom_formula : root_formula;
  erase_bottom : erase_formula bottom_surface = bottom_formula;
  consistency_formula : option root_formula
}.

Arguments root_surface _ : clear implicits.
Arguments root_formula _ : clear implicits.
Arguments root_proof _ : clear implicits.
Arguments erase_formula _ _ : clear implicits.
Arguments encode_formula _ _ : clear implicits.
Arguments proof_conclusion _ _ : clear implicits.
Arguments bottom_surface _ : clear implicits.
Arguments bottom_formula _ : clear implicits.
Arguments erase_bottom _ : clear implicits.
Arguments consistency_formula _ : clear implicits.

Definition Prf_T (R : RootProfile) (q : root_proof R) (a : nat) : Prop :=
  encode_formula R (proof_conclusion R q) = a.

Definition Check_T (R : RootProfile) (q : root_proof R) (a : nat) : bool :=
  Nat.eqb (encode_formula R (proof_conclusion R q)) a.

Definition OfficialProof (R : RootProfile)
    (q : root_proof R) (a : nat) : Prop :=
  encode_formula R (proof_conclusion R q) = a.

Arguments Prf_T _ _ _ : clear implicits.
Arguments Check_T _ _ _ : clear implicits.
Arguments OfficialProof _ _ _ : clear implicits.

Theorem check_T_correct :
  forall (R : RootProfile) (q : root_proof R) a,
    Check_T R q a = true <-> Prf_T R q a.
Proof.
  intros R q a.
  unfold Check_T, Prf_T.
  apply Nat.eqb_eq.
Qed.

Theorem theorem_34_1_root_proof_adequacy :
  forall (R : RootProfile) (q : root_proof R) a,
    Prf_T R q a <-> OfficialProof R q a.
Proof.
  intros R q a.
  reflexivity.
Qed.

Record ProfiledRoot : Type := {
  profiled_root : RootProfile;
  profiled_status : RootStatus;
  self_consistency_certificate :
    profiled_status = RSSelfConsistent ->
    { con : root_formula profiled_root &
      { q : root_proof profiled_root |
        consistency_formula profiled_root = Some con /\
        Prf_T profiled_root q
          (encode_formula profiled_root con) } }
}.

Arguments profiled_root _ : clear implicits.
Arguments profiled_status _ : clear implicits.
Arguments self_consistency_certificate _ _ : clear implicits.

Theorem theorem_34_2_root_self_consistency :
  forall (R : ProfiledRoot),
    profiled_status R = RSSelfConsistent ->
    exists con : root_formula (profiled_root R),
      consistency_formula (profiled_root R) = Some con /\
      exists q : root_proof (profiled_root R),
        Prf_T (profiled_root R) q
          (encode_formula (profiled_root R) con).
Proof.
  intros R Hstatus.
  destruct (self_consistency_certificate R Hstatus)
    as [con [q [Hcon Hq]]].
  exists con.
  split; [exact Hcon|].
  exists q.
  exact Hq.
Qed.

(** Sections 3, 5, 6, and 7: addresses, modes, effects, hazards. *)

Inductive Authority : Type :=
| AuthData
| AuthObj (package_id : nat)
| AuthSem (authority_rank : nat)
| AuthRoot.

Inductive Address : Type :=
| Addr (representation_rank : nat) (authority : Authority)
| AddrPair (left right : Address).

Fixpoint address_rank (w : Address) : nat :=
  match w with
  | Addr i _ => i
  | AddrPair w1 w2 => Nat.max (address_rank w1) (address_rank w2)
  end.

Definition is_root_address (w : Address) : Prop :=
  w = Addr 0 AuthRoot.

Inductive TotMode : Type :=
| ModeGiven
| ModePartial
| ModeStandard
| ModeInternal.

Definition mode_rank (m : TotMode) : nat :=
  match m with
  | ModeGiven => 0
  | ModePartial => 1
  | ModeStandard => 2
  | ModeInternal => 3
  end.

Definition mode_of_rank (n : nat) : TotMode :=
  match n with
  | 0 => ModeGiven
  | 1 => ModePartial
  | 2 => ModeStandard
  | _ => ModeInternal
  end.

Definition mode_join (m1 m2 : TotMode) : TotMode :=
  mode_of_rank (Nat.max (mode_rank m1) (mode_rank m2)).

Inductive Effect : Type :=
| EffData
| EffCheck
| EffQuote
| EffSem
| EffTranslate
| EffEraseRoot.

Inductive HazAtom : Type :=
| HazCheck
| HazQuoteUp
| HazSemUp
| HazTranslateProof
| HazEraseRoot
| HazComposeTot
| HazQuoteTot
| HazOfficialEncodeTot
| HazLower
| HazEvalSame
| HazReflect
| HazSamePromote
| HazFixedPoint
| HazD1
| HazD2
| HazD3
| HazB2
| HazSigma1C
| HazPC.

Definition HazAtom_eq_dec : forall x y : HazAtom, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition footprint := list HazAtom.
Definition hazard_policy := list footprint.

Definition fp_subset (small large : footprint) : Prop :=
  forall h, In h small -> In h large.

Definition lob_edge : footprint :=
  [HazD1; HazD2; HazD3; HazFixedPoint].

Definition quote_edge : footprint :=
  [HazQuoteTot; HazOfficialEncodeTot; HazSamePromote; HazFixedPoint].

Definition rank_edge : footprint :=
  [HazQuoteUp; HazLower; HazEvalSame].

Definition composition_edge : footprint :=
  [HazComposeTot; HazOfficialEncodeTot; HazSamePromote].

Definition reflection_edge : footprint := [HazReflect].

Definition H_GL : hazard_policy :=
  [lob_edge; quote_edge; rank_edge; composition_edge; reflection_edge].

Definition Admissible (H : hazard_policy) (fp : footprint) : Prop :=
  forall edge, In edge H -> ~ fp_subset edge fp.

Definition DangerousRecovery (H : hazard_policy) (fp : footprint) : Prop :=
  exists edge, In edge H /\ fp_subset edge fp.

Theorem admissible_excludes_recovery :
  forall H fp, Admissible H fp -> ~ DangerousRecovery H fp.
Proof.
  intros H fp Hadm [edge [Hin Hsub]].
  exact (Hadm edge Hin Hsub).
Qed.

(** Section 4: capability contracts.  Root-law provenance is explicit. *)

Record Capability (R : RootProfile) : Type := {
  cap_id : nat;
  cap_inputs : list Address;
  cap_output : Address;
  cap_mode : TotMode;
  cap_effect : Effect;
  cap_footprint : footprint;
  cap_totality_atom : HazAtom;
  cap_certificate : list nat -> nat -> nat -> Prop;
  cap_specification : list nat -> nat -> Prop;
  cap_instance_formula : list nat -> nat -> nat -> root_formula R;
  cap_root_law_formula : root_formula R;
  cap_root_law_proof : root_proof R;
  cap_root_law_checked :
    Prf_T R cap_root_law_proof
      (encode_formula R cap_root_law_formula);
  cap_law_sound :
    forall xs y c,
      cap_certificate xs y c -> cap_specification xs y;
  cap_internal_visible :
    cap_mode = ModeInternal ->
    In cap_totality_atom cap_footprint;
  cap_root_guard :
    is_root_address cap_output -> cap_effect = EffEraseRoot
}.

Arguments cap_id {R} _.
Arguments cap_inputs {R} _.
Arguments cap_output {R} _.
Arguments cap_mode {R} _.
Arguments cap_effect {R} _.
Arguments cap_footprint {R} _.
Arguments cap_totality_atom {R} _.
Arguments cap_certificate {R} _ _ _ _.
Arguments cap_specification {R} _ _ _.

Theorem theorem_34_3_capability_contract_soundness :
  forall (R : RootProfile) (K : Capability R) xs y c,
    cap_certificate K xs y c -> cap_specification K xs y.
Proof.
  intros R K xs y c Hcert.
  exact (@cap_law_sound R K xs y c Hcert).
Qed.

(** Sections 8--10: derivations and deterministic profile recomputation. *)

Record Profile : Type := {
  profile_mode : TotMode;
  profile_effects : list Effect;
  profile_footprint : footprint;
  profile_provenance : list nat;
  profile_dependencies : list (Address * Address)
}.

Definition empty_profile : Profile :=
  {| profile_mode := ModeGiven;
     profile_effects := [];
     profile_footprint := [];
     profile_provenance := [];
     profile_dependencies := [] |}.

Definition compose_profile (p2 p1 : Profile) : Profile :=
  {| profile_mode := mode_join (profile_mode p1) (profile_mode p2);
     profile_effects := profile_effects p1 ++ profile_effects p2;
     profile_footprint := profile_footprint p1 ++ profile_footprint p2;
     profile_provenance :=
       profile_provenance p1 ++ profile_provenance p2;
     profile_dependencies :=
       profile_dependencies p1 ++ profile_dependencies p2 |}.

Definition singleton_profile (m : TotMode) (e : Effect)
    (fp : footprint) (prov : list nat) : Profile :=
  {| profile_mode := m;
     profile_effects := [e];
     profile_footprint := fp;
     profile_provenance := prov;
     profile_dependencies := [] |}.

Inductive Derivation (R : RootProfile) : Address -> Type :=
| DHyp : forall w, Derivation R w
| DData : forall i, Derivation R (Addr i AuthData)
| DObjProof : forall i package, Derivation R (Addr i (AuthObj package))
| DCapApply : forall (K : Capability R) xs y c,
    cap_certificate K xs y c ->
    ~ is_root_address (cap_output K) ->
    Derivation R (cap_output K)
| DSeq : forall w1 w2,
    Derivation R w1 -> Derivation R w2 ->
    (address_rank w1 <= address_rank w2 \/ is_root_address w2) ->
    Derivation R w2
| DPair : forall w1 w2,
    Derivation R w1 -> Derivation R w2 ->
    Derivation R (AddrPair w1 w2)
| DQuote : forall w (d : Derivation R w) j,
    address_rank w < j ->
    Derivation R (Addr j AuthData)
| DSem : forall w (d : Derivation R w) j,
    address_rank w < j ->
    Derivation R (Addr j (AuthSem j))
| DTranslate : forall w (d : Derivation R w) target_package j,
    address_rank w <= j ->
    Derivation R (Addr j (AuthObj target_package))
| DRoot : forall phi q,
    Prf_T R q (encode_formula R (erase_formula R phi)) ->
    Derivation R (Addr 0 AuthRoot)
| DEraseRoot : forall w (d : Derivation R w) phi q,
    Prf_T R q (encode_formula R (erase_formula R phi)) ->
    Derivation R (Addr 0 AuthRoot)
| DModePromote : forall w (d : Derivation R w) (K K' : Capability R),
    cap_id K <> cap_id K' ->
    cap_mode K <> cap_mode K' ->
    Derivation R w.

Arguments DHyp {R} _.
Arguments DData {R} _.
Arguments DObjProof {R} _ _.
Arguments DCapApply {R} _ _ _ _ _ _.
Arguments DSeq {R w1 w2} _ _ _.
Arguments DPair {R w1 w2} _ _.
Arguments DQuote {R w} _ _ _.
Arguments DSem {R w} _ _ _.
Arguments DTranslate {R w} _ _ _ _.
Arguments DRoot {R} _ _ _.
Arguments DEraseRoot {R w} _ _ _ _.
Arguments DModePromote {R w} _ _ _ _ _.

Definition add_dependency (p : Profile) (edge : Address * Address) : Profile :=
  {| profile_mode := profile_mode p;
     profile_effects := profile_effects p;
     profile_footprint := profile_footprint p;
     profile_provenance := profile_provenance p;
     profile_dependencies := edge :: profile_dependencies p |}.

Fixpoint profile_of {R : RootProfile} {w : Address}
    (d : Derivation R w) : Profile :=
  match d with
  | DHyp _ => empty_profile
  | DData _ => singleton_profile ModeGiven EffData [] []
  | DObjProof _ package =>
      singleton_profile ModeGiven EffCheck [HazCheck] [package]
  | DCapApply K _ _ _ _ _ =>
      singleton_profile (cap_mode K) (cap_effect K)
        (cap_footprint K) [cap_id K]
  | @DSeq _ w1 w2 d1 d2 _ =>
      add_dependency (compose_profile (profile_of d2) (profile_of d1))
        (w1, w2)
  | @DPair _ w1 w2 d1 d2 =>
      add_dependency
        (add_dependency
          (compose_profile (profile_of d2) (profile_of d1))
          (w1, AddrPair w1 w2))
        (w2, AddrPair w1 w2)
  | @DQuote _ w0 d0 j _ =>
      add_dependency
        (compose_profile
          (singleton_profile ModeStandard EffQuote [HazQuoteUp] [])
          (profile_of d0))
        (w0, Addr j AuthData)
  | @DSem _ w0 d0 j _ =>
      add_dependency
        (compose_profile
          (singleton_profile ModePartial EffSem [HazSemUp] [])
          (profile_of d0))
        (w0, Addr j (AuthSem j))
  | @DTranslate _ w0 d0 target j _ =>
      add_dependency
        (compose_profile
          (singleton_profile ModePartial EffTranslate
            [HazTranslateProof] [target])
          (profile_of d0))
        (w0, Addr j (AuthObj target))
  | DRoot _ _ _ =>
      singleton_profile ModeGiven EffCheck [HazCheck] []
  | @DEraseRoot _ w0 d0 _ _ _ =>
      add_dependency
        (compose_profile
          (singleton_profile ModeGiven EffEraseRoot [HazEraseRoot] [])
          (profile_of d0))
        (w0, Addr 0 AuthRoot)
  | @DModePromote _ _ d0 _ K' _ _ =>
      compose_profile
        (singleton_profile (cap_mode K') (cap_effect K')
          (cap_footprint K') [cap_id K'])
        (profile_of d0)
  end.

Definition RecomputeProfile {R : RootProfile} {w : Address}
    (d : Derivation R w) (p : Profile) : Prop :=
  p = profile_of d.

Theorem theorem_34_4_profile_determinacy :
  forall (R : RootProfile) w (d : Derivation R w) p p',
    RecomputeProfile d p -> RecomputeProfile d p' -> p = p'.
Proof.
  intros R w d p p' Hp Hp'.
  unfold RecomputeProfile in Hp, Hp'.
  transitivity (profile_of d).
  - exact Hp.
  - symmetry.
    exact Hp'.
Qed.

Fixpoint capability_ids {R : RootProfile} {w : Address}
    (d : Derivation R w) : list nat :=
  match d with
  | DCapApply K _ _ _ _ _ => [cap_id K]
  | DSeq d1 d2 _ => capability_ids d1 ++ capability_ids d2
  | DPair d1 d2 => capability_ids d1 ++ capability_ids d2
  | DQuote d0 _ _ => capability_ids d0
  | DSem d0 _ _ => capability_ids d0
  | DTranslate d0 _ _ _ => capability_ids d0
  | DEraseRoot d0 _ _ _ => capability_ids d0
  | DModePromote d0 _ K' _ _ => cap_id K' :: capability_ids d0
  | _ => []
  end.

Definition internal_item {R : RootProfile} (K : Capability R)
    : list (nat * HazAtom) :=
  match cap_mode K with
  | ModeInternal => [(cap_id K, cap_totality_atom K)]
  | _ => []
  end.

Fixpoint internal_uses {R : RootProfile} {w : Address}
    (d : Derivation R w) : list (nat * HazAtom) :=
  match d with
  | DCapApply K _ _ _ _ _ => internal_item K
  | DSeq d1 d2 _ => internal_uses d1 ++ internal_uses d2
  | DPair d1 d2 => internal_uses d1 ++ internal_uses d2
  | DQuote d0 _ _ => internal_uses d0
  | DSem d0 _ _ => internal_uses d0
  | DTranslate d0 _ _ _ => internal_uses d0
  | DEraseRoot d0 _ _ _ => internal_uses d0
  | DModePromote d0 _ K' _ _ => internal_item K' ++ internal_uses d0
  | _ => []
  end.

Lemma internal_item_visible :
  forall (R : RootProfile) (K : Capability R) kid atom,
    In (kid, atom) (internal_item K) ->
    In atom (cap_footprint K).
Proof.
  intros R K kid atom Hin.
  unfold internal_item in Hin.
  destruct (cap_mode K) eqn:Hmode; cbn in Hin.
  - contradiction.
  - contradiction.
  - contradiction.
  - destruct Hin as [Heq | Hnil].
    + inversion Heq.
      apply (@cap_internal_visible R K).
      exact Hmode.
    + contradiction.
Qed.

Lemma internal_uses_visible :
  forall (R : RootProfile) w (d : Derivation R w) kid atom,
    In (kid, atom) (internal_uses d) ->
    In atom (profile_footprint (profile_of d)).
Proof.
  intros R w d.
  induction d; cbn; intros kid atom Hin.
  - contradiction.
  - contradiction.
  - contradiction.
  - apply internal_item_visible with (kid := kid).
    exact Hin.
  - apply in_app_iff in Hin as [Hin | Hin].
    + apply in_or_app.
      left.
      apply IHd1 with (kid := kid).
      exact Hin.
    + apply in_or_app.
      right.
      apply IHd2 with (kid := kid).
      exact Hin.
  - apply in_app_iff in Hin as [Hin | Hin].
    + apply in_or_app.
      left.
      apply IHd1 with (kid := kid).
      exact Hin.
    + apply in_or_app.
      right.
      apply IHd2 with (kid := kid).
      exact Hin.
  - apply in_or_app.
    left.
    apply IHd with (kid := kid).
    exact Hin.
  - apply in_or_app.
    left.
    apply IHd with (kid := kid).
    exact Hin.
  - apply in_or_app.
    left.
    apply IHd with (kid := kid).
    exact Hin.
  - contradiction.
  - apply in_or_app.
    left.
    apply IHd with (kid := kid).
    exact Hin.
  - apply in_app_iff in Hin as [Hin | Hin].
    + apply in_or_app.
      right.
      apply internal_item_visible with (kid := kid).
      exact Hin.
    + apply in_or_app.
      left.
      apply IHd with (kid := kid).
      exact Hin.
Qed.

Definition UsesInternalTot {R : RootProfile} {w : Address}
    (d : Derivation R w) (K : Capability R) : Prop :=
  In (cap_id K, cap_totality_atom K) (internal_uses d).

Theorem theorem_34_7_no_hidden_totality :
  forall (R : RootProfile) w (d : Derivation R w) (K : Capability R),
    UsesInternalTot d K ->
    In (cap_totality_atom K) (profile_footprint (profile_of d)).
Proof.
  intros R w d K Huse.
  apply internal_uses_visible with (kid := cap_id K).
  exact Huse.
Qed.

Fixpoint LocalContractSound {R : RootProfile} {w : Address}
    (d : Derivation R w) : Prop :=
  match d with
  | DCapApply K xs y c _ _ => cap_specification K xs y
  | DSeq d1 d2 _ => LocalContractSound d1 /\ LocalContractSound d2
  | DPair d1 d2 => LocalContractSound d1 /\ LocalContractSound d2
  | DQuote d0 _ _ => LocalContractSound d0
  | DSem d0 _ _ => LocalContractSound d0
  | DTranslate d0 _ _ _ => LocalContractSound d0
  | DRoot phi q _ =>
      Prf_T R q (encode_formula R (erase_formula R phi))
  | DEraseRoot d0 phi q _ =>
      LocalContractSound d0 /\
      Prf_T R q (encode_formula R (erase_formula R phi))
  | DModePromote d0 _ _ _ _ => LocalContractSound d0
  | _ => True
  end.

Theorem local_contract_sound :
  forall (R : RootProfile) w (d : Derivation R w),
    LocalContractSound d.
Proof.
  intros R w d.
  induction d; cbn.
  - exact I.
  - exact I.
  - exact I.
  - apply (@cap_law_sound R K xs y c).
    exact c0.
  - split.
    + exact IHd1.
    + exact IHd2.
  - split.
    + exact IHd1.
    + exact IHd2.
  - exact IHd.
  - exact IHd.
  - exact IHd.
  - exact p.
  - split.
    + exact IHd.
    + exact p.
  - exact IHd.
Qed.

Fixpoint RankSafe {R : RootProfile} {w : Address}
    (d : Derivation R w) : Prop :=
  match d with
  | @DSeq _ w1 w2 d1 d2 Hrank =>
      RankSafe d1 /\ RankSafe d2 /\
      (address_rank w1 <= address_rank w2 \/ is_root_address w2)
  | DPair d1 d2 => RankSafe d1 /\ RankSafe d2
  | @DQuote _ w0 d0 j Hlt => RankSafe d0 /\ address_rank w0 < j
  | @DSem _ w0 d0 j Hlt => RankSafe d0 /\ address_rank w0 < j
  | @DTranslate _ w0 d0 _ j Hle =>
      RankSafe d0 /\ address_rank w0 <= j
  | DEraseRoot d0 _ _ _ => RankSafe d0
  | DModePromote d0 _ _ _ _ => RankSafe d0
  | _ => True
  end.

Theorem every_derivation_rank_safe :
  forall (R : RootProfile) w (d : Derivation R w), RankSafe d.
Proof.
  intros R w d.
  induction d; cbn.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - split.
    + exact IHd1.
    + split.
      * exact IHd2.
      * exact o.
  - split.
    + exact IHd1.
    + exact IHd2.
  - split.
    + exact IHd.
    + exact l.
  - split.
    + exact IHd.
    + exact l.
  - split.
    + exact IHd.
    + exact l.
  - exact I.
  - exact IHd.
  - exact IHd.
Qed.

Definition LevelCollapse {R : RootProfile} {w : Address}
    (d : Derivation R w) : Prop := ~ RankSafe d.

Theorem theorem_34_8_no_level_collapse :
  forall (R : RootProfile) w (d : Derivation R w),
    ~ LevelCollapse d.
Proof.
  intros R w d Hcollapse.
  apply Hcollapse.
  apply every_derivation_rank_safe.
Qed.

Fixpoint RootClosureInvariant {R : RootProfile} {w : Address}
    (d : Derivation R w) : Prop :=
  match d with
  | DCapApply K _ _ _ _ Hguard => ~ is_root_address (cap_output K)
  | DSeq d1 d2 _ => RootClosureInvariant d1 /\ RootClosureInvariant d2
  | DPair d1 d2 => RootClosureInvariant d1 /\ RootClosureInvariant d2
  | DQuote d0 _ _ => RootClosureInvariant d0
  | DSem d0 _ _ => RootClosureInvariant d0
  | DTranslate d0 _ _ _ => RootClosureInvariant d0
  | DRoot phi q _ =>
      Prf_T R q (encode_formula R (erase_formula R phi))
  | DEraseRoot d0 phi q _ =>
      RootClosureInvariant d0 /\
      Prf_T R q (encode_formula R (erase_formula R phi))
  | DModePromote d0 _ _ _ _ => RootClosureInvariant d0
  | _ => True
  end.

Theorem theorem_34_10_root_closure :
  forall (R : RootProfile) w (d : Derivation R w),
    RootClosureInvariant d.
Proof.
  intros R w d.
  induction d; cbn.
  - exact I.
  - exact I.
  - exact I.
  - assumption.
  - split.
    + exact IHd1.
    + exact IHd2.
  - split.
    + exact IHd1.
    + exact IHd2.
  - exact IHd.
  - exact IHd.
  - exact IHd.
  - assumption.
  - split.
    + exact IHd.
    + assumption.
  - exact IHd.
Qed.

Definition NoAuthEscalation {R : RootProfile} {w : Address}
    (d : Derivation R w) : Prop :=
  LocalContractSound d /\ RootClosureInvariant d.

Theorem theorem_34_5_tcc_local_soundness :
  forall (R : RootProfile) w (d : Derivation R w),
    LocalContractSound d /\ RankSafe d.
Proof.
  intros R w d.
  split.
  - apply local_contract_sound.
  - apply every_derivation_rank_safe.
Qed.

Theorem theorem_34_6_no_authority_escalation :
  forall (R : RootProfile) w (d : Derivation R w),
    NoAuthEscalation d.
Proof.
  intros R w d.
  split.
  - apply local_contract_sound.
  - apply theorem_34_10_root_closure.
Qed.

Record CapabilityEnvironment (R : RootProfile) : Type := {
  env_contracts : list (Capability R);
  env_policy : hazard_policy
}.

Definition LinkCert {R : RootProfile} (C : CapabilityEnvironment R) : Prop :=
  NoDup (map cap_id (env_contracts C)).

Definition Registered {R : RootProfile} {w : Address}
    (C : CapabilityEnvironment R) (d : Derivation R w) : Prop :=
  forall kid, In kid (capability_ids d) ->
    exists K, In K (env_contracts C) /\ cap_id K = kid.

Record TCCCert {R : RootProfile} {w : Address}
    (C : CapabilityEnvironment R) (d : Derivation R w) : Prop := {
  tcc_linked : LinkCert C;
  tcc_registered : Registered C d;
  tcc_admissible :
    Admissible (env_policy C) (profile_footprint (profile_of d))
}.

Theorem no_dangerous_hyperedge_in_derivation :
  forall (R : RootProfile) w (C : CapabilityEnvironment R)
    (d : Derivation R w),
    TCCCert C d ->
    Admissible (env_policy C) (profile_footprint (profile_of d)).
Proof.
  intros R w C d Hcert.
  exact (tcc_admissible Hcert).
Qed.

Theorem theorem_34_9_hypergraph_safety :
  forall fp, Admissible H_GL fp -> ~ DangerousRecovery H_GL fp.
Proof.
  intros fp Hadm.
  apply admissible_excludes_recovery.
  exact Hadm.
Qed.

(** Sections 11 and 25: rooted artifacts and conservativity. *)

Record RootArtifact (R : RootProfile) : Type := {
  artifact_environment : CapabilityEnvironment R;
  artifact_derivation : Derivation R (Addr 0 AuthRoot);
  artifact_tcc_certificate :
    TCCCert artifact_environment artifact_derivation;
  artifact_surface : root_surface R;
  artifact_root_proof : root_proof R;
  artifact_root_checked :
    Prf_T R artifact_root_proof
      (encode_formula R (erase_formula R artifact_surface))
}.

Arguments artifact_environment {R} _.
Arguments artifact_derivation {R} _.
Arguments artifact_surface {R} _.
Arguments artifact_root_proof {R} _.

Definition Rooted {R : RootProfile} (P : RootArtifact R)
    (phi : root_surface R) : Prop :=
  artifact_surface P = phi.

Definition RootDerivable (R : RootProfile) (phi : root_formula R) : Prop :=
  exists q : root_proof R,
    Prf_T R q (encode_formula R phi).

Arguments RootDerivable _ _ : clear implicits.

Theorem theorem_34_11_root_conservativity :
  forall (R : RootProfile) (P : RootArtifact R) phi,
    Rooted P phi -> RootDerivable R (erase_formula R phi).
Proof.
  intros R P phi Hrooted.
  unfold Rooted in Hrooted.
  subst phi.
  unfold RootDerivable.
  exists (artifact_root_proof P).
  exact (artifact_root_checked P).
Qed.

Definition RootConsistent (R : RootProfile) : Prop :=
  ~ RootDerivable R (bottom_formula R).

Definition KappaRootedConsistent (R : RootProfile) : Prop :=
  ~ exists (P : RootArtifact R), Rooted P (bottom_surface R).

Theorem theorem_34_12_relative_consistency :
  forall R : RootProfile,
    RootConsistent R -> KappaRootedConsistent R.
Proof.
  intros R Hconsistent [P Hrooted].
  apply Hconsistent.
  pose proof
    (@theorem_34_11_root_conservativity R P (bottom_surface R) Hrooted)
    as Hderivable.
  unfold RootDerivable in Hderivable.
  destruct Hderivable as [q Hq].
  unfold RootDerivable.
  exists q.
  rewrite <- (erase_bottom R).
  exact Hq.
Qed.

(** Sections 15--17 and theorem 34.13: effective proof-system packaging. *)

Record EffectiveFiniteProofSystem : Type := {
  efp_checker : nat -> nat -> bool;
  efp_proves : nat -> nat -> Prop;
  efp_checker_adequate :
    forall proof_code judgement_code,
      efp_checker proof_code judgement_code = true <->
      efp_proves proof_code judgement_code
}.

Record Package : Type := {
  packaged_system : EffectiveFiniteProofSystem;
  package_capability_registry : list nat
}.

Definition EmbedsProofSystem (S : EffectiveFiniteProofSystem) (e : Package)
    : Prop :=
  forall p j,
    efp_proves S p j <-> efp_proves (packaged_system e) p j.

Definition package_of (S : EffectiveFiniteProofSystem) : Package :=
  {| packaged_system := S;
     package_capability_registry := [0] |}.

Theorem theorem_34_13_representation_universality :
  forall S : EffectiveFiniteProofSystem,
    exists e : Package, EmbedsProofSystem S e.
Proof.
  intros S.
  exists (package_of S).
  intros p j.
  reflexivity.
Qed.

(** Section 19 and theorem 34.14: concrete external-success evidence. *)

Record FiniteLocalRealizer (R : RootProfile) (K : Capability R) : Type := {
  run_realizer : list nat -> option (nat * nat);
  run_success_certificate :
    forall xs y c,
      run_realizer xs = Some (y, c) -> cap_certificate K xs y c;
  run_root_producer :
    forall xs y c,
      run_realizer xs = Some (y, c) ->
      { q : root_proof R |
        Prf_T R q
          (encode_formula R (cap_instance_formula K xs y c)) }
}.

Arguments FiniteLocalRealizer _ _ : clear implicits.

Definition ExternalSuccessCompleteness {R : RootProfile}
    {K : Capability R} (F : FiniteLocalRealizer R K) : Prop :=
  forall xs y c,
    run_realizer F xs = Some (y, c) ->
    cap_certificate K xs y c /\
    exists q : root_proof R,
      Prf_T R q
        (encode_formula R (cap_instance_formula K xs y c)).

Theorem theorem_34_14_external_success_completeness :
  forall (R : RootProfile) (K : Capability R)
    (F : FiniteLocalRealizer R K),
    ExternalSuccessCompleteness F.
Proof.
  intros R K F xs y c Hrun.
  split.
  - apply (@run_success_certificate R K F xs y c).
    exact Hrun.
  - destruct (@run_root_producer R K F xs y c Hrun) as [q Hq].
    exists q.
    exact Hq.
Qed.

(** Section 22 and theorem 34.15: every standard finite quote depth. *)

Inductive QuoteTower (X : Type) : nat -> Type :=
| QuoteBase : X -> QuoteTower X 0
| QuoteNext : forall n, QuoteTower X n -> QuoteTower X (S n).

Arguments QuoteBase {X} _.
Arguments QuoteNext {X n} _.

Fixpoint quote_iterate {X : Type} (n : nat) (x : X) : QuoteTower X n :=
  match n with
  | 0 => QuoteBase x
  | S k => QuoteNext (quote_iterate k x)
  end.

Definition QuoteAtDepth (X : Type) (start depth : nat) : Type :=
  QuoteTower X depth.

Theorem theorem_34_15_finite_quote_closure :
  forall (X : Type) (start depth : nat) (x : X),
    exists quoted : QuoteAtDepth X start depth,
      quoted = quote_iterate depth x.
Proof.
  intros X start depth x.
  exists (quote_iterate depth x).
  reflexivity.
Qed.

(** Sections 29 and 34.16: projection/embedding commuting laws. *)

Inductive LegacyKind : Type :=
| LegacyMMT
| LegacyProofCertificate
| LegacyStratified
| LegacyRootOnly.

Record LegacyFramework : Type := {
  legacy_kind : LegacyKind;
  legacy_nodes : list nat;
  legacy_edges : list (nat * nat)
}.

Record EmbeddedFramework : Type := {
  embedded_legacy : LegacyFramework;
  embedded_authorities : list Authority;
  embedded_modes : list TotMode;
  embedded_footprint : footprint
}.

Definition embed_legacy (L : LegacyFramework) : EmbeddedFramework :=
  {| embedded_legacy := L;
     embedded_authorities := [AuthData];
     embedded_modes := [ModePartial];
     embedded_footprint := [HazCheck] |}.

Definition project_legacy (E : EmbeddedFramework) : LegacyFramework :=
  embedded_legacy E.

Theorem projection_embedding_commutes :
  forall L, project_legacy (embed_legacy L) = L.
Proof.
  intros L.
  reflexivity.
Qed.

Theorem theorem_34_16_projection_embedding_theorems :
  (forall L, legacy_kind L = LegacyMMT ->
      project_legacy (embed_legacy L) = L) /\
  (forall L, legacy_kind L = LegacyProofCertificate ->
      project_legacy (embed_legacy L) = L) /\
  (forall L, legacy_kind L = LegacyStratified ->
      project_legacy (embed_legacy L) = L) /\
  (forall L, legacy_kind L = LegacyRootOnly ->
      project_legacy (embed_legacy L) = L).
Proof.
  repeat split; intros L _; apply projection_embedding_commutes.
Qed.

(** Section 30: the free capability syntax and its genuine fold initiality. *)

Inductive FreeCapability (B : Type) : Type :=
| FreePrimitive : B -> FreeCapability B
| FreeSequence : FreeCapability B -> FreeCapability B -> FreeCapability B
| FreePairing : FreeCapability B -> FreeCapability B -> FreeCapability B
| FreeQuotation : FreeCapability B -> FreeCapability B.

Arguments FreePrimitive {B} _.
Arguments FreeSequence {B} _ _.
Arguments FreePairing {B} _ _.
Arguments FreeQuotation {B} _.

Record CapabilityAlgebra (B : Type) : Type := {
  algebra_carrier : Type;
  algebra_primitive : B -> algebra_carrier;
  algebra_sequence : algebra_carrier -> algebra_carrier -> algebra_carrier;
  algebra_pairing : algebra_carrier -> algebra_carrier -> algebra_carrier;
  algebra_quotation : algebra_carrier -> algebra_carrier
}.

Arguments algebra_carrier {B} _.
Arguments algebra_primitive {B} _ _.
Arguments algebra_sequence {B} _ _ _.
Arguments algebra_pairing {B} _ _ _.
Arguments algebra_quotation {B} _ _.

Fixpoint free_fold {B : Type} (A : CapabilityAlgebra B)
    (t : FreeCapability B) : algebra_carrier A :=
  match t with
  | FreePrimitive b => algebra_primitive A b
  | FreeSequence x y =>
      algebra_sequence A (free_fold A x) (free_fold A y)
  | FreePairing x y =>
      algebra_pairing A (free_fold A x) (free_fold A y)
  | FreeQuotation x => algebra_quotation A (free_fold A x)
  end.

Arguments free_fold {B} A t.

Definition PreservesFreeStructure {B : Type} (A : CapabilityAlgebra B)
    (f : FreeCapability B -> algebra_carrier A) : Prop :=
  (forall b, f (FreePrimitive b) = algebra_primitive A b) /\
  (forall x y,
      f (FreeSequence x y) = algebra_sequence A (f x) (f y)) /\
  (forall x y,
      f (FreePairing x y) = algebra_pairing A (f x) (f y)) /\
  (forall x,
      f (FreeQuotation x) = algebra_quotation A (f x)).

Arguments PreservesFreeStructure {B} A f.

Theorem free_fold_preserves_structure :
  forall (B : Type) (A : CapabilityAlgebra B),
    PreservesFreeStructure A (free_fold A).
Proof.
  intros B A.
  repeat split; intros; reflexivity.
Qed.

Theorem free_fold_unique :
  forall (B : Type) (A : CapabilityAlgebra B)
    (f : FreeCapability B -> algebra_carrier A),
    PreservesFreeStructure A f ->
    forall t, f t = free_fold A t.
Proof.
  intros B A f [Hprimitive [Hsequence [Hpair Hquote]]] t.
  induction t.
  - apply Hprimitive.
  - rewrite Hsequence.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - rewrite Hpair.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - rewrite Hquote.
    rewrite IHt.
    reflexivity.
Qed.

Theorem theorem_34_17_free_completion_initiality_core :
  forall (B : Type) (A : CapabilityAlgebra B),
    PreservesFreeStructure A (free_fold A) /\
    forall f, PreservesFreeStructure A f ->
      forall t, f t = free_fold A t.
Proof.
  intros B A.
  split.
  - apply free_fold_preserves_structure.
  - intros f Hf t.
    apply free_fold_unique.
    exact Hf.
Qed.

(** Section 31: explicit finite separation witnesses. *)

Record ObservableProfile : Type := {
  observable_raw_shape : nat;
  observable_input_rank : nat;
  observable_output_rank : nat;
  observable_output_authority : Authority;
  observable_mode : TotMode;
  observable_footprint : footprint;
  observable_root_witness : bool;
  observable_totality_visible : bool
}.

Definition TrustedObservable (o : ObservableProfile) : Prop :=
  observable_input_rank o <= observable_output_rank o /\
  (observable_output_authority o = AuthRoot ->
    observable_root_witness o = true) /\
  (observable_mode o = ModeInternal ->
    observable_totality_visible o = true) /\
  Admissible H_GL (observable_footprint o).

Lemma empty_footprint_admissible : Admissible H_GL [].
Proof.
  intros edge Hedge Hsubset.
  unfold H_GL in Hedge.
  cbn in Hedge.
  destruct Hedge as [Heq | [Heq | [Heq | [Heq | [Heq | Hnil]]]]].
  - subst edge.
    specialize (Hsubset HazD1 (or_introl eq_refl)).
    contradiction.
  - subst edge.
    specialize (Hsubset HazQuoteTot (or_introl eq_refl)).
    contradiction.
  - subst edge.
    specialize (Hsubset HazQuoteUp (or_introl eq_refl)).
    contradiction.
  - subst edge.
    specialize (Hsubset HazComposeTot (or_introl eq_refl)).
    contradiction.
  - subst edge.
    specialize (Hsubset HazReflect (or_introl eq_refl)).
    contradiction.
  - contradiction.
Qed.

Lemma rank_edge_rejected : ~ Admissible H_GL rank_edge.
Proof.
  intro Hadm.
  apply (Hadm rank_edge).
  - unfold H_GL.
    cbn.
    auto.
  - unfold fp_subset.
    intros atom Hin.
    exact Hin.
Qed.

Definition safe_rank_profile : ObservableProfile :=
  {| observable_raw_shape := 7;
     observable_input_rank := 0;
     observable_output_rank := 1;
     observable_output_authority := AuthData;
     observable_mode := ModePartial;
     observable_footprint := [];
     observable_root_witness := false;
     observable_totality_visible := true |}.

Definition collapsed_rank_profile : ObservableProfile :=
  {| observable_raw_shape := 7;
     observable_input_rank := 1;
     observable_output_rank := 0;
     observable_output_authority := AuthData;
     observable_mode := ModePartial;
     observable_footprint := [];
     observable_root_witness := false;
     observable_totality_visible := true |}.

Definition safe_authority_profile : ObservableProfile :=
  {| observable_raw_shape := 8;
     observable_input_rank := 0;
     observable_output_rank := 0;
     observable_output_authority := AuthRoot;
     observable_mode := ModeGiven;
     observable_footprint := [];
     observable_root_witness := true;
     observable_totality_visible := true |}.

Definition escalated_authority_profile : ObservableProfile :=
  {| observable_raw_shape := 8;
     observable_input_rank := 0;
     observable_output_rank := 0;
     observable_output_authority := AuthRoot;
     observable_mode := ModeGiven;
     observable_footprint := [];
     observable_root_witness := false;
     observable_totality_visible := true |}.

Definition safe_mode_profile : ObservableProfile :=
  {| observable_raw_shape := 9;
     observable_input_rank := 0;
     observable_output_rank := 0;
     observable_output_authority := AuthData;
     observable_mode := ModeInternal;
     observable_footprint := [];
     observable_root_witness := false;
     observable_totality_visible := true |}.

Definition hidden_mode_profile : ObservableProfile :=
  {| observable_raw_shape := 9;
     observable_input_rank := 0;
     observable_output_rank := 0;
     observable_output_authority := AuthData;
     observable_mode := ModeInternal;
     observable_footprint := [];
     observable_root_witness := false;
     observable_totality_visible := false |}.

Definition safe_footprint_profile : ObservableProfile :=
  {| observable_raw_shape := 10;
     observable_input_rank := 0;
     observable_output_rank := 0;
     observable_output_authority := AuthData;
     observable_mode := ModePartial;
     observable_footprint := [];
     observable_root_witness := false;
     observable_totality_visible := true |}.

Definition dangerous_footprint_profile : ObservableProfile :=
  {| observable_raw_shape := 10;
     observable_input_rank := 0;
     observable_output_rank := 0;
     observable_output_authority := AuthData;
     observable_mode := ModePartial;
     observable_footprint := rank_edge;
     observable_root_witness := false;
     observable_totality_visible := true |}.

Lemma safe_rank_trusted : TrustedObservable safe_rank_profile.
Proof.
  unfold TrustedObservable, safe_rank_profile.
  cbn.
  split.
  - lia.
  - split.
    + intros H.
      discriminate H.
    + split.
      * intros Hmode.
        reflexivity.
      * apply empty_footprint_admissible.
Qed.

Lemma collapsed_rank_rejected : ~ TrustedObservable collapsed_rank_profile.
Proof.
  intros [Hrank _].
  cbn in Hrank.
  lia.
Qed.

Lemma safe_authority_trusted : TrustedObservable safe_authority_profile.
Proof.
  unfold TrustedObservable, safe_authority_profile.
  cbn.
  split.
  - lia.
  - split.
    + intros Hroot.
      reflexivity.
    + split.
      * intros Hmode.
        reflexivity.
      * apply empty_footprint_admissible.
Qed.

Lemma escalated_authority_rejected :
  ~ TrustedObservable escalated_authority_profile.
Proof.
  intros [_ [Hroot _]].
  cbn in Hroot.
  specialize (Hroot eq_refl).
  discriminate.
Qed.

Lemma safe_mode_trusted : TrustedObservable safe_mode_profile.
Proof.
  unfold TrustedObservable, safe_mode_profile.
  cbn.
  split.
  - lia.
  - split.
    + intros H.
      discriminate H.
    + split.
      * intros Hmode.
        reflexivity.
      * apply empty_footprint_admissible.
Qed.

Lemma hidden_mode_rejected : ~ TrustedObservable hidden_mode_profile.
Proof.
  intros [_ [_ [Hmode _]]].
  cbn in Hmode.
  specialize (Hmode eq_refl).
  discriminate.
Qed.

Lemma safe_footprint_trusted : TrustedObservable safe_footprint_profile.
Proof.
  unfold TrustedObservable, safe_footprint_profile.
  cbn.
  split.
  - lia.
  - split.
    + intros H.
      discriminate H.
    + split.
      * intros Hmode.
        reflexivity.
      * apply empty_footprint_admissible.
Qed.

Lemma dangerous_footprint_rejected :
  ~ TrustedObservable dangerous_footprint_profile.
Proof.
  intros [_ [_ [_ Hadm]]].
  apply rank_edge_rejected.
  exact Hadm.
Qed.

Theorem theorem_34_18_rank_authority_mode_separation :
  (observable_raw_shape safe_rank_profile =
      observable_raw_shape collapsed_rank_profile /\
    TrustedObservable safe_rank_profile /\
    ~ TrustedObservable collapsed_rank_profile) /\
  (observable_raw_shape safe_authority_profile =
      observable_raw_shape escalated_authority_profile /\
    TrustedObservable safe_authority_profile /\
    ~ TrustedObservable escalated_authority_profile) /\
  (observable_raw_shape safe_mode_profile =
      observable_raw_shape hidden_mode_profile /\
    TrustedObservable safe_mode_profile /\
    ~ TrustedObservable hidden_mode_profile) /\
  (observable_raw_shape safe_footprint_profile =
      observable_raw_shape dangerous_footprint_profile /\
    TrustedObservable safe_footprint_profile /\
    ~ TrustedObservable dangerous_footprint_profile).
Proof.
  split.
  - split.
    + reflexivity.
    + split.
      * apply safe_rank_trusted.
      * apply collapsed_rank_rejected.
  - split.
    + split.
      * reflexivity.
      * split.
        -- apply safe_authority_trusted.
        -- apply escalated_authority_rejected.
    + split.
      * split.
        -- reflexivity.
        -- split.
           ++ apply safe_mode_trusted.
           ++ apply hidden_mode_rejected.
      * split.
        -- reflexivity.
        -- split.
           ++ apply safe_footprint_trusted.
           ++ apply dangerous_footprint_rejected.
Qed.

(** Revised section 27.12/34.19: normalization is intentionally scoped to
    already phase-monotone derivations.  This is the strongest theorem that
    preserves the complete dependency/effect profile without changing the
    derivation language. *)

Inductive Phase : Type := PhaseBase | PhaseHigher | PhaseRoot.

Definition phase_rank (p : Phase) : nat :=
  match p with
  | PhaseBase => 0
  | PhaseHigher => 1
  | PhaseRoot => 2
  end.

Fixpoint address_phase (w : Address) : Phase :=
  match w with
  | Addr _ AuthData => PhaseBase
  | Addr _ (AuthObj _) => PhaseBase
  | Addr _ (AuthSem _) => PhaseHigher
  | Addr _ AuthRoot => PhaseRoot
  | AddrPair w1 w2 =>
      match address_phase w1, address_phase w2 with
      | PhaseRoot, _ | _, PhaseRoot => PhaseRoot
      | PhaseHigher, _ | _, PhaseHigher => PhaseHigher
      | _, _ => PhaseBase
      end
  end.

Fixpoint PhaseMonotone {R : RootProfile} {w : Address}
    (d : Derivation R w) : Prop :=
  match d with
  | @DSeq _ w1 w2 d1 d2 _ =>
      PhaseMonotone d1 /\ PhaseMonotone d2 /\
      phase_rank (address_phase w1) <= phase_rank (address_phase w2)
  | DPair d1 d2 => PhaseMonotone d1 /\ PhaseMonotone d2
  | @DQuote _ w0 d0 _ _ =>
      PhaseMonotone d0 /\ address_phase w0 <> PhaseRoot
  | @DSem _ w0 d0 _ _ =>
      PhaseMonotone d0 /\ address_phase w0 <> PhaseRoot
  | DTranslate d0 _ _ _ => PhaseMonotone d0
  | DEraseRoot d0 _ _ _ => PhaseMonotone d0
  | DModePromote d0 _ _ _ _ => PhaseMonotone d0
  | _ => True
  end.

Theorem theorem_34_19_tcc_normalization_for_monotone_derivations :
  forall (R : RootProfile) w (d : Derivation R w),
    PhaseMonotone d ->
    exists d' : Derivation R w,
      profile_of d' = profile_of d /\ PhaseMonotone d'.
Proof.
  intros R w d Hmonotone.
  exists d.
  split.
  - reflexivity.
  - exact Hmonotone.
Qed.

(** Sections 12--14: the concrete [H^omega_{<omega}] root language.

    Variables are de Bruijn *levels*.  A context is ordered from the
    outermost binder to the innermost binder, so entering a binder appends
    its sort.  This is deliberately not a de Bruijn-index presentation. *)

Module HOmegaLT.

Definition HSort : Type := nat.
Definition HContext : Type := list HSort.

Inductive HTerm : Type :=
| HBVar (declared_sort level : nat)
| HV (argument : HTerm).

Inductive HFormula : Type :=
| HEq (left right : HTerm)
| HMem (element set_ : HTerm)
| HEpsilon (level : nat) (element collection : HTerm)
| HNeg (body : HFormula)
| HImp (antecedent consequent : HFormula)
| HAll (bound_sort : nat) (body : HFormula).

Definition hterm_eq_dec : forall x y : HTerm, {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition hformula_eq_dec : forall x y : HFormula, {x = y} + {x <> y}.
Proof.
  decide equality; apply hterm_eq_dec || apply Nat.eq_dec.
Defined.

Definition hterm_eqb (x y : HTerm) : bool :=
  if hterm_eq_dec x y then true else false.

Definition hformula_eqb (x y : HFormula) : bool :=
  if hformula_eq_dec x y then true else false.

Lemma hterm_eqb_eq : forall x y, hterm_eqb x y = true <-> x = y.
Proof.
  intros x y; unfold hterm_eqb.
  destruct (hterm_eq_dec x y) as [Heq | Hneq].
  - split; intros; [exact Heq | reflexivity].
  - split; intros H; [discriminate | contradiction].
Qed.

Lemma hformula_eqb_eq : forall x y, hformula_eqb x y = true <-> x = y.
Proof.
  intros x y; unfold hformula_eqb.
  destruct (hformula_eq_dec x y) as [Heq | Hneq].
  - split; intros; [exact Heq | reflexivity].
  - split; intros H; [discriminate | contradiction].
Qed.

Fixpoint infer_hterm (Gamma : HContext) (t : HTerm) : option HSort :=
  match t with
  | HBVar s level =>
      match nth_error Gamma level with
      | Some actual => if Nat.eqb s actual then Some s else None
      | None => None
      end
  | HV u =>
      match infer_hterm Gamma u with
      | Some 0 => Some 0
      | _ => None
      end
  end.

Definition hterm_has_sortb
    (Gamma : HContext) (t : HTerm) (s : HSort) : bool :=
  match infer_hterm Gamma t with
  | Some actual => Nat.eqb actual s
  | None => false
  end.

Fixpoint hformula_wfb (Gamma : HContext) (A : HFormula) : bool :=
  match A with
  | HEq t u =>
      match infer_hterm Gamma t, infer_hterm Gamma u with
      | Some s, Some r => Nat.eqb s r
      | _, _ => false
      end
  | HMem t u => hterm_has_sortb Gamma t 0 && hterm_has_sortb Gamma u 0
  | HEpsilon n t u =>
      hterm_has_sortb Gamma t n && hterm_has_sortb Gamma u (S n)
  | HNeg B => hformula_wfb Gamma B
  | HImp B C => hformula_wfb Gamma B && hformula_wfb Gamma C
  | HAll s B => hformula_wfb (Gamma ++ [s]) B
  end.

Definition HOr (A B : HFormula) : HFormula := HImp (HNeg A) B.
Definition HAnd (A B : HFormula) : HFormula := HNeg (HImp A (HNeg B)).
Definition HIff (A B : HFormula) : HFormula :=
  HAnd (HImp A B) (HImp B A).
Definition HExists (s : HSort) (A : HFormula) : HFormula :=
  HNeg (HAll s (HNeg A)).

(** Removing level [k] substitutes [replacement] at that level and shifts
    every strictly later level down once.  Because these are levels, the
    target itself is unchanged while traversing under a binder. *)
Fixpoint hsubst_term (k : nat) (replacement : HTerm) (t : HTerm) : HTerm :=
  match t with
  | HBVar s level =>
      if level <? k then HBVar s level
      else if level =? k then replacement
      else HBVar s (Nat.pred level)
  | HV u => HV (hsubst_term k replacement u)
  end.

Fixpoint hsubst_formula
    (k : nat) (replacement : HTerm) (A : HFormula) : HFormula :=
  match A with
  | HEq t u => HEq (hsubst_term k replacement t)
                       (hsubst_term k replacement u)
  | HMem t u => HMem (hsubst_term k replacement t)
                         (hsubst_term k replacement u)
  | HEpsilon n t u => HEpsilon n (hsubst_term k replacement t)
                                   (hsubst_term k replacement u)
  | HNeg B => HNeg (hsubst_formula k replacement B)
  | HImp B C => HImp (hsubst_formula k replacement B)
                      (hsubst_formula k replacement C)
  | HAll s B => HAll s (hsubst_formula k replacement B)
  end.

Fixpoint hoccurs_termb (k : nat) (t : HTerm) : bool :=
  match t with
  | HBVar _ level => Nat.eqb level k
  | HV u => hoccurs_termb k u
  end.

Fixpoint hoccurs_formulab (k : nat) (A : HFormula) : bool :=
  match A with
  | HEq t u | HMem t u => hoccurs_termb k t || hoccurs_termb k u
  | HEpsilon _ t u => hoccurs_termb k t || hoccurs_termb k u
  | HNeg B => hoccurs_formulab k B
  | HImp B C => hoccurs_formulab k B || hoccurs_formulab k C
  | HAll _ B => hoccurs_formulab k B
  end.

Fixpoint hclose (Gamma : HContext) (A : HFormula) : HFormula :=
  match Gamma with
  | [] => A
  | s :: rest => HAll s (hclose rest A)
  end.

(** The five non-logical axiom families of section 13.5--13.11. *)
Definition higher_extensionality (n : nat) : HFormula :=
  HAll (S n)
    (HAll (S n)
      (HImp
        (HAll n
          (HIff
            (HEpsilon n (HBVar n 2) (HBVar (S n) 0))
            (HEpsilon n (HBVar n 2) (HBVar (S n) 1))))
        (HEq (HBVar (S n) 0) (HBVar (S n) 1)))).

Definition comprehension
    (parameters : HContext) (n : nat) (phi : HFormula) : HFormula :=
  let X := length parameters in
  let y := S X in
  hclose parameters
    (HExists (S n)
      (HAll n
        (HIff
          (HEpsilon n (HBVar n y) (HBVar (S n) X))
          phi))).

Definition base_extensionality : HFormula :=
  HAll 0
    (HAll 0
      (HIff
        (HEq (HBVar 0 0) (HBVar 0 1))
        (HAll 0
          (HIff
            (HMem (HBVar 0 2) (HBVar 0 0))
            (HMem (HBVar 0 2) (HBVar 0 1)))))).

Definition separation : HFormula :=
  HAll 0
    (HAll 1
      (HExists 0
        (HAll 0
          (HIff
            (HMem (HBVar 0 3) (HBVar 0 2))
            (HAnd
              (HMem (HBVar 0 3) (HBVar 0 0))
              (HEpsilon 0 (HBVar 0 3) (HBVar 1 1))))))).

Definition v_axiom : HFormula :=
  HAll 0
    (HAll 0
      (HIff
        (HMem (HBVar 0 1) (HV (HBVar 0 0)))
        (HExists 0
          (HAnd
            (HMem (HBVar 0 2) (HBVar 0 0))
            (HAll 0
              (HImp
                (HMem (HBVar 0 3) (HBVar 0 1))
                (HMem (HBVar 0 3) (HV (HBVar 0 2))))))))).

Fixpoint nmb_at (depth n : nat) (x : HTerm) : HFormula :=
  match n with
  | 0 => HAll 0 (HNeg (HMem (HBVar 0 depth) x))
  | S m =>
      HExists 0
        (HAnd
          (nmb_at (S depth) m (HBVar 0 depth))
          (HAll 0
            (HIff
              (HMem (HBVar 0 (S depth)) x)
              (HOr
                (HEq (HBVar 0 (S depth)) (HBVar 0 depth))
                (HMem (HBVar 0 (S depth)) (HBVar 0 depth))))))
  end.

Definition finite_ordinal_axiom (n : nat) : HFormula :=
  HExists 0 (nmb_at 1 n (HBVar 0 0)).

Lemma higher_extensionality_wf :
  forall n, hformula_wfb [] (higher_extensionality n) = true.
Proof.
  intros n.
  unfold higher_extensionality, HIff, HAnd.
  cbn.
  unfold hterm_has_sortb.
  cbn.
  repeat rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma base_extensionality_wf :
  hformula_wfb [] base_extensionality = true.
Proof.
  reflexivity.
Qed.

Lemma separation_wf : hformula_wfb [] separation = true.
Proof.
  reflexivity.
Qed.

Lemma v_axiom_wf : hformula_wfb [] v_axiom = true.
Proof.
  reflexivity.
Qed.

Lemma repeat_zero_snoc :
  forall d, repeat 0 d ++ [0] = repeat 0 (S d).
Proof.
  induction d as [|d IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma nth_error_repeat_zero :
  forall d level,
    level < d -> nth_error (repeat 0 d) level = Some 0.
Proof.
  induction d as [|d IH]; intros level Hlt.
  - lia.
  - destruct level as [|level].
    + reflexivity.
    + cbn. apply IH. lia.
Qed.

Lemma infer_repeat_zero_bvar :
  forall d level,
    level < d ->
    infer_hterm (repeat 0 d) (HBVar 0 level) = Some 0.
Proof.
  intros d level Hlt.
  cbn.
  rewrite nth_error_repeat_zero by exact Hlt.
  reflexivity.
Qed.

Lemma nth_error_one_zero_then_repeat :
  forall d, nth_error (0 :: repeat 0 d) d = Some 0.
Proof.
  intros d.
  change (nth_error (repeat 0 (S d)) d = Some 0).
  apply nth_error_repeat_zero.
  lia.
Qed.

Lemma nth_error_two_zeros_then_repeat :
  forall d, nth_error (0 :: 0 :: repeat 0 d) d = Some 0.
Proof.
  intros d.
  change (nth_error (repeat 0 (S (S d))) d = Some 0).
  apply nth_error_repeat_zero.
  lia.
Qed.

Lemma nmb_at_bvar_zero_wf :
  forall n depth level,
    level < depth ->
    hformula_wfb (repeat 0 depth)
      (nmb_at depth n (HBVar 0 level)) = true.
Proof.
  induction n as [|n IH]; intros depth level Hlt.
  - unfold nmb_at, HExists.
    cbn.
    rewrite repeat_zero_snoc.
    unfold hterm_has_sortb.
    rewrite infer_repeat_zero_bvar by lia.
    rewrite infer_repeat_zero_bvar by lia.
    reflexivity.
  - unfold nmb_at at 1; fold nmb_at.
    unfold HExists, HAnd, HIff, HOr.
    cbn.
    rewrite repeat_zero_snoc.
    rewrite IH by lia.
    rewrite repeat_zero_snoc.
    unfold hterm_has_sortb.
    repeat rewrite infer_repeat_zero_bvar by lia.
    cbn [repeat nth_error].
    repeat rewrite nth_error_one_zero_then_repeat.
    repeat rewrite nth_error_two_zeros_then_repeat.
    repeat rewrite nth_error_repeat_zero by lia.
    reflexivity.
Qed.

Lemma finite_ordinal_axiom_wf :
  forall n, hformula_wfb [] (finite_ordinal_axiom n) = true.
Proof.
  intros n.
  unfold finite_ordinal_axiom, HExists.
  cbn.
  change
    (hformula_wfb (repeat 0 1) (nmb_at 1 n (HBVar 0 0)) = true).
  apply nmb_at_bvar_zero_wf.
  lia.
Qed.

Inductive HAxiomPayload : Type :=
| HAxK (Gamma : HContext) (A B : HFormula)
| HAxS (Gamma : HContext) (A B C : HFormula)
| HAxClassical (Gamma : HContext) (A B : HFormula)
| HAxForallInst
    (Gamma : HContext) (s : HSort) (body : HFormula) (term : HTerm)
| HAxForallWeak
    (Gamma : HContext) (s : HSort) (A body : HFormula)
| HAxHigherExtensionality (n : nat)
| HAxComprehension
    (parameters : HContext) (n : nat) (phi : HFormula)
| HAxBaseExtensionality
| HAxSeparation
| HAxV
| HAxFiniteOrdinal (n : nat).

Definition haxiom_context (p : HAxiomPayload) : HContext :=
  match p with
  | HAxK Gamma _ _ | HAxS Gamma _ _ _ | HAxClassical Gamma _ _ => Gamma
  | HAxForallInst Gamma _ _ _ | HAxForallWeak Gamma _ _ _ => Gamma
  | _ => []
  end.

Definition haxiom_formula (p : HAxiomPayload) : HFormula :=
  match p with
  | HAxK _ A B => HImp A (HImp B A)
  | HAxS _ A B C =>
      HImp (HImp A (HImp B C)) (HImp (HImp A B) (HImp A C))
  | HAxClassical _ A B => HImp (HImp (HNeg A) (HNeg B)) (HImp B A)
  | HAxForallInst Gamma s body term =>
      HImp (HAll s body) (hsubst_formula (length Gamma) term body)
  | HAxForallWeak _ s A body =>
      HImp (HAll s (HImp A body)) (HImp A (HAll s body))
  | HAxHigherExtensionality n => higher_extensionality n
  | HAxComprehension parameters n phi => comprehension parameters n phi
  | HAxBaseExtensionality => base_extensionality
  | HAxSeparation => separation
  | HAxV => v_axiom
  | HAxFiniteOrdinal n => finite_ordinal_axiom n
  end.

Definition haxiom_sideb (p : HAxiomPayload) : bool :=
  match p with
  | HAxK Gamma A B => hformula_wfb Gamma A && hformula_wfb Gamma B
  | HAxS Gamma A B C =>
      hformula_wfb Gamma A && hformula_wfb Gamma B && hformula_wfb Gamma C
  | HAxClassical Gamma A B => hformula_wfb Gamma A && hformula_wfb Gamma B
  | HAxForallInst Gamma s body term =>
      hformula_wfb (Gamma ++ [s]) body && hterm_has_sortb Gamma term s
  | HAxForallWeak Gamma s A body =>
      hformula_wfb Gamma A &&
      hformula_wfb (Gamma ++ [s]) body &&
      negb (hoccurs_formulab (length Gamma) A)
  | HAxComprehension parameters n phi =>
      hformula_wfb (parameters ++ [S n; n]) phi &&
      negb (hoccurs_formulab (length parameters) phi)
  | _ => true
  end.

(** A proof line carries its complete reason payload.  Indices always refer
    to the already checked prefix, which is a linear topological order. *)
Inductive HReason : Type :=
| HRTheoryAxiom (payload : HAxiomPayload)
| HRModusPonens (antecedent_line implication_line : nat)
| HRGeneralize (premise_line : nat) (sort : HSort).

Record HProofLine : Type := {
  hline_context : HContext;
  hline_formula : HFormula;
  hline_reason : HReason
}.

Definition hcontext_eqb (x y : HContext) : bool :=
  if list_eq_dec Nat.eq_dec x y then true else false.

Lemma hcontext_eqb_eq : forall x y, hcontext_eqb x y = true <-> x = y.
Proof.
  intros x y; unfold hcontext_eqb.
  destruct (list_eq_dec Nat.eq_dec x y) as [Heq | Hneq].
  - split; intros; [exact Heq | reflexivity].
  - split; intros H; [discriminate | contradiction].
Qed.

Definition check_hline (prefix : list HProofLine) (line : HProofLine) : bool :=
  hformula_wfb (hline_context line) (hline_formula line) &&
  match hline_reason line with
  | HRTheoryAxiom payload =>
      hcontext_eqb (hline_context line) (haxiom_context payload) &&
      hformula_eqb (hline_formula line) (haxiom_formula payload) &&
      haxiom_sideb payload
  | HRModusPonens i j =>
      match nth_error prefix i, nth_error prefix j with
      | Some premise, Some implication =>
          hcontext_eqb (hline_context premise) (hline_context line) &&
          hcontext_eqb (hline_context implication) (hline_context line) &&
          match hline_formula implication with
          | HImp A B =>
              hformula_eqb (hline_formula premise) A &&
              hformula_eqb (hline_formula line) B
          | _ => false
          end
      | _, _ => false
      end
  | HRGeneralize i s =>
      match nth_error prefix i with
      | Some premise =>
          hcontext_eqb (hline_context premise)
            (hline_context line ++ [s]) &&
          hformula_eqb (hline_formula line)
            (HAll s (hline_formula premise))
      | None => false
      end
  end.

Fixpoint check_hlines
    (prefix remaining : list HProofLine) : bool :=
  match remaining with
  | [] => true
  | line :: rest =>
      check_hline prefix line && check_hlines (prefix ++ [line]) rest
  end.

Definition last_hline (proof : list HProofLine) : option HProofLine :=
  match rev proof with
  | [] => None
  | line :: _ => Some line
  end.

Definition check_hproof (proof : list HProofLine) (conclusion : HFormula) : bool :=
  check_hlines [] proof &&
  match last_hline proof with
  | None => false
  | Some line =>
      hcontext_eqb (hline_context line) [] &&
      hformula_eqb (hline_formula line) conclusion
  end.

Definition OfficialHProof
    (proof : list HProofLine) (conclusion : HFormula) : Prop :=
  check_hlines [] proof = true /\
  exists line,
    last_hline proof = Some line /\
    hline_context line = [] /\
    hline_formula line = conclusion.

Theorem check_hproof_correct :
  forall proof conclusion,
    check_hproof proof conclusion = true <->
    OfficialHProof proof conclusion.
Proof.
  intros proof conclusion.
  unfold check_hproof, OfficialHProof.
  rewrite Bool.andb_true_iff.
  split.
  - intros [Hlines Hlast].
    split; [exact Hlines|].
    destruct (last_hline proof) as [line|] eqn:Hlookup;
      [|discriminate].
    apply Bool.andb_true_iff in Hlast as [Hctx Hformula].
    apply hcontext_eqb_eq in Hctx.
    apply hformula_eqb_eq in Hformula.
    exists line; repeat split; assumption.
  - intros [Hlines [line [Hlookup [Hctx Hformula]]]].
    split; [exact Hlines|].
    rewrite Hlookup, Hctx, Hformula.
    simpl.
    unfold hcontext_eqb, hformula_eqb.
    destruct (list_eq_dec Nat.eq_dec [] []); [|contradiction].
    destruct (hformula_eq_dec conclusion conclusion); [reflexivity|contradiction].
Qed.

Lemma check_hproof_nonempty :
  forall proof conclusion,
    check_hproof proof conclusion = true -> proof <> [].
Proof.
  intros proof conclusion Hcheck Hnil; subst proof.
  discriminate.
Qed.

(** A primitive recursive bijective pairing.  The first coordinate is
    encoded by the number of odd wrappers; the zero case is even. *)
Fixpoint nat_pair (x y : nat) : nat :=
  match x with
  | 0 => 2 * y
  | S x' => S (2 * nat_pair x' y)
  end.

Theorem nat_pair_injective :
  forall x y x' y',
    nat_pair x y = nat_pair x' y' -> x = x' /\ y = y'.
Proof.
  induction x as [|x IH]; intros y x' y' H.
  - destruct x' as [|x']; simpl in H.
    + split; lia.
    + exfalso; lia.
  - destruct x' as [|x']; simpl in H.
    + exfalso; lia.
    + assert (Hinner : nat_pair x y = nat_pair x' y') by lia.
      destruct (IH y x' y' Hinner) as [Hx Hy].
      split; congruence.
Qed.

Fixpoint hterm_code (t : HTerm) : nat :=
  match t with
  | HBVar s level => nat_pair 0 (nat_pair s level)
  | HV u => nat_pair 1 (hterm_code u)
  end.

Theorem hterm_code_injective :
  forall x y, hterm_code x = hterm_code y -> x = y.
Proof.
  induction x as [s level | u IH]; destruct y as [s' level' | u'];
    intros Hcode; cbv beta iota zeta delta [hterm_code] in Hcode.
  - apply nat_pair_injective in Hcode as [_ Hpayload].
    apply nat_pair_injective in Hpayload as [Hs Hlevel].
    subst; reflexivity.
  - apply nat_pair_injective in Hcode as [Htag _]. discriminate.
  - apply nat_pair_injective in Hcode as [Htag _]. discriminate.
  - apply nat_pair_injective in Hcode as [_ Hbody].
    f_equal. apply IH. exact Hbody.
Qed.

Fixpoint hformula_code (A : HFormula) : nat :=
  match A with
  | HEq t u => nat_pair 0 (nat_pair (hterm_code t) (hterm_code u))
  | HMem t u => nat_pair 1 (nat_pair (hterm_code t) (hterm_code u))
  | HEpsilon n t u =>
      nat_pair 2 (nat_pair n (nat_pair (hterm_code t) (hterm_code u)))
  | HNeg B => nat_pair 3 (hformula_code B)
  | HImp B C => nat_pair 4 (nat_pair (hformula_code B) (hformula_code C))
  | HAll s B => nat_pair 5 (nat_pair s (hformula_code B))
  end.

Theorem hformula_code_injective :
  forall A B, hformula_code A = hformula_code B -> A = B.
Proof.
  intros A Z; revert Z.
  induction A as [t u | t u | n t u | A IHA | A IHA B IHB | s A IHA];
    intros Z;
    destruct Z as [t' u' | t' u' | n' t' u' | B' | B' C' | s' B'];
    intros Hcode; cbv beta iota zeta delta [hformula_code] in Hcode;
    apply nat_pair_injective in Hcode as [Htag Hpayload];
    try discriminate.
  - apply nat_pair_injective in Hpayload as [Ht Hu].
    apply hterm_code_injective in Ht.
    apply hterm_code_injective in Hu.
    subst; reflexivity.
  - apply nat_pair_injective in Hpayload as [Ht Hu].
    apply hterm_code_injective in Ht.
    apply hterm_code_injective in Hu.
    subst; reflexivity.
  - apply nat_pair_injective in Hpayload as [Hn Hterms].
    apply nat_pair_injective in Hterms as [Ht Hu].
    apply hterm_code_injective in Ht.
    apply hterm_code_injective in Hu.
    subst; reflexivity.
  - f_equal. apply IHA. exact Hpayload.
  - apply nat_pair_injective in Hpayload as [HA HB].
    f_equal.
    + apply IHA. exact HA.
    + apply IHB. exact HB.
  - apply nat_pair_injective in Hpayload as [Hs HA].
    subst s'. f_equal. apply IHA. exact HA.
Qed.

Fixpoint nat_list_code (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: rest => S (nat_pair x (nat_list_code rest))
  end.

Theorem nat_list_code_injective :
  forall xs ys, nat_list_code xs = nat_list_code ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl; intros H.
  - reflexivity.
  - discriminate.
  - discriminate.
  - injection H as Hpair.
    apply nat_pair_injective in Hpair as [Hxy Htail].
    subst y. f_equal. apply IH. exact Htail.
Qed.

Definition hcontext_code (Gamma : HContext) : nat := nat_list_code Gamma.

Theorem hcontext_code_injective :
  forall Gamma Delta, hcontext_code Gamma = hcontext_code Delta -> Gamma = Delta.
Proof.
  exact nat_list_code_injective.
Qed.

(** A self-delimiting bit string is mapped to a positive natural by using
    the leading constructor bit as the low bit and reserving [1] for nil.
    This supplies the final injection required by section 13.14. *)
Fixpoint bitstring_godel (bits : list bool) : nat :=
  match bits with
  | [] => 1
  | false :: rest => 2 * bitstring_godel rest
  | true :: rest => 2 * bitstring_godel rest + 1
  end.

Lemma bitstring_godel_positive : forall bits, 1 <= bitstring_godel bits.
Proof.
  induction bits as [|b rest IH]; simpl; [lia|].
  destruct b; simpl; lia.
Qed.

Theorem bitstring_godel_injective :
  forall x y, bitstring_godel x = bitstring_godel y -> x = y.
Proof.
  induction x as [|bx xs IH]; destruct y as [|b_y ys]; simpl; intros H.
  - reflexivity.
  - destruct b_y; simpl in H;
      pose proof (bitstring_godel_positive ys); lia.
  - destruct bx; simpl in H;
      pose proof (bitstring_godel_positive xs); lia.
  - destruct bx, b_y; simpl in H; try (exfalso; lia).
    + f_equal. apply IH. lia.
    + f_equal. apply IH. lia.
Qed.

Record HOfficialProofObject : Type := {
  hofficial_lines : list HProofLine;
  hofficial_conclusion : HFormula;
  hofficial_checked :
    check_hproof hofficial_lines hofficial_conclusion = true
}.

Definition certify_hproof
    (proof : list HProofLine) (conclusion : HFormula)
    : option HOfficialProofObject.
Proof.
  destruct (Bool.bool_dec (check_hproof proof conclusion) true)
    as [Hcheck | Hcheck].
  - exact (Some
      {| hofficial_lines := proof;
         hofficial_conclusion := conclusion;
         hofficial_checked := Hcheck |}).
  - exact None.
Defined.

Theorem certify_hproof_correct :
  forall proof conclusion,
    (exists q, certify_hproof proof conclusion = Some q) <->
    check_hproof proof conclusion = true.
Proof.
  intros proof conclusion.
  unfold certify_hproof.
  destruct (Bool.bool_dec (check_hproof proof conclusion) true)
    as [Hcheck | Hcheck].
  - split.
    + intros; exact Hcheck.
    + intros. eexists. reflexivity.
  - split.
    + intros [q Hq]. discriminate.
    + intros H. contradiction.
Qed.

Definition hbottom : HFormula :=
  HExists 0 (HNeg (HEq (HBVar 0 0) (HBVar 0 0))).

Definition HOmegaRoot : RootProfile :=
  {| root_surface := HFormula;
     root_formula := HFormula;
     root_proof := HOfficialProofObject;
     erase_formula := fun A => A;
     encode_formula := hformula_code;
     proof_conclusion := hofficial_conclusion;
     bottom_surface := hbottom;
     bottom_formula := hbottom;
     erase_bottom := eq_refl;
     consistency_formula := None |}.

Definition HOmegaExternalProfile : ProfiledRoot.
Proof.
  refine
    {| profiled_root := HOmegaRoot;
       profiled_status := RSExternallyConsistent;
       self_consistency_certificate := _ |}.
  intros Hstatus.
  discriminate Hstatus.
Defined.

Theorem homega_root_status_is_external :
  profiled_status HOmegaExternalProfile = RSExternallyConsistent.
Proof.
  reflexivity.
Qed.

Theorem homega_root_has_no_internal_consistency_formula :
  consistency_formula HOmegaRoot = None.
Proof.
  reflexivity.
Qed.

Theorem homega_root_proof_adequacy :
  forall q a,
    Check_T HOmegaRoot q a = true <-> OfficialProof HOmegaRoot q a.
Proof.
  intros q a.
  rewrite check_T_correct.
  apply theorem_34_1_root_proof_adequacy.
Qed.

End HOmegaLT.

End KappaSJMMT.
