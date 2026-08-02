From Coq Require Import Lists.List.
From Coq Require Import Logic.Classical_Prop.

Import ListNotations.

Set Implicit Arguments.

Module ConsistencyLattice733.

Inductive star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall x, star R x x
| star_step : forall x y z, R x y -> star R y z -> star R x z.

Lemma star_trans :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    star R x y -> star R y z -> star R x z.
Proof.
  intros A R x y z Hxy.
  revert z.
  induction Hxy as [x|x y mid Hxy Hymid IH]; intros z Hyz.
  - exact Hyz.
  - eapply star_step.
    + exact Hxy.
    + exact (IH z Hyz).
Qed.

Definition subset {A : Type} (P Q : A -> Prop) : Prop :=
  forall x, P x -> Q x.

Definition nonempty {A : Type} (P : A -> Prop) : Prop :=
  exists x, P x.

Definition inter {A : Type} (P Q : A -> Prop) : A -> Prop :=
  fun x => P x /\ Q x.

Definition union {A : Type} (P Q : A -> Prop) : A -> Prop :=
  fun x => P x \/ Q x.

Definition disjoint {A : Type} (P Q : A -> Prop) : Prop :=
  forall x, P x -> Q x -> False.

Definition lower_bound {A : Type}
    (K : A -> Prop) (le : A -> A -> Prop) (x y lb : A) : Prop :=
  K lb /\ le lb x /\ le lb y.

Definition upper_bound {A : Type}
    (K : A -> Prop) (le : A -> A -> Prop) (x y ub : A) : Prop :=
  K ub /\ le x ub /\ le y ub.

Definition glb {A : Type}
    (K : A -> Prop) (le : A -> A -> Prop) (x y lb : A) : Prop :=
  lower_bound K le x y lb /\
  forall m, lower_bound K le x y m -> le m lb.

Definition lub {A : Type}
    (K : A -> Prop) (le : A -> A -> Prop) (x y ub : A) : Prop :=
  upper_bound K le x y ub /\
  forall m, upper_bound K le x y m -> le ub m.

Inductive FmB : Type :=
| BT : FmB
| BF : FmB
| BNeg : FmB -> FmB
| BImp : FmB -> FmB -> FmB.

Inductive CtxB : Type :=
| BHole : CtxB
| CNeg : CtxB -> CtxB
| CImpL : CtxB -> FmB -> CtxB
| CImpR : FmB -> CtxB -> CtxB.

Fixpoint plugB (C : CtxB) (A : FmB) : FmB :=
  match C with
  | BHole => A
  | CNeg D => BNeg (plugB D A)
  | CImpL D B => BImp (plugB D A) B
  | CImpR B D => BImp B (plugB D A)
  end.

Inductive redB : FmB -> FmB -> Prop :=
| red_neg_true : redB (BNeg BT) BF
| red_neg_false : redB (BNeg BF) BT
| red_imp_tt : redB (BImp BT BT) BT
| red_imp_tf : redB (BImp BT BF) BF
| red_imp_ft : redB (BImp BF BT) BT
| red_imp_ff : redB (BImp BF BF) BT.

Inductive stepA : FmB -> FmB -> Prop :=
| stepA_context :
    forall C L R, redB L R -> stepA (plugB C L) (plugB C R).

Definition nfB (A : FmB) : Prop :=
  forall B, ~ stepA A B.

Definition NB_rel (A N : FmB) : Prop :=
  star stepA A N /\
  nfB N /\
  forall M, star stepA A M -> nfB M -> M = N.

Inductive AxB : FmB -> Prop :=
| ax1 : forall A B, AxB (BImp A (BImp B A))
| ax2 :
    forall A B C,
      AxB (BImp (BImp A (BImp B C))
                  (BImp (BImp A B) (BImp A C)))
| ax3 :
    forall A B,
      AxB (BImp (BImp (BNeg B) (BNeg A)) (BImp A B)).

Definition proof_line_ok (seen : list FmB) (A : FmB) : Prop :=
  AxB A \/
  exists P, In P seen /\ In (BImp P A) seen.

Fixpoint valid_proof_from (seen rest : list FmB) : Prop :=
  match rest with
  | [] => True
  | A :: rest' => proof_line_ok seen A /\ valid_proof_from (seen ++ [A]) rest'
  end.

Definition BProof (pi : list FmB) : Prop :=
  pi <> [] /\ valid_proof_from [] pi.

Definition last_is (A : FmB) (pi : list FmB) : Prop :=
  exists prefix, pi = prefix ++ [A].

Definition proves_by_sequence (A : FmB) : Prop :=
  exists pi, BProof pi /\ last_is A pi.

Inductive derivesB : FmB -> Prop :=
| derives_ax : forall A, AxB A -> derivesB A
| derives_mp : forall A B, derivesB A -> derivesB (BImp A B) -> derivesB B.

Definition BKernel : FmB -> Prop := proves_by_sequence.

Definition CKernel (C : FmB) : Prop :=
  exists A, BKernel A /\ C = BNeg A.

Definition separated_consistencyB : Prop :=
  forall A C NA NC,
    BKernel A ->
    CKernel C ->
    NB_rel A NA ->
    NB_rel C NC ->
    NA <> NC.

Theorem boolean_truth_false_separation :
  (forall A, BKernel A -> NB_rel A BT) ->
  (forall A, BKernel A -> NB_rel (BNeg A) BF) ->
  separated_consistencyB.
Proof.
  intros Htrue Hfalse A C NA NC HA HC HNA HNC.
  destruct HC as [P [HP HC]].
  subst C.
  pose proof (Htrue A HA) as [_ [_ HuniqA]].
  pose proof (Hfalse P HP) as [_ [_ HuniqC]].
  specialize (HuniqA NA (proj1 HNA) (proj1 (proj2 HNA))).
  specialize (HuniqC NC (proj1 HNC) (proj1 (proj2 HNC))).
  subst NA NC.
  discriminate.
Qed.

Section AbstractLayers.

Variable W : Type.

Definition WSet : Type := W -> Prop.

Record TwoLayerRewrite : Type := {
  tl_X0 : WSet;
  tl_Y0 : WSet;
  tl_stepX : W -> W -> Prop;
  tl_stepY : W -> W -> Prop
}.

Definition reachable (R : W -> W -> Prop) (S : WSet) : WSet :=
  fun w => exists s, S s /\ star R s w.

Definition RX (S : TwoLayerRewrite) : WSet :=
  reachable (tl_stepX S) (tl_X0 S).

Definition RY (S : TwoLayerRewrite) : WSet :=
  reachable (tl_stepY S) (tl_Y0 S).

Definition normal (R : W -> W -> Prop) (n : W) : Prop :=
  forall z, ~ R n z.

Definition NF_of (R : W -> W -> Prop) (S : WSet) : WSet :=
  fun n => exists s, S s /\ star R s n /\ normal R n.

Definition SourceConverges (R : W -> W -> Prop) (S : WSet) (n : W) : Prop :=
  NF_of R S n /\ forall s, S s -> star R s n.

Definition Converges (R : W -> W -> Prop) (S : WSet) (n : W) : Prop :=
  SourceConverges R S n /\ forall m, NF_of R S m -> m = n.

Definition subset_condition (S : TwoLayerRewrite) : Prop :=
  subset (RX S) (RY S).

Definition weak_separation (S : TwoLayerRewrite) : Prop :=
  exists Z : WSet,
    subset Z (RY S) /\
    nonempty Z /\
    disjoint Z (RX S) /\
    nonempty (NF_of (tl_stepY S) (RX S)) /\
    nonempty (NF_of (tl_stepY S) Z) /\
    disjoint (NF_of (tl_stepY S) (RX S)) (NF_of (tl_stepY S) Z).

Definition pointwise_separation (S : TwoLayerRewrite) : Prop :=
  exists (Z : WSet) (nX nZ : W),
    subset Z (RY S) /\
    nonempty Z /\
    disjoint Z (RX S) /\
    Converges (tl_stepY S) (RX S) nX /\
    Converges (tl_stepY S) Z nZ /\
    nX <> nZ.

Theorem pointwise_separation_implies_weak :
  forall S, pointwise_separation S -> weak_separation S.
Proof.
  intros S [Z [nX [nZ [HZsub [HZne [HZdis [HX [HZ Hneq]]]]]]]].
  destruct HX as [[HNFx _] Huniqx].
  destruct HZ as [[HNFz _] Huniqz].
  exists Z.
  repeat split.
  - exact HZsub.
  - exact HZne.
  - exact HZdis.
  - exists nX; exact HNFx.
  - exists nZ; exact HNFz.
  - intros n Hnx Hnz.
    pose proof (Huniqx n Hnx) as Hn.
    subst n.
    pose proof (Huniqz nX Hnz) as Hxz.
    exact (Hneq Hxz).
Qed.

Definition replace_stepY (S : TwoLayerRewrite) (R : W -> W -> Prop)
    : TwoLayerRewrite :=
  {| tl_X0 := tl_X0 S;
     tl_Y0 := tl_Y0 S;
     tl_stepX := tl_stepX S;
     tl_stepY := R |}.

Definition Y_family (S : TwoLayerRewrite) (R : W -> W -> Prop) : Prop :=
  pointwise_separation (replace_stepY S R).

Definition V_rel (R : W -> W -> Prop) (A : WSet) (n : W) : Prop :=
  Converges R A n.

Definition semantically_determinate (R : W -> W -> Prop) (A : WSet) : Prop :=
  exists n, V_rel R A n.

Definition fusion_Z (S : TwoLayerRewrite) (Z A B : WSet) : Prop :=
  subset Z (RY S) /\
  subset A (RX S) /\
  subset B (RX S) /\
  exists (R : W -> W -> Prop) (nA nB nZ : W),
    Y_family S R /\
    V_rel R A nA /\
    V_rel R B nB /\
    nA = nB /\
    V_rel R Z nZ /\
    nZ <> nA.

Definition co_identifies
    (S : TwoLayerRewrite) (R D : W -> W -> Prop) : Prop :=
  Y_family S R /\
  Y_family S D /\
  exists (A Z : WSet) (nRA nRZ nDA nDZ : W),
    nonempty A /\
    subset A (RX S) /\
    subset Z (RY S) /\
    V_rel R A nRA /\
    V_rel R Z nRZ /\
    nRA <> nRZ /\
    V_rel D A nDA /\
    V_rel D Z nDZ /\
    nDA <> nDZ.

Definition KZ (S : TwoLayerRewrite) (Z A : WSet) : Prop :=
  subset A (RX S) /\ fusion_Z S Z A A.

Definition leZ (_S : TwoLayerRewrite) (_Z : WSet) (A B : WSet) : Prop :=
  subset A B.

Definition meetZ (S : TwoLayerRewrite) (Z A B M : WSet) : Prop :=
  M = inter A B /\ KZ S Z M.

Definition joinZ (S : TwoLayerRewrite) (Z A B J : WSet) : Prop :=
  fusion_Z S Z A B /\ J = union A B /\ KZ S Z J.

Definition join_conflict (S : TwoLayerRewrite) (Z A B : WSet) : Prop :=
  ~ (fusion_Z S Z A B /\ KZ S Z (union A B)).

Theorem lattice_closure_theorem :
  forall S Z,
    (forall A B, KZ S Z A -> KZ S Z B -> KZ S Z (inter A B)) ->
    (forall A B,
        KZ S Z A -> KZ S Z B -> fusion_Z S Z A B ->
        KZ S Z (union A B)) ->
    forall A B,
      KZ S Z A ->
      KZ S Z B ->
      glb (KZ S Z) (@subset W) A B (inter A B) /\
      (fusion_Z S Z A B ->
       lub (KZ S Z) (@subset W) A B (union A B)).
Proof.
  intros S Z Hmeet Hjoin A B HA HB.
  split.
  - unfold glb.
    split.
    + unfold lower_bound.
      split.
      * exact (Hmeet A B HA HB).
      * split.
        -- unfold subset, inter; tauto.
        -- unfold subset, inter; tauto.
    + intros M HM x HxM.
      unfold lower_bound in HM.
      destruct HM as [_ [HMA HMB]].
      split; [exact (HMA x HxM) | exact (HMB x HxM)].
  - intros Hcompat.
    unfold lub.
    split.
    + unfold upper_bound.
      split.
      * exact (Hjoin A B HA HB Hcompat).
      * split.
        -- unfold subset, union; tauto.
        -- unfold subset, union; tauto.
    + intros M HM x HxU.
      unfold union in HxU.
      destruct HxU as [HxA | HxB].
      * unfold upper_bound in HM.
        destruct HM as [_ [HAM _]].
        exact (HAM x HxA).
      * unfold upper_bound in HM.
        destruct HM as [_ [_ HBM]].
        exact (HBM x HxB).
Qed.

End AbstractLayers.

Section MetricProjection.

Variable W : Type.
Variable Der : Type.
Variable root : Der -> W.
Variable trueW falseW : W.

Record StrictTotalOrder
    (K : Type) (lt le : K -> K -> Prop) : Prop := {
  sto_irrefl : forall x, ~ lt x x;
  sto_trans : forall x y z, lt x y -> lt y z -> lt x z;
  sto_le_iff : forall x y, le x y <-> x = y \/ lt x y;
  sto_total : forall x y, x = y \/ lt x y \/ lt y x
}.

Record MetricProjection : Type := {
  mp_K : Type;
  mp_lt : mp_K -> mp_K -> Prop;
  mp_le : mp_K -> mp_K -> Prop;
  mp_order : StrictTotalOrder mp_lt mp_le;
  mp_mu : W -> W;
  mp_key_term : mp_K -> W;
  mp_compare : mp_K -> mp_K -> W;
  mp_step : W -> W -> Prop;
  mp_h : Der -> mp_K;
  mp_projection :
    forall d, star mp_step (mp_mu (root d)) (mp_key_term (mp_h d));
  mp_compare_true :
    forall k1 k2, mp_lt k1 k2 -> mp_step (mp_compare k1 k2) trueW;
  mp_compare_true_reflect :
    forall k1 k2, mp_step (mp_compare k1 k2) trueW -> mp_lt k1 k2;
  mp_compare_false :
    forall k1 k2, mp_le k2 k1 -> mp_step (mp_compare k1 k2) falseW;
  mp_compare_false_reflect :
    forall k1 k2, mp_step (mp_compare k1 k2) falseW -> mp_le k2 k1
}.

Record RosserShape (M : MetricProjection) : Type := {
  rs_rho : W;
  rs_neg_rho : W;
  rs_d_neg : Der;
  rs_d_pos : Der;
  rs_root_neg : root rs_d_neg = rs_neg_rho;
  rs_root_pos : root rs_d_pos = rs_rho;
  rs_equation :
    rs_rho = mp_compare M (mp_h M rs_d_neg) (mp_h M rs_d_pos)
}.

Lemma compare_reduces_true :
  forall (M : MetricProjection) (k1 k2 : mp_K M) rho,
    rho = mp_compare M k1 k2 ->
    mp_lt M k1 k2 ->
    star (mp_step M) rho trueW.
Proof.
  intros M k1 k2 rho Hrho Hlt.
  subst rho.
  eapply star_step.
  - exact (mp_compare_true M k1 k2 Hlt).
  - exact (star_refl (mp_step M) trueW).
Qed.

Lemma compare_reduces_false :
  forall (M : MetricProjection) (k1 k2 : mp_K M) rho,
    rho = mp_compare M k1 k2 ->
    mp_le M k2 k1 ->
    star (mp_step M) rho falseW.
Proof.
  intros M k1 k2 rho Hrho Hle.
  subst rho.
  eapply star_step.
  - exact (mp_compare_false M k1 k2 Hle).
  - exact (star_refl (mp_step M) falseW).
Qed.

Theorem compare_step_true_iff :
  forall (M : MetricProjection) (k1 k2 : mp_K M),
    mp_step M (mp_compare M k1 k2) trueW <->
    mp_lt M k1 k2.
Proof.
  intros M k1 k2.
  split.
  - exact (mp_compare_true_reflect M k1 k2).
  - exact (mp_compare_true M k1 k2).
Qed.

Theorem compare_step_false_iff :
  forall (M : MetricProjection) (k1 k2 : mp_K M),
    mp_step M (mp_compare M k1 k2) falseW <->
    mp_le M k2 k1.
Proof.
  intros M k1 k2.
  split.
  - exact (mp_compare_false_reflect M k1 k2).
  - exact (mp_compare_false M k1 k2).
Qed.

Theorem rosser_projection_reaches_keys :
  forall (M : MetricProjection) (R : RosserShape M),
    star (mp_step M)
      (mp_mu M (rs_neg_rho R))
      (mp_key_term M (mp_h M (rs_d_neg R))) /\
    star (mp_step M)
      (mp_mu M (rs_rho R))
      (mp_key_term M (mp_h M (rs_d_pos R))).
Proof.
  intros M R.
  destruct R as [rho neg_rho d_neg d_pos Hroot_neg Hroot_pos Heq].
  simpl.
  split.
  - rewrite <- Hroot_neg.
    exact (mp_projection M d_neg).
  - rewrite <- Hroot_pos.
    exact (mp_projection M d_pos).
Qed.

Theorem rosser_compare_true_step_iff :
  forall (M : MetricProjection) (R : RosserShape M),
    mp_step M (rs_rho R) trueW <->
    mp_lt M (mp_h M (rs_d_neg R)) (mp_h M (rs_d_pos R)).
Proof.
  intros M R.
  destruct R as [rho neg_rho d_neg d_pos Hroot_neg Hroot_pos Heq].
  simpl.
  split.
  - intro Hstep.
    rewrite Heq in Hstep.
    exact (mp_compare_true_reflect M (mp_h M d_neg) (mp_h M d_pos) Hstep).
  - intro Hlt.
    rewrite Heq.
    exact (mp_compare_true M (mp_h M d_neg) (mp_h M d_pos) Hlt).
Qed.

Theorem rosser_compare_false_step_iff :
  forall (M : MetricProjection) (R : RosserShape M),
    mp_step M (rs_rho R) falseW <->
    mp_le M (mp_h M (rs_d_pos R)) (mp_h M (rs_d_neg R)).
Proof.
  intros M R.
  destruct R as [rho neg_rho d_neg d_pos Hroot_neg Hroot_pos Heq].
  simpl.
  split.
  - intro Hstep.
    rewrite Heq in Hstep.
    exact (mp_compare_false_reflect M (mp_h M d_neg) (mp_h M d_pos) Hstep).
  - intro Hle.
    rewrite Heq.
    exact (mp_compare_false M (mp_h M d_neg) (mp_h M d_pos) Hle).
Qed.

Theorem metric_sensitivity :
  forall (M1 M2 : MetricProjection)
      (rho : W)
      (kneg1 kpos1 : mp_K M1)
      (kneg2 kpos2 : mp_K M2),
    rho = mp_compare M1 kneg1 kpos1 ->
    rho = mp_compare M2 kneg2 kpos2 ->
    mp_lt M1 kneg1 kpos1 ->
    mp_le M2 kpos2 kneg2 ->
    star (mp_step M1) rho trueW /\
    star (mp_step M2) rho falseW.
Proof.
  intros M1 M2 rho kneg1 kpos1 kneg2 kpos2 Hrho1 Hrho2 Hlt Hle.
  split.
  - exact (@compare_reduces_true M1 kneg1 kpos1 rho Hrho1 Hlt).
  - exact (@compare_reduces_false M2 kneg2 kpos2 rho Hrho2 Hle).
Qed.

Corollary metric_sensitivity_projection_dependence :
  trueW <> falseW ->
  forall (M1 M2 : MetricProjection)
      (rho : W)
      (kneg1 kpos1 : mp_K M1)
      (kneg2 kpos2 : mp_K M2),
    rho = mp_compare M1 kneg1 kpos1 ->
    rho = mp_compare M2 kneg2 kpos2 ->
    mp_lt M1 kneg1 kpos1 ->
    mp_le M2 kpos2 kneg2 ->
    exists b1 b2,
      star (mp_step M1) rho b1 /\
      star (mp_step M2) rho b2 /\
      b1 <> b2.
Proof.
  intros Htf M1 M2 rho kneg1 kpos1 kneg2 kpos2 Hrho1 Hrho2 Hlt Hle.
  destruct (@metric_sensitivity
      M1 M2 rho kneg1 kpos1 kneg2 kpos2 Hrho1 Hrho2 Hlt Hle)
    as [HT HF].
  exists trueW, falseW.
  repeat split; assumption.
Qed.

End MetricProjection.

Record CLatSystem : Type := {
  fs_formula : Type;
  fs_formula_matches : fs_formula = FmB;
  fs_context : Type;
  fs_context_matches : fs_context = CtxB;
  fs_plug : CtxB -> FmB -> FmB;
  fs_plug_matches : fs_plug = plugB;
  fs_boolean_step : FmB -> FmB -> Prop;
  fs_boolean_step_matches : fs_boolean_step = stepA;
  fs_boolean_kernel : FmB -> Prop;
  fs_boolean_kernel_matches : fs_boolean_kernel = BKernel;
  fs_W : Type;
  fs_layer : TwoLayerRewrite fs_W;
  fs_X0 : fs_W -> Prop;
  fs_X0_matches : fs_X0 = tl_X0 fs_layer;
  fs_Y0 : fs_W -> Prop;
  fs_Y0_matches : fs_Y0 = tl_Y0 fs_layer;
  fs_stepX : fs_W -> fs_W -> Prop;
  fs_stepX_matches : fs_stepX = tl_stepX fs_layer;
  fs_stepY : fs_W -> fs_W -> Prop;
  fs_stepY_matches : fs_stepY = tl_stepY fs_layer;
  fs_RX : fs_W -> Prop;
  fs_RX_matches : fs_RX = RX fs_layer;
  fs_RY : fs_W -> Prop;
  fs_RY_matches : fs_RY = RY fs_layer;
  fs_NFY : (fs_W -> Prop) -> fs_W -> Prop;
  fs_NFY_matches : fs_NFY = NF_of (tl_stepY fs_layer);
  fs_Y_family : (fs_W -> fs_W -> Prop) -> Prop;
  fs_Y_family_matches : fs_Y_family = Y_family fs_layer;
  fs_VC : (fs_W -> fs_W -> Prop) -> (fs_W -> Prop) -> fs_W -> Prop;
  fs_VC_matches : fs_VC = @V_rel fs_W;
  fs_background : fs_W -> Prop;
  fs_equivZ : (fs_W -> Prop) -> (fs_W -> Prop) -> Prop;
  fs_equivZ_matches : fs_equivZ = fusion_Z fs_layer fs_background;
  fs_parallel :
    (fs_W -> fs_W -> Prop) -> (fs_W -> fs_W -> Prop) -> Prop;
  fs_parallel_matches : fs_parallel = co_identifies fs_layer;
  fs_KZ : (fs_W -> Prop) -> Prop;
  fs_KZ_matches : fs_KZ = KZ fs_layer fs_background;
  fs_order : (fs_W -> Prop) -> (fs_W -> Prop) -> Prop;
  fs_order_matches : fs_order = leZ fs_layer fs_background;
  fs_meetZ :
    (fs_W -> Prop) -> (fs_W -> Prop) -> (fs_W -> Prop) -> Prop;
  fs_meetZ_matches : fs_meetZ = meetZ fs_layer fs_background;
  fs_joinZ :
    (fs_W -> Prop) -> (fs_W -> Prop) -> (fs_W -> Prop) -> Prop;
  fs_joinZ_matches : fs_joinZ = joinZ fs_layer fs_background;
  fs_join_conflict : (fs_W -> Prop) -> (fs_W -> Prop) -> Prop;
  fs_join_conflict_matches :
    fs_join_conflict = join_conflict fs_layer fs_background;
  fs_truth : fs_W;
  fs_falsehood : fs_W;
  fs_Der : Type;
  fs_root : fs_Der -> fs_W;
  fs_metric : @MetricProjection fs_W fs_Der fs_root fs_truth fs_falsehood;
  fs_compare : mp_K fs_metric -> mp_K fs_metric -> fs_W;
  fs_compare_matches : fs_compare = mp_compare fs_metric;
  fs_rho : fs_W;
  fs_rosser_shape :
    @RosserShape fs_W fs_Der fs_root fs_truth fs_falsehood fs_metric;
  fs_rho_matches : fs_rho = rs_rho fs_rosser_shape
}.

End ConsistencyLattice733.
