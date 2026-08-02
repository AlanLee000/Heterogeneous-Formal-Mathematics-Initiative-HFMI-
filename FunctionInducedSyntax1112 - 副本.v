From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.
From Coq Require Import Relations.Relation_Definitions.

Import ListNotations.

Module FunctionInducedSyntax1112.

Inductive label : Type :=
| LSort | LBaseTy | LProdTy | LArrTy | LPiTy
| LKTerm | LKForm | LKCode | LKJudg | LKRule | LKRuleTr | LKFrag | LKClOp
| LObjSh | LProdSh | LMapSh | LDepMapSh | LVal
| LRecIO | LRecCtx | LRecComp | LRecIter | LRecRed | LRecInt
| LProtCtx | LProtComp | LProtIter | LProtRed | LProtInt
| LCtxHole | LCtxVar | LCtxConst | LCtxTuple | LCtxApp | LCtxQuote
| LJdg | LInfRule | LFragObj.

Definition label_code (l : label) : nat :=
  match l with
  | LSort => 0 | LBaseTy => 1 | LProdTy => 2 | LArrTy => 3 | LPiTy => 4
  | LKTerm => 10 | LKForm => 11 | LKCode => 12 | LKJudg => 13
  | LKRule => 14 | LKRuleTr => 15 | LKFrag => 16 | LKClOp => 17
  | LObjSh => 20 | LProdSh => 21 | LMapSh => 22 | LDepMapSh => 23
  | LVal => 30
  | LRecIO => 40 | LRecCtx => 41 | LRecComp => 42 | LRecIter => 43
  | LRecRed => 44 | LRecInt => 45
  | LProtCtx => 46 | LProtComp => 47 | LProtIter => 48
  | LProtRed => 49 | LProtInt => 50
  | LCtxHole => 60 | LCtxVar => 61 | LCtxConst => 62
  | LCtxTuple => 63 | LCtxApp => 64 | LCtxQuote => 65
  | LJdg => 70 | LInfRule => 71 | LFragObj => 72
  end.

Theorem label_code_injective :
  forall a b, label_code a = label_code b -> a = b.
Proof.
  destruct a, b; simpl; intros H; try discriminate; reflexivity.
Qed.

Inductive kind : Type :=
| KTerm | KForm | KCode | KJudg | KRule | KRuleTr | KFrag | KClOp.

Record sort : Type := Sort {
  skind : kind;
  slev : nat;
  stag : nat
}.

Definition TermSort (i : nat) : sort := Sort KTerm i 0.
Definition FormSort (i : nat) : sort := Sort KForm i 0.
Definition CodeSort (i : nat) : sort := Sort KCode (S i) 0.

Inductive kind_dep : kind -> kind -> Prop :=
| KD_Term_Term : kind_dep KTerm KTerm
| KD_Term_Form : kind_dep KTerm KForm
| KD_Term_Judg : kind_dep KTerm KJudg
| KD_Term_Rule : kind_dep KTerm KRule
| KD_Term_RuleTr : kind_dep KTerm KRuleTr
| KD_Term_Frag : kind_dep KTerm KFrag
| KD_Term_ClOp : kind_dep KTerm KClOp
| KD_Form_Judg : kind_dep KForm KJudg
| KD_Form_Rule : kind_dep KForm KRule
| KD_Form_RuleTr : kind_dep KForm KRuleTr
| KD_Form_Frag : kind_dep KForm KFrag
| KD_Form_ClOp : kind_dep KForm KClOp
| KD_Judg_Rule : kind_dep KJudg KRule
| KD_Judg_RuleTr : kind_dep KJudg KRuleTr
| KD_Judg_Frag : kind_dep KJudg KFrag
| KD_Rule_RuleTr : kind_dep KRule KRuleTr
| KD_Rule_Frag : kind_dep KRule KFrag
| KD_RuleTr_Frag : kind_dep KRuleTr KFrag
| KD_Frag_RuleTr : kind_dep KFrag KRuleTr
| KD_Frag_ClOp : kind_dep KFrag KClOp
| KD_ClOp_ClOp : kind_dep KClOp KClOp.

Definition dep (s t : sort) : Prop :=
  slev s <= slev t /\ (skind s = KCode \/ kind_dep (skind s) (skind t)).

Theorem no_same_level_form_to_term_dep :
  forall i, ~ dep (FormSort i) (TermSort i).
Proof.
  intros i [_ [Hcode | Hdep]].
  - discriminate Hcode.
  - inversion Hdep.
Qed.

Inductive ty : Type :=
| Base : sort -> ty
| Prod : list ty -> ty
| Arr : ty -> ty -> ty
| Pi : ty -> list ty -> ty.

Inductive shape : Type :=
| ObjSh : sort -> shape
| ProdSh : list shape -> shape
| MapSh : shape -> shape -> shape
| DepMapSh : shape -> list shape -> shape.

Definition nonempty {A : Type} (xs : list A) : Prop :=
  exists x, In x xs.

Fixpoint sorts_in (tau : ty) : list sort :=
  match tau with
  | Base s => [s]
  | Prod ts => concat (map sorts_in ts)
  | Arr a b => sorts_in a ++ sorts_in b
  | Pi a bs => sorts_in a ++ concat (map sorts_in bs)
  end.

Fixpoint shape_of (tau : ty) : shape :=
  match tau with
  | Base s => ObjSh s
  | Prod ts => ProdSh (map shape_of ts)
  | Arr a b => MapSh (shape_of a) (shape_of b)
  | Pi a bs => DepMapSh (shape_of a) (map shape_of bs)
  end.

Definition arr_ok (sigma tau : ty) : Prop :=
  forall s t, In s (sorts_in sigma) -> In t (sorts_in tau) -> dep s t.

Inductive ty_ok : ty -> Prop :=
| TyBase :
    forall s, ty_ok (Base s)
| TyProd :
    forall ts,
      nonempty ts ->
      Forall ty_ok ts ->
      ty_ok (Prod ts)
| TyArr :
    forall sigma tau,
      ty_ok sigma ->
      ty_ok tau ->
      arr_ok sigma tau ->
      ty_ok (Arr sigma tau)
| TyPi :
    forall sigma branches,
      ty_ok sigma ->
      nonempty branches ->
      Forall ty_ok branches ->
      Forall (arr_ok sigma) branches ->
      ty_ok (Pi sigma branches).

Theorem no_same_level_formula_to_term_arrow :
  forall i, ~ ty_ok (Arr (Base (FormSort i)) (Base (TermSort i))).
Proof.
  intros i H.
  inversion H; subst.
  unfold arr_ok in H4.
  specialize (H4 (FormSort i) (TermSort i)).
  simpl in H4.
  apply no_same_level_form_to_term_dep with (i := i).
  apply H4; left; reflexivity.
Qed.

Fixpoint subsh (H : shape) : list shape :=
  match H with
  | ObjSh _ => [H]
  | ProdSh hs => H :: concat (map subsh hs)
  | MapSh a b => H :: subsh a ++ subsh b
  | DepMapSh a bs => H :: subsh a ++ concat (map subsh bs)
  end.

Fixpoint obj_sorts (H : shape) : list sort :=
  match H with
  | ObjSh s => [s]
  | ProdSh hs => concat (map obj_sorts hs)
  | MapSh a b => obj_sorts a ++ obj_sorts b
  | DepMapSh a bs => obj_sorts a ++ concat (map obj_sorts bs)
  end.

Definition quote_sort (s : sort) : option sort :=
  match skind s with
  | KCode => None
  | _ => Some (Sort KCode (S (slev s)) (stag s))
  end.

Inductive qsort_closure : list sort -> sort -> Prop :=
| QSort_base :
    forall B s, In s B -> qsort_closure B s
| QSort_quote :
    forall B s q,
      qsort_closure B s ->
      quote_sort s = Some q ->
      qsort_closure B q.

Inductive context_shape (tau : ty) : shape -> Prop :=
| CSh_subshape :
    forall H, In H (subsh (shape_of tau)) -> context_shape tau H
| CSh_quote_sort :
    forall s,
      qsort_closure (obj_sorts (shape_of tau)) s ->
      context_shape tau (ObjSh s)
| CSh_prod :
    forall hs,
      nonempty hs ->
      Forall (context_shape tau) hs ->
      context_shape tau (ProdSh hs).

Inductive value : Type :=
| VAtom : sort -> nat -> value
| VTuple : list value -> value
| VFunGraph : list (value * value) -> value
| VDepFunGraph : list (value * value) -> value.

Inductive val_ok : ty -> value -> Prop :=
| ValBase :
    forall s n, val_ok (Base s) (VAtom s n)
| ValProd :
    forall ts xs,
      Forall2 val_ok ts xs ->
      val_ok (Prod ts) (VTuple xs)
| ValArr :
    forall sigma tau graph,
      Forall
        (fun xy => val_ok sigma (fst xy) /\ val_ok tau (snd xy))
        graph ->
      val_ok (Arr sigma tau) (VFunGraph graph)
| ValPi :
    forall sigma branches graph,
      Forall
        (fun xy =>
          val_ok sigma (fst xy) /\
          exists tau, In tau branches /\ val_ok tau (snd xy))
        graph ->
      val_ok (Pi sigma branches) (VDepFunGraph graph).

Inductive shval : shape -> value -> Prop :=
| ShValObj :
    forall s n, shval (ObjSh s) (VAtom s n)
| ShValProd :
    forall hs xs,
      Forall2 shval hs xs ->
      shval (ProdSh hs) (VTuple xs)
| ShValMap :
    forall a b graph,
      Forall
        (fun xy => shval a (fst xy) /\ shval b (snd xy))
        graph ->
      shval (MapSh a b) (VFunGraph graph)
| ShValDep :
    forall a bs graph,
      Forall
        (fun xy =>
          shval a (fst xy) /\
          exists h, In h bs /\ shval h (snd xy))
        graph ->
      shval (DepMapSh a bs) (VDepFunGraph graph).

Inductive ctx : Type :=
| CtxHole : shape -> ctx
| CtxVar : sort -> nat -> ctx
| CtxConst : shape -> value -> ctx
| CtxTuple : list ctx -> ctx
| CtxApp : ctx -> ctx -> ctx
| CtxQuote : ctx -> ctx.

Inductive ctx_ok (tau : ty) : shape -> ctx -> Prop :=
| CtxOKHole :
    ctx_ok tau (shape_of tau) (CtxHole (shape_of tau))
| CtxOKVar :
    forall s q,
      context_shape tau (ObjSh s) ->
      ctx_ok tau (ObjSh s) (CtxVar s q)
| CtxOKConst :
    forall H a,
      context_shape tau H ->
      shval H a ->
      ctx_ok tau H (CtxConst H a)
| CtxOKTuple :
    forall hs cs,
      Forall (context_shape tau) hs ->
      Forall2 (ctx_ok tau) hs cs ->
      ctx_ok tau (ProdSh hs) (CtxTuple cs)
| CtxOKApp :
    forall K L F A,
      context_shape tau (MapSh K L) ->
      ctx_ok tau (MapSh K L) F ->
      ctx_ok tau K A ->
      ctx_ok tau L (CtxApp F A)
| CtxOKDepApp :
    forall K hs F x H,
      context_shape tau (DepMapSh K hs) ->
      In H hs ->
      shval K x ->
      ctx_ok tau (DepMapSh K hs) F ->
      ctx_ok tau H (CtxApp F (CtxConst K x))
| CtxOKQuote :
    forall s q C,
      quote_sort s = Some q ->
      context_shape tau (ObjSh q) ->
      ctx_ok tau (ObjSh s) C ->
      ctx_ok tau (ObjSh q) (CtxQuote C).

Inductive record : Type :=
| RecIO : value -> value -> record
| RecCtx : ctx -> record -> record
| RecComp : record -> record -> record
| RecIter : nat -> record -> record
| RecRed : list record -> record
| RecInt : list record -> record.

Inductive fun_ty : ty -> Prop :=
| FunArr : forall a b, fun_ty (Arr a b)
| FunPi : forall a bs, fun_ty (Pi a bs).

Definition unit_input : value := VAtom (TermSort 0) 0.

Definition io_record_ok (tau : ty) (x y : value) : Prop :=
  match tau with
  | Arr sigma upsilon => val_ok sigma x /\ val_ok upsilon y
  | Pi sigma branches =>
      val_ok sigma x /\
      exists branch, In branch branches /\ val_ok branch y
  | _ => x = unit_input /\ val_ok tau y
  end.

Inductive rec_ok (tau : ty) : record -> Prop :=
| RecOKIO :
    forall x y,
      io_record_ok tau x y ->
      rec_ok tau (RecIO x y)
| RecOKCtx :
    forall C r,
      ctx_ok tau (shape_of tau) C ->
      rec_ok tau r ->
      rec_ok tau (RecCtx C r)
| RecOKComp :
    forall r s,
      rec_ok tau r ->
      rec_ok tau s ->
      rec_ok tau (RecComp r s)
| RecOKIter :
    forall n r,
      rec_ok tau r ->
      rec_ok tau (RecIter n r)
| RecOKRed :
    forall rs,
      Forall (rec_ok tau) rs ->
      rec_ok tau (RecRed rs)
| RecOKInt :
    forall rs,
      Forall (rec_ok tau) rs ->
      rec_ok tau (RecInt rs).

Definition relation_on_records := record -> record -> Prop.

Record equiv_props (R : relation_on_records) : Prop := {
  equiv_refl : forall r, R r r;
  equiv_sym : forall r s, R r s -> R s r;
  equiv_trans : forall r s t, R r s -> R s t -> R r t
}.

Record protocol (tau : ty) : Type := {
  raw_obs : record -> Prop;
  proto_equiv : relation_on_records;
  allowed_ctx : ctx -> Prop;
  allowed_comp : record -> record -> Prop;
  allowed_iter : nat -> record -> Prop;
  allowed_red : list record -> Prop;
  allowed_int : list record -> Prop;
  proto_raw_ok : forall r, raw_obs r -> rec_ok tau r;
  proto_equiv_ok : equiv_props proto_equiv;
  proto_ctx_ok :
    forall C, allowed_ctx C -> ctx_ok tau (shape_of tau) C;
  proto_comp_ok :
    forall r s, allowed_comp r s -> rec_ok tau r /\ rec_ok tau s;
  proto_iter_ok :
    forall n r, allowed_iter n r -> rec_ok tau r;
  proto_red_ok :
    forall rs, allowed_red rs -> Forall (rec_ok tau) rs;
  proto_int_ok :
    forall rs, allowed_int rs -> Forall (rec_ok tau) rs
}.

Inductive obs_closure {tau : ty} (P : protocol tau) : record -> Prop :=
| ObsRaw :
    forall r,
      raw_obs tau P r ->
      obs_closure P r
| ObsEquiv :
    forall r s,
      obs_closure P r ->
      proto_equiv tau P r s ->
      obs_closure P s
| ObsCtx :
    forall C r,
      allowed_ctx tau P C ->
      obs_closure P r ->
      obs_closure P (RecCtx C r)
| ObsComp :
    forall r s,
      allowed_comp tau P r s ->
      obs_closure P r ->
      obs_closure P s ->
      obs_closure P (RecComp r s)
| ObsIter :
    forall n r,
      allowed_iter tau P n r ->
      obs_closure P r ->
      obs_closure P (RecIter n r)
| ObsRed :
    forall rs,
      allowed_red tau P rs ->
      obs_closure_list P rs ->
      obs_closure P (RecRed rs)
| ObsInt :
    forall rs,
      allowed_int tau P rs ->
      obs_closure_list P rs ->
      obs_closure P (RecInt rs)
with obs_closure_list {tau : ty} (P : protocol tau) : list record -> Prop :=
| ObsListNil :
    obs_closure_list P []
| ObsListCons :
    forall r rs,
      obs_closure P r ->
      obs_closure_list P rs ->
      obs_closure_list P (r :: rs).

Definition pseudo (r s : record) : Prop :=
  exists C, r = RecCtx C s \/ s = RecCtx C r.

Definition record_congruence (R : relation_on_records) : Prop :=
  (forall C r s, R r s -> R (RecCtx C r) (RecCtx C s)) /\
  (forall r r' s s',
      R r r' -> R s s' -> R (RecComp r s) (RecComp r' s')) /\
  (forall n r s, R r s -> R (RecIter n r) (RecIter n s)) /\
  (forall rs ss,
      Forall2 R rs ss -> R (RecRed rs) (RecRed ss)) /\
  (forall rs ss,
      Forall2 R rs ss -> R (RecInt rs) (RecInt ss)).

Definition subst := sort -> value -> value.

Fixpoint subst_value (theta : subst) (v : value) : value :=
  match v with
  | VAtom s n => theta s (VAtom s n)
  | VTuple xs => VTuple (map (subst_value theta) xs)
  | VFunGraph graph =>
      VFunGraph
        (map
          (fun xy => (subst_value theta (fst xy), subst_value theta (snd xy)))
          graph)
  | VDepFunGraph graph =>
      VDepFunGraph
        (map
          (fun xy => (subst_value theta (fst xy), subst_value theta (snd xy)))
          graph)
  end.

Fixpoint subst_record (theta : subst) (r : record) : record :=
  match r with
  | RecIO x y => RecIO (subst_value theta x) (subst_value theta y)
  | RecCtx C s => RecCtx C (subst_record theta s)
  | RecComp a b => RecComp (subst_record theta a) (subst_record theta b)
  | RecIter n s => RecIter n (subst_record theta s)
  | RecRed rs => RecRed (map (subst_record theta) rs)
  | RecInt rs => RecInt (map (subst_record theta) rs)
  end.

Definition bsub (theta : subst) : Prop :=
  forall s, exists inv, forall v, inv (theta s v) = v.

Record compatible_equiv (tau : ty) (R : relation_on_records) : Prop := {
  comp_equiv : equiv_props R;
  comp_pseudo : forall r s, pseudo r s -> R r s;
  comp_congruence : record_congruence R;
  comp_subst_stable :
    forall theta r s,
      bsub theta ->
      R r s ->
      R (subst_record theta r) (subst_record theta s)
}.

Definition min_equiv (tau : ty) : relation_on_records :=
  fun r s => forall R, compatible_equiv tau R -> R r s.

Lemma min_equiv_compatible :
  forall tau, compatible_equiv tau (min_equiv tau).
Proof.
  intros tau.
  refine {|
    comp_equiv := _;
    comp_pseudo := _;
    comp_congruence := _;
    comp_subst_stable := _
  |}.
  - refine {|
      equiv_refl := _;
      equiv_sym := _;
      equiv_trans := _
    |}.
    + intros r R HR.
      exact (equiv_refl R (comp_equiv tau R HR) r).
    + intros r s H R HR.
      exact (equiv_sym R (comp_equiv tau R HR) r s (H R HR)).
    + intros r s t Hrs Hst R HR.
      exact
        (equiv_trans R (comp_equiv tau R HR)
          r s t (Hrs R HR) (Hst R HR)).
  - intros r s Hp R HR.
    exact (comp_pseudo tau R HR r s Hp).
  - repeat split.
    + intros C r s H R HR.
      destruct (comp_congruence tau R HR) as [HC _].
      exact (HC C r s (H R HR)).
    + intros r r' s s' Hr Hs R HR.
      destruct (comp_congruence tau R HR) as [_ [HC _]].
      exact (HC r r' s s' (Hr R HR) (Hs R HR)).
    + intros n r s H R HR.
      destruct (comp_congruence tau R HR) as [_ [_ [HI _]]].
      exact (HI n r s (H R HR)).
    + intros rs ss H R HR.
      destruct (comp_congruence tau R HR) as [_ [_ [_ [HRd _]]]].
      apply HRd.
      induction H as [|x y xs ys Hxy Hrest IHrel].
      * constructor.
      * constructor; [exact (Hxy R HR) | exact IHrel].
    + intros rs ss H R HR.
      destruct (comp_congruence tau R HR) as [_ [_ [_ [_ HIn]]]].
      apply HIn.
      induction H as [|x y xs ys Hxy Hrest IHrel].
      * constructor.
      * constructor; [exact (Hxy R HR) | exact IHrel].
  - intros theta r s Hb H R HR.
    exact (comp_subst_stable tau R HR theta r s Hb (H R HR)).
Qed.

Inductive graph_record : ty -> value -> value -> value -> Prop :=
| GraphArr :
    forall sigma tau graph x y,
      In (x, y) graph ->
      val_ok sigma x ->
      val_ok tau y ->
      graph_record (Arr sigma tau) (VFunGraph graph) x y
| GraphPi :
    forall sigma branches graph x y branch,
      In (x, y) graph ->
      In branch branches ->
      val_ok sigma x ->
      val_ok branch y ->
      graph_record (Pi sigma branches) (VDepFunGraph graph) x y.

Lemma graph_record_io_ok :
  forall tau f x y,
    graph_record tau f x y ->
    io_record_ok tau x y.
Proof.
  intros tau f x y H.
  inversion H; subst; simpl.
  - split; assumption.
  - split; [assumption |].
    exists branch. split; assumption.
Qed.

Lemma graph_record_rec_ok :
  forall tau f x y,
    graph_record tau f x y ->
    rec_ok tau (RecIO x y).
Proof.
  intros tau f x y H.
  apply RecOKIO.
  exact (graph_record_io_ok tau f x y H).
Qed.

Record legal_interpretation : Type := {
  lif_ty : ty;
  lif_fun : value;
  lif_protocol : protocol lif_ty;
  lif_fun_ty : fun_ty lif_ty;
  lif_ty_ok : ty_ok lif_ty;
  lif_fun_value : val_ok lif_ty lif_fun;
  lif_behavior_recorded :
    forall x y,
      graph_record lif_ty lif_fun x y ->
      raw_obs lif_ty lif_protocol (RecIO x y);
  lif_equiv_compatible :
    compatible_equiv lif_ty (proto_equiv lif_ty lif_protocol);
  lif_ctx_complete :
    forall C,
      ctx_ok lif_ty (shape_of lif_ty) C ->
      allowed_ctx lif_ty lif_protocol C;
  lif_comp_complete :
    forall r s,
      rec_ok lif_ty r ->
      rec_ok lif_ty s ->
      allowed_comp lif_ty lif_protocol r s;
  lif_iter_complete :
    forall n r,
      rec_ok lif_ty r ->
      allowed_iter lif_ty lif_protocol n r;
  lif_red_complete :
    forall rs,
      Forall (rec_ok lif_ty) rs ->
      allowed_red lif_ty lif_protocol rs;
  lif_int_complete :
    forall rs,
      Forall (rec_ok lif_ty) rs ->
      allowed_int lif_ty lif_protocol rs;
  lif_subst_closure :
    forall theta r,
      bsub theta ->
      obs_closure lif_protocol r ->
      obs_closure lif_protocol (subst_record theta r)
}.

Inductive judg : Type :=
| JRec : record -> judg.

Inductive syn_rule {tau : ty} (P : protocol tau) : list judg -> judg -> Prop :=
| SynEq :
    forall r s,
      proto_equiv tau P r s ->
      syn_rule P [JRec r] (JRec s)
| SynCtx :
    forall C r,
      allowed_ctx tau P C ->
      syn_rule P [JRec r] (JRec (RecCtx C r))
| SynComp :
    forall r s,
      allowed_comp tau P r s ->
      syn_rule P [JRec r; JRec s] (JRec (RecComp r s))
| SynIter :
    forall n r,
      allowed_iter tau P n r ->
      syn_rule P [JRec r] (JRec (RecIter n r))
| SynRed :
    forall rs,
      allowed_red tau P rs ->
      syn_rule P (map JRec rs) (JRec (RecRed rs))
| SynInt :
    forall rs,
      allowed_int tau P rs ->
      syn_rule P (map JRec rs) (JRec (RecInt rs)).

Definition deriv {tau : ty} (P : protocol tau) (j : judg) : Prop :=
  match j with
  | JRec r => obs_closure P r
  end.

Theorem syn_closure_exact :
  forall tau (P : protocol tau) r,
    deriv P (JRec r) <-> obs_closure P r.
Proof.
  intros tau P r.
  split; intro H; exact H.
Qed.

Theorem syntactic_soundness :
  forall tau (P : protocol tau) r,
    deriv P (JRec r) ->
    obs_closure P r.
Proof.
  intros tau P r H.
  exact (proj1 (syn_closure_exact tau P r) H).
Qed.

Definition judg_equiv {tau : ty} (P : protocol tau) (j k : judg) : Prop :=
  match j, k with
  | JRec r, JRec s => proto_equiv tau P r s
  end.

Theorem adequacy_relation_exact :
  forall tau (P : protocol tau) r s,
    proto_equiv tau P r s <-> judg_equiv P (JRec r) (JRec s).
Proof.
  intros; split; intro H; exact H.
Qed.

Record seed (tau : ty) (f : value) (A : record -> Prop) : Prop := {
  seed_graph :
    forall x y, graph_record tau f x y -> A (RecIO x y);
  seed_records :
    forall r, A r -> rec_ok tau r
}.

Definition free_raw_obs {tau : ty} (A : record -> Prop) : record -> Prop := A.

Definition free_protocol
    (tau : ty)
    (A : record -> Prop)
    (HA : forall r, A r -> rec_ok tau r)
    (HC : forall C, ctx_ok tau (shape_of tau) C -> A (RecCtx C (RecIO (VAtom (TermSort 0) 0) (VAtom (TermSort 0) 0))) -> ctx_ok tau (shape_of tau) C)
    : protocol tau.
Proof.
  refine {|
    raw_obs := A;
    proto_equiv := min_equiv tau;
    allowed_ctx := fun C => ctx_ok tau (shape_of tau) C;
    allowed_comp := fun r s => rec_ok tau r /\ rec_ok tau s;
    allowed_iter := fun _ r => rec_ok tau r;
    allowed_red := fun rs => Forall (rec_ok tau) rs;
    allowed_int := fun rs => Forall (rec_ok tau) rs
  |}.
  - exact HA.
  - exact (comp_equiv tau (min_equiv tau) (min_equiv_compatible tau)).
  - intros C HCtx.
    exact HCtx.
  - intros r s H.
    exact H.
  - intros n r H.
    exact H.
  - intros rs H.
    exact H.
  - intros rs H.
    exact H.
Defined.

Lemma free_protocol_equiv_compatible :
  forall tau A HA HC,
    compatible_equiv tau
      (proto_equiv tau (free_protocol tau A HA HC)).
Proof.
  intros.
  exact (min_equiv_compatible tau).
Qed.

Theorem free_legality_core :
  forall tau f A HA HC,
    ty_ok tau ->
    fun_ty tau ->
    val_ok tau f ->
    seed tau f A ->
    (forall theta r,
        bsub theta ->
        obs_closure (free_protocol tau A HA HC) r ->
        obs_closure (free_protocol tau A HA HC) (subst_record theta r)) ->
    legal_interpretation.
Proof.
  intros tau f A HA HC Hty Hfun Hval Hseed Hsubst.
  refine {|
    lif_ty := tau;
    lif_fun := f;
    lif_protocol := free_protocol tau A HA HC;
    lif_fun_ty := Hfun;
    lif_ty_ok := Hty;
    lif_fun_value := Hval;
    lif_equiv_compatible := free_protocol_equiv_compatible tau A HA HC;
    lif_ctx_complete := fun C H => H;
    lif_comp_complete := fun r s Hr Hs => conj Hr Hs;
    lif_iter_complete := fun n r Hr => Hr;
    lif_red_complete := fun rs Hrs => Hrs;
    lif_int_complete := fun rs Hrs => Hrs;
    lif_subst_closure := Hsubst
  |}.
  intros x y Hg.
  exact (seed_graph tau f A Hseed x y Hg).
Defined.

Definition relation_refines (R E : relation_on_records) : Prop :=
  forall r s, R r s -> E r s.

Theorem min_equiv_least :
  forall tau E,
    compatible_equiv tau E ->
    relation_refines (min_equiv tau) E.
Proof.
  intros tau E HE r s H.
  exact (H E HE).
Qed.

Fixpoint free_initiality_map
    (L : legal_interpretation)
    (A : record -> Prop)
    (HA : forall r, A r -> rec_ok (lif_ty L) r)
    (HC : forall C,
      ctx_ok (lif_ty L) (shape_of (lif_ty L)) C ->
      A (RecCtx C (RecIO (VAtom (TermSort 0) 0) (VAtom (TermSort 0) 0))) ->
      ctx_ok (lif_ty L) (shape_of (lif_ty L)) C)
    (Hraw : forall r, A r -> raw_obs (lif_ty L) (lif_protocol L) r)
    (r : record)
    (H : obs_closure (free_protocol (lif_ty L) A HA HC) r)
    {struct H}
    : obs_closure (lif_protocol L) r :=
  match H in obs_closure _ r0 return obs_closure (lif_protocol L) r0 with
  | ObsRaw _ r0 HrawA =>
      ObsRaw (lif_protocol L) r0 (Hraw r0 HrawA)
  | ObsEquiv _ r0 s Hr Hrse =>
      ObsEquiv (lif_protocol L) r0 s
        (free_initiality_map L A HA HC Hraw r0 Hr)
        (min_equiv_least (lif_ty L)
          (proto_equiv (lif_ty L) (lif_protocol L))
          (lif_equiv_compatible L) r0 s Hrse)
  | ObsCtx _ C r0 HCfree Hr =>
      ObsCtx (lif_protocol L) C r0
        (lif_ctx_complete L C HCfree)
        (free_initiality_map L A HA HC Hraw r0 Hr)
  | ObsComp _ r0 s Hcomp Hr Hs =>
      match Hcomp with
      | conj HrOk HsOk =>
          ObsComp (lif_protocol L) r0 s
            (lif_comp_complete L r0 s HrOk HsOk)
            (free_initiality_map L A HA HC Hraw r0 Hr)
            (free_initiality_map L A HA HC Hraw s Hs)
      end
  | ObsIter _ n r0 Hiter Hr =>
      ObsIter (lif_protocol L) n r0
        (lif_iter_complete L n r0 Hiter)
        (free_initiality_map L A HA HC Hraw r0 Hr)
  | ObsRed _ rs Hred Hrs =>
      ObsRed (lif_protocol L) rs
        (lif_red_complete L rs Hred)
        (free_initiality_list_map L A HA HC Hraw rs Hrs)
  | ObsInt _ rs Hint Hrs =>
      ObsInt (lif_protocol L) rs
        (lif_int_complete L rs Hint)
        (free_initiality_list_map L A HA HC Hraw rs Hrs)
  end
with free_initiality_list_map
    (L : legal_interpretation)
    (A : record -> Prop)
    (HA : forall r, A r -> rec_ok (lif_ty L) r)
    (HC : forall C,
      ctx_ok (lif_ty L) (shape_of (lif_ty L)) C ->
      A (RecCtx C (RecIO (VAtom (TermSort 0) 0) (VAtom (TermSort 0) 0))) ->
      ctx_ok (lif_ty L) (shape_of (lif_ty L)) C)
    (Hraw : forall r, A r -> raw_obs (lif_ty L) (lif_protocol L) r)
    (rs : list record)
    (H : obs_closure_list (free_protocol (lif_ty L) A HA HC) rs)
    {struct H}
    : obs_closure_list (lif_protocol L) rs :=
  match H in obs_closure_list _ rs0 return obs_closure_list (lif_protocol L) rs0 with
  | ObsListNil _ =>
      ObsListNil (lif_protocol L)
  | ObsListCons _ r rs Hr Hrs =>
      ObsListCons (lif_protocol L) r rs
        (free_initiality_map L A HA HC Hraw r Hr)
        (free_initiality_list_map L A HA HC Hraw rs Hrs)
  end.

Theorem free_initiality :
  forall (L : legal_interpretation) A HA HC,
    (forall r, A r -> raw_obs (lif_ty L) (lif_protocol L) r) ->
    forall r,
      obs_closure (free_protocol (lif_ty L) A HA HC) r ->
      obs_closure (lif_protocol L) r.
Proof.
  intros L A HA HC Hraw r H.
  exact (free_initiality_map L A HA HC Hraw r H).
Qed.

Definition core_of (L : legal_interpretation) : ty * value :=
  (lif_ty L, lif_fun L).

Definition t_function_core (tau : ty) (f : value) : Prop :=
  ty_ok tau /\ fun_ty tau /\ val_ok tau f.

Theorem legal_core_exact :
  forall L, t_function_core (lif_ty L) (lif_fun L).
Proof.
  intro L.
  split; [exact (lif_ty_ok L) | split; [exact (lif_fun_ty L) | exact (lif_fun_value L)]].
Qed.

Theorem free_core_section :
  forall tau f A HA HC Hty Hfun Hval Hseed Hsubst,
    core_of
      (free_legality_core tau f A HA HC Hty Hfun Hval Hseed Hsubst)
    = (tau, f).
Proof.
  reflexivity.
Qed.

Record quotient_projection (tau : ty) (E : relation_on_records) : Prop := {
  quotient_refines_min :
    relation_refines (min_equiv tau) E;
  quotient_hits_representatives :
    forall r, E r r -> exists s, E r s
}.

Theorem free_quotient_projection :
  forall tau E,
    compatible_equiv tau E ->
    quotient_projection tau E.
Proof.
  intros tau E HE.
  refine {| quotient_refines_min := min_equiv_least tau E HE |}.
  intros r Hr.
  exists r.
  exact Hr.
Qed.

Record decoder : Type := {
  dec_core : nat -> option (ty * value * (record -> Prop) * relation_on_records);
  prf_zfc : nat -> nat -> Prop
}.

Definition lif_core (tau : ty) (f : value) (A : record -> Prop)
    (E : relation_on_records) : Prop :=
  ty_ok tau /\
  fun_ty tau /\
  val_ok tau f /\
  (forall r, A r -> rec_ok tau r) /\
  compatible_equiv tau E.

Definition cert (D : decoder) (e p : nat) : Prop :=
  exists tau f A E,
    dec_core D e = Some (tau, f, A, E) /\
    prf_zfc D p e /\
    lif_core tau f A E.

Definition elif (D : decoder) (e : nat) : Prop :=
  exists p, cert D e p.

Inductive enum_result (D : decoder) : nat -> judg -> Prop :=
| EnumSound :
    forall e p tau f A E r,
      dec_core D e = Some (tau, f, A, E) ->
      cert D e p ->
      A r ->
      enum_result D e (JRec r).

Theorem enum_sound :
  forall D e j,
    enum_result D e j ->
    exists tau f A E,
      dec_core D e = Some (tau, f, A, E) /\
      lif_core tau f A E.
Proof.
  intros D e j H.
  destruct H as [e p tau0 f0 A0 E0 r Hdec Hcert Hr].
  destruct Hcert as [tau' [f' [A' [E' [Hdec' [_ Hcore]]]]]].
  exists tau', f', A', E'.
  split; assumption.
Qed.

Record FIS_system : Type := {
  fis_ty : ty -> Prop;
  fis_rec : ty -> record -> Prop;
  fis_protocol : forall tau, protocol tau -> Prop;
  fis_syn : forall tau, protocol tau -> judg -> Prop;
  fis_obs : forall tau, protocol tau -> record -> Prop;
  fis_syn_exact :
    forall tau P r,
      fis_protocol tau P ->
      (fis_syn tau P (JRec r) <-> fis_obs tau P r);
  fis_sound :
    forall tau P r,
      fis_protocol tau P ->
      fis_syn tau P (JRec r) ->
      fis_obs tau P r;
  fis_free_core :
    forall tau f A HA HC,
      ty_ok tau ->
      fun_ty tau ->
      val_ok tau f ->
      seed tau f A ->
      (forall theta r,
          bsub theta ->
          obs_closure (free_protocol tau A HA HC) r ->
          obs_closure (free_protocol tau A HA HC) (subst_record theta r)) ->
      legal_interpretation;
  fis_enum_sound :
    forall D e j,
      enum_result D e j ->
      exists tau f A E,
        dec_core D e = Some (tau, f, A, E) /\ lif_core tau f A E
}.

Definition FIS_sharp : FIS_system := {|
  fis_ty := ty_ok;
  fis_rec := rec_ok;
  fis_protocol := fun tau P => forall r, raw_obs tau P r -> rec_ok tau r;
  fis_syn := fun tau P j => deriv P j;
  fis_obs := fun tau P r => obs_closure P r;
  fis_syn_exact := fun tau P r _ => syn_closure_exact tau P r;
  fis_sound := fun tau P r _ H => syntactic_soundness tau P r H;
  fis_free_core := free_legality_core;
  fis_enum_sound := enum_sound
|}.

End FunctionInducedSyntax1112.
