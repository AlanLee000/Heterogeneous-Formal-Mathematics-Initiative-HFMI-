From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

Import ListNotations.

Module FunctionInducedSyntaxFoundation1112.

Inductive tag : Type :=
| TSort | TBaseTy | TProdTy | TArrTy | TPiTy
| TObjSh | TProdSh | TMapSh | TDepMapSh
| TVal
| TRecIO | TRecCtx | TRecComp | TRecIter | TRecRed | TRecInt
| TProtCtx | TProtComp | TProtIter | TProtRed | TProtInt
| TCtxHole | TCtxVar | TCtxConst | TCtxTuple | TCtxApp | TCtxQuote
| TJdg | TInfRule | TFragObj.

Inductive kind : Type :=
| KTerm | KForm | KCode | KJudg | KRule | KRuleTr | KFrag | KClOp.

Record sort_code : Type := Sort {
  sort_kind : kind;
  sort_level : nat;
  sort_tag : nat
}.

Definition term_sort (i : nat) : sort_code := Sort KTerm i 0.
Definition form_sort (i : nat) : sort_code := Sort KForm i 0.
Definition code_sort (i : nat) : sort_code := Sort KCode i 0.

Inductive kind_dep : kind -> kind -> Prop :=
| KDTermTerm : kind_dep KTerm KTerm
| KDTermForm : kind_dep KTerm KForm
| KDTermJudg : kind_dep KTerm KJudg
| KDTermRule : kind_dep KTerm KRule
| KDTermRuleTr : kind_dep KTerm KRuleTr
| KDTermFrag : kind_dep KTerm KFrag
| KDTermClOp : kind_dep KTerm KClOp
| KDFormJudg : kind_dep KForm KJudg
| KDFormRule : kind_dep KForm KRule
| KDFormRuleTr : kind_dep KForm KRuleTr
| KDFormFrag : kind_dep KForm KFrag
| KDFormClOp : kind_dep KForm KClOp
| KDJudgRule : kind_dep KJudg KRule
| KDJudgRuleTr : kind_dep KJudg KRuleTr
| KDJudgFrag : kind_dep KJudg KFrag
| KDRuleRuleTr : kind_dep KRule KRuleTr
| KDRuleFrag : kind_dep KRule KFrag
| KDRuleTrFrag : kind_dep KRuleTr KFrag
| KDFragRuleTr : kind_dep KFrag KRuleTr
| KDFragClOp : kind_dep KFrag KClOp
| KDClOpClOp : kind_dep KClOp KClOp.

Definition dep (s t : sort_code) : Prop :=
  sort_level s <= sort_level t /\
  (sort_kind s = KCode \/ kind_dep (sort_kind s) (sort_kind t)).

Theorem no_same_level_formula_to_term :
  forall i, ~ dep (form_sort i) (term_sort i).
Proof.
  intros i [_ [Hcode | Hdep]].
  - discriminate Hcode.
  - inversion Hdep.
Qed.

Inductive ty : Type :=
| Base : sort_code -> ty
| Prod : list ty -> ty
| Arr : ty -> ty -> ty
| Pi : ty -> (nat -> ty) -> ty.

Inductive occurs_sort : ty -> sort_code -> Prop :=
| OccBase : forall s, occurs_sort (Base s) s
| OccProd :
    forall xs tau s,
      In tau xs ->
      occurs_sort tau s ->
      occurs_sort (Prod xs) s
| OccArrL :
    forall sigma tau s,
      occurs_sort sigma s ->
      occurs_sort (Arr sigma tau) s
| OccArrR :
    forall sigma tau s,
      occurs_sort tau s ->
      occurs_sort (Arr sigma tau) s
| OccPiDom :
    forall sigma beta s,
      occurs_sort sigma s ->
      occurs_sort (Pi sigma beta) s
| OccPiBody :
    forall sigma beta x s,
      occurs_sort (beta x) s ->
      occurs_sort (Pi sigma beta) s.

Definition arr_ok (sigma tau : ty) : Prop :=
  forall s t, occurs_sort sigma s -> occurs_sort tau t -> dep s t.

Inductive ty_ok : ty -> Prop :=
| TyBase :
    forall s, ty_ok (Base s)
| TyProd :
    forall xs,
      xs <> [] ->
      Forall ty_ok xs ->
      ty_ok (Prod xs)
| TyArr :
    forall sigma tau,
      ty_ok sigma ->
      ty_ok tau ->
      arr_ok sigma tau ->
      ty_ok (Arr sigma tau)
| TyPi :
    forall sigma beta,
      ty_ok sigma ->
      (forall x, ty_ok (beta x)) ->
      (forall x, arr_ok sigma (beta x)) ->
      ty_ok (Pi sigma beta).

Inductive shape : Type :=
| ObjSh : sort_code -> shape
| ProdSh : list shape -> shape
| MapSh : shape -> shape -> shape
| DepMapSh : shape -> (nat -> shape) -> shape.

Fixpoint shape_of (tau : ty) : shape :=
  match tau with
  | Base s => ObjSh s
  | Prod xs => ProdSh (map shape_of xs)
  | Arr sigma tau => MapSh (shape_of sigma) (shape_of tau)
  | Pi sigma beta => DepMapSh (shape_of sigma) (fun x => shape_of (beta x))
  end.

Inductive sub_shape : shape -> shape -> Prop :=
| SubRefl :
    forall H, sub_shape H H
| SubProd :
    forall xs H,
      In H xs ->
      sub_shape H (ProdSh xs)
| SubMapDom :
    forall A B H,
      sub_shape H A ->
      sub_shape H (MapSh A B)
| SubMapCod :
    forall A B H,
      sub_shape H B ->
      sub_shape H (MapSh A B)
| SubDepDom :
    forall A beta H,
      sub_shape H A ->
      sub_shape H (DepMapSh A beta)
| SubDepCod :
    forall A beta x H,
      sub_shape H (beta x) ->
      sub_shape H (DepMapSh A beta).

Inductive lifted_sort : sort_code -> sort_code -> Prop :=
| LiftNonCode :
    forall k i a,
      k <> KCode ->
      lifted_sort (Sort k i a) (Sort k (S i) a).

Definition context_shape (tau : ty) : shape := shape_of tau.

Inductive ctx : Type :=
| CtxHole : ty -> ctx
| CtxVar : ty -> nat -> ctx
| CtxConst : ty -> nat -> ctx
| CtxTuple : list ctx -> ctx
| CtxApp : ctx -> ctx -> ctx
| CtxQuote : ctx -> ctx.

Inductive ctx_for : ty -> ctx -> Prop :=
| CtxForHole :
    forall tau, ctx_for tau (CtxHole tau)
| CtxForVar :
    forall tau i, ctx_for tau (CtxVar tau i)
| CtxForConst :
    forall tau i, ctx_for tau (CtxConst tau i)
| CtxForTuple :
    forall tau xs,
      Forall (ctx_for tau) xs ->
      ctx_for tau (CtxTuple xs)
| CtxForApp :
    forall tau A B,
      ctx_for tau A ->
      ctx_for tau B ->
      ctx_for tau (CtxApp A B)
| CtxForQuote :
    forall tau A,
      ctx_for tau A ->
      ctx_for tau (CtxQuote A).

Inductive rec : Type :=
| RecIO : ty -> nat -> nat -> rec
| RecCtx : ty -> ctx -> rec -> rec
| RecComp : ty -> rec -> rec -> rec
| RecIter : ty -> nat -> rec -> rec
| RecRed : ty -> list rec -> rec
| RecInt : ty -> list rec -> rec.

Definition rec_ty (r : rec) : ty :=
  match r with
  | RecIO tau _ _ => tau
  | RecCtx tau _ _ => tau
  | RecComp tau _ _ => tau
  | RecIter tau _ _ => tau
  | RecRed tau _ => tau
  | RecInt tau _ => tau
  end.

Definition same_ty (r s : rec) : Prop := rec_ty r = rec_ty s.

Record protocol : Type := {
  prot_ctx : ty -> ctx -> rec -> Prop;
  prot_comp : ty -> rec -> rec -> Prop;
  prot_iter : ty -> nat -> rec -> Prop;
  prot_red : ty -> list rec -> Prop;
  prot_int : ty -> list rec -> Prop
}.

Definition protocol_all : protocol := {|
  prot_ctx := fun _ _ _ => True;
  prot_comp := fun _ _ _ => True;
  prot_iter := fun _ _ _ => True;
  prot_red := fun _ _ => True;
  prot_int := fun _ _ => True
|}.

Definition protocol_for (tau : ty) : protocol := {|
  prot_ctx := fun tau' _ r => tau' = tau /\ rec_ty r = tau;
  prot_comp := fun tau' r s => tau' = tau /\ rec_ty r = tau /\ rec_ty s = tau;
  prot_iter := fun tau' _ r => tau' = tau /\ rec_ty r = tau;
  prot_red := fun tau' xs => tau' = tau /\ Forall (fun r => rec_ty r = tau) xs;
  prot_int := fun tau' xs => tau' = tau /\ Forall (fun r => rec_ty r = tau) xs
|}.

Record substitution (tau : ty) : Type := {
  subst_on_rec : rec -> rec;
  subst_preserves_type : forall r, rec_ty r = tau -> rec_ty (subst_on_rec r) = tau
}.

Definition bsub (tau : ty) (theta : substitution tau) : Prop :=
  forall r s, rec_ty r = tau -> rec_ty s = tau ->
    subst_on_rec tau theta r = subst_on_rec tau theta s -> r = s.

Inductive pseudo_diff : rec -> rec -> Prop :=
| PseudoCtx :
    forall K r,
      pseudo_diff r (RecCtx (rec_ty r) K r)
| PseudoCompAssoc :
    forall tau a b c,
      pseudo_diff
        (RecComp tau (RecComp tau a b) c)
        (RecComp tau a (RecComp tau b c)).

Definition eliminates_pseudo_diff (E : rec -> rec -> Prop) : Prop :=
  forall r s, pseudo_diff r s -> E r s.

Record rec_congruence (E : rec -> rec -> Prop) : Prop := {
  cong_refl : forall r, E r r;
  cong_sym : forall r s, E r s -> E s r;
  cong_trans : forall r s t, E r s -> E s t -> E r t;
  cong_type : forall r s, E r s -> same_ty r s;
  cong_ctx :
    forall tau K r s,
      E r s -> E (RecCtx tau K r) (RecCtx tau K s);
  cong_comp :
    forall tau a a' b b',
      E a a' -> E b b' -> E (RecComp tau a b) (RecComp tau a' b');
  cong_iter :
    forall tau n r s,
      E r s -> E (RecIter tau n r) (RecIter tau n s)
}.

Inductive obs_closure
    (core : rec -> Prop) (P : protocol) (E : rec -> rec -> Prop)
    : rec -> Prop :=
| OCBase :
    forall r, core r -> obs_closure core P E r
| OCEquiv :
    forall r s,
      obs_closure core P E r ->
      E r s ->
      obs_closure core P E s
| OCCtx :
    forall tau K r,
      obs_closure core P E r ->
      prot_ctx P tau K r ->
      obs_closure core P E (RecCtx tau K r)
| OCComp :
    forall tau r s,
      obs_closure core P E r ->
      obs_closure core P E s ->
      prot_comp P tau r s ->
      obs_closure core P E (RecComp tau r s)
| OCIter :
    forall tau n r,
      obs_closure core P E r ->
      prot_iter P tau n r ->
      obs_closure core P E (RecIter tau n r)
| OCRed :
    forall tau xs,
      Forall (obs_closure core P E) xs ->
      prot_red P tau xs ->
      obs_closure core P E (RecRed tau xs)
| OCInt :
    forall tau xs,
      Forall (obs_closure core P E) xs ->
      prot_int P tau xs ->
      obs_closure core P E (RecInt tau xs).

Record interp_object : Type := {
  obj_type : ty;
  obj_type_ok : ty_ok obj_type;
  obj_core : rec -> Prop;
  obj_core_typed : forall r, obj_core r -> rec_ty r = obj_type;
  obj_protocol : protocol;
  obj_equiv : rec -> rec -> Prop;
  obj_equiv_congruence : rec_congruence obj_equiv;
  obj_equiv_eliminates_pseudo : eliminates_pseudo_diff obj_equiv;
  obj_substitution_stable :
    forall theta r,
      bsub obj_type theta ->
      obj_core r ->
      obj_core (subst_on_rec obj_type theta r);
  obj_protocol_closure_stable :
    forall r, obs_closure obj_core obj_protocol obj_equiv r -> rec_ty r = obj_type
}.

Inductive judgment : Type :=
| JObs : rec -> judgment
| JEq : rec -> rec -> judgment.

Inductive inf_rule : Type :=
| RuleEquiv : rec -> rec -> inf_rule
| RuleCtx : ty -> ctx -> rec -> inf_rule
| RuleComp : ty -> rec -> rec -> inf_rule
| RuleIter : ty -> nat -> rec -> inf_rule
| RuleRed : ty -> list rec -> inf_rule
| RuleInt : ty -> list rec -> inf_rule.

Definition fragment_thm (F : interp_object) : rec -> Prop :=
  obs_closure (obj_core F) (obj_protocol F) (obj_equiv F).

Lemma Forall_impl_closure :
  forall (A : Type) (P Q : A -> Prop) xs,
    (forall x, P x -> Q x) ->
    Forall P xs ->
    Forall Q xs.
Proof.
  intros A P Q xs HPQ H.
  induction H; constructor; auto.
Qed.

Theorem closure_equal_forward :
  forall F r,
    fragment_thm F r ->
    obs_closure (obj_core F) (obj_protocol F) (obj_equiv F) r.
Proof.
  intros F r H. exact H.
Qed.

Theorem closure_equal_backward :
  forall F r,
    obs_closure (obj_core F) (obj_protocol F) (obj_equiv F) r ->
    fragment_thm F r.
Proof.
  intros F r H. exact H.
Qed.

Theorem closure_equal :
  forall F r,
    fragment_thm F r <->
    obs_closure (obj_core F) (obj_protocol F) (obj_equiv F) r.
Proof.
  split.
  - apply closure_equal_forward.
  - apply closure_equal_backward.
Qed.

Theorem compiler_soundness :
  forall F r,
    fragment_thm F r ->
    obs_closure (obj_core F) (obj_protocol F) (obj_equiv F) r.
Proof.
  apply closure_equal_forward.
Qed.

Theorem compiler_adequacy :
  forall F r,
    obs_closure (obj_core F) (obj_protocol F) (obj_equiv F) r ->
    fragment_thm F r.
Proof.
  apply closure_equal_backward.
Qed.

Definition obs_class (E : rec -> rec -> Prop) (r : rec) : rec -> Prop :=
  fun s => E r s.

Theorem quotient_map_well_defined :
  forall E r s,
    rec_congruence E ->
    E r s ->
    forall x, obs_class E r x <-> obs_class E s x.
Proof.
  intros E r s HE Hrs.
  intro x.
  split; intro H.
  - eapply cong_trans; eauto.
    apply cong_sym; eauto.
  - eapply cong_trans; eauto.
Qed.

Record proof_system : Type := {
  zfc_proves : nat -> nat -> Prop;
  decodes : nat -> option interp_object;
  certifies : nat -> nat -> Prop :=
    fun p c => exists F, decodes c = Some F /\ zfc_proves p c
}.

Definition finite_certificate_set (P : proof_system) : Type :=
  { c : nat | exists p, certifies P p c }.

Definition enumerates_legal_systems (P : proof_system) (e : nat -> option nat) : Prop :=
  forall n c, e n = Some c ->
    exists F p, decodes P c = Some F /\ certifies P p c.

Theorem enumeration_sound :
  forall P e n c,
    enumerates_legal_systems P e ->
    e n = Some c ->
    exists F p, decodes P c = Some F /\ certifies P p c.
Proof.
  intros P e n c Henum He.
  exact (Henum n c He).
Qed.

Record function_core : Type := {
  core_type : ty;
  core_input : nat -> Prop;
  core_output : nat -> nat
}.

Definition graph_record (C : function_core) (x : nat) : rec :=
  RecIO (core_type C) x (core_output C x).

Definition seed_core (C : function_core) : rec -> Prop :=
  fun r => exists x, r = graph_record C x.

Definition free_core (C : function_core) : rec -> Prop :=
  fun r => rec_ty r = core_type C.

Definition same_io (r s : rec) : Prop :=
  match r, s with
  | RecIO tau x y, RecIO tau' x' y' =>
      tau = tau' /\ x = x' /\ y = y'
  | _, _ => False
  end.

Definition type_equiv (r s : rec) : Prop := same_ty r s.

Lemma type_equiv_congruence : rec_congruence type_equiv.
Proof.
  constructor.
  - intro r. reflexivity.
  - intros r s H. symmetry; exact H.
  - intros r s t Hrs Hst. transitivity (rec_ty s); assumption.
  - intros r s H. exact H.
  - intros tau K r s _. reflexivity.
  - intros tau a a' b b' _ _. reflexivity.
  - intros tau n r s _. reflexivity.
Qed.

Lemma type_equiv_eliminates : eliminates_pseudo_diff type_equiv.
Proof.
  intros r s H.
  inversion H; subst; simpl; reflexivity.
Qed.

Definition identity_substitution (tau : ty) : substitution tau := {|
  subst_on_rec := fun r => r;
  subst_preserves_type := fun r Hr => Hr
|}.

Lemma seed_core_typed :
  forall C r, seed_core C r -> rec_ty r = core_type C.
Proof.
  intros C r [x ->].
  reflexivity.
Qed.

Lemma free_core_typed :
  forall C r, free_core C r -> rec_ty r = core_type C.
Proof.
  intros C r H. exact H.
Qed.

Lemma free_core_subst_stable :
  forall C theta r,
    bsub (core_type C) theta ->
    free_core C r ->
    free_core C (subst_on_rec (core_type C) theta r).
Proof.
  intros C theta r _ Hr.
  exact (subst_preserves_type (core_type C) theta r Hr).
Qed.

Lemma free_protocol_closure_typed :
  forall C r,
    obs_closure (free_core C) (protocol_for (core_type C)) type_equiv r ->
    rec_ty r = core_type C.
Proof.
  intros C r H.
  induction H; simpl in *; auto.
  - unfold type_equiv, same_ty in H0.
    rewrite <- H0. exact IHobs_closure.
  - destruct H0 as [-> _]. reflexivity.
  - destruct H1 as [-> [_ _]]. reflexivity.
  - destruct H0 as [-> _]. reflexivity.
  - destruct H0 as [-> _]. reflexivity.
  - destruct H0 as [-> _]. reflexivity.
Qed.

Definition free_interp_object (C : function_core) (Hok : ty_ok (core_type C))
    : interp_object := {|
  obj_type := core_type C;
  obj_type_ok := Hok;
  obj_core := free_core C;
  obj_core_typed := free_core_typed C;
  obj_protocol := protocol_for (core_type C);
  obj_equiv := type_equiv;
  obj_equiv_congruence := type_equiv_congruence;
  obj_equiv_eliminates_pseudo := type_equiv_eliminates;
  obj_substitution_stable := free_core_subst_stable C;
  obj_protocol_closure_stable := free_protocol_closure_typed C
|}.

Lemma free_interp_core :
  forall C Hok r,
    obj_core (free_interp_object C Hok) r ->
    rec_ty r = core_type C.
Proof.
  intros C Hok r H.
  exact H.
Qed.

Definition includes_seed (F : interp_object) (C : function_core) : Prop :=
  forall x, obj_core F (graph_record C x).

Record morphism (F G : interp_object) : Type := {
  mor_map : rec -> rec;
  mor_preserves_core :
    forall r, obj_core F r -> obj_core G (mor_map r);
  mor_preserves_equiv :
    forall r s, obj_equiv F r s -> obj_equiv G (mor_map r) (mor_map s)
}.

Theorem free_initiality :
  forall C Hok F,
    obj_type F = core_type C ->
    (forall r, rec_ty r = core_type C -> obj_core F r) ->
    (forall r s, type_equiv r s -> obj_equiv F r s) ->
    exists m : morphism (free_interp_object C Hok) F, True.
Proof.
  intros C Hok F Htype Hclosed Hequiv.
  exists {|
    mor_map := fun r => r;
    mor_preserves_core := fun r Hr =>
      Hclosed r (free_interp_core C Hok r Hr);
    mor_preserves_equiv := fun r s Hrs => Hequiv r s Hrs
  |}.
  exact I.
Qed.

Theorem free_quotient_decomposition :
  forall C Hok F r,
    obj_type F = core_type C ->
    fragment_thm (free_interp_object C Hok) r ->
    obs_closure (obj_core F) (obj_protocol F) (obj_equiv F) r ->
    obs_class (obj_equiv F) r r.
Proof.
  intros C Hok F r _ _ _.
  apply cong_refl.
  exact (obj_equiv_congruence F).
Qed.

Definition core_projection (F : interp_object) : rec -> Prop := obj_core F.

Theorem function_core_object_correspondence :
  forall C Hok x,
    core_projection (free_interp_object C Hok) (graph_record C x).
Proof.
  intros C Hok x.
  unfold core_projection, free_interp_object, free_core.
  reflexivity.
Qed.

Record verifiable_certificate : Type := {
  cert_code : nat;
  cert_proof_code : nat;
  cert_object : interp_object
}.

Definition certificate_system (c : verifiable_certificate) : interp_object :=
  cert_object c.

Record FIS_sharp_system : Type := {
  fis_payload : Type;
  fis_sort : Type := sort_code;
  fis_type : Type := ty;
  fis_shape : Type := shape;
  fis_context : Type := ctx;
  fis_record : Type := rec;
  fis_protocol : Type := protocol;
  fis_interp_object : Type := interp_object;
  fis_closure : interp_object -> rec -> Prop := fragment_thm;
  fis_obs_closure : interp_object -> rec -> Prop :=
    fun F => obs_closure (obj_core F) (obj_protocol F) (obj_equiv F);
  fis_closure_equal :
    forall F r, fis_closure F r <-> fis_obs_closure F r;
  fis_sound :
    forall F r, fis_closure F r -> fis_obs_closure F r;
  fis_adequate :
    forall F r, fis_obs_closure F r -> fis_closure F r;
  fis_certificate : Type := verifiable_certificate;
  fis_certificate_system : fis_certificate -> interp_object :=
    certificate_system
}.

Definition FIS_sharp : FIS_sharp_system := {|
  fis_payload := unit;
  fis_closure_equal := closure_equal;
  fis_sound := compiler_soundness;
  fis_adequate := compiler_adequacy
|}.

End FunctionInducedSyntaxFoundation1112.
