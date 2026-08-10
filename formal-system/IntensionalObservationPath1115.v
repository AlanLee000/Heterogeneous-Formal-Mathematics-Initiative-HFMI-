From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.

Import ListNotations.

Module IntensionalObservationPath1115.

Inductive ty (B : Type) : Type :=
| BaseTy : B -> ty B
| ArrTy : ty B -> ty B -> ty B.

Arguments BaseTy {B}.
Arguments ArrTy {B}.

Fixpoint bas {B : Type} (tau : ty B) : ty B :=
  match tau with
  | BaseTy b => BaseTy b
  | ArrTy _ rho => bas rho
  end.

Fixpoint args {B : Type} (tau : ty B) : list (ty B) :=
  match tau with
  | BaseTy _ => []
  | ArrTy sigma rho => sigma :: args rho
  end.

Fixpoint hty {B : Type} (tau : ty B) : nat :=
  match tau with
  | BaseTy _ => 0
  | ArrTy sigma rho => S (Nat.max (hty sigma) (hty rho))
  end.

Section Calculus.

Variable B : Type.
Variable B_eq_dec : forall b c : B, {b = c} + {b <> c}.

Inductive term : Type :=
| Const : nat -> term
| Bullet : nat -> ty B -> term -> term -> term
| Angle : nat -> term -> list formula -> term
| Comp : nat -> term -> term -> term
with formula : Type :=
| BForm : nat -> B -> nat -> formula
| Neg : formula -> formula
| And : formula -> formula -> formula
| Acc : nat -> term -> formula -> formula
with path : Type :=
| ZPath : formula -> path
| CPath : ty B -> term -> path -> path
with judgment : Type :=
| Obs : term -> path -> judgment
| Eval : term -> term -> nat -> ty B -> term -> judgment
| IntJ : term -> formula -> judgment.

Scheme term_ind' := Induction for term Sort Prop
with formula_ind' := Induction for formula Sort Prop
with path_ind' := Induction for path Sort Prop
with judgment_ind' := Induction for judgment Sort Prop.

Combined Scheme syntax_ind from term_ind', formula_ind', path_ind', judgment_ind'.

Record library : Type := {
  const_valid : nat -> Prop;
  const_level : nat -> nat;
  const_type : nat -> ty B;
  const_paths : nat -> list path;
  atom_ok : nat -> B -> nat -> Prop;
  atom_value : nat -> B -> nat -> bool
}.

Variable L : library.

Inductive wf_term : nat -> ty B -> term -> Prop :=
| WFConst :
    forall k,
      const_valid L k ->
      wf_term (const_level L k) (const_type L k) (Const k)
| WFBullet :
    forall ns nu m tau_s tau_u rho s u,
      wf_term ns tau_s s ->
      wf_term nu tau_u u ->
      ns <= m ->
      nu < m ->
      wf_term m rho (Bullet m rho s u)
| WFAngle :
    forall ns m tau s Lambda,
      wf_term ns tau s ->
      ns <= m ->
      Forall (fun phi => exists j, j < m /\ wf_formula j (bas tau) phi) Lambda ->
      wf_term m tau (Angle m s Lambda)
| WFComp :
    forall ns nt m tau rho s t,
      wf_term ns tau s ->
      wf_term nt rho t ->
      ns < m ->
      nt < m ->
      wf_term m tau (Comp m s t)
with wf_formula : nat -> ty B -> formula -> Prop :=
| WFBForm :
    forall n b a,
      atom_ok L n b a ->
      wf_formula n (BaseTy b) (BForm n b a)
| WFNeg :
    forall n beta phi,
      wf_formula n beta phi ->
      wf_formula (S n) beta (Neg phi)
| WFAnd :
    forall n m beta phi psi,
      wf_formula n beta phi ->
      wf_formula m beta psi ->
      wf_formula (S (Nat.max n m)) beta (And phi psi)
| WFAcc :
    forall ns nphi m tau beta s phi,
      wf_term ns tau s ->
      wf_formula nphi beta phi ->
      ns <= m ->
      nphi < m ->
      wf_formula m beta (Acc m s phi).

Scheme wf_term_ind' := Induction for wf_term Sort Prop
with wf_formula_ind' := Induction for wf_formula Sort Prop.

Combined Scheme wf_syntax_ind from wf_term_ind', wf_formula_ind'.

Inductive wf_path : nat -> ty B -> path -> Prop :=
| WFZPath :
    forall n j tau phi,
      j < n ->
      wf_formula j (bas tau) phi ->
      wf_path n tau (ZPath phi)
| WFCPath :
    forall n j sigma rho u q,
      j < n ->
      wf_term j sigma u ->
      wf_path n rho q ->
      wf_path n (ArrTy sigma rho) (CPath sigma u q).

Definition small_path (m : nat) (tau : ty B) (p : path) : Prop :=
  exists n, n < m /\ wf_path n tau p.

Fixpoint reind (m : nat) (t : term) (p : path) : path :=
  match p with
  | ZPath phi => ZPath (Acc (Nat.pred m) t phi)
  | CPath sigma u q =>
      CPath sigma (Bullet (Nat.pred m) sigma t u) (reind m t q)
  end.

Inductive sem_path : term -> path -> Prop :=
| SPConst :
    forall k p,
      In p (const_paths L k) ->
      sem_path (Const k) p
| SPBullet :
    forall m rho s u q,
      sem_path s (CPath rho u q) ->
      sem_path (Bullet m rho s u) q
| SPAngleOld :
    forall m s Lambda p,
      sem_path s p ->
      sem_path (Angle m s Lambda) p
| SPAngleNew :
    forall m s Lambda phi,
      In phi Lambda ->
      sem_path (Angle m s Lambda) (ZPath phi)
| SPComp :
    forall m s t p,
      sem_path s p ->
      sem_path (Comp m s t) (reind m t p).

Fixpoint true_formula (phi : formula) : Prop :=
  match phi with
  | BForm n b a => atom_value L n b a = true
  | Neg psi => ~ true_formula psi
  | And psi chi => true_formula psi /\ true_formula chi
  | Acc _ s psi => sem_path s (ZPath psi)
  end.

Definition wf_obs (s : term) (p : path) : Prop :=
  exists n tau, wf_term n tau s /\ wf_path n tau p.

Definition wf_eval (s u : term) (m : nat) (rho : ty B) (r : term) : Prop :=
  r = Bullet m rho s u /\ wf_term m rho r.

Definition wf_int (s : term) (phi : formula) : Prop :=
  exists n tau j,
    wf_term n tau s /\
    j < n /\
    wf_formula j (bas tau) phi.

Definition wf_judgment (J : judgment) : Prop :=
  match J with
  | Obs s p => wf_obs s p
  | Eval s u m rho r => wf_eval s u m rho r
  | IntJ s phi => wf_int s phi
  end.

Definition sat_judgment (J : judgment) : Prop :=
  match J with
  | Obs s p => sem_path s p
  | Eval s u m rho r => r = Bullet m rho s u
  | IntJ s phi => sem_path s (ZPath phi)
  end.

Variable semantic_family : nat -> ty B -> (path -> Prop) -> Prop.

Hypothesis semantic_family_contains_terms :
  forall n tau s,
    wf_term n tau s ->
    semantic_family n tau (sem_path s).

Hypothesis semantic_family_path_closed :
  forall n tau M p,
    semantic_family n tau M ->
    M p ->
    wf_path n tau p.

Definition finite_path_set (n : nat) (tau : ty B) (A : list path) : Prop :=
  Forall (wf_path n tau) A.

Definition finite_entails_at (n : nat) (tau : ty B)
    (A : list path) (q : path) : Prop :=
  finite_path_set n tau A /\
  wf_path n tau q /\
  forall M : path -> Prop,
    semantic_family n tau M ->
    (forall p, In p A -> M p) ->
    M q.

Record renaming : Type := {
  ren_term : term -> term;
  ren_formula : formula -> formula;
  ren_path : path -> path;
  ren_judgment : judgment -> judgment;
  ren_zpath :
    forall phi, ren_path (ZPath phi) = ZPath (ren_formula phi);
  ren_cpath :
    forall sigma u q,
      ren_path (CPath sigma u q) =
      CPath sigma (ren_term u) (ren_path q);
  ren_bullet :
    forall m rho s u,
      ren_term (Bullet m rho s u) =
      Bullet m rho (ren_term s) (ren_term u);
  ren_angle :
    forall m s Lambda,
      ren_term (Angle m s Lambda) =
      Angle m (ren_term s) (map ren_formula Lambda);
  ren_comp :
    forall m s t,
      ren_term (Comp m s t) =
      Comp m (ren_term s) (ren_term t);
  ren_acc :
    forall m s phi,
      ren_formula (Acc m s phi) =
      Acc m (ren_term s) (ren_formula phi);
  ren_obs :
    forall s p,
      ren_judgment (Obs s p) = Obs (ren_term s) (ren_path p);
  ren_eval :
    forall s u m rho r,
      ren_judgment (Eval s u m rho r) =
      Eval (ren_term s) (ren_term u) m rho (ren_term r);
  ren_int :
    forall s phi,
      ren_judgment (IntJ s phi) = IntJ (ren_term s) (ren_formula phi);
  ren_sem :
    forall s p, sem_path s p -> sem_path (ren_term s) (ren_path p)
}.

Variable allowed_renaming : renaming -> Prop.

Definition c_const (k : nat) : term := Const k.

Inductive fragment (k : nat) : judgment -> Prop :=
| FragAxiom :
    forall p,
      In p (const_paths L k) ->
      fragment k (Obs (c_const k) p)
| FragObsToInt :
    forall s phi,
      fragment k (Obs s (ZPath phi)) ->
      fragment k (IntJ s phi)
| FragIntToObs :
    forall s phi,
      fragment k (IntJ s phi) ->
      fragment k (Obs s (ZPath phi))
| FragEval :
    forall s u m rho r,
      r = Bullet m rho s u ->
      wf_term m rho r ->
      fragment k (Eval s u m rho r)
| FragAppForward :
    forall s u m rho r q,
      fragment k (Obs s (CPath rho u q)) ->
      r = Bullet m rho s u ->
      wf_term m rho r ->
      wf_path m rho q ->
      fragment k (Obs r q)
| FragAppBackward :
    forall s u m rho r q,
      fragment k (Obs r q) ->
      r = Bullet m rho s u ->
      wf_path (const_level L k) (const_type L k) (CPath rho u q) ->
      fragment k (Obs s (CPath rho u q))
| FragAngleOld :
    forall m s Lambda p r,
      r = Angle m s Lambda ->
      fragment k (Obs s p) ->
      fragment k (Obs r p)
| FragAngleNew :
    forall m s Lambda phi r,
      r = Angle m s Lambda ->
      In phi Lambda ->
      fragment k (Obs r (ZPath phi))
| FragComp :
    forall m s t p r,
      r = Comp m s t ->
      fragment k (Obs s p) ->
      fragment k (Obs r (reind m t p))
| FragFinite :
    forall n tau s A q,
      wf_term n tau s ->
      finite_entails_at n tau A q ->
      (forall p, In p A -> fragment k (Obs s p)) ->
      fragment k (Obs s q)
| FragRenameObs :
    forall rho s p,
      allowed_renaming rho ->
      fragment k (Obs s p) ->
      fragment k (Obs (ren_term rho s) (ren_path rho p))
| FragRenameInt :
    forall rho s phi,
      allowed_renaming rho ->
      fragment k (IntJ s phi) ->
      fragment k (IntJ (ren_term rho s) (ren_formula rho phi))
| FragRenameEval :
    forall rho s u m tau r,
      allowed_renaming rho ->
      fragment k (Eval s u m tau r) ->
      fragment k
        (Eval (ren_term rho s) (ren_term rho u) m tau (ren_term rho r)).

Definition calculus (J : judgment) : Prop := sat_judgment J.

Lemma path_monotone :
  forall n m tau p, wf_path n tau p -> n <= m -> wf_path m tau p.
Proof.
  intros n m tau p Hpath Hle.
  induction Hpath.
  - apply WFZPath with (j := j).
    + exact (Nat.lt_le_trans j n m H Hle).
    + exact H0.
  - apply WFCPath with (j := j).
    + exact (Nat.lt_le_trans j n m H Hle).
    + exact H0.
    + exact (IHHpath Hle).
Qed.

Lemma bullet_equation :
  forall m rho s u q,
    sem_path (Bullet m rho s u) q <->
    sem_path s (CPath rho u q).
Proof.
  split.
  - intro H. inversion H; subst; auto.
  - intro H. apply SPBullet. exact H.
Qed.

Lemma angle_equation :
  forall m s Lambda p,
    sem_path (Angle m s Lambda) p <->
    sem_path s p \/ exists phi, In phi Lambda /\ p = ZPath phi.
Proof.
  split.
  - intro H. inversion H; subst; eauto.
  - intros [H | [phi [Hin ->]]].
    + apply SPAngleOld. exact H.
    + apply SPAngleNew. exact Hin.
Qed.

Lemma comp_equation :
  forall m s t p,
    sem_path s p -> sem_path (Comp m s t) (reind m t p).
Proof.
  intros m s t p H. apply SPComp. exact H.
Qed.

Lemma acc_truth_equation :
  forall n s phi,
    true_formula (Acc n s phi) <-> sem_path s (ZPath phi).
Proof.
  intros. simpl. tauto.
Qed.

Lemma int_obs_equiv :
  forall s phi,
    sat_judgment (IntJ s phi) <-> sat_judgment (Obs s (ZPath phi)).
Proof.
  intros. simpl. tauto.
Qed.

Theorem fragment_sound :
  forall k J, fragment k J -> calculus J.
Proof.
  intros k J Hfrag.
  induction Hfrag.
  - simpl. apply SPConst. exact H.
  - simpl in *. exact IHHfrag.
  - simpl in *. exact IHHfrag.
  - simpl. exact H.
  - simpl. subst r.
    apply SPBullet. exact IHHfrag.
  - simpl in *. subst r.
    inversion IHHfrag; subst; auto.
  - simpl in *. subst r.
    apply SPAngleOld. exact IHHfrag.
  - simpl. subst r.
    apply SPAngleNew. exact H0.
  - simpl. subst r.
    apply SPComp. exact IHHfrag.
  - simpl.
    destruct H0 as [_ [_ Hentails]].
    apply Hentails.
    + apply semantic_family_contains_terms. exact H.
    + intros p Hp.
      apply H2. exact Hp.
  - simpl in *. apply ren_sem. exact IHHfrag.
  - simpl in *. rewrite <- (ren_zpath rho phi). apply ren_sem. exact IHHfrag.
  - simpl in *. rewrite IHHfrag. apply ren_bullet.
Qed.

Definition strong_observation_equiv (k l : nat) : Prop :=
  const_level L k = const_level L l /\
  const_type L k = const_type L l /\
  forall J, fragment k J <-> fragment l J.

Definition interface_observation_equiv (k l : nat) : Prop :=
  const_level L k = const_level L l /\
  const_type L k = const_type L l /\
  const_paths L k = const_paths L l.

Definition extensionally_separating (X : list nat) : Prop :=
  forall k l,
    In k X ->
    In l X ->
    const_paths L k <> const_paths L l ->
    exists J, fragment k J /\ ~ fragment l J.

Definition fragment_class (X : list nat) (k l : nat) : Prop :=
  In l X /\ strong_observation_equiv k l.

Record certificate_context : Type := {
  function_code : nat -> Prop;
  decode : nat -> nat -> Prop;
  decode_unique :
    forall e k l, decode e k -> decode e l -> k = l;
  zfc_proof : nat -> nat -> Prop;
  legal_name : nat -> nat -> Prop :=
    fun e k =>
      function_code e /\
      const_valid L k /\
      decode e k
}.

Record certificate (C : certificate_context) : Type := {
  cert_code : nat;
  cert_proof : nat;
  cert_const : nat;
  cert_legal : legal_name C cert_code cert_const;
  cert_zfc : zfc_proof C cert_proof cert_code
}.

Definition certificate_output {C : certificate_context}
    (c : certificate C) : judgment -> Prop :=
  fragment (cert_const C c).

Definition enumerator (C : certificate_context) : Type :=
  nat -> option (certificate C).

Definition enumerator_output {C : certificate_context}
    (E : enumerator C) (J : judgment) : Prop :=
  exists i c, E i = Some c /\ certificate_output c J.

Theorem enumerator_reliable :
  forall (C : certificate_context) (E : enumerator C) J,
    enumerator_output E J -> calculus J.
Proof.
  intros C E J [i [c [_ Hout]]].
  unfold certificate_output in Hout.
  apply fragment_sound with (k := cert_const C c).
  exact Hout.
Qed.

Record judgment_model : Type := {
  model_satisfies : judgment -> Prop
}.

Definition standard_judgment_model : judgment_model := {|
  model_satisfies := sat_judgment
|}.

Definition positive_eval_judgment (tau : ty B) : judgment :=
  (Eval (Const 0) (Const 0) 0 tau (Bullet 0 tau (Const 0) (Const 0))).

Definition negative_eval_judgment (tau : ty B) : judgment :=
  (Eval (Const 0) (Const 0) 0 tau (Const 0)).

Theorem standard_semantics_nontrivial :
  forall tau,
    model_satisfies standard_judgment_model (positive_eval_judgment tau) /\
    ~ model_satisfies standard_judgment_model (negative_eval_judgment tau).
Proof.
  intro tau.
  split.
  - reflexivity.
  - simpl. discriminate.
Qed.

Record calculus_system : Type := {
  system_library : library;
  system_semantic_family : nat -> ty B -> (path -> Prop) -> Prop;
  system_semantic_family_contains_terms :
    forall n tau s,
      wf_term n tau s ->
      system_semantic_family n tau (sem_path s);
  system_finite_entails : nat -> ty B -> list path -> path -> Prop;
  system_renaming_ok : renaming -> Prop;
  system_wf_judgment : judgment -> Prop;
  system_sat_judgment : judgment -> Prop;
  system_fragment : nat -> judgment -> Prop;
  system_sound :
    forall k J, system_fragment k J -> system_sat_judgment J;
  system_model : judgment_model;
  system_semantic_nontriviality :
    forall tau,
      model_satisfies system_model (positive_eval_judgment tau) /\
      ~ model_satisfies system_model (negative_eval_judgment tau)
}.

Definition final_system : calculus_system :=
  {| system_library := L;
     system_semantic_family := semantic_family;
     system_semantic_family_contains_terms := semantic_family_contains_terms;
     system_finite_entails := finite_entails_at;
     system_renaming_ok := allowed_renaming;
     system_wf_judgment := wf_judgment;
     system_sat_judgment := sat_judgment;
     system_fragment := fragment;
     system_sound := fragment_sound;
     system_model := standard_judgment_model;
     system_semantic_nontriviality := standard_semantics_nontrivial |}.

Record certified_calculus_system : Type := {
  certified_core : calculus_system;
  certified_context : certificate_context;
  certified_context_nonempty : inhabited (certificate certified_context)
}.

Definition attach_certificate_layer
    (C : certificate_context) (HC : inhabited (certificate C))
    : certified_calculus_system := {|
  certified_core := final_system;
  certified_context := C;
  certified_context_nonempty := HC
|}.

End Calculus.

End IntensionalObservationPath1115.
