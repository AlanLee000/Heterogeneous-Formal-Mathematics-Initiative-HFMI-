From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.

Import ListNotations.


Module ReifiedQuotientStructure.

Record Var : Type := mkVar {
  vlev : nat;
  vid : nat
}.

Definition var_eq_dec : forall x y : Var, {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition remove_var (x : Var) (xs : list Var) : list Var :=
  remove var_eq_dec x xs.

Fixpoint fresh_from (fuel n : nat) (used : list nat) : nat :=
  match fuel with
  | O => n
  | S fuel' =>
      if in_dec Nat.eq_dec n used
      then fresh_from fuel' (S n) used
      else n
  end.

Definition ids_at (m : nat) (xs : list Var) : list nat :=
  fold_right
    (fun x acc => if Nat.eq_dec (vlev x) m then vid x :: acc else acc)
    [] xs.

Definition fresh_m (m : nat) (xs : list Var) : Var :=
  mkVar m (fresh_from (S (length xs)) 0 (ids_at m xs)).

Inductive Term : Type :=
| TVar : Var -> Term
| TReif : nat -> Frm -> Term
with Frm : Type :=
| FBot : Frm
| FPred : Term -> Term -> Frm
| FNeg : Frm -> Frm
| FAnd : Frm -> Frm -> Frm
| FEx : Var -> Frm -> Frm.

Definition term_level (t : Term) : nat :=
  match t with
  | TVar x => vlev x
  | TReif n _ => S n
  end.

Fixpoint frm_level (a : Frm) : nat :=
  match a with
  | FBot => 0
  | FPred t _ => term_level t
  | FNeg b => frm_level b
  | FAnd b c => Nat.max (frm_level b) (frm_level c)
  | FEx x b => Nat.max (vlev x) (frm_level b)
  end.

Fixpoint wellT (t : Term) : Prop :=
  match t with
  | TVar _ => True
  | TReif n a => wellF a /\ frm_level a <= n
  end
with wellF (a : Frm) : Prop :=
  match a with
  | FBot => True
  | FPred t u => wellT t /\ wellT u /\ term_level u < term_level t
  | FNeg b => wellF b
  | FAnd b c => wellF b /\ wellF c
  | FEx _ b => wellF b
  end.

Definition TermAt (n : nat) (t : Term) : Prop :=
  wellT t /\ term_level t <= n.

Definition FrmAt (n : nat) (a : Frm) : Prop :=
  wellF a /\ frm_level a <= n.

Definition TermExact (n : nat) (t : Term) : Prop :=
  TermAt n t /\ term_level t = n.

Definition FrmExact (n : nat) (a : Frm) : Prop :=
  FrmAt n a /\ frm_level a = n.

Definition TermOmega (t : Term) : Prop :=
  exists n, TermAt n t.

Definition FrmOmega (a : Frm) : Prop :=
  exists n, FrmAt n a.

Fixpoint fvT (t : Term) : list Var :=
  match t with
  | TVar x => [x]
  | TReif _ a => fvF a
  end
with fvF (a : Frm) : list Var :=
  match a with
  | FBot => []
  | FPred t u => fvT t ++ fvT u
  | FNeg b => fvF b
  | FAnd b c => fvF b ++ fvF c
  | FEx x b => remove_var x (fvF b)
  end.

Definition FOr (a b : Frm) : Frm :=
  FNeg (FAnd (FNeg a) (FNeg b)).

Definition FImp (a b : Frm) : Frm :=
  FNeg (FAnd a (FNeg b)).

Definition FIff (a b : Frm) : Frm :=
  FAnd (FImp a b) (FImp b a).

Definition FAll (x : Var) (a : Frm) : Frm :=
  FNeg (FEx x (FNeg a)).

Inductive SubT : Term -> Var -> Var -> Term -> Prop :=
| SubTVarSame :
    forall x y, vlev x = vlev y -> SubT (TVar x) x y (TVar y)
| SubTVarDiff :
    forall x y z, vlev x = vlev y -> z <> x -> SubT (TVar z) x y (TVar z)
| SubTReif :
    forall n a x y a',
      SubF a x y a' ->
      SubT (TReif n a) x y (TReif n a')
with SubF : Frm -> Var -> Var -> Frm -> Prop :=
| SubFBot :
    forall x y, vlev x = vlev y -> SubF FBot x y FBot
| SubFPred :
    forall t u x y t' u',
      SubT t x y t' ->
      SubT u x y u' ->
      SubF (FPred t u) x y (FPred t' u')
| SubFNeg :
    forall a x y a',
      SubF a x y a' ->
      SubF (FNeg a) x y (FNeg a')
| SubFAnd :
    forall a b x y a' b',
      SubF a x y a' ->
      SubF b x y b' ->
      SubF (FAnd a b) x y (FAnd a' b')
| SubFExShadow :
    forall z x y a,
      vlev x = vlev y ->
      z = x ->
      SubF (FEx z a) x y (FEx z a)
| SubFExClear :
    forall z x y a a',
      z <> x ->
      z <> y ->
      SubF a x y a' ->
      SubF (FEx z a) x y (FEx z a')
| SubFExCapture :
    forall z x y a w a1 a2,
      z <> x ->
      z = y ->
      w = fresh_m (vlev z) (fvF a ++ [x; y]) ->
      SubF a z w a1 ->
      SubF a1 x y a2 ->
      SubF (FEx z a) x y (FEx w a2).

Scheme SubT_ind' := Induction for SubT Sort Prop
with SubF_ind' := Induction for SubF Sort Prop.
Combined Scheme Sub_mutind from SubT_ind', SubF_ind'.

Lemma subst_same_level_mut :
  (forall t x y t',
    SubT t x y t' ->
    vlev x = vlev y) /\
  (forall a x y a',
    SubF a x y a' ->
    vlev x = vlev y).
Proof.
  apply Sub_mutind; eauto.
Qed.

Theorem substitution_same_level_term :
  forall t x y t',
    SubT t x y t' ->
    vlev x = vlev y.
Proof.
  exact (proj1 subst_same_level_mut).
Qed.

Theorem substitution_same_level_formula :
  forall a x y a',
    SubF a x y a' ->
    vlev x = vlev y.
Proof.
  exact (proj2 subst_same_level_mut).
Qed.

Lemma subst_preserves_level_mut :
  (forall t x y t',
    SubT t x y t' ->
    vlev x = vlev y ->
    term_level t' = term_level t) /\
  (forall a x y a',
    SubF a x y a' ->
    vlev x = vlev y ->
    frm_level a' = frm_level a).
Proof.
  apply Sub_mutind; simpl; intros; try reflexivity.
  - symmetry. exact H.
  - exact (H H1).
  - now rewrite (H H0).
  - now rewrite (H H1), (H0 H1).
  - now rewrite (H H0).
  - assert (Hzw : vlev z = vlev w).
    { subst w. unfold fresh_m. simpl. reflexivity. }
    rewrite (H0 H1).
    rewrite (H Hzw).
    rewrite <- Hzw.
    reflexivity.
Qed.

Theorem substitution_preserves_term_level :
  forall t x y t',
    SubT t x y t' ->
    vlev x = vlev y ->
    term_level t' = term_level t.
Proof.
  exact (proj1 subst_preserves_level_mut).
Qed.

Theorem substitution_preserves_formula_level :
  forall a x y a',
    SubF a x y a' ->
    vlev x = vlev y ->
    frm_level a' = frm_level a.
Proof.
  exact (proj2 subst_preserves_level_mut).
Qed.

Inductive Alpha : Frm -> Frm -> Prop :=
| AlphaRefl :
    forall a, Alpha a a
| AlphaSym :
    forall a b, Alpha a b -> Alpha b a
| AlphaTrans :
    forall a b c, Alpha a b -> Alpha b c -> Alpha a c
| AlphaBot :
    Alpha FBot FBot
| AlphaPred :
    forall t u, Alpha (FPred t u) (FPred t u)
| AlphaNeg :
    forall a b, Alpha a b -> Alpha (FNeg a) (FNeg b)
| AlphaAnd :
    forall a b c d,
      Alpha a b ->
      Alpha c d ->
      Alpha (FAnd a c) (FAnd b d)
| AlphaExSame :
    forall x a b,
      Alpha a b ->
      Alpha (FEx x a) (FEx x b)
| AlphaExRename :
    forall x y a b,
      vlev x = vlev y ->
      ~ In y (remove_var x (fvF a)) ->
      SubF a x y b ->
      Alpha (FEx x a) (FEx y b).

Definition IntensionalEq (n : nat) (t u : Term) : Frm :=
  let w := fresh_m (S n) (fvT t ++ fvT u) in
  FNeg (FEx w (FNeg (FIff (FPred (TVar w) t) (FPred (TVar w) u)))).

Definition ExistsUniqueCore
    (x y : Var) (a a_y : Frm) : Frm :=
  FEx x
    (FAnd a
      (FNeg (FEx y
        (FNeg (FImp a_y (IntensionalEq (vlev x) (TVar x) (TVar y))))))).

Record SRLStructure : Type := {
  carrier : Type;
  sort : nat -> carrier -> Prop;
  sort_nonempty : forall n, exists a, sort n a;
  sort_disjoint :
    forall n m a, n <> m -> sort n a -> sort m a -> False;
  PRel : nat -> nat -> carrier -> carrier -> Prop
}.

Record Assignment (m : SRLStructure) : Type := {
  aval : Var -> carrier m;
  aval_sort : forall x, sort m (vlev x) (aval x)
}.

Arguments aval {m} _ _.
Arguments aval_sort {m} _ _.

Record Reifier (m : SRLStructure) : Type := {
  J : nat -> Frm -> Assignment m -> carrier m;
  J_sort :
    forall n a rho, FrmAt n a -> sort m (S n) (J n a rho)
}.

Definition cast_sort
    {m : SRLStructure} {n k : nat} {a : carrier m}
    (h : n = k) (ha : sort m k a) : sort m n a :=
  match h in _ = k' return sort m k' a -> sort m n a with
  | eq_refl => fun hb => hb
  end ha.

Definition update
    (m : SRLStructure) (rho : Assignment m)
    (x : Var) (a : carrier m) (ha : sort m (vlev x) a)
    : Assignment m.
Proof.
  refine {| aval := fun z => if var_eq_dec z x then a else aval rho z |}.
  intro z.
  destruct (var_eq_dec z x) as [Hz | Hz].
  - subst z. exact ha.
  - exact (aval_sort rho z).
Defined.

Definition update_to_var
    (m : SRLStructure) (rho : Assignment m)
    (x y : Var) (hxy : vlev x = vlev y)
    : Assignment m :=
  update m rho x (aval rho y) (cast_sort hxy (aval_sort rho y)).

Definition AgreeOn
    {m : SRLStructure}
    (rho sigma : Assignment m) (xset : Var -> Prop) : Prop :=
  forall x, xset x -> aval rho x = aval sigma x.

Definition Perturb
    {m : SRLStructure}
    (xset : Var -> Prop) (rho sigma : Assignment m) : Prop :=
  forall x, ~ xset x -> aval rho x = aval sigma x.

Definition V_le (n : nat) : Var -> Prop :=
  fun x => vlev x <= n.

Definition V_level_except (level : nat) (x : Var) : Var -> Prop :=
  fun z => vlev z = level /\ z <> x.

Definition evalT
    (m : SRLStructure) (r : Reifier m) (rho : Assignment m)
    (t : Term) : carrier m :=
  match t with
  | TVar x => aval rho x
  | TReif n a => J m r n a rho
  end.

Fixpoint forces
    (m : SRLStructure) (r : Reifier m) (rho : Assignment m)
    (a : Frm) : Prop :=
  match a with
  | FBot => False
  | FPred t u =>
      PRel m (term_level t) (term_level u)
        (evalT m r rho t) (evalT m r rho u)
  | FNeg b => ~ forces m r rho b
  | FAnd b c => forces m r rho b /\ forces m r rho c
  | FEx x b =>
      exists d, exists hd : sort m (vlev x) d,
        forces m r (update m rho x d hd) b
  end.

Definition canonical_srl_structure : SRLStructure.
Proof.
  refine {|
    carrier := nat;
    sort := fun n a => a = n;
    sort_nonempty := _;
    sort_disjoint := _;
    PRel := fun _ _ _ _ => True
  |}.
  - intro n. exists n. reflexivity.
  - intros n k a Hnk Han Hak.
    apply Hnk. exact (eq_trans (eq_sym Han) Hak).
Defined.

Definition canonical_assignment : Assignment canonical_srl_structure.
Proof.
  refine (@Build_Assignment canonical_srl_structure
    (fun x : Var => vlev x) _).
  intro x. reflexivity.
Defined.

Definition canonical_reifier : Reifier canonical_srl_structure.
Proof.
  refine (@Build_Reifier canonical_srl_structure
    (fun n (_ : Frm) (_ : Assignment canonical_srl_structure) => S n) _).
  intros n a rho hfrm. reflexivity.
Defined.

Fixpoint canonical_truth (a : Frm) : Prop :=
  match a with
  | FBot => False
  | FPred _ _ => True
  | FNeg b => ~ canonical_truth b
  | FAnd b c => canonical_truth b /\ canonical_truth c
  | FEx _ b => canonical_truth b
  end.

Lemma canonical_forces_iff :
  forall rho a,
    forces canonical_srl_structure canonical_reifier rho a <->
    canonical_truth a.
Proof.
  intros rho a. revert rho.
  induction a as [|t u|b IHb|b IHb c IHc|x b IHb];
    intro rho; cbn.
  - tauto.
  - tauto.
  - rewrite IHb. tauto.
  - rewrite IHb, IHc. tauto.
  - split.
    + intros [d [hd Hb]].
      exact (proj1 (IHb
        (update canonical_srl_structure rho x d hd)) Hb).
    + intro Hb.
      exists (vlev x). exists eq_refl.
      exact (proj2 (IHb
        (update canonical_srl_structure rho x (vlev x) eq_refl)) Hb).
Qed.

Lemma canonical_truth_substitution :
  forall a x y a',
    SubF a x y a' ->
    (canonical_truth a' <-> canonical_truth a).
Proof.
  intros a x y a' Hsub.
  induction Hsub; cbn in *; try tauto.
Qed.

Definition quotient_equiv
    (m : SRLStructure) (r : Reifier m)
    (level : nat) (a : Frm) (rho : Assignment m)
    (p q : carrier m) : Prop :=
  forall x,
    forall hx : vlev x = level,
    forall sigma,
      Perturb (V_level_except level x) rho sigma ->
      forall hp : sort m level p,
      forall hq : sort m level q,
        forces m r (update m sigma x p (cast_sort hx hp)) a <->
        forces m r (update m sigma x q (cast_sort hx hq)) a.

Definition Selected
    (m : SRLStructure) (r : Reifier m)
    (n level : nat) (a : Frm) (rho : Assignment m)
    (base b : carrier m) : Prop :=
  sort m level b /\
  quotient_equiv m r level a rho b base /\
  PRel m (S n) level (J m r n a rho) b.

Definition QuotientClass
    (m : SRLStructure) (r : Reifier m)
    (level : nat) (a : Frm) (rho : Assignment m)
    (base b : carrier m) : Prop :=
  sort m level base /\
  sort m level b /\
  quotient_equiv m r level a rho b base.

Definition QuotientRepresentative
    (m : SRLStructure) (r : Reifier m)
    (n level : nat) (a : Frm) (rho : Assignment m)
    (base b : carrier m) : Prop :=
  QuotientClass m r level a rho base b /\
  PRel m (S n) level (J m r n a rho) b.

Record AdmModel (m : SRLStructure) (r : Reifier m) : Prop := {
  adm_local_determinacy :
    forall n a rho sigma,
      FrmAt n a ->
      AgreeOn rho sigma (fun x => In x (fvF a)) ->
      J m r n a rho = J m r n a sigma;
  adm_reif_subst_compat :
    forall n a a' x y rho hxy,
      FrmAt n a ->
      SubF a x y a' ->
      J m r n a' rho = J m r n a (update_to_var m rho x y hxy);
  adm_formula_subst_compat :
    forall a a' x y rho hxy,
      wellF a ->
      SubF a x y a' ->
      (forces m r rho a' <->
       forces m r (update_to_var m rho x y hxy) a);
  adm_dynamic_extensionality :
    forall n a b rho,
      FrmAt n a ->
      FrmAt n b ->
      (forall sigma,
        Perturb (V_le n) rho sigma ->
        (forces m r sigma a <-> forces m r sigma b)) ->
      J m r n a rho = J m r n b rho;
  adm_quotient_choice :
    forall n level a rho,
      level <= n ->
      FrmAt n a ->
      forall base,
        sort m level base ->
        exists b,
          Selected m r n level a rho base b /\
          forall c,
            Selected m r n level a rho base c ->
            c = b
}.

Definition canonical_admissible_model :
    AdmModel canonical_srl_structure canonical_reifier.
Proof.
  refine {|
    adm_local_determinacy := _;
    adm_reif_subst_compat := _;
    adm_formula_subst_compat := _;
    adm_dynamic_extensionality := _;
    adm_quotient_choice := _
  |}.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros a a' x y rho hxy hwell hsub.
    rewrite !canonical_forces_iff.
    exact (canonical_truth_substitution a x y a' hsub).
  - intros. reflexivity.
  - intros n level a rho hle hfrm base hbase.
    exists level.
    split.
    + split.
      * reflexivity.
      * split.
        -- unfold quotient_equiv.
           intros x hx sigma hpert hp hq.
           rewrite !canonical_forces_iff. tauto.
        -- exact I.
    + intros c Hselected.
      destruct Hselected as [Hc _].
      exact Hc.
Defined.

Theorem canonical_srl_semantics_nontrivial :
  forces canonical_srl_structure canonical_reifier
    canonical_assignment (FNeg FBot) /\
  ~ forces canonical_srl_structure canonical_reifier
      canonical_assignment FBot.
Proof.
  cbn. tauto.
Qed.

Definition AdmSRL (m : SRLStructure) (r : Reifier m) : Prop :=
  AdmModel m r.

Theorem semantic_formula_substitution :
  forall m r,
    AdmModel m r ->
    forall a a' x y rho hxy,
      wellF a ->
      SubF a x y a' ->
      (forces m r rho a' <->
       forces m r (update_to_var m rho x y hxy) a).
Proof.
  intros m r hadm.
  exact (adm_formula_subst_compat m r hadm).
Qed.

Theorem adm_structured_quotient_choice :
  forall m r,
    AdmModel m r ->
    forall n level a rho,
      level <= n ->
      FrmAt n a ->
      forall base,
        sort m level base ->
        exists b,
          QuotientRepresentative m r n level a rho base b /\
          forall c,
            QuotientRepresentative m r n level a rho base c ->
            c = b.
Proof.
  intros m r hadm n level a rho hle hfrm base hbase.
  destruct (adm_quotient_choice m r hadm n level a rho hle hfrm base hbase)
    as [b [[hb [heq hrel]] huniq]].
  exists b.
  split.
  - split.
    + split; [exact hbase |].
      split; [exact hb | exact heq].
    + exact hrel.
  - intros c [[_ [hc heqc]] hrelc].
    apply huniq.
    split; [exact hc |].
    split; [exact heqc | exact hrelc].
Qed.

Definition SemEntails (gamma : Frm -> Prop) (a : Frm) : Prop :=
  forall m r,
    AdmModel m r ->
    forall rho,
      (forall b, gamma b -> forces m r rho b) ->
      forces m r rho a.

Lemma quotient_equiv_bot :
  forall m r level rho p q,
    quotient_equiv m r level FBot rho p q.
Proof.
  unfold quotient_equiv.
  intros m r level rho p q x hx sigma _ hp hq.
  simpl.
  split; intro h; exact h.
Qed.

Theorem dynamic_extensional_collapse :
  forall m r n a b rho,
    AdmModel m r ->
    FrmAt n a ->
    FrmAt n b ->
    (forall sigma,
      Perturb (V_le n) rho sigma ->
      (forces m r sigma a <-> forces m r sigma b)) ->
    J m r n a rho = J m r n b rho.
Proof.
  intros m r n a b rho hadm.
  exact (adm_dynamic_extensionality m r hadm n a b rho).
Qed.

Theorem rigid_projection :
  forall m r n level a rho,
    AdmModel m r ->
    level <= n ->
    FrmAt n a ->
    (forall p q,
      sort m level p ->
      sort m level q ->
      quotient_equiv m r level a rho p q ->
      p = q) ->
    forall p,
      sort m level p ->
      PRel m (S n) level (J m r n a rho) p.
Proof.
  intros m r n level a rho hadm hle hfrm hidentity p hp.
  destruct (adm_quotient_choice m r hadm n level a rho hle hfrm p hp)
    as [b [[hb [hequiv hrel]] _]].
  pose proof (hidentity b p hb hp hequiv) as hb_eq.
  now subst b.
Qed.

Theorem false_singleton_collapse :
  forall m r n level rho,
    AdmModel m r ->
    level <= n ->
    FrmAt n FBot ->
    forall base,
      sort m level base ->
      exists b,
        sort m level b /\
        quotient_equiv m r level FBot rho b base /\
        PRel m (S n) level (J m r n FBot rho) b /\
        forall c,
          sort m level c ->
          quotient_equiv m r level FBot rho c base ->
          PRel m (S n) level (J m r n FBot rho) c ->
          c = b.
Proof.
  intros m r n level rho hadm hle hbot base hbase.
  destruct (adm_quotient_choice m r hadm n level FBot rho hle hbot base hbase)
    as [b [[hb [hequiv hrel]] huniq]].
  exists b.
  split; [exact hb |].
  split; [exact hequiv |].
  split; [exact hrel |].
  intros c hc heq hrelc.
  apply huniq.
  split; [exact hc |].
  split; [exact heq | exact hrelc].
Qed.

Record ReifiedQuotientSystem : Type := {
  sys_Var : Type;
  sys_Term : Type;
  sys_Frm : Type;
  sys_TermAt : nat -> Term -> Prop;
  sys_FrmAt : nat -> Frm -> Prop;
  sys_lev : Term -> nat;
  sys_flev : Frm -> nat;
  sys_FV_T : Term -> list Var;
  sys_FV_F : Frm -> list Var;
  sys_fresh_m : nat -> list Var -> Var;
  sys_SubT : Term -> Var -> Var -> Term -> Prop;
  sys_SubF : Frm -> Var -> Var -> Frm -> Prop;
  sys_Alpha : Frm -> Frm -> Prop;
  sys_IntensionalEq : nat -> Term -> Term -> Frm;
  sys_SRLStructure : Type;
  sys_Reifier : SRLStructure -> Type;
  sys_Assignment : SRLStructure -> Type;
  sys_forces : forall m, Reifier m -> Assignment m -> Frm -> Prop;
  sys_AdmModel : forall m, Reifier m -> Prop;
  sys_concrete_structure : SRLStructure;
  sys_concrete_reifier : Reifier sys_concrete_structure;
  sys_concrete_assignment : Assignment sys_concrete_structure;
  sys_concrete_admissible :
    AdmModel sys_concrete_structure sys_concrete_reifier;
  sys_semantic_nontrivial :
    forces sys_concrete_structure sys_concrete_reifier
      sys_concrete_assignment (FNeg FBot) /\
    ~ forces sys_concrete_structure sys_concrete_reifier
        sys_concrete_assignment FBot;
  sys_SemEntails : (Frm -> Prop) -> Frm -> Prop
}.

Definition L_SRL : ReifiedQuotientSystem := {|
  sys_Var := Var;
  sys_Term := Term;
  sys_Frm := Frm;
  sys_TermAt := TermAt;
  sys_FrmAt := FrmAt;
  sys_lev := term_level;
  sys_flev := frm_level;
  sys_FV_T := fvT;
  sys_FV_F := fvF;
  sys_fresh_m := fresh_m;
  sys_SubT := SubT;
  sys_SubF := SubF;
  sys_Alpha := Alpha;
  sys_IntensionalEq := IntensionalEq;
  sys_SRLStructure := SRLStructure;
  sys_Reifier := Reifier;
  sys_Assignment := Assignment;
  sys_forces := forces;
  sys_AdmModel := AdmModel;
  sys_concrete_structure := canonical_srl_structure;
  sys_concrete_reifier := canonical_reifier;
  sys_concrete_assignment := canonical_assignment;
  sys_concrete_admissible := canonical_admissible_model;
  sys_semantic_nontrivial := canonical_srl_semantics_nontrivial;
  sys_SemEntails := SemEntails
|}.

End ReifiedQuotientStructure.
