From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.

Import ListNotations.

Module StratifiedIntensionalClosure1079.

Inductive formula : Type :=
| FAtom : nat -> nat -> formula
| FBot : nat -> formula
| FNeg : formula -> formula
| FAnd : formula -> formula -> formula
| FOr : formula -> formula -> formula
| FImp : formula -> formula -> formula
| FAct : term -> formula -> formula
with term : Type :=
| TVar : nat -> nat -> term
| TConst : nat -> nat -> term
| TBullet : term -> term -> term
| TComp : term -> term -> term
| TIndex : term -> list formula -> term.

Scheme formula_ind' := Induction for formula Sort Prop
with term_ind' := Induction for term Sort Prop.

Fixpoint trank (s : term) : nat :=
  match s with
  | TVar n _ => n
  | TConst n _ => n
  | TBullet a _ => trank a
  | TComp a _ => trank a
  | TIndex a _ => trank a
  end.

Fixpoint frank (phi : formula) : nat :=
  match phi with
  | FAtom n _ => n
  | FBot n => n
  | FNeg a => frank a
  | FAnd a b => Nat.max (frank a) (frank b)
  | FOr a b => Nat.max (frank a) (frank b)
  | FImp a b => Nat.max (frank a) (frank b)
  | FAct s _ => trank s
  end.

Definition lower_term_than (n : nat) (s : term) : Prop :=
  trank s < n.

Definition lower_formula_than (n : nat) (phi : formula) : Prop :=
  frank phi < n.

Inductive wf_formula : nat -> formula -> Prop :=
| WFAtom :
    forall n i, wf_formula n (FAtom n i)
| WFBot :
    forall n, wf_formula n (FBot n)
| WFNeg :
    forall n phi,
      wf_formula n phi ->
      wf_formula n (FNeg phi)
| WFAnd :
    forall m n phi psi,
      wf_formula m phi ->
      wf_formula n psi ->
      wf_formula (Nat.max m n) (FAnd phi psi)
| WFOr :
    forall m n phi psi,
      wf_formula m phi ->
      wf_formula n psi ->
      wf_formula (Nat.max m n) (FOr phi psi)
| WFImp :
    forall m n phi psi,
      wf_formula m phi ->
      wf_formula n psi ->
      wf_formula (Nat.max m n) (FImp phi psi)
| WFAct :
    forall n m s phi,
      wf_term n s ->
      wf_formula m phi ->
      m < n ->
      wf_formula n (FAct s phi)
with wf_term : nat -> term -> Prop :=
| WFTVar :
    forall n i, wf_term n (TVar n i)
| WFTConst :
    forall n i, wf_term n (TConst n i)
| WFTBullet :
    forall n m s t,
      wf_term n s ->
      wf_term m t ->
      m < n ->
      wf_term n (TBullet s t)
| WFTComp :
    forall n m s t,
      wf_term n s ->
      wf_term m t ->
      m < n ->
      wf_term n (TComp s t)
| WFTIndex :
    forall n s Lambda,
      wf_term n s ->
      Forall
        (fun phi => wf_formula (frank phi) phi /\ frank phi < n)
        Lambda ->
      wf_term n (TIndex s Lambda).

Scheme wf_formula_ind' := Induction for wf_formula Sort Prop
with wf_term_ind' := Induction for wf_term Sort Prop.

Theorem wf_term_rank_exact :
  forall n s, wf_term n s -> trank s = n.
Proof.
  intros n s H.
  induction H; simpl; auto.
Qed.

Theorem wf_formula_rank_exact :
  forall n phi, wf_formula n phi -> frank phi = n.
Proof.
  intros n phi H.
  induction H; simpl; try reflexivity; try assumption;
    try
      (repeat match goal with
       | Hrank : frank ?a = ?r |- context[frank ?a] => rewrite Hrank
       end; reflexivity).
  exact (wf_term_rank_exact n s H).
Qed.

Theorem wf_term_rank_unique :
  forall m n s, wf_term m s -> wf_term n s -> m = n.
Proof.
  intros m n s Hm Hn.
  rewrite <- (wf_term_rank_exact m s Hm).
  rewrite <- (wf_term_rank_exact n s Hn).
  reflexivity.
Qed.

Theorem wf_formula_rank_unique :
  forall m n phi, wf_formula m phi -> wf_formula n phi -> m = n.
Proof.
  intros m n phi Hm Hn.
  rewrite <- (wf_formula_rank_exact m phi Hm).
  rewrite <- (wf_formula_rank_exact n phi Hn).
  reflexivity.
Qed.

Record path : Type := {
  path_terms : list term;
  path_formula : formula
}.

Definition path_wf (n : nat) (p : path) : Prop :=
  Forall
    (fun s => wf_term (trank s) s /\ trank s < n)
    (path_terms p) /\
  wf_formula (frank (path_formula p)) (path_formula p) /\
  frank (path_formula p) < n.

Definition domain (n : nat) : Type := path -> Prop.

Definition domain_respects_level (n : nat) (A : domain n) : Prop :=
  forall p, A p -> path_wf n p.

Definition empty_path (phi : formula) : path :=
  {| path_terms := []; path_formula := phi |}.

Definition prepend_path (s : term) (p : path) : path :=
  {| path_terms := s :: path_terms p; path_formula := path_formula p |}.

Definition resid {n : nat} (A : domain n) (u : term) : domain n :=
  fun p => A (prepend_path u p).

Definition index_ext {n : nat} (A : domain n) (Lambda : list formula) : domain n :=
  fun p => A p \/ (path_terms p = [] /\ In (path_formula p) Lambda).

Definition comp {n : nat} (A : domain n) (t : term) : domain n :=
  fun p =>
    match path_terms p with
    | [] =>
        frank (path_formula p) < trank t /\
        A (empty_path (FAct t (path_formula p)))
    | u :: rest =>
        trank u < trank t /\
        A {| path_terms := TBullet t u :: rest;
             path_formula := path_formula p |}
    end.

Record model : Type := {
  atom_value : nat -> nat -> Prop;
  const_value : forall n, nat -> domain n;
  const_value_level :
    forall n i, domain_respects_level n (const_value n i)
}.

Record valuation : Type := {
  var_value : forall n, nat -> domain n;
  var_value_level :
    forall n i, domain_respects_level n (var_value n i)
}.

Fixpoint term_denote (M : model) (nu : valuation) (s : term)
    : domain (trank s) :=
  match s with
  | TVar n i => var_value nu n i
  | TConst n i => const_value M n i
  | TBullet a b => resid (term_denote M nu a) b
  | TComp a b => comp (term_denote M nu a) b
  | TIndex a Lambda => index_ext (term_denote M nu a) Lambda
  end.

Fixpoint holds (M : model) (nu : valuation) (phi : formula) : Prop :=
  match phi with
  | FAtom n i => atom_value M n i
  | FBot _ => False
  | FNeg a => ~ holds M nu a
  | FAnd a b => holds M nu a /\ holds M nu b
  | FOr a b => holds M nu a \/ holds M nu b
  | FImp a b => holds M nu a -> holds M nu b
  | FAct s a =>
      frank a < trank s /\
      term_denote M nu s (empty_path a)
  end.

Definition bool_truth (P : Prop) (b : bool) : Prop :=
  if b then P else ~ P.

Definition domain_equiv {n : nat} (A B : domain n) : Prop :=
  forall p, A p <-> B p.

Inductive judgment : Type :=
| JFormula : formula -> bool -> judgment
| JTermFormula : term -> formula -> bool -> judgment
| JTermTerm : term -> term -> term -> judgment.

Definition judgment_wf (J : judgment) : Prop :=
  match J with
  | JFormula phi _ => wf_formula (frank phi) phi
  | JTermFormula s phi _ =>
      wf_term (trank s) s /\
      wf_formula (frank phi) phi /\
      frank phi < trank s
  | JTermTerm s u v =>
      wf_term (trank s) s /\
      wf_term (trank u) u /\
      wf_term (trank v) v /\
      trank u < trank s /\
      trank v = trank s
  end.

Definition satisfies (M : model) (nu : valuation) (J : judgment) : Prop :=
  match J with
  | JFormula phi b => bool_truth (holds M nu phi) b
  | JTermFormula s phi b => bool_truth (holds M nu (FAct s phi)) b
  | JTermTerm s u v =>
      domain_equiv
        (term_denote M nu (TBullet s u))
        (term_denote M nu v)
  end.

Definition theory := judgment -> Prop.

Definition sem_entails (Gamma : theory) (J : judgment) : Prop :=
  forall M nu,
    (forall G, Gamma G -> satisfies M nu G) ->
    satisfies M nu J.

Definition bijective (f : nat -> nat) : Prop :=
  (forall x y, f x = f y -> x = y) /\
  (forall y, exists x, f x = y).

Record allowed_renaming : Type := {
  ren_var : nat -> nat -> nat;
  ren_const : nat -> nat -> nat;
  ren_atom : nat -> nat -> nat;
  ren_var_inv : nat -> nat -> nat;
  ren_const_inv : nat -> nat -> nat;
  ren_atom_inv : nat -> nat -> nat;
  ren_var_bijective : forall n, bijective (ren_var n);
  ren_const_bijective : forall n, bijective (ren_const n);
  ren_atom_bijective : forall n, bijective (ren_atom n);
  ren_var_left_inverse :
    forall n i, ren_var_inv n (ren_var n i) = i;
  ren_var_right_inverse :
    forall n i, ren_var n (ren_var_inv n i) = i;
  ren_const_left_inverse :
    forall n i, ren_const_inv n (ren_const n i) = i;
  ren_const_right_inverse :
    forall n i, ren_const n (ren_const_inv n i) = i;
  ren_atom_left_inverse :
    forall n i, ren_atom_inv n (ren_atom n i) = i;
  ren_atom_right_inverse :
    forall n i, ren_atom n (ren_atom_inv n i) = i
}.

Lemma id_nat_bijective : bijective (fun x => x).
Proof.
  split.
  - intros x y H. exact H.
  - intros y. exists y. reflexivity.
Qed.

Definition identity_renaming : allowed_renaming := {|
  ren_var := fun _ i => i;
  ren_const := fun _ i => i;
  ren_atom := fun _ i => i;
  ren_var_inv := fun _ i => i;
  ren_const_inv := fun _ i => i;
  ren_atom_inv := fun _ i => i;
  ren_var_bijective := fun _ => id_nat_bijective;
  ren_const_bijective := fun _ => id_nat_bijective;
  ren_atom_bijective := fun _ => id_nat_bijective;
  ren_var_left_inverse := fun _ _ => eq_refl;
  ren_var_right_inverse := fun _ _ => eq_refl;
  ren_const_left_inverse := fun _ _ => eq_refl;
  ren_const_right_inverse := fun _ _ => eq_refl;
  ren_atom_left_inverse := fun _ _ => eq_refl;
  ren_atom_right_inverse := fun _ _ => eq_refl
|}.

Definition inverse_renaming (rho : allowed_renaming) : allowed_renaming := {|
  ren_var := ren_var_inv rho;
  ren_const := ren_const_inv rho;
  ren_atom := ren_atom_inv rho;
  ren_var_inv := ren_var rho;
  ren_const_inv := ren_const rho;
  ren_atom_inv := ren_atom rho;
  ren_var_bijective :=
    fun n =>
      conj
        (fun x y H =>
          eq_trans
            (eq_sym (ren_var_right_inverse rho n x))
            (eq_trans (f_equal (ren_var rho n) H)
              (ren_var_right_inverse rho n y)))
        (fun y => ex_intro _ (ren_var rho n y)
          (ren_var_left_inverse rho n y));
  ren_const_bijective :=
    fun n =>
      conj
        (fun x y H =>
          eq_trans
            (eq_sym (ren_const_right_inverse rho n x))
            (eq_trans (f_equal (ren_const rho n) H)
              (ren_const_right_inverse rho n y)))
        (fun y => ex_intro _ (ren_const rho n y)
          (ren_const_left_inverse rho n y));
  ren_atom_bijective :=
    fun n =>
      conj
        (fun x y H =>
          eq_trans
            (eq_sym (ren_atom_right_inverse rho n x))
            (eq_trans (f_equal (ren_atom rho n) H)
              (ren_atom_right_inverse rho n y)))
        (fun y => ex_intro _ (ren_atom rho n y)
          (ren_atom_left_inverse rho n y));
  ren_var_left_inverse := ren_var_right_inverse rho;
  ren_var_right_inverse := ren_var_left_inverse rho;
  ren_const_left_inverse := ren_const_right_inverse rho;
  ren_const_right_inverse := ren_const_left_inverse rho;
  ren_atom_left_inverse := ren_atom_right_inverse rho;
  ren_atom_right_inverse := ren_atom_left_inverse rho
|}.

Definition compose_renaming
    (rho sigma : allowed_renaming) : allowed_renaming := {|
  ren_var := fun n i => ren_var rho n (ren_var sigma n i);
  ren_const := fun n i => ren_const rho n (ren_const sigma n i);
  ren_atom := fun n i => ren_atom rho n (ren_atom sigma n i);
  ren_var_inv := fun n i => ren_var_inv sigma n (ren_var_inv rho n i);
  ren_const_inv := fun n i => ren_const_inv sigma n (ren_const_inv rho n i);
  ren_atom_inv := fun n i => ren_atom_inv sigma n (ren_atom_inv rho n i);
  ren_var_bijective :=
    fun n =>
      conj
        (fun x y H =>
          let Hinj_rho := proj1 (ren_var_bijective rho n) in
          let Hinj_sigma := proj1 (ren_var_bijective sigma n) in
          Hinj_sigma x y (Hinj_rho _ _ H))
        (fun y =>
          match proj2 (ren_var_bijective rho n) y with
          | ex_intro _ z Hz =>
              match proj2 (ren_var_bijective sigma n) z with
              | ex_intro _ x Hx =>
                  ex_intro _ x (eq_trans (f_equal (ren_var rho n) Hx) Hz)
              end
          end);
  ren_const_bijective :=
    fun n =>
      conj
        (fun x y H =>
          let Hinj_rho := proj1 (ren_const_bijective rho n) in
          let Hinj_sigma := proj1 (ren_const_bijective sigma n) in
          Hinj_sigma x y (Hinj_rho _ _ H))
        (fun y =>
          match proj2 (ren_const_bijective rho n) y with
          | ex_intro _ z Hz =>
              match proj2 (ren_const_bijective sigma n) z with
              | ex_intro _ x Hx =>
                  ex_intro _ x (eq_trans (f_equal (ren_const rho n) Hx) Hz)
              end
          end);
  ren_atom_bijective :=
    fun n =>
      conj
        (fun x y H =>
          let Hinj_rho := proj1 (ren_atom_bijective rho n) in
          let Hinj_sigma := proj1 (ren_atom_bijective sigma n) in
          Hinj_sigma x y (Hinj_rho _ _ H))
        (fun y =>
          match proj2 (ren_atom_bijective rho n) y with
          | ex_intro _ z Hz =>
              match proj2 (ren_atom_bijective sigma n) z with
              | ex_intro _ x Hx =>
                  ex_intro _ x (eq_trans (f_equal (ren_atom rho n) Hx) Hz)
              end
          end);
  ren_var_left_inverse :=
    fun n i =>
      eq_trans
        (f_equal (ren_var_inv sigma n)
          (ren_var_left_inverse rho n (ren_var sigma n i)))
        (ren_var_left_inverse sigma n i);
  ren_var_right_inverse :=
    fun n i =>
      eq_trans
        (f_equal (ren_var rho n)
          (ren_var_right_inverse sigma n (ren_var_inv rho n i)))
        (ren_var_right_inverse rho n i);
  ren_const_left_inverse :=
    fun n i =>
      eq_trans
        (f_equal (ren_const_inv sigma n)
          (ren_const_left_inverse rho n (ren_const sigma n i)))
        (ren_const_left_inverse sigma n i);
  ren_const_right_inverse :=
    fun n i =>
      eq_trans
        (f_equal (ren_const rho n)
          (ren_const_right_inverse sigma n (ren_const_inv rho n i)))
        (ren_const_right_inverse rho n i);
  ren_atom_left_inverse :=
    fun n i =>
      eq_trans
        (f_equal (ren_atom_inv sigma n)
          (ren_atom_left_inverse rho n (ren_atom sigma n i)))
        (ren_atom_left_inverse sigma n i);
  ren_atom_right_inverse :=
    fun n i =>
      eq_trans
        (f_equal (ren_atom rho n)
          (ren_atom_right_inverse sigma n (ren_atom_inv rho n i)))
        (ren_atom_right_inverse rho n i)
|}.

Fixpoint rename_formula (rho : allowed_renaming) (phi : formula) : formula :=
  match phi with
  | FAtom n i => FAtom n (ren_atom rho n i)
  | FBot n => FBot n
  | FNeg a => FNeg (rename_formula rho a)
  | FAnd a b => FAnd (rename_formula rho a) (rename_formula rho b)
  | FOr a b => FOr (rename_formula rho a) (rename_formula rho b)
  | FImp a b => FImp (rename_formula rho a) (rename_formula rho b)
  | FAct s a => FAct (rename_term rho s) (rename_formula rho a)
  end
with rename_term (rho : allowed_renaming) (s : term) : term :=
  match s with
  | TVar n i => TVar n (ren_var rho n i)
  | TConst n i => TConst n (ren_const rho n i)
  | TBullet a b => TBullet (rename_term rho a) (rename_term rho b)
  | TComp a b => TComp (rename_term rho a) (rename_term rho b)
  | TIndex a Lambda => TIndex (rename_term rho a) (map (rename_formula rho) Lambda)
  end.

Definition rename_judgment (rho : allowed_renaming) (J : judgment) : judgment :=
  match J with
  | JFormula phi b => JFormula (rename_formula rho phi) b
  | JTermFormula s phi b =>
      JTermFormula (rename_term rho s) (rename_formula rho phi) b
  | JTermTerm s u v =>
      JTermTerm (rename_term rho s) (rename_term rho u) (rename_term rho v)
  end.

Fixpoint rename_formula_identity (phi : formula) :
    rename_formula identity_renaming phi = phi
with rename_term_identity (s : term) :
    rename_term identity_renaming s = s.
Proof.
  - destruct phi; simpl.
    + reflexivity.
    + reflexivity.
    + rewrite rename_formula_identity. reflexivity.
    + rewrite rename_formula_identity.
      rewrite rename_formula_identity. reflexivity.
    + rewrite rename_formula_identity.
      rewrite rename_formula_identity. reflexivity.
    + rewrite rename_formula_identity.
      rewrite rename_formula_identity. reflexivity.
    + rewrite rename_term_identity.
      rewrite rename_formula_identity. reflexivity.
  - destruct s; simpl.
    + reflexivity.
    + reflexivity.
    + rewrite rename_term_identity.
      rewrite rename_term_identity. reflexivity.
    + rewrite rename_term_identity.
      rewrite rename_term_identity. reflexivity.
    + rewrite rename_term_identity.
      f_equal.
      induction l as [|phi rest IH]; simpl.
      * reflexivity.
      * rewrite rename_formula_identity. rewrite IH. reflexivity.
Qed.

Lemma rename_judgment_identity :
  forall J, rename_judgment identity_renaming J = J.
Proof.
  intros J. destruct J as [phi b|s phi b|s u v]; simpl;
    repeat rewrite rename_formula_identity;
    repeat rewrite rename_term_identity;
    reflexivity.
Qed.

Fixpoint rename_formula_compose
    (rho sigma : allowed_renaming) (phi : formula) :
    rename_formula (compose_renaming rho sigma) phi =
    rename_formula rho (rename_formula sigma phi)
with rename_term_compose
    (rho sigma : allowed_renaming) (s : term) :
    rename_term (compose_renaming rho sigma) s =
    rename_term rho (rename_term sigma s).
Proof.
  - destruct phi; simpl.
    + reflexivity.
    + reflexivity.
    + rewrite rename_formula_compose. reflexivity.
    + rewrite rename_formula_compose.
      rewrite rename_formula_compose. reflexivity.
    + rewrite rename_formula_compose.
      rewrite rename_formula_compose. reflexivity.
    + rewrite rename_formula_compose.
      rewrite rename_formula_compose. reflexivity.
    + rewrite rename_term_compose.
      rewrite rename_formula_compose. reflexivity.
  - destruct s; simpl.
    + reflexivity.
    + reflexivity.
    + rewrite rename_term_compose.
      rewrite rename_term_compose. reflexivity.
    + rewrite rename_term_compose.
      rewrite rename_term_compose. reflexivity.
    + rewrite rename_term_compose.
      f_equal.
      induction l as [|phi rest IH]; simpl.
      * reflexivity.
      * rewrite rename_formula_compose. rewrite IH. reflexivity.
Qed.

Lemma rename_judgment_compose :
  forall rho sigma J,
    rename_judgment (compose_renaming rho sigma) J =
    rename_judgment rho (rename_judgment sigma J).
Proof.
  intros rho sigma J.
  destruct J as [phi b|s phi b|s u v]; simpl;
    repeat rewrite rename_formula_compose;
    repeat rewrite rename_term_compose;
    reflexivity.
Qed.

Fixpoint rename_formula_inverse_left
    (rho : allowed_renaming) (phi : formula) :
    rename_formula (inverse_renaming rho) (rename_formula rho phi) = phi
with rename_term_inverse_left
    (rho : allowed_renaming) (s : term) :
    rename_term (inverse_renaming rho) (rename_term rho s) = s.
Proof.
  - destruct phi; simpl.
    + rewrite ren_atom_left_inverse. reflexivity.
    + reflexivity.
    + rewrite rename_formula_inverse_left. reflexivity.
    + rewrite rename_formula_inverse_left.
      rewrite rename_formula_inverse_left. reflexivity.
    + rewrite rename_formula_inverse_left.
      rewrite rename_formula_inverse_left. reflexivity.
    + rewrite rename_formula_inverse_left.
      rewrite rename_formula_inverse_left. reflexivity.
    + rewrite rename_term_inverse_left.
      rewrite rename_formula_inverse_left. reflexivity.
  - destruct s; simpl.
    + rewrite ren_var_left_inverse. reflexivity.
    + rewrite ren_const_left_inverse. reflexivity.
    + rewrite rename_term_inverse_left.
      rewrite rename_term_inverse_left. reflexivity.
    + rewrite rename_term_inverse_left.
      rewrite rename_term_inverse_left. reflexivity.
    + rewrite rename_term_inverse_left.
      f_equal.
      induction l as [|phi rest IH]; simpl.
      * reflexivity.
      * rewrite rename_formula_inverse_left. rewrite IH. reflexivity.
Qed.

Lemma rename_judgment_inverse_left :
  forall rho J,
    rename_judgment (inverse_renaming rho) (rename_judgment rho J) = J.
Proof.
  intros rho J.
  destruct J as [phi b|s phi b|s u v]; simpl;
    repeat rewrite rename_formula_inverse_left;
    repeat rewrite rename_term_inverse_left;
    reflexivity.
Qed.

Definition rename_path (rho : allowed_renaming) (p : path) : path := {|
  path_terms := map (rename_term rho) (path_terms p);
  path_formula := rename_formula rho (path_formula p)
|}.

Lemma rename_path_compose :
  forall rho sigma p,
    rename_path (compose_renaming rho sigma) p =
    rename_path rho (rename_path sigma p).
Proof.
  intros rho sigma p.
  destruct p as [terms phi].
  unfold rename_path; simpl.
  f_equal.
  - induction terms as [|s rest IH]; simpl.
    + reflexivity.
    + rewrite rename_term_compose. rewrite IH. reflexivity.
  - apply rename_formula_compose.
Qed.

Lemma rename_path_inverse_left :
  forall rho p,
    rename_path (inverse_renaming rho) (rename_path rho p) = p.
Proof.
  intros rho p.
  destruct p as [terms phi].
  unfold rename_path; simpl.
  f_equal.
  - induction terms as [|s rest IH]; simpl.
    + reflexivity.
    + rewrite rename_term_inverse_left. rewrite IH. reflexivity.
  - apply rename_formula_inverse_left.
Qed.

Theorem rename_term_preserves_rank :
  forall rho s, trank (rename_term rho s) = trank s.
Proof.
  intros rho s.
  induction s; simpl; auto.
Qed.

Theorem rename_formula_preserves_rank :
  forall rho phi, frank (rename_formula rho phi) = frank phi.
Proof.
  intros rho phi.
  induction phi; simpl; auto;
    try
      (repeat match goal with
       | Hrank : frank (rename_formula rho ?a) = frank ?a
           |- context[frank (rename_formula rho ?a)] => rewrite Hrank
       end; reflexivity).
  - apply rename_term_preserves_rank.
Qed.

Lemma rename_formula_injective :
  forall rho phi psi,
    rename_formula rho phi = rename_formula rho psi ->
    phi = psi.
Proof.
  intros rho phi psi H.
  pose proof
    (f_equal (rename_formula (inverse_renaming rho)) H) as Hinv.
  repeat rewrite rename_formula_inverse_left in Hinv.
  exact Hinv.
Qed.

Fixpoint rename_formula_inverse_right
    (rho : allowed_renaming) (phi : formula) :
    rename_formula rho (rename_formula (inverse_renaming rho) phi) = phi
with rename_term_inverse_right
    (rho : allowed_renaming) (s : term) :
    rename_term rho (rename_term (inverse_renaming rho) s) = s.
Proof.
  - destruct phi; simpl.
    + rewrite ren_atom_right_inverse. reflexivity.
    + reflexivity.
    + rewrite rename_formula_inverse_right. reflexivity.
    + rewrite rename_formula_inverse_right.
      rewrite rename_formula_inverse_right. reflexivity.
    + rewrite rename_formula_inverse_right.
      rewrite rename_formula_inverse_right. reflexivity.
    + rewrite rename_formula_inverse_right.
      rewrite rename_formula_inverse_right. reflexivity.
    + rewrite rename_term_inverse_right.
      rewrite rename_formula_inverse_right. reflexivity.
  - destruct s; simpl.
    + rewrite ren_var_right_inverse. reflexivity.
    + rewrite ren_const_right_inverse. reflexivity.
    + rewrite rename_term_inverse_right.
      rewrite rename_term_inverse_right. reflexivity.
    + rewrite rename_term_inverse_right.
      rewrite rename_term_inverse_right. reflexivity.
    + rewrite rename_term_inverse_right.
      f_equal.
      induction l as [|phi rest IH]; simpl.
      * reflexivity.
      * rewrite rename_formula_inverse_right. rewrite IH. reflexivity.
Qed.

Lemma rename_judgment_inverse_right :
  forall rho J,
    rename_judgment rho (rename_judgment (inverse_renaming rho) J) = J.
Proof.
  intros rho J.
  destruct J as [phi b|s phi b|s u v]; simpl;
    repeat rewrite rename_formula_inverse_right;
    repeat rewrite rename_term_inverse_right;
    reflexivity.
Qed.

Lemma rename_path_inverse_right :
  forall rho p,
    rename_path rho (rename_path (inverse_renaming rho) p) = p.
Proof.
  intros rho p.
  destruct p as [terms phi].
  unfold rename_path; simpl.
  f_equal.
  - induction terms as [|s rest IH]; simpl.
    + reflexivity.
    + rewrite rename_term_inverse_right. rewrite IH. reflexivity.
  - apply rename_formula_inverse_right.
Qed.

Fixpoint rename_formula_preserves_wf
    (rho : allowed_renaming) (phi : formula) (n : nat)
    (H : wf_formula n phi) {struct H}
    : wf_formula n (rename_formula rho phi)
with rename_term_preserves_wf
    (rho : allowed_renaming) (s : term) (n : nat)
    (H : wf_term n s) {struct H}
    : wf_term n (rename_term rho s).
Proof.
  - destruct H as
      [n i
      |n
      |n phi Hphi
      |m n phi psi Hphi Hpsi
      |m n phi psi Hphi Hpsi
      |m n phi psi Hphi Hpsi
      |n m s phi Hs Hphi Hlt]; simpl.
    + constructor.
    + constructor.
    + constructor.
      exact (rename_formula_preserves_wf rho phi n Hphi).
    + apply WFAnd.
      * exact (rename_formula_preserves_wf rho phi m Hphi).
      * exact (rename_formula_preserves_wf rho psi n Hpsi).
    + apply WFOr.
      * exact (rename_formula_preserves_wf rho phi m Hphi).
      * exact (rename_formula_preserves_wf rho psi n Hpsi).
    + apply WFImp.
      * exact (rename_formula_preserves_wf rho phi m Hphi).
      * exact (rename_formula_preserves_wf rho psi n Hpsi).
    + apply WFAct with (m := m).
      * exact (rename_term_preserves_wf rho s n Hs).
      * exact (rename_formula_preserves_wf rho phi m Hphi).
      * exact Hlt.
  - destruct H as
      [n i
      |n i
      |n m s t Hs Ht Hlt
      |n m s t Hs Ht Hlt
      |n s Lambda Hs HLambda]; simpl.
    + constructor.
    + constructor.
    + apply WFTBullet with (m := m).
      * exact (rename_term_preserves_wf rho s n Hs).
      * exact (rename_term_preserves_wf rho t m Ht).
      * exact Hlt.
    + apply WFTComp with (m := m).
      * exact (rename_term_preserves_wf rho s n Hs).
      * exact (rename_term_preserves_wf rho t m Ht).
      * exact Hlt.
    + apply WFTIndex.
      * exact (rename_term_preserves_wf rho s n Hs).
      * induction HLambda as [|phi rest [Hphi Hlt] Hrest IHrest]; simpl.
        -- constructor.
        -- constructor.
           ++ split.
              ** change
                   (wf_formula
                     (frank (rename_formula rho phi))
                     (rename_formula rho phi)).
                 rewrite rename_formula_preserves_rank.
                 exact (rename_formula_preserves_wf rho phi (frank phi) Hphi).
              ** rewrite rename_formula_preserves_rank.
                 exact Hlt.
           ++ exact IHrest.
Defined.

Lemma rename_formula_reflects_wf :
  forall rho phi n,
    wf_formula n (rename_formula rho phi) ->
    wf_formula n phi.
Proof.
  intros rho phi n Hwf.
  pose proof
    (rename_formula_preserves_wf
      (inverse_renaming rho) (rename_formula rho phi) n Hwf)
    as Hback.
  rewrite rename_formula_inverse_left in Hback.
  exact Hback.
Qed.

Lemma rename_term_reflects_wf :
  forall rho s n,
    wf_term n (rename_term rho s) ->
    wf_term n s.
Proof.
  intros rho s n Hwf.
  pose proof
    (rename_term_preserves_wf
      (inverse_renaming rho) (rename_term rho s) n Hwf)
    as Hback.
  rewrite rename_term_inverse_left in Hback.
  exact Hback.
Qed.

Lemma rename_path_prepend :
  forall rho s p,
    rename_path rho (prepend_path s p) =
    prepend_path (rename_term rho s) (rename_path rho p).
Proof.
  intros rho s p.
  destruct p as [terms phi].
  reflexivity.
Qed.

Lemma rename_path_empty :
  forall rho phi,
    rename_path rho (empty_path phi) =
    empty_path (rename_formula rho phi).
Proof.
  reflexivity.
Qed.

Lemma rename_path_act_empty :
  forall rho s phi,
    rename_path rho (empty_path (FAct s phi)) =
    empty_path (FAct (rename_term rho s) (rename_formula rho phi)).
Proof.
  reflexivity.
Qed.

Lemma rename_path_bullet_cons :
  forall rho s u rest phi,
    rename_path rho
      {| path_terms := TBullet s u :: rest; path_formula := phi |} =
    {| path_terms :=
         TBullet (rename_term rho s) (rename_term rho u) ::
         map (rename_term rho) rest;
       path_formula := rename_formula rho phi |}.
Proof.
  reflexivity.
Qed.

Lemma rename_path_preserves_wf :
  forall rho n p,
    path_wf n p ->
    path_wf n (rename_path rho p).
Proof.
  intros rho n p [Hterms [Hphi Hlt]].
  destruct p as [terms phi].
  unfold rename_path, path_wf in *; simpl in *.
  split.
  - induction Hterms as [|s rest [Hs Hslt] Hrest IHrest]; simpl.
    + constructor.
    + constructor.
      * split.
        -- rewrite rename_term_preserves_rank.
           apply rename_term_preserves_wf.
           exact Hs.
        -- rewrite rename_term_preserves_rank.
           exact Hslt.
      * exact IHrest.
  - split.
    + rewrite rename_formula_preserves_rank.
      apply rename_formula_preserves_wf.
      exact Hphi.
    + rewrite rename_formula_preserves_rank.
      exact Hlt.
Qed.

Lemma rename_path_reflects_wf :
  forall rho n p,
    path_wf n (rename_path rho p) ->
    path_wf n p.
Proof.
  intros rho n p Hwf.
  pose proof
    (rename_path_preserves_wf
      (inverse_renaming rho) n (rename_path rho p) Hwf)
    as Hback.
  rewrite rename_path_inverse_left in Hback.
  exact Hback.
Qed.

Definition pullback_model
    (rho : allowed_renaming) (M : model) : model := {|
  atom_value := fun n i => atom_value M n (ren_atom rho n i);
  const_value :=
    fun n i p => const_value M n (ren_const rho n i) (rename_path rho p);
  const_value_level :=
    fun n i p Hp =>
      rename_path_reflects_wf rho n p
        (const_value_level M n (ren_const rho n i)
          (rename_path rho p) Hp)
|}.

Definition pullback_valuation
    (rho : allowed_renaming) (nu : valuation) : valuation := {|
  var_value :=
    fun n i p => var_value nu n (ren_var rho n i) (rename_path rho p);
  var_value_level :=
    fun n i p Hp =>
      rename_path_reflects_wf rho n p
        (var_value_level nu n (ren_var rho n i)
          (rename_path rho p) Hp)
|}.

Lemma term_denote_pullback :
  forall rho M nu s p,
    term_denote (pullback_model rho M) (pullback_valuation rho nu) s p <->
    term_denote M nu (rename_term rho s) (rename_path rho p).
Proof.
  intros rho M nu s.
  induction s as
    [n i|n i|s IHs u IHu|s IHs u IHu|s IHs Lambda];
    intros p; simpl.
  - reflexivity.
  - reflexivity.
  - destruct p as [terms phi]; simpl.
    exact (IHs {| path_terms := u :: terms; path_formula := phi |}).
  - destruct p as [[|u0 rest] phi]; simpl.
    + try rewrite rename_formula_preserves_rank.
      try rewrite rename_term_preserves_rank.
      split.
      * intros [Hlt HA].
        split.
        -- simpl. rewrite rename_formula_preserves_rank.
           rewrite rename_term_preserves_rank. exact Hlt.
        -- replace
             (empty_path
               (FAct (rename_term rho u) (rename_formula rho phi)))
             with
             (rename_path rho (empty_path (FAct u phi)))
             by reflexivity.
           apply (proj1 (IHs (empty_path (FAct u phi)))).
           exact HA.
      * intros [Hlt HA].
        split.
        -- simpl in Hlt. rewrite rename_formula_preserves_rank in Hlt.
           rewrite rename_term_preserves_rank in Hlt. exact Hlt.
        -- apply (proj2 (IHs (empty_path (FAct u phi)))).
           replace
             (rename_path rho (empty_path (FAct u phi)))
             with
             (empty_path
               (FAct (rename_term rho u) (rename_formula rho phi)))
             by reflexivity.
           exact HA.
    + try rewrite rename_term_preserves_rank.
      try rewrite rename_term_preserves_rank.
      split.
      * intros [Hlt HA].
        split.
        -- simpl. repeat rewrite rename_term_preserves_rank. exact Hlt.
        -- replace
             {| path_terms :=
                  TBullet (rename_term rho u) (rename_term rho u0) ::
                  map (rename_term rho) rest;
                path_formula := rename_formula rho phi |}
             with
             (rename_path rho
               {| path_terms := TBullet u u0 :: rest;
                  path_formula := phi |})
             by reflexivity.
           apply
             (proj1
               (IHs
                 {| path_terms := TBullet u u0 :: rest;
                    path_formula := phi |})).
           exact HA.
      * intros [Hlt HA].
        split.
        -- simpl in Hlt. repeat rewrite rename_term_preserves_rank in Hlt.
           exact Hlt.
        -- apply
             (proj2
               (IHs
                 {| path_terms := TBullet u u0 :: rest;
                    path_formula := phi |})).
           replace
             (rename_path rho
               {| path_terms := TBullet u u0 :: rest;
                  path_formula := phi |})
             with
             {| path_terms :=
                  TBullet (rename_term rho u) (rename_term rho u0) ::
                  map (rename_term rho) rest;
                path_formula := rename_formula rho phi |}
             by reflexivity.
           exact HA.
  - split.
    + intros [HA | [Hempty Hin]].
      * left. apply (proj1 (IHs p)). exact HA.
      * right.
        destruct p as [terms phi]. simpl in Hempty, Hin |- *.
        subst terms.
        split; [reflexivity|].
        apply in_map. exact Hin.
    + intros [HA | [Hempty Hin]].
      * left. apply (proj2 (IHs p)). exact HA.
      * right.
        destruct p as [terms phi]. simpl in Hempty, Hin |- *.
        destruct terms as [|head rest]; try discriminate.
        split; [reflexivity|].
        apply in_map_iff in Hin.
        destruct Hin as [psi [Hpsi Hin]].
        pose proof
          (rename_formula_injective rho phi psi (eq_sym Hpsi)) as Heq.
        subst psi.
        exact Hin.
Qed.

Lemma holds_pullback :
  forall rho M nu phi,
    holds (pullback_model rho M) (pullback_valuation rho nu) phi <->
    holds M nu (rename_formula rho phi).
Proof.
  intros rho M nu phi.
  induction phi; simpl.
  - reflexivity.
  - reflexivity.
  - split; intros Hnot Hcontra; apply Hnot; apply IHphi; exact Hcontra.
  - split.
    + intros [Ha Hb]. split; [apply IHphi1 | apply IHphi2]; assumption.
    + intros [Ha Hb]. split; [rewrite IHphi1 | rewrite IHphi2]; assumption.
  - split.
    + intros [Ha | Hb]; [left; apply IHphi1 | right; apply IHphi2]; assumption.
    + intros [Ha | Hb]; [left; rewrite IHphi1 | right; rewrite IHphi2]; assumption.
  - split.
    + intros Himp Ha.
      apply IHphi2.
      apply Himp.
      apply IHphi1.
      exact Ha.
    + intros Himp Ha.
      rewrite IHphi2.
      apply Himp.
      rewrite <- IHphi1.
      exact Ha.
  - rewrite rename_formula_preserves_rank.
    rewrite rename_term_preserves_rank.
    split.
    + intros [Hlt HA].
      split; [exact Hlt|].
      rewrite <- rename_path_empty.
      apply term_denote_pullback.
      exact HA.
    + intros [Hlt HA].
      split; [exact Hlt|].
      rewrite term_denote_pullback.
      rewrite rename_path_empty.
      exact HA.
Qed.

Lemma bool_truth_iff :
  forall P Q b,
    (P <-> Q) ->
    bool_truth P b <-> bool_truth Q b.
Proof.
  intros P Q b HPQ.
  destruct b; simpl.
  - exact HPQ.
  - split; intros Hnot Hq; apply Hnot; apply HPQ; exact Hq.
Qed.

Lemma satisfies_pullback :
  forall rho M nu J,
    satisfies (pullback_model rho M) (pullback_valuation rho nu) J <->
    satisfies M nu (rename_judgment rho J).
Proof.
  intros rho M nu J.
  destruct J as [phi b|s phi b|s u v]; simpl.
  - apply bool_truth_iff.
    apply holds_pullback.
  - change
      (bool_truth
        (holds
          (pullback_model rho M) (pullback_valuation rho nu)
          (FAct s phi)) b <->
       bool_truth
        (holds M nu (rename_formula rho (FAct s phi))) b).
    apply bool_truth_iff.
    apply holds_pullback.
  - unfold domain_equiv.
    split.
    + intros H q.
      pose (p := rename_path (inverse_renaming rho) q).
      pose proof (term_denote_pullback rho M nu (TBullet s u) p) as Hsu.
      pose proof (term_denote_pullback rho M nu v p) as Hv.
      unfold p in Hsu, Hv.
      rewrite rename_path_inverse_right in Hsu.
      rewrite rename_path_inverse_right in Hv.
      specialize (H p).
      split; intro Hq.
      * apply (proj1 Hv).
        apply (proj1 H).
        apply (proj2 Hsu).
        exact Hq.
      * apply (proj1 Hsu).
        apply (proj2 H).
        apply (proj2 Hv).
        exact Hq.
    + intros H p.
      pose proof (term_denote_pullback rho M nu (TBullet s u) p) as Hsu.
      pose proof (term_denote_pullback rho M nu v p) as Hv.
      specialize (H (rename_path rho p)).
      split; intro Hp.
      * apply (proj2 Hv).
        apply (proj1 H).
        apply (proj1 Hsu).
        exact Hp.
      * apply (proj2 Hsu).
        apply (proj2 H).
        apply (proj1 Hv).
        exact Hp.
Qed.

Definition renamed_theory (rho : allowed_renaming) (Gamma : theory)
    : theory :=
  fun J => exists G, Gamma G /\ J = rename_judgment rho G.

Lemma sem_entails_renamed :
  forall Gamma J rho,
    sem_entails Gamma J ->
    sem_entails (renamed_theory rho Gamma) (rename_judgment rho J).
Proof.
  unfold sem_entails, renamed_theory.
  intros Gamma J rho Hent M nu Hall.
  rewrite <- satisfies_pullback.
  apply Hent.
  intros G HG.
  rewrite satisfies_pullback.
  apply Hall.
  exists G.
  split; [exact HG|reflexivity].
Qed.

Definition renaming_expansion (Gamma : theory) (J : judgment) : Prop :=
  exists rho G, Gamma G /\ J = rename_judgment rho G.

Lemma renaming_expansion_identity :
  forall Gamma J, Gamma J -> renaming_expansion Gamma J.
Proof.
  intros Gamma J HJ.
  exists identity_renaming, J.
  split.
  - exact HJ.
  - symmetry. apply rename_judgment_identity.
Qed.

Lemma renaming_expansion_rename :
  forall Gamma rho J,
    renaming_expansion Gamma J ->
    renaming_expansion Gamma (rename_judgment rho J).
Proof.
  intros Gamma rho J [sigma [G [HG ->]]].
  exists (compose_renaming rho sigma), G.
  split; [exact HG|].
  rewrite rename_judgment_compose.
  reflexivity.
Qed.

Lemma renaming_expansion_renamed_theory :
  forall Gamma rho J,
    renaming_expansion Gamma J ->
    renaming_expansion
      (renamed_theory rho Gamma)
      (rename_judgment rho J).
Proof.
  intros Gamma rho J [sigma [G [HG ->]]].
  exists
    (compose_renaming
      (compose_renaming rho sigma)
      (inverse_renaming rho)),
    (rename_judgment rho G).
  split.
  - exists G. split; [exact HG|reflexivity].
  - rewrite rename_judgment_compose.
    rewrite rename_judgment_inverse_left.
    rewrite rename_judgment_compose.
    reflexivity.
Qed.

Record closure_certificate (Gamma : theory) (J : judgment) : Type := {
  closure_premises : list judgment;
  closure_premises_ok :
    forall G, In G closure_premises -> renaming_expansion Gamma G;
  closure_entails :
    sem_entails (fun G => In G closure_premises) J
}.

Definition derives (Gamma : theory) (J : judgment) : Prop :=
  inhabited (closure_certificate Gamma J).

Definition empty_theory : theory := fun _ => False.

Definition list_theory (Gamma0 : list judgment) : theory :=
  fun J => In J Gamma0.

Lemma finite_sources_for_expansion :
  forall Gamma Ps,
    (forall G, In G Ps -> renaming_expansion Gamma G) ->
    exists Gamma0 : list judgment,
      (forall G, In G Gamma0 -> Gamma G) /\
      (forall G, In G Ps -> renaming_expansion (list_theory Gamma0) G).
Proof.
  intros Gamma Ps.
  induction Ps as [|P rest IH]; intros Hok.
  - exists [].
    split.
    + intros G H. destruct H.
    + intros G H. destruct H.
  - destruct (Hok P (or_introl eq_refl))
      as [rho [K [HK HP]]].
    destruct (IH (fun G HG => Hok G (or_intror HG)))
      as [Gamma_tail [Htail_sub Htail_ok]].
    exists (K :: Gamma_tail).
    split.
    + intros G HG.
      destruct HG as [HG | HG].
      * subst G. exact HK.
      * apply Htail_sub. exact HG.
    + intros G HG.
      destruct HG as [HG | HG].
      * subst G.
        exists rho, K.
        split; [left; reflexivity|exact HP].
      * destruct (Htail_ok G HG) as [sigma [K0 [HK0 HG0]]].
        exists sigma, K0.
        split; [right; exact HK0|exact HG0].
Qed.

Theorem derives_finitary :
  forall Gamma J,
    derives Gamma J ->
    exists Gamma0 : list judgment,
      (forall G, In G Gamma0 -> Gamma G) /\
      derives (list_theory Gamma0) J.
Proof.
  intros Gamma J [Xi].
  destruct
    (finite_sources_for_expansion
      Gamma
      (closure_premises Gamma J Xi)
      (closure_premises_ok Gamma J Xi))
    as [Gamma0 [Hsub Hprem]].
  exists Gamma0.
  split; [exact Hsub|].
  constructor.
  refine {|
    closure_premises := closure_premises Gamma J Xi;
    closure_premises_ok := Hprem;
    closure_entails := closure_entails Gamma J Xi
  |}.
Qed.

Theorem derives_extensive :
  forall Gamma J, Gamma J -> derives Gamma J.
Proof.
  intros Gamma J HJ.
  constructor.
  refine {|
    closure_premises := [J];
    closure_premises_ok :=
      fun G HG =>
        match HG with
        | or_introl E =>
            eq_rect J
              (fun H =>
                exists rho K, Gamma K /\ H = rename_judgment rho K)
              (ex_intro _
                identity_renaming
                (ex_intro _ J
                  (conj HJ (eq_sym (rename_judgment_identity J)))))
              G E
        | or_intror Hnil => False_rect _ Hnil
        end;
    closure_entails :=
      fun M nu Hall => Hall J (or_introl eq_refl)
|}.
Qed.

Theorem derives_renaming_expansion :
  forall Gamma J, renaming_expansion Gamma J -> derives Gamma J.
Proof.
  intros Gamma J HJ.
  constructor.
  refine {|
    closure_premises := [J];
    closure_premises_ok :=
      fun G HG =>
        match HG with
        | or_introl E =>
            eq_rect J
              (fun H => renaming_expansion Gamma H)
              HJ
              G E
        | or_intror Hnil => False_rect _ Hnil
        end;
    closure_entails :=
      fun M nu Hall => Hall J (or_introl eq_refl)
  |}.
Qed.

Theorem derives_renamed_premise :
  forall Gamma rho J,
    Gamma J ->
    derives Gamma (rename_judgment rho J).
Proof.
  intros Gamma rho J HJ.
  apply derives_renaming_expansion.
  exists rho, J.
  split; [exact HJ|reflexivity].
Qed.

Theorem derives_renaming_closed :
  forall Gamma rho J,
    derives Gamma J ->
    derives Gamma (rename_judgment rho J).
Proof.
  intros Gamma rho J [Xi].
  constructor.
  refine {|
    closure_premises :=
      map (rename_judgment rho) (closure_premises Gamma J Xi);
    closure_premises_ok :=
      fun G HG =>
        match proj1 (in_map_iff _ _ _) HG with
        | ex_intro _ K (conj HK_eq HK_in) =>
            eq_rect
              (rename_judgment rho K)
              (fun H => renaming_expansion Gamma H)
              (renaming_expansion_rename Gamma rho K
                (closure_premises_ok Gamma J Xi K HK_in))
              G HK_eq
        end;
    closure_entails :=
      fun M nu Hall =>
        sem_entails_renamed
          (fun G => In G (closure_premises Gamma J Xi))
          J rho
          (closure_entails Gamma J Xi)
          M nu
          (fun G HG =>
            match HG with
            | ex_intro _ K (conj HK_in HG_eq) =>
                eq_rect
                  (rename_judgment rho K)
                  (fun H => satisfies M nu H)
                  (Hall (rename_judgment rho K)
                    (in_map (rename_judgment rho)
                      (closure_premises Gamma J Xi) K HK_in))
                  G
                  (eq_sym HG_eq)
            end)
  |}.
Qed.

Theorem derives_renaming_covariant :
  forall Gamma rho J,
    derives Gamma J ->
    derives (renamed_theory rho Gamma) (rename_judgment rho J).
Proof.
  intros Gamma rho J [Xi].
  constructor.
  refine {|
    closure_premises :=
      map (rename_judgment rho) (closure_premises Gamma J Xi);
    closure_premises_ok :=
      fun G HG =>
        match proj1 (in_map_iff _ _ _) HG with
        | ex_intro _ K (conj HK_eq HK_in) =>
            eq_rect
              (rename_judgment rho K)
              (fun H =>
                renaming_expansion (renamed_theory rho Gamma) H)
              (renaming_expansion_renamed_theory Gamma rho K
                (closure_premises_ok Gamma J Xi K HK_in))
              G HK_eq
        end;
    closure_entails :=
      fun M nu Hall =>
        sem_entails_renamed
          (fun G => In G (closure_premises Gamma J Xi))
          J rho
          (closure_entails Gamma J Xi)
          M nu
          (fun G HG =>
            match HG with
            | ex_intro _ K (conj HK_in HG_eq) =>
                eq_rect
                  (rename_judgment rho K)
                  (fun H => satisfies M nu H)
                  (Hall (rename_judgment rho K)
                    (in_map (rename_judgment rho)
                      (closure_premises Gamma J Xi) K HK_in))
                  G
                  (eq_sym HG_eq)
            end)
  |}.
Qed.

Theorem derives_monotone :
  forall Gamma Delta J,
    (forall G, Gamma G -> Delta G) ->
    derives Gamma J ->
    derives Delta J.
Proof.
  intros Gamma Delta J Hsub [Xi].
  constructor.
  refine {|
    closure_premises := closure_premises Gamma J Xi;
    closure_premises_ok :=
      fun G HG =>
        match closure_premises_ok Gamma J Xi G HG with
        | ex_intro _ rho Hrest =>
            ex_intro _
              rho
              match Hrest with
              | ex_intro _ A (conj HA HEq) =>
                  ex_intro _ A (conj (Hsub A HA) HEq)
              end
        end;
    closure_entails := closure_entails Gamma J Xi
  |}.
Qed.

Lemma finite_premises_flatten :
  forall Gamma Ks,
    (forall K, In K Ks -> derives Gamma K) ->
    exists Ps : list judgment,
      (forall G, In G Ps -> renaming_expansion Gamma G) /\
      (forall M nu,
        (forall G, In G Ps -> satisfies M nu G) ->
        forall K, In K Ks -> satisfies M nu K).
Proof.
  intros Gamma Ks.
  induction Ks as [|K rest IH]; intros Hder.
  - exists [].
    split.
    + intros G HG. contradiction.
    + intros M nu Hall K HK. contradiction.
  - destruct (Hder K (or_introl eq_refl)) as [XiK].
    destruct
      (IH (fun K0 HK0 => Hder K0 (or_intror HK0)))
      as [Ps [HPs_ok HPs_sat]].
    exists (closure_premises Gamma K XiK ++ Ps).
    split.
    + intros G HG.
      apply in_app_or in HG.
      destruct HG as [HG | HG].
      * exact (closure_premises_ok Gamma K XiK G HG).
      * exact (HPs_ok G HG).
    + intros M nu Hall K0 HK0.
      destruct HK0 as [HK0 | HK0].
      * subst K0.
        apply (closure_entails Gamma K XiK).
        intros G HG.
        apply Hall.
        apply in_or_app. left. exact HG.
      * apply HPs_sat.
        -- intros G HG.
           apply Hall.
           apply in_or_app. right. exact HG.
        -- exact HK0.
Qed.

Theorem derives_cut :
  forall Gamma Delta J,
    (forall G, Delta G -> derives Gamma G) ->
    derives Delta J ->
    derives Gamma J.
Proof.
  intros Gamma Delta J Hsub [Xi].
  destruct
    (finite_premises_flatten Gamma
      (closure_premises Delta J Xi)
      (fun K HK =>
        match closure_premises_ok Delta J Xi K HK with
        | ex_intro _ rho Hrest =>
            match Hrest with
            | ex_intro _ G (conj HG HK_eq) =>
                eq_rect
                  (rename_judgment rho G)
                  (fun H => derives Gamma H)
                  (derives_renaming_closed Gamma rho G (Hsub G HG))
                  K
                  (eq_sym HK_eq)
            end
        end))
    as [Ps [HPs_ok HPs_sat]].
  constructor.
  refine {|
    closure_premises := Ps;
    closure_premises_ok := HPs_ok;
    closure_entails :=
      fun M nu Hall =>
        closure_entails Delta J Xi M nu
          (fun K HK => HPs_sat M nu Hall K HK)
  |}.
Qed.

Theorem derives_idempotent :
  forall Gamma J,
    derives (fun K => derives Gamma K) J ->
    derives Gamma J.
Proof.
  intros Gamma J H.
  eapply derives_cut.
  - intros G HG. exact HG.
  - exact H.
Qed.

Theorem closure_idempotent :
  forall Gamma J,
    derives (fun K => derives Gamma K) J <-> derives Gamma J.
Proof.
  intros Gamma J.
  split.
  - apply derives_idempotent.
  - intros H.
    eapply derives_monotone.
    + intros G HG.
      apply derives_extensive.
      exact HG.
    + exact H.
Qed.

Definition valid (J : judgment) : Prop :=
  sem_entails empty_theory J.

Lemma valid_derives_empty :
  forall J, valid J -> derives empty_theory J.
Proof.
  intros J Hvalid.
  constructor.
  refine {|
    closure_premises := [];
    closure_premises_ok :=
      fun G HG => match HG with end;
    closure_entails := Hvalid
  |}.
Qed.

Theorem index_truth_principle :
  forall s Lambda phi,
    Forall (fun a => frank a < trank s) Lambda ->
    In phi Lambda ->
    derives empty_theory (JTermFormula (TIndex s Lambda) phi true).
Proof.
  intros s Lambda phi Hlower Hin.
  apply valid_derives_empty.
  unfold valid, sem_entails, satisfies, bool_truth.
  intros M nu _.
  simpl.
  split.
  - apply Forall_forall with (x := phi) in Hlower; assumption.
  - right.
    split; [reflexivity | exact Hin].
Qed.

Theorem index_concat_truth_principle :
  forall s Lambda Delta theta,
    Forall (fun a => frank a < trank s) Lambda ->
    Forall (fun a => frank a < trank s) Delta ->
    In theta (Lambda ++ Delta) ->
    derives empty_theory (JTermFormula (TIndex s (Lambda ++ Delta)) theta true).
Proof.
  intros s Lambda Delta theta HL HD Hin.
  apply index_truth_principle.
  - apply Forall_app.
    split; assumption.
  - exact Hin.
Qed.

Theorem term_application_principle :
  forall s u,
    derives empty_theory (JTermTerm s u (TBullet s u)).
Proof.
  intros s u.
  apply valid_derives_empty.
  unfold valid, sem_entails, satisfies, domain_equiv.
  intros M nu _ p.
  split; intro H; exact H.
Qed.

Lemma comp_formula_equiv :
  forall M nu s t phi,
    trank t < trank s ->
    frank phi < trank t ->
    holds M nu (FAct (TComp s t) phi) <->
    holds M nu (FAct s (FAct t phi)).
Proof.
  intros M nu s t phi Hts Hpt.
  simpl.
  split.
  - intros [_ [Hpt' HA]].
    split; [exact Hts | exact HA].
  - intros [_ HA].
    split.
    + exact (Nat.lt_trans _ _ _ Hpt Hts).
    + split; [exact Hpt | exact HA].
Qed.

Definition singleton_theory (J : judgment) : theory :=
  fun G => G = J.

Lemma comp_formula_forward_entails :
  forall s t phi b,
    trank t < trank s ->
    frank phi < trank t ->
    sem_entails
      (fun G => In G [JTermFormula (TComp s t) phi b])
      (JTermFormula s (FAct t phi) b).
Proof.
  unfold sem_entails, satisfies, bool_truth.
  intros s t phi b Hts Hpt M nu Hall.
  specialize
    (Hall (JTermFormula (TComp s t) phi b) (or_introl eq_refl))
    as Hprem.
  simpl in Hprem |- *.
  destruct b.
  - exact (proj1 (comp_formula_equiv M nu s t phi Hts Hpt) Hprem).
  - intro Htarget.
    apply Hprem.
    exact (proj2 (comp_formula_equiv M nu s t phi Hts Hpt) Htarget).
Qed.

Theorem comp_formula_forward :
  forall s t phi b,
    trank t < trank s ->
    frank phi < trank t ->
    derives
      (singleton_theory (JTermFormula (TComp s t) phi b))
      (JTermFormula s (FAct t phi) b).
Proof.
  intros s t phi b Hts Hpt.
  constructor.
  refine {|
    closure_premises := [JTermFormula (TComp s t) phi b];
    closure_premises_ok :=
      fun G HG =>
        match HG with
        | or_introl E =>
            eq_rect
              (JTermFormula (TComp s t) phi b)
              (fun H =>
                renaming_expansion
                  (singleton_theory (JTermFormula (TComp s t) phi b))
                  H)
              (renaming_expansion_identity
                (singleton_theory (JTermFormula (TComp s t) phi b))
                (JTermFormula (TComp s t) phi b)
                eq_refl)
              G E
        | or_intror Hnil => False_rect _ Hnil
        end;
    closure_entails := comp_formula_forward_entails s t phi b Hts Hpt
  |}.
Qed.

Lemma comp_formula_backward_entails :
  forall s t phi b,
    trank t < trank s ->
    frank phi < trank t ->
    sem_entails
      (fun G => In G [JTermFormula s (FAct t phi) b])
      (JTermFormula (TComp s t) phi b).
Proof.
  unfold sem_entails, satisfies, bool_truth.
  intros s t phi b Hts Hpt M nu Hall.
  specialize
    (Hall (JTermFormula s (FAct t phi) b) (or_introl eq_refl))
    as Hprem.
  simpl in Hprem |- *.
  destruct b.
  - exact (proj2 (comp_formula_equiv M nu s t phi Hts Hpt) Hprem).
  - intro Htarget.
    apply Hprem.
    exact (proj1 (comp_formula_equiv M nu s t phi Hts Hpt) Htarget).
Qed.

Theorem comp_formula_backward :
  forall s t phi b,
    trank t < trank s ->
    frank phi < trank t ->
    derives
      (singleton_theory (JTermFormula s (FAct t phi) b))
      (JTermFormula (TComp s t) phi b).
Proof.
  intros s t phi b Hts Hpt.
  constructor.
  refine {|
    closure_premises := [JTermFormula s (FAct t phi) b];
    closure_premises_ok :=
      fun G HG =>
        match HG with
        | or_introl E =>
            eq_rect
              (JTermFormula s (FAct t phi) b)
              (fun H =>
                renaming_expansion
                  (singleton_theory (JTermFormula s (FAct t phi) b))
                  H)
              (renaming_expansion_identity
                (singleton_theory (JTermFormula s (FAct t phi) b))
                (JTermFormula s (FAct t phi) b)
                eq_refl)
              G E
        | or_intror Hnil => False_rect _ Hnil
        end;
    closure_entails := comp_formula_backward_entails s t phi b Hts Hpt
  |}.
Qed.

Lemma comp_term_equiv :
  forall M nu s t u,
    trank t < trank s ->
    trank u < trank t ->
    domain_equiv
      (term_denote M nu (TBullet (TComp s t) u))
      (term_denote M nu (TBullet s (TBullet t u))).
Proof.
  intros M nu s t u _ Hut p.
  simpl.
  split.
  - intros [_ HA].
    exact HA.
  - intros HA.
    split; [exact Hut | exact HA].
Qed.

Theorem comp_term_principle :
  forall s t u,
    trank t < trank s ->
    trank u < trank t ->
    derives empty_theory (JTermTerm (TComp s t) u (TBullet s (TBullet t u))).
Proof.
  intros s t u Hts Hut.
  apply valid_derives_empty.
  unfold valid, sem_entails, satisfies.
  intros M nu _.
  exact (comp_term_equiv M nu s t u Hts Hut).
Qed.

Definition star_atom_value (n i : nat) : Prop :=
  n = 0 /\ i = 0.

Definition star_const_value (n i : nat) : domain n :=
  fun p =>
    n = 1 /\
    i = 0 /\
    p = empty_path (FBot 0).

Lemma star_const_value_level :
  forall n i, domain_respects_level n (star_const_value n i).
Proof.
  unfold domain_respects_level, star_const_value, path_wf.
  intros n i p [Hn [_ Hp]].
  subst p.
  subst n.
  simpl.
  split.
  - constructor.
  - split.
    + constructor.
    + apply Nat.lt_0_1.
Qed.

Definition star_model : model := {|
  atom_value := star_atom_value;
  const_value := star_const_value;
  const_value_level := star_const_value_level
|}.

Definition empty_var_value (n i : nat) : domain n :=
  fun _ => False.

Lemma empty_var_value_level :
  forall n i, domain_respects_level n (empty_var_value n i).
Proof.
  unfold domain_respects_level, empty_var_value.
  intros n i p H.
  contradiction.
Qed.

Definition empty_valuation : valuation := {|
  var_value := empty_var_value;
  var_value_level := empty_var_value_level
|}.

Theorem star_model_nontrivial_atom :
  holds star_model empty_valuation (FAtom 0 0).
Proof.
  simpl.
  split; reflexivity.
Qed.

Theorem star_model_registers_bot_without_reflection :
  holds star_model empty_valuation (FAct (TConst 1 0) (FBot 0)) /\
  ~ holds star_model empty_valuation (FBot 0).
Proof.
  split.
  - simpl.
    split.
    + apply Nat.lt_0_1.
    + repeat split; reflexivity.
  - simpl.
    exact (fun H => H).
Qed.

Lemma renaming_expansion_empty_false :
  forall J, ~ renaming_expansion empty_theory J.
Proof.
  unfold renaming_expansion, empty_theory.
  intros J H.
  destruct H as [rho [G [HG _]]]. contradiction.
Qed.

Theorem empty_formula_consistency :
  forall phi,
    ~ (derives empty_theory (JFormula phi true) /\
       derives empty_theory (JFormula phi false)).
Proof.
  intros phi [[Xi_true] [Xi_false]].
  assert
    (Htrue_assumptions :
      forall G,
        In G (closure_premises empty_theory (JFormula phi true) Xi_true) ->
        satisfies star_model empty_valuation G).
  {
    intros G HG.
    exfalso.
    exact
      (renaming_expansion_empty_false G
        (closure_premises_ok empty_theory (JFormula phi true) Xi_true G HG)).
  }
  assert
    (Hfalse_assumptions :
      forall G,
        In G (closure_premises empty_theory (JFormula phi false) Xi_false) ->
        satisfies star_model empty_valuation G).
  {
    intros G HG.
    exfalso.
    exact
      (renaming_expansion_empty_false G
        (closure_premises_ok empty_theory (JFormula phi false) Xi_false G HG)).
  }
  pose proof
    (closure_entails empty_theory (JFormula phi true) Xi_true
      star_model empty_valuation Htrue_assumptions) as Htrue.
  pose proof
    (closure_entails empty_theory (JFormula phi false) Xi_false
      star_model empty_valuation Hfalse_assumptions) as Hfalse.
  simpl in Htrue, Hfalse.
  exact (Hfalse Htrue).
Qed.

Lemma star_model_class_nontrivial :
  forall M, M = star_model ->
    holds M empty_valuation (FAtom 0 0) /\
    ~ holds M empty_valuation (FBot 0).
Proof.
  intros M HM. subst M.
  exact (conj star_model_nontrivial_atom
    (proj2 star_model_registers_bot_without_reflection)).
Qed.

Record SIC_system : Type := {
  sic_terms : nat -> term -> Prop;
  sic_formulas : nat -> formula -> Prop;
  sic_terms_are_wf :
    forall n s, sic_terms n s -> wf_term n s;
  sic_formulas_are_wf :
    forall n phi, sic_formulas n phi -> wf_formula n phi;
  sic_models : model -> Prop;
  sic_model_witness : sic_models star_model;
  sic_model_nontrivial :
    forall M, sic_models M ->
      holds M empty_valuation (FAtom 0 0) /\
      ~ holds M empty_valuation (FBot 0);
  sic_derives : theory -> judgment -> Prop;
  sic_derives_is_closure :
    forall Gamma J, sic_derives Gamma J -> derives Gamma J;
  sic_index_truth :
    forall s Lambda phi,
      Forall (fun a => frank a < trank s) Lambda ->
      In phi Lambda ->
      sic_derives empty_theory (JTermFormula (TIndex s Lambda) phi true);
  sic_consistency :
    forall phi,
      ~ (sic_derives empty_theory (JFormula phi true) /\
         sic_derives empty_theory (JFormula phi false))
}.

Definition SIC : SIC_system := {|
  sic_terms := wf_term;
  sic_formulas := wf_formula;
  sic_terms_are_wf := fun n s H => H;
  sic_formulas_are_wf := fun n phi H => H;
  sic_models := fun M => M = star_model;
  sic_model_witness := eq_refl;
  sic_model_nontrivial := star_model_class_nontrivial;
  sic_derives := derives;
  sic_derives_is_closure := fun Gamma J H => H;
  sic_index_truth := index_truth_principle;
  sic_consistency := empty_formula_consistency
|}.

End StratifiedIntensionalClosure1079.
