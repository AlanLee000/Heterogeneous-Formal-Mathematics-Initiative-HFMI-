(** Self-contained merge of the five checked OEBRC2173 source files.
    Generated mechanically; no theorem or proof body is omitted. *)

(** ===== BEGIN MERGED SOURCE: OEBRC2173.v ===== *)
From Stdlib Require Import List Bool Arith Lia PeanoNat Wf_nat Relations
  Relation_Definitions Logic.ConstructiveEpsilon.
Import ListNotations.
Set Implicit Arguments.

(** A faithful type-theoretic presentation of OEBRC-v2.1 (source note 2173).
    Raw syntax and well-formedness are deliberately separate: in particular an
    ownership-open quantifier is not silently interpreted as a false formula. *)
Module OEBRC2173Core.

Section GenericKernel.

Context {M O N : Type}.
Variable M_eq_dec : forall x y : M, {x = y} + {x <> y}.
Variable O_eq_dec : forall x y : O, {x = y} + {x <> y}.
Variable N_eq_dec : forall x y : N, {x = y} + {x <> y}.
Variable enumM : list M.
Variable enumO : list O.
Variable enumN : list N.
Hypothesis enumM_complete : forall x : M, In x enumM.
Hypothesis enumO_complete : forall x : O, In x enumO.
Hypothesis enumN_complete : forall x : N, In x enumN.

(** Section 1.2: finite permutations. *)
Record perm : Type := mkPerm {
  pmap : O -> O;
  pinv : O -> O;
  pmap_pinv : forall x, pmap (pinv x) = x;
  pinv_pmap : forall x, pinv (pmap x) = x
}.

Definition perm_eq (p q : perm) : Prop :=
  forall x, pmap p x = pmap q x.

Definition perm_id : perm.
Proof.
  refine (mkPerm (fun x => x) (fun x => x) _ _); intro x; reflexivity.
Defined.

Definition perm_comp (p q : perm) : perm.
Proof.
  refine (mkPerm
    (fun x => pmap p (pmap q x))
    (fun x => pinv q (pinv p x)) _ _).
  - intro x. rewrite pmap_pinv, pmap_pinv. reflexivity.
  - intro x. rewrite pinv_pmap, pinv_pmap. reflexivity.
Defined.

Definition perm_inverse (p : perm) : perm.
Proof.
  refine (mkPerm (pinv p) (pmap p) _ _).
  - exact (pinv_pmap p).
  - exact (pmap_pinv p).
Defined.

Lemma perm_eq_refl : forall p, perm_eq p p.
Proof. intros p x. reflexivity. Qed.

Lemma perm_eq_sym : forall p q, perm_eq p q -> perm_eq q p.
Proof. intros p q H x. symmetry. apply H. Qed.

Lemma perm_eq_trans : forall p q r,
  perm_eq p q -> perm_eq q r -> perm_eq p r.
Proof. intros p q r Hpq Hqr x. rewrite Hpq. apply Hqr. Qed.

Lemma perm_comp_assoc : forall p q r,
  perm_eq (perm_comp p (perm_comp q r))
          (perm_comp (perm_comp p q) r).
Proof. intros p q r x. reflexivity. Qed.

Lemma perm_comp_id_l : forall p, perm_eq (perm_comp perm_id p) p.
Proof. intros p x. reflexivity. Qed.

Lemma perm_comp_id_r : forall p, perm_eq (perm_comp p perm_id) p.
Proof. intros p x. reflexivity. Qed.

Lemma perm_comp_inverse_r : forall p,
  perm_eq (perm_comp p (perm_inverse p)) perm_id.
Proof. intros p x. apply pmap_pinv. Qed.

Lemma perm_comp_inverse_l : forall p,
  perm_eq (perm_comp (perm_inverse p) p) perm_id.
Proof. intros p x. apply pinv_pmap. Qed.

(** Sections 2 and 4 use rule identities at syntax nodes.  Rule data are
    recovered from the finite active environment by [lookup_rule]. *)
Inductive term : Type :=
| TVar : nat -> term
| TApp : nat -> term -> term.

Inductive bterm : Type :=
| BVar : nat -> bterm
| BApp : nat -> bterm -> bterm
| BTarget : bterm -> bterm.

Inductive provenance : Type :=
| ProvInit
| ProvReconstructed :
    nat -> nat -> nat -> list nat -> term ->
    list (M * M) -> list (O * O) -> provenance.

Record generation : Type := mkGeneration {
  g_name : N;
  g_generation : nat;
  g_tab : M -> M;
  g_own : perm;
  g_provenance : provenance;
  g_id : nat
}.

Definition env := list generation.

Fixpoint lookup_rule (E : env) (i : nat) : option generation :=
  match E with
  | [] => None
  | q :: E' => if Nat.eqb i (g_id q) then Some q else lookup_rule E' i
  end.

Fixpoint delete_rule (E : env) (i : nat) : env :=
  match E with
  | [] => []
  | q :: E' =>
      if Nat.eqb i (g_id q) then delete_rule E' i
      else q :: delete_rule E' i
  end.

Definition env_wf (E : env) : Prop :=
  NoDup (map g_id E) /\ NoDup (map g_name E).

Lemma lookup_delete_same : forall E i,
  lookup_rule (delete_rule E i) i = None.
Proof.
  induction E as [|q E IH]; intro i; cbn.
  - reflexivity.
  - destruct (Nat.eqb i (g_id q)) eqn:Hi.
    + exact (IH i).
    + cbn. rewrite Hi. exact (IH i).
Qed.

Lemma lookup_delete_other : forall E i j,
  i <> j -> lookup_rule (delete_rule E j) i = lookup_rule E i.
Proof.
  induction E as [|q E IH]; intros i j Hij; cbn.
  - reflexivity.
  - destruct (Nat.eqb j (g_id q)) eqn:Hj.
    + apply Nat.eqb_eq in Hj. subst.
      destruct (Nat.eqb i (g_id q)) eqn:Hi.
      * apply Nat.eqb_eq in Hi. contradiction.
      * apply IH. exact Hij.
    + destruct (Nat.eqb i (g_id q)) eqn:Hi.
      * cbn. rewrite Hi. reflexivity.
      * cbn. rewrite Hi. apply IH. exact Hij.
Qed.

(** Sections 2.1--2.4: terms, finite supports, semantics and ownership. *)
Inductive wf_term (E : env) (X : list nat) : term -> Prop :=
| WfVar : forall x, In x X -> wf_term E X (TVar x)
| WfApp : forall i q t,
    lookup_rule E i = Some q ->
    wf_term E X t ->
    wf_term E X (TApp i t).

Fixpoint term_height (t : term) : nat :=
  match t with TVar _ => 0 | TApp _ u => S (term_height u) end.

Fixpoint fv_term (t : term) : list nat :=
  match t with TVar x => [x] | TApp _ u => fv_term u end.

Definition bv_term (_ : term) : list nat := [].

Fixpoint opsupp_raw (t : term) : list nat :=
  match t with TVar _ => [] | TApp i u => i :: opsupp_raw u end.

Definition opsupp (t : term) : list nat := nodup Nat.eq_dec (opsupp_raw t).

Fixpoint eval_term (E : env) (v : nat -> M) (t : term) : option M :=
  match t with
  | TVar x => Some (v x)
  | TApp i u =>
      match lookup_rule E i, eval_term E v u with
      | Some q, Some a => Some (g_tab q a)
      | _, _ => None
      end
  end.

Fixpoint own_term (E : env) (t : term) : option perm :=
  match t with
  | TVar _ => Some perm_id
  | TApp i u =>
      match lookup_rule E i, own_term E u with
      | Some q, Some theta => Some (perm_comp (g_own q) theta)
      | _, _ => None
      end
  end.

Fixpoint term_subst (sigma : nat -> term) (t : term) : term :=
  match t with
  | TVar x => sigma x
  | TApp i u => TApp i (term_subst sigma u)
  end.

Definition single_subst (x : nat) (s : term) : nat -> term :=
  fun z => if Nat.eq_dec z x then s else TVar z.

Definition term_rename (eta : nat -> nat) (t : term) : term :=
  term_subst (fun x => TVar (eta x)) t.

Definition TermSubRelation
  (E : env) (X Y : list nat) (t : term)
  (sigma : nat -> term) (out : term) : Prop :=
  wf_term E X t /\
  (forall x, In x X -> wf_term E Y (sigma x)) /\
  out = term_subst sigma t.

Lemma wf_term_eval_total : forall E X t,
  wf_term E X t -> forall v, exists a, eval_term E v t = Some a.
Proof.
  intros E X t Hwf. induction Hwf as [x Hx|i q t Hlook Hwf IH].
  - intro v. exists (v x). reflexivity.
  - intro v. destruct (IH v) as [a Ha].
    exists (g_tab q a). cbn. rewrite Hlook, Ha. reflexivity.
Qed.

Lemma wf_term_own_total : forall E X t,
  wf_term E X t -> exists theta, own_term E t = Some theta.
Proof.
  intros E X t Hwf. induction Hwf as [x Hx|i q t Hlook Hwf [theta Htheta]].
  - exists perm_id. reflexivity.
  - exists (perm_comp (g_own q) theta). cbn. rewrite Hlook, Htheta. reflexivity.
Qed.

Lemma opsupp_raw_nodup_in : forall i t,
  In i (opsupp t) <-> In i (opsupp_raw t).
Proof.
  intros i t. unfold opsupp. apply nodup_In.
Qed.

(** Sections 3.1--3.5: ownership-sensitive raw formulae and their formation. *)
Inductive formula : Type :=
| FAtom : nat -> term -> formula
| FAll : O -> nat -> term -> formula.

Definition close (E : env) (o : O) (t : term) : Prop :=
  exists theta, own_term E t = Some theta /\ pmap theta o = o.

Inductive wf_formula (E : env) : formula -> Prop :=
| WfAtom : forall x t,
    wf_term E [x] t -> wf_formula E (FAtom x t)
| WfAll : forall o x t,
    wf_term E [x] t -> close E o t -> wf_formula E (FAll o x t).

Definition fv_formula (A : formula) : list nat :=
  match A with FAtom _ t => fv_term t | FAll _ _ _ => [] end.

Definition bv_formula (A : formula) : list nat :=
  match A with FAtom _ _ => [] | FAll _ x _ => [x] end.

Definition formula_subst (A : formula) (z w : nat) (s : term) : formula :=
  match A with
  | FAtom x t =>
      if Nat.eq_dec x z
      then FAtom w (term_subst (single_subst z s) t)
      else A
  | FAll _ _ _ => A
  end.

Definition free_rename_formula (A : formula) (z w : nat) : formula :=
  formula_subst A z w (TVar w).

Definition bound_rename (A : formula) (z : nat) : formula :=
  match A with
  | FAtom _ _ => A
  | FAll o x t => FAll o z (term_rename (fun a => if Nat.eq_dec a x then z else a) t)
  end.

Inductive alpha_step : formula -> formula -> Prop :=
| AlphaBound : forall o x z t,
    alpha_step (FAll o x t)
      (FAll o z (term_rename (fun a => if Nat.eq_dec a x then z else a) t)).

Definition alpha_equiv : relation formula :=
  clos_refl_sym_trans formula alpha_step.

Definition satisfies
  (E : env) (P : M -> Prop) (v : nat -> M) (A : formula) : Prop :=
  match A with
  | FAtom _ t => exists a, eval_term E v t = Some a /\ P a
  | FAll _ x t =>
      forall a, exists b,
        eval_term E (fun z => if Nat.eq_dec z x then a else v z) t = Some b /\ P b
  end.

Definition sem_entails (E : env) (Gamma : formula -> Prop) (A : formula) : Prop :=
  forall (P : M -> Prop) (v : nat -> M),
    (forall B, Gamma B -> satisfies E P v B) -> satisfies E P v A.

(** Sections 4--5: the bounded suspension boundary.  The height bound is in
    [wf_boundary]; raw boundary trees remain structurally recursive. *)
Fixpoint boundary_height (b : bterm) : nat :=
  match b with
  | BVar _ => 0
  | BApp _ c => S (boundary_height c)
  | BTarget c => S (boundary_height c)
  end.

Inductive wf_boundary (E : env) (q h : nat) (X : list nat) : bterm -> Prop :=
| WfBVar : forall x,
    In x X -> wf_boundary E q h X (BVar x)
| WfBApp : forall i r b,
    lookup_rule (delete_rule E q) i = Some r ->
    wf_boundary E q h X b ->
    S (boundary_height b) <= h ->
    wf_boundary E q h X (BApp i b)
| WfBTarget : forall b,
    wf_boundary E q h X b ->
    S (boundary_height b) <= h ->
    wf_boundary E q h X (BTarget b).

Fixpoint boundary_embed (t : term) : bterm :=
  match t with
  | TVar x => BVar x
  | TApp i u => BApp i (boundary_embed u)
  end.

Fixpoint boundary_own (E : env) (q : nat) (b : bterm) : option perm :=
  match b with
  | BVar _ => Some perm_id
  | BApp i c =>
      match lookup_rule E i, boundary_own E q c with
      | Some r, Some theta => Some (perm_comp (g_own r) theta)
      | _, _ => None
      end
  | BTarget c =>
      match lookup_rule E q, boundary_own E q c with
      | Some r, Some theta => Some (perm_comp (g_own r) theta)
      | _, _ => None
      end
  end.

Fixpoint excise (q : nat) (t : term) : bterm :=
  match t with
  | TVar x => BVar x
  | TApp i u =>
      if Nat.eqb i q then BTarget (excise q u)
      else BApp i (excise q u)
  end.

Fixpoint boundary_subst (sigma : nat -> term) (b : bterm) : bterm :=
  match b with
  | BVar x => boundary_embed (sigma x)
  | BApp i c => BApp i (boundary_subst sigma c)
  | BTarget c => BTarget (boundary_subst sigma c)
  end.

Fixpoint boundary_eval {A : Type}
  (active : nat -> A -> A) (delta : A -> A)
  (v : nat -> A) (b : bterm) : A :=
  match b with
  | BVar x => v x
  | BApp i c => active i (boundary_eval active delta v c)
  | BTarget c => delta (boundary_eval active delta v c)
  end.

Fixpoint old_boundary_eval
  (E : env) (q : nat) (v : nat -> M) (b : bterm) : option M :=
  match b with
  | BVar x => Some (v x)
  | BApp i c =>
      match lookup_rule E i, old_boundary_eval E q v c with
      | Some r, Some a => Some (g_tab r a)
      | _, _ => None
      end
  | BTarget c =>
      match lookup_rule E q, old_boundary_eval E q v c with
      | Some r, Some a => Some (g_tab r a)
      | _, _ => None
      end
  end.

Fixpoint eliminate_boundary (y : nat) (u : term) (b : bterm) : term :=
  match b with
  | BVar x => TVar x
  | BApp i c => TApp i (eliminate_boundary y u c)
  | BTarget c => term_subst (single_subst y (eliminate_boundary y u c)) u
  end.

Lemma excise_height : forall q t,
  boundary_height (excise q t) = term_height t.
Proof.
  intros q t. induction t as [x|i t IH]; cbn.
  - reflexivity.
  - destruct (Nat.eqb i q); cbn; rewrite IH; reflexivity.
Qed.

Lemma excise_ownership : forall E q t,
  boundary_own E q (excise q t) = own_term E t.
Proof.
  intros E q t. induction t as [x|i t IH]; cbn.
  - reflexivity.
  - destruct (Nat.eqb_spec i q) as [-> | Hneq].
    + cbn. rewrite IH. reflexivity.
    + cbn. rewrite IH. reflexivity.
Qed.

Lemma excise_evaluation : forall E q v t,
  old_boundary_eval E q v (excise q t) = eval_term E v t.
Proof.
  intros E q v t. induction t as [x|i t IH]; cbn.
  - reflexivity.
  - destruct (Nat.eqb_spec i q) as [-> | Hneq].
    + cbn. rewrite IH. reflexivity.
    + cbn. rewrite IH. reflexivity.
Qed.

Lemma boundary_eval_unique :
  forall (A : Type) (active : nat -> A -> A) (delta : A -> A)
         (v : nat -> A) (f : bterm -> A),
    (forall x, f (BVar x) = v x) ->
    (forall i b, f (BApp i b) = active i (f b)) ->
    (forall b, f (BTarget b) = delta (f b)) ->
    forall b, f b = boundary_eval active delta v b.
Proof.
  intros A active delta v f Hvar Happ Htarget b.
  induction b as [x|i b IH|b IH].
  - apply Hvar.
  - rewrite Happ, IH. reflexivity.
  - rewrite Htarget, IH. reflexivity.
Qed.

Lemma excise_no_target_is_embed : forall q t,
  ~ In q (opsupp_raw t) -> excise q t = boundary_embed t.
Proof.
  intros q t. induction t as [x|i t IH]; intro Hnot; cbn.
  - reflexivity.
  - apply Decidable.not_or in Hnot. destruct Hnot as [Hi Htail].
    destruct (Nat.eqb i q) eqn:Hiq.
    + apply Nat.eqb_eq in Hiq. subst. contradiction.
    + rewrite IH by exact Htail. reflexivity.
Qed.

Lemma excise_subst_natural : forall E X q t,
  wf_term E X t ->
  forall sigma,
    (forall x, In x X -> ~ In q (opsupp_raw (sigma x))) ->
    excise q (term_subst sigma t) = boundary_subst sigma (excise q t).
Proof.
  intros E X q t Hwf. induction Hwf as [x Hx|i r t Hlook Hwf IH].
  - intros sigma Hsigma. cbn.
    apply excise_no_target_is_embed. apply Hsigma. exact Hx.
  - intros sigma Hsigma. cbn.
    destruct (Nat.eqb i q); cbn; rewrite IH by exact Hsigma; reflexivity.
Qed.

Lemma subst_under_unary_template : forall E y u,
  wf_term E [y] u ->
  forall sigma s,
    term_subst sigma (term_subst (single_subst y s) u) =
    term_subst (single_subst y (term_subst sigma s)) u.
Proof.
  intros E y u Hwf.
  induction Hwf as [x Hx|i r t Hlook Hwf IH].
  - intros sigma s. cbn in Hx. destruct Hx as [Hxy | []]. subst x.
    unfold single_subst. cbn.
    destruct (Nat.eq_dec y y) as [_|H]; [reflexivity|contradiction].
  - intros sigma s. cbn. rewrite IH. reflexivity.
Qed.

Lemma eliminate_embed : forall y u t,
  eliminate_boundary y u (boundary_embed t) = t.
Proof.
  intros y u t. induction t as [x|i t IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma eliminate_subst_natural : forall E y u,
  wf_term E [y] u ->
  forall b sigma,
    term_subst sigma (eliminate_boundary y u b) =
    eliminate_boundary y u (boundary_subst sigma b).
Proof.
  intros E y u Hu b. induction b as [x|i b IH|b IH]; intro sigma; cbn.
  - rewrite eliminate_embed. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite (subst_under_unary_template Hu), IH. reflexivity.
Qed.

(** Section 6: reconstruction certificates, compilation, elimination and delta. *)
Definition compile_M (E : env) (u : term) (a : M) : option M :=
  eval_term E (fun _ => a) u.

Definition compile_O (E : env) (u : term) : option perm := own_term E u.

Record ORec (E : env) (q k : nat) (u : term) (h : nat) : Type := mkORec {
  orec_old : generation;
  orec_interpreter : generation;
  orec_old_lookup : lookup_rule E q = Some orec_old;
  orec_interpreter_lookup :
    lookup_rule (delete_rule E q) k = Some orec_interpreter;
  orec_template_wf : wf_term (delete_rule E q) [0] u;
  orec_distinct_name : g_name orec_interpreter <> g_name orec_old;
  orec_mentions_interpreter : In k (opsupp_raw u);
  orec_excludes_target : ~ In q (opsupp_raw u);
  orec_semantics : forall a,
    compile_M (delete_rule E q) u a = Some (g_tab orec_old a);
  orec_ownership : exists theta, compile_O (delete_rule E q) u = Some theta;
  orec_positive_height : 0 < h
}.

Definition delta (new old : perm) : perm :=
  perm_comp new (perm_inverse old).

Lemma delta_equation : forall new old,
  perm_eq new (perm_comp (delta new old) old).
Proof.
  intros new old x. unfold delta. cbn.
  rewrite pinv_pmap. reflexivity.
Qed.

Lemma delta_unique : forall new old D,
  perm_eq new (perm_comp D old) -> perm_eq D (delta new old).
Proof.
  intros new old D H x. unfold delta. cbn.
  pose proof (H (pinv old x)) as Hx. cbn in Hx.
  rewrite pmap_pinv in Hx. symmetry. exact Hx.
Qed.

Fixpoint list_max (xs : list nat) : nat :=
  match xs with [] => 0 | x :: tl => Nat.max x (list_max tl) end.

Lemma in_list_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs. induction xs as [|a xs IH]; intro H.
  - contradiction.
  - cbn in *. destruct H as [-> | H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H | apply Nat.le_max_r].
Qed.

Lemma missing_id_exists : forall U : list nat, exists n, ~ In n U.
Proof.
  intro U. exists (S (list_max U)). intro H.
  pose proof (in_list_max (S (list_max U)) U H) as Hle. lia.
Defined.

Definition missing_id_dec (U : list nat) (n : nat) :
  {~ In n U} + {~ ~ In n U}.
Proof.
  destruct (in_dec Nat.eq_dec n U) as [Hin | Hout].
  - right. intro H. exact (H Hin).
  - left. exact Hout.
Defined.

Definition fresh_package (U : list nat) :
  {n : nat | ~ In n U /\ forall k, ~ In k U -> n <= k} :=
  epsilon_smallest (fun n => ~ In n U) (missing_id_dec U)
    (missing_id_exists U).

Definition fresh_id (U : list nat) : nat := proj1_sig (fresh_package U).

Lemma fresh_id_fresh : forall U, ~ In (fresh_id U) U.
Proof.
  intro U. exact (proj1 (proj2_sig (fresh_package U))).
Qed.

Lemma fresh_id_minimal : forall U n,
  n < fresh_id U -> In n U.
Proof.
  intros U n Hlt.
  destruct (in_dec Nat.eq_dec n U) as [Hin | Hout].
  - exact Hin.
  - pose proof (proj2 (proj2_sig (fresh_package U)) n Hout) as Hle.
    unfold fresh_id in Hlt. lia.
Qed.

Definition graph_M (f : M -> M) : list (M * M) :=
  map (fun x => (x, f x)) enumM.

Definition graph_O (p : perm) : list (O * O) :=
  map (fun x => (x, pmap p x)) enumO.

Definition new_generation
  (E : env) (q k : nat) (u : term) (h : nat) (U : list nat)
  : option generation :=
  match lookup_rule E q, compile_O (delete_rule E q) u with
  | Some old, Some theta =>
      Some (mkGeneration
        (g_name old)
        (S (g_generation old))
        (g_tab old)
        theta
        (ProvReconstructed q k h (map g_id E) u
          (graph_M (g_tab old)) (graph_O (delta theta (g_own old))))
        (fresh_id U))
  | _, _ => None
  end.

Theorem new_generation_spec : forall E q k u h U (H : ORec E q k u h),
  exists qplus,
    new_generation E q k u h U = Some qplus /\
    g_name qplus = g_name (orec_old H) /\
    g_generation qplus = S (g_generation (orec_old H)) /\
    (forall a, g_tab qplus a = g_tab (orec_old H) a) /\
    compile_O (delete_rule E q) u = Some (g_own qplus) /\
    g_id qplus = fresh_id U.
Proof.
  intros E q k u h U H.
  destruct H as [old interp Hold Hinterp Hwf Hnames Hmention Hexclude
                  Hsem [theta Htheta] Hheight]. cbn in *.
  unfold new_generation. rewrite Hold, Htheta. eexists. repeat split; reflexivity.
Qed.

Theorem compiled_semantics_faithful : forall E q k u h (H : ORec E q k u h),
  forall a, compile_M (delete_rule E q) u a =
            Some (g_tab (orec_old H) a).
Proof. intros E q k u h H. apply orec_semantics. Qed.

End GenericKernel.

End OEBRC2173Core.

(** ===== END MERGED SOURCE: OEBRC2173.v ===== *)

(** ===== BEGIN MERGED SOURCE: OEBRC2173_Transitions.v ===== *)
From Stdlib Require Import List Bool Arith Lia PeanoNat Relations Relation_Definitions.
Import ListNotations.
Set Implicit Arguments.

Module OEBRC2173Transitions.
Import OEBRC2173Core.

(** Supplement to Sections 2--3: substitution/renaming preservation. *)
Section StructuralLaws.
Context {M O N : Type}.

Lemma wf_term_subst : forall (E : @env M O N) X Y t sigma,
  wf_term E X t ->
  (forall x, In x X -> wf_term E Y (sigma x)) ->
  wf_term E Y (term_subst sigma t).
Proof.
  intros E X Y t sigma Hwf Hsigma.
  induction Hwf as [x Hx|i q t Hlook Hwf IH]; cbn.
  - apply Hsigma. exact Hx.
  - econstructor; eauto.
Qed.

Lemma term_subst_ext_wf : forall (E : @env M O N) X t,
  wf_term E X t -> forall sigma tau,
  (forall x, In x X -> sigma x = tau x) ->
  term_subst sigma t = term_subst tau t.
Proof.
  intros E X t Hwf. induction Hwf as [x Hx|i q t Hlook Hwf IH].
  - intros sigma tau Hext. cbn. apply Hext. exact Hx.
  - intros sigma tau Hext. cbn. rewrite (IH sigma tau Hext). reflexivity.
Qed.

Lemma wf_term_single_subst : forall (E : @env M O N) x y t s,
  wf_term E [x] t -> wf_term E [y] s ->
  wf_term E [y] (term_subst (single_subst x s) t).
Proof.
  intros E x y t s Ht Hs. eapply wf_term_subst; [exact Ht|].
  intros z Hz. cbn in Hz. destruct Hz as [Hz | []]. subst z.
  unfold single_subst. destruct (Nat.eq_dec x x); [exact Hs|contradiction].
Qed.

Lemma eval_term_subst_unary :
  forall (E : @env M O N) x t s v a,
    wf_term E [x] t ->
    eval_term E v s = Some a ->
    eval_term E (fun z => if Nat.eq_dec z x then a else v z) t =
    eval_term E v (term_subst (single_subst x s) t).
Proof.
  intros E x t s v a Hwf. induction Hwf as [z Hz|i q t Hlook Hwf IH].
  - intro Hs. cbn in Hz. destruct Hz as [Hz | []]. subst z. cbn.
    unfold single_subst. destruct (Nat.eq_dec x x) as [_|H]; [|contradiction].
    destruct (Nat.eq_dec x x) as [_|H]; [symmetry; exact Hs|contradiction].
  - intro Hs. cbn. rewrite Hlook, IH by exact Hs. reflexivity.
Qed.

Lemma own_term_subst_unary :
  forall (E : @env M O N) x t s theta_t theta_s,
    wf_term E [x] t ->
    own_term E t = Some theta_t ->
    own_term E s = Some theta_s ->
    exists theta,
      own_term E (term_subst (single_subst x s) t) = Some theta /\
      perm_eq theta (perm_comp theta_t theta_s).
Proof.
  intros E x t s theta_t theta_s Hwf.
  revert theta_t theta_s.
  induction Hwf as [z Hz|i q t Hlook Hwf IH].
  - intros theta_t theta_s Ht Hs. cbn in Hz. destruct Hz as [Hz | []]. subst z.
    cbn in Ht. inversion Ht; subst theta_t.
    exists theta_s. split.
    + cbn. unfold single_subst.
      destruct (Nat.eq_dec x x); [exact Hs|contradiction].
    + apply perm_eq_sym. apply perm_comp_id_l.
  - intros theta_t theta_s Ht Hs. cbn in Ht. rewrite Hlook in Ht.
    destruct (own_term E t) as [theta_body|] eqn:Hbody; try discriminate.
    inversion Ht; subst theta_t.
    destruct (IH theta_body theta_s (eq_refl _) Hs) as [theta' [Htheta' Heq]].
    exists (perm_comp (g_own q) theta'). split.
    + cbn. rewrite Hlook, Htheta'. reflexivity.
    + intro o. cbn. rewrite Heq. reflexivity.
Qed.

Lemma formula_subst_wf :
  forall (E : @env M O N) A z w s,
    wf_formula E A -> wf_term E [w] s ->
    wf_formula E (formula_subst A z w s).
Proof.
  intros E A z w s HA Hs. destruct HA as [x t Ht|o x t Ht Hclose].
  - unfold formula_subst. destruct (Nat.eq_dec x z) as [->|Hneq].
    + constructor. apply wf_term_single_subst; assumption.
    + constructor. exact Ht.
  - cbn. constructor; assumption.
Qed.

Lemma rename_unary_close :
  forall (E : @env M O N) o x z t,
    wf_term E [x] t -> close E o t ->
    close E o (term_rename (fun a => if Nat.eq_dec a x then z else a) t).
Proof.
  intros E o x z t Hwf [theta_t [Ht Hfix]].
  unfold term_rename.
  set (rho := fun a : nat => if Nat.eq_dec a x then z else a).
  assert (Hr : term_subst (fun a => TVar (rho a)) t =
               term_subst (single_subst x (TVar z)) t).
  { eapply term_subst_ext_wf; [exact Hwf|].
    intros a Ha. cbn in Ha. destruct Ha as [Ha | []]. subst a.
    unfold rho, single_subst.
    destruct (Nat.eq_dec x x) as [_|H]; [reflexivity|contradiction]. }
  change (close E o (term_subst (fun a => TVar (rho a)) t)).
  rewrite Hr.
  destruct (@own_term_subst_unary E x t (TVar z)
    theta_t perm_id Hwf Ht (eq_refl (Some perm_id)))
    as [theta [Htheta Heq]].
  exists theta. split; [exact Htheta|].
  rewrite Heq. cbn. exact Hfix.
Qed.

Lemma bound_rename_wf :
  forall (E : @env M O N) o x z t,
    wf_formula E (FAll o x t) -> wf_formula E (bound_rename (FAll o x t) z).
Proof.
  intros E o x z t H. inversion H as [|o' x' t' Hwf Hclose]; subst.
  cbn. constructor.
  - eapply wf_term_subst; [exact Hwf|].
    intros a Ha. cbn in Ha. destruct Ha as [Ha | []]. subst a.
    destruct (Nat.eq_dec x x) as [_|Hneq].
    + constructor. cbn. auto.
    + contradiction.
  - apply rename_unary_close; assumption.
Qed.

End StructuralLaws.

(** Sections 7--10: configurations, labels, transitions, finite runs and
    observations.  A suspension stores [E0,q,h]; its boundary family and
    excision map are definitionally reconstructed from those fields. *)
Section TransitionKernel.
Context {M O N : Type}.
Variable N_eq_dec : forall x y : N, {x = y} + {x <> y}.
Variable enumM : list M.
Variable enumO : list O.

Definition Env := @env M O N.
Definition Gen := @generation M O N.
Definition Perm := @perm O.

Inductive phase : Type :=
| Idle
| Suspended : Env -> nat -> nat -> phase.

Inductive log_entry : Type :=
| LogSuspend : Gen -> nat -> log_entry
| LogResume : Gen -> Gen -> Gen -> term -> Perm -> log_entry.

Inductive label : Type :=
| TestLabel : nat -> nat -> label
| ResumeLabel : nat -> nat -> term -> label.

Record config : Type := mkConfig {
  c_env : Env;
  c_version : N -> nat;
  c_used : list nat;
  c_log : list log_entry;
  c_phase : phase
}.

Inductive phase_ok (E : Env) : phase -> Prop :=
| PhaseIdle : phase_ok E Idle
| PhaseSuspended : forall E0 q h old,
    lookup_rule E0 q = Some old ->
    0 < h ->
    E = delete_rule E0 q ->
    phase_ok E (Suspended E0 q h).

Record config_wf (C : config) : Prop := mkConfigWf {
  cw_env : env_wf (c_env C);
  cw_version : forall q, In q (c_env C) ->
    c_version C (g_name q) = g_generation q;
  cw_used_nodup : NoDup (c_used C);
  cw_ids_used : forall q, In q (c_env C) -> In (g_id q) (c_used C);
  cw_phase : phase_ok (c_env C) (c_phase C)
}.

Definition version_update (nu : N -> nat) (rho : N) (n : nat) : N -> nat :=
  fun x => if N_eq_dec x rho then n else nu x.

Definition test_target
  (E : Env) (nu : N -> nat) U L q h (old : Gen) : config :=
  mkConfig (delete_rule E q) nu U
    (L ++ [LogSuspend old h]) (Suspended E q h).

Inductive test_rule : config -> label -> config -> Prop :=
| TestRuleIntro : forall E nu U L q h old,
    lookup_rule E q = Some old ->
    0 < h ->
    config_wf (mkConfig E nu U L Idle) ->
    config_wf (test_target E nu U L q h old) ->
    test_rule (mkConfig E nu U L Idle) (TestLabel q h)
      (test_target E nu U L q h old).

Definition resume_target
  (E0 : Env) q h nu U L k u (cert : ORec E0 q k u h)
  (qplus : Gen) : config :=
  mkConfig (qplus :: delete_rule E0 q)
    (version_update nu (g_name (orec_old cert))
       (S (g_generation (orec_old cert))))
    (g_id qplus :: U)
    (L ++ [LogResume (orec_old cert) qplus (orec_interpreter cert) u
       (delta (g_own qplus) (g_own (orec_old cert)))])
    Idle.

Inductive resume_rule : config -> label -> config -> Prop :=
| ResumeRuleIntro : forall E0 q k u h nu U L
    (cert : ORec E0 q k u h) qplus,
    new_generation enumM enumO
      E0 q k u h U = Some qplus ->
    config_wf (mkConfig (delete_rule E0 q) nu U L (Suspended E0 q h)) ->
    config_wf (resume_target nu U L cert qplus) ->
    resume_rule
      (mkConfig (delete_rule E0 q) nu U L (Suspended E0 q h))
      (ResumeLabel q k u)
      (resume_target nu U L cert qplus).

Inductive step : config -> label -> config -> Prop :=
| StepTest : forall C l C', test_rule C l C' -> step C l C'
| StepResume : forall C l C', resume_rule C l C' -> step C l C'.

Inductive run : config -> config -> Type :=
| RunRefl : forall C, run C C
| RunStep : forall C l C' C'', step C l C' -> run C' C'' -> run C C''.

Definition reaches (C C' : config) : Prop := inhabited (run C C').

Theorem O1_step_preserves_config : forall C l C',
  step C l C' -> config_wf C /\ config_wf C'.
Proof.
  intros C l C' H. inversion H as [C0 l0 C1 Ht|C0 l0 C1 Hr]; subst.
  - inversion Ht; subst; auto.
  - inversion Hr; subst; auto.
Qed.

Theorem O1_suspended_cannot_test : forall E0 q h E nu U L l C',
  ~ test_rule (mkConfig E nu U L (Suspended E0 q h)) l C'.
Proof. intros E0 q h E nu U L l C' H. inversion H. Qed.

Theorem O1_template_excludes_target : forall (E : Env) q k u h,
  ORec E q k u h -> ~ In q (opsupp_raw u).
Proof. intros E q k u h H. exact (orec_excludes_target H). Qed.

Record observation : Type := mkObservation {
  obs_semantic : option M;
  obs_ownership : option Perm;
  obs_tree : term;
  obs_preorder_ids : list nat
}.

Definition observe (E : Env) (v : nat -> M) (t : term) : observation :=
  mkObservation (eval_term E v t) (own_term E t) t (opsupp_raw t).

End TransitionKernel.

(** O0: executable decision procedures for the inductively generated finite
    judgments.  ORec itself is a finite certificate in [Type]; construction of
    such a value is a successful finite check. *)
Section Deciders.
Context {M O N : Type}.
Variable O_eq_dec : forall x y : O, {x = y} + {x <> y}.

Fixpoint wf_term_dec (E : @env M O N) (X : list nat) (t : term) :
  {wf_term E X t} + {~ wf_term E X t}.
Proof.
  destruct t as [x|i t].
  - destruct (in_dec Nat.eq_dec x X) as [Hin|Hout].
    + left. constructor. exact Hin.
    + right. intro H. inversion H; contradiction.
  - destruct (lookup_rule E i) as [q|] eqn:Hlookup.
    + destruct (wf_term_dec E X t) as [Ht|Ht].
      * left. econstructor; eauto.
      * right. intro H. inversion H; subst. contradiction.
    + right. intro H. inversion H; subst. congruence.
Defined.

Definition close_dec (E : @env M O N) (o : O) (t : term) :
  {close E o t} + {~ close E o t}.
Proof.
  unfold close. destruct (own_term E t) as [theta|] eqn:Htheta.
  - destruct (O_eq_dec (pmap theta o) o) as [Heq|Hneq].
    + left. exists theta. auto.
    + right. intros [theta' [Htheta' Hfix]]. inversion Htheta'; subst. contradiction.
  - right. intros [theta [Hsome _]]. congruence.
Defined.

Definition wf_formula_dec (E : @env M O N) (A : formula) :
  {wf_formula E A} + {~ wf_formula E A}.
Proof.
  destruct A as [x t | o x t].
  - destruct (wf_term_dec E [x] t) as [Hwf | Hwf].
    + left. constructor. exact Hwf.
    + right. intro H. inversion H; subst. contradiction.
  - destruct (wf_term_dec E [x] t) as [Hwf | Hwf].
    + destruct (close_dec E o t) as [Hclose | Hclose].
      * left. constructor; assumption.
      * right. intro H. inversion H; subst. contradiction.
    + right. intro H. inversion H; subst. contradiction.
Defined.

Fixpoint wf_boundary_dec (E : @env M O N) q h X b :
  {wf_boundary E q h X b} + {~ wf_boundary E q h X b}.
Proof.
  destruct b as [x|i b|b].
  - destruct (in_dec Nat.eq_dec x X) as [Hin|Hout].
    + left. constructor. exact Hin.
    + right. intro H. inversion H; contradiction.
  - destruct (lookup_rule (delete_rule E q) i) as [r|] eqn:Hlookup.
    + destruct (wf_boundary_dec E q h X b) as [Hb|Hb].
      * destruct (le_dec (S (boundary_height b)) h) as [Hle|Hle].
        -- left. econstructor; eauto.
        -- right. intro H. inversion H; subst. contradiction.
      * right. intro H. inversion H; subst. contradiction.
    + right. intro H. inversion H; subst. congruence.
  - destruct (wf_boundary_dec E q h X b) as [Hb|Hb].
    + destruct (le_dec (S (boundary_height b)) h) as [Hle|Hle].
      * left. constructor; assumption.
      * right. intro H. inversion H; subst. contradiction.
    + right. intro H. inversion H; subst. contradiction.
Defined.

Record finite_checkability : Type := mkFiniteCheckability {
  fc_term : forall (E : @env M O N) X t,
    {wf_term E X t} + {~ wf_term E X t};
  fc_close : forall (E : @env M O N) o t,
    {close E o t} + {~ close E o t};
  fc_formula : forall (E : @env M O N) A,
    {wf_formula E A} + {~ wf_formula E A};
  fc_boundary : forall (E : @env M O N) q h X b,
    {wf_boundary E q h X b} + {~ wf_boundary E q h X b}
}.

Definition O0_finite_checkability : finite_checkability :=
  mkFiniteCheckability wf_term_dec close_dec wf_formula_dec wf_boundary_dec.

End Deciders.

End OEBRC2173Transitions.

(** ===== END MERGED SOURCE: OEBRC2173_Transitions.v ===== *)

(** ===== BEGIN MERGED SOURCE: OEBRC2173_Model.v ===== *)
From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
Set Implicit Arguments.

Module OEBRC2173Model.
Import OEBRC2173Core.
Import OEBRC2173Transitions.

(** Section 12.1: the closed finite carriers. *)
Inductive M3 : Type := m0 | m1 | m2.
Inductive O2 : Type := o0 | o1.
Inductive N5 : Type := nP | nPinv | nAlpha | nBeta | nGamma.

Definition M3_eq_dec : forall x y : M3, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition O2_eq_dec : forall x y : O2, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition N5_eq_dec : forall x y : N5, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition enumM3 : list M3 := [m0; m1; m2].
Definition enumO2 : list O2 := [o0; o1].
Definition enumN5 : list N5 := [nP; nPinv; nAlpha; nBeta; nGamma].

Lemma enumM3_complete : forall x, In x enumM3.
Proof. intros []; cbn; auto. Qed.
Lemma enumO2_complete : forall x, In x enumO2.
Proof. intros []; cbn; auto. Qed.
Lemma enumN5_complete : forall x, In x enumN5.
Proof. intros []; unfold enumN5; cbn; tauto. Qed.

Definition cyc (x : M3) : M3 :=
  match x with m0 => m1 | m1 => m2 | m2 => m0 end.
Definition cyc_inv (x : M3) : M3 :=
  match x with m0 => m2 | m1 => m0 | m2 => m1 end.
Definition tabA (x : M3) : M3 :=
  match x with m0 => m1 | m1 => m0 | m2 => m2 end.
Definition tabB (x : M3) : M3 :=
  match x with m0 => m0 | m1 => m2 | m2 => m1 end.
Definition tabG (x : M3) : M3 :=
  match x with m0 => m2 | m1 => m1 | m2 => m0 end.

Definition swapO : @perm O2.
Proof.
  refine (mkPerm
    (fun x => match x with o0 => o1 | o1 => o0 end)
    (fun x => match x with o0 => o1 | o1 => o0 end) _ _);
    intros []; reflexivity.
Defined.

Definition idO : @perm O2 := perm_id.
Definition Gen3 := @generation M3 O2 N5.
Definition Env3 := @env M3 O2 N5.

Definition p0 : Gen3 :=
  mkGeneration nP 0 cyc swapO ProvInit 0.
Definition pinv0 : Gen3 :=
  mkGeneration nPinv 0 cyc_inv idO ProvInit 1.
Definition alpha0 : Gen3 :=
  mkGeneration nAlpha 0 tabA idO ProvInit 2.
Definition beta0 : Gen3 :=
  mkGeneration nBeta 0 tabB idO ProvInit 3.
Definition gamma0 : Gen3 :=
  mkGeneration nGamma 0 tabG idO ProvInit 4.

Definition env0 : Env3 := [p0; pinv0; alpha0; beta0; gamma0].
Definition used0 : list nat := seq 0 5.

Lemma env0_wf : env_wf env0.
Proof.
  unfold env_wf, env0. cbn. split.
  - repeat constructor; cbn; intuition congruence.
  - repeat constructor; cbn; intuition congruence.
Qed.

Definition u_beta : term :=
  TApp 0 (TApp 2 (TApp 1 (TVar 0))).

Definition beta_certificate : ORec env0 3 2 u_beta 1.
Proof.
  refine {| orec_old := beta0; orec_interpreter := alpha0 |}.
  - reflexivity.
  - reflexivity.
  - unfold u_beta. repeat econstructor; cbn; eauto.
  - discriminate.
  - unfold u_beta, opsupp_raw. cbn. auto.
  - unfold u_beta, opsupp_raw. cbn.
    intros [H | [H | [H | []]]]; discriminate.
  - intros []; reflexivity.
  - eexists. reflexivity.
  - lia.
Qed.

Definition beta1 : Gen3 :=
  match new_generation enumM3 enumO2 env0 3 2 u_beta 1 used0 with
  | Some q => q
  | None => beta0
  end.

Lemma beta1_new :
  new_generation enumM3 enumO2 env0 3 2 u_beta 1 used0 = Some beta1.
Proof.
  unfold beta1.
  destruct (new_generation enumM3 enumO2 env0 3 2 u_beta 1 used0)
    as [q|] eqn:Hnew; [reflexivity|].
  destruct (new_generation_spec enumM3 enumO2 used0 beta_certificate)
    as [qplus [Hsome _]]. congruence.
Qed.

Lemma beta1_name : g_name beta1 = nBeta.
Proof.
  unfold beta1, new_generation, env0, u_beta, compile_O.
  cbn. reflexivity.
Qed.

Lemma beta1_tab : forall x, g_tab beta1 x = tabB x.
Proof.
  intro x. unfold beta1, new_generation, env0, u_beta, compile_O.
  cbn. reflexivity.
Qed.

Lemma beta1_id : g_id beta1 = fresh_id used0.
Proof.
  unfold beta1, new_generation, env0, u_beta, compile_O.
  cbn. reflexivity.
Qed.

Lemma beta1_id_fresh : ~ In (g_id beta1) used0.
Proof. rewrite beta1_id. apply fresh_id_fresh. Qed.

Definition env1 : Env3 := beta1 :: delete_rule env0 3.
Definition used1 : list nat := g_id beta1 :: used0.

Definition u_gamma : term :=
  TApp 0 (TApp (g_id beta1) (TApp 1 (TVar 0))).

Definition gamma_certificate : ORec env1 4 (g_id beta1) u_gamma 1.
Proof.
  refine {| orec_old := gamma0; orec_interpreter := beta1 |}.
  - unfold env1. cbn. reflexivity.
  - unfold env1. cbn. reflexivity.
  - unfold u_gamma. repeat econstructor; cbn; eauto.
  - rewrite beta1_name. discriminate.
  - unfold u_gamma, opsupp_raw. cbn. auto.
  - unfold u_gamma, opsupp_raw. cbn.
    intros [H | [H | [H | []]]]; discriminate.
  - intros x. destruct x; cbn; rewrite ?beta1_tab; reflexivity.
  - eexists. reflexivity.
  - lia.
Qed.

Definition gamma1 : Gen3 :=
  match new_generation enumM3 enumO2 env1 4 (g_id beta1)
          u_gamma 1 used1 with
  | Some q => q
  | None => gamma0
  end.

Lemma gamma1_new :
  new_generation enumM3 enumO2 env1 4 (g_id beta1)
    u_gamma 1 used1 = Some gamma1.
Proof.
  unfold gamma1.
  destruct (new_generation enumM3 enumO2 env1 4 (g_id beta1)
    u_gamma 1 used1) as [q|] eqn:Hnew; [reflexivity|].
  destruct (new_generation_spec enumM3 enumO2 used1 gamma_certificate)
    as [qplus [Hsome _]]. congruence.
Qed.

Lemma gamma1_name : g_name gamma1 = nGamma.
Proof.
  unfold gamma1, new_generation, env1, u_gamma, compile_O.
  cbn. reflexivity.
Qed.

Lemma gamma1_tab : forall x, g_tab gamma1 x = tabG x.
Proof.
  intro x. unfold gamma1, new_generation, env1, u_gamma, compile_O.
  cbn. reflexivity.
Qed.

Lemma gamma1_id : g_id gamma1 = fresh_id used1.
Proof.
  unfold gamma1, new_generation, env1, u_gamma, compile_O.
  cbn. reflexivity.
Qed.

Lemma gamma1_id_fresh : ~ In (g_id gamma1) used1.
Proof. rewrite gamma1_id. apply fresh_id_fresh. Qed.

Definition env2 : Env3 := gamma1 :: delete_rule env1 4.
Definition used2 : list nat := g_id gamma1 :: used1.

Definition u_alpha : term :=
  TApp 0 (TApp (g_id gamma1) (TApp 1 (TVar 0))).

Lemma alpha_active_p_lookup :
  lookup_rule (delete_rule env2 2) 0 = Some p0.
Proof. unfold env2, env1. cbn. reflexivity. Qed.

Lemma alpha_active_gamma_lookup :
  lookup_rule (delete_rule env2 2) (g_id gamma1) = Some gamma1.
Proof. unfold env2. cbn. reflexivity. Qed.

Lemma alpha_active_pinv_lookup :
  lookup_rule (delete_rule env2 2) 1 = Some pinv0.
Proof. unfold env2, env1. cbn. reflexivity. Qed.

Definition alpha_certificate : ORec env2 2 (g_id gamma1) u_alpha 1.
Proof.
  refine {| orec_old := alpha0; orec_interpreter := gamma1 |}.
  - unfold env2, env1. cbn. reflexivity.
  - unfold env2. cbn. reflexivity.
  - unfold u_alpha. repeat econstructor; cbn; eauto.
  - rewrite gamma1_name. discriminate.
  - unfold u_alpha, opsupp_raw. cbn. auto.
  - unfold u_alpha, opsupp_raw. cbn.
    intros [H | [H | [H | []]]]; discriminate.
  - intros x. unfold compile_M, u_alpha. cbn [eval_term].
    rewrite alpha_active_p_lookup, alpha_active_gamma_lookup,
      alpha_active_pinv_lookup.
    cbn [eval_term]. rewrite gamma1_tab. destruct x; reflexivity.
  - eexists. reflexivity.
  - lia.
Qed.

Definition alpha1 : Gen3 :=
  match new_generation enumM3 enumO2 env2 2 (g_id gamma1)
          u_alpha 1 used2 with
  | Some q => q
  | None => alpha0
  end.

Lemma alpha1_new :
  new_generation enumM3 enumO2 env2 2 (g_id gamma1)
    u_alpha 1 used2 = Some alpha1.
Proof.
  unfold alpha1.
  destruct (new_generation enumM3 enumO2 env2 2 (g_id gamma1)
    u_alpha 1 used2) as [q|] eqn:Hnew; [reflexivity|].
  destruct (new_generation_spec enumM3 enumO2 used2 alpha_certificate)
    as [qplus [Hsome _]]. congruence.
Qed.

Lemma alpha1_name : g_name alpha1 = nAlpha.
Proof.
  unfold alpha1, new_generation, env2, u_alpha, compile_O.
  cbn. reflexivity.
Qed.

Lemma alpha1_tab : forall x, g_tab alpha1 x = tabA x.
Proof.
  intro x. unfold alpha1, new_generation, env2, u_alpha, compile_O.
  cbn. reflexivity.
Qed.

Definition env3 : Env3 := alpha1 :: delete_rule env2 2.

(** Sections 12.3--12.4 and O5. *)
Theorem conjugation_A_B : forall x, cyc (tabA (cyc_inv x)) = tabB x.
Proof. intros []; reflexivity. Qed.
Theorem conjugation_B_G : forall x, cyc (tabB (cyc_inv x)) = tabG x.
Proof. intros []; reflexivity. Qed.
Theorem conjugation_G_A : forall x, cyc (tabG (cyc_inv x)) = tabA x.
Proof. intros []; reflexivity. Qed.

Lemma beta1_own_o0 : pmap (g_own beta1) o0 = o1.
Proof.
  unfold beta1, new_generation, env0, u_beta, compile_O.
  cbn. reflexivity.
Qed.

Lemma gamma1_own_o0 : pmap (g_own gamma1) o0 = o0.
Proof.
  unfold gamma1, new_generation, env1, u_gamma, compile_O.
  cbn.
  reflexivity.
Qed.

Lemma alpha1_own_o0 : pmap (g_own alpha1) o0 = o1.
Proof.
  unfold alpha1, new_generation, env2, u_alpha, compile_O.
  cbn.
  reflexivity.
Qed.

Opaque beta_certificate gamma_certificate alpha_certificate.
Opaque beta1 gamma1 alpha1.

Definition witness_edges : list (N5 * N5) :=
  [(nAlpha,nBeta); (nBeta,nGamma); (nGamma,nAlpha)].

Lemma alpha0_own_identity : g_own alpha0 = idO.
Proof. reflexivity. Qed.

Lemma delta_over_id : forall (theta : @perm O2) x,
  pmap (delta theta idO) x = pmap theta x.
Proof. intros theta []; reflexivity. Qed.

Lemma alpha1_holonomy_o0 :
  pmap (delta (g_own alpha1) (g_own alpha0)) o0 = o1.
Proof.
  rewrite alpha0_own_identity, delta_over_id.
  exact alpha1_own_o0.
Qed.

Theorem O5_non_degenerate_holonomy :
  (forall x, g_tab alpha1 x = g_tab alpha0 x) /\
  pmap (delta (g_own alpha1) (g_own alpha0)) o0 = o1 /\
  o0 <> o1.
Proof.
  split.
  - intro x. apply alpha1_tab.
  - split.
    + exact alpha1_holonomy_o0.
    + discriminate.
Qed.

(** Section 12.5 and O6: formation, not truth value, separates. *)
Definition alpha0_term : term := TApp 2 (TVar 0).
Definition alpha1_term : term := TApp (g_id alpha1) (TVar 0).

Lemma alpha0_close : close env0 o0 alpha0_term.
Proof. exists (perm_comp idO perm_id). split; reflexivity. Qed.

Lemma env3_alpha1_lookup :
  lookup_rule env3 (g_id alpha1) = Some alpha1.
Proof. unfold env3. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma perm_comp_id_at : forall (theta : @perm O2) x,
  pmap (perm_comp theta perm_id) x = pmap theta x.
Proof. intros theta []; reflexivity. Qed.

Lemma perm_id_at : forall x : O2, pmap perm_id x = x.
Proof. intros []; reflexivity. Qed.

Lemma single_app_not_close : forall (E : Env3) i q x o,
  lookup_rule E i = Some q ->
  pmap (g_own q) o <> o ->
  ~ close E o (TApp i (TVar x)).
Proof.
  intros E i q x o Hlook Hmove [theta [Htheta Hfix]].
  cbn [own_term] in Htheta. rewrite Hlook in Htheta. cbn in Htheta.
  injection Htheta as Htheta. subst theta.
  change (pmap (g_own q) o = o) in Hfix.
  exact (Hmove Hfix).
Qed.

Lemma alpha1_not_close : ~ close env3 o0 alpha1_term.
Proof.
  unfold alpha1_term.
  eapply single_app_not_close.
  - exact env3_alpha1_lookup.
  - intro Hfix. rewrite alpha1_own_o0 in Hfix. discriminate.
Qed.

Theorem O6_quantifier_formation_separation :
  wf_formula env0 (FAll o0 0 alpha0_term) /\
  ~ wf_formula env3 (FAll o0 0 alpha1_term) /\
  (forall x, g_tab alpha0 x = g_tab alpha1 x).
Proof.
  split.
  - constructor.
    + unfold alpha0_term. econstructor; [reflexivity|constructor; cbn; auto].
    + exact alpha0_close.
  - split.
    + intro H. inversion H; subst. apply alpha1_not_close. assumption.
    + intro x. symmetry. apply alpha1_tab.
Qed.

(** A closed, genuinely satisfiable formula model. *)
Definition predicate_true (_ : M3) : Prop := True.
Definition valuation0 (_ : nat) : M3 := m0.

Theorem closed_formula_has_model :
  wf_formula env0 (FAll o0 0 alpha0_term) /\
  satisfies env0 predicate_true valuation0 (FAll o0 0 alpha0_term).
Proof.
  split.
  - exact (proj1 O6_quantifier_formation_separation).
  - intro a. exists (tabA a). split.
    + unfold alpha0_term, env0. cbn. destruct a; reflexivity.
    + exact I.
Qed.

(** Section 11 and O7: a structure-preserving flat translation must preserve
    names, tables, ownership holonomy, edge order and Close. *)
Record flat_translation : Type := mkFlatTranslation {
  ft_initial : Gen3;
  ft_final : Gen3;
  ft_edges : list (N5 * N5);
  ft_initial_name : g_name ft_initial = nAlpha;
  ft_final_name : g_name ft_final = nAlpha;
  ft_initial_table : forall x, g_tab ft_initial x = g_tab alpha0 x;
  ft_final_table : forall x, g_tab ft_final x = g_tab alpha1 x;
  ft_initial_own : perm_eq (g_own ft_initial) (g_own alpha0);
  ft_final_own : perm_eq (g_own ft_final) (g_own alpha1);
  ft_edges_preserved : ft_edges = witness_edges;
  ft_holonomy_preserved :
    perm_eq (delta (g_own ft_final) (g_own ft_initial))
            (delta (g_own alpha1) (g_own alpha0));
  ft_close_preserved :
    (pmap (g_own ft_initial) o0 = o0 <-> pmap (g_own alpha0) o0 = o0) /\
    (pmap (g_own ft_final) o0 = o0 <-> pmap (g_own alpha1) o0 = o0);
  ft_flatness :
    (forall x, g_tab ft_initial x = g_tab ft_final x) ->
    perm_eq (delta (g_own ft_final) (g_own ft_initial)) perm_id
}.

Theorem O7_no_path_flat_translation : flat_translation -> False.
Proof.
  intro T.
  assert (Htab : forall x, g_tab (ft_initial T) x = g_tab (ft_final T) x).
  { intro x. rewrite ft_initial_table, ft_final_table.
    symmetry. apply alpha1_tab. }
  pose proof (ft_flatness T Htab o0) as Hflat.
  pose proof (ft_holonomy_preserved T o0) as Hpres.
  pose proof (proj1 (proj2 O5_non_degenerate_holonomy)) as Hconcrete.
  rewrite Hpres, Hconcrete in Hflat. discriminate.
Qed.

Theorem model_nontrivial :
  pmap swapO o0 <> pmap idO o0 /\ tabA m0 <> tabB m0.
Proof. cbn. split; discriminate. Qed.

End OEBRC2173Model.

(** ===== END MERGED SOURCE: OEBRC2173_Model.v ===== *)

(** ===== BEGIN MERGED SOURCE: OEBRC2173_RunAblation.v ===== *)
From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
Set Implicit Arguments.

Module OEBRC2173RunAblation.
Import OEBRC2173Core.
Import OEBRC2173Transitions.
Import OEBRC2173Model.

(** Sections 7--9 and 12.2: a concrete six-transition run containing the
    three legal test/resume pairs. *)

Definition Config3 := @config M3 O2 N5.
Definition Step3 := @step M3 O2 N5 N5_eq_dec enumM3 enumO2.
Definition Run3 := @run M3 O2 N5 N5_eq_dec enumM3 enumO2.

Definition nu0 (_ : N5) : nat := 0.
Definition nu1 : N5 -> nat := version_update N5_eq_dec nu0 nBeta 1.
Definition nu2 : N5 -> nat := version_update N5_eq_dec nu1 nGamma 1.
Definition nu3 : N5 -> nat := version_update N5_eq_dec nu2 nAlpha 1.
Definition used3 : list nat := g_id alpha1 :: used2.

Lemma alpha1_id_value : g_id alpha1 = fresh_id used2.
Proof.
  unfold alpha1, new_generation, env2, u_alpha, compile_O.
  cbn. reflexivity.
Qed.

Lemma alpha1_id_fresh : ~ In (g_id alpha1) used2.
Proof. rewrite alpha1_id_value. apply fresh_id_fresh. Qed.

Lemma beta1_generation : g_generation beta1 = 1.
Proof.
  unfold beta1, new_generation, env0, u_beta, compile_O.
  cbn. reflexivity.
Qed.
Lemma gamma1_generation : g_generation gamma1 = 1.
Proof.
  unfold gamma1, new_generation, env1, u_gamma, compile_O.
  cbn. reflexivity.
Qed.
Lemma alpha1_generation : g_generation alpha1 = 1.
Proof.
  unfold alpha1, new_generation, env2, u_alpha, compile_O.
  cbn. reflexivity.
Qed.

Lemma env3_shape : env3 = [alpha1; gamma1; beta1; p0; pinv0].
Proof. vm_compute. reflexivity. Qed.

Lemma env1_wf_concrete : env_wf env1.
Proof. vm_compute. repeat constructor; simpl; intuition congruence. Qed.
Lemma env2_wf_concrete : env_wf env2.
Proof. vm_compute. repeat constructor; simpl; intuition congruence. Qed.
Lemma env3_wf_concrete : env_wf env3.
Proof. vm_compute. repeat constructor; simpl; intuition congruence. Qed.

Lemma used0_nodup : NoDup used0.
Proof. vm_compute. repeat constructor; simpl; intuition congruence. Qed.
Lemma used1_nodup : NoDup used1.
Proof. vm_compute. repeat constructor; simpl; intuition congruence. Qed.
Lemma used2_nodup : NoDup used2.
Proof. vm_compute. repeat constructor; simpl; intuition congruence. Qed.
Lemma used3_nodup : NoDup used3.
Proof. vm_compute. repeat constructor; simpl; intuition congruence. Qed.

Lemma nu0_ok : forall q, In q env0 -> nu0 (g_name q) = g_generation q.
Proof.
  intros q H. unfold env0 in H; cbn in H.
  destruct H as [<- | [<- | [<- | [<- | [<- | []]]]]]; reflexivity.
Qed.

Lemma nu1_ok : forall q, In q env1 -> nu1 (g_name q) = g_generation q.
Proof.
  intros q H. unfold env1, env0 in H; cbn in H.
  destruct H as [<- | [<- | [<- | [<- | [<- | []]]]]]; vm_compute; tauto.
Qed.

Lemma nu2_ok : forall q, In q env2 -> nu2 (g_name q) = g_generation q.
Proof.
  intros q H. unfold env2, env1, env0 in H; cbn in H.
  destruct H as [<- | [<- | [<- | [<- | [<- | []]]]]]; vm_compute; tauto.
Qed.

Lemma in_delete_rule_original : forall (E : Env3) i q,
  In q (delete_rule E i) -> In q E.
Proof.
  induction E as [|a E IH]; intros i q H; cbn in H.
  - contradiction.
  - destruct (Nat.eqb i (g_id a)) eqn:Ha.
    + right. apply IH with (i := i). exact H.
    + cbn in H. destruct H as [H | H].
      * left. exact H.
      * right. apply IH with (i := i). exact H.
Qed.

Lemma env2_delete_alpha_has_no_alpha_name : forall q,
  In q (delete_rule env2 2) -> g_name q <> nAlpha.
Proof.
  intros q H. unfold env2, env1, env0 in H; cbn in H.
  destruct H as [<- | [<- | [<- | [<- | []]]]];
    rewrite ?gamma1_name, ?beta1_name; discriminate.
Qed.

Lemma nu3_ok : forall q, In q env3 -> nu3 (g_name q) = g_generation q.
Proof.
  intros q H. unfold env3 in H.
  change (alpha1 = q \/ In q (delete_rule env2 2)) in H.
  destruct H as [Halpha | Hrest].
  - subst q. rewrite alpha1_name, alpha1_generation. reflexivity.
  - unfold nu3, version_update.
    destruct (N5_eq_dec (g_name q) nAlpha) as [Heq | Hneq].
    + exfalso. exact (env2_delete_alpha_has_no_alpha_name Hrest Heq).
    + apply nu2_ok. eapply in_delete_rule_original. exact Hrest.
Qed.

Lemma env0_ids_used : forall q, In q env0 -> In (g_id q) used0.
Proof.
  intros q H. unfold env0 in H; cbn in H.
  destruct H as [<- | [<- | [<- | [<- | [<- | []]]]]]; vm_compute; tauto.
Qed.
Lemma env1_ids_used : forall q, In q env1 -> In (g_id q) used1.
Proof.
  intros q H. unfold env1, env0 in H; cbn in H.
  destruct H as [<- | [<- | [<- | [<- | [<- | []]]]]]; vm_compute; tauto.
Qed.
Lemma env2_ids_used : forall q, In q env2 -> In (g_id q) used2.
Proof.
  intros q H. unfold env2, env1, env0 in H; cbn in H.
  destruct H as [<- | [<- | [<- | [<- | [<- | []]]]]]; vm_compute; tauto.
Qed.
Lemma env3_ids_used : forall q, In q env3 -> In (g_id q) used3.
Proof.
  intros q H. unfold env3 in H.
  change (alpha1 = q \/ In q (delete_rule env2 2)) in H.
  destruct H as [Halpha | Hrest].
  - subst q. unfold used3. left. reflexivity.
  - unfold used3. right. apply env2_ids_used.
    eapply in_delete_rule_original. exact Hrest.
Qed.

Lemma beta_certificate_old : orec_old beta_certificate = beta0.
Proof.
  pose proof (orec_old_lookup beta_certificate) as H. cbn in H.
  inversion H. reflexivity.
Qed.
Lemma gamma_certificate_old : orec_old gamma_certificate = gamma0.
Proof.
  pose proof (orec_old_lookup gamma_certificate) as H.
  unfold env1, env0 in H; cbn in H.
  injection H as H. symmetry. exact H.
Qed.
Lemma alpha_certificate_old : orec_old alpha_certificate = alpha0.
Proof.
  pose proof (orec_old_lookup alpha_certificate) as H.
  unfold env2, env1, env0 in H; cbn in H.
  injection H as H. symmetry. exact H.
Qed.

Definition C0 : Config3 := mkConfig env0 nu0 used0 [] Idle.
Definition Sbeta : Config3 := test_target env0 nu0 used0 [] 3 1 beta0.
Definition C1 : Config3 :=
  resume_target N5_eq_dec nu0 used0 (c_log Sbeta) beta_certificate beta1.
Definition L1 := c_log C1.
Definition Sgamma : Config3 := test_target env1 nu1 used1 L1 4 1 gamma0.
Definition C2 : Config3 :=
  resume_target N5_eq_dec nu1 used1 (c_log Sgamma) gamma_certificate gamma1.
Definition L2 := c_log C2.
Definition Salpha : Config3 := test_target env2 nu2 used2 L2 2 1 alpha0.
Definition C3 : Config3 :=
  resume_target N5_eq_dec nu2 used2 (c_log Salpha) alpha_certificate alpha1.

Lemma C0_wf : config_wf C0.
Proof.
  constructor.
  - exact env0_wf.
  - exact nu0_ok.
  - exact used0_nodup.
  - exact env0_ids_used.
  - constructor.
Qed.

Lemma Sbeta_wf : config_wf Sbeta.
Proof.
  unfold Sbeta, test_target.
  constructor.
  - vm_compute. repeat constructor; simpl; intuition congruence.
  - intros q H. apply nu0_ok. eapply in_delete_rule_original. exact H.
  - exact used0_nodup.
  - intros q H. apply env0_ids_used. eapply in_delete_rule_original. exact H.
  - econstructor; [reflexivity | lia | reflexivity].
Qed.

Lemma C1_wf : config_wf C1.
Proof.
  unfold C1, resume_target.
  constructor.
  - change (env_wf env1). exact env1_wf_concrete.
  - rewrite beta_certificate_old. change (forall q, In q env1 ->
      nu1 (g_name q) = g_generation q). exact nu1_ok.
  - change (NoDup used1). exact used1_nodup.
  - change (forall q, In q env1 -> In (g_id q) used1).
    exact env1_ids_used.
  - constructor.
Qed.

Lemma Sgamma_wf : config_wf Sgamma.
Proof.
  unfold Sgamma, test_target.
  constructor.
  - vm_compute. repeat constructor; simpl; intuition congruence.
  - intros q H. apply nu1_ok. eapply in_delete_rule_original. exact H.
  - exact used1_nodup.
  - intros q H. apply env1_ids_used. eapply in_delete_rule_original. exact H.
  - econstructor; [reflexivity | lia | reflexivity].
Qed.

Lemma C2_wf : config_wf C2.
Proof.
  unfold C2, resume_target.
  constructor.
  - change (env_wf env2). exact env2_wf_concrete.
  - rewrite gamma_certificate_old. change (forall q, In q env2 ->
      nu2 (g_name q) = g_generation q). exact nu2_ok.
  - change (NoDup used2). exact used2_nodup.
  - change (forall q, In q env2 -> In (g_id q) used2).
    exact env2_ids_used.
  - constructor.
Qed.

Lemma Salpha_wf : config_wf Salpha.
Proof.
  unfold Salpha, test_target.
  constructor.
  - vm_compute. repeat constructor; simpl; intuition congruence.
  - intros q H. apply nu2_ok. eapply in_delete_rule_original. exact H.
  - exact used2_nodup.
  - intros q H. apply env2_ids_used. eapply in_delete_rule_original. exact H.
  - econstructor; [reflexivity | lia | reflexivity].
Qed.

Lemma C3_wf : config_wf C3.
Proof.
  unfold C3, resume_target.
  constructor.
  - change (env_wf env3). exact env3_wf_concrete.
  - rewrite alpha_certificate_old. change (forall q, In q env3 ->
      nu3 (g_name q) = g_generation q). exact nu3_ok.
  - change (NoDup used3). exact used3_nodup.
  - change (forall q, In q env3 -> In (g_id q) used3).
    exact env3_ids_used.
  - constructor.
Qed.

Lemma C1_shape : C1 = mkConfig env1 nu1 used1 L1 Idle.
Proof.
  unfold L1, C1, resume_target. rewrite beta_certificate_old. reflexivity.
Qed.
Lemma C2_shape : C2 = mkConfig env2 nu2 used2 L2 Idle.
Proof.
  unfold L2, C2, resume_target. rewrite gamma_certificate_old. reflexivity.
Qed.

Lemma beta_test_step : Step3 C0 (TestLabel 3 1) Sbeta.
Proof.
  apply StepTest. apply TestRuleIntro; [reflexivity | lia | exact C0_wf | exact Sbeta_wf].
Qed.

Lemma beta_resume_step : Step3 Sbeta (ResumeLabel 3 2 u_beta) C1.
Proof.
  apply StepResume.
  eapply (@ResumeRuleIntro M3 O2 N5 N5_eq_dec enumM3 enumO2
    env0 3 2 u_beta 1 nu0 used0 (c_log Sbeta) beta_certificate beta1).
  - exact beta1_new.
  - exact Sbeta_wf.
  - exact C1_wf.
Qed.

Lemma gamma_test_step : Step3 C1 (TestLabel 4 1) Sgamma.
Proof.
  rewrite C1_shape. apply StepTest. apply TestRuleIntro.
  - reflexivity.
  - lia.
  - rewrite <- C1_shape. exact C1_wf.
  - exact Sgamma_wf.
Qed.

Lemma gamma_resume_step : Step3 Sgamma (ResumeLabel 4 (g_id beta1) u_gamma) C2.
Proof.
  apply StepResume.
  eapply (@ResumeRuleIntro M3 O2 N5 N5_eq_dec enumM3 enumO2
    env1 4 (g_id beta1) u_gamma 1 nu1 used1 (c_log Sgamma)
    gamma_certificate gamma1).
  - exact gamma1_new.
  - exact Sgamma_wf.
  - exact C2_wf.
Qed.

Lemma alpha_test_step : Step3 C2 (TestLabel 2 1) Salpha.
Proof.
  rewrite C2_shape. apply StepTest. apply TestRuleIntro.
  - reflexivity.
  - lia.
  - rewrite <- C2_shape. exact C2_wf.
  - exact Salpha_wf.
Qed.

Lemma alpha_resume_step : Step3 Salpha (ResumeLabel 2 (g_id gamma1) u_alpha) C3.
Proof.
  apply StepResume.
  eapply (@ResumeRuleIntro M3 O2 N5 N5_eq_dec enumM3 enumO2
    env2 2 (g_id gamma1) u_alpha 1 nu2 used2 (c_log Salpha)
    alpha_certificate alpha1).
  - exact alpha1_new.
  - exact Salpha_wf.
  - exact C3_wf.
Qed.

Definition witness_six_step_run : Run3 C0 C3.
Proof.
  eapply RunStep; [exact beta_test_step |].
  eapply RunStep; [exact beta_resume_step |].
  eapply RunStep; [exact gamma_test_step |].
  eapply RunStep; [exact gamma_resume_step |].
  eapply RunStep; [exact alpha_test_step |].
  eapply RunStep; [exact alpha_resume_step |].
  apply RunRefl.
Defined.

Theorem O5_three_resumptions_are_legal : inhabited (Run3 C0 C3).
Proof. exact (inhabits witness_six_step_run). Qed.

(** Section 13.9, O8.1: the live-target reduction neither deletes the tested
    generation nor excludes it from templates. *)
Definition R_live_test_env (E : Env3) (_q : nat) : Env3 := E.
Definition R_live_template (E : Env3) q k (u : term) : Prop :=
  wf_term E [0] u /\ In k (opsupp_raw u) /\ In q (opsupp_raw u).
Definition live_self_use : term := TApp 2 (TApp 1 (TVar 0)).

Theorem R_live_breaks_O1 :
  lookup_rule (R_live_test_env env0 2) 2 = Some alpha0 /\
  R_live_template env0 2 1 live_self_use /\
  g_name pinv0 <> g_name alpha0.
Proof.
  split.
  - reflexivity.
  - split.
    + unfold R_live_template, live_self_use. split.
      * econstructor; [reflexivity |].
        econstructor; [reflexivity |].
        constructor. cbn. auto.
      * split; cbn; auto.
    + discriminate.
Qed.

(** O8.2: the no-boundary reduction has only ordinary syntax/evaluation and
    explicitly omits every boundary operation needed by O2 and O3. *)
Inductive system_feature : Type :=
| OrdinaryTerms | OrdinaryEvaluation | OrdinaryOwnership
| BoundarySyntax | BoundarySubstitution | BoundaryExcision
| BoundaryNaturality | UniqueDeltaSource.

Definition R_nobnd_features : list system_feature :=
  [OrdinaryTerms; OrdinaryEvaluation; OrdinaryOwnership].

Theorem R_nobnd_loses_O2_O3 :
  ~ In BoundarySyntax R_nobnd_features /\
  ~ In BoundarySubstitution R_nobnd_features /\
  ~ In BoundaryExcision R_nobnd_features /\
  ~ In BoundaryNaturality R_nobnd_features /\
  ~ In UniqueDeltaSource R_nobnd_features.
Proof.
  unfold R_nobnd_features; repeat split; cbn; intuition discriminate.
Qed.

(** O8.3: quotient every ownership value to the identity. *)
Definition R_flatown_own (_E : Env3) (_t : term) : @perm O2 := idO.
Definition R_flatown_close (E : Env3) (o : O2) (t : term) : Prop :=
  pmap (R_flatown_own E t) o = o.

Theorem R_flatown_collapses_O6 :
  R_flatown_close env0 o0 alpha0_term /\
  R_flatown_close env3 o0 alpha1_term /\
  (R_flatown_close env0 o0 alpha0_term <->
   R_flatown_close env3 o0 alpha1_term).
Proof. unfold R_flatown_close, R_flatown_own, idO; cbn; tauto. Qed.

(** O8.4: retain identity-code uniqueness but drop name uniqueness and the
    interpreter/target distinct-name side condition. *)
Definition R_same_env_wf (E : Env3) : Prop := NoDup (map g_id E).
Definition R_same_name_condition (_target _interpreter : Gen3) : Prop := True.
Definition same_name_generations : Env3 := [alpha0; alpha1].

Theorem R_same_breaks_distinct_name_commitment :
  R_same_env_wf same_name_generations /\
  g_name alpha0 = g_name alpha1 /\
  g_generation alpha0 <> g_generation alpha1 /\
  R_same_name_condition alpha0 alpha1.
Proof.
  unfold R_same_env_wf, same_name_generations, R_same_name_condition.
  vm_compute. repeat split; try discriminate;
    repeat constructor; simpl; intuition congruence.
Qed.

(** O8.5: reject an edge whenever it closes a name path. *)
Inductive name_reaches (es : list (N5 * N5)) : N5 -> N5 -> Prop :=
| NR_edge : forall a b, In (a,b) es -> name_reaches es a b
| NR_trans : forall a b c,
    name_reaches es a b -> name_reaches es b c -> name_reaches es a c.

Definition R_acyc_accept (es : list (N5 * N5)) (e : N5 * N5) : Prop :=
  ~ name_reaches es (snd e) (fst e).
Definition first_two_edges : list (N5 * N5) :=
  [(nAlpha,nBeta); (nBeta,nGamma)].

Theorem R_acyc_rejects_third_resume :
  ~ R_acyc_accept first_two_edges (nGamma,nAlpha).
Proof.
  intro Hreject. apply Hreject.
  eapply NR_trans with (b := nBeta); apply NR_edge; cbn; auto.
Qed.

(** O8.6: require ownership preservation; consequently every left delta is
    extensionally the identity. *)
Record R_ownpres_certificate (old : Gen3) (theta : @perm O2) : Prop :=
  mkOwnPres {
    ownpres_equal : perm_eq theta (g_own old)
  }.

Theorem R_ownpres_delta_identity : forall old theta,
  R_ownpres_certificate old theta ->
  perm_eq (delta theta (g_own old)) idO.
Proof.
  intros old theta H x. unfold delta, idO. cbn.
  rewrite (ownpres_equal H). apply pmap_pinv.
Qed.

Theorem R_ownpres_erases_O5_O7 : forall old theta,
  R_ownpres_certificate old theta ->
  forall x, pmap (delta theta (g_own old)) x = x.
Proof. intros old theta H x. exact (R_ownpres_delta_identity H x). Qed.

Theorem O8_exact_ablation :
  (lookup_rule (R_live_test_env env0 2) 2 = Some alpha0 /\
   R_live_template env0 2 1 live_self_use) /\
  (~ In BoundaryNaturality R_nobnd_features /\
   ~ In UniqueDeltaSource R_nobnd_features) /\
  (R_flatown_close env0 o0 alpha0_term <->
   R_flatown_close env3 o0 alpha1_term) /\
  (R_same_env_wf same_name_generations /\
   g_name alpha0 = g_name alpha1) /\
  (~ R_acyc_accept first_two_edges (nGamma,nAlpha)) /\
  (forall old theta, R_ownpres_certificate old theta ->
     perm_eq (delta theta (g_own old)) idO).
Proof.
  split.
  - split.
    + exact (proj1 R_live_breaks_O1).
    + exact (proj1 (proj2 R_live_breaks_O1)).
  - split.
    + split.
      * exact (proj1 (proj2 (proj2 (proj2 R_nobnd_loses_O2_O3)))).
      * exact (proj2 (proj2 (proj2 (proj2 R_nobnd_loses_O2_O3)))).
    + split.
      * exact (proj2 (proj2 R_flatown_collapses_O6)).
      * split.
        -- split.
           ++ exact (proj1 R_same_breaks_distinct_name_commitment).
           ++ exact (proj1 (proj2 R_same_breaks_distinct_name_commitment)).
        -- split.
           ++ exact R_acyc_rejects_third_resume.
           ++ exact R_ownpres_delta_identity.
Qed.

End OEBRC2173RunAblation.

(** ===== END MERGED SOURCE: OEBRC2173_RunAblation.v ===== *)

(** ===== BEGIN MERGED SOURCE: OEBRC2173_All.v ===== *)

Import OEBRC2173Core.
Import OEBRC2173Transitions.
Import OEBRC2173Model.
Import OEBRC2173RunAblation.

(** Aggregate kernel audit for the source's O0--O8 claims and its concrete
    consistency/non-triviality witness. *)
Check O0_finite_checkability.
Check O1_step_preserves_config.
Check excise_height.
Check excise_ownership.
Check excise_evaluation.
Check excise_subst_natural.
Check boundary_eval_unique.
Check delta_unique.
Check compiled_semantics_faithful.
Check O5_three_resumptions_are_legal.
Check O5_non_degenerate_holonomy.
Check O6_quantifier_formation_separation.
Check O7_no_path_flat_translation.
Check O8_exact_ablation.
Check closed_formula_has_model.
Check model_nontrivial.

Print Assumptions O0_finite_checkability.
Print Assumptions O1_step_preserves_config.
Print Assumptions excise_subst_natural.
Print Assumptions boundary_eval_unique.
Print Assumptions delta_unique.
Print Assumptions compiled_semantics_faithful.
Print Assumptions O5_three_resumptions_are_legal.
Print Assumptions O5_non_degenerate_holonomy.
Print Assumptions O6_quantifier_formation_separation.
Print Assumptions O7_no_path_flat_translation.
Print Assumptions O8_exact_ablation.
Print Assumptions closed_formula_has_model.
Print Assumptions model_nontrivial.

(** ===== END MERGED SOURCE: OEBRC2173_All.v ===== *)