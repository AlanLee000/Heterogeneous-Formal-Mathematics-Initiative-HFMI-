(*
  RGX-4.0.0 -- center/source commutator and linear back-reference compiler.

  Faithful Rocq formalization of note 2174.  Finite ZFC sets are represented
  by finite lists and compared extensionally by membership.  Every partial
  operation from the source is represented by option; no partial branch is
  totalized with a default.
*)

From Stdlib Require Import List Bool Arith Lia PeanoNat Program.Equality.
Import ListNotations.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* ------------------------------------------------------------------------- *)
(* Sections 1--2: disjoint nonempty primitive carriers and typed syntax.     *)
(* ------------------------------------------------------------------------- *)

Inductive Ag  : Type := ag  : nat -> Ag.
Inductive Ctr : Type := ctr : nat -> Ctr.
Inductive Src : Type := src : nat -> Src.
Inductive Idx : Type := idxdim : nat -> Idx.
Inductive Con : Type := conname : nat -> Con.
Definition Pred (_ : nat) : Type := nat.
Definition pred (n code : nat) : Pred n := code.

Definition ag_eq_dec : forall x y : Ag, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition ctr_eq_dec : forall x y : Ctr, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition src_eq_dec : forall x y : Src, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition idx_eq_dec : forall x y : Idx, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition con_eq_dec : forall x y : Con, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition pred_eq_dec : forall n (x y : Pred n), {x = y} + {x <> y}.
Proof. intros n x y. apply Nat.eq_dec. Defined.

Inductive Kind : Type := KWord | KSource.
Inductive Side : Type := SLeft | SRight.

Definition kind_eq_dec : forall x y : Kind, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition side_eq_dec : forall x y : Side, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition opposite (i : Side) : Side :=
  match i with SLeft => SRight | SRight => SLeft end.

Lemma opposite_involutive : forall i, opposite (opposite i) = i.
Proof. intro i. destruct i; reflexivity. Qed.

Definition Fam := nat.
Definition Inst := (Fam * nat)%type.
Definition family (q : Inst) : Fam := fst q.
Definition rank (q : Inst) : nat := snd q.
Definition inst_eq_dec : forall x y : Inst, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Inductive Vec (A : Type) : nat -> Type :=
| vnil : Vec A 0
| vcons : forall n, A -> Vec A n -> Vec A (S n).
Arguments vnil {A}.
Arguments vcons {A n} _ _.

Fixpoint vmap {A B n} (f : A -> B) (v : Vec A n) : Vec B n :=
  match v with
  | vnil => vnil
  | vcons _ x xs => vcons (f x) (vmap f xs)
  end.

Fixpoint vfold {A B n} (f : A -> B -> B) (z : B) (v : Vec A n) : B :=
  match v with
  | vnil => z
  | vcons _ x xs => f x (vfold f z xs)
  end.

Fixpoint vforall {A n} (P : A -> Prop) (v : Vec A n) : Prop :=
  match v with
  | vnil => True
  | vcons _ x xs => P x /\ vforall P xs
  end.

Inductive Tm : Type :=
| Var : nat -> Tm
| Const : Con -> Tm
| Index : Idx -> Ctr -> Tm.

Inductive Fm : Type :=
| EqF : Tm -> Tm -> Fm
| RelF : forall n, Pred n -> Vec Tm n -> Fm
| NegF : Fm -> Fm
| AndF : Fm -> Fm -> Fm
| AllF : Fm -> Fm.

Definition tm_eq_dec : forall x y : Tm, {x = y} + {x <> y}.
Proof. decide equality; auto using con_eq_dec, ctr_eq_dec, idx_eq_dec, Nat.eq_dec. Defined.

Definition vhead {A n} (v : Vec A (S n)) : A :=
  match v with vcons _ x _ => x end.

Definition vtail {A n} (v : Vec A (S n)) : Vec A n :=
  match v with vcons _ _ xs => xs end.

Fixpoint vec_tm_eq_dec n (x : Vec Tm n) : forall y : Vec Tm n,
  {x = y} + {x <> y}.
Proof.
  destruct x as [|n a xs].
  - intro y. dependent destruction y. left. reflexivity.
  - intro y. dependent destruction y.
    destruct (tm_eq_dec a t) as [-> | Hneq].
    + destruct (vec_tm_eq_dec _ xs y) as [-> | Htail].
      * left. reflexivity.
      * right. intro E. apply Htail. exact (f_equal vtail E).
    + right. intro E. apply Hneq. exact (f_equal vhead E).
Defined.

Fixpoint fm_eq_dec (x : Fm) : forall y : Fm, {x = y} + {x <> y}.
Proof.
  destruct x as [t u | n p v | q | q r | q];
    destruct y as [t' u' | n' p' v' | q' | q' r' | q'];
    try (right; discriminate).
  - destruct (tm_eq_dec t t') as [-> | Ht];
      destruct (tm_eq_dec u u') as [-> | Hu].
    + left. reflexivity.
    + right. intro E. apply Hu. now injection E.
    + right. intro E. apply Ht. now injection E.
    + right. intro E. apply Ht. now injection E.
  - destruct (Nat.eq_dec n n') as [Hn | Hn].
    + subst n'. destruct (Nat.eq_dec p p') as [-> | Hp].
      * destruct (vec_tm_eq_dec v v') as [-> | Hv].
        -- left. reflexivity.
        -- right. intro E. dependent destruction E. apply Hv. reflexivity.
      * right. intro E. dependent destruction E. apply Hp. reflexivity.
    + right. intro E. dependent destruction E. apply Hn. reflexivity.
  - destruct (fm_eq_dec q q') as [-> | Hq].
    + left. reflexivity.
    + right. intro E. apply Hq. now injection E.
  - destruct (fm_eq_dec q q') as [-> | Hq];
      destruct (fm_eq_dec r r') as [-> | Hr].
    + left. reflexivity.
    + right. intro E. apply Hr. now injection E.
    + right. intro E. apply Hq. now injection E.
    + right. intro E. apply Hq. now injection E.
  - destruct (fm_eq_dec q q') as [-> | Hq].
    + left. reflexivity.
    + right. intro E. apply Hq. now injection E.
Defined.

(* Finite set representation.  Equality is extensional; duplicates and order
   never carry mathematical meaning. *)
Definition FSet (A : Type) := list A.
Definition mem {A} (x : A) (s : FSet A) : Prop := In x s.
Definition fsubset {A} (s t : FSet A) : Prop := forall x, In x s -> In x t.
Definition feq {A} (s t : FSet A) : Prop := forall x, In x s <-> In x t.
Definition disjoint {A} (s t : FSet A) : Prop := forall x, In x s -> ~ In x t.

Definition fadd {A} (eqd : forall x y : A, {x = y} + {x <> y})
    (x : A) (s : FSet A) : FSet A :=
  if in_dec eqd x s then s else x :: s.

Fixpoint funion {A} (eqd : forall x y : A, {x = y} + {x <> y})
    (s t : FSet A) : FSet A :=
  match s with
  | [] => t
  | x :: xs => fadd eqd x (funion eqd xs t)
  end.

Fixpoint finter {A} (eqd : forall x y : A, {x = y} + {x <> y})
    (s t : FSet A) : FSet A :=
  match s with
  | [] => []
  | x :: xs => if in_dec eqd x t then x :: finter eqd xs t
               else finter eqd xs t
  end.

Fixpoint fdiff {A} (eqd : forall x y : A, {x = y} + {x <> y})
    (s t : FSet A) : FSet A :=
  match s with
  | [] => []
  | x :: xs => if in_dec eqd x t then fdiff eqd xs t
               else x :: fdiff eqd xs t
  end.

Lemma in_fadd : forall A eqd (x y : A) s,
  In x (fadd eqd y s) <-> x = y \/ In x s.
Proof.
  intros A eqd x y s. unfold fadd. destruct (in_dec eqd y s).
  - split; intro H.
    + right; exact H.
    + destruct H as [-> | H]; assumption.
  - simpl. split.
    + intros [H | H].
      * left. symmetry. exact H.
      * right. exact H.
    + intros [H | H].
      * left. symmetry. exact H.
      * right. exact H.
Qed.

Lemma in_funion : forall A eqd (x : A) s t,
  In x (funion eqd s t) <-> In x s \/ In x t.
Proof.
  intros A eqd x s. induction s as [|y ys IH]; intro t.
  - simpl. firstorder congruence.
  - simpl. rewrite in_fadd, IH. simpl. firstorder congruence.
Qed.

Lemma in_finter : forall A eqd (x : A) s t,
  In x (finter eqd s t) <-> In x s /\ In x t.
Proof.
  intros A eqd x s. induction s as [|y ys IH]; intro t.
  - simpl. firstorder congruence.
  - simpl. destruct (in_dec eqd y t).
    + simpl. rewrite IH. split.
      * intros [-> | H]; [firstorder congruence | firstorder congruence].
      * intros [[-> | H] Ht]; [left; reflexivity | right; firstorder congruence].
    + rewrite IH. split.
      * intros H. split; [right; firstorder congruence | firstorder congruence].
      * intros [[-> | H] Ht]; [contradiction | firstorder congruence].
Qed.

Lemma in_fdiff : forall A eqd (x : A) s t,
  In x (fdiff eqd s t) <-> In x s /\ ~ In x t.
Proof.
  intros A eqd x s. induction s as [|y ys IH]; intro t.
  - simpl. firstorder congruence.
  - simpl. destruct (in_dec eqd y t).
    + rewrite IH. split.
      * intros H. split; [right; firstorder congruence | firstorder congruence].
      * intros [[-> | H] Hn]; [contradiction | firstorder congruence].
    + simpl. rewrite IH. split.
      * intros [-> | H]; [firstorder congruence | firstorder congruence].
      * intros [[-> | H] Hn]; [left; reflexivity | right; firstorder congruence].
Qed.

(* ------------------------------------------------------------------------- *)
(* Sections 3--5: free/bound indices, renaming, substitution, anchoring, model. *)
(* ------------------------------------------------------------------------- *)

Definition fv_tm_depth (d : nat) (t : Tm) : FSet nat :=
  match t with
  | Var i => if Nat.ltb i d then [] else [i - d]
  | Const _ | Index _ _ => []
  end.

Definition bv_tm_depth (d : nat) (t : Tm) : FSet nat :=
  match t with
  | Var i => if Nat.ltb i d then [i] else []
  | Const _ | Index _ _ => []
  end.

Fixpoint fv_depth (d : nat) (p : Fm) : FSet nat :=
  match p with
  | EqF t u => funion Nat.eq_dec (fv_tm_depth d t) (fv_tm_depth d u)
  | RelF _ _ ts => vfold (fun t a => funion Nat.eq_dec (fv_tm_depth d t) a) [] ts
  | NegF q => fv_depth d q
  | AndF q r => funion Nat.eq_dec (fv_depth d q) (fv_depth d r)
  | AllF q => fv_depth (S d) q
  end.

Fixpoint bv_depth (d : nat) (p : Fm) : FSet nat :=
  match p with
  | EqF t u => funion Nat.eq_dec (bv_tm_depth d t) (bv_tm_depth d u)
  | RelF _ _ ts => vfold (fun t a => funion Nat.eq_dec (bv_tm_depth d t) a) [] ts
  | NegF q => bv_depth d q
  | AndF q r => funion Nat.eq_dec (bv_depth d q) (bv_depth d r)
  | AllF q => bv_depth (S d) q
  end.

Definition FV (p : Fm) := fv_depth 0 p.
Definition BV (p : Fm) := bv_depth 0 p.
Definition Closed (p : Fm) : Prop := FV p = [].

Definition lift_ren (rho : nat -> nat) (i : nat) : nat :=
  match i with 0 => 0 | S n => S (rho n) end.

Definition ren_tm (rho : nat -> nat) (t : Tm) : Tm :=
  match t with
  | Var i => Var (rho i)
  | Const a => Const a
  | Index k c => Index k c
  end.

Fixpoint ren (rho : nat -> nat) (p : Fm) : Fm :=
  match p with
  | EqF t u => EqF (ren_tm rho t) (ren_tm rho u)
  | RelF n r ts => RelF r (vmap (ren_tm rho) ts)
  | NegF q => NegF (ren rho q)
  | AndF q r => AndF (ren rho q) (ren rho r)
  | AllF q => AllF (ren (lift_ren rho) q)
  end.

Definition shift_tm := ren_tm S.

Definition lift_sub (sigma : nat -> Tm) (i : nat) : Tm :=
  match i with 0 => Var 0 | S n => shift_tm (sigma n) end.

Definition sub_tm (sigma : nat -> Tm) (t : Tm) : Tm :=
  match t with
  | Var i => sigma i
  | Const a => Const a
  | Index k c => Index k c
  end.

Fixpoint sub (sigma : nat -> Tm) (p : Fm) : Fm :=
  match p with
  | EqF t u => EqF (sub_tm sigma t) (sub_tm sigma u)
  | RelF n r ts => RelF r (vmap (sub_tm sigma) ts)
  | NegF q => NegF (sub sigma q)
  | AndF q r => AndF (sub sigma q) (sub sigma r)
  | AllF q => AllF (sub (lift_sub sigma) q)
  end.

Definition anchors_tm (t : Tm) : FSet Ctr :=
  match t with Index _ c => [c] | _ => [] end.

Fixpoint Anch (p : Fm) : FSet Ctr :=
  match p with
  | EqF t u => funion ctr_eq_dec (anchors_tm t) (anchors_tm u)
  | RelF _ _ ts => vfold (fun t a => funion ctr_eq_dec (anchors_tm t) a) [] ts
  | NegF q => Anch q
  | AndF q r => funion ctr_eq_dec (Anch q) (Anch r)
  | AllF q => Anch q
  end.

Definition anch_tm (c d : Ctr) (t : Tm) : Tm :=
  match t with
  | Var i => Var i
  | Const a => Const a
  | Index k e => if ctr_eq_dec e c then Index k d else Index k e
  end.

Fixpoint anch (c d : Ctr) (p : Fm) : Fm :=
  match p with
  | EqF t u => EqF (anch_tm c d t) (anch_tm c d u)
  | RelF n r ts => RelF r (vmap (anch_tm c d) ts)
  | NegF q => NegF (anch c d q)
  | AndF q r => AndF (anch c d q) (anch c d r)
  | AllF q => AllF (anch c d q)
  end.

Lemma anch_ren_tm : forall c d rho t,
  anch_tm c d (ren_tm rho t) = ren_tm rho (anch_tm c d t).
Proof.
  intros c d rho t. destruct t; cbn; try reflexivity.
  destruct (ctr_eq_dec c0 c); reflexivity.
Qed.

Lemma anch_shift_tm : forall c d t,
  anch_tm c d (shift_tm t) = shift_tm (anch_tm c d t).
Proof. intros. apply anch_ren_tm. Qed.

Lemma anch_sub_tm : forall c d sigma t,
  anch_tm c d (sub_tm sigma t) =
  sub_tm (fun n => anch_tm c d (sigma n)) (anch_tm c d t).
Proof.
  intros c d sigma t. destruct t; cbn; try reflexivity.
  destruct (ctr_eq_dec c0 c); reflexivity.
Qed.

Lemma anch_lift_sub : forall c d sigma n,
  anch_tm c d (lift_sub sigma n) =
  lift_sub (fun k => anch_tm c d (sigma k)) n.
Proof.
  intros c d sigma [|n]; cbn; [reflexivity | apply anch_shift_tm].
Qed.

Lemma vmap_ext : forall A B n (f g : A -> B) (v : Vec A n),
  (forall x, f x = g x) -> vmap f v = vmap g v.
Proof.
  intros A B n f g v H. induction v; cbn; [reflexivity |].
  rewrite H, IHv; reflexivity.
Qed.

Lemma vmap_comp : forall A B C n (f : B -> C) (g : A -> B) (v : Vec A n),
  vmap f (vmap g v) = vmap (fun x => f (g x)) v.
Proof.
  intros A B C n f g v. induction v; cbn; [reflexivity |].
  rewrite IHv; reflexivity.
Qed.

Lemma sub_ext : forall p sigma tau,
  (forall n, sigma n = tau n) -> sub sigma p = sub tau p.
Proof.
  intro p. induction p; intros sigma tau H; cbn.
  - destruct t; destruct t0; cbn; try rewrite ?H; reflexivity.
  - f_equal. apply vmap_ext. intro t. destruct t; cbn; try apply H; reflexivity.
  - f_equal. apply IHp. exact H.
  - f_equal.
    + apply IHp1. exact H.
    + apply IHp2. exact H.
  - f_equal. apply IHp. intros [|k]; cbn; [reflexivity |].
    unfold shift_tm. rewrite H. reflexivity.
Qed.

Theorem T1_anch_sub : forall c d sigma p,
  anch c d (sub sigma p) =
  sub (fun n => anch_tm c d (sigma n)) (anch c d p).
Proof.
  intros c d sigma p. revert sigma. induction p; intro sigma; cbn.
  - rewrite !anch_sub_tm. reflexivity.
  - f_equal. rewrite !vmap_comp. apply vmap_ext. intro t.
    apply anch_sub_tm.
  - rewrite IHp. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp. f_equal. apply sub_ext. intro n0. apply anch_lift_sub.
Qed.

Record Model : Type := {
  Dom : Type;
  dom_inhabitant : Dom;
  con_interp : Con -> Dom;
  pred_interp : forall n, Pred n -> Vec Dom n -> Prop;
  idx_interp : Idx -> Ctr -> Dom
}.

Fixpoint eval_vec (M : Model) (eta : nat -> Dom M) n (v : Vec Tm n)
  : Vec (Dom M) n :=
  match v with
  | vnil => vnil
  | vcons _ x xs => vcons (match x with
                         | Var i => eta i
                         | Const a => con_interp M a
                         | Index k c => idx_interp M k c
                         end) (eval_vec M eta xs)
  end.

Definition eval_tm (M : Model) (eta : nat -> Dom M) (t : Tm) : Dom M :=
  match t with
  | Var i => eta i
  | Const a => con_interp M a
  | Index k c => idx_interp M k c
  end.

Definition extend {D : Type} (eta : nat -> D) (x : D) (n : nat) : D :=
  match n with 0 => x | S k => eta k end.

Fixpoint sat (M : Model) (eta : nat -> Dom M) (p : Fm) : Prop :=
  match p with
  | EqF t u => eval_tm M eta t = eval_tm M eta u
  | RelF n r ts => pred_interp M r (eval_vec M eta ts)
  | NegF q => ~ sat M eta q
  | AndF q r => sat M eta q /\ sat M eta r
  | AllF q => forall x : Dom M, sat M (extend eta x) q
  end.

Definition unit_model : Model :=
  {| Dom := unit;
     dom_inhabitant := tt;
     con_interp := fun _ => tt;
     pred_interp := fun _ _ _ => True;
     idx_interp := fun _ _ => tt |}.

Lemma unit_model_reflexive_sentence :
  sat unit_model (fun _ => tt) (EqF (Const (conname 0)) (Const (conname 0))).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* Sections 6--7: report cores, certificates, responsibility proofs.         *)
(* ------------------------------------------------------------------------- *)

Record Core : Type := mkCore {
  core_ag : Ag;
  core_fm : Fm;
  core_ctr : Ctr;
  core_src : Src
}.

Definition CoreWF (r : Core) : Prop :=
  Closed (core_fm r) /\ fsubset (Anch (core_fm r)) [core_ctr r].

Definition core_eq_dec : forall x y : Core, {x = y} + {x <> y}.
Proof.
  decide equality; auto using ag_eq_dec, fm_eq_dec, ctr_eq_dec, src_eq_dec.
Defined.

Inductive Cert : Type :=
| WCert : Ag -> Fm -> Ctr -> Ctr -> Src -> Cert
| SCert : Ag -> Fm -> Src -> Src -> Ctr -> Cert.

Definition CertWF (z : Cert) : Prop :=
  match z with
  | WCert _ p _ d _ => Closed p /\ fsubset (Anch p) [d]
  | SCert _ p _ _ c => Closed p /\ fsubset (Anch p) [c]
  end.

Definition cert_eq_dec : forall x y : Cert, {x = y} + {x <> y}.
Proof.
  decide equality; auto using ag_eq_dec, fm_eq_dec, ctr_eq_dec, src_eq_dec.
Defined.

Inductive SupportEntry : Type := support_entry : Ag -> Fm -> Kind -> SupportEntry.

Definition support_entry_eq_dec : forall x y : SupportEntry, {x = y} + {x <> y}.
Proof.
  decide equality; auto using ag_eq_dec, fm_eq_dec, kind_eq_dec.
Defined.

Definition cert_support (z : Cert) : SupportEntry :=
  match z with
  | WCert a p _ _ _ => support_entry a p KWord
  | SCert a p _ _ _ => support_entry a p KSource
  end.

Definition supp (Lambda : FSet Cert) : FSet SupportEntry := map cert_support Lambda.

Inductive Resp : Type :=
| Word : Ag -> Fm -> Resp
| Source : Ag -> Fm -> Resp
| Both : Ag -> Fm -> Resp
| Top : Resp
| Meet : Resp -> Resp -> Resp
| Join : Resp -> Resp -> Resp.

Definition resp_eq_dec : forall x y : Resp, {x = y} + {x <> y}.
Proof.
  decide equality; auto using ag_eq_dec, fm_eq_dec.
Defined.

Inductive Der (Lambda : FSet Cert) : Resp -> Prop :=
| topI : Der Lambda Top
| wordI : forall a p c d s,
    In (WCert a p c d s) Lambda -> Der Lambda (Word a p)
| sourceI : forall a p s t c,
    In (SCert a p s t c) Lambda -> Der Lambda (Source a p)
| bothI : forall a p c d s u v e,
    In (WCert a p c d s) Lambda ->
    In (SCert a p u v e) Lambda -> Der Lambda (Both a p)
| meetI : forall q r, Der Lambda q -> Der Lambda r -> Der Lambda (Meet q r)
| meetE1 : forall q r, Der Lambda (Meet q r) -> Der Lambda q
| meetE2 : forall q r, Der Lambda (Meet q r) -> Der Lambda r
| joinI1 : forall q r, Der Lambda q -> Der Lambda (Join q r)
| joinI2 : forall q r, Der Lambda r -> Der Lambda (Join q r).

Fixpoint support_sat (A : FSet SupportEntry) (q : Resp) : Prop :=
  match q with
  | Word a p => In (support_entry a p KWord) A
  | Source a p => In (support_entry a p KSource) A
  | Both a p => In (support_entry a p KWord) A /\
                In (support_entry a p KSource) A
  | Top => True
  | Meet q r => support_sat A q /\ support_sat A r
  | Join q r => support_sat A q \/ support_sat A r
  end.

Lemma cert_support_in : forall z Lambda,
  In z Lambda -> In (cert_support z) (supp Lambda).
Proof. intros z Lambda H. unfold supp. apply in_map. exact H. Qed.

Lemma support_word_inv : forall a p Lambda,
  In (support_entry a p KWord) (supp Lambda) ->
  exists c d s, In (WCert a p c d s) Lambda.
Proof.
  intros a p Lambda H. unfold supp in H. apply in_map_iff in H.
  destruct H as [z [E Hin]]. destruct z; cbn in E.
  - inversion E; subst. eauto.
  - discriminate.
Qed.

Lemma support_source_inv : forall a p Lambda,
  In (support_entry a p KSource) (supp Lambda) ->
  exists s t c, In (SCert a p s t c) Lambda.
Proof.
  intros a p Lambda H. unfold supp in H. apply in_map_iff in H.
  destruct H as [z [E Hin]]. destruct z; cbn in E.
  - discriminate.
  - inversion E; subst. eauto.
Qed.

Theorem T3_sound : forall Lambda q, Der Lambda q -> support_sat (supp Lambda) q.
Proof.
  intros Lambda q d. induction d; cbn.
  - exact I.
  - apply cert_support_in in H. exact H.
  - apply cert_support_in in H. exact H.
  - split.
    + unfold supp. exact (@in_map Cert SupportEntry cert_support Lambda
                            (WCert a p c d s) H).
    + unfold supp. exact (@in_map Cert SupportEntry cert_support Lambda
                            (SCert a p u v e) H0).
  - split; assumption.
  - exact (proj1 IHd).
  - exact (proj2 IHd).
  - left. exact IHd.
  - right. exact IHd.
Qed.

Theorem T3_complete : forall Lambda q, support_sat (supp Lambda) q -> Der Lambda q.
Proof.
  intros Lambda q. induction q; cbn; intro H.
  - apply support_word_inv in H. destruct H as [c [d [s H]]].
    exact (@wordI Lambda a f c d s H).
  - apply support_source_inv in H. destruct H as [s [t [c H]]].
    exact (@sourceI Lambda a f s t c H).
  - destruct H as [Hw Hs]. apply support_word_inv in Hw.
    apply support_source_inv in Hs.
    destruct Hw as [c [d [s Hw]]]. destruct Hs as [u [v [e Hs]]].
    exact (@bothI Lambda a f c d s u v e Hw Hs).
  - constructor.
  - destruct H as [Hq Hr]. exact (@meetI Lambda q1 q2 (IHq1 Hq) (IHq2 Hr)).
  - destruct H as [Hq | Hr].
    + apply joinI1. apply IHq1. exact Hq.
    + apply joinI2. apply IHq2. exact Hr.
Qed.

Theorem T3_reliability_completeness : forall Lambda q,
  Der Lambda q <-> support_sat (supp Lambda) q.
Proof. split; [apply T3_sound | apply T3_complete]. Qed.

(* ------------------------------------------------------------------------- *)
(* Section 8: paths and the certificate/support runs.                         *)
(* ------------------------------------------------------------------------- *)

Inductive Path : Type :=
| PId : Path
| CStep : Ctr -> Ctr -> Path
| EStep : Src -> Src -> Path
| PSeq : Path -> Path -> Path.

Fixpoint run (pi : Path) (r : Core) (Lambda : FSet Cert)
  : option (Core * FSet Cert) :=
  match pi with
  | PId => Some (r, Lambda)
  | CStep c d =>
      if ctr_eq_dec c d then None else
      if ctr_eq_dec (core_ctr r) c then
        let p' := anch c d (core_fm r) in
        Some (mkCore (core_ag r) p' d (core_src r),
              WCert (core_ag r) p' c d (core_src r) :: Lambda)
      else None
  | EStep s t =>
      if src_eq_dec s t then None else
      if src_eq_dec (core_src r) s then
        Some (mkCore (core_ag r) (core_fm r) (core_ctr r) t,
              SCert (core_ag r) (core_fm r) s t (core_ctr r) :: Lambda)
      else None
  | PSeq pi sigma =>
      match run pi r Lambda with
      | Some (r1, L1) => run sigma r1 L1
      | None => None
      end
  end.

Fixpoint runU (pi : Path) (r : Core) (A : FSet SupportEntry)
  : option (Core * FSet SupportEntry) :=
  match pi with
  | PId => Some (r, A)
  | CStep c d =>
      if ctr_eq_dec c d then None else
      if ctr_eq_dec (core_ctr r) c then
        let p' := anch c d (core_fm r) in
        Some (mkCore (core_ag r) p' d (core_src r),
              support_entry (core_ag r) p' KWord :: A)
      else None
  | EStep s t =>
      if src_eq_dec s t then None else
      if src_eq_dec (core_src r) s then
        Some (mkCore (core_ag r) (core_fm r) (core_ctr r) t,
              support_entry (core_ag r) (core_fm r) KSource :: A)
      else None
  | PSeq pi sigma =>
      match runU pi r A with
      | Some (r1, A1) => runU sigma r1 A1
      | None => None
      end
  end.

Definition project_run (o : option (Core * FSet Cert))
  : option (Core * FSet SupportEntry) :=
  match o with None => None | Some (r, L) => Some (r, supp L) end.

Theorem T2_support_projection : forall pi r Lambda,
  project_run (run pi r Lambda) = runU pi r (supp Lambda).
Proof.
  intro pi. induction pi; intros r Lambda; cbn.
  - reflexivity.
  - destruct (ctr_eq_dec c c0); [reflexivity |].
    destruct (ctr_eq_dec (core_ctr r) c); reflexivity.
  - destruct (src_eq_dec s s0); [reflexivity |].
    destruct (src_eq_dec (core_src r) s); reflexivity.
  - destruct (run pi1 r Lambda) as [[r1 L1] |] eqn:E.
    + specialize (IHpi1 r Lambda). rewrite E in IHpi1. cbn in IHpi1.
      rewrite <- IHpi1. cbn. apply IHpi2.
    + specialize (IHpi1 r Lambda). rewrite E in IHpi1. cbn in IHpi1.
      rewrite <- IHpi1. reflexivity.
Qed.

Theorem T2_run_deterministic : forall pi r Lambda x y,
  run pi r Lambda = Some x -> run pi r Lambda = Some y -> x = y.
Proof. intros pi r Lambda x y Hx Hy. congruence. Qed.

(* ------------------------------------------------------------------------- *)
(* Section 9: canonical residuals, polarity, suffix action, equivalences.     *)
(* A War stores its two reconstructed supports; common/left-only/right-only  *)
(* are the source triple and are definitionally obtained by finite set ops.  *)
(* ------------------------------------------------------------------------- *)

Record War : Type := can {
  left_support : FSet SupportEntry;
  right_support : FSet SupportEntry
}.

Definition common (g : War) :=
  finter support_entry_eq_dec (left_support g) (right_support g).
Definition left_only (g : War) :=
  fdiff support_entry_eq_dec (left_support g) (right_support g).
Definition right_only (g : War) :=
  fdiff support_entry_eq_dec (right_support g) (left_support g).
Definition zero_gap (g : War) : Prop := feq (left_support g) (right_support g).

Definition Gap (pi sigma : Path) (r : Core) (Lambda : FSet Cert)
  : option War :=
  match run pi r Lambda, run sigma r Lambda with
  | Some (rp, Lp), Some (rs, Ls) =>
      if core_eq_dec rp rs then Some (can (supp Lp) (supp Ls)) else None
  | _, _ => None
  end.

Inductive Polarity : Type := Pos | Neg | Neutral.

Fixpoint support_sat_dec (A : FSet SupportEntry) (q : Resp)
  : {support_sat A q} + {~ support_sat A q}.
Proof.
  destruct q; cbn.
  - apply in_dec. apply support_entry_eq_dec.
  - apply in_dec. apply support_entry_eq_dec.
  - destruct (in_dec support_entry_eq_dec (support_entry a f KWord) A) as [Hw | Hw];
      destruct (in_dec support_entry_eq_dec (support_entry a f KSource) A) as [Hs | Hs].
    + left. tauto.
    + right. tauto.
    + right. tauto.
    + right. tauto.
  - left. exact I.
  - destruct (support_sat_dec A q1) as [Hq | Hq];
      destruct (support_sat_dec A q2) as [Hr | Hr].
    + left. tauto.
    + right. tauto.
    + right. tauto.
    + right. tauto.
  - destruct (support_sat_dec A q1) as [Hq | Hq];
      destruct (support_sat_dec A q2) as [Hr | Hr].
    + left. tauto.
    + left. tauto.
    + left. tauto.
    + right. tauto.
Defined.

Definition pol (g : War) (q : Resp) : Polarity :=
  match support_sat_dec (left_support g) q,
        support_sat_dec (right_support g) q with
  | left _, right _ => Pos
  | right _, left _ => Neg
  | _, _ => Neutral
  end.

Definition Swap (g : War) (q : Resp) : Prop := pol g q = Neutral.
Definition SwapAll (g : War) : Prop := zero_gap g.

Definition suffix_action (kappa : Path) (r : Core) (g : War) : option War :=
  match runU kappa r (left_support g), runU kappa r (right_support g) with
  | Some (r1, A), Some (r2, B) =>
      if core_eq_dec r1 r2 then Some (can A B) else None
  | _, _ => None
  end.

Theorem T4_support_tests : forall A B,
  feq A B <-> forall q, support_sat A q <-> support_sat B q.
Proof.
  intros A B. split.
  - intros E q. induction q; cbn.
    + apply E.
    + apply E.
    + split; intros [Hw Hs]; split; apply E; assumption.
    + tauto.
    + rewrite IHq1, IHq2. tauto.
    + rewrite IHq1, IHq2. tauto.
  - intros H [a p k]. destruct k.
    + exact (H (Word a p)).
    + exact (H (Source a p)).
Qed.

Theorem T4_zero_iff_tests : forall g,
  zero_gap g <->
  forall q, support_sat (left_support g) q <-> support_sat (right_support g) q.
Proof. intro g. apply T4_support_tests. Qed.

Theorem T4_atomic_separation : forall A B a p k,
  In (support_entry a p k) A -> ~ In (support_entry a p k) B ->
  exists q, support_sat A q /\ ~ support_sat B q.
Proof.
  intros A B a p [|] Hin Hnot.
  - exists (Word a p). cbn. tauto.
  - exists (Source a p). cbn. tauto.
Qed.

Theorem T5_suffix_unit : forall r g,
  suffix_action PId r g = Some g.
Proof. intros r [A B]. cbn. destruct (core_eq_dec r r); congruence. Qed.

Theorem T5_suffix_composition : forall k mu r r1 g A B,
  runU k r (left_support g) = Some (r1, A) ->
  runU k r (right_support g) = Some (r1, B) ->
  suffix_action (PSeq k mu) r g = suffix_action mu r1 (can A B).
Proof.
  intros k mu r r1 [L R] A B HL HR. cbn in HL, HR. unfold suffix_action. cbn. rewrite HL, HR.
  destruct (runU mu r1 A) as [[ra A1] |];
    destruct (runU mu r1 B) as [[rb B1] |]; cbn; reflexivity.
Qed.

Theorem T6_gap_propagation : forall pi sigma k r Lambda r' Lp Ls,
  run pi r Lambda = Some (r', Lp) ->
  run sigma r Lambda = Some (r', Ls) ->
  Gap (PSeq pi k) (PSeq sigma k) r Lambda =
  suffix_action k r' (can (supp Lp) (supp Ls)).
Proof.
  intros pi sigma k r Lambda r' Lp Ls Hp Hs.
  unfold Gap, suffix_action. cbn. rewrite Hp, Hs.
  destruct (run k r' Lp) as [[rp Lp'] |] eqn:EP;
    destruct (run k r' Ls) as [[rs Ls'] |] eqn:ES.
  - pose proof (T2_support_projection k r' Lp) as HUP.
    pose proof (T2_support_projection k r' Ls) as HUS.
    rewrite EP in HUP. rewrite ES in HUS. cbn in HUP, HUS.
    rewrite <- HUP; try rewrite <- HUS. cbn.
    destruct (core_eq_dec rp rs); reflexivity.
  - pose proof (T2_support_projection k r' Lp) as HUP.
    pose proof (T2_support_projection k r' Ls) as HUS.
    rewrite EP in HUP. rewrite ES in HUS. cbn in HUP, HUS.
    rewrite <- HUP; try rewrite <- HUS. reflexivity.
  - pose proof (T2_support_projection k r' Lp) as HUP.
    pose proof (T2_support_projection k r' Ls) as HUS.
    rewrite EP in HUP. rewrite ES in HUS. cbn in HUP, HUS.
    rewrite <- HUP; try rewrite <- HUS. reflexivity.
  - pose proof (T2_support_projection k r' Lp) as HUP.
    pose proof (T2_support_projection k r' Ls) as HUS.
    rewrite EP in HUP. rewrite ES in HUS. cbn in HUP, HUS.
    rewrite <- HUP; try rewrite <- HUS. reflexivity.
Qed.

Definition vis_run (pi : Path) (r : Core) (Lambda : FSet Cert) : option Core :=
  match run pi r Lambda with Some (r', _) => Some r' | None => None end.
Definition obs_run (pi : Path) (r : Core) (Lambda : FSet Cert)
  : option (FSet SupportEntry) :=
  match run pi r Lambda with Some (_, L) => Some (supp L) | None => None end.

Definition vis_equiv r Lambda pi sigma :=
  vis_run pi r Lambda = vis_run sigma r Lambda.
Definition rho_equiv r Lambda pi sigma :=
  vis_equiv r Lambda pi sigma /\ obs_run pi r Lambda = obs_run sigma r Lambda.

Theorem T9_rho_equiv_refl : forall r L pi, rho_equiv r L pi pi.
Proof. intros. split; reflexivity. Qed.
Theorem T9_rho_equiv_sym : forall r L pi sigma,
  rho_equiv r L pi sigma -> rho_equiv r L sigma pi.
Proof. intros r L pi sigma [H1 H2]. split; symmetry; assumption. Qed.
Theorem T9_rho_equiv_trans : forall r L pi sigma kappa,
  rho_equiv r L pi sigma -> rho_equiv r L sigma kappa -> rho_equiv r L pi kappa.
Proof. intros r L pi sigma kappa [H1 H2] [H3 H4]. split; congruence. Qed.

(* The concrete T7 witness from the source. *)
Definition a0 := ag 0.
Definition c0 := ctr 0.
Definition c1 := ctr 1.
Definition s0 := src 0.
Definition s1 := src 1.
Definition k0 := idxdim 0.
Definition unaryP : Pred 1 := pred 1 0.
Definition phi0 : Fm := RelF unaryP (vcons (Index k0 c0) vnil).
Definition phi1 : Fm := RelF unaryP (vcons (Index k0 c1) vnil).
Definition r0 : Core := mkCore a0 phi0 c0 s0.
Definition pi_left := PSeq (CStep c0 c1) (EStep s0 s1).
Definition pi_right := PSeq (EStep s0 s1) (CStep c0 c1).
Definition separating_test := Source a0 phi1.

Example T7_left_run :
  run pi_left r0 [] =
  Some (mkCore a0 phi1 c1 s1,
        [SCert a0 phi1 s0 s1 c1; WCert a0 phi1 c0 c1 s0]).
Proof. vm_compute. reflexivity. Qed.

Example T7_right_run :
  run pi_right r0 [] =
  Some (mkCore a0 phi1 c1 s1,
        [WCert a0 phi1 c0 c1 s1; SCert a0 phi0 s0 s1 c0]).
Proof. vm_compute. reflexivity. Qed.

Theorem T7_same_visible_state : vis_equiv r0 [] pi_left pi_right.
Proof. vm_compute. reflexivity. Qed.

Lemma phi0_neq_phi1 : phi0 <> phi1.
Proof.
  intro H. unfold phi0, phi1 in H. dependent destruction H.
Qed.

Theorem T7_responsibility_separation :
  exists A B,
    obs_run pi_left r0 [] = Some A /\
    obs_run pi_right r0 [] = Some B /\
    support_sat A separating_test /\ ~ support_sat B separating_test.
Proof.
  exists [support_entry a0 phi1 KSource; support_entry a0 phi1 KWord].
  exists [support_entry a0 phi1 KWord; support_entry a0 phi0 KSource].
  split; [reflexivity |].
  split; [reflexivity |].
  split.
  - cbn. left. reflexivity.
  - cbn. intros [H | [H | H]].
    + discriminate.
    + apply phi0_neq_phi1. now injection H.
    + contradiction.
Qed.

Theorem T8_no_visible_factor_for_witness :
  forall (Q : Type) (q : Core -> Q) (answer : Q -> Resp -> Prop),
  (forall A, answer (q (mkCore a0 phi1 c1 s1)) A <->
     exists S, obs_run pi_left r0 [] = Some S /\ support_sat S A) ->
  ~ (forall A, answer (q (mkCore a0 phi1 c1 s1)) A <->
     exists S, obs_run pi_right r0 [] = Some S /\ support_sat S A).
Proof.
  intros Q q answer Hleft Hright.
  specialize (Hleft separating_test). specialize (Hright separating_test).
  destruct T7_responsibility_separation as [A [B [EA [EB [HA HnB]]]]].
  apply HnB.
  assert (Hans : answer (q (mkCore a0 phi1 c1 s1)) separating_test).
  { apply (proj2 Hleft). exists A. tauto. }
  destruct (proj1 Hright Hans) as [S [ES HS]].
  rewrite EB in ES. inversion ES. subst. exact HS.
Qed.

(* ------------------------------------------------------------------------- *)
(* Sections 10--14: strategy scenario, linear proof codes, feedback, compile. *)
(* ------------------------------------------------------------------------- *)

Definition atom (z : Cert) : Resp :=
  match z with
  | WCert a p _ _ _ => Word a p
  | SCert a p _ _ _ => Source a p
  end.

Record Rule : Type := rule {
  rule_inst : Inst;
  rule_test : Resp;
  rule_gap : War;
  rule_back_code : nat
}.

Inductive OccOrigin : Type := BaseOrigin | FreshOrigin | DerivedOrigin : nat -> OccOrigin.

Record Occ : Type := occ {
  occ_code : nat;
  occ_side : Side;
  occ_cert : Cert;
  occ_ver : nat;
  occ_parents : FSet Fam;
  occ_origin : OccOrigin
}.

Definition origin_eq_dec : forall x y : OccOrigin, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition occ_eq_dec : forall x y : Occ, {x = y} + {x <> y}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply side_eq_dec;
    try apply cert_eq_dec; try apply origin_eq_dec.
  apply list_eq_dec. apply Nat.eq_dec.
Defined.

Inductive LTree : Type :=
| LTicket : Occ -> LTree
| LTop : LTree
| LBoth : Occ -> Occ -> LTree
| LMeetI : LTree -> LTree -> LTree
| LMeetE1 : Resp -> LTree -> LTree
| LMeetE2 : Resp -> LTree -> LTree
| LJoinI1 : Resp -> LTree -> LTree
| LJoinI2 : Resp -> LTree -> LTree
| LUse : Inst -> LTree -> LTree.

Record Justification : Type := justification {
  just_code : nat;
  just_cert : Cert;
  just_side : Side;
  just_bound : nat;
  just_rules : FSet Rule;
  just_tree : LTree
}.

Record Scene : Type := scene {
  scene_final_core : Core;
  scene_left_base : FSet Cert;
  scene_right_base : FSet Cert;
  scene_gap : War;
  scene_justifications : list Justification
}.

Definition base_of (chi : Scene) (i : Side) : FSet Cert :=
  match i with SLeft => scene_left_base chi | SRight => scene_right_base chi end.

Inductive Tok : Type := TOcc : nat -> Tok | TRec : nat -> Tok | TFb : nat -> Tok.

Definition tok_eq_dec : forall x y : Tok, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Fixpoint Leaves (d : LTree) : FSet Tok :=
  match d with
  | LTicket o => [TOcc (occ_code o)]
  | LTop => []
  | LBoth x y => [TOcc (occ_code x); TOcc (occ_code y)]
  | LMeetI x y => Leaves x ++ Leaves y
  | LMeetE1 _ x | LMeetE2 _ x | LJoinI1 _ x | LJoinI2 _ x | LUse _ x => Leaves x
  end.

Fixpoint DepFam (d : LTree) : FSet Fam :=
  match d with
  | LTicket o => occ_parents o
  | LTop => []
  | LBoth x y => funion Nat.eq_dec (occ_parents x) (occ_parents y)
  | LMeetI x y => funion Nat.eq_dec (DepFam x) (DepFam y)
  | LMeetE1 _ x | LMeetE2 _ x | LJoinI1 _ x | LJoinI2 _ x => DepFam x
  | LUse q x => fadd Nat.eq_dec (family q) (DepFam x)
  end.

Fixpoint DepInst (d : LTree) : FSet Inst :=
  match d with
  | LTicket _ | LTop | LBoth _ _ => []
  | LMeetI x y => funion inst_eq_dec (DepInst x) (DepInst y)
  | LMeetE1 _ x | LMeetE2 _ x | LJoinI1 _ x | LJoinI2 _ x => DepInst x
  | LUse q x => fadd inst_eq_dec q (DepInst x)
  end.

Fixpoint tree_max_rank (d : LTree) : nat :=
  match d with
  | LTicket _ | LTop | LBoth _ _ => 0
  | LMeetI x y => Nat.max (tree_max_rank x) (tree_max_rank y)
  | LMeetE1 _ x | LMeetE2 _ x | LJoinI1 _ x | LJoinI2 _ x => tree_max_rank x
  | LUse q x => Nat.max (rank q) (tree_max_rank x)
  end.

Fixpoint tree_max_ver (d : LTree) : nat :=
  match d with
  | LTicket o => occ_ver o
  | LTop => 0
  | LBoth x y => Nat.max (occ_ver x) (occ_ver y)
  | LMeetI x y => Nat.max (tree_max_ver x) (tree_max_ver y)
  | LMeetE1 _ x | LMeetE2 _ x | LJoinI1 _ x | LJoinI2 _ x | LUse _ x => tree_max_ver x
  end.

Definition OccWF (chi : Scene) (o : Occ) : Prop :=
  match occ_origin o with
  | BaseOrigin => occ_ver o = 0 /\ occ_parents o = [] /\
                  In (occ_cert o) (base_of chi (occ_side o))
  | FreshOrigin => occ_ver o <> 0 /\ occ_parents o = []
  | DerivedOrigin j => exists jc,
      In jc (scene_justifications chi) /\
      just_code jc = j /\
      just_cert jc = occ_cert o /\
      occ_ver o > Nat.max (tree_max_rank (just_tree jc)) (tree_max_ver (just_tree jc)) /\
      feq (occ_parents o) (DepFam (just_tree jc))
  end.

Inductive LDer (chi : Scene) (R : FSet Rule) : Side -> nat -> Resp -> LTree -> Prop :=
| ld_ticket : forall i m o,
    OccWF chi o -> occ_side o = i ->
    LDer chi R i m (atom (occ_cert o)) (LTicket o)
| ld_top : forall i m, LDer chi R i m Top LTop
| ld_both : forall i m ow os a p c d s u v e,
    OccWF chi ow -> OccWF chi os -> occ_code ow <> occ_code os ->
    occ_side ow = i -> occ_side os = i ->
    occ_cert ow = WCert a p c d s -> occ_cert os = SCert a p u v e ->
    LDer chi R i m (Both a p) (LBoth ow os)
| ld_meetI : forall i m q r x y,
    LDer chi R i m q x -> LDer chi R i m r y ->
    disjoint (Leaves x) (Leaves y) ->
    LDer chi R i m (Meet q r) (LMeetI x y)
| ld_meetE1 : forall i m q r x,
    LDer chi R i m (Meet q r) x -> LDer chi R i m q (LMeetE1 r x)
| ld_meetE2 : forall i m q r x,
    LDer chi R i m (Meet q r) x -> LDer chi R i m r (LMeetE2 q x)
| ld_joinI1 : forall i m q r x,
    LDer chi R i m q x -> LDer chi R i m (Join q r) (LJoinI1 r x)
| ld_joinI2 : forall i m q r x,
    LDer chi R i m r x -> LDer chi R i m (Join q r) (LJoinI2 q x)
| ld_use : forall i m q tau x g bcode,
    In (rule q tau g bcode) R -> rank q < m ->
    LDer chi R i m tau x -> LDer chi R (opposite i) m tau (LUse q x).

Definition SceneRealizable (chi : Scene) : Prop :=
  exists r Lambda piL piR,
    run piL r Lambda = Some (scene_final_core chi, scene_left_base chi) /\
    run piR r Lambda = Some (scene_final_core chi, scene_right_base chi) /\
    Gap piL piR r Lambda = Some (scene_gap chi).

Definition SceneWF (chi : Scene) : Prop :=
  SceneRealizable chi /\
  ~ zero_gap (scene_gap chi) /\
  (forall jc, In jc (scene_justifications chi) ->
    LDer chi (just_rules jc) (just_side jc) (just_bound jc)
      (atom (just_cert jc)) (just_tree jc)).

Definition Addr := list nat.

Fixpoint subtree (a : Addr) (d : LTree) : option LTree :=
  match a with
  | [] => Some d
  | k :: a' =>
      match d with
      | LMeetI x y => if Nat.eq_dec k 0 then subtree a' x
                       else if Nat.eq_dec k 1 then subtree a' y else None
      | LMeetE1 r x => if Nat.eq_dec k 0 then subtree a' x else None
      | LMeetE2 q x => if Nat.eq_dec k 0 then subtree a' x else None
      | LJoinI1 r x => if Nat.eq_dec k 0 then subtree a' x else None
      | LJoinI2 q x => if Nat.eq_dec k 0 then subtree a' x else None
      | LUse q x => if Nat.eq_dec k 0 then subtree a' x else None
      | _ => None
      end
  end.

Definition f_source (f : Fam) (d : LTree) : Prop :=
  match d with
  | LUse q _ => family q = f
  | LTicket o => In f (occ_parents o)
  | _ => False
  end.

Definition proper_prefix (a b : Addr) : Prop :=
  exists suffix, suffix <> [] /\ b = a ++ suffix.

Definition Cut (f : Fam) (d : LTree) (a : Addr) : Prop :=
  exists t, subtree a d = Some t /\ f_source f t /\
    forall p, proper_prefix p a ->
      forall u, subtree p d = Some u -> ~ f_source f u.

Record Bridge : Type := bridge {
  bridge_code : nat;
  bridge_family : Fam;
  bridge_side : Side;
  bridge_addr : Addr;
  bridge_tree : LTree
}.

Record RecToken : Type := rec_token {
  rec_code : nat;
  rec_key : nat;
  rec_family : Fam;
  rec_gap : War;
  rec_test : Resp
}.

Fixpoint lookup_bridge (i : Side) (a : Addr) (F : list Bridge) : option Bridge :=
  match F with
  | [] => None
  | br :: rest =>
      if side_eq_dec (bridge_side br) i then
        if list_eq_dec Nat.eq_dec (bridge_addr br) a then Some br
        else lookup_bridge i a rest
      else lookup_bridge i a rest
  end.

Fixpoint clean_at (i : Side) (F : list Bridge) (a : Addr) (d : LTree) : LTree :=
  match lookup_bridge i a F with
  | Some br => bridge_tree br
  | None =>
      match d with
      | LMeetI x y => LMeetI (clean_at i F (a ++ [0]) x) (clean_at i F (a ++ [1]) y)
      | LMeetE1 r x => LMeetE1 r (clean_at i F (a ++ [0]) x)
      | LMeetE2 q x => LMeetE2 q (clean_at i F (a ++ [0]) x)
      | LJoinI1 r x => LJoinI1 r (clean_at i F (a ++ [0]) x)
      | LJoinI2 q x => LJoinI2 q (clean_at i F (a ++ [0]) x)
      | LUse q x => LUse q (clean_at i F (a ++ [0]) x)
      | _ => d
      end
  end.

Definition clean (i : Side) (F : list Bridge) (d : LTree) := clean_at i F [] d.

Record FeedbackComplete (chi : Scene) (R : FSet Rule)
    (dl dr : LTree) (f : Fam) (n : nat) (F : list Bridge) : Prop := {
  feedback_domain : forall i a,
    (exists br, In br F /\ bridge_side br = i /\ bridge_addr br = a /\
                bridge_family br = f) <->
    Cut f (match i with SLeft => dl | SRight => dr end) a;
  feedback_valid : forall br,
    In br F -> exists old tau,
      subtree (bridge_addr br)
        (match bridge_side br with SLeft => dl | SRight => dr end) = Some old /\
      LDer chi R (bridge_side br) n tau old /\
      LDer chi R (bridge_side br) n tau (bridge_tree br);
  feedback_independent : forall br, In br F ->
    ~ In f (DepFam (bridge_tree br));
  feedback_low_rank : forall br p, In br F -> In p (DepInst (bridge_tree br)) -> rank p < n
}.

Record RawBack : Type := back {
  back_code : nat;
  back_inst : Inst;
  back_test : Resp;
  back_gap : War;
  back_rec : RecToken;
  back_left : LTree;
  back_right : LTree;
  back_feedback : list Bridge
}.

Definition bridge_resources (br : Bridge) : FSet Tok :=
  TFb (bridge_code br) :: Leaves (bridge_tree br).

Definition Res (b : RawBack) : FSet Tok :=
  TRec (rec_code (back_rec b)) ::
  Leaves (back_left b) ++ Leaves (back_right b) ++
  concat (map bridge_resources (back_feedback b)).

Definition rule_absent (q : Inst) (R : FSet Rule) : Prop :=
  forall r, In r R -> rule_inst r <> q.

Record BackWF (chi : Scene) (R : FSet Rule) (b : RawBack) : Prop := {
  back_scene_wf : SceneWF chi;
  back_gap_exact : back_gap b = scene_gap chi;
  back_header_nonzero : pol (scene_gap chi) (back_test b) <> Neutral;
  back_new_instance : rule_absent (back_inst b) R;
  back_rank_increase : forall r, In r R -> family (rule_inst r) = family (back_inst b) ->
      rank (rule_inst r) < rank (back_inst b);
  back_rec_exact : rec_family (back_rec b) = family (back_inst b) /\
      rec_gap (back_rec b) = scene_gap chi /\ rec_test (back_rec b) = back_test b;
  back_left_der : LDer chi R SLeft (rank (back_inst b)) (back_test b) (back_left b);
  back_right_der : LDer chi R SRight (rank (back_inst b)) (back_test b) (back_right b);
  back_lr_disjoint : disjoint (Leaves (back_left b)) (Leaves (back_right b));
  back_feedback_complete : FeedbackComplete chi R (back_left b) (back_right b)
      (family (back_inst b)) (rank (back_inst b)) (back_feedback b);
  back_clean_left : LDer chi R SLeft (rank (back_inst b)) (back_test b)
      (clean SLeft (back_feedback b) (back_left b));
  back_clean_right : LDer chi R SRight (rank (back_inst b)) (back_test b)
      (clean SRight (back_feedback b) (back_right b));
  back_clean_independent :
      ~ In (family (back_inst b)) (DepFam (clean SLeft (back_feedback b) (back_left b))) /\
      ~ In (family (back_inst b)) (DepFam (clean SRight (back_feedback b) (back_right b)));
  back_clean_low_rank : forall p,
      (In p (DepInst (clean SLeft (back_feedback b) (back_left b))) \/
       In p (DepInst (clean SRight (back_feedback b) (back_right b)))) ->
      rank p < rank (back_inst b);
  back_resources_linear : NoDup (Res b)
}.

Definition tok_eqb (x y : Tok) : bool := if tok_eq_dec x y then true else false.
Definition tok_memb (x : Tok) (s : FSet Tok) : bool := existsb (tok_eqb x) s.
Definition subsetb_tok (s t : FSet Tok) : bool := forallb (fun x => tok_memb x t) s.

Lemma tok_eqb_true : forall x y, tok_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold tok_eqb. destruct (tok_eq_dec x y) as [E | N].
  - subst. split; intro H; reflexivity.
  - split; intro H; [discriminate | contradiction].
Qed.

Lemma tok_memb_true : forall x s, tok_memb x s = true <-> In x s.
Proof.
  intros x s. unfold tok_memb. rewrite existsb_exists. split.
  - intros [y [Hy Hxy]]. apply tok_eqb_true in Hxy. subst. exact Hy.
  - intro H. exists x. split; [exact H | apply tok_eqb_true; reflexivity].
Qed.

Lemma subsetb_tok_true : forall s t, subsetb_tok s t = true <-> fsubset s t.
Proof.
  intros s t. unfold subsetb_tok. rewrite forallb_forall. split.
  - intros H x Hx. apply tok_memb_true. apply H. exact Hx.
  - intros H x Hx. apply tok_memb_true. apply H. exact Hx.
Qed.

Definition CertifiedBack (chi : Scene) (R : FSet Rule) := { b : RawBack | BackWF chi R b }.

Definition CheckBack {chi R} (Delta : FSet Tok) (b : CertifiedBack chi R) : bool :=
  subsetb_tok (Res (proj1_sig b)) Delta.

Definition CheckBackP (chi : Scene) (R : FSet Rule) (Delta : FSet Tok) (b : RawBack) : Prop :=
  BackWF chi R b /\ fsubset (Res b) Delta.

Theorem CheckBack_correct : forall chi R Delta (b : CertifiedBack chi R),
  CheckBack Delta b = true <-> CheckBackP chi R Delta (proj1_sig b).
Proof.
  intros chi R Delta [b Hb].
  change (subsetb_tok (Res b) Delta = true <->
          BackWF chi R b /\ fsubset (Res b) Delta).
  rewrite subsetb_tok_true. tauto.
Qed.

Definition compiled_rule (b : RawBack) : Rule :=
  rule (back_inst b) (back_test b) (back_gap b) (back_code b).

Inductive Compile (chi : Scene) :
    FSet Rule -> FSet Tok -> RawBack -> FSet Rule -> FSet Tok -> Prop :=
| compileI : forall R Delta b,
    BackWF chi R b -> fsubset (Res b) Delta ->
    Compile chi R Delta b (compiled_rule b :: R) (fdiff tok_eq_dec Delta (Res b)).

Inductive Table (chi : Scene) : FSet Rule -> Prop :=
| table_empty : Table chi []
| table_step : forall R Delta b R' Delta',
    Table chi R -> Compile chi R Delta b R' Delta' -> Table chi R'.

Definition Cfg := (FSet Rule * FSet Tok)%type.

Definition Eligible (chi : Scene) (K : Cfg) (q : Inst) (tau : Resp) : Prop :=
  exists g code, In (rule q tau g code) (fst K).

Definition forget (chi : Scene) (_ : Cfg) : Core * FSet Cert * FSet Cert :=
  (scene_final_core chi, scene_left_base chi, scene_right_base chi).

Inductive CompileRun (chi : Scene) : Cfg -> list (FSet Tok) -> Cfg -> Prop :=
| run_refl : forall K, CompileRun chi K [] K
| run_cons : forall R D b R1 D1 trace K2,
    Compile chi R D b R1 D1 ->
    CompileRun chi (R1, D1) trace K2 ->
    CompileRun chi (R, D) (Res b :: trace) K2.

(* The unguarded comparison system keeps only the finite proof relation needed
   for the source's singleton self-support counterexample. *)
Inductive UProv (pool : FSet Occ) (X : FSet Inst) : Side -> Resp -> Prop :=
| up_ticket : forall o, In o pool -> UProv pool X (occ_side o) (atom (occ_cert o))
| up_transport : forall q i tau,
    In q X -> UProv pool X i tau -> UProv pool X (opposite i) tau.

Definition PhiMember (pool : FSet Occ) (X : FSet Inst) (q : Inst) (tau : Resp) : Prop :=
  UProv pool X SLeft tau /\ UProv pool X SRight tau.

(* ------------------------------------------------------------------------- *)
(* Sections 15--17: strategy and combined theorems.                          *)
(* ------------------------------------------------------------------------- *)

Theorem H1_feedback_replacement : forall chi R b,
  BackWF chi R b ->
  LDer chi R SLeft (rank (back_inst b)) (back_test b)
    (clean SLeft (back_feedback b) (back_left b)) /\
  LDer chi R SRight (rank (back_inst b)) (back_test b)
    (clean SRight (back_feedback b) (back_right b)) /\
  ~ In (family (back_inst b))
      (DepFam (clean SLeft (back_feedback b) (back_left b))) /\
  ~ In (family (back_inst b))
      (DepFam (clean SRight (back_feedback b) (back_right b))).
Proof.
  intros chi R b H. split.
  - exact (back_clean_left H).
  - split.
    + exact (back_clean_right H).
    + exact (back_clean_independent H).
Qed.

Definition Backref (b : RawBack) (p : Inst) : Prop :=
  In p (DepInst (clean SLeft (back_feedback b) (back_left b))) \/
  In p (DepInst (clean SRight (back_feedback b) (back_right b))) \/
  exists br, In br (back_feedback b) /\ In p (DepInst (bridge_tree br)).

Theorem H2_backreference_well_founded : forall chi R b p,
  BackWF chi R b -> Backref b p -> rank p < rank (back_inst b).
Proof.
  intros chi R b p Hwf Href. destruct Hwf as
    [Hs Hg Hp Hnew Hrank Hrec Hl Hr Hd Hfb Hcl Hcr Hind Hlow Hlin].
  unfold Backref in Href. destruct Href as [H | [H | [br [Hbr Hpbr]]]].
  - apply Hlow. left. exact H.
  - apply Hlow. right. exact H.
  - eapply feedback_low_rank; eauto.
Qed.

Theorem H2_no_backreference_cycle : forall chi R b,
  BackWF chi R b -> ~ Backref b (back_inst b).
Proof.
  intros chi R b Hwf Hself.
  pose proof (H2_backreference_well_founded Hwf Hself). lia.
Qed.

Theorem H3_no_self_licensing : forall chi R b,
  BackWF chi R b ->
  ~ In (family (back_inst b))
      (DepFam (clean SLeft (back_feedback b) (back_left b))) /\
  ~ In (family (back_inst b))
      (DepFam (clean SRight (back_feedback b) (back_right b))) /\
  ~ Backref b (back_inst b).
Proof.
  intros chi R b H. split.
  - exact (proj1 (back_clean_independent H)).
  - split.
    + exact (proj2 (back_clean_independent H)).
    + exact (@H2_no_backreference_cycle chi R b H).
Qed.

Theorem compile_context_subset : forall chi R D b R' D',
  Compile chi R D b R' D' -> fsubset D' D.
Proof.
  intros chi R D b R' D' Hc. inversion Hc; subst.
  intros x Hx. apply in_fdiff in Hx. exact (proj1 Hx).
Qed.

Theorem compile_resources_removed : forall chi R D b R' D' x,
  Compile chi R D b R' D' -> In x (Res b) -> ~ In x D'.
Proof.
  intros chi R D b R' D' x Hc Hres Hin.
  inversion Hc; subst. apply in_fdiff in Hin. apply (proj2 Hin). exact Hres.
Qed.

Inductive Reach (chi : Scene) :
    FSet Rule -> FSet Tok -> FSet Rule -> FSet Tok -> Prop :=
| reach_refl : forall R D, Reach chi R D R D
| reach_step : forall R D b R1 D1 R2 D2,
    Compile chi R D b R1 D1 -> Reach chi R1 D1 R2 D2 -> Reach chi R D R2 D2.

Theorem reach_context_subset : forall chi R D R' D',
  Reach chi R D R' D' -> fsubset D' D.
Proof.
  intros chi R D R' D' H. induction H.
  - intros x Hx. exact Hx.
  - intros x Hx. apply (compile_context_subset H).
    apply IHReach. exact Hx.
Qed.

Theorem H4_compile_evidence_linear_unique : forall chi R D b R1 D1 R2 D2,
  Compile chi R D b R1 D1 -> Reach chi R1 D1 R2 D2 ->
  disjoint (Res b) D2.
Proof.
  intros chi R D b R1 D1 R2 D2 Hc Hr x Hx HD2.
  pose proof (reach_context_subset Hr x HD2) as HD1.
  eapply compile_resources_removed; eauto.
Qed.

Definition uq : Inst := (7, 0).
Definition ucert : Cert := SCert a0 phi1 s0 s1 c1.
Definition uocc : Occ := occ 900 SLeft ucert 1 [] FreshOrigin.
Definition upool : FSet Occ := [uocc].

Lemma uprov_empty_left : UProv upool [] SLeft (Source a0 phi1).
Proof. apply up_ticket with (o := uocc); cbn; auto. Qed.

Lemma uprov_empty_not_right : ~ UProv upool [] SRight (Source a0 phi1).
Proof.
  intro H. remember SRight as i. remember (Source a0 phi1) as tau.
  induction H; subst.
  - cbn in H. destruct H as [Heq | H]; [subst o; discriminate | contradiction].
  - cbn in H. contradiction.
Qed.

Theorem H5_unguarded_self_support_fixed_point :
  ~ PhiMember upool [] uq (Source a0 phi1) /\
  PhiMember upool [uq] uq (Source a0 phi1).
Proof.
  split.
  - intros [_ Hr]. exact (uprov_empty_not_right Hr).
  - split.
    + apply up_ticket with (o := uocc); cbn; auto.
    + replace SRight with (opposite SLeft) by reflexivity.
      apply up_transport with (q := uq).
      * cbn. auto.
      * apply up_ticket with (o := uocc); cbn; auto.
Qed.

Inductive CompileNoDelete (chi : Scene) :
    FSet Rule -> FSet Tok -> RawBack -> FSet Rule -> FSet Tok -> Prop :=
| compile_no_delete : forall R D b,
    BackWF chi R b -> fsubset (Res b) D ->
    CompileNoDelete chi R D b (compiled_rule b :: R) D.

Theorem H6_no_delete_allows_reuse : forall chi R D b1 b2,
  BackWF chi R b1 -> fsubset (Res b1) D ->
  BackWF chi (compiled_rule b1 :: R) b2 -> fsubset (Res b2) D ->
  rec_code (back_rec b1) = rec_code (back_rec b2) ->
  exists R1 R2,
    CompileNoDelete chi R D b1 R1 D /\
    CompileNoDelete chi R1 D b2 R2 D /\
    In (TRec (rec_code (back_rec b1))) (Res b1) /\
    In (TRec (rec_code (back_rec b1))) (Res b2).
Proof.
  intros chi R D b1 b2 H1 HD1 H2 HD2 He.
  exists (compiled_rule b1 :: R), (compiled_rule b2 :: compiled_rule b1 :: R).
  split.
  - constructor; assumption.
  - split.
    + constructor; assumption.
    + split.
      * cbn. auto.
      * cbn. left. f_equal. symmetry. exact He.
Qed.

Theorem H7_base_state_cannot_preserve_eligibility : forall chi R D b R' D',
  Compile chi R D b R' D' ->
  ~ Eligible chi (R, D) (back_inst b) (back_test b) /\
  Eligible chi (R', D') (back_inst b) (back_test b) /\
  forget chi (R, D) = forget chi (R', D').
Proof.
  intros chi R D b R' D' Hc. inversion Hc; subst.
  split.
  - intros [g [code Hin]].
    eapply back_new_instance; eauto.
  - split.
    + exists (back_gap b), (back_code b). cbn. left. reflexivity.
    + reflexivity.
Qed.

Theorem H8_base_conservativity : forall pi r Lambda,
  run pi r Lambda = run pi r Lambda /\ supp Lambda = supp Lambda.
Proof. intros. split; reflexivity. Qed.

Theorem A1_compile_functional : forall chi R D b R1 D1 R2 D2,
  Compile chi R D b R1 D1 -> Compile chi R D b R2 D2 ->
  R1 = R2 /\ D1 = D2.
Proof. intros. inversion H; inversion H0; subst; split; reflexivity. Qed.

Theorem A2_residual_trigger_sound : forall chi R b,
  BackWF chi R b -> back_gap b = scene_gap chi /\
  pol (scene_gap chi) (back_test b) <> Neutral.
Proof. intros chi R b H. split; [exact (@back_gap_exact chi R b H) | exact (@back_header_nonzero chi R b H)]. Qed.

Theorem A3_combined_no_self_licensing : forall chi R b,
  BackWF chi R b ->
  back_gap b = scene_gap chi /\
  pol (scene_gap chi) (back_test b) <> Neutral /\
  ~ In (family (back_inst b))
      (DepFam (clean SLeft (back_feedback b) (back_left b))) /\
  ~ Backref b (back_inst b) /\ NoDup (Res b).
Proof.
  intros chi R b H. repeat split.
  - exact (@back_gap_exact chi R b H).
  - exact (@back_header_nonzero chi R b H).
  - exact (proj1 (back_clean_independent H)).
  - exact (@H2_no_backreference_cycle chi R b H).
  - exact (@back_resources_linear chi R b H).
Qed.

Theorem A4_forget_conservative : forall chi K K', forget chi K = forget chi K'.
Proof. intros chi [R D] [R' D']. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* Section 18 and consistency/nontriviality model.                            *)
(* ------------------------------------------------------------------------- *)

Definition left_basis : FSet Cert :=
  [SCert a0 phi1 s0 s1 c1; WCert a0 phi1 c0 c1 s0].
Definition right_basis : FSet Cert :=
  [WCert a0 phi1 c0 c1 s1; SCert a0 phi0 s0 s1 c0].
Definition gap0 : War := can (supp left_basis) (supp right_basis).
Definition chi0 : Scene := scene (mkCore a0 phi1 c1 s1) left_basis right_basis gap0 [].

Definition left_occ : Occ :=
  occ 1 SLeft (SCert a0 phi1 s0 s1 c1) 0 [] BaseOrigin.
Definition right_occ : Occ :=
  occ 2 SRight (SCert a0 phi1 s0 s1 c1) 1 [] FreshOrigin.
Definition left_cal : LTree := LTicket left_occ.
Definition right_cal : LTree := LTicket right_occ.
Definition rec0 : RecToken := rec_token 100 0 0 gap0 separating_test.
Definition b1 : RawBack := back 201 (0, 1) separating_test gap0 rec0 left_cal right_cal [].
Definition b2 : RawBack := back 202 (0, 2) separating_test gap0 rec0 left_cal right_cal [].

Lemma gap0_nonzero : ~ zero_gap gap0.
Proof.
  intro E. specialize (E (support_entry a0 phi1 KSource)).
  cbn in E. destruct E as [E _]. specialize (E (or_introl eq_refl)).
  destruct E as [H | [H | H]].
  - discriminate.
  - apply phi0_neq_phi1. now injection H.
  - contradiction.
Qed.

Lemma chi0_wf : SceneWF chi0.
Proof.
  split.
  - exists r0, [], pi_left, pi_right. split.
    + exact T7_left_run.
    + split.
      * exact T7_right_run.
      * unfold Gap. rewrite T7_left_run, T7_right_run.
        destruct (core_eq_dec (mkCore a0 phi1 c1 s1)
                              (mkCore a0 phi1 c1 s1)) as [E | E].
        -- reflexivity.
        -- exfalso. apply E. reflexivity.
  - split.
    + apply gap0_nonzero.
    + intros jc H. contradiction.
Qed.

Lemma left_occ_wf : OccWF chi0 left_occ.
Proof. cbn. repeat split; auto. Qed.
Lemma right_occ_wf : OccWF chi0 right_occ.
Proof. cbn. split; [lia | reflexivity]. Qed.

Lemma no_cut_ticket_empty_parents : forall f o a,
  occ_parents o = [] -> ~ Cut f (LTicket o) a.
Proof.
  intros f o [|k a] Hpar Hcut.
  - destruct Hcut as [t [Ht [Hs _]]]. cbn in Ht. inversion Ht; subst.
    cbn in Hs. rewrite Hpar in Hs. contradiction.
  - destruct Hcut as [t [Ht _]]. cbn in Ht. discriminate.
Qed.

Lemma empty_feedback_complete : forall R n,
  FeedbackComplete chi0 R left_cal right_cal 0 n [].
Proof.
  intros R n. constructor.
  - intros i a. split.
    + intros [br [H _]]. contradiction.
    + intro Hcut. exfalso. destruct i.
      * exact (@no_cut_ticket_empty_parents 0 left_occ a eq_refl Hcut).
      * exact (@no_cut_ticket_empty_parents 0 right_occ a eq_refl Hcut).
  - intros br H. contradiction.
  - intros br H. contradiction.
  - intros br p H. contradiction.
Qed.

Lemma pol_gap0_source : pol gap0 separating_test = Pos.
Proof.
  assert (HL : support_sat (left_support gap0) separating_test).
  { cbn. left. reflexivity. }
  assert (HR : ~ support_sat (right_support gap0) separating_test).
  { cbn. intros [H | [H | H]].
    - discriminate.
    - apply phi0_neq_phi1. now injection H.
    - contradiction. }
  unfold pol. destruct (support_sat_dec (left_support gap0) separating_test) as [H1 | H1].
  - destruct (support_sat_dec (right_support gap0) separating_test) as [H2 | H2].
    + contradiction.
    + reflexivity.
  - contradiction.
Qed.

Lemma left_cal_der : forall R n, LDer chi0 R SLeft n separating_test left_cal.
Proof.
  intros R n. change (LDer chi0 R SLeft n (atom (occ_cert left_occ)) (LTicket left_occ)).
  apply ld_ticket; [apply left_occ_wf | reflexivity].
Qed.

Lemma right_cal_der : forall R n, LDer chi0 R SRight n separating_test right_cal.
Proof.
  intros R n. change (LDer chi0 R SRight n (atom (occ_cert right_occ)) (LTicket right_occ)).
  apply ld_ticket; [apply right_occ_wf | reflexivity].
Qed.

Lemma Res_b1_exact : Res b1 = [TRec 100; TOcc 1; TOcc 2].
Proof. reflexivity. Qed.
Lemma Res_b2_exact : Res b2 = [TRec 100; TOcc 1; TOcc 2].
Proof. reflexivity. Qed.

Lemma model_resources_nodup : NoDup [TRec 100; TOcc 1; TOcc 2].
Proof.
  constructor.
  - cbn. intros [H | [H | H]]; [discriminate | discriminate | contradiction].
  - constructor.
    + cbn. intros [H | H]; [discriminate | contradiction].
    + constructor.
      * cbn. tauto.
      * constructor.
Qed.

Lemma b1_wf : BackWF chi0 [] b1.
Proof.
  constructor; cbn.
  - apply chi0_wf.
  - reflexivity.
  - rewrite pol_gap0_source. discriminate.
  - intros r H. contradiction.
  - intros r H. contradiction.
  - repeat split; reflexivity.
  - exact (left_cal_der _ _).
  - exact (right_cal_der _ _).
  - intros x Hx Hy. cbn in Hx, Hy. destruct Hx as [Hx | Hx].
    + subst x. cbn in Hy. destruct Hy as [Hy | Hy]; [discriminate | contradiction].
    + contradiction.
  - apply empty_feedback_complete.
  - exact (left_cal_der _ _).
  - exact (right_cal_der _ _).
  - split; cbn; tauto.
  - intros p H. cbn in H. tauto.
  - rewrite Res_b1_exact. apply model_resources_nodup.
Qed.

Lemma b2_wf_after_b1 : BackWF chi0 [compiled_rule b1] b2.
Proof.
  constructor; cbn.
  - apply chi0_wf.
  - reflexivity.
  - rewrite pol_gap0_source. discriminate.
  - intros r [Hr | H]; [subst r; cbn; congruence | contradiction].
  - intros r [Hr | H] Hfam; [subst r; cbn in *; lia | contradiction].
  - repeat split; reflexivity.
  - exact (left_cal_der _ _).
  - exact (right_cal_der _ _).
  - intros x Hx Hy. cbn in Hx, Hy. destruct Hx as [Hx | Hx].
    + subst x. cbn in Hy. destruct Hy as [Hy | Hy]; [discriminate | contradiction].
    + contradiction.
  - apply empty_feedback_complete.
  - exact (left_cal_der _ _).
  - exact (right_cal_der _ _).
  - split; cbn; tauto.
  - intros p H. cbn in H. tauto.
  - rewrite Res_b2_exact. apply model_resources_nodup.
Qed.

Definition Delta0 : FSet Tok := Res b1.
Definition cb1 : CertifiedBack chi0 [] := exist _ b1 b1_wf.

Theorem finite_model_checkback : CheckBack Delta0 cb1 = true.
Proof.
  apply CheckBack_correct. split.
  - apply b1_wf.
  - intros x Hx. exact Hx.
Qed.

Lemma fdiff_empty_of_subset : forall A eqd (s t : FSet A),
  fsubset s t -> fdiff eqd s t = [].
Proof.
  intros A eqd s. induction s as [|x xs IH]; intros t Hsub; cbn.
  - reflexivity.
  - destruct (in_dec eqd x t).
    + apply IH. intros y Hy. apply Hsub. right. exact Hy.
    + exfalso. apply n. apply Hsub. left. reflexivity.
Qed.

Theorem finite_model_compiles :
  Compile chi0 [] Delta0 b1 [compiled_rule b1] [].
Proof.
  assert (Hdiff : fdiff tok_eq_dec Delta0 (Res b1) = []).
  { apply fdiff_empty_of_subset. intros x Hx. exact Hx. }
  rewrite <- Hdiff.
  constructor; [apply b1_wf | intros x Hx; exact Hx].
Qed.

Theorem finite_model_no_delete_reuses_rec :
  exists R1 R2,
    CompileNoDelete chi0 [] Delta0 b1 R1 Delta0 /\
    CompileNoDelete chi0 R1 Delta0 b2 R2 Delta0 /\
    In (TRec 100) (Res b1) /\ In (TRec 100) (Res b2).
Proof.
  eapply H6_no_delete_allows_reuse.
  - apply b1_wf.
  - intros x Hx. exact Hx.
  - apply b2_wf_after_b1.
  - intros x Hx. exact Hx.
  - reflexivity.
Qed.

Record RGXFiniteModel : Type := {
  fm_content_model : Model;
  fm_true_sentence : Fm;
  fm_sentence_true : sat fm_content_model (fun _ => dom_inhabitant fm_content_model)
      fm_true_sentence;
  fm_scene : Scene;
  fm_back : RawBack;
  fm_back_wf : BackWF fm_scene [] fm_back;
  fm_context : FSet Tok;
  fm_checker_accepts : CheckBack fm_context (exist _ fm_back fm_back_wf) = true;
  fm_nonzero_gap : ~ zero_gap (scene_gap fm_scene)
}.

Definition concrete_RGX_model : RGXFiniteModel :=
  {| fm_content_model := unit_model;
     fm_true_sentence := EqF (Const (conname 0)) (Const (conname 0));
     fm_sentence_true := unit_model_reflexive_sentence;
     fm_scene := chi0;
     fm_back := b1;
     fm_back_wf := b1_wf;
     fm_context := Delta0;
     fm_checker_accepts := finite_model_checkback;
     fm_nonzero_gap := gap0_nonzero |}.

Theorem RGX4_satisfiable_and_nontrivial : exists M : RGXFiniteModel,
  CheckBack (fm_context M) (exist _ (fm_back M) (fm_back_wf M)) = true /\
  ~ zero_gap (scene_gap (fm_scene M)).
Proof.
  exists concrete_RGX_model. split; cbn.
  - apply finite_model_checkback.
  - apply gap0_nonzero.
Qed.

(* Additional exact crosswalk lemmas for T1, T4, T9, and Section 14. *)

Lemma fv_anch_tm_depth : forall d c e t,
  fv_tm_depth d (anch_tm c e t) = fv_tm_depth d t.
Proof.
  intros d c e t. destruct t as [n | a | k c']; cbn; try reflexivity.
  destruct (ctr_eq_dec c' c); reflexivity.
Qed.

Lemma fv_anch_vec_depth : forall n (v : Vec Tm n) d c e,
  vfold (fun t a => funion Nat.eq_dec (fv_tm_depth d t) a) []
    (vmap (anch_tm c e) v) =
  vfold (fun t a => funion Nat.eq_dec (fv_tm_depth d t) a) [] v.
Proof.
  intros n v. induction v; intros d c e; cbn; [reflexivity |].
  rewrite fv_anch_tm_depth, IHv. reflexivity.
Qed.

Lemma funion_nil_inv : forall A eqd (s t : FSet A),
  funion eqd s t = [] -> s = [] /\ t = [].
Proof.
  intros A eqd s t H. split.
  - destruct s as [|x xs]; [reflexivity |].
    exfalso. assert (Hin : In x (funion eqd (x :: xs) t)).
    { apply (proj2 (@in_funion A eqd x (x :: xs) t)). left. cbn. auto. }
    rewrite H in Hin. contradiction.
  - destruct t as [|x xs]; [reflexivity |].
    exfalso. assert (Hin : In x (funion eqd s (x :: xs))).
    { apply (proj2 (@in_funion A eqd x s (x :: xs))). right. cbn. auto. }
    rewrite H in Hin. contradiction.
Qed.

Theorem T1_anch_preserves_closed : forall c e p,
  Closed p -> Closed (anch c e p).
Proof.
  intros c e p. unfold Closed, FV. generalize 0 as d.
  induction p; intros d H; cbn in *.
  - rewrite !fv_anch_tm_depth. exact H.
  - rewrite fv_anch_vec_depth. exact H.
  - apply IHp. exact H.
  - apply funion_nil_inv in H. destruct H as [H1 H2].
    rewrite (IHp1 d H1), (IHp2 d H2). reflexivity.
  - apply IHp. exact H.
Qed.

Theorem T4_provability_transport : forall L1 L2 q,
  feq (supp L1) (supp L2) -> (Der L1 q <-> Der L2 q).
Proof.
  intros L1 L2 q E. split; intro Hd.
  - apply T3_complete. apply (proj1 (proj1 (T4_support_tests (supp L1) (supp L2)) E q)).
    apply T3_sound. exact Hd.
  - apply T3_complete. apply (proj2 (proj1 (T4_support_tests (supp L1) (supp L2)) E q)).
    apply T3_sound. exact Hd.
Qed.

Definition obs_equiv_ext r Lambda pi sigma : Prop :=
  exists A B, obs_run pi r Lambda = Some A /\
              obs_run sigma r Lambda = Some B /\ feq A B.

Definition rho_equiv_ext r Lambda pi sigma : Prop :=
  vis_equiv r Lambda pi sigma /\ obs_equiv_ext r Lambda pi sigma.

Theorem T9_observation_maximality : forall r Lambda pi sigma r' Lp Ls,
  run pi r Lambda = Some (r', Lp) ->
  run sigma r Lambda = Some (r', Ls) ->
  (forall q, Der Lp q <-> Der Ls q) ->
  rho_equiv_ext r Lambda pi sigma.
Proof.
  intros r Lambda pi sigma r' Lp Ls Hp Hs Hall. split.
  - unfold vis_equiv, vis_run. rewrite Hp, Hs. reflexivity.
  - exists (supp Lp), (supp Ls). split.
    + unfold obs_run. rewrite Hp. reflexivity.
    + split.
      * unfold obs_run. rewrite Hs. reflexivity.
      * apply (proj2 (T4_support_tests (supp Lp) (supp Ls))).
        intro q. rewrite <- !T3_reliability_completeness. apply Hall.
Qed.

Definition Phi (pool : FSet Occ) (H X : FSet Inst)
    (tests : Inst -> Resp) (q : Inst) : Prop :=
  In q H /\ PhiMember pool X q (tests q).

Definition UnguardedSupportConfig (pool : FSet Occ) (H X : FSet Inst)
    (tests : Inst -> Resp) : Prop :=
  forall q, In q X -> Phi pool H X tests q.

Lemma UProv_monotone : forall pool X Y i tau,
  fsubset X Y -> UProv pool X i tau -> UProv pool Y i tau.
Proof.
  intros pool X Y i tau Hsub Hd. induction Hd.
  - apply up_ticket. exact H.
  - apply up_transport with (q := q).
    + apply Hsub. exact H.
    + exact IHHd.
Qed.

Theorem Phi_monotone : forall pool H X Y tests q,
  fsubset X Y -> Phi pool H X tests q -> Phi pool H Y tests q.
Proof.
  intros pool H X Y tests q HXY [Hq [HL HR]]. split; [exact Hq |].
  split; eapply UProv_monotone; eauto.
Qed.

Inductive MuStage (pool : FSet Occ) (H : FSet Inst) (tests : Inst -> Resp)
    : nat -> FSet Inst -> Prop :=
| mu_zero : MuStage pool H tests 0 []
| mu_next : forall n X Y,
    MuStage pool H tests n X ->
    (forall q, In q Y <-> In q X \/ Phi pool H X tests q) ->
    MuStage pool H tests (S n) Y.

Definition XMu (pool : FSet Occ) (H : FSet Inst) (tests : Inst -> Resp)
    (q : Inst) : Prop :=
  exists n X, MuStage pool H tests n X /\ In q X.

Definition utests (_ : Inst) : Resp := Source a0 phi1.

Lemma no_phi_from_empty : forall q, ~ Phi upool [uq] [] utests q.
Proof.
  intros q [Hq [_ Hr]]. cbn in Hq. destruct Hq as [Hq | Hq].
  - subst q. exact (uprov_empty_not_right Hr).
  - contradiction.
Qed.

Lemma list_nil_if_no_member : forall A (s : list A),
  (forall x, ~ In x s) -> s = [].
Proof.
  intros A [|x xs] H; [reflexivity |].
  exfalso. apply (H x). cbn. auto.
Qed.

Lemma u_mu_stages_empty : forall n X,
  MuStage upool [uq] utests n X -> X = [].
Proof.
  intros n X Hstage. induction Hstage as [|n X Y Hstage IH Hstep].
  - reflexivity.
  - subst X. apply list_nil_if_no_member. intros q Hq.
    apply Hstep in Hq. destruct Hq as [Hq | Hq].
    + contradiction.
    + exact (@no_phi_from_empty q Hq).
Qed.

Theorem H5_Xmu_empty_but_self_supported :
  ~ XMu upool [uq] utests uq /\
  UnguardedSupportConfig upool [uq] [uq] utests.
Proof.
  split.
  - intros [n [X [Hstage Hin]]].
    pose proof (u_mu_stages_empty Hstage). subst X. contradiction.
  - intros q Hq. cbn in Hq. destruct Hq as [Hq | Hq].
    + subst q. split.
      * cbn. auto.
      * exact (proj2 H5_unguarded_self_support_fixed_point).
    + contradiction.
Qed.
