(**
  Faithful Rocq formalization of
  "Reflexive Interpreter Holonomy Formal System HRISS v3.2".

  Source: 1817 反身解释器Holonomy形式系统-HRISS-v3.2-正式稿.md
  Target: Coq Platform 8.20.2025.01.

  The file deliberately contains no unfinished proof command, axiom, or
  opaque placeholder.  Source-section numbers are retained in comments so
  that HRISS_v3_2.faithfulness.md can give a line-accurate crosswalk.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Bool.Bool Lists.List Lia.
From Stdlib Require Import Relations Relation_Operators Relation_Definitions.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance Logic.ClassicalDescription
  Logic.ClassicalEpsilon Logic.Eqdep.
From Stdlib Require Import Program.Equality.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(** * 1.1  Finite name sets *)

Definition NameSet := list nat.
Definition ns_empty : NameSet := [].
Definition ns_singleton (i : nat) : NameSet := [i].
Definition ns_union (K L : NameSet) : NameSet := K ++ L.
Definition ns_remove (i : nat) (K : NameSet) : NameSet :=
  remove Nat.eq_dec i K.
Definition ns_same (K L : NameSet) : Prop :=
  forall i, In i K <-> In i L.
Definition Fresh (k : nat) (K : NameSet) : Prop := ~ In k K.
Definition FreshWit (K : NameSet) : Type := { k : nat | Fresh k K }.

Fixpoint ns_max (K : NameSet) : nat :=
  match K with
  | [] => 0
  | k :: K' => Nat.max k (ns_max K')
  end.

Definition fresh_name (K : NameSet) : nat := S (ns_max K).

Lemma in_ns_max_le : forall K k, In k K -> k <= ns_max K.
Proof.
  induction K as [|a K IHK]; intros k Hin.
  - contradiction.
  - cbn in *. destruct Hin as [<- | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IHK; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_name_spec : forall K, Fresh (fresh_name K) K.
Proof.
  intros K Hin. apply in_ns_max_le in Hin. unfold fresh_name in Hin. lia.
Qed.

Definition choose_fresh (K : NameSet) : FreshWit K :=
  exist _ (fresh_name K) (@fresh_name_spec K).

(** * 1.2  The concrete path group [S_3] *)

Inductive Perm3 : Type :=
| pid | sigma | tau | rho | cyc_p | cyc_q.

Definition perm3_eq_dec : forall g h : Perm3, {g = h} + {g <> h}.
Proof. decide equality. Defined.

(** Every permutation fixes names at least [3]. *)
Definition pact (g : Perm3) (i : nat) : nat :=
  match g, i with
  | pid, i => i
  | sigma, 0 => 1 | sigma, 1 => 0 | sigma, S (S n) => S (S n)
  | tau, 0 => 0 | tau, 1 => 2 | tau, 2 => 1
  | tau, S (S (S n)) => S (S (S n))
  | rho, 0 => 2 | rho, 1 => 1 | rho, 2 => 0
  | rho, S (S (S n)) => S (S (S n))
  | cyc_p, 0 => 1 | cyc_p, 1 => 2 | cyc_p, 2 => 0
  | cyc_p, S (S (S n)) => S (S (S n))
  | cyc_q, 0 => 2 | cyc_q, 1 => 0 | cyc_q, 2 => 1
  | cyc_q, S (S (S n)) => S (S (S n))
  end.

Definition perm_of_first_two (a b : nat) : Perm3 :=
  match a, b with
  | 0, 1 => pid
  | 1, 0 => sigma
  | 0, 2 => tau
  | 2, 1 => rho
  | 1, 2 => cyc_p
  | 2, 0 => cyc_q
  | _, _ => pid
  end.

(** [pmul g h] is function composition [g after h]. *)
Definition pmul (g h : Perm3) : Perm3 :=
  perm_of_first_two (pact g (pact h 0)) (pact g (pact h 1)).

Definition pinv (g : Perm3) : Perm3 :=
  match g with
  | pid => pid | sigma => sigma | tau => tau | rho => rho
  | cyc_p => cyc_q | cyc_q => cyc_p
  end.

Lemma pact_mul : forall g h i, pact (pmul g h) i = pact g (pact h i).
Proof.
  intros g h i. destruct g, h; destruct i as [|[|[|i]]]; reflexivity.
Qed.

Lemma pmul_assoc : forall g h k, pmul g (pmul h k) = pmul (pmul g h) k.
Proof. intros g h k. destruct g, h, k; reflexivity. Qed.

Lemma pmul_id_l : forall g, pmul pid g = g.
Proof. intros g. destruct g; reflexivity. Qed.

Lemma pmul_id_r : forall g, pmul g pid = g.
Proof. intros g. destruct g; reflexivity. Qed.

Lemma pmul_inv_l : forall g, pmul (pinv g) g = pid.
Proof. intros g. destruct g; reflexivity. Qed.

Lemma pmul_inv_r : forall g, pmul g (pinv g) = pid.
Proof. intros g. destruct g; reflexivity. Qed.

Lemma pact_inv_l : forall g i, pact (pinv g) (pact g i) = i.
Proof. intros g i. rewrite <- pact_mul, pmul_inv_l. reflexivity. Qed.

Lemma pact_inv_r : forall g i, pact g (pact (pinv g) i) = i.
Proof. intros g i. rewrite <- pact_mul, pmul_inv_r. reflexivity. Qed.

Lemma pact_injective : forall g i j, pact g i = pact g j -> i = j.
Proof.
  intros g i j Hij.
  apply (f_equal (pact (pinv g))) in Hij.
  now rewrite !pact_inv_l in Hij.
Qed.

Lemma p_at_0 : pact (pmul sigma tau) 0 = 1.
Proof. reflexivity. Qed.

Lemma q_at_0 : pact (pmul tau sigma) 0 = 2.
Proof. reflexivity. Qed.

Record Subgroup : Type := {
  hmem : Perm3 -> Prop;
  hmem_pid : hmem pid;
  hmem_mul : forall g h, hmem g -> hmem h -> hmem (pmul g h);
  hmem_inv : forall g, hmem g -> hmem (pinv g)
}.

Definition Hminus (H : Subgroup) (g : Perm3) : Prop :=
  hmem H g /\ g <> pid.

Definition H_nontrivial (H : Subgroup) : Prop := exists g, Hminus H g.

Definition trivial_subgroup : Subgroup.
Proof.
  refine {| hmem := fun g => g = pid |}.
  - reflexivity.
  - intros g h -> ->. reflexivity.
  - intros g ->. reflexivity.
Defined.

Definition full_subgroup : Subgroup.
Proof.
  refine {| hmem := fun _ => True |}; auto.
Defined.

Definition orbit0 (H : Subgroup) (i : nat) : Prop :=
  exists g, hmem H g /\ i = pact g 0.

Definition path_compatible (K : NameSet) (g h : Perm3) : Prop :=
  forall i, In i K -> pact g i = pact h i.

Definition Hol (g h : Perm3) (i : nat) : Prop := pact g i <> pact h i.

(** * 1.3  Arity-indexed object signature *)

Record Signature : Type := {
  TSym : nat -> Type;
  PSym : nat -> Type;
  LSym : nat -> Type;
  QSym : Type
}.

(** * 2  Raw finite syntax

  [Tm_H] and [Fm_H] are represented as raw trees together with the [wf_*]
  carrier predicates below.  This preserves proof-free strict tree equality:
  subgroup-membership evidence is not stored inside a syntax node.
*)

Inductive tm (Sig : Signature) : Type :=
| TVar : nat -> tm Sig
| TFun : forall n, TSym Sig n -> tml Sig n -> tm Sig
| TQuoteT : tm Sig -> tm Sig
| TQuoteF : fm Sig -> tm Sig
| TRApp : tm Sig -> tm Sig -> tm Sig
| TMove : Perm3 -> tm Sig
with fm (Sig : Signature) : Type :=
| FPred : forall n, PSym Sig n -> tml Sig n -> fm Sig
| FConn : forall n, LSym Sig n -> fml Sig n -> fm Sig
| FRApp : tm Sig -> fm Sig -> fm Sig
| FQuant : QSym Sig -> nat -> fm Sig -> fm Sig
with tml (Sig : Signature) : nat -> Type :=
| TNil : tml Sig 0
| TCons : forall n, tm Sig -> tml Sig n -> tml Sig (S n)
with fml (Sig : Signature) : nat -> Type :=
| FNil : fml Sig 0
| FCons : forall n, fm Sig -> fml Sig n -> fml Sig (S n).

Arguments TVar {Sig} _.
Arguments TFun {Sig n} _ _.
Arguments TQuoteT {Sig} _.
Arguments TQuoteF {Sig} _.
Arguments TRApp {Sig} _ _.
Arguments TMove {Sig} _.
Arguments FPred {Sig n} _ _.
Arguments FConn {Sig n} _ _.
Arguments FRApp {Sig} _ _.
Arguments FQuant {Sig} _ _ _.
Arguments TNil {Sig}.
Arguments TCons {Sig n} _ _.
Arguments FNil {Sig}.
Arguments FCons {Sig n} _ _.

Inductive sort := sortT | sortF.

Inductive expr (Sig : Signature) : Type :=
| ETerm : tm Sig -> expr Sig
| EForm : fm Sig -> expr Sig.

Arguments ETerm {Sig} _.
Arguments EForm {Sig} _.

Definition expr_sort {Sig} (z : expr Sig) : sort :=
  match z with ETerm _ => sortT | EForm _ => sortF end.

(** The carrier restrictions defining [Tm_H], [Fm_H], and [S_H]. *)
Fixpoint wf_tm (H : Subgroup) {Sig} (t : tm Sig) : Prop :=
  match t with
  | TVar _ => True
  | TFun _ xs => wf_tml H xs
  | TQuoteT u => wf_tm H u
  | TQuoteF p => wf_fm H p
  | TRApp u v => wf_tm H u /\ wf_tm H v
  | TMove g => Hminus H g
  end
with wf_fm (H : Subgroup) {Sig} (p : fm Sig) : Prop :=
  match p with
  | FPred _ xs => wf_tml H xs
  | FConn _ ps => wf_fml H ps
  | FRApp t q => wf_tm H t /\ wf_fm H q
  | FQuant _ _ q => wf_fm H q
  end
with wf_tml (H : Subgroup) {Sig n} (xs : tml Sig n) : Prop :=
  match xs with
  | TNil => True
  | TCons x xs' => wf_tm H x /\ wf_tml H xs'
  end
with wf_fml (H : Subgroup) {Sig n} (ps : fml Sig n) : Prop :=
  match ps with
  | FNil => True
  | FCons p ps' => wf_fm H p /\ wf_fml H ps'
  end.

Definition wf_expr (H : Subgroup) {Sig} (z : expr Sig) : Prop :=
  match z with ETerm t => wf_tm H t | EForm p => wf_fm H p end.

(** * 2.3  Height *)

Fixpoint tm_height {Sig} (t : tm Sig) : nat :=
  match t with
  | TVar _ => 0
  | TFun _ xs => match xs with TNil => 0 | TCons _ _ => S (tml_height xs) end
  | TQuoteT u => S (tm_height u)
  | TQuoteF p => S (fm_height p)
  | TRApp u v => S (Nat.max (tm_height u) (tm_height v))
  | TMove _ => 0
  end
with fm_height {Sig} (p : fm Sig) : nat :=
  match p with
  | FPred _ xs => match xs with TNil => 0 | TCons _ _ => S (tml_height xs) end
  | FConn _ ps => match ps with FNil => 0 | FCons _ _ => S (fml_height ps) end
  | FRApp t q => S (Nat.max (tm_height t) (fm_height q))
  | FQuant _ _ q => S (fm_height q)
  end
with tml_height {Sig n} (xs : tml Sig n) : nat :=
  match xs with
  | TNil => 0
  | TCons x TNil => tm_height x
  | TCons x xs' => Nat.max (tm_height x) (tml_height xs')
  end
with fml_height {Sig n} (ps : fml Sig n) : nat :=
  match ps with
  | FNil => 0
  | FCons p FNil => fm_height p
  | FCons p ps' => Nat.max (fm_height p) (fml_height ps')
  end.

Definition expr_height {Sig} (z : expr Sig) : nat :=
  match z with ETerm t => tm_height t | EForm p => fm_height p end.

(** * 3.1--3.4  FV, active BV, full support, and active names *)

Definition move_support (g : Perm3) : NameSet :=
  filter (fun i => negb (Nat.eqb (pact g i) i)) [0; 1; 2].

Set Warnings "-non-full-mutual".

Fixpoint FV_tm {Sig} (t : tm Sig) : NameSet :=
  match t with
  | TVar i => [i]
  | TFun _ xs => FV_tml xs
  | TQuoteT _ | TQuoteF _ => []
  | TRApp u _ => FV_tm u
  | TMove _ => []
  end
with FV_fm {Sig} (p : fm Sig) : NameSet :=
  match p with
  | FPred _ xs => FV_tml xs
  | FConn _ ps => FV_fml ps
  | FRApp t _ => FV_tm t
  | FQuant _ i q => ns_remove i (FV_fm q)
  end
with FV_tml {Sig n} (xs : tml Sig n) : NameSet :=
  match xs with
  | TNil => []
  | TCons x xs' => FV_tm x ++ FV_tml xs'
  end
with FV_fml {Sig n} (ps : fml Sig n) : NameSet :=
  match ps with
  | FNil => []
  | FCons p ps' => FV_fm p ++ FV_fml ps'
  end.

Fixpoint BV_tm {Sig} (t : tm Sig) : NameSet :=
  match t with
  | TVar _ | TMove _ => []
  | TFun _ xs => BV_tml xs
  | TQuoteT _ | TQuoteF _ => []
  | TRApp u _ => BV_tm u
  end
with BV_fm {Sig} (p : fm Sig) : NameSet :=
  match p with
  | FPred _ xs => BV_tml xs
  | FConn _ ps => BV_fml ps
  | FRApp t _ => BV_tm t
  | FQuant _ i q => i :: BV_fm q
  end
with BV_tml {Sig n} (xs : tml Sig n) : NameSet :=
  match xs with
  | TNil => []
  | TCons x xs' => BV_tm x ++ BV_tml xs'
  end
with BV_fml {Sig n} (ps : fml Sig n) : NameSet :=
  match ps with
  | FNil => []
  | FCons p ps' => BV_fm p ++ BV_fml ps'
  end.

Fixpoint Supp_tm {Sig} (t : tm Sig) : NameSet :=
  match t with
  | TVar i => [i]
  | TFun _ xs => Supp_tml xs
  | TQuoteT u => Supp_tm u
  | TQuoteF p => Supp_fm p
  | TRApp u v => Supp_tm u ++ Supp_tm v
  | TMove g => move_support g
  end
with Supp_fm {Sig} (p : fm Sig) : NameSet :=
  match p with
  | FPred _ xs => Supp_tml xs
  | FConn _ ps => Supp_fml ps
  | FRApp t q => Supp_tm t ++ Supp_fm q
  | FQuant _ i q => i :: Supp_fm q
  end
with Supp_tml {Sig n} (xs : tml Sig n) : NameSet :=
  match xs with
  | TNil => []
  | TCons x xs' => Supp_tm x ++ Supp_tml xs'
  end
with Supp_fml {Sig n} (ps : fml Sig n) : NameSet :=
  match ps with
  | FNil => []
  | FCons p ps' => Supp_fm p ++ Supp_fml ps'
  end.

Fixpoint AN_tm {Sig} (t : tm Sig) : NameSet :=
  match t with
  | TVar i => [i]
  | TFun _ xs => AN_tml xs
  | TQuoteT _ | TQuoteF _ => []
  | TRApp u _ => AN_tm u
  | TMove _ => []
  end
with AN_fm {Sig} (p : fm Sig) : NameSet :=
  match p with
  | FPred _ xs => AN_tml xs
  | FConn _ ps => AN_fml ps
  | FRApp t _ => AN_tm t
  | FQuant _ i q => i :: AN_fm q
  end
with AN_tml {Sig n} (xs : tml Sig n) : NameSet :=
  match xs with
  | TNil => []
  | TCons x xs' => AN_tm x ++ AN_tml xs'
  end
with AN_fml {Sig n} (ps : fml Sig n) : NameSet :=
  match ps with
  | FNil => []
  | FCons p ps' => AN_fm p ++ AN_fml ps'
  end.

Set Warnings "-non-full-mutual".

Definition FV {Sig} (z : expr Sig) : NameSet :=
  match z with ETerm t => FV_tm t | EForm p => FV_fm p end.
Definition BV {Sig} (z : expr Sig) : NameSet :=
  match z with ETerm t => BV_tm t | EForm p => BV_fm p end.
Definition Supp {Sig} (z : expr Sig) : NameSet :=
  match z with ETerm t => Supp_tm t | EForm p => Supp_fm p end.
Definition AN {Sig} (z : expr Sig) : NameSet :=
  match z with ETerm t => AN_tm t | EForm p => AN_fm p end.

(** * 3.5  Structural group action *)

Definition pconj (g a : Perm3) : Perm3 := pmul (pmul g a) (pinv g).

Fixpoint act_tm {Sig} (g : Perm3) (t : tm Sig) : tm Sig :=
  match t with
  | TVar i => TVar (pact g i)
  | TFun f xs => TFun f (act_tml g xs)
  | TQuoteT u => TQuoteT (act_tm g u)
  | TQuoteF p => TQuoteF (act_fm g p)
  | TRApp u v => TRApp (act_tm g u) (act_tm g v)
  | TMove a => TMove (pconj g a)
  end
with act_fm {Sig} (g : Perm3) (p : fm Sig) : fm Sig :=
  match p with
  | FPred r xs => FPred r (act_tml g xs)
  | FConn c ps => FConn c (act_fml g ps)
  | FRApp t q => FRApp (act_tm g t) (act_fm g q)
  | FQuant q i p' => FQuant q (pact g i) (act_fm g p')
  end
with act_tml {Sig n} (g : Perm3) (xs : tml Sig n) : tml Sig n :=
  match xs with
  | TNil => TNil
  | TCons x xs' => TCons (act_tm g x) (act_tml g xs')
  end
with act_fml {Sig n} (g : Perm3) (ps : fml Sig n) : fml Sig n :=
  match ps with
  | FNil => FNil
  | FCons p ps' => FCons (act_fm g p) (act_fml g ps')
  end.

Definition act_expr {Sig} (g : Perm3) (z : expr Sig) : expr Sig :=
  match z with ETerm t => ETerm (act_tm g t) | EForm p => EForm (act_fm g p) end.

Lemma pconj_nonid : forall g a, a <> pid -> pconj g a <> pid.
Proof. intros g a Ha. destruct g, a; cbn in *; congruence. Qed.

Lemma pconj_mem : forall H g a,
    hmem H g -> hmem H a -> hmem H (pconj g a).
Proof.
  intros H g a Hg Ha. unfold pconj.
  apply hmem_mul.
  - now apply hmem_mul.
  - now apply hmem_inv.
Qed.

Fixpoint wf_act_tm (H : Subgroup) {Sig} (g : Perm3) (Hg : hmem H g)
    (t : tm Sig) {struct t} : wf_tm H t -> wf_tm H (act_tm g t)
with wf_act_fm (H : Subgroup) {Sig} (g : Perm3) (Hg : hmem H g)
    (p : fm Sig) {struct p} : wf_fm H p -> wf_fm H (act_fm g p)
with wf_act_tml (H : Subgroup) {Sig n} (g : Perm3) (Hg : hmem H g)
    (xs : tml Sig n) {struct xs} : wf_tml H xs -> wf_tml H (act_tml g xs)
with wf_act_fml (H : Subgroup) {Sig n} (g : Perm3) (Hg : hmem H g)
    (ps : fml Sig n) {struct ps} : wf_fml H ps -> wf_fml H (act_fml g ps).
Proof.
  - destruct t; cbn; intro Hwf.
    + exact I.
    + now apply wf_act_tml.
    + now apply wf_act_tm.
    + now apply wf_act_fm.
    + destruct Hwf as [Hu Hv]. split; [now apply wf_act_tm | now apply wf_act_tm].
    + destruct Hwf as [Ha Hne]. split.
      * now apply pconj_mem.
      * now apply pconj_nonid.
  - destruct p; cbn; intro Hwf.
    + now apply wf_act_tml.
    + now apply wf_act_fml.
    + destruct Hwf as [Ht Hq]. split; [now apply wf_act_tm | now apply wf_act_fm].
    + now apply wf_act_fm.
  - destruct xs; cbn; intro Hwf.
    + exact I.
    + destruct Hwf as [Hx Hxs]. split; [now apply wf_act_tm | now apply wf_act_tml].
  - destruct ps; cbn; intro Hwf.
    + exact I.
    + destruct Hwf as [Hp Hps]. split; [now apply wf_act_fm | now apply wf_act_fml].
Defined.

Lemma wf_act_expr : forall H Sig g (Hg : hmem H g) (z : expr Sig),
    wf_expr H z -> wf_expr H (act_expr g z).
Proof.
  intros H Sig g Hg [t|p]; cbn; [apply wf_act_tm | apply wf_act_fm]; exact Hg.
Qed.

Fixpoint act_tm_id {Sig} (t : tm Sig) : act_tm pid t = t
with act_fm_id {Sig} (p : fm Sig) : act_fm pid p = p
with act_tml_id {Sig n} (xs : tml Sig n) : act_tml pid xs = xs
with act_fml_id {Sig n} (ps : fml Sig n) : act_fml pid ps = ps.
Proof.
  - destruct t; cbn.
    + reflexivity.
    + now rewrite act_tml_id.
    + now rewrite act_tm_id.
    + now rewrite act_fm_id.
    + now rewrite act_tm_id, act_tm_id.
    + destruct p; reflexivity.
  - destruct p; cbn.
    + now rewrite act_tml_id.
    + now rewrite act_fml_id.
    + now rewrite act_tm_id, act_fm_id.
    + now rewrite act_fm_id.
  - destruct xs; cbn.
    + reflexivity.
    + now rewrite act_tm_id, act_tml_id.
  - destruct ps; cbn.
    + reflexivity.
    + now rewrite act_fm_id, act_fml_id.
Qed.

Lemma pconj_mul : forall g h a,
    pconj g (pconj h a) = pconj (pmul g h) a.
Proof. intros g h a. destruct g, h, a; reflexivity. Qed.

Fixpoint act_tm_mul {Sig} (g h : Perm3) (t : tm Sig) :
    act_tm g (act_tm h t) = act_tm (pmul g h) t
with act_fm_mul {Sig} (g h : Perm3) (p : fm Sig) :
    act_fm g (act_fm h p) = act_fm (pmul g h) p
with act_tml_mul {Sig n} (g h : Perm3) (xs : tml Sig n) :
    act_tml g (act_tml h xs) = act_tml (pmul g h) xs
with act_fml_mul {Sig n} (g h : Perm3) (ps : fml Sig n) :
    act_fml g (act_fml h ps) = act_fml (pmul g h) ps.
Proof.
  - destruct t; cbn.
    + now rewrite pact_mul.
    + now rewrite act_tml_mul.
    + now rewrite act_tm_mul.
    + now rewrite act_fm_mul.
    + now rewrite act_tm_mul, act_tm_mul.
    + now rewrite pconj_mul.
  - destruct p; cbn.
    + now rewrite act_tml_mul.
    + now rewrite act_fml_mul.
    + now rewrite act_tm_mul, act_fm_mul.
    + now rewrite pact_mul, act_fm_mul.
  - destruct xs; cbn.
    + reflexivity.
    + now rewrite act_tm_mul, act_tml_mul.
  - destruct ps; cbn.
    + reflexivity.
    + now rewrite act_fm_mul, act_fml_mul.
Qed.

Lemma act_expr_id : forall Sig (z : expr Sig), act_expr pid z = z.
Proof. intros Sig [t|p]; cbn; [now rewrite act_tm_id | now rewrite act_fm_id]. Qed.

Lemma act_expr_mul : forall Sig g h (z : expr Sig),
    act_expr g (act_expr h z) = act_expr (pmul g h) z.
Proof. intros Sig g h [t|p]; cbn; [now rewrite act_tm_mul | now rewrite act_fm_mul]. Qed.

(** * 4.1  Raw substitution derivations *)

Inductive SubTm {Sig} (i : nat) (s : tm Sig) : tm Sig -> tm Sig -> Prop :=
| S_Hit : SubTm i s (TVar i) s
| S_Miss : forall j, j <> i -> SubTm i s (TVar j) (TVar j)
| S_Fun : forall n (f : TSym Sig n) xs xs',
    SubTml i s xs xs' -> SubTm i s (TFun f xs) (TFun f xs')
| S_QuoteT : forall t, SubTm i s (TQuoteT t) (TQuoteT t)
| S_QuoteF : forall p, SubTm i s (TQuoteF p) (TQuoteF p)
| S_RAppT : forall t t' u,
    SubTm i s t t' -> SubTm i s (TRApp t u) (TRApp t' u)
| S_Move : forall g, SubTm i s (TMove g) (TMove g)
with SubFm {Sig} (i : nat) (s : tm Sig) : fm Sig -> fm Sig -> Prop :=
| S_Pred : forall n (P : PSym Sig n) xs xs',
    SubTml i s xs xs' -> SubFm i s (FPred P xs) (FPred P xs')
| S_Conn : forall n (L : LSym Sig n) ps ps',
    SubFml i s ps ps' -> SubFm i s (FConn L ps) (FConn L ps')
| S_RAppF : forall t t' p,
    SubTm i s t t' -> SubFm i s (FRApp t p) (FRApp t' p)
| S_BindStop : forall Q p,
    SubFm i s (FQuant Q i p) (FQuant Q i p)
| S_BindPass : forall Q j p p',
    j <> i -> ~ In j (FV_tm s) -> SubFm i s p p' ->
    SubFm i s (FQuant Q j p) (FQuant Q j p')
with SubTml {Sig} (i : nat) (s : tm Sig) :
    forall n, tml Sig n -> tml Sig n -> Prop :=
| S_TNil : SubTml i s TNil TNil
| S_TCons : forall n (t t' : tm Sig) (xs xs' : tml Sig n),
    SubTm i s t t' -> SubTml i s xs xs' ->
    SubTml i s (TCons t xs) (TCons t' xs')
with SubFml {Sig} (i : nat) (s : tm Sig) :
    forall n, fml Sig n -> fml Sig n -> Prop :=
| S_FNil : SubFml i s FNil FNil
| S_FCons : forall n (p p' : fm Sig) (ps ps' : fml Sig n),
    SubFm i s p p' -> SubFml i s ps ps' ->
    SubFml i s (FCons p ps) (FCons p' ps').

Arguments S_Hit {Sig i s}.
Arguments S_Miss {Sig i s} _ _.

Inductive SubExpr {Sig} (i : nat) (s : tm Sig) :
    expr Sig -> expr Sig -> Prop :=
| S_ETerm : forall t t', SubTm i s t t' ->
    SubExpr i s (ETerm t) (ETerm t')
| S_EForm : forall p p', SubFm i s p p' ->
    SubExpr i s (EForm p) (EForm p').

(** * 4.2  Bounded active renaming derivations *)

Inductive BRenTmCore {Sig} (j k : nat) : tm Sig -> tm Sig -> Prop :=
| R_Hit : BRenTmCore j k (TVar j) (TVar k)
| R_Miss : forall ell, ell <> j ->
    BRenTmCore j k (TVar ell) (TVar ell)
| R_Fun : forall n (f : TSym Sig n) xs xs',
    BRenTmlCore j k xs xs' ->
    BRenTmCore j k (TFun f xs) (TFun f xs')
| R_QuoteT : forall t, BRenTmCore j k (TQuoteT t) (TQuoteT t)
| R_QuoteF : forall p, BRenTmCore j k (TQuoteF p) (TQuoteF p)
| R_RAppT : forall t t' u,
    BRenTmCore j k t t' ->
    BRenTmCore j k (TRApp t u) (TRApp t' u)
| R_Move : forall g, BRenTmCore j k (TMove g) (TMove g)
with BRenFmCore {Sig} (j k : nat) : fm Sig -> fm Sig -> Prop :=
| R_Pred : forall n (P : PSym Sig n) xs xs',
    BRenTmlCore j k xs xs' ->
    BRenFmCore j k (FPred P xs) (FPred P xs')
| R_Conn : forall n (L : LSym Sig n) ps ps',
    BRenFmlCore j k ps ps' ->
    BRenFmCore j k (FConn L ps) (FConn L ps')
| R_RAppF : forall t t' p,
    BRenTmCore j k t t' ->
    BRenFmCore j k (FRApp t p) (FRApp t' p)
| R_Shadow : forall Q p,
    BRenFmCore j k (FQuant Q j p) (FQuant Q j p)
| R_BindPass : forall Q ell p p',
    ell <> j -> ell <> k -> BRenFmCore j k p p' ->
    BRenFmCore j k (FQuant Q ell p) (FQuant Q ell p')
with BRenTmlCore {Sig} (j k : nat) :
    forall n, tml Sig n -> tml Sig n -> Prop :=
| R_TNil : BRenTmlCore j k TNil TNil
| R_TCons : forall n (t t' : tm Sig) (xs xs' : tml Sig n),
    BRenTmCore j k t t' -> BRenTmlCore j k xs xs' ->
    BRenTmlCore j k (TCons t xs) (TCons t' xs')
with BRenFmlCore {Sig} (j k : nat) :
    forall n, fml Sig n -> fml Sig n -> Prop :=
| R_FNil : BRenFmlCore j k FNil FNil
| R_FCons : forall n (p p' : fm Sig) (ps ps' : fml Sig n),
    BRenFmCore j k p p' -> BRenFmlCore j k ps ps' ->
    BRenFmlCore j k (FCons p ps) (FCons p' ps').

Definition BRenTm {Sig} (j k : nat) (t t' : tm Sig) : Prop :=
  j <> k /\ BRenTmCore j k t t'.
Definition BRenFm {Sig} (j k : nat) (p p' : fm Sig) : Prop :=
  j <> k /\ BRenFmCore j k p p'.
Definition BRenExpr {Sig} (j k : nat) (z z' : expr Sig) : Prop :=
  match z, z' with
  | ETerm t, ETerm t' => BRenTm j k t t'
  | EForm p, EForm p' => BRenFm j k p p'
  | _, _ => False
  end.

(** * 4.3  RootAlpha, active one-step Alpha, and AStar *)

Definition RootAlpha {Sig} (p q : fm Sig) : Prop :=
  exists (Q : QSym Sig) j k body body',
    p = FQuant Q j body /\
    q = FQuant Q k body' /\
    k <> j /\
    ~ In k (AN_fm body) /\
    BRenFm j k body body'.

Inductive Alpha {Sig} : fm Sig -> fm Sig -> Prop :=
| A_Root : forall p q, RootAlpha p q -> Alpha p q
| A_Conn : forall n (L : LSym Sig n) ps ps',
    AlphaFml ps ps' -> Alpha (FConn L ps) (FConn L ps')
| A_Bind : forall Q i p q,
    Alpha p q -> Alpha (FQuant Q i p) (FQuant Q i q)
with AlphaFml {Sig} : forall n, fml Sig n -> fml Sig n -> Prop :=
| A_Here : forall n p q (ps : fml Sig n),
    Alpha p q -> AlphaFml (FCons p ps) (FCons q ps)
| A_There : forall n p (ps qs : fml Sig n),
    AlphaFml ps qs -> AlphaFml (FCons p ps) (FCons p qs).

Inductive AStar {Sig} : expr Sig -> expr Sig -> Prop :=
| AS_Term : forall t, AStar (ETerm t) (ETerm t)
| AS_FormRefl : forall p, AStar (EForm p) (EForm p)
| AS_FormStep : forall p q r,
    Alpha p q -> AStar (EForm q) (EForm r) ->
    AStar (EForm p) (EForm r).

Lemma astar_term_iff : forall Sig (t u : tm Sig),
    AStar (ETerm t) (ETerm u) <-> t = u.
Proof.
  intros Sig t u. split.
  - intro H. inversion H. reflexivity.
  - intro Heq. subst u. constructor.
Qed.

Lemma astar_refl : forall Sig (z : expr Sig), AStar z z.
Proof. intros Sig [t|p]; constructor. Qed.

Lemma astar_trans : forall Sig (x y z : expr Sig),
    AStar x y -> AStar y z -> AStar x z.
Proof.
  intros Sig x y z Hxy Hyz. induction Hxy.
  - inversion Hyz. constructor.
  - exact Hyz.
  - destruct z as [t|f].
    + inversion Hyz.
    + eapply AS_FormStep.
      * exact H.
      * apply IHHxy. exact Hyz.
Qed.

(** * 4.4  Composite substitution and its typed finite witness *)

Inductive CSub {Sig} (i : nat) (s : tm Sig) :
    expr Sig -> expr Sig -> Prop :=
| CSub_intro : forall z z' u u',
    AStar z u -> SubExpr i s u u' -> AStar u' z' ->
    CSub i s z z'.

(** * 5  Path interface *)

Definition witness_support {Sig} (i : nat) (s : tm Sig)
    (z z' : expr Sig) : NameSet :=
  Supp z ++ Supp z' ++ Supp_tm s ++ [i].

Definition PathEq {Sig} (i : nat) (s : tm Sig) (z z' : expr Sig)
    (C : CSub i s z z') (g h : Perm3) : Prop :=
  path_compatible (witness_support i s z z') g h.

Lemma path_eq_only_rule : forall Sig i (s : tm Sig) z z'
    (C : @CSub Sig i s z z') g h,
    PathEq C g h <->
    path_compatible (witness_support i s z z') g h.
Proof. reflexivity. Qed.

(** * 4.5  Exact transport of derivation witnesses *)

Lemma in_ns_remove_iff : forall i j K,
    In i (ns_remove j K) <-> In i K /\ i <> j.
Proof.
  intros i j K. unfold ns_remove. induction K as [|a K IHK]; cbn.
  - tauto.
  - destruct (Nat.eq_dec j a) as [->|Hja].
    + rewrite IHK. split.
      * intros [Hin Hne]. split; [now right | exact Hne].
      * intros [[<-|Hin] Hne]; [contradiction | tauto].
    + cbn. rewrite IHK. split.
      * intros [<- | [Hin Hne]].
        -- split; [now left | congruence].
        -- split; [now right | exact Hne].
      * intros [[<- | Hin] Hne].
        -- now left.
        -- right. tauto.
Qed.

Lemma pact_inverse_eq : forall g x i,
    pact (pinv g) x = i <-> x = pact g i.
Proof.
  intros g x i. split; intro H.
  - apply (f_equal (pact g)) in H. now rewrite pact_inv_r in H.
  - subst x. apply pact_inv_l.
Qed.

Lemma pact_eq_inverse : forall g i x,
    pact g i = x <-> i = pact (pinv g) x.
Proof.
  intros g i x. split; intro H.
  - apply (f_equal (pact (pinv g))) in H. now rewrite pact_inv_l in H.
  - subst i. apply pact_inv_r.
Qed.

Set Warnings "-non-full-mutual".

Fixpoint FV_act_tm_iff {Sig} (g : Perm3) (t : tm Sig) (x : nat) {struct t} :
    In x (FV_tm (act_tm g t)) <-> In (pact (pinv g) x) (FV_tm t)
with FV_act_fm_iff {Sig} (g : Perm3) (p : fm Sig) (x : nat) {struct p} :
    In x (FV_fm (act_fm g p)) <-> In (pact (pinv g) x) (FV_fm p)
with FV_act_tml_iff {Sig n} (g : Perm3) (xs : tml Sig n) (x : nat) {struct xs} :
    In x (FV_tml (act_tml g xs)) <-> In (pact (pinv g) x) (FV_tml xs)
with FV_act_fml_iff {Sig n} (g : Perm3) (ps : fml Sig n) (x : nat) {struct ps} :
    In x (FV_fml (act_fml g ps)) <-> In (pact (pinv g) x) (FV_fml ps).
Proof.
  - destruct t; cbn.
    + rewrite pact_eq_inverse. tauto.
    + apply FV_act_tml_iff.
    + tauto.
    + tauto.
    + apply FV_act_tm_iff.
    + tauto.
  - destruct p; cbn.
    + apply FV_act_tml_iff.
    + apply FV_act_fml_iff.
    + apply FV_act_tm_iff.
    + rewrite !in_ns_remove_iff, FV_act_fm_iff.
      split.
      * intros [Hin Hne]. split; [exact Hin|].
        intro Heq. apply Hne. apply pact_inverse_eq in Heq. exact Heq.
      * intros [Hin Hne]. split; [exact Hin|].
        intro Heq. apply Hne. apply pact_inverse_eq. exact Heq.
  - destruct xs; cbn.
    + tauto.
    + rewrite !in_app_iff, FV_act_tm_iff, FV_act_tml_iff. tauto.
  - destruct ps; cbn.
    + tauto.
    + rewrite !in_app_iff, FV_act_fm_iff, FV_act_fml_iff. tauto.
Defined.

Fixpoint AN_act_tm_iff {Sig} (g : Perm3) (t : tm Sig) (x : nat) {struct t} :
    In x (AN_tm (act_tm g t)) <-> In (pact (pinv g) x) (AN_tm t)
with AN_act_fm_iff {Sig} (g : Perm3) (p : fm Sig) (x : nat) {struct p} :
    In x (AN_fm (act_fm g p)) <-> In (pact (pinv g) x) (AN_fm p)
with AN_act_tml_iff {Sig n} (g : Perm3) (xs : tml Sig n) (x : nat) {struct xs} :
    In x (AN_tml (act_tml g xs)) <-> In (pact (pinv g) x) (AN_tml xs)
with AN_act_fml_iff {Sig n} (g : Perm3) (ps : fml Sig n) (x : nat) {struct ps} :
    In x (AN_fml (act_fml g ps)) <-> In (pact (pinv g) x) (AN_fml ps).
Proof.
  - destruct t; cbn.
    + rewrite pact_eq_inverse. tauto.
    + apply AN_act_tml_iff.
    + tauto.
    + tauto.
    + apply AN_act_tm_iff.
    + tauto.
  - destruct p; cbn.
    + apply AN_act_tml_iff.
    + apply AN_act_fml_iff.
    + apply AN_act_tm_iff.
    + rewrite AN_act_fm_iff, pact_eq_inverse. tauto.
  - destruct xs; cbn.
    + tauto.
    + rewrite !in_app_iff, AN_act_tm_iff, AN_act_tml_iff. tauto.
  - destruct ps; cbn.
    + tauto.
    + rewrite !in_app_iff, AN_act_fm_iff, AN_act_fml_iff. tauto.
Defined.

Set Warnings "-non-full-mutual".

Fixpoint transport_SubTm {Sig} (g : Perm3) i (s : tm Sig) t t'
    (D : SubTm i s t t') {struct D} :
    SubTm (pact g i) (act_tm g s) (act_tm g t) (act_tm g t')
with transport_SubFm {Sig} (g : Perm3) i (s : tm Sig) p p'
    (D : SubFm i s p p') {struct D} :
    SubFm (pact g i) (act_tm g s) (act_fm g p) (act_fm g p')
with transport_SubTml {Sig} (g : Perm3) i (s : tm Sig) n
    (xs xs' : tml Sig n) (D : SubTml i s xs xs') {struct D} :
    SubTml (pact g i) (act_tm g s) (act_tml g xs) (act_tml g xs')
with transport_SubFml {Sig} (g : Perm3) i (s : tm Sig) n
    (ps ps' : fml Sig n) (D : SubFml i s ps ps') {struct D} :
    SubFml (pact g i) (act_tm g s) (act_fml g ps) (act_fml g ps').
Proof.
  - destruct D as [|j Hji|n f xs xs' Dxs|t|p|t t' u Dt|a]; cbn.
    + constructor.
    + apply S_Miss. intro Heq. apply Hji. eapply pact_injective. exact Heq.
    + constructor. now apply transport_SubTml.
    + constructor.
    + constructor.
    + constructor. now apply transport_SubTm.
    + constructor.
  - destruct D as
      [n P xs xs' Dxs|n L ps ps' Dps|t t' p Dt|Q p|
       Q j p p' Hji Hfresh Dp]; cbn.
    + constructor. now apply transport_SubTml.
    + constructor. now apply transport_SubFml.
    + constructor. now apply transport_SubTm.
    + constructor.
    + apply S_BindPass.
      * intro Heq. apply Hji. eapply pact_injective. exact Heq.
      * intro Hin. apply (FV_act_tm_iff g s (pact g j)) in Hin.
        rewrite pact_inv_l in Hin. contradiction.
      * now apply transport_SubFm.
  - destruct D as [|n t t' xs xs' Dt Dxs]; cbn.
    + constructor.
    + constructor; [now apply transport_SubTm | now apply transport_SubTml].
  - destruct D as [|n p p' ps ps' Dp Dps]; cbn.
    + constructor.
    + constructor; [now apply transport_SubFm | now apply transport_SubFml].
Defined.

Definition transport_SubExpr {Sig} (g : Perm3) i (s : tm Sig) z z'
    (D : SubExpr i s z z') :
    SubExpr (pact g i) (act_tm g s) (act_expr g z) (act_expr g z').
Proof.
  destruct D; cbn; constructor.
  - now apply transport_SubTm.
  - now apply transport_SubFm.
Defined.

Fixpoint transport_BRenTmCore {Sig} (g : Perm3) j k (t t' : tm Sig)
    (D : BRenTmCore j k t t') {struct D} :
    BRenTmCore (pact g j) (pact g k) (act_tm g t) (act_tm g t')
with transport_BRenFmCore {Sig} (g : Perm3) j k (p p' : fm Sig)
    (D : BRenFmCore j k p p') {struct D} :
    BRenFmCore (pact g j) (pact g k) (act_fm g p) (act_fm g p')
with transport_BRenTmlCore {Sig} (g : Perm3) j k n
    (xs xs' : tml Sig n) (D : BRenTmlCore j k xs xs') {struct D} :
    BRenTmlCore (pact g j) (pact g k) (act_tml g xs) (act_tml g xs')
with transport_BRenFmlCore {Sig} (g : Perm3) j k n
    (ps ps' : fml Sig n) (D : BRenFmlCore j k ps ps') {struct D} :
    BRenFmlCore (pact g j) (pact g k) (act_fml g ps) (act_fml g ps').
Proof.
  - destruct D as [|ell Hell|n f xs xs' Dxs|t|p|t t' u Dt|a]; cbn.
    + constructor.
    + apply R_Miss. intro Heq. apply Hell. eapply pact_injective. exact Heq.
    + constructor. now apply transport_BRenTmlCore.
    + constructor.
    + constructor.
    + constructor. now apply transport_BRenTmCore.
    + constructor.
  - destruct D as
      [n P xs xs' Dxs|n L ps ps' Dps|t t' p Dt|Q p|
       Q ell p p' Hellj Hellk Dp]; cbn.
    + constructor. now apply transport_BRenTmlCore.
    + constructor. now apply transport_BRenFmlCore.
    + constructor. now apply transport_BRenTmCore.
    + constructor.
    + apply R_BindPass.
      * intro Heq. apply Hellj. eapply pact_injective. exact Heq.
      * intro Heq. apply Hellk. eapply pact_injective. exact Heq.
      * now apply transport_BRenFmCore.
  - destruct D as [|n t t' xs xs' Dt Dxs]; cbn.
    + constructor.
    + constructor; [now apply transport_BRenTmCore | now apply transport_BRenTmlCore].
  - destruct D as [|n p p' ps ps' Dp Dps]; cbn.
    + constructor.
    + constructor; [now apply transport_BRenFmCore | now apply transport_BRenFmlCore].
Defined.

Definition transport_BRrenTm {Sig} (g : Perm3) j k (t t' : tm Sig)
    (D : BRenTm j k t t') :
    BRenTm (pact g j) (pact g k) (act_tm g t) (act_tm g t').
Proof.
  destruct D as [Hjk D]. split.
  - intro Heq. apply Hjk. eapply pact_injective. exact Heq.
  - now apply transport_BRenTmCore.
Defined.

Definition transport_BRrenFm {Sig} (g : Perm3) j k (p p' : fm Sig)
    (D : BRenFm j k p p') :
    BRenFm (pact g j) (pact g k) (act_fm g p) (act_fm g p').
Proof.
  destruct D as [Hjk D]. split.
  - intro Heq. apply Hjk. eapply pact_injective. exact Heq.
  - now apply transport_BRenFmCore.
Defined.

Lemma transport_RootAlpha : forall Sig g (p q : fm Sig),
    RootAlpha p q -> RootAlpha (act_fm g p) (act_fm g q).
Proof.
  intros Sig g p q (Q & j & k & body & body' & -> & -> & Hkj & Hfresh & Hren).
  exists Q, (pact g j), (pact g k), (act_fm g body), (act_fm g body').
  repeat split.
  - intro Heq. apply Hkj. eapply pact_injective. exact Heq.
  - intro Hin. apply (AN_act_fm_iff g body (pact g k)) in Hin.
    rewrite pact_inv_l in Hin. contradiction.
  - intro Heq. apply Hkj. symmetry. eapply pact_injective. exact Heq.
  - exact (proj2 (transport_BRrenFm g Hren)).
Qed.

Fixpoint transport_Alpha {Sig} (g : Perm3) (p q : fm Sig) (D : Alpha p q) {struct D} :
    Alpha (act_fm g p) (act_fm g q)
with transport_AlphaFml {Sig} (g : Perm3) n (ps qs : fml Sig n)
    (D : AlphaFml ps qs) {struct D} :
    AlphaFml (act_fml g ps) (act_fml g qs).
Proof.
  - destruct D; cbn.
    + apply A_Root. now apply transport_RootAlpha.
    + apply A_Conn. now apply transport_AlphaFml.
    + apply A_Bind. now apply transport_Alpha.
  - destruct D; cbn.
    + apply A_Here. now apply transport_Alpha.
    + apply A_There. now apply transport_AlphaFml.
Defined.

Fixpoint transport_AStar {Sig} (g : Perm3) (z z' : expr Sig)
    (D : AStar z z') {struct D} :
    AStar (act_expr g z) (act_expr g z') :=
  match D with
  | AS_Term t => AS_Term (act_tm g t)
  | AS_FormRefl p => AS_FormRefl (act_fm g p)
  | AS_FormStep A D' =>
      AS_FormStep (transport_Alpha g A) (transport_AStar g D')
  end.

Definition transport_CSub {Sig} (g : Perm3) i (s : tm Sig) z z'
    (C : CSub i s z z') :
    CSub (pact g i) (act_tm g s) (act_expr g z) (act_expr g z').
Proof.
  destruct C as [z z' u u' A0 D A1].
  econstructor.
  - exact (transport_AStar g A0).
  - exact (transport_SubExpr g D).
  - exact (transport_AStar g A1).
Defined.

(** * 13.3  Constructive existence of composite substitution

  [active_rename_*] is a proof-local deterministic representative of the
  source's bounded renaming relation.  It is not a coordinate of HRISS and is
  used only under an explicit freshness premise.
*)

Fixpoint active_rename_tm {Sig} (j k : nat) (t : tm Sig) : tm Sig :=
  match t with
  | TVar ell => if Nat.eq_dec ell j then TVar k else TVar ell
  | TFun f xs => TFun f (active_rename_tml j k xs)
  | TQuoteT u => TQuoteT u
  | TQuoteF p => TQuoteF p
  | TRApp u v => TRApp (active_rename_tm j k u) v
  | TMove g => TMove g
  end
with active_rename_fm {Sig} (j k : nat) (p : fm Sig) : fm Sig :=
  match p with
  | FPred P xs => FPred P (active_rename_tml j k xs)
  | FConn L ps => FConn L (active_rename_fml j k ps)
  | FRApp t q => FRApp (active_rename_tm j k t) q
  | FQuant Q ell q =>
      if Nat.eq_dec ell j then FQuant Q ell q
      else if Nat.eq_dec ell k then FQuant Q ell q
      else FQuant Q ell (active_rename_fm j k q)
  end
with active_rename_tml {Sig n} (j k : nat) (xs : tml Sig n) : tml Sig n :=
  match xs with
  | TNil => TNil
  | TCons t ts => TCons (active_rename_tm j k t) (active_rename_tml j k ts)
  end
with active_rename_fml {Sig n} (j k : nat) (ps : fml Sig n) : fml Sig n :=
  match ps with
  | FNil => FNil
  | FCons p qs => FCons (active_rename_fm j k p) (active_rename_fml j k qs)
  end.

Set Warnings "-non-full-mutual".

Fixpoint active_rename_tm_height {Sig} j k (t : tm Sig) {struct t} :
    tm_height (active_rename_tm j k t) = tm_height t
with active_rename_fm_height {Sig} j k (p : fm Sig) {struct p} :
    fm_height (active_rename_fm j k p) = fm_height p
with active_rename_tml_height {Sig n} j k (xs : tml Sig n) {struct xs} :
    tml_height (active_rename_tml j k xs) = tml_height xs
with active_rename_fml_height {Sig n} j k (ps : fml Sig n) {struct ps} :
    fml_height (active_rename_fml j k ps) = fml_height ps.
Proof.
  - destruct t as [i|n f xs|u|p|u v|a]; cbn.
    + destruct (Nat.eq_dec i j); reflexivity.
    + pose proof (@active_rename_tml_height Sig n j k xs) as Hxs.
      destruct xs; cbn in Hxs |- *.
      * reflexivity.
      * exact (f_equal S Hxs).
    + reflexivity.
    + reflexivity.
    + now rewrite active_rename_tm_height.
    + reflexivity.
  - destruct p as [n P xs|n L ps|t q|Q i q]; cbn.
    + pose proof (@active_rename_tml_height Sig n j k xs) as Hxs.
      destruct xs; cbn in Hxs |- *.
      * reflexivity.
      * exact (f_equal S Hxs).
    + pose proof (@active_rename_fml_height Sig n j k ps) as Hps.
      destruct ps; cbn in Hps |- *.
      * reflexivity.
      * exact (f_equal S Hps).
    + now rewrite active_rename_tm_height.
    + destruct (Nat.eq_dec i j), (Nat.eq_dec i k); cbn;
        try reflexivity; now rewrite active_rename_fm_height.
  - destruct xs as [|n t xs]; cbn.
    + reflexivity.
    + pose proof (@active_rename_tm_height Sig j k t) as Ht.
      pose proof (@active_rename_tml_height Sig n j k xs) as Hxs.
      destruct xs; cbn in Ht, Hxs |- *.
      * exact Ht.
      * now rewrite Ht, Hxs.
  - destruct ps as [|n p ps]; cbn.
    + reflexivity.
    + pose proof (@active_rename_fm_height Sig j k p) as Hp.
      pose proof (@active_rename_fml_height Sig n j k ps) as Hps.
      destruct ps; cbn in Hp, Hps |- *.
      * exact Hp.
      * now rewrite Hp, Hps.
Defined.

Set Warnings "-non-full-mutual".

Fixpoint active_rename_BRenTmCore {Sig} j k (t : tm Sig) {struct t} :
    ~ In k (AN_tm t) -> BRenTmCore j k t (active_rename_tm j k t)
with active_rename_BRenFmCore {Sig} j k (p : fm Sig) {struct p} :
    ~ In k (AN_fm p) -> BRenFmCore j k p (active_rename_fm j k p)
with active_rename_BRenTmlCore {Sig n} j k (xs : tml Sig n) {struct xs} :
    ~ In k (AN_tml xs) -> BRenTmlCore j k xs (active_rename_tml j k xs)
with active_rename_BRenFmlCore {Sig n} j k (ps : fml Sig n) {struct ps} :
    ~ In k (AN_fml ps) -> BRenFmlCore j k ps (active_rename_fml j k ps).
Proof.
  - destruct t as [i|n f xs|u|p|u v|a]; cbn; intro Hfresh.
    + destruct (Nat.eq_dec i j) as [->|Hne].
      * constructor.
      * apply R_Miss. exact Hne.
    + constructor. now apply active_rename_BRenTmlCore.
    + constructor.
    + constructor.
    + constructor. apply active_rename_BRenTmCore. exact Hfresh.
    + constructor.
  - destruct p as [n P xs|n L ps|t q|Q ell q]; cbn; intro Hfresh.
    + constructor. now apply active_rename_BRenTmlCore.
    + constructor. now apply active_rename_BRenFmlCore.
    + constructor. apply active_rename_BRenTmCore. exact Hfresh.
    + destruct (Nat.eq_dec ell j) as [->|Hnj].
      * constructor.
      * destruct (Nat.eq_dec ell k) as [->|Hnk].
        -- exfalso. apply Hfresh. now left.
        -- apply R_BindPass.
           ++ exact Hnj.
           ++ exact Hnk.
           ++ apply active_rename_BRenFmCore. intro Hin. apply Hfresh. now right.
  - destruct xs; cbn; intro Hfresh.
    + constructor.
    + apply R_TCons.
      * apply active_rename_BRenTmCore. intro Hin. apply Hfresh.
        apply in_app_iff. now left.
      * apply active_rename_BRenTmlCore. intro Hin. apply Hfresh.
        apply in_app_iff. now right.
  - destruct ps; cbn; intro Hfresh.
    + constructor.
    + apply R_FCons.
      * apply active_rename_BRenFmCore. intro Hin. apply Hfresh.
        apply in_app_iff. now left.
      * apply active_rename_BRenFmlCore. intro Hin. apply Hfresh.
        apply in_app_iff. now right.
Defined.

Lemma active_rename_BRenFm : forall Sig j k (p : fm Sig),
    j <> k -> ~ In k (AN_fm p) ->
    BRenFm j k p (active_rename_fm j k p).
Proof.
  intros Sig j k p Hjk Hfresh. split; [exact Hjk|].
  now apply active_rename_BRenFmCore.
Qed.

(** Raw substitution is total on terms because active formula bodies occur
    only behind Quote/RApp target barriers. *)
Fixpoint raw_sub_tm_exists {Sig} i (s : tm Sig) (t : tm Sig) {struct t} :
    { t' : tm Sig & SubTm i s t t' }
with raw_sub_tml_exists {Sig} i (s : tm Sig) n (xs : tml Sig n) {struct xs} :
    { xs' : tml Sig n & SubTml i s xs xs' }.
Proof.
  - destruct t as [v|n f xs|u|p|u v|a].
    + destruct (Nat.eq_dec v i) as [->|Hne].
      * exists s. constructor.
      * exists (TVar v). now apply S_Miss.
    + destruct (@raw_sub_tml_exists Sig i s n xs) as [xs' Dxs].
      exists (TFun f xs'). now constructor.
    + exists (TQuoteT u). constructor.
    + exists (TQuoteF p). constructor.
    + destruct (raw_sub_tm_exists Sig i s u) as [u' Du].
      exists (TRApp u' v). now constructor.
    + exists (TMove a). constructor.
  - destruct xs as [|n t xs].
    + exists TNil. constructor.
    + destruct (@raw_sub_tm_exists Sig i s t) as [t' Dt].
      destruct (raw_sub_tml_exists Sig i s n xs) as [xs' Dxs].
      exists (TCons t' xs'). now constructor.
Defined.

(** Pointwise Alpha-star on a finite formula tuple. *)
Inductive AStarFml {Sig} : forall n, fml Sig n -> fml Sig n -> Prop :=
| ASF_Refl : forall n (ps : fml Sig n), AStarFml ps ps
| ASF_Step : forall n (ps qs rs : fml Sig n),
    AlphaFml ps qs -> AStarFml qs rs -> AStarFml ps rs.

Lemma astarfml_trans : forall Sig n (ps qs rs : fml Sig n),
    AStarFml ps qs -> AStarFml qs rs -> AStarFml ps rs.
Proof.
  intros Sig n ps qs rs D E. induction D.
  - exact E.
  - econstructor; eauto.
Qed.

Lemma astar_to_astarfml_head : forall Sig n (p q : fm Sig)
    (ps : fml Sig n),
    AStar (EForm p) (EForm q) ->
    AStarFml (FCons p ps) (FCons q ps).
Proof.
  intros Sig n p q ps D. remember (EForm p) as ep eqn:Hp.
  remember (EForm q) as eq eqn:Hq. revert p q Hp Hq.
  induction D; intros p0 q0 Hp Hq; inversion Hp; inversion Hq; subst.
  - constructor.
  - econstructor.
    + apply A_Here. exact H.
    + eapply IHD; reflexivity.
Qed.

Lemma astarfml_tail : forall Sig n p (ps qs : fml Sig n),
    AStarFml ps qs -> AStarFml (FCons p ps) (FCons p qs).
Proof.
  intros Sig n p ps qs D. induction D.
  - constructor.
  - econstructor.
    + apply A_There. exact H.
    + exact IHD.
Qed.

Lemma astarfml_conn : forall Sig n (L : LSym Sig n) (ps qs : fml Sig n),
    AStarFml ps qs -> AStar (EForm (FConn L ps)) (EForm (FConn L qs)).
Proof.
  intros Sig n L ps qs D. induction D.
  - constructor.
  - econstructor.
    + apply A_Conn. exact H.
    + exact (IHD L).
Qed.

Lemma astar_bind : forall Sig (Q : QSym Sig) i (p q : fm Sig),
    AStar (EForm p) (EForm q) ->
    AStar (EForm (FQuant Q i p)) (EForm (FQuant Q i q)).
Proof.
  intros Sig Q i p q D. remember (EForm p) as ep eqn:Hp.
  remember (EForm q) as eq eqn:Hq. revert p q Hp Hq.
  induction D; intros p0 q0 Hp Hq; inversion Hp; inversion Hq; subst.
  - constructor.
  - econstructor.
    + apply A_Bind. exact H.
    + eapply IHD; reflexivity.
Qed.

Lemma fml_head_height_le : forall Sig n (p : fm Sig) (ps : fml Sig n),
    fm_height p <= fml_height (FCons p ps).
Proof.
  intros Sig n p ps. destruct ps; cbn.
  - lia.
  - apply Nat.le_max_l.
Qed.

Lemma fml_tail_height_le : forall Sig n (p : fm Sig) (ps : fml Sig n),
    fml_height ps <= fml_height (FCons p ps).
Proof.
  intros Sig n p ps. destruct ps; cbn.
  - lia.
  - apply Nat.le_max_r.
Qed.

Definition PreSubFm {Sig} (i : nat) (s : tm Sig) (p : fm Sig) : Prop :=
  exists u u', AStar (EForm p) (EForm u) /\ SubFm i s u u'.

Definition PreSubFml {Sig} (i : nat) (s : tm Sig) n
    (ps : fml Sig n) : Prop :=
  exists us us', AStarFml ps us /\ SubFml i s us us'.

Lemma PreSubFm_rank : forall Sig i (s : tm Sig) rank (p : fm Sig),
    fm_height p < rank -> PreSubFm i s p.
Proof.
  intros Sig i s rank. induction rank as [|rank IH].
  - intros p Hlt. lia.
  - intros p Hlt. destruct p as [n P xs|n L ps|t q|Q ell q].
    + destruct (@raw_sub_tml_exists Sig i s n xs) as [xs' Dxs].
      exists (FPred P xs), (FPred P xs'). split.
      * constructor.
      * now constructor.
    + assert (Hlists : forall n0 (qs : fml Sig n0),
          fml_height qs < rank -> PreSubFml i s qs).
      { intros n0 qs. induction qs as [|n0 p qs IHqs]; intro Hbound.
        - exists FNil, FNil. split; constructor.
        - assert (Hp : fm_height p < rank).
          { eapply Nat.le_lt_trans.
            - apply fml_head_height_le.
            - exact Hbound. }
          assert (Hqs : fml_height qs < rank).
          { eapply Nat.le_lt_trans.
            - apply fml_tail_height_le with (p := p).
            - exact Hbound. }
          destruct (IH p Hp) as (u & u' & Au & Du).
          destruct (IHqs Hqs) as (us & us' & Aus & Dus).
          exists (FCons u us), (FCons u' us'). split.
          + eapply astarfml_trans.
            * exact (astar_to_astarfml_head qs Au).
            * exact (astarfml_tail u Aus).
          + now constructor. }
      destruct ps as [|n0 p ps].
      * exists (FConn L FNil), (FConn L FNil). split.
        -- constructor.
        -- constructor. constructor.
      * change (S (fml_height (FCons p ps)) < S rank) in Hlt.
        assert (Hps : fml_height (FCons p ps) < rank) by lia.
        destruct (Hlists _ (FCons p ps) Hps) as (us & us' & Aus & Dus).
        exists (FConn L us), (FConn L us'). split.
        -- now apply astarfml_conn.
        -- now constructor.
    + destruct (@raw_sub_tm_exists Sig i s t) as [t' Dt].
      exists (FRApp t q), (FRApp t' q). split.
      * constructor.
      * now constructor.
    + destruct (Nat.eq_dec ell i) as [->|Helli].
      * exists (FQuant Q i q), (FQuant Q i q). split.
        -- constructor.
        -- constructor.
      * destruct (in_dec Nat.eq_dec ell (FV_tm s)) as [Hconflict|Hpass].
        -- set (K := AN_fm q ++ FV_tm s ++ [i; ell]).
           set (k := fresh_name K).
           assert (HfreshK : ~ In k K).
           { subst k. apply fresh_name_spec. }
           assert (HkAN : ~ In k (AN_fm q)).
           { intro Hin. apply HfreshK. subst K. apply in_app_iff. now left. }
           assert (HkFV : ~ In k (FV_tm s)).
           { intro Hin. apply HfreshK. subst K. apply in_app_iff. right.
             apply in_app_iff. now left. }
           assert (Hki : k <> i).
           { intro Heq. apply HfreshK. subst K. apply in_app_iff. right.
             apply in_app_iff. right. cbn. left. symmetry. exact Heq. }
           assert (Hkell : k <> ell).
           { intro Heq. apply HfreshK. subst K. apply in_app_iff. right.
             apply in_app_iff. right. cbn. right. left. symmetry. exact Heq. }
           set (qr := active_rename_fm ell k q).
           assert (Hqr_rank : fm_height qr < rank).
           { subst qr. rewrite active_rename_fm_height. cbn in Hlt. lia. }
           destruct (IH qr Hqr_rank) as (u & u' & Au & Du).
           assert (Hroot : RootAlpha (FQuant Q ell q) (FQuant Q k qr)).
           { exists Q, ell, k, q, qr. repeat split.
              - exact Hkell.
              - exact HkAN.
              - congruence.
              - subst qr. now apply active_rename_BRenFmCore. }
           exists (FQuant Q k u), (FQuant Q k u'). split.
           ++ eapply AS_FormStep.
              ** apply A_Root. exact Hroot.
              ** exact (astar_bind Q k Au).
           ++ apply S_BindPass.
              ** congruence.
              ** exact HkFV.
              ** exact Du.
        -- assert (Hq_rank : fm_height q < rank) by (cbn in Hlt; lia).
           destruct (IH q Hq_rank) as (u & u' & Au & Du).
           exists (FQuant Q ell u), (FQuant Q ell u'). split.
           ++ exact (astar_bind Q ell Au).
           ++ apply S_BindPass; assumption.
Qed.

Theorem CSub_exists_raw : forall Sig i (s : tm Sig) (z : expr Sig),
    exists z', CSub i s z z'.
Proof.
  intros Sig i s [t|p].
  - destruct (@raw_sub_tm_exists Sig i s t) as [t' Dt].
    exists (ETerm t'). econstructor.
    + constructor.
    + apply S_ETerm. exact Dt.
    + constructor.
  - destruct (@PreSubFm_rank Sig i s (S (fm_height p)) p) as
        (u & u' & A0 & D).
    + lia.
    + exists (EForm u'). econstructor.
      * exact A0.
      * apply S_EForm. exact D.
      * constructor.
Qed.

(** Carrier preservation: the raw inductive encodings above become exactly
    the source judgments after restricting their endpoints by [wf_*]. *)

Fixpoint SubTm_preserves_wf (H : Subgroup) {Sig} i (s t t' : tm Sig)
    (D : SubTm i s t t') {struct D} :
    wf_tm H s -> wf_tm H t -> wf_tm H t'
with SubFm_preserves_wf (H : Subgroup) {Sig} i (s : tm Sig) (p p' : fm Sig)
    (D : SubFm i s p p') {struct D} :
    wf_tm H s -> wf_fm H p -> wf_fm H p'
with SubTml_preserves_wf (H : Subgroup) {Sig} i (s : tm Sig) n
    (xs xs' : tml Sig n) (D : SubTml i s xs xs') {struct D} :
    wf_tm H s -> wf_tml H xs -> wf_tml H xs'
with SubFml_preserves_wf (H : Subgroup) {Sig} i (s : tm Sig) n
    (ps ps' : fml Sig n) (D : SubFml i s ps ps') {struct D} :
    wf_tm H s -> wf_fml H ps -> wf_fml H ps'.
Proof.
  - destruct D as [|j Hji|n f xs xs' Dxs|t|p|t t' u Dt|a]; cbn.
    + intros Hs _. exact Hs.
    + auto.
    + intros Hs Hxs. eapply SubTml_preserves_wf; eauto.
    + auto.
    + auto.
    + intros Hs [Ht Hu]. split.
      * eapply SubTm_preserves_wf; eauto.
      * exact Hu.
    + auto.
  - destruct D as
      [n P xs xs' Dxs|n L ps ps' Dps|t t' p Dt|Q p|
       Q j p p' Hji Hfresh Dp]; cbn.
    + intros Hs Hxs. eapply SubTml_preserves_wf; eauto.
    + intros Hs Hps. eapply SubFml_preserves_wf; eauto.
    + intros Hs [Ht Hp]. split.
      * eapply SubTm_preserves_wf; eauto.
      * exact Hp.
    + auto.
    + intros Hs Hp. eapply SubFm_preserves_wf; eauto.
  - destruct D as [|n t t' xs xs' Dt Dxs]; cbn.
    + auto.
    + intros Hs [Ht Hxs]. split.
      * eapply SubTm_preserves_wf; eauto.
      * eapply SubTml_preserves_wf; eauto.
  - destruct D as [|n p p' ps ps' Dp Dps]; cbn.
    + auto.
    + intros Hs [Hp Hps]. split.
      * eapply SubFm_preserves_wf; eauto.
      * eapply SubFml_preserves_wf; eauto.
Defined.

Lemma SubExpr_preserves_wf : forall H Sig i (s : tm Sig) z z',
    SubExpr i s z z' -> wf_tm H s -> wf_expr H z -> wf_expr H z'.
Proof.
  intros H Sig i s z z' D Hs Hz. destruct D; cbn in *.
  - eapply SubTm_preserves_wf; eauto.
  - eapply SubFm_preserves_wf; eauto.
Qed.

Fixpoint BRenTmCore_preserves_wf (H : Subgroup) {Sig} j k
    (t t' : tm Sig) (D : BRenTmCore j k t t') {struct D} :
    wf_tm H t -> wf_tm H t'
with BRenFmCore_preserves_wf (H : Subgroup) {Sig} j k
    (p p' : fm Sig) (D : BRenFmCore j k p p') {struct D} :
    wf_fm H p -> wf_fm H p'
with BRenTmlCore_preserves_wf (H : Subgroup) {Sig} j k n
    (xs xs' : tml Sig n) (D : BRenTmlCore j k xs xs') {struct D} :
    wf_tml H xs -> wf_tml H xs'
with BRenFmlCore_preserves_wf (H : Subgroup) {Sig} j k n
    (ps ps' : fml Sig n) (D : BRenFmlCore j k ps ps') {struct D} :
    wf_fml H ps -> wf_fml H ps'.
Proof.
  - destruct D as [|ell Hell|n f xs xs' Dxs|t|p|t t' u Dt|a]; cbn.
    + auto.
    + auto.
    + intro Hxs. eapply BRenTmlCore_preserves_wf; eauto.
    + auto.
    + auto.
    + intros [Ht Hu]. split.
      * eapply BRenTmCore_preserves_wf; eauto.
      * exact Hu.
    + auto.
  - destruct D as
      [n P xs xs' Dxs|n L ps ps' Dps|t t' p Dt|Q p|
       Q ell p p' Hellj Hellk Dp]; cbn.
    + intro Hxs. eapply BRenTmlCore_preserves_wf; eauto.
    + intro Hps. eapply BRenFmlCore_preserves_wf; eauto.
    + intros [Ht Hp]. split.
      * eapply BRenTmCore_preserves_wf; eauto.
      * exact Hp.
    + auto.
    + intro Hp. eapply BRenFmCore_preserves_wf; eauto.
  - destruct D as [|n t t' xs xs' Dt Dxs]; cbn.
    + auto.
    + intros [Ht Hxs]. split.
      * eapply BRenTmCore_preserves_wf; eauto.
      * eapply BRenTmlCore_preserves_wf; eauto.
  - destruct D as [|n p p' ps ps' Dp Dps]; cbn.
    + auto.
    + intros [Hp Hps]. split.
      * eapply BRenFmCore_preserves_wf; eauto.
      * eapply BRenFmlCore_preserves_wf; eauto.
Defined.

Lemma RootAlpha_preserves_wf : forall H Sig (p q : fm Sig),
    RootAlpha p q -> wf_fm H p -> wf_fm H q.
Proof.
  intros H Sig p q (Q & j & k & body & body' & -> & -> & Hkj & Hfresh & Hren).
  cbn. intro Hbody. destruct Hren as [_ D].
  eapply BRenFmCore_preserves_wf; eauto.
Qed.

Fixpoint Alpha_preserves_wf (H : Subgroup) {Sig} (p q : fm Sig)
    (D : Alpha p q) {struct D} : wf_fm H p -> wf_fm H q
with AlphaFml_preserves_wf (H : Subgroup) {Sig} n (ps qs : fml Sig n)
    (D : AlphaFml ps qs) {struct D} : wf_fml H ps -> wf_fml H qs.
Proof.
  - destruct D.
    + now apply RootAlpha_preserves_wf.
    + cbn. intro Hps. eapply AlphaFml_preserves_wf; eauto.
    + cbn. intro Hp. eapply Alpha_preserves_wf; eauto.
  - destruct D; cbn; intros [Hp Hps]; split.
    + eapply Alpha_preserves_wf; eauto.
    + exact Hps.
    + exact Hp.
    + eapply AlphaFml_preserves_wf; eauto.
Defined.

Fixpoint AStar_preserves_wf (H : Subgroup) {Sig : Signature}
    (z z' : expr Sig)
    (D : AStar z z') {struct D} : wf_expr H z -> wf_expr H z' :=
  match D with
  | AS_Term t => fun Ht => Ht
  | AS_FormRefl p => fun Hp => Hp
  | AS_FormStep A D' => fun Hp =>
      @AStar_preserves_wf H Sig _ _ D'
        (@Alpha_preserves_wf H Sig _ _ A Hp)
  end.

Lemma CSub_preserves_wf : forall H Sig i (s : tm Sig) z z',
    CSub i s z z' -> wf_tm H s -> wf_expr H z -> wf_expr H z'.
Proof.
  intros H Sig i s z z' C Hs Hz.
  destruct C as [z z' u u' A0 D A1].
  eapply AStar_preserves_wf; [exact A1|].
  eapply SubExpr_preserves_wf; [exact D|exact Hs|].
  eapply AStar_preserves_wf; eauto.
Qed.

Definition CSubJud (H : Subgroup) {Sig} i (s : tm Sig) z z' : Prop :=
  wf_tm H s /\ wf_expr H z /\ wf_expr H z' /\ CSub i s z z'.

Theorem CSub_exists_nontrivial : forall H Sig,
    H_nontrivial H -> forall i (s : tm Sig) (z : expr Sig),
    wf_tm H s -> wf_expr H z -> exists z', CSubJud H i s z z'.
Proof.
  intros H Sig Hnon i s z Hs Hz.
  destruct (CSub_exists_raw i s z) as [z' C].
  exists z'. repeat split; try assumption.
  - eapply CSub_preserves_wf; eauto.
Qed.

(** * 13.4--13.5  Nonzero holonomy and Path-CSub separation *)

Definition p_path : Perm3 := pmul sigma tau.
Definition q_path : Perm3 := pmul tau sigma.

Theorem nonzero_reflection_holonomy : Hol p_path q_path 0.
Proof. cbn. discriminate. Qed.

Theorem path_CSub_separation : forall Sig (s : tm Sig) z z'
    (C : CSub 0 s z z'), ~ PathEq C p_path q_path.
Proof.
  intros Sig s z z' C Hpath.
  specialize (Hpath 0).
  assert (Hin : In 0 (witness_support 0 s z z')).
  { unfold witness_support. repeat rewrite in_app_iff. cbn. tauto. }
  specialize (Hpath Hin). cbn in Hpath. discriminate.
Qed.

(** * 6  Pointed dcpos and Scott-continuous maps

  The source fixes ZFC as metatheory.  The three imported bridge principles
  above realize, for CIC functions and proof fields, ZFC function
  extensionality, proof irrelevance, and classical description.  No target
  theorem is postulated.
*)

Definition upper_bound {A : Type} (le : A -> A -> Prop)
    (X : A -> Prop) (u : A) : Prop := forall x, X x -> le x u.

Definition is_lub {A : Type} (le : A -> A -> Prop)
    (X : A -> Prop) (u : A) : Prop :=
  upper_bound le X u /\ forall v, upper_bound le X v -> le u v.

Definition directed {A : Type} (le : A -> A -> Prop)
    (X : A -> Prop) : Prop :=
  (exists x, X x) /\
  forall x y, X x -> X y -> exists z, X z /\ le x z /\ le y z.

Record PDCPO : Type := {
  dcar : Type;
  dle : dcar -> dcar -> Prop;
  dle_refl : forall x, dle x x;
  dle_trans : forall x y z, dle x y -> dle y z -> dle x z;
  dle_antisym : forall x y, dle x y -> dle y x -> x = y;
  dbot : dcar;
  dbot_least : forall x, dle dbot x;
  dsup : forall (X : dcar -> Prop), directed dle X -> dcar;
  dsup_lub : forall (X : dcar -> Prop) (HX : directed dle X),
      is_lub dle X (@dsup X HX)
}.

Arguments dcar _ : clear implicits.
Arguments dle _ _ _ : clear implicits.
Arguments dle_refl _ _ : clear implicits.
Arguments dle_trans _ _ _ _ _ _ : clear implicits.
Arguments dle_antisym _ _ _ _ _ : clear implicits.
Arguments dbot _ : clear implicits.
Arguments dbot_least _ _ : clear implicits.
Arguments dsup _ _ _ : clear implicits.
Arguments dsup_lub _ _ _ : clear implicits.

Lemma lub_unique : forall D (X : dcar D -> Prop) u v,
    is_lub (dle D) X u -> is_lub (dle D) X v -> u = v.
Proof.
  intros D X u v [Hu Humin] [Hv Hvmin].
  apply (dle_antisym D).
  - apply Humin. exact Hv.
  - apply Hvmin. exact Hu.
Qed.

Definition image_pred {A B : Type} (f : A -> B) (X : A -> Prop)
    (y : B) : Prop := exists x, X x /\ y = f x.

Lemma image_directed : forall A B (leA : A -> A -> Prop)
    (leB : B -> B -> Prop) (f : A -> B),
    (forall x y, leA x y -> leB (f x) (f y)) ->
    forall X, directed leA X -> directed leB (image_pred f X).
Proof.
  intros A B leA leB f Hmono X [[x0 Hx0] Hdir]. split.
  - exists (f x0), x0. auto.
  - intros fx fy [x1 [Hx1 ->]] [y1 [Hy1 ->]].
    destruct (Hdir x1 y1 Hx1 Hy1) as (z & Hz & Hxz & Hyz).
    exists (f z). split.
    + exists z. auto.
    + split; [now apply Hmono | now apply Hmono].
Qed.

Record SCMap (D E : PDCPO) : Type := {
  sc_fun : dcar D -> dcar E;
  sc_monotone : forall x y, dle D x y -> dle E (sc_fun x) (sc_fun y);
  sc_pres_lub : forall X HX,
      is_lub (dle E) (image_pred sc_fun X) (sc_fun (dsup D X HX))
}.

Arguments sc_fun {D E} _ _.
Coercion sc_fun : SCMap >-> Funclass.

Definition sc_id (D : PDCPO) : SCMap D D.
Proof.
  refine {| sc_fun := fun x => x |}.
  - auto.
  - intros X HX. split.
    + intros y (x & Hx & ->). apply (proj1 (dsup_lub D X HX)). exact Hx.
    + intros v Hub. apply (proj2 (dsup_lub D X HX)).
      intros x Hx. apply Hub. exists x. auto.
Defined.

Definition sc_const (D E : PDCPO) (e : dcar E) : SCMap D E.
Proof.
  refine {| sc_fun := fun _ => e |}.
  - intros. apply dle_refl.
  - intros X HX. split.
    + intros y (x & Hx & ->). apply dle_refl.
    + intros v Hub. destruct HX as [[x Hx] Hdir].
      apply Hub. exists x. auto.
Defined.

Definition sc_comp (D E F : PDCPO) (f : SCMap E F) (g : SCMap D E) :
    SCMap D F.
Proof.
  refine {| sc_fun := fun x => f (g x) |}.
  - intros x y Hxy. apply sc_monotone. now apply sc_monotone.
  - intros X HX.
    pose proof (image_directed (sc_monotone g) HX) as Hgdir.
    pose proof (@sc_pres_lub D E g X HX) as Hglub.
    pose proof (@sc_pres_lub E F f (image_pred g X) Hgdir) as Hflub.
    assert (Heq : g (dsup D X HX) = dsup E (image_pred g X) Hgdir).
    { eapply (@lub_unique E (image_pred g X)).
      - exact Hglub.
      - exact (dsup_lub E _ _). }
    rewrite Heq. clear Heq.
    split.
    + intros y (x & Hx & ->).
      destruct Hflub as [Hub Hleast]. apply Hub.
      exists (g x). split.
      * exists x. auto.
      * reflexivity.
    + intros v Hub. destruct Hflub as [Hupper Hleast]. apply Hleast.
      intros y (gx & (x & Hx & ->) & ->). apply Hub.
      exists x. auto.
Defined.

(** Dependent products, including finite powers and the signature product. *)

Section DependentProductDCPO.
  Context {I : Type} (D : I -> PDCPO).

  Definition dep_car := forall i, dcar (D i).
  Definition dep_le (x y : dep_car) : Prop := forall i, dle (D i) (x i) (y i).
  Definition dep_bot : dep_car := fun i => dbot (D i).

  Lemma eval_image_directed : forall (X : dep_car -> Prop),
      directed dep_le X -> forall i,
      directed (dle (D i)) (fun y => exists x, X x /\ y = x i).
  Proof.
    intros X [[x0 Hx0] Hdir] i. split.
    - exists (x0 i), x0. auto.
    - intros a b [x1 [Hx1 ->]] [y1 [Hy1 ->]].
      destruct (Hdir x1 y1 Hx1 Hy1) as (z & Hz & Hxz & Hyz).
      exists (z i). split.
      + exists z. auto.
      + split; [apply Hxz | apply Hyz].
  Qed.

  Definition dep_sup (X : dep_car -> Prop) (HX : directed dep_le X) : dep_car :=
    fun i => dsup (D i) (fun y => exists x, X x /\ y = x i)
                    (@eval_image_directed X HX i).

  Definition dep_product_dcpo : PDCPO.
  Proof.
    refine {| dcar := dep_car; dle := dep_le; dbot := dep_bot;
              dsup := dep_sup |}.
    - intros x i. apply dle_refl.
    - intros x y z Hxy Hyz i. eapply dle_trans; eauto.
    - intros x y Hxy Hyx. apply functional_extensionality_dep. intro i.
      apply (dle_antisym (D i)); auto.
    - intros x i. apply dbot_least.
    - intros X HX. split.
      + intros x Hx i. apply (proj1 (dsup_lub (D i) _ _)).
        exists x. auto.
      + intros y Hy i. apply (proj2 (dsup_lub (D i) _ _)).
        intros a (x & Hx & ->). apply Hy. exact Hx.
  Defined.
End DependentProductDCPO.

Inductive Finite : nat -> Type :=
| fzero : forall n, Finite (S n)
| fsucc : forall n, Finite n -> Finite (S n).

Definition power_dcpo (D : PDCPO) (n : nat) : PDCPO :=
  @dep_product_dcpo (Finite n) (fun _ => D).

(** Scott-continuous function spaces with pointwise order. *)

Definition scmap_le (D E : PDCPO) (f g : SCMap D E) : Prop :=
  forall x, dle E (f x) (g x).

Arguments scmap_le _ _ _ _ : clear implicits.

Lemma SCMap_ext : forall D E (f g : SCMap D E),
    (forall x, f x = g x) -> f = g.
Proof.
  intros D E [f Hfm Hfc] [g Hgm Hgc] Heq. cbn in Heq.
  assert (Hfg : f = g) by (apply functional_extensionality; exact Heq).
  subst g. f_equal; apply proof_irrelevance.
Qed.

Section FunctionSpaceDCPO.
  Context (D E : PDCPO).

  Definition eval_set (F : SCMap D E -> Prop) (x : dcar D)
      (y : dcar E) : Prop := exists f, F f /\ y = f x.

  Lemma eval_set_directed : forall F,
      directed (scmap_le D E) F -> forall x,
      directed (dle E) (eval_set F x).
  Proof.
    intros F [[f Hf] Hdir] x. split.
    - exists (f x), f. auto.
    - intros a b [f1 [Hf1 ->]] [f2 [Hf2 ->]].
      destruct (Hdir f1 f2 Hf1 Hf2) as (f3 & Hf3 & H13 & H23).
      exists (f3 x). split.
      + exists f3. auto.
      + split; [apply H13 | apply H23].
  Qed.

  Definition fsup_fun (F : SCMap D E -> Prop)
      (HF : directed (scmap_le D E) F) (x : dcar D) : dcar E :=
    dsup E (eval_set F x) (@eval_set_directed F HF x).

  Lemma fsup_fun_monotone : forall F HF x y,
      dle D x y -> dle E (@fsup_fun F HF x) (@fsup_fun F HF y).
  Proof.
    intros F HF x y Hxy. unfold fsup_fun.
    apply (proj2 (dsup_lub E _ _)). intros a (f & Hf & ->).
    eapply dle_trans.
    - exact (@sc_monotone D E f x y Hxy).
    - apply (proj1 (dsup_lub E _ _)). exists f. auto.
  Qed.

  Definition fsup_map (F : SCMap D E -> Prop)
      (HF : directed (scmap_le D E) F) : SCMap D E.
  Proof.
    refine {| sc_fun := @fsup_fun F HF;
              sc_monotone := @fsup_fun_monotone F HF |}.
    intros X HX. split.
    - intros y (x & Hx & ->). apply (@fsup_fun_monotone F HF).
      apply (proj1 (dsup_lub D X HX)). exact Hx.
    - intros v Hv. unfold fsup_fun.
      apply (proj2 (dsup_lub E _ _)). intros a (f & Hf & ->).
      destruct (@sc_pres_lub D E f X HX) as [Hfupper Hfleast].
      apply Hfleast. intros b (x & Hx & ->).
      eapply dle_trans.
      + apply (proj1 (dsup_lub E (eval_set F x)
                       (@eval_set_directed F HF x))).
        exists f. auto.
      + apply Hv. exists x. auto.
  Defined.

  Definition scmap_dcpo : PDCPO.
  Proof.
    refine {| dcar := SCMap D E;
              dle := scmap_le D E;
              dbot := @sc_const D E (dbot E);
              dsup := @fsup_map |}.
    - intros f x. apply dle_refl.
    - intros f g h Hfg Hgh x. eapply dle_trans; [apply Hfg | apply Hgh].
    - intros f g Hfg Hgf. apply SCMap_ext. intro x.
      apply (dle_antisym E); [apply Hfg | apply Hgf].
    - intros f x. apply dbot_least.
    - intros F HF. split.
      + intros f Hf x. unfold fsup_map, fsup_fun. cbn.
        apply (proj1 (dsup_lub E _ _)). exists f. auto.
      + intros g Hg x. unfold fsup_map, fsup_fun. cbn.
        apply (proj2 (dsup_lub E _ _)).
        intros y (f & Hf & ->). apply Hg. exact Hf.
  Defined.
End FunctionSpaceDCPO.

(** Continuous coordinatewise maps on dependent products. *)
Section DependentProductMap.
  Context {I : Type} (D E : I -> PDCPO).
  Variable f : forall i, SCMap (D i) (E i).

  Definition dep_map_fun (x : dcar (@dep_product_dcpo I D)) :
      dcar (@dep_product_dcpo I E) := fun i => f i (x i).

  Definition dep_map_sc : SCMap (@dep_product_dcpo I D)
                                (@dep_product_dcpo I E).
  Proof.
    refine {| sc_fun := dep_map_fun |}.
    - intros x y Hxy i. apply sc_monotone. apply Hxy.
    - intros X HX. split.
      + intros y (x & Hx & ->) i. apply sc_monotone.
        apply (proj1 (dsup_lub (D i) _ _)). exists x. auto.
      + intros v Hv i.
        pose proof (@eval_image_directed I D X HX i) as HXi.
        destruct (@sc_pres_lub (D i) (E i) (f i)
                    (fun a => exists x, X x /\ a = x i) HXi)
          as [Hupper Hleast].
        unfold dep_map_fun.
        cbv beta iota zeta delta [dep_product_dcpo dep_sup dsup].
        replace (@eval_image_directed I D X HX i) with HXi
          by apply proof_irrelevance.
        apply Hleast. intros y (a & (x & Hx & ->) & ->).
        apply (Hv (dep_map_fun x)).
        * exists x. auto.
  Defined.
End DependentProductMap.

Lemma dep_map_sc_apply : forall I (D E : I -> PDCPO)
    (f : forall i, SCMap (D i) (E i))
    (x : dcar (@dep_product_dcpo I D)) i,
    @dep_map_sc I D E f x i = f i (x i).
Proof. reflexivity. Qed.

Arguments dep_map_sc_apply _ _ _ _ _ _ : clear implicits.

Definition power_map (D E : PDCPO) (n : nat) (f : SCMap D E) :
    SCMap (power_dcpo D n) (power_dcpo E n) :=
  @dep_map_sc (Finite n) (fun _ => D) (fun _ => E) (fun _ => f).

(** Pre- and post-composition is continuous on Scott function spaces. *)
Definition prepost_map (A B C D : PDCPO)
    (pre : SCMap A B) (post : SCMap C D) :
    SCMap (@scmap_dcpo B C) (@scmap_dcpo A D).
Proof.
  refine (@Build_SCMap (@scmap_dcpo B C) (@scmap_dcpo A D)
    (fun (m : SCMap B C) =>
      @sc_comp A C D post (@sc_comp A B C m pre)) _ _).
  - intros m n Hmn x. cbn in Hmn |- *.
    apply (@sc_monotone C D post). apply Hmn.
  - intros X HX. split.
    + intros y (m & Hm & ->) x. cbn.
      apply sc_monotone. apply (proj1 (dsup_lub C _ _)). exists m. auto.
    + intros v Hv x. cbn.
      pose proof (@eval_set_directed B C X HX (pre x)) as Heval.
      destruct (@sc_pres_lub C D post (@eval_set B C X (pre x)) Heval)
        as [Hupper Hleast].
      unfold fsup_fun.
      replace (@eval_set_directed B C X HX (pre x)) with Heval
        by apply proof_irrelevance.
      apply Hleast. intros y (a & (m & Hm & ->) & ->).
      apply (Hv (@sc_comp A C D post (@sc_comp A B C m pre))).
      * exists m. auto.
Defined.

Lemma prepost_map_apply : forall A B C D
    (pre : SCMap A B) (post : SCMap C D) (m : SCMap B C) x,
    @prepost_map A B C D pre post m x = post (m (pre x)).
Proof. reflexivity. Qed.

Arguments prepost_map_apply _ _ _ _ _ _ _ _ : clear implicits.

(** * 6.2  Embedding-projection pairs *)

Record EPPair (D E : PDCPO) : Type := {
  ep_embed : SCMap D E;
  ep_project : SCMap E D;
  ep_retract : forall x, ep_project (ep_embed x) = x;
  ep_approx : forall y, dle E (ep_embed (ep_project y)) y
}.

Arguments ep_embed {D E} _.
Arguments ep_project {D E} _.

(** * 6.3  The acceptable-structure functor *)

Inductive AIndex (Sig : Signature) : Type :=
| ai_T : forall n, TSym Sig n -> AIndex Sig
| ai_P : forall n, PSym Sig n -> AIndex Sig
| ai_L : forall n, LSym Sig n -> AIndex Sig
| ai_Q : QSym Sig -> AIndex Sig
| ai_var : nat -> AIndex Sig
| ai_slot : nat -> AIndex Sig
| ai_assert : AIndex Sig.

Arguments ai_T {Sig n} _.
Arguments ai_P {Sig n} _.
Arguments ai_L {Sig n} _.
Arguments ai_Q {Sig} _.
Arguments ai_var {Sig} _.
Arguments ai_slot {Sig} _.
Arguments ai_assert {Sig}.

Definition arity {Sig} (a : AIndex Sig) : nat :=
  match a with
  | @ai_T _ n _ => n
  | @ai_P _ n _ => n
  | @ai_L _ n _ => n
  | ai_Q _ => 1
  | ai_var _ => 0
  | ai_slot n => n
  | ai_assert => 1
  end.

Definition F_dcpo (Sig : Signature) (D : PDCPO) : PDCPO :=
  @dep_product_dcpo (AIndex Sig)
    (fun a => @scmap_dcpo (power_dcpo D (arity a)) D).

Definition F_embed (Sig : Signature) (D E : PDCPO) (ep : EPPair D E) :
    SCMap (F_dcpo Sig D) (F_dcpo Sig E) :=
  @dep_map_sc (AIndex Sig)
    (fun a => @scmap_dcpo (power_dcpo D (arity a)) D)
    (fun a => @scmap_dcpo (power_dcpo E (arity a)) E)
    (fun a => @prepost_map
      (power_dcpo E (arity a)) (power_dcpo D (arity a)) D E
      (@power_map E D (arity a) (ep_project ep)) (ep_embed ep)).

Definition F_project (Sig : Signature) (D E : PDCPO) (ep : EPPair D E) :
    SCMap (F_dcpo Sig E) (F_dcpo Sig D) :=
  @dep_map_sc (AIndex Sig)
    (fun a => @scmap_dcpo (power_dcpo E (arity a)) E)
    (fun a => @scmap_dcpo (power_dcpo D (arity a)) D)
    (fun a => @prepost_map
      (power_dcpo D (arity a)) (power_dcpo E (arity a)) E D
      (@power_map D E (arity a) (ep_embed ep)) (ep_project ep)).

Lemma power_ep_retract : forall D E (ep : EPPair D E) n
    (x : dcar (power_dcpo D n)),
    @power_map E D n (ep_project ep)
      (@power_map D E n (ep_embed ep) x) = x.
Proof.
  intros D E ep n x. apply functional_extensionality_dep. intro i.
  apply ep_retract.
Qed.

Lemma power_ep_approx : forall D E (ep : EPPair D E) n
    (x : dcar (power_dcpo E n)),
    dle (power_dcpo E n)
      (@power_map D E n (ep_embed ep)
        (@power_map E D n (ep_project ep) x)) x.
Proof. intros D E ep n x i. apply ep_approx. Qed.

Definition F_ep_pair (Sig : Signature) (D E : PDCPO) (ep : EPPair D E) :
    EPPair (F_dcpo Sig D) (F_dcpo Sig E).
Proof.
  refine {| ep_embed := F_embed Sig ep; ep_project := F_project Sig ep |}.
  - intro M. apply functional_extensionality_dep. intro a. apply SCMap_ext. intro x.
    unfold F_project, F_embed.
    set (ix := @power_map D E (arity a) (ep_embed ep) x).
    set (rix := @power_map E D (arity a) (ep_project ep) ix).
    change (ep_project ep (ep_embed ep (M a rix)) = M a x).
    unfold rix, ix.
    rewrite power_ep_retract. apply ep_retract.
  - intros N a x.
    unfold F_project, F_embed.
    change (dle E
      (ep_embed ep (ep_project ep
        (N a (@power_map D E (arity a) (ep_embed ep)
          (@power_map E D (arity a) (ep_project ep) x)))))
      (N a x)).
    eapply dle_trans.
    + apply ep_approx.
    + apply sc_monotone. apply power_ep_approx.
Defined.

(** * 7.1  The flat initial layer [D_0 = nat_bot] *)

Definition flat_nat := option nat.

Definition flat_le (x y : flat_nat) : Prop :=
  match x, y with
  | None, _ => True
  | Some n, Some m => n = m
  | Some _, None => False
  end.

Lemma flat_le_refl : forall x, flat_le x x.
Proof. destruct x; cbn; auto. Qed.

Lemma flat_le_trans : forall x y z,
    flat_le x y -> flat_le y z -> flat_le x z.
Proof.
  intros [n|] [m|] [k|] Hxy Hyz; cbn in *;
    try contradiction; auto; congruence.
Qed.

Lemma flat_le_antisym : forall x y,
    flat_le x y -> flat_le y x -> x = y.
Proof.
  intros [n|] [m|] Hxy Hyx; cbn in *;
    try contradiction; try reflexivity.
  now subst m.
Qed.

Lemma flat_common_some : forall n m z,
    flat_le (Some n) z -> flat_le (Some m) z -> n = m.
Proof.
  intros n m [k|] Hn Hm; cbn in *.
  - now transitivity k.
  - contradiction.
Qed.

Definition flat_sup (X : flat_nat -> Prop)
    (_ : directed flat_le X) : flat_nat :=
  match excluded_middle_informative (exists n, X (Some n)) with
  | left H => Some (proj1_sig (constructive_indefinite_description _ H))
  | right _ => None
  end.

Lemma flat_sup_lub : forall X (HX : directed flat_le X),
    is_lub flat_le X (@flat_sup X HX).
Proof.
  intros X HX. unfold flat_sup.
  destruct (excluded_middle_informative (exists n, X (Some n))) as [Hs|Hs].
  - destruct (constructive_indefinite_description
                (fun n : nat => X (Some n)) Hs) as [n Hn]. cbn.
    split.
    + intros x Hx. destruct x as [m|]; cbn; auto.
      destruct HX as [_ Hdir].
      destruct (Hdir (Some m) (Some n) Hx Hn)
        as (z & Hz & Hmz & Hnz).
      exact (flat_common_some Hmz Hnz).
    + intros v Hv. apply Hv. exact Hn.
  - split.
    + intros x Hx. destruct x as [n|]; cbn; auto.
      exfalso. apply Hs. now exists n.
    + intros v Hv. destruct v; cbn; auto.
Qed.

Definition flat_nat_dcpo : PDCPO.
Proof.
  refine {| dcar := flat_nat; dle := flat_le;
            dbot := None; dsup := flat_sup |}.
  - exact flat_le_refl.
  - exact flat_le_trans.
  - exact flat_le_antisym.
  - intros []; cbn; auto.
  - exact flat_sup_lub.
Defined.

Lemma flat_lub_some_attained : forall X HX n,
    dsup flat_nat_dcpo X HX = Some n -> X (Some n).
Proof.
  intros X HX n Hsup.
  unfold flat_nat_dcpo, flat_sup in Hsup; cbn in Hsup.
  destruct (excluded_middle_informative (exists k, X (Some k))) as [Hs|Hs].
  - destruct (constructive_indefinite_description
                (fun k : nat => X (Some k)) Hs) as [k Hk].
    cbn in Hsup. inversion Hsup; subst. exact Hk.
  - discriminate.
Qed.

(** * 7.2  The symmetric initial embedding-projection pair *)

Lemma orbit0_zero : forall H, orbit0 H 0.
Proof.
  intro H. exists pid. split; [apply hmem_pid | reflexivity].
Qed.

Lemma orbit0_lt3 : forall H i, orbit0 H i -> i < 3.
Proof.
  intros H i (g & Hg & ->). destruct g; cbn; lia.
Qed.

Definition empty_power (D : PDCPO) : dcar (power_dcpo D 0) :=
  fun i => match i with end.

Lemma empty_power_unique : forall D (x : dcar (power_dcpo D 0)),
    x = empty_power D.
Proof.
  intros D x. apply functional_extensionality_dep. intro i.
  exact (match i with end).
Qed.

Definition orbit_variable {Sig} (H : Subgroup) (a : AIndex Sig) : Prop :=
  match a with
  | ai_var i => orbit0 H i
  | _ => False
  end.

Definition orbit_variable_dec {Sig} (H : Subgroup) (a : AIndex Sig) :
    {orbit_variable H a} + {~ orbit_variable H a} :=
  excluded_middle_informative _.

Definition iota0_fun (Sig : Signature) (H : Subgroup)
    (d : dcar flat_nat_dcpo) : dcar (F_dcpo Sig flat_nat_dcpo) :=
  fun a =>
    if orbit_variable_dec H a
    then @sc_const (power_dcpo flat_nat_dcpo (arity a)) flat_nat_dcpo d
    else @sc_const (power_dcpo flat_nat_dcpo (arity a)) flat_nat_dcpo
                   (dbot flat_nat_dcpo).

Definition iota0 (Sig : Signature) (H : Subgroup) :
    SCMap flat_nat_dcpo (F_dcpo Sig flat_nat_dcpo).
Proof.
  refine {| sc_fun := @iota0_fun Sig H |}.
  - intros d e Hde a x. unfold iota0_fun.
    destruct (orbit_variable_dec H a); cbn.
    + exact Hde.
    + exact I.
  - intros X HX. split.
    + intros y (d & Hd & ->) a x. unfold iota0_fun.
      destruct (orbit_variable_dec H a); cbn.
      * apply (proj1 (dsup_lub flat_nat_dcpo X HX)). exact Hd.
      * exact I.
    + intros v Hv a x. unfold iota0_fun.
      destruct (orbit_variable_dec H a) as [Ha|Ha]; cbn.
      * apply (proj2 (dsup_lub flat_nat_dcpo X HX)).
        intros d Hd.
        pose proof (Hv (@iota0_fun Sig H d)) as Hdv.
        specialize (Hdv ltac:(exists d; auto)).
        specialize (Hdv a x). unfold iota0_fun in Hdv.
        destruct (orbit_variable_dec H a); cbn in Hdv;
          [exact Hdv | contradiction].
      * exact I.
Defined.

Lemma iota0_orbit : forall Sig H d i, orbit0 H i ->
    @iota0 Sig H d (ai_var i) (empty_power flat_nat_dcpo) = d.
Proof.
  intros Sig H d i Hi. unfold iota0, iota0_fun; cbn.
  destruct (orbit_variable_dec H (ai_var i)); cbn; [reflexivity|contradiction].
Qed.

Lemma iota0_off_orbit : forall Sig H d a,
    ~ orbit_variable H a ->
    @iota0 Sig H d a =
      @sc_const (power_dcpo flat_nat_dcpo (arity a))
                flat_nat_dcpo (dbot flat_nat_dcpo).
Proof.
  intros Sig H d a Ha. unfold iota0, iota0_fun; cbn.
  destruct (orbit_variable_dec H a); [contradiction|reflexivity].
Qed.

Definition var_value {Sig} (M : dcar (F_dcpo Sig flat_nat_dcpo))
    (i : nat) : dcar flat_nat_dcpo :=
  M (ai_var i) (empty_power flat_nat_dcpo).

Definition orbit_common {Sig} (H : Subgroup)
    (M : dcar (F_dcpo Sig flat_nat_dcpo))
    (d : dcar flat_nat_dcpo) : Prop :=
  forall i, orbit0 H i -> var_value M i = d.

Lemma orbit_common_unique : forall Sig H
    (M : dcar (F_dcpo Sig flat_nat_dcpo)) d e,
    orbit_common H M d -> orbit_common H M e -> d = e.
Proof.
  intros Sig H M d e Hd He.
  specialize (Hd 0 (orbit0_zero H)).
  specialize (He 0 (orbit0_zero H)).
  now rewrite <- Hd, <- He.
Qed.

Definition rho0_fun (Sig : Signature) (H : Subgroup)
    (M : dcar (F_dcpo Sig flat_nat_dcpo)) : dcar flat_nat_dcpo :=
  match excluded_middle_informative (exists d, orbit_common H M d) with
  | left Hex =>
      proj1_sig (constructive_indefinite_description
        (fun d : dcar flat_nat_dcpo => orbit_common H M d) Hex)
  | right _ => dbot flat_nat_dcpo
  end.

Lemma rho0_of_common : forall Sig H
    (M : dcar (F_dcpo Sig flat_nat_dcpo)) d,
    orbit_common H M d -> @rho0_fun Sig H M = d.
Proof.
  intros Sig H M d Hd. unfold rho0_fun.
  destruct (excluded_middle_informative (exists e, orbit_common H M e))
    as [Hex|Hnone].
  - destruct (constructive_indefinite_description
      (fun e : dcar flat_nat_dcpo => orbit_common H M e) Hex) as [e He].
    cbn. apply (@orbit_common_unique Sig H M); assumption.
  - exfalso. apply Hnone. now exists d.
Qed.

Lemma rho0_result_common : forall Sig H
    (M : dcar (F_dcpo Sig flat_nat_dcpo)),
    @rho0_fun Sig H M <> dbot flat_nat_dcpo ->
    orbit_common H M (@rho0_fun Sig H M).
Proof.
  intros Sig H M Hnb. unfold rho0_fun in *.
  destruct (excluded_middle_informative (exists d, orbit_common H M d))
    as [Hex|Hnone]; [|contradiction].
  destruct (constructive_indefinite_description
    (fun d : dcar flat_nat_dcpo => orbit_common H M d) Hex) as [d Hd].
  exact Hd.
Qed.

Lemma rho0_monotone : forall Sig H
    (M N : dcar (F_dcpo Sig flat_nat_dcpo)),
    dle (F_dcpo Sig flat_nat_dcpo) M N ->
    dle flat_nat_dcpo (@rho0_fun Sig H M) (@rho0_fun Sig H N).
Proof.
  intros Sig H M N HMN.
  destruct (@rho0_fun Sig H M) as [n|] eqn:HM; cbn; auto.
  assert (HcommonM : orbit_common H M (Some n)).
  { pose proof (@rho0_result_common Sig H M) as Hc.
    rewrite HM in Hc. apply Hc. discriminate. }
  assert (HcommonN : orbit_common H N (Some n)).
  { intros i Hi. specialize (HcommonM i Hi).
    pose proof (HMN (ai_var i) (empty_power flat_nat_dcpo)) as Hle.
    unfold var_value in *. rewrite HcommonM in Hle.
    destruct (N (ai_var i) (empty_power flat_nat_dcpo)) as [m|]
      eqn:HN; cbn in Hle.
    - f_equal. symmetry. exact Hle.
    - contradiction. }
  rewrite (@rho0_of_common Sig H N (Some n) HcommonN). reflexivity.
Qed.

Lemma rho0_iota0 : forall Sig H d,
    @rho0_fun Sig H (@iota0 Sig H d) = d.
Proof.
  intros Sig H d. apply rho0_of_common.
  intros i Hi. unfold var_value. apply iota0_orbit. exact Hi.
Qed.

Lemma dep_dsup_apply : forall I (D : I -> PDCPO)
    (X : dcar (@dep_product_dcpo I D) -> Prop)
    (HX : directed (dle (@dep_product_dcpo I D)) X) i,
    dsup (@dep_product_dcpo I D) X HX i =
    dsup (D i) (fun y => exists x, X x /\ y = x i)
      (@eval_image_directed I D X HX i).
Proof. reflexivity. Qed.

Lemma scmap_dsup_apply : forall D E (F : SCMap D E -> Prop)
    (HF : directed (scmap_le D E) F) x,
    dsup (@scmap_dcpo D E) F HF x =
    dsup E (@eval_set D E F x) (@eval_set_directed D E F HF x).
Proof. reflexivity. Qed.

Lemma F_lub_var_some_attained : forall Sig
    (X : dcar (F_dcpo Sig flat_nat_dcpo) -> Prop)
    (HX : directed (dle (F_dcpo Sig flat_nat_dcpo)) X) i n,
    var_value (dsup (F_dcpo Sig flat_nat_dcpo) X HX) i = Some n ->
    exists M, X M /\ var_value M i = Some n.
Proof.
  intros Sig X HX i n H.
  unfold var_value in H. unfold F_dcpo in H.
  rewrite dep_dsup_apply in H. rewrite scmap_dsup_apply in H.
  apply flat_lub_some_attained in H.
  destruct H as (J & (M & HM & HJ) & Hval).
  subst J. exists M. split; [exact HM |].
  unfold var_value. symmetry. exact Hval.
Qed.

Lemma flat_some_below_eq : forall n y,
    flat_le (Some n) y -> y = Some n.
Proof.
  intros n [m|] H; cbn in H; [|contradiction].
  subst m. reflexivity.
Qed.

Definition rho0 (Sig : Signature) (H : Subgroup) :
    SCMap (F_dcpo Sig flat_nat_dcpo) flat_nat_dcpo.
Proof.
  refine {| sc_fun := @rho0_fun Sig H;
            sc_monotone := @rho0_monotone Sig H |}.
  intros X HX. split.
  - intros y (M & HM & ->). apply rho0_monotone.
    apply (proj1 (dsup_lub (F_dcpo Sig flat_nat_dcpo) X HX)). exact HM.
  - intros v Hv.
    destruct (@rho0_fun Sig H (dsup (F_dcpo Sig flat_nat_dcpo) X HX))
      as [n|] eqn:Hrho; cbn; [|exact I].
    assert (Hcommon : orbit_common H
      (dsup (F_dcpo Sig flat_nat_dcpo) X HX) (Some n)).
    { pose proof (@rho0_result_common Sig H
        (dsup (F_dcpo Sig flat_nat_dcpo) X HX)) as Hc.
      rewrite Hrho in Hc. apply Hc. discriminate. }
    assert (Hatt : forall i, orbit0 H i ->
        exists M, X M /\ var_value M i = Some n).
    { intros i Hi. apply (@F_lub_var_some_attained Sig X HX i n).
      apply Hcommon. exact Hi. }
    destruct (Hatt 0 (orbit0_zero H)) as (M0 & HM0 & HM0v).
    destruct (excluded_middle_informative (orbit0 H 1)) as [Ho1|Hno1].
    + destruct (Hatt 1 Ho1) as (M1 & HM1 & HM1v).
      assert (HM1p : orbit0 H 1 -> var_value M1 1 = Some n)
        by (intro; exact HM1v).
      destruct (excluded_middle_informative (orbit0 H 2)) as [Ho2|Hno2].
      * destruct (Hatt 2 Ho2) as (M2 & HM2 & HM2v).
        assert (HM2p : orbit0 H 2 -> var_value M2 2 = Some n)
          by (intro; exact HM2v).
        destruct HX as [Hne Hdir].
        destruct (Hdir M0 M1 HM0 HM1) as (M01 & HM01 & H001 & H101).
        destruct (Hdir M01 M2 HM01 HM2) as (Z & HZ & H01Z & H2Z).
        assert (HZcommon : orbit_common H Z (Some n)).
        { intros i Hi. assert (Hi012 : i = 0 \/ i = 1 \/ i = 2) by
              (pose proof (orbit0_lt3 Hi); lia).
          destruct Hi012 as [H0|[H1|H2]]; subst i.
          - apply flat_some_below_eq.
            unfold var_value in HM0v. rewrite <- HM0v.
            eapply flat_le_trans; [apply (H001 (ai_var 0)
              (empty_power flat_nat_dcpo))|apply (H01Z (ai_var 0)
              (empty_power flat_nat_dcpo))].
          - apply flat_some_below_eq.
            unfold var_value in HM1v. rewrite <- HM1v.
            eapply flat_le_trans; [apply (H101 (ai_var 1)
              (empty_power flat_nat_dcpo))|apply (H01Z (ai_var 1)
              (empty_power flat_nat_dcpo))].
          - apply flat_some_below_eq. unfold var_value in HM2v.
            rewrite <- HM2v. apply (H2Z (ai_var 2)
              (empty_power flat_nat_dcpo)). }
        pose proof (Hv (@rho0_fun Sig H Z)) as HZv.
        specialize (HZv ltac:(exists Z; split; [exact HZ|reflexivity])).
        rewrite (@rho0_of_common Sig H Z (Some n) HZcommon) in HZv.
        exact HZv.
      * assert (HM2p : orbit0 H 2 -> var_value M0 2 = Some n)
          by (intro Hbad; contradiction).
        destruct HX as [Hne Hdir].
        destruct (Hdir M0 M1 HM0 HM1) as (Z & HZ & H0Z & H1Z).
        assert (HZcommon : orbit_common H Z (Some n)).
        { intros i Hi. assert (Hi012 : i = 0 \/ i = 1 \/ i = 2) by
              (pose proof (orbit0_lt3 Hi); lia).
          destruct Hi012 as [H0|[H1|H2]]; subst i.
          - apply flat_some_below_eq. unfold var_value in HM0v.
            rewrite <- HM0v. apply (H0Z (ai_var 0)
              (empty_power flat_nat_dcpo)).
          - apply flat_some_below_eq. unfold var_value in HM1v.
            rewrite <- HM1v. apply (H1Z (ai_var 1)
              (empty_power flat_nat_dcpo)).
          - exfalso. exact (Hno2 Hi). }
        pose proof (Hv (@rho0_fun Sig H Z)) as HZv.
        specialize (HZv ltac:(exists Z; split; [exact HZ|reflexivity])).
        rewrite (@rho0_of_common Sig H Z (Some n) HZcommon) in HZv.
        exact HZv.
    + assert (HM1p : orbit0 H 1 -> var_value M0 1 = Some n)
        by (intro Hbad; contradiction).
      destruct (excluded_middle_informative (orbit0 H 2)) as [Ho2|Hno2].
      * destruct (Hatt 2 Ho2) as (M2 & HM2 & HM2v).
        destruct HX as [Hne Hdir].
        destruct (Hdir M0 M2 HM0 HM2) as (Z & HZ & H0Z & H2Z).
        assert (HZcommon : orbit_common H Z (Some n)).
        { intros i Hi. assert (Hi012 : i = 0 \/ i = 1 \/ i = 2) by
              (pose proof (orbit0_lt3 Hi); lia).
          destruct Hi012 as [H0|[H1|H2]]; subst i.
          - apply flat_some_below_eq. unfold var_value in HM0v.
            rewrite <- HM0v. apply (H0Z (ai_var 0)
              (empty_power flat_nat_dcpo)).
          - exfalso. exact (Hno1 Hi).
          - apply flat_some_below_eq. unfold var_value in HM2v.
            rewrite <- HM2v. apply (H2Z (ai_var 2)
              (empty_power flat_nat_dcpo)). }
        pose proof (Hv (@rho0_fun Sig H Z)) as HZv.
        specialize (HZv ltac:(exists Z; split; [exact HZ|reflexivity])).
        rewrite (@rho0_of_common Sig H Z (Some n) HZcommon) in HZv.
        exact HZv.
      * assert (HZcommon : orbit_common H M0 (Some n)).
        { intros i Hi. assert (Hi012 : i = 0 \/ i = 1 \/ i = 2) by
              (pose proof (orbit0_lt3 Hi); lia).
          destruct Hi012 as [H0|[H1|H2]]; subst i;
            [exact HM0v|contradiction|contradiction]. }
        pose proof (Hv (@rho0_fun Sig H M0)) as HM0upper.
        specialize (HM0upper ltac:(exists M0; split; [exact HM0|reflexivity])).
        rewrite (@rho0_of_common Sig H M0 (Some n) HZcommon) in HM0upper.
        exact HM0upper.
Defined.

Definition initial_ep (Sig : Signature) (H : Subgroup) :
    EPPair flat_nat_dcpo (F_dcpo Sig flat_nat_dcpo).
Proof.
  refine {| ep_embed := @iota0 Sig H; ep_project := @rho0 Sig H |}.
  - intro d. apply rho0_iota0.
  - intros M a x. unfold iota0, iota0_fun; cbn.
    destruct (orbit_variable_dec H a) as [Ha|Ha]; cbn; [|exact I].
    destruct a as [k f|k p|k l|q|i|k|]; cbn in Ha; try contradiction.
    rewrite (@empty_power_unique flat_nat_dcpo x).
    destruct (@rho0_fun Sig H M) as [n|] eqn:Hrho; cbn; [|exact I].
    pose proof (@rho0_result_common Sig H M) as Hcommon.
    rewrite Hrho in Hcommon. specialize (Hcommon ltac:(discriminate)).
    specialize (Hcommon i Ha). unfold var_value in Hcommon.
    destruct (M (ai_var i) (empty_power flat_nat_dcpo)) as [m|]
      eqn:HM; cbn in *.
    + rewrite HM. cbn. injection Hcommon as Hmn. symmetry. exact Hmn.
    + rewrite HM. cbn. discriminate Hcommon.
Defined.

(** * 7.3  The recursively generated ep-chain *)

Lemma ep_project_bottom : forall D E (ep : EPPair D E),
    ep_project ep (dbot E) = dbot D.
Proof.
  intros D E ep. apply (dle_antisym D).
  - rewrite <- (ep_retract ep (dbot D)). apply sc_monotone.
    apply dbot_least.
  - apply dbot_least.
Qed.

Fixpoint D_level (Sig : Signature) (m : nat) : PDCPO :=
  match m with
  | 0 => flat_nat_dcpo
  | S k => F_dcpo Sig (D_level Sig k)
  end.

Fixpoint chain_ep (Sig : Signature) (H : Subgroup) (m : nat) :
    EPPair (D_level Sig m) (D_level Sig (S m)) :=
  match m as k return EPPair (D_level Sig k) (D_level Sig (S k)) with
  | 0 => initial_ep Sig H
  | S k => F_ep_pair Sig (chain_ep Sig H k)
  end.

Definition chain_iota Sig H m :
    SCMap (D_level Sig m) (D_level Sig (S m)) :=
  ep_embed (chain_ep Sig H m).

Definition chain_rho Sig H m :
    SCMap (D_level Sig (S m)) (D_level Sig m) :=
  ep_project (chain_ep Sig H m).

Lemma chain_retract : forall Sig H m x,
    chain_rho Sig H m (chain_iota Sig H m x) = x.
Proof. intros; apply ep_retract. Qed.

Lemma chain_approx : forall Sig H m x,
    dle (D_level Sig (S m))
      (chain_iota Sig H m (chain_rho Sig H m x)) x.
Proof. intros; apply ep_approx. Qed.

Lemma chain_rho_bottom : forall Sig H m,
    chain_rho Sig H m (dbot (D_level Sig (S m))) =
    dbot (D_level Sig m).
Proof. intros; apply ep_project_bottom. Qed.

(** * 7.4  The bilimit carrier and its pointed-dcpo structure *)

Record E_car (Sig : Signature) (H : Subgroup) : Type := {
  ecoord : forall m, dcar (D_level Sig m);
  ecoherent : forall m,
    chain_rho Sig H m (ecoord (S m)) = ecoord m
}.

Arguments ecoord {Sig H} _ _.

Definition E_le {Sig H} (x y : E_car Sig H) : Prop :=
  forall m, dle (D_level Sig m) (ecoord x m) (ecoord y m).

Definition E_bottom (Sig : Signature) (H : Subgroup) : E_car Sig H.
Proof.
  refine {| ecoord := fun m => dbot (D_level Sig m) |}.
  intro m. apply chain_rho_bottom.
Defined.

Lemma E_ext : forall Sig H (x y : E_car Sig H),
    (forall m, ecoord x m = ecoord y m) -> x = y.
Proof.
  intros Sig H [x Hx] [y Hy] Heq. cbn in Heq.
  assert (Hxy : x = y) by (apply functional_extensionality_dep; exact Heq).
  subst y. f_equal. apply proof_irrelevance.
Qed.

Definition E_coord_set {Sig H} (X : E_car Sig H -> Prop) (m : nat)
    (d : dcar (D_level Sig m)) : Prop :=
  exists x, X x /\ d = ecoord x m.

Arguments E_coord_set {Sig H} X m d.

Lemma E_coord_directed : forall Sig H (X : E_car Sig H -> Prop),
    directed E_le X -> forall m,
    directed (dle (D_level Sig m)) (E_coord_set X m).
Proof.
  intros Sig H X [[x Hx] Hdir] m. split.
  - exists (ecoord x m), x. auto.
  - intros a b [x1 [Hx1 ->]] [x2 [Hx2 ->]].
    destruct (Hdir x1 x2 Hx1 Hx2) as (z & Hz & H1z & H2z).
    exists (ecoord z m). split.
    + exists z. auto.
    + split; [apply H1z | apply H2z].
Qed.

Definition E_sup_coord {Sig H} (X : E_car Sig H -> Prop)
    (HX : directed E_le X) (m : nat) : dcar (D_level Sig m) :=
  dsup (D_level Sig m) (E_coord_set X m)
    (@E_coord_directed Sig H X HX m).

Lemma E_sup_coherent : forall Sig H X HX m,
    chain_rho Sig H m (@E_sup_coord Sig H X HX (S m)) =
    @E_sup_coord Sig H X HX m.
Proof.
  intros Sig H X HX m.
  apply (@lub_unique (D_level Sig m) (E_coord_set X m)).
  - pose proof (@sc_pres_lub (D_level Sig (S m)) (D_level Sig m)
      (chain_rho Sig H m) (E_coord_set X (S m))
      (@E_coord_directed Sig H X HX (S m))) as Hrho.
    split.
    + intros d (x & Hx & ->).
      destruct Hrho as [Hub Hleast]. apply Hub.
      exists (ecoord x (S m)). split.
      * exists x. auto.
      * rewrite ecoherent. reflexivity.
    + intros v Hv. destruct Hrho as [Hub Hleast]. apply Hleast.
      intros d (e & (x & Hx & He) & Hd). subst d. subst e.
      rewrite ecoherent. apply Hv. exists x. auto.
  - apply dsup_lub.
Qed.

Definition E_sup {Sig H} (X : E_car Sig H -> Prop)
    (HX : directed E_le X) : E_car Sig H :=
  {| ecoord := @E_sup_coord Sig H X HX;
     ecoherent := @E_sup_coherent Sig H X HX |}.

Definition E_dcpo (Sig : Signature) (H : Subgroup) : PDCPO.
Proof.
  refine {| dcar := E_car Sig H; dle := E_le;
            dbot := E_bottom Sig H; dsup := @E_sup Sig H |}.
  - intros x m. apply dle_refl.
  - intros x y z Hxy Hyz m. eapply dle_trans; [apply Hxy|apply Hyz].
  - intros x y Hxy Hyx. apply E_ext. intro m.
    apply (dle_antisym (D_level Sig m)); [apply Hxy|apply Hyx].
  - intros x m. apply dbot_least.
  - intros X HX. split.
    + intros x Hx m. apply (proj1 (dsup_lub (D_level Sig m)
        (E_coord_set X m) (@E_coord_directed Sig H X HX m))).
      exists x. auto.
    + intros y Hy m. apply (proj2 (dsup_lub (D_level Sig m)
        (E_coord_set X m) (@E_coord_directed Sig H X HX m))).
      intros d (x & Hx & ->). apply Hy. exact Hx.
Defined.

Definition pi_map (Sig : Signature) (H : Subgroup) (m : nat) :
    SCMap (E_dcpo Sig H) (D_level Sig m).
Proof.
  refine (@Build_SCMap (E_dcpo Sig H) (D_level Sig m)
    (fun (x : E_car Sig H) => ecoord x m) _ _).
  - intros x y Hxy. apply Hxy.
  - intros X HX. apply dsup_lub.
Defined.

Fixpoint embed_iter (Sig : Signature) (H : Subgroup) (m n : nat) :
    SCMap (D_level Sig m) (D_level Sig (n + m)) :=
  match n as q return SCMap (D_level Sig m) (D_level Sig (q + m)) with
  | 0 => sc_id (D_level Sig m)
  | S q => @sc_comp (D_level Sig m) (D_level Sig (q + m))
              (D_level Sig (S (q + m)))
              (chain_iota Sig H (q + m)) (embed_iter Sig H m q)
  end.

Fixpoint project_iter (Sig : Signature) (H : Subgroup) (m n : nat) :
    SCMap (D_level Sig (n + m)) (D_level Sig m) :=
  match n as q return SCMap (D_level Sig (q + m)) (D_level Sig m) with
  | 0 => sc_id (D_level Sig m)
  | S q => @sc_comp (D_level Sig (S (q + m)))
              (D_level Sig (q + m)) (D_level Sig m)
              (project_iter Sig H m q) (chain_rho Sig H (q + m))
  end.

Definition sc_cod_cast (Sig : Signature) (m k l : nat) (p : k = l)
    (f : SCMap (D_level Sig m) (D_level Sig k)) :
    SCMap (D_level Sig m) (D_level Sig l) :=
  match p in _ = q return SCMap (D_level Sig m) (D_level Sig q) with
  | eq_refl => f
  end.

Definition sc_dom_cast (Sig : Signature) (m k l : nat) (p : k = l)
    (f : SCMap (D_level Sig k) (D_level Sig m)) :
    SCMap (D_level Sig l) (D_level Sig m) :=
  match p in _ = q return SCMap (D_level Sig q) (D_level Sig m) with
  | eq_refl => f
  end.

Definition level_map (Sig : Signature) (H : Subgroup) (m k : nat) :
    SCMap (D_level Sig m) (D_level Sig k) :=
  match Nat.eq_dec m k with
  | left Heq =>
      @sc_cod_cast Sig m m k Heq (sc_id (D_level Sig m))
  | right Hneq =>
      match le_lt_dec m k with
      | left Hmk =>
          @sc_cod_cast Sig m ((k - m) + m) k (Nat.sub_add m k Hmk)
            (embed_iter Sig H m (k - m))
      | right Hkm =>
          @sc_dom_cast Sig k ((m - k) + k) m
            (Nat.sub_add k m (Nat.lt_le_incl k m Hkm))
            (project_iter Sig H k (m - k))
      end
  end.

Lemma level_map_forward : forall Sig H m k (Hmk : m < k)
    (d : dcar (D_level Sig m)),
    level_map Sig H m k d =
    @sc_cod_cast Sig m ((k - m) + m) k
      (Nat.sub_add m k (Nat.lt_le_incl m k Hmk))
      (embed_iter Sig H m (k - m)) d.
Proof.
  intros Sig H m k Hmk d. unfold level_map.
  destruct (Nat.eq_dec m k) as [Heq|Hneq]; [lia|].
  destruct (le_lt_dec m k) as [Hmk'|Hkm]; [|lia].
  replace Hmk' with (Nat.lt_le_incl m k Hmk) by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma level_map_backward : forall Sig H m k (Hkm : k < m)
    (d : dcar (D_level Sig m)),
    level_map Sig H m k d =
    @sc_dom_cast Sig k ((m - k) + k) m
      (Nat.sub_add k m (Nat.lt_le_incl k m Hkm))
      (project_iter Sig H k (m - k)) d.
Proof.
  intros Sig H m k Hkm d. unfold level_map.
  destruct (Nat.eq_dec m k) as [Heq|Hneq]; [lia|].
  destruct (le_lt_dec m k) as [Hmk|Hkm']; [lia|].
  replace Hkm' with Hkm by apply proof_irrelevance. reflexivity.
Qed.

Lemma level_map_center : forall Sig H m (d : dcar (D_level Sig m)),
    level_map Sig H m m d = d.
Proof.
  intros Sig H m d. unfold level_map.
  destruct (Nat.eq_dec m m) as [Heq|Hneq]; [|contradiction].
  replace Heq with (eq_refl m) by apply proof_irrelevance. reflexivity.
Qed.

Inductive lower_value (Sig : Signature) (H : Subgroup)
    (m : nat) (d : dcar (D_level Sig m)) :
    forall k, dcar (D_level Sig k) -> Prop :=
| lower_here : @lower_value Sig H m d m d
| lower_down : forall k (x : dcar (D_level Sig (S k))),
    @lower_value Sig H m d (S k) x ->
    @lower_value Sig H m d k (chain_rho Sig H k x).

Inductive upper_value (Sig : Signature) (H : Subgroup)
    (m : nat) (d : dcar (D_level Sig m)) :
    forall k, dcar (D_level Sig k) -> Prop :=
| upper_here : @upper_value Sig H m d m d
| upper_up : forall k (x : dcar (D_level Sig k)),
    @upper_value Sig H m d k x ->
    @upper_value Sig H m d (S k) (chain_iota Sig H k x).

Arguments lower_here {Sig H m d}.
Arguments lower_down {Sig H m d k x} _.
Arguments upper_here {Sig H m d}.
Arguments upper_up {Sig H m d k x} _.

Lemma lower_compose : forall Sig H big (D : dcar (D_level Sig big))
    mid (d : dcar (D_level Sig mid)) k (x : dcar (D_level Sig k)),
    @lower_value Sig H big D mid d ->
    @lower_value Sig H mid d k x ->
    @lower_value Sig H big D k x.
Proof.
  intros Sig H big D mid d k x Htop Hlow.
  induction Hlow.
  - exact Htop.
  - apply lower_down. exact IHHlow.
Qed.

Lemma lower_exists : forall Sig H m (d : dcar (D_level Sig m)) k,
    k <= m -> exists x, @lower_value Sig H m d k x.
Proof.
  intros Sig H m. induction m as [|m IH]; intros d k Hkm.
  - assert (k = 0) by lia. subst k. exists d. apply lower_here.
  - destruct (Nat.eq_dec k (S m)) as [->|Hneq].
    + exists d. apply lower_here.
    + assert (Hkm' : k <= m) by lia.
      destruct (IH (chain_rho Sig H m d) k Hkm') as (x & Hx).
      exists x. eapply lower_compose.
      * exact (@lower_down Sig H (S m) d m d
          (@lower_here Sig H (S m) d)).
      * exact Hx.
Qed.

Lemma upper_exists : forall Sig H m (d : dcar (D_level Sig m)) k,
    m <= k -> exists x, @upper_value Sig H m d k x.
Proof.
  intros Sig H m d k. revert m d.
  induction k as [|k IH]; intros m d Hmk.
  - assert (m = 0) by lia. subst m. exists d. apply upper_here.
  - destruct (Nat.eq_dec m (S k)) as [->|Hneq].
    + exists d. apply upper_here.
    + assert (Hmk' : m <= k) by lia.
      destruct (IH m d Hmk') as (x & Hx).
      exists (chain_iota Sig H k x). apply upper_up. exact Hx.
Qed.

Lemma lower_index : forall Sig H m (d : dcar (D_level Sig m))
    k (x : dcar (D_level Sig k)),
    @lower_value Sig H m d k x -> k <= m.
Proof. intros Sig H m d k x Hx. induction Hx; lia. Qed.

Lemma upper_index : forall Sig H m (d : dcar (D_level Sig m))
    k (x : dcar (D_level Sig k)),
    @upper_value Sig H m d k x -> m <= k.
Proof. intros Sig H m d k x Hx. induction Hx; lia. Qed.

Lemma lower_unique : forall Sig H m (d : dcar (D_level Sig m))
    k (x y : dcar (D_level Sig k)),
    @lower_value Sig H m d k x -> @lower_value Sig H m d k y -> x = y.
Proof.
  intros Sig H m d k x y Hx. revert y.
  induction Hx; intros y Hy.
  - dependent destruction Hy.
    + reflexivity.
    + exfalso. pose proof (lower_index Hy). lia.
  - dependent destruction Hy.
    + exfalso. pose proof (lower_index Hx). lia.
    + f_equal. apply IHHx. exact Hy.
Qed.

Lemma upper_unique : forall Sig H m (d : dcar (D_level Sig m))
    k (x y : dcar (D_level Sig k)),
    @upper_value Sig H m d k x -> @upper_value Sig H m d k y -> x = y.
Proof.
  intros Sig H m d k x y Hx. revert y.
  induction Hx; intros y Hy.
  - dependent destruction Hy.
    + reflexivity.
    + exfalso. pose proof (upper_index Hy). lia.
  - dependent destruction Hy.
    + exfalso. pose proof (upper_index Hx). lia.
    + f_equal. apply IHHx. exact Hy.
Qed.

Definition lower_map_property Sig H m k
    (f : SCMap (D_level Sig m) (D_level Sig k)) : Prop :=
  forall d, @lower_value Sig H m d k (f d).

Definition upper_map_property Sig H m k
    (f : SCMap (D_level Sig m) (D_level Sig k)) : Prop :=
  forall d, @upper_value Sig H m d k (f d).

Lemma lower_map_exists : forall Sig H m k, k <= m ->
    exists f : SCMap (D_level Sig m) (D_level Sig k),
      @lower_map_property Sig H m k f.
Proof.
  intros Sig H m. induction m as [|m IH]; intros k Hkm.
  - assert (k = 0) by lia. subst k.
    exists (sc_id (D_level Sig 0)). intro d. apply lower_here.
  - destruct (Nat.eq_dec k (S m)) as [->|Hneq].
    + exists (sc_id (D_level Sig (S m))). intro d. apply lower_here.
    + assert (Hkm' : k <= m) by lia.
      destruct (IH k Hkm') as (f & Hf).
      exists (@sc_comp (D_level Sig (S m)) (D_level Sig m)
        (D_level Sig k) f (chain_rho Sig H m)).
      intro d. eapply lower_compose.
      * exact (@lower_down Sig H (S m) d m d
          (@lower_here Sig H (S m) d)).
      * apply Hf.
Qed.

Lemma upper_map_exists : forall Sig H m k, m <= k ->
    exists f : SCMap (D_level Sig m) (D_level Sig k),
      @upper_map_property Sig H m k f.
Proof.
  intros Sig H m k. revert m.
  induction k as [|k IH]; intros m Hmk.
  - assert (m = 0) by lia. subst m.
    exists (sc_id (D_level Sig 0)). intro d. apply upper_here.
  - destruct (Nat.eq_dec m (S k)) as [->|Hneq].
    + exists (sc_id (D_level Sig (S k))). intro d. apply upper_here.
    + assert (Hmk' : m <= k) by lia.
      destruct (IH m Hmk') as (f & Hf).
      exists (@sc_comp (D_level Sig m) (D_level Sig k)
        (D_level Sig (S k)) (chain_iota Sig H k) f).
      intro d. apply upper_up. apply Hf.
Qed.

Definition eta_coord_map (Sig : Signature) (H : Subgroup) (m k : nat) :
    SCMap (D_level Sig m) (D_level Sig k) :=
  match le_lt_dec k m with
  | left Hkm =>
      proj1_sig (constructive_indefinite_description
        (fun f : SCMap (D_level Sig m) (D_level Sig k) =>
          @lower_map_property Sig H m k f)
        (@lower_map_exists Sig H m k Hkm))
  | right Hmk =>
      proj1_sig (constructive_indefinite_description
        (fun f : SCMap (D_level Sig m) (D_level Sig k) =>
          @upper_map_property Sig H m k f)
        (@upper_map_exists Sig H m k (Nat.lt_le_incl m k Hmk)))
  end.

Lemma eta_coord_lower : forall Sig H m k (Hkm : k <= m) d,
    @lower_value Sig H m d k (eta_coord_map Sig H m k d).
Proof.
  intros Sig H m k Hkm d. unfold eta_coord_map.
  destruct (le_lt_dec k m) as [Hkm'|Hmk]; [|lia].
  destruct (constructive_indefinite_description
    (fun f : SCMap (D_level Sig m) (D_level Sig k) =>
      @lower_map_property Sig H m k f)
    (@lower_map_exists Sig H m k Hkm')) as [f Hf].
  apply Hf.
Qed.

Lemma eta_coord_upper : forall Sig H m k (Hmk : m < k) d,
    @upper_value Sig H m d k (eta_coord_map Sig H m k d).
Proof.
  intros Sig H m k Hmk d. unfold eta_coord_map.
  destruct (le_lt_dec k m) as [Hkm|Hmk']; [lia|].
  destruct (constructive_indefinite_description
    (fun f : SCMap (D_level Sig m) (D_level Sig k) =>
      @upper_map_property Sig H m k f)
    (@upper_map_exists Sig H m k (Nat.lt_le_incl m k Hmk'))) as [f Hf].
  apply Hf.
Qed.

Lemma eta_coord_coherent : forall Sig H m d k,
    chain_rho Sig H k (eta_coord_map Sig H m (S k) d) =
    eta_coord_map Sig H m k d.
Proof.
  intros Sig H m d k.
  destruct (le_lt_dec (S k) m) as [HSk|HmSk].
  - apply (@lower_unique Sig H m d k).
    + apply lower_down. apply eta_coord_lower. exact HSk.
    + apply eta_coord_lower. lia.
  - assert (Hmk : m <= k) by lia.
    destruct (Nat.eq_dec m k) as [HmkEq|HmkNe].
    + subst m.
      assert (Hk : eta_coord_map Sig H k k d = d).
      { apply (@lower_unique Sig H k d k).
        - apply eta_coord_lower. lia.
        - apply lower_here. }
      assert (HSkEq : eta_coord_map Sig H k (S k) d =
          chain_iota Sig H k d).
      { apply (@upper_unique Sig H k d (S k)).
        - apply eta_coord_upper. lia.
        - apply upper_up. apply upper_here. }
      rewrite HSkEq, Hk. apply chain_retract.
    + assert (HmkLt : m < k) by lia.
      assert (HSkEq : eta_coord_map Sig H m (S k) d =
          chain_iota Sig H k (eta_coord_map Sig H m k d)).
      { apply (@upper_unique Sig H m d (S k)).
        - apply eta_coord_upper. lia.
        - apply upper_up. apply eta_coord_upper. exact HmkLt. }
      rewrite HSkEq. apply chain_retract.
Qed.

Definition eta_point (Sig : Signature) (H : Subgroup) (m : nat)
    (d : dcar (D_level Sig m)) : E_car Sig H :=
  {| ecoord := fun k => eta_coord_map Sig H m k d;
     ecoherent := @eta_coord_coherent Sig H m d |}.

Definition eta_map (Sig : Signature) (H : Subgroup) (m : nat) :
    SCMap (D_level Sig m) (E_dcpo Sig H).
Proof.
  refine (@Build_SCMap (D_level Sig m) (E_dcpo Sig H)
    (@eta_point Sig H m) _ _).
  - intros d e Hde k. apply sc_monotone. exact Hde.
  - intros X HX. split.
    + intros y (d & Hd & ->) k. apply sc_monotone.
      apply (proj1 (dsup_lub (D_level Sig m) X HX)). exact Hd.
    + intros v Hv k.
      pose proof (@sc_pres_lub (D_level Sig m) (D_level Sig k)
        (eta_coord_map Sig H m k) X HX) as Hcoord.
      destruct Hcoord as [Hub Hleast]. apply Hleast.
      intros y (d & Hd & ->).
      pose proof (Hv (@eta_point Sig H m d)) as Hdv.
      specialize (Hdv ltac:(exists d; auto)). exact (Hdv k).
Defined.

Lemma pi_eta : forall Sig H m d,
    pi_map Sig H m (eta_map Sig H m d) = d.
Proof.
  intros Sig H m d. cbn.
  apply (@lower_unique Sig H m d m).
  - apply eta_coord_lower. lia.
  - apply lower_here.
Qed.

Lemma upper_compose : forall Sig H small (d : dcar (D_level Sig small))
    mid (e : dcar (D_level Sig mid)) k (x : dcar (D_level Sig k)),
    @upper_value Sig H small d mid e ->
    @upper_value Sig H mid e k x ->
    @upper_value Sig H small d k x.
Proof.
  intros Sig H small d mid e k x Hlow Hhigh.
  induction Hhigh.
  - exact Hlow.
  - apply upper_up. exact IHHhigh.
Qed.

Lemma ecoords_lower : forall Sig H (x : E_car Sig H) m k,
    k <= m -> @lower_value Sig H m (ecoord x m) k (ecoord x k).
Proof.
  intros Sig H x m. induction m as [|m IH]; intros k Hkm.
  - assert (k = 0) by lia. subst k. apply lower_here.
  - destruct (Nat.eq_dec k (S m)) as [->|Hneq].
    + apply lower_here.
    + assert (Hkm' : k <= m) by lia.
      eapply lower_compose.
      * pose proof (@lower_down Sig H (S m) (ecoord x (S m)) m
          (ecoord x (S m)) (@lower_here Sig H (S m) (ecoord x (S m))))
          as Hstep.
        rewrite ecoherent in Hstep. exact Hstep.
      * apply IH. exact Hkm'.
Qed.

Lemma upper_value_below_ecoord : forall Sig H (x : E_car Sig H) m k
    (y : dcar (D_level Sig k)),
    @upper_value Sig H m (ecoord x m) k y ->
    dle (D_level Sig k) y (ecoord x k).
Proof.
  intros Sig H x m k y Hy. induction Hy.
  - apply dle_refl.
  - eapply dle_trans.
    + apply sc_monotone. exact IHHy.
    + pose proof (@chain_approx Sig H k (ecoord x (S k))) as Happ.
      rewrite ecoherent in Happ. exact Happ.
Qed.

Lemma eta_pi_approx : forall Sig H m (x : E_car Sig H),
    E_le (eta_map Sig H m (pi_map Sig H m x)) x.
Proof.
  intros Sig H m x k. cbn.
  destruct (le_lt_dec k m) as [Hkm|Hmk].
  - assert (Heq : eta_coord_map Sig H m k (ecoord x m) = ecoord x k).
    { apply (@lower_unique Sig H m (ecoord x m) k).
      - apply eta_coord_lower. exact Hkm.
      - apply ecoords_lower. exact Hkm. }
    rewrite Heq. apply dle_refl.
  - apply (@upper_value_below_ecoord Sig H x m k
      (eta_coord_map Sig H m k (ecoord x m))).
    apply eta_coord_upper. exact Hmk.
Qed.

Definition bilimit_approx (Sig : Signature) (H : Subgroup)
    (x : E_car Sig H) (m : nat) : E_car Sig H :=
  eta_map Sig H m (pi_map Sig H m x).

Lemma bilimit_approx_at_center : forall Sig H (x : E_car Sig H) m,
    ecoord (@bilimit_approx Sig H x m) m = ecoord x m.
Proof. intros; apply pi_eta. Qed.

Lemma bilimit_approx_le : forall Sig H (x : E_car Sig H) m,
    E_le (@bilimit_approx Sig H x m) x.
Proof. intros; apply eta_pi_approx. Qed.

Lemma bilimit_approx_mono : forall Sig H (x : E_car Sig H) m n,
    m <= n -> E_le (@bilimit_approx Sig H x m)
                     (@bilimit_approx Sig H x n).
Proof.
  intros Sig H x m n Hmn k. unfold bilimit_approx; cbn.
  destruct (le_lt_dec k n) as [Hkn|Hnk].
  - assert (HnEq : eta_coord_map Sig H n k (ecoord x n) = ecoord x k).
    { apply (@lower_unique Sig H n (ecoord x n) k).
      - apply eta_coord_lower. exact Hkn.
      - apply ecoords_lower. exact Hkn. }
    rewrite HnEq. apply eta_pi_approx.
  - assert (HmnLt : m < n \/ m = n) by lia.
    destruct HmnLt as [HmnLt|Hmneq].
    2: { subst n. apply dle_refl. }
    assert (HmNrel : @upper_value Sig H m (ecoord x m) n
        (eta_coord_map Sig H m n (ecoord x m))).
    { apply eta_coord_upper. exact HmnLt. }
    assert (Htail : @upper_value Sig H n
        (eta_coord_map Sig H m n (ecoord x m)) k
        (eta_coord_map Sig H n k
          (eta_coord_map Sig H m n (ecoord x m)))).
    { apply eta_coord_upper. exact Hnk. }
    assert (Hfactor : eta_coord_map Sig H m k (ecoord x m) =
        eta_coord_map Sig H n k
          (eta_coord_map Sig H m n (ecoord x m))).
    { apply (@upper_unique Sig H m (ecoord x m) k).
      - apply eta_coord_upper. lia.
      - eapply upper_compose; eauto. }
    rewrite Hfactor. apply sc_monotone.
    apply eta_pi_approx.
Qed.

Definition bilimit_approx_set {Sig H} (x : E_car Sig H)
    (y : E_car Sig H) : Prop :=
  exists m, y = @bilimit_approx Sig H x m.

Lemma bilimit_approx_directed : forall Sig H (x : E_car Sig H),
    directed E_le (bilimit_approx_set x).
Proof.
  intros Sig H x. split.
  - exists (@bilimit_approx Sig H x 0). now exists 0.
  - intros y z (m & ->) (n & ->).
    exists (@bilimit_approx Sig H x (Nat.max m n)). split.
    + now exists (Nat.max m n).
    + split; apply bilimit_approx_mono; apply Nat.le_max_l || apply Nat.le_max_r.
Qed.

Lemma bilimit_density_lub : forall Sig H (x : E_car Sig H),
    is_lub E_le (bilimit_approx_set x) x.
Proof.
  intros Sig H x. split.
  - intros y (m & ->). apply bilimit_approx_le.
  - intros v Hv k.
    pose proof (Hv (@bilimit_approx Sig H x k)) as Hkv.
    specialize (Hkv ltac:(now exists k)). specialize (Hkv k).
    rewrite bilimit_approx_at_center in Hkv. exact Hkv.
Qed.

Theorem bilimit_density : forall Sig H (x : E_car Sig H),
    x = dsup (E_dcpo Sig H) (bilimit_approx_set x)
      (bilimit_approx_directed x).
Proof.
  intros Sig H x. symmetry.
  apply (@lub_unique (E_dcpo Sig H) (bilimit_approx_set x)).
  - apply dsup_lub.
  - apply bilimit_density_lub.
Qed.

(** * 7.5  The tail limit [L_H] and the tail-shift isomorphism *)

Record L_car (Sig : Signature) (H : Subgroup) : Type := {
  lcoord : forall m, dcar (D_level Sig (S m));
  lcoherent : forall m,
    chain_rho Sig H (S m) (lcoord (S m)) = lcoord m
}.

Arguments lcoord {Sig H} _ _.

Definition L_le {Sig H} (x y : L_car Sig H) : Prop :=
  forall m, dle (D_level Sig (S m)) (lcoord x m) (lcoord y m).

Definition L_bottom (Sig : Signature) (H : Subgroup) : L_car Sig H.
Proof.
  refine {| lcoord := fun m => dbot (D_level Sig (S m)) |}.
  intro m. apply chain_rho_bottom.
Defined.

Lemma L_ext : forall Sig H (x y : L_car Sig H),
    (forall m, lcoord x m = lcoord y m) -> x = y.
Proof.
  intros Sig H [x Hx] [y Hy] Heq. cbn in Heq.
  assert (Hxy : x = y) by (apply functional_extensionality_dep; exact Heq).
  subst y. f_equal. apply proof_irrelevance.
Qed.

Definition L_coord_set {Sig H} (X : L_car Sig H -> Prop) (m : nat)
    (d : dcar (D_level Sig (S m))) : Prop :=
  exists x, X x /\ d = lcoord x m.

Arguments L_coord_set {Sig H} X m d.

Lemma L_coord_directed : forall Sig H (X : L_car Sig H -> Prop),
    directed L_le X -> forall m,
    directed (dle (D_level Sig (S m))) (L_coord_set X m).
Proof.
  intros Sig H X [[x Hx] Hdir] m. split.
  - exists (lcoord x m), x. auto.
  - intros a b [x1 [Hx1 ->]] [x2 [Hx2 ->]].
    destruct (Hdir x1 x2 Hx1 Hx2) as (z & Hz & H1z & H2z).
    exists (lcoord z m). split; [exists z; auto|].
    split; [apply H1z|apply H2z].
Qed.

Definition L_sup_coord {Sig H} (X : L_car Sig H -> Prop)
    (HX : directed L_le X) (m : nat) : dcar (D_level Sig (S m)) :=
  dsup (D_level Sig (S m)) (L_coord_set X m)
    (@L_coord_directed Sig H X HX m).

Lemma L_sup_coherent : forall Sig H X HX m,
    chain_rho Sig H (S m) (@L_sup_coord Sig H X HX (S m)) =
    @L_sup_coord Sig H X HX m.
Proof.
  intros Sig H X HX m.
  apply (@lub_unique (D_level Sig (S m)) (L_coord_set X m)).
  - pose proof (@sc_pres_lub (D_level Sig (S (S m)))
      (D_level Sig (S m)) (chain_rho Sig H (S m))
      (L_coord_set X (S m)) (@L_coord_directed Sig H X HX (S m))) as Hrho.
    split.
    + intros d (x & Hx & ->). destruct Hrho as [Hub Hleast]. apply Hub.
      exists (lcoord x (S m)). split.
      * exists x. auto.
      * rewrite lcoherent. reflexivity.
    + intros v Hv. destruct Hrho as [Hub Hleast]. apply Hleast.
      intros d (e & (x & Hx & He) & Hd). subst d. subst e.
      rewrite lcoherent. apply Hv. exists x. auto.
  - apply dsup_lub.
Qed.

Definition L_sup {Sig H} (X : L_car Sig H -> Prop)
    (HX : directed L_le X) : L_car Sig H :=
  {| lcoord := @L_sup_coord Sig H X HX;
     lcoherent := @L_sup_coherent Sig H X HX |}.

Definition L_dcpo (Sig : Signature) (H : Subgroup) : PDCPO.
Proof.
  refine {| dcar := L_car Sig H; dle := L_le;
            dbot := L_bottom Sig H; dsup := @L_sup Sig H |}.
  - intros x m. apply dle_refl.
  - intros x y z Hxy Hyz m. eapply dle_trans; [apply Hxy|apply Hyz].
  - intros x y Hxy Hyx. apply L_ext. intro m.
    apply (dle_antisym (D_level Sig (S m))); [apply Hxy|apply Hyx].
  - intros x m. apply dbot_least.
  - intros X HX. split.
    + intros x Hx m. apply (proj1 (dsup_lub (D_level Sig (S m))
        (L_coord_set X m) (@L_coord_directed Sig H X HX m))).
      exists x. auto.
    + intros y Hy m. apply (proj2 (dsup_lub (D_level Sig (S m))
        (L_coord_set X m) (@L_coord_directed Sig H X HX m))).
      intros d (x & Hx & ->). apply Hy. exact Hx.
Defined.

Definition tau_point (Sig : Signature) (H : Subgroup)
    (x : E_car Sig H) : L_car Sig H :=
  {| lcoord := fun m => ecoord x (S m);
     lcoherent := fun m => ecoherent x (S m) |}.

Definition untau_point (Sig : Signature) (H : Subgroup)
    (y : L_car Sig H) : E_car Sig H.
Proof.
  refine {| ecoord := fun m =>
    match m with
    | 0 => chain_rho Sig H 0 (lcoord y 0)
    | S k => lcoord y k
    end |}.
  intro m. destruct m as [|m]; cbn.
  - reflexivity.
  - apply lcoherent.
Defined.

Lemma untau_tau : forall Sig H (x : E_car Sig H),
    @untau_point Sig H (@tau_point Sig H x) = x.
Proof.
  intros Sig H x. apply E_ext. intros [|m]; cbn.
  - exact (ecoherent x 0).
  - reflexivity.
Qed.

Lemma tau_untau : forall Sig H (y : L_car Sig H),
    @tau_point Sig H (@untau_point Sig H y) = y.
Proof. intros Sig H y. apply L_ext. intro m. reflexivity. Qed.

Definition tau_map (Sig : Signature) (H : Subgroup) :
    SCMap (E_dcpo Sig H) (L_dcpo Sig H).
Proof.
  refine (@Build_SCMap (E_dcpo Sig H) (L_dcpo Sig H)
    (@tau_point Sig H) _ _).
  - intros x y Hxy m. apply Hxy.
  - intros X HX. split.
    + intros y (x & Hx & ->) m. apply (proj1 (dsup_lub
        (D_level Sig (S m)) (E_coord_set X (S m))
        (@E_coord_directed Sig H X HX (S m)))). exists x. auto.
    + intros v Hv m. apply (proj2 (dsup_lub
        (D_level Sig (S m)) (E_coord_set X (S m))
        (@E_coord_directed Sig H X HX (S m)))).
      intros d (x & Hx & ->).
      pose proof (Hv (@tau_point Sig H x)) as Hxv.
      specialize (Hxv ltac:(exists x; auto)). exact (Hxv m).
Defined.

Definition untau_map (Sig : Signature) (H : Subgroup) :
    SCMap (L_dcpo Sig H) (E_dcpo Sig H).
Proof.
  refine (@Build_SCMap (L_dcpo Sig H) (E_dcpo Sig H)
    (@untau_point Sig H) _ _).
  - intros x y Hxy [|m]; cbn.
    + exact (@sc_monotone (D_level Sig 1) (D_level Sig 0)
        (chain_rho Sig H 0) (lcoord x 0) (lcoord y 0) (Hxy 0)).
    + apply Hxy.
  - intros X HX. split.
    + intros y (x & Hx & ->) [|m]; cbn.
      * apply (@sc_monotone (D_level Sig 1) (D_level Sig 0)
          (chain_rho Sig H 0)).
        apply (proj1 (dsup_lub (D_level Sig 1) (L_coord_set X 0)
          (@L_coord_directed Sig H X HX 0))). exists x. auto.
      * apply (proj1 (dsup_lub (D_level Sig (S m))
          (L_coord_set X m) (@L_coord_directed Sig H X HX m))).
        exists x. auto.
    + intros v Hv [|m]; cbn.
      * pose proof (@sc_pres_lub (D_level Sig 1) (D_level Sig 0)
          (chain_rho Sig H 0) (L_coord_set X 0)
          (@L_coord_directed Sig H X HX 0)) as Hrho.
        destruct Hrho as [Hub Hleast]. apply Hleast.
        intros d (e & (x & Hx & He) & Hd). subst d. subst e.
        pose proof (Hv (@untau_point Sig H x)) as Hxv.
        specialize (Hxv ltac:(exists x; auto)). exact (Hxv 0).
      * apply (proj2 (dsup_lub (D_level Sig (S m))
          (L_coord_set X m) (@L_coord_directed Sig H X HX m))).
        intros d (x & Hx & ->).
        pose proof (Hv (@untau_point Sig H x)) as Hxv.
        specialize (Hxv ltac:(exists x; auto)). exact (Hxv (S m)).
Defined.

Lemma untau_tau_map : forall Sig H x,
    untau_map Sig H (tau_map Sig H x) = x.
Proof. intros; apply untau_tau. Qed.

Lemma tau_untau_map : forall Sig H y,
    tau_map Sig H (untau_map Sig H y) = y.
Proof. intros; apply tau_untau. Qed.

Definition bilimit_ep (Sig : Signature) (H : Subgroup) (m : nat) :
    EPPair (D_level Sig m) (E_dcpo Sig H).
Proof.
  refine {| ep_embed := eta_map Sig H m; ep_project := pi_map Sig H m |}.
  - apply pi_eta.
  - apply eta_pi_approx.
Defined.

Lemma eta_iota_adjacent : forall Sig H m d,
    eta_map Sig H (S m) (chain_iota Sig H m d) =
    eta_map Sig H m d.
Proof.
  intros Sig H m d. apply E_ext. intro k. cbn.
  destruct (le_lt_dec k m) as [Hkm|Hmk].
  - apply (@lower_unique Sig H (S m) (chain_iota Sig H m d) k).
    + apply eta_coord_lower. lia.
    + eapply lower_compose.
      * pose proof (@lower_down Sig H (S m) (chain_iota Sig H m d)
          m (chain_iota Sig H m d)
          (@lower_here Sig H (S m) (chain_iota Sig H m d))) as Hstep.
        rewrite chain_retract in Hstep. exact Hstep.
      * apply eta_coord_lower. exact Hkm.
  - destruct (Nat.eq_dec k (S m)) as [->|Hneq].
    + change (eta_coord_map Sig H (S m) (S m) (chain_iota Sig H m d) =
        eta_coord_map Sig H m (S m) d).
      assert (Hleft : eta_coord_map Sig H (S m) (S m)
          (chain_iota Sig H m d) = chain_iota Sig H m d).
      { apply (@lower_unique Sig H (S m) (chain_iota Sig H m d) (S m)).
        - apply eta_coord_lower. lia.
        - apply lower_here. }
      rewrite Hleft. symmetry.
      apply (@upper_unique Sig H m d (S m)).
      * apply eta_coord_upper. lia.
      * apply upper_up. apply upper_here.
    + apply (@upper_unique Sig H m d k).
      * eapply upper_compose.
        -- exact (@upper_up Sig H m d m d (@upper_here Sig H m d)).
        -- apply eta_coord_upper. lia.
      * apply eta_coord_upper. exact Hmk.
Qed.

Lemma pi_adjacent : forall Sig H m (x : E_car Sig H),
    chain_rho Sig H m (pi_map Sig H (S m) x) = pi_map Sig H m x.
Proof. intros; apply ecoherent. Qed.

Lemma F_project_apply : forall Sig D E (ep : EPPair D E)
    (M : dcar (F_dcpo Sig E)) a x,
    F_project Sig ep M a x =
    ep_project ep (M a (@power_map D E (arity a) (ep_embed ep) x)).
Proof. reflexivity. Qed.

Definition kappa_point (Sig : Signature) (H : Subgroup)
    (M : dcar (F_dcpo Sig (E_dcpo Sig H))) : L_car Sig H.
Proof.
  refine {| lcoord := fun m => F_project Sig (bilimit_ep Sig H m) M |}.
  intro m. apply functional_extensionality_dep. intro a.
  apply SCMap_ext. intro x.
  change (chain_rho Sig H m
    (pi_map Sig H (S m)
      (M a (@power_map (D_level Sig (S m)) (E_dcpo Sig H) (arity a)
        (eta_map Sig H (S m))
        (@power_map (D_level Sig m) (D_level Sig (S m)) (arity a)
          (chain_iota Sig H m) x)))) =
    pi_map Sig H m
      (M a (@power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
        (eta_map Sig H m) x))).
  rewrite pi_adjacent.
  apply (f_equal (fun z => pi_map Sig H m z)).
  apply (f_equal (fun z => M a z)).
  apply functional_extensionality_dep. intro i.
  apply eta_iota_adjacent.
Defined.

Definition kappa_map (Sig : Signature) (H : Subgroup) :
    SCMap (F_dcpo Sig (E_dcpo Sig H)) (L_dcpo Sig H).
Proof.
  refine (@Build_SCMap (F_dcpo Sig (E_dcpo Sig H)) (L_dcpo Sig H)
    (@kappa_point Sig H) _ _).
  - intros M N HMN m. apply sc_monotone. exact HMN.
  - intros X HX. split.
    + intros y (M & HM & ->) m. apply sc_monotone.
      apply (proj1 (dsup_lub (F_dcpo Sig (E_dcpo Sig H)) X HX)). exact HM.
    + intros v Hv m.
      pose proof (@sc_pres_lub (F_dcpo Sig (E_dcpo Sig H))
        (F_dcpo Sig (D_level Sig m))
        (F_project Sig (bilimit_ep Sig H m)) X HX) as Hm.
      destruct Hm as [Hub Hleast]. apply Hleast.
      intros y (M & HM & ->).
      pose proof (Hv (@kappa_point Sig H M)) as HMv.
      specialize (HMv ltac:(exists M; auto)). exact (HMv m).
Defined.

Lemma lcoherent_apply : forall Sig H (y : L_car Sig H) m a x,
    chain_rho Sig H m
      (lcoord y (S m) a
        (@power_map (D_level Sig m) (D_level Sig (S m)) (arity a)
          (chain_iota Sig H m) x)) =
    lcoord y m a x.
Proof.
  intros Sig H y m a x.
  pose proof (f_equal (fun M => M a) (lcoherent y m)) as Heq1.
  pose proof (f_equal
    (fun f : SCMap (power_dcpo (D_level Sig m) (arity a))
                    (D_level Sig m) => sc_fun f x) Heq1) as Heq2.
  exact Heq2.
Qed.

Definition lambda_stage_map (Sig : Signature) (H : Subgroup)
    (y : L_car Sig H) (a : AIndex Sig) (m : nat) :
    SCMap (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H) :=
  @sc_comp (power_dcpo (E_dcpo Sig H) (arity a))
    (D_level Sig m) (E_dcpo Sig H) (eta_map Sig H m)
    (@sc_comp (power_dcpo (E_dcpo Sig H) (arity a))
      (power_dcpo (D_level Sig m) (arity a)) (D_level Sig m)
      (lcoord y m a)
      (@power_map (E_dcpo Sig H) (D_level Sig m) (arity a)
        (pi_map Sig H m))).

Arguments lambda_stage_map Sig H y a m : clear implicits.

Lemma lambda_stage_step : forall Sig H (y : L_car Sig H) a m,
    scmap_le (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
      (lambda_stage_map Sig H y a m)
      (lambda_stage_map Sig H y a (S m)).
Proof.
  intros Sig H y a m xs.
  change (E_le
    (eta_map Sig H m
      (lcoord y m a
        (@power_map (E_dcpo Sig H) (D_level Sig m) (arity a)
          (pi_map Sig H m) xs)))
    (eta_map Sig H (S m)
      (lcoord y (S m) a
        (@power_map (E_dcpo Sig H) (D_level Sig (S m)) (arity a)
          (pi_map Sig H (S m)) xs)))).
  rewrite <- eta_iota_adjacent.
  apply (@sc_monotone (D_level Sig (S m)) (E_dcpo Sig H)
    (eta_map Sig H (S m))).
  rewrite <- lcoherent_apply.
  eapply dle_trans.
  - apply (@chain_approx Sig H m).
  - apply (@sc_monotone
      (power_dcpo (D_level Sig (S m)) (arity a)) (D_level Sig (S m))
      (lcoord y (S m) a)). intro i.
    pose proof (@chain_approx Sig H m
      (pi_map Sig H (S m) (xs i))) as Hi.
    rewrite pi_adjacent in Hi. exact Hi.
Qed.

Lemma lambda_stage_mono : forall Sig H (y : L_car Sig H) a m n,
    m <= n ->
    scmap_le (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
      (lambda_stage_map Sig H y a m)
      (lambda_stage_map Sig H y a n).
Proof.
  intros Sig H y a m n Hmn. induction Hmn.
  - intros x. apply dle_refl.
  - intros x. eapply dle_trans; [apply IHHmn|apply lambda_stage_step].
Qed.

Definition lambda_stage_set {Sig H} (y : L_car Sig H) (a : AIndex Sig)
    (f : SCMap (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)) : Prop :=
  exists m, f = lambda_stage_map Sig H y a m.

Arguments lambda_stage_set {Sig H} y a f.

Lemma lambda_stage_directed : forall Sig H (y : L_car Sig H) a,
    directed (scmap_le (power_dcpo (E_dcpo Sig H) (arity a))
      (E_dcpo Sig H)) (lambda_stage_set y a).
Proof.
  intros Sig H y a. split.
  - exists (lambda_stage_map Sig H y a 0). now exists 0.
  - intros f g (m & ->) (n & ->).
    exists (lambda_stage_map Sig H y a (Nat.max m n)). split.
    + now exists (Nat.max m n).
    + split; apply lambda_stage_mono;
        [apply Nat.le_max_l|apply Nat.le_max_r].
Qed.

Definition lambda_coord (Sig : Signature) (H : Subgroup)
    (y : L_car Sig H) (a : AIndex Sig) :
    SCMap (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H) :=
  dsup (@scmap_dcpo (power_dcpo (E_dcpo Sig H) (arity a))
    (E_dcpo Sig H)) (lambda_stage_set y a)
    (lambda_stage_directed y a).

Definition lambda_point (Sig : Signature) (H : Subgroup)
    (y : L_car Sig H) : dcar (F_dcpo Sig (E_dcpo Sig H)) :=
  fun a => @lambda_coord Sig H y a.

Lemma eta_coord_upper_le : forall Sig H m k (Hmk : m <= k) d,
    @upper_value Sig H m d k (eta_coord_map Sig H m k d).
Proof.
  intros Sig H m k Hmk d.
  destruct (Nat.eq_dec m k) as [Heq|Hneq].
  - subst k. assert (Hcenter : eta_coord_map Sig H m m d = d).
    { apply (@lower_unique Sig H m d m).
      - apply eta_coord_lower. lia.
      - apply lower_here. }
    rewrite Hcenter. apply upper_here.
  - apply eta_coord_upper. lia.
Qed.

Lemma eta_coord_up_step : forall Sig H m n, m <= n ->
    forall d, eta_coord_map Sig H m (S n) d =
      chain_iota Sig H n (eta_coord_map Sig H m n d).
Proof.
  intros Sig H m n Hmn d.
  apply (@upper_unique Sig H m d (S n)).
  - apply eta_coord_upper. lia.
  - apply upper_up. apply eta_coord_upper_le. exact Hmn.
Qed.

Lemma earlier_coords_equal : forall Sig H (x z : E_car Sig H) m n,
    m <= n -> ecoord x n = ecoord z n -> ecoord x m = ecoord z m.
Proof.
  intros Sig H x z m n Hmn Heq.
  apply (@lower_unique Sig H n (ecoord x n) m).
  - apply ecoords_lower. exact Hmn.
  - rewrite Heq. apply ecoords_lower. exact Hmn.
Qed.

Definition lambda_value_set {Sig H} (y : L_car Sig H) (a : AIndex Sig)
    (xs : dcar (power_dcpo (E_dcpo Sig H) (arity a)))
    (e : E_car Sig H) : Prop :=
  exists m, e = lambda_stage_map Sig H y a m xs.

Arguments lambda_value_set {Sig H} y a xs e.

Lemma lambda_coord_lub : forall Sig H (y : L_car Sig H) a xs,
    is_lub E_le (lambda_value_set y a xs)
      (@lambda_coord Sig H y a xs).
Proof.
  intros Sig H y a xs. unfold lambda_coord.
  rewrite scmap_dsup_apply.
  pose proof (dsup_lub (E_dcpo Sig H)
    (@eval_set (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
      (lambda_stage_set y a) xs)
    (@eval_set_directed (power_dcpo (E_dcpo Sig H) (arity a))
      (E_dcpo Sig H) (lambda_stage_set y a)
      (lambda_stage_directed y a) xs)) as Hlub.
  split.
  - intros e (m & ->). apply (proj1 Hlub).
    exists (lambda_stage_map Sig H y a m). split.
    + now exists m.
    + reflexivity.
  - intros v Hv. apply (proj2 Hlub).
    intros e (f & (m & Hf) & He). subst f. subst e.
    apply Hv. now exists m.
Qed.

Lemma lambda_stage_self : forall Sig H (y : L_car Sig H) a m
    (x : dcar (power_dcpo (D_level Sig m) (arity a))),
    pi_map Sig H m
      (lambda_stage_map Sig H y a m
        (@power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
          (eta_map Sig H m) x)) =
    lcoord y m a x.
Proof.
  intros Sig H y a m x.
  change (pi_map Sig H m
    (eta_map Sig H m
      (lcoord y m a
        (@power_map (E_dcpo Sig H) (D_level Sig m) (arity a)
          (pi_map Sig H m)
          (@power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
            (eta_map Sig H m) x)))) = lcoord y m a x).
  rewrite pi_eta. apply (f_equal (fun z => lcoord y m a z)).
  apply functional_extensionality_dep. intro i. apply pi_eta.
Qed.

Lemma eta_center_down_one : forall Sig H n d,
    pi_map Sig H n (eta_map Sig H (S n) d) = chain_rho Sig H n d.
Proof.
  intros Sig H n d.
  pose proof (@eta_coord_coherent Sig H (S n) d n) as Hc.
  assert (Hcenter : eta_coord_map Sig H (S n) (S n) d = d).
  { apply (@lower_unique Sig H (S n) d (S n)).
    - apply eta_coord_lower. lia.
    - apply lower_here. }
  change (chain_rho Sig H n (eta_coord_map Sig H (S n) (S n) d) =
    eta_coord_map Sig H (S n) n d) in Hc.
  rewrite Hcenter in Hc.
  change (eta_coord_map Sig H (S n) n d = chain_rho Sig H n d).
  symmetry. exact Hc.
Qed.

Lemma lambda_stage_succ_projection : forall Sig H (y : L_car Sig H)
    a m n, m <= n ->
    forall (x : dcar (power_dcpo (D_level Sig m) (arity a))),
    pi_map Sig H n
      (lambda_stage_map Sig H y a (S n)
        (@power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
          (eta_map Sig H m) x)) =
    pi_map Sig H n
      (lambda_stage_map Sig H y a n
        (@power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
          (eta_map Sig H m) x)).
Proof.
  intros Sig H y a m n Hmn x.
  set (xs := @power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
    (eta_map Sig H m) x).
  change (pi_map Sig H n
    (eta_map Sig H (S n)
      (lcoord y (S n) a
        (@power_map (E_dcpo Sig H) (D_level Sig (S n)) (arity a)
          (pi_map Sig H (S n)) xs))) =
    pi_map Sig H n
      (eta_map Sig H n
        (lcoord y n a
          (@power_map (E_dcpo Sig H) (D_level Sig n) (arity a)
            (pi_map Sig H n) xs)))).
  rewrite eta_center_down_one, pi_eta.
  rewrite <- lcoherent_apply.
  apply (f_equal (fun z => chain_rho Sig H n (lcoord y (S n) a z))).
  apply functional_extensionality_dep. intro i. unfold xs; cbn.
  apply eta_coord_up_step. exact Hmn.
Qed.

Lemma lambda_stage_project_exact : forall Sig H (y : L_car Sig H)
    a m n, m <= n ->
    forall (x : dcar (power_dcpo (D_level Sig m) (arity a))),
    pi_map Sig H m
      (lambda_stage_map Sig H y a n
        (@power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
          (eta_map Sig H m) x)) =
    lcoord y m a x.
Proof.
  intros Sig H y a m n Hmn. induction Hmn; intro x.
  - apply lambda_stage_self.
  - set (xs := @power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
      (eta_map Sig H m) x).
    assert (Hhigh : pi_map Sig H m
        (lambda_stage_map Sig H y a (S m0) xs) =
        pi_map Sig H m (lambda_stage_map Sig H y a m0 xs)).
    { apply (@earlier_coords_equal Sig H
        (lambda_stage_map Sig H y a (S m0) xs)
        (lambda_stage_map Sig H y a m0 xs) m m0 Hmn).
      apply lambda_stage_succ_projection. exact Hmn. }
    rewrite Hhigh. apply IHHmn.
Qed.

Lemma lambda_value_directed : forall Sig H (y : L_car Sig H) a xs,
    directed E_le (lambda_value_set y a xs).
Proof.
  intros Sig H y a xs. split.
  - exists (lambda_stage_map Sig H y a 0 xs). now exists 0.
  - intros e f (m & ->) (n & ->).
    exists (lambda_stage_map Sig H y a (Nat.max m n) xs). split.
    + now exists (Nat.max m n).
    + split; apply lambda_stage_mono;
        [apply Nat.le_max_l|apply Nat.le_max_r].
Qed.

Lemma kappa_lambda_point : forall Sig H (y : L_car Sig H),
    @kappa_point Sig H (@lambda_point Sig H y) = y.
Proof.
  intros Sig H y. apply L_ext. intro m.
  apply functional_extensionality_dep. intro a. apply SCMap_ext. intro x.
  change (pi_map Sig H m
    (@lambda_coord Sig H y a
      (@power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
        (eta_map Sig H m) x)) = lcoord y m a x).
  set (xs := @power_map (D_level Sig m) (E_dcpo Sig H) (arity a)
    (eta_map Sig H m) x).
  assert (Hlub := @lambda_coord_lub Sig H y a xs).
  assert (Hdir := @lambda_value_directed Sig H y a xs).
  assert (Hsup : @lambda_coord Sig H y a xs =
      dsup (E_dcpo Sig H) (lambda_value_set y a xs) Hdir).
  { apply (@lub_unique (E_dcpo Sig H) (lambda_value_set y a xs)).
    - exact Hlub.
    - apply dsup_lub. }
  rewrite Hsup.
  pose proof (@sc_pres_lub (E_dcpo Sig H) (D_level Sig m)
    (pi_map Sig H m) (lambda_value_set y a xs) Hdir) as Hpi.
  apply (dle_antisym (D_level Sig m)).
  - destruct Hpi as [Hub Hleast]. apply Hleast.
    intros d (e & (n & He) & Hd). subst e. subst d.
    unfold xs.
    destruct (le_lt_dec n m) as [Hnm|Hmn].
    + eapply dle_trans.
      * apply sc_monotone. apply lambda_stage_mono. exact Hnm.
      * rewrite lambda_stage_self. apply dle_refl.
    + rewrite (@lambda_stage_project_exact Sig H y a m n
        (Nat.lt_le_incl m n Hmn) x). apply dle_refl.
  - destruct Hpi as [Hub Hleast]. apply Hub.
    exists (lambda_stage_map Sig H y a m xs). split.
    + now exists m.
    + unfold xs. rewrite lambda_stage_self. reflexivity.
Qed.

Definition bilimit_approx_map (Sig : Signature) (H : Subgroup) (m : nat) :
    SCMap (E_dcpo Sig H) (E_dcpo Sig H) :=
  @sc_comp (E_dcpo Sig H) (D_level Sig m) (E_dcpo Sig H)
    (eta_map Sig H m) (pi_map Sig H m).

Lemma bilimit_approx_map_apply : forall Sig H m (x : E_car Sig H),
    bilimit_approx_map Sig H m x = @bilimit_approx Sig H x m.
Proof. reflexivity. Qed.

Lemma bilimit_approx_arg_mono : forall Sig H m (x z : E_car Sig H),
    E_le x z -> E_le (@bilimit_approx Sig H x m)
                         (@bilimit_approx Sig H z m).
Proof.
  intros Sig H m x z Hxz. unfold bilimit_approx.
  apply (@sc_monotone (D_level Sig m) (E_dcpo Sig H)
    (eta_map Sig H m)).
  apply (@sc_monotone (E_dcpo Sig H) (D_level Sig m)
    (pi_map Sig H m)). exact Hxz.
Qed.

Definition power_bilimit_approx {Sig H} n
    (xs : dcar (power_dcpo (E_dcpo Sig H) n)) (m : nat) :
    dcar (power_dcpo (E_dcpo Sig H) n) :=
  @power_map (E_dcpo Sig H) (E_dcpo Sig H) n
    (bilimit_approx_map Sig H m) xs.

Arguments power_bilimit_approx {Sig H} n xs m.

Definition power_approx_set {Sig H} n
    (xs : dcar (power_dcpo (E_dcpo Sig H) n))
    (ys : dcar (power_dcpo (E_dcpo Sig H) n)) : Prop :=
  exists m, ys = power_bilimit_approx n xs m.

Arguments power_approx_set {Sig H} n xs ys.

Lemma power_approx_mono : forall Sig H n
    (xs : dcar (power_dcpo (E_dcpo Sig H) n)) m k,
    m <= k -> dle (power_dcpo (E_dcpo Sig H) n)
      (power_bilimit_approx n xs m) (power_bilimit_approx n xs k).
Proof. intros Sig H n xs m k Hmk i. apply bilimit_approx_mono. exact Hmk. Qed.

Lemma power_approx_directed : forall Sig H n
    (xs : dcar (power_dcpo (E_dcpo Sig H) n)),
    directed (dle (power_dcpo (E_dcpo Sig H) n))
      (power_approx_set n xs).
Proof.
  intros Sig H n xs. split.
  - exists (power_bilimit_approx n xs 0). now exists 0.
  - intros u v (m & ->) (k & ->).
    exists (power_bilimit_approx n xs (Nat.max m k)). split.
    + now exists (Nat.max m k).
    + split; apply power_approx_mono;
        [apply Nat.le_max_l|apply Nat.le_max_r].
Qed.

Lemma power_approx_lub : forall Sig H n
    (xs : dcar (power_dcpo (E_dcpo Sig H) n)),
    is_lub (dle (power_dcpo (E_dcpo Sig H) n))
      (power_approx_set n xs) xs.
Proof.
  intros Sig H n xs. split.
  - intros ys (m & ->) i. apply bilimit_approx_le.
  - intros v Hv i.
    apply (proj2 (@bilimit_density_lub Sig H (xs i))).
    intros e (m & ->).
    pose proof (Hv (power_bilimit_approx n xs m)) as Hm.
    specialize (Hm ltac:(now exists m)). exact (Hm i).
Qed.

Lemma lambda_kappa_stage : forall Sig H
    (M : dcar (F_dcpo Sig (E_dcpo Sig H))) a m xs,
    lambda_stage_map Sig H (@kappa_point Sig H M) a m xs =
    @bilimit_approx Sig H
      (M a (power_bilimit_approx (arity a) xs m)) m.
Proof. reflexivity. Qed.

Lemma diagonal_stages_lub : forall Sig H
    (M : dcar (F_dcpo Sig (E_dcpo Sig H))) a xs,
    is_lub E_le
      (lambda_value_set (@kappa_point Sig H M) a xs) (M a xs).
Proof.
  intros Sig H M a xs. split.
  - intros e (m & ->). rewrite lambda_kappa_stage.
    eapply (@dle_trans (E_dcpo Sig H)).
    + exact (@bilimit_approx_le Sig H
        (M a (power_bilimit_approx (arity a) xs m)) m).
    + apply (@sc_monotone
        (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H) (M a)).
      intro i. exact (@bilimit_approx_le Sig H (xs i) m).
  - intros v Hv.
    pose proof (@sc_pres_lub
      (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
      (M a) (power_approx_set (arity a) xs)
      (@power_approx_directed Sig H (arity a) xs)) as HMlub.
    assert (Hxs : dsup (power_dcpo (E_dcpo Sig H) (arity a))
        (power_approx_set (arity a) xs)
        (@power_approx_directed Sig H (arity a) xs) = xs).
    { apply (@lub_unique (power_dcpo (E_dcpo Sig H) (arity a))
        (power_approx_set (arity a) xs)).
      - apply dsup_lub.
      - apply power_approx_lub. }
    rewrite Hxs in HMlub. destruct HMlub as [HubM HleastM].
    apply HleastM. intros z (ys & (n & ->) & ->).
    apply (proj2 (@bilimit_density_lub Sig H
      (M a (power_bilimit_approx (arity a) xs n)))).
    intros e (k & ->).
    set (r := Nat.max n k).
    eapply (@dle_trans (E_dcpo Sig H)).
    + apply bilimit_approx_mono. apply Nat.le_max_r.
    + eapply (@dle_trans (E_dcpo Sig H)).
      * apply bilimit_approx_arg_mono.
        apply (@sc_monotone
          (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H) (M a)).
        apply power_approx_mono. apply Nat.le_max_l.
      * apply Hv. exists r. symmetry. apply lambda_kappa_stage.
Qed.

Lemma lambda_kappa_point : forall Sig H
    (M : dcar (F_dcpo Sig (E_dcpo Sig H))),
    @lambda_point Sig H (@kappa_point Sig H M) = M.
Proof.
  intros Sig H M. apply functional_extensionality_dep. intro a.
  apply SCMap_ext. intro xs.
  apply (@lub_unique (E_dcpo Sig H)
    (lambda_value_set (@kappa_point Sig H M) a xs)).
  - apply lambda_coord_lub.
  - apply diagonal_stages_lub.
Qed.

Lemma lambda_stage_arg_mono : forall Sig H
    (y z : L_car Sig H) a m,
    L_le y z ->
    scmap_le (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
      (lambda_stage_map Sig H y a m)
      (lambda_stage_map Sig H z a m).
Proof.
  intros Sig H y z a m Hyz xs.
  apply (@sc_monotone (D_level Sig m) (E_dcpo Sig H)
    (eta_map Sig H m)).
  apply (Hyz m a).
Qed.

Lemma lambda_coord_monotone : forall Sig H
    (y z : L_car Sig H) a,
    L_le y z ->
    scmap_le (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
      (@lambda_coord Sig H y a) (@lambda_coord Sig H z a).
Proof.
  intros Sig H y z a Hyz xs.
  apply (proj2 (dsup_lub (E_dcpo Sig H)
    (@eval_set (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
      (lambda_stage_set y a) xs)
    (@eval_set_directed
      (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
      (lambda_stage_set y a) (lambda_stage_directed y a) xs))).
  intros e (f & (m & ->) & ->).
  eapply (@dle_trans (E_dcpo Sig H)).
  - apply lambda_stage_arg_mono. exact Hyz.
  - apply (proj1 (dsup_lub (E_dcpo Sig H)
      (@eval_set (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
        (lambda_stage_set z a) xs)
      (@eval_set_directed
        (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
        (lambda_stage_set z a) (lambda_stage_directed z a) xs))).
    exists (lambda_stage_map Sig H z a m). split.
    + now exists m.
    + reflexivity.
Qed.

Lemma lambda_point_monotone : forall Sig H (y z : L_car Sig H),
    L_le y z ->
    dle (F_dcpo Sig (E_dcpo Sig H))
      (@lambda_point Sig H y) (@lambda_point Sig H z).
Proof.
  intros Sig H y z Hyz a. apply lambda_coord_monotone. exact Hyz.
Qed.

Definition lambda_map (Sig : Signature) (H : Subgroup) :
    SCMap (L_dcpo Sig H) (F_dcpo Sig (E_dcpo Sig H)).
Proof.
  refine (@Build_SCMap (L_dcpo Sig H) (F_dcpo Sig (E_dcpo Sig H))
    (@lambda_point Sig H) _ _).
  - apply lambda_point_monotone.
  - intros X HX. split.
    + intros y (x & Hx & ->). apply lambda_point_monotone.
      apply (proj1 (dsup_lub (L_dcpo Sig H) X HX)). exact Hx.
    + intros v Hv.
      rewrite <- (@lambda_kappa_point Sig H v).
      apply lambda_point_monotone.
      apply (proj2 (dsup_lub (L_dcpo Sig H) X HX)).
      intros x Hx.
      rewrite <- (@kappa_lambda_point Sig H x).
      apply (@sc_monotone (F_dcpo Sig (E_dcpo Sig H)) (L_dcpo Sig H)
        (kappa_map Sig H)).
      apply Hv. exists x. auto.
Defined.

Lemma kappa_lambda_map : forall Sig H y,
    kappa_map Sig H (lambda_map Sig H y) = y.
Proof. intros; apply kappa_lambda_point. Qed.

Lemma lambda_kappa_map : forall Sig H M,
    lambda_map Sig H (kappa_map Sig H M) = M.
Proof. intros; apply lambda_kappa_point. Qed.

Definition theta_map (Sig : Signature) (H : Subgroup) :
    SCMap (E_dcpo Sig H) (F_dcpo Sig (E_dcpo Sig H)) :=
  @sc_comp (E_dcpo Sig H) (L_dcpo Sig H)
    (F_dcpo Sig (E_dcpo Sig H)) (lambda_map Sig H) (tau_map Sig H).

Definition omega_map (Sig : Signature) (H : Subgroup) :
    SCMap (F_dcpo Sig (E_dcpo Sig H)) (E_dcpo Sig H) :=
  @sc_comp (F_dcpo Sig (E_dcpo Sig H)) (L_dcpo Sig H)
    (E_dcpo Sig H) (untau_map Sig H) (kappa_map Sig H).

Theorem omega_theta : forall Sig H e,
    omega_map Sig H (theta_map Sig H e) = e.
Proof.
  intros Sig H e. unfold omega_map, theta_map; cbn.
  rewrite kappa_lambda_point. apply untau_tau.
Qed.

Theorem theta_omega : forall Sig H M,
    theta_map Sig H (omega_map Sig H M) = M.
Proof.
  intros Sig H M. unfold omega_map, theta_map; cbn.
  rewrite tau_untau. apply lambda_kappa_point.
Qed.

(** * 7.7  Coding and decoding resident operations *)

Definition resident_structure (Sig : Signature) (H : Subgroup) (n : nat)
    (K : SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H)) :
    dcar (F_dcpo Sig (E_dcpo Sig H)).
Proof.
  intro a. destruct a as [k f|k P|k L|Q|i|k|].
  - exact (@sc_const (power_dcpo (E_dcpo Sig H) k) (E_dcpo Sig H)
      (dbot (E_dcpo Sig H))).
  - exact (@sc_const (power_dcpo (E_dcpo Sig H) k) (E_dcpo Sig H)
      (dbot (E_dcpo Sig H))).
  - exact (@sc_const (power_dcpo (E_dcpo Sig H) k) (E_dcpo Sig H)
      (dbot (E_dcpo Sig H))).
  - exact (@sc_const (power_dcpo (E_dcpo Sig H) 1) (E_dcpo Sig H)
      (dbot (E_dcpo Sig H))).
  - exact (@sc_const (power_dcpo (E_dcpo Sig H) 0) (E_dcpo Sig H)
      (dbot (E_dcpo Sig H))).
  - destruct (Nat.eq_dec k n) as [->|Hkn].
    + exact K.
    + exact (@sc_const (power_dcpo (E_dcpo Sig H) k) (E_dcpo Sig H)
        (dbot (E_dcpo Sig H))).
  - exact (@sc_const (power_dcpo (E_dcpo Sig H) 1) (E_dcpo Sig H)
      (dbot (E_dcpo Sig H))).
Defined.

Lemma resident_structure_slot : forall Sig H n
    (K : SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H)),
    @resident_structure Sig H n K (ai_slot n) = K.
Proof.
  intros. unfold resident_structure. destruct (Nat.eq_dec n n) as [p|Hnn].
  - assert (Hp : p = @eq_refl nat n) by apply proof_irrelevance.
    rewrite Hp. reflexivity.
  - contradiction.
Qed.

Definition enc (Sig : Signature) (H : Subgroup) (n : nat)
    (K : SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H)) :
    E_car Sig H :=
  omega_map Sig H (@resident_structure Sig H n K).

Definition dec (Sig : Signature) (H : Subgroup) (n : nat)
    (e : E_car Sig H) :
    SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H) :=
  theta_map Sig H e (ai_slot n).

Arguments enc Sig H n K : clear implicits.
Arguments dec Sig H n e : clear implicits.

Theorem dec_enc : forall Sig H n
    (K : SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H)),
    dec Sig H n (enc Sig H n K) = K.
Proof.
  intros Sig H n K. unfold dec, enc.
  rewrite theta_omega. apply resident_structure_slot.
Qed.

(** * 8.2--8.3  Interpreter coordinates and variable update *)

Definition interp_coord {Sig H} (e : E_car Sig H) (a : AIndex Sig) :=
  theta_map Sig H e a.

Definition variable_coord {Sig H} (e : E_car Sig H) (i : nat) : E_car Sig H :=
  interp_coord e (ai_var i) (empty_power (E_dcpo Sig H)).

Definition assert_coord {Sig H} (e : E_car Sig H) :
    SCMap (power_dcpo (E_dcpo Sig H) 1) (E_dcpo Sig H) :=
  interp_coord e ai_assert.

Definition update_structure (Sig : Signature) (H : Subgroup) (i : nat)
    (M : dcar (F_dcpo Sig (E_dcpo Sig H))) (v : E_car Sig H) :
    dcar (F_dcpo Sig (E_dcpo Sig H)).
Proof.
  intro a. destruct a as [k f|k P|k L|Q|j|k|].
  - exact (M (ai_T f)).
  - exact (M (ai_P P)).
  - exact (M (ai_L L)).
  - exact (M (ai_Q Q)).
  - destruct (Nat.eq_dec j i) as [->|Hji].
    + exact (@sc_const (power_dcpo (E_dcpo Sig H) 0) (E_dcpo Sig H) v).
    + exact (M (ai_var j)).
  - exact (M (ai_slot k)).
  - exact (M ai_assert).
Defined.

Definition upd (Sig : Signature) (H : Subgroup) (i : nat)
    (e v : E_car Sig H) : E_car Sig H :=
  omega_map Sig H
    (@update_structure Sig H i (theta_map Sig H e) v).

Arguments upd Sig H i e v : clear implicits.

Lemma theta_upd : forall Sig H i (e v : E_car Sig H),
    theta_map Sig H (upd Sig H i e v) =
      @update_structure Sig H i (theta_map Sig H e) v.
Proof. intros; unfold upd; apply theta_omega. Qed.

Lemma variable_coord_upd_eq : forall Sig H i (e v : E_car Sig H),
    variable_coord (upd Sig H i e v) i = v.
Proof.
  intros Sig H i e v. unfold variable_coord, interp_coord.
  rewrite theta_upd. unfold update_structure.
  destruct (Nat.eq_dec i i) as [p|Hii]; [|contradiction].
  assert (Hp : p = @eq_refl nat i) by apply proof_irrelevance.
  rewrite Hp. reflexivity.
Qed.

Lemma variable_coord_upd_neq : forall Sig H i j (e v : E_car Sig H),
    i <> j ->
    variable_coord (upd Sig H i e v) j = variable_coord e j.
Proof.
  intros Sig H i j e v Hij. unfold variable_coord, interp_coord.
  rewrite theta_upd. unfold update_structure.
  destruct (Nat.eq_dec j i); congruence.
Qed.

(** * 7.1 and 8.1  The fixed Goedel coding and quotation map

    The paper says "fix a bijection" after its countability argument.  The
    following record is precisely that fixed datum; no property of evaluation
    or of the recursive domain is included in it. *)

Definition SyntaxCarrier (Sig : Signature) (H : Subgroup) : Type :=
  { z : expr Sig | wf_expr H z }.

Definition CodeNat : Type := { n : nat | n <> 0 /\ n <> 1 }.

Record SyntaxCoding (Sig : Signature) (H : Subgroup) : Type := {
  syntax_encode : SyntaxCarrier Sig H -> CodeNat;
  syntax_decode : CodeNat -> SyntaxCarrier Sig H;
  syntax_decode_encode : forall z, syntax_decode (syntax_encode z) = z;
  syntax_encode_decode : forall n, syntax_encode (syntax_decode n) = n
}.

Arguments syntax_encode {Sig H} _ _.
Arguments syntax_decode {Sig H} _ _.

Definition syntax_act {Sig H} (g : Perm3) (Hg : hmem H g)
    (z : SyntaxCarrier Sig H) : SyntaxCarrier Sig H :=
  exist _ (act_expr g (proj1_sig z))
    (@wf_act_expr H Sig g Hg (proj1_sig z) (proj2_sig z)).

Arguments syntax_act {Sig H} g Hg z.

Lemma sig_prop_ext : forall (A : Type) (P : A -> Prop)
    (x y : { a : A | P a }),
    proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros A P [x Hx] [y Hy] He; cbn in He. subst y.
  f_equal. apply proof_irrelevance.
Qed.

Lemma syntax_act_id : forall Sig H (z : SyntaxCarrier Sig H),
    syntax_act pid (hmem_pid H) z = z.
Proof.
  intros Sig H z. apply sig_prop_ext. cbn. apply act_expr_id.
Qed.

Lemma syntax_act_mul : forall Sig H g h
    (Hg : hmem H g) (Hh : hmem H h) (z : SyntaxCarrier Sig H),
    syntax_act g Hg (syntax_act h Hh z) =
    syntax_act (pmul g h) (@hmem_mul H g h Hg Hh) z.
Proof.
  intros Sig H g h Hg Hh z. apply sig_prop_ext. cbn.
  apply act_expr_mul.
Qed.

Definition quote_value {Sig H} (C : SyntaxCoding Sig H)
    (z : SyntaxCarrier Sig H) : E_car Sig H :=
  eta_map Sig H 0 (Some (proj1_sig (syntax_encode C z))).

Definition decode_rel {Sig H} (C : SyntaxCoding Sig H)
    (u : E_car Sig H) (z : SyntaxCarrier Sig H) : Prop :=
  pi_map Sig H 0 u = Some (proj1_sig (syntax_encode C z)).

Lemma pi_quote : forall Sig H (C : SyntaxCoding Sig H) z,
    pi_map Sig H 0 (quote_value C z) =
      Some (proj1_sig (syntax_encode C z)).
Proof. intros; unfold quote_value; apply pi_eta. Qed.

Lemma syntax_encode_injective : forall Sig H (C : SyntaxCoding Sig H) x y,
    syntax_encode C x = syntax_encode C y -> x = y.
Proof.
  intros Sig H C x y He.
  rewrite <- (syntax_decode_encode C x), <- (syntax_decode_encode C y).
  now rewrite He.
Qed.

Theorem quote_value_injective : forall Sig H (C : SyntaxCoding Sig H) x y,
    quote_value C x = quote_value C y -> x = y.
Proof.
  intros Sig H C x y He.
  apply (f_equal (fun u => pi_map Sig H 0 u)) in He.
  rewrite !pi_quote in He. injection He as Hn.
  apply (@syntax_encode_injective Sig H C x y).
  destruct (syntax_encode C x) as [nx Hx].
  destruct (syntax_encode C y) as [ny Hy]. cbn in Hn. subst ny.
  f_equal. apply proof_irrelevance.
Qed.

Theorem decode_rel_functional : forall Sig H (C : SyntaxCoding Sig H) u x y,
    decode_rel C u x -> decode_rel C u y -> x = y.
Proof.
  intros Sig H C u x y Hx Hy. unfold decode_rel in *.
  rewrite Hx in Hy. injection Hy as Hn.
  apply (@syntax_encode_injective Sig H C x y).
  destruct (syntax_encode C x) as [nx Hnx].
  destruct (syntax_encode C y) as [ny Hny]. cbn in Hn. subst ny.
  f_equal. apply proof_irrelevance.
Qed.

Definition nonreserved (n : nat) : Prop := n <> 0 /\ n <> 1.

Theorem decode_rel_domain : forall Sig H (C : SyntaxCoding Sig H) u,
    (exists z, decode_rel C u z) <->
    exists n, nonreserved n /\ pi_map Sig H 0 u = Some n.
Proof.
  intros Sig H C u. split.
  - intros (z & Hz). exists (proj1_sig (syntax_encode C z)). split.
    + exact (proj2_sig (syntax_encode C z)).
    + exact Hz.
  - intros (n & Hn & Hu).
    set (cn := (exist _ n Hn : CodeNat)).
    exists (syntax_decode C cn). unfold decode_rel.
    rewrite syntax_encode_decode. exact Hu.
Qed.

(** The code permutation fixes the two reserved truth tags. *)
Definition code_nat_action {Sig H} (C : SyntaxCoding Sig H)
    (g : Perm3) (Hg : hmem H g) (n : nat) : nat.
Proof.
  destruct (Nat.eq_dec n 0) as [H0|H0]; [exact 0|].
  destruct (Nat.eq_dec n 1) as [H1|H1]; [exact 1|].
  exact (proj1_sig (syntax_encode C
    (syntax_act g Hg (syntax_decode C (exist _ n (conj H0 H1)))))).
Defined.

Arguments code_nat_action {Sig H} C g Hg n.

Definition flat_map (f : nat -> nat) (x : flat_nat) : flat_nat :=
  match x with None => None | Some n => Some (f n) end.

Lemma flat_map_monotone : forall f x y,
    flat_le x y -> flat_le (flat_map f x) (flat_map f y).
Proof.
  intros f [n|] [m|] Hle; cbn in *; try contradiction; auto.
Qed.

Definition flat_map_sc (f : nat -> nat) :
    SCMap flat_nat_dcpo flat_nat_dcpo.
Proof.
  refine (@Build_SCMap flat_nat_dcpo flat_nat_dcpo
    (flat_map f) (flat_map_monotone f) _).
  intros X HX. split.
  - intros y (x & Hx & ->). apply flat_map_monotone.
    apply (proj1 (dsup_lub flat_nat_dcpo X HX)). exact Hx.
  - intros v Hv.
    destruct (dsup flat_nat_dcpo X HX) as [n|] eqn:Hsup; cbn.
    + apply (Hv (Some (f n))). exists (Some n). split.
      * apply (@flat_lub_some_attained X HX n). exact Hsup.
      * reflexivity.
    + exact I.
Defined.

Definition B0_map {Sig H} (C : SyntaxCoding Sig H)
    (g : Perm3) (Hg : hmem H g) :
    SCMap flat_nat_dcpo flat_nat_dcpo :=
  flat_map_sc (code_nat_action C g Hg).

Arguments B0_map {Sig H} C g Hg.

Lemma code_nat_action_zero : forall Sig H (C : SyntaxCoding Sig H) g Hg,
    code_nat_action C g Hg 0 = 0.
Proof.
  intros. unfold code_nat_action.
  destruct (Nat.eq_dec 0 0); [reflexivity|contradiction].
Qed.

Lemma code_nat_action_one : forall Sig H (C : SyntaxCoding Sig H) g Hg,
    code_nat_action C g Hg 1 = 1.
Proof.
  intros. unfold code_nat_action.
  destruct (Nat.eq_dec 1 0) as [H10|H10]; [discriminate|].
  destruct (Nat.eq_dec 1 1); [reflexivity|contradiction].
Qed.

Lemma code_nat_action_nonreserved : forall Sig H (C : SyntaxCoding Sig H)
    g Hg n (H0 : n <> 0) (H1 : n <> 1),
    code_nat_action C g Hg n =
    proj1_sig (syntax_encode C
      (syntax_act g Hg (syntax_decode C (exist _ n (conj H0 H1))))).
Proof.
  intros Sig H C g Hg n H0 H1. unfold code_nat_action.
  destruct (Nat.eq_dec n 0) as [He0|Hd0]; [contradiction|].
  destruct (Nat.eq_dec n 1) as [He1|Hd1]; [contradiction|].
  assert (Hcode : (exist (fun k => k <> 0 /\ k <> 1) n (conj Hd0 Hd1)) =
      exist (fun k => k <> 0 /\ k <> 1) n (conj H0 H1)).
  { apply sig_prop_ext. reflexivity. }
  now rewrite Hcode.
Qed.

Arguments code_nat_action_nonreserved {Sig H} C g Hg n H0 H1.

Theorem code_nat_action_id : forall Sig H (C : SyntaxCoding Sig H) n,
    code_nat_action C pid (hmem_pid H) n = n.
Proof.
  intros Sig H C n.
  destruct (Nat.eq_dec n 0) as [->|H0]; [apply code_nat_action_zero|].
  destruct (Nat.eq_dec n 1) as [->|H1]; [apply code_nat_action_one|].
  rewrite (code_nat_action_nonreserved C pid (hmem_pid H) n H0 H1).
  rewrite syntax_act_id, syntax_encode_decode. reflexivity.
Qed.

Theorem code_nat_action_mul : forall Sig H (C : SyntaxCoding Sig H)
    g h (Hg : hmem H g) (Hh : hmem H h) n,
    code_nat_action C g Hg (code_nat_action C h Hh n) =
    code_nat_action C (pmul g h) (@hmem_mul H g h Hg Hh) n.
Proof.
  intros Sig H C g h Hg Hh n.
  destruct (Nat.eq_dec n 0) as [->|H0].
  - rewrite !code_nat_action_zero. reflexivity.
  - destruct (Nat.eq_dec n 1) as [->|H1].
    + rewrite !code_nat_action_one. reflexivity.
    + rewrite (code_nat_action_nonreserved C h Hh n H0 H1).
      set (z := syntax_act h Hh
        (syntax_decode C (exist _ n (conj H0 H1)))).
      pose proof (proj2_sig (syntax_encode C z)) as Hzcode.
      destruct Hzcode as [Hz0 Hz1].
      rewrite (code_nat_action_nonreserved C g Hg
        (proj1_sig (syntax_encode C z)) Hz0 Hz1).
      rewrite (code_nat_action_nonreserved C (pmul g h)
        (@hmem_mul H g h Hg Hh) n H0 H1).
      assert (Hcn :
        exist (fun k => k <> 0 /\ k <> 1)
          (proj1_sig (syntax_encode C z)) (conj Hz0 Hz1) =
        syntax_encode C z).
      { apply sig_prop_ext. reflexivity. }
      rewrite Hcn, syntax_decode_encode. unfold z.
      rewrite syntax_act_mul. reflexivity.
Qed.

Theorem B0_id : forall Sig H (C : SyntaxCoding Sig H),
    B0_map C pid (hmem_pid H) = sc_id flat_nat_dcpo.
Proof.
  intros Sig H C. apply SCMap_ext. intros [n|]; cbn; [|reflexivity].
  f_equal. apply code_nat_action_id.
Qed.

Theorem B0_mul : forall Sig H (C : SyntaxCoding Sig H)
    g h (Hg : hmem H g) (Hh : hmem H h),
    @sc_comp flat_nat_dcpo flat_nat_dcpo flat_nat_dcpo
      (B0_map C g Hg) (B0_map C h Hh) =
    B0_map C (pmul g h) (@hmem_mul H g h Hg Hh).
Proof.
  intros Sig H C g h Hg Hh. apply SCMap_ext. intros [n|]; cbn;
    [f_equal; apply code_nat_action_mul|reflexivity].
Qed.

(** A monotone order isomorphism between dcpos is Scott continuous. *)
Definition order_iso_sc (D E : PDCPO)
    (f : dcar D -> dcar E) (g : dcar E -> dcar D)
    (Hf : forall x y, dle D x y -> dle E (f x) (f y))
    (Hg : forall x y, dle E x y -> dle D (g x) (g y))
    (Hgf : forall x, g (f x) = x)
    (Hfg : forall y, f (g y) = y) : SCMap D E.
Proof.
  refine (@Build_SCMap D E f Hf _). intros X HX. split.
  - intros y (x & Hx & ->). apply Hf.
    apply (proj1 (dsup_lub D X HX)). exact Hx.
  - intros v Hv. rewrite <- (Hfg v). apply Hf.
    apply (proj2 (dsup_lub D X HX)). intros x Hx.
    rewrite <- (Hgf x). apply Hg, Hv. exists x. auto.
Defined.

Definition aindex_act {Sig} (g : Perm3) (a : AIndex Sig) : AIndex Sig :=
  match a with
  | ai_T f => ai_T f
  | ai_P P => ai_P P
  | ai_L L => ai_L L
  | ai_Q Q => ai_Q Q
  | ai_var i => ai_var (pact g i)
  | ai_slot n => ai_slot n
  | ai_assert => ai_assert
  end.

Lemma aindex_act_id : forall Sig (a : AIndex Sig), aindex_act pid a = a.
Proof. intros Sig [n f|n P|n L|Q|i|n|]; reflexivity. Qed.

Lemma aindex_act_mul : forall Sig g h (a : AIndex Sig),
    aindex_act g (aindex_act h a) = aindex_act (pmul g h) a.
Proof.
  intros Sig g h [n f|n P|n L|Q|i|n|]; cbn; try reflexivity.
  now rewrite pact_mul.
Qed.

Lemma aindex_act_inv_l : forall Sig g (a : AIndex Sig),
    aindex_act (pinv g) (aindex_act g a) = a.
Proof.
  intros Sig g [n f|n P|n L|Q|i|n|]; cbn; try reflexivity.
  now rewrite pact_inv_l.
Qed.

Lemma aindex_act_inv_r : forall Sig g (a : AIndex Sig),
    aindex_act g (aindex_act (pinv g) a) = a.
Proof.
  intros Sig g [n f|n P|n L|Q|i|n|]; cbn; try reflexivity.
  now rewrite pact_inv_r.
Qed.

Lemma aindex_act_arity : forall Sig g (a : AIndex Sig),
    arity (aindex_act g a) = arity a.
Proof. intros Sig g [n f|n P|n L|Q|i|n|]; reflexivity. Qed.

Definition conjugate_operation (D : PDCPO) (n : nat)
    (b binv : SCMap D D)
    (K : SCMap (power_dcpo D n) D) : SCMap (power_dcpo D n) D :=
  @sc_comp (power_dcpo D n) D D b
    (@sc_comp (power_dcpo D n) (power_dcpo D n) D K
      (@power_map D D n binv)).

Arguments conjugate_operation D n b binv K : clear implicits.

Lemma conjugate_operation_monotone : forall D n b binv K L,
    scmap_le (power_dcpo D n) D K L ->
    scmap_le (power_dcpo D n) D
      (conjugate_operation D n b binv K)
      (conjugate_operation D n b binv L).
Proof.
  intros D n b binv K L HK xs. unfold conjugate_operation; cbn.
  apply (@sc_monotone D D b). apply HK.
Qed.

Lemma conjugate_operation_inverse : forall D n (b binv : SCMap D D)
    (Hbb' : forall x, b (binv x) = x)
    (K : SCMap (power_dcpo D n) D),
    conjugate_operation D n b binv
      (conjugate_operation D n binv b K) = K.
Proof.
  intros D n b binv Hbb' K. apply SCMap_ext. intro xs.
  unfold conjugate_operation; cbn. rewrite Hbb'.
  apply (f_equal (fun ys => K ys)).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply Hbb'.
Qed.

Definition F_conjugate_point (Sig : Signature) (D : PDCPO)
    (g : Perm3) (b binv : SCMap D D)
    (M : dcar (F_dcpo Sig D)) : dcar (F_dcpo Sig D).
Proof.
  intro a. destruct a as [n f|n P|n L|Q|i|n|].
  - exact (conjugate_operation D n b binv (M (ai_T f))).
  - exact (conjugate_operation D n b binv (M (ai_P P))).
  - exact (conjugate_operation D n b binv (M (ai_L L))).
  - exact (conjugate_operation D 1 b binv (M (ai_Q Q))).
  - exact (conjugate_operation D 0 b binv
      (M (ai_var (pact (pinv g) i)))).
  - exact (conjugate_operation D n b binv (M (ai_slot n))).
  - exact (conjugate_operation D 1 b binv (M ai_assert)).
Defined.

Arguments F_conjugate_point Sig D g b binv M : clear implicits.

Lemma F_conjugate_point_monotone : forall Sig D g b binv M N,
    dle (F_dcpo Sig D) M N ->
    dle (F_dcpo Sig D)
      (F_conjugate_point Sig D g b binv M)
      (F_conjugate_point Sig D g b binv N).
Proof.
  intros Sig D g b binv M N HMN a.
  destruct a as [n f|n P|n L|Q|i|n|];
    apply conjugate_operation_monotone.
  - exact (HMN (ai_T f)).
  - exact (HMN (ai_P P)).
  - exact (HMN (ai_L L)).
  - exact (HMN (ai_Q Q)).
  - exact (HMN (ai_var (pact (pinv g) i))).
  - exact (HMN (ai_slot n)).
  - exact (HMN ai_assert).
Qed.

Lemma F_conjugate_inverse_l : forall Sig D g (b binv : SCMap D D)
    (Hbb' : forall x, b (binv x) = x)
    (M : dcar (F_dcpo Sig D)),
    F_conjugate_point Sig D g b binv
      (F_conjugate_point Sig D (pinv g) binv b M) = M.
Proof.
  intros Sig D g b binv Hbb' M.
  apply functional_extensionality_dep. intro a.
  assert (Hinv : pinv (pinv g) = g) by (destruct g; reflexivity).
  destruct a as [n f|n P|n L|Q|i|n|]; cbn.
  - apply conjugate_operation_inverse. exact Hbb'.
  - apply conjugate_operation_inverse. exact Hbb'.
  - apply conjugate_operation_inverse. exact Hbb'.
  - apply conjugate_operation_inverse. exact Hbb'.
  - rewrite Hinv, pact_inv_r.
    apply conjugate_operation_inverse. exact Hbb'.
  - apply conjugate_operation_inverse. exact Hbb'.
  - apply conjugate_operation_inverse. exact Hbb'.
Qed.

Lemma F_conjugate_inverse_r : forall Sig D g (b binv : SCMap D D)
    (Hb'b : forall x, binv (b x) = x)
    (M : dcar (F_dcpo Sig D)),
    F_conjugate_point Sig D (pinv g) binv b
      (F_conjugate_point Sig D g b binv M) = M.
Proof.
  intros Sig D g b binv Hb'b M.
  destruct g; cbn; apply F_conjugate_inverse_l; exact Hb'b.
Qed.

Definition F_conjugate_map (Sig : Signature) (D : PDCPO)
    (g : Perm3) (b binv : SCMap D D)
    (Hbb' : forall x, b (binv x) = x)
    (Hb'b : forall x, binv (b x) = x) :
    SCMap (F_dcpo Sig D) (F_dcpo Sig D) :=
  @order_iso_sc (F_dcpo Sig D) (F_dcpo Sig D)
    (F_conjugate_point Sig D g b binv)
    (F_conjugate_point Sig D (pinv g) binv b)
    (@F_conjugate_point_monotone Sig D g b binv)
    (@F_conjugate_point_monotone Sig D (pinv g) binv b)
    (@F_conjugate_inverse_r Sig D g b binv Hb'b)
    (@F_conjugate_inverse_l Sig D g b binv Hbb').

Lemma B0_inv_l : forall Sig H (C : SyntaxCoding Sig H) g
    (Hg : hmem H g) x,
    B0_map C (pinv g) (@hmem_inv H g Hg) (B0_map C g Hg x) = x.
Proof.
  intros Sig H C g Hg [n|]; cbn; [f_equal|reflexivity].
  rewrite (@code_nat_action_mul Sig H C (pinv g) g
    (@hmem_inv H g Hg) Hg n).
  destruct g; cbn;
    match goal with
    | |- code_nat_action C pid ?p n = n =>
        replace p with (hmem_pid H) by apply proof_irrelevance;
        apply code_nat_action_id
    end.
Qed.

Lemma B0_inv_r : forall Sig H (C : SyntaxCoding Sig H) g
    (Hg : hmem H g) x,
    B0_map C g Hg (B0_map C (pinv g) (@hmem_inv H g Hg) x) = x.
Proof.
  intros Sig H C g Hg [n|]; cbn; [f_equal|reflexivity].
  rewrite (@code_nat_action_mul Sig H C g (pinv g)
    Hg (@hmem_inv H g Hg) n).
  destruct g; cbn;
    match goal with
    | |- code_nat_action C pid ?p n = n =>
        replace p with (hmem_pid H) by apply proof_irrelevance;
        apply code_nat_action_id
    end.
Qed.

Record DCPOAuto (D : PDCPO) : Type := {
  auto_fwd : SCMap D D;
  auto_bwd : SCMap D D;
  auto_bwd_fwd : forall x, auto_bwd (auto_fwd x) = x;
  auto_fwd_bwd : forall x, auto_fwd (auto_bwd x) = x
}.

Arguments auto_fwd {D} _.
Arguments auto_bwd {D} _.

Definition B0_auto {Sig H} (C : SyntaxCoding Sig H) g
    (Hg : hmem H g) : DCPOAuto flat_nat_dcpo :=
  {| auto_fwd := B0_map C g Hg;
     auto_bwd := B0_map C (pinv g) (@hmem_inv H g Hg);
     auto_bwd_fwd := @B0_inv_l Sig H C g Hg;
     auto_fwd_bwd := @B0_inv_r Sig H C g Hg |}.

Definition lift_auto (Sig : Signature) (D : PDCPO) (g : Perm3)
    (A : DCPOAuto D) : DCPOAuto (F_dcpo Sig D).
Proof.
  refine {| auto_fwd := @F_conjugate_map Sig D g
      (auto_fwd A) (auto_bwd A) (auto_fwd_bwd A) (auto_bwd_fwd A);
    auto_bwd := @F_conjugate_map Sig D (pinv g)
      (auto_bwd A) (auto_fwd A) (auto_bwd_fwd A) (auto_fwd_bwd A) |}.
  - intro M. apply F_conjugate_inverse_r. apply auto_bwd_fwd.
  - intro M. apply F_conjugate_inverse_l. apply auto_fwd_bwd.
Defined.

Fixpoint B_level_auto (Sig : Signature) (H : Subgroup)
    (C : SyntaxCoding Sig H) (m : nat) (g : Perm3) (Hg : hmem H g) :
    DCPOAuto (D_level Sig m) :=
  match m as k return DCPOAuto (D_level Sig k) with
  | 0 => @B0_auto Sig H C g Hg
  | S k => @lift_auto Sig (D_level Sig k) g
      (@B_level_auto Sig H C k g Hg)
  end.

Definition B_level_map {Sig H} (C : SyntaxCoding Sig H) m g
    (Hg : hmem H g) : SCMap (D_level Sig m) (D_level Sig m) :=
  auto_fwd (@B_level_auto Sig H C m g Hg).

Definition B_level_inv_map {Sig H} (C : SyntaxCoding Sig H) m g
    (Hg : hmem H g) : SCMap (D_level Sig m) (D_level Sig m) :=
  auto_bwd (@B_level_auto Sig H C m g Hg).

Arguments B_level_map {Sig H} C m g Hg.
Arguments B_level_inv_map {Sig H} C m g Hg.

Lemma B_level_bwd_fwd : forall Sig H (C : SyntaxCoding Sig H) m g
    (Hg : hmem H g) x,
    B_level_inv_map C m g Hg (B_level_map C m g Hg x) = x.
Proof. intros; apply auto_bwd_fwd. Qed.

Lemma B_level_fwd_bwd : forall Sig H (C : SyntaxCoding Sig H) m g
    (Hg : hmem H g) x,
    B_level_map C m g Hg (B_level_inv_map C m g Hg x) = x.
Proof. intros; apply auto_fwd_bwd. Qed.

Lemma auto_bwd_comp : forall D (A B C : DCPOAuto D),
    (forall x, auto_fwd A (auto_fwd B x) = auto_fwd C x) ->
    forall x, auto_bwd B (auto_bwd A x) = auto_bwd C x.
Proof.
  intros D A B C Hf x.
  assert (Hinj : forall u v, auto_fwd C u = auto_fwd C v -> u = v).
  { intros u v He. apply (f_equal (auto_bwd C)) in He.
    now rewrite !auto_bwd_fwd in He. }
  apply Hinj. rewrite <- (Hf (auto_bwd B (auto_bwd A x))).
  now rewrite !auto_fwd_bwd.
Qed.

Lemma conjugate_operation_mul : forall D n
    (b ib c ic d id : SCMap D D)
    (Hout : forall x, b (c x) = d x)
    (Hin : forall x, ic (ib x) = id x)
    (K : SCMap (power_dcpo D n) D),
    conjugate_operation D n b ib
      (conjugate_operation D n c ic K) =
    conjugate_operation D n d id K.
Proof.
  intros D n b ib c ic d id Hout Hin K.
  apply SCMap_ext. intro xs. unfold conjugate_operation; cbn.
  rewrite Hout. apply (f_equal (fun ys => d (K ys))).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply Hin.
Qed.

Lemma pinv_mul_rev : forall g h,
    pinv (pmul g h) = pmul (pinv h) (pinv g).
Proof. intros [] []; reflexivity. Qed.

Lemma F_conjugate_point_mul : forall Sig D g h
    (bg ig bh ih bgh igh : SCMap D D)
    (Hout : forall x, bg (bh x) = bgh x)
    (Hin : forall x, ih (ig x) = igh x)
    (M : dcar (F_dcpo Sig D)),
    F_conjugate_point Sig D g bg ig
      (F_conjugate_point Sig D h bh ih M) =
    F_conjugate_point Sig D (pmul g h) bgh igh M.
Proof.
  intros Sig D g h bg ig bh ih bgh igh Hout Hin M.
  apply functional_extensionality_dep. intro a.
  destruct a as [n f|n P|n L|Q|i|n|]; cbn.
  - apply conjugate_operation_mul; assumption.
  - apply conjugate_operation_mul; assumption.
  - apply conjugate_operation_mul; assumption.
  - apply conjugate_operation_mul; assumption.
  - rewrite pinv_mul_rev, pact_mul.
    apply conjugate_operation_mul; assumption.
  - apply conjugate_operation_mul; assumption.
  - apply conjugate_operation_mul; assumption.
Qed.

Theorem B_level_mul : forall Sig H (C : SyntaxCoding Sig H) m g h
    (Hg : hmem H g) (Hh : hmem H h),
    @sc_comp (D_level Sig m) (D_level Sig m) (D_level Sig m)
      (B_level_map C m g Hg) (B_level_map C m h Hh) =
    B_level_map C m (pmul g h) (@hmem_mul H g h Hg Hh).
Proof.
  intros Sig H C m. induction m as [|m IH]; intros g h Hg Hh.
  - apply B0_mul.
  - apply SCMap_ext. intro M. cbn [B_level_map B_level_auto
      lift_auto F_conjugate_map order_iso_sc].
    apply F_conjugate_point_mul.
    + intro x. pose proof (f_equal (fun F : SCMap (D_level Sig m)
          (D_level Sig m) => F x)
        (IH g h Hg Hh)) as Hx. exact Hx.
    + apply auto_bwd_comp. intro x.
      pose proof (f_equal (fun F : SCMap (D_level Sig m)
        (D_level Sig m) => F x) (IH g h Hg Hh)) as Hx.
      exact Hx.
Qed.

Theorem B_level_id : forall Sig H (C : SyntaxCoding Sig H) m,
    B_level_map C m pid (hmem_pid H) = sc_id (D_level Sig m).
Proof.
  intros Sig H C m. apply SCMap_ext. intro x.
  pose proof (f_equal (fun F : SCMap (D_level Sig m)
      (D_level Sig m) => F x)
    (@B_level_mul Sig H C m pid pid (hmem_pid H) (hmem_pid H))) as Hmul.
  cbn [sc_comp] in Hmul.
  replace (@hmem_mul H pid pid (hmem_pid H) (hmem_pid H))
    with (hmem_pid H) in Hmul by apply proof_irrelevance.
  apply (f_equal (fun y =>
    B_level_inv_map C m pid (hmem_pid H) y)) in Hmul.
  unfold sc_comp in Hmul; cbn in Hmul.
  rewrite !B_level_bwd_fwd in Hmul.
  change (B_level_map C m pid (hmem_pid H) x = x). exact Hmul.
Qed.

Lemma orbit0_act_iff : forall H g, hmem H g -> forall i,
    orbit0 H (pact g i) <-> orbit0 H i.
Proof.
  intros H g Hg i. split.
  - intros (k & Hk & Hki).
    exists (pmul (pinv g) k). split.
    + apply hmem_mul; [apply hmem_inv; exact Hg|exact Hk].
    + rewrite pact_mul. rewrite <- Hki. now rewrite pact_inv_l.
  - intros (k & Hk & Hik).
    exists (pmul g k). split.
    + apply hmem_mul; assumption.
    + now rewrite pact_mul, Hik.
Qed.

Lemma orbit0_pinv_iff : forall H g, hmem H g -> forall i,
    orbit0 H (pact (pinv g) i) <-> orbit0 H i.
Proof.
  intros H g Hg i. apply orbit0_act_iff. now apply hmem_inv.
Qed.

Lemma F_conjugate_var_apply : forall Sig D g b binv
    (M : dcar (F_dcpo Sig D)) i,
    F_conjugate_point Sig D g b binv M (ai_var i)
      (empty_power D) =
    b (M (ai_var (pact (pinv g) i)) (empty_power D)).
Proof.
  intros. unfold F_conjugate_point, conjugate_operation; cbn.
  apply (f_equal (fun ys => b (M (ai_var (pact (pinv g) i)) ys))).
  apply empty_power_unique.
Qed.

Lemma initial_iota_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) d,
    F_conjugate_point Sig flat_nat_dcpo g
      (B0_map C g Hg)
      (B0_map C (pinv g) (@hmem_inv H g Hg))
      (iota0 Sig H d) =
    iota0 Sig H (B0_map C g Hg d).
Proof.
  intros Sig H C g Hg d.
  apply functional_extensionality_dep. intro a.
  apply SCMap_ext. intro xs.
  destruct a as [n f|n P|n L|Q|i|n|];
    unfold F_conjugate_point, conjugate_operation, iota0, iota0_fun;
    cbn.
  - destruct (orbit_variable_dec H (ai_T f)); [contradiction|reflexivity].
  - destruct (orbit_variable_dec H (ai_P P)); [contradiction|reflexivity].
  - destruct (orbit_variable_dec H (ai_L L)); [contradiction|reflexivity].
  - destruct (orbit_variable_dec H (ai_Q Q)); [contradiction|reflexivity].
  - destruct (orbit_variable_dec H (ai_var (pact (pinv g) i))) as [Hin|Hin];
    destruct (orbit_variable_dec H (ai_var i)) as [Hout|Hout]; cbn.
    + reflexivity.
    + exfalso. apply Hout. apply (proj1 (@orbit0_pinv_iff H g Hg i)). exact Hin.
    + exfalso. apply Hin. apply (proj2 (@orbit0_pinv_iff H g Hg i)). exact Hout.
    + reflexivity.
  - destruct (orbit_variable_dec H (ai_slot n)); [contradiction|reflexivity].
  - destruct (orbit_variable_dec H ai_assert); [contradiction|reflexivity].
Qed.

Lemma orbit_common_conjugate_forward : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) M d,
    orbit_common H M d ->
    orbit_common H
      (F_conjugate_point Sig flat_nat_dcpo g
        (B0_map C g Hg)
        (B0_map C (pinv g) (@hmem_inv H g Hg)) M)
      (B0_map C g Hg d).
Proof.
  intros Sig H C g Hg M d HM i Hi. unfold var_value.
  rewrite F_conjugate_var_apply.
  apply (f_equal (fun x => B0_map C g Hg x)).
  apply HM. apply (proj2 (@orbit0_pinv_iff H g Hg i)). exact Hi.
Qed.

Lemma var_value_F_conjugate : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) M i,
    var_value
      (F_conjugate_point Sig flat_nat_dcpo g
        (B0_map C g Hg)
        (B0_map C (pinv g) (@hmem_inv H g Hg)) M) i =
    B0_map C g Hg (var_value M (pact (pinv g) i)).
Proof.
  intros. unfold var_value. apply F_conjugate_var_apply.
Qed.

Lemma orbit_common_conjugate_backward : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) M e,
    orbit_common H
      (F_conjugate_point Sig flat_nat_dcpo g
        (B0_map C g Hg)
        (B0_map C (pinv g) (@hmem_inv H g Hg)) M) e ->
    orbit_common H M
      (B0_map C (pinv g) (@hmem_inv H g Hg) e).
Proof.
  intros Sig H C g Hg M e HM j Hj.
  pose proof (HM (pact g j)
    ((proj2 (@orbit0_act_iff H g Hg j)) Hj)) as Heq.
  rewrite (@var_value_F_conjugate Sig H C g Hg M (pact g j)) in Heq.
  rewrite pact_inv_l in Heq.
  apply (f_equal (fun x =>
    B0_map C (pinv g) (@hmem_inv H g Hg) x)) in Heq.
  rewrite B0_inv_l in Heq. exact Heq.
Qed.

Lemma rho0_no_common : forall Sig H
    (M : dcar (F_dcpo Sig flat_nat_dcpo)),
    ~ (exists d, orbit_common H M d) -> @rho0_fun Sig H M = None.
Proof.
  intros Sig H M Hnone. unfold rho0_fun.
  destruct (excluded_middle_informative (exists d, orbit_common H M d));
    [contradiction|reflexivity].
Qed.

Lemma initial_rho_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) M,
    rho0 Sig H
      (F_conjugate_point Sig flat_nat_dcpo g
        (B0_map C g Hg)
        (B0_map C (pinv g) (@hmem_inv H g Hg)) M) =
    B0_map C g Hg (rho0 Sig H M).
Proof.
  intros Sig H C g Hg M. unfold rho0; cbn.
  destruct (excluded_middle_informative
    (exists d, orbit_common H M d)) as [[d Hd]|Hnone].
  - rewrite (@rho0_of_common Sig H M d Hd).
    rewrite (@rho0_of_common Sig H
      (F_conjugate_point Sig flat_nat_dcpo g
        (B0_map C g Hg)
        (B0_map C (pinv g) (@hmem_inv H g Hg)) M)
      (B0_map C g Hg d)).
    + reflexivity.
    + now apply orbit_common_conjugate_forward.
  - rewrite (@rho0_no_common Sig H M Hnone).
    rewrite (@rho0_no_common Sig H
      (F_conjugate_point Sig flat_nat_dcpo g
        (B0_map C g Hg)
        (B0_map C (pinv g) (@hmem_inv H g Hg)) M)).
    + reflexivity.
    + intros (e & He). apply Hnone.
      exists (B0_map C (pinv g) (@hmem_inv H g Hg) e).
      now apply orbit_common_conjugate_backward.
Qed.

Lemma conjugate_prepost_embed : forall D E n
    (e : SCMap D E) (p : SCMap E D)
    (bD iD : SCMap D D) (bE iE : SCMap E E)
    (K : SCMap (power_dcpo D n) D),
    (forall x, bE (e x) = e (bD x)) ->
    (forall y, p (iE y) = iD (p y)) ->
    conjugate_operation E n bE iE
      (@prepost_map (power_dcpo E n) (power_dcpo D n) D E
        (@power_map E D n p) e K) =
    @prepost_map (power_dcpo E n) (power_dcpo D n) D E
      (@power_map E D n p) e
      (conjugate_operation D n bD iD K).
Proof.
  intros D E n e p bD iD bE iE K Heb Hep.
  apply SCMap_ext. intro xs.
  unfold conjugate_operation, prepost_map; cbn. rewrite Heb.
  apply (f_equal (fun ys => e (bD (K ys)))).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply Hep.
Qed.

Lemma conjugate_prepost_project : forall D E n
    (e : SCMap D E) (p : SCMap E D)
    (bD iD : SCMap D D) (bE iE : SCMap E E)
    (K : SCMap (power_dcpo E n) E),
    (forall y, bD (p y) = p (bE y)) ->
    (forall x, e (iD x) = iE (e x)) ->
    conjugate_operation D n bD iD
      (@prepost_map (power_dcpo D n) (power_dcpo E n) E D
        (@power_map D E n e) p K) =
    @prepost_map (power_dcpo D n) (power_dcpo E n) E D
      (@power_map D E n e) p
      (conjugate_operation E n bE iE K).
Proof.
  intros D E n e p bD iD bE iE K Hpb Hei.
  apply SCMap_ext. intro xs.
  unfold conjugate_operation, prepost_map; cbn. rewrite Hpb.
  apply (f_equal (fun ys => p (bE (K ys)))).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. unfold dep_map_fun; cbn.
  exact (Hei (xs j)).
Qed.

Lemma F_embed_conjugate : forall Sig D E (ep : EPPair D E) g
    (bD iD : SCMap D D) (bE iE : SCMap E E)
    (M : dcar (F_dcpo Sig D)),
    (forall x, bE (ep_embed ep x) = ep_embed ep (bD x)) ->
    (forall y, ep_project ep (iE y) = iD (ep_project ep y)) ->
    F_conjugate_point Sig E g bE iE (F_embed Sig ep M) =
    F_embed Sig ep (F_conjugate_point Sig D g bD iD M).
Proof.
  intros Sig D E ep g bD iD bE iE M Heb Hep.
  apply functional_extensionality_dep. intro a.
  destruct a as [n f|n P|n L|Q|i|n|]; cbn [F_embed dep_map_sc dep_map_fun
    F_conjugate_point].
  all: apply conjugate_prepost_embed; assumption.
Qed.

Lemma F_project_conjugate : forall Sig D E (ep : EPPair D E) g
    (bD iD : SCMap D D) (bE iE : SCMap E E)
    (M : dcar (F_dcpo Sig E)),
    (forall y, bD (ep_project ep y) = ep_project ep (bE y)) ->
    (forall x, ep_embed ep (iD x) = iE (ep_embed ep x)) ->
    F_conjugate_point Sig D g bD iD (F_project Sig ep M) =
    F_project Sig ep (F_conjugate_point Sig E g bE iE M).
Proof.
  intros Sig D E ep g bD iD bE iE M Hpb Hei.
  apply functional_extensionality_dep. intro a.
  destruct a as [n f|n P|n L|Q|i|n|]; cbn [F_project dep_map_sc dep_map_fun
    F_conjugate_point].
  all: apply conjugate_prepost_project; assumption.
Qed.

Lemma ep_auto_bwd_embed : forall D E (ep : EPPair D E)
    (A : DCPOAuto D) (B : DCPOAuto E),
    (forall x, ep_embed ep (auto_fwd A x) = auto_fwd B (ep_embed ep x)) ->
    forall x, ep_embed ep (auto_bwd A x) = auto_bwd B (ep_embed ep x).
Proof.
  intros D E ep A B Hf x.
  assert (Hinj : forall u v, auto_fwd B u = auto_fwd B v -> u = v).
  { intros u v He. apply (f_equal (auto_bwd B)) in He.
    now rewrite !auto_bwd_fwd in He. }
  apply Hinj. rewrite <- Hf. now rewrite !auto_fwd_bwd.
Qed.

Lemma ep_auto_bwd_project : forall D E (ep : EPPair D E)
    (A : DCPOAuto D) (B : DCPOAuto E),
    (forall y, ep_project ep (auto_fwd B y) = auto_fwd A (ep_project ep y)) ->
    forall y, ep_project ep (auto_bwd B y) = auto_bwd A (ep_project ep y).
Proof.
  intros D E ep A B Hf y.
  assert (Hinj : forall u v, auto_fwd A u = auto_fwd A v -> u = v).
  { intros u v He. apply (f_equal (auto_bwd A)) in He.
    now rewrite !auto_bwd_fwd in He. }
  apply Hinj. rewrite <- Hf. now rewrite !auto_fwd_bwd.
Qed.

Theorem chain_fwd_natural : forall Sig H (C : SyntaxCoding Sig H) m g
    (Hg : hmem H g),
    (forall x,
      chain_iota Sig H m
        (auto_fwd (@B_level_auto Sig H C m g Hg) x) =
      auto_fwd (@B_level_auto Sig H C (S m) g Hg)
        (chain_iota Sig H m x)) /\
    (forall y,
      chain_rho Sig H m
        (auto_fwd (@B_level_auto Sig H C (S m) g Hg) y) =
      auto_fwd (@B_level_auto Sig H C m g Hg)
        (chain_rho Sig H m y)).
Proof.
  intros Sig H C m. induction m as [|m IH]; intros g Hg.
  - split.
    + intro d. symmetry. apply initial_iota_equivariant.
    + intro M. apply initial_rho_equivariant.
  - destruct (IH g Hg) as [Hi Hr].
    assert (Hbi : forall x,
      chain_iota Sig H m
        (auto_bwd (@B_level_auto Sig H C m g Hg) x) =
      auto_bwd (@B_level_auto Sig H C (S m) g Hg)
        (chain_iota Sig H m x)).
    { apply (@ep_auto_bwd_embed (D_level Sig m) (D_level Sig (S m))
        (chain_ep Sig H m)
        (@B_level_auto Sig H C m g Hg)
        (@B_level_auto Sig H C (S m) g Hg)). exact Hi. }
    assert (Hbr : forall y,
      chain_rho Sig H m
        (auto_bwd (@B_level_auto Sig H C (S m) g Hg) y) =
      auto_bwd (@B_level_auto Sig H C m g Hg)
        (chain_rho Sig H m y)).
    { apply (@ep_auto_bwd_project (D_level Sig m) (D_level Sig (S m))
        (chain_ep Sig H m)
        (@B_level_auto Sig H C m g Hg)
        (@B_level_auto Sig H C (S m) g Hg)). exact Hr. }
    split.
    + intro M. cbn [chain_iota chain_ep B_level_auto lift_auto
        F_conjugate_map order_iso_sc].
      symmetry. apply F_embed_conjugate.
      * intro x. symmetry. apply Hi.
      * exact Hbr.
    + intro M. cbn [chain_rho chain_ep B_level_auto lift_auto
        F_conjugate_map order_iso_sc].
      symmetry. apply F_project_conjugate.
      * intro y. symmetry. apply Hr.
      * exact Hbi.
Qed.

Corollary chain_iota_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    m g (Hg : hmem H g) x,
    chain_iota Sig H m (B_level_map C m g Hg x) =
    B_level_map C (S m) g Hg (chain_iota Sig H m x).
Proof. intros; apply (proj1 (@chain_fwd_natural Sig H C m g Hg)). Qed.

Corollary chain_rho_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    m g (Hg : hmem H g) y,
    chain_rho Sig H m (B_level_map C (S m) g Hg y) =
    B_level_map C m g Hg (chain_rho Sig H m y).
Proof. intros; apply (proj2 (@chain_fwd_natural Sig H C m g Hg)). Qed.

Corollary chain_bwd_iota_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) m g (Hg : hmem H g) x,
    chain_iota Sig H m
      (auto_bwd (@B_level_auto Sig H C m g Hg) x) =
    auto_bwd (@B_level_auto Sig H C (S m) g Hg)
      (chain_iota Sig H m x).
Proof.
  intros Sig H C m g Hg x.
  apply (@ep_auto_bwd_embed (D_level Sig m) (D_level Sig (S m))
    (chain_ep Sig H m)
    (@B_level_auto Sig H C m g Hg)
    (@B_level_auto Sig H C (S m) g Hg)).
  apply (proj1 (@chain_fwd_natural Sig H C m g Hg)).
Qed.

Corollary chain_bwd_rho_equivariant : forall Sig H
    (C : SyntaxCoding Sig H) m g (Hg : hmem H g) y,
    chain_rho Sig H m
      (auto_bwd (@B_level_auto Sig H C (S m) g Hg) y) =
    auto_bwd (@B_level_auto Sig H C m g Hg)
      (chain_rho Sig H m y).
Proof.
  intros Sig H C m g Hg y.
  apply (@ep_auto_bwd_project (D_level Sig m) (D_level Sig (S m))
    (chain_ep Sig H m)
    (@B_level_auto Sig H C m g Hg)
    (@B_level_auto Sig H C (S m) g Hg)).
  apply (proj2 (@chain_fwd_natural Sig H C m g Hg)).
Qed.

(** * 7.6  The induced automorphism of the bilimit *)

Definition transport_point {Sig H} (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) (x : E_car Sig H) : E_car Sig H.
Proof.
  refine {| ecoord := fun m => B_level_map C m g Hg (ecoord x m) |}.
  intro m. rewrite chain_rho_equivariant, ecoherent. reflexivity.
Defined.

Definition transport_inv_point {Sig H} (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) (x : E_car Sig H) : E_car Sig H.
Proof.
  refine {| ecoord := fun m =>
    auto_bwd (@B_level_auto Sig H C m g Hg) (ecoord x m) |}.
  intro m. rewrite chain_bwd_rho_equivariant, ecoherent. reflexivity.
Defined.

Arguments transport_point {Sig H} C g Hg x.
Arguments transport_inv_point {Sig H} C g Hg x.

Lemma transport_inv_fwd : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) x,
    transport_inv_point C g Hg (transport_point C g Hg x) = x.
Proof.
  intros. apply E_ext. intro m. cbn. apply auto_bwd_fwd.
Qed.

Lemma transport_fwd_inv : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) x,
    transport_point C g Hg (transport_inv_point C g Hg x) = x.
Proof.
  intros. apply E_ext. intro m. cbn. apply auto_fwd_bwd.
Qed.

Definition transport_map {Sig H} (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) : SCMap (E_dcpo Sig H) (E_dcpo Sig H).
Proof.
  apply (@order_iso_sc (E_dcpo Sig H) (E_dcpo Sig H)
    (transport_point C g Hg) (transport_inv_point C g Hg)).
  - intros x y Hxy m. apply sc_monotone, Hxy.
  - intros x y Hxy m. apply sc_monotone, Hxy.
  - apply transport_inv_fwd.
  - apply transport_fwd_inv.
Defined.

Arguments transport_map {Sig H} C g Hg.

Theorem transport_id : forall Sig H (C : SyntaxCoding Sig H),
    transport_map C pid (hmem_pid H) = sc_id (E_dcpo Sig H).
Proof.
  intros Sig H C. apply SCMap_ext. intro x. apply E_ext. intro m. cbn.
  pose proof (f_equal (fun F : SCMap (D_level Sig m) (D_level Sig m) =>
    F (ecoord x m)) (@B_level_id Sig H C m)) as He.
  exact He.
Qed.

Theorem transport_mul : forall Sig H (C : SyntaxCoding Sig H)
    g h (Hg : hmem H g) (Hh : hmem H h),
    @sc_comp (E_dcpo Sig H) (E_dcpo Sig H) (E_dcpo Sig H)
      (transport_map C g Hg) (transport_map C h Hh) =
    transport_map C (pmul g h) (@hmem_mul H g h Hg Hh).
Proof.
  intros Sig H C g h Hg Hh. apply SCMap_ext. intro x.
  apply E_ext. intro m. cbn.
  pose proof (f_equal (fun F : SCMap (D_level Sig m) (D_level Sig m) =>
    F (ecoord x m)) (@B_level_mul Sig H C m g h Hg Hh)) as He.
  exact He.
Qed.

Lemma lower_value_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) m (d : dcar (D_level Sig m)) k x,
    @lower_value Sig H m d k x ->
    @lower_value Sig H m (B_level_map C m g Hg d) k
      (B_level_map C k g Hg x).
Proof.
  intros Sig H C g Hg m d k x Hx. induction Hx.
  - apply lower_here.
  - rewrite <- chain_rho_equivariant. apply lower_down. exact IHHx.
Qed.

Lemma upper_value_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) m (d : dcar (D_level Sig m)) k x,
    @upper_value Sig H m d k x ->
    @upper_value Sig H m (B_level_map C m g Hg d) k
      (B_level_map C k g Hg x).
Proof.
  intros Sig H C g Hg m d k x Hx. induction Hx.
  - apply upper_here.
  - rewrite <- chain_iota_equivariant. apply upper_up. exact IHHx.
Qed.

Lemma eta_coord_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) m k (d : dcar (D_level Sig m)),
    B_level_map C k g Hg (eta_coord_map Sig H m k d) =
    eta_coord_map Sig H m k (B_level_map C m g Hg d).
Proof.
  intros Sig H C g Hg m k d.
  destruct (le_lt_dec k m) as [Hkm|Hmk].
  - apply (@lower_unique Sig H m (B_level_map C m g Hg d) k).
    + apply lower_value_equivariant. apply eta_coord_lower. exact Hkm.
    + apply eta_coord_lower. exact Hkm.
  - apply (@upper_unique Sig H m (B_level_map C m g Hg d) k).
    + apply upper_value_equivariant. apply eta_coord_upper. exact Hmk.
    + apply eta_coord_upper. exact Hmk.
Qed.

Theorem transport_eta : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) m (d : dcar (D_level Sig m)),
    transport_map C g Hg (eta_map Sig H m d) =
    eta_map Sig H m (B_level_map C m g Hg d).
Proof.
  intros. apply E_ext. intro k. cbn.
  apply eta_coord_equivariant.
Qed.

Lemma B0_syntax_code : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) z,
    B0_map C g Hg (Some (proj1_sig (syntax_encode C z))) =
    Some (proj1_sig (syntax_encode C (syntax_act g Hg z))).
Proof.
  intros Sig H C g Hg z. cbn.
  destruct (syntax_encode C z) as [n [H0 H1]] eqn:Hcode. cbn.
  rewrite (code_nat_action_nonreserved C g Hg n H0 H1).
  assert (Hcn : exist (fun k => k <> 0 /\ k <> 1) n (conj H0 H1) =
      syntax_encode C z).
  { apply sig_prop_ext. cbn. now rewrite Hcode. }
  rewrite Hcn, syntax_decode_encode. reflexivity.
Qed.

Theorem quote_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) z,
    transport_map C g Hg (quote_value C z) =
    quote_value C (syntax_act g Hg z).
Proof.
  intros Sig H C g Hg z. unfold quote_value.
  rewrite transport_eta.
  change (eta_map Sig H 0
    (B0_map C g Hg (Some (proj1_sig (syntax_encode C z)))) =
    eta_map Sig H 0
      (Some (proj1_sig (syntax_encode C (syntax_act g Hg z))))).
  rewrite B0_syntax_code. reflexivity.
Qed.

(** Cartesian-closed dcpo combinators used by the evaluator. *)

Definition dep_tuple_sc (X : PDCPO) (I : Type) (D : I -> PDCPO)
    (fs : forall i, SCMap X (D i)) :
    SCMap X (@dep_product_dcpo I D).
Proof.
  refine (@Build_SCMap X (@dep_product_dcpo I D)
    (fun x i => fs i x) _ _).
  - intros x y Hxy i. apply sc_monotone. exact Hxy.
  - intros S HS. split.
    + intros y (x & Hx & ->) i. apply sc_monotone.
      apply (proj1 (dsup_lub X S HS)). exact Hx.
    + intros v Hv i.
      pose proof (@sc_pres_lub X (D i) (fs i) S HS) as Hi.
      apply (proj2 Hi). intros y (x & Hx & ->).
      apply (Hv (fun j => fs j x)).
      exists x. split; [exact Hx|reflexivity].
Defined.

Definition dep_projection_sc (I : Type) (D : I -> PDCPO) (i : I) :
    SCMap (@dep_product_dcpo I D) (D i).
Proof.
  refine (@Build_SCMap (@dep_product_dcpo I D) (D i)
    (fun x => x i) _ _).
  - intros x y Hxy. apply Hxy.
  - intros S HS. apply dsup_lub.
Defined.

Definition power_projection_sc (D : PDCPO) n (i : Finite n) :
    SCMap (power_dcpo D n) D :=
  @dep_projection_sc (Finite n) (fun _ => D) i.

Arguments power_projection_sc D n i : clear implicits.

Definition constant_lift (D E : PDCPO) :
    SCMap E (@scmap_dcpo D E).
Proof.
  refine (@Build_SCMap E (@scmap_dcpo D E)
    (fun e => @sc_const D E e) _ _).
  - intros x y Hxy d. exact Hxy.
  - intros S HS. split.
    + intros f (x & Hx & ->) d.
      apply (proj1 (dsup_lub E S HS)). exact Hx.
    + intros v Hv d. apply (proj2 (dsup_lub E S HS)).
      intros x Hx. apply (Hv (@sc_const D E x)).
      exists x. auto.
Defined.

Definition power_one {D : PDCPO} (x : dcar D) :
    dcar (power_dcpo D 1) :=
  fun _ => x.

Definition pair_power {D : PDCPO} (x y : dcar D) :
    dcar (power_dcpo D 2) :=
  fun i => match i with
  | fzero _ => x
  | fsucc _ => y
  end.

Definition first2 (D : PDCPO) : SCMap (power_dcpo D 2) D :=
  power_projection_sc D 2 (fzero 1).

Definition second2 (D : PDCPO) : SCMap (power_dcpo D 2) D :=
  power_projection_sc D 2 (fsucc (fzero 0)).

Lemma sc_image_sup_eq : forall D E (f : SCMap D E) S HS,
    f (dsup D S HS) =
    dsup E (image_pred f S) (image_directed (sc_monotone f) HS).
Proof.
  intros. apply (@lub_unique E (image_pred f S)).
  - apply sc_pres_lub.
  - apply dsup_lub.
Qed.

Definition dynamic_apply (X D E : PDCPO)
    (F : SCMap X (@scmap_dcpo D E)) (a : SCMap X D) : SCMap X E.
Proof.
  refine (@Build_SCMap X E (fun x => F x (a x)) _ _).
  - intros x y Hxy.
    eapply (@dle_trans E).
    + exact (@sc_monotone X (@scmap_dcpo D E) F x y Hxy (a x)).
    + apply (@sc_monotone D E (F y)). apply sc_monotone. exact Hxy.
  - intros S HS. split.
    + intros z (x & Hx & ->).
      eapply (@dle_trans E).
      * exact (@sc_monotone X (@scmap_dcpo D E) F x (dsup X S HS)
          (proj1 (dsup_lub X S HS) x Hx) (a x)).
      * apply (@sc_monotone D E (F (dsup X S HS))).
        apply (@sc_monotone X D a x (dsup X S HS)).
        apply (proj1 (dsup_lub X S HS)). exact Hx.
    + intros v Hv.
      pose proof (image_directed (sc_monotone F) HS) as HFdir.
      pose proof (image_directed (sc_monotone a) HS) as Hadir.
      pose proof (@sc_image_sup_eq X (@scmap_dcpo D E) F S HS) as HFeq.
      pose proof (@sc_image_sup_eq X D a S HS) as Haeq.
      replace (image_directed (sc_monotone F) HS) with HFdir in HFeq
        by apply proof_irrelevance.
      replace (image_directed (sc_monotone a) HS) with Hadir in Haeq
        by apply proof_irrelevance.
      cbn. rewrite HFeq, scmap_dsup_apply, Haeq.
      apply (proj2 (dsup_lub E _ _)).
      intros q (fi & (x & Hx & ->) & ->).
      pose proof (@sc_pres_lub D E (F x) (image_pred a S) Hadir) as Hfi.
      apply (proj2 Hfi). intros r (aj & (j & Hj & ->) & ->).
      pose proof (proj2 HS) as Hdirect.
      destruct (Hdirect x j Hx Hj) as (k & Hk & Hxk & Hjk).
      eapply (@dle_trans E).
      * exact (@sc_monotone X (@scmap_dcpo D E) F x k Hxk (a j)).
      * eapply (@dle_trans E).
        -- apply (@sc_monotone D E (F k)).
           exact (@sc_monotone X D a j k Hjk).
        -- apply Hv. exists k. auto.
Defined.

Definition pair_left_map (D : PDCPO) (x : dcar D) :
    SCMap D (power_dcpo D 2) :=
  @dep_tuple_sc D (Finite 2) (fun _ => D)
    (fun i => match i with
      | fzero _ => @sc_const D D x
      | fsucc _ => sc_id D
      end).

Definition pair_right_map (D : PDCPO) (y : dcar D) :
    SCMap D (power_dcpo D 2) :=
  @dep_tuple_sc D (Finite 2) (fun _ => D)
    (fun i => match i with
      | fzero _ => sc_id D
      | fsucc _ => @sc_const D D y
      end).

Arguments pair_left_map D x : clear implicits.
Arguments pair_right_map D y : clear implicits.

Definition left_section (D E : PDCPO)
    (J : SCMap (power_dcpo D 2) E) (x : dcar D) : SCMap D E :=
  @sc_comp D (power_dcpo D 2) E J (pair_left_map D x).

Definition right_section (D E : PDCPO)
    (J : SCMap (power_dcpo D 2) E) (y : dcar D) : SCMap D E :=
  @sc_comp D (power_dcpo D 2) E J (pair_right_map D y).

Arguments left_section D E J x : clear implicits.
Arguments right_section D E J y : clear implicits.

Lemma sections_agree : forall D E (J : SCMap (power_dcpo D 2) E) x y,
    left_section D E J x y = right_section D E J y x.
Proof.
  intros. unfold left_section, right_section; cbn.
  apply (f_equal (fun z => J z)).
  apply functional_extensionality_dep. intros [n|n i]; reflexivity.
Qed.

Definition curry2 (D E : PDCPO) (J : SCMap (power_dcpo D 2) E) :
    SCMap D (@scmap_dcpo D E).
Proof.
  refine (@Build_SCMap D (@scmap_dcpo D E)
    (fun x => left_section D E J x) _ _).
  - intros x y Hxy v. unfold left_section; cbn.
    apply (@sc_monotone (power_dcpo D 2) E J). intro i.
    destruct i as [n|n i]; cbn.
    + exact Hxy.
    + apply dle_refl.
  - intros S HS. split.
    + intros f (x & Hx & ->) v. unfold left_section; cbn.
      apply (@sc_monotone (power_dcpo D 2) E J). intro i.
      destruct i as [n|n i]; cbn.
      * apply (proj1 (dsup_lub D S HS)). exact Hx.
      * apply dle_refl.
    + intros V HV v.
      pose proof (@sc_pres_lub D E (right_section D E J v) S HS) as Hvsec.
      rewrite sections_agree.
      apply (proj2 Hvsec). intros z (x & Hx & ->).
      rewrite <- sections_agree.
      apply (HV (left_section D E J x)).
      * exists x. auto.
Defined.

Definition F_coord_projection (Sig : Signature) (D : PDCPO)
    (a : AIndex Sig) :
    SCMap (F_dcpo Sig D) (@scmap_dcpo (power_dcpo D (arity a)) D) :=
  @dep_projection_sc (AIndex Sig)
    (fun b => @scmap_dcpo (power_dcpo D (arity b)) D) a.

Arguments F_coord_projection Sig D a : clear implicits.

Definition theta_first_map (Sig : Signature) (H : Subgroup) :
    SCMap (power_dcpo (E_dcpo Sig H) 2)
      (F_dcpo Sig (E_dcpo Sig H)) :=
  @sc_comp (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H)
    (F_dcpo Sig (E_dcpo Sig H)) (theta_map Sig H)
    (first2 (E_dcpo Sig H)).

Arguments theta_first_map Sig H : clear implicits.

Definition update_coord_map (Sig : Signature) (H : Subgroup) (i : nat)
    (a : AIndex Sig) :
    SCMap (power_dcpo (E_dcpo Sig H) 2)
      (@scmap_dcpo (power_dcpo (E_dcpo Sig H) (arity a))
        (E_dcpo Sig H)).
Proof.
  destruct a as [n f|n P|n L|Q|j|n|].
  - exact (@sc_comp _ _ _ (F_coord_projection Sig (E_dcpo Sig H) (ai_T f))
      (theta_first_map Sig H)).
  - exact (@sc_comp _ _ _ (F_coord_projection Sig (E_dcpo Sig H) (ai_P P))
      (theta_first_map Sig H)).
  - exact (@sc_comp _ _ _ (F_coord_projection Sig (E_dcpo Sig H) (ai_L L))
      (theta_first_map Sig H)).
  - exact (@sc_comp _ _ _ (F_coord_projection Sig (E_dcpo Sig H) (ai_Q Q))
      (theta_first_map Sig H)).
  - destruct (Nat.eq_dec j i) as [->|Hji].
    + exact (@sc_comp _ _ _
        (constant_lift (power_dcpo (E_dcpo Sig H) 0) (E_dcpo Sig H))
        (second2 (E_dcpo Sig H))).
    + exact (@sc_comp _ _ _ (F_coord_projection Sig (E_dcpo Sig H) (ai_var j))
        (theta_first_map Sig H)).
  - exact (@sc_comp _ _ _ (F_coord_projection Sig (E_dcpo Sig H) (ai_slot n))
      (theta_first_map Sig H)).
  - exact (@sc_comp _ _ _ (F_coord_projection Sig (E_dcpo Sig H) ai_assert)
      (theta_first_map Sig H)).
Defined.

Arguments update_coord_map Sig H i a : clear implicits.

Definition update_structure_sc (Sig : Signature) (H : Subgroup) (i : nat) :
    SCMap (power_dcpo (E_dcpo Sig H) 2)
      (F_dcpo Sig (E_dcpo Sig H)) :=
  @dep_tuple_sc (power_dcpo (E_dcpo Sig H) 2) (AIndex Sig)
    (fun a => @scmap_dcpo (power_dcpo (E_dcpo Sig H) (arity a))
      (E_dcpo Sig H))
    (update_coord_map Sig H i).

Arguments update_structure_sc Sig H i : clear implicits.

Definition upd_map (Sig : Signature) (H : Subgroup) (i : nat) :
    SCMap (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H) :=
  @sc_comp (power_dcpo (E_dcpo Sig H) 2)
    (F_dcpo Sig (E_dcpo Sig H)) (E_dcpo Sig H)
    (omega_map Sig H) (update_structure_sc Sig H i).

Definition bottom_operation (D : PDCPO) n :
    SCMap (power_dcpo D n) D := @sc_const _ _ (dbot D).

Arguments bottom_operation D n : clear implicits.

Definition constant_bottom_coord (Sig : Signature) (H : Subgroup) n k :
    SCMap (@scmap_dcpo (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H))
      (@scmap_dcpo (power_dcpo (E_dcpo Sig H) k) (E_dcpo Sig H)) :=
  @sc_const
    (@scmap_dcpo (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H))
    (@scmap_dcpo (power_dcpo (E_dcpo Sig H) k) (E_dcpo Sig H))
    (bottom_operation (E_dcpo Sig H) k).

Arguments constant_bottom_coord Sig H n k : clear implicits.

Definition resident_coord_sc (Sig : Signature) (H : Subgroup) (n : nat)
    (a : AIndex Sig) :
    SCMap (@scmap_dcpo (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H))
      (@scmap_dcpo (power_dcpo (E_dcpo Sig H) (arity a))
        (E_dcpo Sig H)).
Proof.
  destruct a as [k f|k P|k L|Q|i|k|].
  - exact (constant_bottom_coord Sig H n k).
  - exact (constant_bottom_coord Sig H n k).
  - exact (constant_bottom_coord Sig H n k).
  - exact (constant_bottom_coord Sig H n 1).
  - exact (constant_bottom_coord Sig H n 0).
  - destruct (Nat.eq_dec k n) as [->|Hkn].
    + exact (sc_id (@scmap_dcpo (power_dcpo (E_dcpo Sig H) n)
        (E_dcpo Sig H))).
    + exact (constant_bottom_coord Sig H n k).
  - exact (constant_bottom_coord Sig H n 1).
Defined.

Arguments resident_coord_sc Sig H n a : clear implicits.

Definition resident_structure_sc (Sig : Signature) (H : Subgroup) (n : nat) :
    SCMap (@scmap_dcpo (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H))
      (F_dcpo Sig (E_dcpo Sig H)) :=
  @dep_tuple_sc (@scmap_dcpo (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H))
    (AIndex Sig)
    (fun a => @scmap_dcpo (power_dcpo (E_dcpo Sig H) (arity a))
      (E_dcpo Sig H))
    (resident_coord_sc Sig H n).

Definition enc_map (Sig : Signature) (H : Subgroup) (n : nat) :
    SCMap (@scmap_dcpo (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H))
      (E_dcpo Sig H) :=
  @sc_comp _ _ _ (omega_map Sig H) (resident_structure_sc Sig H n).

Lemma resident_structure_sc_apply : forall Sig H n
    (K : SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H)),
    resident_structure_sc Sig H n K = @resident_structure Sig H n K.
Proof.
  intros Sig H n K. apply functional_extensionality_dep. intro a.
  destruct a as [k f|k P|k L|Q|i|k|]; cbn
    [resident_structure_sc resident_coord_sc dep_tuple_sc
      constant_bottom_coord bottom_operation resident_structure].
  all: try reflexivity.
  destruct (Nat.eq_dec k n) as [p|Hkn].
  - subst k. transitivity K.
    + unfold resident_structure_sc, dep_tuple_sc; cbn.
      unfold resident_coord_sc.
      destruct (Nat.eq_dec n n) as [q|Hnn]; [|contradiction].
      assert (Hq : q = @eq_refl nat n) by apply proof_irrelevance.
      now rewrite Hq.
    + unfold eq_rect_r. reflexivity.
  - unfold resident_structure_sc, dep_tuple_sc; cbn.
    unfold resident_coord_sc, resident_structure,
      constant_bottom_coord, bottom_operation; cbn.
    destruct (Nat.eq_dec k n); [contradiction|reflexivity].
Qed.

Lemma enc_map_apply : forall Sig H n
    (K : SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H)),
    enc_map Sig H n K = enc Sig H n K.
Proof.
  intros Sig H n K. unfold enc_map, enc.
  change (((omega_map Sig H) (resident_structure_sc Sig H n K)) =
    ((omega_map Sig H) (@resident_structure Sig H n K))).
  now rewrite resident_structure_sc_apply.
Qed.

Lemma update_structure_sc_apply : forall Sig H i (e v : E_car Sig H),
    update_structure_sc Sig H i (@pair_power (E_dcpo Sig H) e v) =
    @update_structure Sig H i (theta_map Sig H e) v.
Proof.
  intros Sig H i e v. apply functional_extensionality_dep. intro a.
  destruct a as [k f|k P|k L|Q|j|k|]; cbn
    [update_structure_sc update_coord_map dep_tuple_sc theta_first_map
      first2 second2 power_projection_sc dep_projection_sc pair_power
      update_structure sc_comp constant_lift].
  all: try reflexivity.
  destruct (Nat.eq_dec j i) as [p|Hji].
  - subst j.
    unfold update_structure_sc, dep_tuple_sc; cbn.
    unfold update_coord_map.
    destruct (Nat.eq_dec i i) as [q|Hii]; [|contradiction].
    assert (Hq : q = @eq_refl nat i) by apply proof_irrelevance.
    rewrite Hq. cbn [sc_comp constant_lift second2
      power_projection_sc dep_projection_sc pair_power].
    unfold update_structure; cbn.
    destruct (Nat.eq_dec i i); [reflexivity|contradiction].
  - unfold update_structure_sc, dep_tuple_sc; cbn.
    unfold update_coord_map.
    destruct (Nat.eq_dec j i); [contradiction|].
    unfold update_structure; cbn.
    destruct (Nat.eq_dec j i); [contradiction|reflexivity].
Qed.

Lemma upd_map_apply : forall Sig H i (e v : E_car Sig H),
    upd_map Sig H i (@pair_power (E_dcpo Sig H) e v) = upd Sig H i e v.
Proof.
  intros Sig H i e v. unfold upd_map, upd.
  change (((omega_map Sig H)
    (update_structure_sc Sig H i (@pair_power (E_dcpo Sig H) e v))) =
    ((omega_map Sig H) (@update_structure Sig H i (theta_map Sig H e) v))).
  now rewrite update_structure_sc_apply.
Qed.

Definition operation_family_map (Sig : Signature) (H : Subgroup)
    (a : AIndex Sig) :
    SCMap (E_dcpo Sig H)
      (@scmap_dcpo (power_dcpo (E_dcpo Sig H) (arity a))
        (E_dcpo Sig H)) :=
  @sc_comp (E_dcpo Sig H) (F_dcpo Sig (E_dcpo Sig H))
    (@scmap_dcpo (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H))
    (F_coord_projection Sig (E_dcpo Sig H) a) (theta_map Sig H).

Definition semantic_node (Sig : Signature) (H : Subgroup) (a : AIndex Sig)
    (args : SCMap (E_dcpo Sig H)
      (power_dcpo (E_dcpo Sig H) (arity a))) :
    SCMap (E_dcpo Sig H) (E_dcpo Sig H) :=
  @dynamic_apply (E_dcpo Sig H)
    (power_dcpo (E_dcpo Sig H) (arity a)) (E_dcpo Sig H)
    (@operation_family_map Sig H a) args.

Definition finite_caseS {n} (i : Finite (S n))
    (P : Finite (S n) -> Type)
    (hz : P (fzero n))
    (hs : forall j : Finite n, P (@fsucc n j)) : P i.
Proof.
  dependent destruction i.
  - exact hz.
  - exact (hs i).
Defined.

Definition power_cons_sc (X D : PDCPO) n
    (f : SCMap X D) (fs : SCMap X (power_dcpo D n)) :
    SCMap X (power_dcpo D (S n)) :=
  @dep_tuple_sc X (Finite (S n)) (fun _ => D)
    (fun i => @finite_caseS n i (fun _ => SCMap X D) f
      (fun j => @sc_comp X (power_dcpo D n) D
        (power_projection_sc D n j) fs)).

Arguments power_cons_sc X D n f fs : clear implicits.

Definition empty_tuple_sc (X D : PDCPO) : SCMap X (power_dcpo D 0) :=
  @sc_const X (power_dcpo D 0) (empty_power D).

Definition singleton_tuple_sc (X D : PDCPO) (f : SCMap X D) :
    SCMap X (power_dcpo D 1) :=
  power_cons_sc X D 0 f (empty_tuple_sc X D).

Definition abstraction_map (Sig : Signature) (H : Subgroup) (i : nat)
    (body : SCMap (E_dcpo Sig H) (E_dcpo Sig H)) :
    SCMap (E_dcpo Sig H)
      (@scmap_dcpo (E_dcpo Sig H) (E_dcpo Sig H)) :=
  @curry2 (E_dcpo Sig H) (E_dcpo Sig H)
    (@sc_comp (power_dcpo (E_dcpo Sig H) 2) (E_dcpo Sig H)
      (E_dcpo Sig H) body (upd_map Sig H i)).
