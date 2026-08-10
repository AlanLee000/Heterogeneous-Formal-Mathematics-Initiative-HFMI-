From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.

Import ListNotations.

Module InterpretivePro1130.

Inductive term : Type :=
| Var : nat -> term
| App : term -> term -> term
| Fun : nat -> list term -> term
| Quote : list (term * term) -> term
| Bot : term
| Eq : term -> term -> term
| Neg : term -> term
| Imp : term -> term -> term
| All : nat -> term -> term.

Fixpoint formula (t : term) : Prop :=
  match t with
  | Bot => True
  | Eq _ _ => True
  | Neg p => formula p
  | Imp p q => formula p /\ formula q
  | All _ p => formula p
  | _ => False
  end.

Record signature : Type := {
  arity : nat -> nat
}.

Definition pair_code (x y : nat) : nat := (2 ^ x) * (2 * y + 1).

Inductive syntax_tag : Set :=
| tag_var | tag_app | tag_fun | tag_quote | tag_bot
| tag_eq | tag_neg | tag_imp | tag_all.

Lemma syntax_tag_separation :
  tag_var <> tag_app /\
  tag_fun <> tag_quote /\
  tag_bot <> tag_eq /\
  tag_neg <> tag_imp /\
  tag_imp <> tag_all.
Proof.
  repeat split; discriminate.
Qed.

Fixpoint remove_nat (i : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: rest =>
      if Nat.eq_dec x i then remove_nat i rest else x :: remove_nat i rest
  end.

Fixpoint union_nat (xs ys : list nat) : list nat :=
  match xs with
  | [] => ys
  | x :: rest =>
      if in_dec Nat.eq_dec x ys then union_nat rest ys
      else x :: union_nat rest ys
  end.

Fixpoint fv (t : term) : list nat :=
  match t with
  | Var i => [i]
  | App p q => union_nat (fv p) (fv q)
  | Fun _ args => fold_right (fun u acc => union_nat (fv u) acc) [] args
  | Quote _ => []
  | Bot => []
  | Eq p q => union_nat (fv p) (fv q)
  | Neg p => fv p
  | Imp p q => union_nat (fv p) (fv q)
  | All i p => remove_nat i (fv p)
  end.

Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: rest => Nat.max x (max_list rest)
  end.

Definition fresh (xs : list nat) : nat := S (max_list xs).

Fixpoint subst_simple (t : term) (i : nat) (r : term) : term :=
  match t with
  | Var j => if Nat.eq_dec j i then r else Var j
  | App p q => App (subst_simple p i r) (subst_simple q i r)
  | Fun s args => Fun s (map (fun u => subst_simple u i r) args)
  | Quote Q => Quote Q
  | Bot => Bot
  | Eq p q => Eq (subst_simple p i r) (subst_simple q i r)
  | Neg p => Neg (subst_simple p i r)
  | Imp p q => Imp (subst_simple p i r) (subst_simple q i r)
  | All j p =>
      if Nat.eq_dec j i then All j p
      else if in_dec Nat.eq_dec j (fv r) then All j p
      else All j (subst_simple p i r)
  end.

Inductive subst_rel : term -> nat -> term -> term -> Prop :=
| SRVarSame :
    forall i r, subst_rel (Var i) i r r
| SRVarOther :
    forall i j r, i <> j -> subst_rel (Var j) i r (Var j)
| SRApp :
    forall p q p' q' i r,
      subst_rel p i r p' ->
      subst_rel q i r q' ->
      subst_rel (App p q) i r (App p' q')
| SRFun :
    forall s args args' i r,
      Forall2 (fun u u' => subst_rel u i r u') args args' ->
      subst_rel (Fun s args) i r (Fun s args')
| SRQuote :
    forall Q i r, subst_rel (Quote Q) i r (Quote Q)
| SRBot :
    forall i r, subst_rel Bot i r Bot
| SREq :
    forall p q p' q' i r,
      subst_rel p i r p' ->
      subst_rel q i r q' ->
      subst_rel (Eq p q) i r (Eq p' q')
| SRNeg :
    forall p p' i r,
      subst_rel p i r p' ->
      subst_rel (Neg p) i r (Neg p')
| SRImp :
    forall p q p' q' i r,
      subst_rel p i r p' ->
      subst_rel q i r q' ->
      subst_rel (Imp p q) i r (Imp p' q')
| SRAllSame :
    forall i p r, subst_rel (All i p) i r (All i p)
| SRAllIrrelevant :
    forall i j p r,
      i <> j ->
      ~ In i (fv p) ->
      subst_rel (All j p) i r (All j p)
| SRAllNoCapture :
    forall i j p p' r,
      i <> j ->
      In i (fv p) ->
      ~ In j (fv r) ->
      subst_rel p i r p' ->
      subst_rel (All j p) i r (All j p')
| SRAllRename :
    forall i j k p renamed p' r,
      i <> j ->
      In i (fv p) ->
      In j (fv r) ->
      k = fresh (union_nat (fv p) (union_nat (fv r) [i; j])) ->
      subst_rel p j (Var k) renamed ->
      subst_rel renamed i r p' ->
      subst_rel (All j p) i r (All k p').

Inductive binder_free : term -> Prop :=
| BFVar : forall j, binder_free (Var j)
| BFApp :
    forall p q,
      binder_free p ->
      binder_free q ->
      binder_free (App p q)
| BFQuote : forall Q, binder_free (Quote Q)
| BFBot : binder_free Bot
| BFEq :
    forall p q,
      binder_free p ->
      binder_free q ->
      binder_free (Eq p q)
| BFNeg :
    forall p,
      binder_free p ->
      binder_free (Neg p)
| BFImp :
    forall p q,
      binder_free p ->
      binder_free q ->
      binder_free (Imp p q).

Fixpoint subst_simple_rel_binder_free
    (t : term) (i : nat) (r : term)
    (h : binder_free t) {struct h}
    : subst_rel t i r (subst_simple t i r).
Proof.
  destruct h as
    [j | p q hp hq | Q | | p q hp hq | p hp | p q hp hq]; simpl.
  - destruct (Nat.eq_dec j i) as [heq | hne].
    + subst j. apply SRVarSame.
    + apply SRVarOther. intro hij. apply hne. symmetry. exact hij.
  - apply SRApp.
    + exact (subst_simple_rel_binder_free p i r hp).
    + exact (subst_simple_rel_binder_free q i r hq).
  - apply SRQuote.
  - apply SRBot.
  - apply SREq.
    + exact (subst_simple_rel_binder_free p i r hp).
    + exact (subst_simple_rel_binder_free q i r hq).
  - apply SRNeg.
    exact (subst_simple_rel_binder_free p i r hp).
  - apply SRImp.
    + exact (subst_simple_rel_binder_free p i r hp).
    + exact (subst_simple_rel_binder_free q i r hq).
Qed.

Inductive reg_tm_direct (i : nat) : term -> Prop :=
| RTVar :
    forall j, reg_tm_direct i (Var j)
| RTApp :
    forall p q,
      reg_tm_direct i p ->
      reg_tm_direct i q ->
      reg_tm_direct i (App p q)
| RTFun :
    forall s args,
      Forall (reg_tm_direct i) args ->
      reg_tm_direct i (Fun s args)
| RTQuote :
    forall Q, reg_tm_direct i (Quote Q)
| RTBot :
    ~ In i (fv Bot) ->
    reg_tm_direct i Bot
| RTEq :
    forall p q,
      ~ In i (fv (Eq p q)) ->
      reg_tm_direct i (Eq p q)
| RTNeg :
    forall p,
      ~ In i (fv (Neg p)) ->
      reg_tm_direct i (Neg p)
| RTImp :
    forall p q,
      ~ In i (fv (Imp p q)) ->
      reg_tm_direct i (Imp p q)
| RTAll :
    forall j p,
      ~ In i (fv (All j p)) ->
      reg_tm_direct i (All j p).

Fixpoint reg_fm (i : nat) (t : term) {struct t} : Prop :=
  match t with
  | Bot => True
  | Eq p q => reg_tm_direct i p /\ reg_tm_direct i q
  | Neg p => reg_fm i p
  | Imp p q => reg_fm i p /\ reg_fm i q
  | All j p => j = i \/ (j <> i /\ reg_fm i p /\ reg_fm j p)
  | _ => False
  end.

Definition Conj (p q : term) : term := Neg (Imp p (Neg q)).
Definition Disj (p q : term) : term := Imp (Neg p) q.
Definition Iff (p q : term) : term := Conj (Imp p q) (Imp q p).

Inductive axiom : term -> Prop :=
| AxProp1 :
    forall p q, formula p -> formula q ->
      axiom (Imp p (Imp q p))
| AxProp2 :
    forall p q r, formula p -> formula q -> formula r ->
      axiom (Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r)))
| AxProp3 :
    forall p q, formula p -> formula q ->
      axiom (Imp (Imp (Neg q) (Neg p)) (Imp p q))
| AxAllInst :
    forall i p t p',
      formula p ->
      reg_fm i p ->
      subst_rel p i t p' ->
      axiom (Imp (All i p) p')
| AxAllDistrib :
    forall i p q,
      formula p -> formula q ->
      ~ In i (fv p) ->
      axiom (Imp (All i (Imp p q)) (Imp p (All i q)))
| AxEqRefl :
    forall t, axiom (Eq t t)
| AxEqSubst :
    forall i p t u pt pu,
      formula p ->
      reg_fm i p ->
      subst_rel p i t pt ->
      subst_rel p i u pu ->
      axiom (Imp (Eq t u) (Imp pt pu)).

Inductive proof_step : list term -> term -> Prop :=
| StepAx :
    forall Gamma p, axiom p -> proof_step Gamma p
| StepHyp :
    forall Gamma p, In p Gamma -> proof_step Gamma p
| StepMP :
    forall Gamma p q,
      proof_step Gamma p ->
      proof_step Gamma (Imp p q) ->
      proof_step Gamma q
| StepGen :
    forall Gamma i p,
      proof_step Gamma p ->
      proof_step Gamma (All i p).

Theorem subst_rel_preserves_formula :
  forall p i r p',
    formula p ->
    subst_rel p i r p' ->
    formula p'.
Proof.
  intros p i r p' Hform Hsubst.
  induction Hsubst; simpl in *.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - exact I.
  - exact I.
  - exact (IHHsubst Hform).
  - destruct Hform as [Hp Hq].
    split.
    + exact (IHHsubst1 Hp).
    + exact (IHHsubst2 Hq).
  - exact Hform.
  - exact Hform.
  - exact (IHHsubst Hform).
  - pose proof (IHHsubst1 Hform) as Hrenamed.
    exact (IHHsubst2 Hrenamed).
Qed.

Definition context_formulas (Gamma : list term) : Prop :=
  forall p, In p Gamma -> formula p.

Theorem axiom_is_formula :
  forall p,
    axiom p ->
    formula p.
Proof.
  intros p Hax.
  destruct Hax; simpl; repeat split; try assumption.
  - exact (subst_rel_preserves_formula p i t p' H H1).
  - exact (subst_rel_preserves_formula p i t pt H H1).
  - exact (subst_rel_preserves_formula p i u pu H H2).
Qed.

Theorem proof_step_is_formula :
  forall Gamma p,
    context_formulas Gamma ->
    proof_step Gamma p ->
    formula p.
Proof.
  intros Gamma p Hctx Hstep.
  induction Hstep.
  - exact (axiom_is_formula p H).
  - exact (Hctx p H).
  - simpl in IHHstep2. exact (proj2 (IHHstep2 Hctx)).
  - simpl. exact (IHHstep Hctx).
Qed.

Record universe : Type := {
  carrier : Type;
  botD : carrier;
  bullet : carrier -> carrier -> carrier;
  syn : term -> carrier;
  syn_injective : forall p q, syn p = syn q -> p = q;
  tup : list carrier -> carrier;
  tag : nat -> list carrier -> carrier;
  tag_injective :
    forall rho xs ys, tag rho xs = tag rho ys -> xs = ys;
  tag_separate :
    forall rho sigma xs ys,
      rho <> sigma -> tag rho xs <> tag sigma ys;
  retag : nat -> nat -> carrier -> carrier;
  retag_tag :
    forall rho sigma xs, retag rho sigma (tag rho xs) = tag sigma xs;
  cur : nat -> carrier -> carrier;
  uncur : nat -> carrier -> carrier;
  cur_uncur : forall n d, cur n (uncur n d) = d;
  uncur_cur : forall n d, uncur n (cur n d) = d;
  cl : list carrier -> carrier
}.

Arguments carrier _ : clear implicits.

Record model (U : universe) : Type := {
  root : carrier U;
  interp : nat -> carrier U
}.

Definition rho_ctx : nat := 20.
Definition rho_ass : nat := 21.
Definition rho_td : nat := 22.
Definition rho_model : nat := 23.
Definition rho_table : nat := 24.
Definition rho_evalarg : nat := 25.
Definition rho_bool : nat := 26.
Definition rho_intstate : nat := 27.
Definition rho_tabstate : nat := 28.
Definition rho_op : nat := 29.

Definition tab {U : universe} (M : model U) : carrier U :=
  tag U rho_table [].

Definition mcode {U : universe} (M : model U) : carrier U :=
  tag U rho_model [root U M; tab M].

Definition td {U : universe} (M : model U) (phi : term) : carrier U :=
  tag U rho_td [mcode M; syn U phi].

Definition evalarg {U : universe} (t : term) : carrier U :=
  tag U rho_evalarg [syn U t].

Definition closure_name {U : universe} (M : model U) (t : term) : carrier U :=
  cl U [mcode M; syn U t].

Fixpoint val {U : universe} (M : model U) (rho : nat -> carrier U)
    (t : term) : carrier U :=
  match t with
  | Var i => rho i
  | App p q => bullet U (val M rho p) (val M rho q)
  | Fun s args => bullet U (interp U M s) (tup U (map (val M rho) args))
  | Quote _ => syn U t
  | Bot => td M t
  | Eq _ _ => td M t
  | Neg _ => td M t
  | Imp _ _ => td M t
  | All _ _ => td M t
  end.

Definition update {U : universe} (rho : nat -> carrier U)
    (i : nat) (b : carrier U) : nat -> carrier U :=
  fun j => if Nat.eq_dec j i then b else rho j.

Fixpoint holds {U : universe} (M : model U)
    (rho : nat -> carrier U) (phi : term) : Prop :=
  match phi with
  | Bot => False
  | Eq p q => val M rho p = val M rho q
  | Neg p => ~ holds M rho p
  | Imp p q => holds M rho p -> holds M rho q
  | All i p => forall b, holds M (update rho i b) p
  | _ => False
  end.

Lemma union_nat_spec :
  forall x xs ys,
    In x (union_nat xs ys) <-> In x xs \/ In x ys.
Proof.
  intros x xs ys.
  induction xs as [| a rest IH]; simpl.
  - tauto.
  - destruct (in_dec Nat.eq_dec a ys) as [Hay | Hnay].
    + rewrite IH. split.
      * intro H. destruct H as [Hrest | Hy].
        -- left. right. exact Hrest.
        -- right. exact Hy.
      * intros [[Hxa | Hrest] | Hy].
        -- subst a. right. exact Hay.
        -- left. exact Hrest.
        -- right. exact Hy.
    + simpl. rewrite IH. split.
      * intros [Hxa | [Hrest | Hy]].
        -- left. left. exact Hxa.
        -- left. right. exact Hrest.
        -- right. exact Hy.
      * intros [[Hxa | Hrest] | Hy].
        -- left. exact Hxa.
        -- right. left. exact Hrest.
        -- right. right. exact Hy.
Qed.

Lemma not_in_union_nat :
  forall x xs ys,
    ~ In x (union_nat xs ys) -> ~ In x xs /\ ~ In x ys.
Proof.
  intros x xs ys H.
  rewrite union_nat_spec in H.
  split; intro Hin; apply H; [left | right]; exact Hin.
Qed.

Lemma remove_nat_spec :
  forall x y xs,
    In x (remove_nat y xs) <-> In x xs /\ x <> y.
Proof.
  intros x y xs.
  induction xs as [| a rest IH]; simpl.
  - split; intro H.
    + contradiction.
    + destruct H as [[] _].
  - destruct (Nat.eq_dec a y) as [Hay | Hnay].
    + subst a. rewrite IH. split.
      * intros [Hin Hne]. split.
        -- right. exact Hin.
        -- exact Hne.
      * intros [[Hxy | Hin] Hne].
        -- exfalso. exact (Hne (eq_sym Hxy)).
        -- split; assumption.
    + simpl. rewrite IH. split.
      * intros [Hxa | [Hin Hne]].
        -- split.
           ++ left. exact Hxa.
           ++ subst a. exact Hnay.
        -- split.
           ++ right. exact Hin.
           ++ exact Hne.
      * intros [[Hxa | Hin] Hne].
        -- left. exact Hxa.
        -- right. split; assumption.
Qed.

Fixpoint term_size (t : term) : nat :=
  match t with
  | Var _ => 1
  | App p q => S (term_size p + term_size q)
  | Fun _ args =>
      S (fold_right (fun u acc => term_size u + acc) 0 args)
  | Quote _ => 1
  | Bot => 1
  | Eq p q => S (term_size p + term_size q)
  | Neg p => S (term_size p)
  | Imp p q => S (term_size p + term_size q)
  | All _ p => S (term_size p)
  end.

Lemma term_size_positive :
  forall t, 1 <= term_size t.
Proof.
  induction t; simpl; lia.
Qed.

Lemma term_size_fun_arg_lt :
  forall s args u,
    In u args ->
    term_size u < term_size (Fun s args).
Proof.
  intros s args u Hin.
  simpl.
  induction args as [| a rest IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hua | Hin].
    + subst a. lia.
    + specialize (IH Hin). lia.
Qed.

Lemma term_size_fun_tail_le :
  forall s a rest n,
    term_size (Fun s (a :: rest)) <= S n ->
    term_size (Fun s rest) <= n.
Proof.
  intros s a rest n Hsize.
  simpl in Hsize |- *.
  pose proof (term_size_positive a).
  lia.
Qed.

Lemma fold_fv_spec :
  forall x args,
    In x (fold_right (fun u acc => union_nat (fv u) acc) [] args) <->
    exists u, In u args /\ In x (fv u).
Proof.
  intros x args.
  induction args as [| a rest IH]; simpl.
  - split.
    + intro H. contradiction.
    + intros [u [[] _]].
  - rewrite union_nat_spec. rewrite IH. split.
    + intros [Ha | [u [Hin Hfv]]].
      * exists a. split; [left; reflexivity | exact Ha].
      * exists u. split; [right; exact Hin | exact Hfv].
    + intros [u [[Hua | Hin] Hfv]].
      * subst u. left. exact Hfv.
      * right. exists u. split; assumption.
Qed.

Lemma max_list_ge :
  forall x xs,
    In x xs -> x <= max_list xs.
Proof.
  intros x xs.
  induction xs as [| a rest IH]; simpl.
  - contradiction.
  - intros [Hxa | Hin].
    + subst a. apply Nat.le_max_l.
    + transitivity (max_list rest).
      * exact (IH Hin).
      * apply Nat.le_max_r.
Qed.

Lemma fresh_not_in :
  forall xs,
    ~ In (fresh xs) xs.
Proof.
  intros xs Hin.
  unfold fresh in Hin.
  pose proof (max_list_ge (S (max_list xs)) xs Hin) as Hle.
  lia.
Qed.

Lemma update_same :
  forall U (rho : nat -> carrier U) i b c,
    update (update rho i b) i c = update rho i c.
Proof.
  intros U rho i b c.
  apply functional_extensionality. intro k.
  unfold update.
  destruct (Nat.eq_dec k i); reflexivity.
Qed.

Lemma update_comm :
  forall U (rho : nat -> carrier U) i j b c,
    i <> j ->
    update (update rho i b) j c =
    update (update rho j c) i b.
Proof.
  intros U rho i j b c Hij.
  apply functional_extensionality. intro k.
  unfold update.
  destruct (Nat.eq_dec k j) as [Hkj | Hnkj];
  destruct (Nat.eq_dec k i) as [Hki | Hnki];
  subst; try contradiction; reflexivity.
Qed.

Lemma update_alpha_rename_env :
  forall U (rho : nat -> carrier U) i j k v b,
    i <> j ->
    i <> k ->
    j <> k ->
    update (update (update rho k b) i v) j b =
    update (update (update rho i v) j b) k b.
Proof.
  intros U rho i j k v b Hij Hik Hjk.
  apply functional_extensionality. intro x.
  unfold update.
  destruct (Nat.eq_dec x j) as [Hxj | Hxj];
  destruct (Nat.eq_dec x k) as [Hxk | Hxk];
  destruct (Nat.eq_dec x i) as [Hxi | Hxi];
  subst; try contradiction; reflexivity.
Qed.

Lemma term_freshness_val_size :
  forall n U (M : model U) rho i b t,
    term_size t <= n ->
    ~ In i (fv t) ->
    val M (update rho i b) t = val M rho t.
Proof.
  induction n as [| n IH]; intros U M rho i b t Hsize Hfresh.
  - pose proof (term_size_positive t). lia.
  - destruct t; simpl in *.
    + unfold update.
      destruct (Nat.eq_dec n0 i) as [Heq | Hne].
      * subst n0. exfalso. apply Hfresh. left. reflexivity.
      * reflexivity.
    + destruct (not_in_union_nat i (fv t1) (fv t2) Hfresh)
        as [Hfresh1 Hfresh2].
      rewrite (IH U M rho i b t1); try lia; try exact Hfresh1.
      rewrite (IH U M rho i b t2); try lia; try exact Hfresh2.
      reflexivity.
    + f_equal.
      f_equal.
      apply map_ext_in. intros a Hin.
      apply IH.
      * pose proof (term_size_fun_arg_lt n0 l a Hin) as Hlt.
        simpl in Hlt. lia.
      * intro Hfv. apply Hfresh.
        rewrite fold_fv_spec.
        exists a. split; assumption.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Theorem term_freshness_val :
  forall U (M : model U) rho i b t,
    ~ In i (fv t) -> 
    val M (update rho i b) t = val M rho t.
Proof.
  intros U M rho i b t Hfresh.
  apply (term_freshness_val_size (term_size t)); [lia | exact Hfresh].
Qed.

Definition transparent_term_substitution_law : Prop :=
  forall U (M : model U) rho i x r x',
    reg_tm_direct i x ->
    subst_rel x i r x' ->
    val M rho x' =
    val M (update rho i (val M rho r)) x.

Lemma subst_rel_notin_identity_size :
  forall n t i r t',
    term_size t <= n ->
    ~ In i (fv t) ->
    subst_rel t i r t' ->
    t' = t.
Proof.
  induction n as [| n IH]; intros t i r t' Hsize Hfresh Hsubst.
  - pose proof (term_size_positive t). lia.
  - inversion Hsubst; subst; simpl in *.
    + exfalso. apply Hfresh. left. reflexivity.
    + reflexivity.
    + destruct (not_in_union_nat i (fv p) (fv q) Hfresh)
        as [Hfreshp Hfreshq].
      f_equal.
      * apply (IH p i r p'); try lia; assumption.
      * apply (IH q i r q'); try lia; assumption.
    + f_equal.
      clear Hsubst.
      revert args' H Hfresh Hsize.
      induction args as [| a rest IHargs];
        intros args' Hargs Hfresh Hsize; inversion Hargs; subst; simpl in *.
      * reflexivity.
      * f_equal.
        -- apply (IH a i r y); try assumption.
           ++ pose proof (term_size_fun_arg_lt s (a :: rest) a
                (or_introl eq_refl)) as Hlt.
              simpl in Hlt. lia.
           ++ intro Hin. apply Hfresh.
              rewrite union_nat_spec.
              left. exact Hin.
        -- apply IHargs; try assumption.
           ++ intro Hin. apply Hfresh.
              rewrite union_nat_spec.
              right. exact Hin.
           ++ lia.
    + reflexivity.
    + reflexivity.
    + destruct (not_in_union_nat i (fv p) (fv q) Hfresh)
        as [Hfreshp Hfreshq].
      f_equal.
      * apply (IH p i r p'); try lia; assumption.
      * apply (IH q i r q'); try lia; assumption.
    + f_equal. apply (IH p i r p'); try lia; assumption.
    + destruct (not_in_union_nat i (fv p) (fv q) Hfresh)
        as [Hfreshp Hfreshq].
      f_equal.
      * apply (IH p i r p'); try lia; assumption.
      * apply (IH q i r q'); try lia; assumption.
    + reflexivity.
    + reflexivity.
    + f_equal.
      apply (IH p i r p'); try lia.
      * intro Hin. apply Hfresh.
        rewrite remove_nat_spec. split.
        -- exact Hin.
        -- intro Heq. apply H. exact Heq.
      * assumption.
    + exfalso. apply Hfresh.
      rewrite remove_nat_spec. split.
      * exact H0.
      * intro Heq. apply H. exact Heq.
Qed.

Theorem subst_rel_notin_identity :
  forall t i r t',
    ~ In i (fv t) ->
    subst_rel t i r t' ->
    t' = t.
Proof.
  intros t i r t' Hfresh Hsubst.
  apply (subst_rel_notin_identity_size (term_size t) t i r t');
    [lia | exact Hfresh | exact Hsubst].
Qed.

Lemma transparent_term_substitution_size :
  forall n U (M : model U) rho i x r x',
    term_size x <= n ->
    reg_tm_direct i x ->
    subst_rel x i r x' ->
    val M rho x' =
    val M (update rho i (val M rho r)) x.
Proof.
  induction n as [| n IH]; intros U M rho i x r x' Hsize Hreg Hsubst.
  - pose proof (term_size_positive x). lia.
  - inversion Hreg; subst; inversion Hsubst; subst; simpl in *.
    + unfold update.
      destruct (Nat.eq_dec i i) as [_ | Hneq].
      * reflexivity.
      * exfalso. apply Hneq. reflexivity.
    + unfold update.
      destruct (Nat.eq_dec j i) as [Heq | _].
      * subst j.
        match goal with
        | Hneq : i <> i |- _ =>
            exfalso; apply Hneq; reflexivity
        end.
      * reflexivity.
    + f_equal.
      * apply (IH U M rho i p r p'); try lia; assumption.
      * apply (IH U M rho i q r q'); try lia; assumption.
    + f_equal. f_equal.
      match goal with
      | Hrel : Forall2 _ args args',
        Hregargs : Forall (reg_tm_direct i) args |- _ =>
          clear Hsubst;
          revert Hregargs Hsize;
          induction Hrel as [| a b rest rest' Hsub Hrel IHHrel];
          intros Hregargs Hsize; inversion Hregargs; subst; simpl in *
      end.
      * reflexivity.
      * f_equal.
        -- apply (IH U M rho i a r b); try assumption.
           pose proof (term_size_fun_arg_lt s (a :: rest) a
             (or_introl eq_refl)) as Hlt.
           simpl in Hlt. lia.
        -- apply IHHrel; try assumption.
           ++ apply RTFun. exact H3.
           ++ apply (term_size_fun_tail_le s a rest n) in Hsize.
              simpl in Hsize |- *.
              lia.
    + reflexivity.
    + reflexivity.
    + assert (Eq p' q' = Eq p q) as Hid.
      { apply subst_rel_notin_identity with (i := i) (r := r); assumption. }
      inversion Hid. reflexivity.
    + assert (Neg p' = Neg p) as Hid.
      { apply subst_rel_notin_identity with (i := i) (r := r); assumption. }
      inversion Hid. reflexivity.
    + assert (Imp p' q' = Imp p q) as Hid.
      { apply subst_rel_notin_identity with (i := i) (r := r); assumption. }
      inversion Hid. reflexivity.
    + reflexivity.
    + reflexivity.
    + assert (All j p' = All j p) as Hid.
      { apply subst_rel_notin_identity with (i := i) (r := r); assumption. }
      inversion Hid. reflexivity.
    + exfalso. apply H.
      rewrite remove_nat_spec. split.
      * exact H3.
      * intro Heq. apply H2. exact Heq.
Qed.

Theorem transparent_term_substitution_law_holds :
  transparent_term_substitution_law.
Proof.
  unfold transparent_term_substitution_law.
  intros U M rho i x r x' Hreg Hsubst.
  apply (transparent_term_substitution_size (term_size x)); [lia | exact Hreg | exact Hsubst].
Qed.

Lemma alpha_rename_preserves_reg_tm_direct_size :
  forall n i j k t t',
    term_size t <= n ->
    i <> k ->
    reg_tm_direct i t ->
    reg_tm_direct j t ->
    subst_rel t j (Var k) t' ->
    reg_tm_direct i t'.
Proof.
  induction n as [| n IH]; intros i j k t t' Hsize Hik Hregi Hregj Hsubst.
  - pose proof (term_size_positive t). lia.
  - inversion Hregi; subst; inversion Hregj; subst; inversion Hsubst; subst; simpl in *.
    + constructor.
    + constructor.
    + apply RTApp.
      * apply (IH i j k p p'); try lia; assumption.
      * apply (IH i j k q q'); try lia; assumption.
    + apply RTFun.
      match goal with
      | Hrel : Forall2 _ args args',
        Hregiargs : Forall (reg_tm_direct i) args,
        Hregjargs : Forall (reg_tm_direct j) args |- _ =>
          clear Hsubst;
          revert Hregiargs Hregjargs Hsize;
          induction Hrel as [| a b rest rest' Hsub Hrel IHHrel];
          intros Hregiargs Hregjargs Hsize;
          inversion Hregiargs; subst; inversion Hregjargs; subst; simpl in *
      end.
      * constructor.
      * constructor.
        -- apply (IH i j k a b); try assumption.
           pose proof (term_size_fun_arg_lt s (a :: rest) a
             (or_introl eq_refl)) as Hlt.
           simpl in Hlt. lia.
        -- apply IHHrel; try assumption.
           ++ apply RTFun. exact H7.
           ++ apply RTFun. exact H4.
           ++ apply (term_size_fun_tail_le s a rest n) in Hsize.
              simpl in Hsize |- *.
              eapply Nat.le_trans.
              ** exact Hsize.
              ** lia.
    + constructor.
    + constructor. exact H.
    + assert (Eq p' q' = Eq p q) as Hid.
      { apply subst_rel_notin_identity with (i := j) (r := Var k); assumption. }
      inversion Hid; subst. apply RTEq. exact H.
    + assert (Neg p' = Neg p) as Hid.
      { apply subst_rel_notin_identity with (i := j) (r := Var k); assumption. }
      inversion Hid; subst. apply RTNeg. exact H.
    + assert (Imp p' q' = Imp p q) as Hid.
      { apply subst_rel_notin_identity with (i := j) (r := Var k); assumption. }
      inversion Hid; subst. apply RTImp. exact H.
    + apply RTAll. exact H.
    + apply RTAll. exact H.
    + assert (All j0 p' = All j0 p) as Hid.
      { apply subst_rel_notin_identity with (i := j) (r := Var k); assumption. }
      inversion Hid; subst. apply RTAll. exact H.
    + exfalso.
      match goal with
      | Hfresh : ~ In j (remove_nat ?binder (fv ?body)),
        Hin : In j (fv ?body),
        Hneq : j <> ?binder |- _ =>
          apply Hfresh; rewrite remove_nat_spec; split;
          [exact Hin | intro Heq; apply Hneq; exact Heq]
      end.
Qed.

Lemma alpha_rename_preserves_reg_tm_direct :
  forall i j k t t',
    i <> k ->
    reg_tm_direct i t ->
    reg_tm_direct j t ->
    subst_rel t j (Var k) t' ->
    reg_tm_direct i t'.
Proof.
  intros i j k t t' Hik Hregi Hregj Hsubst.
  apply (alpha_rename_preserves_reg_tm_direct_size (term_size t) i j k t t');
    [lia | exact Hik | exact Hregi | exact Hregj | exact Hsubst].
Qed.

Lemma reg_tm_direct_from_fresh_size :
  forall n i t,
    term_size t <= n ->
    ~ In i (fv t) ->
    reg_tm_direct i t.
Proof.
  induction n as [| n IH]; intros i t Hsize Hfresh.
  - pose proof (term_size_positive t). lia.
  - destruct t; simpl in *.
    + constructor.
    + apply RTApp.
      * apply (IH i t1); try lia.
        intro Hin. apply Hfresh. rewrite union_nat_spec. left. exact Hin.
      * apply (IH i t2); try lia.
        intro Hin. apply Hfresh. rewrite union_nat_spec. right. exact Hin.
    + apply RTFun.
      induction l as [| a rest IHargs]; simpl in *.
      * constructor.
      * constructor.
        -- apply (IH i a).
           ++ pose proof (term_size_fun_arg_lt n0 (a :: rest) a
                (or_introl eq_refl)) as Hlt.
              simpl in Hlt. lia.
           ++ intro Hin. apply Hfresh.
              rewrite union_nat_spec. left. exact Hin.
        -- apply IHargs.
           ++ pose proof (term_size_fun_tail_le n0 a rest n Hsize) as Htail.
              simpl in Htail |- *. lia.
           ++ intro Hin. apply Hfresh.
              rewrite union_nat_spec. right. exact Hin.
    + constructor.
    + apply RTBot. exact Hfresh.
    + apply RTEq. exact Hfresh.
    + apply RTNeg. exact Hfresh.
    + apply RTImp. exact Hfresh.
    + apply RTAll. exact Hfresh.
Qed.

Lemma reg_tm_direct_from_fresh :
  forall i t,
    ~ In i (fv t) ->
    reg_tm_direct i t.
Proof.
  intros i t Hfresh.
  apply (reg_tm_direct_from_fresh_size (term_size t)); [lia | exact Hfresh].
Qed.

Lemma subst_var_size_preserve_size :
  forall n t j k t',
    term_size t <= n ->
    subst_rel t j (Var k) t' ->
    term_size t' = term_size t.
Proof.
  induction n as [| n IH]; intros t j k t' Hsize Hsubst.
  - pose proof (term_size_positive t). lia.
  - inversion Hsubst; subst; simpl in *.
    + reflexivity.
    + reflexivity.
    + assert (Hp_size : term_size p' = term_size p)
        by (eapply IH; [lia | eassumption]).
      assert (Hq_size : term_size q' = term_size q)
        by (eapply IH; [lia | eassumption]).
      rewrite Hp_size. rewrite Hq_size.
      reflexivity.
    + match goal with
      | Hrel : Forall2 _ args args' |- _ =>
          revert Hsize;
          induction Hrel as [| a b rest rest' Hsub Hrel IHrel];
          intros Hsize; simpl
      end.
      * reflexivity.
      * rewrite (IH a j k b).
        -- assert (Htail_size : term_size (Fun s rest) <= S n).
           { simpl in Hsize |- *.
             pose proof (term_size_positive a). lia. }
           pose proof (IHrel (SRFun s rest rest' j (Var k) H) Htail_size)
             as Htail_eq.
           simpl in Htail_eq. lia.
        -- simpl in Hsize. lia.
        -- exact Hsub.
    + reflexivity.
    + reflexivity.
    + assert (Hp_size : term_size p' = term_size p)
        by (eapply IH; [lia | eassumption]).
      assert (Hq_size : term_size q' = term_size q)
        by (eapply IH; [lia | eassumption]).
      rewrite Hp_size. rewrite Hq_size.
      reflexivity.
    + assert (Hp_size : term_size p' = term_size p)
        by (eapply IH; [lia | eassumption]).
      rewrite Hp_size.
      reflexivity.
    + assert (Hp_size : term_size p' = term_size p)
        by (eapply IH; [lia | eassumption]).
      assert (Hq_size : term_size q' = term_size q)
        by (eapply IH; [lia | eassumption]).
      rewrite Hp_size. rewrite Hq_size.
      reflexivity.
    + reflexivity.
    + reflexivity.
    + assert (Hp_size : term_size p' = term_size p)
        by (eapply IH; [lia | eassumption]).
      rewrite Hp_size.
      reflexivity.
    + assert (Hrenamed_size : term_size renamed = term_size p).
      { eapply IH; try eassumption. lia. }
      assert (Hp'_size : term_size p' = term_size renamed).
      { eapply IH; try eassumption. lia. }
      lia.
Qed.

Lemma subst_var_size_preserve :
  forall t j k t',
    subst_rel t j (Var k) t' ->
    term_size t' = term_size t.
Proof.
  intros t j k t' Hsubst.
  apply (subst_var_size_preserve_size (term_size t) t j k t');
    [lia | exact Hsubst].
Qed.

Lemma subst_var_removes_target_size :
  forall n t j k t',
    term_size t <= n ->
    j <> k ->
    subst_rel t j (Var k) t' ->
    ~ In j (fv t').
Proof.
  induction n as [| n IH]; intros t j k t' Hsize Hjk Hsubst.
  - pose proof (term_size_positive t). lia.
  - inversion Hsubst; subst; simpl in *.
    + intro Hin. destruct Hin as [H | []]. symmetry in H. exact (Hjk H).
    + intro Hin. destruct Hin as [Heq | []]. subst. contradiction.
    + intro Hin. rewrite union_nat_spec in Hin.
      destruct Hin as [Hin | Hin].
      * eapply (IH p j k p'); [lia | exact Hjk | eassumption | exact Hin].
      * eapply (IH q j k q'); [lia | exact Hjk | eassumption | exact Hin].
    + clear Hsubst.
      revert args' H Hsize.
      induction args as [| a rest IHargs];
        intros args' Hargs Hsize; inversion Hargs; subst; simpl in *.
      * intro Hin. contradiction.
      * intro Hin. rewrite union_nat_spec in Hin.
        destruct Hin as [Hfv | Htail].
        -- 
           eapply (IH a j k y).
           ++ pose proof (term_size_fun_arg_lt s (a :: rest) a
                (or_introl eq_refl)) as Hlt.
              simpl in Hlt. lia.
           ++ exact Hjk.
           ++ eassumption.
           ++ exact Hfv.
        -- match goal with
           | Htailrel : Forall2 _ rest ?rest' |- _ =>
               apply (IHargs rest' Htailrel)
           end.
           ++ apply (term_size_fun_tail_le s a rest n) in Hsize.
              simpl in Hsize |- *. lia.
           ++ exact Htail.
    + intro Hin. contradiction.
    + intro Hin. contradiction.
    + intro Hin. rewrite union_nat_spec in Hin.
      destruct Hin as [Hin | Hin].
      * eapply (IH p j k p'); [lia | exact Hjk | eassumption | exact Hin].
      * eapply (IH q j k q'); [lia | exact Hjk | eassumption | exact Hin].
    + intro Hin.
      eapply (IH p j k p'); [lia | exact Hjk | eassumption | exact Hin].
    + intro Hin. rewrite union_nat_spec in Hin.
      destruct Hin as [Hin | Hin].
      * eapply (IH p j k p'); [lia | exact Hjk | eassumption | exact Hin].
      * eapply (IH q j k q'); [lia | exact Hjk | eassumption | exact Hin].
    + intro Hin. rewrite remove_nat_spec in Hin.
      destruct Hin as [_ Hne]. exact (Hne eq_refl).
    + intro Hin. rewrite remove_nat_spec in Hin.
      destruct Hin as [Hin Hne].
      exact (H0 Hin).
    + intro Hin. rewrite remove_nat_spec in Hin.
      destruct Hin as [Hin Hne].
      eapply (IH p j k p'); [lia | exact Hjk | eassumption | exact Hin].
    + intro Hin. rewrite remove_nat_spec in Hin.
      destruct Hin as [Hin Hne].
      assert (Hren_size : term_size renamed <= n).
      { match goal with
        | Hren : subst_rel p ?jj (Var ?kk) renamed |- _ =>
            pose proof (subst_var_size_preserve p jj kk renamed Hren) as Hsz
        end.
        simpl in Hsize. lia. }
      eapply (IH renamed j k p'); [exact Hren_size | exact Hjk | eassumption | exact Hin].
Qed.

Lemma subst_var_removes_target :
  forall t j k t',
    j <> k ->
    subst_rel t j (Var k) t' ->
    ~ In j (fv t').
Proof.
  intros t j k t' Hjk Hsubst.
  apply (subst_var_removes_target_size (term_size t) t j k t');
    [lia | exact Hjk | exact Hsubst].
Qed.

Lemma reg_fm_fresh_from_two_size :
  forall n a b x phi,
    term_size phi <= n ->
    a <> b ->
    a <> x ->
    b <> x ->
    ~ In x (fv phi) ->
    reg_fm a phi ->
    reg_fm b phi ->
    reg_fm x phi.
Proof.
  induction n as [| n IH]; intros a b x phi Hsize Hab Hax Hbx Hfresh Hrega Hregb.
  - pose proof (term_size_positive phi). lia.
  - destruct phi; simpl in *; try contradiction.
    + exact I.
    + destruct (not_in_union_nat x (fv phi1) (fv phi2) Hfresh)
        as [Hfresh1 Hfresh2].
      split; apply reg_tm_direct_from_fresh; assumption.
    + apply (IH a b x phi); try lia; assumption.
    + destruct Hrega as [Hrega1 Hrega2].
      destruct Hregb as [Hregb1 Hregb2].
      destruct (not_in_union_nat x (fv phi1) (fv phi2) Hfresh)
        as [Hfresh1 Hfresh2].
      split.
      * apply (IH a b x phi1); try lia; assumption.
      * apply (IH a b x phi2); try lia; assumption.
    + destruct (Nat.eq_dec n0 x) as [Hnx | Hnx].
      * left. exact Hnx.
      * right.
        assert (Hfresh_body : ~ In x (fv phi)).
        { intro Hin. apply Hfresh.
          rewrite remove_nat_spec. split; [exact Hin | intro Heq; apply Hnx; symmetry; exact Heq]. }
        split; [exact Hnx |].
        destruct (Nat.eq_dec n0 a) as [Hna | Hna].
        -- subst n0.
           destruct Hregb as [Hbad | [Hbna [Hregb_body Hrega_body]]].
           ++ exfalso. apply Hab. exact Hbad.
           ++ split.
              ** apply (IH b a x phi).
                 --- lia.
                 --- intro Heq. apply Hab. symmetry. exact Heq.
                 --- exact Hbx.
                 --- exact Hax.
                 --- exact Hfresh_body.
                 --- exact Hregb_body.
                 --- exact Hrega_body.
              ** exact Hrega_body.
        -- destruct (Nat.eq_dec n0 b) as [Hnb | Hnb].
           ++ subst n0.
              destruct Hrega as [Hbad | [Hanb [Hrega_body Hregb_body]]].
              ** exfalso. apply Hab. symmetry. exact Hbad.
              ** split.
                 --- apply (IH a b x phi); try lia; assumption.
                 --- exact Hregb_body.
           ++ destruct Hrega as [Hbad_a | [Hna_a [Hrega_body Hregn_body]]].
              ** exfalso. apply Hna. exact Hbad_a.
              ** destruct Hregb as [Hbad_b | [Hnb_b [Hregb_body _]]].
                 --- exfalso. apply Hnb. exact Hbad_b.
                 --- split.
                    +++ apply (IH a b x phi); try lia; assumption.
                    +++ exact Hregn_body.
Qed.

Lemma reg_fm_fresh_from_two :
  forall a b x phi,
    a <> b ->
    a <> x ->
    b <> x ->
    ~ In x (fv phi) ->
    reg_fm a phi ->
    reg_fm b phi ->
    reg_fm x phi.
Proof.
  intros a b x phi Hab Hax Hbx Hfresh Hrega Hregb.
  apply (reg_fm_fresh_from_two_size (term_size phi) a b x phi);
    [lia | exact Hab | exact Hax | exact Hbx | exact Hfresh | exact Hrega | exact Hregb].
Qed.

Lemma subst_var_creates_reg_tm_direct_size :
  forall n target freshv t t',
    term_size t <= n ->
    target <> freshv ->
    ~ In freshv (fv t) ->
    reg_tm_direct target t ->
    subst_rel t target (Var freshv) t' ->
    reg_tm_direct freshv t'.
Proof.
  induction n as [| n IH]; intros target freshv t t' Hsize Htf Hfresh Hreg Hsubst.
  - pose proof (term_size_positive t). lia.
  - inversion Hsubst; subst; simpl in *.
    + constructor.
    + constructor.
    + inversion Hreg; subst.
      destruct (not_in_union_nat freshv (fv p) (fv q) Hfresh)
        as [Hfreshp Hfreshq].
      apply RTApp.
      * eapply (IH target freshv p p'); [lia | exact Htf | exact Hfreshp | eassumption | eassumption].
      * eapply (IH target freshv q q'); [lia | exact Htf | exact Hfreshq | eassumption | eassumption].
    + inversion Hreg; subst.
      apply RTFun.
      match goal with
      | Hrel : Forall2 _ args args',
        Hregs : Forall (reg_tm_direct target) args |- _ =>
          clear Hsubst Hreg;
          revert args' Hrel Hregs Hfresh Hsize;
          induction args as [| a rest IHargs];
          intros args' Hrel Hregs Hfresh Hsize;
          inversion Hrel; subst; inversion Hregs; subst; simpl in *
      end.
      * constructor.
      * constructor.
        -- match goal with
           | Hsub : subst_rel a target (Var freshv) ?b |- _ =>
               eapply (IH target freshv a b)
           end.
           ++ simpl in Hsize. lia.
           ++ exact Htf.
           ++ intro Hin. apply Hfresh. rewrite union_nat_spec. left. exact Hin.
           ++ eassumption.
           ++ eassumption.
        -- apply IHargs.
           ++ eassumption.
           ++ eassumption.
           ++ intro Hin. apply Hfresh. rewrite union_nat_spec. right. exact Hin.
           ++ assert (Htail_size : term_size (Fun s rest) <= S n).
              { simpl in Hsize |- *.
                pose proof (term_size_positive a). lia. }
              exact Htail_size.
    + constructor.
    + apply RTBot. exact Hfresh.
    + inversion Hreg; subst.
      assert (Eq p' q' = Eq p q) as Hid.
      { apply subst_rel_notin_identity with (i := target) (r := Var freshv); assumption. }
      inversion Hid; subst.
      apply reg_tm_direct_from_fresh. exact Hfresh.
    + inversion Hreg; subst.
      assert (Neg p' = Neg p) as Hid.
      { apply subst_rel_notin_identity with (i := target) (r := Var freshv); assumption. }
      inversion Hid; subst.
      apply reg_tm_direct_from_fresh. exact Hfresh.
    + inversion Hreg; subst.
      assert (Imp p' q' = Imp p q) as Hid.
      { apply subst_rel_notin_identity with (i := target) (r := Var freshv); assumption. }
      inversion Hid; subst.
      apply reg_tm_direct_from_fresh. exact Hfresh.
    + apply reg_tm_direct_from_fresh. exact Hfresh.
    + apply reg_tm_direct_from_fresh. exact Hfresh.
    + inversion Hreg; subst.
      assert (All j p' = All j p) as Hid.
      { apply subst_rel_notin_identity with (i := target) (r := Var freshv); assumption. }
      inversion Hid; subst.
      apply reg_tm_direct_from_fresh. exact Hfresh.
    + inversion Hreg; subst.
      exfalso.
      match goal with
      | Hnot : ~ In ?x (fv (All ?binder ?body)),
        Hin : In ?x (fv ?body),
        Hneq : ?x <> ?binder |- _ =>
          apply Hnot; simpl; rewrite remove_nat_spec; split;
          [exact Hin | exact Hneq]
      | Hnot : ~ In ?x (fv (All ?binder ?body)),
        Hin : In ?x (fv ?body),
        Hneq : ?binder <> ?x |- _ =>
          apply Hnot; simpl; rewrite remove_nat_spec; split;
          [exact Hin | intro Heq; apply Hneq; symmetry; exact Heq]
      | Hnot : ~ In ?x (remove_nat ?binder (fv ?body)),
        Hin : In ?x (fv ?body),
        Hneq : ?x <> ?binder |- _ =>
          apply Hnot; rewrite remove_nat_spec; split;
          [exact Hin | exact Hneq]
      | Hnot : ~ In ?x (remove_nat ?binder (fv ?body)),
        Hin : In ?x (fv ?body),
        Hneq : ?binder <> ?x |- _ =>
          apply Hnot; rewrite remove_nat_spec; split;
          [exact Hin | intro Heq; apply Hneq; symmetry; exact Heq]
      end.
Qed.

Lemma subst_var_creates_reg_tm_direct :
  forall target freshv t t',
    target <> freshv ->
    ~ In freshv (fv t) ->
    reg_tm_direct target t ->
    subst_rel t target (Var freshv) t' ->
    reg_tm_direct freshv t'.
Proof.
  intros target freshv t t' Htf Hfresh Hreg Hsubst.
  apply (subst_var_creates_reg_tm_direct_size (term_size t) target freshv t t');
    [lia | exact Htf | exact Hfresh | exact Hreg | exact Hsubst].
Qed.

Lemma alpha_rename_preserves_and_creates_reg_fm_size :
  forall n guard target freshv phi phi',
    term_size phi <= n ->
    guard <> target ->
    guard <> freshv ->
    target <> freshv ->
    ~ In freshv (fv phi) ->
    reg_fm guard phi ->
    reg_fm target phi ->
    subst_rel phi target (Var freshv) phi' ->
    reg_fm guard phi' /\ reg_fm freshv phi'.
Proof.
  induction n as [| n IH]; intros guard target freshv phi phi'
    Hsize Hgt Hgf Htf Hfresh Hregg Hregt Hsubst.
  - pose proof (term_size_positive phi). lia.
  - inversion Hsubst; subst; simpl in *; try contradiction.
    + split; exact I.
    + destruct Hregg as [Hreggp Hreggq].
      destruct Hregt as [Hregtp Hregtq].
      destruct (not_in_union_nat freshv (fv p) (fv q) Hfresh)
        as [Hfreshp Hfreshq].
      split.
      * split.
        -- eapply (alpha_rename_preserves_reg_tm_direct guard target freshv p p');
             eassumption.
        -- eapply (alpha_rename_preserves_reg_tm_direct guard target freshv q q');
             eassumption.
      * split.
        -- eapply (subst_var_creates_reg_tm_direct target freshv p p');
             eassumption.
        -- eapply (subst_var_creates_reg_tm_direct target freshv q q');
             eassumption.
    + destruct (IH guard target freshv p p') as [Hpres Hcreate];
        try lia; try assumption.
      split; assumption.
    + destruct Hregg as [Hreggp Hreggq].
      destruct Hregt as [Hregtp Hregtq].
      destruct (not_in_union_nat freshv (fv p) (fv q) Hfresh)
        as [Hfreshp Hfreshq].
      destruct (IH guard target freshv p p') as [Hpresp Hcreatep];
        try lia; try assumption.
      destruct (IH guard target freshv q q') as [Hpresq Hcreateq];
        try lia; try assumption.
      split; split; assumption.
    + split.
      * exact Hregg.
      * destruct Hregg as [Hbad | [Htarget_not_guard [Hregg_body Hregtarget_body]]].
        -- exfalso. apply Hgt. symmetry. exact Hbad.
        -- assert (Hfresh_body : ~ In freshv (fv p)).
           { intro Hin. apply Hfresh.
             rewrite remove_nat_spec. split;
             [exact Hin | intro Heq; apply Htf; symmetry; exact Heq]. }
           right. split; [exact Htf |].
           split.
           ++ eapply reg_fm_fresh_from_two.
              ** exact Hgt.
              ** exact Hgf.
              ** exact Htf.
              ** exact Hfresh_body.
              ** exact Hregg_body.
              ** exact Hregtarget_body.
           ++ exact Hregtarget_body.
    + split.
      * exact Hregg.
      * destruct (Nat.eq_dec j freshv) as [Hjf | Hjf].
        -- left. exact Hjf.
        -- right. split; [exact Hjf |].
           assert (Hfresh_body : ~ In freshv (fv p)).
           { intro Hin. apply Hfresh.
             rewrite remove_nat_spec. split;
             [exact Hin | intro Heq; apply Hjf; symmetry; exact Heq]. }
           destruct Hregt as [Hbad | [_ [Hregtarget_body Hregj_body]]].
           ++ exfalso. apply H. symmetry. exact Hbad.
           ++ split.
              ** eapply reg_fm_fresh_from_two.
                 --- exact H.
                 --- exact Htf.
                 --- exact Hjf.
                 --- exact Hfresh_body.
                 --- exact Hregtarget_body.
                 --- exact Hregj_body.
              ** exact Hregj_body.
    + destruct Hregg as [Hbind_guard | [Hbind_not_guard [Hregg_body Hregbind_body_g]]].
      * subst j.
        split.
        -- left. reflexivity.
        -- assert (Hfresh_body : ~ In freshv (fv p)).
           { intro Hin. apply Hfresh.
             rewrite remove_nat_spec. split;
             [exact Hin | intro Heq; apply Hgf; symmetry; exact Heq]. }
           assert (Hregt_body : reg_fm target p).
           { destruct Hregt as [Hbad | [_ [Hregt_body _]]].
             - exfalso. apply Hgt. exact Hbad.
             - exact Hregt_body. }
           assert (Hregguard_source : reg_fm guard p).
           { destruct Hregt as [Hbad | [_ [_ Hregguard_source]]].
             - exfalso. apply Hgt. exact Hbad.
             - exact Hregguard_source. }
           assert (Hregfresh_body : reg_fm freshv p').
           { destruct (IH guard target freshv p p') as [_ Hcreate].
             - lia.
             - exact Hgt.
             - exact Hgf.
             - exact Htf.
             - exact Hfresh_body.
             - exact Hregguard_source.
             - exact Hregt_body.
             - assumption.
             - exact Hcreate. }
           assert (Hregguard_body : reg_fm guard p').
           { destruct (IH guard target freshv p p') as [Hpres _].
             - lia.
             - exact Hgt.
             - exact Hgf.
             - exact Htf.
             - exact Hfresh_body.
             - exact Hregguard_source.
             - exact Hregt_body.
             - assumption.
             - exact Hpres. }
           right. split; [exact Hgf |].
           split; assumption.
      * destruct (Nat.eq_dec j freshv) as [Hj_eq_freshv | Hj_ne_freshv].
        { exfalso. apply H1. simpl. left. symmetry. exact Hj_eq_freshv. }
        try (exfalso; apply Hj_ne_freshv; reflexivity).
        assert (Hfresh_body : ~ In freshv (fv p)).
        { intro Hin. apply Hfresh.
          rewrite remove_nat_spec. split.
          - exact Hin.
          - intro Heq. apply Hj_ne_freshv. symmetry. exact Heq. }
        assert (Hregt_body : reg_fm target p).
        { destruct Hregt as [Hbad | [_ [Hregt_body _]]].
          - exfalso. apply H. symmetry. exact Hbad.
          - exact Hregt_body. }
        assert (Hreg_guard_p' : reg_fm guard p').
        { destruct (IH guard target freshv p p') as [Hpres _];
            try lia; try assumption. }
        assert (Hreg_fresh_p' : reg_fm freshv p').
        { destruct (IH guard target freshv p p') as [_ Hcreate];
            try lia; try assumption. }
        assert (Hreg_bind_p' : reg_fm j p').
        { destruct (IH j target freshv p p') as [Hpres _].
          - lia.
          - intro Heq. apply H. symmetry. exact Heq.
          - exact Hj_ne_freshv.
          - exact Htf.
          - exact Hfresh_body.
          - exact Hregbind_body_g.
          - exact Hregt_body.
          - assumption.
          - exact Hpres. }
        split.
        -- right. split; [exact Hbind_not_guard |].
           split; assumption.
        -- right. split.
           ++ exact Hj_ne_freshv.
           ++ split; assumption.
    + destruct Hregg as [Hbind_guard | [Hbind_not_guard [Hregg_body Hregbind_body_g]]].
      * subst j.
        exfalso. simpl in H1.
        destruct H1 as [Heq | []].
        apply Hgf. symmetry. exact Heq.
      * assert (Hj_freshv : j = freshv).
        { simpl in H1. destruct H1 as [H1 | []]. symmetry. exact H1. }
        subst j.
        set (k0 := fresh (union_nat (fv p) (union_nat (fv (Var freshv)) [target; freshv]))).
        assert (Hfresh_new_not_p : ~ In k0 (fv p)).
        { subst k0. intro Hin. apply fresh_not_in with
            (xs := union_nat (fv p) (union_nat (fv (Var freshv)) [target; freshv])).
          rewrite union_nat_spec. left. exact Hin. }
        assert (Hnew_ne_target : k0 <> target).
        { subst k0. intro Heq. apply fresh_not_in with
            (xs := union_nat (fv p) (union_nat (fv (Var freshv)) [target; freshv])).
          rewrite union_nat_spec. right. rewrite union_nat_spec. right.
          left. symmetry. exact Heq. }
        assert (Hnew_ne_freshv : k0 <> freshv).
        { subst k0. intro Heq. apply fresh_not_in with
            (xs := union_nat (fv p) (union_nat (fv (Var freshv)) [target; freshv])).
          rewrite union_nat_spec. right. rewrite union_nat_spec. left.
          simpl. left. symmetry. exact Heq. }
        assert (Hregtarget_body : reg_fm target p).
        { destruct Hregt as [Hbad | [_ [Ht _]]].
          - exfalso. apply H. symmetry. exact Hbad.
          - exact Ht. }
        assert (Hreg_guard_renamed : k0 = guard \/ reg_fm guard renamed).
        { destruct (Nat.eq_dec k0 guard) as [Heq | Hne].
          - left. exact Heq.
          - right.
            destruct (IH guard freshv k0 p renamed) as [Hpres _].
            + lia.
            + exact Hgf.
            + intro Heq. apply Hne. symmetry. exact Heq.
            + intro Heq. apply Hnew_ne_freshv. symmetry. exact Heq.
            + exact Hfresh_new_not_p.
            + exact Hregg_body.
            + exact Hregbind_body_g.
            + subst k0. assumption.
            + exact Hpres. }
        assert (Hreg_target_renamed : reg_fm target renamed).
        { destruct (IH target freshv k0 p renamed) as [Hpres _].
          - lia.
          - exact Htf.
          - intro Heq. apply Hnew_ne_target. symmetry. exact Heq.
          - intro Heq. apply Hnew_ne_freshv. symmetry. exact Heq.
          - exact Hfresh_new_not_p.
          - exact Hregtarget_body.
          - exact Hregbind_body_g.
          - subst k0. assumption.
          - exact Hpres. }
        assert (Hreg_new_renamed : reg_fm k0 renamed).
        { destruct (IH target freshv k0 p renamed) as [_ Hcreate].
          - lia.
          - exact Htf.
          - intro Heq. apply Hnew_ne_target. symmetry. exact Heq.
          - intro Heq. apply Hnew_ne_freshv. symmetry. exact Heq.
          - exact Hfresh_new_not_p.
          - exact Hregtarget_body.
          - exact Hregbind_body_g.
          - subst k0. assumption.
          - exact Hcreate. }
        assert (Hfreshv_not_renamed : ~ In freshv (fv renamed)).
        { subst k0. eapply subst_var_removes_target.
          - intro Heq. apply Hnew_ne_freshv. symmetry. exact Heq.
          - eassumption. }
        assert (Hrenamed_size : term_size renamed <= n).
        { subst k0. pose proof (subst_var_size_preserve
            p freshv (fresh (union_nat (fv p) (union_nat (fv (Var freshv)) [target; freshv])))
            renamed H3) as Hsz.
          simpl in Hsize. lia. }
        assert (Hreg_new_p' : reg_fm k0 p' /\ reg_fm freshv p').
        { destruct (IH k0 target freshv renamed p') as [Hpres Hcreate].
          - exact Hrenamed_size.
          - exact Hnew_ne_target.
          - exact Hnew_ne_freshv.
          - exact Htf.
          - exact Hfreshv_not_renamed.
          - exact Hreg_new_renamed.
          - exact Hreg_target_renamed.
          - assumption.
          - split; assumption. }
        assert (Hreg_guard_p' : k0 = guard \/ reg_fm guard p').
        { destruct Hreg_guard_renamed as [Heq | Hgr].
          - left. exact Heq.
          - right.
            destruct (IH guard target freshv renamed p') as [Hpres _].
            + exact Hrenamed_size.
            + exact Hgt.
            + exact Hgf.
            + exact Htf.
            + exact Hfreshv_not_renamed.
            + exact Hgr.
            + exact Hreg_target_renamed.
            + assumption.
            + exact Hpres. }
        destruct Hreg_new_p' as [Hregk_p' Hregfresh_p'].
        split.
        -- destruct (Nat.eq_dec k0 guard) as [Heqkg | Hnekg].
           ++ left.
              transitivity k0.
              ** unfold k0. simpl.
                 destruct (Nat.eq_dec target freshv) as [Heqtf | Hneqtf].
                 --- exfalso. apply Htf. exact Heqtf.
                 --- destruct (Nat.eq_dec freshv freshv) as [_ | Hff].
                     +++ reflexivity.
                     +++ exfalso. apply Hff. reflexivity.
              ** exact Heqkg.
           ++ right. split.
             ** intro Heqexpr. apply Hnekg.
                 subst k0.
                 simpl in Heqexpr |- *.
                 destruct (Nat.eq_dec target freshv) as [Heqtf | Hneqtf].
                 --- exfalso. apply Htf. exact Heqtf.
                 --- destruct (Nat.eq_dec freshv freshv) as [_ | Hff].
                     +++ exact Heqexpr.
                     +++ exfalso. apply Hff. reflexivity.
              ** split.
                 --- destruct Hreg_guard_p' as [Heq | Hregguard_p'].
                     +++ exfalso. apply Hnekg. exact Heq.
                     +++ exact Hregguard_p'.
                 --- exact Hregk_p'.
        -- right. split.
           ++ exact Hnew_ne_freshv.
           ++ split; assumption.
Qed.

Lemma alpha_rename_preserves_and_creates_reg_fm :
  forall guard target freshv phi phi',
    guard <> target ->
    guard <> freshv ->
    target <> freshv ->
    ~ In freshv (fv phi) ->
    reg_fm guard phi ->
    reg_fm target phi ->
    subst_rel phi target (Var freshv) phi' ->
    reg_fm guard phi' /\ reg_fm freshv phi'.
Proof.
  intros guard target freshv phi phi' Hgt Hgf Htf Hfresh Hregg Hregt Hsubst.
  apply (alpha_rename_preserves_and_creates_reg_fm_size
    (term_size phi) guard target freshv phi phi');
    [lia | exact Hgt | exact Hgf | exact Htf | exact Hfresh
    | exact Hregg | exact Hregt | exact Hsubst].
Qed.

Definition formula_freshness_law : Prop :=
  forall U (M : model U) rho i b phi,
    formula phi ->
    ~ In i (fv phi) ->
    (holds M (update rho i b) phi <-> holds M rho phi).

Definition transparent_formula_substitution_law : Prop :=
  forall U (M : model U) rho i phi r phi',
    reg_fm i phi ->
    subst_rel phi i r phi' ->
    (holds M rho phi' <->
     holds M (update rho i (val M rho r)) phi).

Theorem formula_freshness_law_holds :
  formula_freshness_law.
Proof.
  unfold formula_freshness_law.
  intros U0 M rho i b phi Hform Hfresh.
  revert U0 M rho i b Hform Hfresh.
  induction phi; intros U0 M rho i b Hform Hfresh; simpl in *.
  - contradiction.
  - contradiction.
  - contradiction.
  - contradiction.
  - tauto.
  - destruct (not_in_union_nat i (fv phi1) (fv phi2) Hfresh)
      as [Hfresh1 Hfresh2].
    split; intro H.
    + rewrite (term_freshness_val U0 M rho i b phi1 Hfresh1) in H.
      rewrite (term_freshness_val U0 M rho i b phi2 Hfresh2) in H.
      exact H.
    + rewrite (term_freshness_val U0 M rho i b phi1 Hfresh1).
      rewrite (term_freshness_val U0 M rho i b phi2 Hfresh2).
      exact H.
  - destruct (IHphi U0 M rho i b Hform Hfresh) as [Hto Hfrom].
    split; intros Hneg Hsat.
    + apply Hneg. apply Hfrom. exact Hsat.
    + apply Hneg. apply Hto. exact Hsat.
  - destruct Hform as [Hf1 Hf2].
    destruct (not_in_union_nat i (fv phi1) (fv phi2) Hfresh)
      as [Hfresh1 Hfresh2].
    destruct (IHphi1 U0 M rho i b Hf1 Hfresh1) as [H1to H1from].
    destruct (IHphi2 U0 M rho i b Hf2 Hfresh2) as [H2to H2from].
    split; intros Himp Hleft.
    + apply H2to.
      apply Himp.
      apply H1from.
      exact Hleft.
    + apply H2from.
      apply Himp.
      apply H1to.
      exact Hleft.
  - destruct (Nat.eq_dec n i) as [Heq | Hne].
    + subst n. split; intros Hall c.
      * replace (update rho i c) with (update (update rho i b) i c)
          by exact (update_same U0 rho i b c).
        exact (Hall c).
      * replace (update (update rho i b) i c) with (update rho i c)
          by exact (eq_sym (update_same U0 rho i b c)).
        exact (Hall c).
    + assert (Hfresh_body : ~ In i (fv phi)).
      { intro Hin. apply Hfresh.
        rewrite remove_nat_spec. split.
        - exact Hin.
        - intro Heq. apply Hne. symmetry. exact Heq. }
      split; intros Hall c.
      * pose proof (Hall c) as Hc.
        replace (update (update rho i b) n c)
          with (update (update rho n c) i b) in Hc
          by (apply update_comm; intro Heq; apply Hne; exact Heq).
        apply (proj1 (IHphi U0 M (update rho n c) i b Hform Hfresh_body)).
        exact Hc.
      * pose proof
          (proj2 (IHphi U0 M (update rho n c) i b Hform Hfresh_body)
             (Hall c)) as Hc.
        replace (update (update rho i b) n c)
          with (update (update rho n c) i b)
          by (apply update_comm; intro Heq; apply Hne; exact Heq).
        exact Hc.
Qed.

Theorem holds_freshness :
  forall U (M : model U) rho i b phi,
    ~ In i (fv phi) ->
    (holds M (update rho i b) phi <-> holds M rho phi).
Proof.
  intros U0 M rho i b phi Hfresh.
  revert U0 M rho i b Hfresh.
  induction phi; intros U0 M rho i b Hfresh; simpl in *.
  - split; intro H.
    + unfold update in H.
      destruct (Nat.eq_dec n i) as [Heq | Hne].
      * subst n. exfalso. apply Hfresh. left. reflexivity.
      * exact H.
    + unfold update.
      destruct (Nat.eq_dec n i) as [Heq | Hne].
      * subst n. exfalso. apply Hfresh. left. reflexivity.
      * exact H.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct (not_in_union_nat i (fv phi1) (fv phi2) Hfresh)
      as [Hfresh1 Hfresh2].
    split; intro H.
    + rewrite (term_freshness_val U0 M rho i b phi1 Hfresh1) in H.
      rewrite (term_freshness_val U0 M rho i b phi2 Hfresh2) in H.
      exact H.
    + rewrite (term_freshness_val U0 M rho i b phi1 Hfresh1).
      rewrite (term_freshness_val U0 M rho i b phi2 Hfresh2).
      exact H.
  - destruct (IHphi U0 M rho i b Hfresh) as [Hto Hfrom].
    split; intros Hneg Hsat.
    + apply Hneg. apply Hfrom. exact Hsat.
    + apply Hneg. apply Hto. exact Hsat.
  - destruct (not_in_union_nat i (fv phi1) (fv phi2) Hfresh)
      as [Hfresh1 Hfresh2].
    destruct (IHphi1 U0 M rho i b Hfresh1) as [H1to H1from].
    destruct (IHphi2 U0 M rho i b Hfresh2) as [H2to H2from].
    split; intros Himp Hleft.
    + apply H2to.
      apply Himp.
      apply H1from.
      exact Hleft.
    + apply H2from.
      apply Himp.
      apply H1to.
      exact Hleft.
  - destruct (Nat.eq_dec n i) as [Heq | Hne].
    + subst n. split; intros Hall c.
      * replace (update rho i c) with (update (update rho i b) i c)
          by exact (update_same U0 rho i b c).
        exact (Hall c).
      * replace (update (update rho i b) i c) with (update rho i c)
          by exact (eq_sym (update_same U0 rho i b c)).
        exact (Hall c).
    + assert (Hfresh_body : ~ In i (fv phi)).
      { intro Hin. apply Hfresh.
        rewrite remove_nat_spec. split.
        - exact Hin.
        - intro Heq. apply Hne. symmetry. exact Heq. }
      split; intros Hall c.
      * pose proof (Hall c) as Hc.
        replace (update (update rho i b) n c)
          with (update (update rho n c) i b) in Hc
          by (apply update_comm; intro Heq; apply Hne; exact Heq).
        apply (proj1 (IHphi U0 M (update rho n c) i b Hfresh_body)).
        exact Hc.
      * pose proof
          (proj2 (IHphi U0 M (update rho n c) i b Hfresh_body)
             (Hall c)) as Hc.
        replace (update (update rho i b) n c)
          with (update (update rho n c) i b)
          by (apply update_comm; intro Heq; apply Hne; exact Heq).
        exact Hc.
Qed.

Theorem transparent_formula_substitution_law_holds :
  transparent_formula_substitution_law.
Proof.
  unfold transparent_formula_substitution_law.
  intros U M rho i phi r phi' Hreg Hsubst.
  revert U M rho Hreg.
  induction Hsubst; intros U M rho Hreg; simpl in *; try contradiction.
  - tauto.
  - destruct Hreg as [Hregp Hregq].
    rewrite (transparent_term_substitution_law_holds U M rho i p r p' Hregp Hsubst1).
    rewrite (transparent_term_substitution_law_holds U M rho i q r q' Hregq Hsubst2).
    tauto.
  - destruct (IHHsubst U M rho Hreg) as [Hto Hfrom].
    split; intros Hneg Hsat.
    + apply Hneg. apply Hfrom. exact Hsat.
    + apply Hneg. apply Hto. exact Hsat.
  - destruct Hreg as [Hregp Hregq].
    destruct (IHHsubst1 U M rho Hregp) as [Hp_to Hp_from].
    destruct (IHHsubst2 U M rho Hregq) as [Hq_to Hq_from].
    split; intros Himp Hp.
    + apply Hq_to. apply Himp. apply Hp_from. exact Hp.
    + apply Hq_from. apply Himp. apply Hp_to. exact Hp.
  - split; intros Hall b.
    + replace (update (update rho i (val M rho r)) i b)
        with (update rho i b)
        by exact (eq_sym (update_same U rho i (val M rho r) b)).
      exact (Hall b).
    + replace (update rho i b)
        with (update (update rho i (val M rho r)) i b)
        by exact (update_same U rho i (val M rho r) b).
      exact (Hall b).
  - split; intros Hall b.
    + replace (update (update rho i (val M rho r)) j b)
        with (update (update rho j b) i (val M rho r))
        by (apply update_comm; intro Heq; apply H; symmetry; exact Heq).
      apply (proj2 (holds_freshness U M (update rho j b) i (val M rho r) p H0)).
      exact (Hall b).
    + pose proof (Hall b) as Hb.
      replace (update (update rho i (val M rho r)) j b)
        with (update (update rho j b) i (val M rho r)) in Hb
        by (apply update_comm; intro Heq; apply H; symmetry; exact Heq).
      apply (proj1 (holds_freshness U M (update rho j b) i (val M rho r) p H0)).
      exact Hb.
  - destruct Hreg as [Hsame | [Hij [Hreg_i_p Hreg_j_p]]].
    + subst j. exfalso. apply H. reflexivity.
    + split; intros Hall b.
      * destruct (IHHsubst U M (update rho j b) Hreg_i_p) as [Hto _].
        assert (Hr_fresh : val M (update rho j b) r = val M rho r)
          by (apply term_freshness_val; exact H1).
        replace (val M (update rho j b) r) with (val M rho r) in Hto
          by exact (eq_sym Hr_fresh).
        replace (update (update rho j b) i (val M rho r))
          with (update (update rho i (val M rho r)) j b) in Hto
          by (apply update_comm; exact H).
        apply Hto. exact (Hall b).
      * destruct (IHHsubst U M (update rho j b) Hreg_i_p) as [_ Hfrom].
        assert (Hr_fresh : val M (update rho j b) r = val M rho r)
          by (apply term_freshness_val; exact H1).
        replace (val M (update rho j b) r) with (val M rho r) in Hfrom
          by exact (eq_sym Hr_fresh).
        replace (update (update rho j b) i (val M rho r))
          with (update (update rho i (val M rho r)) j b) in Hfrom
          by (apply update_comm; exact H).
        apply Hfrom. exact (Hall b).
  - destruct Hreg as [Hsame | [Hij [Hreg_i_p Hreg_j_p]]].
    + subst j. exfalso. apply H. reflexivity.
    + assert (Hk_not_p : ~ In k (fv p)).
      { subst k. intro Hin. apply fresh_not_in with
          (xs := union_nat (fv p) (union_nat (fv r) [i; j])).
        rewrite union_nat_spec. left. exact Hin. }
      assert (Hk_not_r : ~ In k (fv r)).
      { subst k. intro Hin. apply fresh_not_in with
          (xs := union_nat (fv p) (union_nat (fv r) [i; j])).
        rewrite union_nat_spec. right. rewrite union_nat_spec. left. exact Hin. }
      assert (Hik : i <> k).
      { subst k. intro Heq. apply fresh_not_in with
          (xs := union_nat (fv p) (union_nat (fv r) [i; j])).
        rewrite union_nat_spec. right. rewrite union_nat_spec. right.
        left. exact Heq. }
      assert (Hjk : j <> k).
      { subst k. intro Heq. apply fresh_not_in with
          (xs := union_nat (fv p) (union_nat (fv r) [i; j])).
        rewrite union_nat_spec. right. rewrite union_nat_spec. right.
        right. left. exact Heq. }
      assert (Hreg_i_renamed : reg_fm i renamed).
      { destruct (alpha_rename_preserves_and_creates_reg_fm
          i j k p renamed H Hik Hjk Hk_not_p Hreg_i_p Hreg_j_p Hsubst1)
          as [Hpres _].
        exact Hpres. }
      assert (Hr_fresh : forall b, val M (update rho k b) r = val M rho r).
      { intro b. apply term_freshness_val. exact Hk_not_r. }
      split; intros Hall b.
      * pose proof (Hall b) as Hb.
        destruct (IHHsubst2 U M (update rho k b) Hreg_i_renamed) as [H2to _].
        specialize (H2to Hb).
        rewrite Hr_fresh in H2to.
        destruct (IHHsubst1 U M
          (update (update rho k b) i (val M rho r)) Hreg_j_p) as [H1to _].
        simpl in H1to.
        assert (Hvalk :
          update (update rho k b) i (val M rho r) k = b).
        { unfold update. destruct (Nat.eq_dec k i) as [Hki | _].
          - exfalso. apply Hik. symmetry. exact Hki.
          - destruct (Nat.eq_dec k k) as [_ | Hkk]; [reflexivity | contradiction]. }
        rewrite Hvalk in H1to.
        specialize (H1to H2to).
        replace (update (update (update rho k b) i (val M rho r)) j b)
          with (update (update (update rho i (val M rho r)) j b) k b) in H1to
          by exact (eq_sym (update_alpha_rename_env U rho i j k (val M rho r) b H Hik Hjk)).
        apply (proj1 (holds_freshness U M
          (update (update rho i (val M rho r)) j b) k b p Hk_not_p)).
        exact H1to.
      * assert (Hdesired :
          holds M (update (update (update rho i (val M rho r)) j b) k b) p).
        { apply (proj2 (holds_freshness U M
            (update (update rho i (val M rho r)) j b) k b p Hk_not_p)).
          exact (Hall b). }
        replace (update (update (update rho i (val M rho r)) j b) k b)
          with (update (update (update rho k b) i (val M rho r)) j b) in Hdesired
          by exact (update_alpha_rename_env U rho i j k (val M rho r) b H Hik Hjk).
        destruct (IHHsubst1 U M
          (update (update rho k b) i (val M rho r)) Hreg_j_p) as [_ H1from].
        simpl in H1from.
        assert (Hvalk :
          update (update rho k b) i (val M rho r) k = b).
        { unfold update. destruct (Nat.eq_dec k i) as [Hki | _].
          - exfalso. apply Hik. symmetry. exact Hki.
          - destruct (Nat.eq_dec k k) as [_ | Hkk]; [reflexivity | contradiction]. }
        rewrite Hvalk in H1from.
        specialize (H1from Hdesired).
        destruct (IHHsubst2 U M (update rho k b) Hreg_i_renamed) as [_ H2from].
        rewrite Hr_fresh in H2from.
        apply H2from. exact H1from.
Qed.

Definition retag_term (rho sigma : nat) (z : term) : term :=
  match z with
  | Fun tag args =>
      if Nat.eq_dec tag (S rho) then Fun (S sigma) args else z
  | _ => z
  end.

Definition term_universe : universe.
Proof.
  refine {|
    carrier := term;
    botD := Bot;
    bullet := App;
    syn := fun t => t;
    tup := fun args => Fun 90 args;
    tag := fun rho args => Fun (S rho) args;
    retag := retag_term;
    cur := fun _ d => d;
    uncur := fun _ d => d;
    cl := fun args => Fun 91 args
  |}.
  - intros p q H. exact H.
  - intros rho xs ys H. inversion H. reflexivity.
  - intros rho sigma xs ys Hneq H.
    inversion H. apply Hneq. now apply Nat.succ_inj.
  - intros rho sigma xs. unfold retag_term.
    destruct (Nat.eq_dec (S rho) (S rho)) as [_ | Hneq].
    + reflexivity.
    + exfalso. apply Hneq. reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Definition ce_i : nat := 0.
Definition ce_j : nat := 1.
Definition ce_r : term := Var ce_j.
Definition ce_inner : term := Eq (Var ce_j) (Var ce_j).
Definition ce_p : term := Eq ce_inner (Var ce_i).
Definition ce_k : nat :=
  fresh (union_nat (fv ce_p) (union_nat (fv ce_r) [ce_i; ce_j])).
Definition ce_renamed : term := Eq (Eq (Var ce_k) (Var ce_k)) (Var ce_i).
Definition ce_phi : term := All ce_j ce_p.
Definition ce_phi_sub : term := All ce_k (Eq (Eq (Var ce_k) (Var ce_k)) ce_r).

Lemma ce_k_is_two : ce_k = 2.
Proof. reflexivity. Qed.

Lemma ce_k_ne_zero : ce_k <> 0.
Proof. rewrite ce_k_is_two. discriminate. Qed.

Lemma ce_k_ne_one : ce_k <> 1.
Proof. rewrite ce_k_is_two. discriminate. Qed.

Lemma ce_body_rename_not_transparent :
  ~ reg_fm ce_j ce_p.
Proof.
  unfold ce_p, ce_inner, ce_j.
  simpl. intros [Htm _].
  inversion Htm; subst.
  match goal with
  | Hnot : ~ In 1 (fv (Eq (Var 1) (Var 1))) |- _ =>
      apply Hnot; simpl; left; reflexivity
  end.
Qed.

Lemma ce_reg_blocked :
  ~ reg_fm ce_i ce_phi.
Proof.
  unfold ce_phi, ce_p, ce_inner, ce_i, ce_j.
  simpl. intros [Hbad | [_ [_ Hrename]]].
  - discriminate Hbad.
  - exact (ce_body_rename_not_transparent Hrename).
Qed.

Lemma ce_subst_rel :
  subst_rel ce_phi ce_i ce_r ce_phi_sub.
Proof.
  unfold ce_phi, ce_phi_sub, ce_p, ce_renamed, ce_inner, ce_i, ce_j, ce_r.
  apply (SRAllRename 0 1 ce_k
           (Eq (Eq (Var 1) (Var 1)) (Var 0))
           (Eq (Eq (Var ce_k) (Var ce_k)) (Var 0))
           (Eq (Eq (Var ce_k) (Var ce_k)) (Var 1))
           (Var 1)).
  - discriminate.
  - simpl. right. left. reflexivity.
  - simpl. left. reflexivity.
  - reflexivity.
  - apply SREq.
    + apply SREq; apply SRVarSame.
    + apply SRVarOther. discriminate.
  - apply SREq.
    + apply SREq; apply SRVarOther; intro H; apply ce_k_ne_zero; symmetry; exact H.
    + apply SRVarSame.
Qed.

Definition ce_model : model term_universe.
Proof.
  constructor.
  - exact Bot.
  - intro s. exact Bot.
Defined.

Definition ce_td_inner : carrier term_universe :=
  @td term_universe ce_model ce_inner.

Definition ce_rho (n : nat) : carrier term_universe :=
  if Nat.eq_dec n ce_j then ce_td_inner else Bot.

Lemma ce_val_r :
  @val term_universe ce_model ce_rho ce_r = ce_td_inner.
Proof.
  unfold ce_r, ce_rho, ce_j. simpl.
  destruct (Nat.eq_dec 1 1) as [_ | Hneq].
  - reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

Lemma ce_rhs_holds :
  @holds term_universe ce_model
    (update ce_rho ce_i (@val term_universe ce_model ce_rho ce_r))
    ce_phi.
Proof.
  unfold ce_phi, ce_p, ce_inner, ce_i, ce_j.
  intro b.
  simpl.
  unfold update.
  destruct (Nat.eq_dec 0 1) as [H01 | _]; [discriminate H01 |].
  destruct (Nat.eq_dec 0 0) as [_ | H00]; [reflexivity | contradiction].
Qed.

Lemma ce_lhs_not_holds :
  ~ @holds term_universe ce_model ce_rho ce_phi_sub.
Proof.
  unfold ce_phi_sub.
  intro H.
  specialize (H Bot).
  unfold ce_r, ce_rho, ce_j in H.
  simpl in H.
  destruct (Nat.eq_dec 1 1) as [_ | Hneq].
  - unfold ce_td_inner, ce_inner, td, mcode, tab, ce_model, term_universe in H.
    simpl in H.
    rewrite ce_k_is_two in H.
    discriminate H.
  - exfalso. apply Hneq. reflexivity.
Qed.

Theorem alpha_rename_counterexample_blocked :
  subst_rel ce_phi ce_i ce_r ce_phi_sub /\
  ~ reg_fm ce_i ce_phi /\
  @holds term_universe ce_model
    (update ce_rho ce_i (@val term_universe ce_model ce_rho ce_r))
    ce_phi /\
  ~ @holds term_universe ce_model ce_rho ce_phi_sub.
Proof.
  split.
  - exact ce_subst_rel.
  - split.
    + exact ce_reg_blocked.
    + split.
      * exact ce_rhs_holds.
      * exact ce_lhs_not_holds.
Qed.

Record admissible_model (U : universe) : Type := {
  amodel : model U;
  eval_correct :
    forall t rho,
      bullet U (root U amodel) (evalarg t) = val amodel rho t;
  closure_correct :
    forall t rho,
      bullet U (closure_name amodel t) (tag U rho_ass []) = val amodel rho t;
  closure_wrong_input :
    forall t A,
      A <> tag U rho_ass [] ->
      bullet U (closure_name amodel t) A = botD U
}.

Definition valid {U : universe} (M : model U) (phi : term) : Prop :=
  forall rho, holds M rho phi.

Theorem prop_axiom1_valid :
  forall U (M : model U) p q,
    valid M (Imp p (Imp q p)).
Proof.
  unfold valid. simpl. auto.
Qed.

Theorem prop_axiom2_valid :
  forall U (M : model U) p q r,
    valid M (Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r))).
Proof.
  unfold valid. simpl. auto.
Qed.

Theorem prop_axiom3_valid :
  forall U (M : model U) p q,
    valid M (Imp (Imp (Neg q) (Neg p)) (Imp p q)).
Proof.
  unfold valid. simpl. intros U M p q rho H Hq.
  apply NNPP. intro Hnq.
  exact (H Hnq Hq).
Qed.

Theorem eq_refl_valid :
  forall U (M : model U) t, valid M (Eq t t).
Proof.
  unfold valid. simpl. auto.
Qed.

Theorem mp_valid :
  forall U (M : model U) p q,
    valid M p -> valid M (Imp p q) -> valid M q.
Proof.
  unfold valid. simpl. intros U M p q Hp Hpq rho.
  exact (Hpq rho (Hp rho)).
Qed.

Theorem generalization_valid :
  forall U (M : model U) i p,
    valid M p -> valid M (All i p).
Proof.
  unfold valid. simpl. intros U M i p Hp rho b.
  apply Hp.
Qed.

Inductive core_axiom : term -> Prop :=
| CoreProp1 : forall p q, core_axiom (Imp p (Imp q p))
| CoreProp2 : forall p q r,
    core_axiom (Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r)))
| CoreProp3 : forall p q,
    core_axiom (Imp (Imp (Neg q) (Neg p)) (Imp p q))
| CoreEqRefl : forall t, core_axiom (Eq t t).

Inductive core_derivable : term -> Prop :=
| CoreAx : forall p, core_axiom p -> core_derivable p
| CoreMP : forall p q,
    core_derivable p ->
    core_derivable (Imp p q) ->
    core_derivable q
| CoreGen : forall i p,
    core_derivable p ->
    core_derivable (All i p).

Theorem core_axiom_valid :
  forall U (M : model U) p,
    core_axiom p -> valid M p.
Proof.
  intros U M p Hax. destruct Hax.
  - apply prop_axiom1_valid.
  - apply prop_axiom2_valid.
  - apply prop_axiom3_valid.
  - apply eq_refl_valid.
Qed.

Theorem core_reliability :
  forall U (M : model U) p,
    core_derivable p -> valid M p.
Proof.
  intros U M p H.
  induction H as [p Hax | p q Hp IHp Himp IHimp | i p Hp IHp].
  - now apply core_axiom_valid.
  - exact (mp_valid U M p q IHp IHimp).
  - exact (generalization_valid U M i p IHp).
Qed.

Definition external_reliability_law : Prop :=
  forall U (AM : admissible_model U) phi,
    proof_step [] phi ->
    valid (amodel U AM) phi.

Definition context_valid {U : universe} (M : model U) (Gamma : list term) : Prop :=
  forall p, In p Gamma -> valid M p.

Definition axiom_sound_for {U : universe} (M : model U) : Prop :=
  forall p, axiom p -> valid M p.

Definition all_inst_sound_for {U : universe} (M : model U) : Prop :=
  forall i p t p',
    formula p ->
    reg_fm i p ->
    subst_rel p i t p' ->
    valid M (Imp (All i p) p').

Definition all_distrib_sound_for {U : universe} (M : model U) : Prop :=
  forall i p q,
    formula p ->
    formula q ->
    ~ In i (fv p) ->
    valid M (Imp (All i (Imp p q)) (Imp p (All i q))).

Definition eq_subst_sound_for {U : universe} (M : model U) : Prop :=
  forall i p t u pt pu,
    formula p ->
    reg_fm i p ->
    subst_rel p i t pt ->
    subst_rel p i u pu ->
    valid M (Imp (Eq t u) (Imp pt pu)).

Theorem all_inst_sound_from_transparent_formula_substitution :
  transparent_formula_substitution_law ->
  forall U (M : model U), all_inst_sound_for M.
Proof.
  intros Hsub U M.
  unfold all_inst_sound_for, valid.
  intros i p t p' _ Hreg Hsubst rho Hall.
  simpl in Hall.
  pose proof (Hsub U M rho i p t p' Hreg Hsubst) as Hiff.
  apply Hiff.
  exact (Hall (val M rho t)).
Qed.

Theorem eq_subst_sound_from_transparent_formula_substitution :
  transparent_formula_substitution_law ->
  forall U (M : model U), eq_subst_sound_for M.
Proof.
  intros Hsub U M.
  unfold eq_subst_sound_for, valid.
  intros i p t u pt pu _ Hreg Hsubst_t Hsubst_u rho Htu Hpt.
  simpl in Htu.
  pose proof (Hsub U M rho i p t pt Hreg Hsubst_t) as Hiff_t.
  pose proof (Hsub U M rho i p u pu Hreg Hsubst_u) as Hiff_u.
  apply Hiff_u.
  rewrite <- Htu.
  apply Hiff_t.
  exact Hpt.
Qed.

Theorem all_distrib_sound_from_formula_freshness :
  formula_freshness_law ->
  forall U (M : model U), all_distrib_sound_for M.
Proof.
  intros Hfresh U M.
  unfold all_distrib_sound_for, valid.
  intros i p q Hp _ Hnot rho Hall Hp_rho b.
  simpl in Hall.
  apply Hall.
  apply (proj2 (Hfresh U M rho i b p Hp Hnot)).
  exact Hp_rho.
Qed.

Theorem all_distrib_sound_for_holds :
  forall U (M : model U), all_distrib_sound_for M.
Proof.
  exact (all_distrib_sound_from_formula_freshness formula_freshness_law_holds).
Qed.

Theorem axiom_sound_from_schema_laws :
  forall U (M : model U),
    all_inst_sound_for M ->
    all_distrib_sound_for M ->
    eq_subst_sound_for M ->
    axiom_sound_for M.
Proof.
  unfold axiom_sound_for.
  intros U M Hall_inst Hall_distrib Heq_subst p Hax.
  unfold all_inst_sound_for in Hall_inst.
  unfold all_distrib_sound_for in Hall_distrib.
  unfold eq_subst_sound_for in Heq_subst.
  destruct Hax.
  - apply prop_axiom1_valid.
  - apply prop_axiom2_valid.
  - apply prop_axiom3_valid.
  - exact (Hall_inst i p t p' H H0 H1).
  - exact (Hall_distrib i p q H H0 H1).
  - apply eq_refl_valid.
  - exact (Heq_subst i p t u pt pu H H0 H1 H2).
Qed.

Theorem axiom_sound_from_transparency_and_freshness :
  transparent_formula_substitution_law ->
  formula_freshness_law ->
  forall U (M : model U), axiom_sound_for M.
Proof.
  intros Hsub Hfresh U M.
  apply axiom_sound_from_schema_laws.
  - exact (all_inst_sound_from_transparent_formula_substitution Hsub U M).
  - exact (all_distrib_sound_from_formula_freshness Hfresh U M).
  - exact (eq_subst_sound_from_transparent_formula_substitution Hsub U M).
Qed.

Theorem axiom_sound_from_transparent_formula_substitution :
  transparent_formula_substitution_law ->
  forall U (M : model U), axiom_sound_for M.
Proof.
  intro Hsub.
  apply axiom_sound_from_transparency_and_freshness.
  - exact Hsub.
  - exact formula_freshness_law_holds.
Qed.

Theorem proof_step_sound_from_axioms :
  forall U (M : model U) Gamma phi,
    context_valid M Gamma ->
    axiom_sound_for M ->
    proof_step Gamma phi ->
    valid M phi.
Proof.
  intros U M Gamma phi Hctx Hax Hstep.
  induction Hstep.
  - exact (Hax p H).
  - exact (Hctx p H).
  - exact (mp_valid U M p q (IHHstep1 Hctx) (IHHstep2 Hctx)).
  - exact (generalization_valid U M i p (IHHstep Hctx)).
Qed.

Theorem proof_step_sound_from_schema_laws :
  forall U (M : model U) Gamma phi,
    context_valid M Gamma ->
    all_inst_sound_for M ->
    all_distrib_sound_for M ->
    eq_subst_sound_for M ->
    proof_step Gamma phi ->
    valid M phi.
Proof.
  intros U M Gamma phi Hctx Hall_inst Hall_distrib Heq_subst Hstep.
  apply (proof_step_sound_from_axioms U M Gamma phi Hctx).
  - apply axiom_sound_from_schema_laws; assumption.
  - exact Hstep.
Qed.

Theorem proof_step_sound_from_transparency_and_freshness :
  transparent_formula_substitution_law ->
  formula_freshness_law ->
  forall U (M : model U) Gamma phi,
    context_valid M Gamma ->
    proof_step Gamma phi ->
    valid M phi.
Proof.
  intros Hsub Hfresh U M Gamma phi Hctx Hstep.
  apply (proof_step_sound_from_axioms U M Gamma phi Hctx).
  - exact (axiom_sound_from_transparency_and_freshness Hsub Hfresh U M).
  - exact Hstep.
Qed.

Theorem proof_step_sound_from_transparent_formula_substitution :
  transparent_formula_substitution_law ->
  forall U (M : model U) Gamma phi,
    context_valid M Gamma ->
    proof_step Gamma phi ->
    valid M phi.
Proof.
  intros Hsub U M Gamma phi Hctx Hstep.
  apply (proof_step_sound_from_transparency_and_freshness
           Hsub formula_freshness_law_holds U M Gamma phi Hctx Hstep).
Qed.

Theorem empty_proof_step_sound_from_axioms :
  forall U (AM : admissible_model U) phi,
    axiom_sound_for (amodel U AM) ->
    proof_step [] phi ->
    valid (amodel U AM) phi.
Proof.
  intros U AM phi Hax Hstep.
  apply (proof_step_sound_from_axioms U (amodel U AM) [] phi).
  - intros p Hin. simpl in Hin. contradiction.
  - exact Hax.
  - exact Hstep.
Qed.

Theorem empty_proof_step_sound_from_schema_laws :
  forall U (AM : admissible_model U) phi,
    all_inst_sound_for (amodel U AM) ->
    all_distrib_sound_for (amodel U AM) ->
    eq_subst_sound_for (amodel U AM) ->
    proof_step [] phi ->
    valid (amodel U AM) phi.
Proof.
  intros U AM phi Hall_inst Hall_distrib Heq_subst Hstep.
  apply (proof_step_sound_from_schema_laws
           U (amodel U AM) [] phi).
  - intros p Hin. simpl in Hin. contradiction.
  - exact Hall_inst.
  - exact Hall_distrib.
  - exact Heq_subst.
  - exact Hstep.
Qed.

Theorem empty_proof_step_sound_from_transparency_and_freshness :
  transparent_formula_substitution_law ->
  formula_freshness_law ->
  forall U (AM : admissible_model U) phi,
    proof_step [] phi ->
    valid (amodel U AM) phi.
Proof.
  intros Hsub Hfresh U AM phi Hstep.
  apply (proof_step_sound_from_transparency_and_freshness
           Hsub Hfresh U (amodel U AM) [] phi).
  - intros p Hin. simpl in Hin. contradiction.
  - exact Hstep.
Qed.

Theorem empty_proof_step_sound_from_transparent_formula_substitution :
  transparent_formula_substitution_law ->
  forall U (AM : admissible_model U) phi,
    proof_step [] phi ->
    valid (amodel U AM) phi.
Proof.
  intros Hsub U AM phi Hstep.
  apply (empty_proof_step_sound_from_transparency_and_freshness
           Hsub formula_freshness_law_holds U AM phi Hstep).
Qed.

Theorem all_inst_sound_for_holds :
  forall U (M : model U), all_inst_sound_for M.
Proof.
  exact (all_inst_sound_from_transparent_formula_substitution
           transparent_formula_substitution_law_holds).
Qed.

Theorem eq_subst_sound_for_holds :
  forall U (M : model U), eq_subst_sound_for M.
Proof.
  exact (eq_subst_sound_from_transparent_formula_substitution
           transparent_formula_substitution_law_holds).
Qed.

Theorem axiom_sound_for_holds :
  forall U (M : model U), axiom_sound_for M.
Proof.
  exact (axiom_sound_from_transparent_formula_substitution
           transparent_formula_substitution_law_holds).
Qed.

Theorem proof_step_sound :
  forall U (M : model U) Gamma phi,
    context_valid M Gamma ->
    proof_step Gamma phi ->
    valid M phi.
Proof.
  exact (proof_step_sound_from_transparent_formula_substitution
           transparent_formula_substitution_law_holds).
Qed.

Theorem empty_proof_step_sound :
  forall U (AM : admissible_model U) phi,
    proof_step [] phi ->
    valid (amodel U AM) phi.
Proof.
  exact (empty_proof_step_sound_from_transparent_formula_substitution
           transparent_formula_substitution_law_holds).
Qed.

Theorem external_reliability_law_holds :
  external_reliability_law.
Proof.
  unfold external_reliability_law.
  exact empty_proof_step_sound.
Qed.

Definition IntState {U : universe} (M : model U) : carrier U :=
  tag U rho_intstate [root U M; tab M].

Definition TabState {U : universe} (M : model U) : carrier U :=
  tag U rho_tabstate [root U M; tab M].

Definition Iso {U : universe} (z : carrier U) : carrier U :=
  retag U rho_intstate rho_tabstate z.

Definition IsoInv {U : universe} (z : carrier U) : carrier U :=
  retag U rho_tabstate rho_intstate z.

Theorem iso_int_to_tab :
  forall U (M : model U), Iso (IntState M) = TabState M.
Proof.
  intros U M. unfold Iso, IntState, TabState.
  apply retag_tag.
Qed.

Theorem syntax_quote_distinct :
  forall U,
    syn U (Quote []) <>
    syn U (Quote [(Var 0, Eq (Var 0) (Var 0))]).
Proof.
  intros U H.
  apply syn_injective in H.
  discriminate H.
Qed.

Definition q0 : term := Quote [].
Definition v0 : term := Var 0.
Definition epsilon0 : term := Eq v0 v0.
Definition q1 : term := Quote [(v0, epsilon0)].
Definition theta_sat : term := Eq q0 q0.
Definition theta_unsat : term := Eq q0 q1.

Theorem q0_q1_values_distinct :
  forall U (M : model U) rho,
    val M rho q0 <> val M rho q1.
Proof.
  intros U M rho H.
  unfold q0, q1 in H. simpl in H.
  exact (syntax_quote_distinct U H).
Qed.

Theorem theta_sat_holds :
  forall U (M : model U) rho, holds M rho theta_sat.
Proof.
  unfold theta_sat. simpl. reflexivity.
Qed.

Theorem theta_unsat_not_holds :
  forall U (M : model U) rho, ~ holds M rho theta_unsat.
Proof.
  unfold theta_unsat. simpl.
  apply q0_q1_values_distinct.
Qed.

Definition no_extensionality_principle : Prop :=
  ~ (forall U (a b : carrier U),
       (forall x, bullet U a x = bullet U b x) -> a = b).

Definition unstratified_truth_extractor (T : term -> term) : Prop :=
  forall phi,
    formula phi ->
    formula (T phi) /\ formula (Iff (T phi) phi).

Definition no_unstratified_truth_extractor_law : Prop :=
  forall T, ~ unstratified_truth_extractor T.

Definition axiom_level_truth_extractor (T : term -> term) : Prop :=
  forall phi,
    formula phi ->
    formula (T phi) /\ axiom (Iff (T phi) phi).

Theorem no_truth_pattern_axiom :
  forall T phi,
    ~ axiom (Iff (T phi) phi).
Proof.
  intros T phi H.
  unfold Iff, Conj in H.
  inversion H.
Qed.

Theorem no_axiom_level_truth_extractor_law :
  forall T, ~ axiom_level_truth_extractor T.
Proof.
  intros T H.
  destruct (H Bot I) as [_ Hax].
  exact (no_truth_pattern_axiom T Bot Hax).
Qed.

End InterpretivePro1130.
