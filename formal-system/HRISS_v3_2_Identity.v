(** The exact identity-subgroup branch of HRISS v3.2, Section 12. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lists.List Lia
  Logic.ClassicalDescription Logic.Classical_Prop Program.Equality.
Require Import HRISS_v3_2.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Definition TrivialSyntax (Sig : Signature) := SyntaxCarrier Sig trivial_subgroup.
Definition TrivialTm (Sig : Signature) :=
  { t : tm Sig | wf_tm trivial_subgroup t }.

Lemma Hminus_trivial_empty : forall g, ~ Hminus trivial_subgroup g.
Proof. intros g [Hg Hne]. apply Hne. exact Hg. Qed.

Theorem trivial_syntax_has_no_Move : forall Sig g,
    ~ wf_tm trivial_subgroup (@TMove Sig g).
Proof. intros Sig g. apply Hminus_trivial_empty. Qed.

Theorem trivial_orbit_exact : forall i,
    orbit0 trivial_subgroup i <-> i = 0.
Proof.
  intro i. split.
  - intros (g & Hg & ->). cbn in Hg. subst g. reflexivity.
  - intro Hi. subst i. exists pid. split; reflexivity.
Qed.

(** The least natural outside a finite name set, not merely an arbitrary
    fresh name. *)
Definition IsLeastFresh (K : NameSet) (k : nat) : Prop :=
  Fresh k K /\ forall m, m < k -> In m K.

Lemma bounded_least : forall (P : nat -> Prop) n,
    (exists k, k <= n /\ P k) ->
    exists k, P k /\ forall m, m < k -> ~ P m.
Proof.
  intros P n. induction n as [|n IH]; intros (k & Hkn & Hk).
  - assert (k = 0) by lia. subst k. exists 0. split; [exact Hk|lia].
  - destruct (classic (exists k, k <= n /\ P k)) as [Hex|Hnone].
    + now apply IH.
    + assert (Hnle : ~ k <= n).
      { intro Hle. apply Hnone. exists k. now split. }
      assert (k = S n) by lia. subst k. exists (S n). split; [exact Hk|].
      intros m Hm HPm. apply Hnone. exists m. split; [lia|exact HPm].
Qed.

Lemma least_fresh_exists_unique : forall K, exists! k, IsLeastFresh K k.
Proof.
  intro K.
  destruct (@bounded_least (fun k => Fresh k K) (fresh_name K)) as
      (k & Hfresh & Hmin).
  - exists (fresh_name K). split; [lia|apply fresh_name_spec].
  - exists k. split.
    + split; [exact Hfresh|]. intros m Hmk.
      apply NNPP. intro Hnot. apply (Hmin m Hmk). exact Hnot.
    + intros l [Hlfresh Hlmin].
      destruct (Nat.lt_trichotomy k l) as [Hkl|[Hkl|Hlk]].
      * exfalso. apply Hfresh. now apply Hlmin.
      * exact Hkl.
      * exfalso. exact (Hmin l Hlk Hlfresh).
Qed.

Definition least_fresh (K : NameSet) : nat :=
  proj1_sig (constructive_definite_description (IsLeastFresh K)
    (least_fresh_exists_unique K)).

Lemma least_fresh_spec : forall K, Fresh (least_fresh K) K.
Proof.
  intro K. unfold least_fresh.
  exact (proj1 (proj2_sig (constructive_definite_description
    (IsLeastFresh K) (least_fresh_exists_unique K)))).
Qed.

Lemma least_fresh_minimal : forall K m,
    m < least_fresh K -> In m K.
Proof.
  intro K. unfold least_fresh.
  exact (proj2 (proj2_sig (constructive_definite_description
    (IsLeastFresh K) (least_fresh_exists_unique K)))).
Qed.

Definition active_rename_expr {Sig} j k (z : expr Sig) : expr Sig :=
  match z with
  | ETerm t => ETerm (active_rename_tm j k t)
  | EForm p => EForm (active_rename_fm j k p)
  end.

Lemma active_rename_expr_wf : forall Sig j k (z : expr Sig),
    ~ In k (AN z) -> wf_expr trivial_subgroup z ->
    wf_expr trivial_subgroup (active_rename_expr j k z).
Proof.
  intros Sig j k [t|p] Hfresh Hwf; cbn in *.
  - eapply BRenTmCore_preserves_wf; [apply active_rename_BRenTmCore|exact Hwf].
    exact Hfresh.
  - eapply BRenFmCore_preserves_wf; [apply active_rename_BRenFmCore|exact Hwf].
    exact Hfresh.
Qed.

Definition ORenDomain {Sig} (j k : nat) :=
  { z : TrivialSyntax Sig | ~ In k (AN (proj1_sig z)) }.

Definition ORen {Sig} (j k : nat) (Hjk : j <> k)
    (z : ORenDomain (Sig:=Sig) j k) : TrivialSyntax Sig.
Proof.
  destruct z as [[raw Hwf] Hfresh].
  refine (exist _ (active_rename_expr j k raw) _).
  now apply active_rename_expr_wf.
Defined.

Lemma ORen_sort : forall Sig j k (Hjk : j <> k)
    (z : ORenDomain (Sig:=Sig) j k),
    expr_sort (proj1_sig (@ORen Sig j k Hjk z)) =
      expr_sort (proj1_sig (proj1_sig z)).
Proof.
  intros Sig j k Hjk [z Hfresh]. destruct z as [[t|p] Hwf]; reflexivity.
Qed.

(** Terms contain no active formula recursion because Quote targets are
    shielded.  Hence their identity-branch substitution is structural. *)
Fixpoint Sub0_tm {Sig} (i : nat) (s : tm Sig) (t : tm Sig) : tm Sig :=
  match t with
  | TVar j => if Nat.eq_dec j i then s else TVar j
  | TFun f xs => TFun f (Sub0_tml i s xs)
  | TQuoteT u => TQuoteT u
  | TQuoteF p => TQuoteF p
  | TRApp u v => TRApp (Sub0_tm i s u) v
  | TMove g => TMove g
  end
with Sub0_tml {Sig n} (i : nat) (s : tm Sig) (xs : tml Sig n) : tml Sig n :=
  match xs with
  | TNil => TNil
  | TCons t ts => TCons (Sub0_tm i s t) (Sub0_tml i s ts)
  end.

Definition capture_set {Sig} i j (s : tm Sig) (p : fm Sig) : NameSet :=
  AN_fm p ++ FV_tm s ++ [i; j].

(** Formula recursion is implemented with an explicit structural budget.
    The only non-subterm call is on [active_rename_fm j k p], which preserves
    tree size; the budget decreases before that call. *)
Fixpoint fm_nodes {Sig} (p : fm Sig) : nat :=
  match p with
  | FPred _ xs => S (tml_nodes xs)
  | FConn _ ps => S (fml_nodes ps)
  | FRApp t _ => S (tm_nodes t)
  | FQuant _ _ q => S (fm_nodes q)
  end
with fml_nodes {Sig n} (ps : fml Sig n) : nat :=
  match ps with
  | FNil => 0
  | FCons p qs => S (fm_nodes p + fml_nodes qs)
  end
with tm_nodes {Sig} (t : tm Sig) : nat :=
  match t with
  | TVar _ | TQuoteT _ | TQuoteF _ | TMove _ => 1
  | TFun _ xs => S (tml_nodes xs)
  | TRApp u _ => S (tm_nodes u)
  end
with tml_nodes {Sig n} (xs : tml Sig n) : nat :=
  match xs with
  | TNil => 0
  | TCons t ts => S (tm_nodes t + tml_nodes ts)
  end.

Fixpoint sub0_fm_fuel {Sig} (fuel i : nat) (s : tm Sig) (p : fm Sig) : fm Sig :=
  match fuel with
  | 0 => p
  | S fuel' =>
      match p with
      | FPred P xs => FPred P (Sub0_tml i s xs)
      | FConn L ps => FConn L (sub0_fml_fuel fuel' i s ps)
      | FRApp t q => FRApp (Sub0_tm i s t) q
      | FQuant Q j q =>
          if Nat.eq_dec j i then FQuant Q j q
          else if in_dec Nat.eq_dec j (FV_tm s) then
            let k := least_fresh (capture_set i j s q) in
            FQuant Q k (sub0_fm_fuel fuel' i s (active_rename_fm j k q))
          else FQuant Q j (sub0_fm_fuel fuel' i s q)
      end
  end
with sub0_fml_fuel {Sig n} (fuel i : nat) (s : tm Sig)
    (ps : fml Sig n) : fml Sig n :=
  match fuel with
  | 0 => ps
  | S fuel' =>
      match ps with
      | FNil => FNil
      | FCons p qs =>
          FCons (sub0_fm_fuel fuel' i s p) (sub0_fml_fuel fuel' i s qs)
      end
  end.

Definition Sub0_fm {Sig} i (s : tm Sig) (p : fm Sig) : fm Sig :=
  sub0_fm_fuel (S (fm_nodes p)) i s p.

Definition Sub0_fml {Sig n} i (s : tm Sig) (ps : fml Sig n) : fml Sig n :=
  sub0_fml_fuel (S (fml_nodes ps)) i s ps.

Definition Sub0_expr {Sig} i (s : tm Sig) (z : expr Sig) : expr Sig :=
  match z with
  | ETerm t => ETerm (Sub0_tm i s t)
  | EForm p => EForm (Sub0_fm i s p)
  end.

Lemma Sub0_Var_hit : forall Sig i (s : tm Sig), Sub0_tm i s (TVar i) = s.
Proof. intros. cbn. destruct (Nat.eq_dec i i); congruence. Qed.

Lemma Sub0_Var_miss : forall Sig i j (s : tm Sig),
    j <> i -> Sub0_tm i s (TVar j) = TVar j.
Proof. intros. cbn. destruct (Nat.eq_dec j i); congruence. Qed.

Lemma Sub0_QuoteT_shield : forall Sig i (s t : tm Sig),
    Sub0_tm i s (TQuoteT t) = TQuoteT t.
Proof. reflexivity. Qed.

Lemma Sub0_QuoteF_shield : forall Sig i (s : tm Sig) (p : fm Sig),
    Sub0_tm i s (TQuoteF p) = TQuoteF p.
Proof. reflexivity. Qed.

Lemma Sub0_RAppT_shield : forall Sig i (s t u : tm Sig),
    Sub0_tm i s (TRApp t u) = TRApp (Sub0_tm i s t) u.
Proof. reflexivity. Qed.

Lemma Sub0_RAppF_shield : forall Sig fuel i (s : tm Sig) t p,
    sub0_fm_fuel (S fuel) i s (FRApp t p) = FRApp (Sub0_tm i s t) p.
Proof. reflexivity. Qed.

Lemma Sub0_quant_bound : forall Sig fuel i (s : tm Sig) Q p,
    sub0_fm_fuel (S fuel) i s (FQuant Q i p) = FQuant Q i p.
Proof. intros. cbn. destruct (Nat.eq_dec i i); congruence. Qed.

Lemma least_fresh_capture : forall Sig i j (s : tm Sig) (p : fm Sig),
    let k := least_fresh (capture_set i j s p) in
    ~ In k (AN_fm p) /\ ~ In k (FV_tm s) /\ k <> i /\ k <> j.
Proof.
  intros Sig i j s p. cbn. set (k := least_fresh (capture_set i j s p)).
  pose proof (@least_fresh_spec (capture_set i j s p)) as Hfresh.
  fold k in Hfresh.
  unfold Fresh, capture_set in Hfresh. repeat split; intro Hin; apply Hfresh.
  - apply in_app_iff. now left.
  - apply in_app_iff. right. apply in_app_iff. now left.
  - apply in_app_iff. right. apply in_app_iff. right. now left.
  - apply in_app_iff. right. apply in_app_iff. right. now right; left.
Qed.

(** Well-formedness preservation for the total identity substitution. *)
Fixpoint Sub0_tm_wf {Sig} i (s t : tm Sig) (Hs : wf_tm trivial_subgroup s)
    (Ht : wf_tm trivial_subgroup t) {struct t} :
    wf_tm trivial_subgroup (Sub0_tm i s t)
with Sub0_tml_wf {Sig n} i (s : tm Sig) (xs : tml Sig n)
    (Hs : wf_tm trivial_subgroup s) (Hxs : wf_tml trivial_subgroup xs)
    {struct xs} : wf_tml trivial_subgroup (Sub0_tml i s xs).
Proof.
  - destruct t; cbn in *.
    + destruct (Nat.eq_dec n i); assumption.
    + now apply Sub0_tml_wf.
    + exact Ht.
    + exact Ht.
    + split; [now apply Sub0_tm_wf|exact (proj2 Ht)].
    + exact Ht.
  - destruct xs; cbn in *.
    + exact I.
    + split; [now apply Sub0_tm_wf|now apply Sub0_tml_wf].
Defined.

Fixpoint sub0_fm_fuel_wf {Sig} fuel i (s : tm Sig) (p : fm Sig)
    (Hs : wf_tm trivial_subgroup s) (Hp : wf_fm trivial_subgroup p)
    {struct fuel} : wf_fm trivial_subgroup (sub0_fm_fuel fuel i s p)
with sub0_fml_fuel_wf {Sig n} fuel i (s : tm Sig) (ps : fml Sig n)
    (Hs : wf_tm trivial_subgroup s) (Hps : wf_fml trivial_subgroup ps)
    {struct fuel} : wf_fml trivial_subgroup (sub0_fml_fuel fuel i s ps).
Proof.
  - destruct fuel as [|fuel']; [exact Hp|].
    destruct p as [n P xs|n L ps|t q|Q j q]; cbn in *.
    + now apply Sub0_tml_wf.
    + now apply sub0_fml_fuel_wf.
    + split; [now apply Sub0_tm_wf|exact (proj2 Hp)].
    + destruct (Nat.eq_dec j i) as [Heq|Hne]; [exact Hp|].
      destruct (in_dec Nat.eq_dec j (FV_tm s)) as [Hin|Hnot].
      * cbn. set (k := least_fresh (capture_set i j s q)).
        apply (@sub0_fm_fuel_wf Sig fuel' i s (active_rename_fm j k q) Hs).
        eapply BRenFmCore_preserves_wf.
        -- apply active_rename_BRenFmCore. subst k.
           destruct (least_fresh_capture i j s q) as [Hfresh _]. exact Hfresh.
        -- exact Hp.
      * cbn. now apply sub0_fm_fuel_wf.
  - destruct fuel as [|fuel']; [exact Hps|]. destruct ps; cbn in *.
    + exact I.
    + split; [now apply sub0_fm_fuel_wf|now apply sub0_fml_fuel_wf].
Defined.

Lemma Sub0_expr_wf : forall Sig i (s : tm Sig) z,
    wf_tm trivial_subgroup s -> wf_expr trivial_subgroup z ->
    wf_expr trivial_subgroup (Sub0_expr i s z).
Proof.
  intros Sig i s [t|p] Hs Hz; cbn in *.
  - now apply Sub0_tm_wf.
  - change (wf_fm trivial_subgroup
      (sub0_fm_fuel (S (fm_nodes p)) i s p)).
    exact (@sub0_fm_fuel_wf Sig (S (fm_nodes p)) i s p Hs Hz).
Qed.

Definition Sub0 {Sig} i (s : TrivialTm Sig) (z : TrivialSyntax Sig) :
    TrivialSyntax Sig :=
  exist _ (Sub0_expr i (proj1_sig s) (proj1_sig z))
    (Sub0_expr_wf i (proj2_sig s) (proj2_sig z)).

Lemma Sub0_sort : forall Sig i (s : TrivialTm Sig) (z : TrivialSyntax Sig),
    expr_sort (proj1_sig (Sub0 i s z)) = expr_sort (proj1_sig z).
Proof. intros Sig i s [[t|p] Hz]; reflexivity. Qed.

Record IdentityTransformData (Sig : Signature) : Type := {
  identity_ORen : forall j k, j <> k -> ORenDomain (Sig:=Sig) j k ->
    TrivialSyntax Sig;
  identity_Sub0 : nat -> TrivialTm Sig -> TrivialSyntax Sig ->
    TrivialSyntax Sig
}.

Definition identity_transform_data (Sig : Signature) : IdentityTransformData Sig :=
  {| identity_ORen := @ORen Sig; identity_Sub0 := @Sub0 Sig |}.

Print Assumptions least_fresh_minimal.
Print Assumptions Sub0_expr_wf.
