From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Relations.Relation_Operators.

Import ListNotations.

Module ProgramInducedSyntax1135.

Definition code := nat.
Definition finset := list nat.
Definition in_fin (x : nat) (s : finset) : Prop := In x s.

Fixpoint strictly_increasing (s : list nat) : Prop :=
  match s with
  | [] => True
  | x :: xs => Forall (fun y => x < y) xs /\ strictly_increasing xs
  end.

Definition canonical_finset (s : finset) : Prop := strictly_increasing s.

Theorem canonical_finset_nodup :
  forall s, canonical_finset s -> NoDup s.
Proof.
  unfold canonical_finset.
  induction s as [|x xs IH]; simpl; intros Hs.
  - constructor.
  - destruct Hs as [Hall Htail].
    constructor.
    + intro Hin.
      pose proof (Forall_forall (fun y => x < y) xs) as Hforall.
      destruct Hforall as [Hto _].
      specialize (Hto Hall x Hin). lia.
    + apply IH. exact Htail.
Qed.

Theorem canonical_finset_extensional :
  forall s t,
    canonical_finset s ->
    canonical_finset t ->
    (forall x, In x s <-> In x t) ->
    s = t.
Proof.
  unfold canonical_finset.
  induction s as [|x xs IH]; intros t Hs Ht Hext.
  - destruct t as [|y ys].
    + reflexivity.
    + exfalso.
      specialize (Hext y). destruct Hext as [_ Hback].
      apply (Hback (or_introl eq_refl)).
  - destruct t as [|y ys].
    + exfalso.
      specialize (Hext x). destruct Hext as [Hforth _].
      apply (Hforth (or_introl eq_refl)).
    + simpl in Hs, Ht.
      destruct Hs as [Hxall Hxs].
      destruct Ht as [Hyall Hys].
      assert (Hxin : In x (y :: ys)).
      { apply (proj1 (Hext x)). simpl. left. reflexivity. }
      assert (Hyin : In y (x :: xs)).
      { apply (proj2 (Hext y)). simpl. left. reflexivity. }
      assert (Hxy : x = y).
      {
        destruct Hxin as [Hxy | Hxinys].
        - symmetry. exact Hxy.
        - destruct Hyin as [Hyx | Hyinxs].
          + exact Hyx.
          + assert (Hxlt : x < y).
            { rewrite Forall_forall in Hxall. apply Hxall. exact Hyinxs. }
            assert (Hylt : y < x).
            { rewrite Forall_forall in Hyall. apply Hyall. exact Hxinys. }
            lia.
      }
      subst y.
      f_equal.
      apply IH; try assumption.
      intros z. split; intro Hz.
      * assert (Hzfull : In z (x :: ys)).
        { apply (proj1 (Hext z)). simpl. right. exact Hz. }
        destruct Hzfull as [Hzx | Hzys].
        -- subst z.
            pose proof
              (proj1 (Forall_forall (fun z => x < z) xs) Hxall x Hz)
              as Hlt.
            exfalso.
            exact (Nat.lt_irrefl x Hlt).
        -- exact Hzys.
      * assert (Hzfull : In z (x :: xs)).
        { apply (proj2 (Hext z)). simpl. right. exact Hz. }
        destruct Hzfull as [Hzx | Hzxs].
        -- subst z.
            pose proof
              (proj1 (Forall_forall (fun z => x < z) ys) Hyall x Hz)
              as Hlt.
            exfalso.
            exact (Nat.lt_irrefl x Hlt).
        -- exact Hzxs.
Qed.

Definition pair_code (x y : nat) : nat := (2 ^ x) * (2 * y + 1).
Definition tuple0 : nat := 0.
Definition tuple1 (x : nat) : nat := pair_code 1 x.
Definition tuple2 (x y : nat) : nat := pair_code 2 (pair_code x y).
Definition tuple3 (x y z : nat) : nat := pair_code 3 (pair_code x (pair_code y z)).


Theorem pair_code_witness :
  forall x y, exists c, c = pair_code x y.
Proof.
  intros x y. exists (pair_code x y). reflexivity.
Qed.

Theorem tuple0_code_witness :
  exists c, c = tuple0.
Proof.
  exists tuple0. reflexivity.
Qed.

Theorem tuple1_code_witness :
  forall x, exists c, c = tuple1 x.
Proof.
  intro x. exists (tuple1 x). reflexivity.
Qed.

Theorem tuple2_code_witness :
  forall x y, exists c, c = tuple2 x y.
Proof.
  intros x y. exists (tuple2 x y). reflexivity.
Qed.

Theorem tuple3_code_witness :
  forall x y z, exists c, c = tuple3 x y z.
Proof.
  intros x y z. exists (tuple3 x y z). reflexivity.
Qed.

Definition finfun (A : Type) := list (nat * A).
Definition canonical_finfun {A : Type} (f : finfun A) : Prop :=
  canonical_finset (map fst f).

Fixpoint lookup {A : Type} (x : nat) (f : finfun A) : option A :=
  match f with
  | [] => None
  | (a, b) :: rest => if Nat.eq_dec x a then Some b else lookup x rest
  end.

Fixpoint update {A : Type} (x : nat) (v : A) (f : finfun A) : finfun A :=
  match f with
  | [] => [(x, v)]
  | (a, b) :: rest =>
      if Nat.eq_dec x a then (a, v) :: rest else (a, b) :: update x v rest
  end.

Fixpoint insert_nat (x : nat) (s : list nat) : list nat :=
  match s with
  | [] => [x]
  | y :: ys =>
      if Nat.eq_dec x y then y :: ys
      else if Nat.ltb x y then x :: y :: ys else y :: insert_nat x ys
  end.

Record labelled_edge : Type := {
  edge_src : nat;
  edge_label : nat;
  edge_dst : nat
}.

Definition labelled_graph := list labelled_edge.

Definition labelled_edge_code (e : labelled_edge) : nat :=
  tuple3 (edge_src e) (edge_label e) (edge_dst e).

Fixpoint labelled_graph_code (g : labelled_graph) : finset :=
  match g with
  | [] => []
  | e :: rest => insert_nat (labelled_edge_code e) (labelled_graph_code rest)
  end.

Definition canGraph (g : labelled_graph) : finset :=
  labelled_graph_code g.

Theorem labelled_graph_code_finite_witness :
  forall g, exists c, c = canGraph g.
Proof.
  intro g. exists (canGraph g). reflexivity.
Qed.
Fixpoint canonical_update {A : Type}
    (x : nat) (v : A) (f : finfun A) : finfun A :=
  match f with
  | [] => [(x, v)]
  | (a, b) :: rest =>
      if Nat.eq_dec x a then (a, v) :: rest
      else if Nat.ltb x a then (x, v) :: (a, b) :: rest
      else (a, b) :: canonical_update x v rest
  end.

Lemma lookup_update_hit :
  forall A (x : nat) (v : A) f, lookup x (update x v f) = Some v.
Proof.
  intros A x v f. induction f as [|[a b] rest IH]; simpl.
  - destruct (Nat.eq_dec x x); congruence.
  - destruct (Nat.eq_dec x a) as [E | NE].
    + subst. simpl. destruct (Nat.eq_dec a a); congruence.
    + simpl. destruct (Nat.eq_dec x a); congruence.
Qed.

Lemma lookup_update_miss :
  forall A (x y : nat) (v : A) f,
    x <> y -> lookup x (update y v f) = lookup x f.
Proof.
  intros A x y v f Hxy. induction f as [|[a b] rest IH]; simpl.
  - destruct (Nat.eq_dec x y); congruence.
  - destruct (Nat.eq_dec y a) as [Ey | Ney].
    + simpl. destruct (Nat.eq_dec x a); destruct (Nat.eq_dec x a); congruence.
    + simpl. destruct (Nat.eq_dec x a); auto.
Qed.

Lemma lookup_canonical_update_hit :
  forall A (x : nat) (v : A) f,
    lookup x (canonical_update x v f) = Some v.
Proof.
  intros A x v f. induction f as [|[a b] rest IH]; simpl.
  - destruct (Nat.eq_dec x x); congruence.
  - destruct (Nat.eq_dec x a) as [E | NE].
    + subst. simpl. destruct (Nat.eq_dec a a); congruence.
    + destruct (Nat.ltb x a) eqn:Hlt; simpl.
      * destruct (Nat.eq_dec x x); congruence.
      * destruct (Nat.eq_dec x a); congruence.
Qed.

Lemma lookup_canonical_update_miss :
  forall A (x y : nat) (v : A) f,
    x <> y -> lookup x (canonical_update y v f) = lookup x f.
Proof.
  intros A x y v f Hxy. induction f as [|[a b] rest IH]; simpl.
  - destruct (Nat.eq_dec x y); congruence.
  - destruct (Nat.eq_dec y a) as [Ey | Ney].
    + subst. simpl. destruct (Nat.eq_dec x a); congruence.
    + destruct (Nat.ltb y a) eqn:Hlt; simpl.
      * destruct (Nat.eq_dec x y); [congruence|].
        destruct (Nat.eq_dec x a); reflexivity.
      * destruct (Nat.eq_dec x a); auto.
Qed.

Lemma insert_nat_preserves_all_gt :
  forall y x s,
    y < x ->
    Forall (fun z => y < z) s ->
    Forall (fun z => y < z) (insert_nat x s).
Proof.
  intros y x s Hyx Hall.
  induction s as [|a rest IH]; simpl.
  - constructor; [lia|constructor].
  - inversion Hall as [|? ? Hay Hrest]; subst.
    destruct (Nat.eq_dec x a) as [E | NE].
    + constructor; assumption.
    + destruct (Nat.ltb x a) eqn:Hlt.
      * constructor; [lia|constructor; assumption].
      * constructor; [assumption|apply IH; assumption].
Qed.

Lemma insert_nat_preserves_canonical :
  forall x s,
    canonical_finset s ->
    canonical_finset (insert_nat x s).
Proof.
  unfold canonical_finset.
  induction s as [|a rest IH]; simpl; intros Hs.
  - split; [constructor|exact I].
  - destruct Hs as [Hall Hrest].
    destruct (Nat.eq_dec x a) as [E | NE].
    + split; assumption.
    + destruct (Nat.ltb x a) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt.
        split.
        -- constructor.
           ++ exact Hlt.
           ++ apply Forall_forall. intros z Hz.
              assert (Haz : a < z).
              { rewrite Forall_forall in Hall. apply Hall. exact Hz. }
              lia.
        -- split; assumption.
      * apply Nat.ltb_ge in Hlt.
        split.
        -- apply insert_nat_preserves_all_gt.
           ++ lia.
           ++ exact Hall.
        -- apply IH. exact Hrest.
Qed.

Theorem labelled_graph_code_canonical :
  forall g, canonical_finset (canGraph g).
Proof.
  induction g as [|e rest IH]; simpl.
  - exact I.
  - apply insert_nat_preserves_canonical. exact IH.
Qed.

Definition graph_code_equiv (g h : labelled_graph) : Prop :=
  forall c, In c (canGraph g) <-> In c (canGraph h).

Theorem graph_code_equiv_refl :
  forall g, graph_code_equiv g g.
Proof.
  intros g c. reflexivity.
Qed.

Theorem graph_code_equiv_sym :
  forall g h, graph_code_equiv g h -> graph_code_equiv h g.
Proof.
  intros g h H c. symmetry. exact (H c).
Qed.

Theorem graph_code_equiv_trans :
  forall g h k,
    graph_code_equiv g h ->
    graph_code_equiv h k ->
    graph_code_equiv g k.
Proof.
  intros g h k Hgh Hhk c.
  transitivity (In c (canGraph h)).
  - exact (Hgh c).
  - exact (Hhk c).
Qed.

Theorem graph_code_equiv_canGraph_eq :
  forall g h,
    graph_code_equiv g h ->
    canGraph g = canGraph h.
Proof.
  intros g h H.
  apply canonical_finset_extensional.
  - apply labelled_graph_code_canonical.
  - apply labelled_graph_code_canonical.
  - exact H.
Qed.
Lemma insert_nat_spec :
  forall x y s,
    In y (insert_nat x s) <-> y = x \/ In y s.
Proof.
  intros x y s.
  induction s as [|a rest IH]; simpl.
  - split; intros H.
    + destruct H as [H | []]. left. symmetry. exact H.
    + destruct H as [H | []]. left. symmetry. exact H.
  - destruct (Nat.eq_dec x a) as [Exa | Nxa].
    + subst. simpl. split; intros H.
      * destruct H as [H | H]; [left; symmetry; exact H | right; right; exact H].
      * destruct H as [H | [H | H]]; subst; auto.
    + destruct (Nat.ltb x a) eqn:Hlt; simpl.
      * split; intros H.
        -- destruct H as [H | [H | H]]; subst; auto.
        -- destruct H as [H | [H | H]]; subst; auto.
      * rewrite IH. split; intros H.
        -- destruct H as [H | [H | H]]; subst; auto.
        -- destruct H as [H | [H | H]]; subst; auto.
Qed.

Fixpoint finset_union (s t : finset) : finset :=
  match s with
  | [] => t
  | x :: xs => insert_nat x (finset_union xs t)
  end.

Definition finset_inter (s t : finset) : finset :=
  filter (fun x => if in_dec Nat.eq_dec x t then true else false) s.

Definition finset_diff (s t : finset) : finset :=
  filter (fun x => if in_dec Nat.eq_dec x t then false else true) s.

Theorem finset_union_spec :
  forall x s t,
    In x (finset_union s t) <-> In x s \/ In x t.
Proof.
  intros x s.
  induction s as [|a rest IH]; simpl; intros t.
  - tauto.
  - rewrite insert_nat_spec.
    rewrite IH. simpl. firstorder congruence.
Qed.

Theorem finset_inter_spec :
  forall x s t,
    In x (finset_inter s t) <-> In x s /\ In x t.
Proof.
  intros x s t.
  unfold finset_inter.
  rewrite filter_In.
  destruct (in_dec Nat.eq_dec x t) as [Hin | Hnot].
  - split; intros H.
    + destruct H as [Hs _]. split; assumption.
    + destruct H as [Hs _]. split; [exact Hs | reflexivity].
  - split; intros H.
    + destruct H as [_ Hfalse]. discriminate Hfalse.
    + destruct H as [_ Ht]. contradiction.
Qed.

Theorem finset_diff_spec :
  forall x s t,
    In x (finset_diff s t) <-> In x s /\ ~ In x t.
Proof.
  intros x s t.
  unfold finset_diff.
  rewrite filter_In.
  destruct (in_dec Nat.eq_dec x t) as [Hin | Hnot].
  - split; intros H.
    + destruct H as [_ Hfalse]. discriminate Hfalse.
    + destruct H as [_ Hnotin]. contradiction.
  - split; intros H.
    + destruct H as [Hs _]. split; assumption.
    + destruct H as [Hs _]. split; [exact Hs | reflexivity].
Qed.

Lemma filter_preserves_canonical :
  forall (f : nat -> bool) s,
    canonical_finset s ->
    canonical_finset (filter f s).
Proof.
  unfold canonical_finset.
  intros f s.
  induction s as [|a rest IH]; simpl; intros Hs.
  - exact I.
  - destruct Hs as [Hall Htail].
    destruct (f a) eqn:Hfa; simpl.
    + split.
      * apply Forall_forall. intros y Hy.
        apply filter_In in Hy.
        destruct Hy as [Hy _].
        apply (Forall_forall (fun z => a < z) rest) in Hy; assumption.
      * apply IH. exact Htail.
    + apply IH. exact Htail.
Qed.

Theorem finset_union_preserves_canonical :
  forall s t,
    canonical_finset s ->
    canonical_finset t ->
    canonical_finset (finset_union s t).
Proof.
  intros s t Hs Ht.
  induction s as [|a rest IH]; simpl.
  - exact Ht.
  - destruct Hs as [_ Htail].
    apply insert_nat_preserves_canonical.
    apply IH. exact Htail.
Qed.

Theorem finset_inter_preserves_canonical :
  forall s t,
    canonical_finset s ->
    canonical_finset t ->
    canonical_finset (finset_inter s t).
Proof.
  intros s t Hs _.
  unfold finset_inter.
  apply filter_preserves_canonical.
  exact Hs.
Qed.

Theorem finset_diff_preserves_canonical :
  forall s t,
    canonical_finset s ->
    canonical_finset t ->
    canonical_finset (finset_diff s t).
Proof.
  intros s t Hs _.
  unfold finset_diff.
  apply filter_preserves_canonical.
  exact Hs.
Qed.

Lemma map_fst_canonical_update :
  forall A (x : nat) (v : A) f,
    map fst (canonical_update x v f) = insert_nat x (map fst f).
Proof.
  intros A x v f.
  induction f as [|[a b] rest IH]; simpl.
  - reflexivity.
  - destruct (Nat.eq_dec x a); [reflexivity|].
    destruct (Nat.ltb x a); simpl; [reflexivity|].
    rewrite IH. reflexivity.
Qed.

Theorem canonical_update_preserves :
  forall A (x : nat) (v : A) f,
    canonical_finfun f ->
    canonical_finfun (canonical_update x v f).
Proof.
  intros A x v f Hf.
  unfold canonical_finfun in *.
  rewrite map_fst_canonical_update.
  apply insert_nat_preserves_canonical. exact Hf.
Qed.

Theorem canonical_finfun_nodup_keys :
  forall A (f : finfun A),
    canonical_finfun f -> NoDup (map fst f).
Proof.
  intros A f Hf.
  apply canonical_finset_nodup. exact Hf.
Qed.

Lemma canonical_finfun_tail :
  forall A x (v : A) f,
    canonical_finfun ((x, v) :: f) ->
    canonical_finfun f.
Proof.
  intros A x v f H.
  unfold canonical_finfun, canonical_finset in *.
  simpl in H. exact (proj2 H).
Qed.

Lemma canonical_finfun_head_lt :
  forall A x (v : A) f y,
    canonical_finfun ((x, v) :: f) ->
    In y (map fst f) ->
    x < y.
Proof.
  intros A x v f y H Hy.
  unfold canonical_finfun, canonical_finset in H.
  simpl in H.
  destruct H as [Hall _].
  rewrite Forall_forall in Hall.
  apply Hall. exact Hy.
Qed.

Lemma lookup_some_in_keys :
  forall A (f : finfun A) x v,
    lookup x f = Some v ->
    In x (map fst f).
Proof.
  intros A f.
  induction f as [|[a b] rest IH]; simpl; intros x v H.
  - discriminate H.
  - destruct (Nat.eq_dec x a) as [Hxa | Hxa].
    + subst. simpl. left. reflexivity.
    + simpl. right. apply IH with (v := v). exact H.
Qed.

Lemma lookup_canonical_tail_head_none :
  forall A x (v : A) f,
    canonical_finfun ((x, v) :: f) ->
    lookup x f = None.
Proof.
  intros A x v f Hcanon.
  destruct (lookup x f) eqn:Hlookup.
  - pose proof (lookup_some_in_keys A f x a Hlookup) as Hin.
    pose proof (canonical_finfun_head_lt A x v f x Hcanon Hin) as Hlt.
    lia.
  - reflexivity.
Qed.

Theorem canonical_finfun_lookup_extensional :
  forall A (f g : finfun A),
    canonical_finfun f ->
    canonical_finfun g ->
    (forall x, lookup x f = lookup x g) ->
    f = g.
Proof.
  intros A f.
  induction f as [|[x a] fs IH]; intros g Hf Hg Hext.
  - destruct g as [|[y b] gs].
    + reflexivity.
    + specialize (Hext y). simpl in Hext.
      destruct (Nat.eq_dec y y) as [_ | Hbad]; [discriminate Hext | contradiction].
  - destruct g as [|[y b] gs].
    + specialize (Hext x). simpl in Hext.
      destruct (Nat.eq_dec x x) as [_ | Hbad]; [discriminate Hext | contradiction].
    + assert (Hxy : x = y).
      {
        pose proof (Hext x) as Hextx.
        simpl in Hextx.
        destruct (Nat.eq_dec x x) as [_ | Hbad]; [|contradiction].
        destruct (Nat.eq_dec x y) as [Hxy | Hxy].
        - exact Hxy.
        - assert (Hinx : In x (map fst gs)).
          { apply lookup_some_in_keys with (v := a). symmetry. exact Hextx. }
          pose proof (canonical_finfun_head_lt A y b gs x Hg Hinx) as Hyx.
          pose proof (Hext y) as Hexty.
          simpl in Hexty.
          destruct (Nat.eq_dec y x) as [Hyx_eq | Hyx_neq]; [subst; contradiction |].
          destruct (Nat.eq_dec y y) as [_ | Hbad]; [|contradiction].
          assert (Hiny : In y (map fst fs)).
          { apply lookup_some_in_keys with (v := b). exact Hexty. }
          pose proof (canonical_finfun_head_lt A x a fs y Hf Hiny) as Hxylt.
          lia.
      }
      subst y.
      assert (Hab : a = b).
      {
        pose proof (Hext x) as Hextx.
        simpl in Hextx.
        destruct (Nat.eq_dec x x) as [_ | Hbad]; [|contradiction].
        destruct (Nat.eq_dec x x) as [_ | Hbad]; [|contradiction].
        injection Hextx. intro Hab. exact Hab.
      }
      subst b.
      f_equal.
      apply IH.
      * apply canonical_finfun_tail with (x := x) (v := a). exact Hf.
      * apply canonical_finfun_tail with (x := x) (v := a). exact Hg.
      * intros z.
        pose proof (Hext z) as Hextz.
        simpl in Hextz.
        destruct (Nat.eq_dec z x) as [Hzx | Hzx].
        -- subst z.
           rewrite (lookup_canonical_tail_head_none A x a fs Hf).
           rewrite (lookup_canonical_tail_head_none A x a gs Hg).
           reflexivity.
        -- destruct (Nat.eq_dec z x) as [Hbad | _]; [contradiction |].
           exact Hextz.
Qed.

Record finite_coding_layer : Type := {
  coding_finset : finset -> Prop;
  coding_finfun : forall A : Type, finfun A -> Prop;
  coding_union : finset -> finset -> finset;
  coding_inter : finset -> finset -> finset;
  coding_diff : finset -> finset -> finset;
  coding_update : forall A : Type, nat -> A -> finfun A -> finfun A;
  coding_finset_nodup :
    forall s, coding_finset s -> NoDup s;
  coding_finset_extensional :
    forall s t,
      coding_finset s ->
      coding_finset t ->
      (forall x, In x s <-> In x t) ->
      s = t;
  coding_union_spec :
    forall x s t, In x (coding_union s t) <-> In x s \/ In x t;
  coding_inter_spec :
    forall x s t, In x (coding_inter s t) <-> In x s /\ In x t;
  coding_diff_spec :
    forall x s t, In x (coding_diff s t) <-> In x s /\ ~ In x t;
  coding_union_preserves :
    forall s t,
      coding_finset s -> coding_finset t ->
      coding_finset (coding_union s t);
  coding_inter_preserves :
    forall s t,
      coding_finset s -> coding_finset t ->
      coding_finset (coding_inter s t);
  coding_diff_preserves :
    forall s t,
      coding_finset s -> coding_finset t ->
      coding_finset (coding_diff s t);
  coding_finfun_nodup_keys :
    forall A (f : finfun A),
      coding_finfun A f -> NoDup (map fst f);
  coding_finfun_lookup_extensional :
    forall A (f g : finfun A),
      coding_finfun A f ->
      coding_finfun A g ->
      (forall x, lookup x f = lookup x g) ->
      f = g;
  coding_update_hit :
    forall A (x : nat) (v : A) f,
      lookup x (coding_update A x v f) = Some v;
  coding_update_miss :
    forall A (x y : nat) (v : A) f,
      x <> y -> lookup x (coding_update A y v f) = lookup x f;
  coding_update_preserves :
    forall A (x : nat) (v : A) f,
      coding_finfun A f ->
      coding_finfun A (coding_update A x v f)
}.

Definition canonical_finite_coding_layer : finite_coding_layer := {|
  coding_finset := canonical_finset;
  coding_finfun := @canonical_finfun;
  coding_union := finset_union;
  coding_inter := finset_inter;
  coding_diff := finset_diff;
  coding_update := @canonical_update;
  coding_finset_nodup := canonical_finset_nodup;
  coding_finset_extensional := canonical_finset_extensional;
  coding_union_spec := finset_union_spec;
  coding_inter_spec := finset_inter_spec;
  coding_diff_spec := finset_diff_spec;
  coding_union_preserves := finset_union_preserves_canonical;
  coding_inter_preserves := finset_inter_preserves_canonical;
  coding_diff_preserves := finset_diff_preserves_canonical;
  coding_finfun_nodup_keys := canonical_finfun_nodup_keys;
  coding_finfun_lookup_extensional := canonical_finfun_lookup_extensional;
  coding_update_hit := lookup_canonical_update_hit;
  coding_update_miss := lookup_canonical_update_miss;
  coding_update_preserves := canonical_update_preserves
|}.

Inductive instr : Type :=
| Ret : nat -> instr
| Jmp : nat -> instr
| Ctx : nat -> nat -> list nat -> nat -> instr
| Arr : code -> list nat -> nat -> instr
| App : nat -> nat -> nat -> instr
| Comb : nat -> list nat -> nat -> instr
| Quote : nat -> nat -> instr
| Beq : nat -> nat -> nat -> nat -> instr
| Btag : nat -> nat -> nat -> nat -> instr
| Call : code -> list nat -> nat -> instr.

Definition instr_kind (I : instr) : nat :=
  match I with
  | Ret _ => tuple1 0
  | Jmp _ => tuple1 1
  | Ctx a _ _ _ => tuple2 2 a
  | Arr _ _ _ => tuple1 3
  | App _ _ _ => tuple1 4
  | Comb _ _ _ => tuple1 5
  | Quote _ _ => tuple1 6
  | Beq _ _ _ _ => tuple1 7
  | Btag _ h _ _ => tuple2 8 h
  | Call _ _ _ => tuple1 9
  end.

Inductive cval : Type :=
| CtxVal : nat -> nat -> list cval -> cval
| ArrVal : code -> list cval -> cval.

Definition top (v : cval) : nat :=
  match v with
  | CtxVal a _ _ => tuple2 0 a
  | ArrVal _ _ => tuple2 1 0
  end.

Definition reg := finfun cval.

Fixpoint lookup_values (eta : reg) (rs : list nat) : option (list cval) :=
  match rs with
  | [] => Some []
  | r :: rest =>
      match lookup r eta, lookup_values eta rest with
      | Some v, Some vs => Some (v :: vs)
      | _, _ => None
      end
  end.

Definition entry_reg (vs : list cval) : reg := combine (seq 0 (length vs)) vs.

Record frame : Type := Fr {
  fr_prog : code;
  fr_pc : nat;
  fr_dest : nat;
  fr_reg : reg
}.

Record state : Type := St {
  st_prog : code;
  st_pc : nat;
  st_reg : reg;
  st_stack : list frame
}.

Inductive step (Body : code -> list instr) (q_atom c_atom : nat) :
    state -> state -> Prop :=
| StepRet :
    forall p l eta p' l' j eta' kappa i v,
      nth_error (Body p) l = Some (Ret i) ->
      lookup i eta = Some v ->
      step Body q_atom c_atom
        (St p l eta (Fr p' l' j eta' :: kappa))
        (St p' l' (update j v eta') kappa)
| StepJmp :
    forall p l eta kappa l',
      nth_error (Body p) l = Some (Jmp l') ->
      l' < length (Body p) ->
      step Body q_atom c_atom
        (St p l eta kappa)
        (St p l' eta kappa)
| StepCtx :
    forall p l eta kappa a c rs j vs,
      nth_error (Body p) l = Some (Ctx a c rs j) ->
      lookup_values eta rs = Some vs ->
      S l < length (Body p) ->
      step Body q_atom c_atom
        (St p l eta kappa)
        (St p (S l) (update j (CtxVal a c vs) eta) kappa)
| StepArr :
    forall p l eta kappa q rs j vs,
      nth_error (Body p) l = Some (Arr q rs j) ->
      lookup_values eta rs = Some vs ->
      S l < length (Body p) ->
      step Body q_atom c_atom
        (St p l eta kappa)
        (St p (S l) (update j (ArrVal q vs) eta) kappa)
| StepApp :
    forall p l eta kappa i j k q closed arg,
      nth_error (Body p) l = Some (App i j k) ->
      lookup i eta = Some (ArrVal q closed) ->
      lookup j eta = Some arg ->
      0 < length (Body q) ->
      S l < length (Body p) ->
      step Body q_atom c_atom
        (St p l eta kappa)
        (St q 0 (entry_reg (arg :: closed)) (Fr p (S l) k eta :: kappa))
| StepComb :
    forall p l eta kappa c rs j vs,
      nth_error (Body p) l = Some (Comb c rs j) ->
      lookup_values eta rs = Some vs ->
      S l < length (Body p) ->
      step Body q_atom c_atom
        (St p l eta kappa)
        (St p (S l) (update j (CtxVal c_atom c vs) eta) kappa)
| StepQuote :
    forall p l eta kappa i j v,
      nth_error (Body p) l = Some (Quote i j) ->
      lookup i eta = Some v ->
      S l < length (Body p) ->
      step Body q_atom c_atom
        (St p l eta kappa)
        (St p (S l) (update j (CtxVal q_atom (top v) []) eta) kappa)
| StepBeqTrue :
    forall p l eta kappa i j l0 l1 v,
      nth_error (Body p) l = Some (Beq i j l0 l1) ->
      lookup i eta = Some v ->
      lookup j eta = Some v ->
      l0 < length (Body p) ->
      l1 < length (Body p) ->
      step Body q_atom c_atom (St p l eta kappa) (St p l0 eta kappa)
| StepBeqFalse :
    forall p l eta kappa i j l0 l1 vi vj,
      nth_error (Body p) l = Some (Beq i j l0 l1) ->
      lookup i eta = Some vi ->
      lookup j eta = Some vj ->
      vi <> vj ->
      l0 < length (Body p) ->
      l1 < length (Body p) ->
      step Body q_atom c_atom (St p l eta kappa) (St p l1 eta kappa)
| StepBtagTrue :
    forall p l eta kappa i h l0 l1 v,
      nth_error (Body p) l = Some (Btag i h l0 l1) ->
      lookup i eta = Some v ->
      top v = h ->
      l0 < length (Body p) ->
      l1 < length (Body p) ->
      step Body q_atom c_atom (St p l eta kappa) (St p l0 eta kappa)
| StepBtagFalse :
    forall p l eta kappa i h l0 l1 v,
      nth_error (Body p) l = Some (Btag i h l0 l1) ->
      lookup i eta = Some v ->
      top v <> h ->
      l0 < length (Body p) ->
      l1 < length (Body p) ->
      step Body q_atom c_atom (St p l eta kappa) (St p l1 eta kappa)
| StepCall :
    forall p l eta kappa q rs j vs,
      nth_error (Body p) l = Some (Call q rs j) ->
      lookup_values eta rs = Some vs ->
      0 < length (Body q) ->
      S l < length (Body p) ->
      step Body q_atom c_atom
        (St p l eta kappa)
        (St q 0 (entry_reg vs) (Fr p (S l) j eta :: kappa)).

Theorem step_has_current_instruction :
  forall Body q_atom c_atom s t,
    step Body q_atom c_atom s t ->
    exists I, nth_error (Body (st_prog s)) (st_pc s) = Some I.
Proof.
  intros Body q_atom c_atom s t H.
  inversion H; subst; eexists; eassumption.
Qed.

Inductive steps (Body : code -> list instr) (q_atom c_atom : nat) :
    nat -> state -> state -> Prop :=
| Steps0 : forall s, steps Body q_atom c_atom 0 s s
| StepsS :
    forall m s u t,
      step Body q_atom c_atom s u ->
      steps Body q_atom c_atom m u t ->
      steps Body q_atom c_atom (S m) s t.

Definition steps_star Body q_atom c_atom s t : Prop :=
  exists m, steps Body q_atom c_atom m s t.

Inductive out_c (Body : code -> list instr) : state -> cval -> Prop :=
| OutC :
    forall p l eta i w,
      nth_error (Body p) l = Some (Ret i) ->
      lookup i eta = Some w ->
      out_c Body (St p l eta []) w.

Definition eval_c Body q_atom c_atom p inputs w : Prop :=
  0 < length (Body p) /\
  exists m t,
    steps Body q_atom c_atom m (St p 0 (entry_reg inputs) []) t /\
    out_c Body t w.

Definition eval_clos Body q_atom c_atom v x w : Prop :=
  exists p closed,
    v = ArrVal p closed /\
    eval_c Body q_atom c_atom p (x :: closed) w.

Inductive ty : Type :=
| Base : nat -> ty
| Arrow : ty -> ty -> ty.

Definition pos := list bool.
Definition dom_pos (p : pos) : pos := p ++ [false].
Definition cod_pos (p : pos) : pos := p ++ [true].

Fixpoint subty (tau : ty) (p : pos) : option ty :=
  match p with
  | [] => Some tau
  | false :: rest =>
      match tau with
      | Arrow sigma _ => subty sigma rest
      | Base _ => None
      end
  | true :: rest =>
      match tau with
      | Arrow _ rho => subty rho rest
      | Base _ => None
      end
  end.

Definition is_pos (tau : ty) (p : pos) : Prop :=
  exists theta, subty tau p = Some theta.

Theorem root_is_pos : forall tau, is_pos tau [].
Proof.
  intros tau. unfold is_pos. exists tau. destruct tau; reflexivity.
Qed.

Theorem subty_arrow_dom :
  forall sigma rho p, subty (Arrow sigma rho) (false :: p) = subty sigma p.
Proof. reflexivity. Qed.

Theorem subty_arrow_cod :
  forall sigma rho p, subty (Arrow sigma rho) (true :: p) = subty rho p.
Proof. reflexivity. Qed.

Record decl : Type := Dec {
  dec_prog : code;
  dec_args : list pos;
  dec_ret : pos
}.

Definition tyenv := finfun pos.

Definition env_has (Gamma : tyenv) (i : nat) (p : pos) : Prop :=
  lookup i Gamma = Some p.

Definition env_has_all (Gamma : tyenv) (rs : list nat) : Prop :=
  Forall (fun r => exists p, lookup r Gamma = Some p) rs.

Definition dec_in (d : decl) (D : list decl) : Prop := In d D.

Inductive instr_preserves (Body : code -> list instr) (tau : ty)
    (D : list decl) (q l : nat) (Gamma : tyenv) (b : pos) : instr -> Prop :=
| PreserveRet :
    forall i,
      env_has Gamma i b ->
      instr_preserves Body tau D q l Gamma b (Ret i)
| PreserveJmp :
    forall l',
      l' < length (Body q) ->
      instr_preserves Body tau D q l Gamma b (Jmp l')
| PreserveCtx :
    forall a c rs j p,
      env_has_all Gamma rs ->
      S l < length (Body q) ->
      subty tau p = Some (Base a) ->
      instr_preserves Body tau D q l Gamma b (Ctx a c rs j)
| PreserveArr :
    forall q' rs j p sigma rho,
      env_has_all Gamma rs ->
      S l < length (Body q) ->
      subty tau p = Some (Arrow sigma rho) ->
      dec_in (Dec q' (dom_pos p :: map snd Gamma) (cod_pos p)) D ->
      instr_preserves Body tau D q l Gamma b (Arr q' rs j)
| PreserveApp :
    forall i j k p sigma rho,
      env_has Gamma i p ->
      subty tau p = Some (Arrow sigma rho) ->
      env_has Gamma j (dom_pos p) ->
      S l < length (Body q) ->
      instr_preserves Body tau D q l Gamma b (App i j k)
| PreserveComb :
    forall c rs j p,
      env_has_all Gamma rs ->
      S l < length (Body q) ->
      subty tau p = Some (Base c) ->
      instr_preserves Body tau D q l Gamma b (Comb c rs j)
| PreserveQuote :
    forall i j p,
      (exists pi, env_has Gamma i pi) ->
      S l < length (Body q) ->
      subty tau p = Some (Base 0) ->
      instr_preserves Body tau D q l Gamma b (Quote i j)
| PreserveBeq :
    forall i j l0 l1,
      (exists pi, env_has Gamma i pi) ->
      (exists pj, env_has Gamma j pj) ->
      l0 < length (Body q) ->
      l1 < length (Body q) ->
      instr_preserves Body tau D q l Gamma b (Beq i j l0 l1)
| PreserveBtag :
    forall i h l0 l1,
      (exists pi, env_has Gamma i pi) ->
      l0 < length (Body q) ->
      l1 < length (Body q) ->
      instr_preserves Body tau D q l Gamma b (Btag i h l0 l1)
| PreserveCall :
    forall q' rs j b',
      env_has_all Gamma rs ->
      S l < length (Body q) ->
      dec_in (Dec q' (map snd Gamma) b') D ->
      instr_preserves Body tau D q l Gamma b (Call q' rs j).

Record type_certificate (Body : code -> list instr) (e : code) (tau : ty) : Type := {
  cert_decls : list decl;
  cert_envs : finfun tyenv;
  cert_edges : list (decl * decl);
  cert_rank : nat;
  cert_root :
    match tau with
    | Base _ => In (Dec e [] []) cert_decls
    | Arrow _ _ => In (Dec e [[false]] [true]) cert_decls
    end;
  cert_entry_env :
    forall d,
      In d cert_decls ->
      exists Gamma,
        lookup (pair_code (dec_prog d) 0) cert_envs = Some Gamma /\
        map snd Gamma = dec_args d;
  cert_instr :
    forall d l Gamma I,
      In d cert_decls ->
      lookup (pair_code (dec_prog d) l) cert_envs = Some Gamma ->
      nth_error (Body (dec_prog d)) l = Some I ->
      instr_preserves Body tau cert_decls (dec_prog d) l Gamma (dec_ret d) I;
  cert_edges_sound :
    forall d d',
      In (d, d') cert_edges -> In d cert_decls /\ In d' cert_decls;
  cert_reachable :
    forall d,
      In d cert_decls ->
      d = match tau with
          | Base _ => Dec e [] []
          | Arrow _ _ => Dec e [[false]] [true]
          end \/
      exists root, In root cert_decls /\ clos_refl_trans decl (fun x y => In (x, y) cert_edges) root d
}.

Record legal_input (Body : code -> list instr) (e : code) (tau : ty) : Type := {
  legal_certificate : type_certificate Body e tau;
  legal_minimal :
    forall C : type_certificate Body e tau,
      cert_rank Body e tau legal_certificate <= cert_rank Body e tau C
}.

Record obs_layer : Type := {
  Obs : ty -> nat -> nat -> Prop;
  Pr : ty -> nat -> nat -> Prop;
  Sat : cval -> ty -> nat -> nat -> Prop;
  obs_finite : forall theta n, exists xs, forall o, Obs theta n o -> In o xs;
  pr_finite : forall theta n, exists xs, forall q, Pr theta n q -> In q xs;
  pr_nonempty : forall theta n, exists q, Pr theta n q;
  bottom : ty -> nat -> nat;
  bottom_fresh : forall theta n, ~ Obs theta n (bottom theta n)
}.

Definition cut_nat (n m : nat) : nat :=
  if Nat.leb m n then m else S n.

Definition trunc_code (n d : nat) (v : cval) : nat :=
  if Nat.leb n d then tuple1 0 else tuple2 (cut_nat n (top v)) d.

Fixpoint ty_size (theta : ty) : nat :=
  match theta with
  | Base _ => 1
  | Arrow sigma rho => S (ty_size sigma + ty_size rho)
  end.

Definition obs_bound (theta : ty) (n : nat) : nat :=
  S (n + ty_size theta).

Definition pr_bound (theta : ty) (n : nat) : nat :=
  S (n + ty_size theta + ty_size theta).

Definition concrete_obs (theta : ty) (n o : nat) : Prop :=
  o <= obs_bound theta n.

Definition concrete_pr (theta : ty) (n q : nat) : Prop :=
  q <= pr_bound theta n.

Definition concrete_obs_code (theta : ty) (n : nat) (v : cval) : nat :=
  cut_nat (obs_bound theta n) (trunc_code n 0 v).

Definition concrete_sat (v : cval) (theta : ty) (n o : nat) : Prop :=
  o = concrete_obs_code theta n v.

Definition concrete_bottom (theta : ty) (n : nat) : nat :=
  S (obs_bound theta n).

Lemma concrete_obs_finite :
  forall theta n, exists xs, forall o, concrete_obs theta n o -> In o xs.
Proof.
  intros theta n.
  exists (seq 0 (S (obs_bound theta n))).
  intros o Ho.
  unfold concrete_obs in Ho.
  rewrite in_seq.
  split; lia.
Qed.

Lemma concrete_pr_finite :
  forall theta n, exists xs, forall q, concrete_pr theta n q -> In q xs.
Proof.
  intros theta n.
  exists (seq 0 (S (pr_bound theta n))).
  intros q Hq.
  unfold concrete_pr in Hq.
  rewrite in_seq.
  split; lia.
Qed.

Lemma concrete_pr_nonempty :
  forall theta n, exists q, concrete_pr theta n q.
Proof.
  intros theta n.
  exists 0.
  unfold concrete_pr.
  lia.
Qed.

Lemma concrete_bottom_fresh :
  forall theta n, ~ concrete_obs theta n (concrete_bottom theta n).
Proof.
  intros theta n H.
  unfold concrete_obs, concrete_bottom in H.
  lia.
Qed.

Definition canonical_obs_layer : obs_layer := {|
  Obs := concrete_obs;
  Pr := concrete_pr;
  Sat := concrete_sat;
  obs_finite := concrete_obs_finite;
  pr_finite := concrete_pr_finite;
  pr_nonempty := concrete_pr_nonempty;
  bottom := concrete_bottom;
  bottom_fresh := concrete_bottom_fresh
|}.

Definition SObs (O : obs_layer) theta n o : Prop :=
  o = bottom O theta n \/ Obs O theta n o.

Definition SatSt (O : obs_layer) v theta n o : Prop :=
  o = bottom O theta n \/ (Obs O theta n o /\ Sat O v theta n o).

Theorem SObs_finite :
  forall O theta n, exists xs, forall o, SObs O theta n o -> In o xs.
Proof.
  intros O theta n.
  destruct (obs_finite O theta n) as [xs Hxs].
  exists (bottom O theta n :: xs).
  intros o [Ho | Ho]; subst; simpl; auto.
Qed.


Definition probe_table := finfun nat.

Definition probe_table_ok
    (O : obs_layer) (sigma rho : ty) (n : nat) (tbl : probe_table) : Prop :=
  canonical_finfun tbl /\
  forall q o,
    lookup q tbl = Some o ->
    Pr O sigma n q /\ Obs O rho n o.

Definition ProbeCode (tbl : probe_table) : probe_table := tbl.

Theorem ProbeCode_correct :
  forall O sigma rho n tbl,
    probe_table_ok O sigma rho n tbl ->
    probe_table_ok O sigma rho n (ProbeCode tbl).
Proof.
  intros O sigma rho n tbl H. exact H.
Qed.

Definition arrow_obs_code_from_table (tbl : probe_table) : nat :=
  fold_right pair_code 0 (map snd tbl).

Definition arrow_observation_exact
    (O : obs_layer) (sigma rho : ty) (n : nat)
    (tbl : probe_table) (obs : nat) : Prop :=
  probe_table_ok O sigma rho n tbl /\ obs = arrow_obs_code_from_table tbl.

Theorem arrow_observation_exact_intro :
  forall O sigma rho n tbl,
    probe_table_ok O sigma rho n tbl ->
    arrow_observation_exact O sigma rho n tbl (arrow_obs_code_from_table tbl).
Proof.
  intros O sigma rho n tbl H.
  split; [exact H|reflexivity].
Qed.

Record system_data : Type := {
  finite_coding : finite_coding_layer;
  Body : code -> list instr;
  q_atom : nat;
  c_atom : nat;
  q_c_distinct : q_atom <> c_atom
}.

Definition ObsPr (_ : system_data) : obs_layer := canonical_obs_layer.

Inductive tm : Type :=
| TmVar : nat -> tm
| TmVal : cval -> tm
| TmRoot : tm
| TmPort : nat -> nat -> tm
| TmCtx : nat -> nat -> list tm -> tm
| TmArr : code -> list tm -> tm
| TmApp : tm -> nat -> nat -> tm
| TmComb : nat -> list tm -> tm
| TmQuote : tm -> tm.

Fixpoint tm_subst (t : tm) (i : nat) (u : tm) : tm :=
  match t with
  | TmVar j => if Nat.eq_dec i j then u else TmVar j
  | TmVal v => TmVal v
  | TmRoot => TmRoot
  | TmPort x j => TmPort x j
  | TmCtx a c ss => TmCtx a c (map (fun s => tm_subst s i u) ss)
  | TmArr p ss => TmArr p (map (fun s => tm_subst s i u) ss)
  | TmApp t0 n q => TmApp (tm_subst t0 i u) n q
  | TmComb c ss => TmComb c (map (fun s => tm_subst s i u) ss)
  | TmQuote t0 => TmQuote (tm_subst t0 i u)
  end.

Theorem tm_subst_hit :
  forall i u, tm_subst (TmVar i) i u = u.
Proof.
  intros i u. simpl. destruct (Nat.eq_dec i i); congruence.
Qed.

Theorem tm_subst_miss :
  forall i j u, i <> j -> tm_subst (TmVar j) i u = TmVar j.
Proof.
  intros i j u H. simpl. destruct (Nat.eq_dec i j); congruence.
Qed.


Theorem tm_subst_val :
  forall v i u, tm_subst (TmVal v) i u = TmVal v.
Proof.
  reflexivity.
Qed.

Theorem tm_subst_root :
  forall i u, tm_subst TmRoot i u = TmRoot.
Proof.
  reflexivity.
Qed.

Theorem tm_subst_port :
  forall x j i u, tm_subst (TmPort x j) i u = TmPort x j.
Proof.
  reflexivity.
Qed.

Theorem tm_subst_ctx :
  forall a c args i u,
    tm_subst (TmCtx a c args) i u =
    TmCtx a c (map (fun s => tm_subst s i u) args).
Proof.
  reflexivity.
Qed.

Theorem tm_subst_arr :
  forall p args i u,
    tm_subst (TmArr p args) i u =
    TmArr p (map (fun s => tm_subst s i u) args).
Proof.
  reflexivity.
Qed.

Theorem tm_subst_app :
  forall t n q i u,
    tm_subst (TmApp t n q) i u = TmApp (tm_subst t i u) n q.
Proof.
  reflexivity.
Qed.

Theorem tm_subst_comb :
  forall c args i u,
    tm_subst (TmComb c args) i u =
    TmComb c (map (fun s => tm_subst s i u) args).
Proof.
  reflexivity.
Qed.

Theorem tm_subst_quote :
  forall t i u,
    tm_subst (TmQuote t) i u = TmQuote (tm_subst t i u).
Proof.
  reflexivity.
Qed.
Inductive judg : Type :=
| JProbe : pos -> nat -> nat -> judg
| JObs : pos -> tm -> nat -> nat -> judg
| JApp : pos -> tm -> nat -> nat -> tm -> judg
| JFunObs : pos -> tm -> nat -> nat -> nat -> judg
| JEq : pos -> tm -> tm -> nat -> judg
| JSub : pos -> tm -> nat -> tm -> tm -> judg
| JState : nat -> nat -> nat -> judg
| JRw : nat -> nat -> nat -> nat -> judg.

Definition judg_tag (J : judg) : nat :=
  match J with
  | JProbe _ _ _ => 0
  | JObs _ _ _ _ => 1
  | JApp _ _ _ _ _ => 2
  | JFunObs _ _ _ _ _ => 3
  | JEq _ _ _ _ => 4
  | JSub _ _ _ _ _ => 5
  | JState _ _ _ => 6
  | JRw _ _ _ _ => 7
  end.

Record rule : Type := MkRule {
  premises : list judg;
  conclusion : judg
}.

Inductive skel_rule (O : obs_layer) (tau : ty) : rule -> Prop :=
| SkProbe :
    forall p theta n q,
      subty tau p = Some theta ->
      Pr O theta n q ->
      skel_rule O tau (MkRule [] (JProbe p n q))
| SkValObs :
    forall p theta n v o,
      subty tau p = Some theta ->
      Obs O theta n o ->
      Sat O v theta n o ->
      skel_rule O tau (MkRule [] (JObs p (TmVal v) n o))
| SkSubComputed :
    forall p theta t i u,
      subty tau p = Some theta ->
      skel_rule O tau (MkRule [] (JSub p t i u (tm_subst t i u)))
| SkEqRefl :
    forall p theta t n,
      subty tau p = Some theta ->
      skel_rule O tau (MkRule [] (JEq p t t n))
| SkEqSym :
    forall p t u n,
      skel_rule O tau
        (MkRule [JEq p t u n] (JEq p u t n))
| SkEqTrans :
    forall p t u w n,
      skel_rule O tau
        (MkRule [JEq p t u n; JEq p u w n] (JEq p t w n))
| SkFiniteObsEq :
    forall p theta t u n os,
      subty tau p = Some theta ->
      Forall (fun o => exists m, m <= n /\ Obs O theta m o) os ->
      skel_rule O tau
        (MkRule (flat_map (fun o => [JObs p t n o; JObs p u n o]) os)
                (JEq p t u n))
| SkAppToFunObs :
    forall p sigma rho t n q u o,
      subty tau p = Some (Arrow sigma rho) ->
      Pr O sigma n q ->
      Obs O rho n o ->
      skel_rule O tau
        (MkRule [JProbe (dom_pos p) n q; JApp p t n q u; JObs (cod_pos p) u n o]
                (JFunObs p t n q o))
| SkArrowObs :
    forall p sigma rho t n phi probes,
      subty tau p = Some (Arrow sigma rho) ->
      Forall (Pr O sigma n) probes ->
      Forall (fun q => Obs O rho n (phi q)) probes ->
      skel_rule O tau
        (MkRule (map (fun q => JFunObs p t n q (phi q)) probes)
                (JObs p t n (fold_right pair_code 0 (map phi probes)))).

Inductive exp : Type :=
| BaseExp : pos -> nat -> exp
| ArrExp : pos -> nat -> nat -> exp -> exp.

Inductive action : Type :=
| ActObs : pos -> tm -> nat -> nat -> action
| ActApp : pos -> tm -> nat -> nat -> tm -> action.

Inductive edge_trace (S : system_data) : state -> list (state * state) -> state -> Prop :=
| EdgeTraceNil : forall s, edge_trace S s [] s
| EdgeTraceCons :
    forall s u t T,
      step (Body S) (q_atom S) (c_atom S) s u ->
      edge_trace S u T t ->
      edge_trace S s ((s, u) :: T) t.

Inductive prefix_edge_trace (S : system_data) : state -> nat -> list (state * state) -> Prop :=
| PrefixTraceZero : forall s, prefix_edge_trace S s 0 []
| PrefixTraceSucc :
    forall s u k T,
      step (Body S) (q_atom S) (c_atom S) s u ->
      prefix_edge_trace S u k T ->
      prefix_edge_trace S s (Datatypes.S k) ((s, u) :: T).

Inductive run_exp_down (S : system_data) (tau : ty) :
    pos -> tm -> cval -> nat -> exp -> list (state * state) -> list action -> Prop :=
| RunBaseDown :
    forall p a t v n o,
      subty tau p = Some (Base a) ->
      Sat (ObsPr S) v (Base a) n o ->
      run_exp_down S tau p t v n (BaseExp p n) [] [ActObs p t n o]
| RunArrowDown :
    forall p sigma rho t n q E' r closed x s0 T sm w t' R A,
      subty tau p = Some (Arrow sigma rho) ->
      Pr (ObsPr S) sigma n q ->
      x = CtxVal q 0 [] ->
      0 < length (Body S r) ->
      s0 = St r 0 (entry_reg (x :: closed)) [] ->
      edge_trace S s0 T sm ->
      out_c (Body S) sm w ->
      t' = TmApp t n q ->
      run_exp_down S tau (cod_pos p) t' w n E' R A ->
      run_exp_down S tau p t (ArrVal r closed) n (ArrExp p n q E') (T ++ R)
        (ActApp p t n q t' :: A).

Inductive root_run_down (S : system_data) (tau : ty) (e : code) :
    nat -> exp -> list (state * state) -> list action -> Prop :=
| RootBaseDown :
    forall a n T sm w R A,
      tau = Base a ->
      0 < length (Body S e) ->
      edge_trace S (St e 0 (entry_reg []) []) T sm ->
      out_c (Body S) sm w ->
      run_exp_down S tau [] TmRoot w n (BaseExp [] n) R A ->
      root_run_down S tau e n (BaseExp [] n) (T ++ R) A
| RootArrowDown :
    forall sigma rho n E R A,
      tau = Arrow sigma rho ->
      run_exp_down S tau [] TmRoot (ArrVal e []) n E R A ->
      root_run_down S tau e n E R A.

Inductive run_exp_prefix (S : system_data) (tau : ty) :
    pos -> tm -> cval -> nat -> exp -> list (state * state) -> Prop :=
| RunBasePrefix :
    forall p a t v n,
      subty tau p = Some (Base a) ->
      run_exp_prefix S tau p t v n (BaseExp p n) []
| RunArrowPrefixHere :
    forall p sigma rho t n q E' r closed x s0 k R,
      subty tau p = Some (Arrow sigma rho) ->
      Pr (ObsPr S) sigma n q ->
      x = CtxVal q 0 [] ->
      0 < length (Body S r) ->
      s0 = St r 0 (entry_reg (x :: closed)) [] ->
      prefix_edge_trace S s0 k R ->
      run_exp_prefix S tau p t (ArrVal r closed) n (ArrExp p n q E') R
| RunArrowPrefixLater :
    forall p sigma rho t n q E' r closed x s0 T sm w t' R',
      subty tau p = Some (Arrow sigma rho) ->
      Pr (ObsPr S) sigma n q ->
      x = CtxVal q 0 [] ->
      0 < length (Body S r) ->
      s0 = St r 0 (entry_reg (x :: closed)) [] ->
      edge_trace S s0 T sm ->
      out_c (Body S) sm w ->
      t' = TmApp t n q ->
      run_exp_prefix S tau (cod_pos p) t' w n E' R' ->
      run_exp_prefix S tau p t (ArrVal r closed) n (ArrExp p n q E') (T ++ R').

Inductive root_run_prefix (S : system_data) (tau : ty) (e : code) :
    nat -> exp -> list (state * state) -> Prop :=
| RootBasePrefixHere :
    forall a n k R,
      tau = Base a ->
      0 < length (Body S e) ->
      prefix_edge_trace S (St e 0 (entry_reg []) []) k R ->
      root_run_prefix S tau e n (BaseExp [] n) R
| RootBasePrefixLater :
    forall a n T sm w R',
      tau = Base a ->
      0 < length (Body S e) ->
      edge_trace S (St e 0 (entry_reg []) []) T sm ->
      out_c (Body S) sm w ->
      run_exp_prefix S tau [] TmRoot w n (BaseExp [] n) R' ->
      root_run_prefix S tau e n (BaseExp [] n) (T ++ R')
| RootArrowPrefix :
    forall sigma rho n E R,
      tau = Arrow sigma rho ->
      run_exp_prefix S tau [] TmRoot (ArrVal e []) n E R ->
      root_run_prefix S tau e n E R.

Inductive role : Type :=
| Epsilon | MkCtxRole : nat -> role | MkArrRole | MkCombRole | QuoteRole
| AppOwn | AppExt | CallOwn | ReturnOwn | ReturnOut
| EqTrue | EqFalse | TagTrue | TagFalse.

Definition role_code (r : role) : nat :=
  match r with
  | Epsilon => tuple1 0
  | MkCtxRole a => tuple2 1 a
  | MkArrRole => tuple1 2
  | MkCombRole => tuple1 3
  | QuoteRole => tuple1 4
  | AppOwn => tuple1 5
  | AppExt => tuple1 6
  | CallOwn => tuple1 7
  | ReturnOwn => tuple1 8
  | ReturnOut => tuple1 9
  | EqTrue => tuple1 10
  | EqFalse => tuple1 11
  | TagTrue => tuple1 12
  | TagFalse => tuple1 13
  end.

Record trace_interface (S : system_data) (e : code) (tau : ty) : Type := {
  proto : state -> nat;
  edge_code : nat -> nat -> role -> nat;
  init_obs : nat -> nat -> nat -> Prop;
  edge_obs : nat -> nat -> nat -> nat -> Prop;
  act_inst : nat -> action -> Prop;
  edge_obs_witness :
    forall r n o o',
      edge_obs r n o o' ->
      exists E s s' R k,
        root_run_prefix S tau e n E R /\
        nth_error R k = Some (s, s') /\
        step (Body S) (q_atom S) (c_atom S) s s';
  init_obs_witness :
    forall u n o,
      init_obs u n o ->
      exists s, proto s = u;
  act_witness :
    forall n a,
      act_inst n a ->
      exists E R A,
        root_run_down S tau e n E R A /\ In a A
}.

Inductive trace_rule (S : system_data) (e : code) (tau : ty)
    (TI : trace_interface S e tau) : rule -> Prop :=
| TraceInit :
    forall u n o,
      init_obs S e tau TI u n o ->
      trace_rule S e tau TI (MkRule [] (JState u n o))
| TraceRewrite :
    forall r n o o',
      edge_obs S e tau TI r n o o' ->
      trace_rule S e tau TI (MkRule [] (JRw r n o o'))
| TraceAdvance :
    forall r u v lambda n o o',
      r = edge_code S e tau TI u v lambda ->
      edge_obs S e tau TI r n o o' ->
      trace_rule S e tau TI
        (MkRule [JState u n o; JRw r n o o'] (JState v n o'))
| TraceObserve :
    forall p t n o,
      act_inst S e tau TI n (ActObs p t n o) ->
      trace_rule S e tau TI (MkRule [] (JObs p t n o))
| TraceApply :
    forall p t n q u,
      act_inst S e tau TI n (ActApp p t n q u) ->
      trace_rule S e tau TI (MkRule [] (JApp p t n q u)).

Definition rules (S : system_data) (e : code) (tau : ty)
    (TI : trace_interface S e tau) (r : rule) : Prop :=
  skel_rule (ObsPr S) tau r \/ trace_rule S e tau TI r.

Inductive form : Type :=
| FAtom : judg -> form
| FNeg : form -> form
| FAnd : form -> form -> form
| FOr : form -> form -> form
| FImp : form -> form -> form
| FLocSeq : list form -> form -> form.

Inductive deriv (R : rule -> Prop) : judg -> Type :=
| DerivNode :
    forall ps c,
      R (MkRule ps c) ->
      deriv_list R ps ->
      deriv R c
with deriv_list (R : rule -> Prop) : list judg -> Type :=
| DNil : deriv_list R []
| DCons :
    forall j js,
      deriv R j ->
      deriv_list R js ->
      deriv_list R (j :: js).

Scheme deriv_ind' := Induction for deriv Sort Prop
with deriv_list_ind' := Induction for deriv_list Sort Prop.

Definition Syn S e tau TI (J : judg) : Type :=
  deriv (rules S e tau TI) J.

Definition judg_level (J : judg) : nat :=
  match J with
  | JProbe _ n _ => n
  | JObs _ _ n _ => n
  | JApp _ _ n _ _ => n
  | JFunObs _ _ n _ _ => n
  | JEq _ _ _ n => n
  | JSub _ _ _ _ _ => 0
  | JState _ n _ => n
  | JRw _ n _ _ => n
  end.

Definition judg_level_le (n : nat) (J : judg) : Prop :=
  judg_level J <= n.

Fixpoint deriv_tree_bounded
    (R : rule -> Prop) (n : nat) (J : judg) (d : deriv R J)
    {struct d} : Prop :=
  match d with
  | @DerivNode _ ps c _ ds =>
      judg_level_le n c /\ deriv_list_tree_bounded R n ps ds
  end
with deriv_list_tree_bounded
    (R : rule -> Prop) (n : nat) (ps : list judg) (ds : deriv_list R ps)
    {struct ds} : Prop :=
  match ds with
  | @DNil _ => True
  | @DCons _ j js d ds =>
      deriv_tree_bounded R n j d /\ deriv_list_tree_bounded R n js ds
  end.

Definition Syn_le S e tau TI (n : nat) (J : judg) : Type :=
  { d : Syn S e tau TI J & deriv_tree_bounded (rules S e tau TI) n J d }.

Definition DerivN := Syn_le.

Theorem DerivN_forget :
  forall S e tau TI n J, DerivN S e tau TI n J -> Syn S e tau TI J.
Proof.
  intros S e tau TI n J H. exact (projT1 H).
Qed.

Theorem deriv_tree_bounded_mono :
  forall R n m J (d : deriv R J),
    n <= m ->
    deriv_tree_bounded R n J d ->
    deriv_tree_bounded R m J d
with deriv_list_tree_bounded_mono :
  forall R n m ps (ds : deriv_list R ps),
    n <= m ->
    deriv_list_tree_bounded R n ps ds ->
    deriv_list_tree_bounded R m ps ds.
Proof.
  - intros R n m J d Hnm Hd.
    destruct d as [ps c Hr ds].
    simpl in Hd. destruct Hd as [Hc Hds].
    simpl. split.
    + unfold judg_level_le in *. lia.
    + apply (deriv_list_tree_bounded_mono R n m ps ds); assumption.
  - intros R n m ps ds Hnm Hds.
    destruct ds as [|j js d ds].
    + exact I.
    + simpl in Hds. destruct Hds as [Hd Hds].
      simpl. split.
      * apply (deriv_tree_bounded_mono R n m j d); assumption.
      * apply (deriv_list_tree_bounded_mono R n m js ds); assumption.
Qed.

Theorem DerivN_mono :
  forall S e tau TI n m J,
    n <= m ->
    DerivN S e tau TI n J ->
    DerivN S e tau TI m J.
Proof.
  intros S e tau TI n m J Hnm [d HJ].
  exists d.
  apply (deriv_tree_bounded_mono (rules S e tau TI) n m J d); assumption.
Qed.

Inductive obj : Type :=
| BoUnit : obj
| BoProbe : pos -> nat -> nat -> obj
| BoObs : pos -> tm -> nat -> nat -> obj
| BoApp : pos -> tm -> nat -> nat -> tm -> obj
| BoFunObs : pos -> tm -> nat -> nat -> nat -> obj
| BoEq : pos -> tm -> tm -> nat -> obj
| BoSub : pos -> tm -> nat -> tm -> tm -> obj
| BoState : nat -> nat -> nat -> obj
| BoRw : nat -> nat -> nat -> nat -> obj
| BoSeq : list obj -> obj.

Definition ObjSeq (xs : list obj) : obj :=
  match xs with
  | [] => BoUnit
  | _ => BoSeq xs
  end.

Definition ObjOfJudg (J : judg) : obj :=
  match J with
  | JProbe p n q => BoProbe p n q
  | JObs p t n o => BoObs p t n o
  | JApp p t n q u => BoApp p t n q u
  | JFunObs p t n q o => BoFunObs p t n q o
  | JEq p t u n => BoEq p t u n
  | JSub p t i u t' => BoSub p t i u t'
  | JState x n o => BoState x n o
  | JRw r n o o' => BoRw r n o o'
  end.

Definition PremObj (ps : list judg) : obj := ObjSeq (map ObjOfJudg ps).

Inductive mor (R : rule -> Prop) : obj -> obj -> Type :=
| MorId : forall A, mor R A A
| MorComp : forall A B C, mor R A B -> mor R B C -> mor R A C
| MorPairNil : mor R BoUnit BoUnit
| MorPairCons :
    forall A As,
      mor R BoUnit A ->
      mor R BoUnit (ObjSeq As) ->
      mor R BoUnit (ObjSeq (A :: As))
| MorRule :
    forall r,
      R r ->
      mor R (PremObj (premises r)) (ObjOfJudg (conclusion r)).

Arguments MorId {R} A.
Arguments MorComp {R A B C} _ _.
Arguments MorPairNil {R}.
Arguments MorPairCons {R A As} _ _.
Arguments MorRule {R} r _.

Fixpoint interp_deriv (R : rule -> Prop) (J : judg) (d : deriv R J)
    {struct d} : mor R BoUnit (ObjOfJudg J)
with interp_deriv_list (R : rule -> Prop) (js : list judg) (ds : deriv_list R js)
    {struct ds} : mor R BoUnit (PremObj js).
Proof.
  - destruct d as [ps c Hr ds].
    exact (MorComp (interp_deriv_list R ps ds) (MorRule (MkRule ps c) Hr)).
  - destruct ds as [|j js dj djs].
    + exact MorPairNil.
    + exact (MorPairCons (interp_deriv R j dj) (interp_deriv_list R js djs)).
Defined.

Definition rec_rule (r : rule) : list nat :=
  [length (premises r); judg_tag (conclusion r)].

Fixpoint SRec_deriv (R : rule -> Prop) (J : judg) (d : deriv R J)
    {struct d} : list nat
with SRec_deriv_list (R : rule -> Prop) (js : list judg) (ds : deriv_list R js)
    {struct ds} : list nat.
Proof.
  - destruct d as [ps c _ ds].
    exact (SRec_deriv_list R ps ds ++ rec_rule (MkRule ps c)).
  - destruct ds as [|j js dj djs].
    + exact [].
    + exact (SRec_deriv R j dj ++ SRec_deriv_list R js djs).
Defined.

Fixpoint BRec_mor (R : rule -> Prop) (A B : obj) (m : mor R A B)
    {struct m} : list nat :=
  match m with
  | MorId _ => []
  | MorComp m1 m2 => BRec_mor R _ _ m1 ++ BRec_mor R _ _ m2
  | MorPairNil => []
  | MorPairCons m1 m2 => BRec_mor R _ _ m1 ++ BRec_mor R _ _ m2
  | MorRule r _ => rec_rule r
  end.

Theorem interpretation_record_consistent :
  forall R J (d : deriv R J),
    SRec_deriv R J d = BRec_mor R BoUnit (ObjOfJudg J) (interp_deriv R J d).
Proof.
  intros R J d.
  induction d using deriv_ind' with
      (P0 := fun js ds =>
        SRec_deriv_list R js ds =
        BRec_mor R BoUnit (PremObj js) (interp_deriv_list R js ds)).
  - simpl. now rewrite IHd.
  - reflexivity.
  - simpl. now rewrite IHd, IHd0.
Qed.

Definition syn_equiv R J (A B : deriv R J) : Prop :=
  SRec_deriv R J A = SRec_deriv R J B.

Definition beh_equiv R J (A B : deriv R J) : Prop :=
  BRec_mor R BoUnit (ObjOfJudg J) (interp_deriv R J A) =
  BRec_mor R BoUnit (ObjOfJudg J) (interp_deriv R J B).

Theorem full_abstraction_for_records :
  forall R J (A B : deriv R J),
    syn_equiv R J A B <-> beh_equiv R J A B.
Proof.
  intros R J A B. unfold syn_equiv, beh_equiv.
  repeat rewrite <- interpretation_record_consistent.
  split; auto.
Qed.


Record legal_context : Type := {
  context_eval : list nat -> list nat
}.

Definition context_syntax_record R J (C : legal_context) (d : deriv R J) : list nat :=
  context_eval C (SRec_deriv R J d).

Definition context_behavior_record R J (C : legal_context) (d : deriv R J) : list nat :=
  context_eval C (BRec_mor R BoUnit (ObjOfJudg J) (interp_deriv R J d)).

Definition context_syn_equiv R J (A B : deriv R J) : Prop :=
  forall C, context_syntax_record R J C A = context_syntax_record R J C B.

Definition context_beh_equiv R J (A B : deriv R J) : Prop :=
  forall C, context_behavior_record R J C A = context_behavior_record R J C B.

Theorem full_abstraction_for_legal_contexts :
  forall R J (A B : deriv R J),
    context_syn_equiv R J A B <-> context_beh_equiv R J A B.
Proof.
  intros R J A B.
  unfold context_syn_equiv, context_beh_equiv,
    context_syntax_record, context_behavior_record.
  repeat rewrite <- interpretation_record_consistent.
  split; auto.
Qed.

Theorem syntactic_soundness :
  forall R J (d : deriv R J), mor R BoUnit (ObjOfJudg J).
Proof.
  intros R J d. exact (interp_deriv R J d).
Qed.

Inductive grammar_symbol : Type :=
| Nonterminal : nat -> grammar_symbol
| Terminal : nat -> grammar_symbol.

Definition symbol_declared (N T : list nat) (s : grammar_symbol) : Prop :=
  match s with
  | Nonterminal n => In n N
  | Terminal t => In t T
  end.

Definition word_declared (N T : list nat) (w : list grammar_symbol) : Prop :=
  Forall (symbol_declared N T) w.

Record strict_type0_grammar : Type := {
  nonterminals : list nat;
  terminals : list nat;
  start_symbol : nat;
  productions : list (list grammar_symbol * list grammar_symbol);
  start_in_nonterminals : In start_symbol nonterminals;
  nonterminal_terminal_disjoint :
    forall x, In x nonterminals -> ~ In x terminals;
  productions_wellformed :
    forall alpha beta,
      In (alpha, beta) productions ->
      word_declared nonterminals terminals alpha /\
      word_declared nonterminals terminals beta /\
      alpha <> [] /\
      exists n, In (Nonterminal n) alpha
}.

Inductive grammar_step (G : strict_type0_grammar) :
    list grammar_symbol -> list grammar_symbol -> Prop :=
| GrammarStep :
    forall left right alpha beta,
      In (alpha, beta) (productions G) ->
      grammar_step G (left ++ alpha ++ right) (left ++ beta ++ right).

Inductive grammar_derives (G : strict_type0_grammar) :
    list grammar_symbol -> list grammar_symbol -> Prop :=
| GrammarDerivesRefl :
    forall w, grammar_derives G w w
| GrammarDerivesStep :
    forall w1 w2 w3,
      grammar_step G w1 w2 ->
      grammar_derives G w2 w3 ->
      grammar_derives G w1 w3.

Definition terminal_word (w : list nat) : list grammar_symbol :=
  map Terminal w.

Definition grammar_accepts (G : strict_type0_grammar) (w : list nat) : Prop :=
  grammar_derives G [Nonterminal (start_symbol G)] (terminal_word w).

Definition language := list nat -> Prop.

Record recursively_enumerable (L : language) : Type := {
  enumerator : nat -> option (list nat);
  enumerator_sound :
    forall k w, enumerator k = Some w -> L w;
  enumerator_complete :
    forall w, L w -> exists k, enumerator k = Some w
}.

Record type0_backend_theorem : Prop := {
  type0_complete :
    forall L : language,
      recursively_enumerable L ->
      exists G : strict_type0_grammar,
        forall w, L w <-> grammar_accepts G w
}.

Record finite_layer_language (R : rule -> Prop) : Type := {
  layer_bound : nat;
  layer_word : list nat -> Prop;
  layer_re : recursively_enumerable layer_word;
  layer_witness :
    forall w,
      layer_word w ->
      exists J (d : deriv R J), length (SRec_deriv R J d) <= S (layer_bound)
}.

Record grammar_representation (R : rule -> Prop) : Type := {
  represented_language : finite_layer_language R;
  representing_grammar : strict_type0_grammar;
  grammar_correct :
    forall w,
      layer_word R represented_language w <->
      grammar_accepts representing_grammar w
}.

Definition empty_strict_type0_grammar : strict_type0_grammar.
Proof.
  refine {|
    nonterminals := [0];
    terminals := [];
    start_symbol := 0;
    productions := []
  |}.
  - simpl. left. reflexivity.
  - intros x _ Hin. contradiction.
  - intros alpha beta Hin. contradiction.
Defined.

Definition empty_enumerator (_ : nat) : option (list nat) := None.

Definition empty_recursively_enumerable :
    recursively_enumerable (fun _ : list nat => False).
Proof.
  refine {|
    enumerator := empty_enumerator
  |}.
  - intros k w H. discriminate H.
  - intros w H. contradiction.
Defined.

Definition empty_finite_layer_language (R : rule -> Prop) :
    finite_layer_language R.
Proof.
  refine {|
    layer_bound := 0;
    layer_word := fun _ => False;
    layer_re := empty_recursively_enumerable
  |}.
  intros w H. contradiction.
Defined.

Lemma empty_grammar_step_impossible :
  forall u v, ~ grammar_step empty_strict_type0_grammar u v.
Proof.
  intros u v H.
  inversion H as [left right alpha beta Hin Hu Hv].
  simpl in Hin. contradiction.
Qed.

Lemma empty_grammar_derives_only_refl :
  forall u v,
    grammar_derives empty_strict_type0_grammar u v ->
    u = v.
Proof.
  intros u v H.
  induction H.
  - reflexivity.
  - exfalso. exact (empty_grammar_step_impossible w1 w2 H).
Qed.

Lemma terminal_word_not_single_nonterminal :
  forall x w, [Nonterminal x] <> terminal_word w.
Proof.
  intros x w H.
  destruct w as [| a rest]; simpl in H; discriminate H.
Qed.

Lemma empty_grammar_accepts_no_word :
  forall w, ~ grammar_accepts empty_strict_type0_grammar w.
Proof.
  intros w H.
  unfold grammar_accepts in H.
  simpl in H.
  pose proof (empty_grammar_derives_only_refl
                [Nonterminal 0] (terminal_word w) H) as Heq.
  exact (terminal_word_not_single_nonterminal 0 w Heq).
Qed.

Theorem empty_grammar_representation :
  forall R, grammar_representation R.
Proof.
  intro R.
  refine {|
    represented_language := empty_finite_layer_language R;
    representing_grammar := empty_strict_type0_grammar
  |}.
  intro w. simpl. split.
  - intro H. contradiction.
  - intro H. exfalso. exact (empty_grammar_accepts_no_word w H).
Qed.

Theorem finite_layer_type0_grammar_representation :
  forall (BT : type0_backend_theorem) R (L : finite_layer_language R),
    exists G : grammar_representation R, represented_language R G = L.
Proof.
  intros BT R L.
  destruct (type0_complete BT (layer_word R L) (layer_re R L))
    as [G Hcorrect].
  exists {|
    represented_language := L;
    representing_grammar := G;
    grammar_correct := Hcorrect
  |}.
  reflexivity.
Qed.

Theorem grammar_representation_consistent :
  forall R, exists G : grammar_representation R, True.
Proof.
  intro R.
  exists (empty_grammar_representation R). exact I.
Qed.

Definition trace_edge_from_syn R (r : nat) : Prop :=
  exists n o o', inhabited (deriv R (JRw r n o o')).

Definition edge_obs_edge S e tau (TI : trace_interface S e tau) (r : nat) : Prop :=
  exists n o o', edge_obs S e tau TI r n o o'.

Theorem edge_obs_generates_trace_rewrite :
  forall S e tau TI r n o o',
    edge_obs S e tau TI r n o o' ->
    trace_rule S e tau TI (MkRule [] (JRw r n o o')).
Proof.
  intros S e tau TI r n o o' H.
  exact (TraceRewrite S e tau TI r n o o' H).
Qed.

Theorem edge_obs_generates_syn_rewrite :
  forall S e tau TI r n o o',
    edge_obs S e tau TI r n o o' ->
    inhabited (Syn S e tau TI (JRw r n o o')).
Proof.
  intros S e tau TI r n o o' H.
  constructor.
  unfold Syn.
  apply DerivNode with (ps := []).
  - unfold rules.
    right.
    exact (edge_obs_generates_trace_rewrite S e tau TI r n o o' H).
  - constructor.
Qed.

Theorem edge_obs_edge_recovered_from_syn :
  forall S e tau TI r,
    edge_obs_edge S e tau TI r ->
    trace_edge_from_syn (rules S e tau TI) r.
Proof.
  intros S e tau TI r [n [o [o' H]]].
  unfold trace_edge_from_syn.
  exists n, o, o'.
  exact (edge_obs_generates_syn_rewrite S e tau TI r n o o' H).
Qed.

Theorem skel_rule_never_rewrites :
  forall O tau ps r n o o',
    ~ skel_rule O tau (MkRule ps (JRw r n o o')).
Proof.
  intros O tau ps r n o o' H.
  inversion H.
Qed.

Theorem syn_rewrite_implies_edge_obs :
  forall S e tau TI r n o o',
    Syn S e tau TI (JRw r n o o') ->
    edge_obs S e tau TI r n o o'.
Proof.
  intros S e tau TI r n o o' Hsyn.
  unfold Syn in Hsyn.
  inversion Hsyn as [ps c Hrule _ Hc].
  subst c.
  unfold rules in Hrule.
  destruct Hrule as [Hskel | Htrace].
  - exfalso.
    exact (skel_rule_never_rewrites (ObsPr S) tau ps r n o o' Hskel).
  - inversion Htrace; subst; assumption.
Qed.

Theorem trace_edge_from_syn_iff_edge_obs_edge :
  forall S e tau TI r,
    trace_edge_from_syn (rules S e tau TI) r <->
    edge_obs_edge S e tau TI r.
Proof.
  intros S e tau TI r.
  split.
  - intros [n [o [o' [d]]]].
    exists n, o, o'.
    exact (syn_rewrite_implies_edge_obs S e tau TI r n o o' d).
  - exact (edge_obs_edge_recovered_from_syn S e tau TI r).
Qed.

Definition concrete_prekernel_edge S e tau TI (r : nat) : Prop :=
  edge_obs_edge S e tau TI r.

Theorem concrete_prekernel_edges_exact :
  forall S e tau TI r,
    trace_edge_from_syn (rules S e tau TI) r <->
    concrete_prekernel_edge S e tau TI r.
Proof.
  intros S e tau TI r.
  unfold concrete_prekernel_edge.
  exact (trace_edge_from_syn_iff_edge_obs_edge S e tau TI r).
Qed.


Record weak_quotient_model (S : system_data) (e : code) (tau : ty)
    (TI : trace_interface S e tau) : Type := {
  quotient_edge : nat -> Prop;
  quotient_edge_exact :
    forall r, quotient_edge r <-> edge_obs_edge S e tau TI r
}.

Definition concrete_weak_quotient_model S e tau TI :
    weak_quotient_model S e tau TI.
Proof.
  refine {|
    quotient_edge := concrete_prekernel_edge S e tau TI
  |}.
  intro r. unfold concrete_prekernel_edge. split; intro H; exact H.
Defined.

Theorem weak_quotient_model_consistent :
  forall S e tau TI, exists W : weak_quotient_model S e tau TI, True.
Proof.
  intros S e tau TI.
  exists (concrete_weak_quotient_model S e tau TI). exact I.
Qed.

Record recovery_interface (S : system_data) (e : code) (tau : ty)
    (TI : trace_interface S e tau) : Type := {
  trace_kernel : nat;
  recover : (judg -> Type) -> nat;
  recover_respects_edges :
    recover (Syn S e tau TI) = trace_kernel
}.

Theorem recovery_from_interface :
  forall S e tau TI (RI : recovery_interface S e tau TI),
    recover S e tau TI RI (Syn S e tau TI) = trace_kernel S e tau TI RI.
Proof.
  intros S e tau TI RI. exact (recover_respects_edges S e tau TI RI).
Qed.

Theorem trace_rules_have_witnesses :
  forall S e tau TI r,
    trace_rule S e tau TI r ->
    match r with
    | MkRule [] (JState u n o) => exists s, proto S e tau TI s = u
    | MkRule [] (JRw edge n o o') =>
        exists E s s' R k,
          root_run_prefix S tau e n E R /\
          nth_error R k = Some (s, s') /\
          step (Body S) (q_atom S) (c_atom S) s s'
    | MkRule [] (JObs _ _ n _) =>
        exists E R A, root_run_down S tau e n E R A
    | MkRule [] (JApp _ _ n _ _) =>
        exists E R A, root_run_down S tau e n E R A
    | _ => exists tag, tag = length (premises r)
    end.
Proof.
  intros S e tau TI r H.
  destruct H as
      [u n o Hinit
      | r n o o' Hedge
      | r u v lambda n o o' Hr Hedge
      | p t n o Hact
      | p t n q u Hact]; simpl.
  - exact (init_obs_witness S e tau TI u n o Hinit).
  - exact (edge_obs_witness S e tau TI r n o o' Hedge).
  - exists (length [JState u n o; JRw r n o o']). reflexivity.
  - destruct (act_witness S e tau TI n (ActObs p t n o) Hact) as [E [R [A [HR HA]]]].
    exists E, R, A. exact HR.
  - destruct (act_witness S e tau TI n (ActApp p t n q u) Hact) as [E [R [A [HR HA]]]].
    exists E, R, A. exact HR.
Qed.

End ProgramInducedSyntax1135.
