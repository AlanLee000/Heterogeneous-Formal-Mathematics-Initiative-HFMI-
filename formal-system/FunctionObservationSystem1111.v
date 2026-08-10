From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Lia.

Import ListNotations.

Module FunctionObservationSystem1111.

Definition relation (A B : Type) : Type := list A -> list B -> Prop.

Section ArrowSystem.

Variable A B : Type.
Variable f : A -> B.
Variable primitive_observable : forall m n : nat, relation A B -> Prop.

Definition same_fiber_list (xs xs' : list A) : Prop :=
  Forall2 (fun a a' => f a = f a') xs xs'.

Definition stable (m n : nat) (R : relation A B) : Prop :=
  forall xs xs' ys,
    length xs = m ->
    length xs' = m ->
    length ys = n ->
    same_fiber_list xs xs' ->
    (R xs ys <-> R xs' ys).

Definition arity_member (m n : nat) (xs : list A) (ys : list B) : Prop :=
  length xs = m /\ length ys = n.

Definition arity_clean (m n : nat) (R : relation A B) : Prop :=
  forall xs ys, R xs ys -> arity_member m n xs ys.

Definition empty_rel (m n : nat) : relation A B :=
  fun xs ys => arity_member m n xs ys /\ False.

Definition full_rel (m n : nat) : relation A B :=
  fun xs ys => arity_member m n xs ys.

Definition inter_rel (R S : relation A B) : relation A B :=
  fun xs ys => R xs ys /\ S xs ys.
Definition union_rel (R S : relation A B) : relation A B :=
  fun xs ys => R xs ys \/ S xs ys.
Definition compl_rel (m n : nat) (R : relation A B) : relation A B :=
  fun xs ys => arity_member m n xs ys /\ ~ R xs ys.

Definition graph_rel : relation A B :=
  fun xs ys =>
    match xs, ys with
    | [a], [b] => f a = b
    | _, _ => False
    end.

Definition source_diag_rel : relation A B :=
  fun xs ys =>
    match xs, ys with
    | [a; a'], [] => a = a'
    | _, _ => False
    end.

Definition target_diag_rel : relation A B :=
  fun xs ys =>
    match xs, ys with
    | [], [b; b'] => b = b'
    | _, _ => False
    end.

Definition kernel_rel : relation A B :=
  fun xs ys =>
    match xs, ys with
    | [a; a'], [] => exists b, f a = b /\ f a' = b
    | _, _ => False
    end.

Definition image_rel : relation A B :=
  fun xs ys =>
    match xs, ys with
    | [], [b] => exists a, f a = b
    | _, _ => False
    end.

Definition unreachable_rel : relation A B := compl_rel 0 1 image_rel.

Definition exists_source (m n : nat) (R : relation A B) : relation A B :=
  fun xs ys => arity_member m n xs ys /\ exists a, R (a :: xs) ys.

Definition exists_target (m n : nat) (R : relation A B) : relation A B :=
  fun xs ys => arity_member m n xs ys /\ exists b, R xs (b :: ys).

Definition forall_source (m n : nat) (R : relation A B) : relation A B :=
  compl_rel m n (exists_source m n (compl_rel (S m) n R)).

Definition forall_target (m n : nat) (R : relation A B) : relation A B :=
  compl_rel m n (exists_target m n (compl_rel m (S n) R)).

Definition reindexed_by {X : Type}
    (sigma : list nat) (old new : list X) : Prop :=
  length sigma = length new /\
  forall i x,
    nth_error new i = Some x ->
    exists j, nth_error sigma i = Some j /\ nth_error old j = Some x.

Definition bounded_permutation (k : nat) (sigma : list nat) : Prop :=
  length sigma = k /\ NoDup sigma /\ Forall (fun i => i < k) sigma.

Definition source_permute_rel
    (m n : nat) (sigma : list nat) (R : relation A B) : relation A B :=
  fun xs ys =>
    bounded_permutation m sigma /\
    arity_member m n xs ys /\
    exists xs0, arity_member m n xs0 ys /\ R xs0 ys /\
      reindexed_by sigma xs0 xs.

Definition target_permute_rel
    (m n : nat) (sigma : list nat) (R : relation A B) : relation A B :=
  fun xs ys =>
    bounded_permutation n sigma /\
    arity_member m n xs ys /\
    exists ys0, arity_member m n xs ys0 /\ R xs ys0 /\
      reindexed_by sigma ys0 ys.

Inductive coord_sort : Type :=
| CoordSource : coord_sort
| CoordTarget : coord_sort.

Definition mixed_value : Type := A + B.
Definition mixed_relation : Type := list mixed_value -> Prop.

Definition value_fits (s : coord_sort) (z : mixed_value) : Prop :=
  match s, z with
  | CoordSource, inl _ => True
  | CoordTarget, inr _ => True
  | _, _ => False
  end.

Definition mixed_tuple_shape
    (shape : list coord_sort) (zs : list mixed_value) : Prop :=
  length shape = length zs /\
  forall i s z,
    nth_error shape i = Some s ->
    nth_error zs i = Some z ->
    value_fits s z.

Definition mixed_arity_clean
    (shape : list coord_sort) (R : mixed_relation) : Prop :=
  forall zs, R zs -> mixed_tuple_shape shape zs.

Definition indexed_rewrite {X : Type}
    (sigma : list nat) (old new : list X) : Prop :=
  length new = length sigma /\
  forall i j,
    nth_error sigma i = Some j ->
    nth_error new i = nth_error old j.

Definition shape_permutation
    (shape : list coord_sort) (sigma : list nat)
    (shape' : list coord_sort) : Prop :=
  bounded_permutation (length shape) sigma /\
  length shape' = length sigma /\
  forall i s,
    nth_error shape' i = Some s ->
    exists j, nth_error sigma i = Some j /\ nth_error shape j = Some s.

Definition mixed_permute_rel
    (shape shape' : list coord_sort) (sigma : list nat)
    (R : mixed_relation) : mixed_relation :=
  fun zs =>
    shape_permutation shape sigma shape' /\
    exists zs0,
      mixed_tuple_shape shape zs0 /\
      R zs0 /\
      indexed_rewrite sigma zs0 zs.

Lemma mixed_permute_clean :
  forall shape shape' sigma R,
    mixed_arity_clean shape R ->
    mixed_arity_clean shape' (mixed_permute_rel shape shape' sigma R).
Proof.
  unfold mixed_arity_clean, mixed_permute_rel, mixed_tuple_shape,
    shape_permutation, indexed_rewrite.
  intros shape shape' sigma R Hclean zs
    [[_ [Hshape_len Hshape_map]]
      [zs0 [[Hzs0_len Hzs0_fit] [HR [Hzs_len Hzs_map]]]]].
  split.
  - transitivity (length sigma).
    + exact Hshape_len.
    + symmetry. exact Hzs_len.
  - intros i s z Hshape' Hz.
    specialize (Hshape_map i s Hshape') as [j [Hsigma Hshape_old]].
    specialize (Hzs_map i j Hsigma).
    rewrite Hz in Hzs_map.
    symmetry in Hzs_map.
    exact (Hzs0_fit j s z Hshape_old Hzs_map).
Qed.

Definition block_mixed_shape (m n : nat) : list coord_sort :=
  repeat CoordSource m ++ repeat CoordTarget n.

Definition block_mixed_tuple (xs : list A) (ys : list B) : list mixed_value :=
  map inl xs ++ map inr ys.

Lemma source_value_tuple_shape :
  forall xs,
    mixed_tuple_shape (repeat CoordSource (length xs)) (map (@inl A B) xs).
Proof.
  induction xs as [| a xs IH].
  - split; simpl; auto.
    intros [| i] s z Hs Hz; discriminate.
  - destruct IH as [IHlen IHfit].
    split; simpl; auto.
    intros [| i] s z Hs Hz; simpl in *.
    + inversion Hs; inversion Hz; subst. exact I.
    + eapply IHfit; eauto.
Qed.

Lemma target_value_tuple_shape :
  forall ys,
    mixed_tuple_shape (repeat CoordTarget (length ys)) (map (@inr A B) ys).
Proof.
  induction ys as [| b ys IH].
  - split; simpl; auto.
    intros [| i] s z Hs Hz; discriminate.
  - destruct IH as [IHlen IHfit].
    split; simpl; auto.
    intros [| i] s z Hs Hz; simpl in *.
    + inversion Hs; inversion Hz; subst. exact I.
    + eapply IHfit; eauto.
Qed.

Lemma mixed_tuple_shape_app :
  forall shape1 zs1 shape2 zs2,
    mixed_tuple_shape shape1 zs1 ->
    mixed_tuple_shape shape2 zs2 ->
    mixed_tuple_shape (shape1 ++ shape2) (zs1 ++ zs2).
Proof.
  intros shape1 zs1 shape2 zs2 [Hlen1 Hfit1] [Hlen2 Hfit2].
  split.
  - rewrite !length_app. lia.
  - intros i s z Hshape Hz.
    destruct (lt_dec i (length shape1)) as [Hlt | Hnlt].
    + rewrite nth_error_app1 in Hshape by exact Hlt.
      rewrite nth_error_app1 in Hz by (rewrite <- Hlen1; exact Hlt).
      eapply Hfit1; eauto.
    + assert (Hge : length shape1 <= i) by lia.
      rewrite nth_error_app2 in Hshape by exact Hge.
      rewrite nth_error_app2 in Hz by (rewrite <- Hlen1; exact Hge).
      rewrite <- Hlen1 in Hz.
      eapply Hfit2; eauto.
Qed.

Lemma block_mixed_tuple_shape :
  forall xs ys,
    mixed_tuple_shape
      (block_mixed_shape (length xs) (length ys))
      (block_mixed_tuple xs ys).
Proof.
  intros xs ys.
  unfold block_mixed_shape, block_mixed_tuple.
  apply mixed_tuple_shape_app.
  - apply source_value_tuple_shape.
  - apply target_value_tuple_shape.
Qed.

Definition block_mixed_relation
    (m n : nat) (R : relation A B) : mixed_relation :=
  fun zs =>
    mixed_tuple_shape (block_mixed_shape m n) zs /\
    exists xs ys, zs = block_mixed_tuple xs ys /\ R xs ys.

Definition mixed_empty_rel (shape : list coord_sort) : mixed_relation :=
  fun zs => mixed_tuple_shape shape zs /\ False.

Definition mixed_full_rel (shape : list coord_sort) : mixed_relation :=
  fun zs => mixed_tuple_shape shape zs.

Definition mixed_inter_rel (R S : mixed_relation) : mixed_relation :=
  fun zs => R zs /\ S zs.

Definition mixed_union_rel (R S : mixed_relation) : mixed_relation :=
  fun zs => R zs \/ S zs.

Definition mixed_compl_rel
    (shape : list coord_sort) (R : mixed_relation) : mixed_relation :=
  fun zs => mixed_tuple_shape shape zs /\ ~ R zs.

Lemma block_mixed_relation_clean :
  forall m n R,
    mixed_arity_clean (block_mixed_shape m n) (block_mixed_relation m n R).
Proof.
  unfold mixed_arity_clean, block_mixed_relation.
  intros m n R zs [Hshape _].
  exact Hshape.
Qed.

Lemma mixed_empty_clean :
  forall shape, mixed_arity_clean shape (mixed_empty_rel shape).
Proof.
  unfold mixed_arity_clean, mixed_empty_rel.
  intros shape zs [_ Hfalse]. contradiction.
Qed.

Lemma mixed_full_clean :
  forall shape, mixed_arity_clean shape (mixed_full_rel shape).
Proof.
  unfold mixed_arity_clean, mixed_full_rel.
  intros shape zs Hshape. exact Hshape.
Qed.

Lemma mixed_inter_clean :
  forall shape R S,
    mixed_arity_clean shape R ->
    mixed_arity_clean shape (mixed_inter_rel R S).
Proof.
  unfold mixed_arity_clean, mixed_inter_rel.
  intros shape R S Hclean zs [HR _].
  apply Hclean. exact HR.
Qed.

Lemma mixed_union_clean :
  forall shape R S,
    mixed_arity_clean shape R ->
    mixed_arity_clean shape S ->
    mixed_arity_clean shape (mixed_union_rel R S).
Proof.
  unfold mixed_arity_clean, mixed_union_rel.
  intros shape R S HcleanR HcleanS zs [HR | HS].
  - apply HcleanR. exact HR.
  - apply HcleanS. exact HS.
Qed.

Lemma mixed_compl_clean :
  forall shape R, mixed_arity_clean shape (mixed_compl_rel shape R).
Proof.
  unfold mixed_arity_clean, mixed_compl_rel.
  intros shape R zs [Hshape _].
  exact Hshape.
Qed.

Lemma empty_rel_clean :
  forall m n, arity_clean m n (empty_rel m n).
Proof.
  unfold arity_clean, empty_rel.
  intros m n xs ys [Harity Hfalse].
  contradiction.
Qed.

Lemma full_rel_clean :
  forall m n, arity_clean m n (full_rel m n).
Proof.
  unfold arity_clean, full_rel.
  intros m n xs ys Harity.
  exact Harity.
Qed.

Lemma compl_rel_clean :
  forall m n R, arity_clean m n (compl_rel m n R).
Proof.
  unfold arity_clean, compl_rel.
  intros m n R xs ys [Harity _].
  exact Harity.
Qed.

Lemma exists_source_clean :
  forall m n R, arity_clean m n (exists_source m n R).
Proof.
  unfold arity_clean, exists_source.
  intros m n R xs ys [Harity _].
  exact Harity.
Qed.

Lemma exists_target_clean :
  forall m n R, arity_clean m n (exists_target m n R).
Proof.
  unfold arity_clean, exists_target.
  intros m n R xs ys [Harity _].
  exact Harity.
Qed.

Lemma forall_source_clean :
  forall m n R, arity_clean m n (forall_source m n R).
Proof.
  intros m n R.
  unfold forall_source.
  apply compl_rel_clean.
Qed.

Lemma forall_target_clean :
  forall m n R, arity_clean m n (forall_target m n R).
Proof.
  intros m n R.
  unfold forall_target.
  apply compl_rel_clean.
Qed.

Lemma forall_source_spec :
  forall m n R xs ys,
    arity_member m n xs ys ->
    (forall_source m n R xs ys <-> forall a, R (a :: xs) ys).
Proof.
  unfold forall_source, compl_rel, exists_source.
  intros m n R xs ys Harity.
  destruct Harity as [Hxs Hys].
  split.
  - intros [_ Hnot_exists] a.
    apply NNPP. intro Hnot_R.
    apply Hnot_exists.
    split.
    + split; assumption.
    + exists a. split.
      * split.
        -- simpl. now rewrite Hxs.
        -- exact Hys.
      * exact Hnot_R.
  - intros Hall.
    split.
    + split; assumption.
    + intros [_ [a [_ Hnot_R]]].
      apply Hnot_R. apply Hall.
Qed.

Lemma forall_target_spec :
  forall m n R xs ys,
    arity_member m n xs ys ->
    (forall_target m n R xs ys <-> forall b, R xs (b :: ys)).
Proof.
  unfold forall_target, compl_rel, exists_target.
  intros m n R xs ys Harity.
  destruct Harity as [Hxs Hys].
  split.
  - intros [_ Hnot_exists] b.
    apply NNPP. intro Hnot_R.
    apply Hnot_exists.
    split.
    + split; assumption.
    + exists b. split.
      * split.
        -- exact Hxs.
        -- simpl. now rewrite Hys.
      * exact Hnot_R.
  - intros Hall.
    split.
    + split; assumption.
    + intros [_ [b [_ Hnot_R]]].
      apply Hnot_R. apply Hall.
Qed.

Lemma source_permute_clean :
  forall m n sigma R, arity_clean m n (source_permute_rel m n sigma R).
Proof.
  unfold arity_clean, source_permute_rel.
  intros m n sigma R xs ys [_ [Harity _]].
  exact Harity.
Qed.

Lemma target_permute_clean :
  forall m n sigma R, arity_clean m n (target_permute_rel m n sigma R).
Proof.
  unfold arity_clean, target_permute_rel.
  intros m n sigma R xs ys [_ [Harity _]].
  exact Harity.
Qed.

Inductive observable : nat -> nat -> relation A B -> Prop :=
| ObsPrimitive :
    forall m n R, primitive_observable m n R -> observable m n R
| ObsEmpty : forall m n, observable m n (empty_rel m n)
| ObsFull : forall m n, observable m n (full_rel m n)
| ObsGraph : observable 1 1 graph_rel
| ObsSourceDiagonal : observable 2 0 source_diag_rel
| ObsTargetDiagonal : observable 0 2 target_diag_rel
| ObsKernel : observable 2 0 kernel_rel
| ObsImage : observable 0 1 image_rel
| ObsInter :
    forall m n R S,
      observable m n R -> observable m n S ->
      observable m n (inter_rel R S)
| ObsUnion :
    forall m n R S,
      observable m n R -> observable m n S ->
      observable m n (union_rel R S)
| ObsComplement :
    forall m n R,
      observable m n R -> observable m n (compl_rel m n R)
| ObsExistsSource :
    forall m n R,
      observable (S m) n R -> observable m n (exists_source m n R)
| ObsExistsTarget :
    forall m n R,
      observable m (S n) R -> observable m n (exists_target m n R)
| ObsSourcePermute :
    forall m n sigma R,
      bounded_permutation m sigma ->
      observable m n R -> observable m n (source_permute_rel m n sigma R)
| ObsTargetPermute :
    forall m n sigma R,
      bounded_permutation n sigma ->
      observable m n R -> observable m n (target_permute_rel m n sigma R).

Inductive mixed_observable : list coord_sort -> mixed_relation -> Prop :=
| MixedBlock :
    forall m n R,
      observable m n R ->
      mixed_observable (block_mixed_shape m n) (block_mixed_relation m n R)
| MixedEmpty :
    forall shape, mixed_observable shape (mixed_empty_rel shape)
| MixedFull :
    forall shape, mixed_observable shape (mixed_full_rel shape)
| MixedInter :
    forall shape R S,
      mixed_observable shape R ->
      mixed_observable shape S ->
      mixed_observable shape (mixed_inter_rel R S)
| MixedUnion :
    forall shape R S,
      mixed_observable shape R ->
      mixed_observable shape S ->
      mixed_observable shape (mixed_union_rel R S)
| MixedComplement :
    forall shape R,
      mixed_observable shape R ->
      mixed_observable shape (mixed_compl_rel shape R)
| MixedPermute :
    forall shape shape' sigma R,
      shape_permutation shape sigma shape' ->
      mixed_observable shape R ->
      mixed_observable shape' (mixed_permute_rel shape shape' sigma R).

Theorem mixed_observable_clean :
  forall shape R,
    mixed_observable shape R -> mixed_arity_clean shape R.
Proof.
  intros shape R Hobs.
  induction Hobs.
  - apply block_mixed_relation_clean.
  - apply mixed_empty_clean.
  - apply mixed_full_clean.
  - apply mixed_inter_clean. exact IHHobs1.
  - apply mixed_union_clean; assumption.
  - apply mixed_compl_clean.
  - apply mixed_permute_clean. exact IHHobs.
Qed.

Theorem mixed_coordinate_rearrangement_supported :
  forall m n R sigma shape',
    observable m n R ->
    shape_permutation (block_mixed_shape m n) sigma shape' ->
    mixed_observable shape'
      (mixed_permute_rel (block_mixed_shape m n) shape' sigma
        (block_mixed_relation m n R)).
Proof.
  intros m n R sigma shape' Hobs Hperm.
  apply MixedPermute; auto.
  apply MixedBlock. exact Hobs.
Qed.

Definition stab (m n : nat) (R : relation A B) : Prop :=
  observable m n R /\ stable m n R.

Definition injective : Prop := forall a a', f a = f a' -> a = a'.
Definition surjective : Prop := forall b, exists a, f a = b.
Definition constant_map : Prop := forall a a', f a = f a'.

Lemma graph_observable : observable 1 1 graph_rel.
Proof. apply ObsGraph. Qed.

Lemma source_diag_observable : observable 2 0 source_diag_rel.
Proof. apply ObsSourceDiagonal. Qed.

Lemma target_diag_observable : observable 0 2 target_diag_rel.
Proof. apply ObsTargetDiagonal. Qed.

Lemma kernel_observable : observable 2 0 kernel_rel.
Proof. apply ObsKernel. Qed.

Lemma image_observable : observable 0 1 image_rel.
Proof. apply ObsImage. Qed.

Lemma unreachable_observable : observable 0 1 unreachable_rel.
Proof. unfold unreachable_rel. apply ObsComplement. apply image_observable. Qed.

Lemma forall_source_observable :
  forall m n R,
    observable (S m) n R -> observable m n (forall_source m n R).
Proof.
  intros m n R Hobs.
  unfold forall_source.
  apply ObsComplement.
  apply ObsExistsSource.
  apply ObsComplement.
  exact Hobs.
Qed.

Lemma forall_target_observable :
  forall m n R,
    observable m (S n) R -> observable m n (forall_target m n R).
Proof.
  intros m n R Hobs.
  unfold forall_target.
  apply ObsComplement.
  apply ObsExistsTarget.
  apply ObsComplement.
  exact Hobs.
Qed.

Lemma graph_stable : stable 1 1 graph_rel.
Proof.
  unfold stable, same_fiber_list, graph_rel.
  intros xs xs' ys Hx Hx' Hy Hfib.
  destruct xs as [| a xs]; try discriminate.
  destruct xs as [| ax xs]; try discriminate.
  destruct xs' as [| a' xs']; try discriminate.
  destruct xs' as [| ax' xs']; try discriminate.
  destruct ys as [| b ys]; try discriminate.
  destruct ys as [| b_tail ys]; try discriminate.
  inversion Hfib; subst.
  simpl in *.
  split; intro H; congruence.
Qed.

Lemma target_diag_stable : stable 0 2 target_diag_rel.
Proof.
  unfold stable, target_diag_rel.
  intros xs xs' ys Hx Hx' Hy _.
  destruct xs as [| a xs]; try discriminate.
  destruct xs' as [| a' xs']; try discriminate.
  destruct ys as [| b ys]; try discriminate.
  destruct ys as [| b' ys]; try discriminate.
  destruct ys as [| b_tail ys]; try discriminate.
  simpl. tauto.
Qed.

Lemma kernel_stable : stable 2 0 kernel_rel.
Proof.
  unfold stable, same_fiber_list, kernel_rel.
  intros xs xs' ys Hx Hx' Hy Hfib.
  destruct xs as [| a xs]; try discriminate.
  destruct xs as [| a2 xs]; try discriminate.
  destruct xs as [| ax xs]; try discriminate.
  destruct xs' as [| a' xs']; try discriminate.
  destruct xs' as [| a2' xs']; try discriminate.
  destruct xs' as [| ax' xs']; try discriminate.
  destruct ys as [| b ys]; try discriminate.
  inversion Hfib; subst.
  inversion H4; subst.
  simpl in *.
  split; intros [b [Hb1 Hb2]].
  - exists b. split; congruence.
  - exists b. split; congruence.
Qed.

Lemma image_stable : stable 0 1 image_rel.
Proof.
  unfold stable, image_rel.
  intros xs xs' ys Hx Hx' Hy _.
  destruct xs as [| a xs]; try discriminate.
  destruct xs' as [| a' xs']; try discriminate.
  destruct ys as [| b ys]; try discriminate.
  destruct ys as [| b_tail ys]; try discriminate.
  simpl. tauto.
Qed.

Lemma unreachable_stable : stable 0 1 unreachable_rel.
Proof.
  unfold unreachable_rel, compl_rel, arity_member, stable.
  intros xs xs' ys Hx Hx' Hy Hfib.
  pose proof (image_stable xs xs' ys Hx Hx' Hy Hfib) as H.
  split.
  - intros [[_ _] Hnot].
    repeat split; auto.
    intro Him.
    apply Hnot.
    apply (proj2 H). exact Him.
  - intros [[_ _] Hnot].
    repeat split; auto.
    intro Him.
    apply Hnot.
    apply (proj1 H). exact Him.
Qed.

Lemma kernel_char :
  forall a a', kernel_rel [a; a'] [] <-> f a = f a'.
Proof.
  intros a a'. simpl.
  split.
  - intros [b [H1 H2]]. congruence.
  - intro H. exists (f a'). split; congruence.
Qed.

Lemma kernel_in_stab : stab 2 0 kernel_rel.
Proof. split; [apply kernel_observable | apply kernel_stable]. Qed.

Lemma image_in_stab : stab 0 1 image_rel.
Proof. split; [apply image_observable | apply image_stable]. Qed.

Lemma unreachable_in_stab : stab 0 1 unreachable_rel.
Proof. split; [apply unreachable_observable | apply unreachable_stable]. Qed.

Lemma source_diag_stable_iff_injective :
  stable 2 0 source_diag_rel <-> injective.
Proof.
  split.
  - intros Hstable a a' Hfa.
    pose proof
      (Hstable [a; a] [a; a'] []
        eq_refl eq_refl eq_refl) as H.
    assert (same_fiber_list [a; a] [a; a']) as Hfib.
    { repeat constructor; auto. }
    specialize (H Hfib).
    simpl in H.
    apply H. reflexivity.
  - intros Hinj xs xs' ys Hx Hx' Hy Hfib.
    destruct xs as [| a xs]; try discriminate.
    destruct xs as [| a2 xs]; try discriminate.
    destruct xs as [| ax xs]; try discriminate.
    destruct xs' as [| a' xs']; try discriminate.
    destruct xs' as [| a2' xs']; try discriminate.
    destruct xs' as [| ax' xs']; try discriminate.
    destruct ys as [| b ys]; try discriminate.
    unfold same_fiber_list in Hfib.
    inversion Hfib; subst.
    inversion H4; subst.
    simpl in *.
    split; intro Heq; apply Hinj; congruence.
Qed.

Lemma source_diag_in_stab_iff_injective :
  stab 2 0 source_diag_rel <-> injective.
Proof.
  split.
  - intros [_ H]. apply source_diag_stable_iff_injective. exact H.
  - intro H. split.
    + apply source_diag_observable.
    + apply source_diag_stable_iff_injective. exact H.
Qed.

Lemma target_diag_in_stab : stab 0 2 target_diag_rel.
Proof. split; [apply target_diag_observable | apply target_diag_stable]. Qed.

Record rel_symbol : Type := {
  rel_m : nat;
  rel_n : nat;
  rel_pred : relation A B;
  rel_member : stab rel_m rel_n rel_pred
}.

Record mixed_rel_symbol : Type := {
  mrel_shape : list coord_sort;
  mrel_pred : mixed_relation;
  mrel_member : mixed_observable mrel_shape mrel_pred
}.

Definition block_mixed_symbol (r : rel_symbol) : mixed_rel_symbol.
Proof.
  refine
    {| mrel_shape := block_mixed_shape (rel_m r) (rel_n r);
       mrel_pred := block_mixed_relation (rel_m r) (rel_n r) (rel_pred r);
       mrel_member := _ |}.
  apply MixedBlock.
  destruct (rel_member r) as [Hobs _].
  exact Hobs.
Defined.

Inductive sterm : Type :=
| SVar : nat -> sterm.

Inductive tterm : Type :=
| TVar : nat -> tterm
| TMap : nat -> tterm.

Inductive mixed_term : Type :=
| MSourceTerm : sterm -> mixed_term
| MTargetTerm : tterm -> mixed_term.

Definition mixed_term_fits (s : coord_sort) (t : mixed_term) : Prop :=
  match s, t with
  | CoordSource, MSourceTerm _ => True
  | CoordTarget, MTargetTerm _ => True
  | _, _ => False
  end.

Definition mixed_terms_shape
    (shape : list coord_sort) (ts : list mixed_term) : Prop :=
  length shape = length ts /\
  forall i s t,
    nth_error shape i = Some s ->
    nth_error ts i = Some t ->
    mixed_term_fits s t.

Definition block_mixed_terms (ss : list sterm) (ts : list tterm) :
    list mixed_term :=
  map MSourceTerm ss ++ map MTargetTerm ts.

Lemma source_terms_shape :
  forall ss,
    mixed_terms_shape (repeat CoordSource (length ss)) (map MSourceTerm ss).
Proof.
  induction ss as [| s ss IH].
  - split; simpl; auto.
    intros [| i] q t Hq Ht; discriminate.
  - destruct IH as [IHlen IHfit].
    split; simpl; auto.
    intros [| i] q t Hq Ht; simpl in *.
    + inversion Hq; inversion Ht; subst. exact I.
    + eapply IHfit; eauto.
Qed.

Lemma target_terms_shape :
  forall ts,
    mixed_terms_shape (repeat CoordTarget (length ts)) (map MTargetTerm ts).
Proof.
  induction ts as [| t ts IH].
  - split; simpl; auto.
    intros [| i] q u Hq Hu; discriminate.
  - destruct IH as [IHlen IHfit].
    split; simpl; auto.
    intros [| i] q u Hq Hu; simpl in *.
    + inversion Hq; inversion Hu; subst. exact I.
    + eapply IHfit; eauto.
Qed.

Lemma mixed_terms_shape_app :
  forall shape1 ts1 shape2 ts2,
    mixed_terms_shape shape1 ts1 ->
    mixed_terms_shape shape2 ts2 ->
    mixed_terms_shape (shape1 ++ shape2) (ts1 ++ ts2).
Proof.
  intros shape1 ts1 shape2 ts2 [Hlen1 Hfit1] [Hlen2 Hfit2].
  split.
  - rewrite !length_app. lia.
  - intros i s t Hshape Hterm.
    destruct (lt_dec i (length shape1)) as [Hlt | Hnlt].
    + rewrite nth_error_app1 in Hshape by exact Hlt.
      rewrite nth_error_app1 in Hterm by (rewrite <- Hlen1; exact Hlt).
      eapply Hfit1; eauto.
    + assert (Hge : length shape1 <= i) by lia.
      rewrite nth_error_app2 in Hshape by exact Hge.
      rewrite nth_error_app2 in Hterm by (rewrite <- Hlen1; exact Hge).
      rewrite <- Hlen1 in Hterm.
      eapply Hfit2; eauto.
Qed.

Lemma block_mixed_terms_shape :
  forall ss ts,
    mixed_terms_shape
      (block_mixed_shape (length ss) (length ts))
      (block_mixed_terms ss ts).
Proof.
  intros ss ts.
  unfold block_mixed_shape, block_mixed_terms.
  apply mixed_terms_shape_app.
  - apply source_terms_shape.
  - apply target_terms_shape.
Qed.

Inductive formula : Type :=
| FAtom :
    forall (r : rel_symbol) (ss : list sterm) (ts : list tterm),
      length ss = rel_m r ->
      length ts = rel_n r ->
      formula
| FNeg : formula -> formula
| FAnd : formula -> formula -> formula
| FOr : formula -> formula -> formula
| FImp : formula -> formula -> formula
| FIff : formula -> formula -> formula
| FForallS : nat -> formula -> formula
| FExistsS : nat -> formula -> formula
| FForallT : nat -> formula -> formula
| FExistsT : nat -> formula -> formula.

Inductive mixed_formula : Type :=
| MFAtom :
    forall (r : mixed_rel_symbol) (args : list mixed_term),
      mixed_terms_shape (mrel_shape r) args ->
      mixed_formula
| MFNeg : mixed_formula -> mixed_formula
| MFAnd : mixed_formula -> mixed_formula -> mixed_formula
| MFOr : mixed_formula -> mixed_formula -> mixed_formula
| MFImp : mixed_formula -> mixed_formula -> mixed_formula
| MFIff : mixed_formula -> mixed_formula -> mixed_formula
| MFForallS : nat -> mixed_formula -> mixed_formula
| MFExistsS : nat -> mixed_formula -> mixed_formula
| MFForallT : nat -> mixed_formula -> mixed_formula
| MFExistsT : nat -> mixed_formula -> mixed_formula.

Definition atom (r : rel_symbol) (ss : list sterm) (ts : list tterm)
    (Hs : length ss = rel_m r) (Ht : length ts = rel_n r) : formula :=
  FAtom r ss ts Hs Ht.

Definition block_mixed_atom
    (r : rel_symbol) (ss : list sterm) (ts : list tterm)
    (Hs : length ss = rel_m r) (Ht : length ts = rel_n r) : mixed_formula.
Proof.
  refine (MFAtom (block_mixed_symbol r) (block_mixed_terms ss ts) _).
  simpl.
  rewrite <- Hs.
  rewrite <- Ht.
  apply block_mixed_terms_shape.
Defined.

Fixpoint block_mixed_formula (phi : formula) : mixed_formula :=
  match phi with
  | FAtom r ss ts Hs Ht => block_mixed_atom r ss ts Hs Ht
  | FNeg psi => MFNeg (block_mixed_formula psi)
  | FAnd psi chi => MFAnd (block_mixed_formula psi) (block_mixed_formula chi)
  | FOr psi chi => MFOr (block_mixed_formula psi) (block_mixed_formula chi)
  | FImp psi chi => MFImp (block_mixed_formula psi) (block_mixed_formula chi)
  | FIff psi chi => MFIff (block_mixed_formula psi) (block_mixed_formula chi)
  | FForallS i psi => MFForallS i (block_mixed_formula psi)
  | FExistsS i psi => MFExistsS i (block_mixed_formula psi)
  | FForallT i psi => MFForallT i (block_mixed_formula psi)
  | FExistsT i psi => MFExistsT i (block_mixed_formula psi)
  end.

Definition remove_nat (i : nat) (xs : list nat) : list nat :=
  filter (fun j => negb (Nat.eqb i j)) xs.

Definition fv_s_sterm (t : sterm) : list nat :=
  match t with
  | SVar i => [i]
  end.

Definition fv_s_tterm (t : tterm) : list nat :=
  match t with
  | TVar _ => []
  | TMap i => [i]
  end.

Definition fv_t_tterm (t : tterm) : list nat :=
  match t with
  | TVar i => [i]
  | TMap _ => []
  end.

Definition fv_s_terms (ts : list sterm) : list nat :=
  concat (map fv_s_sterm ts).

Definition fv_s_tterms (ts : list tterm) : list nat :=
  concat (map fv_s_tterm ts).

Definition fv_t_tterms (ts : list tterm) : list nat :=
  concat (map fv_t_tterm ts).

Fixpoint fv_s (phi : formula) : list nat :=
  match phi with
  | FAtom _ ss ts _ _ => fv_s_terms ss ++ fv_s_tterms ts
  | FNeg psi => fv_s psi
  | FAnd psi chi | FOr psi chi | FImp psi chi | FIff psi chi =>
      fv_s psi ++ fv_s chi
  | FForallS i psi | FExistsS i psi => remove_nat i (fv_s psi)
  | FForallT _ psi | FExistsT _ psi => fv_s psi
  end.

Fixpoint fv_t (phi : formula) : list nat :=
  match phi with
  | FAtom _ _ ts _ _ => fv_t_tterms ts
  | FNeg psi => fv_t psi
  | FAnd psi chi | FOr psi chi | FImp psi chi | FIff psi chi =>
      fv_t psi ++ fv_t chi
  | FForallS _ psi | FExistsS _ psi => fv_t psi
  | FForallT i psi | FExistsT i psi => remove_nat i (fv_t psi)
  end.

Record compat_model : Type := {
  domS : Type;
  domT : Type;
  interp_f : domS -> domT;
  alpha : domS -> A;
  beta : domT -> B;
  compat_eq : forall x, beta (interp_f x) = f (alpha x)
}.

Record assignment (M : compat_model) : Type := {
  as_src : nat -> domS M;
  as_tgt : nat -> domT M
}.

Definition updateS {M : compat_model}
    (sigma : assignment M) (i : nat) (u : domS M) : assignment M :=
  {| as_src := fun j => if Nat.eq_dec j i then u else as_src M sigma j;
     as_tgt := as_tgt M sigma |}.

Definition updateT {M : compat_model}
    (sigma : assignment M) (i : nat) (v : domT M) : assignment M :=
  {| as_src := as_src M sigma;
     as_tgt := fun j => if Nat.eq_dec j i then v else as_tgt M sigma j |}.

Definition eval_sterm {M : compat_model}
    (sigma : assignment M) (t : sterm) : domS M :=
  match t with
  | SVar i => as_src M sigma i
  end.

Definition eval_tterm {M : compat_model}
    (sigma : assignment M) (t : tterm) : domT M :=
  match t with
  | TVar i => as_tgt M sigma i
  | TMap i => interp_f M (as_src M sigma i)
  end.

Definition eval_sterms_A {M : compat_model}
    (sigma : assignment M) (ts : list sterm) : list A :=
  map (fun t => alpha M (eval_sterm sigma t)) ts.

Definition eval_tterms_B {M : compat_model}
    (sigma : assignment M) (ts : list tterm) : list B :=
  map (fun t => beta M (eval_tterm sigma t)) ts.

Definition eval_mixed_term {M : compat_model}
    (sigma : assignment M) (t : mixed_term) : mixed_value :=
  match t with
  | MSourceTerm s => inl (alpha M (eval_sterm sigma s))
  | MTargetTerm t => inr (beta M (eval_tterm sigma t))
  end.

Definition eval_mixed_terms {M : compat_model}
    (sigma : assignment M) (ts : list mixed_term) : list mixed_value :=
  map (eval_mixed_term sigma) ts.

Definition mixed_atom_sat {M : compat_model}
    (sigma : assignment M) (r : mixed_rel_symbol)
    (args : list mixed_term) : Prop :=
  mrel_pred r (eval_mixed_terms sigma args).

Fixpoint mixed_sat {M : compat_model}
    (sigma : assignment M) (phi : mixed_formula) : Prop :=
  match phi with
  | MFAtom r args _ => mixed_atom_sat sigma r args
  | MFNeg psi => ~ mixed_sat sigma psi
  | MFAnd psi chi => mixed_sat sigma psi /\ mixed_sat sigma chi
  | MFOr psi chi => mixed_sat sigma psi \/ mixed_sat sigma chi
  | MFImp psi chi => ~ mixed_sat sigma psi \/ mixed_sat sigma chi
  | MFIff psi chi => mixed_sat sigma psi <-> mixed_sat sigma chi
  | MFForallS i psi => forall u, mixed_sat (updateS sigma i u) psi
  | MFExistsS i psi => exists u, mixed_sat (updateS sigma i u) psi
  | MFForallT i psi => forall v, mixed_sat (updateT sigma i v) psi
  | MFExistsT i psi => exists v, mixed_sat (updateT sigma i v) psi
  end.

Lemma eval_block_mixed_terms :
  forall (M : compat_model) (sigma : assignment M) ss ts,
    eval_mixed_terms sigma (block_mixed_terms ss ts) =
    block_mixed_tuple (eval_sterms_A sigma ss) (eval_tterms_B sigma ts).
Proof.
  intros M sigma ss ts.
  unfold eval_mixed_terms, block_mixed_terms, block_mixed_tuple,
    eval_sterms_A, eval_tterms_B.
  rewrite map_app.
  rewrite !map_map.
  reflexivity.
Qed.

Lemma map_inr_injective :
  forall ys ys' : list B,
    map (@inr A B) ys = map (@inr A B) ys' -> ys = ys'.
Proof.
  induction ys as [| b ys IH]; destruct ys' as [| b' ys']; simpl; intro H;
    try discriminate.
  - reflexivity.
  - inversion H; subst. f_equal. apply IH. assumption.
Qed.

Lemma block_mixed_tuple_injective :
  forall xs xs' ys ys',
    block_mixed_tuple xs ys = block_mixed_tuple xs' ys' ->
    xs = xs' /\ ys = ys'.
Proof.
  induction xs as [| a xs IH]; destruct xs' as [| a' xs'];
    intros ys ys' H; simpl in H.
  - split; [reflexivity |].
    apply map_inr_injective. exact H.
  - destruct ys as [| b ys]; discriminate.
  - destruct ys' as [| b' ys']; discriminate.
  - inversion H; subst.
    destruct (IH xs' ys ys' H2) as [Hxs Hys].
    split; congruence.
Qed.

Fixpoint sat {M : compat_model} (sigma : assignment M)
    (phi : formula) : Prop :=
  match phi with
  | FAtom r ss ts _ _ =>
      rel_pred r (eval_sterms_A sigma ss) (eval_tterms_B sigma ts)
  | FNeg psi => ~ sat sigma psi
  | FAnd psi chi => sat sigma psi /\ sat sigma chi
  | FOr psi chi => sat sigma psi \/ sat sigma chi
  | FImp psi chi => ~ sat sigma psi \/ sat sigma chi
  | FIff psi chi => sat sigma psi <-> sat sigma chi
  | FForallS i psi => forall u, sat (updateS sigma i u) psi
  | FExistsS i psi => exists u, sat (updateS sigma i u) psi
  | FForallT i psi => forall v, sat (updateT sigma i v) psi
  | FExistsT i psi => exists v, sat (updateT sigma i v) psi
  end.

Theorem atom_block_mixed_sat_iff :
  forall (M : compat_model) (sigma : assignment M)
    (r : rel_symbol) ss ts Hs Ht,
    sat sigma (atom r ss ts Hs Ht) <->
    mixed_sat sigma (block_mixed_atom r ss ts Hs Ht).
Proof.
  intros M sigma r ss ts Hs Ht.
  split.
  - intro Hsat.
    unfold atom in Hsat.
    simpl in Hsat.
    unfold mixed_sat, block_mixed_atom.
    simpl.
    unfold mixed_atom_sat.
    simpl.
    rewrite eval_block_mixed_terms.
    unfold block_mixed_relation.
    split.
    + replace (rel_m r) with (length (eval_sterms_A sigma ss)).
      * replace (rel_n r) with (length (eval_tterms_B sigma ts)).
        -- apply block_mixed_tuple_shape.
        -- unfold eval_tterms_B. rewrite length_map. exact Ht.
      * unfold eval_sterms_A. rewrite length_map. exact Hs.
    + exists (eval_sterms_A sigma ss), (eval_tterms_B sigma ts).
      split; [reflexivity | exact Hsat].
  - intro Hmixed.
    unfold atom.
    simpl.
    unfold mixed_sat, block_mixed_atom in Hmixed.
    simpl in Hmixed.
    unfold mixed_atom_sat in Hmixed.
    simpl in Hmixed.
    rewrite eval_block_mixed_terms in Hmixed.
    unfold block_mixed_relation in Hmixed.
    destruct Hmixed as [_ [xs [ys [Heq HR]]]].
    destruct (block_mixed_tuple_injective
      (eval_sterms_A sigma ss) xs (eval_tterms_B sigma ts) ys Heq)
      as [Hxs Hys].
    subst. exact HR.
Qed.

Theorem atom_sat_implies_block_mixed_sat :
  forall (M : compat_model) (sigma : assignment M)
    (r : rel_symbol) ss ts Hs Ht,
    sat sigma (atom r ss ts Hs Ht) ->
    mixed_sat sigma (block_mixed_atom r ss ts Hs Ht).
Proof.
  intros M sigma r ss ts Hs Ht Hsat.
  apply (proj1 (atom_block_mixed_sat_iff M sigma r ss ts Hs Ht)).
  exact Hsat.
Qed.

Theorem block_mixed_formula_sat :
  forall (M : compat_model) (sigma : assignment M) (phi : formula),
    sat sigma phi <-> mixed_sat sigma (block_mixed_formula phi).
Proof.
  intros M sigma phi.
  revert sigma.
  induction phi as
    [r ss ts Hs Ht | psi IH | psi IHpsi chi IHchi
    | psi IHpsi chi IHchi | psi IHpsi chi IHchi
    | psi IHpsi chi IHchi | i psi IH | i psi IH
    | i psi IH | i psi IH]; intro sigma; simpl.
  - exact (atom_block_mixed_sat_iff M sigma r ss ts Hs Ht).
  - specialize (IH sigma). tauto.
  - specialize (IHpsi sigma). specialize (IHchi sigma). tauto.
  - specialize (IHpsi sigma). specialize (IHchi sigma). tauto.
  - specialize (IHpsi sigma). specialize (IHchi sigma). tauto.
  - specialize (IHpsi sigma). specialize (IHchi sigma). tauto.
  - split; intros Hall u.
    + apply (proj1 (IH (updateS sigma i u))). apply Hall.
    + apply (proj2 (IH (updateS sigma i u))). apply Hall.
  - split; intros [u Hu]; exists u.
    + apply (proj1 (IH (updateS sigma i u))). exact Hu.
    + apply (proj2 (IH (updateS sigma i u))). exact Hu.
  - split; intros Hall v.
    + apply (proj1 (IH (updateT sigma i v))). apply Hall.
    + apply (proj2 (IH (updateT sigma i v))). apply Hall.
  - split; intros [v Hv]; exists v.
    + apply (proj1 (IH (updateT sigma i v))). exact Hv.
    + apply (proj2 (IH (updateT sigma i v))). exact Hv.
Qed.

Definition graph_symbol : rel_symbol.
Proof.
  refine {| rel_m := 1; rel_n := 1; rel_pred := graph_rel; rel_member := _ |}.
  split; [apply graph_observable | apply graph_stable].
Defined.

Definition kernel_symbol : rel_symbol.
Proof.
  refine {| rel_m := 2; rel_n := 0; rel_pred := kernel_rel; rel_member := _ |}.
  apply kernel_in_stab.
Defined.

Definition image_symbol : rel_symbol.
Proof.
  refine {| rel_m := 0; rel_n := 1; rel_pred := image_rel; rel_member := _ |}.
  apply image_in_stab.
Defined.

Definition unreachable_symbol : rel_symbol.
Proof.
  refine {| rel_m := 0; rel_n := 1; rel_pred := unreachable_rel; rel_member := _ |}.
  apply unreachable_in_stab.
Defined.

Definition graph_atom (i j : nat) : formula :=
  atom graph_symbol [SVar i] [TVar j] eq_refl eq_refl.

Definition Reach (i j : nat) : formula :=
  FExistsS i (graph_atom i j).

Definition Unreach (i j : nat) : formula :=
  FNeg (Reach i j).

Definition Diamond (i j : nat) (phi : formula) : formula :=
  FExistsS i (FAnd (graph_atom i j) phi).

Definition Box (i j : nat) (phi : formula) : formula :=
  FForallS i (FImp (graph_atom i j) phi).

Lemma in_remove_nat_intro :
  forall i j xs, i <> j -> In i xs -> In i (remove_nat j xs).
Proof.
  unfold remove_nat.
  intros i j xs Hij Hin.
  apply filter_In. split; auto.
  apply negb_true_iff.
  apply Nat.eqb_neq. intro Heq. apply Hij. symmetry. exact Heq.
Qed.

Lemma in_remove_nat_elim :
  forall i j xs, In i (remove_nat j xs) -> i <> j /\ In i xs.
Proof.
  unfold remove_nat.
  intros i j xs Hin.
  apply filter_In in Hin as [Hin Hneq].
  apply negb_true_iff in Hneq.
  apply Nat.eqb_neq in Hneq.
  split; auto.
Qed.

Lemma in_app_left_nat :
  forall (i : nat) (xs ys : list nat), In i xs -> In i (xs ++ ys).
Proof.
  intros i xs ys H. apply in_or_app. left. exact H.
Qed.

Lemma in_app_right_nat :
  forall (i : nat) (xs ys : list nat), In i ys -> In i (xs ++ ys).
Proof.
  intros i xs ys H. apply in_or_app. right. exact H.
Qed.

Lemma eval_sterms_same_fiber :
  forall (M : compat_model) (sigma tau : assignment M) ss,
    (forall i, In i (fv_s_terms ss) ->
      f (alpha M (as_src M sigma i)) =
      f (alpha M (as_src M tau i))) ->
    same_fiber_list (eval_sterms_A sigma ss) (eval_sterms_A tau ss).
Proof.
  intros M sigma tau ss.
  induction ss as [| [i] rest IH]; intros Hs; simpl.
  - constructor.
  - constructor.
    + apply Hs. simpl. auto.
    + apply IH. intros j Hj. apply Hs. simpl. auto.
Qed.

Lemma eval_tterms_B_eq :
  forall (M : compat_model) (sigma tau : assignment M) ts,
    (forall i, In i (fv_s_tterms ts) ->
      f (alpha M (as_src M sigma i)) =
      f (alpha M (as_src M tau i))) ->
    (forall i, In i (fv_t_tterms ts) ->
      beta M (as_tgt M sigma i) =
      beta M (as_tgt M tau i)) ->
    eval_tterms_B sigma ts = eval_tterms_B tau ts.
Proof.
  intros M sigma tau ts.
  induction ts as [| t rest IH]; intros Hs Ht; simpl.
  - reflexivity.
  - f_equal.
    + destruct t as [i | i]; simpl.
      * apply Ht. simpl. auto.
      * rewrite !compat_eq. apply Hs. simpl. auto.
    + apply IH.
      * intros j Hj. apply Hs. simpl. destruct t; simpl; auto.
      * intros j Hj. apply Ht. simpl. destruct t; simpl; auto.
Qed.

Theorem formula_stability :
  forall (M : compat_model) (sigma tau : assignment M) (phi : formula),
    (forall i, In i (fv_s phi) ->
      f (alpha M (as_src M sigma i)) =
      f (alpha M (as_src M tau i))) ->
    (forall i, In i (fv_t phi) ->
      beta M (as_tgt M sigma i) =
      beta M (as_tgt M tau i)) ->
    (sat sigma phi <-> sat tau phi).
Proof.
  intros M sigma tau phi.
  revert sigma tau.
  induction phi as
    [r ss ts HlenS HlenT | psi IH | psi IHpsi chi IHchi
    | psi IHpsi chi IHchi | psi IHpsi chi IHchi
    | psi IHpsi chi IHchi | i psi IH | i psi IH
    | i psi IH | i psi IH]; intros sigma tau; simpl; intros Hs Ht.
  - destruct (rel_member r) as [_ Hstable].
    assert (Hsf :
      same_fiber_list (eval_sterms_A sigma ss) (eval_sterms_A tau ss)).
    { apply eval_sterms_same_fiber. intros k Hk.
      apply Hs. apply in_or_app. left. exact Hk. }
    assert (Hteq : eval_tterms_B sigma ts = eval_tterms_B tau ts).
    { apply eval_tterms_B_eq.
      - intros k Hk. apply Hs. apply in_or_app. right. exact Hk.
      - intros k Hk. apply Ht. exact Hk. }
    rewrite <- Hteq.
    apply Hstable.
    + unfold eval_sterms_A. rewrite length_map. exact HlenS.
    + unfold eval_sterms_A. rewrite length_map. exact HlenS.
    + unfold eval_tterms_B. rewrite length_map. exact HlenT.
    + exact Hsf.
  - specialize (IH sigma tau Hs Ht). tauto.
  - specialize (IHpsi sigma tau (fun k H => Hs k (in_app_left_nat k _ _ H))
                    (fun k H => Ht k (in_app_left_nat k _ _ H))).
    specialize (IHchi sigma tau (fun k H => Hs k (in_app_right_nat k _ _ H))
                    (fun k H => Ht k (in_app_right_nat k _ _ H))).
    tauto.
  - specialize (IHpsi sigma tau (fun k H => Hs k (in_app_left_nat k _ _ H))
                    (fun k H => Ht k (in_app_left_nat k _ _ H))).
    specialize (IHchi sigma tau (fun k H => Hs k (in_app_right_nat k _ _ H))
                    (fun k H => Ht k (in_app_right_nat k _ _ H))).
    tauto.
  - specialize (IHpsi sigma tau (fun k H => Hs k (in_app_left_nat k _ _ H))
                    (fun k H => Ht k (in_app_left_nat k _ _ H))).
    specialize (IHchi sigma tau (fun k H => Hs k (in_app_right_nat k _ _ H))
                    (fun k H => Ht k (in_app_right_nat k _ _ H))).
    tauto.
  - specialize (IHpsi sigma tau (fun k H => Hs k (in_app_left_nat k _ _ H))
                    (fun k H => Ht k (in_app_left_nat k _ _ H))).
    specialize (IHchi sigma tau (fun k H => Hs k (in_app_right_nat k _ _ H))
                    (fun k H => Ht k (in_app_right_nat k _ _ H))).
    tauto.
  - split; intros Hall u.
    + assert (Hs' : forall k, In k (fv_s psi) ->
          f (alpha M (as_src M (updateS sigma i u) k)) =
          f (alpha M (as_src M (updateS tau i u) k))).
      { intros k Hk. unfold updateS; simpl.
        destruct (Nat.eq_dec k i) as [-> | Hneq].
        - destruct (Nat.eq_dec i i); [reflexivity | contradiction].
        - destruct (Nat.eq_dec k i); [contradiction |].
          apply Hs. apply in_remove_nat_intro; auto. }
      assert (Ht' : forall k, In k (fv_t psi) ->
          beta M (as_tgt M (updateS sigma i u) k) =
          beta M (as_tgt M (updateS tau i u) k)).
      { intros k Hk. unfold updateS; simpl. apply Ht. exact Hk. }
      apply (proj1 (IH (updateS sigma i u) (updateS tau i u) Hs' Ht')).
      apply Hall.
    + assert (Hs' : forall k, In k (fv_s psi) ->
          f (alpha M (as_src M (updateS sigma i u) k)) =
          f (alpha M (as_src M (updateS tau i u) k))).
      { intros k Hk. unfold updateS; simpl.
        destruct (Nat.eq_dec k i) as [-> | Hneq].
        - destruct (Nat.eq_dec i i); [reflexivity | contradiction].
        - destruct (Nat.eq_dec k i); [contradiction |].
          apply Hs. apply in_remove_nat_intro; auto. }
      assert (Ht' : forall k, In k (fv_t psi) ->
          beta M (as_tgt M (updateS sigma i u) k) =
          beta M (as_tgt M (updateS tau i u) k)).
      { intros k Hk. unfold updateS; simpl. apply Ht. exact Hk. }
      apply (proj2 (IH (updateS sigma i u) (updateS tau i u) Hs' Ht')).
      apply Hall.
  - split; intros [u Hu]; exists u.
    + assert (Hs' : forall k, In k (fv_s psi) ->
          f (alpha M (as_src M (updateS sigma i u) k)) =
          f (alpha M (as_src M (updateS tau i u) k))).
      { intros k Hk. unfold updateS; simpl.
        destruct (Nat.eq_dec k i) as [-> | Hneq].
        - destruct (Nat.eq_dec i i); [reflexivity | contradiction].
        - destruct (Nat.eq_dec k i); [contradiction |].
          apply Hs. apply in_remove_nat_intro; auto. }
      assert (Ht' : forall k, In k (fv_t psi) ->
          beta M (as_tgt M (updateS sigma i u) k) =
          beta M (as_tgt M (updateS tau i u) k)).
      { intros k Hk. unfold updateS; simpl. apply Ht. exact Hk. }
      apply (proj1 (IH (updateS sigma i u) (updateS tau i u) Hs' Ht')).
      exact Hu.
    + assert (Hs' : forall k, In k (fv_s psi) ->
          f (alpha M (as_src M (updateS sigma i u) k)) =
          f (alpha M (as_src M (updateS tau i u) k))).
      { intros k Hk. unfold updateS; simpl.
        destruct (Nat.eq_dec k i) as [-> | Hneq].
        - destruct (Nat.eq_dec i i); [reflexivity | contradiction].
        - destruct (Nat.eq_dec k i); [contradiction |].
          apply Hs. apply in_remove_nat_intro; auto. }
      assert (Ht' : forall k, In k (fv_t psi) ->
          beta M (as_tgt M (updateS sigma i u) k) =
          beta M (as_tgt M (updateS tau i u) k)).
      { intros k Hk. unfold updateS; simpl. apply Ht. exact Hk. }
      apply (proj2 (IH (updateS sigma i u) (updateS tau i u) Hs' Ht')).
      exact Hu.
  - split; intros Hall v.
    + assert (Hs' : forall k, In k (fv_s psi) ->
          f (alpha M (as_src M (updateT sigma i v) k)) =
          f (alpha M (as_src M (updateT tau i v) k))).
      { intros k Hk. unfold updateT; simpl. apply Hs. exact Hk. }
      assert (Ht' : forall k, In k (fv_t psi) ->
          beta M (as_tgt M (updateT sigma i v) k) =
          beta M (as_tgt M (updateT tau i v) k)).
      { intros k Hk. unfold updateT; simpl.
        destruct (Nat.eq_dec k i) as [-> | Hneq].
        - destruct (Nat.eq_dec i i); [reflexivity | contradiction].
        - destruct (Nat.eq_dec k i); [contradiction |].
          apply Ht. apply in_remove_nat_intro; auto. }
      apply (proj1 (IH (updateT sigma i v) (updateT tau i v) Hs' Ht')).
      apply Hall.
    + assert (Hs' : forall k, In k (fv_s psi) ->
          f (alpha M (as_src M (updateT sigma i v) k)) =
          f (alpha M (as_src M (updateT tau i v) k))).
      { intros k Hk. unfold updateT; simpl. apply Hs. exact Hk. }
      assert (Ht' : forall k, In k (fv_t psi) ->
          beta M (as_tgt M (updateT sigma i v) k) =
          beta M (as_tgt M (updateT tau i v) k)).
      { intros k Hk. unfold updateT; simpl.
        destruct (Nat.eq_dec k i) as [-> | Hneq].
        - destruct (Nat.eq_dec i i); [reflexivity | contradiction].
        - destruct (Nat.eq_dec k i); [contradiction |].
          apply Ht. apply in_remove_nat_intro; auto. }
      apply (proj2 (IH (updateT sigma i v) (updateT tau i v) Hs' Ht')).
      apply Hall.
  - split; intros [v Hv]; exists v.
    + assert (Hs' : forall k, In k (fv_s psi) ->
          f (alpha M (as_src M (updateT sigma i v) k)) =
          f (alpha M (as_src M (updateT tau i v) k))).
      { intros k Hk. unfold updateT; simpl. apply Hs. exact Hk. }
      assert (Ht' : forall k, In k (fv_t psi) ->
          beta M (as_tgt M (updateT sigma i v) k) =
          beta M (as_tgt M (updateT tau i v) k)).
      { intros k Hk. unfold updateT; simpl.
        destruct (Nat.eq_dec k i) as [-> | Hneq].
        - destruct (Nat.eq_dec i i); [reflexivity | contradiction].
        - destruct (Nat.eq_dec k i); [contradiction |].
          apply Ht. apply in_remove_nat_intro; auto. }
      apply (proj1 (IH (updateT sigma i v) (updateT tau i v) Hs' Ht')).
      exact Hv.
    + assert (Hs' : forall k, In k (fv_s psi) ->
          f (alpha M (as_src M (updateT sigma i v) k)) =
          f (alpha M (as_src M (updateT tau i v) k))).
      { intros k Hk. unfold updateT; simpl. apply Hs. exact Hk. }
      assert (Ht' : forall k, In k (fv_t psi) ->
          beta M (as_tgt M (updateT sigma i v) k) =
          beta M (as_tgt M (updateT tau i v) k)).
      { intros k Hk. unfold updateT; simpl.
        destruct (Nat.eq_dec k i) as [-> | Hneq].
        - destruct (Nat.eq_dec i i); [reflexivity | contradiction].
        - destruct (Nat.eq_dec k i); [contradiction |].
          apply Ht. apply in_remove_nat_intro; auto. }
      apply (proj2 (IH (updateT sigma i v) (updateT tau i v) Hs' Ht')).
      exact Hv.
Qed.

Definition entails (Gamma : list formula) (phi : formula) : Prop :=
  forall (M : compat_model) (sigma : assignment M),
    (forall gamma, In gamma Gamma -> sat sigma gamma) ->
    sat sigma phi.

Definition rule (Gamma : list formula) (phi : formula) : Prop :=
  entails Gamma phi.

Inductive proves (Gamma : list formula) : formula -> Prop :=
| ProvesHyp :
    forall phi, In phi Gamma -> proves Gamma phi
| ProvesRule :
    forall Delta phi,
      (forall gamma, In gamma Delta -> proves Gamma gamma) ->
      rule Delta phi ->
      proves Gamma phi.

Theorem proves_sound :
  forall Gamma phi, proves Gamma phi -> entails Gamma phi.
Proof.
  unfold entails, rule.
  intros Gamma phi Hpr.
  induction Hpr as [phi Hin | Delta phi HDelta IHDelta Hrule].
  - intros M sigma Hctx. apply Hctx. exact Hin.
  - intros M sigma Hctx.
    apply Hrule.
    intros gamma Hgamma.
    apply (IHDelta gamma Hgamma M sigma Hctx).
Qed.

Definition theorem (phi : formula) : Prop := proves [] phi.

Theorem theorem_sound :
  forall phi M (sigma : assignment M),
    theorem phi -> sat sigma phi.
Proof.
  intros phi M sigma Hthm.
  apply (proves_sound [] phi Hthm M sigma).
  intros gamma Hin. contradiction.
Qed.

Record formal_system : Type := {
  fs_form : Type;
  fs_model : Type;
  fs_assignment : fs_model -> Type;
  fs_sat : forall M : fs_model, fs_assignment M -> fs_form -> Prop;
  fs_rule : list fs_form -> fs_form -> Prop;
  fs_proves : list fs_form -> fs_form -> Prop;
  fs_theorem : fs_form -> Prop
}.

Definition Sys : formal_system :=
  {| fs_form := formula;
     fs_model := compat_model;
     fs_assignment := assignment;
     fs_sat := @sat;
     fs_rule := rule;
     fs_proves := proves;
     fs_theorem := theorem |}.

Definition unary_source_rel (P : A -> Prop) : relation A B :=
  fun xs ys =>
    match xs, ys with
    | [a], [] => P a
    | _, _ => False
    end.

Definition unary_target_rel (Q : B -> Prop) : relation A B :=
  fun xs ys =>
    match xs, ys with
    | [], [b] => Q b
    | _, _ => False
    end.

Definition pullback_target (Q : B -> Prop) : A -> Prop :=
  fun a => Q (f a).

Lemma pullback_target_stable :
  forall Q, stable 1 0 (unary_source_rel (pullback_target Q)).
Proof.
  unfold stable, same_fiber_list, unary_source_rel, pullback_target.
  intros Q xs xs' ys Hx Hx' Hy Hfib.
  destruct xs as [| a xs]; try discriminate.
  destruct xs as [| ax xs]; try discriminate.
  destruct xs' as [| a' xs']; try discriminate.
  destruct xs' as [| ax' xs']; try discriminate.
  destruct ys as [| b ys]; try discriminate.
  inversion Hfib; subst.
  simpl in *.
  split; intro H; congruence.
Qed.

Definition exists_push (P : A -> Prop) : B -> Prop :=
  fun b => exists a, P a /\ f a = b.

Definition forall_push (P : A -> Prop) : B -> Prop :=
  fun b => forall a, f a = b -> P a.

Lemma forall_push_complement :
  forall P b,
    forall_push P b <-> ~ exists_push (fun a => ~ P a) b.
Proof.
  intros P b.
  unfold forall_push, exists_push.
  split.
  - intros Hall [a [HnotP Hfa]]. apply HnotP. apply Hall. exact Hfa.
  - intros Hno a Hfa.
    apply NNPP. intro HnotP.
    apply Hno. exists a. split; auto.
Qed.

Definition standard_model : compat_model :=
  {| domS := A;
     domT := B;
     interp_f := f;
     alpha := fun a => a;
     beta := fun b => b;
     compat_eq := fun _ => eq_refl |}.

Theorem standard_model_nontrivial :
  forall sigma : assignment standard_model,
    sat sigma (FOr (Reach 0 0) (FNeg (Reach 0 0))) /\
    ~ sat sigma (FAnd (Reach 0 0) (FNeg (Reach 0 0))).
Proof.
  intro sigma.
  simpl.
  destruct (classic (sat sigma (Reach 0 0))) as [H | H].
  - split.
    + left. exact H.
    + intros [_ Hnot]. exact (Hnot H).
  - split.
    + right. exact H.
    + intros [Hyes _]. exact (H Hyes).
Qed.
Lemma standard_reach_image :
  forall (sigma : assignment standard_model) i j,
    sat sigma (Reach i j) <-> image_rel [] [as_tgt standard_model sigma j].
Proof.
  intros sigma i j. simpl.
  unfold graph_rel, image_rel, updateS. simpl.
  split.
  - intros [u Hu]. exists u.
    destruct (Nat.eq_dec i i); [exact Hu | contradiction].
  - intros [u Hu]. exists u.
    destruct (Nat.eq_dec i i); [exact Hu | contradiction].
Qed.

Definition unreachable_point (b : B) : Prop :=
  ~ exists a, f a = b.

Lemma standard_unreachable_diamond_false :
  forall (sigma : assignment standard_model) i j phi b,
    as_tgt standard_model sigma j = b ->
    unreachable_point b ->
    ~ sat sigma (Diamond i j phi).
Proof.
  intros sigma i j phi b Hb Hunr [u [Hgraph _]].
  simpl in Hgraph.
  unfold graph_rel, updateS in Hgraph. simpl in Hgraph.
  destruct (Nat.eq_dec i i) as [_ | Hbad]; [| contradiction].
  apply Hunr. exists u. rewrite <- Hb. exact Hgraph.
Qed.

Lemma standard_unreachable_box_true :
  forall (sigma : assignment standard_model) i j phi b,
    as_tgt standard_model sigma j = b ->
    unreachable_point b ->
    sat sigma (Box i j phi).
Proof.
  intros sigma i j phi b Hb Hunr u.
  simpl.
  left.
  unfold graph_rel, updateS. simpl.
  intro H.
  destruct (Nat.eq_dec i i) as [_ | Hbad]; [| contradiction].
  apply Hunr. exists u. rewrite <- Hb. exact H.
Qed.

Lemma injective_kernel_delta :
  injective ->
  forall a a', kernel_rel [a; a'] [] <-> source_diag_rel [a; a'] [].
Proof.
  intros Hinj a a'. rewrite kernel_char. simpl.
  split.
  - intro H. apply Hinj. exact H.
  - intro H. subst. reflexivity.
Qed.

Lemma noninjective_kernel_not_delta :
  forall a a',
    a <> a' ->
    f a = f a' ->
    kernel_rel [a; a'] [] /\ ~ source_diag_rel [a; a'] [].
Proof.
  intros a a' Hneq Hfib.
  split.
  - apply kernel_char. exact Hfib.
  - simpl. exact Hneq.
Qed.

Lemma surjective_image_full :
  surjective ->
  forall b, image_rel [] [b].
Proof.
  intros Hsurj b. simpl. apply Hsurj.
Qed.

Lemma surjective_unreachable_empty :
  surjective ->
  forall b, ~ unreachable_rel [] [b].
Proof.
  unfold unreachable_rel, compl_rel.
  intros Hsurj b [_ Hn].
  apply Hn. apply surjective_image_full; auto.
Qed.

Lemma nonsurjective_unreachable_nonempty :
  (exists b, ~ exists a, f a = b) ->
  exists b, unreachable_rel [] [b].
Proof.
  intros [b Hb]. exists b.
  repeat split; simpl; auto.
Qed.

Lemma constant_kernel_full :
  constant_map ->
  forall a a', kernel_rel [a; a'] [].
Proof.
  intros Hc a a'. apply kernel_char. apply Hc.
Qed.

Section Composition.

Variable C : Type.
Variable g : B -> C.

Definition comp_map (a : A) : C := g (f a).

Definition comp_kernel_rel : list A -> list C -> Prop :=
  fun xs ys =>
    match xs, ys with
    | [a; a'], [] => g (f a) = g (f a')
    | _, _ => False
    end.

Definition comp_image_rel : list A -> list C -> Prop :=
  fun xs ys =>
    match xs, ys with
    | [], [c] => exists a, g (f a) = c
    | _, _ => False
    end.

Definition comp_graph_rel : list A -> list C -> Prop :=
  fun xs ys =>
    match xs, ys with
    | [a], [c] => exists b, f a = b /\ g b = c
    | _, _ => False
    end.

Lemma comp_kernel_char :
  forall a a',
    comp_kernel_rel [a; a'] [] <-> g (f a) = g (f a').
Proof. intros a a'. simpl. tauto. Qed.

Lemma comp_image_char :
  forall c,
    comp_image_rel [] [c] <-> exists a, g (f a) = c.
Proof. intros c. simpl. tauto. Qed.

Lemma comp_graph_char :
  forall a c,
    comp_graph_rel [a] [c] <-> exists b, f a = b /\ g b = c.
Proof. intros a c. simpl. tauto. Qed.

End Composition.

End ArrowSystem.

Record arrow_object : Type := {
  arr_src : Type;
  arr_tgt : Type;
  arr_fun : arr_src -> arr_tgt
}.

Record arrow_morphism (F G : arrow_object) : Type := {
  arr_left : arr_src F -> arr_src G;
  arr_right : arr_tgt F -> arr_tgt G;
  arr_square :
    forall a, arr_right (arr_fun F a) = arr_fun G (arr_left a)
}.

Definition arrow_id (F : arrow_object) : arrow_morphism F F :=
  {| arr_left := fun a => a;
     arr_right := fun b => b;
     arr_square := fun _ => eq_refl |}.

Definition arrow_comp {F G H : arrow_object}
    (u : arrow_morphism F G) (v : arrow_morphism G H) :
    arrow_morphism F H :=
  {| arr_left := fun a => arr_left G H v (arr_left F G u a);
     arr_right := fun b => arr_right G H v (arr_right F G u b);
     arr_square := fun a =>
       eq_trans
         (f_equal (arr_right G H v) (arr_square F G u a))
         (arr_square G H v (arr_left F G u a)) |}.

Record formal_system_object : Type := {
  obj_form : Type;
  obj_model : Type;
  obj_assignment : obj_model -> Type;
  obj_sat : forall M : obj_model, obj_assignment M -> obj_form -> Prop;
  obj_proves : list obj_form -> obj_form -> Prop
}.

Record formal_system_morphism
    (S T : formal_system_object) : Type := {
  mor_translate : obj_form T -> obj_form S;
  mor_model : obj_model S -> obj_model T;
  mor_assignment :
    forall M : obj_model S,
      obj_assignment S M -> obj_assignment T (mor_model M);
  mor_sat_preserve :
    forall M sigma phi,
      obj_sat S M sigma (mor_translate phi) <->
      obj_sat T (mor_model M) (mor_assignment M sigma) phi;
  mor_proof_preserve :
    forall Gamma phi,
      obj_proves T Gamma phi ->
      obj_proves S (map mor_translate Gamma) (mor_translate phi)
}.

Definition formal_system_id (S : formal_system_object) :
    formal_system_morphism S S.
Proof.
  refine
    {| mor_translate := fun phi => phi;
       mor_model := fun M => M;
       mor_assignment := fun _ sigma => sigma;
       mor_sat_preserve := _;
       mor_proof_preserve := _ |}.
  - intros. tauto.
  - intros Gamma phi H. rewrite map_id. exact H.
Defined.

Definition formal_system_comp {S T U : formal_system_object}
    (u : formal_system_morphism S T)
    (v : formal_system_morphism T U) :
    formal_system_morphism S U.
Proof.
  refine
    {| mor_translate := fun phi => mor_translate S T u (mor_translate T U v phi);
       mor_model := fun M => mor_model T U v (mor_model S T u M);
       mor_assignment := fun M sigma =>
         mor_assignment T U v (mor_model S T u M)
           (mor_assignment S T u M sigma);
       mor_sat_preserve := _;
       mor_proof_preserve := _ |}.
  - intros M sigma phi.
    transitivity
      (obj_sat T (mor_model S T u M)
        (mor_assignment S T u M sigma) (mor_translate T U v phi)).
    + apply mor_sat_preserve.
    + apply mor_sat_preserve.
  - intros Gamma phi Hpr.
    replace (map (fun x : obj_form U =>
       mor_translate S T u (mor_translate T U v x)) Gamma)
      with (map (mor_translate S T u) (map (mor_translate T U v) Gamma)).
    + apply mor_proof_preserve.
      apply mor_proof_preserve. exact Hpr.
    + rewrite map_map. reflexivity.
Defined.

Record formal_system_iso (S T : formal_system_object) : Type := {
  iso_forward : formal_system_morphism S T;
  iso_backward : formal_system_morphism T S;
  iso_forward_backward_form :
    forall phi, mor_translate T S iso_backward (mor_translate S T iso_forward phi) = phi;
  iso_backward_forward_form :
    forall phi, mor_translate S T iso_forward (mor_translate T S iso_backward phi) = phi
}.

Definition relation_pullback {F G : arrow_object}
    (u : arrow_morphism F G)
    (R : relation (arr_src G) (arr_tgt G)) :
    relation (arr_src F) (arr_tgt F) :=
  fun xs ys =>
    R (map (arr_left F G u) xs) (map (arr_right F G u) ys).

Lemma relation_pullback_same_fiber :
  forall {F G : arrow_object} (u : arrow_morphism F G) xs xs',
    same_fiber_list (arr_src F) (arr_tgt F) (arr_fun F) xs xs' ->
    same_fiber_list (arr_src G) (arr_tgt G) (arr_fun G)
      (map (arr_left F G u) xs) (map (arr_left F G u) xs').
Proof.
  intros F G u xs xs' Hfib.
  induction Hfib as [| a a' xs xs' Haa' _ IH].
  - constructor.
  - constructor.
    + rewrite <- (arr_square F G u a).
      rewrite <- (arr_square F G u a').
      now rewrite Haa'.
    + exact IH.
Qed.

Lemma relation_pullback_stable :
  forall {F G : arrow_object} (u : arrow_morphism F G) m n R,
    stable (arr_src G) (arr_tgt G) (arr_fun G) m n R ->
    stable (arr_src F) (arr_tgt F) (arr_fun F) m n
      (relation_pullback u R).
Proof.
  intros F G u m n R Hstable.
  unfold stable, relation_pullback in *.
  intros xs xs' ys Hxs Hxs' Hys Hfib.
  apply Hstable.
  - now rewrite length_map.
  - now rewrite length_map.
  - now rewrite length_map.
  - now apply relation_pullback_same_fiber.
Qed.

Record observable_arrow_morphism
    (F G : arrow_object)
    (primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop)
    (primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop) : Type := {
  oam_arrow : arrow_morphism F G;
  oam_observable_pullback :
    forall m n R,
      observable (arr_src G) (arr_tgt G) (arr_fun G) primitive_G m n R ->
      observable (arr_src F) (arr_tgt F) (arr_fun F) primitive_F m n
        (relation_pullback oam_arrow R)
}.

Definition arrow_system_object
    (F : arrow_object)
    (primitive :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop) :
    formal_system_object :=
  {| obj_form := formula (arr_src F) (arr_tgt F) (arr_fun F) primitive;
     obj_model := compat_model (arr_src F) (arr_tgt F) (arr_fun F);
     obj_assignment := assignment (arr_src F) (arr_tgt F) (arr_fun F);
     obj_sat := @sat (arr_src F) (arr_tgt F) (arr_fun F) primitive;
     obj_proves := proves (arr_src F) (arr_tgt F) (arr_fun F) primitive |}.

Definition pullback_rel_symbol
    {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (r : rel_symbol (arr_src G) (arr_tgt G) (arr_fun G) primitive_G) :
    rel_symbol (arr_src F) (arr_tgt F) (arr_fun F) primitive_F.
Proof.
  refine
    {| rel_m := rel_m _ _ _ _ r;
       rel_n := rel_n _ _ _ _ r;
       rel_pred :=
         relation_pullback (oam_arrow F G primitive_F primitive_G u)
           (rel_pred _ _ _ _ r);
       rel_member := _ |}.
  destruct (rel_member _ _ _ _ r) as [Hobs Hstab].
  split.
  - apply oam_observable_pullback. exact Hobs.
  - apply relation_pullback_stable. exact Hstab.
Defined.

Definition arrow_translate_sterm (t : sterm) : sterm := t.

Definition arrow_translate_tterm (t : tterm) : tterm := t.

Fixpoint arrow_formula_translate
    {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (phi : formula (arr_src G) (arr_tgt G) (arr_fun G) primitive_G) :
    formula (arr_src F) (arr_tgt F) (arr_fun F) primitive_F :=
  match phi with
  | @FAtom _ _ _ _ r ss ts Hs Ht =>
      @FAtom (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        (pullback_rel_symbol u r)
        ss ts Hs Ht
  | @FNeg _ _ _ _ psi =>
      @FNeg (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        (arrow_formula_translate u psi)
  | @FAnd _ _ _ _ psi chi =>
      @FAnd (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        (arrow_formula_translate u psi) (arrow_formula_translate u chi)
  | @FOr _ _ _ _ psi chi =>
      @FOr (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        (arrow_formula_translate u psi) (arrow_formula_translate u chi)
  | @FImp _ _ _ _ psi chi =>
      @FImp (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        (arrow_formula_translate u psi) (arrow_formula_translate u chi)
  | @FIff _ _ _ _ psi chi =>
      @FIff (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        (arrow_formula_translate u psi) (arrow_formula_translate u chi)
  | @FForallS _ _ _ _ i psi =>
      @FForallS (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        i (arrow_formula_translate u psi)
  | @FExistsS _ _ _ _ i psi =>
      @FExistsS (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        i (arrow_formula_translate u psi)
  | @FForallT _ _ _ _ i psi =>
      @FForallT (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        i (arrow_formula_translate u psi)
  | @FExistsT _ _ _ _ i psi =>
      @FExistsT (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
        i (arrow_formula_translate u psi)
  end.

Definition arrow_model_map
    {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (M : compat_model (arr_src F) (arr_tgt F) (arr_fun F)) :
    compat_model (arr_src G) (arr_tgt G) (arr_fun G).
Proof.
  refine
    {| domS := domS _ _ _ M;
       domT := domT _ _ _ M;
       interp_f := interp_f _ _ _ M;
       alpha := fun x =>
         arr_left F G (oam_arrow F G primitive_F primitive_G u)
           (alpha _ _ _ M x);
       beta := fun y =>
         arr_right F G (oam_arrow F G primitive_F primitive_G u)
           (beta _ _ _ M y);
       compat_eq := _ |}.
  intro x.
  rewrite compat_eq.
  apply arr_square.
Defined.

Definition arrow_assignment_map
    {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (M : compat_model (arr_src F) (arr_tgt F) (arr_fun F))
    (sigma : assignment (arr_src F) (arr_tgt F) (arr_fun F) M) :
    assignment (arr_src G) (arr_tgt G) (arr_fun G)
      (arrow_model_map u M) :=
  @Build_assignment (arr_src G) (arr_tgt G) (arr_fun G)
    (arrow_model_map u M)
    (as_src _ _ _ M sigma)
    (as_tgt _ _ _ M sigma).

Lemma arrow_eval_sterm :
  forall {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (M : compat_model (arr_src F) (arr_tgt F) (arr_fun F))
    (sigma : assignment (arr_src F) (arr_tgt F) (arr_fun F) M) t,
    @eval_sterm (arr_src G) (arr_tgt G) (arr_fun G)
      (arrow_model_map u M)
      (arrow_assignment_map u M sigma) t =
    @eval_sterm (arr_src F) (arr_tgt F) (arr_fun F) M sigma t.
Proof. intros. destruct t. reflexivity. Qed.

Lemma arrow_eval_tterm :
  forall {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (M : compat_model (arr_src F) (arr_tgt F) (arr_fun F))
    (sigma : assignment (arr_src F) (arr_tgt F) (arr_fun F) M) t,
    @eval_tterm (arr_src G) (arr_tgt G) (arr_fun G)
      (arrow_model_map u M)
      (arrow_assignment_map u M sigma) t =
    @eval_tterm (arr_src F) (arr_tgt F) (arr_fun F) M sigma t.
Proof. intros. destruct t; reflexivity. Qed.

Lemma arrow_eval_sterms_A :
  forall {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (M : compat_model (arr_src F) (arr_tgt F) (arr_fun F))
    (sigma : assignment (arr_src F) (arr_tgt F) (arr_fun F) M) ss,
    @eval_sterms_A (arr_src G) (arr_tgt G) (arr_fun G)
      (arrow_model_map u M) (arrow_assignment_map u M sigma)
      ss =
    map (arr_left F G (oam_arrow F G primitive_F primitive_G u))
      (@eval_sterms_A (arr_src F) (arr_tgt F) (arr_fun F) M sigma ss).
Proof.
  intros F G primitive_F primitive_G u M sigma ss.
  induction ss as [| s ss IH]; simpl.
  - reflexivity.
  - rewrite arrow_eval_sterm. now rewrite IH.
Qed.

Lemma arrow_eval_tterms_B :
  forall {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (M : compat_model (arr_src F) (arr_tgt F) (arr_fun F))
    (sigma : assignment (arr_src F) (arr_tgt F) (arr_fun F) M) ts,
    @eval_tterms_B (arr_src G) (arr_tgt G) (arr_fun G)
      (arrow_model_map u M) (arrow_assignment_map u M sigma)
      ts =
    map (arr_right F G (oam_arrow F G primitive_F primitive_G u))
      (@eval_tterms_B (arr_src F) (arr_tgt F) (arr_fun F) M sigma ts).
Proof.
  intros F G primitive_F primitive_G u M sigma ts.
  induction ts as [| t ts IH]; simpl.
  - reflexivity.
  - rewrite arrow_eval_tterm. now rewrite IH.
Qed.

Theorem arrow_formula_translate_sat :
  forall {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    (M : compat_model (arr_src F) (arr_tgt F) (arr_fun F))
    (sigma : assignment (arr_src F) (arr_tgt F) (arr_fun F) M)
    (phi : formula (arr_src G) (arr_tgt G) (arr_fun G) primitive_G),
    @sat (arr_src F) (arr_tgt F) (arr_fun F) primitive_F M sigma
      (arrow_formula_translate u phi) <->
    @sat (arr_src G) (arr_tgt G) (arr_fun G) primitive_G
      (arrow_model_map u M) (arrow_assignment_map u M sigma) phi.
Proof.
  intros F G primitive_F primitive_G u M sigma phi.
  revert sigma.
  induction phi as
      [r ss ts Hs Ht
      | psi IH
      | psi IHpsi chi IHchi
      | psi IHpsi chi IHchi
      | psi IHpsi chi IHchi
      | psi IHpsi chi IHchi
      | i psi IH
      | i psi IH
      | i psi IH
      | i psi IH]; intro sigma; simpl.
  - unfold relation_pullback.
    rewrite arrow_eval_sterms_A.
    rewrite arrow_eval_tterms_B.
    reflexivity.
  - specialize (IH sigma). tauto.
  - specialize (IHpsi sigma). specialize (IHchi sigma). tauto.
  - specialize (IHpsi sigma). specialize (IHchi sigma). tauto.
  - specialize (IHpsi sigma). specialize (IHchi sigma). tauto.
  - specialize (IHpsi sigma). specialize (IHchi sigma). tauto.
  - split; intros H u0.
    + apply (proj1 (IH (@updateS (arr_src F) (arr_tgt F) (arr_fun F) _ sigma i u0))).
      exact (H u0).
    + apply (proj2 (IH (@updateS (arr_src F) (arr_tgt F) (arr_fun F) _ sigma i u0))).
      exact (H u0).
  - split; intros [u0 Hu0]; exists u0.
    + apply (proj1 (IH (@updateS (arr_src F) (arr_tgt F) (arr_fun F) _ sigma i u0))).
      exact Hu0.
    + apply (proj2 (IH (@updateS (arr_src F) (arr_tgt F) (arr_fun F) _ sigma i u0))).
      exact Hu0.
  - split; intros H v0.
    + apply (proj1 (IH (@updateT (arr_src F) (arr_tgt F) (arr_fun F) _ sigma i v0))).
      exact (H v0).
    + apply (proj2 (IH (@updateT (arr_src F) (arr_tgt F) (arr_fun F) _ sigma i v0))).
      exact (H v0).
  - split; intros [v0 Hv0]; exists v0.
    + apply (proj1 (IH (@updateT (arr_src F) (arr_tgt F) (arr_fun F) _ sigma i v0))).
      exact Hv0.
    + apply (proj2 (IH (@updateT (arr_src F) (arr_tgt F) (arr_fun F) _ sigma i v0))).
      exact Hv0.
Qed.

Theorem arrow_rule_translate :
  forall {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    Delta phi,
    rule (arr_src G) (arr_tgt G) (arr_fun G) primitive_G Delta phi ->
    rule (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
      (map (arrow_formula_translate u) Delta)
      (arrow_formula_translate u phi).
Proof.
  unfold rule, entails.
  intros F G primitive_F primitive_G u Delta phi Hrule M sigma Hctx.
  apply (proj2 (arrow_formula_translate_sat u M sigma phi)).
  apply Hrule.
  intros gamma Hgamma.
  apply (proj1 (arrow_formula_translate_sat u M sigma gamma)).
  apply Hctx.
  apply in_map. exact Hgamma.
Qed.

Theorem arrow_proves_translate :
  forall {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G)
    Gamma phi,
    proves (arr_src G) (arr_tgt G) (arr_fun G) primitive_G Gamma phi ->
    proves (arr_src F) (arr_tgt F) (arr_fun F) primitive_F
      (map (arrow_formula_translate u) Gamma)
      (arrow_formula_translate u phi).
Proof.
  intros F G primitive_F primitive_G u Gamma phi Hpr.
  induction Hpr as [phi Hin | Delta phi HDelta IHDelta Hrule].
  - apply ProvesHyp. apply in_map. exact Hin.
  - apply ProvesRule with (Delta := map (arrow_formula_translate u) Delta).
    + intros gamma Hgamma.
      destruct (proj1 (in_map_iff _ _ _) Hgamma) as
        [delta [Hdelta HdeltaIn]].
      subst gamma.
      apply IHDelta. exact HdeltaIn.
    + apply arrow_rule_translate. exact Hrule.
Qed.

Definition observable_arrow_system_morphism
    {F G : arrow_object}
    {primitive_F :
      forall m n : nat, relation (arr_src F) (arr_tgt F) -> Prop}
    {primitive_G :
      forall m n : nat, relation (arr_src G) (arr_tgt G) -> Prop}
    (u : observable_arrow_morphism F G primitive_F primitive_G) :
    formal_system_morphism
      (arrow_system_object F primitive_F)
      (arrow_system_object G primitive_G).
Proof.
  refine
    {| mor_translate :=
         (@arrow_formula_translate F G primitive_F primitive_G u :
          obj_form (arrow_system_object G primitive_G) ->
          obj_form (arrow_system_object F primitive_F));
       mor_model :=
         (@arrow_model_map F G primitive_F primitive_G u :
          obj_model (arrow_system_object F primitive_F) ->
          obj_model (arrow_system_object G primitive_G));
       mor_assignment :=
         (@arrow_assignment_map F G primitive_F primitive_G u :
          forall M : obj_model (arrow_system_object F primitive_F),
            obj_assignment (arrow_system_object F primitive_F) M ->
            obj_assignment (arrow_system_object G primitive_G)
              (@arrow_model_map F G primitive_F primitive_G u M));
       mor_sat_preserve := @arrow_formula_translate_sat F G primitive_F primitive_G u;
       mor_proof_preserve := @arrow_proves_translate F G primitive_F primitive_G u |}.
Defined.

Record formal_system_morphism_component_law
    {S T : formal_system_object}
    (u v : formal_system_morphism S T) : Prop := {
  fsm_translate_law :
    forall phi,
      mor_translate S T u phi = mor_translate S T v phi;
  fsm_sat_law :
    forall M sigma phi,
      obj_sat T (mor_model S T u M) (mor_assignment S T u M sigma) phi <->
      obj_sat T (mor_model S T v M) (mor_assignment S T v M sigma) phi;
  fsm_proof_law :
    forall Gamma phi,
      obj_proves S (map (mor_translate S T u) Gamma)
        (mor_translate S T u phi) <->
      obj_proves S (map (mor_translate S T v) Gamma)
        (mor_translate S T v phi)
}.

Record observable_arrow_base_category : Type := {
  oabc_obj : Type;
  oabc_arrow : oabc_obj -> oabc_obj -> Type;
  oabc_arrow_object : oabc_obj -> arrow_object;
  oabc_primitive :
    forall x : oabc_obj,
      forall m n : nat,
        relation (arr_src (oabc_arrow_object x))
          (arr_tgt (oabc_arrow_object x)) -> Prop;
  oabc_to_observable_morphism :
    forall x y : oabc_obj,
      oabc_arrow x y ->
      observable_arrow_morphism
        (oabc_arrow_object x) (oabc_arrow_object y)
        (oabc_primitive x) (oabc_primitive y);
  oabc_id : forall x : oabc_obj, oabc_arrow x x;
  oabc_comp :
    forall x y z : oabc_obj,
      oabc_arrow x y -> oabc_arrow y z -> oabc_arrow x z;
  oabc_sys_id_law :
    forall x : oabc_obj,
      formal_system_morphism_component_law
        (observable_arrow_system_morphism
          (oabc_to_observable_morphism x x (oabc_id x)))
        (formal_system_id
          (arrow_system_object (oabc_arrow_object x) (oabc_primitive x)));
  oabc_sys_comp_law :
    forall (x y z : oabc_obj)
      (u : oabc_arrow x y) (v : oabc_arrow y z),
      formal_system_morphism_component_law
        (observable_arrow_system_morphism
          (oabc_to_observable_morphism x z (oabc_comp x y z u v)))
        (formal_system_comp
          (observable_arrow_system_morphism
            (oabc_to_observable_morphism x y u))
          (observable_arrow_system_morphism
            (oabc_to_observable_morphism y z v)))
}.

Definition observable_base_system_object
    (C : observable_arrow_base_category) (x : oabc_obj C) :
    formal_system_object :=
  arrow_system_object (oabc_arrow_object C x) (oabc_primitive C x).

Definition observable_base_system_morphism
    (C : observable_arrow_base_category)
    {x y : oabc_obj C}
    (u : oabc_arrow C x y) :
    formal_system_morphism
      (observable_base_system_object C x)
      (observable_base_system_object C y) :=
  observable_arrow_system_morphism
    (oabc_to_observable_morphism C x y u).

Record system_functor_package
    (C : observable_arrow_base_category) : Type := {
  sf_obj : oabc_obj C -> formal_system_object;
  sf_mor :
    forall x y : oabc_obj C,
      oabc_arrow C x y -> formal_system_morphism (sf_obj x) (sf_obj y);
  sf_id_law :
    forall x : oabc_obj C,
      formal_system_morphism_component_law
        (sf_mor x x (oabc_id C x))
        (formal_system_id (sf_obj x));
  sf_comp_law :
    forall (x y z : oabc_obj C)
      (u : oabc_arrow C x y) (v : oabc_arrow C y z),
      formal_system_morphism_component_law
        (sf_mor x z (oabc_comp C x y z u v))
        (formal_system_comp (sf_mor x y u) (sf_mor y z v))
}.

Definition Sys_functor
    (C : observable_arrow_base_category) : system_functor_package C.
Proof.
  refine
    {| sf_obj := observable_base_system_object C;
       sf_mor := fun x y u => observable_base_system_morphism C u;
       sf_id_law := _;
       sf_comp_law := _ |}.
  - intro x. apply oabc_sys_id_law.
  - intros x y z u v. apply oabc_sys_comp_law.
Defined.

End FunctionObservationSystem1111.
