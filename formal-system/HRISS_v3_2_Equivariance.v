(** Strict equivariance of the recursive structure and evaluation, Sections
    7.6, 8.2--8.3, 9.6, and 11. *)

From Stdlib Require Import Arith.PeanoNat Logic.FunctionalExtensionality
  Logic.ProofIrrelevance.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics.
Set Implicit Arguments.
Unset Strict Implicit.

(** The inverse used in structural conjugation is the actual Scott-continuous
    inverse of [transport_map], rather than a merely set-theoretic function. *)
Definition transport_inverse_map {Sig H} (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) : SCMap (E_dcpo Sig H) (E_dcpo Sig H).
Proof.
  apply (@order_iso_sc (E_dcpo Sig H) (E_dcpo Sig H)
    (transport_inv_point C g Hg) (transport_point C g Hg)).
  - intros x y Hxy m. apply sc_monotone, Hxy.
  - intros x y Hxy m. apply sc_monotone, Hxy.
  - apply transport_fwd_inv.
  - apply transport_inv_fwd.
Defined.

Arguments transport_inverse_map {Sig H} C g Hg.

Lemma transport_backward_forward : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) x,
    transport_inverse_map C g Hg (transport_map C g Hg x) = x.
Proof. intros; apply transport_inv_fwd. Qed.

Lemma transport_forward_backward : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) x,
    transport_map C g Hg (transport_inverse_map C g Hg x) = x.
Proof. intros; apply transport_fwd_inv. Qed.

Lemma transport_pi : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) m x,
    pi_map Sig H m (transport_map C g Hg x) =
    B_level_map C m g Hg (pi_map Sig H m x).
Proof. reflexivity. Qed.

Lemma transport_inverse_pi : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) m x,
    pi_map Sig H m (transport_inverse_map C g Hg x) =
    B_level_inv_map C m g Hg (pi_map Sig H m x).
Proof. reflexivity. Qed.

Lemma transport_inverse_eta : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) m (d : dcar (D_level Sig m)),
    transport_inverse_map C g Hg (eta_map Sig H m d) =
    eta_map Sig H m (B_level_inv_map C m g Hg d).
Proof.
  intros Sig H C g Hg m d.
  pose proof (@transport_eta Sig H C g Hg m
    (B_level_inv_map C m g Hg d)) as Heta.
  apply (f_equal (transport_inverse_map C g Hg)) in Heta.
  rewrite transport_backward_forward in Heta.
  rewrite B_level_fwd_bwd in Heta. symmetry. exact Heta.
Qed.

(** Section 7.6: [Theta] intertwines transport with structural conjugation. *)
Theorem theta_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) e,
    theta_map Sig H (transport_map C g Hg e) =
    F_conjugate_point Sig (E_dcpo Sig H) g
      (transport_map C g Hg) (transport_inverse_map C g Hg)
      (theta_map Sig H e).
Proof.
  intros Sig H C g Hg e.
  rewrite <- (@lambda_kappa_map Sig H
    (theta_map Sig H (transport_map C g Hg e))).
  rewrite <- (@lambda_kappa_map Sig H
    (F_conjugate_point Sig (E_dcpo Sig H) g
      (transport_map C g Hg) (transport_inverse_map C g Hg)
      (theta_map Sig H e))).
  apply (f_equal (lambda_map Sig H)).
  apply L_ext. intro m.
  change
    (lcoord (kappa_map Sig H
      (lambda_map Sig H (tau_map Sig H (transport_map C g Hg e)))) m =
     F_project Sig (bilimit_ep Sig H m)
       (F_conjugate_point Sig (E_dcpo Sig H) g
         (transport_map C g Hg) (transport_inverse_map C g Hg)
         (theta_map Sig H e))).
  rewrite kappa_lambda_map.
  rewrite <- (@F_project_conjugate Sig (D_level Sig m)
    (E_dcpo Sig H) (bilimit_ep Sig H m) g
    (B_level_map C m g Hg) (B_level_inv_map C m g Hg)
    (transport_map C g Hg) (transport_inverse_map C g Hg)
    (theta_map Sig H e)).
  - change
      (B_level_map C (S m) g Hg (ecoord e (S m)) =
       F_conjugate_point Sig (D_level Sig m) g
         (B_level_map C m g Hg) (B_level_inv_map C m g Hg)
         (lcoord (kappa_map Sig H (theta_map Sig H e)) m)).
    change
      (B_level_map C (S m) g Hg (ecoord e (S m)) =
       F_conjugate_point Sig (D_level Sig m) g
         (B_level_map C m g Hg) (B_level_inv_map C m g Hg)
         (lcoord (kappa_map Sig H
           (lambda_map Sig H (tau_map Sig H e))) m)).
    rewrite kappa_lambda_map. reflexivity.
  - intro y. symmetry. apply transport_pi.
  - intro x. symmetry. apply transport_inverse_eta.
Qed.

Theorem omega_conjugate : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) M,
    omega_map Sig H
      (F_conjugate_point Sig (E_dcpo Sig H) g
        (transport_map C g Hg) (transport_inverse_map C g Hg) M) =
    transport_map C g Hg (omega_map Sig H M).
Proof.
  intros Sig H C g Hg M.
  assert (Ht :
    theta_map Sig H
      (omega_map Sig H
        (F_conjugate_point Sig (E_dcpo Sig H) g
          (transport_map C g Hg) (transport_inverse_map C g Hg) M)) =
    theta_map Sig H (transport_map C g Hg (omega_map Sig H M))).
  { rewrite theta_omega, theta_transport, theta_omega. reflexivity. }
  apply (f_equal (omega_map Sig H)) in Ht.
  now rewrite !omega_theta in Ht.
Qed.

Lemma transport_bottom : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g),
    transport_map C g Hg (dbot (E_dcpo Sig H)) =
    dbot (E_dcpo Sig H).
Proof.
  intros Sig H C g Hg. apply (dle_antisym (E_dcpo Sig H)).
  - pose proof (@dbot_least (E_dcpo Sig H)
      (transport_inverse_map C g Hg (dbot (E_dcpo Sig H)))) as Hb.
    apply (@sc_monotone (E_dcpo Sig H) (E_dcpo Sig H)
      (transport_map C g Hg)) in Hb.
    now rewrite transport_forward_backward in Hb.
  - apply dbot_least.
Qed.

Lemma power_transport_inverse : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) n
    (xs : dcar (power_dcpo (E_dcpo Sig H) n)),
    @power_map (E_dcpo Sig H) (E_dcpo Sig H) n
      (transport_inverse_map C g Hg)
      (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
        (transport_map C g Hg) xs) = xs.
Proof.
  intros. apply functional_extensionality_dep. intro i.
  repeat rewrite dep_map_sc_apply. apply transport_backward_forward.
Qed.

Lemma operation_T_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) n (f : TSym Sig n) e xs,
    @operation_family_map Sig H (ai_T f) (transport_map C g Hg e)
      (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
        (transport_map C g Hg) xs) =
    transport_map C g Hg (@operation_family_map Sig H (ai_T f) e xs).
Proof.
  intros. change
    (theta_map Sig H (transport_map C g Hg e) (ai_T f)
       (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
         (transport_map C g Hg) xs) =
     transport_map C g Hg (theta_map Sig H e (ai_T f) xs)).
  rewrite theta_transport.
  cbn [F_conjugate_point conjugate_operation].
  apply (f_equal (transport_map C g Hg)).
  apply (f_equal (fun ys => theta_map Sig H e (ai_T f) ys)).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply transport_backward_forward.
Qed.

Lemma operation_P_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) n (P : PSym Sig n) e xs,
    @operation_family_map Sig H (ai_P P) (transport_map C g Hg e)
      (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
        (transport_map C g Hg) xs) =
    transport_map C g Hg (@operation_family_map Sig H (ai_P P) e xs).
Proof.
  intros. change
    (theta_map Sig H (transport_map C g Hg e) (ai_P P)
       (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
         (transport_map C g Hg) xs) =
     transport_map C g Hg (theta_map Sig H e (ai_P P) xs)).
  rewrite theta_transport.
  cbn [F_conjugate_point conjugate_operation].
  apply (f_equal (transport_map C g Hg)).
  apply (f_equal (fun ys => theta_map Sig H e (ai_P P) ys)).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply transport_backward_forward.
Qed.

Lemma operation_L_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) n (L : LSym Sig n) e xs,
    @operation_family_map Sig H (ai_L L) (transport_map C g Hg e)
      (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
        (transport_map C g Hg) xs) =
    transport_map C g Hg (@operation_family_map Sig H (ai_L L) e xs).
Proof.
  intros. change
    (theta_map Sig H (transport_map C g Hg e) (ai_L L)
       (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
         (transport_map C g Hg) xs) =
     transport_map C g Hg (theta_map Sig H e (ai_L L) xs)).
  rewrite theta_transport.
  cbn [F_conjugate_point conjugate_operation].
  apply (f_equal (transport_map C g Hg)).
  apply (f_equal (fun ys => theta_map Sig H e (ai_L L) ys)).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply transport_backward_forward.
Qed.

Lemma operation_Q_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) (Q : QSym Sig) e xs,
    @operation_family_map Sig H (ai_Q Q) (transport_map C g Hg e)
      (@power_map (E_dcpo Sig H) (E_dcpo Sig H) 1
        (transport_map C g Hg) xs) =
    transport_map C g Hg (@operation_family_map Sig H (ai_Q Q) e xs).
Proof.
  intros. change
    (theta_map Sig H (transport_map C g Hg e) (ai_Q Q)
       (@power_map (E_dcpo Sig H) (E_dcpo Sig H) 1
         (transport_map C g Hg) xs) =
     transport_map C g Hg (theta_map Sig H e (ai_Q Q) xs)).
  rewrite theta_transport.
  cbn [F_conjugate_point conjugate_operation].
  apply (f_equal (transport_map C g Hg)).
  apply (f_equal (fun ys => theta_map Sig H e (ai_Q Q) ys)).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply transport_backward_forward.
Qed.

Lemma operation_var_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) i e,
    @operation_family_map Sig H (ai_var (pact g i))
      (transport_map C g Hg e) (empty_power (E_dcpo Sig H)) =
    transport_map C g Hg
      (@operation_family_map Sig H (ai_var i) e
        (empty_power (E_dcpo Sig H))).
Proof.
  intros. change
    (theta_map Sig H (transport_map C g Hg e) (ai_var (pact g i))
       (empty_power (E_dcpo Sig H)) =
     transport_map C g Hg
       (theta_map Sig H e (ai_var i) (empty_power (E_dcpo Sig H)))).
  rewrite theta_transport.
  cbn [F_conjugate_point conjugate_operation]. rewrite pact_inv_l.
  apply (f_equal (transport_map C g Hg)).
  apply (f_equal (fun ys => theta_map Sig H e (ai_var i) ys)).
  apply empty_power_unique.
Qed.

Lemma operation_slot_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) n e xs,
    @operation_family_map Sig H (ai_slot n) (transport_map C g Hg e)
      (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
        (transport_map C g Hg) xs) =
    transport_map C g Hg (@operation_family_map Sig H (ai_slot n) e xs).
Proof.
  intros. change
    (theta_map Sig H (transport_map C g Hg e) (ai_slot n)
       (@power_map (E_dcpo Sig H) (E_dcpo Sig H) n
         (transport_map C g Hg) xs) =
     transport_map C g Hg (theta_map Sig H e (ai_slot n) xs)).
  rewrite theta_transport.
  cbn [F_conjugate_point conjugate_operation].
  apply (f_equal (transport_map C g Hg)).
  apply (f_equal (fun ys => theta_map Sig H e (ai_slot n) ys)).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply transport_backward_forward.
Qed.

Lemma operation_assert_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) e xs,
    @operation_family_map Sig H ai_assert (transport_map C g Hg e)
      (@power_map (E_dcpo Sig H) (E_dcpo Sig H) 1
        (transport_map C g Hg) xs) =
    transport_map C g Hg (@operation_family_map Sig H ai_assert e xs).
Proof.
  intros. change
    (theta_map Sig H (transport_map C g Hg e) ai_assert
       (@power_map (E_dcpo Sig H) (E_dcpo Sig H) 1
         (transport_map C g Hg) xs) =
     transport_map C g Hg (theta_map Sig H e ai_assert xs)).
  rewrite theta_transport.
  cbn [F_conjugate_point conjugate_operation].
  apply (f_equal (transport_map C g Hg)).
  apply (f_equal (fun ys => theta_map Sig H e ai_assert ys)).
  apply functional_extensionality_dep. intro j.
  repeat rewrite dep_map_sc_apply. apply transport_backward_forward.
Qed.

Lemma conjugate_update_structure : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) i (M : dcar (F_dcpo Sig (E_dcpo Sig H))) v,
    F_conjugate_point Sig (E_dcpo Sig H) g
      (transport_map C g Hg) (transport_inverse_map C g Hg)
      (@update_structure Sig H i M v) =
    @update_structure Sig H (pact g i)
      (F_conjugate_point Sig (E_dcpo Sig H) g
        (transport_map C g Hg) (transport_inverse_map C g Hg) M)
      (transport_map C g Hg v).
Proof.
  intros Sig H C g Hg i M v.
  apply functional_extensionality_dep. intro a.
  destruct a as [n f|n P|n L|Q|j|n|];
    cbn [F_conjugate_point update_structure].
  all: try reflexivity.
  destruct (Nat.eq_dec (pact (pinv g) j) i) as [He|Hne];
    destruct (Nat.eq_dec j (pact g i)) as [He'|Hne'].
  - subst j.
    destruct g; destruct i as [|[|[|i]]]; cbn in *;
      destruct He;
      apply SCMap_ext; intro xs;
      cbn [conjugate_operation]; reflexivity.
  - exfalso. apply Hne'. rewrite <- (pact_inv_r g j). now rewrite He.
  - exfalso. apply Hne. rewrite He', pact_inv_l. reflexivity.
  - reflexivity.
Qed.

Theorem upd_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) i e v,
    transport_map C g Hg (upd Sig H i e v) =
    upd Sig H (pact g i) (transport_map C g Hg e)
      (transport_map C g Hg v).
Proof.
  intros Sig H C g Hg i e v. unfold upd.
  rewrite <- omega_conjugate.
  apply (f_equal (omega_map Sig H)).
  rewrite conjugate_update_structure, theta_transport. reflexivity.
Qed.

Lemma conjugate_bottom_operation : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) n,
    conjugate_operation (E_dcpo Sig H) n
      (transport_map C g Hg) (transport_inverse_map C g Hg)
      (bottom_operation (E_dcpo Sig H) n) =
    bottom_operation (E_dcpo Sig H) n.
Proof.
  intros. apply SCMap_ext. intro xs.
  cbn [conjugate_operation bottom_operation]. apply transport_bottom.
Qed.

Lemma conjugate_resident_structure : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) n
    (K : SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H)),
    F_conjugate_point Sig (E_dcpo Sig H) g
      (transport_map C g Hg) (transport_inverse_map C g Hg)
      (@resident_structure Sig H n K) =
    @resident_structure Sig H n
      (conjugate_operation (E_dcpo Sig H) n
        (transport_map C g Hg) (transport_inverse_map C g Hg) K).
Proof.
  intros Sig H C g Hg n K.
  apply functional_extensionality_dep. intro a.
  destruct a as [k f|k P|k L|Q|i|k|];
    cbn [F_conjugate_point resident_structure].
  - apply conjugate_bottom_operation.
  - apply conjugate_bottom_operation.
  - apply conjugate_bottom_operation.
  - apply conjugate_bottom_operation.
  - apply conjugate_bottom_operation.
  - destruct (Nat.eq_dec k n) as [He|Hne].
    + subst k. reflexivity.
    + apply conjugate_bottom_operation.
  - apply conjugate_bottom_operation.
Qed.

Theorem enc_transport : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) n
    (K : SCMap (power_dcpo (E_dcpo Sig H) n) (E_dcpo Sig H)),
    transport_map C g Hg (enc Sig H n K) =
    enc Sig H n
      (conjugate_operation (E_dcpo Sig H) n
        (transport_map C g Hg) (transport_inverse_map C g Hg) K).
Proof.
  intros Sig H C g Hg n K. unfold enc.
  rewrite <- omega_conjugate.
  apply (f_equal (omega_map Sig H)).
  apply conjugate_resident_structure.
Qed.

Lemma transport_conjugate_apply : forall Sig H (C : SyntaxCoding Sig H)
    g h (Hg : hmem H g) (Hh : hmem H h) e,
    transport_map C (pconj g h) (@pconj_mem H g h Hg Hh)
      (transport_map C g Hg e) =
    transport_map C g Hg (transport_map C h Hh e).
Proof.
  intros Sig H C g h Hg Hh e.
  pose proof (f_equal (fun F : SCMap (E_dcpo Sig H) (E_dcpo Sig H) => F e)
    (@transport_mul Sig H C (pconj g h) g
      (@pconj_mem H g h Hg Hh) Hg)) as Hleft.
  pose proof (f_equal (fun F : SCMap (E_dcpo Sig H) (E_dcpo Sig H) => F e)
    (@transport_mul Sig H C g h Hg Hh)) as Hright.
  cbn in Hleft, Hright.
  transitivity
    (transport_map C (pmul (pconj g h) g)
      (@hmem_mul H (pconj g h) g (@pconj_mem H g h Hg Hh) Hg) e).
  - exact Hleft.
  - transitivity
      (transport_map C (pmul g h) (@hmem_mul H g h Hg Hh) e).
    + destruct g, h; cbn; f_equal; apply proof_irrelevance.
    + symmetry. exact Hright.
Qed.

Lemma quote_tm_raw_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) t,
    wf_tm H t ->
    transport_map C g Hg (quote_tm_raw C t) =
    quote_tm_raw C (act_tm g t).
Proof.
  intros Sig H C g Hg t Ht.
  destruct (@quote_tm_raw_wf Sig H C t Ht) as [Ht' Hraw].
  assert (Hact : wf_tm H (act_tm g t)).
  { now apply wf_act_tm. }
  destruct (@quote_tm_raw_wf Sig H C (act_tm g t) Hact)
    as [Hact' Hrawact].
  rewrite Hraw, Hrawact, quote_equivariant.
  apply (f_equal (quote_value C)). apply sig_prop_ext. reflexivity.
Qed.

Lemma quote_fm_raw_equivariant : forall Sig H (C : SyntaxCoding Sig H)
    g (Hg : hmem H g) p,
    wf_fm H p ->
    transport_map C g Hg (quote_fm_raw C p) =
    quote_fm_raw C (act_fm g p).
Proof.
  intros Sig H C g Hg p Hp.
  destruct (@quote_fm_raw_wf Sig H C p Hp) as [Hp' Hraw].
  assert (Hact : wf_fm H (act_fm g p)).
  { now apply wf_act_fm. }
  destruct (@quote_fm_raw_wf Sig H C (act_fm g p) Hact)
    as [Hact' Hrawact].
  rewrite Hraw, Hrawact, quote_equivariant.
  apply (f_equal (quote_value C)). apply sig_prop_ext. reflexivity.
Qed.

Lemma unary_power_lift_apply : forall D (K : SCMap D D)
    (xs : dcar (power_dcpo D 1)),
    @unary_power_lift D K xs = K (xs (fzero 0)).
Proof. reflexivity. Qed.

Lemma pair_left_map_apply : forall D (e v : dcar D),
    pair_left_map D e v = @pair_power D e v.
Proof.
  intros. apply functional_extensionality_dep. intro j.
  refine (@finite_caseS 1 j
    (fun k => pair_left_map D e v k = @pair_power D e v k)
    (eq_refl _) _).
  intro k.
  refine (@finite_caseS 0 k
    (fun ell => pair_left_map D e v (@fsucc 1 ell) =
      @pair_power D e v (@fsucc 1 ell)) (eq_refl _) _).
  intros impossible. inversion impossible.
Qed.

Lemma abstraction_map_apply : forall Sig H i
    (body : SCMap (E_dcpo Sig H) (E_dcpo Sig H)) e v,
    @abstraction_map Sig H i body e v = body (upd Sig H i e v).
Proof.
  intros. change
    (body (upd_map Sig H i
      (pair_left_map (E_dcpo Sig H) e v)) =
     body (upd Sig H i e v)).
  rewrite pair_left_map_apply, upd_map_apply. reflexivity.
Qed.

Lemma unary_abstraction_conjugate : forall Sig H
    (C : SyntaxCoding Sig H) g (Hg : hmem H g) i
    (body body' : SCMap (E_dcpo Sig H) (E_dcpo Sig H)),
    (forall r, body' (transport_map C g Hg r) =
      transport_map C g Hg (body r)) ->
    forall e,
    conjugate_operation (E_dcpo Sig H) 1
      (transport_map C g Hg) (transport_inverse_map C g Hg)
      (@unary_power_lift (E_dcpo Sig H)
        (@abstraction_map Sig H i body e)) =
    @unary_power_lift (E_dcpo Sig H)
      (@abstraction_map Sig H (pact g i) body'
        (transport_map C g Hg e)).
Proof.
  intros Sig H C g Hg i body body' Hbody e.
  apply SCMap_ext. intro xs.
  unfold conjugate_operation.
  change
    (transport_map C g Hg
       ((@unary_power_lift (E_dcpo Sig H)
          (@abstraction_map Sig H i body e))
        (@power_map (E_dcpo Sig H) (E_dcpo Sig H) 1
          (transport_inverse_map C g Hg) xs)) =
     (@unary_power_lift (E_dcpo Sig H)
       (@abstraction_map Sig H (pact g i) body'
         (transport_map C g Hg e))) xs).
  rewrite !unary_power_lift_apply.
  change
    (transport_map C g Hg
      (@abstraction_map Sig H i body e
        (transport_inverse_map C g Hg (xs (fzero 0)))) =
     @abstraction_map Sig H (pact g i) body'
       (transport_map C g Hg e) (xs (fzero 0))).
  rewrite !abstraction_map_apply.
  rewrite <- Hbody, upd_transport, transport_forward_backward. reflexivity.
Qed.

Lemma enc_unary_family_apply : forall Sig H
    (K : SCMap (E_dcpo Sig H) (E_dcpo Sig H)),
    @enc_unary_family Sig H K =
    enc Sig H 1 (@unary_power_lift (E_dcpo Sig H) K).
Proof.
  intros. change
    (enc_map Sig H 1 (@unary_power_lift (E_dcpo Sig H) K) =
     enc Sig H 1 (@unary_power_lift (E_dcpo Sig H) K)).
  apply enc_map_apply.
Qed.
