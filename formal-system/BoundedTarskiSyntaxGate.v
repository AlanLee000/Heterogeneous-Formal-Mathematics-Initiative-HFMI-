From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Module BoundedTarskiSyntaxGate.

Inductive bit : Set := B0 | B1.
Definition string : Type := list bit.
Definition epsilon_string : string := [].
Definition string_concat (s t : string) : string := s ++ t.
Definition string_length (s : string) : nat := length s.

Fixpoint underline (n : nat) : string :=
  match n with
  | 0 => [B0]
  | S k => B1 :: underline k
  end.

Inductive label : Set :=
| Lv | Lc | La | Ld | Lg
| LE | LL | LW | LN | LA | LBexists | LBforall | LG.

Lemma label_separation :
  Ld <> Lg /\ LE <> LL /\ LW <> LG /\ LN <> LA.
Proof. repeat split; discriminate. Qed.

Record coding (S : Type) : Type := {
  encode_seq : list S -> S;
  encode_seq_injective :
    forall xs ys, encode_seq xs = encode_seq ys -> xs = ys
}.

Inductive tm (S : Type) : Type :=
| TVar : nat -> tm S
| TConst : S -> tm S
| TApp : tm S -> tm S -> tm S
| TDiag : tm S -> tm S
| TGate : tm S -> tm S.

Arguments TVar {S}.
Arguments TConst {S}.
Arguments TApp {S}.
Arguments TDiag {S}.
Arguments TGate {S}.

Inductive ofm (S : Type) : Type :=
| OEq : tm S -> tm S -> ofm S
| OLenLe : tm S -> tm S -> ofm S
| OW : nat -> tm S -> ofm S
| ONeg : ofm S -> ofm S
| OAnd : ofm S -> ofm S -> ofm S
| OExists : nat -> tm S -> ofm S -> ofm S
| OForall : nat -> tm S -> ofm S -> ofm S.

Arguments OEq {S}.
Arguments OLenLe {S}.
Arguments OW {S}.
Arguments ONeg {S}.
Arguments OAnd {S}.
Arguments OExists {S}.
Arguments OForall {S}.

Inductive fm (S : Type) : Type :=
| FOrd : ofm S -> fm S
| FGate : nat -> fm S -> fm S.

Arguments FOrd {S}.
Arguments FGate {S}.

Fixpoint remove_nat (i : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: rest => if Nat.eq_dec x i then remove_nat i rest else x :: remove_nat i rest
  end.

Fixpoint mem_nat (i : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | x :: rest => if Nat.eq_dec x i then true else mem_nat i rest
  end.

Fixpoint fv_tm {S : Type} (t : tm S) : list nat :=
  match t with
  | TVar i => [i]
  | TConst _ => []
  | TApp u v => fv_tm u ++ fv_tm v
  | TDiag u => fv_tm u
  | TGate u => fv_tm u
  end.

Fixpoint fv_ofm {S : Type} (phi : ofm S) : list nat :=
  match phi with
  | OEq u v => fv_tm u ++ fv_tm v
  | OLenLe u v => fv_tm u ++ fv_tm v
  | OW _ u => fv_tm u
  | ONeg psi => fv_ofm psi
  | OAnd psi chi => fv_ofm psi ++ fv_ofm chi
  | OExists i t psi => fv_tm t ++ remove_nat i (fv_ofm psi)
  | OForall i t psi => fv_tm t ++ remove_nat i (fv_ofm psi)
  end.

Definition fv_fm {S : Type} (phi : fm S) : list nat :=
  match phi with
  | FOrd psi => fv_ofm psi
  | FGate _ _ => []
  end.

Definition subset_singleton (i : nat) (xs : list nat) : Prop :=
  forall j, In j xs -> j = i.

Definition singleton_zero (xs : list nat) : Prop :=
  subset_singleton 0 xs.

Definition closed_fm {S : Type} (phi : fm S) : Prop :=
  fv_fm phi = [].

Fixpoint sub_tm {S : Type} (t : tm S) (i : nat) (u : tm S) : tm S :=
  match t with
  | TVar j => if Nat.eq_dec j i then u else TVar j
  | TConst s => TConst s
  | TApp t0 t1 => TApp (sub_tm t0 i u) (sub_tm t1 i u)
  | TDiag t0 => TDiag (sub_tm t0 i u)
  | TGate t0 => TGate (sub_tm t0 i u)
  end.

Fixpoint sub_ofm {S : Type} (phi : ofm S) (i : nat) (u : tm S) : ofm S :=
  match phi with
  | OEq t0 t1 => OEq (sub_tm t0 i u) (sub_tm t1 i u)
  | OLenLe t0 t1 => OLenLe (sub_tm t0 i u) (sub_tm t1 i u)
  | OW k t => OW k (sub_tm t i u)
  | ONeg psi => ONeg (sub_ofm psi i u)
  | OAnd psi chi => OAnd (sub_ofm psi i u) (sub_ofm chi i u)
  | OExists j t psi =>
      if Nat.eq_dec j i then OExists j (sub_tm t i u) psi
      else if mem_nat j (fv_tm u) then OExists j (sub_tm t i u) psi
      else OExists j (sub_tm t i u) (sub_ofm psi i u)
  | OForall j t psi =>
      if Nat.eq_dec j i then OForall j (sub_tm t i u) psi
      else if mem_nat j (fv_tm u) then OForall j (sub_tm t i u) psi
      else OForall j (sub_tm t i u) (sub_ofm psi i u)
  end.

Definition sub_fm {S : Type} (phi : fm S) (i : nat) (u : tm S) : fm S :=
  match phi with
  | FOrd psi => FOrd (sub_ofm psi i u)
  | FGate k e => FGate k e
  end.

Lemma subset_singleton_app_l :
  forall i xs ys,
    subset_singleton i (xs ++ ys) -> subset_singleton i xs.
Proof.
  unfold subset_singleton.
  intros i xs ys H j Hj.
  apply H. apply in_or_app. left. exact Hj.
Qed.

Lemma subset_singleton_app_r :
  forall i xs ys,
    subset_singleton i (xs ++ ys) -> subset_singleton i ys.
Proof.
  unfold subset_singleton.
  intros i xs ys H j Hj.
  apply H. apply in_or_app. right. exact Hj.
Qed.

Lemma mem_nat_false_not_in :
  forall i xs, ~ In i xs -> mem_nat i xs = false.
Proof.
  intros i xs Hnot.
  induction xs as [| x xs IH]; simpl; auto.
  destruct (Nat.eq_dec x i) as [-> | Hne].
  - exfalso. apply Hnot. left. reflexivity.
  - apply IH. intro Hin. apply Hnot. right. exact Hin.
Qed.

Lemma mem_nat_false_of_subset_singleton_ne :
  forall i j xs,
    subset_singleton i xs -> j <> i -> mem_nat j xs = false.
Proof.
  intros i j xs Hsub Hneq.
  apply mem_nat_false_not_in.
  intro Hin.
  apply Hneq. apply Hsub. exact Hin.
Qed.

Lemma fv_tm_sub_closed :
  forall (S : Type) i (t w : tm S),
    subset_singleton i (fv_tm t) ->
    fv_tm w = [] ->
    fv_tm (sub_tm t i w) = [].
Proof.
  intros S i t.
  induction t as [j | c | t0 IH0 t1 IH1 | t IH | t IH];
    intros w Hsub Hw; simpl in *.
  - destruct (Nat.eq_dec j i) as [-> | Hne].
    + exact Hw.
    + exfalso. apply Hne. apply Hsub. left. reflexivity.
  - reflexivity.
  - assert (H0 : subset_singleton i (fv_tm t0)).
    { eapply subset_singleton_app_l. exact Hsub. }
    assert (H1 : subset_singleton i (fv_tm t1)).
    { eapply subset_singleton_app_r. exact Hsub. }
    rewrite (IH0 w H0 Hw), (IH1 w H1 Hw). reflexivity.
  - apply IH; assumption.
  - apply IH; assumption.
Qed.

Lemma sub_tm_comp_proved :
  forall (S : Type) (u t w : tm S) i,
    sub_tm (sub_tm u i t) i w =
    sub_tm u i (sub_tm t i w).
Proof.
  intros S u.
  induction u as [j | c | u0 IH0 u1 IH1 | u IH | u IH];
    intros t w i; simpl.
  - destruct (Nat.eq_dec j i) as [Heq | Hneq].
    + reflexivity.
    + simpl. destruct (Nat.eq_dec j i) as [Heq | _].
      * contradiction.
      * reflexivity.
  - reflexivity.
  - rewrite IH0, IH1. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma sub_ofm_comp_closed_proved :
  forall (S : Type) (phi : ofm S) (t w : tm S) i,
    subset_singleton i (fv_tm t) ->
    fv_tm w = [] ->
    sub_ofm (sub_ofm phi i t) i w =
    sub_ofm phi i (sub_tm t i w).
Proof.
  intros S phi.
  induction phi as
      [u v | u v | k u | psi IH | psi IHpsi chi IHchi
      | j b psi IH | j b psi IH];
    intros t w i Ht Hw; simpl.
  - repeat rewrite sub_tm_comp_proved. reflexivity.
  - repeat rewrite sub_tm_comp_proved. reflexivity.
  - repeat rewrite sub_tm_comp_proved. reflexivity.
  - rewrite IH; auto.
  - rewrite IHpsi; auto. rewrite IHchi; auto.
  - destruct (Nat.eq_dec j i) as [Heq | Hneq].
    + subst.
      simpl.
      destruct (Nat.eq_dec i i) as [_ | Hbad]; [| contradiction].
      repeat rewrite sub_tm_comp_proved.
      reflexivity.
    + assert (Hmemt : mem_nat j (fv_tm t) = false).
      { eapply mem_nat_false_of_subset_singleton_ne; eauto. }
      assert (Hmemw : mem_nat j (fv_tm w) = false).
      { rewrite Hw. reflexivity. }
      assert (Hclosed_sub : fv_tm (sub_tm t i w) = []).
      { apply fv_tm_sub_closed; assumption. }
      assert (Hmemsub : mem_nat j (fv_tm (sub_tm t i w)) = false).
      { rewrite Hclosed_sub. reflexivity. }
      rewrite Hmemt. simpl.
      destruct (Nat.eq_dec j i) as [Heq | _]; [contradiction |].
      rewrite Hmemw, Hmemsub.
      repeat rewrite sub_tm_comp_proved.
      rewrite IH; auto.
  - destruct (Nat.eq_dec j i) as [Heq | Hneq].
    + subst.
      simpl.
      destruct (Nat.eq_dec i i) as [_ | Hbad]; [| contradiction].
      repeat rewrite sub_tm_comp_proved.
      reflexivity.
    + assert (Hmemt : mem_nat j (fv_tm t) = false).
      { eapply mem_nat_false_of_subset_singleton_ne; eauto. }
      assert (Hmemw : mem_nat j (fv_tm w) = false).
      { rewrite Hw. reflexivity. }
      assert (Hclosed_sub : fv_tm (sub_tm t i w) = []).
      { apply fv_tm_sub_closed; assumption. }
      assert (Hmemsub : mem_nat j (fv_tm (sub_tm t i w)) = false).
      { rewrite Hclosed_sub. reflexivity. }
      rewrite Hmemt. simpl.
      destruct (Nat.eq_dec j i) as [Heq | _]; [contradiction |].
      rewrite Hmemw, Hmemsub.
      repeat rewrite sub_tm_comp_proved.
      rewrite IH; auto.
Qed.

Record bounded_tarski_system : Type := {
  carrier : Type;
  eps : carrier;
  cat : carrier -> carrier -> carrier;
  clen : carrier -> nat;
  code : coding carrier;
  tag : label -> carrier;
  numeral : nat -> carrier;

  Tm : nat -> carrier -> Prop;
  OFm : nat -> carrier -> Prop;
  Fm : nat -> carrier -> Prop;
  Sent : nat -> carrier -> Prop;
  Tr : nat -> carrier -> Prop;
  T : nat -> carrier -> Prop;

  quote_tm : nat -> tm carrier -> carrier;
  quote_ofm : nat -> ofm carrier -> carrier;
  quote_fm : nat -> fm carrier -> carrier;
  decode_fm : nat -> carrier -> option (fm carrier);
  quote_fm_decode :
    forall n phi, decode_fm n (quote_fm n phi) = Some phi;
  quote_fm_injective :
    forall n (phi psi : fm carrier),
      quote_fm n phi = quote_fm n psi -> phi = psi;

  bar : nat -> carrier -> tm carrier;
  bar_closed : forall n s, fv_tm (bar n s) = [];
  dterm : nat -> tm carrier -> tm carrier;
  gterm : nat -> tm carrier -> tm carrier;
  Dfun : nat -> carrier -> carrier;
  Gfun : nat -> carrier -> carrier;
  q : nat -> fm carrier -> tm carrier;

  val : nat -> tm carrier -> (nat -> carrier) -> carrier;
  sat : nat -> fm carrier -> (nat -> carrier) -> Prop;

  val_var : forall n i alpha, val n (TVar i) alpha = alpha i;
  val_bar : forall n s alpha, val n (bar n s) alpha = s;
  val_app :
    forall n u v alpha,
      val n (TApp u v) alpha = cat (val n u alpha) (val n v alpha);
  val_diag :
    forall n u alpha,
      val n (dterm n u) alpha = Dfun n (val n u alpha);
  val_gate :
    forall n u alpha,
      val n (gterm n u) alpha = Gfun n (val n u alpha);
  q_eval :
    forall n phi alpha, val (S n) (q n phi) alpha = quote_fm n phi;
  q_injective : forall n phi psi, q n phi = q n psi -> phi = psi;

  Dfun_ofm :
    forall n p phi,
      p = quote_ofm n phi ->
      Dfun n p = quote_fm n (sub_fm (FOrd phi) 0 (bar n p));
  Dfun_other :
    forall n p,
      OFm n p -> p <> p -> Dfun n p = eps;
  Gfun_fm :
    forall n e phi,
      decode_fm n e = Some phi ->
      Gfun n e = quote_fm (S (S n)) (FGate n phi);

  Fm_ord : forall n phi, Fm n (quote_fm n (FOrd phi));
  Fm_gate_iff :
    forall n e phi,
      decode_fm n e = Some phi ->
      Fm (S (S n)) (Gfun n e) <-> Sent n e /\ Tr n e;
  Sent_closed :
    forall n phi,
      closed_fm phi ->
      Sent n (quote_fm n phi);
  Tr_truth :
    forall n e phi,
      decode_fm n e = Some phi ->
      Sent n e ->
      (Tr n e <-> sat n phi (fun _ => eps));
  T_iff_Tr : forall n e, T n e <-> Tr n e;

  sat_eq :
    forall n u v alpha,
      sat n (FOrd (OEq u v)) alpha <->
      val n u alpha = val n v alpha;
  sat_len :
    forall n u v alpha,
      sat n (FOrd (OLenLe u v)) alpha <->
      clen (val n u alpha) <= clen (val n v alpha);
  sat_W :
    forall n u alpha,
      sat n (FOrd (OW (S n) u)) alpha <->
      Fm (S n) (val n u alpha);
  sat_neg :
    forall n phi alpha,
      sat n (FOrd (ONeg phi)) alpha <->
      ~ sat n (FOrd phi) alpha;
  sat_and :
    forall n phi psi alpha,
      sat n (FOrd (OAnd phi psi)) alpha <->
      sat n (FOrd phi) alpha /\ sat n (FOrd psi) alpha;
  sat_exists :
    forall n i t phi alpha,
      sat n (FOrd (OExists i t phi)) alpha <->
      exists s,
        clen s <= clen (val n t alpha) /\
        sat n (FOrd phi) (fun j => if Nat.eq_dec j i then s else alpha j);
  sat_forall :
    forall n i t phi alpha,
      sat n (FOrd (OForall i t phi)) alpha <->
      forall s,
        clen s <= clen (val n t alpha) ->
        sat n (FOrd phi) (fun j => if Nat.eq_dec j i then s else alpha j);
  sat_gate :
    forall n e alpha,
      sat (S (S n)) (FGate n e) alpha <->
      Tr n (quote_fm n e);

  sat_sub :
    forall n (phi : ofm carrier) i u alpha,
      sat n (FOrd (sub_ofm phi i u)) alpha <->
      sat n (FOrd phi)
        (fun j => if Nat.eq_dec j i then val n u alpha else alpha j);
  closed_irrelevant :
    forall n (phi : fm carrier) alpha beta,
      closed_fm phi ->
      (sat n phi alpha <-> sat n phi beta);
  closed_after_sub_zero :
    forall n (phi : ofm carrier) p,
      singleton_zero (fv_ofm phi) ->
      closed_fm (sub_fm (FOrd phi) 0 (bar n p));
  diagonal_sentence :
    forall n (theta : ofm carrier),
      singleton_zero (fv_ofm theta) ->
      let beta := ONeg (sub_ofm theta 0 (dterm n (TVar 0))) in
      closed_fm (sub_fm (FOrd beta) 0 (bar n (quote_ofm n beta)));
  diagonal_liar_equiv :
    forall n (theta : ofm carrier),
      singleton_zero (fv_ofm theta) ->
      let beta := ONeg (sub_ofm theta 0 (dterm n (TVar 0))) in
      let p := quote_ofm n beta in
      let lambda := sub_fm (FOrd beta) 0 (bar n p) in
      sat n lambda (fun _ => eps) <->
      ~ sat n
          (sub_fm (FOrd theta) 0 (bar n (quote_fm n lambda)))
          (fun _ => eps);

  two_layer_rep_to_truth :
    forall n (rho : ofm carrier),
      singleton_zero (fv_ofm rho) ->
      (forall s,
        (Fm (S (S n)) s ->
          T n (quote_fm n (sub_fm (FOrd rho) 0 (bar n s)))) /\
        (~ Fm (S (S n)) s ->
          T n (quote_fm n (FOrd (ONeg (sub_ofm rho 0 (bar n s))))))) ->
      singleton_zero (fv_ofm (sub_ofm rho 0 (gterm n (TVar 0)))) /\
      forall e phi,
        decode_fm n e = Some phi ->
        Sent n e ->
        (sat n
          (sub_fm (FOrd (sub_ofm rho 0 (gterm n (TVar 0)))) 0 (bar n e))
          (fun _ => eps) <->
         Tr n e)
}.

Definition Rep
    (H : bounded_tarski_system) (n : nat)
    (rho : ofm (carrier H)) (A : carrier H -> Prop) : Prop :=
  singleton_zero (fv_ofm rho) /\
  forall s,
    (A s -> T H n (quote_fm H n (sub_fm (FOrd rho) 0 (bar H n s)))) /\
    (~ A s -> T H n (quote_fm H n (FOrd (ONeg (sub_ofm rho 0 (bar H n s)))))).

Definition TruthDefiner
    (H : bounded_tarski_system) (n : nat) (theta : ofm (carrier H))
  : Prop :=
  singleton_zero (fv_ofm theta) /\
  forall e phi,
    decode_fm H n e = Some phi ->
    Sent H n e ->
    (sat H n (sub_fm (FOrd theta) 0 (bar H n e)) (fun _ => eps H) <->
     Tr H n e).

Theorem term_substitution_composition :
  forall H n (u t : tm (carrier H)) i s,
    subset_singleton i (fv_tm t) ->
    sub_tm (sub_tm u i t) i (bar H n s) =
    sub_tm u i (sub_tm t i (bar H n s)).
Proof.
  intros H n u t i s _.
  apply sub_tm_comp_proved.
Qed.

Theorem formula_substitution_composition :
  forall H n (phi : ofm (carrier H)) (t : tm (carrier H)) i s,
    subset_singleton i (fv_tm t) ->
    sub_ofm (sub_ofm phi i t) i (bar H n s) =
    sub_ofm phi i (sub_tm t i (bar H n s)).
Proof.
  intros H n phi t i s Ht.
  apply sub_ofm_comp_closed_proved.
  - exact Ht.
  - apply bar_closed.
Qed.

Theorem diagonal_liar_equivalence :
  forall H n (theta : ofm (carrier H)),
    singleton_zero (fv_ofm theta) ->
    let beta := ONeg (sub_ofm theta 0 (dterm H n (TVar 0))) in
    let p := quote_ofm H n beta in
    let lambda := sub_fm (FOrd beta) 0 (bar H n p) in
    sat H n lambda (fun _ => eps H) <->
    ~ sat H n
        (sub_fm (FOrd theta) 0 (bar H n (quote_fm H n lambda)))
        (fun _ => eps H).
Proof.
  intros H n theta Htheta.
  apply diagonal_liar_equiv.
  exact Htheta.
Qed.

Theorem two_layer_representation_yields_truth_definer :
  forall H n (rho : ofm (carrier H)),
    Rep H n rho (Fm H (S (S n))) ->
    TruthDefiner H n (sub_ofm rho 0 (gterm H n (TVar 0))).
Proof.
  intros H n rho [Hfv Hrep].
  apply two_layer_rep_to_truth; auto.
Qed.

Theorem adjacent_layer_strongly_representable :
  forall H n,
    Rep H n (OW (S n) (TVar 0)) (Fm H (S n)).
Proof.
  intros H n.
  split.
  - intros i Hi. simpl in Hi. destruct Hi as [Hi | []]. now symmetry.
  - intros s; split; intros Hs.
    + apply (proj2 (T_iff_Tr H n _)).
      assert (Hsent :
        Sent H n (quote_fm H n (sub_fm (FOrd (OW (S n) (TVar 0))) 0 (bar H n s)))).
      { apply Sent_closed. apply closed_after_sub_zero.
        intros i Hi. simpl in Hi. destruct Hi as [Hi | []]. now symmetry. }
      eapply Tr_truth.
      * apply quote_fm_decode.
      * exact Hsent.
      * simpl.
        rewrite sat_W.
        rewrite val_bar.
        exact Hs.
    + apply (proj2 (T_iff_Tr H n _)).
      assert (Hsent :
        Sent H n (quote_fm H n
          (FOrd (ONeg (sub_ofm (OW (S n) (TVar 0)) 0 (bar H n s)))))).
      { apply Sent_closed.
        change (closed_fm (sub_fm (FOrd (OW (S n) (TVar 0))) 0 (bar H n s))).
        apply closed_after_sub_zero.
        intros i Hi. simpl in Hi. destruct Hi as [Hi | []]. now symmetry. }
      eapply Tr_truth.
      * apply quote_fm_decode.
      * exact Hsent.
      * rewrite sat_neg.
        simpl.
        rewrite sat_W.
        rewrite val_bar.
        exact Hs.
Qed.

Theorem no_self_truth_definition :
  forall H n theta, ~ TruthDefiner H n theta.
Proof.
  intros H n theta [Hfv Htheta].
  pose (beta := ONeg (sub_ofm theta 0 (dterm H n (TVar 0)))).
  pose (p := quote_ofm H n beta).
  pose (lambda := sub_fm (FOrd beta) 0 (bar H n p)).
  assert (Hlambda_sent : Sent H n (quote_fm H n lambda)).
  { apply Sent_closed.
    unfold lambda, beta.
    apply diagonal_sentence.
    exact Hfv. }
  assert (Hdecode : decode_fm H n (quote_fm H n lambda) = Some lambda).
  { apply quote_fm_decode. }
  specialize (Htheta (quote_fm H n lambda) lambda Hdecode Hlambda_sent).
  assert (Htruth : Tr H n (quote_fm H n lambda) <->
                   sat H n lambda (fun _ => eps H)).
  { eapply Tr_truth; eauto. }
  assert (Hliar :
    sat H n lambda (fun _ => eps H) <->
    ~ sat H n (sub_fm (FOrd theta) 0 (bar H n (quote_fm H n lambda))) (fun _ => eps H)).
  {
    unfold lambda, beta.
    apply diagonal_liar_equivalence.
    exact Hfv.
  }
  destruct Htruth as [Htr_sat Hsat_tr].
  destruct Htheta as [Htheta_tr Htr_theta].
  assert (Hparadox : Tr H n (quote_fm H n lambda) <->
                     ~ Tr H n (quote_fm H n lambda)).
  {
    split; intros HT.
    - pose proof (Htr_sat HT) as Hsat_lambda.
      apply Hliar in Hsat_lambda.
      intro HT2. apply Hsat_lambda. apply Htr_theta. exact HT2.
    - apply Hsat_tr. apply Hliar.
      intro Htheta_sat. apply HT. apply Htheta_tr. exact Htheta_sat.
  }
  destruct Hparadox as [Hp Hnp].
  pose proof (Hnp (fun h => Hp h h)) as h.
  exact (Hp h h).
Qed.

Theorem no_two_layer_strong_representation :
  forall H n rho, ~ Rep H n rho (Fm H (S (S n))).
Proof.
  intros H n rho [Hfv Hrep].
  apply (no_self_truth_definition H n (sub_ofm rho 0 (gterm H n (TVar 0)))).
  apply two_layer_representation_yields_truth_definer.
  split; auto.
Qed.

Record semantic_state (H : bounded_tarski_system) (n : nat) : Type := {
  state_assignment : nat -> carrier H;
  state_formula : fm (carrier H);
  state_formula_member : Fm H n (quote_fm H n state_formula)
}.

Definition SatCert (H : bounded_tarski_system) (n : nat)
    (st : semantic_state H n) : Prop :=
  sat H n (state_formula H n st) (state_assignment H n st).

Definition TrueCert (H : bounded_tarski_system) (n : nat)
    (e : carrier H) : Prop :=
  Sent H n e /\ forall alpha phi,
    decode_fm H n e = Some phi -> sat H n phi alpha.

Record GateCertificate (H : bounded_tarski_system) (n : nat)
    (e : carrier H) : Type := {
  gate_cert_formula : fm (carrier H);
  gate_cert_decode : decode_fm H n e = Some gate_cert_formula;
  gate_cert_sentence : Sent H n e;
  gate_cert_truth : Tr H n e
}.

Definition GateAdmits (H : bounded_tarski_system) (n : nat)
    (e : carrier H) : Prop :=
  Fm H (S (S n)) (Gfun H n e).

Theorem gate_admits_iff_true_sentence_code :
  forall H n e phi,
    decode_fm H n e = Some phi ->
    GateAdmits H n e <-> Sent H n e /\ Tr H n e.
Proof.
  intros H n e phi Hdecode.
  unfold GateAdmits.
  exact (Fm_gate_iff H n e phi Hdecode).
Qed.

Theorem gate_certificate_admitted :
  forall H n e,
    GateCertificate H n e -> GateAdmits H n e.
Proof.
  intros H n e C.
  destruct C as [phi Hdecode Hsent Htruth].
  unfold GateAdmits.
  apply (proj2 (Fm_gate_iff H n e phi Hdecode)).
  split; assumption.
Qed.

Theorem gate_admission_yields_certificate :
  forall H n e phi,
    decode_fm H n e = Some phi ->
    GateAdmits H n e ->
    GateCertificate H n e.
Proof.
  intros H n e phi Hdecode Hadmit.
  pose proof
    (proj1 (gate_admits_iff_true_sentence_code H n e phi Hdecode) Hadmit)
    as [Hsent Htruth].
  refine {| gate_cert_formula := phi |}; assumption.
Qed.

Definition semantic_consequence
    (H : bounded_tarski_system) (n : nat)
    (Gamma : fm (carrier H) -> Prop) (phi : fm (carrier H)) : Prop :=
  forall alpha,
    (forall gamma, Gamma gamma -> sat H n gamma alpha) ->
    sat H n phi alpha.

Theorem bounded_semantics_nontrivial :
  forall H n,
    sat H n (FOrd (OEq (TConst (eps H)) (TConst (eps H))))
      (fun _ => eps H) /\
    ~ sat H n (FOrd (ONeg (OEq (TConst (eps H)) (TConst (eps H)))))
      (fun _ => eps H).
Proof.
  intros H n.
  split.
  - apply (proj2 (sat_eq H n
      (TConst (eps H)) (TConst (eps H)) (fun _ => eps H))).
    reflexivity.
  - intro Hneg.
    apply (proj1 (sat_neg H n
      (OEq (TConst (eps H)) (TConst (eps H))) (fun _ => eps H))) in Hneg.
    apply Hneg.
    apply (proj2 (sat_eq H n
      (TConst (eps H)) (TConst (eps H)) (fun _ => eps H))).
    reflexivity.
Qed.
Record formal_system : Type := {
  fs_system : bounded_tarski_system;
  fs_adjacent_rep :
    forall n, Rep fs_system n (OW (S n) (TVar 0)) (Fm fs_system (S n));
  fs_no_truth :
    forall n theta, ~ TruthDefiner fs_system n theta;
  fs_no_two_layer :
    forall n rho, ~ Rep fs_system n rho (Fm fs_system (S (S n)));
  fs_semantic_nontriviality :
    forall n,
      sat fs_system n
        (FOrd (OEq (TConst (eps fs_system)) (TConst (eps fs_system))))
        (fun _ => eps fs_system) /\
      ~ sat fs_system n
        (FOrd (ONeg (OEq (TConst (eps fs_system)) (TConst (eps fs_system)))))
        (fun _ => eps fs_system)
}.

Definition build_formal_system (H : bounded_tarski_system) : formal_system := {|
  fs_system := H;
  fs_adjacent_rep := adjacent_layer_strongly_representable H;
  fs_no_truth := no_self_truth_definition H;
  fs_no_two_layer := no_two_layer_strong_representation H;
  fs_semantic_nontriviality := bounded_semantics_nontrivial H
|}.

End BoundedTarskiSyntaxGate.
