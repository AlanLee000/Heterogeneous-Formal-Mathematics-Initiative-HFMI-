(** Height/history stability for the HRISS evaluator. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

Definition history_agree {Sig H} (k : nat)
    (rs ss : list (RunMap Sig H)) : Prop :=
  forall j, j < k ->
    nth j rs (run_bottom Sig H) = nth j ss (run_bottom Sig H).

Lemma history_agree_mono : forall Sig H k l
    (rs ss : list (RunMap Sig H)),
    l <= k -> history_agree k rs ss -> history_agree l rs ss.
Proof.
  unfold history_agree. intros Sig H k l rs ss Hlk Hag j Hj.
  apply Hag. lia.
Qed.

Lemma tm_head_le_tml : forall Sig n (x : tm Sig) (xs : tml Sig n),
    tm_height x <= tml_height (TCons x xs).
Proof. intros; destruct xs; cbn; lia. Qed.

Lemma tml_tail_le_tml : forall Sig n (x : tm Sig) (xs : tml Sig n),
    tml_height xs <= tml_height (TCons x xs).
Proof. intros; destruct xs; cbn; lia. Qed.

Lemma fm_head_le_fml : forall Sig n (p : fm Sig) (ps : fml Sig n),
    fm_height p <= fml_height (FCons p ps).
Proof. intros; destruct ps; cbn; lia. Qed.

Lemma fml_tail_le_fml : forall Sig n (p : fm Sig) (ps : fml Sig n),
    fml_height ps <= fml_height (FCons p ps).
Proof. intros; destruct ps; cbn; lia. Qed.

Fixpoint val_tm_history_agree {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) (t : tm Sig) {struct t} :
    forall rs ss,
      history_agree (tm_height t) rs ss ->
      val_tm_hist H C rs t = val_tm_hist H C ss t
with val_fm_history_agree {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) (p : fm Sig) {struct p} :
    forall rs ss,
      history_agree (fm_height p) rs ss ->
      val_fm_hist H C rs p = val_fm_hist H C ss p
with val_tml_history_agree {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) {n} (xs : tml Sig n) {struct xs} :
    forall rs ss,
      history_agree (tml_height xs) rs ss ->
      val_tml_hist H C rs xs = val_tml_hist H C ss xs
with val_fml_history_agree {Sig} (H : Subgroup)
    (C : SyntaxCoding Sig H) {n} (ps : fml Sig n) {struct ps} :
    forall rs ss,
      history_agree (fml_height ps) rs ss ->
      val_fml_hist H C rs ps = val_fml_hist H C ss ps.
Proof.
  - destruct t as [i|n f xs|u|p|u v|g]; intros rs ss Hag;
      cbn [val_tm_hist].
    + reflexivity.
    + assert (Hxs : val_tml_hist H C rs xs = val_tml_hist H C ss xs).
      { apply val_tml_history_agree.
        destruct xs; cbn in Hag |- *.
        - exact Hag.
        - eapply history_agree_mono; [|exact Hag]. lia. }
      now rewrite Hxs.
    + reflexivity.
    + reflexivity.
    + assert (Hu : val_tm_hist H C rs u = val_tm_hist H C ss u).
      { apply val_tm_history_agree.
        eapply history_agree_mono; [|exact Hag]. cbn; lia. }
      assert (Hr : nth (Nat.pred (tm_height (TRApp u v))) rs
          (run_bottom Sig H) =
          nth (Nat.pred (tm_height (TRApp u v))) ss (run_bottom Sig H)).
      { apply Hag. cbn. lia. }
      now rewrite Hu, Hr.
    + reflexivity.
  - destruct p as [n P xs|n L ps|t q|Q i q]; intros rs ss Hag;
      cbn [val_fm_hist].
    + assert (Hxs : val_tml_hist H C rs xs = val_tml_hist H C ss xs).
      { apply val_tml_history_agree.
        destruct xs; cbn in Hag |- *.
        - exact Hag.
        - eapply history_agree_mono; [|exact Hag]. lia. }
      now rewrite Hxs.
    + assert (Hps : val_fml_hist H C rs ps = val_fml_hist H C ss ps).
      { apply val_fml_history_agree.
        destruct ps; cbn in Hag |- *.
        - exact Hag.
        - eapply history_agree_mono; [|exact Hag]. lia. }
      now rewrite Hps.
    + assert (Ht : val_tm_hist H C rs t = val_tm_hist H C ss t).
      { apply val_tm_history_agree.
        eapply history_agree_mono; [|exact Hag]. cbn; lia. }
      assert (Hr : nth (Nat.pred (fm_height (FRApp t q))) rs
          (run_bottom Sig H) =
          nth (Nat.pred (fm_height (FRApp t q))) ss (run_bottom Sig H)).
      { apply Hag. cbn. lia. }
      now rewrite Ht, Hr.
    + assert (Hq : val_fm_hist H C rs q = val_fm_hist H C ss q).
      { apply val_fm_history_agree.
        eapply history_agree_mono; [|exact Hag]. cbn; lia. }
      now rewrite Hq.
  - destruct xs as [|n x xs]; intros rs ss Hag; cbn [val_tml_hist].
    + reflexivity.
    + assert (Hx : val_tm_hist H C rs x = val_tm_hist H C ss x).
      { apply val_tm_history_agree.
        eapply history_agree_mono; [|exact Hag]. apply tm_head_le_tml. }
      assert (Hxs : val_tml_hist H C rs xs = val_tml_hist H C ss xs).
      { apply val_tml_history_agree.
        eapply history_agree_mono; [|exact Hag]. apply tml_tail_le_tml. }
      now rewrite Hx, Hxs.
  - destruct ps as [|n p ps]; intros rs ss Hag; cbn [val_fml_hist].
    + reflexivity.
    + assert (Hp : val_fm_hist H C rs p = val_fm_hist H C ss p).
      { apply val_fm_history_agree.
        eapply history_agree_mono; [|exact Hag]. apply fm_head_le_fml. }
      assert (Hps : val_fml_hist H C rs ps = val_fml_hist H C ss ps).
      { apply val_fml_history_agree.
        eapply history_agree_mono; [|exact Hag]. apply fml_tail_le_fml. }
      now rewrite Hp, Hps.
Defined.

Lemma val_expr_history_agree : forall Sig H (C : SyntaxCoding Sig H) z rs ss,
    history_agree (expr_height z) rs ss ->
    val_expr_hist C rs z = val_expr_hist C ss z.
Proof.
  intros Sig H C [t|p] rs ss Hag; cbn in Hag |- *.
  - now apply val_tm_history_agree.
  - now apply val_fm_history_agree.
Qed.

Print Assumptions val_expr_history_agree.
