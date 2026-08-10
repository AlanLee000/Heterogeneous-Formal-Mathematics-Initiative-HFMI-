(** Completeness and uniqueness of finite HRISS evaluation trees. *)

From Stdlib Require Import Arith.PeanoNat Lia Logic.ProofIrrelevance.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics HRISS_v3_2_Clauses
  HRISS_v3_2_FiniteTrees.
Set Implicit Arguments.
Unset Strict Implicit.

(** A canonical finite tree is obtained by structural recursion on a
    well-formed expression. *)
Fixpoint build_tm_tree {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    (t : tm Sig) {struct t} : wf_tm H t -> TmEvalTree C e
with build_fm_tree {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    (p : fm Sig) {struct p} : wf_fm H p -> FmEvalTree C e
with build_tml_tree {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    n (xs : tml Sig n) {struct xs} : wf_tml H xs -> TmlEvalTree C e n
with build_fml_tree {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    n (ps : fml Sig n) {struct ps} : wf_fml H ps -> FmlEvalTree C e n.
Proof.
  - destruct t; cbn; intro Hwf.
    + exact (@Tree_Var Sig H C e n).
    + exact (@Tree_Fun Sig H C e n t
        (@build_tml_tree Sig H C e n t0 Hwf)).
    + exact (@Tree_QuoteT Sig H C e t Hwf).
    + exact (@Tree_QuoteF Sig H C e f Hwf).
    + exact (@Tree_RAppT Sig H C e
        (@build_tm_tree Sig H C e t1 (proj1 Hwf)) t2 (proj2 Hwf)).
    + exact (@Tree_Move Sig H C e p Hwf).
  - destruct p; cbn; intro Hwf.
    + exact (@Tree_Pred Sig H C e n p
        (@build_tml_tree Sig H C e n t Hwf)).
    + exact (@Tree_Conn Sig H C e n l
        (@build_fml_tree Sig H C e n f Hwf)).
    + exact (@Tree_RAppF Sig H C e
        (@build_tm_tree Sig H C e t (proj1 Hwf)) p (proj2 Hwf)).
    + exact (@Tree_Quant Sig H C e q n p Hwf).
  - destruct xs; cbn; intro Hwf.
    + exact (@Tree_TNil Sig H C e).
    + exact (@Tree_TCons Sig H C e n
        (@build_tm_tree Sig H C e t (proj1 Hwf))
        (@build_tml_tree Sig H C e n xs (proj2 Hwf))).
  - destruct ps; cbn; intro Hwf.
    + exact (@Tree_FNil Sig H C e).
    + exact (@Tree_FCons Sig H C e n
        (@build_fm_tree Sig H C e f (proj1 Hwf))
        (@build_fml_tree Sig H C e n ps (proj2 Hwf))).
Defined.

Fixpoint build_tm_tree_root {Sig H} (C : SyntaxCoding Sig H) e
    (t : tm Sig) (Ht : wf_tm H t) {struct t} :
    tm_tree_syntax (@build_tm_tree Sig H C e t Ht) = t
with build_fm_tree_root {Sig H} (C : SyntaxCoding Sig H) e
    (p : fm Sig) (Hp : wf_fm H p) {struct p} :
    fm_tree_syntax (@build_fm_tree Sig H C e p Hp) = p
with build_tml_tree_root {Sig H} (C : SyntaxCoding Sig H) e n
    (xs : tml Sig n) (Hxs : wf_tml H xs) {struct xs} :
    tml_tree_syntax (@build_tml_tree Sig H C e n xs Hxs) = xs
with build_fml_tree_root {Sig H} (C : SyntaxCoding Sig H) e n
    (ps : fml Sig n) (Hps : wf_fml H ps) {struct ps} :
    fml_tree_syntax (@build_fml_tree Sig H C e n ps Hps) = ps.
Proof.
  - destruct t; cbn.
    + reflexivity.
    + f_equal. apply build_tml_tree_root.
    + reflexivity.
    + reflexivity.
    + f_equal. apply build_tm_tree_root.
    + reflexivity.
  - destruct p; cbn.
    + f_equal. apply build_tml_tree_root.
    + f_equal. apply build_fml_tree_root.
    + f_equal. apply build_tm_tree_root.
    + reflexivity.
  - destruct xs; cbn.
    + reflexivity.
    + f_equal; [apply build_tm_tree_root|apply build_tml_tree_root].
  - destruct ps; cbn.
    + reflexivity.
    + f_equal; [apply build_fm_tree_root|apply build_fml_tree_root].
Defined.

Lemma build_tm_tree_value : forall Sig H (C : SyntaxCoding Sig H) e t
    (Ht : wf_tm H t),
    tm_tree_value (@build_tm_tree Sig H C e t Ht) = @ValTm Sig H C e t Ht.
Proof.
  intros Sig H C e t Ht.
  pose proof (@tm_tree_sound Sig H C e (@build_tm_tree Sig H C e t Ht)) as Hs.
  assert (Hcarrier :
      @TmCarrier Sig H
        (tm_tree_syntax (@build_tm_tree Sig H C e t Ht))
        (tm_tree_wf (@build_tm_tree Sig H C e t Ht)) =
      @TmCarrier Sig H t Ht).
  { apply sig_prop_ext. cbn. f_equal.
    apply (@build_tm_tree_root Sig H C e t Ht). }
  unfold ValTm in Hs |- *. rewrite Hcarrier in Hs.
  exact Hs.
Qed.

Lemma build_fm_tree_value : forall Sig H (C : SyntaxCoding Sig H) e p
    (Hp : wf_fm H p),
    fm_tree_value (@build_fm_tree Sig H C e p Hp) = @ValFm Sig H C e p Hp.
Proof.
  intros Sig H C e p Hp.
  pose proof (@fm_tree_sound Sig H C e (@build_fm_tree Sig H C e p Hp)) as Hs.
  assert (Hcarrier :
      @FmCarrier Sig H
        (fm_tree_syntax (@build_fm_tree Sig H C e p Hp))
        (fm_tree_wf (@build_fm_tree Sig H C e p Hp)) =
      @FmCarrier Sig H p Hp).
  { apply sig_prop_ext. cbn. f_equal.
    apply (@build_fm_tree_root Sig H C e p Hp). }
  unfold ValFm in Hs |- *. rewrite Hcarrier in Hs.
  exact Hs.
Qed.

Theorem EvalTmDerives_iff_Val : forall Sig H (C : SyntaxCoding Sig H) e t v
    (Ht : wf_tm H t),
    EvalTmDerives C e t v <-> v = @ValTm Sig H C e t Ht.
Proof.
  intros Sig H C e t v Ht. split.
  - apply EvalTmDerives_sound.
  - intro Hv. exists (@build_tm_tree Sig H C e t Ht). split.
    + apply build_tm_tree_root.
    + rewrite build_tm_tree_value. symmetry. exact Hv.
Qed.

Theorem EvalFmDerives_iff_Val : forall Sig H (C : SyntaxCoding Sig H) e p v
    (Hp : wf_fm H p),
    EvalFmDerives C e p v <-> v = @ValFm Sig H C e p Hp.
Proof.
  intros Sig H C e p v Hp. split.
  - apply EvalFmDerives_sound.
  - intro Hv. exists (@build_fm_tree Sig H C e p Hp). split.
    + apply build_fm_tree_root.
    + rewrite build_fm_tree_value. symmetry. exact Hv.
Qed.

Theorem EvalDerives_iff_Val : forall Sig H (C : SyntaxCoding Sig H) e
    (z : SyntaxCarrier Sig H) v,
    EvalDerives C e z v <-> v = Val C e z.
Proof.
  intros Sig H C e [[t|p] Hz] v; cbn.
  - change (EvalTmDerives C e t v <-> v = @ValTm Sig H C e t Hz).
    apply EvalTmDerives_iff_Val.
  - change (EvalFmDerives C e p v <-> v = @ValFm Sig H C e p Hz).
    apply EvalFmDerives_iff_Val.
Qed.

Corollary EvalDerives_unique : forall Sig H (C : SyntaxCoding Sig H) e
    (z : SyntaxCarrier Sig H) v w,
    EvalDerives C e z v -> EvalDerives C e z w -> v = w.
Proof.
  intros Sig H C e z v w Dv Dw.
  apply (proj1 (EvalDerives_iff_Val C e z v)) in Dv.
  apply (proj1 (EvalDerives_iff_Val C e z w)) in Dw.
  now rewrite Dv, Dw.
Qed.

Lemma tm_tree_size_positive : forall Sig H (C : SyntaxCoding Sig H) e
    (D : TmEvalTree C e), 1 <= tm_tree_size D.
Proof. intros; destruct D; cbn; lia. Qed.

Lemma fm_tree_size_positive : forall Sig H (C : SyntaxCoding Sig H) e
    (D : FmEvalTree C e), 1 <= fm_tree_size D.
Proof. intros; destruct D; cbn; lia. Qed.

Print Assumptions EvalDerives_iff_Val.
Print Assumptions EvalDerives_unique.
