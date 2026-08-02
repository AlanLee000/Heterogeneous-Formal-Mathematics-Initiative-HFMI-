From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.

Import ListNotations.

Set Implicit Arguments.

Module HypergraphModalRewrite788.

Inductive star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| star_refl : forall x, star R x x
| star_step : forall x y z, R x y -> star R y z -> star R x z.

Lemma star_trans :
  forall (A : Type) (R : A -> A -> Prop) x y z,
    star R x y -> star R y z -> star R x z.
Proof.
  intros A R x y z Hxy.
  revert z.
  induction Hxy as [x|x y mid Hxy Hymid IH]; intros z Hyz.
  - exact Hyz.
  - eapply star_step.
    + exact Hxy.
    + exact (IH z Hyz).
Qed.

Lemma star_monotone :
  forall (A : Type) (R S : A -> A -> Prop),
    (forall x y, R x y -> S x y) ->
    forall x y, star R x y -> star S x y.
Proof.
  intros A R S Hsub x y Hxy.
  induction Hxy as [x|x y z Hxy Hyz IH].
  - constructor.
  - eapply star_step.
    + exact (Hsub x y Hxy).
    + exact IH.
Qed.

Section Signature.

Context {Fun : Type}.
Variable ar : Fun -> nat.

Inductive Term : Type :=
| TVar : nat -> Term
| TApp : Fun -> list Term -> Term.

Inductive wf_term : Term -> Prop :=
| wf_var : forall x, wf_term (TVar x)
| wf_app :
    forall f args,
      length args = ar f ->
      Forall wf_term args ->
      wf_term (TApp f args).

Inductive FV : nat -> Term -> Prop :=
| fv_var : forall x, FV x (TVar x)
| fv_app :
    forall x f args t,
      In t args ->
      FV x t ->
      FV x (TApp f args).

Definition BV (_x : nat) (_t : Term) : Prop := False.

Inductive SubRel : Term -> nat -> Term -> Term -> Prop :=
| sub_var_same :
    forall x s, SubRel (TVar x) x s s
| sub_var_diff :
    forall y x s, y <> x -> SubRel (TVar y) x s (TVar y)
| sub_app :
    forall f args args' x s,
      Forall2 (fun a b => SubRel a x s b) args args' ->
      SubRel (TApp f args) x s (TApp f args').

Definition alpha_equiv (t u : Term) : Prop := t = u.

Section Hypergraph.

Context {V Edge : Type}.
Variable in_edge : Edge -> V -> Prop.
Variable node_edge_total : forall v : V, exists e : Edge, in_edge e v.
Variable rho : V -> Term -> Term -> Prop.

Definition Rel : Type := Term -> Term -> Prop.
Definition RelVec : Type := V -> Term -> Term -> Prop.

Definition eta (v : V) (e : Edge) : Prop := in_edge e v.

Definition rel_comp (P Q : Rel) : Rel :=
  fun s t => exists u, P s u /\ Q u t.

Definition rel_star (P : Rel) : Rel := star P.

Definition rel_le (R S : Rel) : Prop :=
  forall t u, R t u -> S t u.

Definition relvec_le (R S : RelVec) : Prop :=
  forall v t u, R v t u -> S v t u.

Definition relvec_equiv (R S : RelVec) : Prop :=
  relvec_le R S /\ relvec_le S R.

Record closure_props (R C : Rel) : Prop := {
  cp_base : forall s t, R s t -> C s t;
  cp_refl : forall t, C t t;
  cp_sym : forall s t, C s t -> C t s;
  cp_trans : forall s u t, C s u -> C u t -> C s t;
  cp_app :
    forall f xs ys,
      length xs = ar f ->
      length ys = ar f ->
      Forall2 C xs ys ->
      C (TApp f xs) (TApp f ys)
}.

Definition cong_closure (R : Rel) : Rel :=
  fun s t => forall C : Rel, closure_props R C -> C s t.

Lemma cc_base : forall R s t, R s t -> cong_closure R s t.
Proof.
  unfold cong_closure; intros R s t H C HC.
  exact (cp_base HC s t H).
Qed.

Lemma cc_refl : forall R t, cong_closure R t t.
Proof.
  unfold cong_closure; intros R t C HC.
  exact (cp_refl HC t).
Qed.

Lemma cc_sym :
  forall R s t, cong_closure R s t -> cong_closure R t s.
Proof.
  unfold cong_closure; intros R s t H C HC.
  exact (cp_sym HC s t (H C HC)).
Qed.

Lemma cc_trans :
  forall R s u t,
    cong_closure R s u ->
    cong_closure R u t ->
    cong_closure R s t.
Proof.
  unfold cong_closure; intros R s u t Hsu Hut C HC.
  exact (cp_trans HC s u t (Hsu C HC) (Hut C HC)).
Qed.

Lemma cc_app :
  forall R f xs ys,
    length xs = ar f ->
    length ys = ar f ->
    Forall2 (cong_closure R) xs ys ->
    cong_closure R (TApp f xs) (TApp f ys).
Proof.
  unfold cong_closure; intros R f xs ys Hx Hy Hargs C HC.
  assert (HargsC : Forall2 C xs ys).
  { clear f Hx Hy.
    induction Hargs.
    - constructor.
    - constructor.
      + exact (H C HC).
      + exact IHHargs.
  }
  exact (@cp_app R C HC f xs ys Hx Hy HargsC).
Qed.

Lemma cong_closure_monotone :
  forall R S, rel_le R S -> rel_le (cong_closure R) (cong_closure S).
Proof.
  intros R S Hsub t u Htu.
  unfold cong_closure in *.
  intros C HC.
  apply Htu.
  refine {| cp_base := _;
            cp_refl := cp_refl HC;
            cp_sym := cp_sym HC;
            cp_trans := cp_trans HC;
            cp_app := cp_app HC |}.
  intros s r HR.
  exact (cp_base HC s r (Hsub s r HR)).
Qed.

Definition union_edge (R : RelVec) (e : Edge) : Rel :=
  fun t u => exists v : V, in_edge e v /\ R v t u.

Definition theta (R : RelVec) (e : Edge) : Rel :=
  cong_closure (union_edge R e).

Lemma theta_monotone :
  forall R S,
    relvec_le R S ->
    forall e, rel_le (theta R e) (theta S e).
Proof.
  intros R S HRS e.
  apply cong_closure_monotone.
  intros t u [v [Hve HR]].
  exists v; split; [exact Hve | exact (HRS v t u HR)].
Qed.

Definition one_env (R : RelVec) (v : V) : Rel :=
  fun t u => exists e : Edge, in_edge e v /\ theta R e t u.

Definition env_equiv (R : RelVec) (v : V) : Rel :=
  star (one_env R v).

Lemma env_monotone :
  forall R S,
    relvec_le R S ->
    forall v, rel_le (env_equiv R v) (env_equiv S v).
Proof.
  intros R S HRS v t u Henv.
  refine (@star_monotone Term (one_env R v) (one_env S v) _ t u Henv).
  intros a b Hstep.
  destruct Hstep as [e [Hev Htheta]].
  exists e; split.
  - exact Hev.
  - exact (@theta_monotone R S HRS e a b Htheta).
Qed.

Definition psi (R : RelVec) : RelVec :=
  fun v t s =>
    exists l r,
      env_equiv R v t l /\
      rho v l r /\
      env_equiv R v r s.

Theorem psi_monotone :
  forall R S, relvec_le R S -> relvec_le (psi R) (psi S).
Proof.
  intros R S HRS v t s [l [r [Htl [Hlr Hrs]]]].
  exists l, r.
  repeat split.
  - exact (@env_monotone R S HRS v t l Htl).
  - exact Hlr.
  - exact (@env_monotone R S HRS v r s Hrs).
Qed.

Definition prefixed (R : RelVec) : Prop := relvec_le (psi R) R.

Definition R_infty : RelVec :=
  fun v t s => forall R, prefixed R -> R v t s.

Lemma R_infty_lower :
  forall R, prefixed R -> relvec_le R_infty R.
Proof.
  intros R HR v t s Hinf.
  exact (Hinf R HR).
Qed.

Lemma R_infty_prefixed : prefixed R_infty.
Proof.
  intros v t s Hpsi R HR.
  apply HR.
  apply (@psi_monotone R_infty R).
  - intros w a b Hab.
    exact (Hab R HR).
  - exact Hpsi.
Qed.

Lemma R_infty_le_psi : relvec_le R_infty (psi R_infty).
Proof.
  intros v t s Hinf.
  apply Hinf.
  intros w a b Hpp.
  apply (@psi_monotone (psi R_infty) R_infty).
  - exact R_infty_prefixed.
  - exact Hpp.
Qed.

Theorem R_infty_fixed : relvec_equiv (psi R_infty) R_infty.
Proof.
  split.
  - exact R_infty_prefixed.
  - exact R_infty_le_psi.
Qed.

Definition semantic_rw (v : V) (t s : Term) : Prop := R_infty v t s.

Inductive Judgment : Type :=
| JRw : V -> Term -> Term -> Judgment
| JEq : Edge -> Term -> Term -> Judgment
| JEnv : V -> Term -> Term -> Judgment.

Definition eqv_premises (e : Edge) (xs ys : list Term) : list Judgment :=
  map (fun p => JEq e (fst p) (snd p)) (combine xs ys).

Inductive ruleHMR : list Judgment -> Judgment -> Prop :=
| Rule_Base :
    forall v l r,
      rho v l r ->
      ruleHMR [] (JRw v l r)
| Rule_EqInit :
    forall e v t s,
      in_edge e v ->
      ruleHMR [JRw v t s] (JEq e t s)
| Rule_EqRefl :
    forall e t,
      ruleHMR [] (JEq e t t)
| Rule_EqSymm :
    forall e t s,
      ruleHMR [JEq e t s] (JEq e s t)
| Rule_EqTrans :
    forall e t u s,
      ruleHMR [JEq e t u; JEq e u s] (JEq e t s)
| Rule_EqCong :
    forall e f xs ys,
      length xs = ar f ->
      length ys = ar f ->
      ruleHMR (eqv_premises e xs ys) (JEq e (TApp f xs) (TApp f ys))
| Rule_Context :
    forall e v t s,
      in_edge e v ->
      ruleHMR [JEq e t s] (JEnv v t s)
| Rule_EnvTrans :
    forall v t u s,
      ruleHMR [JEnv v t u; JEnv v u s] (JEnv v t s)
| Rule_RewriteModulo :
    forall v t l r s,
      ruleHMR [JEnv v t l; JRw v l r; JEnv v r s] (JRw v t s).

Inductive derives : Judgment -> Prop :=
| derives_step :
    forall premises J,
      ruleHMR premises J ->
      derives_list premises ->
      derives J
with derives_list : list Judgment -> Prop :=
| derives_nil : derives_list []
| derives_cons :
    forall J premises,
      derives J ->
      derives_list premises ->
      derives_list (J :: premises).

Definition derivation_tree_node_rw (v : V) (t s : Term) : Prop :=
  derives (JRw v t s).

Inductive premises_before : list Judgment -> list Judgment -> Prop :=
| pb_nil : forall lines, premises_before [] lines
| pb_here :
    forall P premises lines,
      premises_before premises lines ->
      premises_before (P :: premises) (P :: lines)
| pb_skip :
    forall P premises J lines,
      premises_before (P :: premises) lines ->
      premises_before (P :: premises) (J :: lines).

Inductive derivation_sequence : list Judgment -> Prop :=
| ds_nil : derivation_sequence []
| ds_snoc :
    forall lines premises J,
      derivation_sequence lines ->
      ruleHMR premises J ->
      premises_before premises lines ->
      derivation_sequence (lines ++ [J]).

Fixpoint last_judgment (lines : list Judgment) : option Judgment :=
  match lines with
  | [] => None
  | [J] => Some J
  | _ :: rest => last_judgment rest
  end.

Definition sequence_derives (J : Judgment) : Prop :=
  exists lines, derivation_sequence lines /\ last_judgment lines = Some J.

Lemma premises_before_forall :
  forall (P : Judgment -> Prop) premises lines,
    Forall P lines ->
    premises_before premises lines ->
    Forall P premises.
Proof.
  intros P premises lines Hlines Hbefore.
  induction Hbefore.
  - constructor.
  - inversion Hlines as [|J0 lines0 Hhead Htail]; subst.
    constructor; [exact Hhead |].
    exact (IHHbefore Htail).
  - inversion Hlines as [|J0 lines0 Hhead Htail]; subst.
    exact (IHHbefore Htail).
Qed.

Lemma derives_list_from_forall :
  forall premises,
    Forall derives premises ->
    derives_list premises.
Proof.
  intros premises Hprem.
  induction Hprem as [|P premises HP Hrest IH].
  - constructor.
  - constructor.
    + exact HP.
    + exact IH.
Qed.

Lemma derivation_sequence_all_derives :
  forall lines,
    derivation_sequence lines ->
    Forall derives lines.
Proof.
  intros lines Hseq.
  induction Hseq.
  - constructor.
  - apply Forall_app.
    split.
    + exact IHHseq.
    + constructor.
      * eapply derives_step.
        -- exact H.
        -- apply derives_list_from_forall.
           eapply premises_before_forall; eauto.
      * constructor.
Qed.

Theorem sequence_derives_sound :
  forall J,
    sequence_derives J ->
    derives J.
Proof.
  intros J [lines [Hseq Hlast]].
  pose proof (@derivation_sequence_all_derives lines Hseq) as Hderives.
  assert (Hlast_sound :
    forall ls J,
      Forall derives ls ->
      last_judgment ls = Some J ->
      derives J).
  {
    intros ls.
    induction ls as [|x xs IH]; intros J0 HFor Hlast0.
    - simpl in Hlast0.
      discriminate Hlast0.
    - destruct xs as [|y ys].
      + simpl in Hlast0. inversion Hlast0; subst.
        inversion HFor; subst; assumption.
      + simpl in Hlast0.
        inversion HFor; subst.
        eapply IH; eassumption.
  }
  exact (Hlast_sound lines J Hderives Hlast).
Qed.

Lemma last_judgment_snoc :
  forall lines J,
    last_judgment (lines ++ [J]) = Some J.
Proof.
  induction lines as [|x xs IH]; intros J.
  - reflexivity.
  - destruct xs as [|y ys].
    + reflexivity.
    + simpl. exact (IH J).
Qed.

Lemma last_judgment_in :
  forall lines J,
    last_judgment lines = Some J ->
    In J lines.
Proof.
  induction lines as [|x xs IH]; intros J Hlast.
  - simpl in Hlast. discriminate Hlast.
  - destruct xs as [|y ys].
    + simpl in Hlast. inversion Hlast; subst. left; reflexivity.
    + simpl in Hlast. right. exact (IH J Hlast).
Qed.

Lemma derivation_sequence_app :
  forall left right,
    derivation_sequence left ->
    derivation_sequence right ->
    derivation_sequence (left ++ right).
Proof.
  intros left right Hleft Hright.
  induction Hright as [|lines premises J Hseq IH Hrule Hprem].
  - rewrite app_nil_r. exact Hleft.
  - rewrite app_assoc.
    apply ds_snoc with (premises := premises).
    + exact IH.
    + exact Hrule.
    + clear Hleft Hseq IH Hrule.
      induction left as [|L left IHleft].
      * exact Hprem.
      * simpl.
        destruct premises as [|P ps].
        -- constructor.
        -- apply pb_skip. exact IHleft.
Qed.

Lemma premises_before_weaken_left :
  forall premises left right,
    premises_before premises right ->
    premises_before premises (left ++ right).
Proof.
  intros premises left right Hprem.
  induction left as [|L left IH].
  - exact Hprem.
  - simpl.
    destruct premises as [|P ps].
    + constructor.
    + apply pb_skip. exact IH.
Qed.

Lemma premises_before_cons_app :
  forall P premises left right,
    In P left ->
    premises_before premises right ->
    premises_before (P :: premises) (left ++ right).
Proof.
  intros P premises left right Hin Hprem.
  induction left as [|L left IH].
  - contradiction.
  - simpl in *.
    destruct Hin as [HL | Hin].
    + subst L.
      apply pb_here.
      apply premises_before_weaken_left.
      exact Hprem.
    + apply pb_skip.
      exact (IH Hin).
Qed.

Lemma sequence_derives_list_from_forall :
  forall premises,
    Forall sequence_derives premises ->
    exists lines,
      derivation_sequence lines /\
      premises_before premises lines.
Proof.
  intros premises Hprem.
  induction Hprem as [|P premises HPseq Hrest IH].
  - exists [].
    split; constructor.
  - destruct HPseq as [linesP [HseqP HlastP]].
    destruct IH as [linesRest [HseqRest HInRest]].
    exists (linesP ++ linesRest).
    split.
    + apply derivation_sequence_app; assumption.
    + apply premises_before_cons_app.
      * eapply last_judgment_in; eassumption.
      * exact HInRest.
Qed.

Lemma rule_sequence_derives :
  forall premises J,
    ruleHMR premises J ->
    Forall sequence_derives premises ->
    sequence_derives J.
Proof.
  intros premises J Hrule Hseqs.
  destruct (@sequence_derives_list_from_forall premises Hseqs)
    as [lines [Hlines HpremIn]].
  exists (lines ++ [J]).
  split.
  - apply ds_snoc with (premises := premises); assumption.
  - apply last_judgment_snoc.
Qed.

Fixpoint derives_to_sequence (J : Judgment) (H : derives J) {struct H}
    : sequence_derives J
with derives_list_to_sequence_list
    (premises : list Judgment) (H : derives_list premises) {struct H}
    : Forall sequence_derives premises.
Proof.
  - destruct H as [premises J Hrule Hprem].
    exact (rule_sequence_derives Hrule
             (derives_list_to_sequence_list premises Hprem)).
  - destruct H as [|J premises HJ Hprem].
    + constructor.
    + constructor.
      * exact (derives_to_sequence J HJ).
      * exact (derives_list_to_sequence_list premises Hprem).
Defined.

Theorem derives_sequence_iff :
  forall J,
    derives J <-> sequence_derives J.
Proof.
  intros J.
  split.
  - apply derives_to_sequence.
  - apply sequence_derives_sound.
Qed.

Definition syntactic_derives (J : Judgment) : Prop := sequence_derives J.

Definition syntactic_node_rw (v : V) (t s : Term) : Prop :=
  syntactic_derives (JRw v t s).

Definition jud_sem (J : Judgment) : Prop :=
  match J with
  | JRw v t s => R_infty v t s
  | JEq e t s => theta R_infty e t s
  | JEnv v t s => env_equiv R_infty v t s
  end.

Lemma Forall_eqv_premises_forall2 :
  forall e xs ys,
    length xs = length ys ->
    Forall jud_sem (eqv_premises e xs ys) ->
    Forall2 (cong_closure (union_edge R_infty e)) xs ys.
Proof.
  intros e xs.
  induction xs as [|x xs IH]; intros ys Hlen Hsem.
  - destruct ys; [constructor | discriminate].
  - destruct ys as [|y ys]; [discriminate |].
    simpl in Hlen.
    inversion Hlen as [Hlen'].
    simpl in Hsem.
    inversion Hsem as [|J rest Hxy Hrest]; subst.
    constructor.
    + exact Hxy.
    + exact (IH ys Hlen' Hrest).
Qed.

Lemma Forall2_derives_eqv_premises :
  forall e xs ys,
    Forall2 (fun x y => derives (JEq e x y)) xs ys ->
    derives_list (eqv_premises e xs ys).
Proof.
  intros e xs ys Hxy.
  induction Hxy.
  - constructor.
  - simpl.
    constructor; assumption.
Qed.

Lemma rule_sound :
  forall premises J,
    ruleHMR premises J ->
    Forall jud_sem premises ->
    jud_sem J.
Proof.
  intros premises J Hrule Hprem.
  destruct Hrule.
  - simpl.
    apply (proj1 R_infty_fixed).
    exists l, r.
    repeat split.
    + constructor.
    + exact H.
    + constructor.
  - simpl in *.
    inversion Hprem as [|J rest Hrw Hnil]; subst.
    eapply cc_base.
    exists v; split; [exact H | exact Hrw].
  - simpl.
    apply cc_refl.
  - simpl in *.
    inversion Hprem as [|J rest Hts Hnil]; subst.
    exact (cc_sym Hts).
  - simpl in *.
    inversion Hprem as [|J1 rest Htu Hrest]; subst.
    inversion Hrest as [|J2 rest' Hus Hnil]; subst.
    eapply cc_trans; eauto.
  - simpl in *.
    eapply cc_app; eauto.
    apply Forall_eqv_premises_forall2.
    + rewrite H, H0; reflexivity.
    + exact Hprem.
  - simpl in *.
    inversion Hprem as [|J rest Heq Hnil]; subst.
    eapply star_step.
    + exists e; split; [exact H | exact Heq].
    + constructor.
  - simpl in *.
    inversion Hprem as [|J1 rest Htu Hrest]; subst.
    inversion Hrest as [|J2 rest' Hus Hnil]; subst.
    exact (star_trans Htu Hus).
  - simpl in *.
    inversion Hprem as [|J1 rest Htl Hrest]; subst.
    inversion Hrest as [|J2 rest2 Hlr Hrest2]; subst.
    inversion Hrest2 as [|J3 rest3 Hrs Hnil]; subst.
    pose proof (proj2 R_infty_fixed v l r Hlr) as Hpsi.
    destruct Hpsi as [l0 [r0 [Hll0 [Hrho Hr0r]]]].
    apply (proj1 R_infty_fixed).
    exists l0, r0.
    repeat split.
    + exact (star_trans Htl Hll0).
    + exact Hrho.
    + exact (star_trans Hr0r Hrs).
Qed.

Fixpoint derives_sound (J : Judgment) (H : derives J) {struct H}
    : jud_sem J
with derives_list_sound
    (premises : list Judgment) (H : derives_list premises) {struct H}
    : Forall jud_sem premises.
Proof.
  - destruct H as [premises J Hrule Hprem].
    exact (rule_sound Hrule (derives_list_sound premises Hprem)).
  - destruct H as [|J premises HJ Hprem].
    + constructor.
    + constructor.
      * exact (derives_sound J HJ).
      * exact (derives_list_sound premises Hprem).
Defined.

Theorem syntactic_soundness :
  forall v t s,
    syntactic_node_rw v t s ->
    semantic_rw v t s.
Proof.
  intros v t s Hsyn.
  exact (derives_sound (sequence_derives_sound Hsyn)).
Qed.

Fixpoint approx (n : nat) : RelVec :=
  match n with
  | O => fun _ _ _ => False
  | S k => psi (approx k)
  end.

Definition omega_union : RelVec :=
  fun v t s => exists n, approx n v t s.

Definition psi_omega_continuity : Prop :=
  relvec_equiv
    (psi omega_union)
    (fun v t s => exists n, psi (approx n) v t s).

Lemma approx_le_prefixed :
  forall n R, prefixed R -> relvec_le (approx n) R.
Proof.
  induction n as [|n IH]; intros R HR v t s Hn.
  - contradiction.
  - simpl in Hn.
    apply HR.
    apply (@psi_monotone (approx n) R).
    + exact (IH R HR).
    + exact Hn.
Qed.

Lemma omega_union_le_R_infty : relvec_le omega_union R_infty.
Proof.
  intros v t s [n Hn] R HR.
  exact (approx_le_prefixed n HR v t s Hn).
Qed.

Lemma omega_union_prefixed :
  psi_omega_continuity -> prefixed omega_union.
Proof.
  intros Hcont v t s Hpsi.
  destruct Hcont as [Hleft _].
  destruct (Hleft v t s Hpsi) as [n Hn].
  exists (S n).
  exact Hn.
Qed.

Theorem omega_continuity_R_infty :
  psi_omega_continuity ->
  relvec_equiv R_infty omega_union.
Proof.
  intros Hcont.
  split.
  - intros v t s Hinf.
    exact (Hinf omega_union (omega_union_prefixed Hcont)).
  - exact omega_union_le_R_infty.
Qed.

Lemma theta_complete :
  forall R,
    (forall v t s, R v t s -> derives (JRw v t s)) ->
    forall e t s, theta R e t s -> derives (JEq e t s).
Proof.
  intros R HR e t s Htheta.
  unfold theta, cong_closure in Htheta.
  apply Htheta.
  refine {| cp_base := _;
            cp_refl := _;
            cp_sym := _;
            cp_trans := _;
            cp_app := _ |}.
  - intros a b [v [Hev HRv]].
    eapply derives_step.
    + apply Rule_EqInit; exact Hev.
    + constructor; [exact (HR v a b HRv) | constructor].
  - intros a.
    eapply derives_step.
    + apply Rule_EqRefl.
    + constructor.
  - intros a b Hab.
    eapply derives_step.
    + apply Rule_EqSymm.
    + constructor; [exact Hab | constructor].
  - intros a b c Hab Hbc.
    eapply derives_step.
    + apply Rule_EqTrans.
    + constructor; [exact Hab | constructor; [exact Hbc | constructor]].
  - intros f xs ys Hx Hy Hargs.
    eapply derives_step.
    + eapply Rule_EqCong; eauto.
    + exact (@Forall2_derives_eqv_premises e xs ys Hargs).
Qed.

Lemma env_complete :
  forall R,
    (forall v t s, R v t s -> derives (JRw v t s)) ->
    forall v t s, env_equiv R v t s -> derives (JEnv v t s).
Proof.
  intros R HR v t s Henv.
  induction Henv as [t|t u s Hone Hrest IH].
  - destruct (node_edge_total v) as [e Hev].
    eapply derives_step.
    + apply Rule_Context; exact Hev.
    + constructor.
      * eapply derives_step.
        -- apply Rule_EqRefl.
        -- constructor.
      * constructor.
  - destruct Hone as [e [Hev Htheta]].
    eapply derives_step.
    + apply Rule_EnvTrans.
    + constructor.
      * eapply derives_step.
        -- apply Rule_Context; exact Hev.
        -- constructor; [exact (theta_complete HR Htheta) | constructor].
      * constructor; [exact IH | constructor].
Qed.

Theorem approx_complete :
  forall n v t s,
    approx n v t s ->
    derives (JRw v t s).
Proof.
  induction n as [|n IH]; intros v t s Hn.
  - contradiction.
  - simpl in Hn.
    destruct Hn as [l [r [Htl [Hrho Hrs]]]].
    eapply derives_step.
    + apply Rule_RewriteModulo.
    + constructor.
      * exact (env_complete IH Htl).
      * constructor.
        -- eapply derives_step.
           ++ apply Rule_Base; exact Hrho.
           ++ constructor.
        -- constructor; [exact (env_complete IH Hrs) | constructor].
Qed.

Theorem omega_union_complete :
  forall v t s,
    omega_union v t s ->
    syntactic_node_rw v t s.
Proof.
  intros v t s [n Hn].
  exact (derives_to_sequence (@approx_complete n v t s Hn)).
Qed.

Theorem semantic_completeness_under_omega_continuity :
  psi_omega_continuity ->
  forall v t s,
    semantic_rw v t s ->
    syntactic_node_rw v t s.
Proof.
  intros Hcont v t s Hsem.
  destruct (omega_continuity_R_infty Hcont) as [Hto _].
  exact (omega_union_complete (Hto v t s Hsem)).
Qed.

Record HMRSystem : Type := {
  hmr_system_marker : unit;
  hmr_signature_functions : Type := Fun;
  hmr_arity : Fun -> nat := ar;
  hmr_nodes : Type := V;
  hmr_edges : Type := Edge;
  hmr_incidence : Edge -> V -> Prop := in_edge;
  hmr_node_edge_total : forall v : V, exists e : Edge, in_edge e v
    := node_edge_total;
  hmr_eta : V -> Edge -> Prop := eta;
  hmr_terms : Type := Term;
  hmr_wf_term : Term -> Prop := wf_term;
  hmr_fv : nat -> Term -> Prop := FV;
  hmr_bv : nat -> Term -> Prop := BV;
  hmr_substitution_graph : Term -> nat -> Term -> Term -> Prop := SubRel;
  hmr_alpha_equiv : Term -> Term -> Prop := alpha_equiv;
  hmr_primitive_rewrite : V -> Term -> Term -> Prop := rho;
  hmr_relation_comp : Rel -> Rel -> Rel := rel_comp;
  hmr_relation_star : Rel -> Rel := rel_star;
  hmr_congruence_closure : Rel -> Rel := cong_closure;
  hmr_theta : RelVec -> Edge -> Rel := theta;
  hmr_environment_equiv : RelVec -> V -> Rel := env_equiv;
  hmr_semantic_operator : RelVec -> RelVec := psi;
  hmr_least_fixed_point : RelVec := R_infty;
  hmr_semantic_rewrite : V -> Term -> Term -> Prop := semantic_rw;
  hmr_judgment : Type := Judgment;
  hmr_rule : list Judgment -> Judgment -> Prop := ruleHMR;
  hmr_derives : Judgment -> Prop := syntactic_derives;
  hmr_syntactic_rewrite : V -> Term -> Term -> Prop := syntactic_node_rw;
  hmr_tree_sequence_equivalence :
    forall J, derives J <-> syntactic_derives J := derives_sequence_iff;
  hmr_soundness :
    forall v t s, syntactic_node_rw v t s -> semantic_rw v t s
    := syntactic_soundness;
  hmr_completeness_condition : Prop := psi_omega_continuity;
  hmr_conditional_completeness :
    psi_omega_continuity ->
    forall v t s, semantic_rw v t s -> syntactic_node_rw v t s
    := semantic_completeness_under_omega_continuity
}.

End Hypergraph.

End Signature.

End HypergraphModalRewrite788.
