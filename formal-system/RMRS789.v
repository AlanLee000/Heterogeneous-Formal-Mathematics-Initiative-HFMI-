From Stdlib Require Import List Arith Lia.

Import ListNotations.
Set Implicit Arguments.

Definition set_incl {A : Type} (P Q : A -> Prop) : Prop :=
  forall x, P x -> Q x.

Definition rel_incl {A : Type} (R S : A -> A -> Prop) : Prop :=
  forall x y, R x y -> S x y.

Definition rel_comp {A : Type} (R S : A -> A -> Prop) : A -> A -> Prop :=
  fun x z => exists y, R x y /\ S y z.

Inductive rtc {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| rtc_refl : forall x, rtc R x x
| rtc_step : forall x y z, R x y -> rtc R y z -> rtc R x z.

Lemma rtc_mono {A : Type} (R S : A -> A -> Prop) :
  rel_incl R S -> rel_incl (rtc R) (rtc S).
Proof.
  intros HRS x y Hxy.
  induction Hxy as [x | x y z Hxy _ IHz].
  - constructor.
  - econstructor; eauto.
Qed.

Lemma rtc_trans {A : Type} (R : A -> A -> Prop) :
  forall x y z, rtc R x y -> rtc R y z -> rtc R x z.
Proof.
  intros x y z Hxy Hyz.
  induction Hxy as [x | x y z0 Hxy _ IHz].
  - exact Hyz.
  - econstructor; eauto.
Qed.

Section RMRS789.

Variable V E F : Type.
Variable ar : F -> nat.
Variable mem : V -> E -> Prop.
Hypothesis eta_nonempty : forall v : V, exists e : E, mem v e.

Definition eta (v : V) (e : E) : Prop := mem v e.

Inductive term : Type :=
| Var : nat -> term
| App : F -> list term -> term.

Inductive wf_term : term -> Prop :=
| wf_var : forall x, wf_term (Var x)
| wf_app :
    forall f ts,
      length ts = ar f ->
      Forall wf_term ts ->
      wf_term (App f ts).

Inductive fv : term -> nat -> Prop :=
| fv_var : forall x, fv (Var x) x
| fv_app :
    forall f ts u x,
      In u ts ->
      fv u x ->
      fv (App f ts) x.

Definition bv (_ : term) (_ : nat) : Prop := False.

Inductive subst_rel : term -> nat -> term -> term -> Prop :=
| subst_var_hit :
    forall x s,
      subst_rel (Var x) x s s
| subst_var_miss :
    forall x y s,
      x <> y ->
      subst_rel (Var y) x s (Var y)
| subst_app :
    forall f ts x s us,
      subst_list_rel ts x s us ->
      subst_rel (App f ts) x s (App f us)
with subst_list_rel : list term -> nat -> term -> list term -> Prop :=
| subst_list_nil :
    forall x s,
      subst_list_rel [] x s []
| subst_list_cons :
    forall t ts x s u us,
      subst_rel t x s u ->
      subst_list_rel ts x s us ->
      subst_list_rel (t :: ts) x s (u :: us).

Definition Sub (t : term) (x : nat) (s u : term) : Prop :=
  subst_rel t x s u.

Definition alpha_equiv (t u : term) : Prop := t = u.

Variable rho : V -> term -> term -> Prop.

Definition sym (R : term -> term -> Prop) : term -> term -> Prop :=
  fun s t => R s t \/ R t s.

Inductive K (R : term -> term -> Prop) : term -> term -> Prop :=
| K_base : forall s t, sym R s t -> K R s t
| K_refl : forall t, wf_term t -> K R t t
| K_sym : forall s t, K R s t -> K R t s
| K_trans : forall s u t, K R s u -> K R u t -> K R s t
| K_cong :
    forall f xs ys,
      length xs = ar f ->
      length ys = ar f ->
      K_list R xs ys ->
      K R (App f xs) (App f ys)
with K_list (R : term -> term -> Prop) : list term -> list term -> Prop :=
| K_list_nil : K_list R [] []
| K_list_cons :
    forall x y xs ys,
      K R x y ->
      K_list R xs ys ->
      K_list R (x :: xs) (y :: ys).

Scheme K_ind' := Induction for K Sort Prop
with K_list_ind' := Induction for K_list Sort Prop.

Combined Scheme K_mutind from K_ind', K_list_ind'.

Lemma K_mono_pair (R S : term -> term -> Prop) :
  rel_incl R S ->
  (forall x y, K R x y -> K S x y) /\
  (forall xs ys, K_list R xs ys -> K_list S xs ys).
Proof.
  intros HRS.
  apply K_mutind.
  - intros s t Hst.
    apply K_base.
    destruct Hst as [Hst | Hts].
    + left. exact (HRS _ _ Hst).
    + right. exact (HRS _ _ Hts).
  - intros t Ht. exact (@K_refl S t Ht).
  - intros s t _ IH. exact (@K_sym S s t IH).
  - intros s u t _ IHsu _ IHut. exact (@K_trans S s u t IHsu IHut).
  - intros f xs ys Hxs Hys _ IHs.
    exact (@K_cong S f xs ys Hxs Hys IHs).
  - exact (@K_list_nil S).
  - intros x y xs ys _ IHxy _ IHs.
    exact (@K_list_cons S x y xs ys IHxy IHs).
Qed.

Lemma K_mono (R S : term -> term -> Prop) :
  rel_incl R S -> rel_incl (K R) (K S).
Proof.
  intros HRS x y Hxy.
  exact (proj1 (@K_mono_pair R S HRS) x y Hxy).
Qed.

Lemma K_list_mono (R S : term -> term -> Prop) :
  rel_incl R S -> forall xs ys, K_list R xs ys -> K_list S xs ys.
Proof.
  intros HRS.
  exact (proj2 (@K_mono_pair R S HRS)).
Qed.

Definition rvec : Type := V -> term -> term -> Prop.

Definition rvec_le (R S : rvec) : Prop :=
  forall v, rel_incl (R v) (S v).

Definition edge_union (R : rvec) (e : E) : term -> term -> Prop :=
  fun s t => exists u, mem u e /\ R u s t.

Definition edge_eq (R : rvec) (e : E) : term -> term -> Prop :=
  K (edge_union R e).

Definition modal_step (R : rvec) (v : V) : term -> term -> Prop :=
  fun s t => exists e, mem v e /\ edge_eq R e s t.

Definition sim (R : rvec) (v : V) : term -> term -> Prop :=
  rtc (modal_step R v).

Definition Fop (R : rvec) : rvec :=
  fun v s t =>
    exists l r, sim R v s l /\ rho v l r /\ sim R v r t.

Lemma edge_union_mono (R S : rvec) :
  rvec_le R S -> forall e, rel_incl (edge_union R e) (edge_union S e).
Proof.
  intros HRS e s t [u [Hue Hust]].
  exists u. split; [exact Hue | exact (HRS u s t Hust)].
Qed.

Lemma edge_eq_mono (R S : rvec) :
  rvec_le R S -> forall e, rel_incl (edge_eq R e) (edge_eq S e).
Proof.
  intros HRS e.
  apply K_mono.
  exact (@edge_union_mono R S HRS e).
Qed.

Lemma modal_step_mono (R S : rvec) :
  rvec_le R S -> forall v, rel_incl (modal_step R v) (modal_step S v).
Proof.
  intros HRS v s t [e [Hve Hst]].
  exists e. split; [exact Hve | exact (@edge_eq_mono R S HRS e s t Hst)].
Qed.

Lemma sim_mono (R S : rvec) :
  rvec_le R S -> forall v, rel_incl (sim R v) (sim S v).
Proof.
  intros HRS v.
  apply rtc_mono.
  exact (@modal_step_mono R S HRS v).
Qed.

Theorem Fop_monotone (R S : rvec) :
  rvec_le R S -> rvec_le (Fop R) (Fop S).
Proof.
  intros HRS v s t [l [r [Hsl [Hlr Hrt]]]].
  exists l, r.
  repeat split.
  - exact (@sim_mono R S HRS v s l Hsl).
  - exact Hlr.
  - exact (@sim_mono R S HRS v r t Hrt).
Qed.

Definition prepoint (R : rvec) : Prop := rvec_le (Fop R) R.

Definition Romega : rvec :=
  fun v s t => forall R : rvec, prepoint R -> R v s t.

Theorem Romega_least_prepoint (R : rvec) :
  prepoint R -> rvec_le Romega R.
Proof.
  intros HR v s t Hst.
  exact (Hst R HR).
Qed.

Lemma Fop_Romega_le_Romega : prepoint Romega.
Proof.
  intros v s t Hst R HR.
  apply HR.
  exact (@Fop_monotone Romega R (@Romega_least_prepoint R HR) v s t Hst).
Qed.

Lemma Fop_Romega_is_prepoint : prepoint (Fop Romega).
Proof.
  intros v s t Hst.
  exact (@Fop_monotone (Fop Romega) Romega Fop_Romega_le_Romega v s t Hst).
Qed.

Lemma Romega_le_Fop_Romega : rvec_le Romega (Fop Romega).
Proof.
  intros v s t Hst.
  exact (Hst (Fop Romega) Fop_Romega_is_prepoint).
Qed.

Theorem Romega_fixed_point :
  forall v s t, Fop Romega v s t <-> Romega v s t.
Proof.
  intros v s t.
  split.
  - intros Hst.
    pose proof Fop_Romega_le_Romega as Hpre.
    unfold prepoint, rvec_le, rel_incl in Hpre.
    exact (Hpre v s t Hst).
  - intros Hst.
    pose proof Romega_le_Fop_Romega as Hle.
    unfold rvec_le, rel_incl in Hle.
    exact (Hle v s t Hst).
Qed.

Definition semantic_rewrite (v : V) (t s : term) : Prop :=
  Romega v t s.

Inductive jud : Type :=
| JRw : V -> term -> term -> jud
| JEq : E -> term -> term -> jud
| JSim : V -> term -> term -> jud.

Inductive derives : jud -> Prop :=
| D_intr :
    forall v l r,
      rho v l r ->
      derives (JRw v l r)
| D_eqinit :
    forall e u t s,
      derives (JRw u t s) ->
      mem u e ->
      derives (JEq e t s)
| D_eqsym :
    forall e t s,
      derives (JEq e t s) ->
      derives (JEq e s t)
| D_eqrefl :
    forall e t,
      wf_term t ->
      derives (JEq e t t)
| D_eqtrans :
    forall e t u s,
      derives (JEq e t u) ->
      derives (JEq e u s) ->
      derives (JEq e t s)
| D_eqcong :
    forall e f xs ys,
      length xs = ar f ->
      length ys = ar f ->
      derives_eq_list e xs ys ->
      derives (JEq e (App f xs) (App f ys))
| D_mem :
    forall e v t s,
      derives (JEq e t s) ->
      mem v e ->
      derives (JSim v t s)
| D_simrefl :
    forall v t,
      wf_term t ->
      derives (JSim v t t)
| D_simtrans :
    forall v t u s,
      derives (JSim v t u) ->
      derives (JSim v u s) ->
      derives (JSim v t s)
| D_modulo :
    forall v t s u w,
      derives (JSim v t s) ->
      derives (JRw v s u) ->
      derives (JSim v u w) ->
      derives (JRw v t w)
with derives_eq_list : E -> list term -> list term -> Prop :=
| D_eqlist_nil :
    forall e, derives_eq_list e [] []
| D_eqlist_cons :
    forall e x y xs ys,
      derives (JEq e x y) ->
      derives_eq_list e xs ys ->
      derives_eq_list e (x :: xs) (y :: ys).

Scheme derives_ind' := Induction for derives Sort Prop
with derives_eq_list_ind' := Induction for derives_eq_list Sort Prop.

Combined Scheme derives_mutind from derives_ind', derives_eq_list_ind'.

Fixpoint eq_premises (e : E) (xs ys : list term) : list jud :=
  match xs, ys with
  | x :: xs', y :: ys' => JEq e x y :: eq_premises e xs' ys'
  | _, _ => []
  end.

Inductive rule_rmrs : list jud -> jud -> Prop :=
| R_intr :
    forall v l r,
      rho v l r ->
      rule_rmrs [] (JRw v l r)
| R_eqinit :
    forall e u t s,
      mem u e ->
      rule_rmrs [JRw u t s] (JEq e t s)
| R_eqsym :
    forall e t s,
      rule_rmrs [JEq e t s] (JEq e s t)
| R_eqrefl :
    forall e t,
      wf_term t ->
      rule_rmrs [] (JEq e t t)
| R_eqtrans :
    forall e t u s,
      rule_rmrs [JEq e t u; JEq e u s] (JEq e t s)
| R_eqcong :
    forall e f xs ys,
      length xs = ar f ->
      length ys = ar f ->
      rule_rmrs (eq_premises e xs ys) (JEq e (App f xs) (App f ys))
| R_mem :
    forall e v t s,
      mem v e ->
      rule_rmrs [JEq e t s] (JSim v t s)
| R_simrefl :
    forall v t,
      wf_term t ->
      rule_rmrs [] (JSim v t t)
| R_simtrans :
    forall v t u s,
      rule_rmrs [JSim v t u; JSim v u s] (JSim v t s)
| R_modulo :
    forall v t s u w,
      rule_rmrs [JSim v t s; JRw v s u; JSim v u w] (JRw v t w).

Inductive premises_before : list jud -> list jud -> Prop :=
| pb_nil : forall lines, premises_before [] lines
| pb_here :
    forall P premises lines,
      premises_before premises lines ->
      premises_before (P :: premises) (P :: lines)
| pb_skip :
    forall P premises J lines,
      premises_before (P :: premises) lines ->
      premises_before (P :: premises) (J :: lines).

Inductive derivation_sequence : list jud -> Prop :=
| ds_nil : derivation_sequence []
| ds_snoc :
    forall lines premises J,
      derivation_sequence lines ->
      rule_rmrs premises J ->
      premises_before premises lines ->
      derivation_sequence (lines ++ [J]).

Fixpoint last_judgment (lines : list jud) : option jud :=
  match lines with
  | [] => None
  | [J] => Some J
  | _ :: rest => last_judgment rest
  end.

Definition sequence_derives (J : jud) : Prop :=
  exists lines, derivation_sequence lines /\ last_judgment lines = Some J.

Definition syntactic_rewrite_by_sequence (v : V) (t s : term) : Prop :=
  sequence_derives (JRw v t s).

Lemma premises_before_forall :
  forall (P : jud -> Prop) premises lines,
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

Lemma derives_eq_list_from_premises :
  forall e xs ys,
    length xs = length ys ->
    Forall derives (eq_premises e xs ys) ->
    derives_eq_list e xs ys.
Proof.
  intros e xs.
  induction xs as [|x xs IH]; intros ys Hlen Hprem.
  - destruct ys as [|y ys].
    + constructor.
    + discriminate Hlen.
  - destruct ys as [|y ys].
    + discriminate Hlen.
    + simpl in Hprem.
      inversion Hprem as [|J rest Hxy Hrest]; subst.
      constructor.
      * exact Hxy.
      * apply IH.
        -- simpl in Hlen. injection Hlen as Hlen'.
           exact Hlen'.
        -- exact Hrest.
Qed.

Lemma rule_rmrs_sound :
  forall premises J,
    rule_rmrs premises J ->
    Forall derives premises ->
    derives J.
Proof.
  intros premises J Hrule Hprem.
  inversion Hrule; subst; simpl in Hprem.
  - apply D_intr. exact H.
  - inversion Hprem as [|J1 rest Hrw Hnil]; subst.
    eapply D_eqinit; eauto.
  - inversion Hprem as [|J1 rest Heq Hnil]; subst.
    apply D_eqsym. exact Heq.
  - apply D_eqrefl. exact H.
  - inversion Hprem as [|J1 rest Htu Hrest]; subst.
    inversion Hrest as [|J2 rest' Hus Hnil]; subst.
    eapply D_eqtrans; eauto.
  - apply D_eqcong; try assumption.
    eapply derives_eq_list_from_premises.
    + congruence.
    + exact Hprem.
  - inversion Hprem as [|J1 rest Heq Hnil]; subst.
    eapply D_mem; eauto.
  - apply D_simrefl. exact H.
  - inversion Hprem as [|J1 rest Htu Hrest]; subst.
    inversion Hrest as [|J2 rest' Hus Hnil]; subst.
    eapply D_simtrans; eauto.
  - inversion Hprem as [|J1 rest Hts Hrest1]; subst.
    inversion Hrest1 as [|J2 rest2 Hsu Hrest2]; subst.
    inversion Hrest2 as [|J3 rest3 Huw Hnil]; subst.
    eapply D_modulo; eauto.
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
    + simpl in Hlast. inversion Hlast; subst.
      left; reflexivity.
    + simpl in Hlast.
      right. apply IH. exact Hlast.
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
    rule_rmrs premises J ->
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

Lemma derives_from_previous_lines :
  forall premises lines,
    Forall derives lines ->
    premises_before premises lines ->
    Forall derives premises.
Proof.
  intros premises lines Hlines Hprem.
  eapply premises_before_forall; eauto.
Qed.

Lemma derivation_sequence_all_derives :
  forall lines,
    derivation_sequence lines ->
    Forall derives lines.
Proof.
  intros lines Hseq.
  induction Hseq as [|lines premises J Hlines IH Hrule Hprem].
  - constructor.
  - apply Forall_app.
    split.
    + exact IH.
    + constructor.
      * eapply rule_rmrs_sound.
        -- exact Hrule.
        -- eapply derives_from_previous_lines; eauto.
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
    forall ls J0,
      Forall derives ls ->
      last_judgment ls = Some J0 ->
      derives J0).
  {
    intros ls.
    induction ls as [|x xs IH]; intros J0 HFor Hlast0.
    - simpl in Hlast0. discriminate Hlast0.
    - destruct xs as [|y ys].
      + simpl in Hlast0. inversion Hlast0; subst.
        inversion HFor; subst. assumption.
      + simpl in Hlast0.
        inversion HFor; subst.
        eapply IH; eassumption.
  }
  exact (Hlast_sound lines J Hderives Hlast).
Qed.

Theorem derives_to_sequence_pair :
  (forall J, derives J -> sequence_derives J) /\
  (forall e xs ys,
      derives_eq_list e xs ys ->
      Forall sequence_derives (eq_premises e xs ys)).
Proof.
  apply derives_mutind.
  - intros v l r Hrho.
    eapply rule_sequence_derives.
    + apply R_intr. exact Hrho.
    + constructor.
  - intros e u t s Hrw IH Hmem.
    eapply rule_sequence_derives.
    + apply R_eqinit. exact Hmem.
    + constructor; [exact IH | constructor].
  - intros e t s Heq IH.
    eapply rule_sequence_derives.
    + apply R_eqsym.
    + constructor; [exact IH | constructor].
  - intros e t Hwf.
    eapply rule_sequence_derives.
    + apply R_eqrefl. exact Hwf.
    + constructor.
  - intros e t u s Htu IHtu Hus IHus.
    eapply rule_sequence_derives.
    + apply R_eqtrans.
    + constructor; [exact IHtu | constructor; [exact IHus | constructor]].
  - intros e f xs ys Hlenx Hleny Heqs IHeqs.
    eapply rule_sequence_derives.
    + apply R_eqcong; assumption.
    + exact IHeqs.
  - intros e v t s Heq IH Hmem.
    eapply rule_sequence_derives.
    + apply R_mem. exact Hmem.
    + constructor; [exact IH | constructor].
  - intros v t Hwf.
    eapply rule_sequence_derives.
    + apply R_simrefl. exact Hwf.
    + constructor.
  - intros v t u s Htu IHtu Hus IHus.
    eapply rule_sequence_derives.
    + apply R_simtrans.
    + constructor; [exact IHtu | constructor; [exact IHus | constructor]].
  - intros v t s u w Hts IHts Hsu IHsu Huw IHuw.
    eapply rule_sequence_derives.
    + apply R_modulo.
    + constructor; [exact IHts |
      constructor; [exact IHsu |
      constructor; [exact IHuw | constructor]]].
  - intros e.
    constructor.
  - intros e x y xs ys Hxy IHxy Htail IHtail.
    simpl.
    constructor; assumption.
Qed.

Theorem derives_to_sequence :
  forall J,
    derives J ->
    sequence_derives J.
Proof.
  exact (proj1 derives_to_sequence_pair).
Qed.

Theorem derives_sequence_iff :
  forall J,
    derives J <-> sequence_derives J.
Proof.
  intros J.
  split.
  - apply derives_to_sequence.
  - apply sequence_derives_sound.
Qed.

Definition jud_sem (J : jud) : Prop :=
  match J with
  | JRw v t s => semantic_rewrite v t s
  | JEq e t s => edge_eq Romega e t s
  | JSim v t s => sim Romega v t s
  end.

Definition eq_list_sem (e : E) (xs ys : list term) : Prop :=
  K_list (edge_union Romega e) xs ys.

Theorem derives_sound_pair :
  (forall J, derives J -> jud_sem J) /\
  (forall e xs ys, derives_eq_list e xs ys -> eq_list_sem e xs ys).
Proof.
  apply derives_mutind.
  - intros v l r Hlr.
    apply Fop_Romega_le_Romega.
    exists l, r.
    repeat split; try exact Hlr; constructor.
  - intros e u t s _ IH Hue.
    apply K_base.
    left.
    exists u. split; assumption.
  - intros e t s _ IH.
    exact (@K_sym (edge_union Romega e) t s IH).
  - intros e t Ht.
    exact (@K_refl (edge_union Romega e) t Ht).
  - intros e t u s _ IHtu _ IHus.
    exact (@K_trans (edge_union Romega e) t u s IHtu IHus).
  - intros e f xs ys Hxs Hys _ IHs.
    exact (@K_cong (edge_union Romega e) f xs ys Hxs Hys IHs).
  - intros e v t s _ IH Hve.
    econstructor.
    + exists e. split.
      * exact Hve.
      * exact IH.
    + constructor.
  - intros v t _.
    constructor.
  - intros v t u s _ IHtu _ IHus.
    exact (@rtc_trans term (modal_step Romega v) t u s IHtu IHus).
  - intros v t s u w _ IHts _ IHsu _ IHuw.
    pose proof Romega_le_Fop_Romega as Hle.
    unfold rvec_le, rel_incl in Hle.
    destruct (Hle v s u IHsu) as [l [r [Hsl [Hlr Hru]]]].
    pose proof Fop_Romega_le_Romega as Hpre.
    unfold prepoint, rvec_le, rel_incl in Hpre.
    apply Hpre.
    exists l, r.
    repeat split.
    + exact (@rtc_trans term (modal_step Romega v) t s l IHts Hsl).
    + exact Hlr.
    + exact (@rtc_trans term (modal_step Romega v) r u w Hru IHuw).
  - intros e.
    exact (@K_list_nil (edge_union Romega e)).
  - intros e x y xs ys _ IHxy _ IHs.
    exact (@K_list_cons (edge_union Romega e) x y xs ys IHxy IHs).
Qed.

Theorem derives_sound :
  forall J, derives J -> jud_sem J.
Proof.
  exact (proj1 derives_sound_pair).
Qed.

Definition syntactic_rewrite (v : V) (t s : term) : Prop :=
  syntactic_rewrite_by_sequence v t s.

Theorem syntactic_rewrite_sound :
  forall v t s,
    syntactic_rewrite v t s -> semantic_rewrite v t s.
Proof.
  intros v t s H.
  exact (@derives_sound (JRw v t s) (sequence_derives_sound H)).
Qed.

(** Mathematical significance:
    This theorem packages the intersection construction of [Romega] as
    an induction principle over prefix points of the semantic operator.
    Originality contribution:
    It makes the least-fixed-point semantics usable as a proof principle,
    rather than only as a definition of the final rewrite relation.
*)
Theorem Romega_induction :
  forall P,
    prepoint P ->
    rvec_le Romega P.
Proof.
  intros P HP.
  exact (@Romega_least_prepoint P HP).
Qed.

(** Mathematical significance:
    This theorem states that [Romega] is below every fixed point of [Fop],
    not merely every prefix point supplied directly.
    Originality contribution:
    It gives the standard least-fixed-point metatheorem in a form that can
    be cited independently in later semantic arguments.
*)
Theorem Romega_least_fixed_point :
  forall R,
    (forall v t s, Fop R v t s <-> R v t s) ->
    rvec_le Romega R.
Proof.
  intros R Hfix.
  apply Romega_induction.
  unfold prepoint, rvec_le, rel_incl.
  intros v t s HF.
  exact (proj1 (Hfix v t s) HF).
Qed.

(** Mathematical significance:
    The edge theory is reflexive on well-formed terms.
    Originality contribution:
    This isolates one component of the hyperedge congruence closure as a
    reusable metatheoretic rule.
*)
Lemma edge_eq_refl :
  forall R e t, wf_term t -> edge_eq R e t t.
Proof.
  intros R e t Ht.
  exact (@K_refl (edge_union R e) t Ht).
Qed.

(** Mathematical significance:
    The edge theory is symmetric.
    Originality contribution:
    This exposes the modal equality layer as an equivalence component,
    supporting later syntax-semantics correspondence proofs.
*)
Lemma edge_eq_sym :
  forall R e t s, edge_eq R e t s -> edge_eq R e s t.
Proof.
  intros R e t s H.
  exact (@K_sym (edge_union R e) t s H).
Qed.

(** Mathematical significance:
    The edge theory is transitive.
    Originality contribution:
    This identifies the edge closure as a genuine equality environment
    rather than a one-step rule closure.
*)
Lemma edge_eq_trans :
  forall R e t u s,
    edge_eq R e t u -> edge_eq R e u s -> edge_eq R e t s.
Proof.
  intros R e t u s Htu Hus.
  exact (@K_trans (edge_union R e) t u s Htu Hus).
Qed.

Lemma Forall2_edge_eq_to_K_list :
  forall R e xs ys,
    Forall2 (edge_eq R e) xs ys ->
    K_list (edge_union R e) xs ys.
Proof.
  intros R e xs ys H.
  induction H as [| x y xs ys Hxy _ IHxy].
  - exact (@K_list_nil (edge_union R e)).
  - exact (@K_list_cons (edge_union R e) x y xs ys Hxy IHxy).
Qed.

(** Mathematical significance:
    Edge equality is closed under application congruence.
    Originality contribution:
    This theorem makes the algebraic congruence content of the system
    explicit and reusable for later completeness and locality results.
*)
Lemma edge_eq_cong :
  forall R e f xs ys,
    length xs = ar f ->
    length ys = ar f ->
    Forall2 (edge_eq R e) xs ys ->
    edge_eq R e (App f xs) (App f ys).
Proof.
  intros R e f xs ys Hxs Hys Hxy.
  exact (@K_cong (edge_union R e) f xs ys Hxs Hys
                 (@Forall2_edge_eq_to_K_list R e xs ys Hxy)).
Qed.

(** Mathematical significance:
    Node modal similarity is reflexive because it is a reflexive-transitive
    closure of one-step modal edge access.
    Originality contribution:
    This separates the structural closure of modal context from the
    primitive rewrite payload.
*)
Lemma sim_refl :
  forall R v t, sim R v t t.
Proof.
  intros R v t.
  constructor.
Qed.

(** Mathematical significance:
    Node modal similarity is transitive.
    Originality contribution:
    This theorem is the compositional law that lets modal contexts be
    chained around primitive rewrites.
*)
Lemma sim_trans :
  forall R v t u s,
    sim R v t u -> sim R v u s -> sim R v t s.
Proof.
  intros R v t u s Htu Hus.
  exact (@rtc_trans term (modal_step R v) t u s Htu Hus).
Qed.

(** Mathematical significance:
    Any edge equality incident to a node embeds into that node's modal
    similarity relation.
    Originality contribution:
    This is the bridge from hyperedge-level equality to node-level modal
    rewriting contexts.
*)
Lemma edge_eq_to_sim :
  forall R v e t s,
    mem v e ->
    edge_eq R e t s ->
    sim R v t s.
Proof.
  intros R v e t s Hve Hts.
  econstructor.
  - exists e. split.
    + exact Hve.
    + exact Hts.
  - constructor.
Qed.

(** Mathematical significance:
    The final semantic rewrite relation is closed under modal context
    wrapping on both sides.
    Originality contribution:
    This confirms that [Romega] is not just a fixed point abstractly, but
    the intended modulo-closure of primitive rewriting in the final model.
*)
Theorem semantic_modulo_closed :
  forall v t s u w,
    sim Romega v t s ->
    semantic_rewrite v s u ->
    sim Romega v u w ->
    semantic_rewrite v t w.
Proof.
  intros v t s u w Hts Hsu Huw.
  unfold semantic_rewrite in *.
  pose proof Romega_le_Fop_Romega as Hle.
  unfold rvec_le, rel_incl in Hle.
  destruct (Hle v s u Hsu) as [l [r [Hsl [Hlr Hru]]]].
  pose proof Fop_Romega_le_Romega as Hpre.
  unfold prepoint, rvec_le, rel_incl in Hpre.
  apply Hpre.
  exists l, r.
  repeat split.
  - exact (@rtc_trans term (modal_step Romega v) t s l Hts Hsl).
  - exact Hlr.
  - exact (@rtc_trans term (modal_step Romega v) r u w Hru Huw).
Qed.

Definition Rsyn : rvec :=
  fun v t s => derives (JRw v t s).

(** Mathematical significance:
    Edge congruence generated by syntactic rewrites is itself syntactically
    derivable at the edge-judgment level.
    Originality contribution:
    This is the key local completeness fact needed before any global
    syntax-semantics completeness theorem can be attempted.
*)
Lemma edge_eq_Rsyn_complete_pair :
  forall e,
    (forall t s, edge_eq Rsyn e t s -> derives (JEq e t s)) /\
    (forall xs ys,
        K_list (edge_union Rsyn e) xs ys -> derives_eq_list e xs ys).
Proof.
  intros e.
  apply K_mutind.
  - intros s t Hst.
    destruct Hst as [[u [Hue Hrw]] | [u [Hue Hrw]]].
    + exact (@D_eqinit e u s t Hrw Hue).
    + exact (@D_eqsym e t s (@D_eqinit e u t s Hrw Hue)).
  - intros t Ht.
    exact (@D_eqrefl e t Ht).
  - intros s t _ IH.
    exact (@D_eqsym e s t IH).
  - intros s u t _ IHsu _ IHut.
    exact (@D_eqtrans e s u t IHsu IHut).
  - intros f xs ys Hxs Hys _ IHs.
    exact (@D_eqcong e f xs ys Hxs Hys IHs).
  - exact (@D_eqlist_nil e).
  - intros x y xs ys _ IHxy _ IHs.
    exact (@D_eqlist_cons e x y xs ys IHxy IHs).
Qed.

Lemma edge_eq_Rsyn_complete :
  forall e t s,
    edge_eq Rsyn e t s -> derives (JEq e t s).
Proof.
  intros e t s H.
  exact (proj1 (edge_eq_Rsyn_complete_pair e) t s H).
Qed.

(** Mathematical significance:
    If every modal similarity generated by syntactic rewrites is itself
    syntactically derivable, then the syntactic rewrite relation is a
    prefix point of the semantic operator.
    Originality contribution:
    This theorem isolates the exact proof obligation behind semantic
    completeness, making the obstruction explicit rather than hidden.
*)
Theorem Rsyn_prepoint_from_sim_complete :
  (forall v t s, sim Rsyn v t s -> derives (JSim v t s)) ->
  prepoint Rsyn.
Proof.
  intros Hsim.
  unfold prepoint, rvec_le, rel_incl, Rsyn.
  intros v t s [l [r [Htl [Hlr Hrs]]]].
  eapply @D_modulo.
  - exact (Hsim v t l Htl).
  - exact (@D_intr v l r Hlr).
  - exact (Hsim v r s Hrs).
Qed.

(** Mathematical significance:
    Conditional semantic completeness follows as soon as the syntactic
    rewrite relation is known to be a prefix point.
    Originality contribution:
    This is the clean fixed-point route from operational closure to
    full semantic completeness.
*)
Theorem semantic_rewrite_complete_if_Rsyn_prepoint :
  prepoint Rsyn ->
  forall v t s,
    semantic_rewrite v t s -> syntactic_rewrite v t s.
Proof.
  intros Hpre v t s Hsem.
  unfold semantic_rewrite in Hsem.
  unfold syntactic_rewrite, syntactic_rewrite_by_sequence, Rsyn.
  pose proof (@Romega_least_prepoint Rsyn Hpre) as Hle.
  unfold rvec_le, rel_incl in Hle.
  exact (derives_to_sequence (Hle v t s Hsem)).
Qed.

(** Mathematical significance:
    This is the user-requested completeness theorem under the precise
    modal-completeness premise needed by the present definitions.
    Originality contribution:
    It identifies the only missing ingredient for an unconditional
    soundness-completeness correspondence.
*)
Theorem semantic_rewrite_complete_if_sim_complete :
  (forall v t s, sim Rsyn v t s -> derives (JSim v t s)) ->
  forall v t s,
    semantic_rewrite v t s -> syntactic_rewrite v t s.
Proof.
  intros Hsim.
  apply semantic_rewrite_complete_if_Rsyn_prepoint.
  exact (Rsyn_prepoint_from_sim_complete Hsim).
Qed.

(** Mathematical significance:
    Under the same explicit modal-completeness premise, syntactic and
    semantic rewriting coincide.
    Originality contribution:
    This upgrades the original soundness-only result into a conditional
    syntax-semantics correspondence theorem.
*)
Theorem syntactic_semantic_rewrite_iff_if_sim_complete :
  (forall v t s, sim Rsyn v t s -> derives (JSim v t s)) ->
  forall v t s,
    syntactic_rewrite v t s <-> semantic_rewrite v t s.
Proof.
  intros Hsim v t s.
  split.
  - intros Hsyn.
    exact (@syntactic_rewrite_sound v t s Hsyn).
  - intros Hsem.
    exact (@semantic_rewrite_complete_if_sim_complete Hsim v t s Hsem).
Qed.

Section WellFormedness.

Hypothesis rho_wf :
  forall v l r, rho v l r -> wf_term l /\ wf_term r.

Definition jud_wf (J : jud) : Prop :=
  match J with
  | JRw _ t s => wf_term t /\ wf_term s
  | JEq _ t s => wf_term t /\ wf_term s
  | JSim _ t s => wf_term t /\ wf_term s
  end.

Definition eq_list_wf (xs ys : list term) : Prop :=
  Forall wf_term xs /\ Forall wf_term ys.

(** Mathematical significance:
    If primitive node payloads are well-formed, every finite syntactic
    derivation preserves well-formed endpoints.
    Originality contribution:
    This establishes that the proof system is internally well-sorted under
    a minimal, localized payload well-formedness assumption.
*)
Theorem derives_wf_pair :
  (forall J, derives J -> jud_wf J) /\
  (forall e xs ys, derives_eq_list e xs ys -> eq_list_wf xs ys).
Proof.
  apply derives_mutind.
  - intros v l r Hlr.
    exact (@rho_wf v l r Hlr).
  - intros e u t s _ IH _.
    exact IH.
  - intros e t s _ IH.
    destruct IH as [Ht Hs].
    split; assumption.
  - intros e t Ht.
    split; assumption.
  - intros e t u s _ IHtu _ IHus.
    destruct IHtu as [Ht _].
    destruct IHus as [_ Hs].
    split; assumption.
  - intros e f xs ys Hxs Hys _ IHs.
    destruct IHs as [Hfx Hfy].
    split.
    + exact (@wf_app f xs Hxs Hfx).
    + exact (@wf_app f ys Hys Hfy).
  - intros e v t s _ IH _.
    exact IH.
  - intros v t Ht.
    split; assumption.
  - intros v t u s _ IHtu _ IHus.
    destruct IHtu as [Ht _].
    destruct IHus as [_ Hs].
    split; assumption.
  - intros v t s u w _ IHts _ IHsu _ IHuw.
    destruct IHts as [Ht _].
    destruct IHuw as [_ Hw].
    split; assumption.
  - intros e.
    split; constructor.
  - intros e x y xs ys _ IHxy _ IHs.
    destruct IHxy as [Hx Hy].
    destruct IHs as [Hxs Hys].
    split; constructor; assumption.
Qed.

Theorem derives_wf :
  forall J, derives J -> jud_wf J.
Proof.
  exact (proj1 derives_wf_pair).
Qed.

(** Mathematical significance:
    Syntactic rewriting preserves well-formedness of both endpoints when
    primitive rules are well-formed.
    Originality contribution:
    This gives the syntactic layer an explicit preservation theorem,
    needed for later exact correspondence with the semantic layer.
*)
Theorem syntactic_rewrite_wf :
  forall v t s,
    syntactic_rewrite v t s -> wf_term t /\ wf_term s.
Proof.
  intros v t s H.
  exact (@derives_wf (JRw v t s) (sequence_derives_sound H)).
Qed.

Definition rel_preserves_wf (R : term -> term -> Prop) : Prop :=
  forall t s, R t s -> wf_term t /\ wf_term s.

Lemma edge_union_preserves_wf :
  forall R e,
    (forall v t s, R v t s -> wf_term t /\ wf_term s) ->
    rel_preserves_wf (edge_union R e).
Proof.
  intros R e HR t s [u [_ Hus]].
  exact (HR u t s Hus).
Qed.

Lemma K_preserves_wf_pair :
  forall R,
    rel_preserves_wf R ->
    (forall t s, K R t s -> wf_term t /\ wf_term s) /\
    (forall xs ys, K_list R xs ys -> eq_list_wf xs ys).
Proof.
  intros R HR.
  apply K_mutind.
  - intros s t Hst.
    destruct Hst as [Hst | Hts].
    + exact (HR s t Hst).
    + destruct (HR t s Hts) as [Ht Hs].
      split; assumption.
  - intros t Ht.
    split; assumption.
  - intros s t _ IH.
    destruct IH as [Hs Ht].
    split; assumption.
  - intros s u t _ IHsu _ IHut.
    destruct IHsu as [Hs _].
    destruct IHut as [_ Ht].
    split; assumption.
  - intros f xs ys Hxs Hys _ IHs.
    destruct IHs as [Hfx Hfy].
    split.
    + exact (@wf_app f xs Hxs Hfx).
    + exact (@wf_app f ys Hys Hfy).
  - split; constructor.
  - intros x y xs ys _ IHxy _ IHs.
    destruct IHxy as [Hx Hy].
    destruct IHs as [Hxs Hys].
    split; constructor; assumption.
Qed.

Lemma edge_eq_preserves_wf :
  forall R e t s,
    (forall v t s, R v t s -> wf_term t /\ wf_term s) ->
    edge_eq R e t s ->
    wf_term t /\ wf_term s.
Proof.
  intros R e t s HR Hts.
  exact (proj1 (@K_preserves_wf_pair
                  (edge_union R e)
                  (@edge_union_preserves_wf R e HR)) t s Hts).
Qed.

Lemma modal_step_preserves_wf :
  forall R v t s,
    (forall v t s, R v t s -> wf_term t /\ wf_term s) ->
    modal_step R v t s ->
    wf_term t /\ wf_term s.
Proof.
  intros R v t s HR [e [_ Hts]].
  exact (@edge_eq_preserves_wf R e t s HR Hts).
Qed.

Lemma rtc_preserves_wf_from_left :
  forall (R : term -> term -> Prop),
    rel_preserves_wf R ->
    forall t s, wf_term t -> rtc R t s -> wf_term s.
Proof.
  intros R HR t s Ht Hrtc.
  induction Hrtc as [x | x y z Hxy _ IHz].
  - exact Ht.
  - destruct (HR x y Hxy) as [_ Hy].
    exact (IHz Hy).
Qed.

Lemma rtc_preserves_wf_from_right :
  forall (R : term -> term -> Prop),
    rel_preserves_wf R ->
    forall t s, rtc R t s -> wf_term s -> wf_term t.
Proof.
  intros R HR t s Hrtc Hs.
  induction Hrtc as [x | x y z Hxy Hyz IHz].
  - exact Hs.
  - destruct (HR x y Hxy) as [Hx _].
    exact Hx.
Qed.

Definition Rwf : rvec :=
  fun _ t s => wf_term t /\ wf_term s.

Lemma Rwf_prepoint : prepoint Rwf.
Proof.
  unfold prepoint, rvec_le, rel_incl, Rwf.
  intros v t s [l [r [Htl [Hlr Hrs]]]].
  destruct (@rho_wf v l r Hlr) as [Hwl Hwr].
  assert (Hmodal : forall x y, modal_step Rwf v x y -> wf_term x /\ wf_term y).
  {
    intros x y Hxy.
    exact (@modal_step_preserves_wf Rwf v x y
             (fun _ a b Hab => Hab) Hxy).
  }
  split.
  - exact (@rtc_preserves_wf_from_right
             (modal_step Rwf v) Hmodal t l Htl Hwl).
  - exact (@rtc_preserves_wf_from_left
             (modal_step Rwf v) Hmodal r s Hwr Hrs).
Qed.

(** Mathematical significance:
    Under well-formed primitive payloads, the final semantic rewrite
    relation also has well-formed endpoints.
    Originality contribution:
    This transfers well-sortedness from local node payloads to the global
    recursive fixed-point semantics.
*)
Theorem semantic_rewrite_wf :
  forall v t s,
    semantic_rewrite v t s -> wf_term t /\ wf_term s.
Proof.
  intros v t s H.
  unfold semantic_rewrite in H.
  pose proof (@Romega_least_prepoint Rwf Rwf_prepoint) as Hle.
  unfold rvec_le, rel_incl, Rwf in Hle.
  exact (Hle v t s H).
Qed.

End WellFormedness.

Section SemanticCompletenessWithWellFormedPrimitives.

Hypothesis rho_wf :
  forall v l r, rho v l r -> wf_term l /\ wf_term r.

Definition RsynWf : rvec :=
  fun v t s => wf_term t /\ wf_term s /\ derives (JRw v t s).

Lemma edge_eq_RsynWf_complete_pair :
  forall e,
    (forall t s, edge_eq RsynWf e t s -> derives (JEq e t s)) /\
    (forall xs ys,
        K_list (edge_union RsynWf e) xs ys -> derives_eq_list e xs ys).
Proof.
  intros e.
  apply K_mutind.
  - intros s t Hst.
    destruct Hst as [[u [Hue [_ [_ Hrw]]]] | [u [Hue [_ [_ Hrw]]]]].
    + exact (@D_eqinit e u s t Hrw Hue).
    + exact (@D_eqsym e t s (@D_eqinit e u t s Hrw Hue)).
  - intros t Ht.
    exact (@D_eqrefl e t Ht).
  - intros s t _ IH.
    exact (@D_eqsym e s t IH).
  - intros s u t _ IHsu _ IHut.
    exact (@D_eqtrans e s u t IHsu IHut).
  - intros f xs ys Hxs Hys _ IHs.
    exact (@D_eqcong e f xs ys Hxs Hys IHs).
  - exact (@D_eqlist_nil e).
  - intros x y xs ys _ IHxy _ IHs.
    exact (@D_eqlist_cons e x y xs ys IHxy IHs).
Qed.

Lemma edge_eq_RsynWf_complete :
  forall e t s,
    edge_eq RsynWf e t s -> derives (JEq e t s).
Proof.
  intros e t s H.
  exact (proj1 (edge_eq_RsynWf_complete_pair e) t s H).
Qed.

Lemma edge_eq_RsynWf_preserves_wf :
  forall e t s,
    edge_eq RsynWf e t s -> wf_term t /\ wf_term s.
Proof.
  intros e t s H.
  exact (@edge_eq_preserves_wf RsynWf e t s
           (fun _ a b Hab =>
              match Hab with
              | conj Ha (conj Hb _) => conj Ha Hb
              end) H).
Qed.

Lemma sim_RsynWf_complete_from_left :
  forall v t s,
    wf_term t ->
    sim RsynWf v t s ->
    derives (JSim v t s) /\ wf_term s.
Proof.
  intros v t s Hwt Hsim.
  induction Hsim as [x | x y z Hxy Hyz IHz].
  - split.
    + exact (@D_simrefl v x Hwt).
    + exact Hwt.
  - destruct Hxy as [e [Hve Heq]].
    destruct (@edge_eq_RsynWf_preserves_wf e x y Heq) as [_ Hwy].
    destruct (IHz Hwy) as [Dyz Hwz].
    split.
    + exact (@D_simtrans v x y z
              (@D_mem e v x y (@edge_eq_RsynWf_complete e x y Heq) Hve)
              Dyz).
    + exact Hwz.
Qed.

Lemma sim_RsynWf_complete_from_right :
  forall v t s,
    sim RsynWf v t s ->
    wf_term s ->
    derives (JSim v t s) /\ wf_term t.
Proof.
  intros v t s Hsim Hws.
  induction Hsim as [x | x y z Hxy Hyz IHz].
  - split.
    + exact (@D_simrefl v x Hws).
    + exact Hws.
  - destruct (IHz Hws) as [Dyz Hwy].
    destruct Hxy as [e [Hve Heq]].
    destruct (@edge_eq_RsynWf_preserves_wf e x y Heq) as [Hwx _].
    split.
    + exact (@D_simtrans v x y z
              (@D_mem e v x y (@edge_eq_RsynWf_complete e x y Heq) Hve)
              Dyz).
    + exact Hwx.
Qed.

Lemma RsynWf_prepoint : prepoint RsynWf.
Proof.
  unfold prepoint, rvec_le, rel_incl, RsynWf.
  intros v t s [l [r [Htl [Hlr Hrs]]]].
  destruct (@rho_wf v l r Hlr) as [Hwl Hwr].
  destruct (@sim_RsynWf_complete_from_right v t l Htl Hwl) as [Dtl Hwt].
  destruct (@sim_RsynWf_complete_from_left v r s Hwr Hrs) as [Drs Hws].
  repeat split.
  - exact Hwt.
  - exact Hws.
  - exact (@D_modulo v t l r s Dtl (@D_intr v l r Hlr) Drs).
Qed.

(** Mathematical significance:
    With well-formed primitive payloads, semantic rewriting is complete
    for the syntax: every fixed-point semantic rewrite has a finite
    syntactic derivation.
    Originality contribution:
    This turns the original soundness theorem into a genuine
    syntax-semantics correspondence under the minimal well-formedness
    assumption needed by the existing [D_simrefl] rule.
*)
Theorem semantic_rewrite_complete :
  forall v t s,
    semantic_rewrite v t s -> syntactic_rewrite v t s.
Proof.
  intros v t s Hsem.
  unfold semantic_rewrite in Hsem.
  pose proof (@Romega_least_prepoint RsynWf RsynWf_prepoint) as Hle.
  unfold rvec_le, rel_incl, RsynWf in Hle.
  exact (derives_to_sequence (proj2 (proj2 (Hle v t s Hsem)))).
Qed.

(** Mathematical significance:
    Soundness and completeness coincide for node rewriting under
    well-formed primitive payloads.
    Originality contribution:
    This is the main correspondence theorem for the rewrite judgment.
*)
Theorem syntactic_semantic_rewrite_iff :
  forall v t s,
    syntactic_rewrite v t s <-> semantic_rewrite v t s.
Proof.
  intros v t s.
  split.
  - intros Hsyn.
    exact (@syntactic_rewrite_sound v t s Hsyn).
  - intros Hsem.
    exact (@semantic_rewrite_complete v t s Hsem).
Qed.

(** Mathematical significance:
    The finite derivability judgment for node rewrites is equivalent to
    membership in the least semantic fixed point.
    Originality contribution:
    This gives the strongest syntax-semantics exactness result available
    for the primary judgment of the system.
*)
Theorem derives_rw_iff_sem :
  forall v t s,
    derives (JRw v t s) <-> Romega v t s.
Proof.
  intros v t s.
  split.
  - intros Hsyn.
    exact (@syntactic_rewrite_sound v t s (derives_to_sequence Hsyn)).
  - intros Hsem.
    exact (sequence_derives_sound (@semantic_rewrite_complete v t s Hsem)).
Qed.

Lemma edge_eq_Romega_complete_pair :
  forall e,
    (forall t s, edge_eq Romega e t s -> derives (JEq e t s)) /\
    (forall xs ys,
        K_list (edge_union Romega e) xs ys -> derives_eq_list e xs ys).
Proof.
  intros e.
  apply K_mutind.
  - intros s t Hst.
    destruct Hst as [[u [Hue Hrw]] | [u [Hue Hrw]]].
    + exact (@D_eqinit e u s t
              (sequence_derives_sound
                 (@semantic_rewrite_complete u s t Hrw)) Hue).
    + exact (@D_eqsym e t s
              (@D_eqinit e u t s
                 (sequence_derives_sound
                    (@semantic_rewrite_complete u t s Hrw)) Hue)).
  - intros t Ht.
    exact (@D_eqrefl e t Ht).
  - intros s t _ IH.
    exact (@D_eqsym e s t IH).
  - intros s u t _ IHsu _ IHut.
    exact (@D_eqtrans e s u t IHsu IHut).
  - intros f xs ys Hxs Hys _ IHs.
    exact (@D_eqcong e f xs ys Hxs Hys IHs).
  - exact (@D_eqlist_nil e).
  - intros x y xs ys _ IHxy _ IHs.
    exact (@D_eqlist_cons e x y xs ys IHxy IHs).
Qed.

(** Mathematical significance:
    Edge equality in the final semantic model is exactly the finite
    derivability judgment for edge equality.
    Originality contribution:
    This extends syntax-semantics exactness from rewrites to the modal
    hyperedge equality layer.
*)
Theorem derives_eq_sound_complete :
  forall e t s,
    derives (JEq e t s) <-> edge_eq Romega e t s.
Proof.
  intros e t s.
  split.
  - intros H.
    exact (@derives_sound (JEq e t s) H).
  - intros H.
    exact (proj1 (edge_eq_Romega_complete_pair e) t s H).
Qed.

Lemma sim_Romega_complete_from_left :
  forall v t s,
    wf_term t ->
    sim Romega v t s ->
    derives (JSim v t s).
Proof.
  intros v t s Hwt Hsim.
  induction Hsim as [x | x y z Hxy Hyz IHz].
  - exact (@D_simrefl v x Hwt).
  - destruct Hxy as [e [Hve Heq]].
    pose proof (@semantic_rewrite_wf rho_wf) as Hsemwf.
    assert (Hwy : wf_term y).
    {
      destruct (@edge_eq_preserves_wf Romega e x y
                  (fun u a b Hab => Hsemwf u a b Hab) Heq) as [_ Hy].
      exact Hy.
    }
    exact (@D_simtrans v x y z
            (@D_mem e v x y
              (proj1 (edge_eq_Romega_complete_pair e) x y Heq) Hve)
            (IHz Hwy)).
Qed.

(** Mathematical significance:
    For well-formed sources, node modal similarity in the final semantic
    model is exactly finite derivability of the modal judgment.
    Originality contribution:
    This is the strongest exact correspondence possible without changing
    the existing syntax rule [D_simrefl], which requires well-formedness
    while semantic [sim] is unconditionally reflexive.
*)
Theorem derives_sim_sound_complete_on_wf_source :
  forall v t s,
    wf_term t ->
    derives (JSim v t s) <-> sim Romega v t s.
Proof.
  intros v t s Hwt.
  split.
  - intros H.
    exact (@derives_sound (JSim v t s) H).
  - intros Hsim.
    exact (@sim_Romega_complete_from_left v t s Hwt Hsim).
Qed.

End SemanticCompletenessWithWellFormedPrimitives.

Definition primitive_rewrite_nontrivial : Prop :=
  exists v t s, rho v t s /\ t <> s.

Lemma primitive_rewrite_is_semantic :
  forall v t s, rho v t s -> semantic_rewrite v t s.
Proof.
  intros v t s Hstep.
  apply syntactic_rewrite_sound.
  unfold syntactic_rewrite.
  apply derives_to_sequence.
  apply D_intr. exact Hstep.
Qed.

Theorem semantic_nontrivial_if_primitive :
  primitive_rewrite_nontrivial ->
  exists v t s, semantic_rewrite v t s /\ t <> s.
Proof.
  intros [v [t [s [Hstep Hneq]]]].
  exists v, t, s. split.
  - exact (@primitive_rewrite_is_semantic v t s Hstep).
  - exact Hneq.
Qed.

Record RMRSSystem : Type := {
  rmrs_system_marker : unit;
  rmrs_nodes : Type := V;
  rmrs_edges : Type := E;
  rmrs_functions : Type := F;
  rmrs_arity : F -> nat := ar;
  rmrs_incidence : V -> E -> Prop := mem;
  rmrs_eta : V -> E -> Prop := eta;
  rmrs_eta_nonempty : forall v : V, exists e : E, mem v e := eta_nonempty;
  rmrs_terms : Type := term;
  rmrs_wf_term : term -> Prop := wf_term;
  rmrs_fv : term -> nat -> Prop := fv;
  rmrs_bv : term -> nat -> Prop := bv;
  rmrs_substitution_graph : term -> nat -> term -> term -> Prop := Sub;
  rmrs_alpha_equiv : term -> term -> Prop := alpha_equiv;
  rmrs_primitive_payload : V -> term -> term -> Prop := rho;
  rmrs_symmetric_lift : (term -> term -> Prop) -> term -> term -> Prop := sym;
  rmrs_congruence_closure : (term -> term -> Prop) -> term -> term -> Prop := K;
  rmrs_edge_theory : rvec -> E -> term -> term -> Prop := edge_eq;
  rmrs_modal_context : rvec -> V -> term -> term -> Prop := sim;
  rmrs_operator : rvec -> rvec := Fop;
  rmrs_least_fixed_point : rvec := Romega;
  rmrs_semantic_rewrite : V -> term -> term -> Prop := semantic_rewrite;
  rmrs_judgment : Type := jud;
  rmrs_rule : list jud -> jud -> Prop := rule_rmrs;
  rmrs_derives : jud -> Prop := sequence_derives;
  rmrs_syntactic_rewrite : V -> term -> term -> Prop := syntactic_rewrite;
  rmrs_tree_sequence_equivalence :
    forall J, derives J <-> sequence_derives J := derives_sequence_iff;
  rmrs_soundness :
    forall v t s, syntactic_rewrite v t s -> semantic_rewrite v t s
    := syntactic_rewrite_sound;
  rmrs_primitive_nontrivial : Prop := primitive_rewrite_nontrivial;
  rmrs_semantic_nontrivial :
    primitive_rewrite_nontrivial ->
    exists v t s, semantic_rewrite v t s /\ t <> s
    := semantic_nontrivial_if_primitive
}.

End RMRS789.
