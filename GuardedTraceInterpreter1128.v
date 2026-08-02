From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.

Import ListNotations.

Module GuardedTraceInterpreter1128.

Record signature : Type := {
  fsym : Type;
  gsym : Type;
  nsym : Type;
  arF : fsym -> nat;
  arG : gsym -> nat;
  arN : nsym -> nat
}.

Section System.

Variable Sig : signature.

Inductive ptm : Type :=
| PV : nat -> ptm
| PFun : fsym Sig -> pvec -> ptm
with pvec : Type :=
| PNil : pvec
| PCons : ptm -> pvec -> pvec.

Scheme ptm_ind' := Induction for ptm Sort Prop
with pvec_ind' := Induction for pvec Sort Prop.
Combined Scheme ptm_pvec_ind from ptm_ind', pvec_ind'.

Inductive gform : Type :=
| GTop : gform
| GRel : gsym Sig -> pvec -> gform
| GAnd : gform -> gform -> gform.

Inductive tm : Type :=
| TV : nat -> tm
| TFun : fsym Sig -> tvec -> tm
| TSeq : trace -> tm
with tvec : Type :=
| TNil : tvec
| TCons : tm -> tvec -> tvec
with trace : Type :=
| RNil : trace
| RCons : tm -> gform -> trace -> trace.

Scheme tm_ind' := Induction for tm Sort Prop
with tvec_ind' := Induction for tvec Sort Prop
with trace_ind' := Induction for trace Sort Prop.
Combined Scheme tm_tvec_trace_ind from tm_ind', tvec_ind', trace_ind'.

Inductive form : Type :=
| FTop : form
| FBot : form
| FEq : tm -> tm -> form
| FRelG : gsym Sig -> tvec -> form
| FRelN : nsym Sig -> tvec -> form
| FNeg : form -> form
| FAnd : form -> form -> form
| FOr : form -> form -> form
| FImp : form -> form -> form
| FIff : form -> form -> form
| FAll : nat -> form -> form
| FEx : nat -> form -> form.

Fixpoint pvec_length (xs : pvec) : nat :=
  match xs with
  | PNil => 0
  | PCons _ rest => S (pvec_length rest)
  end.

Fixpoint tvec_length (xs : tvec) : nat :=
  match xs with
  | TNil => 0
  | TCons _ rest => S (tvec_length rest)
  end.

Fixpoint wf_ptm (p : ptm) : Prop :=
  match p with
  | PV _ => True
  | PFun f args => wf_pvec args /\ pvec_length args = arF Sig f
  end
with wf_pvec (xs : pvec) : Prop :=
  match xs with
  | PNil => True
  | PCons p rest => wf_ptm p /\ wf_pvec rest
  end.

Fixpoint wf_gform (gamma : gform) : Prop :=
  match gamma with
  | GTop => True
  | GRel R args => wf_pvec args /\ pvec_length args = arG Sig R
  | GAnd gamma0 gamma1 => wf_gform gamma0 /\ wf_gform gamma1
  end.

Fixpoint wf_tm (t : tm) : Prop :=
  match t with
  | TV _ => True
  | TFun f args => wf_tvec args /\ tvec_length args = arF Sig f
  | TSeq q => wf_trace q
  end
with wf_tvec (xs : tvec) : Prop :=
  match xs with
  | TNil => True
  | TCons t rest => wf_tm t /\ wf_tvec rest
  end
with wf_trace (q : trace) : Prop :=
  match q with
  | RNil => True
  | RCons t gamma rest => wf_tm t /\ wf_gform gamma /\ wf_trace rest
  end.

Fixpoint wf_form (phi : form) : Prop :=
  match phi with
  | FTop => True
  | FBot => True
  | FEq t u => wf_tm t /\ wf_tm u
  | FRelG R args => wf_tvec args /\ tvec_length args = arG Sig R
  | FRelN R args => wf_tvec args /\ tvec_length args = arN Sig R
  | FNeg psi => wf_form psi
  | FAnd psi chi => wf_form psi /\ wf_form chi
  | FOr psi chi => wf_form psi /\ wf_form chi
  | FImp psi chi => wf_form psi /\ wf_form chi
  | FIff psi chi => wf_form psi /\ wf_form chi
  | FAll _ psi => wf_form psi
  | FEx _ psi => wf_form psi
  end.

Fixpoint embed_ptm (p : ptm) : tm :=
  match p with
  | PV i => TV i
  | PFun f args => TFun f (embed_pvec args)
  end
with embed_pvec (xs : pvec) : tvec :=
  match xs with
  | PNil => TNil
  | PCons p rest => TCons (embed_ptm p) (embed_pvec rest)
  end.

Fixpoint gform_to_form (gamma : gform) : form :=
  match gamma with
  | GTop => FTop
  | GRel R args => FRelG R (embed_pvec args)
  | GAnd gamma0 gamma1 => FAnd (gform_to_form gamma0) (gform_to_form gamma1)
  end.

Lemma embed_pvec_length :
  forall xs, tvec_length (embed_pvec xs) = pvec_length xs.
Proof.
  induction xs; simpl; auto.
Qed.

Lemma embed_wf_ptm :
  (forall p, wf_ptm p -> wf_tm (embed_ptm p)) /\
  (forall xs, wf_pvec xs -> wf_tvec (embed_pvec xs)).
Proof.
  apply (ptm_pvec_ind
    (fun p => wf_ptm p -> wf_tm (embed_ptm p))
    (fun xs => wf_pvec xs -> wf_tvec (embed_pvec xs))); simpl; intros; auto.
  - destruct H0 as [Hwf Hlen]. split; auto.
    now rewrite embed_pvec_length.
  - destruct H1 as [Hp Hrest]. split; auto.
Qed.

Lemma gform_to_form_wf :
  forall gamma, wf_gform gamma -> wf_form (gform_to_form gamma).
Proof.
  induction gamma; simpl; intros Hwf; auto.
  - destruct Hwf as [Hargs Hlen]. split.
    + exact (proj2 embed_wf_ptm _ Hargs).
    + now rewrite embed_pvec_length.
  - destruct Hwf as [H0 H1]. split; auto.
Qed.

Inductive code : Type :=
| CBase : code
| CComp : code -> code -> code
| CGuard : code -> gfacts -> code
| CApp : fsym Sig -> clist -> code
| CActCode : code -> code -> code
| CFactCode : gfact -> code
| CAtomF : fsym Sig -> code
| CAtomG : gsym Sig -> code
| CAtomN : nsym Sig -> code
| CNat : nat -> code
| CSeqCode : clist -> code
| CFinCode : clist -> code
with clist : Type :=
| CNil : clist
| CCons : code -> clist -> clist
with gfact : Type :=
| GFact : gsym Sig -> clist -> gfact
with gfacts : Type :=
| GFNil : gfacts
| GFCons : gfact -> gfacts -> gfacts.

Scheme code_ind' := Induction for code Sort Prop
with clist_ind' := Induction for clist Sort Prop
with gfact_ind' := Induction for gfact Sort Prop
with gfacts_ind' := Induction for gfacts Sort Prop.
Combined Scheme code_clist_gfact_gfacts_ind
  from code_ind', clist_ind', gfact_ind', gfacts_ind'.

Fixpoint gfacts_app (xs ys : gfacts) : gfacts :=
  match xs with
  | GFNil => ys
  | GFCons x rest => GFCons x (gfacts_app rest ys)
  end.

Fixpoint gfacts_in (x : gfact) (xs : gfacts) : Prop :=
  match xs with
  | GFNil => False
  | GFCons y rest => x = y \/ gfacts_in x rest
  end.

Lemma gfacts_app_assoc :
  forall xs ys zs,
    gfacts_app (gfacts_app xs ys) zs =
    gfacts_app xs (gfacts_app ys zs).
Proof.
  induction xs; simpl; intros; auto.
  now rewrite IHxs.
Qed.

Lemma gfacts_app_nil_r :
  forall xs, gfacts_app xs GFNil = xs.
Proof.
  induction xs; simpl; auto.
  now rewrite IHxs.
Qed.

Lemma gfacts_in_app_l :
  forall x xs ys, gfacts_in x xs -> gfacts_in x (gfacts_app xs ys).
Proof.
  induction xs; simpl; intros ys Hin.
  - contradiction.
  - destruct Hin as [Hx | Hin].
    + now left.
    + right. now apply IHxs.
Qed.

Lemma gfacts_in_app_r :
  forall x xs ys, gfacts_in x ys -> gfacts_in x (gfacts_app xs ys).
Proof.
  induction xs; simpl; intros ys Hin.
  - exact Hin.
  - right. now apply IHxs.
Qed.

Fixpoint act (c a : code) : code :=
  match c with
  | CBase => a
  | CComp d0 d1 => act d1 (act d0 a)
  | CGuard d _ => act d a
  | _ => CActCode c a
  end.

Fixpoint facts (c : code) : gfacts :=
  match c with
  | CComp d0 d1 => gfacts_app (facts d0) (facts d1)
  | CGuard d B => gfacts_app (facts d) B
  | _ => GFNil
  end.

Definition FactCode (R : gsym Sig) (args : clist) : code :=
  CFactCode (GFact R args).

Lemma comp_code_injective :
  forall c d c' d',
    CComp c d = CComp c' d' <-> c = c' /\ d = d'.
Proof.
  split; intros H.
  - now inversion H.
  - destruct H as [-> ->]. reflexivity.
Qed.

Lemma guard_code_injective :
  forall c B c' B',
    CGuard c B = CGuard c' B' <-> c = c' /\ B = B'.
Proof.
  split; intros H.
  - now inversion H.
  - destruct H as [-> ->]. reflexivity.
Qed.

Lemma app_code_injective :
  forall f args f' args',
    CApp f args = CApp f' args' -> existT _ f args = existT _ f' args'.
Proof.
  intros f args f' args' H.
  now inversion H.
Qed.

Lemma fact_code_injective :
  forall R args R' args',
    FactCode R args = FactCode R' args' ->
    existT _ R args = existT _ R' args'.
Proof.
  unfold FactCode. intros R args R' args' H.
  now inversion H; inversion H1.
Qed.

Lemma code_class_separation :
  (forall c d, CBase <> CComp c d) /\
  (forall c B, CBase <> CGuard c B) /\
  (forall f args c d, CApp f args <> CComp c d) /\
  (forall R args c B, FactCode R args <> CGuard c B).
Proof.
  repeat split; intros; discriminate.
Qed.

Lemma act_base : forall a, act CBase a = a.
Proof. reflexivity. Qed.

Lemma act_comp :
  forall c d a, act (CComp c d) a = act d (act c a).
Proof. reflexivity. Qed.

Lemma act_guard :
  forall c B a, act (CGuard c B) a = act c a.
Proof. reflexivity. Qed.

Lemma facts_comp :
  forall c d, facts (CComp c d) = gfacts_app (facts c) (facts d).
Proof. reflexivity. Qed.

Lemma facts_guard :
  forall c B, facts (CGuard c B) = gfacts_app (facts c) B.
Proof. reflexivity. Qed.

Lemma facts_guard_contains :
  forall x c B, gfacts_in x B -> gfacts_in x (facts (CGuard c B)).
Proof.
  intros x c B Hin. simpl.
  now apply gfacts_in_app_r.
Qed.

Record env : Type := {
  env_val : code -> nat -> code;
  env_guard :
    forall c B i, env_val (CGuard c B) i = env_val c i
}.

Definition env_update (E : env) (i : nat) (a : code) : env.
Proof.
  refine {| env_val := fun c j =>
      if Nat.eq_dec j i then a else env_val E c j |}.
  intros c B j. destruct (Nat.eq_dec j i); auto.
  apply env_guard.
Defined.

Fixpoint tau_p (c : code) (E : env) (p : ptm) : code :=
  match p with
  | PV i => env_val E c i
  | PFun f args => act c (CApp f (tau_p_vec c E args))
  end
with tau_p_vec (c : code) (E : env) (xs : pvec) : clist :=
  match xs with
  | PNil => CNil
  | PCons p rest => CCons (tau_p c E p) (tau_p_vec c E rest)
  end.

Fixpoint real (c : code) (E : env) (gamma : gform) : gfacts :=
  match gamma with
  | GTop => GFNil
  | GRel R args => GFCons (GFact R (tau_p_vec c E args)) GFNil
  | GAnd gamma0 gamma1 => gfacts_app (real c E gamma0) (real c E gamma1)
  end.

Fixpoint tau (c : code) (E : env) (t : tm) : code :=
  match t with
  | TV i => env_val E c i
  | TFun f args => act c (CApp f (tau_vec c E args))
  | TSeq q => trace_eval c E q
  end
with tau_vec (c : code) (E : env) (xs : tvec) : clist :=
  match xs with
  | TNil => CNil
  | TCons t rest => CCons (tau c E t) (tau_vec c E rest)
  end
with trace_eval (c : code) (E : env) (q : trace) : code :=
  match q with
  | RNil => c
  | RCons t gamma rest =>
      let d := tau c E t in
      let r := CComp c d in
      let B := real r E gamma in
      trace_eval (CGuard r B) E rest
  end.

Lemma tau_p_guard_invariant :
  (forall p c B E, tau_p (CGuard c B) E p = tau_p c E p) /\
  (forall xs c B E, tau_p_vec (CGuard c B) E xs = tau_p_vec c E xs).
Proof.
  apply (ptm_pvec_ind
    (fun p => forall c B E, tau_p (CGuard c B) E p = tau_p c E p)
    (fun xs => forall c B E, tau_p_vec (CGuard c B) E xs = tau_p_vec c E xs));
    simpl; intros; auto.
  - apply env_guard.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Lemma tau_p_guard_term :
  forall p c B E, tau_p (CGuard c B) E p = tau_p c E p.
Proof. exact (proj1 tau_p_guard_invariant). Qed.

Lemma tau_p_guard_vec :
  forall xs c B E, tau_p_vec (CGuard c B) E xs = tau_p_vec c E xs.
Proof. exact (proj2 tau_p_guard_invariant). Qed.

Lemma tau_embed_pure :
  (forall p c E, tau c E (embed_ptm p) = tau_p c E p) /\
  (forall xs c E, tau_vec c E (embed_pvec xs) = tau_p_vec c E xs).
Proof.
  apply (ptm_pvec_ind
    (fun p => forall c E, tau c E (embed_ptm p) = tau_p c E p)
    (fun xs => forall c E, tau_vec c E (embed_pvec xs) = tau_p_vec c E xs));
    simpl; intros; auto.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Lemma tau_embed_pure_term :
  forall p c E, tau c E (embed_ptm p) = tau_p c E p.
Proof. exact (proj1 tau_embed_pure). Qed.

Lemma tau_embed_pure_vec :
  forall xs c E, tau_vec c E (embed_pvec xs) = tau_p_vec c E xs.
Proof. exact (proj2 tau_embed_pure). Qed.

Lemma tau_embed_pure_vec_guard :
  forall xs c B E,
    tau_vec (CGuard c B) E (embed_pvec xs) = tau_p_vec c E xs.
Proof.
  intros xs c B E.
  rewrite tau_embed_pure_vec.
  apply tau_p_guard_vec.
Qed.

Variable Delta : nsym Sig -> code -> clist -> Prop.

Fixpoint holds (c : code) (E : env) (phi : form) : Prop :=
  match phi with
  | FTop => True
  | FBot => False
  | FEq t u => tau c E t = tau c E u
  | FRelG R args => gfacts_in (GFact R (tau_vec c E args)) (facts c)
  | FRelN R args => Delta R c (tau_vec c E args)
  | FNeg psi => ~ holds c E psi
  | FAnd psi chi => holds c E psi /\ holds c E chi
  | FOr psi chi => holds c E psi \/ holds c E chi
  | FImp psi chi => holds c E psi -> holds c E chi
  | FIff psi chi => holds c E psi <-> holds c E chi
  | FAll i psi => forall a, holds c (env_update E i a) psi
  | FEx i psi => exists a, holds c (env_update E i a) psi
  end.

Lemma fact_in_guard_context :
  forall x c pre mid post,
    gfacts_in x mid ->
    gfacts_in x
      (facts (CGuard c (gfacts_app pre (gfacts_app mid post)))).
Proof.
  intros x c pre mid post Hin. simpl.
  apply gfacts_in_app_r.
  apply gfacts_in_app_r.
  now apply gfacts_in_app_l.
Qed.

Lemma real_guard_satisfies_context :
  forall gamma c E pre post,
    holds (CGuard c (gfacts_app pre (gfacts_app (real c E gamma) post)))
      E (gform_to_form gamma).
Proof.
  induction gamma; simpl; intros c E pre post.
  - exact I.
  - rewrite tau_embed_pure_vec_guard.
    apply gfacts_in_app_r.
    apply gfacts_in_app_r.
    simpl. now left.
  - split.
    + rewrite gfacts_app_assoc.
      apply IHgamma1.
    + rewrite gfacts_app_assoc.
      rewrite <- gfacts_app_assoc.
      apply IHgamma2.
Qed.

Theorem real_guard_satisfies :
  forall gamma c E,
    holds (CGuard c (real c E gamma)) E (gform_to_form gamma).
Proof.
  intros gamma c E.
  replace (real c E gamma)
    with (gfacts_app GFNil (gfacts_app (real c E gamma) GFNil)).
  apply real_guard_satisfies_context.
  simpl. apply gfacts_app_nil_r.
Qed.

Inductive trace_realized : code -> env -> trace -> Prop :=
| trace_realized_nil :
    forall c E, trace_realized c E RNil
| trace_realized_cons :
    forall c E t gamma rest,
      let d := tau c E t in
      let r := CComp c d in
      holds (CGuard r (real r E gamma)) E (gform_to_form gamma) ->
      trace_realized (CGuard r (real r E gamma)) E rest ->
      trace_realized c E (RCons t gamma rest).

Theorem finite_trace_guard_realization :
  forall c E q, trace_realized c E q.
Proof.
  intros c E q. revert c E.
  induction q; intros c E.
  - constructor.
  - simpl. constructor.
    + apply real_guard_satisfies.
    + apply IHq.
Qed.

Definition T_c (c : code) (E : env) (t : tm) : code :=
  tau c E t.

Definition P_c (c : code) (E : env) (phi : form) : Prop :=
  holds c E phi.

Record interpretation_function : Type := {
  interp_code : code
}.

Definition I_c (c : code) : interpretation_function := {|
  interp_code := c
|}.

Definition kappa (I : interpretation_function) : code :=
  interp_code I.

Definition eta (c : code) : interpretation_function := I_c c.

Lemma I_c_eq_iff :
  forall c d, I_c c = I_c d <-> c = d.
Proof.
  split; intros H.
  - now inversion H.
  - now subst.
Qed.

Lemma kappa_eta :
  forall c, kappa (eta c) = c.
Proof. reflexivity. Qed.

Record IEnv : Type := {
  ienv_kappa : env
}.

Definition rho_kappa (rho : IEnv) : env := ienv_kappa rho.

Definition rho_apply
    (rho : IEnv) (I : interpretation_function) (i : nat)
    : interpretation_function :=
  I_c (env_val (rho_kappa rho) (kappa I) i).

Lemma rho_apply_guard :
  forall rho c B i,
    rho_apply rho (I_c (CGuard c B)) i =
    rho_apply rho (I_c c) i.
Proof.
  intros rho c B i.
  unfold rho_apply, rho_kappa, kappa. simpl.
  now rewrite env_guard.
Qed.

Record operation_interpretation : Type := {
  op_code : code
}.

Definition Omega_c (c : code) (f : fsym Sig) (args : clist) : code :=
  act c (CApp f args).

Definition O_c (c : code) : operation_interpretation := {|
  op_code := c
|}.

Definition Theta (I : interpretation_function) : operation_interpretation :=
  O_c (kappa I).

Definition Theta_inv (O : operation_interpretation) : interpretation_function :=
  I_c (op_code O).

Lemma Theta_left_inverse :
  forall I, Theta_inv (Theta I) = I.
Proof.
  intros [c]. reflexivity.
Qed.

Lemma Theta_right_inverse :
  forall O, Theta (Theta_inv O) = O.
Proof.
  intros [c]. reflexivity.
Qed.

Definition diamond_I (I J : interpretation_function) : interpretation_function :=
  I_c (CComp (kappa I) (kappa J)).

Definition diamond_O (O P : operation_interpretation) : operation_interpretation :=
  O_c (CComp (op_code O) (op_code P)).

Theorem Theta_diamond_hom :
  forall I J,
    Theta (diamond_I I J) = diamond_O (Theta I) (Theta J).
Proof.
  intros [c] [d]. reflexivity.
Qed.

Theorem code_action_composition :
  forall c d a, act (CComp c d) a = act d (act c a).
Proof. reflexivity. Qed.

Fixpoint union_nat (xs ys : list nat) : list nat :=
  match xs with
  | [] => ys
  | x :: rest =>
      if in_dec Nat.eq_dec x ys then union_nat rest ys
      else x :: union_nat rest ys
  end.

Fixpoint remove_nat (i : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: rest =>
      if Nat.eq_dec x i then remove_nat i rest else x :: remove_nat i rest
  end.

Fixpoint fv_ptm (p : ptm) : list nat :=
  match p with
  | PV i => [i]
  | PFun _ args => fv_pvec args
  end
with fv_pvec (xs : pvec) : list nat :=
  match xs with
  | PNil => []
  | PCons p rest => union_nat (fv_ptm p) (fv_pvec rest)
  end.

Fixpoint fv_gform (gamma : gform) : list nat :=
  match gamma with
  | GTop => []
  | GRel _ args => fv_pvec args
  | GAnd gamma0 gamma1 => union_nat (fv_gform gamma0) (fv_gform gamma1)
  end.

Fixpoint fv_tm (t : tm) : list nat :=
  match t with
  | TV i => [i]
  | TFun _ args => fv_tvec args
  | TSeq q => fv_trace q
  end
with fv_tvec (xs : tvec) : list nat :=
  match xs with
  | TNil => []
  | TCons t rest => union_nat (fv_tm t) (fv_tvec rest)
  end
with fv_trace (q : trace) : list nat :=
  match q with
  | RNil => []
  | RCons t gamma rest =>
      union_nat (union_nat (fv_tm t) (fv_gform gamma)) (fv_trace rest)
  end.

Fixpoint fv_form (phi : form) : list nat :=
  match phi with
  | FTop => []
  | FBot => []
  | FEq t u => union_nat (fv_tm t) (fv_tm u)
  | FRelG _ args => fv_tvec args
  | FRelN _ args => fv_tvec args
  | FNeg psi => fv_form psi
  | FAnd psi chi => union_nat (fv_form psi) (fv_form chi)
  | FOr psi chi => union_nat (fv_form psi) (fv_form chi)
  | FImp psi chi => union_nat (fv_form psi) (fv_form chi)
  | FIff psi chi => union_nat (fv_form psi) (fv_form chi)
  | FAll i psi => remove_nat i (fv_form psi)
  | FEx i psi => remove_nat i (fv_form psi)
  end.

Definition subst : Type := list (nat * ptm).

Fixpoint subst_lookup (sigma : subst) (i : nat) : ptm :=
  match sigma with
  | [] => PV i
  | (j, p) :: rest =>
      if Nat.eq_dec i j then p else subst_lookup rest i
  end.

Fixpoint subst_support (sigma : subst) : list nat :=
  match sigma with
  | [] => []
  | (i, _) :: rest => union_nat [i] (subst_support rest)
  end.

Fixpoint subst_rfv (sigma : subst) : list nat :=
  match sigma with
  | [] => []
  | (_, p) :: rest => union_nat (fv_ptm p) (subst_rfv rest)
  end.

Fixpoint subst_remove (i : nat) (sigma : subst) : subst :=
  match sigma with
  | [] => []
  | (j, p) :: rest =>
      if Nat.eq_dec i j then subst_remove i rest
      else (j, p) :: subst_remove i rest
  end.

Definition rename_subst (i j : nat) : subst := [(i, PV j)].

Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: rest => Nat.max x (max_list rest)
  end.

Definition fresh (xs : list nat) : nat := S (max_list xs).

Fixpoint sub_ptm (p : ptm) (sigma : subst) : ptm :=
  match p with
  | PV i => subst_lookup sigma i
  | PFun f args => PFun f (sub_pvec args sigma)
  end
with sub_pvec (xs : pvec) (sigma : subst) : pvec :=
  match xs with
  | PNil => PNil
  | PCons p rest => PCons (sub_ptm p sigma) (sub_pvec rest sigma)
  end.

Fixpoint sub_gform (gamma : gform) (sigma : subst) : gform :=
  match gamma with
  | GTop => GTop
  | GRel R args => GRel R (sub_pvec args sigma)
  | GAnd gamma0 gamma1 => GAnd (sub_gform gamma0 sigma) (sub_gform gamma1 sigma)
  end.

Fixpoint sub_tm (t : tm) (sigma : subst) : tm :=
  match t with
  | TV i => embed_ptm (subst_lookup sigma i)
  | TFun f args => TFun f (sub_tvec args sigma)
  | TSeq q => TSeq (sub_trace q sigma)
  end
with sub_tvec (xs : tvec) (sigma : subst) : tvec :=
  match xs with
  | TNil => TNil
  | TCons t rest => TCons (sub_tm t sigma) (sub_tvec rest sigma)
  end
with sub_trace (q : trace) (sigma : subst) : trace :=
  match q with
  | RNil => RNil
  | RCons t gamma rest =>
      RCons (sub_tm t sigma) (sub_gform gamma sigma) (sub_trace rest sigma)
  end.

Inductive sub_form_rel : form -> subst -> form -> Prop :=
| STop :
    forall sigma, sub_form_rel FTop sigma FTop
| SBot :
    forall sigma, sub_form_rel FBot sigma FBot
| SEq :
    forall t u sigma,
      sub_form_rel (FEq t u) sigma (FEq (sub_tm t sigma) (sub_tm u sigma))
| SRelG :
    forall R args sigma,
      sub_form_rel (FRelG R args) sigma (FRelG R (sub_tvec args sigma))
| SRelN :
    forall R args sigma,
      sub_form_rel (FRelN R args) sigma (FRelN R (sub_tvec args sigma))
| SNeg :
    forall psi psi' sigma,
      sub_form_rel psi sigma psi' ->
      sub_form_rel (FNeg psi) sigma (FNeg psi')
| SAnd :
    forall psi chi psi' chi' sigma,
      sub_form_rel psi sigma psi' ->
      sub_form_rel chi sigma chi' ->
      sub_form_rel (FAnd psi chi) sigma (FAnd psi' chi')
| SOr :
    forall psi chi psi' chi' sigma,
      sub_form_rel psi sigma psi' ->
      sub_form_rel chi sigma chi' ->
      sub_form_rel (FOr psi chi) sigma (FOr psi' chi')
| SImp :
    forall psi chi psi' chi' sigma,
      sub_form_rel psi sigma psi' ->
      sub_form_rel chi sigma chi' ->
      sub_form_rel (FImp psi chi) sigma (FImp psi' chi')
| SIff :
    forall psi chi psi' chi' sigma,
      sub_form_rel psi sigma psi' ->
      sub_form_rel chi sigma chi' ->
      sub_form_rel (FIff psi chi) sigma (FIff psi' chi')
| SAll :
    forall i psi sigma renamed body',
      let X := union_nat (fv_form psi)
        (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i])) in
      let j := fresh X in
      sub_form_rel psi (rename_subst i j) renamed ->
      sub_form_rel renamed (subst_remove i sigma) body' ->
      sub_form_rel (FAll i psi) sigma (FAll j body')
| SEx :
    forall i psi sigma renamed body',
      let X := union_nat (fv_form psi)
        (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i])) in
      let j := fresh X in
      sub_form_rel psi (rename_subst i j) renamed ->
      sub_form_rel renamed (subst_remove i sigma) body' ->
      sub_form_rel (FEx i psi) sigma (FEx j body').

Inductive qfree_form : form -> Prop :=
| QFTop : qfree_form FTop
| QFBot : qfree_form FBot
| QFEq : forall t u, qfree_form (FEq t u)
| QFRelG : forall R args, qfree_form (FRelG R args)
| QFRelN : forall R args, qfree_form (FRelN R args)
| QFNeg :
    forall psi,
      qfree_form psi ->
      qfree_form (FNeg psi)
| QFAnd :
    forall psi chi,
      qfree_form psi ->
      qfree_form chi ->
      qfree_form (FAnd psi chi)
| QFOr :
    forall psi chi,
      qfree_form psi ->
      qfree_form chi ->
      qfree_form (FOr psi chi)
| QFImp :
    forall psi chi,
      qfree_form psi ->
      qfree_form chi ->
      qfree_form (FImp psi chi)
| QFIff :
    forall psi chi,
      qfree_form psi ->
      qfree_form chi ->
      qfree_form (FIff psi chi).

Definition env_subst (E : env) (sigma : subst) : env.
Proof.
  refine {| env_val := fun c i => tau_p c E (subst_lookup sigma i) |}.
  intros c B i. apply tau_p_guard_term.
Defined.

Definition rho_sigma (rho : IEnv) (sigma : subst) : IEnv := {|
  ienv_kappa := env_subst (rho_kappa rho) sigma
|}.

Lemma rho_sigma_value :
  forall rho sigma c i,
    rho_apply (rho_sigma rho sigma) (I_c c) i =
    I_c (tau_p c (rho_kappa rho) (subst_lookup sigma i)).
Proof. reflexivity. Qed.

Theorem rho_sigma_kappa :
  forall rho sigma c i,
    env_val (rho_kappa (rho_sigma rho sigma)) c i =
    env_val (env_subst (rho_kappa rho) sigma) c i.
Proof. reflexivity. Qed.

Lemma sub_pure_semantics :
  (forall p c E sigma,
      tau_p c E (sub_ptm p sigma) = tau_p c (env_subst E sigma) p) /\
  (forall xs c E sigma,
      tau_p_vec c E (sub_pvec xs sigma) = tau_p_vec c (env_subst E sigma) xs).
Proof.
  apply (ptm_pvec_ind
    (fun p => forall c E sigma,
      tau_p c E (sub_ptm p sigma) = tau_p c (env_subst E sigma) p)
    (fun xs => forall c E sigma,
      tau_p_vec c E (sub_pvec xs sigma) = tau_p_vec c (env_subst E sigma) xs));
    simpl; intros; auto.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Lemma sub_pure_semantics_term :
  forall p c E sigma,
    tau_p c E (sub_ptm p sigma) = tau_p c (env_subst E sigma) p.
Proof. exact (proj1 sub_pure_semantics). Qed.

Lemma sub_pure_semantics_vec :
  forall xs c E sigma,
    tau_p_vec c E (sub_pvec xs sigma) = tau_p_vec c (env_subst E sigma) xs.
Proof. exact (proj2 sub_pure_semantics). Qed.

Lemma real_substitution :
  forall gamma c E sigma,
    real c E (sub_gform gamma sigma) = real c (env_subst E sigma) gamma.
Proof.
  induction gamma; simpl; intros; auto.
  - now rewrite sub_pure_semantics_vec.
  - now rewrite IHgamma1, IHgamma2.
Qed.

Lemma term_substitution_semantics :
  (forall t c E sigma,
      tau c E (sub_tm t sigma) = tau c (env_subst E sigma) t) /\
  (forall xs c E sigma,
      tau_vec c E (sub_tvec xs sigma) = tau_vec c (env_subst E sigma) xs) /\
  (forall q c E sigma,
      trace_eval c E (sub_trace q sigma) =
      trace_eval c (env_subst E sigma) q).
Proof.
  apply (tm_tvec_trace_ind
    (fun t => forall c E sigma,
      tau c E (sub_tm t sigma) = tau c (env_subst E sigma) t)
    (fun xs => forall c E sigma,
      tau_vec c E (sub_tvec xs sigma) = tau_vec c (env_subst E sigma) xs)
    (fun q => forall c E sigma,
      trace_eval c E (sub_trace q sigma) =
      trace_eval c (env_subst E sigma) q));
    simpl; intros; auto.
  - rewrite tau_embed_pure_term. reflexivity.
  - now rewrite H.
  - now rewrite H, H0.
  - rewrite H.
    rewrite real_substitution.
    apply H0.
Qed.

Theorem item_substitution_theorem :
  forall t c E sigma,
    tau c E (sub_tm t sigma) = tau c (env_subst E sigma) t.
Proof.
  exact (proj1 term_substitution_semantics).
Qed.

Lemma in_union_nat_iff :
  forall x xs ys, In x (union_nat xs ys) <-> In x xs \/ In x ys.
Proof.
  intros x xs.
  induction xs as [|a xs IH]; simpl; intros ys.
  - tauto.
  - destruct (in_dec Nat.eq_dec a ys) as [Ha | Hna].
    + split; intro H.
      * destruct (proj1 (IH ys) H) as [Hx | Hy].
        -- left. right. exact Hx.
        -- right. exact Hy.
      * apply (proj2 (IH ys)).
        destruct H as [[Hx | Hx] | Hy].
        -- subst. right. exact Ha.
        -- left. exact Hx.
        -- right. exact Hy.
    + split; intro H.
      * destruct H as [Hx | Hrest].
        -- subst. left. left. reflexivity.
        -- destruct (proj1 (IH ys) Hrest) as [Hx | Hy].
           ++ left. right. exact Hx.
           ++ right. exact Hy.
      * destruct H as [[Hx | Hx] | Hy].
        -- subst. left. reflexivity.
        -- right. apply (proj2 (IH ys)). left. exact Hx.
        -- right. apply (proj2 (IH ys)). right. exact Hy.
Qed.

Lemma in_remove_nat_iff :
  forall x i xs, In x (remove_nat i xs) <-> In x xs /\ x <> i.
Proof.
  intros x i xs.
  induction xs as [|a xs IH]; simpl.
  - split; intros H; [contradiction | tauto].
  - destruct (Nat.eq_dec a i) as [Hai | Hnai].
    + subst. split; intros H.
      * destruct (proj1 IH H) as [Hin Hneq].
        split; [right; exact Hin | exact Hneq].
      * destruct H as [[Hx | Hin] Hneq].
        -- congruence.
        -- apply (proj2 IH). split; assumption.
    + split; intros H.
      * destruct H as [Hx | Hrest].
        -- subst. split; [left; reflexivity | exact Hnai].
        -- destruct (proj1 IH Hrest) as [Hin Hneq].
           split; [right; exact Hin | exact Hneq].
      * destruct H as [[Hx | Hin] Hneq].
        -- subst. left. reflexivity.
        -- right. apply (proj2 IH). split; assumption.
Qed.

Lemma max_list_ge :
  forall x xs, In x xs -> x <= max_list xs.
Proof.
  induction xs as [|a xs IH]; simpl; intros H.
  - contradiction.
  - destruct H as [Hx | Hx]; subst; [lia | specialize (IH Hx); lia].
Qed.

Lemma fresh_not_in :
  forall xs, ~ In (fresh xs) xs.
Proof.
  intros xs H.
  unfold fresh in H.
  pose proof (max_list_ge (S (max_list xs)) xs H).
  lia.
Qed.

Lemma subst_lookup_remove_eq :
  forall sigma i, subst_lookup (subst_remove i sigma) i = PV i.
Proof.
  induction sigma as [|[j p] rest IH]; simpl; intros i.
  - destruct (Nat.eq_dec i i); congruence.
  - destruct (Nat.eq_dec i j) as [Hij | Hnij].
    + exact (IH i).
    + simpl. destruct (Nat.eq_dec i j); congruence.
Qed.

Lemma subst_lookup_remove_miss :
  forall sigma i k,
    k <> i ->
    subst_lookup (subst_remove i sigma) k = subst_lookup sigma k.
Proof.
  induction sigma as [|[j p] rest IH]; simpl; intros i k Hki.
  - reflexivity.
  - destruct (Nat.eq_dec i j) as [Hij | Hnij].
    + subst. simpl. destruct (Nat.eq_dec k j); [congruence | exact (IH j k Hki)].
    + simpl. destruct (Nat.eq_dec k j) as [Hkj | Hnkj]; [reflexivity | exact (IH i k Hki)].
Qed.

Lemma subst_lookup_notin_support :
  forall sigma i,
    ~ In i (subst_support sigma) ->
    subst_lookup sigma i = PV i.
Proof.
  induction sigma as [|[j p] rest IH]; simpl; intros i Hnot.
  - destruct (Nat.eq_dec i i); congruence.
  - assert (Hnot' : ~ (In i [j] \/ In i (subst_support rest))).
    { intro H. apply Hnot. apply (proj2 (in_union_nat_iff i [j] (subst_support rest))). exact H. }
    destruct (Nat.eq_dec i j) as [Hij | Hnij].
    + subst. exfalso. apply Hnot'. left. simpl. auto.
    + apply IH. intro Hin. apply Hnot'. right. exact Hin.
Qed.

Lemma subst_lookup_notin_rfv :
  forall sigma x i,
    ~ In x (subst_rfv sigma) ->
    x <> i ->
    ~ In x (fv_ptm (subst_lookup sigma i)).
Proof.
  induction sigma as [|[j p] rest IH]; simpl; intros x i Hrfv Hxi.
  - simpl. intros [Hx | []]. apply Hxi. symmetry. exact Hx.
  - assert (Hrfv' : ~ (In x (fv_ptm p) \/ In x (subst_rfv rest))).
    { intro H. apply Hrfv. apply (proj2 (in_union_nat_iff x (fv_ptm p) (subst_rfv rest))). exact H. }
    destruct (Nat.eq_dec i j) as [Hij | Hnij].
    + subst. intro Hin. apply Hrfv'. left. exact Hin.
    + apply IH.
      * intro Hin. apply Hrfv'. right. exact Hin.
      * exact Hxi.
Qed.

Definition env_agree_on (xs : list nat) (E1 E2 : env) : Prop :=
  forall c i, In i xs -> env_val E1 c i = env_val E2 c i.

Lemma env_agree_union_left :
  forall xs ys E1 E2,
    env_agree_on (union_nat xs ys) E1 E2 ->
    env_agree_on xs E1 E2.
Proof.
  unfold env_agree_on. intros xs ys E1 E2 H c i Hi.
  apply H. rewrite in_union_nat_iff. now left.
Qed.

Lemma env_agree_union_right :
  forall xs ys E1 E2,
    env_agree_on (union_nat xs ys) E1 E2 ->
    env_agree_on ys E1 E2.
Proof.
  unfold env_agree_on. intros xs ys E1 E2 H c i Hi.
  apply H. rewrite in_union_nat_iff. now right.
Qed.

Lemma tau_p_env_agree :
  (forall p c E1 E2,
      env_agree_on (fv_ptm p) E1 E2 ->
      tau_p c E1 p = tau_p c E2 p) /\
  (forall xs c E1 E2,
      env_agree_on (fv_pvec xs) E1 E2 ->
      tau_p_vec c E1 xs = tau_p_vec c E2 xs).
Proof.
  apply (ptm_pvec_ind
    (fun p => forall c E1 E2,
      env_agree_on (fv_ptm p) E1 E2 ->
      tau_p c E1 p = tau_p c E2 p)
    (fun xs => forall c E1 E2,
      env_agree_on (fv_pvec xs) E1 E2 ->
      tau_p_vec c E1 xs = tau_p_vec c E2 xs));
    simpl; intros; auto.
  - apply H. simpl. auto.
  - match goal with
    | IH : forall c E1 E2, env_agree_on (fv_pvec ?args) E1 E2 -> _,
      Hagree : env_agree_on (fv_pvec ?args) ?E1 ?E2 |- _ =>
        rewrite (IH c E1 E2 Hagree);
        reflexivity
    end.
  - match goal with
    | IH1 : forall c E1 E2, env_agree_on (fv_ptm ?p) E1 E2 -> _,
      IH2 : forall c E1 E2, env_agree_on (fv_pvec ?xs) E1 E2 -> _,
      Hagree : env_agree_on (union_nat (fv_ptm ?p) (fv_pvec ?xs)) ?E1 ?E2 |- _ =>
        rewrite (IH1 c E1 E2 (env_agree_union_left _ _ _ _ Hagree));
        rewrite (IH2 c E1 E2 (env_agree_union_right _ _ _ _ Hagree));
        reflexivity
    end.
Qed.

Lemma tau_p_update_irrel :
  (forall p c E i a,
      ~ In i (fv_ptm p) ->
      tau_p c (env_update E i a) p = tau_p c E p) /\
  (forall xs c E i a,
      ~ In i (fv_pvec xs) ->
      tau_p_vec c (env_update E i a) xs = tau_p_vec c E xs).
Proof.
  apply (ptm_pvec_ind
    (fun p => forall c E i a,
      ~ In i (fv_ptm p) ->
      tau_p c (env_update E i a) p = tau_p c E p)
    (fun xs => forall c E i a,
      ~ In i (fv_pvec xs) ->
      tau_p_vec c (env_update E i a) xs = tau_p_vec c E xs));
    simpl; intros; auto.
  - destruct (Nat.eq_dec n i); subst; [exfalso; apply H; simpl; auto | reflexivity].
  - match goal with
    | IH : forall c E i a, ~ In i (fv_pvec ?args) -> _,
      Hnot : ~ In ?i (fv_pvec ?args) |- _ =>
        rewrite (IH c E i a Hnot);
        reflexivity
    end.
  - match goal with
    | IH1 : forall c E i a, ~ In i (fv_ptm ?p) -> _,
      IH2 : forall c E i a, ~ In i (fv_pvec ?xs) -> _,
      Hnot : ~ In ?i (union_nat (fv_ptm ?p) (fv_pvec ?xs)) |- _ =>
        rewrite (IH1 c E i a (fun Hin => Hnot ((proj2 (in_union_nat_iff i (fv_ptm p) (fv_pvec xs))) (or_introl Hin))));
        rewrite (IH2 c E i a (fun Hin => Hnot ((proj2 (in_union_nat_iff i (fv_ptm p) (fv_pvec xs))) (or_intror Hin))));
        reflexivity
    end.
Qed.

Lemma real_env_agree :
  forall gamma c E1 E2,
    env_agree_on (fv_gform gamma) E1 E2 ->
    real c E1 gamma = real c E2 gamma.
Proof.
  induction gamma; simpl; intros; auto.
  - match goal with
    | Hagree : env_agree_on (fv_pvec ?xs) ?E1 ?E2 |- _ =>
        rewrite (proj2 tau_p_env_agree xs c E1 E2 Hagree);
        reflexivity
    end.
  - rewrite (IHgamma1 c E1 E2 (env_agree_union_left _ _ _ _ H)).
    rewrite (IHgamma2 c E1 E2 (env_agree_union_right _ _ _ _ H)).
    reflexivity.
Qed.

Lemma term_env_agree :
  (forall t c E1 E2,
      env_agree_on (fv_tm t) E1 E2 ->
      tau c E1 t = tau c E2 t) /\
  (forall xs c E1 E2,
      env_agree_on (fv_tvec xs) E1 E2 ->
      tau_vec c E1 xs = tau_vec c E2 xs) /\
  (forall q c E1 E2,
      env_agree_on (fv_trace q) E1 E2 ->
      trace_eval c E1 q = trace_eval c E2 q).
Proof.
  apply (tm_tvec_trace_ind
    (fun t => forall c E1 E2,
      env_agree_on (fv_tm t) E1 E2 ->
      tau c E1 t = tau c E2 t)
    (fun xs => forall c E1 E2,
      env_agree_on (fv_tvec xs) E1 E2 ->
      tau_vec c E1 xs = tau_vec c E2 xs)
    (fun q => forall c E1 E2,
      env_agree_on (fv_trace q) E1 E2 ->
      trace_eval c E1 q = trace_eval c E2 q));
    simpl; intros; auto.
  - apply H. simpl. auto.
  - match goal with
    | IH : forall c E1 E2, env_agree_on (fv_tvec ?args) E1 E2 -> _,
      Hagree : env_agree_on (fv_tvec ?args) ?E1 ?E2 |- _ =>
        rewrite (IH c E1 E2 Hagree);
        reflexivity
    end.
  - rewrite (H c E1 E2 (env_agree_union_left _ _ _ _ H1)).
    rewrite (H0 c E1 E2 (env_agree_union_right _ _ _ _ H1)).
    reflexivity.
  - match goal with
    | IHt : forall c E1 E2, env_agree_on (fv_tm ?t) E1 E2 -> _,
      IHq : forall c E1 E2, env_agree_on (fv_trace ?q) E1 E2 -> _,
      Hagree : env_agree_on (union_nat (union_nat (fv_tm ?t) (fv_gform ?g)) (fv_trace ?q)) ?E1 ?E2 |- _ =>
        rewrite (IHt c E1 E2
          (env_agree_union_left _ _ _ _
            (env_agree_union_left _ _ _ _ Hagree)));
        rewrite (real_env_agree g (CComp c (tau c E2 t)) E1 E2
          (env_agree_union_right _ _ _ _
            (env_agree_union_left _ _ _ _ Hagree)));
        apply IHq;
        apply env_agree_union_right with (xs := union_nat (fv_tm t) (fv_gform g));
        exact Hagree
    end.
Qed.

Lemma env_agree_remove_update :
  forall xs i a E1 E2,
    env_agree_on (remove_nat i xs) E1 E2 ->
    env_agree_on xs (env_update E1 i a) (env_update E2 i a).
Proof.
  unfold env_agree_on. intros xs i a E1 E2 H c k Hk.
  simpl. destruct (Nat.eq_dec k i) as [Hki | Hki]; [reflexivity |].
  apply H. rewrite in_remove_nat_iff. split; assumption.
Qed.

Lemma holds_env_agree :
  forall phi c E1 E2,
    env_agree_on (fv_form phi) E1 E2 ->
    holds c E1 phi <-> holds c E2 phi.
Proof.
  induction phi; simpl; intros c E1 E2 Hagree.
  - tauto.
  - tauto.
  - rewrite (proj1 term_env_agree t c E1 E2
      (env_agree_union_left _ _ _ _ Hagree)).
    rewrite (proj1 term_env_agree t0 c E1 E2
      (env_agree_union_right _ _ _ _ Hagree)).
    tauto.
  - rewrite (proj1 (proj2 term_env_agree) t c E1 E2 Hagree). tauto.
  - rewrite (proj1 (proj2 term_env_agree) t c E1 E2 Hagree). tauto.
  - specialize (IHphi c E1 E2 Hagree). tauto.
  - specialize (IHphi1 c E1 E2 (env_agree_union_left _ _ _ _ Hagree)).
    specialize (IHphi2 c E1 E2 (env_agree_union_right _ _ _ _ Hagree)).
    tauto.
  - specialize (IHphi1 c E1 E2 (env_agree_union_left _ _ _ _ Hagree)).
    specialize (IHphi2 c E1 E2 (env_agree_union_right _ _ _ _ Hagree)).
    tauto.
  - specialize (IHphi1 c E1 E2 (env_agree_union_left _ _ _ _ Hagree)).
    specialize (IHphi2 c E1 E2 (env_agree_union_right _ _ _ _ Hagree)).
    tauto.
  - specialize (IHphi1 c E1 E2 (env_agree_union_left _ _ _ _ Hagree)).
    specialize (IHphi2 c E1 E2 (env_agree_union_right _ _ _ _ Hagree)).
    tauto.
  - split; intros H a.
    + assert (Hag' :
        env_agree_on (fv_form phi) (env_update E1 n a) (env_update E2 n a)).
      { apply env_agree_remove_update. exact Hagree. }
      pose proof (IHphi c (env_update E1 n a) (env_update E2 n a) Hag') as IH.
      exact (proj1 IH (H a)).
    + assert (Hag' :
        env_agree_on (fv_form phi) (env_update E1 n a) (env_update E2 n a)).
      { apply env_agree_remove_update. exact Hagree. }
      pose proof (IHphi c (env_update E1 n a) (env_update E2 n a) Hag') as IH.
      exact (proj2 IH (H a)).
  - split; intros [a H].
    + exists a.
      assert (Hag' :
        env_agree_on (fv_form phi) (env_update E1 n a) (env_update E2 n a)).
      { apply env_agree_remove_update. exact Hagree. }
      pose proof (IHphi c (env_update E1 n a) (env_update E2 n a) Hag') as IH.
      exact (proj1 IH H).
    + exists a.
      assert (Hag' :
        env_agree_on (fv_form phi) (env_update E1 n a) (env_update E2 n a)).
      { apply env_agree_remove_update. exact Hagree. }
      pose proof (IHphi c (env_update E1 n a) (env_update E2 n a) Hag') as IH.
      exact (proj2 IH H).
Qed.

Lemma quantified_env_agree :
  forall psi sigma i j a E,
    ~ In j (fv_form psi) ->
    ~ In j (subst_rfv sigma) ->
    ~ In j (subst_support sigma) ->
    j <> i ->
    env_agree_on (fv_form psi)
      (env_subst
        (env_subst (env_update E j a) (subst_remove i sigma))
        (rename_subst i j))
      (env_update (env_subst E sigma) i a).
Proof.
  unfold env_agree_on.
  intros psi sigma i j a E Hjfv Hjrfv Hjsupp Hji c k Hk.
  unfold env_subst, rename_subst.
  simpl.
  destruct (Nat.eq_dec k i) as [Hki | Hki].
  - subst k.
    destruct (Nat.eq_dec i i) as [_ | Hbad]; [|contradiction].
    unfold env_subst.
    simpl.
    rewrite subst_lookup_remove_miss by exact Hji.
    rewrite subst_lookup_notin_support by exact Hjsupp.
    simpl. destruct (Nat.eq_dec j j); [reflexivity | congruence].
  - destruct (Nat.eq_dec k i) as [Hbad | _]; [congruence |].
    unfold env_subst.
    simpl.
    rewrite subst_lookup_remove_miss by exact Hki.
    rewrite (proj1 tau_p_update_irrel).
    + reflexivity.
    + apply subst_lookup_notin_rfv.
      * exact Hjrfv.
      * intro Hkj. subst k. exact (Hjfv Hk).
Qed.

Lemma fresh_quantifier_conditions :
  forall psi sigma i,
    let X := union_nat (fv_form psi)
      (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i])) in
    let j := fresh X in
    ~ In j (fv_form psi) /\
    ~ In j (subst_rfv sigma) /\
    ~ In j (subst_support sigma) /\
    j <> i.
Proof.
  intros psi sigma i X j.
  assert (Hfresh : ~ In j X).
  { subst j. apply fresh_not_in. }
  repeat split; intro H; apply Hfresh; subst X.
  - apply (proj2 (in_union_nat_iff j (fv_form psi)
      (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i])))).
    left. exact H.
  - apply (proj2 (in_union_nat_iff j (fv_form psi)
      (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i])))).
    right.
    apply (proj2 (in_union_nat_iff j (subst_rfv sigma)
      (union_nat (subst_support sigma) [i]))).
    left. exact H.
  - apply (proj2 (in_union_nat_iff j (fv_form psi)
      (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i])))).
    right.
    apply (proj2 (in_union_nat_iff j (subst_rfv sigma)
      (union_nat (subst_support sigma) [i]))).
    right.
    apply (proj2 (in_union_nat_iff j (subst_support sigma) [i])).
    left. exact H.
  - apply (proj2 (in_union_nat_iff j (fv_form psi)
      (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i])))).
    right.
    apply (proj2 (in_union_nat_iff j (subst_rfv sigma)
      (union_nat (subst_support sigma) [i]))).
    right.
    apply (proj2 (in_union_nat_iff j (subst_support sigma) [i])).
    right. simpl. left. symmetry. exact H.
Qed.

Definition formula_substitution_statement : Prop :=
  forall phi phi' c E sigma,
    sub_form_rel phi sigma phi' ->
    holds c E phi' <-> holds c (env_subst E sigma) phi.

Theorem qfree_formula_substitution :
  forall phi phi' c E sigma,
    qfree_form phi ->
    sub_form_rel phi sigma phi' ->
    holds c E phi' <-> holds c (env_subst E sigma) phi.
Proof.
  intros phi phi' c E sigma Hq Hsub.
  induction Hsub; inversion Hq; subst; simpl.
  - split; intro h; exact h.
  - split; intro h; exact h.
  - rewrite (proj1 term_substitution_semantics).
    rewrite (proj1 term_substitution_semantics).
    split; intro h; exact h.
  - rewrite (proj1 (proj2 term_substitution_semantics)).
    split; intro h; exact h.
  - rewrite (proj1 (proj2 term_substitution_semantics)).
    split; intro h; exact h.
  - match goal with
    | Hpsi : qfree_form psi |- _ => specialize (IHHsub Hpsi)
    end.
    split; intro h; intro hp.
    + apply h. exact (proj2 IHHsub hp).
    + apply h. exact (proj1 IHHsub hp).
  - match goal with
    | Hpsi : qfree_form psi, Hchi : qfree_form chi |- _ =>
        specialize (IHHsub1 Hpsi);
        specialize (IHHsub2 Hchi)
    end.
    split; intros [hp hq].
    + split; [exact (proj1 IHHsub1 hp) | exact (proj1 IHHsub2 hq)].
    + split; [exact (proj2 IHHsub1 hp) | exact (proj2 IHHsub2 hq)].
  - match goal with
    | Hpsi : qfree_form psi, Hchi : qfree_form chi |- _ =>
        specialize (IHHsub1 Hpsi);
        specialize (IHHsub2 Hchi)
    end.
    split; intros [hp | hq].
    + left. exact (proj1 IHHsub1 hp).
    + right. exact (proj1 IHHsub2 hq).
    + left. exact (proj2 IHHsub1 hp).
    + right. exact (proj2 IHHsub2 hq).
  - match goal with
    | Hpsi : qfree_form psi, Hchi : qfree_form chi |- _ =>
        specialize (IHHsub1 Hpsi);
        specialize (IHHsub2 Hchi)
    end.
    split; intros h hp.
    + apply (proj1 IHHsub2).
      apply h.
      exact (proj2 IHHsub1 hp).
    + apply (proj2 IHHsub2).
      apply h.
      exact (proj1 IHHsub1 hp).
  - match goal with
    | Hpsi : qfree_form psi, Hchi : qfree_form chi |- _ =>
        specialize (IHHsub1 Hpsi);
        specialize (IHHsub2 Hchi)
    end.
    split; intros [hl hr].
    + split.
      * intro hp.
        apply (proj1 IHHsub2).
        apply hl.
        exact (proj2 IHHsub1 hp).
      * intro hq.
        apply (proj1 IHHsub1).
        apply hr.
        exact (proj2 IHHsub2 hq).
    + split.
      * intro hp.
        apply (proj2 IHHsub2).
        apply hl.
        exact (proj1 IHHsub1 hp).
      * intro hq.
        apply (proj2 IHHsub1).
        apply hr.
        exact (proj1 IHHsub2 hq).
Qed.

Theorem formula_substitution_law :
  formula_substitution_statement.
Proof.
  unfold formula_substitution_statement.
  intros phi phi' c E sigma Hsub.
  revert c E.
  induction Hsub; intros c E; simpl.
  - split; intro H; exact H.
  - split; intro H; exact H.
  - rewrite (proj1 term_substitution_semantics).
    rewrite (proj1 term_substitution_semantics).
    split; intro H; exact H.
  - rewrite (proj1 (proj2 term_substitution_semantics)).
    split; intro H; exact H.
  - rewrite (proj1 (proj2 term_substitution_semantics)).
    split; intro H; exact H.
  - specialize (IHHsub c E).
    split; intros H Hpsi.
    + apply H. exact (proj2 IHHsub Hpsi).
    + apply H. exact (proj1 IHHsub Hpsi).
  - specialize (IHHsub1 c E).
    specialize (IHHsub2 c E).
    split; intros [Hpsi Hchi].
    + split; [exact (proj1 IHHsub1 Hpsi) | exact (proj1 IHHsub2 Hchi)].
    + split; [exact (proj2 IHHsub1 Hpsi) | exact (proj2 IHHsub2 Hchi)].
  - specialize (IHHsub1 c E).
    specialize (IHHsub2 c E).
    split; intros [Hpsi | Hchi].
    + left. exact (proj1 IHHsub1 Hpsi).
    + right. exact (proj1 IHHsub2 Hchi).
    + left. exact (proj2 IHHsub1 Hpsi).
    + right. exact (proj2 IHHsub2 Hchi).
  - specialize (IHHsub1 c E).
    specialize (IHHsub2 c E).
    split; intros H Hpsi.
    + apply (proj1 IHHsub2).
      apply H.
      exact (proj2 IHHsub1 Hpsi).
    + apply (proj2 IHHsub2).
      apply H.
      exact (proj1 IHHsub1 Hpsi).
  - specialize (IHHsub1 c E).
    specialize (IHHsub2 c E).
    split; intros [HL HR].
    + split.
      * intro Hpsi.
        apply (proj1 IHHsub2).
        apply HL.
        exact (proj2 IHHsub1 Hpsi).
      * intro Hchi.
        apply (proj1 IHHsub1).
        apply HR.
        exact (proj2 IHHsub2 Hchi).
    + split.
      * intro Hpsi.
        apply (proj2 IHHsub2).
        apply HL.
        exact (proj1 IHHsub1 Hpsi).
      * intro Hchi.
        apply (proj2 IHHsub1).
        apply HR.
        exact (proj1 IHHsub2 Hchi).
  - set (Xq := union_nat (fv_form psi)
      (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i]))) in *.
    set (jq := fresh Xq) in *.
    destruct (fresh_quantifier_conditions psi sigma i)
      as [Hjfv [Hjrfv [Hjsupp Hji]]].
    fold Xq in Hjfv, Hjrfv, Hjsupp, Hji.
    fold jq in Hjfv, Hjrfv, Hjsupp, Hji.
    split; intros Hall a.
    + pose proof (proj1 (IHHsub2 c (env_update E jq a)) (Hall a)) as Hrenamed.
      pose proof
        (proj1 (IHHsub1 c
          (env_subst (env_update E jq a) (subst_remove i sigma)))
          Hrenamed) as Hpsi.
      pose proof (quantified_env_agree psi sigma i jq a E
        Hjfv Hjrfv Hjsupp Hji) as Hagree.
      exact (proj1 (holds_env_agree psi c
        (env_subst
          (env_subst (env_update E jq a) (subst_remove i sigma))
          (rename_subst i jq))
        (env_update (env_subst E sigma) i a)
        Hagree) Hpsi).
    + pose proof (quantified_env_agree psi sigma i jq a E
        Hjfv Hjrfv Hjsupp Hji) as Hagree.
      pose proof (proj2 (holds_env_agree psi c
        (env_subst
          (env_subst (env_update E jq a) (subst_remove i sigma))
          (rename_subst i jq))
        (env_update (env_subst E sigma) i a)
        Hagree) (Hall a)) as Hpsi.
      pose proof
        (proj2 (IHHsub1 c
          (env_subst (env_update E jq a) (subst_remove i sigma)))
          Hpsi) as Hrenamed.
      exact (proj2 (IHHsub2 c (env_update E jq a)) Hrenamed).
  - set (Xq := union_nat (fv_form psi)
      (union_nat (subst_rfv sigma) (union_nat (subst_support sigma) [i]))) in *.
    set (jq := fresh Xq) in *.
    destruct (fresh_quantifier_conditions psi sigma i)
      as [Hjfv [Hjrfv [Hjsupp Hji]]].
    fold Xq in Hjfv, Hjrfv, Hjsupp, Hji.
    fold jq in Hjfv, Hjrfv, Hjsupp, Hji.
    split; intros [a Hex].
    + exists a.
      pose proof (proj1 (IHHsub2 c (env_update E jq a)) Hex) as Hrenamed.
      pose proof
        (proj1 (IHHsub1 c
          (env_subst (env_update E jq a) (subst_remove i sigma)))
          Hrenamed) as Hpsi.
      pose proof (quantified_env_agree psi sigma i jq a E
        Hjfv Hjrfv Hjsupp Hji) as Hagree.
      exact (proj1 (holds_env_agree psi c
        (env_subst
          (env_subst (env_update E jq a) (subst_remove i sigma))
          (rename_subst i jq))
        (env_update (env_subst E sigma) i a)
        Hagree) Hpsi).
    + exists a.
      pose proof (quantified_env_agree psi sigma i jq a E
        Hjfv Hjrfv Hjsupp Hji) as Hagree.
      pose proof (proj2 (holds_env_agree psi c
        (env_subst
          (env_subst (env_update E jq a) (subst_remove i sigma))
          (rename_subst i jq))
        (env_update (env_subst E sigma) i a)
        Hagree) Hex) as Hpsi.
      pose proof
        (proj2 (IHHsub1 c
          (env_subst (env_update E jq a) (subst_remove i sigma)))
          Hpsi) as Hrenamed.
      exact (proj2 (IHHsub2 c (env_update E jq a)) Hrenamed).
Qed.

Theorem sub_form_rel_functional :
  forall phi sigma phi1 phi2,
    sub_form_rel phi sigma phi1 ->
    sub_form_rel phi sigma phi2 ->
    phi1 = phi2.
Proof.
  intros phi sigma phi1 phi2 H1.
  revert phi2.
  induction H1; intros phi2 H2; inversion H2; subst; try reflexivity.
  - f_equal. eapply IHsub_form_rel; eauto.
  - f_equal; [eapply IHsub_form_rel1 | eapply IHsub_form_rel2]; eauto.
  - f_equal; [eapply IHsub_form_rel1 | eapply IHsub_form_rel2]; eauto.
  - f_equal; [eapply IHsub_form_rel1 | eapply IHsub_form_rel2]; eauto.
  - f_equal; [eapply IHsub_form_rel1 | eapply IHsub_form_rel2]; eauto.
  - assert (renamed = renamed0) by (eapply IHsub_form_rel1; eauto).
    subst renamed0.
    assert (body' = body'0) by (eapply IHsub_form_rel2; eauto).
    subst body'0.
    reflexivity.
  - assert (renamed = renamed0) by (eapply IHsub_form_rel1; eauto).
    subst renamed0.
    assert (body' = body'0) by (eapply IHsub_form_rel2; eauto).
    subst body'0.
    reflexivity.
Qed.

Definition term_denotation
    (rho : IEnv) (I : interpretation_function) (t : tm)
    : interpretation_function := 
  I_c (tau (kappa I) (rho_kappa rho) t).

Definition evaluation_structure_preservation_law : Prop :=
  forall rho sigma t c,
    Theta (term_denotation rho (I_c c) (sub_tm t sigma)) =
    Theta (term_denotation (rho_sigma rho sigma) (I_c c) t).

Theorem evaluation_structure_preservation :
  evaluation_structure_preservation_law.
Proof.
  unfold evaluation_structure_preservation_law.
  intros rho sigma t c.
  unfold term_denotation, Theta, O_c, kappa, rho_sigma, rho_kappa.
  simpl.
  now rewrite item_substitution_theorem.
Qed.

Record GuardedTraceInterpreterSystem : Type := {
  gti_signature : signature;
  gti_external_relation :
    nsym Sig -> code -> clist -> Prop;

  gti_pure_term : Type;
  gti_guard_formula : Type;
  gti_term : Type;
  gti_trace : Type;
  gti_formula : Type;
  gti_code : Type;
  gti_environment : Type;

  gti_wf_pure_term : ptm -> Prop;
  gti_wf_guard_formula : gform -> Prop;
  gti_wf_term : tm -> Prop;
  gti_wf_trace : trace -> Prop;
  gti_wf_formula : form -> Prop;

  gti_base_code : code;
  gti_comp_code : code -> code -> code;
  gti_guard_code : code -> gfacts -> code;
  gti_app_code : fsym Sig -> clist -> code;
  gti_fact_code : gsym Sig -> clist -> code;
  gti_act : code -> code -> code;
  gti_facts : code -> gfacts;
  gti_act_base_law : forall a, act CBase a = a;
  gti_act_comp_law : forall c d a, act (CComp c d) a = act d (act c a);
  gti_act_guard_law : forall c B a, act (CGuard c B) a = act c a;
  gti_facts_comp_law :
    forall c d, facts (CComp c d) = gfacts_app (facts c) (facts d);
  gti_facts_guard_law :
    forall c B, facts (CGuard c B) = gfacts_app (facts c) B;

  gti_tau_p : code -> env -> ptm -> code;
  gti_real : code -> env -> gform -> gfacts;
  gti_tau : code -> env -> tm -> code;
  gti_trace_eval : code -> env -> trace -> code;
  gti_holds : code -> env -> form -> Prop;
  gti_tau_p_guard :
    forall p c B E, tau_p (CGuard c B) E p = tau_p c E p;
  gti_real_guard_satisfies :
    forall gamma c E,
      holds (CGuard c (real c E gamma)) E (gform_to_form gamma);
  gti_trace_realized : code -> env -> trace -> Prop;
  gti_finite_trace_guard_realization :
    forall c E q, trace_realized c E q;

  gti_interpretation_function : Type;
  gti_I_c : code -> interpretation_function;
  gti_kappa : interpretation_function -> code;
  gti_eta : code -> interpretation_function;
  gti_kappa_eta : forall c, kappa (eta c) = c;
  gti_I_c_extensional :
    forall c d, I_c c = I_c d <-> c = d;

  gti_interpretation_environment : Type;
  gti_rho_kappa : IEnv -> env;
  gti_rho_apply :
    IEnv -> interpretation_function -> nat -> interpretation_function;
  gti_rho_apply_guard :
    forall rho c B i,
      rho_apply rho (I_c (CGuard c B)) i =
      rho_apply rho (I_c c) i;

  gti_operation_interpretation : Type;
  gti_O_c : code -> operation_interpretation;
  gti_Theta : interpretation_function -> operation_interpretation;
  gti_Theta_inv : operation_interpretation -> interpretation_function;
  gti_Theta_left_inverse :
    forall I, Theta_inv (Theta I) = I;
  gti_Theta_right_inverse :
    forall O, Theta (Theta_inv O) = O;
  gti_Theta_diamond_hom :
    forall I J,
      Theta (diamond_I I J) = diamond_O (Theta I) (Theta J);
  gti_code_action_composition :
    forall c d a, act (CComp c d) a = act d (act c a);

  gti_free_vars_pure_term : ptm -> list nat;
  gti_free_vars_guard_formula : gform -> list nat;
  gti_free_vars_term : tm -> list nat;
  gti_free_vars_trace : trace -> list nat;
  gti_free_vars_formula : form -> list nat;
  gti_substitution : Type;
  gti_subst_lookup : subst -> nat -> ptm;
  gti_env_subst : env -> subst -> env;
  gti_sub_pure_term : ptm -> subst -> ptm;
  gti_sub_guard_formula : gform -> subst -> gform;
  gti_sub_term : tm -> subst -> tm;
  gti_sub_trace : trace -> subst -> trace;
  gti_sub_formula : form -> subst -> form -> Prop;
  gti_term_substitution_semantics :
    forall t c E sigma,
      tau c E (sub_tm t sigma) = tau c (env_subst E sigma) t;
  gti_formula_substitution_semantics :
    formula_substitution_statement;
  gti_sub_formula_functional :
    forall phi sigma phi1 phi2,
      sub_form_rel phi sigma phi1 ->
      sub_form_rel phi sigma phi2 ->
      phi1 = phi2;

  gti_rho_sigma : IEnv -> subst -> IEnv;
  gti_rho_sigma_kappa :
    forall rho sigma c i,
      env_val (rho_kappa (rho_sigma rho sigma)) c i =
      env_val (env_subst (rho_kappa rho) sigma) c i;
  gti_term_denotation :
    IEnv -> interpretation_function -> tm -> interpretation_function;
  gti_evaluation_structure_preservation :
    evaluation_structure_preservation_law
}.

Definition GTI_1128 : GuardedTraceInterpreterSystem := {|
  gti_signature := Sig;
  gti_external_relation := Delta;

  gti_pure_term := ptm;
  gti_guard_formula := gform;
  gti_term := tm;
  gti_trace := trace;
  gti_formula := form;
  gti_code := code;
  gti_environment := env;

  gti_wf_pure_term := wf_ptm;
  gti_wf_guard_formula := wf_gform;
  gti_wf_term := wf_tm;
  gti_wf_trace := wf_trace;
  gti_wf_formula := wf_form;

  gti_base_code := CBase;
  gti_comp_code := CComp;
  gti_guard_code := CGuard;
  gti_app_code := CApp;
  gti_fact_code := FactCode;
  gti_act := act;
  gti_facts := facts;
  gti_act_base_law := act_base;
  gti_act_comp_law := act_comp;
  gti_act_guard_law := act_guard;
  gti_facts_comp_law := facts_comp;
  gti_facts_guard_law := facts_guard;

  gti_tau_p := tau_p;
  gti_real := real;
  gti_tau := tau;
  gti_trace_eval := trace_eval;
  gti_holds := holds;
  gti_tau_p_guard := tau_p_guard_term;
  gti_real_guard_satisfies := real_guard_satisfies;
  gti_trace_realized := trace_realized;
  gti_finite_trace_guard_realization := finite_trace_guard_realization;

  gti_interpretation_function := interpretation_function;
  gti_I_c := I_c;
  gti_kappa := kappa;
  gti_eta := eta;
  gti_kappa_eta := kappa_eta;
  gti_I_c_extensional := I_c_eq_iff;

  gti_interpretation_environment := IEnv;
  gti_rho_kappa := rho_kappa;
  gti_rho_apply := rho_apply;
  gti_rho_apply_guard := rho_apply_guard;

  gti_operation_interpretation := operation_interpretation;
  gti_O_c := O_c;
  gti_Theta := Theta;
  gti_Theta_inv := Theta_inv;
  gti_Theta_left_inverse := Theta_left_inverse;
  gti_Theta_right_inverse := Theta_right_inverse;
  gti_Theta_diamond_hom := Theta_diamond_hom;
  gti_code_action_composition := code_action_composition;

  gti_free_vars_pure_term := fv_ptm;
  gti_free_vars_guard_formula := fv_gform;
  gti_free_vars_term := fv_tm;
  gti_free_vars_trace := fv_trace;
  gti_free_vars_formula := fv_form;
  gti_substitution := subst;
  gti_subst_lookup := subst_lookup;
  gti_env_subst := env_subst;
  gti_sub_pure_term := sub_ptm;
  gti_sub_guard_formula := sub_gform;
  gti_sub_term := sub_tm;
  gti_sub_trace := sub_trace;
  gti_sub_formula := sub_form_rel;
  gti_term_substitution_semantics := item_substitution_theorem;
  gti_formula_substitution_semantics := formula_substitution_law;
  gti_sub_formula_functional := sub_form_rel_functional;

  gti_rho_sigma := rho_sigma;
  gti_rho_sigma_kappa := rho_sigma_kappa;
  gti_term_denotation := term_denotation;
  gti_evaluation_structure_preservation := evaluation_structure_preservation
|}.

End System.

End GuardedTraceInterpreter1128.
