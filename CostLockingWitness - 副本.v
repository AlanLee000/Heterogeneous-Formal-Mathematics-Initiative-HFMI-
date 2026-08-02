From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.
From Coq Require Import Sorting.Permutation.

Import ListNotations.

Module CostLockingWitness.

Record cost_structure : Type := {
  cost_carrier : Type;
  cost_zero : cost_carrier;
  cost_plus : cost_carrier -> cost_carrier -> cost_carrier;
  cost_le : cost_carrier -> cost_carrier -> Prop;
  cost_plus_assoc :
    forall a b c, cost_plus a (cost_plus b c) =
                  cost_plus (cost_plus a b) c;
  cost_plus_comm : forall a b, cost_plus a b = cost_plus b a;
  cost_plus_zero_r : forall a, cost_plus a cost_zero = a;
  cost_plus_zero_l : forall a, cost_plus cost_zero a = a;
  cost_le_refl : forall a, cost_le a a;
  cost_le_antisym : forall a b, cost_le a b -> cost_le b a -> a = b;
  cost_le_trans : forall a b c, cost_le a b -> cost_le b c -> cost_le a c;
  cost_plus_monotone_r :
    forall a b c, cost_le a b -> cost_le (cost_plus a c) (cost_plus b c);
  cost_zero_min : forall a, cost_le cost_zero a
}.

Arguments cost_zero {_}.
Arguments cost_plus {_} _ _.
Arguments cost_le {_} _ _.

Definition positive_cost (K : cost_structure) : Type :=
  { c : cost_carrier K | c <> cost_zero }.

Fixpoint ncostmul {K : cost_structure} (n : nat)
    (c : cost_carrier K) : cost_carrier K :=
  match n with
  | 0 => cost_zero
  | S m => cost_plus (ncostmul m c) c
  end.

Lemma ncostmul_zero :
  forall (K : cost_structure) (c : cost_carrier K), ncostmul 0 c = cost_zero.
Proof. reflexivity. Qed.

Lemma ncostmul_succ :
  forall (K : cost_structure) n (c : cost_carrier K),
    ncostmul (S n) c = cost_plus (ncostmul n c) c.
Proof. reflexivity. Qed.

Record signature : Type := {
  sig_sort : Type;
  sig_vfun : Type;
  sig_cfun : Type;
  sig_vpred : Type;
  sig_cpred : Type;
  sig_vfun_dom : sig_vfun -> list sig_sort;
  sig_vfun_cod : sig_vfun -> sig_sort;
  sig_cfun_dom : sig_cfun -> list sig_sort;
  sig_cfun_cod : sig_cfun -> sig_sort;
  sig_vpred_dom : sig_vpred -> list sig_sort;
  sig_cpred_dom : sig_cpred -> list sig_sort
}.

Section System.

Context (K : cost_structure).
Context (L : signature).

Definition sort : Type := sig_sort L.
Definition ctx : Type := list sort.
Definition lock_name : Type := nat.
Definition responsibility_name : Type := nat.
Definition evidence_name : Type := nat.

Inductive cfun_symbol : Type :=
| CFunVerified : sig_vfun L -> cfun_symbol
| CFunClaimed : sig_cfun L -> cfun_symbol.

Definition cfun_dom (f : cfun_symbol) : list sort :=
  match f with
  | CFunVerified g => sig_vfun_dom L g
  | CFunClaimed g => sig_cfun_dom L g
  end.

Definition cfun_cod (f : cfun_symbol) : sort :=
  match f with
  | CFunVerified g => sig_vfun_cod L g
  | CFunClaimed g => sig_cfun_cod L g
  end.

Inductive cpred_symbol : Type :=
| CPredVerified : sig_vpred L -> cpred_symbol
| CPredClaimed : sig_cpred L -> cpred_symbol.

Definition cpred_dom (P : cpred_symbol) : list sort :=
  match P with
  | CPredVerified Q => sig_vpred_dom L Q
  | CPredClaimed Q => sig_cpred_dom L Q
  end.

Inductive vterm : Type :=
| VVar : nat -> vterm
| VFun : sig_vfun L -> list vterm -> vterm.

Inductive vformula : Type :=
| VPred : sig_vpred L -> list vterm -> vformula
| VBot : vformula
| VAnd : vformula -> vformula -> vformula
| VImp : vformula -> vformula -> vformula
| VAll : sort -> vformula -> vformula
| VEx : sort -> vformula -> vformula.

Inductive locked_existence : Type :=
| Lock : lock_name -> sort -> cformula -> locked_existence
with cterm : Type :=
| CVar : nat -> cterm
| CFun : cfun_symbol -> list cterm -> cterm
| CWitness :
    locked_existence -> responsibility_name -> positive_cost K -> cterm
with cformula : Type :=
| CPred : cpred_symbol -> list cterm -> cformula
| CBot : cformula
| CAnd : cformula -> cformula -> cformula
| CImp : cformula -> cformula -> cformula
| CAll : sort -> cformula -> cformula
| CEx : sort -> cformula -> cformula.

Scheme locked_existence_ind' := Induction for locked_existence Sort Prop
with cterm_ind' := Induction for cterm Sort Prop
with cformula_ind' := Induction for cformula Sort Prop.

Definition locked_sort (E : locked_existence) : sort :=
  match E with
  | Lock _ sigma _ => sigma
  end.

Definition locked_body (E : locked_existence) : cformula :=
  match E with
  | Lock _ _ A => A
  end.

Fixpoint iota_term (t : vterm) : cterm :=
  match t with
  | VVar i => CVar i
  | VFun f args => CFun (CFunVerified f) (map iota_term args)
  end.

Fixpoint jmath (A : vformula) : cformula :=
  match A with
  | VPred P args => CPred (CPredVerified P) (map iota_term args)
  | VBot => CBot
  | VAnd B C => CAnd (jmath B) (jmath C)
  | VImp B C => CImp (jmath B) (jmath C)
  | VAll sigma B => CAll sigma (jmath B)
  | VEx sigma B => CEx sigma (jmath B)
  end.

Lemma jmath_bot : jmath VBot = CBot.
Proof. reflexivity. Qed.

Lemma jmath_and :
  forall A B, jmath (VAnd A B) = CAnd (jmath A) (jmath B).
Proof. reflexivity. Qed.

Lemma jmath_imp :
  forall A B, jmath (VImp A B) = CImp (jmath A) (jmath B).
Proof. reflexivity. Qed.

Lemma jmath_all :
  forall sigma A, jmath (VAll sigma A) = CAll sigma (jmath A).
Proof. reflexivity. Qed.

Lemma jmath_ex :
  forall sigma A, jmath (VEx sigma A) = CEx sigma (jmath A).
Proof. reflexivity. Qed.

Lemma witness_not_iota :
  forall (E : locked_existence) alpha c t,
    CWitness E alpha c <> iota_term t.
Proof.
  intros E alpha c t.
  destruct t; simpl; discriminate.
Qed.

Inductive transparent_term : cterm -> vterm -> Prop :=
| TransparentVar :
    forall i, transparent_term (CVar i) (VVar i)
| TransparentFun :
    forall f cargs vargs,
      Forall2 transparent_term cargs vargs ->
      transparent_term (CFun (CFunVerified f) cargs) (VFun f vargs).

Definition opaque_claimed_term (t : cterm) : Prop :=
  forall s, ~ transparent_term t s.

Definition address : Type := list nat.

Inductive term_occurrence : cterm -> address -> cterm -> Prop :=
| TermOccHere :
    forall t, term_occurrence t [] t
| TermOccFun :
    forall f args i arg p t,
      nth_error args i = Some arg ->
      term_occurrence arg p t ->
      term_occurrence (CFun f args) (i :: p) t.

Inductive formula_term_occurrence : cformula -> address -> cterm -> Prop :=
| FormulaOccPred :
    forall P args i arg p t,
      nth_error args i = Some arg ->
      term_occurrence arg p t ->
      formula_term_occurrence (CPred P args) (i :: p) t
| FormulaOccAndLeft :
    forall A B p t,
      formula_term_occurrence A p t ->
      formula_term_occurrence (CAnd A B) (0 :: p) t
| FormulaOccAndRight :
    forall A B p t,
      formula_term_occurrence B p t ->
      formula_term_occurrence (CAnd A B) (1 :: p) t
| FormulaOccImpLeft :
    forall A B p t,
      formula_term_occurrence A p t ->
      formula_term_occurrence (CImp A B) (0 :: p) t
| FormulaOccImpRight :
    forall A B p t,
      formula_term_occurrence B p t ->
      formula_term_occurrence (CImp A B) (1 :: p) t
| FormulaOccAllBody :
    forall sigma A p t,
      formula_term_occurrence A p t ->
      formula_term_occurrence (CAll sigma A) (0 :: p) t
| FormulaOccExBody :
    forall sigma A p t,
      formula_term_occurrence A p t ->
      formula_term_occurrence (CEx sigma A) (0 :: p) t.

Definition address_prefix (p q : address) : Prop :=
  exists r, q = p ++ r.

Definition address_strict_prefix (p q : address) : Prop :=
  address_prefix p q /\ p <> q.

Definition externally_extractable
    (A : cformula) (p : address) (t : cterm) : Prop :=
  formula_term_occurrence A p t.

Definition maximal_external_opaque_occurrence
    (A : cformula) (p : address) (t : cterm) : Prop :=
  formula_term_occurrence A p t /\
  opaque_claimed_term t /\
  externally_extractable A p t /\
  forall q u,
    formula_term_occurrence A q u ->
    opaque_claimed_term u ->
    externally_extractable A q u ->
    address_strict_prefix q p ->
    False.

Inductive term_abs (opaque_params : list cterm) : cterm -> vterm -> Prop :=
| TermAbsTransparent :
    forall t s,
      transparent_term t s ->
      term_abs opaque_params t s
| TermAbsOpaque :
    forall i t,
      nth_error opaque_params i = Some t ->
      opaque_claimed_term t ->
      term_abs opaque_params t (VVar i)
| TermAbsVerifiedFun :
    forall f cargs vargs,
      Forall2 (term_abs opaque_params) cargs vargs ->
      term_abs opaque_params (CFun (CFunVerified f) cargs) (VFun f vargs).

Inductive formula_abs (opaque_params : list cterm)
    : cformula -> vformula -> Prop :=
| FormulaAbsPred :
    forall P cargs vargs,
      Forall2 (term_abs opaque_params) cargs vargs ->
      formula_abs opaque_params
        (CPred (CPredVerified P) cargs) (VPred P vargs)
| FormulaAbsBot :
    formula_abs opaque_params CBot VBot
| FormulaAbsAnd :
    forall A B Av Bv,
      formula_abs opaque_params A Av ->
      formula_abs opaque_params B Bv ->
      formula_abs opaque_params (CAnd A B) (VAnd Av Bv)
| FormulaAbsImp :
    forall A B Av Bv,
      formula_abs opaque_params A Av ->
      formula_abs opaque_params B Bv ->
      formula_abs opaque_params (CImp A B) (VImp Av Bv)
| FormulaAbsAll :
    forall sigma A Av,
      formula_abs opaque_params A Av ->
      formula_abs opaque_params (CAll sigma A) (VAll sigma Av)
| FormulaAbsEx :
    forall sigma A Av,
      formula_abs opaque_params A Av ->
      formula_abs opaque_params (CEx sigma A) (VEx sigma Av).

Definition abs_pair (A B : cformula)
    (opaque_params : list cterm) (Av Bv : vformula) : Prop :=
  formula_abs opaque_params A Av /\ formula_abs opaque_params B Bv.

Definition addressed_opaque_params : Type := list (address * cterm).

Definition addressed_terms (params : addressed_opaque_params) : list cterm :=
  map snd params.

Lemma nth_error_addressed_terms :
  forall params i p t,
    nth_error params i = Some (p, t) ->
    nth_error (addressed_terms params) i = Some t.
Proof.
  induction params as [|[q u] rest IH]; intros i p t H.
  - destruct i; discriminate.
  - destruct i as [|i]; simpl in *.
    + inversion H. reflexivity.
    + apply IH with (p := p). exact H.
Qed.

Inductive term_abs_at (params : addressed_opaque_params)
    : address -> cterm -> vterm -> Prop :=
| TermAbsAtParam :
    forall p i t,
      nth_error params i = Some (p, t) ->
      opaque_claimed_term t ->
      term_abs_at params p t (VVar i)
| TermAbsAtTransparent :
    forall p t s,
      transparent_term t s ->
      term_abs_at params p t s
| TermAbsAtVerifiedFun :
    forall p f cargs vargs,
      term_list_abs_at params p 0 cargs vargs ->
      term_abs_at params p (CFun (CFunVerified f) cargs) (VFun f vargs)
with term_list_abs_at (params : addressed_opaque_params)
    : address -> nat -> list cterm -> list vterm -> Prop :=
| TermListAbsAtNil :
    forall p i,
      term_list_abs_at params p i [] []
| TermListAbsAtCons :
    forall p i c cs v vs,
      term_abs_at params (p ++ [i]) c v ->
      term_list_abs_at params p (S i) cs vs ->
      term_list_abs_at params p i (c :: cs) (v :: vs)
with formula_abs_at (params : addressed_opaque_params)
    : address -> cformula -> vformula -> Prop :=
| FormulaAbsAtPred :
    forall p P cargs vargs,
      term_list_abs_at params p 0 cargs vargs ->
      formula_abs_at params p
        (CPred (CPredVerified P) cargs) (VPred P vargs)
| FormulaAbsAtBot :
    forall p,
      formula_abs_at params p CBot VBot
| FormulaAbsAtAnd :
    forall p A B Av Bv,
      formula_abs_at params (p ++ [0]) A Av ->
      formula_abs_at params (p ++ [1]) B Bv ->
      formula_abs_at params p (CAnd A B) (VAnd Av Bv)
| FormulaAbsAtImp :
    forall p A B Av Bv,
      formula_abs_at params (p ++ [0]) A Av ->
      formula_abs_at params (p ++ [1]) B Bv ->
      formula_abs_at params p (CImp A B) (VImp Av Bv)
| FormulaAbsAtAll :
    forall p sigma A Av,
      formula_abs_at params (p ++ [0]) A Av ->
      formula_abs_at params p (CAll sigma A) (VAll sigma Av)
| FormulaAbsAtEx :
    forall p sigma A Av,
      formula_abs_at params (p ++ [0]) A Av ->
      formula_abs_at params p (CEx sigma A) (VEx sigma Av).

Scheme term_abs_at_ind' := Induction for term_abs_at Sort Prop
with term_list_abs_at_ind' := Induction for term_list_abs_at Sort Prop
with formula_abs_at_ind' := Induction for formula_abs_at Sort Prop.

Theorem term_abs_at_forget :
  forall params p t v,
    term_abs_at params p t v ->
    term_abs (addressed_terms params) t v
with term_list_abs_at_forget :
  forall params p i cargs vargs,
    term_list_abs_at params p i cargs vargs ->
    Forall2 (term_abs (addressed_terms params)) cargs vargs
with formula_abs_at_forget :
  forall params p A Av,
    formula_abs_at params p A Av ->
    formula_abs (addressed_terms params) A Av.
Proof.
  - intros params p t v H.
    induction H using term_abs_at_ind'
      with
        (P0 := fun p i cargs vargs H =>
          Forall2 (term_abs (addressed_terms params)) cargs vargs)
        (P1 := fun p A Av H =>
          formula_abs (addressed_terms params) A Av).
    all: try solve
      [ eapply TermAbsOpaque; eauto using nth_error_addressed_terms
      | eapply TermAbsTransparent; eauto
      | eapply TermAbsVerifiedFun; eauto
      | eapply FormulaAbsPred; eauto
      | eapply FormulaAbsBot; eauto
      | eapply FormulaAbsAnd; eauto
      | eapply FormulaAbsImp; eauto
      | eapply FormulaAbsAll; eauto
      | eapply FormulaAbsEx; eauto
      | constructor; eauto ].
  - intros params p i cargs vargs H.
    induction H using term_list_abs_at_ind'
      with
        (P := fun p t v H =>
          term_abs (addressed_terms params) t v)
        (P1 := fun p A Av H =>
          formula_abs (addressed_terms params) A Av).
    all: try solve
      [ eapply TermAbsOpaque; eauto using nth_error_addressed_terms
      | eapply TermAbsTransparent; eauto
      | eapply TermAbsVerifiedFun; eauto
      | eapply FormulaAbsPred; eauto
      | eapply FormulaAbsBot; eauto
      | eapply FormulaAbsAnd; eauto
      | eapply FormulaAbsImp; eauto
      | eapply FormulaAbsAll; eauto
      | eapply FormulaAbsEx; eauto
      | constructor; eauto ].
  - intros params p A Av H.
    induction H using formula_abs_at_ind'
      with
        (P := fun p t v H =>
          term_abs (addressed_terms params) t v)
        (P0 := fun p i cargs vargs H =>
          Forall2 (term_abs (addressed_terms params)) cargs vargs).
    all: try solve
      [ eapply TermAbsOpaque; eauto using nth_error_addressed_terms
      | eapply TermAbsTransparent; eauto
      | eapply TermAbsVerifiedFun; eauto
      | eapply FormulaAbsPred; eauto
      | eapply FormulaAbsBot; eauto
      | eapply FormulaAbsAnd; eauto
      | eapply FormulaAbsImp; eauto
      | eapply FormulaAbsAll; eauto
      | eapply FormulaAbsEx; eauto
      | constructor; eauto ].
Qed.

Definition abs_pair_at (A B : cformula)
    (params : addressed_opaque_params) (Av Bv : vformula) : Prop :=
  formula_abs_at params [] A Av /\ formula_abs_at params [] B Bv.

Theorem abs_pair_at_forget :
  forall A B params Av Bv,
    abs_pair_at A B params Av Bv ->
    abs_pair A B (addressed_terms params) Av Bv.
Proof.
  intros A B params Av Bv [HA HB].
  split.
  - apply formula_abs_at_forget with (p := []). exact HA.
  - apply formula_abs_at_forget with (p := []). exact HB.
Qed.

Definition maximal_params_for_formula
    (A : cformula) (params : addressed_opaque_params) : Prop :=
  forall i p t,
    nth_error params i = Some (p, t) ->
    maximal_external_opaque_occurrence A p t.

Lemma maximal_params_are_opaque :
  forall A params i p t,
    maximal_params_for_formula A params ->
    nth_error params i = Some (p, t) ->
    opaque_claimed_term t.
Proof.
  intros A params i p t Hmax Hnth.
  exact (proj1 (proj2 (Hmax i p t Hnth))).
Qed.

Definition maximal_formula_abs
    (A : cformula) (params : addressed_opaque_params) (Av : vformula)
    : Prop :=
  maximal_params_for_formula A params /\
  formula_abs_at params [] A Av.

Theorem maximal_formula_abs_forget :
  forall A params Av,
    maximal_formula_abs A params Av ->
    formula_abs (addressed_terms params) A Av.
Proof.
  intros A params Av [_ Habs].
  apply formula_abs_at_forget with (p := []).
  exact Habs.
Qed.

Definition ctx_has (Xi : ctx) (x : nat) (sigma : sort) : Prop :=
  nth_error Xi x = Some sigma.

Inductive vterm_wf (Xi : ctx) : vterm -> sort -> Prop :=
| WFVVar :
    forall x sigma,
      ctx_has Xi x sigma ->
      vterm_wf Xi (VVar x) sigma
| WFVFun :
    forall f args,
      Forall2 (fun t sigma => vterm_wf Xi t sigma)
        args (sig_vfun_dom L f) ->
      vterm_wf Xi (VFun f args) (sig_vfun_cod L f).

Inductive vformula_wf (Xi : ctx) : vformula -> Prop :=
| WFVP :
    forall P args,
      Forall2 (fun t sigma => vterm_wf Xi t sigma)
        args (sig_vpred_dom L P) ->
      vformula_wf Xi (VPred P args)
| WFVB : vformula_wf Xi VBot
| WFVA :
    forall A B,
      vformula_wf Xi A ->
      vformula_wf Xi B ->
      vformula_wf Xi (VAnd A B)
| WFVI :
    forall A B,
      vformula_wf Xi A ->
      vformula_wf Xi B ->
      vformula_wf Xi (VImp A B)
| WFVAll :
    forall sigma A,
      vformula_wf (sigma :: Xi) A ->
      vformula_wf Xi (VAll sigma A)
| WFVEx :
    forall sigma A,
      vformula_wf (sigma :: Xi) A ->
      vformula_wf Xi (VEx sigma A).

Inductive cterm_wf (Xi : ctx) : cterm -> sort -> Prop :=
| WFCVar :
    forall x sigma,
      ctx_has Xi x sigma ->
      cterm_wf Xi (CVar x) sigma
| WFCFun :
    forall f args,
      Forall2 (fun t sigma => cterm_wf Xi t sigma) args (cfun_dom f) ->
      cterm_wf Xi (CFun f args) (cfun_cod f)
| WFCWitness :
    forall E alpha c,
      locked_wf Xi E ->
      cterm_wf Xi (CWitness E alpha c) (locked_sort E)
with cformula_wf (Xi : ctx) : cformula -> Prop :=
| WFCP :
    forall P args,
      Forall2 (fun t sigma => cterm_wf Xi t sigma) args (cpred_dom P) ->
      cformula_wf Xi (CPred P args)
| WFCB : cformula_wf Xi CBot
| WFCA :
    forall A B,
      cformula_wf Xi A ->
      cformula_wf Xi B ->
      cformula_wf Xi (CAnd A B)
| WFCI :
    forall A B,
      cformula_wf Xi A ->
      cformula_wf Xi B ->
      cformula_wf Xi (CImp A B)
| WFCAll :
    forall sigma A,
      cformula_wf (sigma :: Xi) A ->
      cformula_wf Xi (CAll sigma A)
| WFCEx :
    forall sigma A,
      cformula_wf (sigma :: Xi) A ->
      cformula_wf Xi (CEx sigma A)
with locked_wf (Xi : ctx) : locked_existence -> Prop :=
| WFCLock :
    forall eta sigma A,
      cformula_wf (sigma :: Xi) A ->
      locked_wf Xi (Lock eta sigma A).

Fixpoint vsubst_term (x : nat) (u : vterm) (t : vterm) : vterm :=
  match t with
  | VVar y => if Nat.eqb x y then u else VVar y
  | VFun f args => VFun f (map (vsubst_term x u) args)
  end.

Fixpoint vsubst_formula (x : nat) (u : vterm) (A : vformula) : vformula :=
  match A with
  | VPred P args => VPred P (map (vsubst_term x u) args)
  | VBot => VBot
  | VAnd B C => VAnd (vsubst_formula x u B) (vsubst_formula x u C)
  | VImp B C => VImp (vsubst_formula x u B) (vsubst_formula x u C)
  | VAll sigma B => VAll sigma (vsubst_formula (S x) u B)
  | VEx sigma B => VEx sigma (vsubst_formula (S x) u B)
  end.

Fixpoint csubst_term (x : nat) (u : cterm) (t : cterm) : cterm :=
  match t with
  | CVar y => if Nat.eqb x y then u else CVar y
  | CFun f args => CFun f (map (csubst_term x u) args)
  | CWitness E alpha c => CWitness (csubst_locked x u E) alpha c
  end
with csubst_formula (x : nat) (u : cterm) (A : cformula) : cformula :=
  match A with
  | CPred P args => CPred P (map (csubst_term x u) args)
  | CBot => CBot
  | CAnd B C => CAnd (csubst_formula x u B) (csubst_formula x u C)
  | CImp B C => CImp (csubst_formula x u B) (csubst_formula x u C)
  | CAll sigma B => CAll sigma (csubst_formula (S x) u B)
  | CEx sigma B => CEx sigma (csubst_formula (S x) u B)
  end
with csubst_locked (x : nat) (u : cterm)
    (E : locked_existence) : locked_existence :=
  match E with
  | Lock eta sigma A => Lock eta sigma (csubst_formula (S x) u A)
  end.

Fixpoint cterm_avoids (x : nat) (t : cterm) {struct t} : Prop :=
  match t with
  | CVar y => y <> x
  | CFun _ args =>
      let fix args_avoid (xs : list cterm) : Prop :=
        match xs with
        | [] => True
        | a :: rest => cterm_avoids x a /\ args_avoid rest
        end
      in args_avoid args
  | CWitness E _ _ => locked_avoids x E
  end
with cformula_avoids (x : nat) (A : cformula) {struct A} : Prop :=
  match A with
  | CPred _ args =>
      let fix args_avoid (xs : list cterm) : Prop :=
        match xs with
        | [] => True
        | a :: rest => cterm_avoids x a /\ args_avoid rest
        end
      in args_avoid args
  | CBot => True
  | CAnd B C => cformula_avoids x B /\ cformula_avoids x C
  | CImp B C => cformula_avoids x B /\ cformula_avoids x C
  | CAll _ B => cformula_avoids (S x) B
  | CEx _ B => cformula_avoids (S x) B
  end
with locked_avoids (x : nat) (E : locked_existence) {struct E} : Prop :=
  match E with
  | Lock _ _ A => cformula_avoids (S x) A
  end.

Record resp_atom : Type := Resp {
  resp_owner : responsibility_name;
  resp_claim : cformula;
  resp_charge : positive_cost K
}.

Definition resp_atom_avoids (x : nat) (rho : resp_atom) : Prop :=
  cformula_avoids x (resp_claim rho).

Definition ledger : Type := list resp_atom.
Definition ledger_empty : ledger := [].
Definition ledger_single (rho : resp_atom) : ledger := [rho].
Definition ledger_union (lambda mu : ledger) : ledger := lambda ++ mu.

Definition ledger_avoids (x : nat) (lambda : ledger) : Prop :=
  Forall (resp_atom_avoids x) lambda.

Definition ledger_le (lambda mu : ledger) : Prop :=
  exists extra, Permutation mu (lambda ++ extra).

Definition atom_cost (rho : resp_atom) : cost_carrier K :=
  proj1_sig (resp_charge rho).

Fixpoint ledger_cost (lambda : ledger) : cost_carrier K :=
  match lambda with
  | [] => cost_zero
  | rho :: rest => cost_plus (atom_cost rho) (ledger_cost rest)
  end.

Lemma ledger_le_refl : forall lambda, ledger_le lambda lambda.
Proof.
  intros lambda. exists []; rewrite app_nil_r. reflexivity.
Qed.

Lemma ledger_le_empty : forall lambda, ledger_le [] lambda.
Proof.
  intros lambda. exists lambda. reflexivity.
Qed.

Lemma ledger_le_trans :
  forall a b c, ledger_le a b -> ledger_le b c -> ledger_le a c.
Proof.
  intros a b c [eb Hab] [ec Hbc].
  exists (eb ++ ec).
  eapply Permutation_trans; [exact Hbc|].
  eapply Permutation_trans.
  - apply Permutation_app; [exact Hab|reflexivity].
  - repeat rewrite app_assoc. reflexivity.
Qed.

Lemma ledger_le_app :
  forall a b c d,
    ledger_le a b ->
    ledger_le c d ->
    ledger_le (ledger_union a c) (ledger_union b d).
Proof.
  intros a b c d [eb Hab] [ed Hcd].
  unfold ledger_union, ledger_le in *.
  exists (eb ++ ed).
  eapply Permutation_trans.
  - apply Permutation_app; [exact Hab|exact Hcd].
  - replace ((a ++ eb) ++ (c ++ ed)) with (a ++ ((eb ++ c) ++ ed))
      by (repeat rewrite app_assoc; reflexivity).
    replace ((a ++ c) ++ (eb ++ ed)) with (a ++ ((c ++ eb) ++ ed))
      by (repeat rewrite app_assoc; reflexivity).
    apply Permutation_app_head.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
Qed.

Record internal_ctx : Type := {
  int_objects : ctx;
  int_evidence : list cformula
}.

Definition empty_internal_ctx : internal_ctx := {|
  int_objects := [];
  int_evidence := []
|}.

Definition extend_object (Sigma : internal_ctx) (sigma : sort) : internal_ctx := {|
  int_objects := sigma :: int_objects Sigma;
  int_evidence := int_evidence Sigma
|}.

Definition extend_evidence (Sigma : internal_ctx) (A : cformula) : internal_ctx := {|
  int_objects := int_objects Sigma;
  int_evidence := A :: int_evidence Sigma
|}.

Context (base_proves : forall Xi : ctx, list vformula -> vformula -> Prop).

Inductive deriv_v (Xi : ctx) (Gamma : list vformula) : vformula -> Prop :=
| DVBase :
    forall A,
      base_proves Xi Gamma A ->
      deriv_v Xi Gamma A.

Definition conflict_by_verified
    (Xi : ctx) (Gamma : list vformula) (A B : cformula) : Prop :=
  exists opaque_params Av Bv,
    abs_pair A B opaque_params Av Bv /\
    deriv_v Xi Gamma (VImp (VAnd Av Bv) VBot).

Inductive deriv_c
    (Xi : ctx) (Gamma : list vformula)
    (Omega : list locked_existence) (Delta : list cformula)
    (Sigma : internal_ctx)
    : ledger -> cformula -> Type :=
| DCTruth :
    forall A,
      deriv_v Xi Gamma A ->
      deriv_c Xi Gamma Omega Delta Sigma ledger_empty (jmath A)
| DCPay :
    forall alpha A c,
      deriv_c Xi Gamma Omega Delta Sigma
        (ledger_single (Resp alpha A c)) A
| DCAssume :
    forall A,
      In A Delta ->
      deriv_c Xi Gamma Omega Delta Sigma ledger_empty A
| DCExt :
    forall lambda mu A,
      deriv_c Xi Gamma Omega Delta Sigma lambda A ->
      ledger_le lambda mu ->
      deriv_c Xi Gamma Omega Delta Sigma mu A
| DCAndIntro :
    forall lambda mu A B,
      deriv_c Xi Gamma Omega Delta Sigma lambda A ->
      deriv_c Xi Gamma Omega Delta Sigma mu B ->
      deriv_c Xi Gamma Omega Delta Sigma (ledger_union lambda mu) (CAnd A B)
| DCAndElimL :
    forall lambda A B,
      deriv_c Xi Gamma Omega Delta Sigma lambda (CAnd A B) ->
      deriv_c Xi Gamma Omega Delta Sigma lambda A
| DCAndElimR :
    forall lambda A B,
      deriv_c Xi Gamma Omega Delta Sigma lambda (CAnd A B) ->
      deriv_c Xi Gamma Omega Delta Sigma lambda B
| DCImpIntro :
    forall lambda A B,
      deriv_c Xi Gamma Omega (A :: Delta) Sigma lambda B ->
      deriv_c Xi Gamma Omega Delta Sigma lambda (CImp A B)
| DCImpElim :
    forall lambda mu A B,
      deriv_c Xi Gamma Omega Delta Sigma lambda (CImp A B) ->
      deriv_c Xi Gamma Omega Delta Sigma mu A ->
      deriv_c Xi Gamma Omega Delta Sigma (ledger_union lambda mu) B
| DCAllIntro :
    forall lambda sigma A,
      deriv_c (sigma :: Xi) Gamma Omega Delta Sigma lambda A ->
      deriv_c Xi Gamma Omega Delta Sigma lambda (CAll sigma A)
| DCAllElim :
    forall lambda sigma A t,
      deriv_c Xi Gamma Omega Delta Sigma lambda (CAll sigma A) ->
      deriv_c Xi Gamma Omega Delta Sigma lambda (csubst_formula 0 t A)
| DCExIntro :
    forall lambda sigma A t,
      deriv_c Xi Gamma Omega Delta Sigma lambda (csubst_formula 0 t A) ->
      deriv_c Xi Gamma Omega Delta Sigma lambda (CEx sigma A)
| DCExElim :
    forall lambda mu sigma A B,
      deriv_c Xi Gamma Omega Delta Sigma lambda (CEx sigma A) ->
      deriv_c (sigma :: Xi) Gamma Omega (A :: Delta) Sigma mu B ->
      cformula_avoids 0 B ->
      ledger_avoids 0 mu ->
      deriv_c Xi Gamma Omega Delta Sigma (ledger_union lambda mu) B
| DCPaidWitness :
    forall (E : locked_existence) alpha c,
      deriv_locked Xi Gamma Omega [] empty_internal_ctx E ->
      deriv_c Xi Gamma Omega Delta Sigma (ledger_single (Resp alpha (locked_body E) c))
        (csubst_formula 0 (CWitness E alpha c) (locked_body E))
with deriv_int
    (Xi : ctx) (Gamma : list vformula)
    (Omega : list locked_existence) (Delta : list cformula)
    (Sigma : internal_ctx)
    : cformula -> Type :=
| DITruth :
    forall A,
      deriv_v Xi Gamma A ->
      deriv_int Xi Gamma Omega Delta Sigma (jmath A)
| DIEvidence :
    forall A,
      In A (int_evidence Sigma) ->
      deriv_int Xi Gamma Omega Delta Sigma A
| DIAndIntro :
    forall A B,
      deriv_int Xi Gamma Omega Delta Sigma A ->
      deriv_int Xi Gamma Omega Delta Sigma B ->
      deriv_int Xi Gamma Omega Delta Sigma (CAnd A B)
| DIAndElimL :
    forall A B,
      deriv_int Xi Gamma Omega Delta Sigma (CAnd A B) ->
      deriv_int Xi Gamma Omega Delta Sigma A
| DIAndElimR :
    forall A B,
      deriv_int Xi Gamma Omega Delta Sigma (CAnd A B) ->
      deriv_int Xi Gamma Omega Delta Sigma B
| DIImpIntro :
    forall A B,
      deriv_int Xi Gamma Omega Delta (extend_evidence Sigma A) B ->
      deriv_int Xi Gamma Omega Delta Sigma (CImp A B)
| DIImpElim :
    forall A B,
      deriv_int Xi Gamma Omega Delta Sigma (CImp A B) ->
      deriv_int Xi Gamma Omega Delta Sigma A ->
      deriv_int Xi Gamma Omega Delta Sigma B
| DIAllIntro :
    forall sigma A,
      deriv_int Xi Gamma Omega Delta (extend_object Sigma sigma) A ->
      deriv_int Xi Gamma Omega Delta Sigma (CAll sigma A)
| DIAllElim :
    forall sigma A t,
      deriv_int Xi Gamma Omega Delta Sigma (CAll sigma A) ->
      deriv_int Xi Gamma Omega Delta Sigma (csubst_formula 0 t A)
| DIExIntro :
    forall sigma A t,
      deriv_int Xi Gamma Omega Delta Sigma (csubst_formula 0 t A) ->
      deriv_int Xi Gamma Omega Delta Sigma (CEx sigma A)
| DIExElim :
    forall sigma A C,
      deriv_int Xi Gamma Omega Delta Sigma (CEx sigma A) ->
      deriv_int Xi Gamma Omega Delta (extend_evidence (extend_object Sigma sigma) A) C ->
      cformula_avoids 0 C ->
      deriv_int Xi Gamma Omega Delta Sigma C
| DILockedOpen :
    forall eta sigma A C,
      deriv_locked Xi Gamma Omega Delta Sigma (Lock eta sigma A) ->
      deriv_int Xi Gamma Omega Delta (extend_evidence (extend_object Sigma sigma) A) C ->
      cformula_avoids 0 C ->
      deriv_int Xi Gamma Omega Delta Sigma C
with deriv_locked
    (Xi : ctx) (Gamma : list vformula)
    (Omega : list locked_existence) (Delta : list cformula)
    (Sigma : internal_ctx)
    : locked_existence -> Type :=
| DLAssume :
    forall E,
      In E Omega ->
      deriv_locked Xi Gamma Omega Delta Sigma E
| DLVerifiedExist :
    forall eta sigma A,
      deriv_v Xi Gamma (VEx sigma A) ->
      deriv_locked Xi Gamma Omega Delta Sigma (Lock eta sigma (jmath A))
| DLInternalPackage :
    forall theta sigma B t,
      deriv_int Xi Gamma Omega Delta Sigma (csubst_formula 0 t B) ->
      deriv_locked Xi Gamma Omega Delta Sigma (Lock theta sigma B)
| DLOpenToLocked :
    forall eta sigma A M,
      deriv_locked Xi Gamma Omega Delta Sigma (Lock eta sigma A) ->
      deriv_locked Xi Gamma Omega Delta (extend_evidence (extend_object Sigma sigma) A) M ->
      locked_avoids 0 M ->
      deriv_locked Xi Gamma Omega Delta Sigma M.

Scheme deriv_c_ind' := Induction for deriv_c Sort Prop
with deriv_int_ind' := Induction for deriv_int Sort Prop
with deriv_locked_ind' := Induction for deriv_locked Sort Prop.

Inductive deriv_disputed
    (Xi : ctx) (Gamma : list vformula) (Omega : list locked_existence)
    : ledger -> cformula -> cformula -> Type :=
| DDConflict :
    forall lambda mu A B,
      deriv_c Xi Gamma Omega [] empty_internal_ctx lambda A ->
      deriv_c Xi Gamma Omega [] empty_internal_ctx mu B ->
      conflict_by_verified Xi Gamma A B ->
      deriv_disputed Xi Gamma Omega (ledger_union lambda mu) A B.

Fixpoint responsibility_leaves
    {Xi Gamma Omega Delta Sigma lambda A}
    (D : deriv_c Xi Gamma Omega Delta Sigma lambda A) : ledger :=
  match D with
  | DCTruth _ _ _ _ _ _ _ => ledger_empty
  | DCPay _ _ _ _ _ alpha A c => ledger_single (Resp alpha A c)
  | DCAssume _ _ _ _ _ _ _ => ledger_empty
  | DCExt _ _ _ _ _ _ _ _ D0 _ => responsibility_leaves D0
  | DCAndIntro _ _ _ _ _ _ _ _ _ D1 D2 =>
      ledger_union (responsibility_leaves D1) (responsibility_leaves D2)
  | DCAndElimL _ _ _ _ _ _ _ _ D0 => responsibility_leaves D0
  | DCAndElimR _ _ _ _ _ _ _ _ D0 => responsibility_leaves D0
  | DCImpIntro _ _ _ _ _ _ _ _ D0 => responsibility_leaves D0
  | DCImpElim _ _ _ _ _ _ _ _ _ D1 D2 =>
      ledger_union (responsibility_leaves D1) (responsibility_leaves D2)
  | DCAllIntro _ _ _ _ _ _ _ _ D0 => responsibility_leaves D0
  | DCAllElim _ _ _ _ _ _ _ _ _ D0 => responsibility_leaves D0
  | DCExIntro _ _ _ _ _ _ _ _ _ D0 => responsibility_leaves D0
  | DCExElim _ _ _ _ _ _ _ _ _ _ D1 D2 _ _ =>
      ledger_union (responsibility_leaves D1) (responsibility_leaves D2)
  | DCPaidWitness _ _ _ _ _ E alpha c _ =>
      ledger_single (Resp alpha (locked_body E) c)
  end.

Theorem responsibility_propagation :
  forall Xi Gamma Omega Delta Sigma lambda A
    (D : deriv_c Xi Gamma Omega Delta Sigma lambda A),
    ledger_le (responsibility_leaves D) lambda.
Proof.
  intros Xi Gamma Omega Delta Sigma lambda A D.
  induction D; simpl.
  - apply ledger_le_refl.
  - apply ledger_le_refl.
  - apply ledger_le_refl.
  - eapply ledger_le_trans; eauto.
  - apply ledger_le_app; assumption.
  - assumption.
  - assumption.
  - assumption.
  - apply ledger_le_app; assumption.
  - assumption.
  - assumption.
  - assumption.
  - apply ledger_le_app; assumption.
  - apply ledger_le_refl.
Qed.

Theorem truth_layer_conservative :
  forall Xi Gamma A,
    deriv_v Xi Gamma A <-> base_proves Xi Gamma A.
Proof.
  intros Xi Gamma A; split.
  - intros H. destruct H as [A Hbase]. exact Hbase.
  - intros H. constructor. exact H.
Qed.

Definition public_v (Xi : ctx) (Gamma : list vformula) (A : vformula) :=
  deriv_v Xi Gamma A.

Definition public_c
    (Xi : ctx) (Gamma : list vformula) (lambda : ledger) (A : cformula) :=
  deriv_c Xi Gamma [] [] empty_internal_ctx lambda A.

Definition public_locked
    (Xi : ctx) (Gamma : list vformula) (E : locked_existence) :=
  deriv_locked Xi Gamma [] [] empty_internal_ctx E.

Definition public_disputed
    (Xi : ctx) (Gamma : list vformula)
    (lambda : ledger) (A B : cformula) :=
  deriv_disputed Xi Gamma [] lambda A B.

Theorem dispute_intro :
  forall Xi Gamma Omega lambda mu A B,
    deriv_c Xi Gamma Omega [] empty_internal_ctx lambda A ->
    deriv_c Xi Gamma Omega [] empty_internal_ctx mu B ->
    conflict_by_verified Xi Gamma A B ->
    deriv_disputed Xi Gamma Omega (ledger_union lambda mu) A B.
Proof.
  intros. constructor; assumption.
Qed.

Theorem paid_witness_derivable :
  forall Xi Gamma Omega E alpha c,
    deriv_locked Xi Gamma Omega [] empty_internal_ctx E ->
    deriv_c Xi Gamma Omega [] empty_internal_ctx
      (ledger_single (Resp alpha (locked_body E) c))
      (csubst_formula 0 (CWitness E alpha c) (locked_body E)).
Proof.
  intros Xi Gamma Omega E alpha c Hlock.
  apply DCPaidWitness. exact Hlock.
Qed.

Theorem paid_witness_charge_positive :
  forall (c : positive_cost K), proj1_sig c <> cost_zero.
Proof.
  intros c. exact (proj2_sig c).
Qed.

Record derivation_certificate : Type := {
  cert_statement : cformula;
  cert_ledger : ledger;
  cert_derivation :
    deriv_c [] [] [] [] empty_internal_ctx cert_ledger cert_statement
}.

Definition has_derivation_certificate (A : cformula) : Prop :=
  exists C, cert_statement C = A.

Record formal_system_tuple : Type := {
  fs_cost : cost_structure;
  fs_signature : signature;
  fs_vterm : Type;
  fs_cterm : Type;
  fs_vformula : Type;
  fs_cformula : Type;
  fs_locked : Type;
  fs_iota : vterm -> cterm;
  fs_jmath : vformula -> cformula;
  fs_ledger : Type;
  fs_ledger_union : ledger -> ledger -> ledger;
  fs_deriv_v : ctx -> list vformula -> vformula -> Type;
  fs_deriv_c :
    ctx -> list vformula -> list locked_existence -> list cformula ->
    internal_ctx -> ledger -> cformula -> Type;
  fs_deriv_int :
    ctx -> list vformula -> list locked_existence -> list cformula ->
    internal_ctx ->
    cformula -> Type;
  fs_deriv_locked :
    ctx -> list vformula -> list locked_existence -> list cformula ->
    internal_ctx ->
    locked_existence -> Type;
  fs_deriv_disputed :
    ctx -> list vformula -> list locked_existence ->
    ledger -> cformula -> cformula -> Type
}.

Definition canonical_formal_system_tuple : formal_system_tuple := {|
  fs_cost := K;
  fs_signature := L;
  fs_vterm := vterm;
  fs_cterm := cterm;
  fs_vformula := vformula;
  fs_cformula := cformula;
  fs_locked := locked_existence;
  fs_iota := iota_term;
  fs_jmath := jmath;
  fs_ledger := ledger;
  fs_ledger_union := ledger_union;
  fs_deriv_v := deriv_v;
  fs_deriv_c := deriv_c;
  fs_deriv_int := deriv_int;
  fs_deriv_locked := deriv_locked;
  fs_deriv_disputed := deriv_disputed
|}.

End System.

End CostLockingWitness.
