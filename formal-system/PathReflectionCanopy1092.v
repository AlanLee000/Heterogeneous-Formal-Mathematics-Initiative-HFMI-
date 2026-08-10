From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.

Import ListNotations.

Module PathReflectionCanopy1092.

Record ms_signature : Type := {
  SortSym : Type;
  RelSym : Type;
  FunSym : Type;
  ConstSym : Type;
  rel_type : RelSym -> list SortSym;
  fun_dom : FunSym -> list SortSym;
  fun_cod : FunSym -> SortSym;
  const_type : ConstSym -> SortSym
}.

Record rooted_tree : Type := {
  Node : Type;
  node_eq_dec : forall x y : Node, {x = y} + {x <> y};
  root : Node;
  leq : Node -> Node -> Prop;
  leq_refl : forall x, leq x x;
  leq_trans : forall x y z, leq x y -> leq y z -> leq x z;
  leq_antisym : forall x y, leq x y -> leq y x -> x = y;
  root_leq : forall x, leq root x;
  predecessor_linear :
    forall v x y, leq x v -> leq y v -> leq x y \/ leq y x;
  no_infinite_descending :
    forall f : nat -> Node,
      ~ (forall n, leq (f (S n)) (f n) /\ f (S n) <> f n)
}.

Section System.

Variable T : rooted_tree.

Definition node : Type := Node T.
Definition root_node : node := root T.
Definition le (x y : node) : Prop := leq T x y.
Definition ordinary (v : node) : Prop := v <> root_node.
Definition strict (x y : node) : Prop := le x y /\ x <> y.
Definition visible (u v : node) : Prop :=
  ordinary u /\ ordinary v /\ strict u v.
Definition incompatible (u v : node) : Prop :=
  ordinary u /\ ordinary v /\ ~ le u v /\ ~ le v u.

Record object_signature_family : Type := {
  obj_sig : node -> ms_signature;
  object_symbols_disjoint :
    forall u v, ordinary u -> ordinary v -> u <> v -> Prop;
  code_sorts_distinct :
    forall u v, ordinary u -> ordinary v -> u <> v -> Prop;
  code_domains_disjoint :
    forall u v, ordinary u -> ordinary v -> u <> v -> Prop
}.

Theorem no_infinite_strict_descent :
  forall f : nat -> node, ~ (forall n, strict (f (S n)) (f n)).
Proof.
  intros f H.
  exact (no_infinite_descending T f H).
Qed.

Lemma strict_irrefl : forall v, ~ strict v v.
Proof.
  intros v [Hle Hneq]. apply Hneq. reflexivity.
Qed.

Lemma strict_trans : forall x y z, strict x y -> strict y z -> strict x z.
Proof.
  intros x y z [Hxy Hneqxy] [Hyz Hneqyz].
  split.
  - exact (leq_trans T x y z Hxy Hyz).
  - intro Heq. subst z.
    apply Hneqxy.
    apply leq_antisym; auto.
Qed.

Lemma incompatible_distinct : forall u v, incompatible u v -> u <> v.
Proof.
  intros u v [_ [_ [Hnle _]]] Heq.
  subst v. apply Hnle. apply leq_refl.
Qed.

Lemma incompatible_not_visible_left :
  forall u v, incompatible u v -> ~ visible u v.
Proof.
  intros u v [_ [_ [Hnle _]]] [_ [_ [Hle _]]].
  exact (Hnle Hle).
Qed.

Lemma incompatible_not_visible_right :
  forall u v, incompatible u v -> ~ visible v u.
Proof.
  intros u v [_ [_ [_ Hnle]]] [_ [_ [Hle _]]].
  exact (Hnle Hle).
Qed.

Definition code_sort_in_local (u v : node) : Prop :=
  ordinary u /\ ordinary v /\ le u v.
Definition sent_pred_in_local (u v : node) : Prop :=
  code_sort_in_local u v.
Definition prov_pred_in_local (u v : node) : Prop :=
  code_sort_in_local u v.
Definition truth_pred_in_local (u v : node) : Prop :=
  ordinary u /\ ordinary v /\ strict u v.
Definition q_fun_in_local (r u v : node) : Prop :=
  ordinary r /\ ordinary u /\ ordinary v /\ strict r u /\ le u v.
Definition gtr_in_local (_ : node) : Prop := False.
Definition local_truth_in_canopy (_ _ : node) : Prop := False.

Lemma no_self_truth_symbol :
  forall v, ~ truth_pred_in_local v v.
Proof.
  intros v [_ [_ Hstrict]]. exact (strict_irrefl v Hstrict).
Qed.

Lemma branch_has_no_left_symbols :
  forall u v,
    incompatible u v ->
    ~ code_sort_in_local u v /\
    ~ sent_pred_in_local u v /\
    ~ prov_pred_in_local u v /\
    ~ truth_pred_in_local u v.
Proof.
  intros u v Hinc.
  destruct Hinc as [Hou [Hov [Hnle _]]].
  repeat split; intros H.
  - destruct H as [_ [_ Hle]]. exact (Hnle Hle).
  - destruct H as [_ [_ Hle]]. exact (Hnle Hle).
  - destruct H as [_ [_ Hle]]. exact (Hnle Hle).
  - destruct H as [_ [_ [Hle _]]]. exact (Hnle Hle).
Qed.

Lemma branch_has_no_right_truth :
  forall u v,
    incompatible u v -> ~ truth_pred_in_local v u.
Proof.
  intros u v [_ [_ [_ Hnle]]] [_ [_ [Hle _]]].
  exact (Hnle Hle).
Qed.

Inductive term : Type :=
| TVar : nat -> term
| TObjectCode : node -> nat -> term
| TCanopyCode : nat -> term
| TInjected : node -> term -> term
| TNodeConst : node -> term
| TQ : node -> node -> term -> term.

Inductive atom : Type :=
| AEq : term -> term -> atom
| AObjRel : nat -> list term -> atom
| ASent : node -> term -> atom
| AProv : node -> term -> atom
| ATr : node -> node -> term -> atom
| APath : node -> node -> atom
| AIncomp : node -> node -> atom
| ALangReg : node -> term -> atom
| AThReg : node -> term -> atom
| ARegSent : node -> term -> atom
| ARegProv : node -> term -> atom
| AGTr : node -> term -> atom.

Inductive formula : Type :=
| FAtom : atom -> formula
| FNeg : formula -> formula
| FAnd : formula -> formula -> formula
| FOr : formula -> formula -> formula
| FImp : formula -> formula -> formula
| FIff : formula -> formula -> formula
| FForall : nat -> formula -> formula
| FExists : nat -> formula -> formula.

Fixpoint last_formula (xs : list formula) : option formula :=
  match xs with
  | [] => None
  | [x] => Some x
  | _ :: rest => last_formula rest
  end.

Fixpoint wf_local_term (v : node) (t : term) : Prop :=
  match t with
  | TVar _ => True
  | TObjectCode u _ => code_sort_in_local u v
  | TCanopyCode _ => False
  | TInjected _ _ => False
  | TNodeConst _ => False
  | TQ u r s => q_fun_in_local r u v /\ wf_local_term v s
  end.

Fixpoint wf_canopy_term (t : term) : Prop :=
  match t with
  | TVar _ => True
  | TObjectCode u _ => ordinary u
  | TCanopyCode _ => True
  | TInjected u s => ordinary u /\ wf_canopy_term s
  | TNodeConst u => ordinary u
  | TQ u r s => strict r u /\ wf_canopy_term s
  end.

Definition registered_code_term (t : term) : Prop :=
  (exists u s, t = TInjected u s /\ ordinary u /\ wf_canopy_term s) \/
  (exists i, t = TVar i).

Fixpoint all_local_terms (v : node) (ts : list term) : Prop :=
  match ts with
  | [] => True
  | t :: rest => wf_local_term v t /\ all_local_terms v rest
  end.

Fixpoint all_canopy_terms (ts : list term) : Prop :=
  match ts with
  | [] => True
  | t :: rest => wf_canopy_term t /\ all_canopy_terms rest
  end.

Definition wf_local_atom (v : node) (a : atom) : Prop :=
  match a with
  | AEq s t => wf_local_term v s /\ wf_local_term v t
  | AObjRel _ ts => all_local_terms v ts
  | ASent u t => sent_pred_in_local u v /\ wf_local_term v t
  | AProv u t => prov_pred_in_local u v /\ wf_local_term v t
  | ATr owner u t => owner = v /\ truth_pred_in_local u v /\ wf_local_term v t
  | APath _ _ => False
  | AIncomp _ _ => False
  | ALangReg _ _ => False
  | AThReg _ _ => False
  | ARegSent _ _ => False
  | ARegProv _ _ => False
  | AGTr _ _ => False
  end.

Definition wf_canopy_atom (a : atom) : Prop :=
  match a with
  | AEq s t => wf_canopy_term s /\ wf_canopy_term t
  | AObjRel _ ts => all_canopy_terms ts
  | ASent _ _ => False
  | AProv _ _ => False
  | ATr _ _ _ => False
  | APath u v => ordinary u /\ ordinary v
  | AIncomp u v => ordinary u /\ ordinary v
  | ALangReg u c => ordinary u /\ wf_canopy_term c
  | AThReg u c => ordinary u /\ wf_canopy_term c
  | ARegSent u c => ordinary u /\ registered_code_term c
  | ARegProv u c => ordinary u /\ registered_code_term c
  | AGTr u c => ordinary u /\ registered_code_term c
  end.

Fixpoint wf_local_formula (v : node) (phi : formula) : Prop :=
  match phi with
  | FAtom a => wf_local_atom v a
  | FNeg p => wf_local_formula v p
  | FAnd p q | FOr p q | FImp p q | FIff p q =>
      wf_local_formula v p /\ wf_local_formula v q
  | FForall _ p | FExists _ p => wf_local_formula v p
  end.

Fixpoint wf_canopy_formula (phi : formula) : Prop :=
  match phi with
  | FAtom a => wf_canopy_atom a
  | FNeg p => wf_canopy_formula p
  | FAnd p q | FOr p q | FImp p q | FIff p q =>
      wf_canopy_formula p /\ wf_canopy_formula q
  | FForall _ p | FExists _ p => wf_canopy_formula p
  end.

Variable code_of : node -> formula -> nat.

Hypothesis code_of_injective :
  forall v phi psi,
    wf_local_formula v phi ->
    wf_local_formula v psi ->
    code_of v phi = code_of v psi ->
    phi = psi.

Variable tarski_fragment : node -> node -> formula -> Prop.

Hypothesis tarski_fragment_sound :
  forall u v phi,
    tarski_fragment u v phi ->
    truth_pred_in_local u v /\ wf_local_formula u phi.

Lemma gtr_not_local :
  forall v n c, ~ wf_local_atom v (AGTr n c).
Proof. intros v n c H. exact H. Qed.

Lemma local_truth_not_canopy :
  forall v u t, ~ wf_canopy_atom (ATr v u t).
Proof. intros v u t H. exact H. Qed.

Lemma local_self_truth_atom_not_wf :
  forall v t, ~ wf_local_atom v (ATr v v t).
Proof.
  intros v t [_ [Htruth _]].
  exact (no_self_truth_symbol v Htruth).
Qed.

Lemma canopy_root_gtr_not_wf :
  forall c, ~ wf_canopy_atom (AGTr root_node c).
Proof.
  intros c [Hordinary _]. apply Hordinary. reflexivity.
Qed.

Lemma canopy_own_code_not_registered :
  forall c, ~ registered_code_term (TCanopyCode c).
Proof.
  intros c Hreg.
  destruct Hreg as [[u [s [H _]]] | [i H]]; discriminate H.
Qed.

Lemma canopy_own_code_not_gtr :
  forall n c, ~ wf_canopy_atom (AGTr n (TCanopyCode c)).
Proof.
  intros n c [_ Hreg].
  exact (canopy_own_code_not_registered c Hreg).
Qed.

Fixpoint lift_term_local (u v : node) (t : term) : term :=
  match t with
  | TVar i => TVar i
  | TObjectCode a k => TObjectCode a k
  | TCanopyCode k => TCanopyCode k
  | TInjected a s => TInjected a (lift_term_local u v s)
  | TNodeConst a => TNodeConst a
  | TQ a r s => TQ a r (lift_term_local u v s)
  end.

Definition lift_atom_local (u v : node) (a : atom) : atom :=
  match a with
  | AEq s t => AEq (lift_term_local u v s) (lift_term_local u v t)
  | AObjRel k ts => AObjRel k (map (lift_term_local u v) ts)
  | ASent a t => ASent a (lift_term_local u v t)
  | AProv a t => AProv a (lift_term_local u v t)
  | ATr owner subject t =>
      if node_eq_dec T owner u
      then ATr v subject (lift_term_local u v t)
      else ATr owner subject (lift_term_local u v t)
  | APath a b => APath a b
  | AIncomp a b => AIncomp a b
  | ALangReg a t => ALangReg a (lift_term_local u v t)
  | AThReg a t => AThReg a (lift_term_local u v t)
  | ARegSent a t => ARegSent a (lift_term_local u v t)
  | ARegProv a t => ARegProv a (lift_term_local u v t)
  | AGTr a t => AGTr a (lift_term_local u v t)
  end.

Fixpoint lift_formula_local (u v : node) (phi : formula) : formula :=
  match phi with
  | FAtom a => FAtom (lift_atom_local u v a)
  | FNeg p => FNeg (lift_formula_local u v p)
  | FAnd p q => FAnd (lift_formula_local u v p) (lift_formula_local u v q)
  | FOr p q => FOr (lift_formula_local u v p) (lift_formula_local u v q)
  | FImp p q => FImp (lift_formula_local u v p) (lift_formula_local u v q)
  | FIff p q => FIff (lift_formula_local u v p) (lift_formula_local u v q)
  | FForall x p => FForall x (lift_formula_local u v p)
  | FExists x p => FExists x (lift_formula_local u v p)
  end.

Fixpoint canopy_term (t : term) : term :=
  match t with
  | TVar i => TVar i
  | TObjectCode u k => TObjectCode u k
  | TCanopyCode k => TCanopyCode k
  | TInjected u s => TInjected u (canopy_term s)
  | TNodeConst u => TNodeConst u
  | TQ u r s => TQ u r (canopy_term s)
  end.

Definition canopy_atom (v : node) (a : atom) : atom :=
  match a with
  | AEq s t => AEq (canopy_term s) (canopy_term t)
  | AObjRel k ts => AObjRel k (map canopy_term ts)
  | ASent u t => ARegSent u (TInjected u (canopy_term t))
  | AProv u t => ARegProv u (TInjected u (canopy_term t))
  | ATr owner u t =>
      if node_eq_dec T owner v
      then AGTr u (TInjected u (canopy_term t))
      else AGTr u (TInjected u (canopy_term t))
  | APath u w => APath u w
  | AIncomp u w => AIncomp u w
  | ALangReg u t => ALangReg u (canopy_term t)
  | AThReg u t => AThReg u (canopy_term t)
  | ARegSent u t => ARegSent u (canopy_term t)
  | ARegProv u t => ARegProv u (canopy_term t)
  | AGTr u t => AGTr u (canopy_term t)
  end.

Fixpoint canopy_formula (v : node) (phi : formula) : formula :=
  match phi with
  | FAtom a => FAtom (canopy_atom v a)
  | FNeg p => FNeg (canopy_formula v p)
  | FAnd p q => FAnd (canopy_formula v p) (canopy_formula v q)
  | FOr p q => FOr (canopy_formula v p) (canopy_formula v q)
  | FImp p q => FImp (canopy_formula v p) (canopy_formula v q)
  | FIff p q => FIff (canopy_formula v p) (canopy_formula v q)
  | FForall x p => FForall x (canopy_formula v p)
  | FExists x p => FExists x (canopy_formula v p)
  end.

Definition quote_code (v : node) (k : nat) : term := TObjectCode v k.
Definition quote_formula (v : node) (phi : formula) : term :=
  quote_code v (code_of v phi).
Definition q_code (u r : node) (x : term) : term := TQ u r x.
Definition tr_atom (v u : node) (x : term) : formula :=
  FAtom (ATr v u x).
Definition sent_atom (u : node) (x : term) : formula :=
  FAtom (ASent u x).
Definition prov_atom (u : node) (x : term) : formula :=
  FAtom (AProv u x).
Definition gtr_atom (u : node) (x : term) : formula :=
  FAtom (AGTr u x).

Definition weak_comp_formula (r u v : node) : formula :=
  FForall 0
    (FImp (sent_atom r (TVar 0))
      (FImp
        (tr_atom v u (q_code u r (TVar 0)))
        (tr_atom v r (TVar 0)))).

Definition q_code_axiom_formula (r u : node) (phi : formula) : formula :=
  FAtom
    (AEq
      (q_code u r (quote_formula r phi))
      (quote_formula u (tr_atom u r (quote_formula r phi)))).

Definition q_sent_formula (r u : node) : formula :=
  FForall 0
    (FImp
      (sent_atom r (TVar 0))
      (sent_atom u (q_code u r (TVar 0)))).

Definition tarski_formula (u v : node) (phi : formula) : formula :=
  FIff
    (tr_atom v u (quote_formula u phi))
    (lift_formula_local u v phi).

Definition global_truth_registered_formula (u : node) : formula :=
  FForall 0
    (FImp
      (gtr_atom u (TVar 0))
      (FAtom (ARegSent u (TVar 0)))).

Definition global_truth_schema_formula (v : node) (phi : formula) : formula :=
  FIff
    (gtr_atom v (TInjected v (canopy_term (quote_formula v phi))))
    (canopy_formula v phi).

Lemma quote_formula_injective :
  forall v phi psi,
    wf_local_formula v phi ->
    wf_local_formula v psi ->
    quote_formula v phi = quote_formula v psi ->
    phi = psi.
Proof.
  intros v phi psi Hphi Hpsi Heq.
  unfold quote_formula, quote_code in Heq.
  injection Heq as Hcode.
  exact (code_of_injective v phi psi Hphi Hpsi Hcode).
Qed.

Inductive local_axiom (v : node) : formula -> Prop :=
| AxCodeDistinct :
    forall u a b,
      code_sort_in_local u v -> a <> b ->
      local_axiom v (FNeg (FAtom (AEq (quote_code u a) (quote_code u b))))
| AxSynSentQuote :
    forall u phi,
      code_sort_in_local u v ->
      wf_local_formula u phi ->
      local_axiom v (sent_atom u (quote_formula u phi))
| AxSynProvSent :
    forall u,
      prov_pred_in_local u v ->
      local_axiom v
        (FForall 0 (FImp (prov_atom u (TVar 0)) (sent_atom u (TVar 0))))
| AxSynTruthSent :
    forall u,
      truth_pred_in_local u v ->
      local_axiom v
        (FForall 0 (FImp (tr_atom v u (TVar 0)) (sent_atom u (TVar 0))))
| AxReflection :
    forall u,
      truth_pred_in_local u v ->
      local_axiom v
        (FForall 0
          (FImp
            (FAnd (sent_atom u (TVar 0)) (prov_atom u (TVar 0)))
            (tr_atom v u (TVar 0))))
| AxCodeQ :
    forall r u phi,
      q_fun_in_local r u v ->
      wf_local_formula r phi ->
      local_axiom v (q_code_axiom_formula r u phi)
| AxSynQSent :
    forall r u,
      q_fun_in_local r u v ->
      local_axiom v (q_sent_formula r u)
| AxTarski :
    forall u phi,
      tarski_fragment u v phi ->
      local_axiom v (tarski_formula u v phi)
| AxCompWeak :
    forall r u,
      strict r u -> strict u v ->
      local_axiom v (weak_comp_formula r u v).

Inductive canopy_axiom : formula -> Prop :=
| AxPath :
    forall u v, strict u v -> canopy_axiom (FAtom (APath u v))
| AxNoPath :
    forall u v, ~ strict u v -> canopy_axiom (FNeg (FAtom (APath u v)))
| AxIncomp :
    forall u v, incompatible u v -> canopy_axiom (FAtom (AIncomp u v))
| AxNoIncomp :
    forall u v, ~ incompatible u v -> canopy_axiom (FNeg (FAtom (AIncomp u v)))
| AxNodeDistinct :
    forall u v,
      ordinary u ->
      ordinary v ->
      u <> v ->
      canopy_axiom (FNeg (FAtom (AEq (TNodeConst u) (TNodeConst v))))
| AxRegSentQuote :
    forall v phi,
      ordinary v ->
      wf_local_formula v phi ->
      canopy_axiom
        (FAtom (ARegSent v (TInjected v (canopy_term (quote_formula v phi)))))
| AxGlobalTruthSchema :
    forall v phi,
      ordinary v ->
      wf_local_formula v phi ->
      canopy_axiom (global_truth_schema_formula v phi)
| AxGTrTyped :
    forall u,
      ordinary u ->
      canopy_axiom (global_truth_registered_formula u).

Lemma local_tarski_axiom :
  forall u v phi,
    tarski_fragment u v phi ->
    local_axiom v (tarski_formula u v phi).
Proof.
  intros u v phi Hfrag. exact (AxTarski v u phi Hfrag).
Qed.

Lemma global_truth_typed_axiom :
  forall u,
    ordinary u ->
    canopy_axiom (global_truth_registered_formula u).
Proof.
  intros u Hou. exact (AxGTrTyped u Hou).
Qed.

Lemma global_truth_schema_axiom :
  forall v phi,
    ordinary v ->
    wf_local_formula v phi ->
    canopy_axiom (global_truth_schema_formula v phi).
Proof.
  intros v phi Hov Hwf. exact (AxGlobalTruthSchema v phi Hov Hwf).
Qed.

Lemma no_incomp_axiom :
  forall u v,
    ~ incompatible u v ->
    canopy_axiom (FNeg (FAtom (AIncomp u v))).
Proof.
  intros u v H. exact (AxNoIncomp u v H).
Qed.

Lemma path_composition_axiom :
  forall r u v,
    strict r u ->
    strict u v ->
    local_axiom v (weak_comp_formula r u v).
Proof.
  intros r u v Hru Huv. apply AxCompWeak; auto.
Qed.

Definition comp_symbols_available (r u v : node) : Prop :=
  truth_pred_in_local u v /\ truth_pred_in_local r v /\ q_fun_in_local r u v.

Lemma comp_symbols_from_path :
  forall r u v,
    ordinary r -> ordinary u -> ordinary v ->
    strict r u -> strict u v ->
    comp_symbols_available r u v.
Proof.
  intros r u v Hor Hou Hov Hru Huv.
  unfold comp_symbols_available, truth_pred_in_local, q_fun_in_local.
  split.
  - exact (conj Hou (conj Hov Huv)).
  - split.
    + exact (conj Hor (conj Hov (strict_trans r u v Hru Huv))).
    + destruct Huv as [Hle _].
      exact (conj Hor (conj Hou (conj Hov (conj Hru Hle)))).
Qed.

Lemma no_comp_symbols_without_path :
  forall r u v,
    ~ (strict r u /\ strict u v) ->
    ~ comp_symbols_available r u v.
Proof.
  intros r u v Hno [Htruthuv [_ Hq]].
  destruct Htruthuv as [_ [_ Huv]].
  destruct Hq as [_ [_ [_ [Hru _]]]].
  apply Hno. split; assumption.
Qed.

Record path_model : Type := {
  local_sat : node -> formula -> Prop;
  canopy_sat : formula -> Prop;
  local_truth_correct :
    forall u v phi,
      truth_pred_in_local u v ->
      wf_local_formula u phi ->
      local_sat v (tr_atom v u (quote_formula u phi)) <->
      local_sat u phi;
  global_truth_correct :
    forall v phi,
      ordinary v ->
      wf_local_formula v phi ->
      canopy_sat (gtr_atom v (TInjected v (canopy_term (quote_formula v phi)))) <->
      local_sat v phi;
  local_axioms_valid :
    forall v phi, local_axiom v phi -> local_sat v phi;
  canopy_axioms_valid :
    forall phi, canopy_axiom phi -> canopy_sat phi
}.

Definition local_interface_sat (_ : node) (phi : formula) : Prop :=
  match phi with
  | FAtom (AGTr _ _) => False
  | _ => True
  end.

Definition canopy_interface_sat (phi : formula) : Prop :=
  match phi with
  | FAtom (ATr _ _ _) => False
  | _ => True
  end.

Lemma wf_local_formula_interface_true :
  forall v phi,
    wf_local_formula v phi -> local_interface_sat v phi.
Proof.
  intros v phi Hwf.
  destruct phi; cbn [local_interface_sat]; try exact I.
  destruct a; cbn [wf_local_formula wf_local_atom] in Hwf;
    cbn [local_interface_sat]; try exact I.
  exact Hwf.
Qed.

Lemma wf_canopy_formula_interface_true :
  forall phi,
    wf_canopy_formula phi -> canopy_interface_sat phi.
Proof.
  intros phi Hwf.
  destruct phi; cbn [canopy_interface_sat]; try exact I.
  destruct a; cbn [wf_canopy_formula wf_canopy_atom] in Hwf;
    cbn [canopy_interface_sat]; try exact I.
  exact Hwf.
Qed.

Definition interface_path_model : path_model.
Proof.
  refine {|
    local_sat := local_interface_sat;
    canopy_sat := canopy_interface_sat;
    local_truth_correct := _;
    global_truth_correct := _;
    local_axioms_valid := _;
    canopy_axioms_valid := _
  |}.
  - intros u v phi Htruth Hwf.
    split; intro H.
    + exact (wf_local_formula_interface_true u phi Hwf).
    + exact I.
  - intros v phi Hordinary Hwf.
    split; intro H.
    + exact (wf_local_formula_interface_true v phi Hwf).
    + exact I.
  - intros v phi Hax.
    destruct Hax; cbn [local_interface_sat tr_atom sent_atom prov_atom
      q_code_axiom_formula q_sent_formula tarski_formula weak_comp_formula];
      exact I.
  - intros phi Hax.
    destruct Hax; cbn [canopy_interface_sat
      global_truth_schema_formula global_truth_registered_formula gtr_atom];
      exact I.
Defined.

Definition rejected_local_global_truth_atom : formula :=
  FAtom (AGTr root_node (TVar 0)).

Theorem interface_path_model_nontrivial :
  local_sat interface_path_model root_node
      (FNeg rejected_local_global_truth_atom) /\
  ~ local_sat interface_path_model root_node
      rejected_local_global_truth_atom.
Proof.
  split.
  - change True. exact I.
  - change (~ False). tauto.
Qed.

Inductive derives_local (v : node) (Gamma : list formula) : formula -> Prop :=
| DLHyp : forall phi, In phi Gamma -> derives_local v Gamma phi
| DLAx : forall phi, local_axiom v phi -> derives_local v Gamma phi
| DLMP : forall p q,
    derives_local v Gamma p ->
    derives_local v Gamma (FImp p q) ->
    derives_local v Gamma q
| DLGen : forall x p,
    derives_local v Gamma p ->
    derives_local v Gamma (FForall x p)
| DLAlpha : forall p q,
    p = q -> derives_local v Gamma p -> derives_local v Gamma q.

Inductive derives_canopy (Gamma : list formula) : formula -> Prop :=
| DCHyp : forall phi, In phi Gamma -> derives_canopy Gamma phi
| DCAx : forall phi, canopy_axiom phi -> derives_canopy Gamma phi
| DCMP : forall p q,
    derives_canopy Gamma p ->
    derives_canopy Gamma (FImp p q) ->
    derives_canopy Gamma q
| DCGen : forall x p,
    derives_canopy Gamma p ->
    derives_canopy Gamma (FForall x p)
| DCAlpha : forall p q,
    p = q -> derives_canopy Gamma p -> derives_canopy Gamma q.

Definition local_proof_certificate (v : node) (Gamma : list formula)
    (pi : list formula) (phi : formula) : Prop :=
  pi <> [] /\ last_formula pi = Some phi /\ Forall (derives_local v Gamma) pi.

Definition canopy_proof_certificate (Gamma : list formula)
    (pi : list formula) (phi : formula) : Prop :=
  pi <> [] /\ last_formula pi = Some phi /\ Forall (derives_canopy Gamma) pi.

Record path_reflection_canopy_system : Type := {
  system_tree : rooted_tree;
  system_local_axiom : node -> formula -> Prop;
  system_canopy_axiom : formula -> Prop;
  system_local_derives : node -> list formula -> formula -> Prop;
  system_canopy_derives : list formula -> formula -> Prop;
  system_interface_model : path_model;
  system_interface_model_nontrivial :
    local_sat system_interface_model root_node
        (FNeg rejected_local_global_truth_atom) /\
    ~ local_sat system_interface_model root_node
        rejected_local_global_truth_atom;
  system_truth_boundary :
    forall u v, truth_pred_in_local u v <-> ordinary u /\ ordinary v /\ strict u v;
  system_no_local_gtr : forall v n c, ~ wf_local_atom v (AGTr n c);
  system_no_canopy_local_truth : forall v u t, ~ wf_canopy_atom (ATr v u t)
}.

Definition final_system : path_reflection_canopy_system :=
  {| system_tree := T;
     system_local_axiom := local_axiom;
     system_canopy_axiom := canopy_axiom;
     system_local_derives := derives_local;
     system_canopy_derives := derives_canopy;
     system_interface_model := interface_path_model;
     system_interface_model_nontrivial := interface_path_model_nontrivial;
     system_truth_boundary := fun u v => conj (fun H => H) (fun H => H);
     system_no_local_gtr := gtr_not_local;
     system_no_canopy_local_truth := local_truth_not_canopy |}.

Definition linear_order (I : Type) (lt : I -> I -> Prop) : Prop :=
  forall x y, x <> y -> lt x y \/ lt y x.

Definition boundary_preserving {I : Type} (lt : I -> I -> Prop)
    (h : node -> I) : Prop :=
  forall u v, strict u v <-> lt (h u) (h v).

Definition injective_map {I : Type} (h : node -> I) : Prop :=
  forall x y, h x = h y -> x = y.

Theorem no_linear_compression_for_branching :
  forall (I : Type) (lt : I -> I -> Prop) (h : node -> I),
    (exists a b, incompatible a b) ->
    linear_order I lt ->
    injective_map h ->
    boundary_preserving lt h ->
    False.
Proof.
  intros I lt h [a [b Hab]] Hlin Hinj Hpres.
  assert (a <> b) as Habneq by (apply incompatible_distinct; exact Hab).
  assert (h a <> h b) as Hhab.
  { intro Heq. apply Habneq. apply Hinj. exact Heq. }
  destruct (Hlin (h a) (h b) Hhab) as [Hlt | Hlt].
  - apply (incompatible_not_visible_left a b Hab).
    unfold visible.
    destruct Hab as [Hoa [Hob _]].
    repeat split; auto.
    apply Hpres. exact Hlt.
  - apply (incompatible_not_visible_right a b Hab).
    unfold visible.
    destruct Hab as [Hoa [Hob _]].
    repeat split; auto.
    apply Hpres. exact Hlt.
Qed.

End System.

End PathReflectionCanopy1092.
