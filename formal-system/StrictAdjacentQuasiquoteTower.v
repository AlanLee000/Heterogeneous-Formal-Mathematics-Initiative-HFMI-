From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.PeanoNat.

Import ListNotations.

Module StrictAdjacentQuasiquoteTower.

Definition delta (k : nat) : nat :=
  match k with
  | 0 => 0
  | S j => j
  end.

Fixpoint list_last_error {A : Type} (xs : list A) : option A :=
  match xs with
  | [] => None
  | [x] => Some x
  | _ :: rest => list_last_error rest
  end.

Lemma delta_zero : delta 0 = 0.
Proof. reflexivity. Qed.

Lemma delta_pos : forall k, 0 < k -> delta k = k - 1.
Proof. destruct k; simpl; lia. Qed.

Lemma delta_succ : forall k, delta (S k) = k.
Proof. reflexivity. Qed.

Inductive ty : Type :=
| Ty0 : ty
| TyArr : ty -> ty -> ty.

Fixpoint rho (sigma : ty) : nat :=
  match sigma with
  | Ty0 => 0
  | TyArr s t => Nat.max (S (rho s)) (rho t)
  end.

Inductive sort : Type :=
| D : ty -> sort
| E : nat -> sort.

Definition ell_sort (s : sort) : nat :=
  match s with
  | D sigma => rho sigma
  | E k => delta k
  end.

Fixpoint all_sorts_le (k : nat) (xs : list sort) : Prop :=
  match xs with
  | [] => True
  | x :: rest => ell_sort x <= k /\ all_sorts_le k rest
  end.

Definition sort_in_language (n : nat) (s : sort) : Prop :=
  ell_sort s <= n.

Inductive fun_symbol : Type :=
| App : ty -> ty -> fun_symbol
| VarCode : nat -> sort -> nat -> fun_symbol
| FunCode : nat -> fun_symbol -> fun_symbol
| RelCode : nat -> rel_symbol -> fun_symbol
| EqCode : nat -> sort -> fun_symbol
| NegCode : nat -> fun_symbol
| ImpCode : nat -> fun_symbol
| AllCode : nat -> sort -> fun_symbol
| NilCode : nat -> fun_symbol
| ConsCode : nat -> fun_symbol
| SubCode : nat -> list sort -> list sort -> fun_symbol
with rel_symbol : Type :=
| TmRel : nat -> list sort -> sort -> rel_symbol
| FmRel : nat -> list sort -> rel_symbol
| SentRel : nat -> rel_symbol
| PrfRel : nat -> rel_symbol.

Scheme fun_symbol_ind' := Induction for fun_symbol Sort Prop
with rel_symbol_ind' := Induction for rel_symbol Sort Prop.

Definition ell_fun (f : fun_symbol) : nat :=
  match f with
  | App sigma tau => rho (TyArr sigma tau)
  | VarCode k _ _ => delta k
  | FunCode k _ => delta k
  | RelCode k _ => delta k
  | EqCode k _ => delta k
  | NegCode k => delta k
  | ImpCode k => delta k
  | AllCode k _ => delta k
  | NilCode k => delta k
  | ConsCode k => delta k
  | SubCode k _ _ => delta k
  end.

Definition ell_rel (R : rel_symbol) : nat :=
  match R with
  | TmRel k _ _ => delta k
  | FmRel k _ => delta k
  | SentRel k => delta k
  | PrfRel k => delta k
  end.

Definition arity_rel (R : rel_symbol) : nat :=
  match R with
  | TmRel _ _ _ => 1
  | FmRel _ _ => 1
  | SentRel _ => 1
  | PrfRel _ => 2
  end.

Fixpoint arity_fun (f : fun_symbol) : nat :=
  match f with
  | App _ _ => 2
  | VarCode _ _ _ => 0
  | FunCode _ g => arity_fun g
  | RelCode _ R => arity_rel R
  | EqCode _ _ => 2
  | NegCode _ => 1
  | ImpCode _ => 2
  | AllCode _ _ => 1
  | NilCode _ => 0
  | ConsCode _ => 2
  | SubCode _ _ Delta => S (length Delta)
  end.

Definition dom_fun (f : fun_symbol) : list sort :=
  match f with
  | App sigma tau => [D (TyArr sigma tau); D sigma]
  | VarCode _ _ _ => []
  | FunCode k g => repeat (E k) (arity_fun g)
  | RelCode k R => repeat (E k) (arity_rel R)
  | EqCode k _ => [E k; E k]
  | NegCode k => [E k]
  | ImpCode k => [E k; E k]
  | AllCode k _ => [E k]
  | NilCode _ => []
  | ConsCode k => [E k; E k]
  | SubCode k _ Delta => repeat (E k) (S (length Delta))
  end.

Definition cod_fun (f : fun_symbol) : sort :=
  match f with
  | App _ tau => D tau
  | VarCode k _ _ => E k
  | FunCode k _ => E k
  | RelCode k _ => E k
  | EqCode k _ => E k
  | NegCode k => E k
  | ImpCode k => E k
  | AllCode k _ => E k
  | NilCode k => E k
  | ConsCode k => E k
  | SubCode k _ _ => E k
  end.

Definition dom_rel (R : rel_symbol) : list sort :=
  match R with
  | TmRel k _ _ => [E k]
  | FmRel k _ => [E k]
  | SentRel k => [E k]
  | PrfRel k => [E k; E k]
  end.

Definition rel_wf (R : rel_symbol) : Prop :=
  match R with
  | TmRel k Gamma alpha => all_sorts_le k Gamma /\ ell_sort alpha <= k
  | FmRel k Gamma => all_sorts_le k Gamma
  | SentRel _ => True
  | PrfRel _ => True
  end.

Fixpoint fun_wf (f : fun_symbol) : Prop :=
  match f with
  | App _ _ => True
  | VarCode k alpha _ => ell_sort alpha <= k
  | FunCode k g => fun_wf g /\ ell_fun g <= k
  | RelCode k R => rel_wf R /\ ell_rel R <= k
  | EqCode k alpha => ell_sort alpha <= k
  | NegCode _ => True
  | ImpCode _ => True
  | AllCode k alpha => ell_sort alpha <= k
  | NilCode _ => True
  | ConsCode _ => True
  | SubCode k Gamma Delta => all_sorts_le k Gamma /\ all_sorts_le k Delta
  end.

Definition fun_in_language (n : nat) (f : fun_symbol) : Prop :=
  fun_wf f /\ ell_fun f <= n.

Definition rel_in_language (n : nat) (R : rel_symbol) : Prop :=
  rel_wf R /\ ell_rel R <= n.

Inductive raw_term (k : nat) : Type :=
| Var : sort -> nat -> raw_term k
| FApp : fun_symbol -> list (raw_term k) -> raw_term k.

Arguments Var {k}.
Arguments FApp {k}.

Inductive raw_form (k : nat) : Type :=
| RApp : rel_symbol -> list (raw_term k) -> raw_form k
| EqForm : sort -> raw_term k -> raw_term k -> raw_form k
| NegForm : raw_form k -> raw_form k
| ImpForm : raw_form k -> raw_form k -> raw_form k
| AllForm : sort -> raw_form k -> raw_form k.

Arguments RApp {k}.
Arguments EqForm {k}.
Arguments NegForm {k}.
Arguments ImpForm {k}.
Arguments AllForm {k}.

Fixpoint retag_term {k m : nat} (t : raw_term k) : raw_term m :=
  match t with
  | Var alpha i => Var alpha i
  | FApp f args => FApp f (map (@retag_term k m) args)
  end.

Fixpoint retag_form {k m : nat} (phi : raw_form k) : raw_form m :=
  match phi with
  | RApp R args => RApp R (map (@retag_term k m) args)
  | EqForm alpha t u => EqForm alpha (retag_term t) (retag_term u)
  | NegForm psi => NegForm (retag_form psi)
  | ImpForm psi chi => ImpForm (retag_form psi) (retag_form chi)
  | AllForm alpha psi => AllForm alpha (retag_form psi)
  end.

Inductive term_ok (k : nat) : list sort -> sort -> raw_term k -> Prop :=
| TermVar :
    forall Gamma alpha i,
      nth_error Gamma i = Some alpha ->
      term_ok k Gamma alpha (Var alpha i)
| TermFun :
    forall Gamma f args beta,
      fun_in_language k f ->
      cod_fun f = beta ->
      args_ok k Gamma (dom_fun f) args ->
      term_ok k Gamma beta (FApp f args)
with args_ok (k : nat) : list sort -> list sort -> list (raw_term k) -> Prop :=
| ArgsNil : forall Gamma, args_ok k Gamma [] []
| ArgsCons :
    forall Gamma alpha rest t ts,
      term_ok k Gamma alpha t ->
      args_ok k Gamma rest ts ->
      args_ok k Gamma (alpha :: rest) (t :: ts).

Inductive form_ok (k : nat) : list sort -> raw_form k -> Prop :=
| FormRel :
    forall Gamma R args,
      rel_in_language k R ->
      args_ok k Gamma (dom_rel R) args ->
      form_ok k Gamma (RApp R args)
| FormEq :
    forall Gamma alpha t u,
      sort_in_language k alpha ->
      term_ok k Gamma alpha t ->
      term_ok k Gamma alpha u ->
      form_ok k Gamma (EqForm alpha t u)
| FormNeg :
    forall Gamma phi,
      form_ok k Gamma phi ->
      form_ok k Gamma (NegForm phi)
| FormImp :
    forall Gamma phi psi,
      form_ok k Gamma phi ->
      form_ok k Gamma psi ->
      form_ok k Gamma (ImpForm phi psi)
| FormAll :
    forall Gamma alpha phi,
      sort_in_language k alpha ->
      form_ok k (alpha :: Gamma) phi ->
      form_ok k Gamma (AllForm alpha phi).

Definition sentence (k : nat) (phi : raw_form k) : Prop :=
  form_ok k [] phi.

Inductive syntactic_object (k : nat) : Type :=
| ObjTerm : raw_term k -> syntactic_object k
| ObjForm : raw_form k -> syntactic_object k
| ObjProofSeq : list (raw_form k) -> syntactic_object k.

Arguments ObjTerm {k}.
Arguments ObjForm {k}.
Arguments ObjProofSeq {k}.

Fixpoint quote_term (k : nat) (t : raw_term k) : raw_term (delta k) :=
  match t with
  | Var alpha i => FApp (VarCode k alpha i) []
  | FApp f args => FApp (FunCode k f) (map (quote_term k) args)
  end.

Fixpoint quote_form (k : nat) (phi : raw_form k) : raw_term (delta k) :=
  match phi with
  | RApp R args => FApp (RelCode k R) (map (quote_term k) args)
  | EqForm alpha t u => FApp (EqCode k alpha) [quote_term k t; quote_term k u]
  | NegForm psi => FApp (NegCode k) [quote_form k psi]
  | ImpForm psi chi => FApp (ImpCode k) [quote_form k psi; quote_form k chi]
  | AllForm alpha psi => FApp (AllCode k alpha) [quote_form k psi]
  end.

Fixpoint list_code (k : nat) (p : list (raw_form k)) : raw_term (delta k) :=
  match p with
  | [] => FApp (NilCode k) []
  | phi :: rest => FApp (ConsCode k) [quote_form k phi; list_code k rest]
  end.

Definition quote_object (k : nat) (a : syntactic_object k)
  : raw_term (delta k) :=
  match a with
  | ObjTerm t => quote_term k t
  | ObjForm phi => quote_form k phi
  | ObjProofSeq p => list_code k p
  end.

Fixpoint raise_term (k d : nat) (t : raw_term k) : raw_term k :=
  match t with
  | Var alpha i => Var alpha (i + d)
  | FApp f args => FApp f (map (raise_term k d) args)
  end.

Fixpoint replace_term
    (k r c : nat) (subs : list (raw_term k)) (t : raw_term k)
  : raw_term k :=
  match t with
  | Var alpha i =>
      if i <? c then Var alpha i
      else if i <? c + r then
        match nth_error subs (i - c) with
        | Some u => raise_term k c u
        | None => Var alpha i
        end
      else Var alpha (i - r)
  | FApp f args => FApp f (map (replace_term k r c subs) args)
  end.

Fixpoint replace_form
    (k r c : nat) (subs : list (raw_term k)) (phi : raw_form k)
  : raw_form k :=
  match phi with
  | RApp R args => RApp R (map (replace_term k r c subs) args)
  | EqForm alpha t u =>
      EqForm alpha (replace_term k r c subs t) (replace_term k r c subs u)
  | NegForm psi => NegForm (replace_form k r c subs psi)
  | ImpForm psi chi =>
      ImpForm (replace_form k r c subs psi) (replace_form k r c subs chi)
  | AllForm alpha psi => AllForm alpha (replace_form k r (S c) subs psi)
  end.

Definition sub_object
    (k : nat) (a : syntactic_object k) (subs : list (raw_term k))
  : syntactic_object k :=
  match a with
  | ObjTerm t => ObjTerm (replace_term k (length subs) 0 subs t)
  | ObjForm phi => ObjForm (replace_form k (length subs) 0 subs phi)
  | ObjProofSeq p => ObjProofSeq p
  end.

Section HilbertPart.

Variable LogAx : forall n, raw_form n -> Prop.

Definition line_ok
    (n : nat) (A : raw_form n -> Prop)
    (p : list (raw_form n)) (i : nat) (psi_i : raw_form n) : Prop :=
  A psi_i \/
  LogAx n psi_i \/
  (exists j l psi,
      j < i /\ l < i /\
      nth_error p j = Some psi /\
      nth_error p l = Some (ImpForm psi psi_i)) \/
  (exists j alpha psi,
      j < i /\
      nth_error p j = Some psi /\
      psi_i = AllForm alpha psi).

Definition proof_H
    (n : nat) (A : raw_form n -> Prop)
    (p : list (raw_form n)) (phi : raw_form n) : Prop :=
  p <> [] /\
  list_last_error p = Some phi /\
  forall i psi_i,
    nth_error p i = Some psi_i ->
    line_ok n A p i psi_i.

Definition ProofPredicate : Type :=
  forall n, list (raw_form n) -> raw_form n -> Prop.

Definition leP (P Q : ProofPredicate) : Prop :=
  forall n p phi, P n p phi -> Q n p phi.

Definition proof_graph
    (P : ProofPredicate) (n : nat) (psi : raw_form n) : Prop :=
  exists k (p : list (raw_form k)) (phi : raw_form k),
    k <= n + 1 /\
    P k p phi /\
    psi =
      RApp (PrfRel k) [retag_term (list_code k p); retag_term (quote_form k phi)].

Inductive base_ax (n : nat) : raw_form n -> Prop :=
| BaseTmPos :
    forall k Gamma alpha t,
      k <= n + 1 ->
      term_ok k Gamma alpha t ->
      base_ax n (RApp (TmRel k Gamma alpha) [retag_term (quote_term k t)])
| BaseFmPos :
    forall k Gamma phi,
      k <= n + 1 ->
      form_ok k Gamma phi ->
      base_ax n (RApp (FmRel k Gamma) [retag_term (quote_form k phi)])
| BaseSentPos :
    forall k phi,
      k <= n + 1 ->
      sentence k phi ->
      base_ax n (RApp (SentRel k) [retag_term (quote_form k phi)])
| BaseTmNeg :
    forall k Gamma alpha a,
      k <= n + 1 ->
      (~ exists t, a = ObjTerm t /\ term_ok k Gamma alpha t) ->
      base_ax n (NegForm (RApp (TmRel k Gamma alpha) [retag_term (quote_object k a)]))
| BaseFmNeg :
    forall k Gamma a,
      k <= n + 1 ->
      (~ exists phi, a = ObjForm phi /\ form_ok k Gamma phi) ->
      base_ax n (NegForm (RApp (FmRel k Gamma) [retag_term (quote_object k a)]))
| BaseSentNeg :
    forall k a,
      k <= n + 1 ->
      (~ exists phi, a = ObjForm phi /\ sentence k phi) ->
      base_ax n (NegForm (RApp (SentRel k) [retag_term (quote_object k a)]))
| BaseSep :
    forall k a b,
      k <= n + 1 ->
      a <> b ->
      base_ax n
        (NegForm (EqForm (E k) (retag_term (quote_object k a)) (retag_term (quote_object k b))))
| BaseSub :
    forall k Gamma Delta a subs,
      k <= n + 1 ->
      length subs = length Delta ->
      base_ax n
        (EqForm (E k)
          (FApp (SubCode k Gamma Delta)
            (retag_term (quote_object k a) ::
             map (fun t => retag_term (quote_term k t)) subs))
          (retag_term (quote_object k (sub_object k a subs)))).

Definition A_of (P : ProofPredicate) (n : nat) (psi : raw_form n) : Prop :=
  base_ax n psi \/ proof_graph P n psi.

Definition Phi (P : ProofPredicate) : ProofPredicate :=
  fun n p phi => proof_H n (A_of P n) p phi.

Definition prefixed (P : ProofPredicate) : Prop := leP (Phi P) P.

Definition Pstar : ProofPredicate :=
  fun n p phi => forall P, prefixed P -> P n p phi.

Definition T (n : nat) (psi : raw_form n) : Prop := A_of Pstar n psi.

Definition PrfObj (n : nat) (p : list (raw_form n)) (phi : raw_form n) : Prop :=
  Pstar n p phi.

Definition proves_in_layer (n : nat) (phi : raw_form n) : Prop :=
  exists p, PrfObj n p phi.

Lemma line_ok_monotone :
  forall n A B p i psi,
    (forall x, A x -> B x) ->
    line_ok n A p i psi ->
    line_ok n B p i psi.
Proof.
  intros n A B p i psi Hsub H.
  destruct H as [HA | [HL | [HMP | HG]]].
  - left; apply Hsub; exact HA.
  - right; left; exact HL.
  - right; right; left; exact HMP.
  - right; right; right; exact HG.
Qed.

Lemma proof_H_monotone :
  forall n A B p phi,
    (forall x, A x -> B x) ->
    proof_H n A p phi ->
    proof_H n B p phi.
Proof.
  intros n A B p phi Hsub [Hne [Hlast Hlines]].
  repeat split; try assumption.
  intros i psi Hi.
  apply line_ok_monotone with (A := A); auto.
Qed.

Lemma proof_graph_monotone :
  forall P Q n psi,
    leP P Q ->
    proof_graph P n psi ->
    proof_graph Q n psi.
Proof.
  intros P Q n psi HPQ [k [p [phi [Hk [HP Heq]]]]].
  exists k, p, phi; repeat split; auto.
Qed.

Lemma Phi_monotone :
  forall P Q, leP P Q -> leP (Phi P) (Phi Q).
Proof.
  intros P Q HPQ n p phi [Hne [Hlast Hlines]].
  unfold Phi, proof_H.
  repeat split; try assumption.
  intros i psi Hi.
  specialize (Hlines i psi Hi).
  destruct Hlines as [HA | [HL | [HMP | HG]]].
  - destruct HA as [HB | HGraph].
    + left. left. exact HB.
    + left. right. eapply proof_graph_monotone; eauto.
  - right. left. exact HL.
  - right. right. left. exact HMP.
  - right. right. right. exact HG.
Qed.

Lemma Pstar_prefixed : prefixed Pstar.
Proof.
  intros n p phi HPhi P HP.
  apply HP.
  apply Phi_monotone with (P := Pstar); auto.
  intros n' p' phi' HPs.
  apply HPs; exact HP.
Qed.

Theorem Pstar_fixed : forall n p phi, Pstar n p phi <-> Phi Pstar n p phi.
Proof.
  intros n p phi; split.
  - intros HPs.
    apply HPs.
    unfold prefixed.
    apply Phi_monotone.
    apply Pstar_prefixed.
  - apply Pstar_prefixed.
Qed.

End HilbertPart.

Theorem E_in_language_iff :
  forall k m, sort_in_language m (E k) <-> ell_sort (E k) <= m.
Proof. intros; unfold sort_in_language; tauto. Qed.

Theorem E0_in_every_language : forall m, sort_in_language m (E 0).
Proof. intros m; unfold sort_in_language, ell_sort; simpl; lia. Qed.

Theorem E_pos_in_language_iff :
  forall k m, 0 < k -> sort_in_language m (E k) <-> k <= m + 1.
Proof.
  intros k m Hk.
  unfold sort_in_language, ell_sort.
  rewrite delta_pos by exact Hk.
  lia.
Qed.

Theorem E_n_in_previous :
  forall n, 1 <= n -> sort_in_language (n - 1) (E n).
Proof.
  intros n Hn.
  apply E_pos_in_language_iff; lia.
Qed.

Theorem E_succ_not_in_previous :
  forall n, 1 <= n -> ~ sort_in_language (n - 1) (E (S n)).
Proof.
  intros n Hn.
  unfold sort_in_language, ell_sort; rewrite delta_succ; lia.
Qed.

Theorem TmRel_adjacent :
  forall n Gamma alpha,
    1 <= n ->
    all_sorts_le n Gamma ->
    ell_sort alpha <= n ->
    rel_in_language (n - 1) (TmRel n Gamma alpha).
Proof.
  intros n Gamma alpha Hn HG Ha.
  split; simpl; auto; rewrite delta_pos by lia; lia.
Qed.

Theorem FmRel_adjacent :
  forall n Gamma,
    1 <= n ->
    all_sorts_le n Gamma ->
    rel_in_language (n - 1) (FmRel n Gamma).
Proof.
  intros n Gamma Hn HG.
  split; simpl; auto; rewrite delta_pos by lia; lia.
Qed.

Theorem SentRel_adjacent :
  forall n, 1 <= n -> rel_in_language (n - 1) (SentRel n).
Proof.
  intros n Hn; split; simpl; auto; rewrite delta_pos by lia; lia.
Qed.

Theorem PrfRel_adjacent :
  forall n, 1 <= n -> rel_in_language (n - 1) (PrfRel n).
Proof.
  intros n Hn; split; simpl; auto; rewrite delta_pos by lia; lia.
Qed.

Theorem TmRel_next_not_adjacent :
  forall n Gamma alpha,
    1 <= n ->
    ~ rel_in_language (n - 1) (TmRel (S n) Gamma alpha).
Proof. intros n Gamma alpha Hn [_ Hlev]; simpl in Hlev; lia. Qed.

Theorem FmRel_next_not_adjacent :
  forall n Gamma,
    1 <= n ->
    ~ rel_in_language (n - 1) (FmRel (S n) Gamma).
Proof. intros n Gamma Hn [_ Hlev]; simpl in Hlev; lia. Qed.

Theorem SentRel_next_not_adjacent :
  forall n, 1 <= n -> ~ rel_in_language (n - 1) (SentRel (S n)).
Proof. intros n Hn [_ Hlev]; simpl in Hlev; lia. Qed.

Theorem PrfRel_next_not_adjacent :
  forall n, 1 <= n -> ~ rel_in_language (n - 1) (PrfRel (S n)).
Proof. intros n Hn [_ Hlev]; simpl in Hlev; lia. Qed.

Theorem quote_target_sort :
  forall k (a : syntactic_object k), ell_sort (E k) = delta k.
Proof. reflexivity. Qed.

Theorem quote_adjacent_for_positive_layers :
  forall k (a : syntactic_object k),
    0 < k ->
    sort_in_language (k - 1) (E k).
Proof.
  intros k a Hk.
  apply E_pos_in_language_iff; lia.
Qed.

Theorem next_quote_sort_not_available :
  forall k,
    0 < k ->
    ~ sort_in_language (k - 1) (E (S k)).
Proof.
  intros k Hk.
  apply E_succ_not_in_previous; lia.
Qed.

Theorem D_in_language_iff :
  forall n sigma, sort_in_language n (D sigma) <-> rho sigma <= n.
Proof. intros; unfold sort_in_language, ell_sort; tauto. Qed.

Theorem App_in_language_iff :
  forall n sigma tau,
    fun_in_language n (App sigma tau) <->
    rho (TyArr sigma tau) <= n.
Proof.
  intros; unfold fun_in_language; simpl; tauto.
Qed.

Inductive internal_layer_index_sort : Set := .
Inductive internal_unified_form_predicate : Set := .
Inductive internal_decode_function : Set := .

Theorem no_internal_layer_index_sort :
  forall x : internal_layer_index_sort, False.
Proof. intros []. Qed.

Theorem no_internal_unified_form_predicate :
  forall x : internal_unified_form_predicate, False.
Proof. intros []. Qed.

Theorem no_internal_decode_function :
  forall x : internal_decode_function, False.
Proof. intros []. Qed.

Record layer_visibility_model : Type := {
  visible_relation : nat -> rel_symbol -> Prop
}.

Definition canonical_layer_visibility_model : layer_visibility_model := {|
  visible_relation := rel_in_language
|}.

Theorem layer_visibility_model_nontrivial :
  forall n,
    1 <= n ->
    visible_relation canonical_layer_visibility_model (n - 1) (SentRel n) /\
    ~ visible_relation canonical_layer_visibility_model (n - 1) (SentRel (S n)).
Proof.
  intros n Hn.
  split.
  - exact (SentRel_adjacent n Hn).
  - exact (SentRel_next_not_adjacent n Hn).
Qed.
Record formal_system (LogAx : forall n, raw_form n -> Prop) : Type := {
  fs_delta : nat -> nat;
  fs_ty : Type;
  fs_sort : Type;
  fs_fun : Type;
  fs_rel : Type;
  fs_raw_term : nat -> Type;
  fs_raw_form : nat -> Type;
  fs_quote : forall k, syntactic_object k -> raw_term (delta k);
  fs_sub : forall k, syntactic_object k -> list (raw_term k) -> syntactic_object k;
  fs_line_ok :
    forall n,
      (raw_form n -> Prop) ->
      list (raw_form n) -> nat -> raw_form n -> Prop;
  fs_proof_H :
    forall n,
      (raw_form n -> Prop) ->
      list (raw_form n) -> raw_form n -> Prop;
  fs_phi : ProofPredicate -> ProofPredicate;
  fs_pstar : ProofPredicate;
  fs_pstar_fixed :
    forall n p phi, fs_pstar n p phi <-> fs_phi fs_pstar n p phi;
  fs_theory : forall n, raw_form n -> Prop;
  fs_prf_obj : forall n, list (raw_form n) -> raw_form n -> Prop;
  fs_proves : forall n, raw_form n -> Prop;
  fs_layer_model : layer_visibility_model;
  fs_layer_model_nontrivial :
    forall n, 1 <= n ->
      visible_relation fs_layer_model (n - 1) (SentRel n) /\
      ~ visible_relation fs_layer_model (n - 1) (SentRel (S n));
  fs_fm_adjacent :
    forall n Gamma,
      1 <= n ->
      all_sorts_le n Gamma ->
      rel_in_language (n - 1) (FmRel n Gamma);
  fs_fm_next_not_adjacent :
    forall n Gamma,
      1 <= n ->
      ~ rel_in_language (n - 1) (FmRel (S n) Gamma);
  fs_sent_adjacent :
    forall n, 1 <= n -> rel_in_language (n - 1) (SentRel n);
  fs_sent_next_not_adjacent :
    forall n, 1 <= n -> ~ rel_in_language (n - 1) (SentRel (S n));
  fs_prf_adjacent :
    forall n, 1 <= n -> rel_in_language (n - 1) (PrfRel n);
  fs_prf_next_not_adjacent :
    forall n, 1 <= n -> ~ rel_in_language (n - 1) (PrfRel (S n));
  fs_no_internal_layer_index :
    forall x : internal_layer_index_sort, False;
  fs_no_internal_form_predicate :
    forall x : internal_unified_form_predicate, False;
  fs_no_internal_decode :
    forall x : internal_decode_function, False
}.

Definition canonical_formal_system
    (LogAx : forall n, raw_form n -> Prop) : formal_system LogAx := {|
  fs_delta := delta;
  fs_ty := ty;
  fs_sort := sort;
  fs_fun := fun_symbol;
  fs_rel := rel_symbol;
  fs_raw_term := raw_term;
  fs_raw_form := raw_form;
  fs_quote := quote_object;
  fs_sub := sub_object;
  fs_line_ok := line_ok LogAx;
  fs_proof_H := proof_H LogAx;
  fs_phi := Phi LogAx;
  fs_pstar := Pstar LogAx;
  fs_pstar_fixed := Pstar_fixed LogAx;
  fs_theory := T LogAx;
  fs_prf_obj := PrfObj LogAx;
  fs_proves := proves_in_layer LogAx;
  fs_layer_model := canonical_layer_visibility_model;
  fs_layer_model_nontrivial := layer_visibility_model_nontrivial;
  fs_fm_adjacent := FmRel_adjacent;
  fs_fm_next_not_adjacent := FmRel_next_not_adjacent;
  fs_sent_adjacent := SentRel_adjacent;
  fs_sent_next_not_adjacent := SentRel_next_not_adjacent;
  fs_prf_adjacent := PrfRel_adjacent;
  fs_prf_next_not_adjacent := PrfRel_next_not_adjacent;
  fs_no_internal_layer_index := no_internal_layer_index_sort;
  fs_no_internal_form_predicate := no_internal_unified_form_predicate;
  fs_no_internal_decode := no_internal_decode_function
|}.

End StrictAdjacentQuasiquoteTower.
