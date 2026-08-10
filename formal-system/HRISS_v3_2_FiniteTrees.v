(** Explicit finite rooted ordered evaluation trees for HRISS v3.2. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Logic.ProofIrrelevance.
Require Import HRISS_v3_2 HRISS_v3_2_Semantics HRISS_v3_2_Stability
  HRISS_v3_2_Theory HRISS_v3_2_Clauses HRISS_v3_2_Eval
  HRISS_v3_2_Certificates.
Set Implicit Arguments.
Unset Strict Implicit.

(** These four mutually inductive datatypes are literally finite ordered
    trees.  Tuple trees record the ordered premise families of ordinary
    constructors.  RApp nodes have an evaluated term child and the canonical
    zero-premise Quote child determined by their final two arguments. *)
Inductive TmEvalTree {Sig} {H : Subgroup} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) : Type :=
| Tree_Var : forall i : nat, TmEvalTree C e
| Tree_Fun : forall n (f : TSym Sig n), TmlEvalTree C e n -> TmEvalTree C e
| Tree_QuoteT : forall t : tm Sig, wf_tm H t -> TmEvalTree C e
| Tree_QuoteF : forall p : fm Sig, wf_fm H p -> TmEvalTree C e
| Tree_RAppT : TmEvalTree C e -> forall u : tm Sig,
    wf_tm H u -> TmEvalTree C e
| Tree_Move : forall g : Perm3, Hminus H g -> TmEvalTree C e
with FmEvalTree {Sig} {H : Subgroup} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) : Type :=
| Tree_Pred : forall n (P : PSym Sig n), TmlEvalTree C e n -> FmEvalTree C e
| Tree_Conn : forall n (L : LSym Sig n), FmlEvalTree C e n -> FmEvalTree C e
| Tree_RAppF : TmEvalTree C e -> forall p : fm Sig,
    wf_fm H p -> FmEvalTree C e
| Tree_Quant : forall (Q : QSym Sig) (i : nat) (p : fm Sig),
    wf_fm H p -> FmEvalTree C e
with TmlEvalTree {Sig} {H : Subgroup} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) : nat -> Type :=
| Tree_TNil : TmlEvalTree C e 0
| Tree_TCons : forall n, TmEvalTree C e -> TmlEvalTree C e n ->
    TmlEvalTree C e (S n)
with FmlEvalTree {Sig} {H : Subgroup} (C : SyntaxCoding Sig H)
    (e : E_car Sig H) : nat -> Type :=
| Tree_FNil : FmlEvalTree C e 0
| Tree_FCons : forall n, FmEvalTree C e -> FmlEvalTree C e n ->
    FmlEvalTree C e (S n).

Fixpoint tm_tree_syntax {Sig H C e} (D : @TmEvalTree Sig H C e) : tm Sig :=
  match D with
  | @Tree_Var _ _ _ _ i => TVar i
  | @Tree_Fun _ _ _ _ _ f Ds => TFun f (tml_tree_syntax Ds)
  | @Tree_QuoteT _ _ _ _ t _ => TQuoteT t
  | @Tree_QuoteF _ _ _ _ p _ => TQuoteF p
  | @Tree_RAppT _ _ _ _ Dt u _ => TRApp (tm_tree_syntax Dt) u
  | @Tree_Move _ _ _ _ g _ => TMove g
  end
with fm_tree_syntax {Sig H C e} (D : @FmEvalTree Sig H C e) : fm Sig :=
  match D with
  | @Tree_Pred _ _ _ _ _ P Ds => FPred P (tml_tree_syntax Ds)
  | @Tree_Conn _ _ _ _ _ L Ds => FConn L (fml_tree_syntax Ds)
  | @Tree_RAppF _ _ _ _ Dt p _ => FRApp (tm_tree_syntax Dt) p
  | @Tree_Quant _ _ _ _ Q i p _ => FQuant Q i p
  end
with tml_tree_syntax {Sig H C e n} (D : @TmlEvalTree Sig H C e n) :
    tml Sig n :=
  match D with
  | @Tree_TNil _ _ _ _ => TNil
  | Tree_TCons Dt Ds => TCons (tm_tree_syntax Dt) (tml_tree_syntax Ds)
  end
with fml_tree_syntax {Sig H C e n} (D : @FmlEvalTree Sig H C e n) :
    fml Sig n :=
  match D with
  | @Tree_FNil _ _ _ _ => FNil
  | Tree_FCons Dp Ds => FCons (fm_tree_syntax Dp) (fml_tree_syntax Ds)
  end.

Fixpoint tm_tree_wf {Sig H C e} (D : @TmEvalTree Sig H C e) :
    wf_tm H (tm_tree_syntax D) :=
  match D with
  | @Tree_Var _ _ _ _ _ => I
  | @Tree_Fun _ _ _ _ _ _ Ds => tml_tree_wf Ds
  | @Tree_QuoteT _ _ _ _ _ Ht => Ht
  | @Tree_QuoteF _ _ _ _ _ Hp => Hp
  | @Tree_RAppT _ _ _ _ Dt _ Hu => conj (tm_tree_wf Dt) Hu
  | @Tree_Move _ _ _ _ _ Hg => Hg
  end
with fm_tree_wf {Sig H C e} (D : @FmEvalTree Sig H C e) :
    wf_fm H (fm_tree_syntax D) :=
  match D with
  | @Tree_Pred _ _ _ _ _ _ Ds => tml_tree_wf Ds
  | @Tree_Conn _ _ _ _ _ _ Ds => fml_tree_wf Ds
  | @Tree_RAppF _ _ _ _ Dt _ Hp => conj (tm_tree_wf Dt) Hp
  | @Tree_Quant _ _ _ _ _ _ _ Hp => Hp
  end
with tml_tree_wf {Sig H C e n} (D : @TmlEvalTree Sig H C e n) :
    wf_tml H (tml_tree_syntax D) :=
  match D with
  | @Tree_TNil _ _ _ _ => I
  | Tree_TCons Dt Ds => conj (tm_tree_wf Dt) (tml_tree_wf Ds)
  end
with fml_tree_wf {Sig H C e n} (D : @FmlEvalTree Sig H C e n) :
    wf_fml H (fml_tree_syntax D) :=
  match D with
  | @Tree_FNil _ _ _ _ => I
  | Tree_FCons Dp Ds => conj (fm_tree_wf Dp) (fml_tree_wf Ds)
  end.

Fixpoint tm_tree_value {Sig H} {C : SyntaxCoding Sig H} {e}
    (D : TmEvalTree C e) : E_car Sig H :=
  match D with
  | @Tree_Var _ _ _ _ i =>
      @operation_family_map Sig H (ai_var i) e (empty_power (E_dcpo Sig H))
  | @Tree_Fun _ _ _ _ _ f Ds =>
      @operation_family_map Sig H (ai_T f) e (tml_tree_value Ds)
  | @Tree_QuoteT _ _ _ _ t Ht => quote_value C (@TmCarrier Sig H t Ht)
  | @Tree_QuoteF _ _ _ _ p Hp => quote_value C (@FmCarrier Sig H p Hp)
  | @Tree_RAppT _ _ _ _ Dt u Hu =>
      Run C (@pair_power (E_dcpo Sig H) (tm_tree_value Dt)
        (quote_value C (@TmCarrier Sig H u Hu)))
  | @Tree_Move _ _ _ _ g Hg => transport_map C g (proj1 Hg) e
  end
with fm_tree_value {Sig H} {C : SyntaxCoding Sig H} {e}
    (D : FmEvalTree C e) : E_car Sig H :=
  match D with
  | @Tree_Pred _ _ _ _ _ P Ds =>
      @operation_family_map Sig H (ai_P P) e (tml_tree_value Ds)
  | @Tree_Conn _ _ _ _ _ L Ds =>
      @operation_family_map Sig H (ai_L L) e (fml_tree_value Ds)
  | @Tree_RAppF _ _ _ _ Dt p Hp =>
      Run C (@pair_power (E_dcpo Sig H) (tm_tree_value Dt)
        (quote_value C (@FmCarrier Sig H p Hp)))
  | @Tree_Quant _ _ _ _ Q i p Hp => @quant_rule_value Sig H C e Q i p Hp
  end
with tml_tree_value {Sig H} {C : SyntaxCoding Sig H} {e n}
    (D : TmlEvalTree C e n) : dcar (power_dcpo (E_dcpo Sig H) n) :=
  match D with
  | @Tree_TNil _ _ _ _ => empty_power (E_dcpo Sig H)
  | @Tree_TCons _ _ _ _ n Dt Ds =>
      @tuple_cons_value (E_dcpo Sig H) n
        (tm_tree_value Dt) (tml_tree_value Ds)
  end
with fml_tree_value {Sig H} {C : SyntaxCoding Sig H} {e n}
    (D : FmlEvalTree C e n) : dcar (power_dcpo (E_dcpo Sig H) n) :=
  match D with
  | @Tree_FNil _ _ _ _ => empty_power (E_dcpo Sig H)
  | @Tree_FCons _ _ _ _ n Dp Ds =>
      @tuple_cons_value (E_dcpo Sig H) n
        (fm_tree_value Dp) (fml_tree_value Ds)
  end.

(** Every explicit tree is a derivation in the rule-indexed presentation. *)
Fixpoint tm_tree_rule {Sig H} {C : SyntaxCoding Sig H} {e}
    (D : TmEvalTree C e) :
    EvalTmCert C e (tm_tree_syntax D) (tm_tree_value D)
with fm_tree_rule {Sig H} {C : SyntaxCoding Sig H} {e}
    (D : FmEvalTree C e) :
    EvalFmCert C e (fm_tree_syntax D) (fm_tree_value D)
with tml_tree_rule {Sig H} {C : SyntaxCoding Sig H} {e n}
    (D : TmlEvalTree C e n) :
    EvalTmlCert C e (tml_tree_syntax D) (tml_tree_value D)
with fml_tree_rule {Sig H} {C : SyntaxCoding Sig H} {e n}
    (D : FmlEvalTree C e n) :
    EvalFmlCert C e (fml_tree_syntax D) (fml_tree_value D).
Proof.
  - destruct D; cbn [tm_tree_value tm_tree_syntax tm_tree_wf].
    + constructor.
    + constructor. apply tml_tree_rule.
    + constructor.
    + constructor.
    + exact (@Cert_RAppT Sig H C e (tm_tree_syntax D) u
        (tm_tree_value D) (quote_value C (@TmCarrier Sig H u w))
        (@tm_tree_rule Sig H C e D) (@Cert_QuoteT Sig H C e u w)).
    + constructor.
  - destruct D; cbn [fm_tree_value fm_tree_syntax fm_tree_wf].
    + constructor. apply tml_tree_rule.
    + constructor. apply fml_tree_rule.
    + match goal with
      | [ Dt : TmEvalTree C e, Hp0 : wf_fm H ?p0 |- _ ] =>
          exact (@Cert_RAppF Sig H C e (tm_tree_syntax Dt) p0
            (tm_tree_value Dt) (quote_value C (@FmCarrier Sig H p0 Hp0))
            (@tm_tree_rule Sig H C e Dt) (@Cert_QuoteF Sig H C e p0 Hp0))
      end.
    + constructor.
  - destruct D; cbn [tml_tree_value tml_tree_syntax tml_tree_wf].
    + constructor.
    + constructor; [apply tm_tree_rule|apply tml_tree_rule].
  - destruct D; cbn [fml_tree_value fml_tree_syntax fml_tree_wf].
    + constructor.
    + constructor; [apply fm_tree_rule|apply fml_tree_rule].
Defined.

(** Soundness of root labels. *)
Fixpoint tm_tree_sound {Sig H} {C : SyntaxCoding Sig H} {e}
    (D : TmEvalTree C e) {struct D} :
    tm_tree_value D = @ValTm Sig H C e (tm_tree_syntax D) (tm_tree_wf D)
with fm_tree_sound {Sig H} {C : SyntaxCoding Sig H} {e}
    (D : FmEvalTree C e) {struct D} :
    fm_tree_value D = @ValFm Sig H C e (fm_tree_syntax D) (fm_tree_wf D)
with tml_tree_sound {Sig H} {C : SyntaxCoding Sig H} {e n}
    (D : TmlEvalTree C e n) {struct D} :
    tml_tree_value D = ValTmlMap C (tml_tree_syntax D) e
with fml_tree_sound {Sig H} {C : SyntaxCoding Sig H} {e n}
    (D : FmlEvalTree C e n) {struct D} :
    fml_tree_value D = ValFmlMap C (fml_tree_syntax D) e.
Proof.
  - destruct D; cbn [tm_tree_value tm_tree_syntax tm_tree_wf].
    + symmetry. apply (@Val_Var Sig H C e).
    + rewrite (Val_Fun C e f (tml_tree_wf t)).
      now rewrite (@tml_tree_sound Sig H C e _ t).
    + symmetry. apply Val_QuoteT.
    + symmetry. apply Val_QuoteF.
    + match goal with
      | [ Dt : TmEvalTree C e, Hu : wf_tm H ?u |- _ ] =>
          rewrite (Val_RAppT C e (tm_tree_wf Dt) Hu);
          now rewrite (@tm_tree_sound Sig H C e Dt)
      end.
    + symmetry. apply Val_Move.
  - destruct D; cbn [fm_tree_value fm_tree_syntax fm_tree_wf].
    + match goal with
      | [ P0 : PSym Sig ?n, Ds : TmlEvalTree C e n |- _ ] =>
          rewrite (Val_Pred C e P0 (tml_tree_wf Ds));
          now rewrite (@tml_tree_sound Sig H C e n Ds)
      end.
    + match goal with
      | [ L0 : LSym Sig ?n, Ds : FmlEvalTree C e n |- _ ] =>
          rewrite (Val_Conn C e L0 (fml_tree_wf Ds));
          now rewrite (@fml_tree_sound Sig H C e n Ds)
      end.
    + match goal with
      | [ Dt : TmEvalTree C e, Hp : wf_fm H ?p0 |- _ ] =>
          rewrite (Val_RAppF C e (tm_tree_wf Dt) Hp);
          now rewrite (@tm_tree_sound Sig H C e Dt)
      end.
    + unfold quant_rule_value. symmetry. apply Val_Quant.
  - destruct D; cbn [tml_tree_value tml_tree_syntax tml_tree_wf].
    + reflexivity.
    + match goal with
      | [ Dt : TmEvalTree C e, Ds : TmlEvalTree C e ?n |- _ ] =>
          rewrite (@tm_tree_sound Sig H C e Dt),
            (@tml_tree_sound Sig H C e n Ds);
          symmetry; apply ValTmlMap_cons
      end.
  - destruct D; cbn [fml_tree_value fml_tree_syntax fml_tree_wf].
    + reflexivity.
    + match goal with
      | [ Dp : FmEvalTree C e, Ds : FmlEvalTree C e ?n |- _ ] =>
          rewrite (@fm_tree_sound Sig H C e Dp),
            (@fml_tree_sound Sig H C e n Ds);
          symmetry; apply ValFmlMap_cons
      end.
Defined.

(** Certificate size is an explicit finite natural number. *)
Fixpoint tm_tree_size {Sig H C e} (D : @TmEvalTree Sig H C e) : nat :=
  match D with
  | @Tree_Var _ _ _ _ _ | @Tree_QuoteT _ _ _ _ _ _
  | @Tree_QuoteF _ _ _ _ _ _ | @Tree_Move _ _ _ _ _ _ => 1
  | @Tree_Fun _ _ _ _ _ _ Ds => S (tml_tree_size Ds)
  | @Tree_RAppT _ _ _ _ Dt _ _ => S (S (tm_tree_size Dt))
  end
with fm_tree_size {Sig H C e} (D : @FmEvalTree Sig H C e) : nat :=
  match D with
  | @Tree_Pred _ _ _ _ _ _ Ds => S (tml_tree_size Ds)
  | @Tree_Conn _ _ _ _ _ _ Ds => S (fml_tree_size Ds)
  | @Tree_RAppF _ _ _ _ Dt _ _ => S (S (tm_tree_size Dt))
  | @Tree_Quant _ _ _ _ _ _ _ _ => 1
  end
with tml_tree_size {Sig H C e n} (D : @TmlEvalTree Sig H C e n) : nat :=
  match D with
  | @Tree_TNil _ _ _ _ => 0
  | @Tree_TCons _ _ _ _ _ Dt Ds => tm_tree_size Dt + tml_tree_size Ds
  end
with fml_tree_size {Sig H C e n} (D : @FmlEvalTree Sig H C e n) : nat :=
  match D with
  | @Tree_FNil _ _ _ _ => 0
  | @Tree_FCons _ _ _ _ _ Dp Ds => fm_tree_size Dp + fml_tree_size Ds
  end.

Definition EvalTmDerives {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    (t : tm Sig) (v : E_car Sig H) : Prop :=
  exists D : TmEvalTree C e, tm_tree_syntax D = t /\ tm_tree_value D = v.

Definition EvalFmDerives {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    (p : fm Sig) (v : E_car Sig H) : Prop :=
  exists D : FmEvalTree C e, fm_tree_syntax D = p /\ fm_tree_value D = v.

Definition EvalDerives {Sig H} (C : SyntaxCoding Sig H) (e : E_car Sig H)
    (z : SyntaxCarrier Sig H) (v : E_car Sig H) : Prop :=
  match proj1_sig z with
  | ETerm t => EvalTmDerives C e t v
  | EForm p => EvalFmDerives C e p v
  end.

Theorem EvalTmDerives_sound : forall Sig H (C : SyntaxCoding Sig H) e t v
    (Ht : wf_tm H t),
    EvalTmDerives C e t v -> v = @ValTm Sig H C e t Ht.
Proof.
  intros Sig H C e t v Ht (D & Hr & Hv). subst t; subst v.
  replace Ht with (tm_tree_wf D) by apply proof_irrelevance.
  apply tm_tree_sound.
Qed.

Theorem EvalFmDerives_sound : forall Sig H (C : SyntaxCoding Sig H) e p v
    (Hp : wf_fm H p),
    EvalFmDerives C e p v -> v = @ValFm Sig H C e p Hp.
Proof.
  intros Sig H C e p v Hp (D & Hr & Hv). subst p; subst v.
  replace Hp with (fm_tree_wf D) by apply proof_irrelevance.
  apply fm_tree_sound.
Qed.

Print Assumptions tm_tree_sound.
Print Assumptions EvalTmDerives_sound.
