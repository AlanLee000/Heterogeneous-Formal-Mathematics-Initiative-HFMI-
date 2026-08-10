(*
  SRBE-065 / "1787 枚举反射"
  Faithful Rocq 8.20 formalization of the finite syntactic and stage machinery.

  The kernel file represents decoded finite sequences and trees by inductive
  data.  SRBE1787Codec.v supplies the proved reversible single-natural-number
  coding of the complete syntax, open skeleton, and certificate language.
  All checkers below are total structural functions; no fuel, classical
  choice, or proof placeholder is used in their definitions.
*)

From Stdlib Require Import List Bool Arith PeanoNat Lia Classical_Prop.
Require FormalSystemFactoryStructuralCodec FormalSystemFactoryNatCodec.
Import ListNotations.
Set Implicit Arguments.

Module FSCode := FormalSystemFactoryStructuralCodec.FormalSystemFactoryStructuralCodec.
Module FSNat := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.

(** * 1. Metatheory, sorts, signatures, and codes *)

Definition cantor_pair (m n : nat) : nat :=
  ((m + n) * (m + n + 1)) / 2 + n.

Inductive sort : Type :=
| SD
| SN
| SLow (stage : nat)
| SList (stage : nat).

Definition sort_eqb (s t : sort) : bool :=
  match s, t with
  | SD, SD | SN, SN => true
  | SLow k, SLow l | SList k, SList l => Nat.eqb k l
  | _, _ => false
  end.

Lemma sort_eqb_spec : forall s t, sort_eqb s t = true <-> s = t.
Proof.
  intros s t. destruct s, t; cbn; try (split; congruence).
  - destruct (Nat.eqb_spec stage stage0); subst; split; congruence.
  - destruct (Nat.eqb_spec stage stage0); subst; split; congruence.
Qed.

Definition base_sortb (s : sort) : bool :=
  match s with SD | SN => true | _ => false end.

Definition stage_sortb (k : nat) (s : sort) : bool :=
  match s with
  | SD | SN => true
  | SLow j | SList j => Nat.eqb j k && Nat.ltb 0 k
  end.

Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool)
    (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => eqb x y && list_eqb eqb xs' ys'
  | _, _ => false
  end.

Fixpoint forall2b {A B : Type} (p : A -> B -> bool)
    (xs : list A) (ys : list B) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => p x y && forall2b p xs' ys'
  | _, _ => false
  end.

Definition list_sort_eqb := list_eqb sort_eqb.

Inductive fsym : Type :=
| FBase (code : nat) (inputs : list sort) (output : sort)
| FZero | FSucc | FAdd | FMul
| FLowConst (stage source root cert : nat)
| FSource (stage : nat)
| FRootCode (stage : nat)
| FCert (stage : nat)
| FNil (stage : nat)
| FCons (stage : nat)
| FEnum (stage : nat).

Definition fsig (f : fsym) : list sort * sort :=
  match f with
  | FBase _ ins out => (ins, out)
  | FZero => ([], SN)
  | FSucc => ([SN], SN)
  | FAdd | FMul => ([SN; SN], SN)
  | FLowConst k _ _ _ => ([], SLow k)
  | FSource k | FRootCode k | FCert k => ([SLow k], SN)
  | FNil k => ([], SList k)
  | FCons k => ([SLow k; SList k], SList k)
  | FEnum k => ([SN], SList k)
  end.

Definition fsym_allowedb (k : nat) (f : fsym) : bool :=
  match f with
  | FBase _ ins out => forallb base_sortb ins && base_sortb out
  | FZero | FSucc | FAdd | FMul => true
  | FLowConst j _ _ _ | FSource j | FRootCode j | FCert j
  | FNil j | FCons j | FEnum j => Nat.eqb j k && Nat.ltb 0 k
  end.

Definition fsym_eqb (f g : fsym) : bool :=
  match f, g with
  | FBase c ins out, FBase d ins' out' =>
      Nat.eqb c d && list_sort_eqb ins ins' && sort_eqb out out'
  | FZero, FZero | FSucc, FSucc | FAdd, FAdd | FMul, FMul => true
  | FLowConst k s r c, FLowConst k' s' r' c' =>
      Nat.eqb k k' && Nat.eqb s s' && Nat.eqb r r' && Nat.eqb c c'
  | FSource k, FSource k' | FRootCode k, FRootCode k'
  | FCert k, FCert k' | FNil k, FNil k' | FCons k, FCons k'
  | FEnum k, FEnum k' => Nat.eqb k k'
  | _, _ => false
  end.

Inductive rsym : Type :=
| RBase (code : nat) (inputs : list sort)
| RD3
| RP (index : nat)
| RMember (stage : nat).

Definition rsig (r : rsym) : list sort :=
  match r with
  | RBase _ ins => ins
  | RD3 => [SD; SD; SD]
  | RP _ => []
  | RMember k => [SLow k; SList k]
  end.

Definition rsym_allowedb (k : nat) (r : rsym) : bool :=
  match r with
  | RBase _ ins => forallb base_sortb ins
  | RD3 | RP _ => true
  | RMember j => Nat.eqb j k && Nat.ltb 0 k
  end.

Definition rsym_eqb (r q : rsym) : bool :=
  match r, q with
  | RBase c ins, RBase d ins' => Nat.eqb c d && list_sort_eqb ins ins'
  | RD3, RD3 => true
  | RP n, RP m => Nat.eqb n m
  | RMember k, RMember l => Nat.eqb k l
  | _, _ => false
  end.

(** * 2. Raw terms, formulas, contexts, and sequents *)

Inductive term : Type :=
| TVar (s : sort) (index : nat)
| TFun (f : fsym) (args : terms)
with terms : Type :=
| TNil
| TCons (head : term) (tail : terms).

Fixpoint term_eqb (t u : term) : bool :=
  match t, u with
  | TVar s i, TVar r j => sort_eqb s r && Nat.eqb i j
  | TFun f ts, TFun g us => fsym_eqb f g && terms_eqb ts us
  | _, _ => false
  end
with terms_eqb (ts us : terms) : bool :=
  match ts, us with
  | TNil, TNil => true
  | TCons t ts', TCons u us' => term_eqb t u && terms_eqb ts' us'
  | _, _ => false
  end.

Fixpoint terms_to_list (ts : terms) : list term :=
  match ts with TNil => [] | TCons t us => t :: terms_to_list us end.

Fixpoint terms_length (ts : terms) : nat :=
  match ts with TNil => 0 | TCons _ us => S (terms_length us) end.

Fixpoint term_sort (k : nat) (t : term) : option sort :=
  match t with
  | TVar s _ => if stage_sortb k s then Some s else None
  | TFun f ts =>
      if fsym_allowedb k f then
        let '(ins, out) := fsig f in
        if terms_have_sorts k ts ins then Some out else None
      else None
  end
with terms_have_sorts (k : nat) (ts : terms) (ss : list sort) : bool :=
  match ts, ss with
  | TNil, [] => true
  | TCons t us, s :: vs =>
      match term_sort k t with
      | Some r => sort_eqb r s && terms_have_sorts k us vs
      | None => false
      end
  | _, _ => false
  end.

Definition WT (k : nat) (t : term) (s : sort) : bool :=
  match term_sort k t with Some r => sort_eqb r s | None => false end.

Inductive formula : Type :=
| Bot
| Eq (s : sort) (left right : term)
| Rel (r : rsym) (args : terms)
| And (left right : formula)
| Or (left right : formula)
| Imp (left right : formula)
| All (s : sort) (body : formula)
| Ex (s : sort) (body : formula).

Fixpoint formula_eqb (A B : formula) : bool :=
  match A, B with
  | Bot, Bot => true
  | Eq s t u, Eq r v w =>
      sort_eqb s r && term_eqb t v && term_eqb u w
  | Rel r ts, Rel q us => rsym_eqb r q && terms_eqb ts us
  | And A1 A2, And B1 B2 | Or A1 A2, Or B1 B2
  | Imp A1 A2, Imp B1 B2 => formula_eqb A1 B1 && formula_eqb A2 B2
  | All s A, All r B | Ex s A, Ex r B =>
      sort_eqb s r && formula_eqb A B
  | _, _ => false
  end.

Fixpoint formula_wtb (k : nat) (A : formula) : bool :=
  match A with
  | Bot => true
  | Eq s t u => WT k t s && WT k u s
  | Rel r ts => rsym_allowedb k r && terms_have_sorts k ts (rsig r)
  | And B C | Or B C | Imp B C => formula_wtb k B && formula_wtb k C
  | All s B | Ex s B => stage_sortb k s && formula_wtb k B
  end.

Definition context := list formula.
Record sequent : Type := mkSeq { antecedent : context; succedent : context }.

Definition context_eqb := list_eqb formula_eqb.
Definition sequent_eqb (S T : sequent) : bool :=
  context_eqb (antecedent S) (antecedent T) &&
  context_eqb (succedent S) (succedent T).

Definition context_wtb (k : nat) (G : context) : bool := forallb (formula_wtb k) G.
Definition sequent_wtb (k : nat) (S : sequent) : bool :=
  context_wtb k (antecedent S) && context_wtb k (succedent S).

(** * 3. Free variables, lift, substitution, and free renaming *)

Definition variable := (sort * nat)%type.

Definition variable_eqb (x y : variable) : bool :=
  sort_eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

Definition var_mem (x : variable) (xs : list variable) : bool :=
  existsb (variable_eqb x) xs.

Definition var_add (x : variable) (xs : list variable) : list variable :=
  if var_mem x xs then xs else x :: xs.

Definition var_union (xs ys : list variable) : list variable :=
  fold_right var_add ys xs.

Fixpoint fv_term (t : term) : list variable :=
  match t with
  | TVar s i => [(s, i)]
  | TFun _ ts => fv_terms ts
  end
with fv_terms (ts : terms) : list variable :=
  match ts with
  | TNil => []
  | TCons t us => var_union (fv_term t) (fv_terms us)
  end.

Definition down_var (s : sort) (x : variable) : option variable :=
  let '(r, i) := x in
  if sort_eqb r s then
    match i with 0 => None | S j => Some (r, j) end
  else Some x.

Fixpoint filter_map {A B : Type} (f : A -> option B) (xs : list A) : list B :=
  match xs with
  | [] => []
  | x :: ys => match f x with Some z => z :: filter_map f ys | None => filter_map f ys end
  end.

Definition down (s : sort) (xs : list variable) : list variable :=
  fold_right var_add [] (filter_map (down_var s) xs).

Fixpoint fv_formula (A : formula) : list variable :=
  match A with
  | Bot => []
  | Eq _ t u => var_union (fv_term t) (fv_term u)
  | Rel _ ts => fv_terms ts
  | And B C | Or B C | Imp B C => var_union (fv_formula B) (fv_formula C)
  | All s B | Ex s B => down s (fv_formula B)
  end.

Definition fv_context (G : context) : list variable :=
  fold_right (fun A acc => var_union (fv_formula A) acc) [] G.

Definition fv_sequent (S : sequent) : list variable :=
  var_union (fv_context (antecedent S)) (fv_context (succedent S)).

Fixpoint lift_term (s : sort) (depth : nat) (t : term) : term :=
  match t with
  | TVar r i =>
      if sort_eqb r s && Nat.leb depth i then TVar r (S i) else TVar r i
  | TFun f ts => TFun f (lift_terms s depth ts)
  end
with lift_terms (s : sort) (depth : nat) (ts : terms) : terms :=
  match ts with
  | TNil => TNil
  | TCons t us => TCons (lift_term s depth t) (lift_terms s depth us)
  end.

Fixpoint lift_formula (s : sort) (depth : nat) (A : formula) : formula :=
  match A with
  | Bot => Bot
  | Eq r t u => Eq r (lift_term s depth t) (lift_term s depth u)
  | Rel r ts => Rel r (lift_terms s depth ts)
  | And B C => And (lift_formula s depth B) (lift_formula s depth C)
  | Or B C => Or (lift_formula s depth B) (lift_formula s depth C)
  | Imp B C => Imp (lift_formula s depth B) (lift_formula s depth C)
  | All r B => All r (lift_formula s (if sort_eqb r s then S depth else depth) B)
  | Ex r B => Ex r (lift_formula s (if sort_eqb r s then S depth else depth) B)
  end.

Fixpoint sub_term (s : sort) (t : term) (index : nat) (u : term) : term :=
  match t with
  | TVar r j =>
      if sort_eqb r s then
        if Nat.eqb j index then u
        else if Nat.ltb index j then TVar r (Nat.pred j)
             else TVar r j
      else TVar r j
  | TFun f ts => TFun f (sub_terms s ts index u)
  end
with sub_terms (s : sort) (ts : terms) (index : nat) (u : term) : terms :=
  match ts with
  | TNil => TNil
  | TCons t vs => TCons (sub_term s t index u) (sub_terms s vs index u)
  end.

Fixpoint sub_formula (s : sort) (A : formula) (index : nat) (u : term) : formula :=
  match A with
  | Bot => Bot
  | Eq r t v => Eq r (sub_term s t index u) (sub_term s v index u)
  | Rel r ts => Rel r (sub_terms s ts index u)
  | And B C => And (sub_formula s B index u) (sub_formula s C index u)
  | Or B C => Or (sub_formula s B index u) (sub_formula s C index u)
  | Imp B C => Imp (sub_formula s B index u) (sub_formula s C index u)
  | All r B =>
      if sort_eqb r s
      then All r (sub_formula s B (S index) (lift_term s 0 u))
      else All r (sub_formula s B index u)
  | Ex r B =>
      if sort_eqb r s
      then Ex r (sub_formula s B (S index) (lift_term s 0 u))
      else Ex r (sub_formula s B index u)
  end.

Fixpoint ren_term (s : sort) (depth i j : nat) (t : term) : term :=
  match t with
  | TVar r n =>
      if sort_eqb r s && Nat.eqb n (i + depth)
      then TVar r (j + depth) else TVar r n
  | TFun f ts => TFun f (ren_terms s depth i j ts)
  end
with ren_terms (s : sort) (depth i j : nat) (ts : terms) : terms :=
  match ts with
  | TNil => TNil
  | TCons t us => TCons (ren_term s depth i j t) (ren_terms s depth i j us)
  end.

Fixpoint ren_formula (s : sort) (depth i j : nat) (A : formula) : formula :=
  match A with
  | Bot => Bot
  | Eq r t u => Eq r (ren_term s depth i j t) (ren_term s depth i j u)
  | Rel r ts => Rel r (ren_terms s depth i j ts)
  | And B C => And (ren_formula s depth i j B) (ren_formula s depth i j C)
  | Or B C => Or (ren_formula s depth i j B) (ren_formula s depth i j C)
  | Imp B C => Imp (ren_formula s depth i j B) (ren_formula s depth i j C)
  | All r B => All r (ren_formula s (if sort_eqb r s then S depth else depth) i j B)
  | Ex r B => Ex r (ren_formula s (if sort_eqb r s then S depth else depth) i j B)
  end.

Definition FreeRen (s : sort) (A : formula) (i j : nat) : formula :=
  ren_formula s 0 i j A.

(** * 4. The sequent-calculus kernel *)

Definition tzero : term := TFun FZero TNil.
Definition tsucc (t : term) : term := TFun FSucc (TCons t TNil).
Definition tadd (t u : term) : term := TFun FAdd (TCons t (TCons u TNil)).
Definition tmul (t u : term) : term := TFun FMul (TCons t (TCons u TNil)).
Definition neq (s : sort) (t u : term) : formula := Imp (Eq s t u) Bot.

Definition nvar (i : nat) : term := TVar SN i.

Definition qax1 : formula :=
  All SN (neq SN (tsucc (nvar 0)) tzero).
Definition qax2 : formula :=
  All SN (All SN
    (Imp (Eq SN (tsucc (nvar 1)) (tsucc (nvar 0)))
         (Eq SN (nvar 1) (nvar 0)))).
Definition qax3 : formula :=
  All SN (Imp (neq SN (nvar 0) tzero)
    (Ex SN (Eq SN (nvar 1) (tsucc (nvar 0))))).
Definition qax4 : formula :=
  All SN (Eq SN (tadd (nvar 0) tzero) (nvar 0)).
Definition qax5 : formula :=
  All SN (All SN
    (Eq SN (tadd (nvar 1) (tsucc (nvar 0)))
           (tsucc (tadd (nvar 1) (nvar 0))))).
Definition qax6 : formula :=
  All SN (Eq SN (tmul (nvar 0) tzero) tzero).
Definition qax7 : formula :=
  All SN (All SN
    (Eq SN (tmul (nvar 1) (tsucc (nvar 0)))
           (tadd (tmul (nvar 1) (nvar 0)) (nvar 1)))).

Definition AxQ : list formula := [qax1; qax2; qax3; qax4; qax5; qax6; qax7].
Definition qaxiomb (A : formula) : bool := existsb (formula_eqb A) AxQ.

Inductive gq_witness : Type :=
| WId (Gamma Delta : context) (A : formula)
| WBotL (Gamma Delta : context)
| WWkL (Gamma Delta : context) (A : formula)
| WWkR (Gamma Delta : context) (A : formula)
| WCtrL (Gamma Delta : context) (A : formula)
| WCtrR (Gamma Delta : context) (A : formula)
| WExchL (Gamma0 Gamma1 Delta : context) (A B : formula)
| WExchR (Gamma Delta0 Delta1 : context) (A B : formula)
| WCut (Gamma Delta Pi Lambda : context) (A : formula)
| WRefl (Gamma Delta : context) (s : sort) (t : term)
| WEqL (Gamma Delta : context) (s : sort) (t u : term) (A : formula) (j : nat)
| WEqR (Gamma Delta : context) (s : sort) (t u : term) (A : formula) (j : nat)
| WAndL (Gamma Delta : context) (A B : formula)
| WAndR (Gamma Delta : context) (A B : formula)
| WOrL (Gamma Delta : context) (A B : formula)
| WOrR (Gamma Delta : context) (A B : formula)
| WImpL (Gamma Delta Pi Lambda : context) (A B : formula)
| WImpR (Gamma Delta : context) (A B : formula)
| WAllL (Gamma Delta : context) (s : sort) (A : formula) (t : term)
| WAllR (Gamma Delta : context) (s : sort) (A : formula) (eigen : nat)
| WExL (Gamma Delta : context) (s : sort) (A : formula) (eigen : nat)
| WExR (Gamma Delta : context) (s : sort) (A : formula) (t : term)
| WQAx (Gamma Delta : context) (A : formula).

Definition gq_premises (w : gq_witness) : list sequent :=
  match w with
  | WId _ _ _ | WBotL _ _ | WRefl _ _ _ _ | WQAx _ _ _ => []
  | WWkL G D _ | WWkR G D _ => [mkSeq G D]
  | WCtrL G D A => [mkSeq (G ++ [A; A]) D]
  | WCtrR G D A => [mkSeq G (A :: A :: D)]
  | WExchL G0 G1 D A B => [mkSeq (G0 ++ A :: B :: G1) D]
  | WExchR G D0 D1 A B => [mkSeq G (D0 ++ A :: B :: D1)]
  | WCut G D P L A => [mkSeq G (A :: D); mkSeq (P ++ [A]) L]
  | WEqL G D s t _ A j => [mkSeq (G ++ [sub_formula s A j t]) D]
  | WEqR G D s t _ A j => [mkSeq G (sub_formula s A j t :: D)]
  | WAndL G D A B => [mkSeq (G ++ [A; B]) D]
  | WAndR G D A B => [mkSeq G (A :: D); mkSeq G (B :: D)]
  | WOrL G D A B => [mkSeq (G ++ [A]) D; mkSeq (G ++ [B]) D]
  | WOrR G D A B => [mkSeq G (A :: B :: D)]
  | WImpL G D P L A B => [mkSeq G (A :: D); mkSeq (P ++ [B]) L]
  | WImpR G D A B => [mkSeq (G ++ [A]) (B :: D)]
  | WAllL G D s A t => [mkSeq (G ++ [sub_formula s A 0 t]) D]
  | WAllR G D s A y => [mkSeq G (sub_formula s A 0 (TVar s y) :: D)]
  | WExL G D s A y => [mkSeq (G ++ [sub_formula s A 0 (TVar s y)]) D]
  | WExR G D s A t => [mkSeq G (sub_formula s A 0 t :: D)]
  end.

Definition gq_conclusion (w : gq_witness) : sequent :=
  match w with
  | WId G D A => mkSeq (G ++ [A]) (A :: D)
  | WBotL G D => mkSeq (G ++ [Bot]) D
  | WWkL G D A => mkSeq (G ++ [A]) D
  | WWkR G D A => mkSeq G (A :: D)
  | WCtrL G D A => mkSeq (G ++ [A]) D
  | WCtrR G D A => mkSeq G (A :: D)
  | WExchL G0 G1 D A B => mkSeq (G0 ++ B :: A :: G1) D
  | WExchR G D0 D1 A B => mkSeq G (D0 ++ B :: A :: D1)
  | WCut G D P L _ => mkSeq (G ++ P) (D ++ L)
  | WRefl G D s t => mkSeq G (Eq s t t :: D)
  | WEqL G D s t u A j =>
      mkSeq (G ++ Eq s t u :: sub_formula s A j u :: nil) D
  | WEqR G D s t u A j =>
      mkSeq (G ++ [Eq s t u]) (sub_formula s A j u :: D)
  | WAndL G D A B => mkSeq (G ++ [And A B]) D
  | WAndR G D A B => mkSeq G (And A B :: D)
  | WOrL G D A B => mkSeq (G ++ [Or A B]) D
  | WOrR G D A B => mkSeq G (Or A B :: D)
  | WImpL G D P L A B => mkSeq (G ++ P ++ [Imp A B]) (D ++ L)
  | WImpR G D A B => mkSeq G (Imp A B :: D)
  | WAllL G D s A _ => mkSeq (G ++ [All s A]) D
  | WAllR G D s A _ => mkSeq G (All s A :: D)
  | WExL G D s A _ => mkSeq (G ++ [Ex s A]) D
  | WExR G D s A _ => mkSeq G (Ex s A :: D)
  | WQAx G D A => mkSeq G (A :: D)
  end.

Definition eigen_freshb (s : sort) (y : nat) (S : sequent) : bool :=
  negb (var_mem (s, y) (fv_sequent S)).

Definition gq_sideb (w : gq_witness) : bool :=
  match w with
  | WAllR G D s A y => eigen_freshb s y (mkSeq G (All s A :: D))
  | WExL G D s A y => eigen_freshb s y (mkSeq (G ++ [Ex s A]) D)
  | WQAx _ _ A => qaxiomb A
  | _ => true
  end.

Definition gq_parameter_wtb (k : nat) (w : gq_witness) : bool :=
  match w with
  | WRefl _ _ s t => WT k t s
  | WEqL _ _ s t u _ _ | WEqR _ _ s t u _ _ => WT k t s && WT k u s
  | WAllL _ _ s _ t | WExR _ _ s _ t => WT k t s
  | WAllR _ _ s _ _ | WExL _ _ s _ _ => stage_sortb k s
  | _ => true
  end.

Definition gq_validb (k : nat) (w : gq_witness) : bool :=
  (forallb (sequent_wtb k) (gq_premises w ++ [gq_conclusion w]) &&
   gq_sideb w) && gq_parameter_wtb k w.

Definition GQRule (k : nat) (prems : list sequent) (concl : sequent) : Prop :=
  exists w,
    gq_validb k w = true /\
    prems = gq_premises w /\ concl = gq_conclusion w.

(** * 5. Rule schemes and the canonical finite certificate registry *)

Inductive sch_term : Type :=
| STMVar (s : sort) (name : nat)
| STVar (s : sort) (index : nat)
| STFun (f : fsym) (args : sch_terms)
with sch_terms : Type :=
| STNil
| STCons (head : sch_term) (tail : sch_terms).

Inductive sch_formula : Type :=
| SFMVar (name : nat)
| SBot
| SEq (s : sort) (left right : sch_term)
| SRel (r : rsym) (args : sch_terms)
| SAnd (left right : sch_formula)
| SOr (left right : sch_formula)
| SImp (left right : sch_formula)
| SAll (s : sort) (body : sch_formula)
| SEx (s : sort) (body : sch_formula)
| SSubFm (s : sort) (body : sch_formula) (index : nat) (replacement : sch_term).

Inductive sch_ctx_atom : Type :=
| SCFormula (A : sch_formula)
| SCContext (name : nat).

Definition sch_context := list sch_ctx_atom.
Record sch_sequent : Type := mkSchSeq {
  sch_antecedent : sch_context;
  sch_succedent : sch_context
}.

Inductive side_condition : Type :=
| SideSortEq (left right : sort)
| SideCodeEq (left right : nat)
| SideEigenFresh (s : sort) (index : nat) (conclusion : sch_sequent).

Record rule_scheme : Type := mkScheme {
  scheme_tag : nat;
  scheme_premises : list sch_sequent;
  scheme_conclusion : sch_sequent;
  scheme_conditions : list side_condition
}.

Record instantiation : Type := mkInst {
  inst_terms : list (nat * sort * term);
  inst_formulas : list (nat * formula);
  inst_contexts : list (nat * context)
}.

Fixpoint lookup_term_inst (name : nat) (s : sort)
    (xs : list (nat * sort * term)) : option term :=
  match xs with
  | [] => None
  | (m, r, t) :: ys =>
      if Nat.eqb name m && sort_eqb s r then Some t
      else lookup_term_inst name s ys
  end.

Fixpoint lookup_formula_inst (name : nat)
    (xs : list (nat * formula)) : option formula :=
  match xs with
  | [] => None
  | (m, A) :: ys => if Nat.eqb name m then Some A else lookup_formula_inst name ys
  end.

Fixpoint lookup_context_inst (name : nat)
    (xs : list (nat * context)) : option context :=
  match xs with
  | [] => None
  | (m, G) :: ys => if Nat.eqb name m then Some G else lookup_context_inst name ys
  end.

Fixpoint instantiate_term (sigma : instantiation) (t : sch_term) : option term :=
  match t with
  | STMVar s n => lookup_term_inst n s (inst_terms sigma)
  | STVar s i => Some (TVar s i)
  | STFun f ts =>
      match instantiate_terms sigma ts with
      | Some us => Some (TFun f us)
      | None => None
      end
  end
with instantiate_terms (sigma : instantiation) (ts : sch_terms) : option terms :=
  match ts with
  | STNil => Some TNil
  | STCons t us =>
      match instantiate_term sigma t, instantiate_terms sigma us with
      | Some v, Some vs => Some (TCons v vs)
      | _, _ => None
      end
  end.

Fixpoint instantiate_formula (sigma : instantiation) (A : sch_formula)
    : option formula :=
  match A with
  | SFMVar n => lookup_formula_inst n (inst_formulas sigma)
  | SBot => Some Bot
  | SEq s t u =>
      match instantiate_term sigma t, instantiate_term sigma u with
      | Some v, Some w => Some (Eq s v w)
      | _, _ => None
      end
  | SRel r ts =>
      match instantiate_terms sigma ts with
      | Some us => Some (Rel r us)
      | None => None
      end
  | SAnd B C =>
      match instantiate_formula sigma B, instantiate_formula sigma C with
      | Some D, Some E => Some (And D E)
      | _, _ => None
      end
  | SOr B C =>
      match instantiate_formula sigma B, instantiate_formula sigma C with
      | Some D, Some E => Some (Or D E)
      | _, _ => None
      end
  | SImp B C =>
      match instantiate_formula sigma B, instantiate_formula sigma C with
      | Some D, Some E => Some (Imp D E)
      | _, _ => None
      end
  | SAll s B =>
      match instantiate_formula sigma B with Some C => Some (All s C) | None => None end
  | SEx s B =>
      match instantiate_formula sigma B with Some C => Some (Ex s C) | None => None end
  | SSubFm s B i t =>
      match instantiate_formula sigma B, instantiate_term sigma t with
      | Some C, Some u => Some (sub_formula s C i u)
      | _, _ => None
      end
  end.

Fixpoint instantiate_context (sigma : instantiation) (G : sch_context)
    : option context :=
  match G with
  | [] => Some []
  | SCFormula A :: H =>
      match instantiate_formula sigma A, instantiate_context sigma H with
      | Some B, Some D => Some (B :: D)
      | _, _ => None
      end
  | SCContext n :: H =>
      match lookup_context_inst n (inst_contexts sigma), instantiate_context sigma H with
      | Some D, Some E => Some (D ++ E)
      | _, _ => None
      end
  end.

Definition instantiate_sequent (sigma : instantiation) (S : sch_sequent)
    : option sequent :=
  match instantiate_context sigma (sch_antecedent S),
        instantiate_context sigma (sch_succedent S) with
  | Some G, Some D => Some (mkSeq G D)
  | _, _ => None
  end.

Fixpoint instantiate_sequents (sigma : instantiation) (ss : list sch_sequent)
    : option (list sequent) :=
  match ss with
  | [] => Some []
  | ss0 :: us =>
      match instantiate_sequent sigma ss0, instantiate_sequents sigma us with
      | Some T, Some vs => Some (T :: vs)
      | _, _ => None
      end
  end.

Definition side_conditionb (sigma : instantiation) (c : side_condition) : bool :=
  match c with
  | SideSortEq s r => sort_eqb s r
  | SideCodeEq m n => Nat.eqb m n
  | SideEigenFresh s i ss0 =>
      match instantiate_sequent sigma ss0 with
      | Some T => eigen_freshb s i T
      | None => false
      end
  end.

Definition legal_instantiationb (k : nat) (q : rule_scheme)
    (sigma : instantiation) : bool :=
  match instantiate_sequents sigma (scheme_premises q),
        instantiate_sequent sigma (scheme_conclusion q) with
  | Some ps, Some c =>
      forallb (sequent_wtb k) (ps ++ [c]) &&
      forallb (side_conditionb sigma) (scheme_conditions q)
  | _, _ => false
  end.

Definition sch_H : sch_sequent :=
  mkSchSeq [SCContext 0] [SCContext 1].

Definition sch_P (n : nat) : sch_formula := SRel (RP n) STNil.

Definition qn_left (n : nat) : sch_context :=
  SCContext 0 :: map (fun i => SCFormula (sch_P i)) (seq 0 n).

Definition qn (n : nat) : rule_scheme :=
  mkScheme n [sch_H] (mkSchSeq (qn_left n) [SCContext 1]) [].

Definition identity_scheme (tag : nat) : rule_scheme :=
  mkScheme tag [sch_H] sch_H [].

(** ** 5.1a. Literal equality, sorting, quotation, and scheme-to-scheme
    instantiation.  The latter repairs the source's implicit use of
    [depapp(c_n,id)]: a base instantiation produces ground syntax, whereas
    that canonical dependency step needs an identity endomorphism of scheme
    syntax. *)

Fixpoint sch_term_eqb (t u : sch_term) : bool :=
  match t, u with
  | STMVar s n, STMVar r m | STVar s n, STVar r m =>
      sort_eqb s r && Nat.eqb n m
  | STFun f ts, STFun g us => fsym_eqb f g && sch_terms_eqb ts us
  | _, _ => false
  end
with sch_terms_eqb (ts us : sch_terms) : bool :=
  match ts, us with
  | STNil, STNil => true
  | STCons t ts', STCons u us' => sch_term_eqb t u && sch_terms_eqb ts' us'
  | _, _ => false
  end.

Fixpoint sch_formula_eqb (A B : sch_formula) : bool :=
  match A, B with
  | SFMVar n, SFMVar m => Nat.eqb n m
  | SBot, SBot => true
  | SEq s t u, SEq r v w =>
      sort_eqb s r && sch_term_eqb t v && sch_term_eqb u w
  | SRel p ts, SRel q us => rsym_eqb p q && sch_terms_eqb ts us
  | SAnd A1 A2, SAnd B1 B2
  | SOr A1 A2, SOr B1 B2
  | SImp A1 A2, SImp B1 B2 =>
      sch_formula_eqb A1 B1 && sch_formula_eqb A2 B2
  | SAll s C, SAll r D
  | SEx s C, SEx r D => sort_eqb s r && sch_formula_eqb C D
  | SSubFm s C i t, SSubFm r D j u =>
      sort_eqb s r && sch_formula_eqb C D &&
      Nat.eqb i j && sch_term_eqb t u
  | _, _ => false
  end.

Definition sch_ctx_atom_eqb (a b : sch_ctx_atom) : bool :=
  match a, b with
  | SCFormula A, SCFormula B => sch_formula_eqb A B
  | SCContext n, SCContext m => Nat.eqb n m
  | _, _ => false
  end.

Definition sch_context_eqb := list_eqb sch_ctx_atom_eqb.

Definition sch_sequent_eqb (S T : sch_sequent) : bool :=
  sch_context_eqb (sch_antecedent S) (sch_antecedent T) &&
  sch_context_eqb (sch_succedent S) (sch_succedent T).

Definition sch_sequent_list_eqb := list_eqb sch_sequent_eqb.

Definition side_condition_eqb (c d : side_condition) : bool :=
  match c, d with
  | SideSortEq s r, SideSortEq t u => sort_eqb s t && sort_eqb r u
  | SideCodeEq m n, SideCodeEq p q => Nat.eqb m p && Nat.eqb n q
  | SideEigenFresh s i seq0, SideEigenFresh r j seq1 =>
      sort_eqb s r && Nat.eqb i j && sch_sequent_eqb seq0 seq1
  | _, _ => false
  end.

Definition side_condition_list_eqb := list_eqb side_condition_eqb.

Definition rule_scheme_eqb (q r : rule_scheme) : bool :=
  Nat.eqb (scheme_tag q) (scheme_tag r) &&
  sch_sequent_list_eqb (scheme_premises q) (scheme_premises r) &&
  sch_sequent_eqb (scheme_conclusion q) (scheme_conclusion r) &&
  side_condition_list_eqb (scheme_conditions q) (scheme_conditions r).

Lemma list_eqb_self : forall (A : Type) (eqb : A -> A -> bool),
  (forall x, eqb x x = true) -> forall xs, list_eqb eqb xs xs = true.
Proof.
  intros A eqb H xs. induction xs as [|x xs IH]; cbn.
  - reflexivity.
  - rewrite H, IH. reflexivity.
Qed.

Lemma sch_sort_eqb_refl : forall s, sort_eqb s s = true.
Proof. intros [| |k|k]; cbn; rewrite ?Nat.eqb_refl; reflexivity. Qed.

Lemma sch_list_sort_eqb_refl : forall ss, list_sort_eqb ss ss = true.
Proof. apply list_eqb_self, sch_sort_eqb_refl. Qed.

Lemma sch_fsym_eqb_refl : forall f, fsym_eqb f f = true.
Proof.
  intros [code inputs output| | | | |k source root cert|k|k|k|k|k|k]; cbn;
    rewrite ?Nat.eqb_refl, ?sch_list_sort_eqb_refl, ?sch_sort_eqb_refl;
    reflexivity.
Qed.

Lemma sch_rsym_eqb_refl : forall r, rsym_eqb r r = true.
Proof.
  intros [code inputs| |n|k]; cbn;
    rewrite ?Nat.eqb_refl, ?sch_list_sort_eqb_refl; reflexivity.
Qed.

Lemma sch_term_eqb_refl : forall t, sch_term_eqb t t = true
with sch_terms_eqb_refl : forall ts, sch_terms_eqb ts ts = true.
Proof.
  - intro t. destruct t; cbn.
    + rewrite sch_sort_eqb_refl, Nat.eqb_refl. reflexivity.
    + rewrite sch_sort_eqb_refl, Nat.eqb_refl. reflexivity.
    + rewrite sch_fsym_eqb_refl, sch_terms_eqb_refl. reflexivity.
  - intro ts. destruct ts; cbn.
    + reflexivity.
    + rewrite sch_term_eqb_refl, sch_terms_eqb_refl. reflexivity.
Qed.

Lemma sch_formula_eqb_refl : forall A, sch_formula_eqb A A = true.
Proof.
  induction A; cbn; rewrite ?Nat.eqb_refl, ?sch_sort_eqb_refl,
      ?sch_rsym_eqb_refl, ?sch_term_eqb_refl, ?sch_terms_eqb_refl,
      ?IHA, ?IHA1, ?IHA2; reflexivity.
Qed.

Lemma sch_ctx_atom_eqb_refl : forall a, sch_ctx_atom_eqb a a = true.
Proof. intros [A|n]; cbn; [apply sch_formula_eqb_refl|apply Nat.eqb_refl]. Qed.

Lemma sch_context_eqb_refl : forall G, sch_context_eqb G G = true.
Proof. apply list_eqb_self, sch_ctx_atom_eqb_refl. Qed.

Lemma sch_sequent_eqb_refl : forall S, sch_sequent_eqb S S = true.
Proof.
  intros [G D]. unfold sch_sequent_eqb. cbn.
  rewrite !sch_context_eqb_refl. reflexivity.
Qed.

Lemma sch_sequent_list_eqb_refl : forall ss,
  sch_sequent_list_eqb ss ss = true.
Proof. apply list_eqb_self, sch_sequent_eqb_refl. Qed.

Lemma side_condition_eqb_refl : forall c, side_condition_eqb c c = true.
Proof.
  intros [s r|m n|s i S]; cbn;
    rewrite ?sch_sort_eqb_refl, ?Nat.eqb_refl, ?sch_sequent_eqb_refl;
    reflexivity.
Qed.

Lemma side_condition_list_eqb_refl : forall cs,
  side_condition_list_eqb cs cs = true.
Proof. apply list_eqb_self, side_condition_eqb_refl. Qed.

Lemma rule_scheme_eqb_refl : forall q, rule_scheme_eqb q q = true.
Proof.
  intros [tag ps C cs]. unfold rule_scheme_eqb. cbn.
  rewrite Nat.eqb_refl, sch_sequent_list_eqb_refl,
          sch_sequent_eqb_refl, side_condition_list_eqb_refl.
  reflexivity.
Qed.

Fixpoint sch_term_sort (k : nat) (t : sch_term) : option sort :=
  match t with
  | STMVar s _ | STVar s _ => if stage_sortb k s then Some s else None
  | STFun f ts =>
      if fsym_allowedb k f then
        match sch_terms_sorts k ts with
        | Some actual =>
            if list_sort_eqb actual (fst (fsig f))
            then Some (snd (fsig f)) else None
        | None => None
        end
      else None
  end
with sch_terms_sorts (k : nat) (ts : sch_terms) : option (list sort) :=
  match ts with
  | STNil => Some []
  | STCons t us =>
      match sch_term_sort k t, sch_terms_sorts k us with
      | Some s, Some ss => Some (s :: ss)
      | _, _ => None
      end
  end.

Definition sch_WT (k : nat) (t : sch_term) (s : sort) : bool :=
  match sch_term_sort k t with Some r => sort_eqb r s | None => false end.

Fixpoint sch_formula_wtb (k : nat) (A : sch_formula) : bool :=
  match A with
  | SFMVar _ | SBot => true
  | SEq s t u => stage_sortb k s && sch_WT k t s && sch_WT k u s
  | SRel r ts =>
      rsym_allowedb k r &&
      match sch_terms_sorts k ts with
      | Some actual => list_sort_eqb actual (rsig r)
      | None => false
      end
  | SAnd B C | SOr B C | SImp B C =>
      sch_formula_wtb k B && sch_formula_wtb k C
  | SAll s B | SEx s B => stage_sortb k s && sch_formula_wtb k B
  | SSubFm s B _ t =>
      stage_sortb k s && sch_formula_wtb k B && sch_WT k t s
  end.

Definition sch_ctx_atom_wtb (k : nat) (a : sch_ctx_atom) : bool :=
  match a with SCFormula A => sch_formula_wtb k A | SCContext _ => true end.

Definition sch_context_wtb (k : nat) (G : sch_context) : bool :=
  forallb (sch_ctx_atom_wtb k) G.

Definition sch_sequent_wtb (k : nat) (S : sch_sequent) : bool :=
  sch_context_wtb k (sch_antecedent S) &&
  sch_context_wtb k (sch_succedent S).

Fixpoint quote_term (t : term) : sch_term :=
  match t with
  | TVar s i => STVar s i
  | TFun f ts => STFun f (quote_terms ts)
  end
with quote_terms (ts : terms) : sch_terms :=
  match ts with
  | TNil => STNil
  | TCons t us => STCons (quote_term t) (quote_terms us)
  end.

Fixpoint quote_formula (A : formula) : sch_formula :=
  match A with
  | Bot => SBot
  | Eq s t u => SEq s (quote_term t) (quote_term u)
  | Rel r ts => SRel r (quote_terms ts)
  | And B C => SAnd (quote_formula B) (quote_formula C)
  | Or B C => SOr (quote_formula B) (quote_formula C)
  | Imp B C => SImp (quote_formula B) (quote_formula C)
  | All s B => SAll s (quote_formula B)
  | Ex s B => SEx s (quote_formula B)
  end.

Record sch_instantiation : Type := mkSchInst {
  sch_inst_terms : list (nat * sort * sch_term);
  sch_inst_formulas : list (nat * sch_formula);
  sch_inst_contexts : list (nat * sch_context)
}.

Fixpoint lookup_sch_term_inst (name : nat) (s : sort)
    (xs : list (nat * sort * sch_term)) : option sch_term :=
  match xs with
  | [] => None
  | (m, r, t) :: ys =>
      if Nat.eqb name m && sort_eqb s r then Some t
      else lookup_sch_term_inst name s ys
  end.

Fixpoint lookup_sch_formula_inst (name : nat)
    (xs : list (nat * sch_formula)) : option sch_formula :=
  match xs with
  | [] => None
  | (m, A) :: ys => if Nat.eqb name m then Some A
                    else lookup_sch_formula_inst name ys
  end.

Fixpoint lookup_sch_context_inst (name : nat)
    (xs : list (nat * sch_context)) : option sch_context :=
  match xs with
  | [] => None
  | (m, G) :: ys => if Nat.eqb name m then Some G
                    else lookup_sch_context_inst name ys
  end.

Fixpoint sch_instantiate_term (rho : sch_instantiation) (t : sch_term)
    : option sch_term :=
  match t with
  | STMVar s n => lookup_sch_term_inst n s (sch_inst_terms rho)
  | STVar s i => Some (STVar s i)
  | STFun f ts =>
      match sch_instantiate_terms rho ts with
      | Some us => Some (STFun f us)
      | None => None
      end
  end
with sch_instantiate_terms (rho : sch_instantiation) (ts : sch_terms)
    : option sch_terms :=
  match ts with
  | STNil => Some STNil
  | STCons t us =>
      match sch_instantiate_term rho t, sch_instantiate_terms rho us with
      | Some v, Some vs => Some (STCons v vs)
      | _, _ => None
      end
  end.

Fixpoint sch_instantiate_formula (rho : sch_instantiation) (A : sch_formula)
    : option sch_formula :=
  match A with
  | SFMVar n => lookup_sch_formula_inst n (sch_inst_formulas rho)
  | SBot => Some SBot
  | SEq s t u =>
      match sch_instantiate_term rho t, sch_instantiate_term rho u with
      | Some v, Some w => Some (SEq s v w)
      | _, _ => None
      end
  | SRel r ts =>
      match sch_instantiate_terms rho ts with
      | Some us => Some (SRel r us)
      | None => None
      end
  | SAnd B C =>
      match sch_instantiate_formula rho B, sch_instantiate_formula rho C with
      | Some D, Some E => Some (SAnd D E)
      | _, _ => None
      end
  | SOr B C =>
      match sch_instantiate_formula rho B, sch_instantiate_formula rho C with
      | Some D, Some E => Some (SOr D E)
      | _, _ => None
      end
  | SImp B C =>
      match sch_instantiate_formula rho B, sch_instantiate_formula rho C with
      | Some D, Some E => Some (SImp D E)
      | _, _ => None
      end
  | SAll s B =>
      match sch_instantiate_formula rho B with
      | Some C => Some (SAll s C) | None => None
      end
  | SEx s B =>
      match sch_instantiate_formula rho B with
      | Some C => Some (SEx s C) | None => None
      end
  | SSubFm s B i t =>
      match sch_instantiate_formula rho B, sch_instantiate_term rho t with
      | Some C, Some u => Some (SSubFm s C i u)
      | _, _ => None
      end
  end.

Fixpoint sch_instantiate_context (rho : sch_instantiation) (G : sch_context)
    : option sch_context :=
  match G with
  | [] => Some []
  | SCFormula A :: H =>
      match sch_instantiate_formula rho A, sch_instantiate_context rho H with
      | Some B, Some D => Some (SCFormula B :: D)
      | _, _ => None
      end
  | SCContext n :: H =>
      match lookup_sch_context_inst n (sch_inst_contexts rho),
            sch_instantiate_context rho H with
      | Some D, Some E => Some (D ++ E)
      | _, _ => None
      end
  end.

Definition sch_instantiate_sequent (rho : sch_instantiation) (S : sch_sequent)
    : option sch_sequent :=
  match sch_instantiate_context rho (sch_antecedent S),
        sch_instantiate_context rho (sch_succedent S) with
  | Some G, Some D => Some (mkSchSeq G D)
  | _, _ => None
  end.

Fixpoint sch_instantiate_sequents (rho : sch_instantiation)
    (ss : list sch_sequent) : option (list sch_sequent) :=
  match ss with
  | [] => Some []
  | seq0 :: us =>
      match sch_instantiate_sequent rho seq0, sch_instantiate_sequents rho us with
      | Some seq1, Some vs => Some (seq1 :: vs)
      | _, _ => None
      end
  end.

Definition sch_instantiate_condition (rho : sch_instantiation)
    (c : side_condition) : option side_condition :=
  match c with
  | SideSortEq s r => Some (SideSortEq s r)
  | SideCodeEq m n => Some (SideCodeEq m n)
  | SideEigenFresh s i seq0 =>
      match sch_instantiate_sequent rho seq0 with
      | Some seq1 => Some (SideEigenFresh s i seq1)
      | None => None
      end
  end.

Fixpoint sch_instantiate_conditions (rho : sch_instantiation)
    (cs : list side_condition) : option (list side_condition) :=
  match cs with
  | [] => Some []
  | c :: ds =>
      match sch_instantiate_condition rho c, sch_instantiate_conditions rho ds with
      | Some d, Some es => Some (d :: es)
      | _, _ => None
      end
  end.

Definition sch_instantiate_rule_scheme (rho : sch_instantiation)
    (q : rule_scheme) : option rule_scheme :=
  match sch_instantiate_sequents rho (scheme_premises q),
        sch_instantiate_sequent rho (scheme_conclusion q),
        sch_instantiate_conditions rho (scheme_conditions q) with
  | Some ps, Some C, Some cs => Some (mkScheme (scheme_tag q) ps C cs)
  | _, _, _ => None
  end.

Definition static_side_conditionb (c : side_condition) : bool :=
  match c with
  | SideSortEq s r => sort_eqb s r
  | SideCodeEq m n => Nat.eqb m n
  | SideEigenFresh _ _ _ => true
  end.

Definition sch_legal_instantiationb (q : rule_scheme)
    (rho : sch_instantiation) : bool :=
  match sch_instantiate_rule_scheme rho q with
  | Some r =>
      forallb (sch_sequent_wtb 0)
        (scheme_premises r ++ [scheme_conclusion r]) &&
      forallb static_side_conditionb (scheme_conditions r)
  | None => false
  end.

Inductive sch_gq_witness : Type :=
| SGId (Gamma Delta : sch_context) (A : sch_formula)
| SGBotL (Gamma Delta : sch_context)
| SGWkL (Gamma Delta : sch_context) (A : sch_formula)
| SGWkR (Gamma Delta : sch_context) (A : sch_formula)
| SGCtrL (Gamma Delta : sch_context) (A : sch_formula)
| SGCtrR (Gamma Delta : sch_context) (A : sch_formula)
| SGExchL (Gamma0 Gamma1 Delta : sch_context) (A B : sch_formula)
| SGExchR (Gamma Delta0 Delta1 : sch_context) (A B : sch_formula)
| SGCut (Gamma Delta Pi Lambda : sch_context) (A : sch_formula)
| SGRefl (Gamma Delta : sch_context) (s : sort) (t : sch_term)
| SGEqL (Gamma Delta : sch_context) (s : sort)
        (t u : sch_term) (A : sch_formula) (j : nat)
| SGEqR (Gamma Delta : sch_context) (s : sort)
        (t u : sch_term) (A : sch_formula) (j : nat)
| SGAndL (Gamma Delta : sch_context) (A B : sch_formula)
| SGAndR (Gamma Delta : sch_context) (A B : sch_formula)
| SGOrL (Gamma Delta : sch_context) (A B : sch_formula)
| SGOrR (Gamma Delta : sch_context) (A B : sch_formula)
| SGImpL (Gamma Delta Pi Lambda : sch_context) (A B : sch_formula)
| SGImpR (Gamma Delta : sch_context) (A B : sch_formula)
| SGAllL (Gamma Delta : sch_context) (s : sort)
         (A : sch_formula) (t : sch_term)
| SGAllR (Gamma Delta : sch_context) (s : sort)
         (A : sch_formula) (eigen : nat)
| SGExL (Gamma Delta : sch_context) (s : sort)
        (A : sch_formula) (eigen : nat)
| SGExR (Gamma Delta : sch_context) (s : sort)
        (A : sch_formula) (t : sch_term)
| SGQAx (Gamma Delta : sch_context) (A : formula).

Definition sch_gq_premises (w : sch_gq_witness) : list sch_sequent :=
  match w with
  | SGId _ _ _ | SGBotL _ _ | SGRefl _ _ _ _ | SGQAx _ _ _ => []
  | SGWkL G D _ | SGWkR G D _ => [mkSchSeq G D]
  | SGCtrL G D A => [mkSchSeq (G ++ [SCFormula A; SCFormula A]) D]
  | SGCtrR G D A => [mkSchSeq G (SCFormula A :: SCFormula A :: D)]
  | SGExchL G0 G1 D A B =>
      [mkSchSeq (G0 ++ SCFormula A :: SCFormula B :: G1) D]
  | SGExchR G D0 D1 A B =>
      [mkSchSeq G (D0 ++ SCFormula A :: SCFormula B :: D1)]
  | SGCut G D P L A =>
      [mkSchSeq G (SCFormula A :: D); mkSchSeq (P ++ [SCFormula A]) L]
  | SGEqL G D s t _ A j =>
      [mkSchSeq (G ++ [SCFormula (SSubFm s A j t)]) D]
  | SGEqR G D s t _ A j =>
      [mkSchSeq G (SCFormula (SSubFm s A j t) :: D)]
  | SGAndL G D A B => [mkSchSeq (G ++ [SCFormula A; SCFormula B]) D]
  | SGAndR G D A B =>
      [mkSchSeq G (SCFormula A :: D); mkSchSeq G (SCFormula B :: D)]
  | SGOrL G D A B =>
      [mkSchSeq (G ++ [SCFormula A]) D; mkSchSeq (G ++ [SCFormula B]) D]
  | SGOrR G D A B => [mkSchSeq G (SCFormula A :: SCFormula B :: D)]
  | SGImpL G D P L A B =>
      [mkSchSeq G (SCFormula A :: D); mkSchSeq (P ++ [SCFormula B]) L]
  | SGImpR G D A B => [mkSchSeq (G ++ [SCFormula A]) (SCFormula B :: D)]
  | SGAllL G D s A t =>
      [mkSchSeq (G ++ [SCFormula (SSubFm s A 0 t)]) D]
  | SGAllR G D s A y =>
      [mkSchSeq G (SCFormula (SSubFm s A 0 (STVar s y)) :: D)]
  | SGExL G D s A y =>
      [mkSchSeq (G ++ [SCFormula (SSubFm s A 0 (STVar s y))]) D]
  | SGExR G D s A t =>
      [mkSchSeq G (SCFormula (SSubFm s A 0 t) :: D)]
  end.

Definition sch_gq_conclusion (w : sch_gq_witness) : sch_sequent :=
  match w with
  | SGId G D A => mkSchSeq (G ++ [SCFormula A]) (SCFormula A :: D)
  | SGBotL G D => mkSchSeq (G ++ [SCFormula SBot]) D
  | SGWkL G D A => mkSchSeq (G ++ [SCFormula A]) D
  | SGWkR G D A => mkSchSeq G (SCFormula A :: D)
  | SGCtrL G D A => mkSchSeq (G ++ [SCFormula A]) D
  | SGCtrR G D A => mkSchSeq G (SCFormula A :: D)
  | SGExchL G0 G1 D A B =>
      mkSchSeq (G0 ++ SCFormula B :: SCFormula A :: G1) D
  | SGExchR G D0 D1 A B =>
      mkSchSeq G (D0 ++ SCFormula B :: SCFormula A :: D1)
  | SGCut G D P L _ => mkSchSeq (G ++ P) (D ++ L)
  | SGRefl G D s t => mkSchSeq G (SCFormula (SEq s t t) :: D)
  | SGEqL G D s t u A j =>
      mkSchSeq
        (G ++ SCFormula (SEq s t u) ::
              SCFormula (SSubFm s A j u) :: nil) D
  | SGEqR G D s t u A j =>
      mkSchSeq (G ++ [SCFormula (SEq s t u)])
        (SCFormula (SSubFm s A j u) :: D)
  | SGAndL G D A B => mkSchSeq (G ++ [SCFormula (SAnd A B)]) D
  | SGAndR G D A B => mkSchSeq G (SCFormula (SAnd A B) :: D)
  | SGOrL G D A B => mkSchSeq (G ++ [SCFormula (SOr A B)]) D
  | SGOrR G D A B => mkSchSeq G (SCFormula (SOr A B) :: D)
  | SGImpL G D P L A B =>
      mkSchSeq (G ++ P ++ [SCFormula (SImp A B)]) (D ++ L)
  | SGImpR G D A B => mkSchSeq G (SCFormula (SImp A B) :: D)
  | SGAllL G D s A _ => mkSchSeq (G ++ [SCFormula (SAll s A)]) D
  | SGAllR G D s A _ => mkSchSeq G (SCFormula (SAll s A) :: D)
  | SGExL G D s A _ => mkSchSeq (G ++ [SCFormula (SEx s A)]) D
  | SGExR G D s A _ => mkSchSeq G (SCFormula (SEx s A) :: D)
  | SGQAx G D A => mkSchSeq G (SCFormula (quote_formula A) :: D)
  end.

Definition sch_gq_conditions (w : sch_gq_witness) : list side_condition :=
  match w with
  | SGAllR G D s A y =>
      [SideEigenFresh s y (mkSchSeq G (SCFormula (SAll s A) :: D))]
  | SGExL G D s A y =>
      [SideEigenFresh s y (mkSchSeq (G ++ [SCFormula (SEx s A)]) D)]
  | _ => []
  end.

Definition sch_gq_validb (w : sch_gq_witness) : bool :=
  forallb (sch_sequent_wtb 0)
    (sch_gq_premises w ++ [sch_gq_conclusion w]) &&
  match w with SGQAx _ _ A => qaxiomb A | _ => true end.

Inductive cert_id : Type :=
| CChain (index : nat)
| CHa | CHaMinus | CHb | CHbMinus.

Definition cert_id_eqb (c d : cert_id) : bool :=
  match c, d with
  | CChain n, CChain m => Nat.eqb n m
  | CHa, CHa | CHaMinus, CHaMinus | CHb, CHb | CHbMinus, CHbMinus => true
  | _, _ => false
  end.

Definition cert_encode (c : cert_id) : nat :=
  match c with
  | CHa => 0 | CHaMinus => 1 | CHb => 2 | CHbMinus => 3
  | CChain n => 4 + n
  end.

Definition cert_decode (n : nat) : cert_id :=
  match n with
  | 0 => CHa | 1 => CHaMinus | 2 => CHb | 3 => CHbMinus
  | S (S (S (S m))) => CChain m
  end.

Lemma cert_decode_encode : forall c, cert_decode (cert_encode c) = c.
Proof. destruct c; reflexivity. Qed.

Definition root_scheme (c : cert_id) : rule_scheme :=
  match c with
  | CChain n => qn n
  | CHa => identity_scheme 100
  | CHaMinus => identity_scheme 101
  | CHb => identity_scheme 102
  | CHbMinus => identity_scheme 103
  end.

Definition root_code (c : cert_id) : nat := scheme_tag (root_scheme c).

Definition cert_dependencies (c : cert_id) : list cert_id :=
  match c with CChain (S n) => [CChain n] | _ => [] end.

Definition cert_source (c : cert_id) : nat :=
  match c with CChain n => n | _ => 0 end.

Inductive canonical_skeleton : Type :=
| SkChainZero
| SkChainStep (previous : cert_id) (weaken_by : nat)
| SkIdentity.

Record certificate_data : Type := mkCertificate {
  certificate_root_tag : nat;
  certificate_skeleton : canonical_skeleton;
  certificate_dependencies : list cert_id
}.

Definition decode_certificate (c : cert_id) : certificate_data :=
  match c with
  | CChain 0 => mkCertificate 0 SkChainZero []
  | CChain (S n) => mkCertificate (S n) (SkChainStep (CChain n) n) [CChain n]
  | CHa => mkCertificate 100 SkIdentity []
  | CHaMinus => mkCertificate 101 SkIdentity []
  | CHb => mkCertificate 102 SkIdentity []
  | CHbMinus => mkCertificate 103 SkIdentity []
  end.

Definition cert_list_eqb := list_eqb cert_id_eqb.

Definition PCOK (d : certificate_data) : bool :=
  match certificate_skeleton d with
  | SkChainZero =>
      Nat.eqb (certificate_root_tag d) 0 &&
      cert_list_eqb (certificate_dependencies d) []
  | SkChainStep previous n =>
      Nat.eqb (certificate_root_tag d) (S n) &&
      cert_id_eqb previous (CChain n) &&
      cert_list_eqb (certificate_dependencies d) [CChain n]
  | SkIdentity =>
      ((certificate_root_tag d =? 100) || (certificate_root_tag d =? 101) ||
       (certificate_root_tag d =? 102) || (certificate_root_tag d =? 103)) &&
      cert_list_eqb (certificate_dependencies d) []
  end.

Theorem canonical_certificates_check :
  forall c, PCOK (decode_certificate c) = true.
Proof.
  intros c. destruct c; try reflexivity.
  destruct index; cbn; try reflexivity. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Definition Reg_H (d : certificate_data) : Prop :=
  exists c, d = decode_certificate c.

(** ** 5.2--5.3. General open skeletons and the literal post-order
    certificate checker.  This is intentionally separate from the compact
    canonical certificate decoder above: [open_certificate] is the full
    certificate language, while [cert_id] is exactly the registered family
    used by the stage dynamics. *)

Inductive sch_exchange_side : Type := SchLeft | SchRight.

Record sch_adjacent_exchange : Type := mkSchExchange {
  sch_exchange_side_of : sch_exchange_side;
  sch_exchange_index : nat
}.

Fixpoint swap_adjacent_sch_formulas (i : nat) (G : sch_context)
    : option sch_context :=
  match i, G with
  | 0, SCFormula A :: SCFormula B :: H =>
      Some (SCFormula B :: SCFormula A :: H)
  | S j, a :: H =>
      match swap_adjacent_sch_formulas j H with
      | Some D => Some (a :: D)
      | None => None
      end
  | _, _ => None
  end.

Definition apply_sch_exchange (e : sch_adjacent_exchange) (S : sch_sequent)
    : option sch_sequent :=
  match sch_exchange_side_of e with
  | SchLeft =>
      match swap_adjacent_sch_formulas (sch_exchange_index e)
              (sch_antecedent S) with
      | Some G => Some (mkSchSeq G (sch_succedent S))
      | None => None
      end
  | SchRight =>
      match swap_adjacent_sch_formulas (sch_exchange_index e)
              (sch_succedent S) with
      | Some D => Some (mkSchSeq (sch_antecedent S) D)
      | None => None
      end
  end.

Fixpoint execute_sch_exchanges (es : list sch_adjacent_exchange)
    (S : sch_sequent) : option sch_sequent :=
  match es with
  | [] => Some S
  | e :: fs =>
      match apply_sch_exchange e S with
      | Some T => execute_sch_exchanges fs T
      | None => None
      end
  end.

Inductive open_tree : Type :=
| OpenHole (index : nat) (label : sch_sequent)
| OpenQAxiom (axiom : formula) (label : sch_sequent)
| OpenGQ (rule : sch_gq_witness) (label : sch_sequent)
         (children : open_forest)
| OpenDepApp (dependency : cert_id) (rho : sch_instantiation)
             (label : sch_sequent) (children : open_forest)
| OpenPerm (exchanges : list sch_adjacent_exchange)
           (child : open_tree) (label : sch_sequent)
with open_forest : Type :=
| OpenNil
| OpenCons (head : open_tree) (tail : open_forest).

Definition open_root (p : open_tree) : sch_sequent :=
  match p with
  | OpenHole _ lbl | OpenQAxiom _ lbl | OpenGQ _ lbl _
  | OpenDepApp _ _ lbl _ | OpenPerm _ _ lbl => lbl
  end.

Fixpoint open_forest_roots (ps : open_forest) : list sch_sequent :=
  match ps with
  | OpenNil => []
  | OpenCons p qs => open_root p :: open_forest_roots qs
  end.

Fixpoint open_dependencies (p : open_tree) : list cert_id :=
  match p with
  | OpenHole _ _ | OpenQAxiom _ _ => []
  | OpenGQ _ _ ps => open_forest_dependencies ps
  | OpenDepApp d _ _ ps => d :: open_forest_dependencies ps
  | OpenPerm _ q _ => open_dependencies q
  end
with open_forest_dependencies (ps : open_forest) : list cert_id :=
  match ps with
  | OpenNil => []
  | OpenCons p qs => open_dependencies p ++ open_forest_dependencies qs
  end.

Definition instantiated_dependency_conditions (d : cert_id)
    (rho : sch_instantiation) : list side_condition :=
  match sch_instantiate_conditions rho (scheme_conditions (root_scheme d)) with
  | Some cs => cs
  | None => []
  end.

Fixpoint open_obligations (p : open_tree) : list side_condition :=
  match p with
  | OpenHole _ _ | OpenQAxiom _ _ => []
  | OpenGQ w _ ps => sch_gq_conditions w ++ open_forest_obligations ps
  | OpenDepApp d rho _ ps =>
      instantiated_dependency_conditions d rho ++ open_forest_obligations ps
  | OpenPerm _ q _ => open_obligations q
  end
with open_forest_obligations (ps : open_forest) : list side_condition :=
  match ps with
  | OpenNil => []
  | OpenCons p qs => open_obligations p ++ open_forest_obligations qs
  end.

Fixpoint open_tree_check (q : rule_scheme) (p : open_tree) : bool :=
  match p with
  | OpenHole i lbl =>
      match nth_error (scheme_premises q) i with
      | Some target => sch_sequent_eqb lbl target
      | None => false
      end
  | OpenQAxiom A lbl =>
      qaxiomb A &&
      sch_sequent_eqb lbl (mkSchSeq [] [SCFormula (quote_formula A)])
  | OpenGQ w lbl ps =>
      sch_gq_validb w &&
      sch_sequent_list_eqb (open_forest_roots ps) (sch_gq_premises w) &&
      sch_sequent_eqb lbl (sch_gq_conclusion w) &&
      open_forest_check q ps
  | OpenDepApp d rho lbl ps =>
      match sch_instantiate_rule_scheme rho (root_scheme d) with
      | Some r =>
          sch_legal_instantiationb (root_scheme d) rho &&
          sch_sequent_list_eqb (open_forest_roots ps) (scheme_premises r) &&
          sch_sequent_eqb lbl (scheme_conclusion r) &&
          open_forest_check q ps
      | None => false
      end
  | OpenPerm es child lbl =>
      open_tree_check q child &&
      match execute_sch_exchanges es (open_root child) with
      | Some target => sch_sequent_eqb target lbl
      | None => false
      end
  end
with open_forest_check (q : rule_scheme) (ps : open_forest) : bool :=
  match ps with
  | OpenNil => true
  | OpenCons p qs => open_tree_check q p && open_forest_check q qs
  end.

Definition cert_id_memberb (d : cert_id) (ds : list cert_id) : bool :=
  existsb (cert_id_eqb d) ds.

Definition same_cert_setb (ds es : list cert_id) : bool :=
  forallb (fun d => cert_id_memberb d es) ds &&
  forallb (fun e => cert_id_memberb e ds) es.

Fixpoint strictly_increasing_cert_codes (ds : list cert_id) : bool :=
  match ds with
  | [] => true
  | d :: rest =>
      match rest with
      | [] => true
      | e :: _ =>
          Nat.ltb (cert_encode d) (cert_encode e) &&
          strictly_increasing_cert_codes rest
      end
  end.

Definition obligation_declaredb (q : rule_scheme) (c : side_condition) : bool :=
  match c with
  | SideEigenFresh _ _ _ => existsb (side_condition_eqb c) (scheme_conditions q)
  | SideSortEq s r => sort_eqb s r
  | SideCodeEq m n => Nat.eqb m n
  end.

Record open_certificate : Type := mkOpenCertificate {
  open_certificate_root : rule_scheme;
  open_certificate_skeleton : open_tree;
  open_certificate_dependencies : list cert_id
}.

Definition GeneralPCOK (c : open_certificate) : bool :=
  let q := open_certificate_root c in
  let p := open_certificate_skeleton c in
  let ds := open_certificate_dependencies c in
  forallb (sch_sequent_wtb 0)
    (scheme_premises q ++ [scheme_conclusion q]) &&
  forallb static_side_conditionb (scheme_conditions q) &&
  open_tree_check q p &&
  sch_sequent_eqb (open_root p) (scheme_conclusion q) &&
  strictly_increasing_cert_codes ds &&
  same_cert_setb ds (open_dependencies p) &&
  forallb (obligation_declaredb q) (open_obligations p).

Definition qn_schematic_identity : sch_instantiation :=
  mkSchInst [] []
    [(0, [SCContext 0]); (1, [SCContext 1])].

Definition canonical_open_skeleton (n : nat) : open_tree :=
  match n with
  | 0 => OpenHole 0 sch_H
  | S j =>
      let dep :=
        OpenDepApp (CChain j) qn_schematic_identity
          (scheme_conclusion (qn j))
          (OpenCons (OpenHole 0 sch_H) OpenNil) in
      OpenGQ
        (SGWkL (qn_left j) [SCContext 1] (sch_P j))
        (scheme_conclusion (qn (S j)))
        (OpenCons dep OpenNil)
  end.

Definition canonical_open_certificate (c : cert_id) : open_certificate :=
  match c with
  | CChain n =>
      mkOpenCertificate (qn n) (canonical_open_skeleton n)
        (match n with 0 => [] | S j => [CChain j] end)
  | CHa => mkOpenCertificate (identity_scheme 100) (OpenHole 0 sch_H) []
  | CHaMinus => mkOpenCertificate (identity_scheme 101) (OpenHole 0 sch_H) []
  | CHb => mkOpenCertificate (identity_scheme 102) (OpenHole 0 sch_H) []
  | CHbMinus => mkOpenCertificate (identity_scheme 103) (OpenHole 0 sch_H) []
  end.

(** The registered family is checked by the full open-skeleton checker, not
    merely by the compact tag checker used for fast stage computation. *)

Lemma seq_zero_succ : forall n,
  seq 0 (S n) = seq 0 n ++ [n].
Proof. intro n. apply seq_S. Qed.

Lemma sch_instantiate_sch_P_identity : forall n,
  sch_instantiate_formula qn_schematic_identity (sch_P n) = Some (sch_P n).
Proof. reflexivity. Qed.

Lemma sch_instantiate_P_context_identity : forall n,
  sch_instantiate_context qn_schematic_identity
    (map (fun i => SCFormula (sch_P i)) (seq 0 n)) =
  Some (map (fun i => SCFormula (sch_P i)) (seq 0 n)).
Proof.
  intro n. induction (seq 0 n) as [|i is IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma sch_instantiate_qn_identity : forall n,
  sch_instantiate_rule_scheme qn_schematic_identity (qn n) = Some (qn n).
Proof.
  intro n. unfold sch_instantiate_rule_scheme, qn, sch_H, qn_left.
  cbn. unfold sch_instantiate_sequent. cbn.
  rewrite sch_instantiate_P_context_identity. reflexivity.
Qed.

Lemma qn_left_succ : forall n,
  qn_left (S n) = qn_left n ++ [SCFormula (sch_P n)].
Proof.
  intro n. unfold qn_left. rewrite seq_zero_succ, map_app. reflexivity.
Qed.

Lemma qn_schemes_well_sorted : forall n,
  forallb (sch_sequent_wtb 0)
    (scheme_premises (qn n) ++ [scheme_conclusion (qn n)]) = true.
Proof.
  intro n. unfold qn, sch_H, qn_left. cbn.
  induction (seq 0 n) as [|i is IH]; cbn in *.
  - reflexivity.
  - exact IH.
Qed.

Lemma qn_conclusion_well_sorted : forall n,
  sch_sequent_wtb 0 (scheme_conclusion (qn n)) = true.
Proof.
  intro n. unfold qn, qn_left. cbn.
  induction (seq 0 n) as [|i is IH]; cbn in *.
  - reflexivity.
  - exact IH.
Qed.

Lemma qn_weaken_witness_valid : forall n,
  sch_gq_validb (SGWkL (qn_left n) [SCContext 1] (sch_P n)) = true.
Proof.
  intro n. unfold sch_gq_validb. cbn [sch_gq_premises sch_gq_conclusion].
  rewrite <- qn_left_succ.
  change
    ((sch_sequent_wtb 0 (scheme_conclusion (qn n)) &&
      (sch_sequent_wtb 0 (scheme_conclusion (qn (S n))) && true)) &&
     true = true).
  rewrite !qn_conclusion_well_sorted. reflexivity.
Qed.

Lemma qn_static_conditions : forall n,
  forallb static_side_conditionb (scheme_conditions (qn n)) = true.
Proof. reflexivity. Qed.

Lemma qn_premises_exact : forall n, scheme_premises (qn n) = [sch_H].
Proof. reflexivity. Qed.

Lemma qn_conclusion_exact : forall n,
  scheme_conclusion (qn n) = mkSchSeq (qn_left n) [SCContext 1].
Proof. reflexivity. Qed.

Lemma qn_identity_dependency_conditions : forall n,
  instantiated_dependency_conditions (CChain n) qn_schematic_identity = [].
Proof. intro n. unfold instantiated_dependency_conditions, root_scheme, qn. reflexivity. Qed.

Theorem canonical_open_certificates_check : forall c,
  GeneralPCOK (canonical_open_certificate c) = true.
Proof.
  intro c. destruct c as [n| | | |]; try reflexivity.
  destruct n as [|n].
  - reflexivity.
  - unfold canonical_open_certificate, GeneralPCOK.
    cbn [canonical_open_skeleton open_tree_check open_forest_check
         sch_gq_validb sch_gq_premises sch_gq_conclusion
         open_forest_roots root_scheme open_certificate_root
         open_certificate_skeleton open_certificate_dependencies].
    rewrite qn_schemes_well_sorted, sch_instantiate_qn_identity.
    unfold sch_legal_instantiationb.
    rewrite sch_instantiate_qn_identity, qn_schemes_well_sorted.
    rewrite !qn_static_conditions, qn_weaken_witness_valid.
    cbn [sch_gq_premises sch_gq_conclusion qn sch_H
         open_root open_dependencies open_forest_dependencies open_obligations
         open_forest_obligations
         strictly_increasing_cert_codes same_cert_setb cert_id_memberb
         cert_id_eqb].
    rewrite !qn_premises_exact, !qn_conclusion_exact, qn_left_succ,
            qn_identity_dependency_conditions.
    cbn [sch_gq_conditions instantiated_dependency_conditions
         same_cert_setb cert_id_memberb cert_id_eqb].
    rewrite !sch_sequent_eqb_refl, !sch_sequent_list_eqb_refl.
    unfold same_cert_setb, cert_id_memberb.
    simpl. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Theorem compact_and_open_checkers_agree_on_registry : forall c,
  PCOK (decode_certificate c) =
  GeneralPCOK (canonical_open_certificate c).
Proof.
  intro c. rewrite canonical_certificates_check,
                   canonical_open_certificates_check. reflexivity.
Qed.

Definition registered_PCOK (c : cert_id) : bool :=
  GeneralPCOK (canonical_open_certificate c).

Lemma registered_PCOK_true : forall c, registered_PCOK c = true.
Proof.
  intro c. unfold registered_PCOK. apply canonical_open_certificates_check.
Qed.

Definition OpenReg_H (c : open_certificate) : Prop :=
  exists d, c = canonical_open_certificate d.

(** * 6. Certification history, source, Low_k, and bounded enumeration *)

Fixpoint INX (c : cert_id) (k : nat) {struct k} : bool :=
  match k with
  | 0 => false
  | S j =>
      INX c j ||
      (registered_PCOK c &&
       forallb (fun d => INX d j) (cert_dependencies c))
  end.

Definition dep_subsetb (c : cert_id) (k : nat) : bool :=
  forallb (fun d => INX d k) (cert_dependencies c).

Theorem INX_zero : forall c, INX c 0 = false.
Proof. reflexivity. Qed.

Theorem INX_step_equation : forall c k,
  INX c (S k) =
  (INX c k ||
   (registered_PCOK c && dep_subsetb c k)).
Proof.
  reflexivity.
Qed.

Lemma INX_chain_closed : forall k n,
  INX (CChain n) k = Nat.ltb n k.
Proof.
  induction k as [| k IH]; intro n.
  - reflexivity.
  - rewrite INX_step_equation, registered_PCOK_true. unfold dep_subsetb. destruct n.
    + cbn. destruct (INX (CChain 0) k); reflexivity.
    + cbn [cert_dependencies forallb]. rewrite !IH, !andb_true_r, !andb_true_l.
      apply (proj2 (eq_iff_eq_true _ _)).
      rewrite orb_true_iff, !Nat.ltb_lt. lia.
Qed.

Lemma INX_identity_closed : forall k c,
  (c = CHa \/ c = CHaMinus \/ c = CHb \/ c = CHbMinus) ->
  INX c k = Nat.ltb 0 k.
Proof.
  induction k as [| k IH]; intros c Hc.
  - reflexivity.
  - rewrite INX_step_equation, registered_PCOK_true. unfold dep_subsetb.
    destruct Hc as [-> | [-> | [-> | ->]]]; cbn;
      destruct (INX _ k); reflexivity.
Qed.

Theorem canonical_Xk : forall k c,
  INX c k = true <->
  match k with
  | 0 => False
  | S _ =>
      match c with CChain n => n < k | _ => True end
  end.
Proof.
  intros k c. destruct c.
  - rewrite INX_chain_closed, Nat.ltb_lt. destruct k; cbn; lia.
  - rewrite INX_identity_closed by tauto. rewrite Nat.ltb_lt. destruct k; cbn; lia.
  - rewrite INX_identity_closed by tauto. rewrite Nat.ltb_lt. destruct k; cbn; lia.
  - rewrite INX_identity_closed by tauto. rewrite Nat.ltb_lt. destruct k; cbn; lia.
  - rewrite INX_identity_closed by tauto. rewrite Nat.ltb_lt. destruct k; cbn; lia.
Qed.

Record low_value : Type := mkLow {
  low_source : nat;
  low_root : nat;
  low_certificate : cert_id
}.

Definition low_value_eqb (u v : low_value) : bool :=
  Nat.eqb (low_source u) (low_source v) &&
  Nat.eqb (low_root u) (low_root v) &&
  cert_id_eqb (low_certificate u) (low_certificate v).

Definition low_of_cert (c : cert_id) : low_value :=
  mkLow (cert_source c) (root_code c) c.

Definition low_okb (k : nat) (u : low_value) : bool :=
  Nat.ltb (low_source u) k &&
  INX (low_certificate u) k &&
  Nat.eqb (low_source u) (cert_source (low_certificate u)) &&
  Nat.eqb (low_root u) (root_code (low_certificate u)).

Definition cert_prefix (n : nat) : list cert_id :=
  map cert_decode (seq 0 (S n)).

Definition e_k (k n : nat) : list low_value :=
  map low_of_cert (filter (fun c => INX c k) (cert_prefix n)).

Definition enum_term (k n : nat) : term :=
  TFun (FEnum k) (TCons (Nat.iter n tsucc tzero) TNil).

Fixpoint encoded_low_list_term (k : nat) (xs : list low_value) : term :=
  match xs with
  | [] => TFun (FNil k) TNil
  | u :: us =>
      TFun (FCons k)
        (TCons (TFun (FLowConst k (low_source u) (low_root u)
                                  (cert_encode (low_certificate u))) TNil)
          (TCons (encoded_low_list_term k us) TNil))
  end.

Definition enum_axiom (k n : nat) : sequent :=
  mkSeq [] [Eq (SList k) (enum_term k n) (encoded_low_list_term k (e_k k n))].

Definition EnumRule (k : nat) (prems : list sequent) (concl : sequent) : Prop :=
  exists n, prems = [] /\ concl = enum_axiom k n.

Lemma low_of_cert_ok : forall k c,
  INX c k = true -> low_okb k (low_of_cert c) = true.
Proof.
  intros k c H. unfold low_okb, low_of_cert. cbn.
  rewrite H, !Nat.eqb_refl, !andb_true_r. apply Nat.ltb_lt.
  destruct c.
  - rewrite INX_chain_closed, Nat.ltb_lt in H. exact H.
  - rewrite INX_identity_closed, Nat.ltb_lt in H by tauto. exact H.
  - rewrite INX_identity_closed, Nat.ltb_lt in H by tauto. exact H.
  - rewrite INX_identity_closed, Nat.ltb_lt in H by tauto. exact H.
  - rewrite INX_identity_closed, Nat.ltb_lt in H by tauto. exact H.
Qed.

(** * 7. Obstacles, timing, adaptation, and rule availability *)

Record obstacle : Type := mkObstacle {
  emitting_certificate : cert_id;
  obstructed_rule : nat;
  obstacle_tag : nat
}.

Inductive timing : Type := Delayed | Immediate | Ablated.

Definition emitb (c : cert_id) (q tag : nat) : bool :=
  match c with
  | CChain n => Nat.eqb q n && Nat.eqb tag 0
  | _ => false
  end.

Definition satb (q a : nat) (o : obstacle) : bool :=
  match emitting_certificate o with
  | CChain n =>
      if Nat.eqb (obstructed_rule o) n && Nat.eqb (obstacle_tag o) 0 && Nat.eqb q n
      then false else true
  | _ => true
  end.

Definition Adapt (B : list obstacle) (q a : nat) : bool :=
  forallb (satb q a) B.

Definition chain_obstacle (n : nat) : obstacle :=
  mkObstacle (CChain n) n 0.

Definition delayed_count (k : nat) : nat := Nat.pred k.

Definition barriers (tau : timing) (k : nat) : list obstacle :=
  match tau with
  | Delayed => map chain_obstacle (seq 0 (delayed_count k))
  | Immediate => map chain_obstacle (seq 0 k)
  | Ablated => []
  end.

Definition blockedb (tau : timing) (k n : nat) : bool :=
  match tau with
  | Delayed => Nat.ltb (S n) k
  | Immediate => Nat.ltb n k
  | Ablated => false
  end.

Definition canonical_adaptb (tau : timing) (k n : nat) : bool :=
  negb (blockedb tau k n).

Definition certificate_adaptb (tau : timing) (k : nat) (c : cert_id) : bool :=
  match c with CChain n => canonical_adaptb tau k n | _ => true end.

Definition traceb (tau : timing) (n k : nat) : bool :=
  INX (CChain n) k && canonical_adaptb tau k n.

Theorem delayed_trace : forall n k,
  traceb Delayed n k = true <-> k = S n.
Proof.
  intros n k. unfold traceb, canonical_adaptb, blockedb.
  rewrite INX_chain_closed.
  rewrite andb_true_iff, negb_true_iff, Nat.ltb_lt, Nat.ltb_ge.
  lia.
Qed.

Theorem immediate_trace : forall n k,
  traceb Immediate n k = false.
Proof.
  intros n k. unfold traceb, canonical_adaptb, blockedb.
  rewrite INX_chain_closed.
  destruct (Nat.ltb n k); reflexivity.
Qed.

Theorem ablated_trace : forall n k,
  traceb Ablated n k = true <-> S n <= k.
Proof.
  intros n k. unfold traceb, canonical_adaptb, blockedb.
  rewrite INX_chain_closed.
  rewrite andb_true_r, Nat.ltb_lt. lia.
Qed.

Definition AppRule (k : nat) (tau : timing)
    (c : cert_id) (sigma : instantiation) (a : nat)
    (prems : list sequent) (concl : sequent) : Prop :=
  INX c k = true /\
  legal_instantiationb k (root_scheme c) sigma = true /\
  certificate_adaptb tau k c = true /\
  instantiate_sequents sigma (scheme_premises (root_scheme c)) = Some prems /\
  instantiate_sequent sigma (scheme_conclusion (root_scheme c)) = Some concl.

Definition StageRule (k : nat) (tau : timing)
    (prems : list sequent) (concl : sequent) : Prop :=
  GQRule k prems concl \/ EnumRule k prems concl \/
  exists c sigma a, AppRule k tau c sigma a prems concl.

(** * 8. Ownership paths and one-step noncommutative transport *)

Inductive vertex : Type := VX | VY | VZ.
Inductive owner : Type := Owner0 | Owner1 | Owner2.

Definition vertex_eqb (v w : vertex) : bool :=
  match v, w with VX, VX | VY, VY | VZ, VZ => true | _, _ => false end.

Definition owner_eqb (a b : owner) : bool :=
  match a, b with
  | Owner0, Owner0 | Owner1, Owner1 | Owner2, Owner2 => true
  | _, _ => false
  end.

Record permutation : Type := mkPerm {
  image_x : vertex;
  image_y : vertex;
  image_z : vertex
}.

Definition perm_apply (g : permutation) (v : vertex) : vertex :=
  match v with VX => image_x g | VY => image_y g | VZ => image_z g end.

Definition perm_id : permutation := mkPerm VX VY VZ.
Definition swap_xy : permutation := mkPerm VY VX VZ.
Definition swap_yz : permutation := mkPerm VX VZ VY.

Definition perm_comp (g h : permutation) : permutation :=
  mkPerm (perm_apply g (perm_apply h VX))
         (perm_apply g (perm_apply h VY))
         (perm_apply g (perm_apply h VZ)).

Definition vertex_count (v : vertex) (xs : list vertex) : nat :=
  length (filter (vertex_eqb v) xs).

Definition PERM (g : permutation) : bool :=
  let xs := [image_x g; image_y g; image_z g] in
  Nat.eqb (vertex_count VX xs) 1 &&
  Nat.eqb (vertex_count VY xs) 1 &&
  Nat.eqb (vertex_count VZ xs) 1.

Definition inverse_at (g : permutation) (v : vertex) : vertex :=
  if vertex_eqb (perm_apply g VX) v then VX
  else if vertex_eqb (perm_apply g VY) v then VY
       else VZ.

Definition perm_inverse (g : permutation) : permutation :=
  mkPerm (inverse_at g VX) (inverse_at g VY) (inverse_at g VZ).

Inductive path_letter : Type := LA | LAMinus | LB | LBMinus.

Definition path_letter_eqb (a b : path_letter) : bool :=
  match a, b with
  | LA, LA | LAMinus, LAMinus | LB, LB | LBMinus, LBMinus => true
  | _, _ => false
  end.

Definition letter_certificate (a : path_letter) : cert_id :=
  match a with
  | LA => CHa | LAMinus => CHaMinus | LB => CHb | LBMinus => CHbMinus
  end.

Definition letter_permutation (a : path_letter) : permutation :=
  match a with LA | LAMinus => swap_xy | LB | LBMinus => swap_yz end.

Definition letter_count (a : path_letter) (p : list path_letter) : nat :=
  length (filter (path_letter_eqb a) p).

Definition SEED (p : list path_letter) : bool :=
  Nat.eqb (length p) 4 &&
  Nat.eqb (letter_count LA p) 1 &&
  Nat.eqb (letter_count LAMinus p) 1 &&
  Nat.eqb (letter_count LB p) 1 &&
  Nat.eqb (letter_count LBMinus p) 1.

Definition LIFT (k : nat) (p : list path_letter) : list low_value :=
  map (fun a => low_of_cert (letter_certificate a)) p.

Definition LIFT_term (k : nat) (p : list path_letter) : term :=
  encoded_low_list_term k (LIFT k p).

Definition low_to_letter (u : low_value) : option path_letter :=
  if low_value_eqb u (low_of_cert CHa) then Some LA
  else if low_value_eqb u (low_of_cert CHaMinus) then Some LAMinus
  else if low_value_eqb u (low_of_cert CHb) then Some LB
  else if low_value_eqb u (low_of_cert CHbMinus) then Some LBMinus
  else None.

Fixpoint decode_path (xs : list low_value) : option (list path_letter) :=
  match xs with
  | [] => Some []
  | u :: us =>
      match low_to_letter u, decode_path us with
      | Some a, Some p => Some (a :: p)
      | _, _ => None
      end
  end.

Definition PATHCHK (k : nat) (xs : list low_value) : bool :=
  Nat.ltb 0 k && forallb (low_okb k) xs &&
  match decode_path xs with Some p => SEED p | None => false end.

Lemma low_to_letter_lift : forall a,
  low_to_letter (low_of_cert (letter_certificate a)) = Some a.
Proof. destruct a; reflexivity. Qed.

Lemma decode_LIFT : forall k p, decode_path (LIFT k p) = Some p.
Proof.
  intros k p. induction p as [| a p IH].
  - reflexivity.
  - change
      (match low_to_letter (low_of_cert (letter_certificate a)),
             decode_path (LIFT k p) with
       | Some b, Some q => Some (b :: q)
       | _, _ => None
       end = Some (a :: p)).
    rewrite low_to_letter_lift, IH. reflexivity.
Qed.

Lemma lifted_letters_are_low : forall k p,
  Nat.ltb 0 k = true -> forallb (low_okb k) (LIFT k p) = true.
Proof.
  intros k p Hk. induction p as [| a p IH].
  - reflexivity.
  - change
      (low_okb k (low_of_cert (letter_certificate a)) &&
       forallb (low_okb k) (LIFT k p) = true).
    rewrite IH by exact Hk. rewrite andb_true_r.
    apply low_of_cert_ok. destruct a;
      rewrite INX_identity_closed by tauto; exact Hk.
Qed.

Theorem PATHCHK_LIFT_iff_SEED : forall k p,
  Nat.ltb 0 k = true ->
  PATHCHK k (LIFT k p) = true <-> SEED p = true.
Proof.
  intros k p Hk. unfold PATHCHK. rewrite Hk, lifted_letters_are_low by exact Hk.
  rewrite decode_LIFT. cbn. tauto.
Qed.

Fixpoint Hol (p : list path_letter) : permutation :=
  match p with
  | [] => perm_id
  | a :: q => perm_comp (Hol q) (letter_permutation a)
  end.

(* The displayed recursion equals the source's left-to-right update
   h := g(c_i) o h: unfolding gives g(last) o ... o g(first). *)

Definition pi_h : list path_letter := [LA; LB; LAMinus; LBMinus].
Definition pi_0 : list path_letter := [LA; LAMinus; LB; LBMinus].

Theorem seed_pi_h : SEED pi_h = true.
Proof. reflexivity. Qed.

Theorem seed_pi_0 : SEED pi_0 = true.
Proof. reflexivity. Qed.

Theorem hol_pi_h :
  perm_apply (Hol pi_h) VX = VY /\
  perm_apply (Hol pi_h) VY = VZ /\
  perm_apply (Hol pi_h) VZ = VX.
Proof. repeat split; reflexivity. Qed.

Theorem hol_pi_0 :
  perm_apply (Hol pi_0) VX = VX /\
  perm_apply (Hol pi_0) VY = VY /\
  perm_apply (Hol pi_0) VZ = VZ.
Proof. repeat split; reflexivity. Qed.

Record ownership : Type := mkOwnership {
  owner_x : owner;
  owner_y : owner;
  owner_z : owner
}.

Definition ownership_lookup (o : ownership) (v : vertex) : owner :=
  match v with VX => owner_x o | VY => owner_y o | VZ => owner_z o end.

Definition Omega0 : ownership := mkOwnership Owner0 Owner1 Owner2.

Definition ownership_action (g : permutation) (o : ownership) : ownership :=
  let gi := perm_inverse g in
  mkOwnership (ownership_lookup o (perm_apply gi VX))
              (ownership_lookup o (perm_apply gi VY))
              (ownership_lookup o (perm_apply gi VZ)).

Definition Omega_at (k : nat) (p : list path_letter) : ownership :=
  match k with
  | 0 | 1 => Omega0
  | S (S _) => ownership_action (Hol p) Omega0
  end.

Inductive path_state : Type :=
| PIdle
| PActive (stage : nat) (path : list low_value).

Definition P_at (k : nat) (p : list path_letter) : path_state :=
  match k with 0 => PIdle | S _ => PActive k (LIFT k p) end.

Definition XLIST (k : nat) : list cert_id :=
  match k with
  | 0 => []
  | S _ => [CHa; CHaMinus; CHb; CHbMinus] ++ map CChain (seq 0 k)
  end.

Record finite_state : Type := mkState {
  state_X : list cert_id;
  state_B : list obstacle;
  state_Omega : ownership;
  state_path : path_state
}.

Definition state_at (k : nat) (tau : timing) (p : list path_letter) : finite_state :=
  mkState (XLIST k) (barriers tau k) (Omega_at k p) (P_at k p).

Definition RUN (p : list path_letter) (N : nat) (tau : timing)
    : list finite_state :=
  map (fun k => state_at k tau p) (seq 0 (S N)).

Theorem omega2_pi_h_x : ownership_lookup (Omega_at 2 pi_h) VX = Owner2.
Proof. reflexivity. Qed.

Theorem omega2_pi_0_x : ownership_lookup (Omega_at 2 pi_0) VX = Owner0.
Proof. reflexivity. Qed.

(** * 9. Ownership-sensitive surface formulas and core erasure *)

Inductive sformula : Type :=
| SFBot
| SFEq (s : sort) (left right : term)
| SFRel (r : rsym) (args : terms)
| SFAnd (left right : sformula)
| SFOr (left right : sformula)
| SFImp (left right : sformula)
| SFAll (s : sort) (body : sformula)
| SFEx (s : sort) (body : sformula)
| OwnAll (v : vertex) (body : sformula).

Fixpoint sformula_eqb (A B : sformula) : bool :=
  match A, B with
  | SFBot, SFBot => true
  | SFEq s t u, SFEq r v w => sort_eqb s r && term_eqb t v && term_eqb u w
  | SFRel r ts, SFRel q us => rsym_eqb r q && terms_eqb ts us
  | SFAnd A1 A2, SFAnd B1 B2 | SFOr A1 A2, SFOr B1 B2
  | SFImp A1 A2, SFImp B1 B2 => sformula_eqb A1 B1 && sformula_eqb A2 B2
  | SFAll s C, SFAll r D | SFEx s C, SFEx r D => sort_eqb s r && sformula_eqb C D
  | OwnAll v C, OwnAll w D => vertex_eqb v w && sformula_eqb C D
  | _, _ => false
  end.

Definition vertex_index (v : vertex) : nat :=
  match v with VX => 0 | VY => 1 | VZ => 2 end.

Definition vertex_variable (v : vertex) : variable := (SD, vertex_index v).

Definition remove_var (x : variable) (xs : list variable) : list variable :=
  filter (fun y => negb (variable_eqb x y)) xs.

Fixpoint sfv (A : sformula) : list variable :=
  match A with
  | SFBot => []
  | SFEq _ t u => var_union (fv_term t) (fv_term u)
  | SFRel _ ts => fv_terms ts
  | SFAnd B C | SFOr B C | SFImp B C => var_union (sfv B) (sfv C)
  | SFAll s B | SFEx s B => down s (sfv B)
  | OwnAll v B => remove_var (vertex_variable v) (sfv B)
  end.

Fixpoint body_close_term (target depth : nat) (t : term) : term :=
  match t with
  | TVar SD i =>
      if Nat.ltb i depth then TVar SD i
      else if Nat.eqb i (target + depth) then TVar SD depth
           else TVar SD (S i)
  | TVar s i => TVar s i
  | TFun f ts => TFun f (body_close_terms target depth ts)
  end
with body_close_terms (target depth : nat) (ts : terms) : terms :=
  match ts with
  | TNil => TNil
  | TCons t us =>
      TCons (body_close_term target depth t) (body_close_terms target depth us)
  end.

Fixpoint body_close_formula (target depth : nat) (A : formula) : formula :=
  match A with
  | Bot => Bot
  | Eq s t u => Eq s (body_close_term target depth t) (body_close_term target depth u)
  | Rel r ts => Rel r (body_close_terms target depth ts)
  | And B C => And (body_close_formula target depth B) (body_close_formula target depth C)
  | Or B C => Or (body_close_formula target depth B) (body_close_formula target depth C)
  | Imp B C => Imp (body_close_formula target depth B) (body_close_formula target depth C)
  | All SD B => All SD (body_close_formula target (S depth) B)
  | Ex SD B => Ex SD (body_close_formula target (S depth) B)
  | All s B => All s (body_close_formula target depth B)
  | Ex s B => Ex s (body_close_formula target depth B)
  end.

Definition Close (v : vertex) (A : formula) : formula :=
  All SD (body_close_formula (vertex_index v) 0 A).

Fixpoint UNDER (A : sformula) : formula :=
  match A with
  | SFBot => Bot
  | SFEq s t u => Eq s t u
  | SFRel r ts => Rel r ts
  | SFAnd B C => And (UNDER B) (UNDER C)
  | SFOr B C => Or (UNDER B) (UNDER C)
  | SFImp B C => Imp (UNDER B) (UNDER C)
  | SFAll s B => All s (UNDER B)
  | SFEx s B => Ex s (UNDER B)
  | OwnAll v B => Close v (UNDER B)
  end.

Fixpoint TCHK_H (k : nat) (omega : ownership) (A : sformula) : bool :=
  match A with
  | SFBot => true
  | SFEq s t u => WT k t s && WT k u s
  | SFRel r ts => rsym_allowedb k r && terms_have_sorts k ts (rsig r)
  | SFAnd B C | SFOr B C | SFImp B C => TCHK_H k omega B && TCHK_H k omega C
  | SFAll s B | SFEx s B => stage_sortb k s && TCHK_H k omega B
  | OwnAll v B =>
      TCHK_H k omega B && var_mem (vertex_variable v) (sfv B) &&
      owner_eqb (ownership_lookup omega v) Owner0
  end.

Definition assignment_context := list (variable * term).

Definition assignment_has (x : variable) (Xi : assignment_context) : bool :=
  existsb (fun entry => variable_eqb x (fst entry)) Xi.

Definition CodeOK (k : nat) (A : sformula) (Xi : assignment_context) : bool :=
  forallb
    (fun x => if sort_eqb (fst x) (SLow k) then assignment_has x Xi else true)
    (sfv A).

Definition FCHK_H (k : nat) (omega : ownership)
    (Xi : assignment_context) (A : sformula) : bool :=
  TCHK_H k omega A && CodeOK k A Xi.

Definition Preform (k : nat) (omega : ownership) (A : sformula) : Prop :=
  TCHK_H k omega A = true.

Definition Form (k : nat) (omega : ownership)
    (Xi : assignment_context) (A : sformula) : Prop :=
  FCHK_H k omega Xi A = true.

Theorem FCHK_H_reflects_formation : forall k omega Xi A,
  FCHK_H k omega Xi A = true <-> Form k omega Xi A.
Proof. reflexivity. Qed.

Definition dx : term := TVar SD 0.
Definition dy : term := TVar SD 1.
Definition dz : term := TVar SD 2.
Definition A_circ : sformula := SFRel RD3 (TCons dx (TCons dy (TCons dz TNil))).
Definition Q_x : sformula := OwnAll VX A_circ.

Theorem ownership_formation_pi_0 : Form 2 (Omega_at 2 pi_0) [] Q_x.
Proof. reflexivity. Qed.

Theorem ownership_nonformation_pi_h : ~ Form 2 (Omega_at 2 pi_h) [] Q_x.
Proof. cbn. discriminate. Qed.

Theorem same_surface_tree : sformula_eqb Q_x Q_x = true.
Proof. reflexivity. Qed.

Theorem same_core_tree : formula_eqb (UNDER Q_x) (UNDER Q_x) = true.
Proof. reflexivity. Qed.

(** * 12.5. Forgetting order cannot factor the formation judgment *)

Definition letter_present (a : path_letter) (p : list path_letter) : bool :=
  existsb (path_letter_eqb a) p.

Definition path_set (p : list path_letter) : list cert_id :=
  map letter_certificate
    (filter (fun a => letter_present a p) [LA; LAMinus; LB; LBMinus]).

Record set_shadow : Type := mkSetShadow {
  shadow_X : list cert_id;
  shadow_B : list obstacle;
  shadow_path_set : list cert_id
}.

Definition SetSh (k : nat) (tau : timing) (p : list path_letter) : set_shadow :=
  mkSetShadow (XLIST k) (barriers tau k) (path_set p).

Theorem set_shadow_paths_equal : SetSh 2 Delayed pi_h = SetSh 2 Delayed pi_0.
Proof. reflexivity. Qed.

Theorem no_set_factorized_formation :
  ~ exists T : set_shadow -> sformula -> bool,
      forall p, SEED p = true ->
        T (SetSh 2 Delayed p) Q_x = FCHK_H 2 (Omega_at 2 p) [] Q_x.
Proof.
  intros [T HT].
  pose proof (HT pi_h seed_pi_h) as Hh.
  pose proof (HT pi_0 seed_pi_0) as H0.
  rewrite set_shadow_paths_equal in Hh.
  cbn in Hh, H0. congruence.
Qed.

(** * 10. Finite stage derivation objects and executable checking *)

Inductive rule_evidence : Type :=
| EvGQ (witness : gq_witness)
| EvEnum (number : nat)
| EvApp (certificate : cert_id) (sigma : instantiation) (adapter : nat).

Definition evidence_premises (k : nat) (ev : rule_evidence)
    : option (list sequent) :=
  match ev with
  | EvGQ w => Some (gq_premises w)
  | EvEnum _ => Some []
  | EvApp c sigma _ => instantiate_sequents sigma (scheme_premises (root_scheme c))
  end.

Definition evidence_conclusion (k : nat) (ev : rule_evidence)
    : option sequent :=
  match ev with
  | EvGQ w => Some (gq_conclusion w)
  | EvEnum n => Some (enum_axiom k n)
  | EvApp c sigma _ => instantiate_sequent sigma (scheme_conclusion (root_scheme c))
  end.

Definition evidence_validb (k : nat) (tau : timing) (ev : rule_evidence) : bool :=
  match ev with
  | EvGQ w => gq_validb k w
  | EvEnum _ => Nat.ltb 0 k
  | EvApp c sigma _ =>
      INX c k && legal_instantiationb k (root_scheme c) sigma &&
      certificate_adaptb tau k c
  end.

Inductive derivation_tree : Type :=
| DNode (evidence : rule_evidence) (label : sequent) (children : derivation_forest)
with derivation_forest : Type :=
| DNil
| DCons (head : derivation_tree) (tail : derivation_forest).

Definition derivation_root (d : derivation_tree) : sequent :=
  match d with DNode _ seq0 _ => seq0 end.

Fixpoint forest_roots (ds : derivation_forest) : list sequent :=
  match ds with
  | DNil => []
  | DCons d es => derivation_root d :: forest_roots es
  end.

Fixpoint DCHK (k : nat) (tau : timing) (d : derivation_tree) : bool :=
  match d with
  | DNode ev seq0 ds =>
      evidence_validb k tau ev &&
      match evidence_premises k ev, evidence_conclusion k ev with
      | Some ps, Some C =>
          list_eqb sequent_eqb (forest_roots ds) ps &&
          sequent_eqb seq0 C && DCHK_forest k tau ds
      | _, _ => false
      end
  end
with DCHK_forest (k : nat) (tau : timing) (ds : derivation_forest) : bool :=
  match ds with
  | DNil => true
  | DCons d es => DCHK k tau d && DCHK_forest k tau es
  end.

Definition CoreDerivation (k : nat) (tau : timing) (d : derivation_tree) : Prop :=
  DCHK k tau d = true.

Record annotated_formula : Type := mkAnnotatedFormula {
  surface_part : sformula;
  core_part : formula
}.

Definition annotated_context := list annotated_formula.
Record annotated_sequent : Type := mkAnnotatedSeq {
  annotated_antecedent : annotated_context;
  annotated_succedent : annotated_context
}.

Definition annotated_formula_eqb (a b : annotated_formula) : bool :=
  sformula_eqb (surface_part a) (surface_part b) &&
  formula_eqb (core_part a) (core_part b).

Definition annotated_context_eqb := list_eqb annotated_formula_eqb.
Definition annotated_sequent_eqb (S T : annotated_sequent) : bool :=
  annotated_context_eqb (annotated_antecedent S) (annotated_antecedent T) &&
  annotated_context_eqb (annotated_succedent S) (annotated_succedent T).

Definition erase_annotated_context (G : annotated_context) : context :=
  map core_part G.

Definition erase_annotated_sequent (S : annotated_sequent) : sequent :=
  mkSeq (erase_annotated_context (annotated_antecedent S))
        (erase_annotated_context (annotated_succedent S)).

Definition annotated_formula_validb (k : nat) (omega : ownership)
    (Xi : assignment_context) (a : annotated_formula) : bool :=
  FCHK_H k omega Xi (surface_part a) &&
  formula_eqb (core_part a) (UNDER (surface_part a)).

Definition annotated_context_validb (k : nat) (omega : ownership)
    (Xi : assignment_context) (G : annotated_context) : bool :=
  forallb (annotated_formula_validb k omega Xi) G.

Definition annotated_sequent_validb (k : nat) (omega : ownership)
    (Xi : assignment_context) (S : annotated_sequent) : bool :=
  annotated_context_validb k omega Xi (annotated_antecedent S) &&
  annotated_context_validb k omega Xi (annotated_succedent S).

Inductive annotated_tree : Type :=
| ANode (evidence : rule_evidence) (label : annotated_sequent)
        (children : annotated_forest)
with annotated_forest : Type :=
| ANil
| ACons (head : annotated_tree) (tail : annotated_forest).

Fixpoint CORETREE (d : annotated_tree) : derivation_tree :=
  match d with
  | ANode ev seq0 ds => DNode ev (erase_annotated_sequent seq0) (COREFOREST ds)
  end
with COREFOREST (ds : annotated_forest) : derivation_forest :=
  match ds with
  | ANil => DNil
  | ACons d es => DCons (CORETREE d) (COREFOREST es)
  end.

Fixpoint annotations_validb (k : nat) (omega : ownership)
    (Xi : assignment_context) (d : annotated_tree) : bool :=
  match d with
  | ANode _ seq0 ds =>
      annotated_sequent_validb k omega Xi seq0 &&
      annotations_forest_validb k omega Xi ds
  end
with annotations_forest_validb (k : nat) (omega : ownership)
    (Xi : assignment_context) (ds : annotated_forest) : bool :=
  match ds with
  | ANil => true
  | ACons d es =>
      annotations_validb k omega Xi d &&
      annotations_forest_validb k omega Xi es
  end.

Definition timing_eqb (a b : timing) : bool :=
  match a, b with
  | Delayed, Delayed | Immediate, Immediate | Ablated, Ablated => true
  | _, _ => false
  end.

Definition path_eqb := list_eqb path_letter_eqb.

Record staged_annotated_derivation : Type := mkStagedDerivation {
  literal_stage : nat;
  literal_timing : timing;
  literal_path : list path_letter;
  annotated_body : annotated_tree
}.

Definition DCHK_H (d : staged_annotated_derivation)
    (Xi : assignment_context) : bool :=
  let k := literal_stage d in
  let tau := literal_timing d in
  let p := literal_path d in
  SEED p &&
  annotations_validb k (Omega_at k p) Xi (annotated_body d) &&
  DCHK k tau (CORETREE (annotated_body d)).

Definition annotated_root (d : annotated_tree) : annotated_sequent :=
  match d with ANode _ seq0 _ => seq0 end.

Definition StageDerivable (Xi : assignment_context)
    (Gamma Delta : annotated_context) (k : nat)
    (p : list path_letter) (tau : timing) : Prop :=
  exists d : staged_annotated_derivation,
    literal_stage d = k /\ literal_timing d = tau /\ literal_path d = p /\
    DCHK_H d Xi = true /\
    annotated_root (annotated_body d) = mkAnnotatedSeq Gamma Delta.

Definition annotated_Qx : annotated_formula := mkAnnotatedFormula Q_x (UNDER Q_x).

Definition Qx_identity_tree : annotated_tree :=
  ANode (EvGQ (WId [] [] (UNDER Q_x)))
        (mkAnnotatedSeq [annotated_Qx] [annotated_Qx]) ANil.

Definition Qx_identity_derivation : staged_annotated_derivation :=
  mkStagedDerivation 2 Delayed pi_0 Qx_identity_tree.

Theorem checked_Qx_identity : DCHK_H Qx_identity_derivation [] = true.
Proof. reflexivity. Qed.

Theorem Qx_identity_is_derivable :
  StageDerivable [] [annotated_Qx] [annotated_Qx] 2 pi_0 Delayed.
Proof.
  exists Qx_identity_derivation. repeat split; reflexivity.
Qed.

(** * 11. Structural semantics and reliability infrastructure *)

Definition sort_eq_dec (s t : sort) : {s = t} + {s <> t}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Record semantic_frame (k : nat) : Type := mkSemanticFrame {
  sem_value : sort -> Type;
  sem_inhabited : forall s, stage_sortb k s = true -> sem_value s;
  sem_eval : forall s, term -> (forall r, nat -> sem_value r) -> option (sem_value s);
  sem_relation : rsym -> terms -> (forall r, nat -> sem_value r) -> Prop
}.

Definition sem_environment {k : nat} (M : semantic_frame k) : Type :=
  forall s, nat -> sem_value M s.

Definition cast_value {k : nat} {M : semantic_frame k}
    {s r : sort} (e : s = r) (v : sem_value M s) : sem_value M r :=
  match e with eq_refl => v end.

Definition sem_update {k : nat} (M : semantic_frame k)
    (eta : sem_environment M) (s : sort) (v : sem_value M s)
    : sem_environment M :=
  fun r i =>
    match sort_eq_dec s r with
    | left e =>
        match i with
        | 0 => cast_value e v
        | S j => eta r j
        end
    | right _ => eta r i
    end.

Definition sem_replace {k : nat} (M : semantic_frame k)
    (eta : sem_environment M) (s : sort) (index : nat)
    (v : sem_value M s) : sem_environment M :=
  fun r i =>
    match sort_eq_dec s r with
    | left e => if Nat.eqb i index then cast_value e v else eta r i
    | right _ => eta r i
    end.

Arguments sem_update {k} M eta s v.
Arguments sem_replace {k} M eta s index v.

Fixpoint satisfies {k : nat} (M : semantic_frame k)
    (eta : sem_environment M) (A : formula) : Prop :=
  match A with
  | Bot => False
  | Eq s t u =>
      exists v : sem_value M s,
        sem_eval M s t eta = Some v /\ sem_eval M s u eta = Some v
  | Rel r ts => sem_relation M r ts eta
  | And B C => @satisfies k M eta B /\ @satisfies k M eta C
  | Or B C => @satisfies k M eta B \/ @satisfies k M eta C
  | Imp B C => ~ @satisfies k M eta B \/ @satisfies k M eta C
  | All s B => forall v : sem_value M s,
      @satisfies k M (@sem_update k M eta s v) B
  | Ex s B => exists v : sem_value M s,
      @satisfies k M (@sem_update k M eta s v) B
  end.

Arguments satisfies {k} M eta A.

Definition sem_context {k : nat} (M : semantic_frame k)
    (eta : sem_environment M) (G : context) : Prop :=
  forall A, In A G -> satisfies M eta A.

Definition sem_succedent {k : nat} (M : semantic_frame k)
    (eta : sem_environment M) (D : context) : Prop :=
  exists A, In A D /\ satisfies M eta A.

Definition sequent_true {k : nat} (M : semantic_frame k)
    (eta : sem_environment M) (S : sequent) : Prop :=
  @sem_context k M eta (antecedent S) ->
  @sem_succedent k M eta (succedent S).

Definition sequent_valid {k : nat} (M : semantic_frame k) (S : sequent) : Prop :=
  forall eta, @sequent_true k M eta S.

Arguments sem_context {k} M eta G.
Arguments sem_succedent {k} M eta D.
Arguments sequent_true {k} M eta S.
Arguments sequent_valid {k} M S.

(* These are the standard substitution/freshness lemmas forced by the source's
   de Bruijn interpretation.  They are kept as named model-coherence fields so
   no rule soundness or final reliability theorem is assumed. *)
Record lawful_stage_model (k : nat) : Type := mkLawfulStageModel {
  model_frame : semantic_frame k;

  term_total : forall eta s t,
    WT k t s = true ->
    exists v : sem_value model_frame s,
      sem_eval model_frame s t eta = Some v;

  formula_substitution_zero : forall eta s A t v,
    WT k t s = true ->
    sem_eval model_frame s t eta = Some v ->
    (satisfies model_frame eta (sub_formula s A 0 t) <->
     satisfies model_frame (sem_update model_frame eta s v) A);

  equality_substitution : forall eta s A j t u,
    satisfies model_frame eta (Eq s t u) ->
    (satisfies model_frame eta (sub_formula s A j t) <->
     satisfies model_frame eta (sub_formula s A j u));

  fresh_replacement : forall eta s j v A,
    var_mem (s, j) (fv_formula A) = false ->
    (satisfies model_frame eta A <->
     satisfies model_frame (sem_replace model_frame eta s j v) A);

  eigen_substitution : forall eta s A j v,
    var_mem (s, j) (fv_formula (All s A)) = false ->
    (satisfies model_frame
       (sem_replace model_frame eta s j v)
       (sub_formula s A 0 (TVar s j)) <->
     satisfies model_frame (sem_update model_frame eta s v) A);

  q_axioms_true : forall eta A, In A AxQ -> satisfies model_frame eta A;

  enumeration_equations_true : forall eta n,
    satisfies model_frame eta
      (Eq (SList k) (enum_term k n) (encoded_low_list_term k (e_k k n)))
}.


Definition model_sequent_valid {k : nat} (M : lawful_stage_model k)
    (S : sequent) : Prop := sequent_valid (model_frame M) S.

Definition evidence_local_sound {k : nat} (M : lawful_stage_model k)
    (tau : timing) (ev : rule_evidence) : Prop :=
  forall ps C,
    evidence_premises k ev = Some ps ->
    evidence_conclusion k ev = Some C ->
    (forall S, In S ps -> model_sequent_valid M S) ->
    model_sequent_valid M C.

Definition all_checked_rules_sound {k : nat} (M : lawful_stage_model k)
    (tau : timing) : Prop :=
  forall ev, evidence_validb k tau ev = true -> evidence_local_sound M tau ev.

Lemma variable_eqb_spec : forall x y, variable_eqb x y = true <-> x = y.
Proof.
  intros [s i] [r j]. unfold variable_eqb. cbn.
  rewrite andb_true_iff, sort_eqb_spec, Nat.eqb_eq.
  split.
  - intros [-> ->]. reflexivity.
  - intro H. inversion H. subst. split; reflexivity.
Qed.

Lemma var_mem_spec : forall x xs, var_mem x xs = true <-> In x xs.
Proof.
  intros x xs. unfold var_mem. rewrite existsb_exists.
  split.
  - intros [y [Hy Hxy]]. apply variable_eqb_spec in Hxy. subst. exact Hy.
  - intro Hx. exists x. split; [exact Hx|apply variable_eqb_spec; reflexivity].
Qed.

Lemma var_add_spec : forall x y xs,
  In x (var_add y xs) <-> x = y \/ In x xs.
Proof.
  intros x y xs. unfold var_add. destruct (var_mem y xs) eqn:Hy.
  - apply var_mem_spec in Hy. split; intro H; [right; exact H|].
    destruct H as [->|H]; assumption.
  - cbn. split.
    + intros [H | H]; [left; symmetry|right]; assumption.
    + intros [H | H]; [left; symmetry|right]; assumption.
Qed.

Lemma var_union_spec : forall x xs ys,
  In x (var_union xs ys) <-> In x xs \/ In x ys.
Proof.
  intros x xs. induction xs as [| y xs IH]; intro ys.
  - change (In x ys <-> False \/ In x ys).
    split; intro H; [right; exact H|]. destruct H as [H|H]; [contradiction|exact H].
  - change (In x (var_add y (var_union xs ys)) <->
            (y = x \/ In x xs) \/ In x ys).
    rewrite var_add_spec, IH. split.
    + intros [Hxy | [Hxs | Hys]].
      * left. left. symmetry. exact Hxy.
      * left. right. exact Hxs.
      * right. exact Hys.
    + intros [[Hyx | Hxs] | Hys].
      * left. symmetry. exact Hyx.
      * right. left. exact Hxs.
      * right. right. exact Hys.
Qed.

Lemma fv_context_spec : forall x G,
  In x (fv_context G) <-> exists A, In A G /\ In x (fv_formula A).
Proof.
  intros x G. induction G as [| A G IH].
  - change (In x [] <-> exists B, In B [] /\ In x (fv_formula B)).
    split; [contradiction|intros [B [H _]]; contradiction].
  - change
      (In x (var_union (fv_formula A) (fv_context G)) <->
       exists B, (A = B \/ In B G) /\ In x (fv_formula B)).
    rewrite var_union_spec, IH. split.
    + intros [HA | [B [HB Hx]]].
      * exists A. split; [left; reflexivity|exact HA].
      * exists B. split; [right; exact HB|exact Hx].
    + intros [B [[-> | HB] Hx]].
      * left. exact Hx.
      * right. exists B. tauto.
Qed.

Lemma fresh_sequent_formula : forall s j S A,
  eigen_freshb s j S = true ->
  (In A (antecedent S) \/ In A (succedent S)) ->
  var_mem (s, j) (fv_formula A) = false.
Proof.
  intros s j [G D] A Hfresh HA. unfold eigen_freshb in Hfresh.
  apply negb_true_iff in Hfresh.
  apply Bool.not_true_iff_false. intro Hmem.
  assert (Hall : var_mem (s, j) (fv_sequent (mkSeq G D)) = true).
  { apply var_mem_spec. unfold fv_sequent. cbn. apply var_union_spec.
  destruct HA as [HA|HA].
  - left. apply fv_context_spec. exists A. split; [exact HA|].
    apply var_mem_spec. exact Hmem.
  - right. apply fv_context_spec. exists A. split; [exact HA|].
    apply var_mem_spec. exact Hmem. }
  rewrite Hfresh in Hall. discriminate.
Qed.

Lemma sem_context_app : forall k (F : semantic_frame k) eta G D,
  sem_context F eta (G ++ D) <-> sem_context F eta G /\ sem_context F eta D.
Proof.
  intros. unfold sem_context. split.
  - intro H. split; intros A HA; apply H; apply in_app_iff; tauto.
  - intros [HG HD] A HA. apply in_app_iff in HA. destruct HA; [apply HG|apply HD]; assumption.
Qed.

Lemma sem_context_cons : forall k (F : semantic_frame k) eta A G,
  sem_context F eta (A :: G) <-> satisfies F eta A /\ sem_context F eta G.
Proof.
  intros. unfold sem_context. split.
  - intro H. split.
    + apply H. left. reflexivity.
    + intros B HB. apply H. right. exact HB.
  - intros [HA HG] B HB. destruct HB as [HAB | HB].
    + subst B. exact HA.
    + apply HG. exact HB.
Qed.

Lemma sem_succedent_app : forall k (F : semantic_frame k) eta G D,
  sem_succedent F eta (G ++ D) <->
  sem_succedent F eta G \/ sem_succedent F eta D.
Proof.
  intros. unfold sem_succedent. split.
  - intros [A [HA Hsat]]. apply in_app_iff in HA. destruct HA as [HA|HA].
    + left. exists A. tauto.
    + right. exists A. tauto.
  - intros [[A [HA Hsat]] | [A [HA Hsat]]]; exists A; split.
    + apply in_app_iff. left. exact HA.
    + exact Hsat.
    + apply in_app_iff. right. exact HA.
    + exact Hsat.
Qed.

Lemma sem_succedent_cons : forall k (F : semantic_frame k) eta A D,
  sem_succedent F eta (A :: D) <->
  satisfies F eta A \/ sem_succedent F eta D.
Proof.
  intros. unfold sem_succedent. split.
  - intros [B [[HAB | HB] Hsat]].
    + left. subst B. exact Hsat.
    + right. exists B. tauto.
  - intros [HA | [B [HB Hsat]]].
    + exists A. split; [left; reflexivity|exact HA].
    + exists B. split; [right; exact HB|exact Hsat].
Qed.

Arguments sem_context_app {k} F eta G D.
Arguments sem_context_cons {k} F eta A G.
Arguments sem_succedent_app {k} F eta G D.
Arguments sem_succedent_cons {k} F eta A D.

Lemma sem_context_replace_fresh : forall k (M : lawful_stage_model k)
    eta s j v G,
  (forall A, In A G -> var_mem (s, j) (fv_formula A) = false) ->
  (sem_context (model_frame M) eta G <->
   sem_context (model_frame M)
     (sem_replace (model_frame M) eta s j v) G).
Proof.
  intros k M eta s j v G Hfresh. unfold sem_context.
  split; intros H A HA.
  - apply (proj1 (fresh_replacement M eta s j v A (Hfresh A HA))). apply H; exact HA.
  - apply (proj2 (fresh_replacement M eta s j v A (Hfresh A HA))). apply H; exact HA.
Qed.

Lemma sem_succedent_replace_fresh : forall k (M : lawful_stage_model k)
    eta s j v D,
  (forall A, In A D -> var_mem (s, j) (fv_formula A) = false) ->
  (sem_succedent (model_frame M) eta D <->
   sem_succedent (model_frame M)
     (sem_replace (model_frame M) eta s j v) D).
Proof.
  intros k M eta s j v D Hfresh. unfold sem_succedent.
  split.
  - intros [A [HA Hsat]]. exists A. split; [exact HA|].
    apply (proj1 (fresh_replacement M eta s j v A (Hfresh A HA))). exact Hsat.
  - intros [A [HA Hsat]]. exists A. split; [exact HA|].
    apply (proj2 (fresh_replacement M eta s j v A (Hfresh A HA))). exact Hsat.
Qed.

Lemma list_eqb_sound : forall (A : Type) (eqb : A -> A -> bool),
  (forall x y, eqb x y = true -> x = y) ->
  forall xs ys, list_eqb eqb xs ys = true -> xs = ys.
Proof.
  intros A eqb Heq xs. induction xs as [| x xs IH]; intros ys H.
  - destruct ys; cbn in H; [reflexivity|discriminate].
  - destruct ys as [| y ys]; cbn in H; [discriminate|].
    apply andb_true_iff in H as [Hxy Hrest].
    rewrite (Heq x y Hxy), (IH ys Hrest). reflexivity.
Qed.

Lemma list_eqb_refl : forall (A : Type) (eqb : A -> A -> bool),
  (forall x, eqb x x = true) -> forall xs, list_eqb eqb xs xs = true.
Proof.
  intros A eqb Heq xs. induction xs; cbn; [reflexivity|rewrite Heq, IHxs; reflexivity].
Qed.

Lemma sort_eqb_refl : forall s, sort_eqb s s = true.
Proof. intro s. apply sort_eqb_spec. reflexivity. Qed.

Lemma list_sort_eqb_sound : forall xs ys,
  list_sort_eqb xs ys = true -> xs = ys.
Proof. apply list_eqb_sound. intros x y H. apply sort_eqb_spec. exact H. Qed.

Lemma list_sort_eqb_refl : forall xs, list_sort_eqb xs xs = true.
Proof. apply list_eqb_refl. exact sort_eqb_refl. Qed.

Lemma fsym_eqb_sound : forall f g, fsym_eqb f g = true -> f = g.
Proof.
  intros f g. destruct f, g; cbn; try discriminate; intro H;
    repeat match goal with
    | h : _ && _ = true |- _ => apply andb_true_iff in h; destruct h
    end;
    repeat match goal with
    | h : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in h
    | h : sort_eqb _ _ = true |- _ => apply sort_eqb_spec in h
    | h : list_sort_eqb _ _ = true |- _ => apply list_sort_eqb_sound in h
    end;
    subst; reflexivity.
Qed.

Lemma fsym_eqb_refl : forall f, fsym_eqb f f = true.
Proof.
  intro f. destruct f; cbn; try reflexivity;
    rewrite ?list_sort_eqb_refl, ?sort_eqb_refl, !Nat.eqb_refl; reflexivity.
Qed.

Lemma rsym_eqb_sound : forall r q, rsym_eqb r q = true -> r = q.
Proof.
  intros r q. destruct r, q; cbn; try discriminate; intro H;
    repeat match goal with
    | h : _ && _ = true |- _ => apply andb_true_iff in h; destruct h
    end;
    repeat match goal with
    | h : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in h
    | h : list_sort_eqb _ _ = true |- _ => apply list_sort_eqb_sound in h
    end;
    subst; reflexivity.
Qed.

Lemma rsym_eqb_refl : forall r, rsym_eqb r r = true.
Proof.
  intro r. destruct r; cbn; try reflexivity;
    rewrite ?list_sort_eqb_refl, !Nat.eqb_refl; reflexivity.
Qed.

Scheme term_ind3 := Induction for term Sort Prop
with terms_ind3 := Induction for terms Sort Prop.
Combined Scheme term_terms_mutind3 from term_ind3, terms_ind3.

Lemma term_terms_eqb_sound :
  (forall t u, term_eqb t u = true -> t = u) /\
  (forall ts us, terms_eqb ts us = true -> ts = us).
Proof.
  apply term_terms_mutind3.
  - intros s i u H. destruct u; cbn in H; try discriminate.
    apply andb_true_iff in H as [Hs Hi].
    apply sort_eqb_spec in Hs. apply Nat.eqb_eq in Hi. subst. reflexivity.
  - intros f ts IH u H. destruct u; cbn in H; try discriminate.
    apply andb_true_iff in H as [Hf Hts].
    rewrite (fsym_eqb_sound _ _ Hf), (IH _ Hts). reflexivity.
  - intros us H. destruct us; cbn in H; [reflexivity|discriminate].
  - intros t IHt ts IHts us H. destruct us; cbn in H; try discriminate.
    apply andb_true_iff in H as [Ht Hts].
    rewrite (IHt _ Ht), (IHts _ Hts). reflexivity.
Qed.

Definition term_eqb_sound := proj1 term_terms_eqb_sound.
Definition terms_eqb_sound := proj2 term_terms_eqb_sound.

Lemma term_terms_eqb_refl :
  (forall t, term_eqb t t = true) /\
  (forall ts, terms_eqb ts ts = true).
Proof.
  apply term_terms_mutind3.
  - intros. cbn. rewrite sort_eqb_refl, Nat.eqb_refl. reflexivity.
  - intros. cbn. rewrite fsym_eqb_refl, H. reflexivity.
  - reflexivity.
  - intros. cbn. rewrite H, H0. reflexivity.
Qed.

Definition term_eqb_refl := proj1 term_terms_eqb_refl.
Definition terms_eqb_refl := proj2 term_terms_eqb_refl.

Lemma formula_eqb_sound : forall A B, formula_eqb A B = true -> A = B.
Proof.
  induction A; intros B0 H; destruct B0; cbn in H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [Hleft Hu].
    apply andb_true_iff in Hleft as [Hs Ht].
    apply sort_eqb_spec in Hs. apply term_eqb_sound in Ht.
    apply term_eqb_sound in Hu. subst. reflexivity.
  - apply andb_true_iff in H as [Hr Hts].
    apply rsym_eqb_sound in Hr. apply terms_eqb_sound in Hts. subst. reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    rewrite (IHA1 _ H1), (IHA2 _ H2). reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    rewrite (IHA1 _ H1), (IHA2 _ H2). reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    rewrite (IHA1 _ H1), (IHA2 _ H2). reflexivity.
  - apply andb_true_iff in H as [Hs HA].
    apply sort_eqb_spec in Hs. rewrite Hs, (IHA _ HA). reflexivity.
  - apply andb_true_iff in H as [Hs HA].
    apply sort_eqb_spec in Hs. rewrite Hs, (IHA _ HA). reflexivity.
Qed.

Lemma formula_eqb_refl : forall A, formula_eqb A A = true.
Proof.
  induction A; cbn; try reflexivity;
    rewrite ?sort_eqb_refl, ?term_eqb_refl, ?terms_eqb_refl,
      ?rsym_eqb_refl, ?IHA, ?IHA1, ?IHA2; reflexivity.
Qed.

Lemma sequent_eqb_sound : forall S T, sequent_eqb S T = true -> S = T.
Proof.
  intros [G D] [P L] H. cbn in H. apply andb_true_iff in H as [HG HD].
  apply list_eqb_sound in HG; [|exact formula_eqb_sound].
  apply list_eqb_sound in HD; [|exact formula_eqb_sound].
  cbn in HG, HD. subst. reflexivity.
Qed.

Lemma sequent_eqb_refl : forall S, sequent_eqb S S = true.
Proof.
  intros [G D]. unfold sequent_eqb, context_eqb. cbn.
  rewrite !list_eqb_refl by exact formula_eqb_refl. reflexivity.
Qed.

Lemma qaxiomb_sound : forall A, qaxiomb A = true -> In A AxQ.
Proof.
  intros A H. unfold qaxiomb in H. apply existsb_exists in H.
  destruct H as [B [HB HAB]]. apply formula_eqb_sound in HAB. subst. exact HB.
Qed.

Theorem checked_gq_evidence_sound : forall k (M : lawful_stage_model k)
    tau w,
  gq_validb k w = true -> evidence_local_sound M tau (EvGQ w).
Proof.
  intros k M tau w Hvalid.
  unfold gq_validb in Hvalid. apply andb_true_iff in Hvalid as [Hbasic Hparam].
  apply andb_true_iff in Hbasic as [_ Hside].
  unfold evidence_local_sound. intros ps C Hps HC Hprem.
  destruct w; cbn [evidence_premises evidence_conclusion gq_premises gq_conclusion]
    in Hps, HC; inversion Hps; inversion HC; subst ps C; clear Hps HC;
    cbn [gq_parameter_wtb gq_sideb] in Hparam, Hside.
  - (* Id *)
    intros eta HG. exists A. split.
    + left. reflexivity.
    + apply HG. apply in_app_iff. right. left. reflexivity.
  - (* BotL *)
    intros eta HG. exfalso. apply (HG Bot).
    + apply in_app_iff. right. left. reflexivity.
  - (* WkL *)
    intros eta HG. apply ((Hprem (mkSeq Gamma Delta) (or_introl eq_refl)) eta).
    intros A0 HA0. apply (HG A0). apply in_app_iff. left. exact HA0.
  - (* WkR *)
    intros eta HG.
    pose proof ((Hprem (mkSeq Gamma Delta) (or_introl eq_refl)) eta HG) as HD.
    apply (proj2 (sem_succedent_cons (model_frame M) eta A Delta)). right. exact HD.
  - (* CtrL *)
    intros eta HG. apply ((Hprem (mkSeq (Gamma ++ [A; A]) Delta)
      (or_introl eq_refl)) eta).
    intros B HB. apply in_app_iff in HB as [HB | [-> | [-> | []]]].
    + apply HG. apply in_app_iff. left. exact HB.
    + apply HG. apply in_app_iff. right. left. reflexivity.
    + apply HG. apply in_app_iff. right. left. reflexivity.
  - (* CtrR *)
    intros eta HG.
    pose proof ((Hprem (mkSeq Gamma (A :: A :: Delta)) (or_introl eq_refl)) eta HG) as HD.
    apply (proj1 (sem_succedent_cons (model_frame M) eta A (A :: Delta))) in HD.
    apply (proj2 (sem_succedent_cons (model_frame M) eta A Delta)).
    destruct HD as [HA | HD]; [left; exact HA|].
    apply (proj1 (sem_succedent_cons (model_frame M) eta A Delta)) in HD.
    destruct HD as [HA | HD]; [left; exact HA|right; exact HD].
  - (* ExchL *)
    intros eta HG. apply ((Hprem (mkSeq (Gamma0 ++ A :: B :: Gamma1) Delta)
      (or_introl eq_refl)) eta).
    intros C HC0. apply in_app_iff in HC0 as [HC0 | [-> | [-> | HC0]]].
    + apply HG. apply in_app_iff. left. exact HC0.
    + apply HG. apply in_app_iff. right. right. left. reflexivity.
    + apply HG. apply in_app_iff. right. left. reflexivity.
    + apply HG. apply in_app_iff. right. right. right. exact HC0.
  - (* ExchR *)
    intros eta HG.
    pose proof ((Hprem (mkSeq Gamma (Delta0 ++ A :: B :: Delta1))
      (or_introl eq_refl)) eta HG) as HD.
    unfold sem_succedent in HD |- *. destruct HD as [C [HC Hsat]].
    exists C. split; [|exact Hsat].
    apply in_app_iff in HC as [HC | [-> | [-> | HC]]].
    + apply in_app_iff. left. exact HC.
    + apply in_app_iff. right. right. left. reflexivity.
    + apply in_app_iff. right. left. reflexivity.
    + apply in_app_iff. right. right. right. exact HC.
  - (* Cut *)
    intros eta HG.
    assert (HGamma : sem_context (model_frame M) eta Gamma).
    { intros C HC0. apply (HG C). apply in_app_iff. left. exact HC0. }
    assert (HPi : sem_context (model_frame M) eta Pi).
    { intros C HC0. apply (HG C). apply in_app_iff. right. exact HC0. }
    pose proof ((Hprem (mkSeq Gamma (A :: Delta)) (or_introl eq_refl)) eta HGamma) as H1.
    apply (proj1 (sem_succedent_cons (model_frame M) eta A Delta)) in H1.
    destruct H1 as [HA | HD].
    + assert (HPA : sem_context (model_frame M) eta (Pi ++ [A])).
      { intros C HC0. apply in_app_iff in HC0 as [HC0 | [-> | []]]; [apply HPi|exact HA]; exact HC0. }
      pose proof ((Hprem (mkSeq (Pi ++ [A]) Lambda) (or_intror (or_introl eq_refl)))
        eta HPA) as HL.
      apply (proj2 (sem_succedent_app (model_frame M) eta Delta Lambda)). right. exact HL.
    + apply (proj2 (sem_succedent_app (model_frame M) eta Delta Lambda)). left. exact HD.
  - (* Refl *)
    intros eta _. apply (proj2 (sem_succedent_cons (model_frame M) eta
      (Eq s t t) Delta)). left. cbn [satisfies].
    destruct (term_total M eta s t Hparam) as [v Hv]. exists v. tauto.
  - (* EqL *)
    intros eta HG.
    assert (Heq : satisfies (model_frame M) eta (Eq s t u)).
    { apply HG. apply in_app_iff. right. left. reflexivity. }
    assert (HAu : satisfies (model_frame M) eta (sub_formula s A j u)).
    { apply HG. apply in_app_iff. right. right. left. reflexivity. }
    assert (HAt : satisfies (model_frame M) eta (sub_formula s A j t)).
    { apply (proj2 (@equality_substitution k M eta s A j t u Heq)). exact HAu. }
    apply ((Hprem (mkSeq (Gamma ++ [sub_formula s A j t]) Delta)
      (or_introl eq_refl)) eta).
    intros C HC0. cbn in HC0. apply in_app_iff in HC0 as [HC0 | HC0].
    + apply HG. apply in_app_iff. left. exact HC0.
    + destruct HC0 as [HeqC | Hnil]; [subst C; exact HAt|contradiction].
  - (* EqR *)
    intros eta HG.
    assert (Heq : satisfies (model_frame M) eta (Eq s t u)).
    { apply HG. apply in_app_iff. right. left. reflexivity. }
    assert (HGamma : sem_context (model_frame M) eta Gamma).
    { intros C HC0. apply HG. apply in_app_iff. left. exact HC0. }
    pose proof ((Hprem (mkSeq Gamma (sub_formula s A j t :: Delta))
      (or_introl eq_refl)) eta HGamma) as HP.
    apply (proj1 (sem_succedent_cons (model_frame M) eta
      (sub_formula s A j t) Delta)) in HP.
    apply (proj2 (sem_succedent_cons (model_frame M) eta
      (sub_formula s A j u) Delta)).
    destruct HP as [HAt | HD].
    + left. apply (proj1 (@equality_substitution k M eta s A j t u Heq)). exact HAt.
    + right. exact HD.
  - (* AndL *)
    intros eta HG. apply ((Hprem (mkSeq (Gamma ++ [A; B]) Delta)
      (or_introl eq_refl)) eta).
    intros C HC0.
    assert (HAnd : satisfies (model_frame M) eta (And A B)).
    { apply HG. cbn. apply in_app_iff. right. left. reflexivity. }
    cbn in HC0. apply in_app_iff in HC0 as [HC0 | HC0].
    + apply HG. apply in_app_iff. left. exact HC0.
    + destruct HC0 as [HAC | [HBC | Hnil]].
      * subst C. exact (proj1 HAnd).
      * subst C. exact (proj2 HAnd).
      * contradiction.
  - (* AndR *)
    intros eta HG.
    pose proof ((Hprem (mkSeq Gamma (A :: Delta)) (or_introl eq_refl)) eta HG) as H1.
    pose proof ((Hprem (mkSeq Gamma (B :: Delta)) (or_intror (or_introl eq_refl))) eta HG) as H2.
    apply sem_succedent_cons in H1. apply sem_succedent_cons in H2.
    apply sem_succedent_cons. destruct H1 as [HA|HD]; [|right; exact HD].
    destruct H2 as [HB|HD]; [left; split; assumption|right; exact HD].
  - (* OrL *)
    intros eta HG.
    assert (HOr : satisfies (model_frame M) eta (Or A B)).
    { apply HG. cbn. apply in_app_iff. right. left. reflexivity. }
    destruct HOr as [HA|HB].
    + apply ((Hprem (mkSeq (Gamma ++ [A]) Delta) (or_introl eq_refl)) eta).
      intros C HC0. cbn in HC0. apply in_app_iff in HC0 as [HC0|HC0].
      * apply HG. apply in_app_iff. left. exact HC0.
      * destruct HC0 as [HeqC|Hnil]; [subst C; exact HA|contradiction].
    + apply ((Hprem (mkSeq (Gamma ++ [B]) Delta) (or_intror (or_introl eq_refl))) eta).
      intros C HC0. cbn in HC0. apply in_app_iff in HC0 as [HC0|HC0].
      * apply HG. apply in_app_iff. left. exact HC0.
      * destruct HC0 as [HeqC|Hnil]; [subst C; exact HB|contradiction].
  - (* OrR *)
    intros eta HG.
    pose proof ((Hprem (mkSeq Gamma (A :: B :: Delta)) (or_introl eq_refl)) eta HG) as HP.
    apply sem_succedent_cons in HP. apply sem_succedent_cons.
    destruct HP as [HA | HP]; [left; left; exact HA|].
    apply sem_succedent_cons in HP. destruct HP as [HB|HD].
    + left. right. exact HB.
    + right. exact HD.
  - (* ImpL *)
    intros eta HG.
    assert (HGamma : sem_context (model_frame M) eta Gamma).
    { intros C HC0. apply HG. apply in_app_iff. left. exact HC0. }
    pose proof ((Hprem (mkSeq Gamma (A :: Delta)) (or_introl eq_refl)) eta HGamma) as H1.
    apply sem_succedent_cons in H1.
    destruct H1 as [HA | HD].
    + assert (HImp : satisfies (model_frame M) eta (Imp A B)).
      { apply HG. cbn. apply in_app_iff. right. apply in_app_iff. right.
        left. reflexivity. }
      destruct HImp as [HnotA | HB].
      * exfalso. exact (HnotA HA).
      * assert (HPiB : sem_context (model_frame M) eta (Pi ++ [B])).
        { intros C HC0. apply in_app_iff in HC0 as [HC0|[->|[]]].
          - apply HG. apply in_app_iff. right. apply in_app_iff. left. exact HC0.
          - exact HB. }
        pose proof ((Hprem (mkSeq (Pi ++ [B]) Lambda)
          (or_intror (or_introl eq_refl))) eta HPiB) as HL.
        apply sem_succedent_app. right. exact HL.
    + apply sem_succedent_app. left. exact HD.
  - (* ImpR *)
    intros eta HG. apply sem_succedent_cons.
    destruct (classic (satisfies (model_frame M) eta A)) as [HA|HnotA].
    + assert (HGA : sem_context (model_frame M) eta (Gamma ++ [A])).
      { intros C HC0. apply in_app_iff in HC0 as [HC0|[->|[]]]; [apply HG|exact HA]; exact HC0. }
      pose proof ((Hprem (mkSeq (Gamma ++ [A]) (B :: Delta))
        (or_introl eq_refl)) eta HGA) as HP.
      apply sem_succedent_cons in HP. destruct HP as [HB|HD].
      * left. right. exact HB.
      * right. exact HD.
    + left. left. exact HnotA.
  - (* AllL *)
    intros eta HG.
    destruct (term_total M eta s t Hparam) as [v Hv].
    assert (Hall : satisfies (model_frame M) eta (All s A)).
    { apply HG. apply in_app_iff. right. left. reflexivity. }
    assert (Hinst : satisfies (model_frame M) eta (sub_formula s A 0 t)).
    { apply (proj2 (@formula_substitution_zero k M eta s A t v Hparam Hv)). apply Hall. }
    apply ((Hprem (mkSeq (Gamma ++ [sub_formula s A 0 t]) Delta)
      (or_introl eq_refl)) eta).
    intros C HC0. cbn in HC0. apply in_app_iff in HC0 as [HC0|HC0].
    + apply HG. apply in_app_iff. left. exact HC0.
    + destruct HC0 as [HeqC|Hnil]; [subst C; exact Hinst|contradiction].
  - (* AllR *)
    intros eta HG. apply sem_succedent_cons.
    destruct (classic (sem_succedent (model_frame M) eta Delta)) as [HD|HnotD].
    + right. exact HD.
    + left. intro v.
      set (eta' := sem_replace (model_frame M) eta s eigen v).
      assert (HGfresh : forall C, In C Gamma ->
        var_mem (s, eigen) (fv_formula C) = false).
      { intros C HC0. apply (fresh_sequent_formula s eigen
          (mkSeq Gamma (All s A :: Delta)) C Hside). left. exact HC0. }
      assert (HDfresh : forall C, In C Delta ->
        var_mem (s, eigen) (fv_formula C) = false).
      { intros C HC0. apply (fresh_sequent_formula s eigen
          (mkSeq Gamma (All s A :: Delta)) C Hside). right. right. exact HC0. }
      assert (HAfresh : var_mem (s, eigen) (fv_formula (All s A)) = false).
      { apply (fresh_sequent_formula s eigen
          (mkSeq Gamma (All s A :: Delta)) (All s A) Hside). right. left. reflexivity. }
      assert (HG' : sem_context (model_frame M) eta' Gamma).
      { apply (proj1 (sem_context_replace_fresh M eta s eigen v Gamma HGfresh)). exact HG. }
      pose proof ((Hprem (mkSeq Gamma
        (sub_formula s A 0 (TVar s eigen) :: Delta)) (or_introl eq_refl)) eta' HG') as HP.
      apply sem_succedent_cons in HP. destruct HP as [HAinst|HD'].
      * apply (proj1 (@eigen_substitution k M eta s A eigen v HAfresh)). exact HAinst.
      * exfalso. apply HnotD.
        apply (proj2 (sem_succedent_replace_fresh M eta s eigen v Delta HDfresh)). exact HD'.
  - (* ExL *)
    intros eta HG.
    assert (HEx : satisfies (model_frame M) eta (Ex s A)).
    { apply HG. cbn. apply in_app_iff. right. left. reflexivity. }
    destruct HEx as [v HA].
    set (eta' := sem_replace (model_frame M) eta s eigen v).
    assert (HGfresh : forall C, In C Gamma ->
      var_mem (s, eigen) (fv_formula C) = false).
    { intros C HC0. apply (fresh_sequent_formula s eigen
        (mkSeq (Gamma ++ [Ex s A]) Delta) C Hside). left.
      apply in_app_iff. left. exact HC0. }
    assert (HDfresh : forall C, In C Delta ->
      var_mem (s, eigen) (fv_formula C) = false).
    { intros C HC0. apply (fresh_sequent_formula s eigen
        (mkSeq (Gamma ++ [Ex s A]) Delta) C Hside). right. exact HC0. }
    assert (HAfresh : var_mem (s, eigen) (fv_formula (All s A)) = false).
    { (* FV(All A) = FV(Ex A) by definition. *)
      change (var_mem (s, eigen) (down s (fv_formula A)) = false).
      apply (fresh_sequent_formula s eigen
        (mkSeq (Gamma ++ [Ex s A]) Delta) (Ex s A) Hside).
      left. apply in_app_iff. right. left. reflexivity. }
    assert (HG' : sem_context (model_frame M) eta' Gamma).
    { apply (proj1 (sem_context_replace_fresh M eta s eigen v Gamma HGfresh)).
      intros C HC0. apply HG. apply in_app_iff. left. exact HC0. }
    assert (HAinst : satisfies (model_frame M) eta'
      (sub_formula s A 0 (TVar s eigen))).
    { apply (proj2 (@eigen_substitution k M eta s A eigen v HAfresh)). exact HA. }
    pose proof ((Hprem (mkSeq (Gamma ++ [sub_formula s A 0 (TVar s eigen)]) Delta)
      (or_introl eq_refl)) eta') as HP.
    assert (HD' : sem_succedent (model_frame M) eta' Delta).
    { apply HP. intros C HC0. cbn in HC0. apply in_app_iff in HC0 as [HC0|HC0].
      - apply HG'. exact HC0.
      - destruct HC0 as [HeqC|Hnil]; [subst C; exact HAinst|contradiction]. }
    apply (proj2 (sem_succedent_replace_fresh M eta s eigen v Delta HDfresh)). exact HD'.
  - (* ExR *)
    intros eta HG.
    pose proof ((Hprem (mkSeq Gamma (sub_formula s A 0 t :: Delta))
      (or_introl eq_refl)) eta HG) as HP.
    apply sem_succedent_cons in HP. apply sem_succedent_cons.
    destruct HP as [Hinst|HD]; [left|right; exact HD].
    destruct (term_total M eta s t Hparam) as [v Hv]. exists v.
    apply (proj1 (@formula_substitution_zero k M eta s A t v Hparam Hv)). exact Hinst.
  - (* QAx *)
    intros eta _. apply sem_succedent_cons. left.
    apply q_axioms_true. apply qaxiomb_sound. exact Hside.
Qed.

Theorem checked_enum_evidence_sound : forall k (M : lawful_stage_model k)
    tau n,
  evidence_local_sound M tau (EvEnum n).
Proof.
  intros k M tau n ps C Hps HC _. cbn in Hps, HC.
  inversion Hps; inversion HC; subst. intros eta _.
  exists (Eq (SList k) (enum_term k n) (encoded_low_list_term k (e_k k n))).
  split; [left; reflexivity|apply enumeration_equations_true].
Qed.

Definition P_formula (n : nat) : formula := Rel (RP n) TNil.

Lemma instantiate_sch_P : forall sigma n,
  instantiate_formula sigma (sch_P n) = Some (P_formula n).
Proof. reflexivity. Qed.

Lemma instantiate_P_context : forall sigma ns,
  instantiate_context sigma (map (fun i => SCFormula (sch_P i)) ns) =
  Some (map P_formula ns).
Proof.
  intros sigma ns. induction ns as [| n ns IH].
  - reflexivity.
  - change
      (match instantiate_formula sigma (sch_P n),
             instantiate_context sigma (map (fun i => SCFormula (sch_P i)) ns) with
       | Some A, Some G => Some (A :: G)
       | _, _ => None
       end = Some (P_formula n :: map P_formula ns)).
    rewrite instantiate_sch_P, IH. reflexivity.
Qed.

Lemma instantiate_qn_conclusion : forall sigma n G D,
  lookup_context_inst 0 (inst_contexts sigma) = Some G ->
  lookup_context_inst 1 (inst_contexts sigma) = Some D ->
  instantiate_sequent sigma (scheme_conclusion (qn n)) =
  Some (mkSeq (G ++ map P_formula (seq 0 n)) D).
Proof.
  intros sigma n G D HG HD.
  unfold qn, qn_left, instantiate_sequent. cbn.
  rewrite HG, HD, instantiate_P_context. cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma instantiate_single_context : forall sigma n,
  instantiate_context sigma [SCContext n] =
  lookup_context_inst n (inst_contexts sigma).
Proof.
  intros sigma n.
  change
    (match lookup_context_inst n (inst_contexts sigma) with
     | Some D => Some (D ++ [])
     | None => None
     end = lookup_context_inst n (inst_contexts sigma)).
  destruct (lookup_context_inst n (inst_contexts sigma));
    simpl; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma instantiate_sch_H : forall sigma,
  instantiate_sequent sigma sch_H =
  match lookup_context_inst 0 (inst_contexts sigma) with
  | Some G =>
      match lookup_context_inst 1 (inst_contexts sigma) with
      | Some D => Some (mkSeq G D)
      | None => None
      end
  | None => None
  end.
Proof.
  intro sigma. unfold sch_H, instantiate_sequent.
  cbn [sch_antecedent sch_succedent].
  rewrite !instantiate_single_context.
  destruct (lookup_context_inst 0 (inst_contexts sigma));
    destruct (lookup_context_inst 1 (inst_contexts sigma)); reflexivity.
Qed.

Theorem checked_app_evidence_sound : forall k (M : lawful_stage_model k)
    tau c sigma a,
  evidence_local_sound M tau (EvApp c sigma a).
Proof.
  intros k M tau c sigma a ps C Hps HC Hprem.
  destruct c.
  - (* q_n: the conclusion only adds P_0,...,P_{n-1} on the left. *)
    destruct (lookup_context_inst 0 (inst_contexts sigma)) as [G|] eqn:HG.
    + destruct (lookup_context_inst 1 (inst_contexts sigma)) as [D|] eqn:HD.
      * assert (Hsch : instantiate_sequent sigma sch_H = Some (mkSeq G D)).
        { rewrite instantiate_sch_H, HG, HD. reflexivity. }
        assert (Hqn := @instantiate_qn_conclusion sigma index G D HG HD).
        cbn [evidence_conclusion root_scheme] in HC. rewrite Hqn in HC.
        inversion HC; subst C.
        change
          (match instantiate_sequent sigma sch_H with
           | Some T => Some [T]
           | None => None
           end = Some ps) in Hps.
        rewrite Hsch in Hps. inversion Hps; subst ps.
        intros eta HGall.
        apply ((Hprem (mkSeq G D) (or_introl eq_refl)) eta).
        intros A HA. apply HGall. cbn. apply in_app_iff. left. exact HA.
      * assert (Hsch : instantiate_sequent sigma sch_H = None).
        { rewrite instantiate_sch_H, HG, HD. reflexivity. }
        change
          (match instantiate_sequent sigma sch_H with
           | Some T => Some [T]
           | None => None
           end = Some ps) in Hps.
        rewrite Hsch in Hps. discriminate.
    + assert (Hsch : instantiate_sequent sigma sch_H = None).
      { rewrite instantiate_sch_H, HG. reflexivity. }
      change
        (match instantiate_sequent sigma sch_H with
         | Some T => Some [T]
         | None => None
         end = Some ps) in Hps.
      rewrite Hsch in Hps. discriminate.
  - (* h_a *)
    change (match instantiate_sequent sigma sch_H with
      | Some T => Some [T] | None => None end = Some ps) in Hps.
    change (instantiate_sequent sigma sch_H = Some C) in HC.
    destruct (instantiate_sequent sigma sch_H) as [S|]; try discriminate.
    inversion Hps; inversion HC; subst. apply Hprem. left. reflexivity.
  - (* h_a^- *)
    change (match instantiate_sequent sigma sch_H with
      | Some T => Some [T] | None => None end = Some ps) in Hps.
    change (instantiate_sequent sigma sch_H = Some C) in HC.
    destruct (instantiate_sequent sigma sch_H) as [S|]; try discriminate.
    inversion Hps; inversion HC; subst. apply Hprem. left. reflexivity.
  - (* h_b *)
    change (match instantiate_sequent sigma sch_H with
      | Some T => Some [T] | None => None end = Some ps) in Hps.
    change (instantiate_sequent sigma sch_H = Some C) in HC.
    destruct (instantiate_sequent sigma sch_H) as [S|]; try discriminate.
    inversion Hps; inversion HC; subst. apply Hprem. left. reflexivity.
  - (* h_b^- *)
    change (match instantiate_sequent sigma sch_H with
      | Some T => Some [T] | None => None end = Some ps) in Hps.
    change (instantiate_sequent sigma sch_H = Some C) in HC.
    destruct (instantiate_sequent sigma sch_H) as [S|]; try discriminate.
    inversion Hps; inversion HC; subst. apply Hprem. left. reflexivity.
Qed.

Theorem every_checked_rule_is_sound : forall k (M : lawful_stage_model k) tau,
  all_checked_rules_sound M tau.
Proof.
  intros k M tau ev Hev. destruct ev.
  - apply checked_gq_evidence_sound. exact Hev.
  - apply checked_enum_evidence_sound.
  - apply checked_app_evidence_sound.
Qed.

Scheme derivation_tree_ind2 := Induction for derivation_tree Sort Prop
with derivation_forest_ind2 := Induction for derivation_forest Sort Prop.

Combined Scheme derivation_tree_forest_mutind
  from derivation_tree_ind2, derivation_forest_ind2.

Theorem checked_core_derivation_sound : forall k tau
    (M : lawful_stage_model k),
  all_checked_rules_sound M tau ->
  forall d, DCHK k tau d = true -> model_sequent_valid M (derivation_root d).
Proof.
  intros k tau M Hrules.
  apply (derivation_tree_ind2
    (fun d => DCHK k tau d = true -> model_sequent_valid M (derivation_root d))
    (fun ds => DCHK_forest k tau ds = true ->
      forall S, In S (forest_roots ds) -> model_sequent_valid M S)).
  - intros ev C ds IHforest Hd.
    cbn [DCHK] in Hd.
    apply andb_true_iff in Hd as [Hev Hrest].
    destruct (evidence_premises k ev) as [ps|] eqn:Hps; try discriminate.
    destruct (evidence_conclusion k ev) as [concl|] eqn:Hc; try discriminate.
    apply andb_true_iff in Hrest as [Hpair Hds].
    apply andb_true_iff in Hpair as [Hroots HC].
    apply sequent_eqb_sound in HC. subst C. cbn.
    apply (Hrules ev Hev ps concl Hps Hc).
    intros S HS. apply IHforest; [exact Hds|].
    apply list_eqb_sound in Hroots; [|exact sequent_eqb_sound].
    rewrite Hroots. exact HS.
  - intros _ S H. inversion H.
  - intros d IHd ds IHds Hforest S HS.
    cbn [DCHK_forest] in Hforest. apply andb_true_iff in Hforest as [Hd Hds].
    cbn [forest_roots] in HS. destruct HS as [HSroot | HS].
    + subst S. apply IHd. exact Hd.
    + apply IHds; assumption.
Qed.

Theorem core_reliability : forall k tau d,
  DCHK k tau d = true ->
  forall M : lawful_stage_model k,
    model_sequent_valid M (derivation_root d).
Proof.
  intros k tau d Hd M. apply (@checked_core_derivation_sound k tau M).
  - apply every_checked_rule_is_sound.
  - exact Hd.
Qed.

Theorem canonical_certificate_reliability : forall k (tau : timing) c sigma a ps C,
  registered_PCOK c = true ->
  evidence_premises k (EvApp c sigma a) = Some ps ->
  evidence_conclusion k (EvApp c sigma a) = Some C ->
  forall M : lawful_stage_model k,
    (forall S, In S ps -> model_sequent_valid M S) ->
    model_sequent_valid M C.
Proof.
  intros k tau c sigma a ps C _ Hps HC M Hprem.
  exact (@checked_app_evidence_sound k M tau c sigma a ps C Hps HC Hprem).
Qed.

Theorem annotated_stage_reliability : forall Xi Gamma Delta k p tau,
  StageDerivable Xi Gamma Delta k p tau ->
  forall M : lawful_stage_model k,
    model_sequent_valid M (erase_annotated_sequent (mkAnnotatedSeq Gamma Delta)).
Proof.
  intros Xi Gamma Delta k p tau [d [Hk [Htau [Hp [Hd Hroot]]]]] M.
  destruct d as [dk dt dp body]. cbn in Hk, Htau, Hp. subst dk dt dp.
  unfold DCHK_H in Hd. cbn in Hd.
  apply andb_true_iff in Hd as [Hpair Hcore].
  apply core_reliability with (M := M) in Hcore.
  destruct body as [ev seq0 children].
  change (model_sequent_valid M (erase_annotated_sequent seq0)) in Hcore.
  change (seq0 = mkAnnotatedSeq Gamma Delta) in Hroot.
  rewrite Hroot in Hcore. exact Hcore.
Qed.

(** * 12.1--12.2. Total checkers and the delayed least fixed point *)

Definition obstacle_eqb (o p : obstacle) : bool :=
  cert_id_eqb (emitting_certificate o) (emitting_certificate p) &&
  Nat.eqb (obstructed_rule o) (obstructed_rule p) &&
  Nat.eqb (obstacle_tag o) (obstacle_tag p).

Definition OBIN (tau : timing) (k : nat) (o : obstacle) : bool :=
  existsb (obstacle_eqb o) (barriers tau k).

Record mechanical_snapshot : Type := mkMechanicalSnapshot {
  mech_inx : bool;
  mech_obin : bool;
  mech_pcok : bool;
  mech_adapt : bool;
  mech_seed : bool;
  mech_pathchk : bool;
  mech_perm : bool;
  mech_formation : bool;
  mech_derivation : bool
}.

Definition run_mechanical_checks c tau k o q a p xs omega Xi A d :=
  mkMechanicalSnapshot
    (INX c k) (OBIN tau k o) (registered_PCOK c)
    (Adapt (barriers tau k) q a) (SEED p) (PATHCHK k xs)
    (PERM (Hol p)) (FCHK_H k omega Xi A) (DCHK_H d Xi).

Theorem mechanical_checks_total : forall c tau k o q a p xs omega Xi A d,
  exists result,
    result = run_mechanical_checks c tau k o q a p xs omega Xi A d.
Proof. intros. eexists. reflexivity. Qed.

Definition cert_set := cert_id -> Prop.
Definition obstacle_set := obstacle -> Prop.

Definition Kset (X : cert_set) : cert_set :=
  fun c => registered_PCOK c = true /\
           forall d, In d (cert_dependencies c) -> X d.

Definition Emit (c : cert_id) (o : obstacle) : Prop :=
  exists n, c = CChain n /\ o = chain_obstacle n.

Definition Fset (X : cert_set) : obstacle_set :=
  fun o => exists c, X c /\ Emit c o.

Definition pred_included {A : Type} (X Y : A -> Prop) : Prop :=
  forall x, X x -> Y x.

Lemma Kset_monotone : forall X Y,
  pred_included X Y -> pred_included (Kset X) (Kset Y).
Proof.
  intros X Y HXY c [Hcheck Hdeps]. split; [exact Hcheck|].
  intros d Hd. apply HXY, Hdeps, Hd.
Qed.

Lemma Fset_monotone : forall X Y,
  pred_included X Y -> pred_included (Fset X) (Fset Y).
Proof.
  intros X Y HXY o [c [HX HE]]. exists c. split; [apply HXY, HX|exact HE].
Qed.

Definition X_stage (k : nat) : cert_set := fun c => INX c k = true.

Fixpoint B_delayed_stage (k : nat) : obstacle_set :=
  match k with
  | 0 => fun _ => False
  | S j => fun o => B_delayed_stage j o \/ Fset (X_stage j) o
  end.

Theorem X_stage_step : forall k c,
  X_stage (S k) c <-> X_stage k c \/ Kset (X_stage k) c.
Proof.
  intros k c. unfold X_stage, Kset.
  rewrite INX_step_equation, orb_true_iff, andb_true_iff.
  unfold dep_subsetb. rewrite forallb_forall. tauto.
Qed.

Theorem B_delayed_stage_step : forall k o,
  B_delayed_stage (S k) o <->
  B_delayed_stage k o \/ Fset (X_stage k) o.
Proof. reflexivity. Qed.

Lemma X_stage_mono : forall k l,
  k <= l -> pred_included (X_stage k) (X_stage l).
Proof.
  intros k l Hkl. induction Hkl.
  - intros c Hc. exact Hc.
  - intros c Hc. apply X_stage_step. left. apply IHHkl. exact Hc.
Qed.

Lemma B_delayed_stage_mono : forall k l,
  k <= l -> pred_included (B_delayed_stage k) (B_delayed_stage l).
Proof.
  intros k l Hkl. induction Hkl.
  - intros o Ho. exact Ho.
  - intros o Ho. apply B_delayed_stage_step. left. apply IHHkl. exact Ho.
Qed.

Definition increasing {A : Type} (C : nat -> A -> Prop) : Prop :=
  forall k, pred_included (C k) (C (S k)).

Lemma increasing_le : forall (A : Type) (C : nat -> A -> Prop),
  increasing C -> forall k l, k <= l -> pred_included (C k) (C l).
Proof.
  intros A C HC k l Hkl. induction Hkl.
  - intros x Hx. exact Hx.
  - intros x Hx. apply HC, IHHkl, Hx.
Qed.

Lemma finite_chain_bound : forall (A : Type) (C : nat -> A -> Prop) xs,
  increasing C ->
  (forall x, In x xs -> exists k, C k x) ->
  exists k, forall x, In x xs -> C k x.
Proof.
  intros A C xs HC. induction xs as [|x xs IH]; intro Hall.
  - exists 0. intros y Hy. inversion Hy.
  - destruct (Hall x (or_introl eq_refl)) as [kx Hx].
    destruct IH as [kt Ht].
    { intros y Hy. apply Hall. right. exact Hy. }
    exists (Nat.max kx kt). intros y [<-|Hy].
    + eapply increasing_le; [exact HC|apply Nat.le_max_l|exact Hx].
    + eapply increasing_le; [exact HC|apply Nat.le_max_r|apply Ht; exact Hy].
Qed.

Definition omega_union {A : Type} (C : nat -> A -> Prop) : A -> Prop :=
  fun x => exists k, C k x.

Theorem Kset_preserves_increasing_omega_unions : forall C c,
  increasing C ->
  Kset (omega_union C) c <-> exists k, Kset (C k) c.
Proof.
  intros C c HC. split.
  - intros [Hcheck Hdeps].
    destruct (@finite_chain_bound cert_id C (cert_dependencies c) HC Hdeps)
      as [k Hk].
    exists k. split; assumption.
  - intros [k [Hcheck Hdeps]]. split; [exact Hcheck|].
    intros d Hd. exists k. apply Hdeps, Hd.
Qed.

Theorem Fset_preserves_omega_unions : forall C o,
  Fset (omega_union C) o <-> exists k, Fset (C k) o.
Proof.
  intros C o. split.
  - intros [c [[k Hc] HE]]. exists k, c. split; assumption.
  - intros [k [c [Hc HE]]]. exists c. split; [exists k; exact Hc|exact HE].
Qed.

Record lattice_state : Type := mkLatticeState {
  lattice_X : cert_set;
  lattice_B : obstacle_set
}.

Definition U_delayed (S : lattice_state) : lattice_state :=
  mkLatticeState
    (fun c => lattice_X S c \/ Kset (lattice_X S) c)
    (fun o => lattice_B S o \/ Fset (lattice_X S) o).

Definition state_included (S T : lattice_state) : Prop :=
  pred_included (lattice_X S) (lattice_X T) /\
  pred_included (lattice_B S) (lattice_B T).

Theorem U_delayed_monotone : forall S T,
  state_included S T -> state_included (U_delayed S) (U_delayed T).
Proof.
  intros [X B] [Y C] [HXY HBC]. split; cbn.
  - intros c [HX|HK]. left; apply HXY, HX.
    right. eapply Kset_monotone; eauto.
  - intros o [HB|HF]. left; apply HBC, HB.
    right. eapply Fset_monotone; eauto.
Qed.

Definition X_omega : cert_set := omega_union X_stage.
Definition B_omega_delayed : obstacle_set := omega_union B_delayed_stage.

Theorem X_omega_fixed : forall c,
  X_omega c <-> X_omega c \/ Kset X_omega c.
Proof.
  intro c. split; [intro H; left; exact H|].
  intros [H|[Hcheck Hdeps]]; [exact H|].
  destruct (@finite_chain_bound cert_id X_stage (cert_dependencies c)
              (fun k => X_stage_mono (Nat.le_succ_diag_r k)) Hdeps)
    as [k Hk].
  exists (S k). apply X_stage_step. right. split; assumption.
Qed.

Theorem B_omega_delayed_fixed : forall o,
  B_omega_delayed o <-> B_omega_delayed o \/ Fset X_omega o.
Proof.
  intro o. split; [intro H; left; exact H|].
  intros [H|[c [[k Hc] HE]]]; [exact H|].
  exists (S k). apply B_delayed_stage_step. right.
  exists c. split; assumption.
Qed.

Definition pre_fixed (X : cert_set) (B : obstacle_set) : Prop :=
  pred_included (Kset X) X /\ pred_included (Fset X) B.

Lemma finite_stages_are_least : forall k X B,
  pre_fixed X B ->
  pred_included (X_stage k) X /\ pred_included (B_delayed_stage k) B.
Proof.
  induction k as [|k IH]; intros X B [HK HF].
  - split.
    + intros x Hx. unfold X_stage in Hx. discriminate Hx.
    + intros o Ho. exact (False_rect _ Ho).
  - destruct (IH X B (conj HK HF)) as [IHX IHB]. split.
    + intros c Hc. apply X_stage_step in Hc. destruct Hc as [Hc|Hc].
      * apply IHX, Hc.
      * apply HK. eapply Kset_monotone; [exact IHX|exact Hc].
    + intros o Ho. apply B_delayed_stage_step in Ho. destruct Ho as [Ho|Ho].
      * apply IHB, Ho.
      * apply HF. eapply Fset_monotone; [exact IHX|exact Ho].
Qed.

Theorem delayed_omega_is_least : forall X B,
  pre_fixed X B ->
  pred_included X_omega X /\ pred_included B_omega_delayed B.
Proof.
  intros X B Hpre. split.
  - intros c [k Hc]. apply (proj1 (finite_stages_are_least k Hpre)), Hc.
  - intros o [k Ho]. apply (proj2 (finite_stages_are_least k Hpre)), Ho.
Qed.

Theorem canonical_chain_strict_growth : forall k,
  X_stage (S k) (CChain k) /\ ~ X_stage k (CChain k).
Proof.
  intro k. unfold X_stage. rewrite !INX_chain_closed. split.
  - apply Nat.ltb_lt. lia.
  - intro H. apply Nat.ltb_lt in H. lia.
Qed.

Definition Omega_omega (p : list path_letter) : ownership :=
  ownership_action (Hol p) Omega0.

Inductive omega_path_state : Type :=
| ActiveSeed (p : list path_letter) (valid_seed : SEED p = true).

Definition P_omega (p : list path_letter) (Hp : SEED p = true) : omega_path_state :=
  ActiveSeed p Hp.

Definition project_finite_path (s : path_state) : option (list path_letter) :=
  match s with
  | PIdle => None
  | PActive _ xs => decode_path xs
  end.

Theorem Omega_stable_from_stage_two : forall k p,
  2 <= k -> Omega_at k p = Omega_omega p.
Proof. intros k p Hk. destruct k as [|[|k]]; cbn in *; try lia; reflexivity. Qed.

Theorem finite_paths_project_to_the_seed : forall k p,
  1 <= k -> project_finite_path (P_at k p) = Some p.
Proof.
  intros k p Hk. destruct k; [lia|]. cbn [project_finite_path P_at].
  apply decode_LIFT.
Qed.

Record delayed_limit_state (p : list path_letter) (Hp : SEED p = true) : Type :=
  mkDelayedLimitState {
    limit_X : cert_set;
    limit_B : obstacle_set;
    limit_Omega : ownership;
    limit_path : omega_path_state
  }.

Definition S_omega_delayed p Hp : delayed_limit_state p Hp :=
  mkDelayedLimitState p Hp X_omega B_omega_delayed (Omega_omega p) (P_omega p Hp).

Definition union_lattice_state (C : nat -> lattice_state) : lattice_state :=
  mkLatticeState
    (fun c => exists k, lattice_X (C k) c)
    (fun o => exists k, lattice_B (C k) o).

Definition increasing_lattice_chain (C : nat -> lattice_state) : Prop :=
  increasing (fun k => lattice_X (C k)) /\
  increasing (fun k => lattice_B (C k)).

Theorem U_delayed_preserves_increasing_omega_unions : forall C,
  increasing_lattice_chain C ->
  (forall c,
    lattice_X (U_delayed (union_lattice_state C)) c <->
    exists k, lattice_X (U_delayed (C k)) c) /\
  (forall o,
    lattice_B (U_delayed (union_lattice_state C)) o <->
    exists k, lattice_B (U_delayed (C k)) o).
Proof.
  intros C [HCX HCB]. split.
  - intro c. cbn. split.
    + intros [[k HX]|HK].
      * exists k. left. exact HX.
      * apply Kset_preserves_increasing_omega_unions in HK; [|exact HCX].
        destruct HK as [k HK]. exists k. right. exact HK.
    + intros [k [HX|HK]].
      * left. exists k. exact HX.
      * right. apply Kset_preserves_increasing_omega_unions; [exact HCX|].
        exists k. exact HK.
  - intro o. cbn. split.
    + intros [[k HB]|HF].
      * exists k. left. exact HB.
      * apply Fset_preserves_omega_unions in HF.
        destruct HF as [k HF]. exists k. right. exact HF.
    + intros [k [HB|HF]].
      * left. exists k. exact HB.
      * right. apply Fset_preserves_omega_unions. exists k. exact HF.
Qed.

(** * 12.6. Arithmetic display, execution separation, and EUQ interface *)

Definition ar_args1 (t : term) : terms := TCons t TNil.
Definition ar_args2 (t u : term) : terms := TCons t (TCons u TNil).
Definition ar_args3 (t u v : term) : terms :=
  TCons t (TCons u (TCons v TNil)).

Definition ar_PC (c : term) : formula :=
  Rel (RBase 200 [SN]) (ar_args1 c).
Definition ar_root (c q : term) : formula :=
  Rel (RBase 201 [SN; SN]) (ar_args2 c q).
Definition ar_dep (c i d : term) : formula :=
  Rel (RBase 202 [SN; SN; SN]) (ar_args3 c i d).
Definition ar_length (c ell : term) : formula :=
  Rel (RBase 203 [SN; SN]) (ar_args2 c ell).
Definition ar_inx (k : nat) (d : term) : formula :=
  Rel (RBase (204 + k) [SN]) (ar_args1 d).
Definition ar_lt (i ell : term) : formula :=
  Rel (RBase 205 [SN; SN]) (ar_args2 i ell).

(** De Bruijn indices in the displayed matrix are, from the innermost point,
    d=0, i=1, ell=2, c=3, q=4.  Outside the inner binders the corresponding
    lower indices are used. *)
Definition theta_k (k : nat) : formula :=
  Ex SN (Ex SN
    (And (ar_PC (TVar SN 1))
      (And (ar_root (TVar SN 1) (TVar SN 2))
        (And (ar_length (TVar SN 1) (TVar SN 0))
          (All SN
            (Imp (ar_lt (TVar SN 0) (TVar SN 1))
              (Ex SN
                (And (ar_dep (TVar SN 3) (TVar SN 1) (TVar SN 0))
                     (ar_inx k (TVar SN 0)))))))))).

Theorem theta_k_is_N_sorted : forall k, formula_wtb k (theta_k k) = true.
Proof. reflexivity. Qed.

Definition CanCert_canonical (k q : nat) : Prop :=
  exists c,
    root_code c = q /\
    registered_PCOK c = true /\
    forall d, In d (cert_dependencies c) -> X_stage k d.

Definition theta_decoded_semantics (k q : nat) : Prop :=
  exists c ell,
    registered_PCOK c = true /\
    root_code c = q /\
    length (cert_dependencies c) = ell /\
    forall i, i < ell ->
      exists d,
        nth_error (cert_dependencies c) i = Some d /\ X_stage k d.

Theorem theta_decoded_represents_CanCert : forall k q,
  theta_decoded_semantics k q <-> CanCert_canonical k q.
Proof.
  intros k q. split.
  - intros [c [ell [Hcheck [Hroot [Hlen Hindexed]]]]].
    exists c. split; [exact Hroot|]. split; [exact Hcheck|].
    intros d Hd.
    destruct (In_nth_error _ _ Hd) as [i Hi].
    assert (Hilength : i < length (cert_dependencies c)).
    { apply nth_error_Some. rewrite Hi. discriminate. }
    rewrite Hlen in Hilength.
    destruct (Hindexed i Hilength) as [d' [Hi' HX]].
    rewrite Hi in Hi'. inversion Hi'. subst. exact HX.
  - intros [c [Hroot [Hcheck Hdeps]]].
    exists c, (length (cert_dependencies c)).
    repeat split; try assumption.
    intros i Hi.
    destruct (nth_error (cert_dependencies c) i) as [d|] eqn:Hnth.
    + exists d. split; [reflexivity|]. apply Hdeps.
      eapply nth_error_In. exact Hnth.
    + apply nth_error_None in Hnth. lia.
Qed.

Theorem no_N_to_current_Low_decoder : forall k f,
  fsym_allowedb k f = true -> fsig f = ([SN], SLow k) -> False.
Proof.
  intros k f Hallowed Hsig. destruct f; cbn in Hsig; try discriminate.
  inversion Hsig; subst. cbn in Hallowed. discriminate.
Qed.

Theorem Low_values_have_strictly_earlier_source : forall k u,
  low_okb k u = true -> low_source u < k.
Proof.
  intros k u H. unfold low_okb in H.
  apply andb_true_iff in H as [Hsource _].
  apply andb_true_iff in Hsource as [Hsource _].
  apply andb_true_iff in Hsource as [Hsource _].
  apply Nat.ltb_lt. exact Hsource.
Qed.

(** Unlike the concrete canonical chain used for trace calculations,
    [CanCert_X] ranges over all finite checked derivation objects. *)
Definition CanCert_X (k : nat) (tau : timing) (q : sequent) : Prop :=
  exists d, DCHK k tau d = true /\ derivation_root d = q.

Definition T_closed_proves (k : nat) (tau : timing) (A : formula) : Prop :=
  exists d,
    DCHK k tau d = true /\ derivation_root d = mkSeq [] [A].

Theorem closed_proof_certificate_equivalence : forall k tau A,
  T_closed_proves k tau A <-> CanCert_X k tau (mkSeq [] [A]).
Proof. reflexivity. Qed.

Definition theory_consistent (T : formula -> Prop) : Prop := ~ T Bot.

Definition theory_recursively_enumerable (T : formula -> Prop) : Prop :=
  exists enumerate : nat -> option formula,
    forall A, T A <-> exists n, enumerate n = Some A.

Definition extends_Robinson_Q (T : formula -> Prop) : Prop :=
  forall A, In A AxQ -> T A.

Definition Q_axiom_derivation (A : formula) : derivation_tree :=
  DNode (EvGQ (WQAx [] [] A)) (mkSeq [] [A]) DNil.

Theorem Q_axiom_derivation_checks : forall k tau A,
  In A AxQ -> DCHK k tau (Q_axiom_derivation A) = true.
Proof.
  intros k tau A HA. unfold AxQ in HA.
  destruct HA as [H|[H|[H|[H|[H|[H|[H|H]]]]]]];
    try contradiction; subst A; reflexivity.
Qed.

Theorem checked_closed_theory_extends_Robinson_Q : forall k tau,
  extends_Robinson_Q (T_closed_proves k tau).
Proof.
  intros k tau A HA. exists (Q_axiom_derivation A). split.
  - apply Q_axiom_derivation_checks. exact HA.
  - reflexivity.
Qed.

Section EUQ_Interface.
  Variable external_EUQ : forall T : formula -> Prop,
    theory_consistent T ->
    theory_recursively_enumerable T ->
    extends_Robinson_Q T ->
    ~ exists decide : formula -> bool,
        forall A, decide A = true <-> T A.

  Theorem no_total_same_layer_certificate_decider : forall k tau,
    theory_consistent (T_closed_proves k tau) ->
    theory_recursively_enumerable (T_closed_proves k tau) ->
    ~ exists decide : sequent -> bool,
        forall q, decide q = true <-> CanCert_X k tau q.
  Proof.
    intros k tau Hconsistent Hre [decide Hdecide].
    apply (@external_EUQ (T_closed_proves k tau) Hconsistent Hre
             (checked_closed_theory_extends_Robinson_Q k tau)).
    exists (fun A => decide (mkSeq [] [A])). intro A.
    rewrite Hdecide. apply closed_proof_certificate_equivalence.
  Qed.
End EUQ_Interface.

(** * 12.7. The two stated ablations *)

Definition forget_ownership_and_path (s : finite_state)
    : list cert_id * list obstacle := (state_X s, state_B s).

Theorem ownership_path_ablation_is_exact : forall k tau p q,
  forget_ownership_and_path (state_at k tau p) =
  forget_ownership_and_path (state_at k tau q).
Proof. reflexivity. Qed.

Definition layered_reflection_state (k : nat) : list cert_id * list obstacle :=
  (XLIST k, []).

Theorem feedback_edge_ablation_is_exact : forall k p,
  forget_ownership_and_path (state_at k Ablated p) =
  layered_reflection_state k.
Proof. reflexivity. Qed.

(** * 13. A single package naming every component of SRBE_065 *)

Record srbe_system : Type := mkSRBESystem {
  sys_fsym_allowed : nat -> fsym -> bool;
  sys_rsym_allowed : nat -> rsym -> bool;
  sys_term_sort : nat -> term -> option sort;
  sys_formula_wt : nat -> formula -> bool;
  sys_sequent_wt : nat -> sequent -> bool;
  sys_fv_term : term -> list variable;
  sys_fv_formula : formula -> list variable;
  sys_fv_sequent : sequent -> list variable;
  sys_lift_formula : sort -> nat -> formula -> formula;
  sys_free_rename : sort -> formula -> nat -> nat -> formula;
  sys_sub_term : sort -> term -> nat -> term -> term;
  sys_sub_formula : sort -> formula -> nat -> term -> formula;
  sys_gq_rule : nat -> list sequent -> sequent -> Prop;
  sys_rule_scheme : Type;
  sys_certificate : Type;
  sys_pcok : open_certificate -> bool;
  sys_registry : open_certificate -> Prop;
  sys_inx : cert_id -> nat -> bool;
  sys_enum : nat -> nat -> list low_value;
  sys_barriers : timing -> nat -> list obstacle;
  sys_adapt : list obstacle -> nat -> nat -> bool;
  sys_seed : list path_letter -> bool;
  sys_lift_path : nat -> list path_letter -> list low_value;
  sys_pathchk : nat -> list low_value -> bool;
  sys_hol : list path_letter -> permutation;
  sys_omega : nat -> list path_letter -> ownership;
  sys_path_state : nat -> list path_letter -> path_state;
  sys_under : sformula -> formula;
  sys_form : nat -> ownership -> assignment_context -> sformula -> Prop;
  sys_dchk_h : staged_annotated_derivation -> assignment_context -> bool;
  sys_derivable : assignment_context -> annotated_context -> annotated_context ->
                  nat -> list path_letter -> timing -> Prop
}.

Definition SRBE_065 : srbe_system :=
  {| sys_fsym_allowed := fsym_allowedb;
     sys_rsym_allowed := rsym_allowedb;
     sys_term_sort := term_sort;
     sys_formula_wt := formula_wtb;
     sys_sequent_wt := sequent_wtb;
     sys_fv_term := fv_term;
     sys_fv_formula := fv_formula;
     sys_fv_sequent := fv_sequent;
     sys_lift_formula := lift_formula;
     sys_free_rename := FreeRen;
     sys_sub_term := sub_term;
     sys_sub_formula := sub_formula;
     sys_gq_rule := GQRule;
     sys_rule_scheme := rule_scheme;
     sys_certificate := open_certificate;
     sys_pcok := GeneralPCOK;
     sys_registry := OpenReg_H;
     sys_inx := INX;
     sys_enum := e_k;
     sys_barriers := barriers;
     sys_adapt := Adapt;
     sys_seed := SEED;
     sys_lift_path := LIFT;
     sys_pathchk := PATHCHK;
     sys_hol := Hol;
     sys_omega := Omega_at;
     sys_path_state := P_at;
     sys_under := UNDER;
     sys_form := Form;
     sys_dchk_h := DCHK_H;
     sys_derivable := StageDerivable |}.
