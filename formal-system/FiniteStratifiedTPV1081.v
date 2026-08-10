From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.

Import ListNotations.

Module FiniteStratifiedTPV1081.

Inductive sort : Type :=
| SortN
| SortS.

Record var : Type := {
  var_sort : sort;
  var_id : nat
}.

Definition sort_eqb (a b : sort) : bool :=
  match a, b with
  | SortN, SortN => true
  | SortS, SortS => true
  | _, _ => false
  end.

Definition var_eqb (x y : var) : bool :=
  sort_eqb (var_sort x) (var_sort y) && Nat.eqb (var_id x) (var_id y).

Fixpoint remove_var (x : var) (xs : list var) : list var :=
  match xs with
  | [] => []
  | y :: ys =>
      if var_eqb x y then remove_var x ys else y :: remove_var x ys
  end.

Fixpoint union_var (xs ys : list var) : list var :=
  match xs with
  | [] => ys
  | x :: rest =>
      if existsb (var_eqb x) ys then union_var rest ys
      else x :: union_var rest ys
  end.

Fixpoint max_id_for_sort (s : sort) (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: rest =>
      if sort_eqb (var_sort x) s
      then Nat.max (var_id x) (max_id_for_sort s rest)
      else max_id_for_sort s rest
  end.

Definition fresh (s : sort) (xs : list var) : var :=
  {| var_sort := s; var_id := S (max_id_for_sort s xs) |}.

Inductive func_symbol : Type :=
| FZero
| FOne
| FAdd
| FMul
| FLen
| FPrim : nat -> list sort -> sort -> func_symbol.

Inductive rel_symbol : Type :=
| RLe
| RMem
| RPrim : nat -> list sort -> rel_symbol
| RAxHat : nat -> rel_symbol
| REvTreeHat : nat -> rel_symbol
| RSat : nat -> rel_symbol
| RCertT : nat -> rel_symbol
| RPrT : nat -> rel_symbol
| RCertEv : nat -> rel_symbol
| RPrEv : nat -> rel_symbol
| RProofDef : nat -> rel_symbol
| REvTreeDef : nat -> rel_symbol.

Definition func_type (f : func_symbol) : list sort * sort :=
  match f with
  | FZero => ([], SortN)
  | FOne => ([], SortN)
  | FAdd => ([SortN; SortN], SortN)
  | FMul => ([SortN; SortN], SortN)
  | FLen => ([SortS], SortN)
  | FPrim _ args out => (args, out)
  end.

Definition rel_type (R : rel_symbol) : list sort :=
  match R with
  | RLe => [SortN; SortN]
  | RMem => [SortN; SortS]
  | RPrim _ args => args
  | RAxHat _ => [SortN]
  | REvTreeHat _ => [SortN; SortN]
  | RSat _ => [SortN]
  | RCertT _ => [SortN; SortN]
  | RPrT _ => [SortN]
  | RCertEv _ => [SortN; SortN]
  | RPrEv _ => [SortN]
  | RProofDef _ => [SortN; SortN]
  | REvTreeDef _ => [SortN; SortN]
  end.

Definition in_height (H n : nat) : Prop := n <= H.
Definition proper_lower_layer (i n : nat) : Prop := i < n.
Definition positive_layer (k : nat) : Prop := 1 <= k.

Definition func_in_signature (H n : nat) (_ : func_symbol) : Prop :=
  in_height H n.

Definition rel_in_signature (H n : nat) (R : rel_symbol) : Prop :=
  in_height H n /\
  match R with
  | RLe | RMem | RPrim _ _ => True
  | RAxHat i | REvTreeHat i | RSat i | RCertT i | RPrT i
  | RProofDef i | REvTreeDef i => proper_lower_layer i n
  | RCertEv k | RPrEv k => positive_layer k /\ k <= n
  end.

Theorem signature_monotone :
  forall H n m R,
    n <= m ->
    m <= H ->
    rel_in_signature H n R ->
    rel_in_signature H m R.
Proof.
  intros H n m R Hnm Hm [_ HR].
  split; [exact Hm|].
  destruct R; simpl in *.
  - exact I.
  - exact I.
  - exact I.
  - unfold proper_lower_layer in *; lia.
  - unfold proper_lower_layer in *; lia.
  - unfold proper_lower_layer in *; lia.
  - unfold proper_lower_layer in *; lia.
  - unfold proper_lower_layer in *; lia.
  - destruct HR as [Hpos Hle].
    unfold positive_layer in *; split; lia.
  - destruct HR as [Hpos Hle].
    unfold positive_layer in *; split; lia.
  - unfold proper_lower_layer in *; lia.
  - unfold proper_lower_layer in *; lia.
Qed.

Theorem sat_not_in_own_layer :
  forall H i, i <= H -> ~ rel_in_signature H i (RSat i).
Proof.
  intros H i Hi [_ Hlt].
  simpl in Hlt.
  unfold proper_lower_layer in Hlt.
  lia.
Qed.

Theorem truth_proof_symbols_enter_next_layer :
  forall H i,
    S i <= H ->
    rel_in_signature H (S i) (RSat i) /\
    rel_in_signature H (S i) (RCertT i) /\
    rel_in_signature H (S i) (RPrT i).
Proof.
  intros H i Hi.
  repeat split; simpl; unfold proper_lower_layer, in_height; lia.
Qed.

Theorem eval_symbols_enter_next_layer :
  forall H i,
    S i <= H ->
    rel_in_signature H (S i) (RCertEv (S i)) /\
    rel_in_signature H (S i) (RPrEv (S i)).
Proof.
  intros H i Hi.
  repeat split; simpl; unfold positive_layer, in_height; lia.
Qed.

Inductive term : Type :=
| TVar : var -> term
| TNum : nat -> term
| TStr : list bool -> term
| TFun : func_symbol -> list term -> term.

Inductive formula : Type :=
| FEq : term -> term -> formula
| FRel : rel_symbol -> list term -> formula
| FNeg : formula -> formula
| FAnd : formula -> formula -> formula
| FOr : formula -> formula -> formula
| FImp : formula -> formula -> formula
| FAll : var -> formula -> formula
| FEx : var -> formula -> formula.

Inductive term_wf (H n : nat) : term -> sort -> Prop :=
| WfVar :
    forall x,
      n <= H ->
      term_wf H n (TVar x) (var_sort x)
| WfNum :
    forall k,
      n <= H ->
      term_wf H n (TNum k) SortN
| WfStr :
    forall bs,
      n <= H ->
      term_wf H n (TStr bs) SortS
| WfFun :
    forall f args arg_sorts out_sort,
      func_type f = (arg_sorts, out_sort) ->
      func_in_signature H n f ->
      Forall2 (term_wf H n) args arg_sorts ->
      term_wf H n (TFun f args) out_sort.

Inductive formula_wf (H n : nat) : formula -> Prop :=
| WfEq :
    forall u v s,
      term_wf H n u s ->
      term_wf H n v s ->
      formula_wf H n (FEq u v)
| WfRel :
    forall R args,
      rel_in_signature H n R ->
      Forall2 (term_wf H n) args (rel_type R) ->
      formula_wf H n (FRel R args)
| WfNeg :
    forall A,
      formula_wf H n A ->
      formula_wf H n (FNeg A)
| WfAnd :
    forall A B,
      formula_wf H n A ->
      formula_wf H n B ->
      formula_wf H n (FAnd A B)
| WfOr :
    forall A B,
      formula_wf H n A ->
      formula_wf H n B ->
      formula_wf H n (FOr A B)
| WfImp :
    forall A B,
      formula_wf H n A ->
      formula_wf H n B ->
      formula_wf H n (FImp A B)
| WfAll :
    forall x A,
      formula_wf H n A ->
      formula_wf H n (FAll x A)
| WfEx :
    forall x A,
      formula_wf H n A ->
      formula_wf H n (FEx x A).

Fixpoint fv_term (t : term) : list var :=
  match t with
  | TVar x => [x]
  | TNum _ => []
  | TStr _ => []
  | TFun _ args =>
      let fix scan (ts : list term) : list var :=
        match ts with
        | [] => []
        | u :: rest => union_var (fv_term u) (scan rest)
        end
      in scan args
  end.

Fixpoint fv_terms (ts : list term) : list var :=
  match ts with
  | [] => []
  | t :: rest => union_var (fv_term t) (fv_terms rest)
  end.

Fixpoint fv_formula (A : formula) : list var :=
  match A with
  | FEq u v => union_var (fv_term u) (fv_term v)
  | FRel _ args => fv_terms args
  | FNeg B => fv_formula B
  | FAnd B C | FOr B C | FImp B C =>
      union_var (fv_formula B) (fv_formula C)
  | FAll x B | FEx x B => remove_var x (fv_formula B)
  end.

Fixpoint subst_term (t : term) (x : var) (u : term) {struct t} : term :=
  match t with
  | TVar y => if var_eqb y x then u else TVar y
  | TNum k => TNum k
  | TStr bs => TStr bs
  | TFun f args => TFun f (map (fun a => subst_term a x u) args)
  end.

Fixpoint rename_var_term (old new : var) (t : term) {struct t} : term :=
  match t with
  | TVar y => if var_eqb y old then TVar new else TVar y
  | TNum k => TNum k
  | TStr bs => TStr bs
  | TFun f args => TFun f (map (rename_var_term old new) args)
  end.

Fixpoint rename_var_formula (old new : var) (A : formula) {struct A} : formula :=
  match A with
  | FEq u v => FEq (rename_var_term old new u) (rename_var_term old new v)
  | FRel R args => FRel R (map (rename_var_term old new) args)
  | FNeg B => FNeg (rename_var_formula old new B)
  | FAnd B C => FAnd (rename_var_formula old new B) (rename_var_formula old new C)
  | FOr B C => FOr (rename_var_formula old new B) (rename_var_formula old new C)
  | FImp B C => FImp (rename_var_formula old new B) (rename_var_formula old new C)
  | FAll y B =>
      let y' := if var_eqb y old then new else y in
      FAll y' (rename_var_formula old new B)
  | FEx y B =>
      let y' := if var_eqb y old then new else y in
      FEx y' (rename_var_formula old new B)
  end.

Fixpoint subst_formula (A : formula) (x : var) (u : term) {struct A} : formula :=
  match A with
  | FEq a b => FEq (subst_term a x u) (subst_term b x u)
  | FRel R args => FRel R (map (fun a => subst_term a x u) args)
  | FNeg B => FNeg (subst_formula B x u)
  | FAnd B C => FAnd (subst_formula B x u) (subst_formula C x u)
  | FOr B C => FOr (subst_formula B x u) (subst_formula C x u)
  | FImp B C => FImp (subst_formula B x u) (subst_formula C x u)
  | FAll y B =>
      if var_eqb y x then FAll y B
      else if existsb (var_eqb y) (fv_term u)
           then
             let z := fresh (var_sort y) (fv_formula B ++ fv_term u ++ [x; y]) in
             FAll z (rename_var_formula y z (subst_formula B x u))
           else FAll y (subst_formula B x u)
  | FEx y B =>
      if var_eqb y x then FEx y B
      else if existsb (var_eqb y) (fv_term u)
           then
             let z := fresh (var_sort y) (fv_formula B ++ fv_term u ++ [x; y]) in
             FEx z (rename_var_formula y z (subst_formula B x u))
           else FEx y (subst_formula B x u)
  end.

Inductive alpha_equiv : formula -> formula -> Prop :=
| AlphaRefl :
    forall A, alpha_equiv A A
| AlphaSym :
    forall A B, alpha_equiv A B -> alpha_equiv B A
| AlphaTrans :
    forall A B C, alpha_equiv A B -> alpha_equiv B C -> alpha_equiv A C
| AlphaNeg :
    forall A B, alpha_equiv A B -> alpha_equiv (FNeg A) (FNeg B)
| AlphaAnd :
    forall A A' B B',
      alpha_equiv A A' ->
      alpha_equiv B B' ->
      alpha_equiv (FAnd A B) (FAnd A' B')
| AlphaOr :
    forall A A' B B',
      alpha_equiv A A' ->
      alpha_equiv B B' ->
      alpha_equiv (FOr A B) (FOr A' B')
| AlphaImp :
    forall A A' B B',
      alpha_equiv A A' ->
      alpha_equiv B B' ->
      alpha_equiv (FImp A B) (FImp A' B')
| AlphaAllCong :
    forall x A B,
      alpha_equiv A B ->
      alpha_equiv (FAll x A) (FAll x B)
| AlphaExCong :
    forall x A B,
      alpha_equiv A B ->
      alpha_equiv (FEx x A) (FEx x B)
| AlphaAllRename :
    forall x y A,
      var_sort x = var_sort y ->
      ~ In y (remove_var x (fv_formula A)) ->
      alpha_equiv (FAll x A) (FAll y (subst_formula A x (TVar y)))
| AlphaExRename :
    forall x y A,
      var_sort x = var_sort y ->
      ~ In y (remove_var x (fv_formula A)) ->
      alpha_equiv (FEx x A) (FEx y (subst_formula A x (TVar y))).

Definition is_atomic_formula (A : formula) : Prop :=
  match A with
  | FEq _ _ => True
  | FRel _ _ => True
  | _ => False
  end.

Definition leq_formula (x : var) (t : term) : formula :=
  FRel RLe [TVar x; t].

Definition strlen_leq_formula (X : var) (t : term) : formula :=
  FRel RLe [TFun FLen [TVar X]; t].

Inductive bform (H n : nat) : formula -> Prop :=
| BAtomic :
    forall A,
      formula_wf H n A ->
      is_atomic_formula A ->
      bform H n A
| BNeg :
    forall A, bform H n A -> bform H n (FNeg A)
| BAnd :
    forall A B, bform H n A -> bform H n B -> bform H n (FAnd A B)
| BOr :
    forall A B, bform H n A -> bform H n B -> bform H n (FOr A B)
| BImp :
    forall A B, bform H n A -> bform H n B -> bform H n (FImp A B)
| BAllN :
    forall x t A,
      var_sort x = SortN ->
      term_wf H n t SortN ->
      ~ In x (fv_term t) ->
      bform H n A ->
      bform H n (FAll x (FImp (leq_formula x t) A))
| BExN :
    forall x t A,
      var_sort x = SortN ->
      term_wf H n t SortN ->
      ~ In x (fv_term t) ->
      bform H n A ->
      bform H n (FEx x (FAnd (leq_formula x t) A))
| BAllS :
    forall X t A,
      var_sort X = SortS ->
      term_wf H n t SortN ->
      ~ In X (fv_term t) ->
      bform H n A ->
      bform H n (FAll X (FImp (strlen_leq_formula X t) A))
| BExS :
    forall X t A,
      var_sort X = SortS ->
      term_wf H n t SortN ->
      ~ In X (fv_term t) ->
      bform H n A ->
      bform H n (FEx X (FAnd (strlen_leq_formula X t) A)).

Definition bsent (H n : nat) (A : formula) : Prop :=
  bform H n A /\ fv_formula A = [].

Fixpoint bool_list_eqb (xs ys : list bool) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Bool.eqb x y && bool_list_eqb xs' ys'
  | _, _ => false
  end.

Inductive nat_term_value : term -> nat -> Prop :=
| ValZero :
    nat_term_value (TFun FZero []) 0
| ValOne :
    nat_term_value (TFun FOne []) 1
| ValNum :
    forall k, nat_term_value (TNum k) k
| ValAdd :
    forall a b va vb,
      nat_term_value a va ->
      nat_term_value b vb ->
      nat_term_value (TFun FAdd [a; b]) (va + vb)
| ValMul :
    forall a b va vb,
      nat_term_value a va ->
      nat_term_value b vb ->
      nat_term_value (TFun FMul [a; b]) (va * vb)
| ValLen :
    forall bs,
      nat_term_value (TFun FLen [TStr bs]) (length bs).

Definition value_determined (H n : nat) (t : term) : Prop :=
  term_wf H n t SortN /\ exists v, nat_term_value t v.

Inductive decsent (H n : nat) : formula -> Prop :=
| DecAtomic :
    forall A,
      bsent H n A ->
      is_atomic_formula A ->
      decsent H n A
| DecNeg :
    forall A, decsent H n A -> decsent H n (FNeg A)
| DecAnd :
    forall A B, decsent H n A -> decsent H n B -> decsent H n (FAnd A B)
| DecOr :
    forall A B, decsent H n A -> decsent H n B -> decsent H n (FOr A B)
| DecImp :
    forall A B, decsent H n A -> decsent H n B -> decsent H n (FImp A B)
| DecBoundedN :
    forall x t A Q,
      var_sort x = SortN ->
      value_determined H n t ->
      ~ In x (fv_term t) ->
      decsent H n A ->
      (Q = FAll x (FImp (leq_formula x t) A) \/
       Q = FEx x (FAnd (leq_formula x t) A)) ->
      decsent H n Q
| DecBoundedS :
    forall X t A Q,
      var_sort X = SortS ->
      value_determined H n t ->
      ~ In X (fv_term t) ->
      decsent H n A ->
      (Q = FAll X (FImp (strlen_leq_formula X t) A) \/
       Q = FEx X (FAnd (strlen_leq_formula X t) A)) ->
      decsent H n Q.

Fixpoint code_term (t : term) : nat :=
  match t with
  | TVar x => 11 + 2 * var_id x
  | TNum k => 17 + 3 * k
  | TStr bs => 19 + length bs
  | TFun _ args => 23 + fold_right Nat.add 0 (map code_term args)
  end.

Fixpoint code_formula (A : formula) : nat :=
  match A with
  | FEq u v => 31 + code_term u + code_term v
  | FRel _ args => 37 + fold_right Nat.add 0 (map code_term args)
  | FNeg B => 41 + code_formula B
  | FAnd B C => 43 + code_formula B + code_formula C
  | FOr B C => 47 + code_formula B + code_formula C
  | FImp B C => 53 + code_formula B + code_formula C
  | FAll x B => 59 + var_id x + code_formula B
  | FEx x B => 61 + var_id x + code_formula B
  end.

Definition quote (A : formula) : term := TNum (code_formula A).

Definition sat_formula (i : nat) (A : formula) : formula :=
  FRel (RSat i) [quote A].

Definition certT_formula (i p : nat) (A : formula) : formula :=
  FRel (RCertT i) [TNum p; quote A].

Definition prT_formula (i : nat) (A : formula) : formula :=
  FRel (RPrT i) [quote A].

Definition certEv_formula (k e : nat) (A : formula) : formula :=
  FRel (RCertEv k) [TNum e; quote A].

Definition prEv_formula (k : nat) (A : formula) : formula :=
  FRel (RPrEv k) [quote A].

Definition axHat_formula (i : nat) (A : formula) : formula :=
  FRel (RAxHat i) [quote A].

Definition evTreeHat_formula (i e : nat) (A : formula) : formula :=
  FRel (REvTreeHat i) [TNum e; quote A].

Definition iff_formula (A B : formula) : formula :=
  FAnd (FImp A B) (FImp B A).

Inductive log_axiom (H n : nat) : formula -> Prop :=
| LogImp1 :
    forall A B,
      formula_wf H n A ->
      formula_wf H n B ->
      log_axiom H n (FImp A (FImp B A))
| LogImp2 :
    forall A B C,
      formula_wf H n A ->
      formula_wf H n B ->
      formula_wf H n C ->
      log_axiom H n
        (FImp (FImp A (FImp B C))
          (FImp (FImp A B) (FImp A C)))
| LogImp3 :
    forall A B,
      formula_wf H n A ->
      formula_wf H n B ->
      log_axiom H n
        (FImp (FImp (FNeg A) (FNeg B)) (FImp B A))
| LogForall1 :
    forall x A t,
      formula_wf H n (FAll x A) ->
      term_wf H n t (var_sort x) ->
      log_axiom H n (FImp (FAll x A) (subst_formula A x t))
| LogForall2 :
    forall x A B,
      formula_wf H n A ->
      formula_wf H n B ->
      ~ In x (fv_formula A) ->
      log_axiom H n (FImp (FAll x (FImp A B)) (FImp A (FAll x B))).

Inductive primitive_diagram (H : nat) : formula -> Prop :=
| PrimFunctionGraph :
    forall k args out,
      primitive_diagram H (FEq (TFun (FPrim k args out) []) (TFun (FPrim k args out) []))
| PrimRelationGraph :
    forall k args,
      primitive_diagram H (FRel (RPrim k args) []).

Inductive basic_axiom (H n : nat) : formula -> Prop :=
| BasicZero :
    n <= H -> basic_axiom H n (FEq (TNum 0) (TNum 0))
| BasicOne :
    n <= H -> basic_axiom H n (FEq (TNum 1) (TNum 1))
| BasicLeqRefl :
    forall t,
      term_wf H n t SortN ->
      basic_axiom H n (FRel RLe [t; t])
| BasicMemImage :
    forall k bs,
      n <= H ->
      basic_axiom H n (FRel RMem [TNum k; TStr bs]).

Inductive theory_axiom (H n : nat) : formula -> Prop :=
| TheoryLog :
    forall A, log_axiom H n A -> theory_axiom H n A
| TheoryEqRefl :
    forall t s,
      term_wf H n t s ->
      theory_axiom H n (FEq t t)
| TheoryEqSubst :
    forall A x u v,
      formula_wf H n A ->
      term_wf H n u (var_sort x) ->
      term_wf H n v (var_sort x) ->
      theory_axiom H n
        (FImp (FEq u v) (FImp (subst_formula A x u) (subst_formula A x v)))
| TheoryPrimitive :
    forall A, primitive_diagram H A -> theory_axiom H n A
| TheoryBasic :
    forall A, basic_axiom H n A -> theory_axiom H n A
| TheoryBInd :
    forall A x t,
      bform H n A ->
      var_sort x = SortN ->
      term_wf H n t SortN ->
      theory_axiom H n
        (FImp
          (FAnd
            (subst_formula A x (TNum 0))
            (FAll x
              (FImp (leq_formula x t)
                (FImp A (subst_formula A x (TFun FAdd [TVar x; TNum 1]))))))
          (FAll x (FImp (leq_formula x t) A)))
| TheoryDefCertT :
    forall i,
      i < n ->
      theory_axiom H n
        (iff_formula
          (FRel (RCertT i) [TVar {| var_sort := SortN; var_id := 0 |};
                            TVar {| var_sort := SortN; var_id := 1 |}])
          (FRel (RProofDef i) [TVar {| var_sort := SortN; var_id := 0 |};
                                TVar {| var_sort := SortN; var_id := 1 |}]))
| TheoryDefPrT :
    forall i,
      i < n ->
      theory_axiom H n
        (FImp
          (FRel (RPrT i) [TVar {| var_sort := SortN; var_id := 0 |}])
          (FEx {| var_sort := SortN; var_id := 1 |}
             (FRel (RCertT i) [TVar {| var_sort := SortN; var_id := 1 |};
                               TVar {| var_sort := SortN; var_id := 0 |}])))
| TheoryDefCertEv :
    forall k,
      1 <= k <= n ->
      theory_axiom H n
        (iff_formula
          (FRel (RCertEv k) [TVar {| var_sort := SortN; var_id := 0 |};
                             TVar {| var_sort := SortN; var_id := 1 |}])
          (FRel (REvTreeDef (pred k)) [TVar {| var_sort := SortN; var_id := 0 |};
                                        TVar {| var_sort := SortN; var_id := 1 |}]))
| TheoryDefPrEv :
    forall k,
      1 <= k <= n ->
      theory_axiom H n
        (FImp
          (FRel (RPrEv k) [TVar {| var_sort := SortN; var_id := 0 |}])
          (FEx {| var_sort := SortN; var_id := 1 |}
             (FRel (RCertEv k) [TVar {| var_sort := SortN; var_id := 1 |};
                                TVar {| var_sort := SortN; var_id := 0 |}])))
| TheoryTruth :
    forall i A,
      i < n ->
      bsent H i A ->
      theory_axiom H n (iff_formula (sat_formula i A) A)
| TheoryEvalEq :
    forall i A,
      i < n ->
      decsent H i A ->
      theory_axiom H n
        (iff_formula
          (sat_formula i A)
          (prEv_formula (S i) (sat_formula i A)))
| TheorySound :
    forall i A,
      i < n ->
      bsent H i A ->
      theory_axiom H n (FImp (prT_formula i A) (sat_formula i A))
| TheoryProofMp :
    forall i A B,
      i < n ->
      bsent H i A ->
      bsent H i B ->
      theory_axiom H n
        (FImp
          (prT_formula i (FImp A B))
          (FImp (prT_formula i A) (prT_formula i B)))
| TheoryProofUp :
    forall i A,
      S i < n ->
      bsent H i A ->
      theory_axiom H n
        (FImp
          (prT_formula i A)
          (prT_formula (S i) (prT_formula i A))).

Inductive line_ok (H n : nat) : formula -> Prop :=
| LineLog :
    forall A, log_axiom H n A -> line_ok H n A
| LineTheory :
    forall A, theory_axiom H n A -> line_ok H n A
| LineAlpha :
    forall A B, alpha_equiv A B -> line_ok H n A -> line_ok H n B.

Definition mp_sequence (p q : list formula) (B : formula) : list formula :=
  p ++ q ++ [B].

Definition up_sequence (p : list formula) (A : formula) : list formula :=
  p ++ [prT_formula 0 A].

Inductive proof_cert (H : nat) : nat -> list formula -> formula -> Prop :=
| ProofLine :
    forall n A,
      n <= H ->
      line_ok H n A ->
      proof_cert H n [A] A
| ProofMP :
    forall n p q A B,
      proof_cert H n p (FImp A B) ->
      proof_cert H n q A ->
      proof_cert H n (mp_sequence p q B) B
| ProofGen :
    forall n p x A,
      proof_cert H n p A ->
      proof_cert H n (p ++ [FAll x A]) (FAll x A)
| ProofAlpha :
    forall n p A B,
      proof_cert H n p A ->
      alpha_equiv A B ->
      proof_cert H n (p ++ [B]) B
| ProofUp :
    forall i p A,
      S i <= H ->
      proof_cert H i p A ->
      proof_cert H (S i) (p ++ [prT_formula i A]) (prT_formula i A).

Definition proves (H n : nat) (A : formula) : Prop :=
  exists p, proof_cert H n p A.

Definition proof_predicate (H i p y : nat) : Prop :=
  exists seq A, length seq = p /\ proof_cert H i seq A /\ y = code_formula A.

Theorem proof_mp_combines :
  forall H i p q A B,
    proof_cert H i p (FImp A B) ->
    proof_cert H i q A ->
    proof_cert H i (mp_sequence p q B) B.
Proof.
  intros H i p q A B Hp Hq.
  exact (ProofMP H i p q A B Hp Hq).
Qed.

Theorem proof_up_combines :
  forall H i p A,
    S i <= H ->
    proof_cert H i p A ->
    proof_cert H (S i) (p ++ [prT_formula i A]) (prT_formula i A).
Proof.
  intros H i p A Hi Hp.
  exact (ProofUp H i p A Hi Hp).
Qed.

Inductive standard_atom_value : formula -> bool -> Prop :=
| StdEqNum :
    forall a b,
      standard_atom_value (FEq (TNum a) (TNum b)) (Nat.eqb a b)
| StdEqStr :
    forall xs ys,
      standard_atom_value (FEq (TStr xs) (TStr ys)) (bool_list_eqb xs ys)
| StdLeNum :
    forall a b,
      standard_atom_value (FRel RLe [TNum a; TNum b]) (Nat.leb a b)
| StdMem :
    forall k bs,
      standard_atom_value (FRel RMem [TNum k; TStr bs]) (nth k bs false).

Definition complete_nat_enumeration (bound : nat) (values : list nat) : Prop :=
  Forall (fun m => m <= bound) values /\
  forall m, m <= bound -> In m values.

Definition complete_string_enumeration
    (bound : nat) (values : list (list bool)) : Prop :=
  Forall (fun bs => length bs <= bound) values /\
  forall bs, length bs <= bound -> In bs values.

Inductive ev_tree (H i : nat) : formula -> bool -> Type :=
| EvAtom :
    forall A b,
      decsent H i A ->
      is_atomic_formula A ->
      standard_atom_value A b ->
      ev_tree H i A b
| EvNeg :
    forall A b,
      ev_tree H i A b ->
      ev_tree H i (FNeg A) (negb b)
| EvAnd :
    forall A B a b,
      ev_tree H i A a ->
      ev_tree H i B b ->
      ev_tree H i (FAnd A B) (andb a b)
| EvOr :
    forall A B a b,
      ev_tree H i A a ->
      ev_tree H i B b ->
      ev_tree H i (FOr A B) (orb a b)
| EvImp :
    forall A B a b,
      ev_tree H i A a ->
      ev_tree H i B b ->
      ev_tree H i (FImp A B) (orb (negb a) b)
| EvAllNTrue :
    forall x t body bound values,
      var_sort x = SortN ->
      nat_term_value t bound ->
      complete_nat_enumeration bound values ->
      Forall
        (fun m => ev_tree H i (subst_formula body x (TNum m)) true)
        values ->
      ev_tree H i (FAll x (FImp (leq_formula x t) body)) true
| EvAllNFalse :
    forall x t body bound values m,
      var_sort x = SortN ->
      nat_term_value t bound ->
      complete_nat_enumeration bound values ->
      In m values ->
      ev_tree H i (subst_formula body x (TNum m)) false ->
      ev_tree H i (FAll x (FImp (leq_formula x t) body)) false
| EvExNTrue :
    forall x t body bound values m,
      var_sort x = SortN ->
      nat_term_value t bound ->
      complete_nat_enumeration bound values ->
      In m values ->
      ev_tree H i (subst_formula body x (TNum m)) true ->
      ev_tree H i (FEx x (FAnd (leq_formula x t) body)) true
| EvExNFalse :
    forall x t body bound values,
      var_sort x = SortN ->
      nat_term_value t bound ->
      complete_nat_enumeration bound values ->
      Forall
        (fun m => ev_tree H i (subst_formula body x (TNum m)) false)
        values ->
      ev_tree H i (FEx x (FAnd (leq_formula x t) body)) false
| EvAllSTrue :
    forall X t body bound values,
      var_sort X = SortS ->
      nat_term_value t bound ->
      complete_string_enumeration bound values ->
      Forall
        (fun bs => ev_tree H i (subst_formula body X (TStr bs)) true)
        values ->
      ev_tree H i (FAll X (FImp (strlen_leq_formula X t) body)) true
| EvAllSFalse :
    forall X t body bound values bs,
      var_sort X = SortS ->
      nat_term_value t bound ->
      complete_string_enumeration bound values ->
      In bs values ->
      ev_tree H i (subst_formula body X (TStr bs)) false ->
      ev_tree H i (FAll X (FImp (strlen_leq_formula X t) body)) false
| EvExSTrue :
    forall X t body bound values bs,
      var_sort X = SortS ->
      nat_term_value t bound ->
      complete_string_enumeration bound values ->
      In bs values ->
      ev_tree H i (subst_formula body X (TStr bs)) true ->
      ev_tree H i (FEx X (FAnd (strlen_leq_formula X t) body)) true
| EvExSFalse :
    forall X t body bound values,
      var_sort X = SortS ->
      nat_term_value t bound ->
      complete_string_enumeration bound values ->
      Forall
        (fun bs => ev_tree H i (subst_formula body X (TStr bs)) false)
        values ->
      ev_tree H i (FEx X (FAnd (strlen_leq_formula X t) body)) false.

Definition ev_accept (H i : nat) (A : formula) : Prop :=
  ev_tree H i A true.

Definition ev_tree_predicate (H i e y : nat) : Prop :=
  exists A, ev_accept H i A /\ e = code_formula A /\ y = code_formula A.

Record standard_model (H : nat) : Type := {
  standard_holds : nat -> formula -> Prop;
  standard_ax_hat_exact :
    forall i A,
      S i <= H ->
      (standard_holds (S i) (axHat_formula i A) <->
        theory_axiom H i A);
  standard_ev_tree_hat_exact :
    forall i e A,
      S i <= H ->
      (standard_holds (S i) (evTreeHat_formula i e A) <->
        ev_tree_predicate H i e (code_formula A));
  standard_certT_exact :
    forall i p A,
      S i <= H ->
      (standard_holds (S i) (certT_formula i p A) <->
        proof_predicate H i p (code_formula A));
  standard_prT_exact :
    forall i A,
      S i <= H ->
      (standard_holds (S i) (prT_formula i A) <->
        exists p, proof_predicate H i p (code_formula A));
  standard_certEv_exact :
    forall k e A,
      1 <= k ->
      k <= H ->
      (standard_holds k (certEv_formula k e A) <->
        ev_tree_predicate H (pred k) e (code_formula A));
  standard_prEv_exact :
    forall k A,
      1 <= k ->
      k <= H ->
      (standard_holds k (prEv_formula k A) <->
        exists e, ev_tree_predicate H (pred k) e (code_formula A));
  standard_theory_sound :
    forall n A, n <= H -> theory_axiom H n A -> standard_holds n A;
  standard_proof_sound :
    forall n p A, proof_cert H n p A -> standard_holds n A;
  standard_eval_correct :
    forall i A, ev_accept H i A -> standard_holds i A;
  standard_consistent :
    forall n A, ~ (standard_holds n A /\ standard_holds n (FNeg A))
}.

Definition model_satisfies_theory (H n : nat) (M : standard_model H) : Prop :=
  forall A, theory_axiom H n A -> standard_holds H M n A.

Theorem standard_correctness :
  forall H n (M : standard_model H),
    n <= H ->
    model_satisfies_theory H n M.
Proof.
  intros H n M Hn A HA.
  exact (standard_theory_sound H M n A Hn HA).
Qed.

Theorem theory_consistency_from_standard_model :
  forall H n (M : standard_model H),
    n <= H ->
    ~ exists A p q,
      proof_cert H n p A /\
      proof_cert H n q (FNeg A).
Proof.
  intros H n M _ [A [p [q [Hp Hq]]]].
  pose proof (standard_proof_sound H M n p A Hp) as HA.
  pose proof (standard_proof_sound H M n q (FNeg A) Hq) as HnA.
  exact (standard_consistent H M n A (conj HA HnA)).
Qed.

Definition proves_formula (H i : nat) (A : formula) : Prop :=
  exists p, proof_cert H i p A.

Definition proves_eval (H i : nat) (A : formula) : Prop :=
  ev_tree H i A true.

Theorem hbl_necessitation :
  forall H i A,
    i < H ->
    bsent H i A ->
    proves_formula H i A ->
    proves_formula H (S i) (prT_formula i A).
Proof.
  intros H i A Hi _ [p Hp].
  exists (p ++ [prT_formula i A]).
  apply ProofUp; [lia|exact Hp].
Qed.

Theorem hbl_distribution :
  forall H i A B,
    i < H ->
    bsent H i A ->
    bsent H i B ->
    proves_formula H (S i)
      (FImp
        (prT_formula i (FImp A B))
        (FImp (prT_formula i A) (prT_formula i B))).
Proof.
  intros H i A B Hi HA HB.
  exists [FImp (prT_formula i (FImp A B))
          (FImp (prT_formula i A) (prT_formula i B))].
  apply ProofLine.
  - lia.
  - apply LineTheory.
    apply TheoryProofMp; try lia; assumption.
Qed.

Theorem hbl_positive_introspection :
  forall H i A,
    S i < H ->
    bsent H i A ->
    proves_formula H (S (S i))
      (FImp
        (prT_formula i A)
        (prT_formula (S i) (prT_formula i A))).
Proof.
  intros H i A Hi HA.
  exists [FImp (prT_formula i A) (prT_formula (S i) (prT_formula i A))].
  apply ProofLine.
  - lia.
  - apply LineTheory.
    apply TheoryProofUp; try lia; exact HA.
Qed.

Record TPV_system (H : nat) : Type := {
  tpv_formula_carrier : Type;
  tpv_level : nat -> Prop := in_height H;
  tpv_lower_level : nat -> Prop := fun i => i < H;
  tpv_func_signature : nat -> func_symbol -> Prop := func_in_signature H;
  tpv_rel_signature : nat -> rel_symbol -> Prop := rel_in_signature H;
  tpv_term : nat -> term -> sort -> Prop := term_wf H;
  tpv_formula : nat -> formula -> Prop := formula_wf H;
  tpv_bform : nat -> formula -> Prop := bform H;
  tpv_bsent : nat -> formula -> Prop := bsent H;
  tpv_decsent : nat -> formula -> Prop := decsent H;
  tpv_fv_term : term -> list var := fv_term;
  tpv_fv_formula : formula -> list var := fv_formula;
  tpv_sub_term : term -> var -> term -> term := subst_term;
  tpv_sub_formula : formula -> var -> term -> formula := subst_formula;
  tpv_alpha : formula -> formula -> Prop := alpha_equiv;
  tpv_theory : nat -> formula -> Prop := theory_axiom H;
  tpv_proof : nat -> list formula -> formula -> Prop := proof_cert H;
  tpv_ev_tree : nat -> formula -> bool -> Type := ev_tree H;
  tpv_no_self_truth :
    forall i, i <= H -> ~ rel_in_signature H i (RSat i);
  tpv_truth_next :
    forall i, S i <= H -> rel_in_signature H (S i) (RSat i);
  tpv_hbl_necessitation :
    forall i A,
      i < H ->
      bsent H i A ->
      proves_formula H i A ->
      proves_formula H (S i) (prT_formula i A);
  tpv_hbl_distribution :
    forall i A B,
      i < H ->
      bsent H i A ->
      bsent H i B ->
      proves_formula H (S i)
        (FImp
          (prT_formula i (FImp A B))
          (FImp (prT_formula i A) (prT_formula i B)));
  tpv_hbl_positive :
    forall i A,
      S i < H ->
      bsent H i A ->
      proves_formula H (S (S i))
        (FImp
          (prT_formula i A)
          (prT_formula (S i) (prT_formula i A)))
}.

Definition build_TPV_system (H : nat) : TPV_system H := {|
  tpv_formula_carrier := formula;
  tpv_no_self_truth := sat_not_in_own_layer H;
  tpv_truth_next :=
    fun i Hi => proj1 (truth_proof_symbols_enter_next_layer H i Hi);
  tpv_hbl_necessitation := hbl_necessitation H;
  tpv_hbl_distribution := hbl_distribution H;
  tpv_hbl_positive := hbl_positive_introspection H
|}.

End FiniteStratifiedTPV1081.
