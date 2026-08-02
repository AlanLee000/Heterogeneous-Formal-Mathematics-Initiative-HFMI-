From Coq Require Import Lists.List Arith.PeanoNat Lia.
From Coq Require Import Logic.Classical Logic.ClassicalEpsilon.
From Coq Require Import Logic.ClassicalDescription.
From Coq Require Import Logic.ConstructiveEpsilon.

Import ListNotations.

(** * Theory Differentiation Consistency Logic (TDB)

    Faithful Rocq formalization of source note 1146.  Object-language syntax is
    represented structurally; natural numbers still index r.e. theories. *)

Module TheoryDifferentiationConsistencyLogic1146.

(** ** 1. Fixed syntax and coding interface *)

Inductive obj_term : Type :=
| TVar : nat -> obj_term
| TConst : nat -> obj_term
| TFun : nat -> nat -> term_args -> obj_term
with term_args : Type :=
| ANil : term_args
| ACons : obj_term -> term_args -> term_args.

Inductive formula : Type :=
| FEq : obj_term -> obj_term -> formula
| FRel : nat -> nat -> term_args -> formula
| FMarkMw : nat -> formula
| FMarkBr : nat -> formula
| FMarkSeal : nat -> formula
| FNeg : formula -> formula
| FAnd : formula -> formula -> formula
| FEx : nat -> formula -> formula.

Fixpoint args_length (args : term_args) : nat :=
  match args with
  | ANil => 0
  | ACons _ rest => S (args_length rest)
  end.

Fixpoint well_term (t : obj_term) : Prop :=
  match t with
  | TVar _ | TConst _ => True
  | TFun _ k args => args_length args = k /\ well_args args
  end
with well_args (args : term_args) : Prop :=
  match args with
  | ANil => True
  | ACons t rest => well_term t /\ well_args rest
  end.

Fixpoint well_formula (f : formula) : Prop :=
  match f with
  | FEq s t => well_term s /\ well_term t
  | FRel _ k args => args_length args = k /\ well_args args
  | FMarkMw _ | FMarkBr _ | FMarkSeal _ => True
  | FNeg a => well_formula a
  | FAnd a b => well_formula a /\ well_formula b
  | FEx _ a => well_formula a
  end.

Fixpoint vars_term (t : obj_term) : list nat :=
  match t with
  | TVar x => [x]
  | TConst _ => []
  | TFun _ _ args => vars_args args
  end
with vars_args (args : term_args) : list nat :=
  match args with
  | ANil => []
  | ACons t rest => vars_term t ++ vars_args rest
  end.

Fixpoint free_vars (f : formula) : list nat :=
  match f with
  | FEq s t => vars_term s ++ vars_term t
  | FRel _ _ args => vars_args args
  | FMarkMw _ | FMarkBr _ | FMarkSeal _ => []
  | FNeg a => free_vars a
  | FAnd a b => free_vars a ++ free_vars b
  | FEx x a => remove Nat.eq_dec x (free_vars a)
  end.

Definition Sentence (f : formula) : Prop :=
  well_formula f /\ free_vars f = [].

Definition Imp (a b : formula) : formula :=
  FNeg (FAnd a (FNeg b)).

Definition Or (a b : formula) : formula :=
  FNeg (FAnd (FNeg a) (FNeg b)).

Definition All (x : nat) (a : formula) : formula :=
  FNeg (FEx x (FNeg a)).

Definition Top : formula := FEq (TConst 0) (TConst 0).
Definition Bot : formula := FAnd Top (FNeg Top).

Definition cantor_pair (x y : nat) : nat :=
  ((x + y) * (x + y + 1)) / 2 + y.

Definition IsMark (f : formula) : Prop :=
  (exists n, f = FMarkMw n) \/
  (exists n, f = FMarkBr n) \/
  (exists n, f = FMarkSeal n).

Inductive nonlogical_symbol : Type :=
| SRel : nat -> nat -> nonlogical_symbol
| SFun : nat -> nat -> nonlogical_symbol
| SConst : nat -> nonlogical_symbol
| SMarkMw : nat -> nonlogical_symbol
| SMarkBr : nat -> nonlogical_symbol
| SMarkSeal : nat -> nonlogical_symbol.

Fixpoint symbol_in_term (s : nonlogical_symbol) (t : obj_term) : Prop :=
  match t with
  | TVar _ => False
  | TConst n => s = SConst n
  | TFun n k args => s = SFun n k \/ symbol_in_args s args
  end
with symbol_in_args (s : nonlogical_symbol) (args : term_args) : Prop :=
  match args with
  | ANil => False
  | ACons t rest => symbol_in_term s t \/ symbol_in_args s rest
  end.

Fixpoint symbol_in_formula (s : nonlogical_symbol) (f : formula) : Prop :=
  match f with
  | FEq a b => symbol_in_term s a \/ symbol_in_term s b
  | FRel n k args => s = SRel n k \/ symbol_in_args s args
  | FMarkMw n => s = SMarkMw n
  | FMarkBr n => s = SMarkBr n
  | FMarkSeal n => s = SMarkSeal n
  | FNeg a => symbol_in_formula s a
  | FAnd a b => symbol_in_formula s a \/ symbol_in_formula s b
  | FEx _ a => symbol_in_formula s a
  end.

Record FixedCoding : Type := {
  enumerate : nat -> nat -> option formula;
  logical_axiom : formula -> Prop;
  quantifier_rule : formula -> formula -> Prop;
  equality_axiom : formula -> Prop;

  delta_schema : nat -> nat -> formula;
  epsilon_schema : nat -> nat -> nat -> formula;
  rho_schema : nat -> nat -> nat -> list nat -> formula;
  phi_schema : nat -> nat -> nat -> list nat -> nat -> formula;
  gamma_schema : nat -> nat -> nat -> formula
}.

Definition Theory (E : FixedCoding) (e : nat) (f : formula) : Prop :=
  Sentence f /\ exists stage, enumerate E e stage = Some f.

Definition TheoryEq (E : FixedCoding) (e f : nat) : Prop :=
  forall x, Theory E e x <-> Theory E f x.

Definition TheoryExt (E : FixedCoding) (e : nat)
    (P : formula -> Prop) : Prop :=
  forall x, Theory E e x <-> P x.

Definition CoreSet (E : FixedCoding) (e : nat) (x : formula) : Prop :=
  Theory E e x /\ ~ IsMark x.

Definition Reg (E : FixedCoding) (e d : nat) : Prop :=
  Theory E e (FMarkSeal d).

Definition RegUnion (E : FixedCoding) (X : list nat) (d : nat) : Prop :=
  exists e, In e X /\ Reg E e d.

Definition RegTheory (E : FixedCoding) (X : list nat)
    (x : formula) : Prop :=
  exists d, RegUnion E X d /\ x = FMarkSeal d.

(** Natural-number minimization is used only after an explicit existence proof. *)
Definition least_nat_certificate (P : nat -> Prop)
    (Hex : exists n, P n) :
    {n : nat | P n /\ forall k, P k -> n <= k} :=
  epsilon_smallest P
    (fun n => excluded_middle_informative (P n)) Hex.

Definition least_nat (P : nat -> Prop) (Hex : exists n, P n) : nat :=
  proj1_sig (least_nat_certificate P Hex).

Lemma least_nat_spec :
  forall (P : nat -> Prop) (Hex : exists n, P n),
    P (least_nat P Hex).
Proof.
  intros P Hex.
  unfold least_nat.
  exact (proj1 (proj2_sig (least_nat_certificate P Hex))).
Qed.

Lemma least_nat_minimal :
  forall (P : nat -> Prop) (Hex : exists n, P n) n,
    P n -> least_nat P Hex <= n.
Proof.
  intros P Hex n Hn.
  unfold least_nat.
  exact (proj2 (proj2_sig (least_nat_certificate P Hex)) n Hn).
Qed.

(** ** 2. Hilbert proof predicate *)

Definition ProofLine (E : FixedCoding) (e : nat)
    (p : list formula) (i : nat) (psi : formula) : Prop :=
  logical_axiom E psi \/
  (exists j k antecedent,
      j < i /\ k < i /\
      nth_error p j = Some antecedent /\
      nth_error p k = Some (Imp antecedent psi)) \/
  (exists j premise,
      j < i /\ nth_error p j = Some premise /\
      quantifier_rule E premise psi) \/
  Theory E e psi \/
  equality_axiom E psi.

Definition Prf (E : FixedCoding) (e : nat) (phi : formula)
    (p : list formula) : Prop :=
  exists m,
    length p = S m /\
    nth_error p m = Some phi /\
    forall i psi, nth_error p i = Some psi -> ProofLine E e p i psi.

Definition Derives (E : FixedCoding) (e : nat) (phi : formula) : Prop :=
  exists p, Prf E e phi p.

Definition Con (E : FixedCoding) (e : nat) : Prop :=
  ~ Derives E e Bot.

(** ** 3. Effective index closures, cores, registers, and minima *)

Definition FailSet (E : FixedCoding) (X : list nat) (m x : formula) : Prop :=
  Sentence x /\ (x = Bot \/ x = m \/ RegTheory E X x).

Definition MwSuccessSet (E : FixedCoding) (u : nat) (X : list nat)
    (m x : formula) : Prop :=
  Sentence x /\ (Theory E u x \/ RegTheory E X x \/ x = m).

Definition BrSuccessSet (E : FixedCoding) (a b : nat) (X : list nat)
    (m x : formula) : Prop :=
  Sentence x /\
  (CoreSet E a x \/ CoreSet E b x \/ RegTheory E X x \/ x = m).

Definition SealSet (E : FixedCoding) (a : nat) (X : list nat)
    (m x : formula) : Prop :=
  Sentence x /\ (CoreSet E a x \/ RegTheory E X x \/ x = m).

Record IndexClosure (E : FixedCoding) : Type := {
  core_index_exists : forall e,
      exists d, TheoryExt E d (CoreSet E e);
  register_index_exists : forall X,
      exists d, TheoryExt E d (RegTheory E X);
  fail_index_exists : forall X m,
      exists d, TheoryExt E d (FailSet E X m);
  mw_success_index_exists : forall u X m,
      exists d, TheoryExt E d (MwSuccessSet E u X m);
  br_success_index_exists : forall a b X m,
      exists d, TheoryExt E d (BrSuccessSet E a b X m);
  seal_index_exists : forall a X m,
      exists d, TheoryExt E d (SealSet E a X m);
  union_index : nat -> nat -> nat;
  union_index_spec : forall a b x,
      Theory E (union_index a b) x <-> Theory E a x \/ Theory E b x
}.

Definition least_index (E : FixedCoding) (P : formula -> Prop)
    (Hex : exists d, TheoryExt E d P) : nat :=
  least_nat (fun d => TheoryExt E d P) Hex.

Lemma least_index_spec :
  forall (E : FixedCoding) (P : formula -> Prop)
      (Hex : exists d, TheoryExt E d P),
    TheoryExt E (least_index E P Hex) P.
Proof.
  intros E P Hex.
  unfold least_index.
  apply least_nat_spec.
Qed.

Lemma least_index_minimal :
  forall (E : FixedCoding) (P : formula -> Prop)
      (Hex : exists d, TheoryExt E d P) d,
    TheoryExt E d P -> least_index E P Hex <= d.
Proof.
  intros E P Hex d Hd.
  unfold least_index.
  apply least_nat_minimal.
  exact Hd.
Qed.

Definition kappa (E : FixedCoding) (C : IndexClosure E) (e : nat) : nat :=
  least_index E (CoreSet E e) (core_index_exists E C e).

Lemma kappa_spec :
  forall (E : FixedCoding) (C : IndexClosure E) e,
    TheoryExt E (kappa E C e) (CoreSet E e).
Proof.
  intros E C e.
  apply least_index_spec.
Qed.

Lemma kappa_minimal :
  forall (E : FixedCoding) (C : IndexClosure E) e d,
    TheoryExt E d (CoreSet E e) -> kappa E C e <= d.
Proof.
  intros E C e d Hd.
  apply least_index_minimal.
  exact Hd.
Qed.

Definition RegCode (E : FixedCoding) (C : IndexClosure E)
    (X : list nat) : nat :=
  least_index E (RegTheory E X) (register_index_exists E C X).

Lemma RegCode_spec :
  forall (E : FixedCoding) (C : IndexClosure E) X,
    TheoryExt E (RegCode E C X) (RegTheory E X).
Proof.
  intros E C X.
  apply least_index_spec.
Qed.

Definition Blocked (E : FixedCoding) (C : IndexClosure E)
    (X : list nat) (e : nat) : Prop :=
  RegUnion E X (kappa E C e).

Definition theory_union (E : FixedCoding) (C : IndexClosure E)
    (a b : nat) : nat := union_index E C a b.

(** ** 4. Interpretation codes and capture-avoiding translation *)

Fixpoint max_var_term (t : obj_term) : nat :=
  match t with
  | TVar x => x
  | TConst _ => 0
  | TFun _ _ args => max_var_args args
  end
with max_var_args (args : term_args) : nat :=
  match args with
  | ANil => 0
  | ACons t rest => Nat.max (max_var_term t) (max_var_args rest)
  end.

Fixpoint max_var_formula (f : formula) : nat :=
  match f with
  | FEq s t => Nat.max (max_var_term s) (max_var_term t)
  | FRel _ _ args => max_var_args args
  | FMarkMw _ | FMarkBr _ | FMarkSeal _ => 0
  | FNeg a => max_var_formula a
  | FAnd a b => Nat.max (max_var_formula a) (max_var_formula b)
  | FEx x a => Nat.max x (max_var_formula a)
  end.

Fixpoint all_vars_formula (f : formula) : list nat :=
  match f with
  | FEq s t => vars_term s ++ vars_term t
  | FRel _ _ args => vars_args args
  | FMarkMw _ | FMarkBr _ | FMarkSeal _ => []
  | FNeg a => all_vars_formula a
  | FAnd a b => all_vars_formula a ++ all_vars_formula b
  | FEx x a => x :: all_vars_formula a
  end.

Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: rest => Nat.max x (max_list rest)
  end.

Lemma in_max_list_le :
  forall xs x, In x xs -> x <= max_list xs.
Proof.
  intros xs.
  induction xs as [| y rest IH].
  - intros x Hin. contradiction.
  - intros x Hin. cbn.
    destruct Hin as [Heq | Hin].
    + subst x. apply Nat.le_max_l.
    + apply Nat.le_trans with (m := max_list rest).
      * apply IH. exact Hin.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_exists :
  forall used : list nat, exists n, ~ In n used.
Proof.
  intro used.
  exists (S (max_list used)).
  intro Hin.
  pose proof (in_max_list_le used (S (max_list used)) Hin).
  lia.
Qed.

Definition fresh (used : list nat) : nat :=
  least_nat (fun n => ~ In n used) (fresh_exists used).

Lemma fresh_not_in :
  forall used : list nat, ~ In (fresh used) used.
Proof.
  intro used.
  unfold fresh.
  apply least_nat_spec.
Qed.

Lemma fresh_minimal :
  forall (used : list nat) n, ~ In n used -> fresh used <= n.
Proof.
  intros used n Hnotin.
  unfold fresh.
  apply least_nat_minimal.
  exact Hnotin.
Qed.

Fixpoint freshes (used : list nat) (count : nat) : list nat :=
  match count with
  | 0 => []
  | S count' =>
      let z := fresh used in z :: freshes (z :: used) count'
  end.

Fixpoint exists_many (xs : list nat) (body : formula) : formula :=
  match xs with
  | [] => body
  | x :: rest => FEx x (exists_many rest body)
  end.

Fixpoint all_many (xs : list nat) (body : formula) : formula :=
  match xs with
  | [] => body
  | x :: rest => All x (all_many rest body)
  end.

Fixpoint trm (E : FixedCoding) (q : nat) (used : list nat)
    (t : obj_term) (z : nat) : formula :=
  match t with
  | TVar x => epsilon_schema E q z x
  | TConst n => gamma_schema E q n z
  | TFun n k args =>
      let zs := freshes (z :: used ++ vars_term t) (args_length args) in
      exists_many zs
        (trm_args E q (zs ++ z :: used) args zs
          (phi_schema E q n k zs z))
  end
with trm_args (E : FixedCoding) (q : nat) (used : list nat)
    (args : term_args) (zs : list nat) (tail : formula) : formula :=
  match args, zs with
  | ANil, _ => tail
  | ACons t rest, z :: zs' =>
      FAnd (trm E q used t z)
        (trm_args E q used rest zs' tail)
  | ACons _ _, [] => tail
  end.

Fixpoint tau_from (E : FixedCoding) (q : nat) (used : list nat)
    (theta : formula) : formula :=
  match theta with
  | FEq s t =>
      let zs := freshes used 2 in
      match zs with
      | [z0; z1] =>
          exists_many zs
            (FAnd (trm E q (zs ++ used) s z0)
              (FAnd (trm E q (zs ++ used) t z1)
                (epsilon_schema E q z0 z1)))
      | _ => theta
      end
  | FRel n k args =>
      let zs := freshes used (args_length args) in
      exists_many zs
        (trm_args E q (zs ++ used) args zs
          (rho_schema E q n k zs))
  | FMarkMw n => FMarkMw n
  | FMarkBr n => FMarkBr n
  | FMarkSeal n => FMarkSeal n
  | FNeg a => FNeg (tau_from E q used a)
  | FAnd a b => FAnd (tau_from E q used a) (tau_from E q used b)
  | FEx x a => FEx x (FAnd (delta_schema E q x) (tau_from E q used a))
  end.

Definition tau (E : FixedCoding) (q : nat) (theta : formula) : formula :=
  tau_from E q (all_vars_formula theta) theta.

Fixpoint schema_symbol_in_term (E : FixedCoding) (q : nat)
    (t : obj_term) (s : nonlogical_symbol) : Prop :=
  match t with
  | TVar _ => symbol_in_formula s (epsilon_schema E q 0 1)
  | TConst n => symbol_in_formula s (gamma_schema E q n 0)
  | TFun n k args =>
      symbol_in_formula s (phi_schema E q n k (seq 0 k) k) \/
      schema_symbol_in_args E q args s
  end
with schema_symbol_in_args (E : FixedCoding) (q : nat)
    (args : term_args) (s : nonlogical_symbol) : Prop :=
  match args with
  | ANil => False
  | ACons t rest =>
      schema_symbol_in_term E q t s \/
      schema_symbol_in_args E q rest s
  end.

Fixpoint schema_symbol_in_formula (E : FixedCoding) (q : nat)
    (f : formula) (s : nonlogical_symbol) : Prop :=
  match f with
  | FEq a b =>
      symbol_in_formula s (epsilon_schema E q 0 1) \/
      schema_symbol_in_term E q a s \/ schema_symbol_in_term E q b s
  | FRel n k args =>
      symbol_in_formula s (rho_schema E q n k (seq 0 k)) \/
      schema_symbol_in_args E q args s
  | FMarkMw _ | FMarkBr _ | FMarkSeal _ => False
  | FNeg a => schema_symbol_in_formula E q a s
  | FAnd a b =>
      schema_symbol_in_formula E q a s \/
      schema_symbol_in_formula E q b s
  | FEx x a =>
      symbol_in_formula s (delta_schema E q x) \/
      schema_symbol_in_formula E q a s
  end.

Definition Uses (E : FixedCoding) (q a b : nat) : Prop :=
  forall theta s,
    CoreSet E b theta ->
    schema_symbol_in_formula E q theta s ->
    exists y, CoreSet E a y /\ symbol_in_formula s y.

(** ** 5. Correct interpretations and the minimal model-witness core *)

Definition SymOcc (E : FixedCoding) (s : nonlogical_symbol) (b : nat) : Prop :=
  exists x, CoreSet E b x /\ symbol_in_formula s x.

Definition big_conj (fs : list formula) : formula :=
  match fs with
  | [] => Top
  | f :: rest => fold_left FAnd rest f
  end.

Definition domain_nonempty_sentence (E : FixedCoding) (q : nat) : formula :=
  FEx 0 (delta_schema E q 0).

Definition equality_reflexive_sentence (E : FixedCoding) (q : nat) : formula :=
  All 0 (Imp (delta_schema E q 0) (epsilon_schema E q 0 0)).

Definition equality_typed_sentence (E : FixedCoding) (q : nat) : formula :=
  all_many [0; 1]
    (Imp (epsilon_schema E q 0 1)
      (FAnd (delta_schema E q 0) (delta_schema E q 1))).

Definition equality_symmetric_sentence (E : FixedCoding) (q : nat) : formula :=
  all_many [0; 1]
    (Imp (epsilon_schema E q 0 1) (epsilon_schema E q 1 0)).

Definition equality_transitive_sentence (E : FixedCoding) (q : nat) : formula :=
  all_many [0; 1; 2]
    (Imp (FAnd (epsilon_schema E q 0 1) (epsilon_schema E q 1 2))
      (epsilon_schema E q 0 2)).

Definition constant_exists_sentence (E : FixedCoding) (q n : nat) : formula :=
  FEx 0 (FAnd (delta_schema E q 0) (gamma_schema E q n 0)).

Definition constant_unique_sentence (E : FixedCoding) (q n : nat) : formula :=
  all_many [0; 1]
    (Imp (big_conj
      [delta_schema E q 0; delta_schema E q 1;
       gamma_schema E q n 0; gamma_schema E q n 1])
      (epsilon_schema E q 0 1)).

Definition deltas (E : FixedCoding) (q : nat) (zs : list nat) : list formula :=
  map (delta_schema E q) zs.

Definition epsilon_input_triplets (E : FixedCoding) (q : nat)
    (zs zs' : list nat) : list formula :=
  map (fun zz =>
    let '(z, z') := zz in
    big_conj [delta_schema E q z; delta_schema E q z';
              epsilon_schema E q z z']) (combine zs zs').

Definition function_total_sentence (E : FixedCoding) (q n k : nat) : formula :=
  let zs := seq 0 k in
  let y := k in
  all_many zs
    (Imp (big_conj (deltas E q zs))
      (FEx y (FAnd (delta_schema E q y)
        (phi_schema E q n k zs y)))).

Definition function_unique_sentence (E : FixedCoding) (q n k : nat) : formula :=
  let zs := seq 0 k in
  let y := k in
  let y' := S k in
  all_many (zs ++ [y; y'])
    (Imp (big_conj
      (deltas E q zs ++
       [delta_schema E q y; delta_schema E q y';
        phi_schema E q n k zs y; phi_schema E q n k zs y']))
      (epsilon_schema E q y y')).

Definition function_compatible_sentence (E : FixedCoding)
    (q n k : nat) : formula :=
  let zs := seq 0 k in
  let zs' := seq k k in
  let y := 2 * k in
  let y' := S (2 * k) in
  all_many (zs ++ zs' ++ [y; y'])
    (Imp (big_conj
      (epsilon_input_triplets E q zs zs' ++
       [phi_schema E q n k zs y; phi_schema E q n k zs' y']))
      (epsilon_schema E q y y')).

Definition relation_compatible_sentence (E : FixedCoding)
    (q n k : nat) : formula :=
  let zs := seq 0 k in
  let zs' := seq k k in
  all_many (zs ++ zs')
    (Imp (big_conj
      (epsilon_input_triplets E q zs zs' ++
       [rho_schema E q n k zs]))
      (rho_schema E q n k zs')).

Definition Int (E : FixedCoding) (u a b q : nat) : Prop :=
  (forall x, Theory E u x -> CoreSet E a x) /\
  Uses E q a b /\
  Derives E u (domain_nonempty_sentence E q) /\
  Derives E u (equality_reflexive_sentence E q) /\
  Derives E u (equality_typed_sentence E q) /\
  Derives E u (equality_symmetric_sentence E q) /\
  Derives E u (equality_transitive_sentence E q) /\
  (forall n, SymOcc E (SConst n) b ->
      Derives E u (constant_exists_sentence E q n) /\
      Derives E u (constant_unique_sentence E q n)) /\
  (forall n k, SymOcc E (SFun n k) b ->
      Derives E u (function_total_sentence E q n k) /\
      Derives E u (function_unique_sentence E q n k) /\
      Derives E u (function_compatible_sentence E q n k)) /\
  (forall n k, SymOcc E (SRel n k) b ->
      Derives E u (relation_compatible_sentence E q n k)) /\
  (forall x, CoreSet E b x -> Derives E u (tau E q x)).

Definition CandidateMw (E : FixedCoding) (C : IndexClosure E)
    (u a b : nat) : Prop :=
  Con E (kappa E C u) /\
  (forall x, Theory E u x -> CoreSet E a x) /\
  exists q, Int E u a b q.

Definition mu_mw (E : FixedCoding) (C : IndexClosure E)
    (a b : nat) : option nat :=
  match excluded_middle_informative
    (exists u, CandidateMw E C u a b) with
  | left Hex =>
      Some (least_nat (fun u => CandidateMw E C u a b) Hex)
  | right _ => None
  end.

Lemma mu_mw_some_spec :
  forall (E : FixedCoding) (C : IndexClosure E) a b u,
    mu_mw E C a b = Some u -> CandidateMw E C u a b.
Proof.
  intros E C a b u Hmu.
  unfold mu_mw in Hmu.
  destruct (excluded_middle_informative
    (exists u0, CandidateMw E C u0 a b)) as [Hex | Hnone].
  - inversion Hmu; subst u.
    apply least_nat_spec.
  - discriminate Hmu.
Qed.

Lemma mu_mw_defined_iff :
  forall (E : FixedCoding) (C : IndexClosure E) a b,
    (exists u, mu_mw E C a b = Some u) <->
    (exists u, CandidateMw E C u a b).
Proof.
  intros E C a b.
  split.
  - intros [u Hmu].
    exists u.
    apply (mu_mw_some_spec E C a b u Hmu).
  - intro Hex.
    unfold mu_mw.
    destruct (excluded_middle_informative
      (exists u, CandidateMw E C u a b)) as [Hex' | Hnone].
    + eexists; reflexivity.
    + contradiction.
Qed.

Lemma mu_mw_none_iff :
  forall (E : FixedCoding) (C : IndexClosure E) a b,
    mu_mw E C a b = None <->
    ~ exists u, CandidateMw E C u a b.
Proof.
  intros E C a b.
  unfold mu_mw.
  destruct (excluded_middle_informative
    (exists u, CandidateMw E C u a b)) as [Hex | Hnone].
  - split; intro H.
    + discriminate H.
    + contradiction.
  - split; intro H.
    + exact Hnone.
    + reflexivity.
Qed.

(** ** 6. Finite refutation and branch compatibility *)

Definition FinAx (E : FixedCoding) (s : list formula) (b : nat) : Prop :=
  Forall (CoreSet E b) s.

Definition Refutes (E : FixedCoding) (C : IndexClosure E)
    (a b : nat) : Prop :=
  exists s,
    s <> [] /\ FinAx E s b /\
    Derives E (kappa E C a) (FNeg (big_conj s)).

Definition Compatible (E : FixedCoding) (C : IndexClosure E)
    (a b : nat) : Prop :=
  Con E (theory_union E C (kappa E C a) (kappa E C b)).

Definition BranchOK (E : FixedCoding) (C : IndexClosure E)
    (a b : nat) : Prop :=
  Compatible E C a b /\ ~ Refutes E C a b.

(** ** 7. The three total operators *)

Definition Fail (E : FixedCoding) (C : IndexClosure E)
    (X : list nat) (m : formula) : nat :=
  least_index E (FailSet E X m) (fail_index_exists E C X m).

Definition MwSuccessCode (E : FixedCoding) (C : IndexClosure E)
    (u : nat) (X : list nat) (m : formula) : nat :=
  least_index E (MwSuccessSet E u X m)
    (mw_success_index_exists E C u X m).

Definition BrSuccessCode (E : FixedCoding) (C : IndexClosure E)
    (a b : nat) (X : list nat) (m : formula) : nat :=
  least_index E (BrSuccessSet E a b X m)
    (br_success_index_exists E C a b X m).

Definition SealCode (E : FixedCoding) (C : IndexClosure E)
    (a : nat) (X : list nat) (m : formula) : nat :=
  least_index E (SealSet E a X m)
    (seal_index_exists E C a X m).

Definition MW (E : FixedCoding) (C : IndexClosure E) (a b : nat) : nat :=
  let X := [a; b] in
  let m := FMarkMw (cantor_pair a b) in
  match excluded_middle_informative
    (Blocked E C X a \/ Blocked E C X b) with
  | left _ => Fail E C X m
  | right _ =>
      match mu_mw E C a b with
      | Some u => MwSuccessCode E C u X m
      | None => Fail E C X m
      end
  end.

Definition BR (E : FixedCoding) (C : IndexClosure E) (a b : nat) : nat :=
  let X := [a; b] in
  let m := FMarkBr (cantor_pair a b) in
  match excluded_middle_informative
    (Blocked E C X a \/ Blocked E C X b \/ ~ BranchOK E C a b) with
  | left _ => Fail E C X m
  | right _ => BrSuccessCode E C a b X m
  end.

Definition SEAL (E : FixedCoding) (C : IndexClosure E) (a : nat) : nat :=
  let m := FMarkSeal (kappa E C a) in
  SealCode E C a [a] m.

Lemma Fail_spec :
  forall (E : FixedCoding) (C : IndexClosure E) X m,
    TheoryExt E (Fail E C X m) (FailSet E X m).
Proof.
  intros E C X m.
  apply least_index_spec.
Qed.

Lemma MwSuccessCode_spec :
  forall (E : FixedCoding) (C : IndexClosure E) u X m,
    TheoryExt E (MwSuccessCode E C u X m) (MwSuccessSet E u X m).
Proof.
  intros E C u X m.
  apply least_index_spec.
Qed.

Lemma BrSuccessCode_spec :
  forall (E : FixedCoding) (C : IndexClosure E) a b X m,
    TheoryExt E (BrSuccessCode E C a b X m) (BrSuccessSet E a b X m).
Proof.
  intros E C a b X m.
  apply least_index_spec.
Qed.

Lemma SEAL_spec :
  forall (E : FixedCoding) (C : IndexClosure E) a,
    TheoryExt E (SEAL E C a)
      (SealSet E a [a] (FMarkSeal (kappa E C a))).
Proof.
  intros E C a.
  apply least_index_spec.
Qed.

Lemma MW_blocked_is_fail :
  forall (E : FixedCoding) (C : IndexClosure E) a b,
    Blocked E C [a; b] a \/ Blocked E C [a; b] b ->
    MW E C a b = Fail E C [a; b] (FMarkMw (cantor_pair a b)).
Proof.
  intros E C a b Hblocked.
  unfold MW.
  destruct (excluded_middle_informative
    (Blocked E C [a; b] a \/ Blocked E C [a; b] b))
    as [Hbad | Hgood].
  - reflexivity.
  - contradiction.
Qed.

Lemma MW_no_candidate_is_fail :
  forall (E : FixedCoding) (C : IndexClosure E) a b,
    mu_mw E C a b = None ->
    MW E C a b = Fail E C [a; b] (FMarkMw (cantor_pair a b)).
Proof.
  intros E C a b Hnone.
  unfold MW.
  destruct (excluded_middle_informative
    (Blocked E C [a; b] a \/ Blocked E C [a; b] b)).
  - reflexivity.
  - rewrite Hnone. reflexivity.
Qed.

Lemma MW_success_spec :
  forall (E : FixedCoding) (C : IndexClosure E) a b u,
    ~ (Blocked E C [a; b] a \/ Blocked E C [a; b] b) ->
    mu_mw E C a b = Some u ->
    TheoryExt E (MW E C a b)
      (MwSuccessSet E u [a; b] (FMarkMw (cantor_pair a b))).
Proof.
  intros E C a b u Hopen Hmu.
  unfold MW.
  destruct (excluded_middle_informative
    (Blocked E C [a; b] a \/ Blocked E C [a; b] b))
    as [Hbad | Hgood].
  - contradiction.
  - rewrite Hmu. apply MwSuccessCode_spec.
Qed.

Lemma BR_failure_is_fail :
  forall (E : FixedCoding) (C : IndexClosure E) a b,
    Blocked E C [a; b] a \/ Blocked E C [a; b] b \/
      ~ BranchOK E C a b ->
    BR E C a b = Fail E C [a; b] (FMarkBr (cantor_pair a b)).
Proof.
  intros E C a b Hbad.
  unfold BR.
  destruct (excluded_middle_informative
    (Blocked E C [a; b] a \/ Blocked E C [a; b] b \/
      ~ BranchOK E C a b)) as [Hfail | Hsuccess].
  - reflexivity.
  - contradiction.
Qed.

Lemma BR_success_spec :
  forall (E : FixedCoding) (C : IndexClosure E) a b,
    ~ (Blocked E C [a; b] a \/ Blocked E C [a; b] b \/
      ~ BranchOK E C a b) ->
    TheoryExt E (BR E C a b)
      (BrSuccessSet E a b [a; b] (FMarkBr (cantor_pair a b))).
Proof.
  intros E C a b Hsuccess.
  unfold BR.
  destruct (excluded_middle_informative
    (Blocked E C [a; b] a \/ Blocked E C [a; b] b \/
      ~ BranchOK E C a b)) as [Hfail | Hopen].
  - contradiction.
  - apply BrSuccessCode_spec.
Qed.

Lemma marker_sentence :
  forall n, Sentence (FMarkSeal n).
Proof.
  intro n.
  split; reflexivity.
Qed.

Lemma seal_registers_core :
  forall (E : FixedCoding) (C : IndexClosure E) a,
    Reg E (SEAL E C a) (kappa E C a).
Proof.
  intros E C a.
  unfold Reg.
  pose proof (SEAL_spec E C a (FMarkSeal (kappa E C a))) as Hspec.
  apply Hspec.
  split.
  - apply marker_sentence.
  - right; right; reflexivity.
Qed.

(** ** 8. Theory terms and their unique interpretation *)

Inductive theory_term : Type :=
| PVar : nat -> theory_term
| TMw : theory_term -> theory_term -> theory_term
| TBr : theory_term -> theory_term -> theory_term
| TSeal : theory_term -> theory_term.

Definition valuation := nat -> nat.

Fixpoint eval (E : FixedCoding) (C : IndexClosure E)
    (v : valuation) (A : theory_term) : nat :=
  match A with
  | PVar i => v i
  | TMw B D => MW E C (eval E C v B) (eval E C v D)
  | TBr B D => BR E C (eval E C v B) (eval E C v D)
  | TSeal B => SEAL E C (eval E C v B)
  end.

Theorem eval_exists_unique :
  forall (E : FixedCoding) (C : IndexClosure E) v A,
    exists! n, n = eval E C v A.
Proof.
  intros E C v A.
  exists (eval E C v A).
  split.
  - reflexivity.
  - intros y Hy.
    symmetry; exact Hy.
Qed.

(** ** 9. Finite path contexts and legality *)

Inductive subterm_at : theory_term -> list bool -> theory_term -> Prop :=
| subterm_root : forall A, subterm_at A [] A
| subterm_mw_left : forall A B path S,
    subterm_at A path S -> subterm_at (TMw A B) (false :: path) S
| subterm_mw_right : forall A B path S,
    subterm_at B path S -> subterm_at (TMw A B) (true :: path) S
| subterm_br_left : forall A B path S,
    subterm_at A path S -> subterm_at (TBr A B) (false :: path) S
| subterm_br_right : forall A B path S,
    subterm_at B path S -> subterm_at (TBr A B) (true :: path) S
| subterm_seal_child : forall A path S,
    subterm_at A path S -> subterm_at (TSeal A) (false :: path) S.

Definition Reg_v (E : FixedCoding) (C : IndexClosure E)
    (v : valuation) (Gamma : list theory_term) (d : nat) : Prop :=
  exists A, In A Gamma /\ Reg E (eval E C v A) d.

Definition CtxBlocked (E : FixedCoding) (C : IndexClosure E)
    (v : valuation) (Gamma : list theory_term) (A : theory_term) : Prop :=
  Reg_v E C v Gamma (kappa E C (eval E C v A)).

Definition CCon (E : FixedCoding) (C : IndexClosure E)
    (v : valuation) (A : theory_term) : Prop :=
  Con E (kappa E C (eval E C v A)).

Definition Open (E : FixedCoding) (C : IndexClosure E)
    (v : valuation) (Gamma : list theory_term) (A : theory_term) : Prop :=
  CCon E C v A /\ ~ CtxBlocked E C v Gamma A.

Definition subterm_condition (E : FixedCoding) (C : IndexClosure E)
    (v : valuation) (Gamma : list theory_term) (S : theory_term) : Prop :=
  match S with
  | PVar _ => True
  | TMw B D =>
      Open E C v Gamma B /\
      ~ CtxBlocked E C v Gamma D /\
      exists u, mu_mw E C (eval E C v B) (eval E C v D) = Some u
  | TBr B D =>
      Open E C v Gamma B /\
      ~ CtxBlocked E C v Gamma D /\
      BranchOK E C (eval E C v B) (eval E C v D)
  | TSeal B => CCon E C v B
  end.

Definition Legal (E : FixedCoding) (C : IndexClosure E)
    (v : valuation) (Gamma : list theory_term) : Prop :=
  (forall A, In A Gamma -> CCon E C v A) /\
  (forall A path S,
      In A Gamma -> subterm_at A path S ->
      subterm_condition E C v Gamma S).

Lemma legal_member_ccon :
  forall (E : FixedCoding) (C : IndexClosure E) v Gamma A,
    Legal E C v Gamma -> In A Gamma -> CCon E C v A.
Proof.
  intros E C v Gamma A Hlegal Hin.
  exact (proj1 Hlegal A Hin).
Qed.

Lemma legal_root_condition :
  forall (E : FixedCoding) (C : IndexClosure E) v Gamma A,
    Legal E C v Gamma -> In A Gamma ->
    subterm_condition E C v Gamma A.
Proof.
  intros E C v Gamma A Hlegal Hin.
  exact (proj2 Hlegal A [] A Hin (subterm_root A)).
Qed.

(** ** 10. Evolution graph, usable edges, and semantic consequence *)

Inductive edge_kind : Type := EdgeMw | EdgeBr | EdgeSeal.

Inductive EvolutionEdge : theory_term -> theory_term -> edge_kind -> Prop :=
| edge_mw_left : forall A B, EvolutionEdge A (TMw A B) EdgeMw
| edge_mw_right : forall A B, EvolutionEdge B (TMw A B) EdgeMw
| edge_br_left : forall A B, EvolutionEdge A (TBr A B) EdgeBr
| edge_br_right : forall A B, EvolutionEdge B (TBr A B) EdgeBr
| edge_seal : forall A, EvolutionEdge A (TSeal A) EdgeSeal.

Definition EdgeUsable (E : FixedCoding) (C : IndexClosure E)
    (v : valuation) (Gamma : list theory_term)
    (source target : theory_term) (kind : edge_kind) : Prop :=
  Legal E C v Gamma /\
  In target Gamma /\
  EvolutionEdge source target kind /\
  subterm_condition E C v Gamma target.

Definition TDB_consequence (E : FixedCoding) (C : IndexClosure E)
    (Gamma : list theory_term) (A : theory_term) : Prop :=
  forall v, Legal E C v Gamma -> Legal E C v (A :: Gamma).

(** ** 11. Basic ZFC-level facts, now kernel-checked *)

Theorem legal_branch_implies_compatible :
  forall (E : FixedCoding) (C : IndexClosure E) v Gamma A B,
    Legal E C v (TBr A B :: Gamma) ->
    Con E (theory_union E C
      (kappa E C (eval E C v A))
      (kappa E C (eval E C v B))).
Proof.
  intros E C v Gamma A B Hlegal.
  pose proof (legal_root_condition E C v (TBr A B :: Gamma)
    (TBr A B) Hlegal (or_introl eq_refl)) as Hroot.
  cbn in Hroot.
  destruct Hroot as [_ [_ Hbranch]].
  exact (proj1 Hbranch).
Qed.

Theorem seal_coexistence_and_exclusion :
  forall (E : FixedCoding) (C : IndexClosure E) v A,
    Legal E C v [A; TSeal A] ->
    CCon E C v A /\ CCon E C v (TSeal A) /\
    forall B, ~ Legal E C v [A; TSeal A; TMw B A].
Proof.
  intros E C v A Hlegal.
  split.
  - apply (legal_member_ccon E C v [A; TSeal A] A Hlegal).
    left; reflexivity.
  - split.
    + apply (legal_member_ccon E C v [A; TSeal A] (TSeal A) Hlegal).
      right; left; reflexivity.
    + intros B Hextended.
      pose proof (legal_root_condition E C v
        [A; TSeal A; TMw B A] (TMw B A) Hextended) as Hroot.
      assert (HinMw : In (TMw B A) [A; TSeal A; TMw B A]).
      { right; right; left; reflexivity. }
      specialize (Hroot HinMw).
      cbn in Hroot.
      destruct Hroot as [_ [Hnotblocked _]].
      apply Hnotblocked.
      unfold CtxBlocked, Reg_v.
      exists (TSeal A).
      split.
      * right; left; reflexivity.
      * cbn. apply seal_registers_core.
Qed.

Theorem sealed_target_excludes_mw_extension :
  forall (E : FixedCoding) (C : IndexClosure E) v Gamma B,
    Legal E C v Gamma ->
    In (TSeal B) Gamma ->
    forall A, ~ Legal E C v (TMw A B :: Gamma).
Proof.
  intros E C v Gamma B Hlegal HinSeal A Hextended.
  pose proof (legal_root_condition E C v (TMw A B :: Gamma)
    (TMw A B) Hextended (or_introl eq_refl)) as Hroot.
  cbn in Hroot.
  destruct Hroot as [_ [Hnotblocked _]].
  apply Hnotblocked.
  unfold CtxBlocked, Reg_v.
  exists (TSeal B).
  split.
  - right; exact HinSeal.
  - cbn. apply seal_registers_core.
Qed.

End TheoryDifferentiationConsistencyLogic1146.
