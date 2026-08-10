(* Natural-number coding layer for the full SRBE-065 certificate language. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia.
Require Import SRBE1787.
Require FormalSystemFactoryStructuralCodec FormalSystemFactoryNatCodec.
Import ListNotations.
Set Implicit Arguments.

Module SC := FormalSystemFactoryStructuralCodec.FormalSystemFactoryStructuralCodec.
Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.

Definition dec_atom (c : SC.code) : option nat :=
  match c with SC.CAtom n => Some n | _ => None end.

Definition omap2 {A B C} (f : A -> B -> C) (x : option A) (y : option B) :=
  match x, y with Some a, Some b => Some (f a b) | _, _ => None end.
Definition omap3 {A B C D} (f : A -> B -> C -> D)
    (x : option A) (y : option B) (z : option C) :=
  match x, y, z with Some a, Some b, Some c => Some (f a b c) | _, _, _ => None end.
Definition omap4 {A B C D E} (f : A -> B -> C -> D -> E)
    (x : option A) (y : option B) (z : option C) (w : option D) :=
  match x, y, z, w with
  | Some a, Some b, Some c, Some d => Some (f a b c d)
  | _, _, _, _ => None
  end.
Definition omap5 {A B C D E F} (f : A -> B -> C -> D -> E -> F)
    (a : option A) (b : option B) (c : option C) (d : option D) (e : option E) :=
  match a, b, c, d, e with
  | Some x, Some y, Some z, Some u, Some v => Some (f x y z u v)
  | _, _, _, _, _ => None
  end.
Definition omap6 {A B C D E F G} (f : A -> B -> C -> D -> E -> F -> G)
    (a : option A) (b : option B) (c : option C) (d : option D)
    (e : option E) (g : option F) :=
  match a, b, c, d, e, g with
  | Some x, Some y, Some z, Some u, Some v, Some w => Some (f x y z u v w)
  | _, _, _, _, _, _ => None
  end.
Definition omap7 {A B C D E F G H} (f : A -> B -> C -> D -> E -> F -> G -> H)
    (a : option A) (b : option B) (c : option C) (d : option D)
    (e : option E) (g : option F) (h : option G) :=
  match a, b, c, d, e, g, h with
  | Some x, Some y, Some z, Some u, Some v, Some w, Some r =>
      Some (f x y z u v w r)
  | _, _, _, _, _, _, _ => None
  end.

(** Base sorted syntax. *)

Definition encode_sort_code (s : sort) : SC.code :=
  match s with
  | SD => SC.CNode 0 [] | SN => SC.CNode 1 []
  | SLow k => SC.CNode 2 [SC.CAtom k]
  | SList k => SC.CNode 3 [SC.CAtom k]
  end.

Definition decode_sort_code (c : SC.code) : option sort :=
  match c with
  | SC.CNode 0 [] => Some SD | SC.CNode 1 [] => Some SN
  | SC.CNode 2 [SC.CAtom k] => Some (SLow k)
  | SC.CNode 3 [SC.CAtom k] => Some (SList k)
  | _ => None
  end.

Lemma decode_encode_sort_code : forall s,
  decode_sort_code (encode_sort_code s) = Some s.
Proof. destruct s; reflexivity. Qed.

Definition encode_sort_list := SC.encode_code_list encode_sort_code.
Definition decode_sort_list := SC.decode_code_list_node decode_sort_code.

Lemma decode_encode_sort_list : forall ss,
  decode_sort_list (encode_sort_list ss) = Some ss.
Proof. apply SC.decode_code_list_node_encode, decode_encode_sort_code. Qed.

Definition encode_fsym_code (f : fsym) : SC.code :=
  match f with
  | FBase n ins out => SC.CNode 0 [SC.CAtom n; encode_sort_list ins; encode_sort_code out]
  | FZero => SC.CNode 1 [] | FSucc => SC.CNode 2 []
  | FAdd => SC.CNode 3 [] | FMul => SC.CNode 4 []
  | FLowConst k s r c => SC.CNode 5 [SC.CAtom k; SC.CAtom s; SC.CAtom r; SC.CAtom c]
  | FSource k => SC.CNode 6 [SC.CAtom k]
  | FRootCode k => SC.CNode 7 [SC.CAtom k]
  | FCert k => SC.CNode 8 [SC.CAtom k]
  | FNil k => SC.CNode 9 [SC.CAtom k]
  | FCons k => SC.CNode 10 [SC.CAtom k]
  | FEnum k => SC.CNode 11 [SC.CAtom k]
  end.

Definition decode_fsym_code (c : SC.code) : option fsym :=
  match c with
  | SC.CNode 0 [SC.CAtom n; ins; out] =>
      omap2 (FBase n) (decode_sort_list ins) (decode_sort_code out)
  | SC.CNode 1 [] => Some FZero | SC.CNode 2 [] => Some FSucc
  | SC.CNode 3 [] => Some FAdd | SC.CNode 4 [] => Some FMul
  | SC.CNode 5 [SC.CAtom k; SC.CAtom s; SC.CAtom r; SC.CAtom d] =>
      Some (FLowConst k s r d)
  | SC.CNode 6 [SC.CAtom k] => Some (FSource k)
  | SC.CNode 7 [SC.CAtom k] => Some (FRootCode k)
  | SC.CNode 8 [SC.CAtom k] => Some (FCert k)
  | SC.CNode 9 [SC.CAtom k] => Some (FNil k)
  | SC.CNode 10 [SC.CAtom k] => Some (FCons k)
  | SC.CNode 11 [SC.CAtom k] => Some (FEnum k)
  | _ => None
  end.

Lemma decode_encode_fsym_code : forall f,
  decode_fsym_code (encode_fsym_code f) = Some f.
Proof.
  destruct f; unfold encode_fsym_code, decode_fsym_code; try reflexivity.
  rewrite decode_encode_sort_list, decode_encode_sort_code. reflexivity.
Qed.

Definition encode_rsym_code (r : rsym) : SC.code :=
  match r with
  | RBase n ins => SC.CNode 0 [SC.CAtom n; encode_sort_list ins]
  | RD3 => SC.CNode 1 [] | RP n => SC.CNode 2 [SC.CAtom n]
  | RMember k => SC.CNode 3 [SC.CAtom k]
  end.

Definition decode_rsym_code (c : SC.code) : option rsym :=
  match c with
  | SC.CNode 0 [SC.CAtom n; ins] =>
      match decode_sort_list ins with Some ss => Some (RBase n ss) | None => None end
  | SC.CNode 1 [] => Some RD3
  | SC.CNode 2 [SC.CAtom n] => Some (RP n)
  | SC.CNode 3 [SC.CAtom k] => Some (RMember k)
  | _ => None
  end.

Lemma decode_encode_rsym_code : forall r,
  decode_rsym_code (encode_rsym_code r) = Some r.
Proof.
  destruct r; unfold encode_rsym_code, decode_rsym_code; try reflexivity.
  rewrite decode_encode_sort_list. reflexivity.
Qed.

Fixpoint encode_term_code (t : term) : SC.code :=
  match t with
  | TVar s i => SC.CNode 0 [encode_sort_code s; SC.CAtom i]
  | TFun f ts => SC.CNode 1 [encode_fsym_code f; encode_terms_code ts]
  end
with encode_terms_code (ts : terms) : SC.code :=
  match ts with
  | TNil => SC.CNode 0 []
  | TCons t us => SC.CNode 1 [encode_term_code t; encode_terms_code us]
  end.

Fixpoint decode_term_code (c : SC.code) : option term :=
  match c with
  | SC.CNode 0 [s; SC.CAtom i] =>
      match decode_sort_code s with Some r => Some (TVar r i) | None => None end
  | SC.CNode 1 [f; ts] => omap2 TFun (decode_fsym_code f) (decode_terms_code ts)
  | _ => None
  end
with decode_terms_code (c : SC.code) : option terms :=
  match c with
  | SC.CNode 0 [] => Some TNil
  | SC.CNode 1 [t; ts] => omap2 TCons (decode_term_code t) (decode_terms_code ts)
  | _ => None
  end.

Lemma decode_encode_term_code : forall t,
  decode_term_code (encode_term_code t) = Some t
with decode_encode_terms_code : forall ts,
  decode_terms_code (encode_terms_code ts) = Some ts.
Proof.
  - intro t. destruct t; cbn.
    + rewrite decode_encode_sort_code. reflexivity.
    + rewrite decode_encode_fsym_code, decode_encode_terms_code. reflexivity.
  - intro ts. destruct ts; cbn.
    + reflexivity.
    + rewrite decode_encode_term_code, decode_encode_terms_code. reflexivity.
Qed.

Fixpoint encode_formula_code (A : formula) : SC.code :=
  match A with
  | Bot => SC.CNode 0 []
  | Eq s t u => SC.CNode 1 [encode_sort_code s; encode_term_code t; encode_term_code u]
  | Rel r ts => SC.CNode 2 [encode_rsym_code r; encode_terms_code ts]
  | And B C => SC.CNode 3 [encode_formula_code B; encode_formula_code C]
  | Or B C => SC.CNode 4 [encode_formula_code B; encode_formula_code C]
  | Imp B C => SC.CNode 5 [encode_formula_code B; encode_formula_code C]
  | All s B => SC.CNode 6 [encode_sort_code s; encode_formula_code B]
  | Ex s B => SC.CNode 7 [encode_sort_code s; encode_formula_code B]
  end.

Fixpoint decode_formula_code (c : SC.code) : option formula :=
  match c with
  | SC.CNode 0 [] => Some Bot
  | SC.CNode 1 [s; t; u] =>
      omap3 Eq (decode_sort_code s) (decode_term_code t) (decode_term_code u)
  | SC.CNode 2 [r; ts] => omap2 Rel (decode_rsym_code r) (decode_terms_code ts)
  | SC.CNode 3 [B; C] => omap2 And (decode_formula_code B) (decode_formula_code C)
  | SC.CNode 4 [B; C] => omap2 Or (decode_formula_code B) (decode_formula_code C)
  | SC.CNode 5 [B; C] => omap2 Imp (decode_formula_code B) (decode_formula_code C)
  | SC.CNode 6 [s; B] => omap2 All (decode_sort_code s) (decode_formula_code B)
  | SC.CNode 7 [s; B] => omap2 Ex (decode_sort_code s) (decode_formula_code B)
  | _ => None
  end.

Lemma decode_encode_formula_code : forall A,
  decode_formula_code (encode_formula_code A) = Some A.
Proof.
  induction A; cbn; rewrite ?decode_encode_sort_code, ?decode_encode_term_code,
    ?decode_encode_terms_code, ?decode_encode_rsym_code, ?IHA, ?IHA1, ?IHA2;
    reflexivity.
Qed.

(** Scheme syntax and rule schemes. *)

Fixpoint encode_sch_term_code (t : sch_term) : SC.code :=
  match t with
  | STMVar s n => SC.CNode 0 [encode_sort_code s; SC.CAtom n]
  | STVar s i => SC.CNode 1 [encode_sort_code s; SC.CAtom i]
  | STFun f ts => SC.CNode 2 [encode_fsym_code f; encode_sch_terms_code ts]
  end
with encode_sch_terms_code (ts : sch_terms) : SC.code :=
  match ts with
  | STNil => SC.CNode 0 []
  | STCons t us => SC.CNode 1 [encode_sch_term_code t; encode_sch_terms_code us]
  end.

Fixpoint decode_sch_term_code (c : SC.code) : option sch_term :=
  match c with
  | SC.CNode 0 [s; SC.CAtom n] =>
      match decode_sort_code s with Some r => Some (STMVar r n) | None => None end
  | SC.CNode 1 [s; SC.CAtom i] =>
      match decode_sort_code s with Some r => Some (STVar r i) | None => None end
  | SC.CNode 2 [f; ts] => omap2 STFun (decode_fsym_code f) (decode_sch_terms_code ts)
  | _ => None
  end
with decode_sch_terms_code (c : SC.code) : option sch_terms :=
  match c with
  | SC.CNode 0 [] => Some STNil
  | SC.CNode 1 [t; ts] => omap2 STCons (decode_sch_term_code t) (decode_sch_terms_code ts)
  | _ => None
  end.

Lemma decode_encode_sch_term_code : forall t,
  decode_sch_term_code (encode_sch_term_code t) = Some t
with decode_encode_sch_terms_code : forall ts,
  decode_sch_terms_code (encode_sch_terms_code ts) = Some ts.
Proof.
  - intro t. destruct t; cbn.
    + rewrite decode_encode_sort_code. reflexivity.
    + rewrite decode_encode_sort_code. reflexivity.
    + rewrite decode_encode_fsym_code, decode_encode_sch_terms_code. reflexivity.
  - intro ts. destruct ts; cbn.
    + reflexivity.
    + rewrite decode_encode_sch_term_code, decode_encode_sch_terms_code. reflexivity.
Qed.

Fixpoint encode_sch_formula_code (A : sch_formula) : SC.code :=
  match A with
  | SFMVar n => SC.CNode 0 [SC.CAtom n]
  | SBot => SC.CNode 1 []
  | SEq s t u => SC.CNode 2 [encode_sort_code s; encode_sch_term_code t; encode_sch_term_code u]
  | SRel r ts => SC.CNode 3 [encode_rsym_code r; encode_sch_terms_code ts]
  | SAnd B C => SC.CNode 4 [encode_sch_formula_code B; encode_sch_formula_code C]
  | SOr B C => SC.CNode 5 [encode_sch_formula_code B; encode_sch_formula_code C]
  | SImp B C => SC.CNode 6 [encode_sch_formula_code B; encode_sch_formula_code C]
  | SAll s B => SC.CNode 7 [encode_sort_code s; encode_sch_formula_code B]
  | SEx s B => SC.CNode 8 [encode_sort_code s; encode_sch_formula_code B]
  | SSubFm s B i t =>
      SC.CNode 9 [encode_sort_code s; encode_sch_formula_code B;
                  SC.CAtom i; encode_sch_term_code t]
  end.

Fixpoint decode_sch_formula_code (c : SC.code) : option sch_formula :=
  match c with
  | SC.CNode 0 [SC.CAtom n] => Some (SFMVar n)
  | SC.CNode 1 [] => Some SBot
  | SC.CNode 2 [s; t; u] =>
      omap3 SEq (decode_sort_code s) (decode_sch_term_code t) (decode_sch_term_code u)
  | SC.CNode 3 [r; ts] => omap2 SRel (decode_rsym_code r) (decode_sch_terms_code ts)
  | SC.CNode 4 [B; C] => omap2 SAnd (decode_sch_formula_code B) (decode_sch_formula_code C)
  | SC.CNode 5 [B; C] => omap2 SOr (decode_sch_formula_code B) (decode_sch_formula_code C)
  | SC.CNode 6 [B; C] => omap2 SImp (decode_sch_formula_code B) (decode_sch_formula_code C)
  | SC.CNode 7 [s; B] => omap2 SAll (decode_sort_code s) (decode_sch_formula_code B)
  | SC.CNode 8 [s; B] => omap2 SEx (decode_sort_code s) (decode_sch_formula_code B)
  | SC.CNode 9 [s; B; SC.CAtom i; t] =>
      omap3 (fun r C u => SSubFm r C i u)
        (decode_sort_code s) (decode_sch_formula_code B) (decode_sch_term_code t)
  | _ => None
  end.

Lemma decode_encode_sch_formula_code : forall A,
  decode_sch_formula_code (encode_sch_formula_code A) = Some A.
Proof.
  induction A; cbn; rewrite ?decode_encode_sort_code, ?decode_encode_sch_term_code,
    ?decode_encode_sch_terms_code, ?decode_encode_rsym_code, ?IHA, ?IHA1, ?IHA2;
    reflexivity.
Qed.

Definition encode_sch_ctx_atom_code (a : sch_ctx_atom) : SC.code :=
  match a with
  | SCFormula A => SC.CNode 0 [encode_sch_formula_code A]
  | SCContext n => SC.CNode 1 [SC.CAtom n]
  end.

Definition decode_sch_ctx_atom_code (c : SC.code) : option sch_ctx_atom :=
  match c with
  | SC.CNode 0 [A] =>
      match decode_sch_formula_code A with Some B => Some (SCFormula B) | None => None end
  | SC.CNode 1 [SC.CAtom n] => Some (SCContext n)
  | _ => None
  end.

Lemma decode_encode_sch_ctx_atom_code : forall a,
  decode_sch_ctx_atom_code (encode_sch_ctx_atom_code a) = Some a.
Proof. destruct a; cbn; try reflexivity. rewrite decode_encode_sch_formula_code. reflexivity. Qed.

Definition encode_sch_context_code := SC.encode_code_list encode_sch_ctx_atom_code.
Definition decode_sch_context_code := SC.decode_code_list_node decode_sch_ctx_atom_code.

Lemma decode_encode_sch_context_code : forall G,
  decode_sch_context_code (encode_sch_context_code G) = Some G.
Proof. apply SC.decode_code_list_node_encode, decode_encode_sch_ctx_atom_code. Qed.

Definition encode_sch_sequent_code (S : sch_sequent) : SC.code :=
  SC.CNode 0 [encode_sch_context_code (sch_antecedent S);
              encode_sch_context_code (sch_succedent S)].

Definition decode_sch_sequent_code (c : SC.code) : option sch_sequent :=
  match c with
  | SC.CNode 0 [G; D] => omap2 mkSchSeq (decode_sch_context_code G) (decode_sch_context_code D)
  | _ => None
  end.

Lemma decode_encode_sch_sequent_code : forall S,
  decode_sch_sequent_code (encode_sch_sequent_code S) = Some S.
Proof.
  intros [G D]. unfold encode_sch_sequent_code, decode_sch_sequent_code.
  rewrite !decode_encode_sch_context_code. reflexivity.
Qed.

Definition encode_sch_sequent_list := SC.encode_code_list encode_sch_sequent_code.
Definition decode_sch_sequent_list := SC.decode_code_list_node decode_sch_sequent_code.
Lemma decode_encode_sch_sequent_list : forall ss,
  decode_sch_sequent_list (encode_sch_sequent_list ss) = Some ss.
Proof. apply SC.decode_code_list_node_encode, decode_encode_sch_sequent_code. Qed.

Definition encode_side_condition_code (c : side_condition) : SC.code :=
  match c with
  | SideSortEq s r => SC.CNode 0 [encode_sort_code s; encode_sort_code r]
  | SideCodeEq m n => SC.CNode 1 [SC.CAtom m; SC.CAtom n]
  | SideEigenFresh s i seq0 =>
      SC.CNode 2 [encode_sort_code s; SC.CAtom i; encode_sch_sequent_code seq0]
  end.

Definition decode_side_condition_code (c : SC.code) : option side_condition :=
  match c with
  | SC.CNode 0 [s; r] => omap2 SideSortEq (decode_sort_code s) (decode_sort_code r)
  | SC.CNode 1 [SC.CAtom m; SC.CAtom n] => Some (SideCodeEq m n)
  | SC.CNode 2 [s; SC.CAtom i; seq0] =>
      omap2 (fun r T => SideEigenFresh r i T)
        (decode_sort_code s) (decode_sch_sequent_code seq0)
  | _ => None
  end.

Lemma decode_encode_side_condition_code : forall c,
  decode_side_condition_code (encode_side_condition_code c) = Some c.
Proof.
  destruct c; unfold encode_side_condition_code, decode_side_condition_code.
  - rewrite !decode_encode_sort_code. reflexivity.
  - reflexivity.
  - rewrite decode_encode_sort_code, decode_encode_sch_sequent_code. reflexivity.
Qed.

Definition encode_side_condition_list := SC.encode_code_list encode_side_condition_code.
Definition decode_side_condition_list := SC.decode_code_list_node decode_side_condition_code.
Lemma decode_encode_side_condition_list : forall cs,
  decode_side_condition_list (encode_side_condition_list cs) = Some cs.
Proof. apply SC.decode_code_list_node_encode, decode_encode_side_condition_code. Qed.

Definition encode_rule_scheme_code (q : rule_scheme) : SC.code :=
  SC.CNode 0 [SC.CAtom (scheme_tag q);
              encode_sch_sequent_list (scheme_premises q);
              encode_sch_sequent_code (scheme_conclusion q);
              encode_side_condition_list (scheme_conditions q)].

Definition decode_rule_scheme_code (c : SC.code) : option rule_scheme :=
  match c with
  | SC.CNode 0 [SC.CAtom tag; ps; C; cs] =>
      omap3 (mkScheme tag) (decode_sch_sequent_list ps)
        (decode_sch_sequent_code C) (decode_side_condition_list cs)
  | _ => None
  end.

Lemma decode_encode_rule_scheme_code : forall q,
  decode_rule_scheme_code (encode_rule_scheme_code q) = Some q.
Proof.
  intros [tag ps C cs]. unfold encode_rule_scheme_code, decode_rule_scheme_code.
  rewrite decode_encode_sch_sequent_list, decode_encode_sch_sequent_code,
          decode_encode_side_condition_list. reflexivity.
Qed.

(** Scheme instantiations. *)

Definition encode_sch_term_binding_code (x : nat * sort * sch_term) : SC.code :=
  let '(n, s, t) := x in
  SC.CNode 0 [SC.CAtom n; encode_sort_code s; encode_sch_term_code t].

Definition decode_sch_term_binding_code (c : SC.code)
    : option (nat * sort * sch_term) :=
  match c with
  | SC.CNode 0 [SC.CAtom n; s; t] =>
      omap2 (fun r u => (n, r, u)) (decode_sort_code s) (decode_sch_term_code t)
  | _ => None
  end.

Lemma decode_encode_sch_term_binding_code : forall x,
  decode_sch_term_binding_code (encode_sch_term_binding_code x) = Some x.
Proof.
  intros [[n s] t]. unfold encode_sch_term_binding_code, decode_sch_term_binding_code.
  rewrite decode_encode_sort_code, decode_encode_sch_term_code. reflexivity.
Qed.

Definition encode_sch_formula_binding_code (x : nat * sch_formula) : SC.code :=
  let '(n, A) := x in SC.CNode 0 [SC.CAtom n; encode_sch_formula_code A].
Definition decode_sch_formula_binding_code (c : SC.code)
    : option (nat * sch_formula) :=
  match c with
  | SC.CNode 0 [SC.CAtom n; A] =>
      match decode_sch_formula_code A with Some B => Some (n, B) | None => None end
  | _ => None
  end.
Lemma decode_encode_sch_formula_binding_code : forall x,
  decode_sch_formula_binding_code (encode_sch_formula_binding_code x) = Some x.
Proof.
  intros [n A]. unfold encode_sch_formula_binding_code, decode_sch_formula_binding_code.
  rewrite decode_encode_sch_formula_code. reflexivity.
Qed.

Definition encode_sch_context_binding_code (x : nat * sch_context) : SC.code :=
  let '(n, G) := x in SC.CNode 0 [SC.CAtom n; encode_sch_context_code G].
Definition decode_sch_context_binding_code (c : SC.code)
    : option (nat * sch_context) :=
  match c with
  | SC.CNode 0 [SC.CAtom n; G] =>
      match decode_sch_context_code G with Some H => Some (n, H) | None => None end
  | _ => None
  end.
Lemma decode_encode_sch_context_binding_code : forall x,
  decode_sch_context_binding_code (encode_sch_context_binding_code x) = Some x.
Proof.
  intros [n G]. unfold encode_sch_context_binding_code, decode_sch_context_binding_code.
  rewrite decode_encode_sch_context_code. reflexivity.
Qed.

Definition encode_sch_term_bindings := SC.encode_code_list encode_sch_term_binding_code.
Definition decode_sch_term_bindings := SC.decode_code_list_node decode_sch_term_binding_code.
Definition encode_sch_formula_bindings := SC.encode_code_list encode_sch_formula_binding_code.
Definition decode_sch_formula_bindings := SC.decode_code_list_node decode_sch_formula_binding_code.
Definition encode_sch_context_bindings := SC.encode_code_list encode_sch_context_binding_code.
Definition decode_sch_context_bindings := SC.decode_code_list_node decode_sch_context_binding_code.

Lemma decode_encode_sch_term_bindings : forall xs,
  decode_sch_term_bindings (encode_sch_term_bindings xs) = Some xs.
Proof. apply SC.decode_code_list_node_encode, decode_encode_sch_term_binding_code. Qed.
Lemma decode_encode_sch_formula_bindings : forall xs,
  decode_sch_formula_bindings (encode_sch_formula_bindings xs) = Some xs.
Proof. apply SC.decode_code_list_node_encode, decode_encode_sch_formula_binding_code. Qed.
Lemma decode_encode_sch_context_bindings : forall xs,
  decode_sch_context_bindings (encode_sch_context_bindings xs) = Some xs.
Proof. apply SC.decode_code_list_node_encode, decode_encode_sch_context_binding_code. Qed.

Definition encode_sch_instantiation_code (rho : sch_instantiation) : SC.code :=
  SC.CNode 0 [encode_sch_term_bindings (sch_inst_terms rho);
              encode_sch_formula_bindings (sch_inst_formulas rho);
              encode_sch_context_bindings (sch_inst_contexts rho)].

Definition decode_sch_instantiation_code (c : SC.code) : option sch_instantiation :=
  match c with
  | SC.CNode 0 [ts; fs; cs] =>
      omap3 mkSchInst (decode_sch_term_bindings ts)
        (decode_sch_formula_bindings fs) (decode_sch_context_bindings cs)
  | _ => None
  end.

Lemma decode_encode_sch_instantiation_code : forall rho,
  decode_sch_instantiation_code (encode_sch_instantiation_code rho) = Some rho.
Proof.
  intros [ts fs cs]. unfold encode_sch_instantiation_code, decode_sch_instantiation_code.
  rewrite decode_encode_sch_term_bindings, decode_encode_sch_formula_bindings,
          decode_encode_sch_context_bindings. reflexivity.
Qed.

(** All twenty-three GQ witness constructors. *)

Definition encode_sch_gq_witness_code (w : sch_gq_witness) : SC.code :=
  match w with
  | SGId G D A => SC.CNode 0 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A]
  | SGBotL G D => SC.CNode 1 [encode_sch_context_code G; encode_sch_context_code D]
  | SGWkL G D A => SC.CNode 2 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A]
  | SGWkR G D A => SC.CNode 3 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A]
  | SGCtrL G D A => SC.CNode 4 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A]
  | SGCtrR G D A => SC.CNode 5 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A]
  | SGExchL G H D A B => SC.CNode 6 [encode_sch_context_code G; encode_sch_context_code H; encode_sch_context_code D; encode_sch_formula_code A; encode_sch_formula_code B]
  | SGExchR G D E A B => SC.CNode 7 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_context_code E; encode_sch_formula_code A; encode_sch_formula_code B]
  | SGCut G D P L A => SC.CNode 8 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_context_code P; encode_sch_context_code L; encode_sch_formula_code A]
  | SGRefl G D s t => SC.CNode 9 [encode_sch_context_code G; encode_sch_context_code D; encode_sort_code s; encode_sch_term_code t]
  | SGEqL G D s t u A j => SC.CNode 10 [encode_sch_context_code G; encode_sch_context_code D; encode_sort_code s; encode_sch_term_code t; encode_sch_term_code u; encode_sch_formula_code A; SC.CAtom j]
  | SGEqR G D s t u A j => SC.CNode 11 [encode_sch_context_code G; encode_sch_context_code D; encode_sort_code s; encode_sch_term_code t; encode_sch_term_code u; encode_sch_formula_code A; SC.CAtom j]
  | SGAndL G D A B => SC.CNode 12 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A; encode_sch_formula_code B]
  | SGAndR G D A B => SC.CNode 13 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A; encode_sch_formula_code B]
  | SGOrL G D A B => SC.CNode 14 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A; encode_sch_formula_code B]
  | SGOrR G D A B => SC.CNode 15 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A; encode_sch_formula_code B]
  | SGImpL G D P L A B => SC.CNode 16 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_context_code P; encode_sch_context_code L; encode_sch_formula_code A; encode_sch_formula_code B]
  | SGImpR G D A B => SC.CNode 17 [encode_sch_context_code G; encode_sch_context_code D; encode_sch_formula_code A; encode_sch_formula_code B]
  | SGAllL G D s A t => SC.CNode 18 [encode_sch_context_code G; encode_sch_context_code D; encode_sort_code s; encode_sch_formula_code A; encode_sch_term_code t]
  | SGAllR G D s A y => SC.CNode 19 [encode_sch_context_code G; encode_sch_context_code D; encode_sort_code s; encode_sch_formula_code A; SC.CAtom y]
  | SGExL G D s A y => SC.CNode 20 [encode_sch_context_code G; encode_sch_context_code D; encode_sort_code s; encode_sch_formula_code A; SC.CAtom y]
  | SGExR G D s A t => SC.CNode 21 [encode_sch_context_code G; encode_sch_context_code D; encode_sort_code s; encode_sch_formula_code A; encode_sch_term_code t]
  | SGQAx G D A => SC.CNode 22 [encode_sch_context_code G; encode_sch_context_code D; encode_formula_code A]
  end.

Definition decode_sch_gq_witness_code (c : SC.code) : option sch_gq_witness :=
  match c with
  | SC.CNode 0 [G;D;A] => omap3 SGId (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A)
  | SC.CNode 1 [G;D] => omap2 SGBotL (decode_sch_context_code G) (decode_sch_context_code D)
  | SC.CNode 2 [G;D;A] => omap3 SGWkL (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A)
  | SC.CNode 3 [G;D;A] => omap3 SGWkR (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A)
  | SC.CNode 4 [G;D;A] => omap3 SGCtrL (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A)
  | SC.CNode 5 [G;D;A] => omap3 SGCtrR (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A)
  | SC.CNode 6 [G;H;D;A;B] => omap5 SGExchL (decode_sch_context_code G) (decode_sch_context_code H) (decode_sch_context_code D) (decode_sch_formula_code A) (decode_sch_formula_code B)
  | SC.CNode 7 [G;D;E;A;B] => omap5 SGExchR (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_context_code E) (decode_sch_formula_code A) (decode_sch_formula_code B)
  | SC.CNode 8 [G;D;P;L;A] => omap5 SGCut (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_context_code P) (decode_sch_context_code L) (decode_sch_formula_code A)
  | SC.CNode 9 [G;D;s;t] => omap4 SGRefl (decode_sch_context_code G) (decode_sch_context_code D) (decode_sort_code s) (decode_sch_term_code t)
  | SC.CNode 10 [G;D;s;t;u;A;SC.CAtom j] => omap6 (fun G0 D0 s0 t0 u0 A0 => SGEqL G0 D0 s0 t0 u0 A0 j) (decode_sch_context_code G) (decode_sch_context_code D) (decode_sort_code s) (decode_sch_term_code t) (decode_sch_term_code u) (decode_sch_formula_code A)
  | SC.CNode 11 [G;D;s;t;u;A;SC.CAtom j] => omap6 (fun G0 D0 s0 t0 u0 A0 => SGEqR G0 D0 s0 t0 u0 A0 j) (decode_sch_context_code G) (decode_sch_context_code D) (decode_sort_code s) (decode_sch_term_code t) (decode_sch_term_code u) (decode_sch_formula_code A)
  | SC.CNode 12 [G;D;A;B] => omap4 SGAndL (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A) (decode_sch_formula_code B)
  | SC.CNode 13 [G;D;A;B] => omap4 SGAndR (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A) (decode_sch_formula_code B)
  | SC.CNode 14 [G;D;A;B] => omap4 SGOrL (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A) (decode_sch_formula_code B)
  | SC.CNode 15 [G;D;A;B] => omap4 SGOrR (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A) (decode_sch_formula_code B)
  | SC.CNode 16 [G;D;P;L;A;B] => omap6 SGImpL (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_context_code P) (decode_sch_context_code L) (decode_sch_formula_code A) (decode_sch_formula_code B)
  | SC.CNode 17 [G;D;A;B] => omap4 SGImpR (decode_sch_context_code G) (decode_sch_context_code D) (decode_sch_formula_code A) (decode_sch_formula_code B)
  | SC.CNode 18 [G;D;s;A;t] => omap5 SGAllL (decode_sch_context_code G) (decode_sch_context_code D) (decode_sort_code s) (decode_sch_formula_code A) (decode_sch_term_code t)
  | SC.CNode 19 [G;D;s;A;SC.CAtom y] => omap4 (fun G0 D0 s0 A0 => SGAllR G0 D0 s0 A0 y) (decode_sch_context_code G) (decode_sch_context_code D) (decode_sort_code s) (decode_sch_formula_code A)
  | SC.CNode 20 [G;D;s;A;SC.CAtom y] => omap4 (fun G0 D0 s0 A0 => SGExL G0 D0 s0 A0 y) (decode_sch_context_code G) (decode_sch_context_code D) (decode_sort_code s) (decode_sch_formula_code A)
  | SC.CNode 21 [G;D;s;A;t] => omap5 SGExR (decode_sch_context_code G) (decode_sch_context_code D) (decode_sort_code s) (decode_sch_formula_code A) (decode_sch_term_code t)
  | SC.CNode 22 [G;D;A] => omap3 SGQAx (decode_sch_context_code G) (decode_sch_context_code D) (decode_formula_code A)
  | _ => None
  end.

Lemma decode_encode_sch_gq_witness_code : forall w,
  decode_sch_gq_witness_code (encode_sch_gq_witness_code w) = Some w.
Proof.
  destruct w; unfold encode_sch_gq_witness_code, decode_sch_gq_witness_code;
    rewrite ?decode_encode_sch_context_code, ?decode_encode_sch_formula_code,
      ?decode_encode_sort_code, ?decode_encode_sch_term_code,
      ?decode_encode_formula_code; reflexivity.
Qed.

(** Certificate identifiers, exchanges, and the mutually recursive open tree. *)

Definition encode_cert_id_code (c : cert_id) : SC.code :=
  match c with
  | CChain n => SC.CNode 0 [SC.CAtom n]
  | CHa => SC.CNode 1 [] | CHaMinus => SC.CNode 2 []
  | CHb => SC.CNode 3 [] | CHbMinus => SC.CNode 4 []
  end.
Definition decode_cert_id_code (c : SC.code) : option cert_id :=
  match c with
  | SC.CNode 0 [SC.CAtom n] => Some (CChain n)
  | SC.CNode 1 [] => Some CHa | SC.CNode 2 [] => Some CHaMinus
  | SC.CNode 3 [] => Some CHb | SC.CNode 4 [] => Some CHbMinus
  | _ => None
  end.
Lemma decode_encode_cert_id_code : forall c,
  decode_cert_id_code (encode_cert_id_code c) = Some c.
Proof. destruct c; reflexivity. Qed.

Definition encode_cert_id_list := SC.encode_code_list encode_cert_id_code.
Definition decode_cert_id_list := SC.decode_code_list_node decode_cert_id_code.
Lemma decode_encode_cert_id_list : forall ds,
  decode_cert_id_list (encode_cert_id_list ds) = Some ds.
Proof. apply SC.decode_code_list_node_encode, decode_encode_cert_id_code. Qed.

Definition encode_exchange_side_code (s : sch_exchange_side) : SC.code :=
  match s with SchLeft => SC.CNode 0 [] | SchRight => SC.CNode 1 [] end.
Definition decode_exchange_side_code (c : SC.code) : option sch_exchange_side :=
  match c with SC.CNode 0 [] => Some SchLeft | SC.CNode 1 [] => Some SchRight | _ => None end.
Lemma decode_encode_exchange_side_code : forall s,
  decode_exchange_side_code (encode_exchange_side_code s) = Some s.
Proof. destruct s; reflexivity. Qed.

Definition encode_exchange_code (e : sch_adjacent_exchange) : SC.code :=
  SC.CNode 0 [encode_exchange_side_code (sch_exchange_side_of e);
              SC.CAtom (sch_exchange_index e)].
Definition decode_exchange_code (c : SC.code) : option sch_adjacent_exchange :=
  match c with
  | SC.CNode 0 [s; SC.CAtom i] =>
      match decode_exchange_side_code s with Some r => Some (mkSchExchange r i) | None => None end
  | _ => None
  end.
Lemma decode_encode_exchange_code : forall e,
  decode_exchange_code (encode_exchange_code e) = Some e.
Proof.
  intros [s i]. unfold encode_exchange_code, decode_exchange_code.
  rewrite decode_encode_exchange_side_code. reflexivity.
Qed.

Definition encode_exchange_list := SC.encode_code_list encode_exchange_code.
Definition decode_exchange_list := SC.decode_code_list_node decode_exchange_code.
Lemma decode_encode_exchange_list : forall es,
  decode_exchange_list (encode_exchange_list es) = Some es.
Proof. apply SC.decode_code_list_node_encode, decode_encode_exchange_code. Qed.

Fixpoint encode_open_tree_code (p : open_tree) : SC.code :=
  match p with
  | OpenHole i lbl => SC.CNode 0 [SC.CAtom i; encode_sch_sequent_code lbl]
  | OpenQAxiom A lbl => SC.CNode 1 [encode_formula_code A; encode_sch_sequent_code lbl]
  | OpenGQ w lbl ps => SC.CNode 2 [encode_sch_gq_witness_code w; encode_sch_sequent_code lbl; encode_open_forest_code ps]
  | OpenDepApp d rho lbl ps => SC.CNode 3 [encode_cert_id_code d; encode_sch_instantiation_code rho; encode_sch_sequent_code lbl; encode_open_forest_code ps]
  | OpenPerm es child lbl => SC.CNode 4 [encode_exchange_list es; encode_open_tree_code child; encode_sch_sequent_code lbl]
  end
with encode_open_forest_code (ps : open_forest) : SC.code :=
  match ps with
  | OpenNil => SC.CNode 0 []
  | OpenCons p qs => SC.CNode 1 [encode_open_tree_code p; encode_open_forest_code qs]
  end.

Fixpoint decode_open_tree_code (c : SC.code) : option open_tree :=
  match c with
  | SC.CNode 0 [SC.CAtom i; lbl] =>
      match decode_sch_sequent_code lbl with Some S0 => Some (OpenHole i S0) | None => None end
  | SC.CNode 1 [A; lbl] => omap2 OpenQAxiom (decode_formula_code A) (decode_sch_sequent_code lbl)
  | SC.CNode 2 [w; lbl; ps] => omap3 OpenGQ (decode_sch_gq_witness_code w) (decode_sch_sequent_code lbl) (decode_open_forest_code ps)
  | SC.CNode 3 [d; rho; lbl; ps] => omap4 OpenDepApp (decode_cert_id_code d) (decode_sch_instantiation_code rho) (decode_sch_sequent_code lbl) (decode_open_forest_code ps)
  | SC.CNode 4 [es; child; lbl] => omap3 OpenPerm (decode_exchange_list es) (decode_open_tree_code child) (decode_sch_sequent_code lbl)
  | _ => None
  end
with decode_open_forest_code (c : SC.code) : option open_forest :=
  match c with
  | SC.CNode 0 [] => Some OpenNil
  | SC.CNode 1 [p; ps] => omap2 OpenCons (decode_open_tree_code p) (decode_open_forest_code ps)
  | _ => None
  end.

Lemma decode_encode_open_tree_code : forall p,
  decode_open_tree_code (encode_open_tree_code p) = Some p
with decode_encode_open_forest_code : forall ps,
  decode_open_forest_code (encode_open_forest_code ps) = Some ps.
Proof.
  - intro p. destruct p as
      [index label | axiom label | rule label children |
       dependency rho label children | exchanges child label].
    + change
        (match decode_sch_sequent_code (encode_sch_sequent_code label) with
         | Some seq0 => Some (OpenHole index seq0) | None => None end =
         Some (OpenHole index label)).
      rewrite decode_encode_sch_sequent_code. reflexivity.
    + change
        (omap2 OpenQAxiom
          (decode_formula_code (encode_formula_code axiom))
          (decode_sch_sequent_code (encode_sch_sequent_code label)) =
         Some (OpenQAxiom axiom label)).
      rewrite decode_encode_formula_code, decode_encode_sch_sequent_code. reflexivity.
    + change
        (omap3 OpenGQ
          (decode_sch_gq_witness_code (encode_sch_gq_witness_code rule))
          (decode_sch_sequent_code (encode_sch_sequent_code label))
          (decode_open_forest_code (encode_open_forest_code children)) =
         Some (OpenGQ rule label children)).
      rewrite decode_encode_sch_gq_witness_code, decode_encode_sch_sequent_code,
              decode_encode_open_forest_code. reflexivity.
    + change
        (omap4 OpenDepApp
          (decode_cert_id_code (encode_cert_id_code dependency))
          (decode_sch_instantiation_code (encode_sch_instantiation_code rho))
          (decode_sch_sequent_code (encode_sch_sequent_code label))
          (decode_open_forest_code (encode_open_forest_code children)) =
         Some (OpenDepApp dependency rho label children)).
      rewrite decode_encode_cert_id_code, decode_encode_sch_instantiation_code,
              decode_encode_sch_sequent_code, decode_encode_open_forest_code.
      reflexivity.
    + change
        (omap3 OpenPerm
          (decode_exchange_list (encode_exchange_list exchanges))
          (decode_open_tree_code (encode_open_tree_code child))
          (decode_sch_sequent_code (encode_sch_sequent_code label)) =
         Some (OpenPerm exchanges child label)).
      rewrite decode_encode_exchange_list, decode_encode_open_tree_code,
              decode_encode_sch_sequent_code. reflexivity.
  - intro ps. destruct ps as [|head tail].
    + reflexivity.
    + change
        (omap2 OpenCons
          (decode_open_tree_code (encode_open_tree_code head))
          (decode_open_forest_code (encode_open_forest_code tail)) =
         Some (OpenCons head tail)).
      rewrite decode_encode_open_tree_code, decode_encode_open_forest_code. reflexivity.
Qed.

Definition encode_open_certificate_code (c : open_certificate) : SC.code :=
  SC.CNode 0 [encode_rule_scheme_code (open_certificate_root c);
              encode_open_tree_code (open_certificate_skeleton c);
              encode_cert_id_list (open_certificate_dependencies c)].
Definition decode_open_certificate_code (c : SC.code) : option open_certificate :=
  match c with
  | SC.CNode 0 [q; p; ds] =>
      omap3 mkOpenCertificate (decode_rule_scheme_code q)
        (decode_open_tree_code p) (decode_cert_id_list ds)
  | _ => None
  end.
Lemma decode_encode_open_certificate_code : forall c,
  decode_open_certificate_code (encode_open_certificate_code c) = Some c.
Proof.
  intros [q p ds]. unfold encode_open_certificate_code, decode_open_certificate_code.
  rewrite decode_encode_rule_scheme_code, decode_encode_open_tree_code,
          decode_encode_cert_id_list. reflexivity.
Qed.

Definition open_certificate_structural_codec : SC.StructuralCodec open_certificate.
Proof.
  refine {| SC.encode_code := encode_open_certificate_code;
            SC.decode_code := decode_open_certificate_code |}.
  exact decode_encode_open_certificate_code.
Defined.

(** A single natural number carries both decoder fuel and structural payload. *)

Definition pack_code (c : SC.code) : nat :=
  NC.pair_nat (S (NC.code_depth c)) (NC.encode_code_nat c).

Definition unpack_code (n : nat) : option SC.code :=
  match NC.unpair_nat n with
  | Some (fuel, payload) => NC.decode_code_nat_fuel fuel payload
  | None => None
  end.

Lemma unpack_pack_code : forall c, unpack_code (pack_code c) = Some c.
Proof.
  intro c. unfold unpack_code, pack_code. rewrite NC.unpair_pair.
  apply NC.decode_encode_code_nat_fuel.
Qed.

Definition encode_rule_scheme_nat (q : rule_scheme) : nat :=
  pack_code (encode_rule_scheme_code q).
Definition decode_rule_scheme_nat (n : nat) : option rule_scheme :=
  match unpack_code n with Some c => decode_rule_scheme_code c | None => None end.
Lemma decode_encode_rule_scheme_nat : forall q,
  decode_rule_scheme_nat (encode_rule_scheme_nat q) = Some q.
Proof.
  intro q. unfold decode_rule_scheme_nat, encode_rule_scheme_nat.
  rewrite unpack_pack_code. apply decode_encode_rule_scheme_code.
Qed.

Definition encode_open_certificate_nat (c : open_certificate) : nat :=
  pack_code (encode_open_certificate_code c).
Definition decode_open_certificate_nat (n : nat) : option open_certificate :=
  match unpack_code n with Some c => decode_open_certificate_code c | None => None end.
Lemma decode_encode_open_certificate_nat : forall c,
  decode_open_certificate_nat (encode_open_certificate_nat c) = Some c.
Proof.
  intro c. unfold decode_open_certificate_nat, encode_open_certificate_nat.
  rewrite unpack_pack_code. apply decode_encode_open_certificate_code.
Qed.

Definition GeneralPCOK_nat (n : nat) : bool :=
  match decode_open_certificate_nat n with
  | Some c => GeneralPCOK c
  | None => false
  end.

Theorem GeneralPCOK_nat_agrees : forall c,
  GeneralPCOK_nat (encode_open_certificate_nat c) = GeneralPCOK c.
Proof.
  intro c. unfold GeneralPCOK_nat. rewrite decode_encode_open_certificate_nat. reflexivity.
Qed.

(** Full-domain certificate existence and the decoded theta matrix. *)

Definition CanCert_open (k q : nat) : Prop :=
  exists c : open_certificate,
    encode_rule_scheme_nat (open_certificate_root c) = q /\
    GeneralPCOK c = true /\
    forall d, In d (open_certificate_dependencies c) -> X_stage k d.

Definition CanCert_codeb (k q n : nat) : bool :=
  match decode_open_certificate_nat n with
  | Some c =>
      Nat.eqb (encode_rule_scheme_nat (open_certificate_root c)) q &&
      GeneralPCOK c &&
      forallb (fun d => INX d k) (open_certificate_dependencies c)
  | None => false
  end.

Lemma CanCert_codeb_spec : forall k q n,
  CanCert_codeb k q n = true <->
  exists c,
    decode_open_certificate_nat n = Some c /\
    encode_rule_scheme_nat (open_certificate_root c) = q /\
    GeneralPCOK c = true /\
    forall d, In d (open_certificate_dependencies c) -> X_stage k d.
Proof.
  intros k q n. unfold CanCert_codeb.
  destruct (decode_open_certificate_nat n) as [c|] eqn:Hdec.
  - split.
    + intro H. apply andb_true_iff in H as [Hhead Hdeps].
      apply andb_true_iff in Hhead as [Hroot Hcheck].
      apply Nat.eqb_eq in Hroot. rewrite forallb_forall in Hdeps.
      exists c. repeat split; try assumption.
    + intros [c' [Hdec' [Hroot [Hcheck Hdeps]]]].
      inversion Hdec'; subst c'.
      apply andb_true_iff. split.
      * apply andb_true_iff. split; [apply Nat.eqb_eq; exact Hroot|exact Hcheck].
      * rewrite forallb_forall. intros d Hd. apply Hdeps, Hd.
  - split; [discriminate|]. intros [c [H _]]. discriminate.
Qed.

Theorem CanCert_open_is_recursively_enumerated : forall k q,
  CanCert_open k q <-> exists n, CanCert_codeb k q n = true.
Proof.
  intros k q. split.
  - intros [c [Hroot [Hcheck Hdeps]]].
    exists (encode_open_certificate_nat c). apply CanCert_codeb_spec.
    exists c. rewrite decode_encode_open_certificate_nat. repeat split; assumption.
  - intros [n Hn]. apply CanCert_codeb_spec in Hn.
    destruct Hn as [c [_ [Hroot [Hcheck Hdeps]]]].
    exists c. repeat split; assumption.
Qed.

Definition theta_open_decoded_semantics (k q : nat) : Prop :=
  exists n c ell,
    decode_open_certificate_nat n = Some c /\
    GeneralPCOK c = true /\
    encode_rule_scheme_nat (open_certificate_root c) = q /\
    length (open_certificate_dependencies c) = ell /\
    forall i, i < ell ->
      exists d, nth_error (open_certificate_dependencies c) i = Some d /\
                X_stage k d.

Theorem theta_open_decoded_represents_CanCert : forall k q,
  theta_open_decoded_semantics k q <-> CanCert_open k q.
Proof.
  intros k q. split.
  - intros [n [c [ell [_ [Hcheck [Hroot [Hlen Hindexed]]]]]]].
    exists c. split; [exact Hroot|]. split; [exact Hcheck|].
    intros d Hd. destruct (In_nth_error _ _ Hd) as [i Hi].
    assert (Hilength : i < length (open_certificate_dependencies c)).
    { apply nth_error_Some. rewrite Hi. discriminate. }
    rewrite Hlen in Hilength. destruct (Hindexed i Hilength) as [d' [Hi' HX]].
    rewrite Hi in Hi'. inversion Hi'. subst. exact HX.
  - intros [c [Hroot [Hcheck Hdeps]]].
    exists (encode_open_certificate_nat c), c,
      (length (open_certificate_dependencies c)).
    rewrite decode_encode_open_certificate_nat. repeat split; try assumption.
    intros i Hi. destruct (nth_error (open_certificate_dependencies c) i) as [d|] eqn:Hnth.
    + exists d. split; [reflexivity|]. apply Hdeps.
      apply nth_error_In with (n := i). exact Hnth.
    + exfalso. apply nth_error_None in Hnth. lia.
Qed.

Theorem theta_k_full_domain_is_N_sorted : forall k,
  formula_wtb k (theta_k k) = true.
Proof. apply theta_k_is_N_sorted. Qed.

(** The source invokes the standard arithmetical representability theorem at
    this exact boundary.  Everything below that boundary--the decoded
    relation and its equivalence with full-domain [CanCert_open]--has already
    been proved constructively above. *)
Section Arithmetic_Representability_Interface.
  Variable standard_N_satisfies_theta : nat -> nat -> Prop.
  Variable primitive_recursive_representation : forall k q,
    standard_N_satisfies_theta k q <-> theta_open_decoded_semantics k q.

  Theorem theta_standard_represents_full_CanCert : forall k q,
    standard_N_satisfies_theta k q <-> CanCert_open k q.
  Proof.
    intros k q. rewrite primitive_recursive_representation.
    apply theta_open_decoded_represents_CanCert.
  Qed.
End Arithmetic_Representability_Interface.

(** The closed certificate theory is recursively enumerable internally. *)

Definition encode_formula_nat (A : formula) : nat :=
  pack_code (encode_formula_code A).
Definition decode_formula_nat (n : nat) : option formula :=
  match unpack_code n with Some c => decode_formula_code c | None => None end.
Lemma decode_encode_formula_nat : forall A,
  decode_formula_nat (encode_formula_nat A) = Some A.
Proof.
  intro A. unfold decode_formula_nat, encode_formula_nat.
  rewrite unpack_pack_code. apply decode_encode_formula_code.
Qed.

Definition closed_rule_scheme (A : formula) : rule_scheme :=
  mkScheme 0 [] (mkSchSeq [] [SCFormula (quote_formula A)]) [].

Definition closed_open_certificate (A : formula) : open_certificate :=
  mkOpenCertificate (closed_rule_scheme A)
    (OpenQAxiom A (mkSchSeq [] [SCFormula (quote_formula A)])) [].

Lemma AxQ_qaxiomb_complete : forall A, In A AxQ -> qaxiomb A = true.
Proof.
  intros A HA. unfold AxQ in HA.
  destruct HA as [H|[H|[H|[H|[H|[H|[H|H]]]]]]];
    try contradiction; subst A; reflexivity.
Qed.

Lemma closed_Q_open_certificate_checks : forall A,
  In A AxQ -> GeneralPCOK (closed_open_certificate A) = true.
Proof.
  intros A HA. unfold AxQ in HA.
  destruct HA as [H|[H|[H|[H|[H|[H|[H|H]]]]]]];
    try contradiction; subst A; reflexivity.
Qed.

Definition T_open_closed (k : nat) (A : formula) : Prop :=
  CanCert_open k (encode_rule_scheme_nat (closed_rule_scheme A)).

Theorem checked_open_theory_extends_Robinson_Q : forall k,
  extends_Robinson_Q (T_open_closed k).
Proof.
  intros k A HA. unfold T_open_closed, CanCert_open.
  exists (closed_open_certificate A). repeat split.
  - apply closed_Q_open_certificate_checks. exact HA.
  - intros d H. contradiction.
Qed.

Definition enumerate_open_closed (k n : nat) : option formula :=
  match NC.unpair_nat n with
  | Some (formula_code, certificate_code) =>
      match decode_formula_nat formula_code with
      | Some A =>
          if CanCert_codeb k
               (encode_rule_scheme_nat (closed_rule_scheme A)) certificate_code
          then Some A else None
      | None => None
      end
  | None => None
  end.

Theorem open_closed_theory_recursively_enumerable : forall k,
  theory_recursively_enumerable (T_open_closed k).
Proof.
  intro k. exists (enumerate_open_closed k). intro A. split.
  - intro HT. unfold T_open_closed in HT.
    apply CanCert_open_is_recursively_enumerated in HT.
    destruct HT as [certificate_code Hcert].
    exists (NC.pair_nat (encode_formula_nat A) certificate_code).
    unfold enumerate_open_closed. rewrite NC.unpair_pair, decode_encode_formula_nat.
    rewrite Hcert. reflexivity.
  - intros [n Hn]. unfold enumerate_open_closed in Hn.
    destruct (NC.unpair_nat n) as [[formula_code certificate_code]|] eqn:Hpair;
      try discriminate.
    destruct (decode_formula_nat formula_code) as [B|] eqn:Hformula;
      try discriminate.
    destruct (CanCert_codeb k
      (encode_rule_scheme_nat (closed_rule_scheme B)) certificate_code) eqn:Hcert;
      try discriminate.
    inversion Hn; subst B. unfold T_open_closed.
    apply CanCert_open_is_recursively_enumerated. exists certificate_code. exact Hcert.
Qed.

Section Full_EUQ_Interface.
  Variable external_EUQ_full : forall T : formula -> Prop,
    theory_consistent T ->
    theory_recursively_enumerable T ->
    extends_Robinson_Q T ->
    ~ exists decide : formula -> bool,
        forall A, decide A = true <-> T A.

  Theorem no_total_same_layer_open_certificate_decider : forall k,
    theory_consistent (T_open_closed k) ->
    ~ exists decide : nat -> bool,
        forall q, decide q = true <-> CanCert_open k q.
  Proof.
    intros k Hconsistent [decide Hdecide].
    apply (@external_EUQ_full (T_open_closed k) Hconsistent
      (open_closed_theory_recursively_enumerable k)
      (checked_open_theory_extends_Robinson_Q k)).
    exists (fun A => decide (encode_rule_scheme_nat (closed_rule_scheme A))).
    intro A. apply Hdecide.
  Qed.
End Full_EUQ_Interface.
