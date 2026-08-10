(*
  Faithful Rocq formalization of
  "040 — 自问句的层级呼吸：密封许可证呼吸演算 BRC-HL".

  Source:
  0.我的问题和知识库/3. Idea/3.1 Philosophy/logic/1. 未完成/
  1884 自问句的层级呼吸-成品形式系统.md

  The source works in ZFC and fixes an admissible coding gamma.  Here the
  finite-tree syntax is represented by inductive types.  The restrictions
  defining RawSent and RawExpr are predicates on those ambient finite trees.
  This mirrors "least finite-tree closure" without admitting ill-closed Ev
  nodes into RawSent.
*)

From Stdlib Require Import
  List
  Arith
  Bool
  Lia
  PeanoNat
  Program.Equality
  Classical_Prop.

Import ListNotations.
Set Implicit Arguments.
Set Asymmetric Patterns.

Module BRC_HL.

Definition var := nat.

(* Sections 1--2: the eight object-language function symbols, with their
   arities made intrinsic by the constructors. *)
Inductive tm : Type :=
| TVar : var -> tm
| TZero : tm
| TSucc : tm -> tm
| TAdd : tm -> tm -> tm
| TMul : tm -> tm -> tm
| TNum : tm -> tm
| TSub : tm -> tm -> tm -> tm
| TD : tm -> tm
| TU : tm -> tm.

Inductive sent : Type :=
| SEq : tm -> tm -> sent
| SSeen : tm -> sent
| SProbe : tm -> sent
| SCert : nat -> tm -> tm -> tm -> tm -> tm -> tm -> sent
| SNeg : sent -> sent
| SAnd : sent -> sent -> sent
| SAll : var -> sent -> sent
| SEv : sent -> sent.

Inductive expr : Type :=
| ESent : sent -> expr
| EAsk : expr -> expr.

Scheme tm_ind' := Induction for tm Sort Prop.
Scheme sent_ind' := Induction for sent Sort Prop.
Scheme expr_ind' := Induction for expr Sort Prop.

Fixpoint tm_eq_dec (t u : tm) : {t = u} + {t <> u}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Fixpoint sent_eq_dec (A B : sent) : {A = B} + {A <> B}.
Proof. decide equality; apply tm_eq_dec || apply Nat.eq_dec. Defined.

Fixpoint expr_eq_dec (e f : expr) : {e = f} + {e <> f}.
Proof. decide equality; apply sent_eq_dec. Defined.

Definition memb (x : nat) (xs : list nat) : bool :=
  existsb (Nat.eqb x) xs.

Definition union (xs ys : list nat) : list nat :=
  nodup Nat.eq_dec (xs ++ ys).

Fixpoint unions (xss : list (list nat)) : list nat :=
  match xss with
  | [] => []
  | xs :: rest => union xs (unions rest)
  end.

Fixpoint fv_tm (t : tm) : list var :=
  match t with
  | TVar x => [x]
  | TZero => []
  | TSucc u | TNum u | TD u | TU u => fv_tm u
  | TAdd u v | TMul u v => union (fv_tm u) (fv_tm v)
  | TSub u v z => unions [fv_tm u; fv_tm v; fv_tm z]
  end.

Definition allvars_tm (t : tm) : list var := fv_tm t.

Fixpoint fv_sent (A : sent) : list var :=
  match A with
  | SEq t u => union (fv_tm t) (fv_tm u)
  | SSeen t | SProbe t => fv_tm t
  | SCert _ t0 t1 t2 t3 t4 t5 =>
      unions [fv_tm t0; fv_tm t1; fv_tm t2;
              fv_tm t3; fv_tm t4; fv_tm t5]
  | SNeg B => fv_sent B
  | SAnd B C => union (fv_sent B) (fv_sent C)
  | SAll x B => remove Nat.eq_dec x (fv_sent B)
  | SEv _ => []
  end.

Fixpoint bv_sent (A : sent) : list var :=
  match A with
  | SEq _ _ | SSeen _ | SProbe _ | SCert _ _ _ _ _ _ _ => []
  | SNeg B => bv_sent B
  | SAnd B C => union (bv_sent B) (bv_sent C)
  | SAll x B => union [x] (bv_sent B)
  | SEv _ => []
  end.

Definition allvars_sent (A : sent) : list var :=
  union (fv_sent A) (bv_sent A).

Fixpoint fv_expr (e : expr) : list var :=
  match e with
  | ESent A => fv_sent A
  | EAsk f => fv_expr f
  end.

Fixpoint bv_expr (e : expr) : list var :=
  match e with
  | ESent A => bv_sent A
  | EAsk f => bv_expr f
  end.

Definition closed_tm (t : tm) : Prop := fv_tm t = [].
Definition closed_sent (A : sent) : Prop := fv_sent A = [].
Definition closed_expr (e : expr) : Prop := fv_expr e = [].

(* RawSent is the subset in which every quotation body is itself RawSent and
   is closed.  Other constructors merely recurse. *)
Fixpoint raw_sent (A : sent) : Prop :=
  match A with
  | SEq _ _ | SSeen _ | SProbe _ | SCert _ _ _ _ _ _ _ => True
  | SNeg B => raw_sent B
  | SAnd B C => raw_sent B /\ raw_sent C
  | SAll _ B => raw_sent B
  | SEv B => raw_sent B /\ closed_sent B
  end.

Fixpoint raw_expr (e : expr) : Prop :=
  match e with
  | ESent A => raw_sent A
  | EAsk f => raw_expr f
  end.

Definition simp (A B : sent) : sent := SNeg (SAnd A (SNeg B)).
Definition sor (A B : sent) : sent := SNeg (SAnd (SNeg A) (SNeg B)).
Definition siff (A B : sent) : sent := SAnd (simp A B) (simp B A).
Definition sexists (x : var) (A : sent) : sent := SNeg (SAll x (SNeg A)).

Definition stop : sent := SEq TZero TZero.
Definition delta : sent := SProbe TZero.

Fixpoint numeral (n : nat) : tm :=
  match n with
  | 0 => TZero
  | S k => TSucc (numeral k)
  end.

(* Section 3.  Simultaneous finite substitutions let the quantifier case make
   exactly one structural recursive call.  The one-variable operation below
   has the source clauses.  In the collision branch the fresh name avoids both
   FV and BV of the body; this is the harmless strengthening needed to make
   the source's intended capture avoidance literal at nested binders. *)
Definition subst_env := list (var * tm).

Fixpoint lookup_subst (x : var) (env : subst_env) : option tm :=
  match env with
  | [] => None
  | (y,t) :: env' =>
      if Nat.eq_dec x y then Some t else lookup_subst x env'
  end.

Fixpoint remove_subst (x : var) (env : subst_env) : subst_env :=
  match env with
  | [] => []
  | (y,t) :: env' =>
      if Nat.eq_dec x y then remove_subst x env'
      else (y,t) :: remove_subst x env'
  end.

Fixpoint subst_tm_env (env : subst_env) (t : tm) : tm :=
  match t with
  | TVar x =>
      match lookup_subst x env with
      | Some u => u
      | None => TVar x
      end
  | TZero => TZero
  | TSucc u => TSucc (subst_tm_env env u)
  | TAdd u v => TAdd (subst_tm_env env u) (subst_tm_env env v)
  | TMul u v => TMul (subst_tm_env env u) (subst_tm_env env v)
  | TNum u => TNum (subst_tm_env env u)
  | TSub u v z =>
      TSub (subst_tm_env env u) (subst_tm_env env v) (subst_tm_env env z)
  | TD u => TD (subst_tm_env env u)
  | TU u => TU (subst_tm_env env u)
  end.

Definition subst_tm (t : tm) (x : var) (u : tm) : tm :=
  subst_tm_env [(x,u)] t.

Fixpoint fv_subst_env (env : subst_env) : list var :=
  match env with
  | [] => []
  | (_,t) :: env' => union (fv_tm t) (fv_subst_env env')
  end.

Fixpoint dom_subst_env (env : subst_env) : list var :=
  match env with
  | [] => []
  | (x,_) :: env' => union [x] (dom_subst_env env')
  end.

Fixpoint max_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (max_list xs')
  end.

Fixpoint first_missing (fuel start : nat) (xs : list nat) : nat :=
  match fuel with
  | 0 => start
  | S fuel' =>
      if in_dec Nat.eq_dec start xs
      then first_missing fuel' (S start) xs
      else start
  end.

Definition fresh (xs : list nat) : nat :=
  first_missing (S (max_list xs)) 0 xs.

Fixpoint subst_sent_env (env : subst_env) (A : sent) : sent :=
  match A with
  | SEq t u => SEq (subst_tm_env env t) (subst_tm_env env u)
  | SSeen t => SSeen (subst_tm_env env t)
  | SProbe t => SProbe (subst_tm_env env t)
  | SCert n t0 t1 t2 t3 t4 t5 =>
      SCert n
        (subst_tm_env env t0) (subst_tm_env env t1)
        (subst_tm_env env t2) (subst_tm_env env t3)
        (subst_tm_env env t4) (subst_tm_env env t5)
  | SNeg B => SNeg (subst_sent_env env B)
  | SAnd B C => SAnd (subst_sent_env env B) (subst_sent_env env C)
  | SAll y B =>
      let env' := remove_subst y env in
      if memb y (fv_subst_env env') then
        let z :=
          fresh (allvars_sent B ++ fv_subst_env env' ++
                 dom_subst_env env' ++ [y]) in
        SAll z (subst_sent_env ((y,TVar z) :: env') B)
      else
        SAll y (subst_sent_env env' B)
  | SEv B => SEv B
  end.

Definition subst_sent (A : sent) (x : var) (u : tm) : sent :=
  subst_sent_env [(x,u)] A.

Fixpoint subst_expr_env (env : subst_env) (e : expr) : expr :=
  match e with
  | ESent A => ESent (subst_sent_env env A)
  | EAsk f => EAsk (subst_expr_env env f)
  end.

Definition subst_expr (e : expr) (x : var) (u : tm) : expr :=
  subst_expr_env [(x,u)] e.

Definition free_ren (e : expr) (x y : var) : expr :=
  subst_expr e x (TVar y).

Definition bound_ren (x y : var) (A : sent) : sent :=
  SAll y (subst_sent A x (TVar y)).

Inductive alpha_sent : sent -> sent -> Prop :=
| AlphaRefl : forall A, alpha_sent A A
| AlphaSym : forall A B, alpha_sent A B -> alpha_sent B A
| AlphaTrans : forall A B C,
    alpha_sent A B -> alpha_sent B C -> alpha_sent A C
| AlphaBound : forall x y A,
    ~ In y (remove Nat.eq_dec x (fv_sent A)) ->
    alpha_sent (SAll x A) (bound_ren x y A)
| AlphaNeg : forall A B,
    alpha_sent A B -> alpha_sent (SNeg A) (SNeg B)
| AlphaAnd : forall A A' B B',
    alpha_sent A A' -> alpha_sent B B' ->
    alpha_sent (SAnd A B) (SAnd A' B')
| AlphaAll : forall x A B,
    alpha_sent A B -> alpha_sent (SAll x A) (SAll x B)
| AlphaEv : forall A B,
    alpha_sent A B -> alpha_sent (SEv A) (SEv B).

Inductive alpha_expr : expr -> expr -> Prop :=
| AlphaExprSent : forall A B,
    alpha_sent A B -> alpha_expr (ESent A) (ESent B)
| AlphaExprAsk : forall e f,
    alpha_expr e f -> alpha_expr (EAsk e) (EAsk f)
| AlphaExprRefl : forall e, alpha_expr e e
| AlphaExprSym : forall e f, alpha_expr e f -> alpha_expr f e
| AlphaExprTrans : forall e f g,
    alpha_expr e f -> alpha_expr f g -> alpha_expr e g.

Fixpoint qdepth (e : expr) : nat :=
  match e with
  | ESent _ => 0
  | EAsk f => S (qdepth f)
  end.

Fixpoint askn (n : nat) (e : expr) : expr :=
  match n with
  | 0 => e
  | S k => EAsk (askn k e)
  end.

(* Section 4: sealed-license automaton and formation. *)
Inductive letter : Type := La | Lb.

Inductive license_state : Type :=
| St0 | Sta | Stb | Stab | Stba.

Definition license_step (s : license_state) (a : letter) : license_state :=
  match s, a with
  | St0, La => Sta
  | St0, Lb => Stb
  | Sta, La => Stba
  | Sta, Lb => Stab
  | Stb, _ => Stba
  | Stab, _ => Stab
  | Stba, _ => Stba
  end.

Definition word := list letter.

Definition run_license_from (s : license_state) (w : word) : license_state :=
  fold_left license_step w s.

Definition run_license (w : word) : license_state :=
  run_license_from St0 w.

Definition grant (w : word) : Prop := run_license w = Stab.

Lemma run_ab : run_license [La; Lb] = Stab.
Proof. reflexivity. Qed.

Lemma run_ba : run_license [Lb; La] = Stba.
Proof. reflexivity. Qed.

Lemma Stab_absorbing : forall u,
    run_license_from Stab u = Stab.
Proof.
  induction u as [|a u IHu].
  - reflexivity.
  - cbn. exact IHu.
Qed.

Lemma Stba_absorbing : forall u,
    run_license_from Stba u = Stba.
Proof.
  induction u as [|a u IHu].
  - reflexivity.
  - cbn. exact IHu.
Qed.

Fixpoint formed_sent (w : word) (A : sent) : Prop :=
  match A with
  | SEq _ _ | SSeen _ | SCert _ _ _ _ _ _ _ => True
  | SProbe _ => grant w
  | SNeg B => formed_sent w B
  | SAnd B C => formed_sent w B /\ formed_sent w C
  | SAll _ B => formed_sent w B
  | SEv B => formed_sent w B /\ closed_sent B
  end.

Fixpoint formed_expr (w : word) (e : expr) : Prop :=
  match e with
  | ESent A => raw_sent A /\ formed_sent w A
  | EAsk f => formed_expr w f
  end.

Fixpoint rank (A : sent) : nat :=
  match A with
  | SEq _ _ | SCert _ _ _ _ _ _ _ => 0
  | SSeen _ | SProbe _ => 1
  | SNeg B => rank B
  | SAnd B C => Nat.max (rank B) (rank C)
  | SAll _ B => rank B
  | SEv B => S (rank B)
  end.

(* Sections 5 and 8 use the same four-field events. *)
Record event : Type := Event {
  event_id : nat;
  event_key : nat;
  event_answer : bool;
  event_proof : nat
}.

Definition hist := list event.
Definition keys (h : hist) : list nat := map event_key h.
Definition valuation := var -> nat.
Definition zero_val : valuation := fun _ => 0.

Definition update_val (s : valuation) (x : var) (n : nat) : valuation :=
  fun y => if Nat.eq_dec y x then n else s y.

(* Section 1 fixes one admissible gamma on a disjoint union.  A Rocq record is
   the direct expression of that explicit ambient choice.  Each restriction
   comes with its partial inverse and injectivity evidence. *)
Inductive ftree : Type :=
| FNode : nat -> list ftree -> ftree.

Inductive coded_object : Type :=
| COTm : tm -> coded_object
| COExpr : expr -> coded_object
| COHist : hist -> coded_object
| COWord : word -> coded_object
| COSeq : list nat -> coded_object
| COTree : ftree -> coded_object.

Record admissible_coding : Type := Coding {
  code_object : coded_object -> nat;
  code_object_inj :
    forall x y, code_object x = code_object y -> x = y;

  code_tm : tm -> nat;
  code_tm_agrees : forall t, code_tm t = code_object (COTm t);
  decode_tm : nat -> option tm;
  decode_code_tm : forall t, decode_tm (code_tm t) = Some t;
  decode_tm_sound :
    forall n t, decode_tm n = Some t -> n = code_tm t;
  code_tm_inj : forall t u, code_tm t = code_tm u -> t = u;

  code_expr : expr -> nat;
  code_expr_agrees : forall e, code_expr e = code_object (COExpr e);
  decode_expr : nat -> option expr;
  decode_code_expr : forall e, decode_expr (code_expr e) = Some e;
  decode_expr_sound :
    forall n e, decode_expr n = Some e -> n = code_expr e;
  code_expr_inj : forall e f, code_expr e = code_expr f -> e = f;

  code_hist : hist -> nat;
  code_hist_agrees : forall h, code_hist h = code_object (COHist h);
  decode_hist : nat -> option hist;
  decode_code_hist : forall h, decode_hist (code_hist h) = Some h;
  decode_hist_sound :
    forall n h, decode_hist n = Some h -> n = code_hist h;
  code_hist_inj : forall h k, code_hist h = code_hist k -> h = k;

  code_word : word -> nat;
  code_word_agrees : forall w, code_word w = code_object (COWord w);
  decode_word : nat -> option word;
  decode_code_word : forall w, decode_word (code_word w) = Some w;
  decode_word_sound :
    forall n w, decode_word n = Some w -> n = code_word w;
  code_word_inj : forall w u, code_word w = code_word u -> w = u;

  code_seq : list nat -> nat;
  code_seq_agrees : forall xs, code_seq xs = code_object (COSeq xs);
  decode_seq : nat -> option (list nat);
  decode_code_seq : forall xs, decode_seq (code_seq xs) = Some xs;
  decode_seq_sound :
    forall n xs, decode_seq n = Some xs -> n = code_seq xs;
  code_seq_inj : forall xs ys, code_seq xs = code_seq ys -> xs = ys;

  code_tree : ftree -> nat;
  code_tree_agrees : forall t, code_tree t = code_object (COTree t);
  decode_tree : nat -> option ftree;
  decode_code_tree : forall t, decode_tree (code_tree t) = Some t;
  decode_tree_sound :
    forall n t, decode_tree n = Some t -> n = code_tree t;
  code_tree_inj : forall t u, code_tree t = code_tree u -> t = u
}.

Section WithCoding.
Context (coding : admissible_coding).

Definition num_meta (n : nat) : nat :=
  code_tm coding (numeral n).

Definition sub_meta (m i n : nat) : nat :=
  match decode_expr coding m, decode_tm coding n with
  | Some e, Some t => code_expr coding (subst_expr e i t)
  | _, _ => 0
  end.

Definition d_meta (m : nat) : nat :=
  sub_meta m 0 (num_meta m).

Definition u_meta (m : nat) : nat :=
  match decode_expr coding m with
  | Some e => code_expr coding (EAsk e)
  | None => 0
  end.

Fixpoint val_tm (t : tm) (s : valuation) : nat :=
  match t with
  | TVar x => s x
  | TZero => 0
  | TSucc u => S (val_tm u s)
  | TAdd u v => val_tm u s + val_tm v s
  | TMul u v => val_tm u s * val_tm v s
  | TNum u => num_meta (val_tm u s)
  | TSub u v z => sub_meta (val_tm u s) (val_tm v s) (val_tm z s)
  | TD u => d_meta (val_tm u s)
  | TU u => u_meta (val_tm u s)
  end.

Lemma val_numeral : forall n s, val_tm (numeral n) s = n.
Proof.
  induction n as [|n IHn]; intros s.
  - reflexivity.
  - cbn. rewrite IHn. reflexivity.
Qed.

Definition jud (w : word) (l : nat) (A : sent) : Prop :=
  raw_sent A /\ formed_sent w A /\ rank A <= l.

(* Section 6.1: precisely the twelve displayed static axiom families. *)
Inductive axiom : sent -> Prop :=
| Ax1 : forall A B,
    raw_sent A -> raw_sent B ->
    axiom (simp A (simp B A))
| Ax2 : forall A B C,
    raw_sent A -> raw_sent B -> raw_sent C ->
    axiom
      (simp (simp A (simp B C))
        (simp (simp A B) (simp A C)))
| Ax3 : forall A B,
    raw_sent A -> raw_sent B ->
    axiom (simp (simp (SNeg A) (SNeg B)) (simp B A))
| AxAnd1 : forall A B,
    raw_sent A -> raw_sent B ->
    axiom (simp (SAnd A B) A)
| AxAnd2 : forall A B,
    raw_sent A -> raw_sent B ->
    axiom (simp (SAnd A B) B)
| AxAnd3 : forall A B,
    raw_sent A -> raw_sent B ->
    axiom (simp A (simp B (SAnd A B)))
| AxDN : forall A,
    raw_sent A ->
    axiom (simp A (SNeg (SNeg A)))
| AxAll1 : forall x A t,
    raw_sent A ->
    axiom (simp (SAll x A) (subst_sent A x t))
| AxAll2 : forall x A B,
    raw_sent A -> raw_sent B ->
    ~ In x (fv_sent A) ->
    axiom (simp (SAll x (simp A B)) (simp A (SAll x B)))
| AxEq1 : forall t,
    axiom (SEq t t)
| AxEq2 : forall x A t u,
    raw_sent A ->
    axiom
      (simp (SEq t u)
        (simp (subst_sent A x t) (subst_sent A x u)))
| AxNat : forall t u,
    closed_tm t -> closed_tm u ->
    val_tm t zero_val = val_tm u zero_val ->
    axiom (SEq t u).

(* Section 6.4: fixed-arity constructors are a canonical presentation of the
   finite nonempty ordered trees whose rule labels have arities 0, 1, or 2. *)
Inductive proof_tree : Type :=
| PTAx : nat -> sent -> proof_tree
| PTSeenPos : nat -> tm -> proof_tree
| PTSeenNeg : nat -> tm -> proof_tree
| PTProbe : nat -> tm -> proof_tree
| PTMP : nat -> sent -> sent -> proof_tree -> proof_tree -> proof_tree
| PTGen : nat -> var -> sent -> proof_tree -> proof_tree
| PTAlpha : nat -> sent -> sent -> proof_tree -> proof_tree
| PTEvPos : nat -> sent -> proof_tree -> proof_tree
| PTEvNeg : nat -> sent -> proof_tree -> proof_tree.

Definition conclusion (pi : proof_tree) : nat * sent :=
  match pi with
  | PTAx l A => (l,A)
  | PTSeenPos l t => (l,SSeen t)
  | PTSeenNeg l t => (l,SNeg (SSeen t))
  | PTProbe l t => (l,SProbe t)
  | PTMP l _ B _ _ => (l,B)
  | PTGen l x A _ => (l,SAll x A)
  | PTAlpha l _ B _ => (l,B)
  | PTEvPos k A _ => (S k,SEv A)
  | PTEvNeg k A _ => (S k,SNeg (SEv A))
  end.

Fixpoint valid_proof (h : hist) (w : word) (pi : proof_tree) : Prop :=
  match pi with
  | PTAx l A =>
      jud w l A /\ axiom A
  | PTSeenPos l t =>
      jud w l (SSeen t) /\
      closed_tm t /\
      In (val_tm t zero_val) (keys h)
  | PTSeenNeg l t =>
      jud w l (SNeg (SSeen t)) /\
      closed_tm t /\
      ~ In (val_tm t zero_val) (keys h)
  | PTProbe l t =>
      jud w l (SProbe t) /\
      closed_tm t /\
      val_tm t zero_val = 0
  | PTMP l A B pA pImp =>
      jud w l B /\
      conclusion pA = (l,A) /\
      conclusion pImp = (l,simp A B) /\
      valid_proof h w pA /\
      valid_proof h w pImp
  | PTGen l x A p =>
      jud w l (SAll x A) /\
      conclusion p = (l,A) /\
      valid_proof h w p
  | PTAlpha l A B p =>
      jud w l A /\
      jud w l B /\
      alpha_sent A B /\
      conclusion p = (l,A) /\
      valid_proof h w p
  | PTEvPos k A p =>
      jud w k A /\
      jud w (S k) (SEv A) /\
      conclusion p = (k,A) /\
      valid_proof h w p
  | PTEvNeg k A p =>
      jud w k (SNeg A) /\
      jud w (S k) (SNeg (SEv A)) /\
      conclusion p = (k,SNeg A) /\
      valid_proof h w p
  end.

Definition proves (l : nat) (h : hist) (w : word)
    (pi : proof_tree) (A : sent) : Prop :=
  valid_proof h w pi /\ conclusion pi = (l,A).

Definition tag_code (pi : proof_tree) : nat :=
  match pi with
  | PTAx _ _ => 0 | PTSeenPos _ _ => 1 | PTSeenNeg _ _ => 2
  | PTProbe _ _ => 3 | PTMP _ _ _ _ _ => 4 | PTGen _ _ _ _ => 5
  | PTAlpha _ _ _ _ => 6 | PTEvPos _ _ _ => 7 | PTEvNeg _ _ _ => 8
  end.

Fixpoint proof_as_tree (pi : proof_tree) : ftree :=
  let '(l,A) := conclusion pi in
  let header :=
    [FNode l []; FNode (code_expr coding (ESent A)) []] in
  match pi with
  | PTAx _ _ | PTSeenPos _ _ | PTSeenNeg _ _ | PTProbe _ _ =>
      FNode (tag_code pi) header
  | PTMP _ _ _ p q =>
      FNode (tag_code pi) (header ++ [proof_as_tree p; proof_as_tree q])
  | PTGen _ _ _ p | PTAlpha _ _ _ p
  | PTEvPos _ _ p | PTEvNeg _ _ p =>
      FNode (tag_code pi) (header ++ [proof_as_tree p])
  end.

Definition proof_code (pi : proof_tree) : nat :=
  code_tree coding (proof_as_tree pi).

Fixpoint neg_support (pi : proof_tree) : list nat :=
  match pi with
  | PTSeenNeg _ t => [val_tm t zero_val]
  | PTMP _ _ _ p q => union (neg_support p) (neg_support q)
  | PTGen _ _ _ p | PTAlpha _ _ _ p
  | PTEvPos _ _ p | PTEvNeg _ _ p => neg_support p
  | _ => []
  end.

Definition bool_code (b : bool) : nat := if b then 1 else 0.

(* Section 7's closed administrative formula NoCert_n. *)
Definition no_cert_formula
    (n l : nat) (h : hist) (w : word) (e : expr) : sent :=
  let v0 := TVar 0 in
  let v1 := TVar 1 in
  let isbit := sor (SEq v0 TZero) (SEq v0 (TSucc TZero)) in
  let atom :=
    SCert n
      (numeral l)
      (numeral (code_hist coding h))
      (numeral (code_word coding w))
      (numeral (code_expr coding e))
      v0 v1 in
  SAll 0 (SAll 1 (SNeg (SAnd isbit atom))).

Definition trace_code
    (n : nat) (e : expr) (b : bool) (p : nat) : option nat :=
  match n, e with
  | 0, ESent _ => Some p
  | S k, EAsk f =>
      if b then
        match decode_seq coding p with
        | Some [b0;p0;w0] =>
            if (Nat.eqb b0 0 || Nat.eqb b0 1)%bool
            then Some (code_seq coding [1;b0;p0;w0])
            else None
        | _ => None
        end
      else Some (code_seq coding [0;p])
  | _, _ => None
  end.

Fixpoint cert
    (n l : nat) (h : hist) (w : word)
    (e : expr) (b : bool) (p : nat) : Prop :=
  match n, e with
  | 0, ESent A =>
      if b then
        exists pi, proves l h w pi A /\ p = proof_code pi
      else
        exists pi, proves l h w pi (SNeg A) /\ p = proof_code pi
  | S k, EAsk f =>
      if b then
        exists b0 p0 tr,
          cert k l h w f b0 p0 /\
          trace_code k f b0 p0 = Some tr /\
          p = code_seq coding [bool_code b0;p0;tr]
      else
        exists pi,
          proves l h w pi (no_cert_formula k l h w f) /\
          p = proof_code pi
  | _, _ => False
  end.

Definition answer_cert
    (l : nat) (h : hist) (w : word)
    (e : expr) (b : bool) (p : nat) : Prop :=
  cert (qdepth e) l h w e b p.

(* Section 5: the partial domain is kept separate from the recursive truth
   clauses.  Administrative atoms decode the three gamma-coded arguments. *)
Fixpoint sat
    (l : nat) (h : hist) (w : word)
    (s : valuation) (A : sent) : Prop :=
  match A with
  | SEq t u => val_tm t s = val_tm u s
  | SSeen t => 1 <= l /\ In (val_tm t s) (keys h)
  | SProbe t => 1 <= l /\ grant w /\ val_tm t s = 0
  | SCert n t0 t1 t2 t3 t4 t5 =>
      match
        decode_hist coding (val_tm t1 s),
        decode_word coding (val_tm t2 s),
        decode_expr coding (val_tm t3 s)
      with
      | Some h', Some w', Some e' =>
          match val_tm t4 s with
          | 0 =>
              cert n (val_tm t0 s) h' w' e' false (val_tm t5 s)
          | 1 =>
              cert n (val_tm t0 s) h' w' e' true (val_tm t5 s)
          | _ => False
          end
      | _, _, _ => False
      end
  | SNeg B => ~ sat l h w s B
  | SAnd B C => sat l h w s B /\ sat l h w s C
  | SAll x B => forall n, sat l h w (update_val s x n) B
  | SEv B => rank B + 1 <= l /\ sat (Nat.pred l) h w zero_val B
  end.

Definition models
    (l : nat) (h : hist) (w : word) (s : valuation) (A : sent) : Prop :=
  raw_sent A /\ formed_sent w A /\ rank A <= l /\ sat l h w s A.

Definition models_closed
    (l : nat) (h : hist) (w : word) (A : sent) : Prop :=
  models l h w zero_val A.

Lemma base_state_models_stop :
  models_closed 0 [] [] stop.
Proof.
  unfold models_closed, models.
  cbn [stop raw_sent formed_sent rank sat val_tm zero_val].
  repeat split; try exact I; try reflexivity; lia.
Qed.

Lemma base_state_refutes_negated_stop :
  ~ models_closed 0 [] [] (SNeg stop).
Proof.
  unfold models_closed, models.
  cbn [stop raw_sent formed_sent rank sat val_tm zero_val].
  intros [_ [_ [_ Hnot]]].
  apply Hnot. reflexivity.
Qed.

Theorem hierarchical_semantics_nontrivial :
  models_closed 0 [] [] stop /\
  ~ models_closed 0 [] [] (SNeg stop).
Proof.
  split.
  - exact base_state_models_stop.
  - exact base_state_refutes_negated_stop.
Qed.

(* Sections 8--9: frames, configurations, the ten labelled rules, and runs. *)
Inductive frame : Type :=
| FOrd : nat -> expr -> nat -> frame
| FLic : nat -> nat -> letter -> nat -> frame.

Inductive current : Type :=
| CurExpr : expr -> current
| CurAns : bool -> nat -> current
| CurRet : expr -> bool -> nat -> event -> current.

Record conf : Type := Conf {
  level_of : nat;
  hist_of : hist;
  stack_of : list frame;
  current_of : current;
  word_of : word
}.

Definition frame_numbers (f : frame) : list nat :=
  match f with
  | FOrd a _ _ => [a]
  | FLic a _ _ nu => [a;nu]
  end.

Definition used_numbers (h : hist) (sigma : list frame) : list nat :=
  map event_id h ++ flat_map frame_numbers sigma.

Definition fresh_id (h : hist) (sigma : list frame) : nat :=
  match used_numbers h sigma with
  | [] => 0
  | xs => S (max_list xs)
  end.

Definition top_public : nat := 20.
Definition top_a : nat := 21.
Definition top_b : nat := 22.

Definition license_proof (a : letter) : nat :=
  match a with La => top_a | Lb => top_b end.

Definition erase_license_proof (_ : letter) : nat := top_public.
Definition erased_event_proof : nat := code_seq coding [top_public].

Inductive action : Type :=
| ActUP | ActCertS | ActCertQPos | ActCertQNeg | ActDOWN
| ActLUP : letter -> action
| ActLCert : letter -> action
| ActLDOWN : letter -> action
| ActREASK | ActTRY.

Inductive step : action -> conf -> conf -> Prop :=
| StepUP : forall l h sigma w e a,
    formed_expr w e ->
    a = fresh_id h sigma ->
    step ActUP
      (Conf l h sigma (CurExpr (EAsk e)) w)
      (Conf (S l) h (sigma ++ [FOrd a e l]) (CurExpr e) w)
| StepCertS : forall l h pre w a A p b,
    1 <= l ->
    answer_cert l h w (ESent A) b p ->
    step ActCertS
      (Conf l h (pre ++ [FOrd a (ESent A) (Nat.pred l)])
        (CurExpr (ESent A)) w)
      (Conf l h (pre ++ [FOrd a (ESent A) (Nat.pred l)])
        (CurAns b p) w)
| StepCertQPos : forall l h pre w a e b0 p0 r0 tr,
    1 <= l ->
    answer_cert l h w e b0 p0 ->
    trace_code (qdepth e) e b0 p0 = Some tr ->
    step ActCertQPos
      (Conf l h (pre ++ [FOrd a (EAsk e) (Nat.pred l)])
        (CurRet e b0 p0 r0) w)
      (Conf l h (pre ++ [FOrd a (EAsk e) (Nat.pred l)])
        (CurAns true (code_seq coding [bool_code b0;p0;tr])) w)
| StepCertQNeg : forall l h pre w a e p,
    1 <= l ->
    answer_cert l h w (EAsk e) false p ->
    step ActCertQNeg
      (Conf l h (pre ++ [FOrd a (EAsk e) (Nat.pred l)])
        (CurExpr (EAsk e)) w)
      (Conf l h (pre ++ [FOrd a (EAsk e) (Nat.pred l)])
        (CurAns false p) w)
| StepDOWN : forall k h pre w a e b p r,
    answer_cert (S k) h w e b p ->
    r = Event a (code_expr coding (EAsk e)) b p ->
    step ActDOWN
      (Conf (S k) h (pre ++ [FOrd a e k]) (CurAns b p) w)
      (Conf k (h ++ [r]) pre (CurRet e b p r) w)
| StepLUP : forall l h sigma w a lam,
    a = fresh_id h sigma ->
    step (ActLUP lam)
      (Conf l h sigma (CurExpr (EAsk (ESent stop))) w)
      (Conf (S l) h
        (sigma ++ [FLic a l lam a]) (CurExpr (ESent stop)) w)
| StepLCert : forall l h pre w a lam,
    step (ActLCert lam)
      (Conf (S l) h (pre ++ [FLic a l lam a])
        (CurExpr (ESent stop)) w)
      (Conf (S l) h (pre ++ [FLic a l lam a])
        (CurAns true (license_proof lam)) w)
| StepLDOWN : forall k h pre w a lam r,
    r = Event a (code_expr coding (EAsk (ESent stop)))
          true erased_event_proof ->
    step (ActLDOWN lam)
      (Conf (S k) h (pre ++ [FLic a k lam a])
        (CurAns true (license_proof lam)) w)
      (Conf k (h ++ [r]) pre
        (CurRet (ESent stop) true top_public r) (w ++ [lam]))
| StepREASK : forall k h w e b p r,
    step ActREASK
      (Conf k h [] (CurRet e b p r) w)
      (Conf k h [] (CurExpr (EAsk (ESent stop))) w)
| StepTRY : forall k h w a,
    formed_sent w delta ->
    a = fresh_id h [] ->
    step ActTRY
      (Conf k h [] (CurExpr (EAsk (ESent stop))) w)
      (Conf (S k) h [FOrd a (ESent delta) k]
        (CurExpr (ESent delta)) w).

Inductive run : conf -> list action -> conf -> Prop :=
| RunNil : forall C, run C [] C
| RunCons : forall C D E a acts,
    step a C D -> run D acts E -> run C (a :: acts) E.

Lemma run_app : forall C xs D ys E,
    run C xs D -> run D ys E -> run C (xs ++ ys) E.
Proof.
  intros C xs D ys E Hxs Hys.
  induction Hxs.
  - exact Hys.
  - cbn. eapply RunCons; eauto.
Qed.

Definition reaches (C D : conf) : Prop := exists acts, run C acts D.

Definition down_weight (a : action) : nat :=
  match a with ActDOWN | ActLDOWN _ => 1 | _ => 0 end.

Definition ldown_weight (a : action) : nat :=
  match a with ActLDOWN _ => 1 | _ => 0 end.

Definition count_weight (f : action -> nat) (acts : list action) : nat :=
  fold_right (fun a n => f a + n) 0 acts.

Lemma count_weight_app : forall f xs ys,
    count_weight f (xs ++ ys) =
      count_weight f xs + count_weight f ys.
Proof.
  intros f xs ys.
  induction xs as [|x xs IH].
  - cbn [count_weight]. reflexivity.
  - unfold count_weight in *.
    cbn. rewrite IH. apply Nat.add_assoc.
Qed.

Lemma count_weight_cons : forall f a xs,
    count_weight f (a :: xs) = f a + count_weight f xs.
Proof. reflexivity. Qed.

Lemma count_weight_nil : forall f, count_weight f [] = 0.
Proof. reflexivity. Qed.

Definition balanced_from (k : nat) (C : conf) : Prop :=
  level_of C = k + length (stack_of C).

Lemma step_preserves_balance : forall k a C D,
    balanced_from k C -> step a C D -> balanced_from k D.
Proof.
  intros k a C D Hbal Hstep.
  destruct Hstep; unfold balanced_from in *; cbn in *.
  - rewrite length_app. cbn. lia.
  - exact Hbal.
  - exact Hbal.
  - exact Hbal.
  - rewrite length_app in Hbal. cbn in Hbal. lia.
  - rewrite length_app. cbn. lia.
  - exact Hbal.
  - rewrite length_app in Hbal. cbn in Hbal. lia.
  - exact Hbal.
  - cbn. lia.
Qed.

Lemma B3_run_level_invariant : forall k C acts D,
    balanced_from k C -> run C acts D -> balanced_from k D.
Proof.
  intros k C acts D Hbal Hrun.
  induction Hrun.
  - exact Hbal.
  - apply IHHrun. eapply step_preserves_balance; eauto.
Qed.

Lemma step_history_length : forall a C D,
    step a C D ->
    length (hist_of D) = length (hist_of C) + down_weight a.
Proof.
  intros a C D H.
  destruct H; cbn; try lia; rewrite length_app; cbn; lia.
Qed.

Lemma step_word_length : forall a C D,
    step a C D ->
    length (word_of D) = length (word_of C) + ldown_weight a.
Proof.
  intros a C D H.
  destruct H; cbn; try lia; rewrite length_app; cbn; lia.
Qed.

Lemma B3_run_history_count : forall C acts D,
    run C acts D ->
    length (hist_of D) =
      length (hist_of C) + count_weight down_weight acts.
Proof.
  intros C acts D Hrun.
  unfold count_weight.
  induction Hrun.
  - cbn. lia.
  - cbn. pose proof (step_history_length H) as Hlen. lia.
Qed.

Lemma H2_run_license_count : forall C acts D,
    run C acts D ->
    length (word_of D) =
      length (word_of C) + count_weight ldown_weight acts.
Proof.
  intros C acts D Hrun.
  unfold count_weight.
  induction Hrun.
  - cbn. lia.
  - cbn. pose proof (step_word_length H) as Hlen. lia.
Qed.

Lemma step_history_prefix : forall a C D,
    step a C D -> exists suffix, hist_of D = hist_of C ++ suffix.
Proof.
  intros a C D H.
  destruct H; cbn; try (exists []; now rewrite app_nil_r).
  - exists [r]. reflexivity.
  - exists [r]. reflexivity.
Qed.

Lemma step_word_prefix : forall a C D,
    step a C D -> exists suffix, word_of D = word_of C ++ suffix.
Proof.
  intros a C D H.
  destruct H; cbn; try (exists []; now rewrite app_nil_r).
  exists [lam]. reflexivity.
Qed.

Lemma B3_run_history_prefix : forall C acts D,
    run C acts D -> exists suffix, hist_of D = hist_of C ++ suffix.
Proof.
  intros C acts D Hrun.
  induction Hrun.
  - exists []; now rewrite app_nil_r.
  - destruct (step_history_prefix H) as [s1 Hs1].
    destruct IHHrun as [s2 Hs2].
    exists (s1 ++ s2). rewrite Hs2, Hs1, app_assoc. reflexivity.
Qed.

Lemma H2_run_word_prefix : forall C acts D,
    run C acts D -> exists suffix, word_of D = word_of C ++ suffix.
Proof.
  intros C acts D Hrun.
  induction Hrun.
  - exists []; now rewrite app_nil_r.
  - destruct (step_word_prefix H) as [s1 Hs1].
    destruct IHHrun as [s2 Hs2].
    exists (s1 ++ s2). rewrite Hs2, Hs1, app_assoc. reflexivity.
Qed.

Fixpoint positive_actions (n : nat) : list action :=
  match n with
  | 0 => []
  | 1 => [ActUP;ActCertS;ActDOWN]
  | S k => ActUP :: positive_actions k ++ [ActCertQPos;ActDOWN]
  end.

Definition action_is_up (a : action) : nat :=
  match a with ActUP => 1 | _ => 0 end.
Definition action_is_certs (a : action) : nat :=
  match a with ActCertS => 1 | _ => 0 end.
Definition action_is_certqpos (a : action) : nat :=
  match a with ActCertQPos => 1 | _ => 0 end.

Lemma B5_positive_witness_count : forall n,
    1 <= n ->
    count_weight action_is_up (positive_actions n) = n /\
    count_weight action_is_certqpos (positive_actions n) = n - 1 /\
    count_weight action_is_certs (positive_actions n) = 1 /\
    count_weight down_weight (positive_actions n) = n.
Proof.
  induction n as [|n IHn]; intro Hn.
  - lia.
  - destruct n as [|n].
    + cbn [count_weight]. repeat split; lia.
    + assert (1 <= S n) by lia.
      specialize (IHn H).
      destruct IHn as [Hu [Hq [Hs Hd]]].
      change
        (count_weight action_is_up
           (ActUP :: positive_actions (S n) ++
             [ActCertQPos;ActDOWN]) = S (S n) /\
         count_weight action_is_certqpos
           (ActUP :: positive_actions (S n) ++
             [ActCertQPos;ActDOWN]) = S (S n) - 1 /\
         count_weight action_is_certs
           (ActUP :: positive_actions (S n) ++
             [ActCertQPos;ActDOWN]) = 1 /\
         count_weight down_weight
           (ActUP :: positive_actions (S n) ++
             [ActCertQPos;ActDOWN]) = S (S n)).
      repeat split.
      * rewrite count_weight_cons, count_weight_app.
        change (1 + (count_weight action_is_up
          (positive_actions (S n)) + 0) = S (S n)).
        rewrite Hu. lia.
      * rewrite count_weight_cons, count_weight_app.
        change (0 + (count_weight action_is_certqpos
          (positive_actions (S n)) + 1) = S (S n) - 1).
        rewrite Hq. lia.
      * rewrite count_weight_cons, count_weight_app.
        change (0 + (count_weight action_is_certs
          (positive_actions (S n)) + 0) = 1).
        rewrite Hs. lia.
      * rewrite count_weight_cons, count_weight_app.
        change (0 + (count_weight down_weight
          (positive_actions (S n)) + 1) = S (S n)).
        rewrite Hd. lia.
Qed.

(* The four-step license macro and the two concrete noncommuting paths. *)
Definition license_event (C : conf) : event :=
  Event (fresh_id (hist_of C) (stack_of C))
    (code_expr coding (EAsk (ESent stop))) true erased_event_proof.

Definition license_breath (C : conf) (lam : letter) : conf :=
  Conf (level_of C)
    (hist_of C ++ [license_event C])
    (stack_of C)
    (CurExpr (EAsk (ESent stop)))
    (word_of C ++ [lam]).

Definition root_conf : conf :=
  Conf 0 [] [] (CurExpr (EAsk (ESent stop))) [].

Definition C_ab : conf := license_breath (license_breath root_conf La) Lb.
Definition C_ba : conf := license_breath (license_breath root_conf Lb) La.

Lemma license_breath_run : forall k h w lam,
    let C := Conf k h [] (CurExpr (EAsk (ESent stop))) w in
    run C [ActLUP lam; ActLCert lam; ActLDOWN lam; ActREASK]
      (license_breath C lam).
Proof.
  intros k h w lam C.
  unfold license_breath, license_event, C.
  eapply RunCons.
  - apply StepLUP. reflexivity.
  - eapply RunCons.
    + apply StepLCert.
    + eapply RunCons.
      * apply StepLDOWN. reflexivity.
      * eapply RunCons.
        -- apply StepREASK.
        -- apply RunNil.
Qed.

Lemma C_ab_actual_run :
    exists acts, run root_conf acts C_ab.
Proof.
  unfold C_ab.
  pose proof (license_breath_run 0 [] [] La) as Ha.
  pose proof
    (license_breath_run 0 [license_event root_conf] [La] Lb) as Hb.
  exists
    ([ActLUP La;ActLCert La;ActLDOWN La;ActREASK] ++
     [ActLUP Lb;ActLCert Lb;ActLDOWN Lb;ActREASK]).
  eapply run_app.
  - exact Ha.
  - exact Hb.
Qed.

Lemma C_ba_actual_run :
    exists acts, run root_conf acts C_ba.
Proof.
  unfold C_ba.
  pose proof (license_breath_run 0 [] [] Lb) as Hb.
  pose proof
    (license_breath_run 0 [license_event root_conf] [Lb] La) as Ha.
  exists
    ([ActLUP Lb;ActLCert Lb;ActLDOWN Lb;ActREASK] ++
     [ActLUP La;ActLCert La;ActLDOWN La;ActREASK]).
  eapply run_app.
  - exact Hb.
  - exact Ha.
Qed.

(* Sections 10--11: public projection and the two observation relations. *)
Fixpoint public_sent (A : sent) : Prop :=
  match A with
  | SEq _ _ | SSeen _ => True
  | SProbe _ | SCert _ _ _ _ _ _ _ => False
  | SNeg B => public_sent B
  | SAnd B C => public_sent B /\ public_sent C
  | SAll _ B | SEv B => public_sent B
  end.

Inductive public_frame : Type :=
| PFOrd : nat -> expr -> nat -> public_frame
| PFLic : nat -> nat -> nat -> public_frame.

Definition project_frame (f : frame) : public_frame :=
  match f with
  | FOrd a e k => PFOrd a e k
  | FLic a k _ nu => PFLic a k nu
  end.

Inductive public_current : Type :=
| PCExpr : expr -> public_current
| PCAns : bool -> nat -> public_current
| PCRet : expr -> bool -> nat -> event -> public_current.

Definition project_proof (p : nat) : nat :=
  if Nat.eq_dec p top_a then top_public
  else if Nat.eq_dec p top_b then top_public
  else p.

Definition project_current (x : current) : public_current :=
  match x with
  | CurExpr e => PCExpr e
  | CurAns b p => PCAns b (project_proof p)
  | CurRet e b p r => PCRet e b p r
  end.

Record public_conf : Type := PublicConf {
  public_level : nat;
  public_hist : hist;
  public_stack : list public_frame;
  public_object : public_current;
  public_word_length : nat
}.

Definition pub (C : conf) : public_conf :=
  PublicConf
    (level_of C)
    (hist_of C)
    (map project_frame (stack_of C))
    (project_current (current_of C))
    (length (word_of C)).

Definition approx0 (C D : conf) : Prop :=
  pub C = pub D /\
  forall A,
    raw_sent A ->
    public_sent A ->
    closed_sent A ->
    (models_closed (level_of C) (hist_of C) (word_of C) A <->
     models_closed (level_of D) (hist_of D) (word_of D) A).

Definition surface (C : conf) : Prop := stack_of C = [].

Definition approx_future (C D : conf) : Prop :=
  surface C /\ surface D /\
  forall u e,
    (formed_expr (word_of C ++ u) e <->
     formed_expr (word_of D ++ u) e).

Definition approx_safe (C D : conf) : Prop :=
  approx0 C D /\ approx_future C D.

Lemma formed_public_word_irrelevant : forall A,
    public_sent A ->
    forall w u, (formed_sent w A <-> formed_sent u A).
Proof.
  induction A; cbn; intros Hpub w u.
  - tauto.
  - tauto.
  - contradiction.
  - contradiction.
  - specialize (IHA Hpub w u). tauto.
  - destruct Hpub as [HB HC].
    specialize (IHA1 HB w u).
    specialize (IHA2 HC w u). tauto.
  - apply IHA. exact Hpub.
  - specialize (IHA Hpub w u). tauto.
Qed.

Lemma sat_public_word_irrelevant : forall A,
    public_sent A ->
    forall l h s w u, (sat l h w s A <-> sat l h u s A).
Proof.
  induction A; cbn; intros Hpub l h s w u.
  - tauto.
  - tauto.
  - contradiction.
  - contradiction.
  - specialize (IHA Hpub l h s w u). tauto.
  - destruct Hpub as [HB HC].
    specialize (IHA1 HB l h s w u).
    specialize (IHA2 HC l h s w u). tauto.
  - split; intros Hall n.
    + apply (proj1 (IHA Hpub l h (update_val s v n) w u)).
      apply Hall.
    + apply (proj2 (IHA Hpub l h (update_val s v n) w u)).
      apply Hall.
  - specialize (IHA Hpub (Nat.pred l) h zero_val w u). tauto.
Qed.

Lemma models_public_word_irrelevant : forall A,
    public_sent A ->
    forall l h s w u, (models l h w s A <-> models l h u s A).
Proof.
  intros A Hpub l h s w u.
  unfold models.
  pose proof (formed_public_word_irrelevant A Hpub w u) as Hform.
  pose proof (sat_public_word_irrelevant A Hpub l h s w u) as Hsat.
  tauto.
Qed.

Lemma C_ab_public_components :
    pub C_ab = pub C_ba.
Proof.
  unfold C_ab, C_ba, license_breath, license_event, root_conf, pub.
  cbn [fresh_id used_numbers frame_numbers max_list].
  reflexivity.
Qed.

Lemma H3_current_invisibility : approx0 C_ab C_ba.
Proof.
  split.
  - apply C_ab_public_components.
  - intros A Hraw Hpub Hclosed.
    unfold models_closed.
    unfold C_ab, C_ba, license_breath, license_event, root_conf.
    cbn [fresh_id used_numbers frame_numbers max_list].
    apply models_public_word_irrelevant. exact Hpub.
Qed.

Lemma ab_grants : grant [La;Lb].
Proof. reflexivity. Qed.

Lemma ba_rejects : ~ grant [Lb;La].
Proof. discriminate. Qed.

Lemma H4_ab_forms_delta : formed_expr [La;Lb] (ESent delta).
Proof. cbn. split; [exact I | reflexivity]. Qed.

Lemma H4_ba_does_not_form_delta :
    ~ formed_expr [Lb;La] (ESent delta).
Proof. cbn. intros [_ H]. discriminate. Qed.

Lemma H4_noncommuting_future_formation :
    ~ approx_future C_ab C_ba.
Proof.
  intros [_ [_ Hfuture]].
  specialize (Hfuture [] (ESent delta)).
  rewrite !app_nil_r in Hfuture.
  unfold C_ab, C_ba, license_breath, root_conf in Hfuture.
  cbn in Hfuture.
  apply H4_ba_does_not_form_delta.
  apply (proj1 Hfuture).
  exact H4_ab_forms_delta.
Qed.

Definition enabled (a : action) (C : conf) : Prop :=
  exists D, step a C D.

Lemma H5_try_enabled_ab : enabled ActTRY C_ab.
Proof.
  unfold enabled, C_ab, license_breath, root_conf.
  eexists. apply StepTRY.
  - cbn. exact (proj2 H4_ab_forms_delta).
  - reflexivity.
Qed.

Lemma H5_try_disabled_ba : ~ enabled ActTRY C_ba.
Proof.
  intros [D Hstep].
  inversion Hstep; subst.
  apply H4_ba_does_not_form_delta.
  cbn. split; [exact I |].
  match goal with
  | Hform : formed_sent _ delta |- _ =>
      cbn in Hform; exact Hform
  end.
Qed.

Theorem H5_current_quotient_obstruction :
    approx0 C_ab C_ba /\
    enabled ActTRY C_ab /\
    ~ enabled ActTRY C_ba.
Proof.
  split.
  - exact H3_current_invisibility.
  - split.
    + exact H5_try_enabled_ab.
    + exact H5_try_disabled_ba.
Qed.

(* A transparent target includes the enabledness and matching-successor halves
   of observation congruence from section 11. *)
Record transparent_target : Type := Target {
  target_state : Type;
  target_action : Type;
  target_step : target_action -> target_state -> target_state -> Prop;
  target_language : Type;
  target_models : target_state -> target_language -> Prop;
  target_obs_congruence_enabled :
    forall x y,
      (forall A, target_models x A <-> target_models y A) ->
      forall a,
        ((exists x', target_step a x x') <->
         (exists y', target_step a y y'));
  target_obs_congruence_forth :
    forall x y,
      (forall A, target_models x A <-> target_models y A) ->
      forall a x',
        target_step a x x' ->
        exists y', target_step a y y' /\
          (forall A, target_models x' A <-> target_models y' A);
  target_obs_congruence_back :
    forall x y,
      (forall A, target_models x A <-> target_models y A) ->
      forall a y',
        target_step a y y' ->
        exists x', target_step a x x' /\
          (forall A, target_models x' A <-> target_models y' A)
}.

Definition target_obs_equiv (M : transparent_target)
    (x y : target_state M) : Prop :=
  forall A, target_models M x A <-> target_models M y A.

Record faithful_translation (M : transparent_target) : Type := Translation {
  translate_conf : conf -> target_state M;
  translate_action : action -> target_action M;
  translation_current_full_abstraction :
    forall C D,
      approx0 C D <->
      target_obs_equiv M (translate_conf C) (translate_conf D);
  translation_step_exact :
    forall a C D,
      step a C D <->
      target_step M (translate_action a)
        (translate_conf C) (translate_conf D);
  translation_try_enabled_exact :
    forall C,
      enabled ActTRY C <->
      exists y,
        target_step M (translate_action ActTRY) (translate_conf C) y
}.

Definition translate_trace {M : transparent_target}
    (T : faithful_translation M) (acts : list action) :
    list (target_action M) :=
  map (translate_action T) acts.

Lemma translate_trace_composes : forall M
    (T : faithful_translation M) xs ys,
    translate_trace T (xs ++ ys) =
      translate_trace T xs ++ translate_trace T ys.
Proof. intros. apply map_app. Qed.

Theorem H6_no_faithful_transparent_translation :
    forall M : transparent_target, faithful_translation M -> False.
Proof.
  intros M T.
  pose proof
    (proj1 (translation_current_full_abstraction T C_ab C_ba)
      H3_current_invisibility) as Hobs.
  pose proof
    (target_obs_congruence_enabled M
      (translate_conf T C_ab) (translate_conf T C_ba)
      Hobs (translate_action T ActTRY)) as Henabled.
  apply H5_try_disabled_ba.
  apply (proj2 (translation_try_enabled_exact T C_ba)).
  apply (proj1 Henabled).
  apply (proj1 (translation_try_enabled_exact T C_ab)).
  exact H5_try_enabled_ab.
Qed.

Lemma ba_extension_rejects : forall u,
    ~ grant ([Lb;La] ++ u).
Proof.
  intros u Hgrant.
  unfold grant, run_license in Hgrant.
  change (run_license_from St0 ([Lb;La] ++ u) = Stab) in Hgrant.
  unfold run_license_from in Hgrant.
  rewrite fold_left_app in Hgrant.
  cbn in Hgrant.
  change (run_license_from Stba u = Stab) in Hgrant.
  rewrite Stba_absorbing in Hgrant.
  discriminate.
Qed.

Definition instantiate_code (A : sent) (x : var) (n : nat) : sent :=
  subst_sent A x (numeral n).

Inductive interface_kind : Type :=
| IKDom
| IKTr.

Definition tagged_interface_instance
    (D T : sent) (x : var) (e : expr) (i : interface_kind) : sent :=
  match i with
  | IKDom => instantiate_code D x (code_expr coding e)
  | IKTr => instantiate_code T x (code_expr coding e)
  end.

Definition interface_required
    (C : conf) (e : expr) (i : interface_kind) : Prop :=
  raw_expr e /\
  match i, e with
  | IKDom, _ => True
  | IKTr, ESent A => formed_sent (word_of C) A
  | IKTr, EAsk _ => False
  end.

Record future_domain_interface : Type := FutureInterface {
  dom_var : var;
  dom_formula : sent;
  truth_formula : sent;
  certificate_map :
    hist -> word -> expr -> interface_kind -> option nat;
  dom_is_public : public_sent dom_formula;
  truth_is_public : public_sent truth_formula;
  dom_free_vars :
    forall y, In y (fv_sent dom_formula) -> y = dom_var;
  truth_free_vars :
    forall y, In y (fv_sent truth_formula) -> y = dom_var;
  interface_nonleakage :
    forall C D e i,
      approx0 C D ->
      (models_closed (level_of C) (hist_of C) (word_of C)
        (tagged_interface_instance
          dom_formula truth_formula dom_var e i) <->
       models_closed (level_of D) (hist_of D) (word_of D)
        (tagged_interface_instance
          dom_formula truth_formula dom_var e i));
  dom_future_complete :
    forall C e,
      raw_expr e ->
      surface C ->
      (models_closed (level_of C) (hist_of C) (word_of C)
        (instantiate_code dom_formula dom_var (code_expr coding e)) <->
       exists u, formed_expr (word_of C ++ u) e);
  truth_correct :
    forall C A,
      raw_sent A ->
      surface C ->
      formed_sent (word_of C) A ->
      (models_closed (level_of C) (hist_of C) (word_of C)
        (instantiate_code truth_formula dom_var
          (code_expr coding (ESent A))) <->
       models_closed (level_of C) (hist_of C) (word_of C) A);
  certificate_map_covers_required_instances :
    forall C e i,
      surface C ->
      interface_required C e i ->
      exists b p,
        certificate_map (hist_of C) (word_of C) e i = Some p /\
        answer_cert (level_of C) (hist_of C) (word_of C)
          (ESent (tagged_interface_instance
            dom_formula truth_formula dom_var e i)) b p /\
        (b = true <->
         models_closed (level_of C) (hist_of C) (word_of C)
           (tagged_interface_instance
             dom_formula truth_formula dom_var e i));
  interface_return_persistent_dom :
    forall C acts D e,
      run C acts D ->
      surface C ->
      surface D ->
      level_of C = level_of D ->
      (models_closed (level_of C) (hist_of C) (word_of C)
        (instantiate_code dom_formula dom_var (code_expr coding e)) <->
       models_closed (level_of D) (hist_of D) (word_of D)
        (instantiate_code dom_formula dom_var (code_expr coding e)));
  interface_return_persistent_truth :
    forall C acts D e,
      run C acts D ->
      surface C ->
      surface D ->
      level_of C = level_of D ->
      (models_closed (level_of C) (hist_of C) (word_of C)
        (instantiate_code truth_formula dom_var (code_expr coding e)) <->
       models_closed (level_of D) (hist_of D) (word_of D)
        (instantiate_code truth_formula dom_var (code_expr coding e)));
  interface_return_persistent_certificate :
    forall C acts D e i b p,
      run C acts D ->
      surface C ->
      surface D ->
      level_of C = level_of D ->
      certificate_map (hist_of C) (word_of C) e i = Some p ->
      answer_cert (level_of C) (hist_of C) (word_of C)
        (ESent (tagged_interface_instance
          dom_formula truth_formula dom_var e i)) b p ->
      certificate_map (hist_of D) (word_of D) e i = Some p /\
      answer_cert (level_of D) (hist_of D) (word_of D)
        (ESent (tagged_interface_instance
          dom_formula truth_formula dom_var e i)) b p
}.

Theorem H7_no_future_domain_truth_interface :
    future_domain_interface -> False.
Proof.
  intros I.
  pose proof
    (interface_nonleakage I
      (C:=C_ab) (D:=C_ba) (ESent delta) IKDom
      H3_current_invisibility) as Hsame.
  assert (Hrawdelta : raw_expr (ESent delta)).
  { split; exact delta_raw. }
  pose proof
    (dom_future_complete I (C:=C_ab) (ESent delta)
      Hrawdelta eq_refl) as Hab.
  pose proof
    (dom_future_complete I (C:=C_ba) (ESent delta)
      Hrawdelta eq_refl) as Hba.
  assert (Eab : exists u, formed_expr (word_of C_ab ++ u) (ESent delta)).
  {
    exists [].
    rewrite app_nil_r.
    unfold C_ab, license_breath, root_conf. cbn.
    exact H4_ab_forms_delta.
  }
  assert (Enba :
    ~ exists u, formed_expr (word_of C_ba ++ u) (ESent delta)).
  {
    intros [u Hu].
    unfold C_ba, license_breath, root_conf in Hu.
    cbn in Hu.
    apply (ba_extension_rejects (u:=u)).
    exact (proj2 Hu).
  }
  apply Enba.
  apply (proj1 Hba).
  apply (proj1 Hsame).
  apply (proj2 Hab).
  exact Eab.
Qed.

(* Sections 12--13.1: the self-scar sentence and the residual flip. *)
Definition theta : sent :=
  SNeg (SSeen (TU (TD (TVar 0)))).

Definition theta_code : nat :=
  code_expr coding (ESent theta).

Definition beta : sent :=
  subst_sent theta 0 (numeral theta_code).

Definition beta_term : tm :=
  TU (TD (numeral theta_code)).

Definition c_beta : nat :=
  code_expr coding (EAsk (ESent beta)).

Lemma fv_numeral : forall n, fv_tm (numeral n) = [].
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn. exact IH.
Qed.

Lemma beta_shape : beta = SNeg (SSeen beta_term).
Proof. reflexivity. Qed.

Lemma d_theta_equation :
    d_meta theta_code = code_expr coding (ESent beta).
Proof.
  unfold d_meta, sub_meta, num_meta, theta_code, beta.
  rewrite decode_code_expr, decode_code_tm.
  reflexivity.
Qed.

Lemma u_d_theta_equation :
    u_meta (d_meta theta_code) = c_beta.
Proof.
  rewrite d_theta_equation.
  unfold u_meta, c_beta.
  rewrite decode_code_expr.
  reflexivity.
Qed.

Lemma beta_term_value : forall s,
    val_tm beta_term s = c_beta.
Proof.
  intro s.
  unfold beta_term.
  cbn [val_tm].
  rewrite val_numeral.
  apply u_d_theta_equation.
Qed.

Lemma beta_rank : rank beta = 1.
Proof. rewrite beta_shape. reflexivity. Qed.

Lemma beta_closed : closed_sent beta.
Proof.
  rewrite beta_shape.
  unfold closed_sent, beta_term. cbn.
  apply fv_numeral.
Qed.

Lemma beta_term_closed : closed_tm beta_term.
Proof.
  unfold closed_tm, beta_term. cbn.
  apply fv_numeral.
Qed.

Lemma beta_raw : raw_sent beta.
Proof. rewrite beta_shape. exact I. Qed.

Lemma beta_formed : forall w, formed_sent w beta.
Proof. intro w. rewrite beta_shape. exact I. Qed.

Definition beta_positive_tree : proof_tree :=
  PTSeenNeg 1 beta_term.

Lemma beta_positive_proof : forall h w,
    ~ In c_beta (keys h) ->
    proves 1 h w beta_positive_tree beta.
Proof.
  intros h w Habsent.
  unfold proves, beta_positive_tree.
  split.
  - cbn [valid_proof jud].
    repeat split.
    + exact (Nat.le_refl 1).
    + apply beta_term_closed.
    + rewrite beta_term_value. exact Habsent.
  - rewrite beta_shape. reflexivity.
Qed.

Definition beta_return_event (h : hist) (a p : nat) : event :=
  Event a c_beta true p.

Definition beta_after (h : hist) (a p : nat) : hist :=
  h ++ [beta_return_event h a p].

Lemma beta_key_after : forall h a p,
    In c_beta (keys (beta_after h a p)).
Proof.
  intros h a p.
  unfold beta_after, beta_return_event, keys.
  rewrite map_app. cbn. apply in_or_app. right. cbn. tauto.
Qed.

Definition beta_seen_tree : proof_tree :=
  PTSeenPos 1 beta_term.

Definition beta_dn_tree : proof_tree :=
  PTAx 1 (simp (SSeen beta_term)
    (SNeg (SNeg (SSeen beta_term)))).

Definition beta_negative_tree : proof_tree :=
  PTMP 1 (SSeen beta_term)
    (SNeg (SNeg (SSeen beta_term)))
    beta_seen_tree beta_dn_tree.

Lemma beta_seen_proof_after : forall h w a p,
    proves 1 (beta_after h a p) w beta_seen_tree (SSeen beta_term).
Proof.
  intros h w a p.
  unfold proves, beta_seen_tree.
  split.
  - cbn [valid_proof jud].
    repeat split.
    + exact (Nat.le_refl 1).
    + apply beta_term_closed.
    + rewrite beta_term_value. apply beta_key_after.
  - reflexivity.
Qed.

Lemma beta_dn_axiom_proof : forall h w,
    proves 1 h w beta_dn_tree
      (simp (SSeen beta_term)
        (SNeg (SNeg (SSeen beta_term)))).
Proof.
  intros h w.
  unfold proves, beta_dn_tree.
  split.
  - cbn [valid_proof jud].
    split.
    + unfold jud. cbn.
      repeat split; try exact I.
      exact (Nat.le_refl 1).
    + apply AxDN. exact I.
  - reflexivity.
Qed.

Lemma beta_negative_proof_after : forall h w a p,
    proves 1 (beta_after h a p) w beta_negative_tree (SNeg beta).
Proof.
  intros h w a p.
  unfold beta_negative_tree.
  pose proof (beta_seen_proof_after h w a p) as Hseen.
  pose proof (beta_dn_axiom_proof (beta_after h a p) w) as Hdn.
  destruct Hseen as [Vseen Cseen].
  destruct Hdn as [Vdn Cdn].
  unfold proves.
  split.
  - cbn [valid_proof].
    split.
    + unfold jud. cbn.
      repeat split; try exact I.
      exact (Nat.le_refl 1).
    + split; [exact Cseen |].
      split; [exact Cdn |].
      split; [exact Vseen | exact Vdn].
  - rewrite beta_shape. reflexivity.
Qed.

Lemma old_positive_tree_rejected_after : forall h w a p,
    ~ valid_proof (beta_after h a p) w beta_positive_tree.
Proof.
  intros h w a p Hvalid.
  unfold beta_positive_tree in Hvalid.
  cbn [valid_proof] in Hvalid.
  destruct Hvalid as [_ [_ Hnot]].
  rewrite beta_term_value in Hnot.
  apply Hnot. apply beta_key_after.
Qed.

Lemma proof_as_tree_seen_neg_inv : forall pi l t,
    proof_as_tree pi = proof_as_tree (PTSeenNeg l t) ->
    pi = PTSeenNeg l t.
Proof.
  intros pi l t Htree.
  destruct pi; cbn in Htree; try discriminate.
  injection Htree as Hheaders.
  inversion Hheaders; subst.
  match goal with
  | Hcode :
      code_expr coding (ESent (SNeg (SSeen ?u))) =
      code_expr coding (ESent (SNeg (SSeen ?v))) |- _ =>
      apply code_expr_inj in Hcode; inversion Hcode; subst; reflexivity
  end.
Qed.

Lemma proof_code_seen_neg_inv : forall pi l t,
    proof_code pi = proof_code (PTSeenNeg l t) ->
    pi = PTSeenNeg l t.
Proof.
  intros pi l t Hcode.
  unfold proof_code in Hcode.
  apply code_tree_inj in Hcode.
  apply proof_as_tree_seen_neg_inv. exact Hcode.
Qed.

Lemma old_positive_code_rejected_after : forall h w a p,
    ~ answer_cert 1 (beta_after h a p) w
        (ESent beta) true (proof_code beta_positive_tree).
Proof.
  intros h w a p Hold.
  unfold answer_cert in Hold.
  cbn [qdepth cert] in Hold.
  destruct Hold as [pi [[V C] Hcode]].
  assert (Hpi : pi = beta_positive_tree).
  {
    apply proof_code_seen_neg_inv.
    symmetry. exact Hcode.
  }
  subst pi.
  apply (@old_positive_tree_rejected_after h w a p).
  exact V.
Qed.

Theorem B6_two_breath_flip : forall h w a p,
    ~ In c_beta (keys h) ->
    proves 1 h w beta_positive_tree beta /\
    proves 1 (beta_after h a p) w beta_negative_tree (SNeg beta) /\
    ~ answer_cert 1 (beta_after h a p) w
        (ESent beta) true (proof_code beta_positive_tree).
Proof.
  intros h w a p Habsent.
  split.
  - apply beta_positive_proof. exact Habsent.
  - split.
    + apply beta_negative_proof_after.
    + apply old_positive_code_rejected_after.
Qed.

Lemma beta_positive_answer_cert : forall h w,
    ~ In c_beta (keys h) ->
    answer_cert 1 h w (ESent beta) true
      (proof_code beta_positive_tree).
Proof.
  intros h w Habsent.
  unfold answer_cert. cbn [qdepth cert].
  exists beta_positive_tree. split.
  - apply beta_positive_proof. exact Habsent.
  - reflexivity.
Qed.

Lemma beta_negative_answer_cert_after : forall h w a p,
    answer_cert 1 (beta_after h a p) w (ESent beta) false
      (proof_code beta_negative_tree).
Proof.
  intros h w a p.
  unfold answer_cert. cbn [qdepth cert].
  exists beta_negative_tree. split.
  - apply beta_negative_proof_after.
  - reflexivity.
Qed.

Definition beta_query_conf (h : hist) (w : word) : conf :=
  Conf 0 h [] (CurExpr (EAsk (ESent beta))) w.

Definition beta_breath_return
    (h : hist) (w : word) (a : nat) (b : bool) (p : nat) : conf :=
  let r := Event a c_beta b p in
  Conf 0 (h ++ [r]) [] (CurRet (ESent beta) b p r) w.

Lemma beta_positive_breath_run : forall h w,
    ~ In c_beta (keys h) ->
    let a := fresh_id h [] in
    let p := proof_code beta_positive_tree in
    run (beta_query_conf h w)
      [ActUP;ActCertS;ActDOWN]
      (beta_breath_return h w a true p).
Proof.
  intros h w Habsent. cbn zeta.
  unfold beta_query_conf, beta_breath_return.
  eapply RunCons.
  - eapply StepUP.
    + split; [apply beta_raw | apply beta_formed].
    + reflexivity.
  - eapply RunCons.
    + eapply (StepCertS (l := 1)
        h [] w (fresh_id h []) beta
        (proof_code beta_positive_tree) true).
      * lia.
      * apply beta_positive_answer_cert. exact Habsent.
    + eapply RunCons.
      * eapply (@StepDOWN 0
          h [] w (fresh_id h []) (ESent beta) true
          (proof_code beta_positive_tree)
          (Event (fresh_id h []) c_beta true
            (proof_code beta_positive_tree))).
        -- apply beta_positive_answer_cert. exact Habsent.
        -- unfold c_beta. reflexivity.
      * apply RunNil.
Qed.

Lemma beta_negative_breath_run_after : forall h w a p,
    let h' := beta_after h a p in
    let a' := fresh_id h' [] in
    let p' := proof_code beta_negative_tree in
    run (beta_query_conf h' w)
      [ActUP;ActCertS;ActDOWN]
      (beta_breath_return h' w a' false p').
Proof.
  intros h w a p. cbn zeta.
  unfold beta_query_conf, beta_breath_return.
  eapply RunCons.
  - eapply StepUP.
    + split; [apply beta_raw | apply beta_formed].
    + reflexivity.
  - eapply RunCons.
    + eapply (StepCertS (l := 1)
        (beta_after h a p) [] w (fresh_id (beta_after h a p) [])
        beta (proof_code beta_negative_tree) false).
      * lia.
      * apply beta_negative_answer_cert_after.
    + eapply RunCons.
      * eapply (@StepDOWN 0
          (beta_after h a p) [] w
          (fresh_id (beta_after h a p) []) (ESent beta) false
          (proof_code beta_negative_tree)
          (Event (fresh_id (beta_after h a p) []) c_beta false
            (proof_code beta_negative_tree))).
        -- apply beta_negative_answer_cert_after.
        -- unfold c_beta. reflexivity.
      * apply RunNil.
Qed.

Theorem B6_two_actual_breaths_flip : forall h w,
    ~ In c_beta (keys h) ->
    let a := fresh_id h [] in
    let p := proof_code beta_positive_tree in
    let h' := beta_after h a p in
    let a' := fresh_id h' [] in
    let p' := proof_code beta_negative_tree in
    run (beta_query_conf h w)
      [ActUP;ActCertS;ActDOWN]
      (beta_breath_return h w a true p) /\
    run (beta_query_conf h' w)
      [ActUP;ActCertS;ActDOWN]
      (beta_breath_return h' w a' false p') /\
    ~ answer_cert 1 h' w (ESent beta) true p.
Proof.
  intros h w Habsent. cbn zeta.
  split.
  - apply beta_positive_breath_run. exact Habsent.
  - split.
    + apply beta_negative_breath_run_after.
    + apply old_positive_code_rejected_after.
Qed.

Lemma beta_truth_characterization : forall h w,
    (models_closed 1 h w beta <-> ~ In c_beta (keys h)).
Proof.
  intros h w.
  unfold models_closed, models.
  rewrite beta_shape.
  cbn [sat].
  rewrite beta_term_value.
  split.
  - intros [_ [_ [_ Hnot]]] Hin.
    apply Hnot. split; [lia | exact Hin].
  - intro Habsent.
    repeat split.
    + exact (Nat.le_refl 1).
    + intros [_ Hin]. exact (Habsent Hin).
Qed.

Definition K_beta (A : sent) : Prop :=
  A = beta \/ A = SNeg beta.

Definition reachable_surface0 (h : hist) (w : word) : Prop :=
  exists x0 x acts,
    run (Conf 0 [] [] x0 [])
      acts
      (Conf 0 h [] x w).

Lemma reachable_surface0_empty : reachable_surface0 [] [].
Proof.
  exists (CurExpr (EAsk (ESent beta))),
    (CurExpr (EAsk (ESent beta))), [].
  apply RunNil.
Qed.

Record beta_stable_answerer : Type := BetaStableAnswerer {
  beta_answer : hist -> word -> sent -> bool * nat;
  beta_answer_certified :
    forall h w A,
      reachable_surface0 h w ->
      K_beta A ->
      answer_cert 1 h w (ESent A)
        (fst (beta_answer h w A)) (snd (beta_answer h w A));
  beta_answer_disquotes :
    forall h w A,
      reachable_surface0 h w ->
      K_beta A ->
      (fst (beta_answer h w A) = true <->
       models_closed 1 h w A);
  beta_finite_return_stable :
    forall h w A,
      reachable_surface0 h w ->
      K_beta A ->
      let b := fst (beta_answer h w A) in
      let p := snd (beta_answer h w A) in
      let a := fresh_id h [] in
      let r := Event a (code_expr coding (EAsk (ESent A))) b p in
      let h' := h ++ [r] in
      run (Conf 0 h [] (CurExpr (EAsk (ESent A))) w)
        [ActUP;ActCertS;ActDOWN]
        (Conf 0 h' [] (CurRet (ESent A) b p r) w) /\
      reachable_surface0 h' w /\
      beta_answer h' w A = beta_answer h w A /\
      answer_cert 1 h' w (ESent A) b p /\
      (models_closed 1 h w A <->
       models_closed 1 h' w A)
}.

Theorem B7_no_same_level_stable_answerer :
    beta_stable_answerer -> False.
Proof.
  intros B.
  pose proof
    (beta_answer_disquotes B (h := []) (w := []) (A := beta)
      reachable_surface0_empty (or_introl eq_refl)) as Hdq.
  assert (Htrue : models_closed 1 [] [] beta).
  {
    apply (proj2 (beta_truth_characterization [] [])).
    cbn. tauto.
  }
  assert (Hb : fst (beta_answer B [] [] beta) = true).
  { apply (proj2 Hdq). exact Htrue. }
  pose proof
    (beta_finite_return_stable B (h := []) (w := []) (A := beta)
      reachable_surface0_empty (or_introl eq_refl)) as Hreturn.
  destruct (beta_answer B [] [] beta) as [b p] eqn:Hans.
  cbn in Hb. subst b.
  cbn zeta in Hreturn.
  destruct Hreturn as
    [Hrun [Hreachable [Hanswer [Hcert Hstable]]]].
  change
    (models_closed 1 [] [] beta <->
     models_closed 1
       (beta_after [] (fresh_id [] []) p) [] beta)
    in Hstable.
  apply (proj1 (beta_truth_characterization
    (beta_after [] (fresh_id [] []) p) [])).
  - apply (proj1 Hstable).
    exact Htrue.
  - apply beta_key_after.
Qed.

(* B8: in the residual-erased boundary the fixed empty history never changes,
   so beta has a fixed positive truth value and the flip cannot occur. *)
Theorem B8_residual_ablation : forall w,
    models_closed 1 [] w beta /\
    (models_closed 1 [] w beta <->
     models_closed 1 [] w beta).
Proof.
  intro w. split.
  - apply (proj2 (beta_truth_characterization [] w)).
    cbn. tauto.
  - tauto.
Qed.

Definition dn_axiom_tree (l : nat) (A : sent) : proof_tree :=
  PTAx l (simp A (SNeg (SNeg A))).

Lemma dn_axiom_tree_proves : forall l h w A,
    raw_sent A ->
    formed_sent w A ->
    rank A <= l ->
    proves l h w (dn_axiom_tree l A)
      (simp A (SNeg (SNeg A))).
Proof.
  intros l h w A Hraw Hform Hrank.
  unfold proves, dn_axiom_tree.
  split.
  - cbn [valid_proof].
    split.
    + unfold jud, simp. cbn.
      repeat split; try assumption.
      rewrite Nat.max_id. exact Hrank.
    + apply AxDN. exact Hraw.
  - reflexivity.
Qed.

Definition beta_double_neg_tree : proof_tree :=
  PTMP 1 beta (SNeg (SNeg beta))
    beta_positive_tree (dn_axiom_tree 1 beta).

Lemma beta_double_neg_proof_empty : forall w,
    proves 1 [] w beta_double_neg_tree (SNeg (SNeg beta)).
Proof.
  intro w.
  pose proof (beta_positive_proof [] w) as Hpos.
  assert (Hempty : ~ In c_beta (keys [])) by (cbn; tauto).
  specialize (Hpos Hempty).
  pose proof
    (dn_axiom_tree_proves (l := 1) [] w beta
      beta_raw (beta_formed w)) as Hdn.
  assert (Hrank : rank beta <= 1).
  { rewrite beta_rank. apply Nat.le_refl. }
  specialize (Hdn Hrank).
  destruct Hpos as [Vpos Cpos].
  destruct Hdn as [Vdn Cdn].
  unfold beta_double_neg_tree, proves.
  split.
  - cbn [valid_proof].
    split.
    + unfold jud. rewrite beta_shape. cbn.
      repeat split; try exact I.
      exact (Nat.le_refl 1).
    + split; [exact Cpos |].
      split; [exact Cdn |].
      split; assumption.
  - reflexivity.
Qed.

Definition erased_fixed_answer (A : sent) : bool * nat :=
  if sent_eq_dec A beta
  then (true, proof_code beta_positive_tree)
  else (false, proof_code beta_double_neg_tree).

Lemma neg_beta_neq_beta : SNeg beta <> beta.
Proof. rewrite beta_shape. discriminate. Qed.

Lemma neg_beta_not_true_empty : forall w,
    ~ models_closed 1 [] w (SNeg beta).
Proof.
  intros w Hneg.
  unfold models_closed, models in Hneg.
  destruct Hneg as [_ [_ [_ Hsatneg]]].
  cbn [sat] in Hsatneg.
  apply Hsatneg.
  pose proof (proj2 (beta_truth_characterization [] w)) as Hbeta.
  specialize (Hbeta (ltac:(cbn; tauto))).
  unfold models_closed, models in Hbeta.
  tauto.
Qed.

Theorem B8_fixed_stable_answer_on_Kbeta : forall w A,
    K_beta A ->
    answer_cert 1 [] w (ESent A)
      (fst (erased_fixed_answer A))
      (snd (erased_fixed_answer A)) /\
    (fst (erased_fixed_answer A) = true <->
     models_closed 1 [] w A).
Proof.
  intros w A [HA | HA]; subst A.
  - unfold erased_fixed_answer.
    destruct (sent_eq_dec beta beta) as [_ | Hneq].
    + split.
      * unfold answer_cert. cbn [qdepth cert].
        exists beta_positive_tree. split.
        -- apply beta_positive_proof. cbn. tauto.
        -- reflexivity.
      * split.
        -- intros _. apply (proj2 (beta_truth_characterization [] w)).
           cbn. tauto.
        -- reflexivity.
    + contradiction.
  - unfold erased_fixed_answer.
    destruct (sent_eq_dec (SNeg beta) beta) as [Heq | Hneq].
    + exact (False_ind _ (neg_beta_neq_beta Heq)).
    + split.
      * unfold answer_cert. cbn [qdepth cert].
        exists beta_double_neg_tree. split.
        -- apply beta_double_neg_proof_empty.
        -- reflexivity.
      * split.
        -- discriminate.
        -- intro Htrue. exfalso.
           apply (neg_beta_not_true_empty (w := w)). exact Htrue.
Qed.

(* B1 packages the single disjoint-union coding and the structurally recursive
   question-depth computation.  Primitive-recursive admissibility is the
   source's ambient condition on the chosen coding; the record exposes the
   unified injection, partial inverses, and constructor-facing operations used
   by the formal system. *)
Theorem B1_single_syntax_and_coding :
    (forall x y,
      code_object coding x = code_object coding y -> x = y) /\
    (forall t, decode_tm coding (code_tm coding t) = Some t) /\
    (forall e, decode_expr coding (code_expr coding e) = Some e) /\
    (forall h, decode_hist coding (code_hist coding h) = Some h) /\
    (forall w, decode_word coding (code_word coding w) = Some w) /\
    (forall xs, decode_seq coding (code_seq coding xs) = Some xs) /\
    (forall tr, decode_tree coding (code_tree coding tr) = Some tr) /\
    (forall e n, qdepth (askn n e) = n + qdepth e).
Proof.
  repeat split.
  - apply code_object_inj.
  - apply decode_code_tm.
  - apply decode_code_expr.
  - apply decode_code_hist.
  - apply decode_code_word.
  - apply decode_code_seq.
  - apply decode_code_tree.
  - intros e n. induction n as [|n IH].
    + cbn. lia.
    + cbn. rewrite IH. lia.
Qed.

Theorem B2_local_reflection : forall l h w A,
    raw_sent A ->
    closed_sent A ->
    formed_sent w A ->
    rank A <= l ->
    (models_closed (S l) h w (SEv A) <->
     models_closed l h w A).
Proof.
  intros l h w A Hraw Hclosed Hform Hrank.
  unfold models_closed, models.
  cbn [sat].
  split.
  - intros [[Hr Hc] [[Hf _] [_ [_ Hsat]]]].
    split; [exact Hr |].
    split; [exact Hf |].
    split; [lia | exact Hsat].
  - intros [Hr [Hf [Hrnk Hsat]]].
    split.
    + split; [exact Hr | exact Hclosed].
    + split.
      * split; [exact Hf | exact Hclosed].
      * split.
        -- apply le_n_S. exact Hrnk.
        -- split.
           ++ rewrite Nat.add_1_r. apply le_n_S. exact Hrnk.
           ++ exact Hsat.
Qed.

(* B9: iterated quotations witness strictness of every level. *)
Fixpoint iter_ev (n : nat) (A : sent) : sent :=
  match n with
  | 0 => A
  | S k => SEv (iter_ev k A)
  end.

Lemma iter_ev_rank : forall n,
    rank (iter_ev n stop) = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma iter_ev_closed : forall n,
    closed_sent (iter_ev n stop).
Proof.
  induction n; reflexivity.
Qed.

Lemma iter_ev_raw : forall n,
    raw_sent (iter_ev n stop).
Proof.
  induction n as [|n IH].
  - exact I.
  - cbn. split; [exact IH | apply iter_ev_closed].
Qed.

Lemma iter_ev_formed : forall n,
    formed_sent [] (iter_ev n stop).
Proof.
  induction n as [|n IH].
  - exact I.
  - cbn. split; [exact IH | apply iter_ev_closed].
Qed.

Definition S_level (n : nat) (A : sent) : Prop :=
  raw_sent A /\ closed_sent A /\ formed_sent [] A /\ rank A <= n.

Theorem B9_tower_strict_direct_system : forall n,
    (forall A, S_level n A -> S_level (S n) A) /\
    S_level (S n) (iter_ev (S n) stop) /\
    ~ S_level n (iter_ev (S n) stop).
Proof.
  intro n.
  split.
  - intros A [Hr [Hc [Hf Hrank]]].
    repeat split; try assumption; lia.
  - split.
    + unfold S_level.
      split; [apply iter_ev_raw |].
      split; [apply iter_ev_closed |].
      split; [apply iter_ev_formed |].
      rewrite iter_ev_rank. apply Nat.le_refl.
    + intros [_ [_ [_ Hrank]]].
      rewrite iter_ev_rank in Hrank. lia.
Qed.

(* H1: the ordinary subsystem is literally a restriction of the full step
   relation; no rule is reinterpreted. *)
Definition ordinary_action (a : action) : Prop :=
  match a with
  | ActUP | ActCertS | ActCertQPos | ActCertQNeg | ActDOWN => True
  | _ => False
  end.

Definition ordinary_step (a : action) (C D : conf) : Prop :=
  ordinary_action a /\ word_of C = [] /\ word_of D = [] /\ step a C D.

Theorem H1_ordinary_is_conservative : forall a C D,
    ordinary_step a C D -> step a C D.
Proof. intros a C D [_ [_ [_ H]]]. exact H. Qed.

(* H8's three concrete ablations. *)
Definition identity_word_projection (C : conf) : word := word_of C.

Lemma H8_reveal_license_breaks_H3 :
    identity_word_projection C_ab <> identity_word_projection C_ba.
Proof. cbn [identity_word_projection C_ab C_ba license_breath root_conf].
  discriminate.
Qed.

Definition count_letter (a : letter) (w : word) : nat :=
  length (filter
    (fun b =>
      match a,b with
      | La,La | Lb,Lb => true
      | _,_ => false
      end) w).

Definition commutative_word_view (w : word) : nat * nat :=
  (count_letter La w, count_letter Lb w).

Lemma H8_commutativization_erases_order :
    commutative_word_view [La;Lb] =
    commutative_word_view [Lb;La].
Proof. reflexivity. Qed.

Definition formed_sent_probe_blind (_ : word) (A : sent) : Prop :=
  raw_sent A.

Lemma H8_probe_blind_erases_future_difference :
    formed_sent_probe_blind [La;Lb] delta <->
    formed_sent_probe_blind [Lb;La] delta.
Proof. reflexivity. Qed.

(* If future completeness is deleted, the public/free-variable/nonleakage
   fragment has a concrete model: the constantly true public formula.  Thus
   the H7 contradiction cannot be reconstructed from that fragment alone. *)
Record weak_future_domain_interface : Type := WeakFutureInterface {
  weak_dom_var : var;
  weak_dom_formula : sent;
  weak_dom_is_public : public_sent weak_dom_formula;
  weak_dom_free_vars :
    forall y, In y (fv_sent weak_dom_formula) -> y = weak_dom_var;
  weak_dom_nonleakage :
    forall C D e,
      approx0 C D ->
      (models_closed (level_of C) (hist_of C) (word_of C)
        (instantiate_code weak_dom_formula weak_dom_var
          (code_expr coding e)) <->
       models_closed (level_of D) (hist_of D) (word_of D)
        (instantiate_code weak_dom_formula weak_dom_var
          (code_expr coding e)))
}.

Definition weak_interface_without_future_completeness :
    weak_future_domain_interface.
Proof.
  refine
    {| weak_dom_var := 0;
       weak_dom_formula := stop |}.
  - cbn [stop public_sent]. exact I.
  - intros y Hy. cbn [stop fv_sent fv_tm] in Hy. contradiction.
  - intros C D e Happrox.
    destruct Happrox as [_ Hpublic].
    change
      (models_closed (level_of C) (hist_of C) (word_of C) stop <->
       models_closed (level_of D) (hist_of D) (word_of D) stop).
    apply Hpublic.
    + cbn [stop raw_sent]. exact I.
    + cbn [stop public_sent]. exact I.
    + reflexivity.
Defined.

Theorem H8_without_future_completeness_H7_is_not_forced :
    exists W : weak_future_domain_interface,
      weak_dom_formula W = stop.
Proof.
  exists weak_interface_without_future_completeness.
  reflexivity.
Qed.

(* Section 9's no-residual ordinary nested boundary. *)
Fixpoint ordinary_stack (sigma : list frame) : Prop :=
  match sigma with
  | [] => True
  | FOrd _ _ _ :: rest => ordinary_stack rest
  | FLic _ _ _ _ :: _ => False
  end.

Definition conf_O_star (C : conf) : Prop :=
  word_of C = [La;Lb] /\ ordinary_stack (stack_of C).

Definition conf_O (C : conf) : Prop :=
  conf_O_star C /\ hist_of C = [].

Definition reset_event (e : expr) (b : bool) (p : nat) : event :=
  Event 0 (code_expr coding (EAsk e)) b p.

Definition reset_current (x : current) : current :=
  match x with
  | CurExpr e => CurExpr e
  | CurAns b p => CurAns b p
  | CurRet e b p _ => CurRet e b p (reset_event e b p)
  end.

Definition reset_conf (C : conf) : conf :=
  Conf (level_of C) [] (stack_of C)
    (reset_current (current_of C)) [La;Lb].

Inductive qcurrent : Type :=
| QExpr : expr -> qcurrent
| QAns : bool -> nat -> qcurrent
| QRet : expr -> bool -> nat -> qcurrent.

Definition qstate : Type := list expr * qcurrent.

Fixpoint forget_stack (sigma : list frame) : list expr :=
  match sigma with
  | [] => []
  | FOrd _ e _ :: rest => e :: forget_stack rest
  | FLic _ _ _ _ :: rest => forget_stack rest
  end.

Definition forget_current (x : current) : qcurrent :=
  match x with
  | CurExpr e => QExpr e
  | CurAns b p => QAns b p
  | CurRet e b p _ => QRet e b p
  end.

Definition forget_conf (C : conf) : qstate :=
  (forget_stack (stack_of C), forget_current (current_of C)).

Definition ordinary_base_action (a : action) : Prop :=
  match a with
  | ActUP | ActCertS | ActCertQPos | ActCertQNeg | ActDOWN => True
  | _ => False
  end.

Definition step0 (a : action) (C D : conf) : Prop :=
  exists C0 D0,
    conf_O C0 /\
    conf_O_star D0 /\
    ordinary_base_action a /\
    step a C0 D0 /\
    C = reset_conf C0 /\
    D = reset_conf D0.

Definition qstep (a : action) (y y' : qstate) : Prop :=
  exists C D,
    step0 a C D /\
    forget_conf C = y /\
    forget_conf D = y'.

Inductive qint_action : Type :=
| QBase : action -> qint_action
| QPose | QTry.

Inductive qint_step : qint_action -> qstate -> qstate -> Prop :=
| QIntBase : forall a y y',
    qstep a y y' -> qint_step (QBase a) y y'
| QIntPose : forall e b p,
    qint_step QPose
      ([],QRet e b p)
      ([],QExpr (EAsk (ESent stop)))
| QIntTry :
    qint_step QTry
      ([],QExpr (EAsk (ESent stop)))
      ([ESent delta],QExpr (ESent delta)).

Definition forget_relation (C : conf) (y : qstate) : Prop :=
  conf_O C /\ forget_conf C = y.

Theorem B10_no_residual_strong_bisimulation :
    (forall a C D,
      step0 a C D ->
      qstep a (forget_conf C) (forget_conf D)) /\
    (forall a y y',
      qstep a y y' ->
      exists C D,
        step0 a C D /\
        forget_conf C = y /\
        forget_conf D = y').
Proof.
  split.
  - intros a C D Hstep.
    exists C, D. tauto.
  - intros a y y' Hq.
    exact Hq.
Qed.

(* The tower boundary retains only UP and therefore has no return-labelled
   edge. *)
Definition tower_conf (C : conf) : Prop :=
  hist_of C = [] /\ word_of C = [] /\ ordinary_stack (stack_of C).

Definition tower_step (C D : conf) : Prop :=
  tower_conf C /\ tower_conf D /\ step ActUP C D.

Lemma B11_tower_has_no_return : forall C D,
    tower_step C D ->
    ~ step ActDOWN C D.
Proof.
  intros C D [_ [_ Hup]] Hdown.
  inversion Hup; subst.
  inversion Hdown.
Qed.

Definition beta_positive_code : nat :=
  proof_code beta_positive_tree.

Lemma B11_beta_positive_answer_cert :
    answer_cert 1 [] [] (ESent beta) true beta_positive_code.
Proof.
  unfold answer_cert, beta_positive_code.
  cbn [qdepth cert].
  exists beta_positive_tree.
  split.
  - apply beta_positive_proof. cbn. tauto.
  - reflexivity.
Qed.

Definition beta_down_source : conf :=
  Conf 1 [] [FOrd 0 (ESent beta) 0]
    (CurAns true beta_positive_code) [].

Definition beta_down_event : event :=
  Event 0 c_beta true beta_positive_code.

Definition beta_down_target : conf :=
  Conf 0 [beta_down_event] []
    (CurRet (ESent beta) true beta_positive_code beta_down_event) [].

Lemma B11_brc_has_return_and_strict_residual :
    step ActDOWN beta_down_source beta_down_target /\
    length (hist_of beta_down_target) =
      S (length (hist_of beta_down_source)).
Proof.
  split.
  - unfold beta_down_source, beta_down_target, beta_down_event.
    eapply StepDOWN with
      (pre:=[]) (a:=0) (e:=ESent beta)
      (b:=true) (p:=beta_positive_code)
      (r:=Event 0 c_beta true beta_positive_code).
    + exact B11_beta_positive_answer_cert.
    + reflexivity.
  - reflexivity.
Qed.

Theorem B11_three_shape_separation_witnesses :
    (forall C D, tower_step C D -> ~ step ActDOWN C D) /\
    (exists C D,
      step ActDOWN C D /\
      length (hist_of D) = S (length (hist_of C))) /\
    (beta_stable_answerer -> False).
Proof.
  split.
  - exact B11_tower_has_no_return.
  - split.
    + exists beta_down_source, beta_down_target.
      exact B11_brc_has_return_and_strict_residual.
    + exact B7_no_same_level_stable_answerer.
Qed.

Theorem H9_two_extreme_boundaries :
    (forall n,
      (forall A, S_level n A -> S_level (S n) A) /\
      S_level (S n) (iter_ev (S n) stop) /\
      ~ S_level n (iter_ev (S n) stop)) /\
    (forall a C D,
      step0 a C D ->
      qstep a (forget_conf C) (forget_conf D)).
Proof.
  split.
  - exact B9_tower_strict_direct_system.
  - exact (proj1 B10_no_residual_strong_bisimulation).
Qed.

(* B4, phase 1: finite-set, freshness, valuation, and substitution facts. *)
Lemma in_union_iff : forall x xs ys,
    In x (union xs ys) <-> In x xs \/ In x ys.
Proof.
  intros x xs ys. unfold union.
  rewrite nodup_In, in_app_iff. tauto.
Qed.

Lemma memb_false_notin : forall x xs,
    memb x xs = false -> ~ In x xs.
Proof.
  intros x xs. induction xs as [|a xs IH].
  - cbn. tauto.
  - cbn. intro Hfalse.
    apply Bool.orb_false_iff in Hfalse as [Hxa Htail].
    intros [Heq | Hin].
    + subst. rewrite Nat.eqb_refl in Hxa. discriminate.
    + apply (IH Htail). exact Hin.
Qed.

Lemma fv_lookup_in_env : forall env x t y,
    lookup_subst x env = Some t ->
    In y (fv_tm t) ->
    In y (fv_subst_env env).
Proof.
  induction env as [|[z u] env IH]; intros x t y Hlook Hin.
  - discriminate.
  - cbn in Hlook |- *.
    destruct (Nat.eq_dec x z) as [Heq | Hneq].
    + inversion Hlook; subst. apply in_union_iff. left. exact Hin.
    + apply in_union_iff. right. eapply IH; eauto.
Qed.

Lemma lookup_remove_same : forall env x,
    lookup_subst x (remove_subst x env) = None.
Proof.
  induction env as [|[y t] env IH]; intro x.
  - reflexivity.
  - cbn. destruct (Nat.eq_dec x y) as [Heq | Hneq].
    + subst. destruct (Nat.eq_dec y y); [apply IH | contradiction].
    + cbn. destruct (Nat.eq_dec x y); [contradiction | apply IH].
Qed.

Lemma lookup_remove_other : forall env x y,
    x <> y ->
    lookup_subst x (remove_subst y env) = lookup_subst x env.
Proof.
  induction env as [|[z t] env IH]; intros x y Hxy.
  - reflexivity.
  - cbn.
    destruct (Nat.eq_dec y z) as [Hyz | Hyz].
    + subst. destruct (Nat.eq_dec x z); [contradiction |].
      apply IH. exact Hxy.
    + cbn. destruct (Nat.eq_dec x z) as [Hxz | Hxz].
      * reflexivity.
      * rewrite IH; [reflexivity | exact Hxy].
Qed.

Lemma in_max_list : forall xs x,
    In x xs -> x <= max_list xs.
Proof.
  induction xs as [|a xs IH]; intros x Hin.
  - contradiction.
  - cbn. destruct Hin as [Heq | Hin].
    + subst. apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma first_missing_spec : forall fuel start xs,
    ~ In (first_missing fuel start xs) xs \/
    first_missing fuel start xs = start + fuel.
Proof.
  induction fuel as [|fuel IH]; intros start xs.
  - right. cbn. lia.
  - cbn. destruct (in_dec Nat.eq_dec start xs) as [Hin | Hnot].
    + specialize (IH (S start) xs).
      destruct IH as [Hfree | Hend].
      * left. exact Hfree.
      * right. rewrite Hend. lia.
    + left. exact Hnot.
Qed.

Lemma fresh_not_in : forall xs, ~ In (fresh xs) xs.
Proof.
  intro xs. unfold fresh.
  destruct (first_missing_spec (S (max_list xs)) 0 xs)
    as [Hfree | Hend].
  - exact Hfree.
  - rewrite Hend. cbn.
    intro Hin.
    pose proof (in_max_list xs (S (max_list xs)) Hin).
    lia.
Qed.

Definition agree_on (xs : list var) (s t : valuation) : Prop :=
  forall x, In x xs -> s x = t x.

Lemma val_tm_ext : forall t s u,
    agree_on (fv_tm t) s u ->
    val_tm t s = val_tm t u.
Proof.
  induction t; intros s u Hagree; cbn in *.
  - apply Hagree. left. reflexivity.
  - reflexivity.
  - rewrite (IHt s u); [reflexivity | exact Hagree].
  - assert (H1 : val_tm t1 s = val_tm t1 u).
    { apply IHt1. intros x Hx. apply Hagree.
      apply in_union_iff. left. exact Hx. }
    assert (H2 : val_tm t2 s = val_tm t2 u).
    { apply IHt2. intros x Hx. apply Hagree.
      apply in_union_iff. right. exact Hx. }
    rewrite H1, H2. reflexivity.
  - assert (H1 : val_tm t1 s = val_tm t1 u).
    { apply IHt1. intros x Hx. apply Hagree.
      apply in_union_iff. left. exact Hx. }
    assert (H2 : val_tm t2 s = val_tm t2 u).
    { apply IHt2. intros x Hx. apply Hagree.
      apply in_union_iff. right. exact Hx. }
    rewrite H1, H2. reflexivity.
  - rewrite (IHt s u); [reflexivity | exact Hagree].
  - assert (H1 : val_tm t1 s = val_tm t1 u).
    { apply IHt1. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. left. exact Hx. }
    assert (H2 : val_tm t2 s = val_tm t2 u).
    { apply IHt2. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. right. apply in_union_iff. left. exact Hx. }
    assert (H3 : val_tm t3 s = val_tm t3 u).
    { apply IHt3. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. right. apply in_union_iff. right.
      apply in_union_iff. left. exact Hx. }
    rewrite H1, H2, H3. reflexivity.
  - rewrite (IHt s u); [reflexivity | exact Hagree].
  - rewrite (IHt s u); [reflexivity | exact Hagree].
Qed.

Definition env_val (env : subst_env) (s : valuation) : valuation :=
  fun x =>
    match lookup_subst x env with
    | Some t => val_tm t s
    | None => s x
    end.

Lemma update_val_same : forall s x n,
    update_val s x n x = n.
Proof.
  intros s x n. unfold update_val.
  destruct (Nat.eq_dec x x); [reflexivity | contradiction].
Qed.

Lemma update_val_other : forall s x y n,
    x <> y ->
    update_val s y n x = s x.
Proof.
  intros s x y n Hxy. unfold update_val.
  destruct (Nat.eq_dec x y); [contradiction | reflexivity].
Qed.

Lemma val_subst_tm_env : forall t env s,
    val_tm (subst_tm_env env t) s =
    val_tm t (env_val env s).
Proof.
  induction t; intros env s; cbn.
  - unfold env_val. destruct (lookup_subst v env); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma val_update_not_free : forall t s x n,
    ~ In x (fv_tm t) ->
    val_tm t (update_val s x n) = val_tm t s.
Proof.
  intros t s x n Hnot.
  apply val_tm_ext.
  intros y Hy.
  unfold update_val.
  destruct (Nat.eq_dec y x) as [Heq | Hneq].
  - subst. contradiction.
  - reflexivity.
Qed.

Lemma env_no_collision_agree : forall env y s n,
    memb y (fv_subst_env (remove_subst y env)) = false ->
    agree_on (fv_sent (SAll y stop))
      (env_val (remove_subst y env) (update_val s y n))
      (update_val (env_val env s) y n).
Proof.
  intros. cbn. intros x Hx. contradiction.
Qed.

(* The useful no-collision statement is independent of a particular body. *)
Lemma env_no_collision_pointwise : forall env y s n x,
    memb y (fv_subst_env (remove_subst y env)) = false ->
    env_val (remove_subst y env) (update_val s y n) x =
    update_val (env_val env s) y n x.
Proof.
  intros env y s n x Hfresh.
  unfold env_val, update_val.
  destruct (Nat.eq_dec x y) as [Heq | Hneq].
  - subst. rewrite lookup_remove_same.
    destruct (Nat.eq_dec y y); [reflexivity | contradiction].
  - rewrite lookup_remove_other by exact Hneq.
    destruct (Nat.eq_dec x y); [contradiction |].
    destruct (lookup_subst x env) eqn:Hlook.
    + apply val_update_not_free.
      intro Hy.
      apply (@memb_false_notin y
        (fv_subst_env (remove_subst y env)) Hfresh).
      eapply fv_lookup_in_env.
      * rewrite lookup_remove_other by exact Hneq. exact Hlook.
      * exact Hy.
    + reflexivity.
Qed.

Lemma env_collision_agree : forall env y s n B,
    let env' := remove_subst y env in
    let z := fresh
      (allvars_sent B ++ fv_subst_env env' ++
       dom_subst_env env' ++ [y]) in
    agree_on (fv_sent B)
      (env_val ((y,TVar z)::env') (update_val s z n))
      (update_val (env_val env s) y n).
Proof.
  intros env y s n B env' z x Hx.
  assert (Hzall :
    ~ In z
      (allvars_sent B ++ fv_subst_env env' ++
       dom_subst_env env' ++ [y])).
  { unfold z. apply fresh_not_in. }
  assert (HzB : ~ In z (fv_sent B)).
  {
    intro Hz.
    apply Hzall. apply in_app_iff. left.
    unfold allvars_sent. apply in_union_iff. left. exact Hz.
  }
  assert (HzEnv : ~ In z (fv_subst_env env')).
  {
    intro Hz.
    apply Hzall. apply in_app_iff. right.
    apply in_app_iff. left. exact Hz.
  }
  unfold env_val. cbn.
  destruct (Nat.eq_dec x y) as [Hxy | Hxy].
  - subst. destruct (Nat.eq_dec y y); [|contradiction].
    cbn. fold z. rewrite !update_val_same. reflexivity.
  - destruct (Nat.eq_dec x y); [contradiction |].
    assert (Hrem :
      lookup_subst x env' = lookup_subst x env).
    { unfold env'. apply lookup_remove_other. exact Hxy. }
    rewrite Hrem.
    destruct (Nat.eq_dec x y); [contradiction |].
    fold (env_val env s).
    rewrite (@update_val_other (env_val env s) x y n Hxy).
    destruct (lookup_subst x env) eqn:Hlook.
    + unfold env_val. rewrite Hlook.
      rewrite val_update_not_free.
      * reflexivity.
      * intro Hz.
        apply HzEnv. eapply fv_lookup_in_env.
        -- exact Hrem.
        -- exact Hz.
    + unfold env_val. rewrite Hlook.
      destruct (Nat.eq_dec x z) as [Hxz | Hxz].
      * subst. contradiction.
      * change (update_val s z n x = s x).
        apply update_val_other. exact Hxz.
Qed.

Lemma in_remove_other : forall xs x y,
    In x xs -> x <> y -> In x (remove Nat.eq_dec y xs).
Proof.
  induction xs as [|a xs IH]; intros x y Hin Hneq.
  - contradiction.
  - cbn. destruct Hin as [Heq | Hin].
    + subst. destruct (Nat.eq_dec y x) as [Hyx | Hyx].
      * symmetry in Hyx. contradiction.
      * left. reflexivity.
    + destruct (Nat.eq_dec y a).
      * apply IH; assumption.
      * right. apply IH; assumption.
Qed.

Lemma sat_ext : forall A l h w s u,
    agree_on (fv_sent A) s u ->
    (sat l h w s A <-> sat l h w u A).
Proof.
  induction A; intros l h w s u Hagree; cbn in *.
  - assert (Ht : val_tm t s = val_tm t u).
    { apply val_tm_ext. intros x Hx. apply Hagree.
      apply in_union_iff. left. exact Hx. }
    assert (Ht0 : val_tm t0 s = val_tm t0 u).
    { apply val_tm_ext. intros x Hx. apply Hagree.
      apply in_union_iff. right. exact Hx. }
    rewrite Ht, Ht0. tauto.
  - assert (Ht : val_tm t s = val_tm t u).
    { apply val_tm_ext. exact Hagree. }
    rewrite Ht. tauto.
  - assert (Ht : val_tm t s = val_tm t u).
    { apply val_tm_ext. exact Hagree. }
    rewrite Ht. tauto.
  - assert (H0 : val_tm t s = val_tm t u).
    { apply val_tm_ext. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. left. exact Hx. }
    assert (H1 : val_tm t0 s = val_tm t0 u).
    { apply val_tm_ext. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. right. apply in_union_iff. left. exact Hx. }
    assert (H2 : val_tm t1 s = val_tm t1 u).
    { apply val_tm_ext. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. right. apply in_union_iff. right.
      apply in_union_iff. left. exact Hx. }
    assert (H3 : val_tm t2 s = val_tm t2 u).
    { apply val_tm_ext. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. right. apply in_union_iff. right.
      apply in_union_iff. right. apply in_union_iff. left. exact Hx. }
    assert (H4 : val_tm t3 s = val_tm t3 u).
    { apply val_tm_ext. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. right. apply in_union_iff. right.
      apply in_union_iff. right. apply in_union_iff. right.
      apply in_union_iff. left. exact Hx. }
    assert (H5 : val_tm t4 s = val_tm t4 u).
    { apply val_tm_ext. intros x Hx. apply Hagree. cbn.
      apply in_union_iff. right. apply in_union_iff. right.
      apply in_union_iff. right. apply in_union_iff. right.
      apply in_union_iff. right. apply in_union_iff. left. exact Hx. }
    rewrite H0, H1, H2, H3, H4, H5. tauto.
  - specialize (IHA l h w s u Hagree). tauto.
  - assert (HB : sat l h w s A1 <-> sat l h w u A1).
    { apply IHA1. intros x Hx. apply Hagree.
      apply in_union_iff. left. exact Hx. }
    assert (HC : sat l h w s A2 <-> sat l h w u A2).
    { apply IHA2. intros x Hx. apply Hagree.
      apply in_union_iff. right. exact Hx. }
    tauto.
  - split; intros Hall n.
    + assert (Heq :
        sat l h w (update_val s v n) A <->
        sat l h w (update_val u v n) A).
      { apply IHA. intros x Hx. unfold update_val.
        destruct (Nat.eq_dec x v) as [Heq | Hneq].
        -- reflexivity.
        -- apply Hagree. apply in_remove_other; assumption. }
      apply (proj1 Heq). apply Hall.
    + assert (Heq :
        sat l h w (update_val s v n) A <->
        sat l h w (update_val u v n) A).
      { apply IHA. intros x Hx. unfold update_val.
        destruct (Nat.eq_dec x v) as [Heq | Hneq].
        -- reflexivity.
        -- apply Hagree. apply in_remove_other; assumption. }
      apply (proj2 Heq). apply Hall.
  - reflexivity.
Qed.

Lemma sat_subst_env : forall A env l h w s,
    (sat l h w s (subst_sent_env env A) <->
     sat l h w (env_val env s) A).
Proof.
  induction A; intros env l h w s; cbn.
  - rewrite !val_subst_tm_env. tauto.
  - rewrite val_subst_tm_env. tauto.
  - rewrite val_subst_tm_env. tauto.
  - rewrite !val_subst_tm_env. tauto.
  - specialize (IHA env l h w s). tauto.
  - specialize (IHA1 env l h w s).
    specialize (IHA2 env l h w s). tauto.
  - destruct
      (memb v (fv_subst_env (remove_subst v env)))
      eqn:Hcollision.
    + set (z := fresh
        (allvars_sent A ++
         fv_subst_env (remove_subst v env) ++
         dom_subst_env (remove_subst v env) ++ [v])).
      split; intros Hall n.
      * specialize (Hall n).
        assert (Heq :
          sat l h w
            (env_val ((v,TVar z)::remove_subst v env)
              (update_val s z n)) A <->
          sat l h w (update_val (env_val env s) v n) A).
        { apply sat_ext. unfold z. apply env_collision_agree. }
        apply (proj1 Heq).
        apply (proj1
          (IHA ((v,TVar z)::remove_subst v env)
            l h w (update_val s z n))).
        exact Hall.
      * apply (proj2
          (IHA ((v,TVar z)::remove_subst v env)
            l h w (update_val s z n))).
        assert (Heq :
          sat l h w
            (env_val ((v,TVar z)::remove_subst v env)
              (update_val s z n)) A <->
          sat l h w (update_val (env_val env s) v n) A).
        { apply sat_ext. unfold z. apply env_collision_agree. }
        apply (proj2 Heq). apply Hall.
    + split; intros Hall n.
      * specialize (Hall n).
        assert (Heq :
          sat l h w
            (env_val (remove_subst v env) (update_val s v n)) A <->
          sat l h w (update_val (env_val env s) v n) A).
        { apply sat_ext. intros x Hx.
          apply env_no_collision_pointwise. exact Hcollision. }
        apply (proj1 Heq).
        apply (proj1
          (IHA (remove_subst v env)
            l h w (update_val s v n))).
        exact Hall.
      * apply (proj2
          (IHA (remove_subst v env)
            l h w (update_val s v n))).
        assert (Heq :
          sat l h w
            (env_val (remove_subst v env) (update_val s v n)) A <->
          sat l h w (update_val (env_val env s) v n) A).
        { apply sat_ext. intros x Hx.
          apply env_no_collision_pointwise. exact Hcollision. }
        apply (proj2 Heq). apply Hall.
  - reflexivity.
Qed.

Lemma env_val_single_pointwise : forall x t s y,
    env_val [(x,t)] s y =
    update_val s x (val_tm t s) y.
Proof.
  intros x t s y.
  unfold env_val, update_val. cbn.
  destruct (Nat.eq_dec y x) as [Heq | Hneq].
  - subst. destruct (Nat.eq_dec x x); [reflexivity | contradiction].
  - destruct (Nat.eq_dec y x); [contradiction | reflexivity].
Qed.

Lemma sat_subst : forall A x t l h w s,
    (sat l h w s (subst_sent A x t) <->
     sat l h w (update_val s x (val_tm t s)) A).
Proof.
  intros A x t l h w s.
  unfold subst_sent.
  rewrite sat_subst_env.
  apply sat_ext.
  intros y Hy. apply env_val_single_pointwise.
Qed.

Lemma rank_subst_env : forall A env,
    rank (subst_sent_env env A) = rank A.
Proof.
  induction A; intro env; cbn; try reflexivity.
  - apply IHA.
  - rewrite IHA1, IHA2. reflexivity.
  - destruct
      (memb v (fv_subst_env (remove_subst v env)));
      apply IHA.
Qed.

Lemma rank_subst : forall A x t,
    rank (subst_sent A x t) = rank A.
Proof. intros. apply rank_subst_env. Qed.

Lemma alpha_rank : forall A B,
    alpha_sent A B -> rank A = rank B.
Proof.
  intros A B Halpha. induction Halpha; cbn.
  - reflexivity.
  - symmetry. exact IHHalpha.
  - rewrite IHHalpha1. exact IHHalpha2.
  - unfold bound_ren. cbn. rewrite rank_subst. reflexivity.
  - exact IHHalpha.
  - rewrite IHHalpha1, IHHalpha2. reflexivity.
  - exact IHHalpha.
  - rewrite IHHalpha. reflexivity.
Qed.

Lemma bound_rename_agree : forall A x y s n,
    ~ In y (remove Nat.eq_dec x (fv_sent A)) ->
    agree_on (fv_sent A)
      (update_val s x n)
      (update_val (update_val s y n) x n).
Proof.
  intros A x y s n Hfresh z Hz.
  destruct (Nat.eq_dec z x) as [Hzx | Hzx].
  - subst. rewrite !update_val_same. reflexivity.
  - rewrite (@update_val_other s z x n Hzx).
    rewrite (@update_val_other (update_val s y n) z x n Hzx).
    destruct (Nat.eq_dec z y) as [Hzy | Hzy].
    + subst. exfalso. apply Hfresh.
      apply in_remove_other; assumption.
    + rewrite (@update_val_other s z y n Hzy). reflexivity.
Qed.

Lemma alpha_sound : forall A B,
    alpha_sent A B ->
    forall l h w s, (sat l h w s A <-> sat l h w s B).
Proof.
  intros A B Halpha.
  induction Halpha; intros l h w s; cbn.
  - tauto.
  - specialize (IHHalpha l h w s). tauto.
  - specialize (IHHalpha1 l h w s).
    specialize (IHHalpha2 l h w s). tauto.
  - unfold bound_ren. cbn.
    split; intros Hall n.
    + apply (proj2 (sat_subst A x (TVar y)
        l h w (update_val s y n))).
      cbn. rewrite update_val_same.
      assert (Heq :
        sat l h w (update_val s x n) A <->
        sat l h w (update_val (update_val s y n) x n) A).
      { apply sat_ext. apply bound_rename_agree. exact H. }
      apply (proj1 Heq). apply Hall.
    + pose proof (Hall n) as Hsub.
      apply (proj1 (sat_subst A x (TVar y)
        l h w (update_val s y n))) in Hsub.
      cbn in Hsub. rewrite update_val_same in Hsub.
      assert (Heq :
        sat l h w (update_val s x n) A <->
        sat l h w (update_val (update_val s y n) x n) A).
      { apply sat_ext. apply bound_rename_agree. exact H. }
      apply (proj2 Heq). exact Hsub.
  - specialize (IHHalpha l h w s). tauto.
  - specialize (IHHalpha1 l h w s).
    specialize (IHHalpha2 l h w s). tauto.
  - split; intros Hall n.
    + apply (proj1 (IHHalpha l h w (update_val s x n))).
      apply Hall.
    + apply (proj2 (IHHalpha l h w (update_val s x n))).
      apply Hall.
  - pose proof (alpha_rank Halpha) as Hrank.
    specialize (IHHalpha (Nat.pred l) h w zero_val).
    rewrite Hrank. tauto.
Qed.

Lemma sat_update_not_free : forall A x l h w s n,
    ~ In x (fv_sent A) ->
    (sat l h w s A <-> sat l h w (update_val s x n) A).
Proof.
  intros A x l h w s n Hnot.
  apply sat_ext.
  intros y Hy.
  unfold update_val.
  destruct (Nat.eq_dec y x) as [Heq | Hneq].
  - subst. contradiction.
  - reflexivity.
Qed.

Lemma val_closed_zero : forall t s,
    closed_tm t ->
    val_tm t s = val_tm t zero_val.
Proof.
  intros t s Hclosed.
  apply val_tm_ext.
  unfold closed_tm in Hclosed.
  intros x Hx. rewrite Hclosed in Hx. contradiction.
Qed.

Lemma axiom_sound : forall A,
    axiom A ->
    forall l h w s, sat l h w s A.
Proof.
  intros A Hax.
  destruct Hax; intros l h w s.
  - unfold simp. cbn [sat]. tauto.
  - unfold simp. cbn [sat]. tauto.
  - unfold simp. cbn [sat]. apply NNPP. tauto.
  - unfold simp. cbn [sat]. tauto.
  - unfold simp. cbn [sat]. tauto.
  - unfold simp. cbn [sat]. tauto.
  - unfold simp. cbn [sat]. tauto.
  - unfold simp. cbn [sat].
    fold (subst_sent A x t).
    rewrite sat_subst.
    intros [Hall Hnot].
    apply Hnot. apply Hall.
  - unfold simp. cbn [sat].
    intros [Hall Hneg].
    apply Hneg.
    intros [HA HnotAll].
    apply HnotAll. intro n.
    specialize (Hall n).
    assert (HAup : sat l h w (update_val s x n) A).
    {
      assert (Heq :
        sat l h w s A <->
        sat l h w (update_val s x n) A).
      { apply sat_update_not_free. assumption. }
      apply (proj1 Heq).
      exact HA.
    }
    tauto.
  - cbn [sat]. reflexivity.
  - unfold simp. cbn [sat].
    intros [Heq Hbad].
    fold (subst_sent A x t) in Hbad.
    fold (subst_sent A x u) in Hbad.
    apply Hbad.
    intros [Hleft Hnotright].
    apply Hnotright.
    apply (proj2 (sat_subst A x u l h w s)).
    apply (proj1 (sat_subst A x t l h w s)) in Hleft.
    rewrite <- Heq. exact Hleft.
  - cbn [sat].
    rewrite (@val_closed_zero t s H).
    rewrite (@val_closed_zero u s H0).
    exact H1.
Qed.

Lemma valid_proof_jud : forall h w pi,
    valid_proof h w pi ->
    let '(l,A) := conclusion pi in jud w l A.
Proof.
  intros h w pi Hvalid.
  destruct pi; cbn in *; tauto.
Qed.

Lemma valid_proof_sound_at : forall pi h w,
    valid_proof h w pi ->
    forall l A,
      conclusion pi = (l,A) ->
      forall s, sat l h w s A.
Proof.
  induction pi as
    [lev A
    |lev t
    |lev t
    |lev t
    |lev A B pA IH_A pImp IH_Imp
    |lev x A p IH
    |lev A B p IH
    |k A p IH
    |k A p IH];
    intros h w Hvalid l0 X Hcon rho0;
    cbn in Hcon; inversion Hcon; subst; clear Hcon;
    cbn in Hvalid.
  - destruct Hvalid as [_ Hax].
    eapply axiom_sound. exact Hax.
  - destruct Hvalid as [HJ [Hclosed Hin]].
    destruct HJ as [_ [_ Hrank]].
    split.
    + exact Hrank.
    + rewrite (@val_closed_zero t rho0 Hclosed). exact Hin.
  - destruct Hvalid as [HJ [Hclosed Hnot]].
    destruct HJ as [_ [_ Hrank]].
    cbn [sat]. intros [_ Hin].
    apply Hnot.
    rewrite <- (@val_closed_zero t rho0 Hclosed).
    exact Hin.
  - destruct Hvalid as [HJ [Hclosed Hzero]].
    destruct HJ as [_ [Hgrant Hrank]].
    repeat split.
    + exact Hrank.
    + exact Hgrant.
    + rewrite (@val_closed_zero t rho0 Hclosed). exact Hzero.
  - destruct Hvalid as [HJ [HC1 [HC2 [V1 V2]]]].
    pose proof (IH_A h w V1 _ _ HC1 rho0) as HA.
    pose proof (IH_Imp h w V2 _ _ HC2 rho0) as Himp.
    unfold simp in Himp. cbn [sat] in Himp. tauto.
  - destruct Hvalid as [HJ [HC V]].
    intro m.
    eapply IH.
    + exact V.
    + exact HC.
  - destruct Hvalid as [HJA [HJB [Halpha [HC V]]]].
    pose proof (IH h w V _ _ HC rho0) as HA.
    apply (proj1 (@alpha_sound A X Halpha l0 h w rho0)).
    exact HA.
  - destruct Hvalid as [HJA [HJE [HC V]]].
    destruct HJE as [_ [_ Hrank]].
    split.
    + cbn in Hrank. rewrite Nat.add_1_r. exact Hrank.
    + eapply IH.
      * exact V.
      * exact HC.
  - destruct Hvalid as [HJneg [HJE [HC V]]].
    cbn [sat].
    intros [_ HA].
    pose proof (IH h w V k (SNeg A) HC zero_val) as Hneg.
    cbn [sat] in Hneg. exact (Hneg HA).
Qed.

Theorem B4_certificate_reliability : forall l h w pi A,
    proves l h w pi A ->
    forall s, models l h w s A.
Proof.
  intros l h w pi A [Hvalid Hcon] s.
  pose proof (valid_proof_jud h w pi Hvalid) as HJ.
  rewrite Hcon in HJ. cbn in HJ.
  destruct HJ as [Hraw [Hform Hrank]].
  unfold models.
  repeat split; try assumption.
  eapply valid_proof_sound_at.
  - exact Hvalid.
  - exact Hcon.
Qed.

End WithCoding.
End BRC_HL.
