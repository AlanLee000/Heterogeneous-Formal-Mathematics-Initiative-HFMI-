(* Standalone all-in-one formalization of SSTC-TCR 2171. *)
From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat Lia Sorting.Permutation.
Import ListNotations.
Set Implicit Arguments.
Unset Strict Implicit.

(* BEGIN SSTC_TCR_Core.v, original line 6 *)
Module SSTC_TCR_Core.

Inductive atom : Type := AP | AQ.
Inductive form : Type := FP | FQ | FImpPQ.
Definition atom_eq_dec : forall x y : atom, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition form_eq_dec : forall x y : form, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition all_forms : list form := [FP; FQ; FImpPQ].
Definition valuation : Type := atom -> bool.
Definition eval (v : valuation) (A : form) : bool :=
  match A with FP => v AP | FQ => v AQ
  | FImpPQ => negb (v AP) || v AQ end.
Definition valuation_of_bits (bp bq : bool) : valuation :=
  fun a => match a with AP => bp | AQ => bq end.
Definition all_valuations : list valuation :=
  [valuation_of_bits false false; valuation_of_bits false true;
   valuation_of_bits true false; valuation_of_bits true true].
Lemma form_p_neq_q : FP <> FQ.
Proof. discriminate. Qed.
Lemma implication_semantics :
  forall v, eval v FImpPQ = negb (eval v FP) || eval v FQ.
Proof. reflexivity. Qed.

Inductive rule : Type := Rho | Alpha | Upsilon | Beta | Delta.
Inductive adm_tag : Type := AdmBegin | AdmInspect | AdmResume.
Inductive kat : Type := K_wf | K_truth | K_deps | K_ownbegin | K_foreignresume.
Inductive check_result : Type := Pass | Fail.
Definition rule_eq_dec : forall x y : rule, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition adm_tag_eq_dec : forall x y : adm_tag, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition kat_eq_dec : forall x y : kat, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition check_result_eq_dec :
  forall x y : check_result, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Definition all_rules : list rule := [Rho; Alpha; Upsilon; Beta; Delta].
Definition all_kats : list kat :=
  [K_wf; K_truth; K_deps; K_ownbegin; K_foreignresume].
Definition clause : Type := (list form * form)%type.
Definition logic_of (r : rule) : list clause :=
  match r with
  | Rho => [([FP; FImpPQ], FQ)]
  | Beta => [([FP], FQ)]
  | _ => []
  end.
Definition adm_of (r : rule) : list adm_tag :=
  match r with
  | Rho => [AdmBegin; AdmInspect]
  | Alpha | Upsilon => [AdmBegin; AdmInspect; AdmResume]
  | Beta => [AdmBegin]
  | Delta => [AdmInspect; AdmResume]
  end.
Definition dep0_of (r : rule) : list rule :=
  match r with Delta => [Rho] | _ => [] end.
Definition alias_of (_ : rule) : list rule := [].
Record rule_code : Type := {
  rc_name : rule;
  rc_logic : list clause;
  rc_adm : list adm_tag;
  rc_dep0 : list rule;
  rc_alias : list rule;
  rc_kats : list kat
}.
Definition code (r : rule) : rule_code :=
  {| rc_name := r; rc_logic := logic_of r; rc_adm := adm_of r;
     rc_dep0 := dep0_of r; rc_alias := alias_of r; rc_kats := all_kats |}.
Definition rule_code_eq_dec :
  forall x y : rule_code, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.
Definition rule_mem (x : rule) (xs : list rule) : bool :=
  if in_dec rule_eq_dec x xs then true else false.
Definition form_mem (x : form) (xs : list form) : bool :=
  if in_dec form_eq_dec x xs then true else false.
Definition add_rule (x : rule) (xs : list rule) : list rule :=
  if in_dec rule_eq_dec x xs then xs else x :: xs.
Definition union_rules (xs ys : list rule) : list rule :=
  fold_right add_rule ys xs.
Definition direct_refs (r : rule) : list rule := dep0_of r ++ alias_of r.
Definition D (x y : rule) : Prop := In x (direct_refs y).
Definition closure_step (xs : list rule) : list rule :=
  fold_right (fun y acc => union_rules (direct_refs y) acc) xs xs.
Fixpoint closure_iter (n : nat) (xs : list rule) : list rule :=
  match n with 0 => xs | S n0 => closure_iter n0 (closure_step xs) end.
Definition closure (r : rule) : list rule := closure_iter 5 [r].
Definition block (r : rule) : list rule :=
  filter (fun y => rule_mem r (closure y)) all_rules.

Definition clause_wf_b (cl : clause) : bool :=
  let '(premises, conclusion) := cl in
  forallb (fun A => form_mem A all_forms) premises
  && form_mem conclusion all_forms.
Definition clause_true_b (v : valuation) (cl : clause) : bool :=
  let '(premises, conclusion) := cl in
  negb (forallb (eval v) premises) || eval v conclusion.
Definition wf_b (r : rule) : bool := forallb clause_wf_b (logic_of r).
Definition truth_b (r : rule) : bool :=
  forallb (fun v => forallb (clause_true_b v) (logic_of r)) all_valuations.
Definition deps_b (r : rule) : bool :=
  forallb (fun x => rule_mem x all_rules) (direct_refs r)
  && forallb (fun x => rule_mem x (dep0_of r)) (alias_of r).
Definition satk (r : rule) (k : kat) : bool :=
  match k with
  | K_wf => wf_b r | K_truth => truth_b r | K_deps => deps_b r
  | K_ownbegin => true | K_foreignresume => true
  end.
Definition chk (r : rule) : check_result :=
  if forallb (satk r) all_kats then Pass else Fail.

Theorem check_registry_table :
  chk Rho = Pass /\ chk Alpha = Pass /\ chk Upsilon = Pass /\
  chk Delta = Pass /\ chk Beta = Fail.
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem closure_table :
  closure Rho = [Rho] /\ closure Alpha = [Alpha] /\
  closure Upsilon = [Upsilon] /\ closure Beta = [Beta] /\
  closure Delta = [Rho; Delta].
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem block_table :
  block Rho = [Rho; Delta] /\ block Alpha = [Alpha] /\
  block Upsilon = [Upsilon] /\ block Beta = [Beta] /\
  block Delta = [Delta].
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition explicit_model : valuation := valuation_of_bits true true.
Theorem explicit_model_initial :
  eval explicit_model FP = true /\ eval explicit_model FImpPQ = true.
Proof. vm_compute. split; reflexivity. Qed.
Theorem rho_is_truth_preserving :
  forall v, eval v FP = true -> eval v FImpPQ = true -> eval v FQ = true.
Proof.
  intros v Hp Hi.
  cbn in Hp, Hi.
  rewrite Hp in Hi.
  exact Hi.
Qed.
Definition beta_countermodel : valuation := valuation_of_bits true false.
Theorem beta_rejected_by_countermodel :
  eval beta_countermodel FP = true /\ eval beta_countermodel FQ = false.
Proof. vm_compute. split; reflexivity. Qed.


End SSTC_TCR_Core.
Export SSTC_TCR_Core.

(* BEGIN SSTC_TCR_State.v, original line 6 *)
Module SSTC_TCR_State.
Import SSTC_TCR_Core.

Record certificate : Type := {
  cert_kind : check_result;
  cert_id : nat;
  cert_target : rule;
  cert_actor : rule;
  cert_begin : nat;
  cert_inspect : nat;
  cert_snapshot : rule_code;
  cert_delta : list (list rule);
  cert_length : nat
}.
Definition certificate_eq_dec :
  forall x y : certificate, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Inductive event : Type :=
| EvBegin : nat -> rule -> event
| EvInspect : nat -> rule -> check_result -> event
| EvResume : nat -> rule -> certificate -> event
| EvInfer : rule -> list form -> form -> event.
Definition event_eq_dec : forall x y : event, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Definition event_exec (e : event) : rule :=
  match e with
  | EvBegin _ r => r | EvInspect _ a _ => a
  | EvResume _ u _ => u | EvInfer r _ _ => r
  end.
Definition decl_supp (e : event) : list rule := closure (event_exec e).
Definition disjoint_rules_b (xs ys : list rule) : bool :=
  forallb (fun x => negb (rule_mem x ys)) xs.
Definition list_rule_eq_dec :
  forall x y : list rule, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Fixpoint indexed_forallb {A : Type} (f : nat -> A -> bool)
         (i : nat) (xs : list A) : bool :=
  match xs with
  | [] => true
  | x :: tl => f i x && indexed_forallb f (S i) tl
  end.

Definition no_target_begin_between_b
           (tau : list event) (b j : nat) (r : rule) : bool :=
  forallb
    (fun h =>
       match nth_error tau h with
       | Some (EvBegin _ r0) => negb (rule_mem r0 [r])
       | _ => true
       end)
    (seq (S b) (j - S b)).

Definition valid_cert_b (c : certificate) (tau : list event) : bool :=
  let b := cert_begin c in
  let j := cert_inspect c in
  (b <? j) && (j <? length tau)
  && (match nth_error tau b with
      | Some (EvBegin i r) =>
          Nat.eqb i (cert_id c) && rule_mem r [cert_target c]
      | _ => false end)
  && (match nth_error tau j with
      | Some (EvInspect i a k) =>
          Nat.eqb i (cert_id c) && rule_mem a [cert_actor c]
          && (if check_result_eq_dec k (cert_kind c) then true else false)
          && negb (rule_mem a [cert_target c])
      | _ => false end)
  && (if check_result_eq_dec (cert_kind c) (chk (cert_target c))
      then true else false)
  && (if rule_code_eq_dec (cert_snapshot c) (code (cert_target c))
      then true else false)
  && Nat.eqb (cert_length c) (j - b)
  && Nat.eqb (length (cert_delta c)) (cert_length c)
  && indexed_forallb
       (fun m ds =>
          match nth_error tau (b + 1 + m) with
          | Some e =>
              if list_rule_eq_dec ds (decl_supp e) then true else false
          | None => false end)
       0 (cert_delta c)
  && forallb (fun ds => disjoint_rules_b ds (block (cert_target c)))
             (cert_delta c)
  && no_target_begin_between_b tau b j (cert_target c).
Definition VCert (c : certificate) (tau : list event) : Prop :=
  valid_cert_b c tau = true.
Definition Cert (c : certificate) : Prop :=
  cert_snapshot c = code (cert_target c)
  /\ Forall (@NoDup rule) (cert_delta c).
Definition EventFormed (e : event) : Prop :=
  match e with
  | EvResume _ _ c => Cert c
  | _ => True
  end.

Inductive obligation_status : Type := StOpen | StPass | StFail | StClosed.
Definition obligation_status_eq_dec :
  forall x y : obligation_status, {x = y} + {x <> y}.
Proof. decide equality. Defined.
Record obligation : Type := {
  ob_target : rule;
  ob_begin : nat;
  ob_status : obligation_status;
  ob_cert : option certificate
}.
Definition obligation_eq_dec :
  forall x y : obligation, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.

Definition nat_map (A : Type) := list (nat * A).
Definition rule_map (A : Type) := list (rule * A).
Fixpoint lookup_nat {A : Type} (i : nat) (m : nat_map A) : option A :=
  match m with
  | [] => None
  | (j,x) :: tl => if Nat.eq_dec i j then Some x else lookup_nat i tl
  end.
Fixpoint update_nat {A : Type} (i : nat) (x : A)
         (m : nat_map A) : nat_map A :=
  match m with
  | [] => [(i,x)]
  | (j,y) :: tl =>
      if Nat.eq_dec i j then (i,x) :: tl else (j,y) :: update_nat i x tl
  end.
Fixpoint lookup_rule {A : Type} (r : rule) (m : rule_map A) : option A :=
  match m with
  | [] => None
  | (q,x) :: tl => if rule_eq_dec r q then Some x else lookup_rule r tl
  end.
Fixpoint update_rule {A : Type} (r : rule) (x : A)
         (m : rule_map A) : rule_map A :=
  match m with
  | [] => [(r,x)]
  | (q,y) :: tl =>
      if rule_eq_dec r q then (r,x) :: tl else (q,y) :: update_rule r x tl
  end.
Fixpoint remove_rule_keys {A : Type} (keys : list rule)
         (m : rule_map A) : rule_map A :=
  match m with
  | [] => []
  | (r,x) :: tl =>
      if in_dec rule_eq_dec r keys then remove_rule_keys keys tl
      else (r,x) :: remove_rule_keys keys tl
  end.

Record state : Type := {
  st_gamma : list form;
  st_holds : rule -> list nat;
  st_obligations : nat_map obligation;
  st_certs : list certificate;
  st_consumed : list certificate;
  st_licenses : rule_map certificate;
  st_trace : list event;
  st_next : nat
}.

Definition active_b (s : state) (r : rule) : bool :=
  match st_holds s r with [] => true | _ => false end.
Definition enabled_b (s : state) (r : rule) : bool :=
  forallb (active_b s) (closure r).
Definition Act (s : state) (r : rule) : Prop := active_b s r = true.
Definition Enabled (s : state) (r : rule) : Prop := enabled_b s r = true.
Definition cert_mem (c : certificate) (cs : list certificate) : bool :=
  if in_dec certificate_eq_dec c cs then true else false.
Definition nat_mem (i : nat) (xs : list nat) : bool :=
  if in_dec Nat.eq_dec i xs then true else false.
Definition adm_mem (a : adm_tag) (xs : list adm_tag) : bool :=
  if in_dec adm_tag_eq_dec a xs then true else false.
Definition clause_eq_dec : forall x y : clause, {x = y} + {x <> y}.
Proof. repeat decide equality. Defined.
Definition clause_mem (cl : clause) (xs : list clause) : bool :=
  if in_dec clause_eq_dec cl xs then true else false.

Definition usable_b (c : certificate) (s : state) : bool :=
  valid_cert_b c (st_trace s)
  && cert_mem c (st_certs s) && negb (cert_mem c (st_consumed s))
  && (if check_result_eq_dec (cert_kind c) Pass then true else false)
  && (match lookup_nat (cert_id c) (st_obligations s) with
      | Some o =>
          rule_mem (ob_target o) [cert_target c]
          && Nat.eqb (ob_begin o) (cert_begin c)
          && match ob_status o, ob_cert o with
             | StPass, Some c0 =>
                 if certificate_eq_dec c0 c then true else false
             | _,_ => false end
      | None => false end)
  && forallb (fun x => nat_mem (cert_id c) (st_holds s x))
             (block (cert_target c)).

Definition license_valid_b (r : rule) (c : certificate) (s : state) : bool :=
  valid_cert_b c (st_trace s) && cert_mem c (st_consumed s)
  && rule_mem (cert_target c) [r]
  && match lookup_nat (cert_id c) (st_obligations s) with
     | Some o =>
         rule_mem (ob_target o) [r]
         && Nat.eqb (ob_begin o) (cert_begin c)
         && match ob_status o, ob_cert o with
            | StClosed, Some c0 =>
                if certificate_eq_dec c0 c then true else false
            | _,_ => false end
     | None => false end.
Definition Usable c s : Prop := usable_b c s = true.
Definition LicValid r c s : Prop := license_valid_b r c s = true.
Definition logic_if_b (s : state) (r : rule) : bool :=
  enabled_b s r
  && match lookup_rule r (st_licenses s) with
     | Some c => license_valid_b r c s
     | None => false end.
Definition LogicIf s r : Prop := logic_if_b s r = true.

Definition key_nat (p : nat * obligation) := fst p.
Definition key_rule_cert (p : rule * certificate) := fst p.
Definition state_formed (s : state) : Prop :=
  NoDup (st_gamma s)
  /\ (forall r, NoDup (st_holds s r))
  /\ NoDup (map key_nat (st_obligations s))
  /\ NoDup (st_certs s)
  /\ NoDup (st_consumed s)
  /\ (forall c, In c (st_consumed s) -> In c (st_certs s))
  /\ NoDup (map key_rule_cert (st_licenses s))
  /\ st_next s = length (st_trace s).

Definition State (s : state) : Prop :=
  state_formed s
  /\ Forall Cert (st_certs s)
  /\ (forall i o, In (i,o) (st_obligations s) ->
       match ob_cert o with None => True | Some c => Cert c end)
  /\ (forall r c, In (r,c) (st_licenses s) -> Cert c).

Definition nonclosed (o : obligation) : Prop := ob_status o <> StClosed.
Definition token_cover (s : state) (i : nat) (r : rule) : Prop :=
  forall x, In x (block r) -> In i (st_holds s x).
Definition no_token (s : state) (i : nat) : Prop :=
  forall x, ~ In i (st_holds s x).
Definition unique_cert_id (s : state) (c : certificate) : Prop :=
  forall c0, In c0 (st_certs s) -> cert_id c0 = cert_id c -> c0 = c.

Definition obligation_coherent
           (s : state) (io : nat * obligation) : Prop :=
  let '(i,o) := io in
  match ob_status o with
  | StOpen =>
      ob_cert o = None
      /\ nth_error (st_trace s) (ob_begin o) = Some (EvBegin i (ob_target o))
      /\ count_occ event_eq_dec (st_trace s) (EvBegin i (ob_target o)) = 1
      /\ (forall c, In c (st_certs s) -> cert_id c <> i)
      /\ token_cover s i (ob_target o)
  | StPass =>
      exists c, ob_cert o = Some c /\ cert_id c = i
      /\ cert_target c = ob_target o /\ cert_begin c = ob_begin o
      /\ cert_kind c = Pass /\ VCert c (st_trace s)
      /\ In c (st_certs s) /\ unique_cert_id s c
      /\ token_cover s i (ob_target o)
  | StFail =>
      exists c, ob_cert o = Some c /\ cert_id c = i
      /\ cert_target c = ob_target o /\ cert_begin c = ob_begin o
      /\ cert_kind c = Fail /\ VCert c (st_trace s)
      /\ In c (st_certs s) /\ unique_cert_id s c
      /\ token_cover s i (ob_target o)
  | StClosed =>
      exists c, ob_cert o = Some c /\ cert_id c = i
      /\ cert_target c = ob_target o /\ cert_begin c = ob_begin o
      /\ cert_kind c = Pass /\ VCert c (st_trace s)
      /\ In c (st_certs s) /\ In c (st_consumed s) /\ no_token s i
  end.

Definition Coh (s : state) : Prop :=
  State s
  /\ (forall io, In io (st_obligations s) -> obligation_coherent s io)
  /\ (forall c, In c (st_certs s) <->
        exists i o, In (i,o) (st_obligations s) /\ ob_cert o = Some c)
  /\ (forall c, In c (st_consumed s) <->
        exists i o, In (i,o) (st_obligations s)
        /\ ob_status o = StClosed /\ ob_cert o = Some c)
  /\ (forall r c, In (r,c) (st_licenses s) -> LicValid r c s)
  /\ (forall x i, In i (st_holds s x) <->
        exists r o, In (i,o) (st_obligations s)
        /\ ob_target o = r /\ nonclosed o /\ In x (block r)).

Definition empty_holds : rule -> list nat := fun _ => [].
Definition S0 : state :=
  {| st_gamma := [FP; FImpPQ]; st_holds := empty_holds;
     st_obligations := []; st_certs := []; st_consumed := [];
     st_licenses := []; st_trace := []; st_next := 0 |}.

Theorem coh_S0 : Coh S0.
Proof.
  vm_compute. intuition.
  - repeat constructor; simpl; intuition discriminate.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct x0 as [i [o [H _]]]. contradiction.
  - destruct x0 as [i [o [H _]]]. contradiction.
  - destruct x1 as [r [o [H _]]]. contradiction.
Qed.

Definition add_nat (i : nat) (xs : list nat) : list nat :=
  if in_dec Nat.eq_dec i xs then xs else i :: xs.
Definition remove_nat (i : nat) (xs : list nat) : list nat :=
  filter (fun j => negb (Nat.eqb i j)) xs.
Definition add_form (A : form) (xs : list form) : list form :=
  if in_dec form_eq_dec A xs then xs else A :: xs.
Definition add_cert (c : certificate) (xs : list certificate) : list certificate :=
  if in_dec certificate_eq_dec c xs then xs else c :: xs.
Definition map_holds_add (H : rule -> list nat) (r : rule) (i : nat) :=
  fun x => if rule_mem x (block r) then add_nat i (H x) else H x.
Definition map_holds_remove (H : rule -> list nat) (r : rule) (i : nat) :=
  fun x => if rule_mem x (block r) then remove_nat i (H x) else H x.

Definition no_live_target_b (s : state) (r : rule) : bool :=
  forallb
    (fun io => let '(_,o) := io in
       negb (rule_mem (ob_target o) [r])
       || match ob_status o with StClosed => true | _ => false end)
    (st_obligations s).

Definition append_trace (s : state) (e : event) : list event :=
  st_trace s ++ [e].
Definition inspect_delta (s : state) (b : nat) (e : event) :=
  map decl_supp (skipn (S b) (st_trace s) ++ [e]).
Definition make_inspect_cert
  (s : state) (i : nat) (a : rule) (k : check_result)
  (r : rule) (b : nat) : certificate :=
  let e := EvInspect i a k in
  {| cert_kind := k; cert_id := i; cert_target := r; cert_actor := a;
     cert_begin := b; cert_inspect := st_next s; cert_snapshot := code r;
     cert_delta := inspect_delta s b e;
     cert_length := st_next s - b |}.

Definition supports_clear_b (s : state) (b : nat) (r : rule) (e : event) :=
  forallb (fun d => disjoint_rules_b d (block r))
    (map decl_supp (skipn (S b) (st_trace s) ++ [e])).

Definition checked_status (k : check_result) :=
  match k with Pass => StPass | Fail => StFail end.

Definition execute (s : state) (e : event) : option state :=
  match e with
  | EvBegin i r =>
      if enabled_b s r && adm_mem AdmBegin (adm_of r)
         && match lookup_nat i (st_obligations s) with
            | None => true | Some _ => false end
         && no_live_target_b s r
      then Some
        {| st_gamma := st_gamma s;
           st_holds := map_holds_add (st_holds s) r i;
           st_obligations := update_nat i
             {| ob_target := r; ob_begin := st_next s;
                ob_status := StOpen; ob_cert := None |}
             (st_obligations s);
           st_certs := st_certs s; st_consumed := st_consumed s;
           st_licenses := remove_rule_keys (block r) (st_licenses s);
           st_trace := append_trace s e; st_next := S (st_next s) |}
      else None
  | EvInspect i a k =>
      match lookup_nat i (st_obligations s) with
      | Some o =>
          match ob_status o, ob_cert o with
          | StOpen, None =>
              let r := ob_target o in let b := ob_begin o in
              if enabled_b s a && adm_mem AdmInspect (adm_of a)
                 && negb (rule_mem a [r])
                 && (if check_result_eq_dec k (chk r) then true else false)
                 && supports_clear_b s b r e
              then
                let c := make_inspect_cert s i a k r b in
                Some
                 {| st_gamma := st_gamma s; st_holds := st_holds s;
                    st_obligations := update_nat i
                      {| ob_target := r; ob_begin := b;
                         ob_status := checked_status k; ob_cert := Some c |}
                      (st_obligations s);
                    st_certs := add_cert c (st_certs s);
                    st_consumed := st_consumed s;
                    st_licenses := st_licenses s;
                    st_trace := append_trace s e; st_next := S (st_next s) |}
              else None
          | _,_ => None end
      | None => None end
  | EvResume i u c =>
      if (if check_result_eq_dec (cert_kind c) Pass then true else false)
         && Nat.eqb i (cert_id c) && enabled_b s u
         && adm_mem AdmResume (adm_of u)
         && negb (rule_mem u [cert_target c]) && usable_b c s
      then Some
        {| st_gamma := st_gamma s;
           st_holds := map_holds_remove (st_holds s) (cert_target c) i;
           st_obligations := update_nat i
             {| ob_target := cert_target c; ob_begin := cert_begin c;
                ob_status := StClosed; ob_cert := Some c |}
             (st_obligations s);
           st_certs := st_certs s;
           st_consumed := add_cert c (st_consumed s);
           st_licenses := update_rule (cert_target c) c (st_licenses s);
           st_trace := append_trace s e; st_next := S (st_next s) |}
      else None
  | EvInfer r premises conclusion =>
      if logic_if_b s r && clause_mem (premises,conclusion) (logic_of r)
         && forallb (fun A => form_mem A (st_gamma s)) premises
      then Some
        {| st_gamma := add_form conclusion (st_gamma s);
           st_holds := st_holds s; st_obligations := st_obligations s;
           st_certs := st_certs s; st_consumed := st_consumed s;
           st_licenses := st_licenses s; st_trace := append_trace s e;
           st_next := S (st_next s) |}
      else None
  end.

Definition Step (s : state) (e : event) (t : state) : Prop :=
  execute s e = Some t.
Inductive run : state -> list event -> state -> Prop :=
| run_nil : forall s, run s [] s
| run_cons : forall s e t es u,
    Step s e t -> run t es u -> run s (e :: es) u.

Inductive run_states : state -> list event -> list state -> state -> Prop :=
| rs_nil : forall s, run_states s [] [s] s
| rs_cons : forall s e t es states u,
    Step s e t -> run_states t es states u ->
    run_states s (e::es) (s::states) u.

Record run_witness (s t : state) : Type := {
  rw_states : list state;
  rw_events : list event;
  rw_chain : run_states s rw_events rw_states t
}.
Theorem run_states_length :
  forall s es states t, run_states s es states t ->
  length states = S (length es).
Proof.
  intros s es states t H. induction H.
  - reflexivity.
  - cbn. now rewrite IHrun_states.
Qed.
Definition RunJudgement (s t : state) (rw : run_witness s t) : Prop :=
  forall r, LogicIf t r <-> logic_if_b t r = true.
Theorem run_interface_exact :
  forall s t (rw : run_witness s t), @RunJudgement s t rw.
Proof. intros s t rw r. reflexivity. Qed.









End SSTC_TCR_State.
Export SSTC_TCR_State.

(* BEGIN SSTC_TCR_Schedule.v, original line 6 *)
Module SSTC_TCR_Schedule.
Import SSTC_TCR_Core SSTC_TCR_State.

Record boundary : Type := {
  bd_target : rule; bd_actor : rule; bd_snapshot : rule_code;
  bd_prefix : list (list rule); bd_suffix : list (list rule)
}.
Definition boundary_eq_dec : forall x y : boundary, {x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition kappa (c : certificate) (t : nat) : boundary :=
  {| bd_target := cert_target c; bd_actor := cert_actor c;
     bd_snapshot := cert_snapshot c; bd_prefix := firstn t (cert_delta c);
     bd_suffix := skipn t (cert_delta c) |}.
Inductive residual : Type := Mu : boundary -> residual.
Definition residual_eq_dec : forall x y : residual, {x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition ResWord := list residual.
Definition IsBoundary (k : boundary) : Prop :=
  exists c t, Cert c /\ cert_kind c = Pass
              /\ t <= length (cert_delta c) /\ k = kappa c t.
Definition IsResidual (m : residual) : Prop :=
  exists k, IsBoundary k /\ m = Mu k.
Definition ResWordFormed (w : ResWord) : Prop := Forall IsResidual w.
Definition CatalyticObject (s : state) (w : ResWord) : Prop :=
  Coh s /\ ResWordFormed w.

Inductive raw_term : Type :=
| RTId | RTStep : event -> raw_term | RTCat : event -> nat -> raw_term
| RTKres : event -> raw_term | RTEmit : boundary -> raw_term
| RTProbe : boundary -> raw_term | RTComp : raw_term -> raw_term -> raw_term.
Definition non_resume (e : event) : Prop :=
  match e with EvResume _ _ _ => False | _ => True end.
Inductive term_type : raw_term -> state -> ResWord -> state -> ResWord -> Prop :=
| TyId : forall s w, term_type RTId s w s w
| TyStep : forall s w e t, non_resume e -> Step s e t ->
    term_type (RTStep e) s w t w
| TyCat : forall s w i u c t q, Step s (EvResume i u c) q ->
    t <= length (cert_delta c) ->
    term_type (RTCat (EvResume i u c) t) s w q (w ++ [Mu (kappa c t)])
| TyKres : forall s w i u c q, Step s (EvResume i u c) q ->
    term_type (RTKres (EvResume i u c)) s w q w
| TyEmit : forall s w k, IsBoundary k ->
    term_type (RTEmit k) s w s (w ++ [Mu k])
| TyProbe : forall s v k, IsBoundary k ->
    term_type (RTProbe k) s (v ++ [Mu k]) s (v ++ [Mu k])
| TyComp : forall M N s w t v u z,
    term_type M s w t v -> term_type N t v u z ->
    term_type (RTComp M N) s w u z.

Inductive term_equiv : raw_term -> raw_term -> Prop :=
| TE_refl : forall M, term_equiv M M
| TE_sym : forall M N, term_equiv M N -> term_equiv N M
| TE_trans : forall M N P, term_equiv M N -> term_equiv N P -> term_equiv M P
| TE_cat : forall i u c t, term_equiv (RTCat (EvResume i u c) t)
      (RTComp (RTKres (EvResume i u c)) (RTEmit (kappa c t)))
| TE_assoc : forall M N P,
    term_equiv (RTComp (RTComp M N) P) (RTComp M (RTComp N P))
| TE_unit_l : forall M, term_equiv (RTComp RTId M) M
| TE_unit_r : forall M, term_equiv (RTComp M RTId) M
| TE_comp : forall M M0 N N0, term_equiv M M0 -> term_equiv N N0 ->
    term_equiv (RTComp M N) (RTComp M0 N0).
Fixpoint residual_trace (M : raw_term) : ResWord :=
  match M with
  | RTCat (EvResume _ _ c) t => [Mu (kappa c t)]
  | RTEmit k => [Mu k] | RTComp M N => residual_trace M ++ residual_trace N
  | _ => [] end.
Theorem cat_residual_factorization : forall i u c t,
  residual_trace (RTCat (EvResume i u c) t) =
  residual_trace (RTComp (RTKres (EvResume i u c)) (RTEmit (kappa c t))).
Proof. reflexivity. Qed.
Definition Closed (s : state) : Prop := Coh s
  /\ (forall r, st_holds s r = [])
  /\ (forall i o, In (i,o) (st_obligations s) -> ob_status o = StClosed).

Record cert_signature : Type := {
 cs_kind : check_result; cs_target : rule; cs_actor : rule;
 cs_snapshot : rule_code; cs_delta : list (list rule); cs_length : nat
}.
Definition cert_signature_eq_dec :
 forall x y : cert_signature, {x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition cert_sig c :=
 {| cs_kind:=cert_kind c; cs_target:=cert_target c; cs_actor:=cert_actor c;
    cs_snapshot:=cert_snapshot c; cs_delta:=cert_delta c;
    cs_length:=cert_length c |}.
Record obligation_signature : Type := {
 os_target : rule; os_status : obligation_status; os_cert : option cert_signature
}.
Definition obligation_signature_eq_dec :
 forall x y : obligation_signature, {x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition ob_sig o :=
 {| os_target:=ob_target o; os_status:=ob_status o;
    os_cert:=option_map cert_sig (ob_cert o) |}.
Record can_profile : Type := {
 can_gamma : list form; can_enabled : list rule; can_logic_if : list rule;
 can_obligations : list obligation_signature; can_certs : list cert_signature;
 can_consumed : list cert_signature; can_licenses : list (rule*cert_signature)
}.
Definition rule_sig_pair_eq_dec :
 forall x y : rule*cert_signature, {x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition Can (s:state) : can_profile :=
 {| can_gamma:=st_gamma s; can_enabled:=filter (enabled_b s) all_rules;
    can_logic_if:=filter (logic_if_b s) all_rules;
    can_obligations:=map (fun io=>ob_sig (snd io)) (st_obligations s);
    can_certs:=map cert_sig (st_certs s);
    can_consumed:=map cert_sig (st_consumed s);
    can_licenses:=map (fun rc=>(fst rc,cert_sig (snd rc))) (st_licenses s) |}.
Definition form_list_set_eq_b xs ys :=
 forallb (fun x=>form_mem x ys) xs && forallb (fun y=>form_mem y xs) ys.
Definition rule_list_set_eq_b xs ys :=
 forallb (fun x=>rule_mem x ys) xs && forallb (fun y=>rule_mem y xs) ys.
Definition multiset_eq_b {A} (dec:forall x y:A,{x=y}+{x<>y}) xs ys :=
 forallb (fun x=>Nat.eqb (count_occ dec xs x) (count_occ dec ys x)) (xs++ys).
Definition can_eq_b x y :=
 form_list_set_eq_b (can_gamma x) (can_gamma y)
 && rule_list_set_eq_b (can_enabled x) (can_enabled y)
 && rule_list_set_eq_b (can_logic_if x) (can_logic_if y)
 && multiset_eq_b obligation_signature_eq_dec (can_obligations x) (can_obligations y)
 && multiset_eq_b cert_signature_eq_dec (can_certs x) (can_certs y)
 && multiset_eq_b cert_signature_eq_dec (can_consumed x) (can_consumed y)
 && multiset_eq_b rule_sig_pair_eq_dec (can_licenses x) (can_licenses y).
Definition CanEq x y : Prop := can_eq_b x y=true.
Theorem CanEq_dec : forall x y,{CanEq x y}+{~CanEq x y}.
Proof. intros x y; unfold CanEq; destruct(can_eq_b x y);[left|right];congruence. Defined.

Inductive skeleton : Type :=
| Blk : rule->rule->rule->nat->skeleton
| Inf : rule->list form->form->skeleton.
Definition skeleton_eq_dec : forall x y:skeleton,{x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition tagged := (nat*skeleton)%type.
Definition tagged_eq_dec : forall x y:tagged,{x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Fixpoint tag_from (h:nat) (xs:list skeleton) : list tagged :=
 match xs with []=>[] | x::tl=>(h,x)::tag_from (S h) tl end.
Definition Tag (xs:list skeleton) : list tagged := tag_from 0 xs.

Definition obligation_domain (s:state) : list nat := map fst (st_obligations s).
Definition max_domain (s:state) : nat := fold_right Nat.max 0 (obligation_domain s).
Fixpoint nth_missing_fuel (fuel candidate h:nat) (used:list nat) : option nat :=
 match fuel with
 | 0=>None
 | S fuel0=>if in_dec Nat.eq_dec candidate used
   then nth_missing_fuel fuel0 (S candidate) h used
   else match h with 0=>Some candidate
        | S h0=>nth_missing_fuel fuel0 (S candidate) h0 used end
 end.
Definition nu (s:state) (m h:nat) : option nat :=
 nth_missing_fuel (S(max_domain s+length(obligation_domain s)+m))
 0 h (obligation_domain s).

Record run_result : Type := {
 rr_term : raw_term; rr_state : state; rr_word : ResWord
}.
Fixpoint run_loop (initial:state) (total:nat) (current:state) (word:ResWord) (lambda:list tagged) : option run_result :=
 match lambda with
 | []=>Some {|rr_term:=RTId;rr_state:=current;rr_word:=word|}
 | (h,Blk r a u t)::rest=>
   match nu initial total h with None=>None | Some i=>
   match execute current (EvBegin i r) with None=>None | Some s1=>
   match execute s1 (EvInspect i a Pass) with None=>None | Some s2=>
   match lookup_nat i (st_obligations s2) with None=>None | Some o=>
   match ob_cert o with None=>None | Some c=>
   match execute s2 (EvResume i u c) with None=>None | Some s3=>
   if Nat.leb t (length(cert_delta c)) then
    let k:=kappa c t in
    match run_loop initial total s3 (word++[Mu k]) rest with
    | None=>None | Some z=>Some {|rr_term:=RTComp (RTStep(EvBegin i r)) (RTComp (RTStep(EvInspect i a Pass)) (RTComp (RTCat(EvResume i u c)t)(rr_term z)));
      rr_state:=rr_state z;rr_word:=rr_word z|} end
   else None end end end end end end
 | (h,Inf r ps q)::rest=>
   match execute current (EvInfer r ps q) with None=>None | Some s1=>
   match run_loop initial total s1 word rest with None=>None | Some z=>
    Some {|rr_term:=RTComp(RTStep(EvInfer r ps q))(rr_term z);
      rr_state:=rr_state z;rr_word:=rr_word z|} end end
 end.
Definition Run (s:state) (w:ResWord) (lambda:list tagged) : option run_result := run_loop s (length lambda) s w lambda.
Definition run_defined_b (s:state) (w:ResWord) (l:list tagged) : bool := match Run s w l with Some _=>true|None=>false end.
Definition inc (w:ResWord) (z:run_result) : ResWord := skipn (length w) (rr_word z).
Theorem Run_deterministic : forall s w l x y,
 Run s w l=Some x->Run s w l=Some y->x=y.
Proof. intros;congruence. Qed.

Theorem run_loop_typed : forall lambda initial total current word z,
 run_loop initial total current word lambda=Some z ->
 term_type (rr_term z) current word (rr_state z) (rr_word z).
Proof.
 induction lambda as [|[h sk] rest IH];
 intros initial total current word z Hrun.
 - cbn [run_loop] in Hrun. inversion Hrun; subst. constructor.
 - destruct sk as [r a u t|r ps q].
   + cbn [run_loop] in Hrun.
     destruct (nu initial total h) as [i|] eqn:Hnu;try discriminate.
     destruct (execute current (EvBegin i r)) as [s1|] eqn:Hbeg;
       try discriminate.
     destruct (execute s1 (EvInspect i a Pass)) as [s2|] eqn:Hins;
       try discriminate.
     destruct (lookup_nat i (st_obligations s2)) as [o|] eqn:Hlook;
       try discriminate.
     destruct (ob_cert o) as [c|] eqn:Hcert;try discriminate.
     destruct (execute s2 (EvResume i u c)) as [s3|] eqn:Hres;
       try discriminate.
     destruct (Nat.leb t (length (cert_delta c))) eqn:Hle;
       try discriminate.
     destruct (run_loop initial total s3 (word++[Mu(kappa c t)]) rest)
       as [z0|] eqn:Hrec;try discriminate.
     injection Hrun as Hz;subst z;cbn.
     eapply TyComp.
     * eapply TyStep;[exact I|unfold Step;exact Hbeg].
     * eapply TyComp.
       -- eapply TyStep;[exact I|unfold Step;exact Hins].
       -- eapply TyComp.
          ++ eapply TyCat;[unfold Step;exact Hres|].
             apply Nat.leb_le. exact Hle.
          ++ eapply IH. exact Hrec.
   + cbn [run_loop] in Hrun.
     destruct (execute current (EvInfer r ps q)) as [s1|] eqn:Hinf;
       try discriminate.
     destruct (run_loop initial total s1 word rest) as [z0|] eqn:Hrec;
       try discriminate.
     injection Hrun as Hz;subst z;cbn.
     eapply TyComp.
     * eapply TyStep;[exact I|unfold Step;exact Hinf].
     * eapply IH. exact Hrec.
Qed.

Theorem Run_returns_typed_term : forall s w lambda z,
 Run s w lambda=Some z ->
 term_type (rr_term z) s w (rr_state z) (rr_word z).
Proof. intros. eapply run_loop_typed. exact H. Qed.

Fixpoint insertions {A} (x:A) (xs:list A) : list (list A) :=
 match xs with []=>[[x]]|y::tl=>(x::xs)::map(cons y)(insertions x tl) end.
Fixpoint permutations {A} (xs:list A) : list (list A) :=
 match xs with []=>[[]]|x::tl=>flat_map(insertions x)(permutations tl) end.
Definition permutation_b (xs ys:list tagged) : bool :=
 Nat.eqb(length xs)(length ys)&&multiset_eq_b tagged_eq_dec xs ys.
Definition Vertex_b (s:state) (w:ResWord) (xi:list skeleton) (l:list tagged) : bool := permutation_b(Tag xi)l&&run_defined_b s w l.
Definition Vert (s:state) (w:ResWord) (xi:list skeleton) : list (list tagged) := filter(Vertex_b s w xi)(permutations(Tag xi)).

Record swap_context := {sw_prefix:list tagged;sw_left:tagged;
 sw_right:tagged;sw_suffix:list tagged}.
Definition prefix_swap_context (x:tagged) (c:swap_context) : swap_context :=
 {| sw_prefix:=x::sw_prefix c; sw_left:=sw_left c;
    sw_right:=sw_right c; sw_suffix:=sw_suffix c |}.
Fixpoint swap_contexts (xs:list tagged) : list swap_context :=
 match xs with
 | [] => []
 | x :: tail =>
   let later:=map (prefix_swap_context x) (swap_contexts tail) in
   match tail with
   | [] => []
   | y :: tl =>
     {|sw_prefix:=[];sw_left:=x;sw_right:=y;sw_suffix:=tl|} :: later
   end
 end.
Definition swapped (c:swap_context) : list tagged:=sw_prefix c++sw_right c::sw_left c::sw_suffix c.
Definition tagged_list_eq_dec : forall x y:list tagged,{x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition tagged_list_eq_b x y:=if tagged_list_eq_dec x y then true else false.
Definition local_pair_can_eq_b s w total c :=
 match run_loop s total s w (sw_prefix c) with None=>false | Some p=>
 match run_loop s total (rr_state p)(rr_word p)[sw_left c;sw_right c],
       run_loop s total (rr_state p)(rr_word p)[sw_right c;sw_left c] with
 | Some x,Some y=>can_eq_b(Can(rr_state x))(Can(rr_state y))|_,_=>false end end.
Definition E_b s w l l0 :=
 run_defined_b s w l&&run_defined_b s w l0&&
 existsb(fun c=>tagged_list_eq_b l0(swapped c)&&
  local_pair_can_eq_b s w (length l)c)(swap_contexts l).
Definition E s w l l0 : Prop := E_b s w l l0=true.
Theorem E_dec : forall s w x y,{E s w x y}+{~E s w x y}.
Proof. intros;unfold E;destruct(E_b s w x y);[left|right];congruence. Defined.
Inductive EPath (s:state) (w:ResWord) :
  list tagged -> list tagged -> Prop :=
| EP_refl : forall l,EPath s w l l
| EP_step : forall l m n,EPath s w l m ->
    (E s w m n \/ E s w n m) -> EPath s w l n.
Definition D_semantic s w xi l : Prop :=
  Vertex_b s w xi l=true /\ EPath s w (Tag xi) l.
Definition Orb_semantic s w xi z : Prop :=
  exists l,D_semantic s w xi l /\ Run s w l=Some z.
Definition Omega_semantic s w xi out : Prop :=
  exists z,Orb_semantic s w xi z /\ inc w z=out.
Definition add_tagged_list x xs :=
 if in_dec tagged_list_eq_dec x xs then xs else xs++[x].
Definition adjacent_to_b s w x y:=E_b s w x y||E_b s w y x.
Definition expand_reached s w verts reached :=
 fold_left(fun acc v=>if existsb(fun u=>adjacent_to_b s w u v)acc
  then add_tagged_list v acc else acc)verts reached.
Fixpoint saturate s w fuel verts reached :=
 match fuel with 0=>reached|S n=>saturate s w n verts(expand_reached s w verts reached)end.
Definition D_branch s w xi :=
 let vs:=Vert s w xi in saturate s w (length vs) vs [Tag xi].
Definition orbit s w xi :=
 fold_right(fun l acc=>match Run s w l with Some z=>z::acc|None=>acc end)
 [] (D_branch s w xi).
Definition Omega s w xi:=map(inc w)(orbit s w xi).

Definition rule_rank r:=match r with Rho=>0|Alpha=>1|Upsilon=>2|Beta=>3|Delta=>4 end.
Definition form_rank A:=match A with FP=>0|FQ=>1|FImpPQ=>2 end.
Fixpoint nat_list_leb xs ys :=
 match xs,ys with [],_=>true|_::_,[]=>false|x::xt,y::yt=>
 if Nat.ltb x y then true else if Nat.eqb x y then nat_list_leb xt yt else false end.
Definition skeleton_key x:=match x with
 | Blk r a u t=>[0;rule_rank r;rule_rank a;rule_rank u;t]
 | Inf r ps q=>1::rule_rank r::map form_rank ps++[99;form_rank q] end.
Fixpoint skeleton_list_key xs:=match xs with []=>[]|x::tl=>
 length(skeleton_key x)::skeleton_key x++skeleton_list_key tl end.
Definition skeleton_list_leb xs ys:=nat_list_leb(skeleton_list_key xs)(skeleton_list_key ys).
Definition strip_tags (xs:list tagged) : list skeleton:=map snd xs.
Fixpoint min_skeleton_lists (best:list skeleton) (xs:list(list skeleton)) : list skeleton:=match xs with []=>best|x::tl=>
 min_skeleton_lists(if skeleton_list_leb x best then x else best)tl end.
Definition Base (s:state) (w:ResWord) (xi:list skeleton) : list skeleton:=match map strip_tags(D_branch s w xi)with
 | []=>[]|x::tl=>min_skeleton_lists x tl end.

Record ceq := {ce_source:state;ce_input:ResWord;ce_base:list skeleton;
 ce_source_can:can_profile;ce_target_cans:list can_profile;
 ce_D:list tagged->Prop;ce_Orb:run_result->Prop;ce_Omega:ResWord->Prop;
 ce_domain:list(list tagged);ce_orbit:list run_result;ce_omega:list ResWord}.
Definition CEq (s:state) (w:ResWord) (xi:list skeleton) : option ceq :=
 match Run s w (Tag xi) with None=>None|Some _=>
 let os:=orbit s w xi in Some {|ce_source:=s;ce_input:=w;ce_base:=Base s w xi;
 ce_source_can:=Can s;ce_target_cans:=map(fun z=>Can(rr_state z))os;
 ce_D:=D_semantic s w xi;ce_Orb:=Orb_semantic s w xi;
 ce_Omega:=Omega_semantic s w xi;
 ce_domain:=D_branch s w xi;ce_orbit:=os;ce_omega:=map(inc w)os|} end.
Definition all_can_eq_b (x:can_profile) (xs:list can_profile) : bool :=
 forallb (can_eq_b x) xs.
Definition common_target (e:ceq) : option can_profile :=
 match ce_target_cans e with
 | []=>None
 | x::tl=>if all_can_eq_b x tl then Some x else None
 end.
Definition ceq_comp (e f:ceq) : option ceq:=match common_target e with None=>None|Some t=>
 if can_eq_b t(ce_source_can f)
 then CEq(ce_source e)(ce_input e)(ce_base e++ce_base f)else None end.
Theorem Vert_finite : forall s w xi,exists xs,xs=Vert s w xi.
Proof. intros;eexists;reflexivity. Qed.
Theorem D_branch_finite : forall s w xi,exists xs,xs=D_branch s w xi.
Proof. intros;eexists;reflexivity. Qed.












End SSTC_TCR_Schedule.
Export SSTC_TCR_Schedule.

(* BEGIN SSTC_TCR_Critical.v, original line 6 *)
Module SSTC_TCR_Critical.
Import SSTC_TCR_Core SSTC_TCR_State SSTC_TCR_Schedule.

Inductive foot_atom : Type :=
| FObligation : rule -> foot_atom
| FCertificate : rule -> rule -> foot_atom
| FConsumption : rule -> rule -> foot_atom
| FLicense : rule -> foot_atom
| FFormula : form -> foot_atom.
Definition foot_atom_eq_dec :
  forall x y : foot_atom, {x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition Foot (x:skeleton) : list foot_atom :=
 match x with
 | Blk r a _ _ =>
   [FObligation r;FCertificate r a;FConsumption r a;FLicense r]
 | Inf _ _ q => [FFormula q]
 end.
Definition foot_mem x xs :=
 if in_dec foot_atom_eq_dec x xs then true else false.
Definition foot_intersection x y :=
 filter (fun z=>foot_mem z (Foot y)) (Foot x).
Definition overlap_b x y :=
 match foot_intersection x y with []=>false|_=>true end.

Definition local_pair_can_diff_b s w total c :=
 match run_loop s total s w (sw_prefix c) with
 | None=>false
 | Some p=>
   match run_loop s total (rr_state p)(rr_word p)[sw_left c;sw_right c],
         run_loop s total (rr_state p)(rr_word p)[sw_right c;sw_left c] with
   | Some x,Some y=>negb(can_eq_b(Can(rr_state x))(Can(rr_state y)))
   | _,_=>false end
 end.
Definition context_overlap_b c :=
 overlap_b (snd(sw_left c)) (snd(sw_right c)).
Definition C_b s w l l0 :=
 run_defined_b s w l&&run_defined_b s w l0&&
 existsb(fun c=>tagged_list_eq_b l0(swapped c)&&context_overlap_b c&&
   local_pair_can_diff_b s w (length l)c)(swap_contexts l).
Definition CEdge s w l l0 : Prop := C_b s w l l0=true.
Theorem CEdge_dec : forall s w x y,{CEdge s w x y}+{~CEdge s w x y}.
Proof. intros;unfold CEdge;destruct(C_b s w x y);[left|right];congruence. Defined.

Definition pair_code x y := ((x+y)*S(x+y))/2+y.
Fixpoint encode_list {A}(f:A->nat)(xs:list A) :=
 match xs with []=>0|x::tl=>S(pair_code(f x)(encode_list f tl))end.
Fixpoint insert_nat (x:nat) (xs:list nat) : list nat :=
 match xs with []=>[x]|y::tl=>if x<=?y then x::xs else y::insert_nat x tl end.
Fixpoint sort_nat (xs:list nat) : list nat :=
 match xs with []=>[]|x::tl=>insert_nat x(sort_nat tl)end.
Definition encode_multiset {A}(f:A->nat)(xs:list A) :=
 encode_list (fun n=>n) (sort_nat(map f xs)).
Definition check_rank k:=match k with Pass=>0|Fail=>1 end.
Definition adm_rank a:=match a with AdmBegin=>0|AdmInspect=>1|AdmResume=>2 end.
Definition kat_rank k:=match k with
 K_wf=>0|K_truth=>1|K_deps=>2|K_ownbegin=>3|K_foreignresume=>4 end.
Definition rule_set_code xs:=encode_multiset rule_rank xs.
Definition clause_code (cl:clause) :=
 pair_code(encode_list form_rank(fst cl))(form_rank(snd cl)).
Definition rcode_code c :=
 pair_code(rule_rank(rc_name c))
  (pair_code(encode_multiset clause_code(rc_logic c))
   (pair_code(encode_multiset adm_rank(rc_adm c))
    (pair_code(encode_multiset rule_rank(rc_dep0 c))
     (pair_code(encode_multiset rule_rank(rc_alias c))
      (encode_multiset kat_rank(rc_kats c)))))).
Definition sig_code c :=
 pair_code(check_rank(cs_kind c))
  (pair_code(rule_rank(cs_target c))
   (pair_code(rule_rank(cs_actor c))
    (pair_code(rcode_code(cs_snapshot c))
     (pair_code(encode_list rule_set_code(cs_delta c))
                (cs_length c))))).
Definition osig_code o :=
 pair_code(rule_rank(os_target o))
  (pair_code(match os_status o with
   |StOpen=>0|StPass=>1|StFail=>2|StClosed=>3 end)
   (match os_cert o with None=>0|Some c=>S(sig_code c)end)).
Definition rule_sig_code p:=pair_code(rule_rank(fst p))(sig_code(snd p)).
Definition can_code c :=
 pair_code(encode_multiset form_rank(can_gamma c))
  (pair_code(encode_multiset rule_rank(can_enabled c))
   (pair_code(encode_multiset rule_rank(can_logic_if c))
    (pair_code(encode_multiset osig_code(can_obligations c))
     (pair_code(encode_multiset sig_code(can_certs c))
      (pair_code(encode_multiset sig_code(can_consumed c))
                 (encode_multiset rule_sig_code(can_licenses c))))))).
Definition boundary_code k :=
 pair_code(rule_rank(bd_target k))
  (pair_code(rule_rank(bd_actor k))
   (pair_code(rcode_code(bd_snapshot k))
    (pair_code(encode_list rule_set_code(bd_prefix k))
               (encode_list rule_set_code(bd_suffix k))))).
Definition residual_code m:=match m with Mu k=>boundary_code k end.
Definition word_code w:=encode_list residual_code w.
Definition skeleton_leb x y:=nat_list_leb(skeleton_key x)(skeleton_key y).
Definition min_skeleton_pair x y:=if skeleton_leb x y then (x,y)else(y,x).
Definition min_can_pair x y:=if can_code x<=?can_code y then(x,y)else(y,x).
Definition min_word_pair x y:=if word_code x<=?word_code y then(x,y)else(y,x).

Record critical_residual : Type := {
 cr_skeletons : skeleton*skeleton;
 cr_overlap : list foot_atom;
 cr_ends : can_profile*can_profile;
 cr_outputs : ResWord*ResWord
}.
Definition critical_residual_eq_dec :
 forall x y:critical_residual,{x=y}+{x<>y}.
Proof. repeat decide equality. Defined.

Definition critical_context l l0 :=
 find(fun c=>tagged_list_eq_b l0(swapped c))(swap_contexts l).
Definition critical_residual_of s w l l0 : option critical_residual :=
 match critical_context l l0,Run s w l,Run s w l0 with
 | Some c,Some x,Some y=>
   let A:=snd(sw_left c) in let B:=snd(sw_right c) in
   let K0:=Can(rr_state x) in let K1:=Can(rr_state y) in
   Some {|cr_skeletons:=min_skeleton_pair A B;
          cr_overlap:=foot_intersection A B;
          cr_ends:=min_can_pair K0 K1;
          cr_outputs:=min_word_pair(inc w x)(inc w y)|}
 | _,_,_=>None end.
Definition Crit s w l l0 chi : Prop :=
 CEdge s w l l0 /\ critical_residual_of s w l l0=Some chi.
Theorem critical_residual_unique :
 forall s w l l0 x y,Crit s w l l0 x->Crit s w l l0 y->x=y.
Proof. intros s w l l0 x y[_ Hx][_ Hy]. congruence. Qed.

Record bicont : Type := {
 bc_parent : critical_residual;
 bc_left : ceq;
 bc_right : ceq
}.
Record child_residual : Type := {
 child_parent : critical_residual;
 child_left_base : list skeleton;
 child_right_base : list skeleton;
 child_targets : can_profile*can_profile
}.
Definition child_residual_eq_dec :
 forall x y:child_residual,{x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition ceq_common_b (e:ceq) : bool :=
 match ce_target_cans e with
 | []=>false
 | x::tl=>forallb(fun y=>can_eq_b x y)tl
 end.
Definition child_of expected left_end right_end (b:bicont) : option child_residual :=
 if critical_residual_eq_dec expected (bc_parent b) then
 if can_eq_b left_end(ce_source_can(bc_left b))&&
    can_eq_b right_end(ce_source_can(bc_right b))&&
    ceq_common_b(bc_left b)&&ceq_common_b(bc_right b) then
 match common_target(bc_left b),common_target(bc_right b)with
 |Some x,Some y=>Some{|child_parent:=expected;
   child_left_base:=ce_base(bc_left b);child_right_base:=ce_base(bc_right b);
   child_targets:=min_can_pair x y|}
 |_,_=>None end
 else None else None.

Record bicont_result : Type := {
 br_parent : critical_residual; br_child : child_residual;
 br_M0 : raw_term; br_N0 : raw_term; br_M1 : raw_term; br_N1 : raw_term;
 br_K0 : can_profile; br_K1 : can_profile;
 br_K0p : can_profile; br_K1p : can_profile
}.
Definition bicont_result_of s w l l0 expected (b:bicont) : option bicont_result :=
 if C_b s w l l0 then
 match critical_residual_of s w l l0 with
 | Some actual =>
   if critical_residual_eq_dec actual expected then
   match Run s w l,Run s w l0,ce_orbit(bc_left b),ce_orbit(bc_right b)with
   |Some z0,Some z1,n0::_,n1::_=>
    let K0:=Can(rr_state z0)in let K1:=Can(rr_state z1)in
    match child_of expected K0 K1 b with
    |None=>None|Some ch=>Some{|br_parent:=expected;br_child:=ch;
     br_M0:=rr_term z0;br_N0:=rr_term n0;br_M1:=rr_term z1;br_N1:=rr_term n1;
     br_K0:=K0;br_K1:=K1;br_K0p:=Can(rr_state n0);br_K1p:=Can(rr_state n1)|}end
   |_,_,_,_=>None end
   else None
 | None=>None end
 else None.
Theorem child_residual_unique :
 forall s w l l0 chi b x y,
 bicont_result_of s w l l0 chi b=Some x->
 bicont_result_of s w l l0 chi b=Some y->x=y.
Proof. intros;congruence. Qed.
Definition CEqCommon (e:ceq) (I:can_profile) : Prop :=
  forall z,ce_Orb e z -> CanEq (Can(rr_state z)) I.
Definition BicontValid s w l l0 expected (b:bicont) : Prop :=
  Crit s w l l0 expected /\ bc_parent b=expected
  /\ exists z0 z1,Run s w l=Some z0 /\ Run s w l0=Some z1
  /\ CanEq (Can(rr_state z0)) (ce_source_can(bc_left b))
  /\ CanEq (Can(rr_state z1)) (ce_source_can(bc_right b))
  /\ (exists I,common_target(bc_left b)=Some I /\ CEqCommon(bc_left b)I)
  /\ (exists I,common_target(bc_right b)=Some I /\ CEqCommon(bc_right b)I).
Definition BicontResult s w l l0 expected b R : Prop :=
  BicontValid s w l l0 expected b
  /\ bicont_result_of s w l l0 expected b=Some R.
Theorem BicontResult_unique :
 forall s w l l0 chi b x y,
 BicontResult s w l l0 chi b x -> BicontResult s w l l0 chi b y -> x=y.
Proof. intros s w l l0 chi b x y [_ Hx][_ Hy]. congruence. Qed.

Definition schedule_pair := (list tagged*list tagged)%type.
Definition all_schedule_pairs (xs:list(list tagged)) : list schedule_pair :=
 flat_map(fun x=>map(fun y=>(x,y))xs)xs.
Definition E_edges s w xi :=
 filter(fun p=>E_b s w(fst p)(snd p))(all_schedule_pairs(Vert s w xi)).
Definition C_edges s w xi :=
 filter(fun p=>C_b s w(fst p)(snd p))(all_schedule_pairs(Vert s w xi)).
Record critical_entry : Type := {
 entry_left:list tagged;entry_right:list tagged;entry_residual:critical_residual
}.
Definition CritSet s w xi :=
 fold_right(fun p acc=>match critical_residual_of s w(fst p)(snd p)with
 |Some chi=>{|entry_left:=fst p;entry_right:=snd p;
   entry_residual:=chi|}::acc|None=>acc end)[](C_edges s w xi).
Definition all_orbit s w xi :=
 fold_right(fun l acc=>match Run s w l with Some z=>z::acc|None=>acc end)
 [] (Vert s w xi).
Definition OmegaAll s w xi:=map(inc w)(all_orbit s w xi).

Record tri_object : Type := {
 tri_vertices:list(list tagged);
 tri_E:list schedule_pair;
 tri_C:list schedule_pair;
 tri_ceq:ceq;
 tri_critset:list critical_entry;
 tri_omega_all:list ResWord
}.
Definition Tri s w xi : option tri_object :=
 match CEq s w xi with
 |None=>None|Some e=>Some{|tri_vertices:=Vert s w xi;
   tri_E:=E_edges s w xi;tri_C:=C_edges s w xi;tri_ceq:=e;
   tri_critset:=CritSet s w xi;tri_omega_all:=OmegaAll s w xi|}end.

Definition TCR_judgement s w xi B tr I : Prop :=
 CatalyticObject s w /\ Run s w(Tag xi)<>None /\ Tri s w xi=Some tr
 /\ common_target(tri_ceq tr)=Some I
 /\ (forall z,ce_Orb(tri_ceq tr)z->CanEq (Can(rr_state z)) I)
 /\ forall z,ce_Orb(tri_ceq tr)z->In B(st_gamma(rr_state z)).

Theorem finite_decidable_layer :
 forall s w xi,
 (exists xs,xs=Vert s w xi)/\(exists es,es=E_edges s w xi)
 /\(exists cs,cs=C_edges s w xi)/\(exists ks,ks=CritSet s w xi).
Proof. intros;repeat split;eexists;reflexivity. Qed.
Definition schedule_pair_eq_dec :
 forall x y:schedule_pair,{x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Definition critical_entry_eq_dec :
 forall x y:critical_entry,{x=y}+{x<>y}.
Proof. repeat decide equality. Defined.
Theorem Vert_member_dec :
 forall s w xi l,{In l(Vert s w xi)}+{~In l(Vert s w xi)}.
Proof. intros;apply in_dec;exact tagged_list_eq_dec. Defined.
Theorem E_edges_member_dec :
 forall s w xi p,{In p(E_edges s w xi)}+{~In p(E_edges s w xi)}.
Proof. intros;apply in_dec;exact schedule_pair_eq_dec. Defined.
Theorem C_edges_member_dec :
 forall s w xi p,{In p(C_edges s w xi)}+{~In p(C_edges s w xi)}.
Proof. intros;apply in_dec;exact schedule_pair_eq_dec. Defined.
Theorem CritSet_member_dec :
 forall s w xi k,{In k(CritSet s w xi)}+{~In k(CritSet s w xi)}.
Proof. intros;apply in_dec;exact critical_entry_eq_dec. Defined.

Definition A_critical:=Blk Alpha Upsilon Upsilon 0.
Definition B_critical:=Blk Alpha Rho Upsilon 0.
Definition critical_xi:=[A_critical;B_critical].
Definition critical_left:=Tag critical_xi.
Definition critical_right:=[(1,B_critical);(0,A_critical)].
Definition critical_ctx : swap_context :=
 {|sw_prefix:=[];sw_left:=(0,A_critical);sw_right:=(1,B_critical);
   sw_suffix:=[]|}.
Lemma critical_left_defined :
 run_defined_b S0 [] critical_left=true.
Proof. vm_compute. reflexivity. Qed.
Lemma critical_right_defined :
 run_defined_b S0 [] critical_right=true.
Proof. vm_compute. reflexivity. Qed.
Lemma critical_local_diff :
 local_pair_can_diff_b S0 [] 2 critical_ctx=true.
Proof. vm_compute. reflexivity. Qed.
Lemma critical_existsb :
 existsb(fun c=>tagged_list_eq_b critical_right(swapped c)&&
  context_overlap_b c&&local_pair_can_diff_b S0 [](length critical_left)c)
  (swap_contexts critical_left)=true.
Proof.
 change (local_pair_can_diff_b S0 [] 2 critical_ctx=true).
 exact critical_local_diff.
Qed.
Theorem prescribed_critical_example :
 C_b S0 [] critical_left critical_right=true.
Proof.
 unfold C_b.
 rewrite critical_left_defined,critical_right_defined,critical_existsb.
 reflexivity.
Qed.
Lemma run_defined_some : forall s w l,
 run_defined_b s w l=true -> exists z,Run s w l=Some z.
Proof.
 intros s w l H. unfold run_defined_b in H.
 destruct (Run s w l) eqn:Hr;[eauto|discriminate].
Qed.
Lemma find_some_from_exists : forall (A:Type)(f:A->bool) xs,
 (exists x,In x xs /\ f x=true)->exists y,find f xs=Some y.
Proof.
 intros A f xs [x [Hin Hfx]]. induction xs as [|a tl IH].
 - contradiction.
 - simpl in Hin. destruct Hin as [Heq|Hin].
   + subst a. simpl. rewrite Hfx. eauto.
   + simpl. destruct (f a) eqn:Ha;[eauto|].
     apply IH. exact Hin.
Qed.
Lemma critical_edge_has_residual : forall s w l l0,
 CEdge s w l l0 -> exists chi,critical_residual_of s w l l0=Some chi.
Proof.
 intros s w l l0 HC. unfold CEdge,C_b in HC.
 apply andb_true_iff in HC as [Hrunpair Hctx].
 apply andb_true_iff in Hrunpair as [Hr Hr0].
 destruct (@run_defined_some s w l Hr) as [z Hz].
 destruct (@run_defined_some s w l0 Hr0) as [z0 Hz0].
 apply existsb_exists in Hctx.
 destruct Hctx as [c [Hcin Hcb]].
 apply andb_true_iff in Hcb as [Htagover _].
 apply andb_true_iff in Htagover as [Heq _].
 assert (Hsome:exists d,critical_context l l0=Some d).
 { unfold critical_context. apply find_some_from_exists.
   exists c. split;assumption. }
 destruct Hsome as [d Hd].
 unfold critical_residual_of. rewrite Hd,Hz,Hz0.
 eexists. reflexivity.
Qed.
Lemma critical_residual_present :
 exists chi,critical_residual_of S0 [] critical_left critical_right=Some chi.
Proof. apply critical_edge_has_residual. exact prescribed_critical_example. Qed.
Theorem prescribed_critical_has_unique_residual :
 exists chi,Crit S0 [] critical_left critical_right chi /\
 forall z,Crit S0 [] critical_left critical_right z->z=chi.
Proof.
 destruct critical_residual_present as [chi Hchi].
 exists chi. split.
 - split;[exact prescribed_critical_example|exact Hchi].
 - intros z Hz. eapply critical_residual_unique.
   + exact Hz.
   + split;[exact prescribed_critical_example|exact Hchi].
Qed.

Record equivalent_schedule_system:Type:={eqs_data:ceq}.
Record single_track_system:Type:={sts_source:state;sts_result:run_result}.
Record transition_only_system:Type:={tos_state:state}.
Definition delete_critical (t:tri_object):equivalent_schedule_system:=
 {|eqs_data:=tri_ceq t|}.
Definition delete_schedule (e:ceq):list single_track_system:=
 map(fun z=>{|sts_source:=ce_source e;sts_result:=z|})(ce_orbit e).
Definition delete_catalysis (z:single_track_system):transition_only_system:=
 {|tos_state:=rr_state(sts_result z)|}.
Theorem critical_deletion_exact :
 forall t,eqs_data(delete_critical t)=tri_ceq t.
Proof. reflexivity. Qed.
Theorem schedule_deletion_exact :
 forall e,delete_schedule e=
 map(fun z=>{|sts_source:=ce_source e;sts_result:=z|})(ce_orbit e).
Proof. reflexivity. Qed.
Theorem catalytic_deletion_exact :
 forall z,tos_state(delete_catalysis z)=rr_state(sts_result z).
Proof. reflexivity. Qed.

Definition rho_program:=[Blk Rho Alpha Alpha 0;Inf Rho[FP;FImpPQ]FQ].
Theorem explicit_run_derives_q :
 exists z,Run S0 [](Tag rho_program)=Some z /\ In FQ(st_gamma(rr_state z)).
Proof. vm_compute. eexists. split;[reflexivity|now left]. Qed.
Definition registry_model_b :=
 forallb(fun r=>match chk r with Pass=>truth_b r|Fail=>true end)all_rules.
Theorem registry_has_boolean_model : registry_model_b=true.
Proof. vm_compute. reflexivity. Qed.
Record satisfiable_model : Type := {
 model_valuation:valuation;
 model_initial_p:eval model_valuation FP=true;
 model_initial_imp:eval model_valuation FImpPQ=true;
 model_pass_rules:registry_model_b=true
}.
Definition concrete_satisfiable_model : satisfiable_model :=
 {|model_valuation:=explicit_model;
   model_initial_p:=proj1 explicit_model_initial;
   model_initial_imp:=proj2 explicit_model_initial;
   model_pass_rules:=registry_has_boolean_model|}.
Theorem system_nontrivial :
 FP<>FQ /\ eval explicit_model FP=true /\ eval beta_countermodel FQ=false.
Proof.
 split.
 - discriminate.
 - split;reflexivity.
Qed.

Record sstc_tcr_package : Type := {
 pkg_forms:list form;pkg_valuations:list valuation;
 pkg_eval:valuation->form->bool;
 pkg_rules:list rule;pkg_code:rule->rule_code;pkg_check:rule->check_result;
 pkg_event_formed:event->Prop;pkg_cert:certificate->Prop;
 pkg_vcert:certificate->list event->Prop;
 pkg_state:state->Prop;pkg_coh:state->Prop;
 pkg_step:state->event->state->Prop;pkg_initial:state;
 pkg_residual:residual->Prop;
 pkg_term_type:raw_term->state->ResWord->state->ResWord->Prop;
 pkg_run:state->ResWord->list tagged->option run_result;
 pkg_can:state->can_profile;pkg_ceq:state->ResWord->list skeleton->option ceq;
 pkg_crit:state->ResWord->list tagged->list tagged->critical_residual->Prop;
 pkg_tri:state->ResWord->list skeleton->option tri_object;
 pkg_tcr:state->ResWord->list skeleton->form->tri_object->can_profile->Prop
}.
Definition SSTC_TCR : sstc_tcr_package :=
 {|pkg_forms:=all_forms;pkg_valuations:=all_valuations;pkg_eval:=eval;
   pkg_rules:=all_rules;pkg_code:=code;pkg_check:=chk;
   pkg_event_formed:=EventFormed;pkg_cert:=Cert;pkg_vcert:=VCert;
   pkg_state:=State;pkg_coh:=Coh;pkg_step:=Step;pkg_initial:=S0;
   pkg_residual:=IsResidual;pkg_term_type:=term_type;
   pkg_run:=Run;pkg_can:=Can;pkg_ceq:=CEq;pkg_crit:=Crit;
   pkg_tri:=Tri;pkg_tcr:=TCR_judgement|}.

End SSTC_TCR_Critical.
Export SSTC_TCR_Critical.

(* Original aggregate checks and assumption audit. *)

Check SSTC_TCR.
Check prescribed_critical_example.
Check prescribed_critical_has_unique_residual.
Check explicit_run_derives_q.
Check registry_has_boolean_model.
Check system_nontrivial.

Print Assumptions prescribed_critical_example.
Print Assumptions prescribed_critical_has_unique_residual.
Print Assumptions explicit_run_derives_q.
Print Assumptions registry_has_boolean_model.
Print Assumptions system_nontrivial.