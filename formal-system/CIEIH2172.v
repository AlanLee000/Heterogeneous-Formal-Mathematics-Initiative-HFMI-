From Stdlib Require Import List Bool Arith Lia PeanoNat Arith.Cantor Relations
  Relation_Definitions.
Import ListNotations.
Set Implicit Arguments.

Module CIEIH2172.

(** 1--3. Finite signatures, de Bruijn formulae, FV and renaming. *)

Definition relsym := nat.
Definition signature := list (relsym * nat).

Fixpoint lookup_arity (R : relsym) (S : signature) : option nat :=
  match S with
  | [] => None
  | (Q,a) :: tl => if Nat.eqb R Q then Some a else lookup_arity R tl
  end.

Definition declaration_eqb (x y : relsym * nat) : bool :=
  Nat.eqb (fst x) (fst y) && Nat.eqb (snd x) (snd y).

Definition sig_eqb (S T : signature) : bool :=
  forallb (fun d => existsb (declaration_eqb d) T) S &&
  forallb (fun d => existsb (declaration_eqb d) S) T.

Definition subsig (D S : signature) : bool :=
  forallb (fun d => existsb (declaration_eqb d) S) D.

Inductive fm : Type :=
| EqF : nat -> nat -> fm
| AtF : relsym -> list nat -> fm
| NegF : fm -> fm
| AndF : fm -> fm -> fm
| ExF : fm -> fm.

Fixpoint all_lt (k : nat) (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: tl => (x <? k) && all_lt k tl
  end.

Fixpoint wf_fm (S : signature) (k : nat) (p : fm) : bool :=
  match p with
  | EqF i j => (i <? k) && (j <? k)
  | AtF R xs =>
      match lookup_arity R S with
      | Some a => Nat.eqb (length xs) a && all_lt k xs
      | None => false
      end
  | NegF q => wf_fm S k q
  | AndF q r => wf_fm S k q && wf_fm S k r
  | ExF q => wf_fm S (Datatypes.S k) q
  end.

Definition OrF p q := NegF (AndF (NegF p) (NegF q)).
Definition ImpF p q := NegF (AndF p (NegF q)).
Definition AllF p := NegF (ExF (NegF p)).

Definition lift_ren (f : nat -> nat) (x : nat) : nat :=
  match x with 0 => 0 | S i => S (f i) end.

Fixpoint ren (f : nat -> nat) (p : fm) : fm :=
  match p with
  | EqF i j => EqF (f i) (f j)
  | AtF R xs => AtF R (map f xs)
  | NegF q => NegF (ren f q)
  | AndF q r => AndF (ren f q) (ren f r)
  | ExF q => ExF (ren (lift_ren f) q)
  end.

Lemma map_ext_pointwise :
  forall (f g : nat -> nat) xs,
    (forall x, f x = g x) -> map f xs = map g xs.
Proof.
  intros f g xs H. induction xs as [|x xs IH].
  - reflexivity.
  - cbn. rewrite H, IH. reflexivity.
Qed.

Lemma ren_ext :
  forall p f g, (forall x, f x = g x) -> ren f p = ren g p.
Proof.
  induction p as [i j|R xs|p IH|p IHp q IHq|p IH];
    intros f g H; cbn.
  - rewrite H, H. reflexivity.
  - f_equal. apply map_ext_pointwise. exact H.
  - f_equal. apply IH. exact H.
  - f_equal; [apply IHp | apply IHq]; exact H.
  - f_equal. apply IH. intros [|x]; cbn; [reflexivity | rewrite H; reflexivity].
Qed.

Theorem ren_id : forall p, ren (fun x => x) p = p.
Proof.
  induction p as [i j|R xs|p IH|p IHp q IHq|p IH]; cbn.
  - reflexivity.
  - f_equal. induction xs as [|x xs IHxs]; cbn; [reflexivity | rewrite IHxs; reflexivity].
  - rewrite IH. reflexivity.
  - rewrite IHp, IHq. reflexivity.
  - f_equal. transitivity (ren (fun x => x) p).
    + apply ren_ext. intros [|x]; reflexivity.
    + exact IH.
Qed.

Theorem ren_comp :
  forall p f g,
    ren g (ren f p) = ren (fun x => g (f x)) p.
Proof.
  induction p as [i j|R xs|p IH|p IHp q IHq|p IH];
    intros f g; cbn.
  - reflexivity.
  - f_equal. rewrite map_map. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IHp, IHq. reflexivity.
  - f_equal. rewrite IH. apply ren_ext. intros [|x]; reflexivity.
Qed.

Fixpoint fv_raw (p : fm) : list nat :=
  match p with
  | EqF i j => [i;j]
  | AtF _ xs => xs
  | NegF q => fv_raw q
  | AndF q r => fv_raw q ++ fv_raw r
  | ExF q =>
      map Nat.pred
        (filter (fun x => negb (Nat.eqb x 0)) (fv_raw q))
  end.

Definition FV (p : fm) : list nat := nodup Nat.eq_dec (fv_raw p).

(** 4. Finite pointed relational states and satisfaction. *)

Definition tuple := list nat.
Definition reltable := list (relsym * list tuple).

Record state : Type := mkState {
  st_size : nat;
  st_rels : reltable;
  st_pts : list nat
}.

Fixpoint tuple_eqb (xs ys : tuple) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => Nat.eqb x y && tuple_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint tuple_mem (x : tuple) (xs : list tuple) : bool :=
  match xs with
  | [] => false
  | y::ys => tuple_eqb x y || tuple_mem x ys
  end.

Fixpoint lookup_relation (R : relsym) (M : reltable) : list tuple :=
  match M with
  | [] => []
  | (Q,ts)::tl => if Nat.eqb R Q then ts else lookup_relation R tl
  end.

Definition eval_args (s : state) (xs : list nat) : tuple :=
  map (fun i => nth i (st_pts s) 0) xs.

Definition rel_holds (s : state) (R : relsym) (xs : list nat) : bool :=
  tuple_mem (eval_args s xs) (lookup_relation R (st_rels s)).

Fixpoint sat (s : state) (p : fm) : bool :=
  match p with
  | EqF i j => Nat.eqb (nth i (st_pts s) 0) (nth j (st_pts s) 0)
  | AtF R xs => rel_holds s R xs
  | NegF q => negb (sat s q)
  | AndF q r => sat s q && sat s r
  | ExF q =>
      existsb
        (fun b => sat (mkState (st_size s) (st_rels s) (b :: st_pts s)) q)
        (seq 0 (st_size s))
  end.

Fixpoint wf_reltable (S : signature) (n : nat) (M : reltable) : bool :=
  match S with
  | [] => Nat.eqb (length M) 0
  | (R,a)::S' =>
      match M with
      | [] => false
      | (Q,ts)::M' =>
          Nat.eqb R Q &&
          forallb (fun xs => Nat.eqb (length xs) a && all_lt n xs) ts &&
          wf_reltable S' n M'
      end
  end.

Definition wf_state (S : signature) (k : nat) (s : state) : bool :=
  negb (Nat.eqb (st_size s) 0) &&
  Nat.eqb (length (st_pts s)) k &&
  all_lt (st_size s) (st_pts s) &&
  wf_reltable S (st_size s) (st_rels s).

Fixpoint code_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x::tl => S (Cantor.to_nat (x, code_list tl))
  end.

Fixpoint code_tuples (xs : list tuple) : nat :=
  match xs with
  | [] => 0
  | x::tl => S (Cantor.to_nat (code_list x, code_tuples tl))
  end.

Fixpoint code_rels (M : reltable) : nat :=
  match M with
  | [] => 0
  | (R,ts)::tl =>
      S (Cantor.to_nat
        (Cantor.to_nat (R, code_tuples ts), code_rels tl))
  end.

Definition state_code (s : state) : nat :=
  Cantor.to_nat
    (st_size s,
     Cantor.to_nat (code_rels (st_rels s), code_list (st_pts s))).
Definition apply_map (h : list nat) (x : nat) : nat := nth x h 0.

Definition finite_bijection (n m : nat) (h : list nat) : Prop :=
  length h = n /\ NoDup h /\
  (forall x, In x h -> x < m) /\
  forall y, y < m -> In y h.

Definition state_iso (S : signature) (k : nat) (s t : state) : Prop :=
  exists h : list nat,
    finite_bijection (st_size s) (st_size t) h /\
    map (apply_map h) (st_pts s) = st_pts t /\
    (forall R xs,
       lookup_arity R S <> None ->
       (tuple_mem xs (lookup_relation R (st_rels s)) = true <->
        tuple_mem (map (apply_map h) xs)
          (lookup_relation R (st_rels t)) = true)).

Definition canonical_state (S : signature) (k : nat) (s : state) : Prop :=
  wf_state S k s = true /\
  forall t, state_iso S k s t -> state_code s <= state_code t.

Definition CanState (S : signature) (k : nat) (s t : state) : Prop :=
  state_iso S k s t /\ canonical_state S k t.

Definition boundary_reduct (D : signature) (s : state) : state :=
  mkState (st_size s)
    (filter
      (fun e =>
        existsb (fun d => Nat.eqb (fst e) (fst d)) D)
      (st_rels s))
    (st_pts s).

Definition state_embed (D : signature) (s t : state) : Prop :=
  exists h : list nat,
    length h = st_size s /\
    NoDup h /\
    (forall x, In x h -> x < st_size t) /\
    map (apply_map h) (st_pts s) = st_pts t /\
    (forall R xs,
      lookup_arity R D <> None ->
      (tuple_mem xs (lookup_relation R (st_rels s)) = true <->
       tuple_mem (map (apply_map h) xs)
         (lookup_relation R (st_rels t)) = true)).

(** 5. Atomic edits and finite scripts. *)

Inductive atom_edit : Type :=
| Stay
| AddRel : relsym -> tuple -> atom_edit
| DelRel : relsym -> tuple -> atom_edit
| SetPt : nat -> nat -> atom_edit
| AddPoint
| DelLast.

Fixpoint replace_nth {A} (i : nat) (x : A) (xs : list A) : list A :=
  match i, xs with
  | 0, _::tl => x::tl
  | S j, y::tl => y :: replace_nth j x tl
  | _, [] => []
  end.

Fixpoint update_relation
  (R : relsym) (f : list tuple -> list tuple) (M : reltable) : reltable :=
  match M with
  | [] => []
  | (Q,ts)::tl =>
      if Nat.eqb R Q then (Q,f ts)::tl
      else (Q,ts)::update_relation R f tl
  end.

Definition tuple_mentions (x : nat) (ts : list tuple) : bool :=
  existsb (fun ys => existsb (Nat.eqb x) ys) ts.

Definition point_unused (s : state) (x : nat) : bool :=
  negb (existsb (Nat.eqb x) (st_pts s)) &&
  negb (existsb (fun e => tuple_mentions x (snd e)) (st_rels s)).

Definition step (s : state) (e : atom_edit) : option state :=
  match e with
  | Stay => Some s
  | AddRel R xs =>
      if tuple_mem xs (lookup_relation R (st_rels s)) then None
      else Some (mkState (st_size s)
             (update_relation R (fun ts => xs::ts) (st_rels s))
             (st_pts s))
  | DelRel R xs =>
      if tuple_mem xs (lookup_relation R (st_rels s))
      then Some (mkState (st_size s)
              (update_relation R (filter (fun ys => negb (tuple_eqb xs ys)))
                (st_rels s)) (st_pts s))
      else None
  | SetPt i b =>
      if (i <? length (st_pts s)) && (b <? st_size s)
      then Some (mkState (st_size s) (st_rels s)
              (replace_nth i b (st_pts s)))
      else None
  | AddPoint =>
      Some (mkState (S (st_size s)) (st_rels s) (st_pts s))
  | DelLast =>
      match st_size s with
      | 0 | 1 => None
      | S n =>
          if point_unused s n
          then Some (mkState n (st_rels s) (st_pts s))
          else None
      end
  end.

Fixpoint run (s : state) (w : list atom_edit) : option state :=
  match w with
  | [] => Some s
  | e::tl =>
      match step s e with
      | None => None
      | Some t => run t tl
      end
  end.

Definition Edit (s : state) (w : list atom_edit) (t : state) : Prop :=
  run s w = Some t.

Theorem run_empty : forall s, run s [] = Some s.
Proof. reflexivity. Qed.


(** 6--12. Objects, verified presentations, semantic channels and gates. *)

Fixpoint tuples_eqb (xs ys : list tuple) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => tuple_eqb x y && tuples_eqb xs' ys'
  | _, _ => false
  end.

Fixpoint reltable_eqb (M N : reltable) : bool :=
  match M, N with
  | [], [] => true
  | (R,ts)::M', (Q,us)::N' =>
      Nat.eqb R Q && tuples_eqb ts us && reltable_eqb M' N'
  | _, _ => false
  end.

Definition state_eqb (s t : state) : bool :=
  Nat.eqb (st_size s) (st_size t) &&
  reltable_eqb (st_rels s) (st_rels t) &&
  tuple_eqb (st_pts s) (st_pts t).

Lemma tuple_eqb_true_iff :
  forall xs ys, tuple_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys]; simpl.
  - tauto.
  - split; [discriminate | intros H; discriminate].
  - split; [discriminate | intros H; discriminate].
  - rewrite Bool.andb_true_iff, Nat.eqb_eq, IH.
    split.
    + intros [Hxy Htl]. subst. reflexivity.
    + intros H. inversion H. auto.
Qed.

Lemma tuples_eqb_true_iff :
  forall xs ys, tuples_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys]; simpl.
  - tauto.
  - split; [discriminate | intros H; discriminate].
  - split; [discriminate | intros H; discriminate].
  - rewrite Bool.andb_true_iff, tuple_eqb_true_iff, IH.
    split.
    + intros [Hxy Htl]. subst. reflexivity.
    + intros H. inversion H. auto.
Qed.

Lemma reltable_eqb_true_iff :
  forall M N, reltable_eqb M N = true <-> M = N.
Proof.
  induction M as [|[R ts] M IH]; intros [|[Q us] N]; simpl.
  - tauto.
  - split; [discriminate | intros H; discriminate].
  - split; [discriminate | intros H; discriminate].
  - rewrite !Bool.andb_true_iff, Nat.eqb_eq,
      tuples_eqb_true_iff, IH.
    split.
    + intros [[HR Hts] HM]. subst. reflexivity.
    + intros H. inversion H. subst. repeat split; reflexivity.
Qed.

Lemma state_eqb_true_iff :
  forall s t, state_eqb s t = true <-> s = t.
Proof.
  intros [n M ps] [m N qs].
  unfold state_eqb. simpl.
  rewrite !Bool.andb_true_iff, Nat.eqb_eq,
    reltable_eqb_true_iff, tuple_eqb_true_iff.
  split.
  - intros [[Hn HM] Hps]. subst. reflexivity.
  - intros H. inversion H. subst. repeat split; reflexivity.
Qed.
Definition state_in (s : state) (D : list state) : bool :=
  existsb (state_eqb s) D.

Record obj : Type := mkObj {
  o_sig : signature;
  o_boundary : signature;
  o_k : nat;
  o_states : list state;
  o_goal : fm
}.

Definition Obj (X : obj) : Prop :=
  subsig (o_boundary X) (o_sig X) = true /\
  o_states X <> [] /\
  (forall s, In s (o_states X) ->
     wf_state (o_sig X) (o_k X) s = true /\
     canonical_state (o_sig X) (o_k X) s) /\
  wf_fm (o_sig X) (o_k X) (o_goal X) = true.

Definition satisfies_obj (s : state) (X : obj) : bool :=
  state_in s (o_states X) && sat s (o_goal X).

Record edge_certificate : Type := mkEdgeCert {
  ec_u : nat;
  ec_v : nat;
  ec_left : list atom_edit;
  ec_right : list atom_edit
}.

Record presentation : Type := mkPres {
  pr_m : nat;
  pr_edges : list (nat * nat);
  pr_lambda : list state;
  pr_rho : list state;
  pr_kappa : list edge_certificate
}.

Definition edge_eqb (e f : nat * nat) : bool :=
  Nat.eqb (fst e) (fst f) && Nat.eqb (snd e) (snd f).

Definition edge_in (u v : nat) (es : list (nat * nat)) : bool :=
  existsb (edge_eqb (u,v)) es.

Definition endpoints_in (xs D : list state) : bool :=
  forallb (fun s => state_in s D) xs.

Definition surjective_list (xs D : list state) : bool :=
  forallb (fun s => state_in s xs) D.

Definition irreflexive_check (m : nat) (es : list (nat * nat)) : bool :=
  forallb (fun u => negb (edge_in u u es)) (seq 0 m).

Definition bounded_edges (m : nat) (es : list (nat * nat)) : bool :=
  forallb (fun e => (fst e <? m) && (snd e <? m)) es.

Definition transitive_check (m : nat) (es : list (nat * nat)) : bool :=
  forallb
    (fun u =>
      forallb
        (fun v =>
          forallb
            (fun w =>
              negb (edge_in u v es && edge_in v w es) ||
              edge_in u w es)
            (seq 0 m))
        (seq 0 m))
    (seq 0 m).

Fixpoint find_certificate
  (u v : nat) (ks : list edge_certificate)
  : option (list atom_edit * list atom_edit) :=
  match ks with
  | [] => None
  | c::tl =>
      if Nat.eqb u (ec_u c) && Nat.eqb v (ec_v c)
      then Some (ec_left c, ec_right c)
      else find_certificate u v tl
  end.

Definition empty_state := mkState 1 [] [].

Definition certifies_edge
  (p : presentation) (u v : nat) : bool :=
  match find_certificate u v (pr_kappa p) with
  | None => false
  | Some (wx,wy) =>
      match run (nth u (pr_lambda p) empty_state) wx,
            run (nth u (pr_rho p) empty_state) wy with
      | Some x', Some y' =>
          state_eqb x' (nth v (pr_lambda p) empty_state) &&
          state_eqb y' (nth v (pr_rho p) empty_state)
      | _, _ => false
      end
  end.

Definition VerifyPres (X Y : obj) (p : presentation) : bool :=
  negb (Nat.eqb (pr_m p) 0) &&
  Nat.eqb (length (pr_lambda p)) (pr_m p) &&
  Nat.eqb (length (pr_rho p)) (pr_m p) &&
  bounded_edges (pr_m p) (pr_edges p) &&
  irreflexive_check (pr_m p) (pr_edges p) &&
  transitive_check (pr_m p) (pr_edges p) &&
  endpoints_in (pr_lambda p) (o_states X) &&
  endpoints_in (pr_rho p) (o_states Y) &&
  surjective_list (pr_lambda p) (o_states X) &&
  surjective_list (pr_rho p) (o_states Y) &&
  forallb
    (fun e => certifies_edge p (fst e) (snd e))
    (pr_edges p).

Record channel : Type := mkChannel {
  ch_m : nat;
  ch_edges : list (nat * nat);
  ch_lambda : list state;
  ch_rho : list state
}.

Definition forget_scripts (p : presentation) : channel :=
  mkChannel (pr_m p) (pr_edges p) (pr_lambda p) (pr_rho p).

Definition legal_channel (X Y : obj) (c : channel) : Prop :=
  exists p, VerifyPres X Y p = true /\ forget_scripts p = c.

Fixpoint code_edges (es : list (nat * nat)) : nat :=
  match es with
  | [] => 0
  | (u,v)::tl =>
      S (Cantor.to_nat (Cantor.to_nat (u,v), code_edges tl))
  end.

Fixpoint code_states (ss : list state) : nat :=
  match ss with
  | [] => 0
  | s::tl => S (Cantor.to_nat (state_code s, code_states tl))
  end.

Definition channel_code (c : channel) : nat :=
  Cantor.to_nat
    (ch_m c,
     Cantor.to_nat
       (code_edges (ch_edges c),
        Cantor.to_nat
          (code_states (ch_lambda c), code_states (ch_rho c)))).
Definition channel_iso (p q : channel) : Prop :=
  exists h : list nat,
    finite_bijection (ch_m p) (ch_m q) h /\
    map (fun u => nth (apply_map h u) (ch_lambda q) empty_state)
      (seq 0 (ch_m p)) = ch_lambda p /\
    map (fun u => nth (apply_map h u) (ch_rho q) empty_state)
      (seq 0 (ch_m p)) = ch_rho p /\
    (forall u v, u < ch_m p -> v < ch_m p ->
      (edge_in u v (ch_edges p) = true <->
       edge_in (apply_map h u) (apply_map h v) (ch_edges q) = true)).

Definition canonical_channel (X Y : obj) (c : channel) : Prop :=
  legal_channel X Y c /\
  forall d, channel_iso c d -> channel_code c <= channel_code d.

Definition Ch (X Y : obj) := { c : channel | canonical_channel X Y c }.

Definition le_edge (c : channel) (u v : nat) : bool :=
  Nat.eqb u v || edge_in u v (ch_edges c).

Definition badb (X Y : obj) (c : channel) (u : nat) : bool :=
  satisfies_obj (nth u (ch_lambda c) empty_state) X &&
  negb (satisfies_obj (nth u (ch_rho c) empty_state) Y).

Definition Bad (X Y : obj) (c : channel) : list nat :=
  filter (fun u => badb X Y c u) (seq 0 (ch_m c)).

Definition minimal_badb (X Y : obj) (c : channel) (u : nat) : bool :=
  badb X Y c u &&
  negb
    (existsb
      (fun v => badb X Y c v && edge_in v u (ch_edges c))
      (seq 0 (ch_m c))).

Definition Cbase (X Y : obj) (c : channel) : list nat :=
  filter (minimal_badb X Y c) (seq 0 (ch_m c)).

Record exclusion_index : Type := mkIndex {
  ix_base : list nat;
  ix_lambda : list state;
  ix_rho : list state
}.

Definition exclusion (X Y : obj) (c : channel) : exclusion_index :=
  let C := Cbase X Y c in
  mkIndex C
    (map (fun u => nth u (ch_lambda c) empty_state) C)
    (map (fun u => nth u (ch_rho c) empty_state) C).

Definition negative_spectrum (X Y : obj) (p : channel) : list state :=
  map
    (fun c =>
      boundary_reduct (o_boundary Y)
        (nth c (ch_rho p) empty_state))
    (Cbase X Y p).

Definition positive_spectrum (Y Z : obj) (q : channel) : list state :=
  map
    (fun d =>
      boundary_reduct (o_boundary Y)
        (nth d (ch_lambda q) empty_state))
    (Cbase Y Z q).

Definition conflict_set
  (X Y Z : obj) (p q : channel) : list state :=
  filter
    (fun s => state_in s (positive_spectrum Y Z q))
    (negative_spectrum X Y p).

Definition bowtie (X Y Z : obj) (p q : channel) : bool :=
  Nat.eqb (length (conflict_set X Y Z p q)) 0.

Definition Kminimal
  (X Y Z : obj) (p q : channel) (d : state) : Prop :=
  In d (conflict_set X Y Z p q) /\
  ~ exists e,
      In e (conflict_set X Y Z p q) /\
      state_eqb e d = false /\
      state_embed (o_boundary Y) e d.

Record mismatch_entry : Type := mkMisEntry {
  me_boundary : state;
  me_left_scenario : nat;
  me_right_scenario : nat;
  me_minus_aligned : state;
  me_plus_aligned : state
}.

Record mismatch : Type := mkMismatch {
  mis_entries : list mismatch_entry
}.

Definition least_witness
  (pred : nat -> bool) (n u : nat) : Prop :=
  u < n /\ pred u = true /\
  forall v, v < u -> pred v = false.

Definition Mis
  (X Y Z : obj) (p q : channel) (m : mismatch) : Prop :=
  conflict_set X Y Z p q <> [] /\
  (forall d,
    Kminimal X Y Z p q d <->
    exists e,
      In e (mis_entries m) /\
      state_eqb (me_boundary e) d = true /\
      least_witness
        (fun c =>
          minimal_badb X Y p c &&
          state_eqb
            (boundary_reduct (o_boundary Y)
              (nth c (ch_rho p) empty_state)) d)
        (ch_m p) (me_left_scenario e) /\
      least_witness
        (fun c =>
          minimal_badb Y Z q c &&
          state_eqb
            (boundary_reduct (o_boundary Y)
              (nth c (ch_lambda q) empty_state)) d)
        (ch_m q) (me_right_scenario e)) /\
  (forall e,
    In e (mis_entries m) ->
    state_eqb (me_minus_aligned e)
      (nth (me_left_scenario e) (ch_rho p) empty_state) = true /\
    state_eqb (me_plus_aligned e)
      (nth (me_right_scenario e) (ch_lambda q) empty_state) = true /\
    state_eqb
      (boundary_reduct (o_boundary Y) (me_minus_aligned e))
      (me_boundary e) = true /\
    state_eqb
      (boundary_reduct (o_boundary Y) (me_plus_aligned e))
      (me_boundary e) = true).
Definition all_pairs (m n : nat) : list (nat * nat) :=
  flat_map (fun u => map (fun v => (u,v)) (seq 0 n)) (seq 0 m).

Definition fiber (p q : channel) : list (nat * nat) :=
  filter
    (fun uv =>
      state_eqb
        (nth (fst uv) (ch_rho p) empty_state)
        (nth (snd uv) (ch_lambda q) empty_state))
    (all_pairs (ch_m p) (ch_m q)).

Definition pair_le (c : channel) (x y : nat) : bool := le_edge c x y.

Definition composite_edge (p q : channel)
  (a b : nat * nat) : bool :=
  pair_le p (fst a) (fst b) &&
  pair_le q (snd a) (snd b) &&
  (edge_in (fst a) (fst b) (ch_edges p) ||
   edge_in (snd a) (snd b) (ch_edges q)).

Definition composite_raw (p q : channel) : channel :=
  let F := fiber p q in
  let r := length F in
  mkChannel r
    (filter
      (fun ij =>
        composite_edge p q
          (nth (fst ij) F (0,0))
          (nth (snd ij) F (0,0)))
      (all_pairs r r))
    (map
      (fun uv => nth (fst uv) (ch_lambda p) empty_state) F)
    (map
      (fun uv => nth (snd uv) (ch_rho q) empty_state) F).

Definition Compose
  (X Y Z : obj) (p q r : channel) : Prop :=
  bowtie X Y Z p q = true /\
  channel_iso (composite_raw p q) r /\
  canonical_channel X Z r.

Definition identity_channel (X : obj) : channel :=
  mkChannel (length (o_states X)) [] (o_states X) (o_states X).

Definition ordinary_relation (c : channel) : list (state * state) :=
  map
    (fun u =>
      (nth u (ch_lambda c) empty_state,
       nth u (ch_rho c) empty_state))
    (seq 0 (ch_m c)).

(** 11 and 16. Proof terms, object judgments and meta-judgments. *)

Inductive proof_term : Type :=
| IdT : obj -> proof_term
| GenT : nat -> proof_term
| SeqT : proof_term -> proof_term -> proof_term.

Record generator : Type := mkGenerator {
  gen_source : obj;
  gen_target : obj;
  gen_presentation : presentation
}.

Definition generator_table := list generator.

Inductive Derives (G : generator_table)
  : proof_term -> obj -> channel -> obj -> Prop :=
| D_Id : forall X c,
    channel_iso (identity_channel X) c ->
    canonical_channel X X c ->
    Derives G (IdT X) X c X
| D_Gen : forall g n c,
    nth_error G n = Some g ->
    VerifyPres (gen_source g) (gen_target g) (gen_presentation g) = true ->
    channel_iso (forget_scripts (gen_presentation g)) c ->
    canonical_channel (gen_source g) (gen_target g) c ->
    Derives G (GenT n) (gen_source g) c (gen_target g)
| D_Seq : forall d e X Y Z p q r,
    Derives G d X p Y ->
    Derives G e Y q Z ->
    Compose X Y Z p q r ->
    Derives G (SeqT d e) X r Z.

Definition MisJud (G : generator_table)
  (d e : proof_term) (X Y Z : obj)
  (p q : channel) (m : mismatch) : Prop :=
  Derives G d X p Y /\
  Derives G e Y q Z /\
  Mis X Y Z p q m.

(** 13--16. Hiding, retargeting, stable restatement and residuals. *)

Definition symbols_of (S : signature) : list relsym := map fst S.

Definition diff_symbols (S : signature) (s t : state) : list relsym :=
  filter
    (fun R =>
      negb
        (tuples_eqb
          (lookup_relation R (st_rels s))
          (lookup_relation R (st_rels t))))
    (symbols_of S).

Definition hidden_symbols (Y : obj) (m : mismatch) : list relsym :=
  nodup Nat.eq_dec
    (flat_map
      (fun e =>
        diff_symbols (o_sig Y)
          (me_minus_aligned e) (me_plus_aligned e))
      (mis_entries m)).

Definition masked_signature (Y : obj) (m : mismatch) : signature :=
  filter
    (fun d => negb (existsb (Nat.eqb (fst d)) (hidden_symbols Y m)))
    (o_sig Y).

Definition red_state (Y : obj) (m : mismatch) (s : state) : state :=
  boundary_reduct (masked_signature Y m) s.

Fixpoint vectors (r n : nat) : list (list nat) :=
  match r with
  | 0 => [[]]
  | S r' =>
      flat_map
        (fun b => map (cons b) (vectors r' n))
        (seq 0 n)
  end.

Definition retarget_catalog (Y : obj) (r : nat) : list state :=
  flat_map
    (fun s =>
      map
        (fun bs => mkState (st_size s) (st_rels s) bs)
        (vectors r (st_size s)))
    (o_states Y).

Definition same_red (Y : obj) (m : mismatch) (s t : state) : bool :=
  state_eqb (red_state Y m s) (red_state Y m t).

Definition Stableb
  (Y : obj) (m : mismatch) (r : nat) (psi : fm) : bool :=
  forallb
    (fun s =>
      forallb
        (fun t =>
          negb (same_red Y m s t) ||
          Bool.eqb (sat s psi) (sat t psi))
        (retarget_catalog Y r))
    (retarget_catalog Y r).

Definition Stable
  (Y : obj) (m : mismatch) (r : nat) (psi : fm) : Prop :=
  wf_fm (o_sig Y) r psi = true /\
  Stableb Y m r psi = true.

Definition counterexample_pair
  (Y : obj) (m : mismatch) (psi : fm)
  (st : state * state) : bool :=
  same_red Y m (fst st) (snd st) &&
  negb (Bool.eqb (sat (fst st) psi) (sat (snd st) psi)).

Definition state_pairs (D : list state) : list (state * state) :=
  flat_map (fun s => map (fun t => (s,t)) D) D.

Definition NoRest
  (Y : obj) (m : mismatch) (r : nat) (psi : fm)
  (st : state * state) : Prop :=
  In st (state_pairs (retarget_catalog Y r)) /\
  counterexample_pair Y m psi st = true /\
  forall uv,
    In uv (state_pairs (retarget_catalog Y r)) ->
    counterexample_pair Y m psi uv = true ->
    state_code (fst st) + state_code (snd st) <=
    state_code (fst uv) + state_code (snd uv).

Fixpoint fm_code (p : fm) : nat :=
  match p with
  | EqF i j =>
      Cantor.to_nat (0, Cantor.to_nat (i,j))
  | AtF R xs =>
      Cantor.to_nat (1, Cantor.to_nat (R, code_list xs))
  | NegF q =>
      Cantor.to_nat (2, fm_code q)
  | AndF q r =>
      Cantor.to_nat (3, Cantor.to_nat (fm_code q, fm_code r))
  | ExF q =>
      Cantor.to_nat (4, fm_code q)
  end.
Local Opaque Cantor.to_nat.

Lemma code_list_injective :
  forall xs ys, code_list xs = code_list ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; unfold code_list in H.
  - reflexivity.
  - discriminate.
  - discriminate.
  - apply Nat.succ_inj in H.
    apply Cantor.to_nat_inj in H.
    injection H as Hx Htl.
    subst y. f_equal. apply IH. exact Htl.
Qed.

Theorem fm_code_injective :
  forall p q, fm_code p = fm_code q -> p = q.
Proof.
  induction p as
    [i j | R xs | p IHp | p IHp q IHq | p IHp];
    intros z H;
    destruct z as [i' j' | R' ys | z | z1 z2 | z];
    cbn in H;
    apply Cantor.to_nat_inj in H;
    try discriminate.
  - injection H as Hinner.
    apply Cantor.to_nat_inj in Hinner.
    injection Hinner as Hi Hj. subst. reflexivity.
  - injection H as Hinner.
    apply Cantor.to_nat_inj in Hinner.
    injection Hinner as HR Hxs.
    subst R'. apply code_list_injective in Hxs. subst ys. reflexivity.
  - injection H as Hcode.
    f_equal. apply IHp. exact Hcode.
  - injection H as Hinner.
    apply Cantor.to_nat_inj in Hinner.
    injection Hinner as Hp Hq.
    f_equal.
    + apply IHp. exact Hp.
    + apply IHq. exact Hq.
  - injection H as Hcode.
    f_equal. apply IHp. exact Hcode.
Qed.

Theorem fm_code_identity :
  forall p q, p = q <-> fm_code p = fm_code q.
Proof.
  intros p q. split.
  - intros H. subst q. reflexivity.
  - apply fm_code_injective.
Qed.
Local Transparent Cantor.to_nat.

Definition restates
  (Y : obj) (m : mismatch) (r : nat)
  (psi theta : fm) : Prop :=
  wf_fm (masked_signature Y m) r theta = true /\
  forall s,
    In s (retarget_catalog Y r) ->
    sat s psi = sat (red_state Y m s) theta.

Definition Rest
  (Y : obj) (m : mismatch) (r : nat)
  (psi theta : fm) : Prop :=
  restates Y m r psi theta /\
  forall eta, restates Y m r psi eta -> fm_code theta <= fm_code eta.

Definition template := list (relsym * fm).

Fixpoint lookup_template (R : relsym) (tau : template) : option fm :=
  match tau with
  | [] => None
  | (Q,p)::tl => if Nat.eqb R Q then Some p else lookup_template R tl
  end.

Definition Tpl (S L : signature) (tau : template) : Prop :=
  forall R a,
    lookup_arity R S = Some a ->
    exists p,
      lookup_template R tau = Some p /\
      wf_fm L a p = true.

Fixpoint template_action (tau : template) (p : fm) : option fm :=
  match p with
  | EqF i j => Some (EqF i j)
  | AtF R xs =>
      match lookup_template R tau with
      | None => None
      | Some q => Some (ren (fun i => nth i xs 0) q)
      end
  | NegF q =>
      match template_action tau q with
      | None => None
      | Some q' => Some (NegF q')
      end
  | AndF q r =>
      match template_action tau q, template_action tau r with
      | Some q', Some r' => Some (AndF q' r')
      | _, _ => None
      end
  | ExF q =>
      match template_action tau q with
      | None => None
      | Some q' => Some (ExF q')
      end
  end.

Definition residual_component
  (Y : obj) (m : mismatch) (tau : template)
  (R : relsym) (theta : fm) : Prop :=
  exists a p,
    lookup_arity R (masked_signature Y m) = Some a /\
    lookup_template R tau = Some p /\
    Rest Y m a p theta.

Definition Res
  (Y : obj) (m : mismatch)
  (tau bartau : template) : Prop :=
  Tpl (o_sig Y) (o_sig Y) tau /\
  Tpl (masked_signature Y m) (masked_signature Y m) bartau /\
  forall R a,
    lookup_arity R (masked_signature Y m) = Some a ->
    exists theta,
      lookup_template R bartau = Some theta /\
      residual_component Y m tau R theta.

Definition NoRes
  (Y : obj) (m : mismatch) (tau : template)
  (R : relsym) (st : state * state) : Prop :=
  exists a p,
    lookup_arity R (masked_signature Y m) = Some a /\
    lookup_template R tau = Some p /\
    NoRest Y m a p st /\
    forall Q,
      Q < R ->
      lookup_arity Q (masked_signature Y m) <> None ->
      exists theta, residual_component Y m tau Q theta.

Definition HideJud (G : generator_table)
  (d e : proof_term) (X Y Z : obj)
  (p q : channel) (m : mismatch)
  (H : list relsym) (S' : signature) : Prop :=
  MisJud G d e X Y Z p q m /\
  H = hidden_symbols Y m /\
  S' = masked_signature Y m.

Definition RestJud (G : generator_table)
  (d e : proof_term) (X Y Z : obj)
  (p q : channel) (m : mismatch)
  (r : nat) (psi theta : fm) : Prop :=
  HideJud G d e X Y Z p q m
    (hidden_symbols Y m) (masked_signature Y m) /\
  Rest Y m r psi theta.

Definition ResidualJud (G : generator_table)
  (d e : proof_term) (X Y Z : obj)
  (p q : channel) (m : mismatch)
  (tau bartau : template) : Prop :=
  HideJud G d e X Y Z p q m
    (hidden_symbols Y m) (masked_signature Y m) /\
  Res Y m tau bartau.

Inductive meta_judgment (G : generator_table) : Type :=
| MJ_Mis : proof_term -> proof_term -> obj -> obj -> obj ->
    channel -> channel -> mismatch -> meta_judgment G
| MJ_Hide : proof_term -> proof_term -> obj -> obj -> obj ->
    channel -> channel -> mismatch -> list relsym -> signature ->
    meta_judgment G
| MJ_Rest : proof_term -> proof_term -> obj -> obj -> obj ->
    channel -> channel -> mismatch -> nat -> fm -> fm ->
    meta_judgment G
| MJ_Residual : proof_term -> proof_term -> obj -> obj -> obj ->
    channel -> channel -> mismatch -> template -> template ->
    meta_judgment G.

(** A quotient-independent semantic channel algebra for 17.3 and 17.5. *)

Record sem_channel (A B : Type) : Type := mkSemChannel {
  sc_scene : Type;
  sc_valid : sc_scene -> Prop;
  sc_source : sc_scene -> A;
  sc_target : sc_scene -> B;
  sc_strict : sc_scene -> sc_scene -> Prop
}.

Arguments sc_scene {_ _} _.
Arguments sc_valid {_ _} _ _.
Arguments sc_source {_ _} _ _.
Arguments sc_target {_ _} _ _.
Arguments sc_strict {_ _} _ _ _.

Definition sc_le {A B} (p : sem_channel A B)
  (u v : sc_scene p) : Prop :=
  u = v \/ sc_strict p u v.

Definition sem_identity (A : Type) : sem_channel A A :=
  @mkSemChannel A A A (fun _ => True) (fun x => x) (fun x => x)
    (fun _ _ => False).

Definition sem_comp {A B C}
  (p : sem_channel A B) (q : sem_channel B C)
  : sem_channel A C :=
  @mkSemChannel A C (sc_scene p * sc_scene q)%type
    (fun uv =>
      sc_valid p (fst uv) /\
      sc_valid q (snd uv) /\
      sc_target p (fst uv) = sc_source q (snd uv))
    (fun uv => sc_source p (fst uv))
    (fun uv => sc_target q (snd uv))
    (fun uv xy =>
      sc_le p (fst uv) (fst xy) /\
      sc_le q (snd uv) (snd xy) /\
      (sc_strict p (fst uv) (fst xy) \/
       sc_strict q (snd uv) (snd xy))).

Record sem_equiv {A B}
  (p q : sem_channel A B) : Type := mkSemEquiv {
  se_f : sc_scene p -> sc_scene q;
  se_g : sc_scene q -> sc_scene p;
  se_valid_f : forall x, sc_valid p x -> sc_valid q (se_f x);
  se_valid_g : forall y, sc_valid q y -> sc_valid p (se_g y);
  se_gf : forall x, sc_valid p x -> se_g (se_f x) = x;
  se_fg : forall y, sc_valid q y -> se_f (se_g y) = y;
  se_source : forall x, sc_valid p x ->
    sc_source q (se_f x) = sc_source p x;
  se_target : forall x, sc_valid p x ->
    sc_target q (se_f x) = sc_target p x;
  se_order : forall x y, sc_valid p x -> sc_valid p y ->
    (sc_strict p x y <-> sc_strict q (se_f x) (se_f y))
}.

Definition source_constant {A B} (p : sem_channel A B) : Prop :=
  forall u v,
    sc_valid p u -> sc_valid p v -> sc_strict p u v ->
    sc_source p u = sc_source p v.

Definition target_constant {A B} (p : sem_channel A B) : Prop :=
  forall u v,
    sc_valid p u -> sc_valid p v -> sc_strict p u v ->
    sc_target p u = sc_target p v.

Theorem sem_left_identity_corrected :
  forall A B (p : sem_channel A B),
    source_constant p ->
    sem_equiv (sem_comp (sem_identity A) p) p.
Proof.
  intros A B p Hsource.
  refine (mkSemEquiv (sem_comp (sem_identity A) p) p
    (fun au => snd au) (fun u => (sc_source p u,u)) _ _ _ _ _ _ _).
  - intros [a u] [_ [Hu Hmatch]]. exact Hu.
  - intro u. cbn. tauto.
  - intros [a u] [_ [Hu Ha]]. cbn in Ha. subst a. reflexivity.
  - intros u Hu. reflexivity.
  - intros [a u] [_ [Hu Ha]]. cbn in Ha. symmetry. exact Ha.
  - intros [a u] H. reflexivity.
  - intros [a u] [b v] [Ha [Hu Eau]] [Hb [Hv Ebv]].
    cbn in *. split.
    + tauto.
    + intro Huv.
      assert (Hs : sc_source p u = sc_source p v).
      { apply Hsource; assumption. }
      assert (Hab : a = b) by congruence.
      split.
      * left. exact Hab.
      * split.
        -- right. exact Huv.
        -- right. exact Huv.
Qed.

Theorem sem_right_identity_corrected :
  forall A B (p : sem_channel A B),
    target_constant p ->
    sem_equiv (sem_comp p (sem_identity B)) p.
Proof.
  intros A B p Htarget.
  refine (mkSemEquiv (sem_comp p (sem_identity B)) p
    (fun ub => fst ub) (fun u => (u,sc_target p u)) _ _ _ _ _ _ _).
  - intros [u b] [Hu [_ Hmatch]]. exact Hu.
  - intro u. cbn. tauto.
  - intros [u b] [Hu [_ Hub]]. cbn in Hub. subst b. reflexivity.
  - intros u Hu. reflexivity.
  - intros [u b] H. reflexivity.
  - intros [u b] [Hu [_ Hub]]. cbn in Hub. exact Hub.
  - intros [u a] [v b] [Hu [_ Hua]] [Hv [_ Hvb]].
    cbn in *. split.
    + tauto.
    + intro Huv.
      assert (Ht : sc_target p u = sc_target p v).
      { apply Htarget; assumption. }
      assert (Hab : a = b) by congruence.
      split.
      * right. exact Huv.
      * split.
        -- left. exact Hab.
        -- left. exact Huv.
Qed.
Lemma sem_comp_le :
  forall A B C (p : sem_channel A B) (q : sem_channel B C)
    (x y : sc_scene (sem_comp p q)),
    sc_le (sem_comp p q) x y <->
    sc_le p (fst x) (fst y) /\ sc_le q (snd x) (snd y).
Proof.
  intros A B C p q [u v] [u' v'].
  unfold sc_le. cbn.
  split.
  - intros [E | [Hp [Hq Hstrict]]].
    + inversion E. subst. split; left; reflexivity.
    + exact (conj Hp Hq).
  - intros [[Eu | Pu] [Ev | Qv]].
    + left. subst. reflexivity.
    + right. split.
      * left. exact Eu.
      * split.
        -- right. exact Qv.
        -- right. exact Qv.
    + right. split.
      * right. exact Pu.
      * split.
        -- left. exact Ev.
        -- left. exact Pu.
    + right. split.
      * right. exact Pu.
      * split.
        -- right. exact Qv.
        -- left. exact Pu.
Qed.
Theorem sem_associative :
  forall A B C D
    (p : sem_channel A B)
    (q : sem_channel B C)
    (r : sem_channel C D),
    sem_equiv (sem_comp (sem_comp p q) r)
              (sem_comp p (sem_comp q r)).
Proof.
  intros A B C D p q r.
  refine (mkSemEquiv
    (sem_comp (sem_comp p q) r)
    (sem_comp p (sem_comp q r))
    (fun x => (fst (fst x),(snd (fst x),snd x)))
    (fun x => ((fst x,fst (snd x)),snd (snd x)))
    _ _ _ _ _ _ _).
  - intros [[u v] w]. cbn. tauto.
  - intros [u [v w]]. cbn. tauto.
  - intros [[u v] w] H. reflexivity.
  - intros [u [v w]] H. reflexivity.
  - intros [[u v] w] H. reflexivity.
  - intros [[u v] w] H. reflexivity.
  - intros [[u v] w] [[u' v'] w'] H H'.
    change
      (sc_le (sem_comp p q) (u,v) (u',v') /\
       sc_le r w w' /\
       ((sc_le p u u' /\ sc_le q v v' /\
         (sc_strict p u u' \/ sc_strict q v v')) \/
        sc_strict r w w')
       <->
       sc_le p u u' /\
       sc_le (sem_comp q r) (v,w) (v',w') /\
       (sc_strict p u u' \/
        (sc_le q v v' /\ sc_le r w w' /\
         (sc_strict q v v' \/ sc_strict r w w')))).
    rewrite (@sem_comp_le A B C p q (u,v) (u',v')).
    rewrite (@sem_comp_le B C D q r (v,w) (v',w')).
    tauto.
Qed.

Definition sem_U {A B} (p : sem_channel A B) (a : A) (b : B) : Prop :=
  exists u, sc_valid p u /\ sc_source p u = a /\ sc_target p u = b.

Theorem sem_U_identity :
  forall A (a b : A),
    sem_U (sem_identity A) a b <-> a = b.
Proof.
  intros A a b. split.
  - intros [u [_ [Hu Hv]]]. cbn in *. congruence.
  - intro H. subst b. exists a. cbn.
    split.
    + exact I.
    + split; reflexivity.
Qed.

Theorem sem_U_composition :
  forall A B C (p : sem_channel A B) (q : sem_channel B C) a c,
    sem_U (sem_comp p q) a c <->
    exists b, sem_U p a b /\ sem_U q b c.
Proof.
  intros A B C p q a c. split.
  - intros [[u v] [[Hu [Hv Hmatch]] [Hsrc Hdst]]].
    exists (sc_target p u). split.
    + exists u. split.
      * exact Hu.
      * split; [exact Hsrc | reflexivity].
    + exists v. split.
      * exact Hv.
      * split; [symmetry; exact Hmatch | exact Hdst].
  - intros [b [[u [Hu [Hsrc Hmid]]]
               [v [Hv [Hmid' Hdst]]]]].
    exists (u,v). cbn. split.
    + split.
      * exact Hu.
      * split.
        -- exact Hv.
        -- transitivity b; [exact Hmid | symmetry; exact Hmid'].
    + split; [exact Hsrc | exact Hdst].
Qed.
(** 18. The concrete joint finite witness. *)

Definition A_sym := 0.
Definition D_sym := 1.
Definition H_sym := 2.
Definition Z_sym := 3.

Definition sigX : signature := [(A_sym,1)].
Definition sigY : signature := [(D_sym,1);(H_sym,1)].
Definition delY : signature := [(D_sym,1)].
Definition sigZ : signature := [(Z_sym,1)].

Definition x_state : state :=
  mkState 1 [(A_sym,[[0]])] [0].
Definition y0_state : state :=
  mkState 1 [(D_sym,[]);(H_sym,[])] [0].
Definition y1_state : state :=
  mkState 1 [(D_sym,[[0]]);(H_sym,[])] [0].
Definition y2_state : state :=
  mkState 1 [(D_sym,[]);(H_sym,[[0]])] [0].
Definition z_state : state :=
  mkState 1 [(Z_sym,[])] [0].

Definition X_obj : obj :=
  mkObj sigX [] 1 [x_state] (AtF A_sym [0]).
Definition Y_obj : obj :=
  mkObj sigY delY 1 [y0_state;y1_state;y2_state] (AtF H_sym [0]).
Definition Z_obj : obj :=
  mkObj sigZ [] 1 [z_state] (AtF Z_sym [0]).

Definition p_pres : presentation :=
  mkPres 3 [(0,1)]
    [x_state;x_state;x_state]
    [y0_state;y1_state;y2_state]
    [mkEdgeCert 0 1 [Stay] [AddRel D_sym [0]]].

Definition p'_pres : presentation :=
  mkPres 3 [(1,0)]
    [x_state;x_state;x_state]
    [y0_state;y1_state;y2_state]
    [mkEdgeCert 1 0 [Stay] [DelRel D_sym [0]]].

Definition q_pres : presentation :=
  mkPres 3 []
    [y0_state;y1_state;y2_state]
    [z_state;z_state;z_state]
    [].

Definition p_ch := forget_scripts p_pres.
Definition p'_ch := forget_scripts p'_pres.
Definition q_ch := forget_scripts q_pres.

Theorem witness_presentations_verified :
  VerifyPres X_obj Y_obj p_pres = true /\
  VerifyPres X_obj Y_obj p'_pres = true /\
  VerifyPres Y_obj Z_obj q_pres = true.
Proof. vm_compute. tauto. Qed.

Theorem witness_bad_bases :
  Cbase X_obj Y_obj p_ch = [0] /\
  Cbase X_obj Y_obj p'_ch = [1] /\
  Cbase Y_obj Z_obj q_ch = [2].
Proof. vm_compute. tauto. Qed.

Theorem witness_same_ordinary_projection :
  ordinary_relation p_ch = ordinary_relation p'_ch.
Proof. reflexivity. Qed.

Theorem witness_opposite_gates :
  conflict_set X_obj Y_obj Z_obj p_ch q_ch =
    [boundary_reduct delY y0_state] /\
  bowtie X_obj Y_obj Z_obj p_ch q_ch = false /\
  bowtie X_obj Y_obj Z_obj p'_ch q_ch = true.
Proof. vm_compute. tauto. Qed.

Definition witness_mismatch : mismatch :=
  mkMismatch
    [mkMisEntry
      (boundary_reduct delY y0_state)
      0 2 y0_state y2_state].


Theorem witness_alignment_certificate :
  conflict_set X_obj Y_obj Z_obj p_ch q_ch =
    [boundary_reduct delY y0_state] /\
  state_eqb y0_state
    (nth 0 (ch_rho p_ch) empty_state) = true /\
  state_eqb y2_state
    (nth 2 (ch_lambda q_ch) empty_state) = true /\
  state_eqb (boundary_reduct delY y0_state)
    (boundary_reduct delY y2_state) = true.
Proof. vm_compute. tauto. Qed.
Theorem witness_mis :
  Mis X_obj Y_obj Z_obj p_ch q_ch witness_mismatch.
Proof.
  pose proof witness_opposite_gates as [Hconf [Hgate Hgate']].
  unfold Mis.
  split.
  - rewrite Hconf. discriminate.
  - split.
    + intro d. split.
      * intros [Hd Hminimal].
        rewrite Hconf in Hd. simpl in Hd.
        destruct Hd as [Hd | Hd]; [subst d | contradiction].
        exists (mkMisEntry
          (boundary_reduct delY y0_state)
          0 2 y0_state y2_state).
        split.
        -- left. reflexivity.
        -- split.
           ++ vm_compute. reflexivity.
           ++ split.
              ** unfold least_witness. split; [vm_compute; lia |].
                 split.
                 --- vm_compute. reflexivity.
                 --- intros v Hv. vm_compute in Hv. lia.
              ** unfold least_witness. split; [vm_compute; lia |].
                 split.
                 --- vm_compute. reflexivity.
                 --- intros v Hv. destruct v as [|[|v]].
                     +++ vm_compute. reflexivity.
                     +++ vm_compute. reflexivity.
                     +++ vm_compute in Hv. lia.
      * intros [e [He [Heqd [Hl Hr]]]].
        simpl in He.
        destruct He as [He | He]; [subst e | contradiction].
        cbn in Heqd.
        apply state_eqb_true_iff in Heqd. subst d.
        split.
        -- rewrite Hconf. left. reflexivity.
        -- intros [e [He [Hneq Hembed]]].
           rewrite Hconf in He. simpl in He.
           destruct He as [He | He]; [subst e | contradiction].
           vm_compute in Hneq. discriminate.
    + intros e He.
      simpl in He.
      destruct He as [He | He]; [subst e | contradiction].
      vm_compute. repeat split; reflexivity.
Qed.
Theorem witness_hidden_support :
  hidden_symbols Y_obj witness_mismatch = [H_sym] /\
  masked_signature Y_obj witness_mismatch = delY.
Proof. vm_compute. tauto. Qed.

Definition D_formula := AtF D_sym [0].
Definition H_formula := AtF H_sym [0].

Theorem witness_restatement_split :
  Stableb Y_obj witness_mismatch 1 D_formula = true /\
  Stableb Y_obj witness_mismatch 1 H_formula = false.
Proof. vm_compute. tauto. Qed.

Definition tau_id_D : template :=
  [(D_sym,D_formula);(H_sym,H_formula)].
Definition tau_H_D : template :=
  [(D_sym,H_formula);(H_sym,H_formula)].

Definition residual_domainb (tau : template) : bool :=
  match lookup_template D_sym tau with
  | None => false
  | Some p => Stableb Y_obj witness_mismatch 1 p
  end.

Theorem witness_residual_split :
  residual_domainb tau_id_D = true /\
  residual_domainb tau_H_D = false.
Proof. vm_compute. tauto. Qed.

Theorem no_total_truth_preserving_residual :
  ~ exists R : template -> fm,
      forall tau s,
        In s [y0_state;y1_state;y2_state] ->
        sat s
          (match lookup_template D_sym tau with
           | Some p => p | None => EqF 0 0
           end)
        =
        sat (red_state Y_obj witness_mismatch s) (R tau).
Proof.
  intros [R HR].
  pose proof (HR tau_H_D y0_state (or_introl eq_refl)) as H0.
  pose proof (HR tau_H_D y2_state
    (or_intror (or_intror (or_introl eq_refl)))) as H2.
  vm_compute in H0, H2.
  congruence.
Qed.

Theorem witness_model_nontrivial :
  sat x_state (o_goal X_obj) = true /\
  sat y0_state (o_goal Y_obj) = false /\
  sat y2_state (o_goal Y_obj) = true /\
  sat z_state (o_goal Z_obj) = false.
Proof. vm_compute. tauto. Qed.


(** 17. Named metatheorems and the repaired unit-law counterexample. *)

Lemma bool_check_decidable :
  forall b : bool, {b = true} + {b = false}.
Proof.
  intro b. destruct (Bool.bool_dec b true) as [H|H].
  - left. exact H.
  - right. apply Bool.not_true_is_false. exact H.
Defined.
Theorem finite_executable_core :
  forall S k s phi X Y p q m r,
    ({wf_fm S k phi = true} + {wf_fm S k phi = false}) *
    ({sat s phi = true} + {sat s phi = false}) *
    ({VerifyPres X Y p = true} + {VerifyPres X Y p = false}) *
    ({bowtie X Y Y (forget_scripts p) q = true} +
     {bowtie X Y Y (forget_scripts p) q = false}) *
    ({Stableb Y m r phi = true} + {Stableb Y m r phi = false})%type.
Proof.
  intros.
  repeat match goal with |- (_ * _)%type => split end;
    apply bool_check_decidable.
Defined.

Theorem index_exactness :
  forall X Y c u,
    In u (Cbase X Y c) <->
    In u (seq 0 (ch_m c)) /\ minimal_badb X Y c u = true.
Proof.
  intros. unfold Cbase. apply filter_In.
Qed.

Theorem success_mismatch_dichotomy :
  forall X Y Z p q,
    (bowtie X Y Z p q = true /\
     conflict_set X Y Z p q = []) \/
    (bowtie X Y Z p q = false /\
     conflict_set X Y Z p q <> []).
Proof.
  intros X Y Z p q.
  unfold bowtie.
  destruct (conflict_set X Y Z p q) as [|d tl] eqn:E.
  - left. cbn. tauto.
  - right. cbn. split; [reflexivity | discriminate].
Qed.

Theorem witness_minimal_deletion_breaks_coverage :
  ~ exists c,
      In c (remove Nat.eq_dec 0 (Cbase X_obj Y_obj p_ch)) /\
      le_edge p_ch c 0 = true.
Proof.
  intros [c [Hin Hle]]. vm_compute in Hin. exact Hin.
Qed.

Theorem ordinary_projection_does_not_reflect_gate :
  ~ exists F :
      list (state * state) -> list (state * state) -> bool,
      forall p q,
        F (ordinary_relation p) (ordinary_relation q) =
        bowtie X_obj Y_obj Z_obj p q.
Proof.
  intros [F HF].
  pose proof (HF p_ch q_ch) as Hbad.
  pose proof (HF p'_ch q_ch) as Hgood.
  rewrite witness_same_ordinary_projection in Hbad.
  vm_compute in Hbad, Hgood.
  congruence.
Qed.

Theorem original_right_unit_law_counterexample :
  ch_edges (composite_raw p_ch (identity_channel Y_obj)) = [] /\
  ch_edges p_ch = [(0,1)].
Proof. vm_compute. tauto. Qed.

Theorem witness_D_is_restatable :
  restates Y_obj witness_mismatch 1 D_formula D_formula.
Proof.
  split.
  - reflexivity.
  - intros s Hs.
    vm_compute in Hs |- *.
    destruct Hs as [Hs|[Hs|[Hs|Hs]]]; try contradiction;
      subst s; reflexivity.
Qed.

Theorem witness_original_goal_has_no_restatement :
  forall theta,
    ~ restates Y_obj witness_mismatch 1 H_formula theta.
Proof.
  intros theta [Hwf Hrest].
  pose proof
    (Hrest y0_state (or_introl eq_refl)) as H0.
  pose proof
    (Hrest y2_state
      (or_intror (or_intror (or_introl eq_refl)))) as H2.
  vm_compute in H0, H2.
  congruence.
Qed.

Theorem reliable_finite_model :
  wf_state sigX 1 x_state = true /\
  wf_state sigY 1 y0_state = true /\
  wf_state sigY 1 y1_state = true /\
  wf_state sigY 1 y2_state = true /\
  wf_state sigZ 1 z_state = true /\
  wf_fm sigX 1 (o_goal X_obj) = true /\
  wf_fm sigY 1 (o_goal Y_obj) = true /\
  wf_fm sigZ 1 (o_goal Z_obj) = true /\
  VerifyPres X_obj Y_obj p_pres = true /\
  VerifyPres X_obj Y_obj p'_pres = true /\
  VerifyPres Y_obj Z_obj q_pres = true /\
  sat x_state (o_goal X_obj) = true /\
  sat y0_state (o_goal Y_obj) = false /\
  sat y2_state (o_goal Y_obj) = true /\
  sat z_state (o_goal Z_obj) = false.
Proof. vm_compute. tauto. Qed.

End CIEIH2172.
