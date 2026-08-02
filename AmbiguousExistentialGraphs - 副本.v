From Coq Require Import Lists.List.
From Coq Require Import Arith.PeanoNat.

Import ListNotations.

Module AmbiguousExistentialGraphs.

Fixpoint remove_nat (x : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | y :: ys => if Nat.eqb x y then remove_nat x ys else y :: remove_nat x ys
  end.

Fixpoint union_nat (xs ys : list nat) : list nat :=
  match xs with
  | [] => ys
  | x :: rest => if existsb (Nat.eqb x) ys then union_nat rest ys
                 else x :: union_nat rest ys
  end.

Section FirstOrder.

Variable Dom : Type.
Variable Rel : Type.
Variable rel_arity : Rel -> nat.

Inductive formula : Type :=
| FRel : Rel -> list nat -> formula
| FEq : nat -> nat -> formula
| FTop : formula
| FBot : formula
| FNeg : formula -> formula
| FAnd : formula -> formula -> formula
| FOr : formula -> formula -> formula
| FImp : formula -> formula -> formula
| FIff : formula -> formula -> formula
| FExists : nat -> formula -> formula
| FForall : nat -> formula -> formula.

Fixpoint fv (phi : formula) : list nat :=
  match phi with
  | FRel _ xs => xs
  | FEq x y => [x; y]
  | FTop => []
  | FBot => []
  | FNeg psi => fv psi
  | FAnd psi chi
  | FOr psi chi
  | FImp psi chi
  | FIff psi chi => union_nat (fv psi) (fv chi)
  | FExists x psi
  | FForall x psi => remove_nat x (fv psi)
  end.

Fixpoint wf_formula (phi : formula) : Prop :=
  match phi with
  | FRel R xs => length xs = rel_arity R
  | FEq _ _ => True
  | FTop => True
  | FBot => True
  | FNeg psi => wf_formula psi
  | FAnd psi chi
  | FOr psi chi
  | FImp psi chi
  | FIff psi chi => wf_formula psi /\ wf_formula chi
  | FExists _ psi
  | FForall _ psi => wf_formula psi
  end.

Definition sentence (phi : formula) : Prop :=
  wf_formula phi /\ fv phi = [].

Record structure : Type := {
  rel_denote : Rel -> list Dom -> Prop
}.

Definition assignment : Type := nat -> Dom.

Definition update (g : assignment) (x : nat) (a : Dom) : assignment :=
  fun y => if Nat.eqb y x then a else g y.

Fixpoint sat (M : structure) (g : assignment) (phi : formula) : Prop :=
  match phi with
  | FRel R xs => rel_denote M R (map g xs)
  | FEq x y => g x = g y
  | FTop => True
  | FBot => False
  | FNeg psi => ~ sat M g psi
  | FAnd psi chi => sat M g psi /\ sat M g chi
  | FOr psi chi => sat M g psi \/ sat M g chi
  | FImp psi chi => sat M g psi -> sat M g chi
  | FIff psi chi => sat M g psi <-> sat M g chi
  | FExists x psi => exists a, sat M (update g x a) psi
  | FForall x psi => forall a, sat M (update g x a) psi
  end.

Definition models_sentence (M : structure) (phi : formula) : Prop :=
  sentence phi /\ forall g, sat M g phi.

Definition sent_consequence (Gamma : formula -> Prop) (phi : formula) : Prop :=
  forall M,
    (forall gamma, Gamma gamma -> models_sentence M gamma) ->
    models_sentence M phi.

Record region_tree : Type := {
  region_node : Type;
  region_nodes : list region_node;
  region_root : region_node;
  region_parent : region_node -> option region_node
}.

Inductive region_ancestor (T : region_tree) :
    region_node T -> region_node T -> Prop :=
| AncRefl :
    forall n, region_ancestor T n n
| AncStep :
    forall m p n,
      region_parent T m = Some p ->
      region_ancestor T p n ->
      region_ancestor T m n.

Definition region_strict_ancestor
    (T : region_tree) (m n : region_node T) : Prop :=
  region_ancestor T m n /\ m <> n.

Definition region_child
    (T : region_tree) (m n : region_node T) : Prop :=
  region_parent T m = Some n.

Record ceg : Type := {
  ceg_tree : region_tree;
  relation_occurrence : Type;
  relation_occurrences : list relation_occurrence;
  occurrence_label : relation_occurrence -> Rel;
  occurrence_region : relation_occurrence -> region_node ceg_tree;
  port_equiv : relation_occurrence * nat -> relation_occurrence * nat -> Prop;
  id_class : Type;
  id_classes : list id_class;
  port_id : relation_occurrence -> nat -> id_class;
  port_equiv_iff :
    forall a i b j, port_equiv (a, i) (b, j) <-> port_id a i = port_id b j;
  id_birth : id_class -> region_node ceg_tree;
  id_birth_loc :
    forall c a i,
      In a relation_occurrences ->
      i < rel_arity (occurrence_label a) ->
      port_id a i = c ->
      region_ancestor ceg_tree (occurrence_region a) (id_birth c);
  id_birth_lca :
    forall c v,
      (forall a i,
        In a relation_occurrences ->
        i < rel_arity (occurrence_label a) ->
        port_id a i = c ->
        region_ancestor ceg_tree (occurrence_region a) v) ->
      region_ancestor ceg_tree (id_birth c) v
}.

Definition born_class (G : ceg) (n : region_node (ceg_tree G))
    (c : id_class G) : Prop :=
  id_birth G c = n.

Definition ext_class (G : ceg) (n : region_node (ceg_tree G))
    (c : id_class G) : Prop :=
  region_strict_ancestor (ceg_tree G) n (id_birth G c).

Definition extends_on {A B : Type} (P : A -> Prop)
    (h g : A -> B) : Prop :=
  forall x, P x -> g x = h x.

Definition occurrence_tuple
    (G : ceg) (env : id_class G -> Dom) (a : relation_occurrence G)
    : list Dom :=
  map (fun i => env (port_id G a i))
      (seq 0 (rel_arity (occurrence_label G a))).

Definition region_relations_hold
    (M : structure) (G : ceg) (n : region_node (ceg_tree G))
    (env : id_class G -> Dom) : Prop :=
  forall a,
    In a (relation_occurrences G) ->
    occurrence_region G a = n ->
    rel_denote M (occurrence_label G a) (occurrence_tuple G env a).

Fixpoint region_sat_fuel
    (fuel : nat) (M : structure) (G : ceg)
    (n : region_node (ceg_tree G)) (h : id_class G -> Dom) : Prop :=
  match fuel with
  | 0 => False
  | S fuel' =>
      exists hplus : id_class G -> Dom,
        extends_on (ext_class G n) h hplus /\
        region_relations_hold M G n hplus /\
        forall m,
          In m (region_nodes (ceg_tree G)) ->
          region_child (ceg_tree G) m n ->
          ~ region_sat_fuel fuel' M G m hplus
  end.

Definition ceg_sat (M : structure) (G : ceg) : Prop :=
  exists h0 : id_class G -> Dom,
    region_sat_fuel (length (region_nodes (ceg_tree G))) M G
      (region_root (ceg_tree G)) h0.

Definition ceg_consequence (Gamma : ceg -> Prop) (H : ceg) : Prop :=
  forall M, (forall G, Gamma G -> ceg_sat M G) -> ceg_sat M H.

Definition rep_tau (tau : formula -> ceg) : Prop :=
  forall phi M, sentence phi ->
    (models_sentence M phi <-> ceg_sat M (tau phi)).

Record lae_expr : Type := {
  lae_choice : Type;
  lae_legal : lae_choice -> Prop;
  lae_parse : lae_choice -> formula;
  lae_choices : list lae_choice;
  lae_choices_complete : forall w, lae_legal w <-> In w lae_choices;
  lae_nonempty : exists w, lae_legal w;
  lae_sentence : forall w, lae_legal w -> sentence (lae_parse w)
}.

Definition parse_lae (E : lae_expr) (phi : formula) : Prop :=
  exists w, lae_legal E w /\ phi = lae_parse E w.

Definition lae_parse_list (E : lae_expr) : list formula :=
  map (lae_parse E) (lae_choices E).

Lemma parse_lae_list_complete :
  forall E phi, parse_lae E phi <-> In phi (lae_parse_list E).
Proof.
  intros E phi; split.
  - intros [w [Hw ->]].
    unfold lae_parse_list.
    apply in_map.
    apply (proj1 (lae_choices_complete E w)).
    exact Hw.
  - intros Hphi.
    unfold lae_parse_list in Hphi.
    destruct (proj1 (in_map_iff _ _ _) Hphi)
      as [w [Hw_eq Hw_in]].
    exists w; split.
    + apply (proj2 (lae_choices_complete E w)).
      exact Hw_in.
    + symmetry. exact Hw_eq.
Qed.

Lemma lae_parse_list_nonempty :
  forall E, exists phi, In phi (lae_parse_list E).
Proof.
  intros E.
  destruct (lae_nonempty E) as [w Hw].
  exists (lae_parse E w).
  unfold lae_parse_list.
  apply in_map.
  apply (proj1 (lae_choices_complete E w)).
  exact Hw.
Qed.

Definition lae_preorder (E F : lae_expr) : Prop :=
  forall phi, parse_lae E phi -> parse_lae F phi.

Lemma lae_preorder_refl : forall E, lae_preorder E E.
Proof.
  intros E phi Hphi. exact Hphi.
Qed.

Lemma lae_preorder_trans :
  forall E F G, lae_preorder E F -> lae_preorder F G -> lae_preorder E G.
Proof.
  intros E F G HEF HFG phi Hphi.
  apply HFG. apply HEF. exact Hphi.
Qed.

Record aeg : Type := {
  aeg_choice : Type;
  aeg_legal : aeg_choice -> Prop;
  aeg_parse : aeg_choice -> ceg;
  aeg_choices : list aeg_choice;
  aeg_choices_complete : forall w, aeg_legal w <-> In w aeg_choices;
  aeg_nonempty : exists w, aeg_legal w
}.

Definition parse_aeg (D : aeg) (G : ceg) : Prop :=
  exists w, aeg_legal D w /\ G = aeg_parse D w.

Definition aeg_parse_list (D : aeg) : list ceg :=
  map (aeg_parse D) (aeg_choices D).

Lemma parse_aeg_list_complete :
  forall D G, parse_aeg D G <-> In G (aeg_parse_list D).
Proof.
  intros D G; split.
  - intros [w [Hw ->]].
    unfold aeg_parse_list.
    apply in_map.
    apply (proj1 (aeg_choices_complete D w)).
    exact Hw.
  - intros HG.
    unfold aeg_parse_list in HG.
    destruct (proj1 (in_map_iff _ _ _) HG)
      as [w [Hw_eq Hw_in]].
    exists w; split.
    + apply (proj2 (aeg_choices_complete D w)).
      exact Hw_in.
    + symmetry. exact Hw_eq.
Qed.

Lemma aeg_parse_list_nonempty :
  forall D, exists G, In G (aeg_parse_list D).
Proof.
  intros D.
  destruct (aeg_nonempty D) as [w Hw].
  exists (aeg_parse D w).
  unfold aeg_parse_list.
  apply in_map.
  apply (proj1 (aeg_choices_complete D w)).
  exact Hw.
Qed.

Definition aeg_preorder (D E : aeg) : Prop :=
  forall G, parse_aeg D G -> parse_aeg E G.

Lemma aeg_preorder_refl : forall D, aeg_preorder D D.
Proof.
  intros D G HG. exact HG.
Qed.

Lemma aeg_preorder_trans :
  forall D E F, aeg_preorder D E -> aeg_preorder E F -> aeg_preorder D F.
Proof.
  intros D E F HDE HEF G HG.
  apply HEF. apply HDE. exact HG.
Qed.

Definition translate_expr (tau : formula -> ceg) (E : lae_expr) : aeg := {|
  aeg_choice := lae_choice E;
  aeg_legal := lae_legal E;
  aeg_parse := fun w => tau (lae_parse E w);
  aeg_choices := lae_choices E;
  aeg_choices_complete := lae_choices_complete E;
  aeg_nonempty := lae_nonempty E
|}.

Lemma translate_parse :
  forall tau E w,
    lae_legal E w ->
    parse_aeg (translate_expr tau E) (tau (lae_parse E w)).
Proof.
  intros tau E w Hw.
  exists w; split; [exact Hw|reflexivity].
Qed.

Definition iota_ceg (G : ceg) : aeg := {|
  aeg_choice := unit;
  aeg_legal := fun _ => True;
  aeg_parse := fun _ => G;
  aeg_choices := [tt];
  aeg_choices_complete :=
    fun w =>
      match w with
      | tt => conj (fun _ => or_introl eq_refl) (fun _ => I)
      end;
  aeg_nonempty := ex_intro _ tt I
|}.

Lemma parse_iota_ceg :
  forall G H, parse_aeg (iota_ceg G) H <-> H = G.
Proof.
  intros G H; split.
  - intros [[ ] [_ HH]]. exact HH.
  - intros ->. exists tt; split; [exact I|reflexivity].
Qed.

Record lae_framework : Type := {
  lf_index : Type;
  lf_indices : list lf_index;
  lf_strategy : Type;
  lf_legal_strategy : lf_strategy -> Prop;
  lf_strategies : list lf_strategy;
  lf_strategy_complete : forall s, lf_legal_strategy s <-> In s lf_strategies;
  lf_strategy_nonempty : exists s, lf_legal_strategy s;
  lf_premise : lf_index -> lae_expr;
  lf_conclusion : lae_expr;
  lf_choose_premise : forall i, lf_strategy -> lae_choice (lf_premise i);
  lf_choose_conclusion : lf_strategy -> lae_choice lf_conclusion;
  lf_premise_legal :
    forall i s, lf_legal_strategy s ->
      lae_legal (lf_premise i) (lf_choose_premise i s);
  lf_conclusion_legal :
    forall s, lf_legal_strategy s ->
      lae_legal lf_conclusion (lf_choose_conclusion s)
}.

Definition lae_premise_set (A : lae_framework)
    (s : lf_strategy A) : formula -> Prop :=
  fun phi =>
    exists i,
      In i (lf_indices A) /\
      phi = lae_parse (lf_premise A i) (lf_choose_premise A i s).

Definition lae_conclusion_at (A : lae_framework)
    (s : lf_strategy A) : formula :=
  lae_parse (lf_conclusion A) (lf_choose_conclusion A s).

Definition lae_valid (A : lae_framework) : Prop :=
  forall s,
    lf_legal_strategy A s ->
    sent_consequence (lae_premise_set A s) (lae_conclusion_at A s).

Record aeg_framework : Type := {
  af_index : Type;
  af_indices : list af_index;
  af_strategy : Type;
  af_legal_strategy : af_strategy -> Prop;
  af_strategies : list af_strategy;
  af_strategy_complete : forall s, af_legal_strategy s <-> In s af_strategies;
  af_strategy_nonempty : exists s, af_legal_strategy s;
  af_premise : af_index -> aeg;
  af_conclusion : aeg;
  af_choose_premise : forall i, af_strategy -> aeg_choice (af_premise i);
  af_choose_conclusion : af_strategy -> aeg_choice af_conclusion;
  af_premise_legal :
    forall i s, af_legal_strategy s ->
      aeg_legal (af_premise i) (af_choose_premise i s);
  af_conclusion_legal :
    forall s, af_legal_strategy s ->
      aeg_legal af_conclusion (af_choose_conclusion s)
}.

Definition aeg_premise_set (A : aeg_framework)
    (s : af_strategy A) : ceg -> Prop :=
  fun G =>
    exists i,
      In i (af_indices A) /\
      G = aeg_parse (af_premise A i) (af_choose_premise A i s).

Definition aeg_conclusion_at (A : aeg_framework)
    (s : af_strategy A) : ceg :=
  aeg_parse (af_conclusion A) (af_choose_conclusion A s).

Definition aeg_valid (A : aeg_framework) : Prop :=
  forall s,
    af_legal_strategy A s ->
    ceg_consequence (aeg_premise_set A s) (aeg_conclusion_at A s).

Definition translate_framework
    (tau : formula -> ceg) (A : lae_framework) : aeg_framework := {|
  af_index := lf_index A;
  af_indices := lf_indices A;
  af_strategy := lf_strategy A;
  af_legal_strategy := lf_legal_strategy A;
  af_strategies := lf_strategies A;
  af_strategy_complete := lf_strategy_complete A;
  af_strategy_nonempty := lf_strategy_nonempty A;
  af_premise := fun i => translate_expr tau (lf_premise A i);
  af_conclusion := translate_expr tau (lf_conclusion A);
  af_choose_premise := lf_choose_premise A;
  af_choose_conclusion := lf_choose_conclusion A;
  af_premise_legal := lf_premise_legal A;
  af_conclusion_legal := lf_conclusion_legal A
|}.

Theorem lae_to_aeg_sound :
  forall tau A,
    rep_tau tau ->
    lae_valid A ->
    aeg_valid (translate_framework tau A).
Proof.
  intros tau A Htau Hlae s Hs M Hprem.
  simpl in *.
  set (concl := lae_parse (lf_conclusion A) (lf_choose_conclusion A s)).
  assert (Hsent_concl : sentence concl).
  { unfold concl. apply lae_sentence. apply lf_conclusion_legal. exact Hs. }
  apply (proj1 (Htau concl M Hsent_concl)).
  apply (Hlae s Hs M).
  intros gamma [i [Hin Hgamma]].
  subst gamma.
  assert (Hsent :
    sentence (lae_parse (lf_premise A i) (lf_choose_premise A i s))).
  { apply lae_sentence. apply lf_premise_legal. exact Hs. }
  apply (proj2 (Htau _ M Hsent)).
  apply Hprem.
  exists i; split; [exact Hin|reflexivity].
Qed.

Theorem lae_aeg_equivalent :
  forall tau A,
    rep_tau tau ->
    (lae_valid A <-> aeg_valid (translate_framework tau A)).
Proof.
  intros tau A Htau; split.
  - apply lae_to_aeg_sound; exact Htau.
  - intros Haeg s Hs M Hprem.
    simpl in *.
    set (concl := lae_parse (lf_conclusion A) (lf_choose_conclusion A s)).
    assert (Hsent_concl : sentence concl).
    { unfold concl. apply lae_sentence. apply lf_conclusion_legal. exact Hs. }
    apply (proj2 (Htau concl M Hsent_concl)).
    apply (Haeg s Hs M).
    intros G [i [Hin HG]].
    subst G.
    assert (Hsent :
      sentence (lae_parse (lf_premise A i) (lf_choose_premise A i s))).
    { apply lae_sentence. apply lf_premise_legal. exact Hs. }
    apply (proj1 (Htau _ M Hsent)).
    apply Hprem.
    exists i; split; [exact Hin|reflexivity].
Qed.

Definition classic_framework (Gamma : list ceg) (H : ceg) : aeg_framework := {|
  af_index := ceg;
  af_indices := Gamma;
  af_strategy := unit;
  af_legal_strategy := fun _ => True;
  af_strategies := [tt];
  af_strategy_complete :=
    fun s =>
      match s with
      | tt => conj (fun _ => or_introl eq_refl) (fun _ => I)
      end;
  af_strategy_nonempty := ex_intro _ tt I;
  af_premise := fun G => iota_ceg G;
  af_conclusion := iota_ceg H;
  af_choose_premise := fun _ _ => tt;
  af_choose_conclusion := fun _ => tt;
  af_premise_legal := fun _ _ _ => I;
  af_conclusion_legal := fun _ _ => I
|}.

Definition ceg_consequence_list (Gamma : list ceg) (H : ceg) : Prop :=
  ceg_consequence (fun G => In G Gamma) H.

Theorem classic_embedding_conservative :
  forall Gamma H,
    aeg_valid (classic_framework Gamma H) <->
    ceg_consequence_list Gamma H.
Proof.
  intros Gamma H; split.
  - intros HA M Hprem.
    specialize (HA tt I M).
    apply HA.
    intros G [i [Hin HG]].
    simpl in HG. subst G. exact (Hprem i Hin).
  - intros HC s Hs M Hprem.
    destruct s.
    apply HC.
    intros G Hin.
    apply Hprem.
    exists G; split; [exact Hin|reflexivity].
Qed.

Definition res_cert (D : aeg) (w : aeg_choice D) (G : ceg) : Prop :=
  aeg_legal D w /\ G = aeg_parse D w.

Definition strategy_counter
    (A : aeg_framework) (s : af_strategy A) (M : structure) : Prop :=
  af_legal_strategy A s /\
  (forall G, aeg_premise_set A s G -> ceg_sat M G) /\
  ~ ceg_sat M (aeg_conclusion_at A s).

Definition aeg_judgment (A : aeg_framework) : Prop :=
  ~ exists s M, strategy_counter A s M.

Theorem aeg_valid_no_counter :
  forall A, aeg_valid A -> aeg_judgment A.
Proof.
  intros A HA [s [M [Hs [Hprem Hnot]]]].
  apply Hnot.
  apply (HA s Hs M Hprem).
Qed.

Inductive beta_pattern : Type :=
| ScopePattern : aeg -> beta_pattern
| IdLinePattern : aeg -> beta_pattern
| CutAttachPattern : aeg -> beta_pattern
| RegionMembershipPattern : aeg -> beta_pattern
| ArgumentAttachPattern : aeg -> beta_pattern.

Definition beta_pattern_diagram (P : beta_pattern) : aeg :=
  match P with
  | ScopePattern D => D
  | IdLinePattern D => D
  | CutAttachPattern D => D
  | RegionMembershipPattern D => D
  | ArgumentAttachPattern D => D
  end.

Record formal_system (tau : formula -> ceg) : Type := {
  fs_rep_tau : rep_tau tau;
  fs_lae_valid : lae_framework -> Prop := lae_valid;
  fs_aeg_valid : aeg_framework -> Prop := aeg_valid;
  fs_translate_expr : lae_expr -> aeg := translate_expr tau;
  fs_translate_framework : lae_framework -> aeg_framework :=
    translate_framework tau;
  fs_lae_to_aeg :
    forall A, lae_valid A -> aeg_valid (translate_framework tau A);
  fs_lae_aeg_equiv :
    forall A, lae_valid A <-> aeg_valid (translate_framework tau A);
  fs_classic_conservative :
    forall Gamma H,
      aeg_valid (classic_framework Gamma H) <->
      ceg_consequence_list Gamma H;
  fs_res_cert : forall D, aeg_choice D -> ceg -> Prop := res_cert;
  fs_counter : forall A : aeg_framework, af_strategy A -> structure -> Prop :=
    strategy_counter;
  fs_beta_pattern : Type;
  fs_beta_pattern_diagram : fs_beta_pattern -> aeg
}.

Definition build_formal_system
    (tau : formula -> ceg) (Htau : rep_tau tau) : formal_system tau := {|
  fs_rep_tau := Htau;
  fs_lae_to_aeg := fun A => lae_to_aeg_sound tau A Htau;
  fs_lae_aeg_equiv := fun A => lae_aeg_equivalent tau A Htau;
  fs_classic_conservative := classic_embedding_conservative
  ;
  fs_beta_pattern := beta_pattern;
  fs_beta_pattern_diagram := beta_pattern_diagram
|}.

End FirstOrder.

End AmbiguousExistentialGraphs.
