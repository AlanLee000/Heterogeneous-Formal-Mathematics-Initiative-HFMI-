From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryRuleAPI.
Require Import FormalSystemFactoryStructuralCodec.
Require Import FormalSystemFactoryNatCodec.

Import ListNotations.

Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.
Module SC := FormalSystemFactoryStructuralCodec.FormalSystemFactoryStructuralCodec.
Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.

Module FormalSystemFactoryCanonicalFuel.

Definition canonical_fuel (n : nat) : nat := S (S n).

Lemma code_depth_nat_index_bound :
  forall n,
    (forall c,
        NC.code_depth c <= n ->
        NC.code_depth c <= S (NC.encode_code_nat c)) /\
    (forall cs,
        NC.code_list_depth cs <= n ->
        NC.code_list_depth cs <= S (NC.encode_code_list_nat cs)).
Proof.
  induction n as [|n IH].
  - split.
    + intros c Hdepth.
      destruct c; simpl in *; lia.
    + intros cs Hdepth.
      destruct cs as [|c rest]; simpl in *; lia.
  - destruct IH as [IHc IHl].
    split.
    + intros c Hdepth.
      destruct c as [atom | tag children].
      * simpl; lia.
      * simpl NC.code_depth in Hdepth.
        change
          (S
             ((fix children_depth (cs : list SC.code) : nat :=
                 match cs with
                 | [] => 0
                 | child :: rest =>
                     S (Nat.max (NC.code_depth child)
                          (children_depth rest))
                 end) children) <=
           S (NC.encode_code_nat (SC.CNode tag children))).
        assert
          (Hdepth_eq :
            ((fix children_depth (cs : list SC.code) : nat :=
                match cs with
                | [] => 0
                | child :: rest =>
                    S (Nat.max (NC.code_depth child)
                         (children_depth rest))
                end) children) = NC.code_list_depth children).
        {
          clear Hdepth.
          induction children as [|child rest IHrest]; simpl.
          - reflexivity.
          - rewrite IHrest; reflexivity.
        }
        assert
          (Henc :
            ((fix encode_children (cs : list SC.code) : nat :=
                match cs with
                | [] => 0
                | child :: rest =>
                    S (NC.pair_nat (NC.encode_code_nat child)
                         (encode_children rest))
                end) children) = NC.encode_code_list_nat children).
        {
          clear Hdepth Hdepth_eq.
          induction children as [|child rest IHrest]; simpl.
          - reflexivity.
          - rewrite IHrest; reflexivity.
        }
        rewrite Hdepth_eq in Hdepth.
        rewrite Hdepth_eq.
        simpl NC.encode_code_nat.
        rewrite Henc.
        change
          (S (NC.code_list_depth children) <=
           S (S (NC.pair_nat (S tag) (NC.encode_code_list_nat children)))).
        specialize (IHl children).
        assert (NC.code_list_depth children <= S (NC.encode_code_list_nat children))
          by (apply IHl; lia).
        pose proof (NC.pair_nat_ge_right (S tag) (NC.encode_code_list_nat children)).
        lia.
    + intros cs Hdepth.
      destruct cs as [|c rest].
      * simpl; lia.
      * simpl NC.code_list_depth in Hdepth.
        simpl NC.encode_code_list_nat.
        change
          (S (Nat.max (NC.code_depth c) (NC.code_list_depth rest)) <=
           S (S (NC.pair_nat
                   (NC.encode_code_nat c)
                   (NC.encode_code_list_nat rest)))).
        assert (Hc : NC.code_depth c <= S (NC.encode_code_nat c))
          by (apply IHc; lia).
        assert (Hr : NC.code_list_depth rest <= S (NC.encode_code_list_nat rest))
          by (apply IHl; lia).
        pose proof (NC.pair_nat_ge_left
                      (NC.encode_code_nat c)
                      (NC.encode_code_list_nat rest)) as Hleft.
        pose proof (NC.pair_nat_ge_right
                      (NC.encode_code_nat c)
                      (NC.encode_code_list_nat rest)) as Hright.
        assert
          (Nat.max (NC.code_depth c) (NC.code_list_depth rest) <=
           S (NC.pair_nat
                (NC.encode_code_nat c)
                (NC.encode_code_list_nat rest))).
        {
          apply Nat.max_lub; lia.
        }
        lia.
Qed.

Lemma code_depth_le_encoded_index :
  forall c, NC.code_depth c <= S (NC.encode_code_nat c).
Proof.
  intro c.
  pose proof (proj1 (code_depth_nat_index_bound (NC.code_depth c)) c) as H.
  apply H; lia.
Qed.

Lemma code_list_depth_le_encoded_index :
  forall cs, NC.code_list_depth cs <= S (NC.encode_code_list_nat cs).
Proof.
  intro cs.
  pose proof (proj2 (code_depth_nat_index_bound (NC.code_list_depth cs)) cs) as H.
  apply H; lia.
Qed.

Definition decode_code_nat (n : nat) : option SC.code :=
  NC.decode_code_nat_fuel (canonical_fuel n) n.

Lemma decode_encode_code_nat :
  forall c,
    decode_code_nat (NC.encode_code_nat c) = Some c.
Proof.
  intro c.
  unfold decode_code_nat, canonical_fuel.
  pose proof (proj1 (NC.code_depth_bound (S (NC.encode_code_nat c))) c) as H.
  apply H.
  apply code_depth_le_encoded_index.
Qed.

Definition decode_proof_object_nat (n : nat) : option R.proof_object :=
  match decode_code_nat n with
  | Some c => SC.decode_proof_object c
  | None => None
  end.

Definition decode_judgment_nat (n : nat) : option R.judgment :=
  match decode_code_nat n with
  | Some c => SC.decode_judgment c
  | None => None
  end.

Definition check_proof_nat
           (spec : R.TheorySpec)
           (proof_nat goal_nat : nat) : bool :=
  match decode_proof_object_nat proof_nat,
        decode_judgment_nat goal_nat with
  | Some p, Some goal => R.check_proof spec p goal
  | _, _ => false
  end.

Lemma decode_encode_proof_object_nat :
  forall p,
    decode_proof_object_nat (NC.encode_proof_object_nat p) = Some p.
Proof.
  intro p.
  unfold decode_proof_object_nat, NC.encode_proof_object_nat.
  rewrite decode_encode_code_nat.
  apply SC.decode_encode_proof_object.
Qed.

Lemma decode_encode_judgment_nat :
  forall j,
    decode_judgment_nat (NC.encode_judgment_nat j) = Some j.
Proof.
  intro j.
  unfold decode_judgment_nat, NC.encode_judgment_nat.
  rewrite decode_encode_code_nat.
  apply SC.decode_encode_judgment.
Qed.

Lemma check_proof_nat_agrees :
  forall spec p goal,
    check_proof_nat
      spec
      (NC.encode_proof_object_nat p)
      (NC.encode_judgment_nat goal) =
    R.check_proof spec p goal.
Proof.
  intros spec p goal.
  unfold check_proof_nat.
  rewrite decode_encode_proof_object_nat.
  rewrite decode_encode_judgment_nat.
  reflexivity.
Qed.

Definition canonical_nat_rule_api : R.RuleAPI :=
  {|
    R.api_judgment := nat;
    R.api_formula_judgment :=
      fun t => NC.encode_judgment_nat (R.JFormula t);
    R.api_sequent_judgment :=
      fun ctx t => NC.encode_judgment_nat (R.JSequent ctx t);
    R.api_rule_schema := R.raw_rule_api.(R.api_rule_schema);
    R.api_theory_spec := R.raw_rule_api.(R.api_theory_spec);
    R.api_proof_object := nat;
    R.api_check_proof := fun spec proof_nat goal => check_proof_nat spec proof_nat goal;
    R.api_derivable :=
      fun spec goal_nat =>
        exists goal,
          decode_judgment_nat goal_nat = Some goal /\
          R.Derivable spec goal
  |}.

Lemma canonical_nat_example_rule_checked :
  check_proof_nat
    R.example_rule_theory
    (NC.encode_proof_object_nat R.example_rule_proof)
    (NC.encode_judgment_nat (R.rule_conclusion R.example_rule)) = true.
Proof.
  rewrite check_proof_nat_agrees.
  exact R.example_rule_checked.
Qed.

End FormalSystemFactoryCanonicalFuel.
