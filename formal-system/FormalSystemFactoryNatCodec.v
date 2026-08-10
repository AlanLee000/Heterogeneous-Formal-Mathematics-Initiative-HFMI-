From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryRuleAPI.
Require Import FormalSystemFactoryStructuralCodec.

Import ListNotations.

Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.
Module SC := FormalSystemFactoryStructuralCodec.FormalSystemFactoryStructuralCodec.

Module FormalSystemFactoryNatCodec.

Fixpoint pair_nat (x y : nat) : nat :=
  match x with
  | 0 => 2 * y
  | S x' => S (2 * pair_nat x' y)
  end.

Fixpoint unpair_nat_fuel (fuel n : nat) : option (nat * nat) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      if Nat.even n then Some (0, Nat.div2 n)
      else
        match unpair_nat_fuel fuel' (Nat.div2 n) with
        | Some (x, y) => Some (S x, y)
        | None => None
        end
  end.

Definition unpair_nat (n : nat) : option (nat * nat) :=
  unpair_nat_fuel (S n) n.

Lemma even_pair_zero :
  forall y, Nat.even (pair_nat 0 y) = true.
Proof.
  intros y; simpl.
  apply Nat.even_even.
Qed.

Lemma div2_pair_zero :
  forall y, Nat.div2 (pair_nat 0 y) = y.
Proof.
  intros y; simpl.
  apply Nat.div2_even.
Qed.

Lemma even_pair_succ :
  forall x y, Nat.even (pair_nat (S x) y) = false.
Proof.
  intros x y.
  change (Nat.even (S (2 * pair_nat x y)) = false).
  replace (S (2 * pair_nat x y)) with (2 * pair_nat x y + 1) by lia.
  apply Nat.even_odd.
Qed.

Lemma div2_pair_succ :
  forall x y, Nat.div2 (pair_nat (S x) y) = pair_nat x y.
Proof.
  intros x y; simpl.
  apply Nat.div2_succ_double.
Qed.

Lemma unpair_pair_fuel :
  forall x y fuel,
    x < fuel ->
    unpair_nat_fuel fuel (pair_nat x y) = Some (x, y).
Proof.
  induction x as [|x IH]; intros y fuel Hfuel.
  - destruct fuel as [|fuel']; [lia |].
    change (unpair_nat_fuel (S fuel') (pair_nat 0 y) = Some (0, y)).
    simpl unpair_nat_fuel.
    simpl pair_nat.
    replace (y + (y + 0)) with (2 * y) by lia.
    rewrite Nat.even_even, Nat.div2_even.
    reflexivity.
  - destruct fuel as [|fuel']; [lia |].
    change (unpair_nat_fuel (S fuel') (pair_nat (S x) y) = Some (S x, y)).
    simpl unpair_nat_fuel.
    change
      ((if Nat.even (S (2 * pair_nat x y))
        then Some (0, Nat.div2 (S (2 * pair_nat x y)))
        else
          match unpair_nat_fuel fuel' (Nat.div2 (S (2 * pair_nat x y))) with
          | Some (x0, y0) => Some (S x0, y0)
          | None => None
          end) = Some (S x, y)).
    replace (S (2 * pair_nat x y)) with (2 * pair_nat x y + 1) by lia.
    rewrite Nat.even_odd, Nat.div2_odd'.
    rewrite IH by lia.
    reflexivity.
Qed.

Lemma unpair_pair :
  forall x y,
    unpair_nat (pair_nat x y) = Some (x, y).
Proof.
  intros x y.
  unfold unpair_nat.
  apply unpair_pair_fuel.
  induction x as [|x IH]; simpl; lia.
Qed.

Lemma pair_nat_ge_left :
  forall x y, x <= pair_nat x y.
Proof.
  induction x as [|x IH]; intros y; simpl.
  - lia.
  - specialize (IH y).
    assert (pair_nat x y <= 2 * pair_nat x y) by lia.
    lia.
Qed.

Lemma pair_nat_ge_right :
  forall x y, y <= pair_nat x y.
Proof.
  induction x as [|x IH]; intros y; simpl.
  - lia.
  - specialize (IH y).
    assert (pair_nat x y <= 2 * pair_nat x y) by lia.
    lia.
Qed.

Fixpoint encode_code_nat (c : SC.code) : nat :=
  match c with
  | SC.CAtom n => S (pair_nat 0 n)
  | SC.CNode tag children =>
      let fix encode_children (cs : list SC.code) : nat :=
          match cs with
          | [] => 0
          | child :: rest =>
              S (pair_nat (encode_code_nat child) (encode_children rest))
          end in
      S (pair_nat (S tag) (encode_children children))
  end.

Fixpoint encode_code_list_nat (cs : list SC.code) : nat :=
  match cs with
  | [] => 0
  | c :: rest => S (pair_nat (encode_code_nat c) (encode_code_list_nat rest))
  end.

Fixpoint code_depth (c : SC.code) : nat :=
  match c with
  | SC.CAtom _ => 1
  | SC.CNode _ children =>
      let fix children_depth (cs : list SC.code) : nat :=
          match cs with
          | [] => 0
          | child :: rest => S (Nat.max (code_depth child) (children_depth rest))
          end in
      S (children_depth children)
  end.

Fixpoint code_list_depth (cs : list SC.code) : nat :=
  match cs with
  | [] => 0
  | c :: rest => S (Nat.max (code_depth c) (code_list_depth rest))
  end.

Fixpoint decode_code_nat_fuel (fuel n : nat) : option SC.code :=
  match fuel, n with
  | 0, _ => None
  | S fuel', 0 => None
  | S fuel', S payload =>
      match unpair_nat payload with
      | Some (0, atom) => Some (SC.CAtom atom)
      | Some (S tag, child_payload) =>
          match decode_code_list_nat_fuel fuel' child_payload with
          | Some children => Some (SC.CNode tag children)
          | None => None
          end
      | None => None
      end
  end
with decode_code_list_nat_fuel (fuel n : nat) : option (list SC.code) :=
  match fuel, n with
  | 0, _ => None
  | S fuel', 0 => Some []
  | S fuel', S payload =>
      match unpair_nat payload with
      | Some (head_payload, tail_payload) =>
          match decode_code_nat_fuel fuel' head_payload,
                decode_code_list_nat_fuel fuel' tail_payload with
          | Some head, Some tail => Some (head :: tail)
          | _, _ => None
          end
      | None => None
      end
  end.

Lemma decode_code_nat_atom_fuel :
  forall fuel atom,
    decode_code_nat_fuel (S fuel) (S (pair_nat 0 atom)) =
    Some (SC.CAtom atom).
Proof.
  intros fuel atom.
  change
    (match unpair_nat (pair_nat 0 atom) with
     | Some (0, atom0) => Some (SC.CAtom atom0)
     | Some (S tag, child_payload) =>
         match decode_code_list_nat_fuel fuel child_payload with
         | Some children => Some (SC.CNode tag children)
         | None => None
         end
     | None => None
     end = Some (SC.CAtom atom)).
  rewrite unpair_pair.
  reflexivity.
Qed.

Lemma decode_code_nat_node_fuel :
  forall fuel tag payload children,
    decode_code_list_nat_fuel fuel payload = Some children ->
    decode_code_nat_fuel (S fuel) (S (pair_nat (S tag) payload)) =
    Some (SC.CNode tag children).
Proof.
  intros fuel tag payload children Hchildren.
  change
    (match unpair_nat (pair_nat (S tag) payload) with
     | Some (0, atom) => Some (SC.CAtom atom)
     | Some (S tag0, child_payload) =>
         match decode_code_list_nat_fuel fuel child_payload with
         | Some children0 => Some (SC.CNode tag0 children0)
         | None => None
         end
     | None => None
     end = Some (SC.CNode tag children)).
  rewrite unpair_pair.
  rewrite Hchildren.
  reflexivity.
Qed.

Lemma code_depth_bound :
  forall n,
    (forall c,
        code_depth c <= n ->
        decode_code_nat_fuel (S n) (encode_code_nat c) = Some c) /\
    (forall cs,
        code_list_depth cs <= n ->
        decode_code_list_nat_fuel (S n) (encode_code_list_nat cs) = Some cs).
Proof.
  induction n as [|n IH].
  - split.
    + intros c Hdepth.
      destruct c; simpl in Hdepth; lia.
    + intros cs Hdepth.
      destruct cs as [|c cs].
      * reflexivity.
      * simpl in Hdepth; lia.
  - destruct IH as [IHc IHl].
    split.
    + intros c Hdepth.
      destruct c as [atom | tag children].
      * simpl code_depth in Hdepth.
        apply decode_code_nat_atom_fuel.
      * simpl code_depth in Hdepth.
        change
          (decode_code_nat_fuel (S (S n))
             (S (pair_nat (S tag)
                   ((fix encode_children (cs : list SC.code) : nat :=
                       match cs with
                       | [] => 0
                       | child :: rest =>
                           S (pair_nat (encode_code_nat child)
                                (encode_children rest))
                       end) children))) =
           Some (SC.CNode tag children)).
        assert
          (Henc :
            ((fix encode_children (cs : list SC.code) : nat :=
                match cs with
                | [] => 0
                | child :: rest =>
                    S (pair_nat (encode_code_nat child)
                         (encode_children rest))
                end) children) = encode_code_list_nat children).
        {
          clear Hdepth.
          induction children as [|child rest IHrest]; simpl.
          - reflexivity.
          - rewrite IHrest; reflexivity.
        }
        assert
          (Hdepth_eq :
            ((fix children_depth (cs : list SC.code) : nat :=
                match cs with
                | [] => 0
                | child :: rest =>
                    S (Nat.max (code_depth child)
                         (children_depth rest))
                end) children) = code_list_depth children).
        {
          clear Hdepth Henc.
          induction children as [|child rest IHrest]; simpl.
          - reflexivity.
          - rewrite IHrest; reflexivity.
        }
        rewrite Hdepth_eq in Hdepth.
        rewrite Henc.
        apply decode_code_nat_node_fuel.
        apply IHl.
        lia.
    + intros cs Hdepth.
      destruct cs as [|c rest]; simpl in *.
      * reflexivity.
      * rewrite unpair_pair.
        rewrite IHc.
        -- rewrite IHl.
           ++ reflexivity.
           ++ lia.
        -- lia.
Qed.

Lemma decode_encode_code_nat_fuel :
  forall c,
    decode_code_nat_fuel (S (code_depth c)) (encode_code_nat c) = Some c.
Proof.
  intro c.
  pose proof (proj1 (code_depth_bound (code_depth c)) c) as H.
  apply H.
  lia.
Qed.

Lemma decode_encode_code_list_nat_fuel :
  forall cs,
    decode_code_list_nat_fuel (S (code_list_depth cs))
                              (encode_code_list_nat cs) = Some cs.
Proof.
  intro cs.
  pose proof (proj2 (code_depth_bound (code_list_depth cs)) cs) as H.
  apply H.
  lia.
Qed.

Definition encode_proof_object_nat (p : R.proof_object) : nat :=
  encode_code_nat (SC.encode_proof_object p).

Definition encode_judgment_nat (j : R.judgment) : nat :=
  encode_code_nat (SC.encode_judgment j).

Definition decode_proof_object_nat
           (fuel n : nat) : option R.proof_object :=
  match decode_code_nat_fuel fuel n with
  | Some c => SC.decode_proof_object c
  | None => None
  end.

Definition decode_judgment_nat
           (fuel n : nat) : option R.judgment :=
  match decode_code_nat_fuel fuel n with
  | Some c => SC.decode_judgment c
  | None => None
  end.

Lemma decode_encode_proof_object_nat :
  forall p,
    decode_proof_object_nat
      (S (code_depth (SC.encode_proof_object p)))
      (encode_proof_object_nat p) = Some p.
Proof.
  intro p.
  unfold decode_proof_object_nat, encode_proof_object_nat.
  rewrite decode_encode_code_nat_fuel.
  apply SC.decode_encode_proof_object.
Qed.

Lemma decode_encode_judgment_nat :
  forall j,
    decode_judgment_nat
      (S (code_depth (SC.encode_judgment j)))
      (encode_judgment_nat j) = Some j.
Proof.
  intro j.
  unfold decode_judgment_nat, encode_judgment_nat.
  rewrite decode_encode_code_nat_fuel.
  apply SC.decode_encode_judgment.
Qed.

Definition decoded_nat_check_proof_with_fuel
           (spec : R.TheorySpec)
           (proof_fuel goal_fuel proof_nat goal_nat : nat) : bool :=
  match decode_proof_object_nat proof_fuel proof_nat,
        decode_judgment_nat goal_fuel goal_nat with
  | Some p, Some goal => R.check_proof spec p goal
  | _, _ => false
  end.

Lemma decoded_nat_check_proof_agrees :
  forall spec p goal,
    decoded_nat_check_proof_with_fuel
      spec
      (S (code_depth (SC.encode_proof_object p)))
      (S (code_depth (SC.encode_judgment goal)))
      (encode_proof_object_nat p)
      (encode_judgment_nat goal) =
    R.check_proof spec p goal.
Proof.
  intros spec p goal.
  unfold decoded_nat_check_proof_with_fuel.
  rewrite decode_encode_proof_object_nat.
  rewrite decode_encode_judgment_nat.
  reflexivity.
Qed.

Lemma decoded_nat_example_rule_checked :
  decoded_nat_check_proof_with_fuel
    R.example_rule_theory
    (S (code_depth (SC.encode_proof_object R.example_rule_proof)))
    (S (code_depth (SC.encode_judgment (R.rule_conclusion R.example_rule))))
    (encode_proof_object_nat R.example_rule_proof)
    (encode_judgment_nat (R.rule_conclusion R.example_rule)) = true.
Proof.
  rewrite decoded_nat_check_proof_agrees.
  exact R.example_rule_checked.
Qed.

End FormalSystemFactoryNatCodec.
