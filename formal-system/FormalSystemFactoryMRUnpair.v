From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryEPRUnpairInterface.

Import ListNotations.

Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module UI := FormalSystemFactoryEPRUnpairInterface.FormalSystemFactoryEPRUnpairInterface.

Module FormalSystemFactoryMRUnpair.

Record UnpairState : Type := {
  st_done : nat;
  st_left : nat;
  st_current : nat;
  st_right : nat
}.

Definition state_is_done (s : UnpairState) : bool :=
  negb (Nat.eqb (st_done s) 0).

Definition done_state (left right current : nat) : UnpairState :=
  {|
    st_done := 1;
    st_left := left;
    st_current := current;
    st_right := right
  |}.

Definition active_state (left current : nat) : UnpairState :=
  {|
    st_done := 0;
    st_left := left;
    st_current := current;
    st_right := 0
  |}.

Definition unpair_state_step (s : UnpairState) : UnpairState :=
  if state_is_done s then s
  else if Nat.even (st_current s)
       then done_state (st_left s) (Nat.div2 (st_current s)) (st_current s)
       else active_state (S (st_left s)) (Nat.div2 (st_current s)).

Fixpoint run_unpair_state (fuel : nat) (s : UnpairState) : UnpairState :=
  match fuel with
  | 0 => s
  | S fuel' => run_unpair_state fuel' (unpair_state_step s)
  end.

Definition unpair_state_output (s : UnpairState) : nat :=
  if state_is_done s
  then S (NC.pair_nat (st_left s) (st_right s))
  else 0.

Definition shift_unpair_result
           (left_offset : nat)
           (r : option (nat * nat)) : option (nat * nat) :=
  match r with
  | None => None
  | Some (x, y) => Some (left_offset + x, y)
  end.

Lemma run_done_state_stable :
  forall fuel left right current,
    run_unpair_state fuel (done_state left right current) =
    done_state left right current.
Proof.
  induction fuel as [|fuel IH]; intros left right current.
  - reflexivity.
  - simpl.
    unfold unpair_state_step, state_is_done, done_state.
    simpl.
    apply IH.
Qed.

Lemma output_done_state :
  forall left right current,
    unpair_state_output (done_state left right current) =
    S (NC.pair_nat left right).
Proof.
  intros left right current.
  unfold unpair_state_output, state_is_done, done_state.
  simpl.
  reflexivity.
Qed.

Lemma output_active_state :
  forall left current,
    unpair_state_output (active_state left current) = 0.
Proof.
  intros left current.
  unfold unpair_state_output, state_is_done, active_state.
  simpl.
  reflexivity.
Qed.

Lemma encode_shift_succ :
  forall left x y,
    UI.encode_option_pair (shift_unpair_result (S left) (Some (x, y))) =
    UI.encode_option_pair (shift_unpair_result left (Some (S x, y))).
Proof.
  intros left x y.
  unfold UI.encode_option_pair, shift_unpair_result.
  replace (S left + x) with (left + S x) by lia.
  reflexivity.
Qed.

Lemma run_unpair_state_active_correct :
  forall fuel left current,
    unpair_state_output
      (run_unpair_state fuel (active_state left current)) =
    UI.encode_option_pair
      (shift_unpair_result left (NC.unpair_nat_fuel fuel current)).
Proof.
  induction fuel as [|fuel IH]; intros left current.
  - simpl.
    rewrite output_active_state.
    reflexivity.
  - simpl run_unpair_state.
    unfold unpair_state_step, state_is_done, active_state.
    simpl.
    destruct (Nat.even current) eqn:Heven.
    + rewrite run_done_state_stable.
      rewrite output_done_state.
      unfold UI.encode_option_pair, shift_unpair_result.
      simpl.
      replace (left + 0) with left by lia.
      reflexivity.
    + specialize (IH (S left) (Nat.div2 current)).
      change
        (unpair_state_output
           (run_unpair_state fuel
              (active_state (S left) (Nat.div2 current))) =
         UI.encode_option_pair
           (shift_unpair_result left
              match NC.unpair_nat_fuel fuel (Nat.div2 current) with
              | Some (x, y) => Some (S x, y)
              | None => None
              end)).
      rewrite IH.
      simpl.
      destruct (NC.unpair_nat_fuel fuel (Nat.div2 current)) as [[x y] |].
      * apply encode_shift_succ.
      * reflexivity.
Qed.

Definition mr_unpair_result_fuel (fuel current : nat) : nat :=
  unpair_state_output
    (run_unpair_state fuel (active_state 0 current)).

Theorem mr_unpair_result_fuel_correct :
  forall fuel current,
    mr_unpair_result_fuel fuel current =
    UI.unpair_result_fuel fuel current.
Proof.
  intros fuel current.
  unfold mr_unpair_result_fuel, UI.unpair_result_fuel.
  rewrite run_unpair_state_active_correct.
  unfold shift_unpair_result.
  destruct (NC.unpair_nat_fuel fuel current) as [[x y] |]; reflexivity.
Qed.

Definition mr_unpair_result (current : nat) : nat :=
  mr_unpair_result_fuel (S current) current.

Theorem mr_unpair_result_correct :
  forall current,
    mr_unpair_result current = UI.unpair_result current.
Proof.
  intro current.
  unfold mr_unpair_result, UI.unpair_result.
  apply mr_unpair_result_fuel_correct.
Qed.

Theorem mr_unpair_result_pair :
  forall x y,
    mr_unpair_result (NC.pair_nat x y) =
    S (NC.pair_nat x y).
Proof.
  intros x y.
  rewrite mr_unpair_result_correct.
  apply UI.unpair_result_pair.
Qed.

End FormalSystemFactoryMRUnpair.
