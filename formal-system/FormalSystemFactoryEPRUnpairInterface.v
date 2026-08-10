From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryPrimitiveRecursion.
Require Import FormalSystemFactoryEPRPairing.
Require Import FormalSystemFactoryEPRParityDiv2.

Import ListNotations.

Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.
Module EP := FormalSystemFactoryEPRPairing.FormalSystemFactoryEPRPairing.
Module PD := FormalSystemFactoryEPRParityDiv2.FormalSystemFactoryEPRParityDiv2.

Module FormalSystemFactoryEPRUnpairInterface.

Definition encode_option_pair (r : option (nat * nat)) : nat :=
  match r with
  | None => 0
  | Some (x, y) => S (NC.pair_nat x y)
  end.

Definition decode_option_pair (n : nat) : option (option (nat * nat)) :=
  match n with
  | 0 => Some None
  | S payload =>
      match NC.unpair_nat payload with
      | Some xy => Some (Some xy)
      | None => None
      end
  end.

Lemma decode_encode_option_pair :
  forall r,
    decode_option_pair (encode_option_pair r) = Some r.
Proof.
  intros [xy |].
  - destruct xy as [x y].
    simpl.
    rewrite NC.unpair_pair.
    reflexivity.
  - reflexivity.
Qed.

Definition unpair_result_fuel (fuel n : nat) : nat :=
  encode_option_pair (NC.unpair_nat_fuel fuel n).

Definition EPRUnpairCodeSpec (code : EPR.EPRCode) : Prop :=
  forall fuel n,
    EPR.eval_EPR code [fuel; n] = unpair_result_fuel fuel n.

Record EPRUnpairCertificate : Type := {
  epr_unpair_code : EPR.EPRCode;
  epr_unpair_correct : EPRUnpairCodeSpec epr_unpair_code
}.

Definition unpair_result (n : nat) : nat :=
  unpair_result_fuel (S n) n.

Definition EPRCanonicalUnpairCodeSpec (code : EPR.EPRCode) : Prop :=
  forall n,
    EPR.eval_EPR code [n] = unpair_result n.

Record EPRCanonicalUnpairCertificate : Type := {
  epr_canonical_unpair_code : EPR.EPRCode;
  epr_canonical_unpair_correct :
    EPRCanonicalUnpairCodeSpec epr_canonical_unpair_code
}.

Lemma unpair_result_fuel_pair :
  forall x y fuel,
    x < fuel ->
    unpair_result_fuel fuel (NC.pair_nat x y) =
    S (NC.pair_nat x y).
Proof.
  intros x y fuel Hfuel.
  unfold unpair_result_fuel, encode_option_pair.
  rewrite NC.unpair_pair_fuel by exact Hfuel.
  reflexivity.
Qed.

Lemma unpair_result_pair :
  forall x y,
    unpair_result (NC.pair_nat x y) =
    S (NC.pair_nat x y).
Proof.
  intros x y.
  unfold unpair_result.
  apply unpair_result_fuel_pair.
  pose proof (NC.pair_nat_ge_left x y).
  lia.
Qed.

Lemma certified_unpair_code_on_pair :
  forall cert x y fuel,
    x < fuel ->
    EPR.eval_EPR (epr_unpair_code cert) [fuel; NC.pair_nat x y] =
    S (NC.pair_nat x y).
Proof.
  intros cert x y fuel Hfuel.
  rewrite epr_unpair_correct.
  apply unpair_result_fuel_pair.
  exact Hfuel.
Qed.

Lemma certified_canonical_unpair_code_on_pair :
  forall cert x y,
    EPR.eval_EPR
      (epr_canonical_unpair_code cert)
      [NC.pair_nat x y] =
    S (NC.pair_nat x y).
Proof.
  intros cert x y.
  rewrite epr_canonical_unpair_correct.
  apply unpair_result_pair.
Qed.

Record EPRStateProjectionKit : Type := {
  epr_left_projection : EPR.EPRCode;
  epr_right_projection : EPR.EPRCode;
  epr_left_projection_correct :
    forall x y,
      EPR.eval_EPR epr_left_projection [NC.pair_nat x y] = x;
  epr_right_projection_correct :
    forall x y,
      EPR.eval_EPR epr_right_projection [NC.pair_nat x y] = y
}.

Definition state_projection_kit_suffices_for_unpair_state : Prop :=
  inhabited EPRStateProjectionKit.

End FormalSystemFactoryEPRUnpairInterface.
