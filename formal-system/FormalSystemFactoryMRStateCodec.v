From Stdlib Require Import Lists.List.

Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryPrimitiveRecursion.
Require Import FormalSystemFactoryEPRPairing.

Import ListNotations.

Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.
Module EP := FormalSystemFactoryEPRPairing.FormalSystemFactoryEPRPairing.

Module FormalSystemFactoryMRStateCodec.

Record Reg4State : Type := {
  reg4_0 : nat;
  reg4_1 : nat;
  reg4_2 : nat;
  reg4_3 : nat
}.

Definition regs_of_reg4 (s : Reg4State) : list nat :=
  [reg4_0 s; reg4_1 s; reg4_2 s; reg4_3 s].

Definition reg4_of_regs (regs : list nat) : option Reg4State :=
  match regs with
  | [a; b; c; d] =>
      Some
        {|
          reg4_0 := a;
          reg4_1 := b;
          reg4_2 := c;
          reg4_3 := d
        |}
  | _ => None
  end.

Lemma reg4_of_regs_of_reg4 :
  forall s, reg4_of_regs (regs_of_reg4 s) = Some s.
Proof.
  intros [a b c d].
  reflexivity.
Qed.

Definition encode_reg4_state (s : Reg4State) : nat :=
  NC.pair_nat
    (reg4_0 s)
    (NC.pair_nat
       (reg4_1 s)
       (NC.pair_nat (reg4_2 s) (reg4_3 s))).

Definition decode_reg4_state (n : nat) : option Reg4State :=
  match NC.unpair_nat n with
  | Some (a, rest_a) =>
      match NC.unpair_nat rest_a with
      | Some (b, rest_b) =>
          match NC.unpair_nat rest_b with
          | Some (c, d) =>
              Some
                {|
                  reg4_0 := a;
                  reg4_1 := b;
                  reg4_2 := c;
                  reg4_3 := d
                |}
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Lemma decode_encode_reg4_state :
  forall s, decode_reg4_state (encode_reg4_state s) = Some s.
Proof.
  intros [a b c d].
  unfold decode_reg4_state, encode_reg4_state.
  simpl.
  rewrite NC.unpair_pair.
  rewrite NC.unpair_pair.
  rewrite NC.unpair_pair.
  reflexivity.
Qed.

Definition encode_reg4_regs (regs : list nat) : option nat :=
  match reg4_of_regs regs with
  | Some s => Some (encode_reg4_state s)
  | None => None
  end.

Definition decode_reg4_regs (n : nat) : option (list nat) :=
  match decode_reg4_state n with
  | Some s => Some (regs_of_reg4 s)
  | None => None
  end.

Lemma decode_encode_reg4_regs :
  forall s,
    decode_reg4_regs (encode_reg4_state s) = Some (regs_of_reg4 s).
Proof.
  intro s.
  unfold decode_reg4_regs.
  rewrite decode_encode_reg4_state.
  reflexivity.
Qed.

Definition reg4_project_0 (n : nat) : option nat :=
  match decode_reg4_state n with
  | Some s => Some (reg4_0 s)
  | None => None
  end.

Definition reg4_project_1 (n : nat) : option nat :=
  match decode_reg4_state n with
  | Some s => Some (reg4_1 s)
  | None => None
  end.

Definition reg4_project_2 (n : nat) : option nat :=
  match decode_reg4_state n with
  | Some s => Some (reg4_2 s)
  | None => None
  end.

Definition reg4_project_3 (n : nat) : option nat :=
  match decode_reg4_state n with
  | Some s => Some (reg4_3 s)
  | None => None
  end.

Lemma reg4_project_0_encode :
  forall s, reg4_project_0 (encode_reg4_state s) = Some (reg4_0 s).
Proof.
  intro s.
  unfold reg4_project_0.
  rewrite decode_encode_reg4_state.
  reflexivity.
Qed.

Lemma reg4_project_1_encode :
  forall s, reg4_project_1 (encode_reg4_state s) = Some (reg4_1 s).
Proof.
  intro s.
  unfold reg4_project_1.
  rewrite decode_encode_reg4_state.
  reflexivity.
Qed.

Lemma reg4_project_2_encode :
  forall s, reg4_project_2 (encode_reg4_state s) = Some (reg4_2 s).
Proof.
  intro s.
  unfold reg4_project_2.
  rewrite decode_encode_reg4_state.
  reflexivity.
Qed.

Lemma reg4_project_3_encode :
  forall s, reg4_project_3 (encode_reg4_state s) = Some (reg4_3 s).
Proof.
  intro s.
  unfold reg4_project_3.
  rewrite decode_encode_reg4_state.
  reflexivity.
Qed.

Definition EPRPackReg4
           (a b c d : EPR.EPRCode) : EPR.EPRCode :=
  EP.EPRPair a (EP.EPRPair b (EP.EPRPair c d)).

Lemma eval_EPRPackReg4 :
  forall a b c d env,
    EPR.eval_EPR (EPRPackReg4 a b c d) env =
    encode_reg4_state
      {|
        reg4_0 := EPR.eval_EPR a env;
        reg4_1 := EPR.eval_EPR b env;
        reg4_2 := EPR.eval_EPR c env;
        reg4_3 := EPR.eval_EPR d env
      |}.
Proof.
  intros a b c d env.
  unfold EPRPackReg4, encode_reg4_state.
  rewrite EP.eval_EPRPair.
  rewrite EP.eval_EPRPair.
  rewrite EP.eval_EPRPair.
  reflexivity.
Qed.

Definition EPRPackReg4Args : EPR.EPRCode :=
  EPRPackReg4
    (EPR.EPRArg 0) (EPR.EPRArg 1)
    (EPR.EPRArg 2) (EPR.EPRArg 3).

Lemma eval_EPRPackReg4Args :
  forall a b c d,
    EPR.eval_EPR EPRPackReg4Args [a; b; c; d] =
    encode_reg4_state
      {|
        reg4_0 := a;
        reg4_1 := b;
        reg4_2 := c;
        reg4_3 := d
      |}.
Proof.
  intros a b c d.
  unfold EPRPackReg4Args.
  rewrite eval_EPRPackReg4.
  reflexivity.
Qed.

Record EPRReg4PackCertificate : Type := {
  epr_reg4_pack_code : EPR.EPRCode;
  epr_reg4_pack_correct :
    forall a b c d,
      EPR.eval_EPR epr_reg4_pack_code [a; b; c; d] =
      encode_reg4_state
        {|
          reg4_0 := a;
          reg4_1 := b;
          reg4_2 := c;
          reg4_3 := d
        |}
}.

Definition epr_reg4_pack_certificate : EPRReg4PackCertificate :=
  {|
    epr_reg4_pack_code := EPRPackReg4Args;
    epr_reg4_pack_correct := eval_EPRPackReg4Args
  |}.

Record EPRReg4ProjectionKit : Type := {
  epr_reg4_project_0_code : EPR.EPRCode;
  epr_reg4_project_1_code : EPR.EPRCode;
  epr_reg4_project_2_code : EPR.EPRCode;
  epr_reg4_project_3_code : EPR.EPRCode;
  epr_reg4_project_0_correct :
    forall s,
      EPR.eval_EPR epr_reg4_project_0_code
        [encode_reg4_state s] = reg4_0 s;
  epr_reg4_project_1_correct :
    forall s,
      EPR.eval_EPR epr_reg4_project_1_code
        [encode_reg4_state s] = reg4_1 s;
  epr_reg4_project_2_correct :
    forall s,
      EPR.eval_EPR epr_reg4_project_2_code
        [encode_reg4_state s] = reg4_2 s;
  epr_reg4_project_3_correct :
    forall s,
      EPR.eval_EPR epr_reg4_project_3_code
        [encode_reg4_state s] = reg4_3 s
}.

Inductive EPRReg4ProjectionStatus : Type :=
| Reg4ProjectionCertified :
    EPRReg4ProjectionKit -> EPRReg4ProjectionStatus
| Reg4ProjectionNotYetCertified :
    EPRReg4ProjectionStatus.

Definition default_reg4_projection_status : EPRReg4ProjectionStatus :=
  Reg4ProjectionNotYetCertified.

End FormalSystemFactoryMRStateCodec.
