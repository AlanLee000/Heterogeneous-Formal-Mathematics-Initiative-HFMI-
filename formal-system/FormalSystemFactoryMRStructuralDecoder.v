From Stdlib Require Import Lists.List.

Require Import FormalSystemFactoryStructuralCodec.
Require Import FormalSystemFactoryRuleAPI.
Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryEPRUnpairInterface.
Require Import FormalSystemFactoryMRBackend.

Import ListNotations.

Module SC := FormalSystemFactoryStructuralCodec.FormalSystemFactoryStructuralCodec.
Module R := FormalSystemFactoryRuleAPI.FormalSystemFactoryRuleAPI.
Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module UI := FormalSystemFactoryEPRUnpairInterface.FormalSystemFactoryEPRUnpairInterface.
Module MRB := FormalSystemFactoryMRBackend.FormalSystemFactoryMRBackend.

Module FormalSystemFactoryMRStructuralDecoder.

Definition backend_unpair_nat
           (backend : MRB.MRDecoderBackend) (n : nat)
  : option (nat * nat) :=
  match
    UI.decode_option_pair
      (MRB.eval_MRCanonicalUnpair
         (MRB.mr_canonical_unpair_code
            (MRB.backend_canonical_unpair_certificate backend))
         n)
  with
  | Some r => r
  | None => None
  end.

Lemma backend_unpair_nat_correct :
  forall backend n,
    backend_unpair_nat backend n = NC.unpair_nat n.
Proof.
  intros backend n.
  unfold backend_unpair_nat.
  rewrite (MRB.mr_canonical_unpair_correct
             (MRB.backend_canonical_unpair_certificate backend) n).
  unfold UI.unpair_result, UI.unpair_result_fuel, NC.unpair_nat.
  rewrite UI.decode_encode_option_pair.
  reflexivity.
Qed.

Fixpoint backend_decode_code_nat_fuel
         (backend : MRB.MRDecoderBackend)
         (fuel n : nat) : option SC.code :=
  match fuel, n with
  | 0, _ => None
  | S fuel', 0 => None
  | S fuel', S payload =>
      match backend_unpair_nat backend payload with
      | Some (0, atom) => Some (SC.CAtom atom)
      | Some (S tag, child_payload) =>
          match backend_decode_code_list_nat_fuel
                  backend fuel' child_payload with
          | Some children => Some (SC.CNode tag children)
          | None => None
          end
      | None => None
      end
  end
with backend_decode_code_list_nat_fuel
       (backend : MRB.MRDecoderBackend)
       (fuel n : nat) : option (list SC.code) :=
  match fuel, n with
  | 0, _ => None
  | S fuel', 0 => Some []
  | S fuel', S payload =>
      match backend_unpair_nat backend payload with
      | Some (head_payload, tail_payload) =>
          match backend_decode_code_nat_fuel
                  backend fuel' head_payload,
                backend_decode_code_list_nat_fuel
                  backend fuel' tail_payload with
          | Some head, Some tail => Some (head :: tail)
          | _, _ => None
          end
      | None => None
      end
  end.

Lemma backend_decode_nat_fuel_correct :
  forall fuel,
    (forall backend n,
        backend_decode_code_nat_fuel backend fuel n =
        NC.decode_code_nat_fuel fuel n) /\
    (forall backend n,
        backend_decode_code_list_nat_fuel backend fuel n =
        NC.decode_code_list_nat_fuel fuel n).
Proof.
  induction fuel as [|fuel IH].
  - split; intros backend n; destruct n; reflexivity.
  - destruct IH as [IHcode IHlist].
    split.
    + intros backend n.
      destruct n as [|payload]; simpl.
      * reflexivity.
      * rewrite backend_unpair_nat_correct.
        destruct (NC.unpair_nat payload) as [[head tail] |].
        -- destruct head as [|tag].
           ++ reflexivity.
           ++ rewrite IHlist.
              reflexivity.
        -- reflexivity.
    + intros backend n.
      destruct n as [|payload]; simpl.
      * reflexivity.
      * rewrite backend_unpair_nat_correct.
        destruct (NC.unpair_nat payload) as [[head tail] |].
        -- rewrite IHcode.
           rewrite IHlist.
           reflexivity.
        -- reflexivity.
Qed.

Theorem backend_decode_code_nat_fuel_correct :
  forall backend fuel n,
    backend_decode_code_nat_fuel backend fuel n =
    NC.decode_code_nat_fuel fuel n.
Proof.
  intros backend fuel n.
  exact (proj1 (backend_decode_nat_fuel_correct fuel) backend n).
Qed.

Theorem backend_decode_code_list_nat_fuel_correct :
  forall backend fuel n,
    backend_decode_code_list_nat_fuel backend fuel n =
    NC.decode_code_list_nat_fuel fuel n.
Proof.
  intros backend fuel n.
  exact (proj2 (backend_decode_nat_fuel_correct fuel) backend n).
Qed.

Theorem backend_decode_encode_code_nat_fuel :
  forall backend c,
    backend_decode_code_nat_fuel
      backend (S (NC.code_depth c)) (NC.encode_code_nat c) = Some c.
Proof.
  intros backend c.
  rewrite backend_decode_code_nat_fuel_correct.
  apply NC.decode_encode_code_nat_fuel.
Qed.

Theorem backend_decode_encode_code_list_nat_fuel :
  forall backend cs,
    backend_decode_code_list_nat_fuel
      backend (S (NC.code_list_depth cs))
      (NC.encode_code_list_nat cs) = Some cs.
Proof.
  intros backend cs.
  rewrite backend_decode_code_list_nat_fuel_correct.
  apply NC.decode_encode_code_list_nat_fuel.
Qed.

Definition backend_decode_proof_object_nat
           (backend : MRB.MRDecoderBackend)
           (fuel n : nat) : option R.proof_object :=
  match backend_decode_code_nat_fuel backend fuel n with
  | Some c => SC.decode_proof_object c
  | None => None
  end.

Definition backend_decode_judgment_nat
           (backend : MRB.MRDecoderBackend)
           (fuel n : nat) : option R.judgment :=
  match backend_decode_code_nat_fuel backend fuel n with
  | Some c => SC.decode_judgment c
  | None => None
  end.

Theorem backend_decode_proof_object_nat_correct :
  forall backend fuel n,
    backend_decode_proof_object_nat backend fuel n =
    NC.decode_proof_object_nat fuel n.
Proof.
  intros backend fuel n.
  unfold backend_decode_proof_object_nat, NC.decode_proof_object_nat.
  rewrite backend_decode_code_nat_fuel_correct.
  reflexivity.
Qed.

Theorem backend_decode_judgment_nat_correct :
  forall backend fuel n,
    backend_decode_judgment_nat backend fuel n =
    NC.decode_judgment_nat fuel n.
Proof.
  intros backend fuel n.
  unfold backend_decode_judgment_nat, NC.decode_judgment_nat.
  rewrite backend_decode_code_nat_fuel_correct.
  reflexivity.
Qed.

Theorem backend_decode_encode_proof_object_nat :
  forall backend p,
    backend_decode_proof_object_nat
      backend
      (S (NC.code_depth (SC.encode_proof_object p)))
      (NC.encode_proof_object_nat p) = Some p.
Proof.
  intros backend p.
  rewrite backend_decode_proof_object_nat_correct.
  apply NC.decode_encode_proof_object_nat.
Qed.

Theorem backend_decode_encode_judgment_nat :
  forall backend j,
    backend_decode_judgment_nat
      backend
      (S (NC.code_depth (SC.encode_judgment j)))
      (NC.encode_judgment_nat j) = Some j.
Proof.
  intros backend j.
  rewrite backend_decode_judgment_nat_correct.
  apply NC.decode_encode_judgment_nat.
Qed.

Definition backend_decoded_nat_check_proof_with_fuel
           (backend : MRB.MRDecoderBackend)
           (spec : R.TheorySpec)
           (proof_fuel goal_fuel proof_nat goal_nat : nat) : bool :=
  match backend_decode_proof_object_nat backend proof_fuel proof_nat,
        backend_decode_judgment_nat backend goal_fuel goal_nat with
  | Some p, Some goal => R.check_proof spec p goal
  | _, _ => false
  end.

Theorem backend_decoded_nat_check_proof_agrees_with_nat :
  forall backend spec proof_fuel goal_fuel proof_nat goal_nat,
    backend_decoded_nat_check_proof_with_fuel
      backend spec proof_fuel goal_fuel proof_nat goal_nat =
    NC.decoded_nat_check_proof_with_fuel
      spec proof_fuel goal_fuel proof_nat goal_nat.
Proof.
  intros backend spec proof_fuel goal_fuel proof_nat goal_nat.
  unfold backend_decoded_nat_check_proof_with_fuel,
         NC.decoded_nat_check_proof_with_fuel.
  rewrite backend_decode_proof_object_nat_correct.
  rewrite backend_decode_judgment_nat_correct.
  reflexivity.
Qed.

Theorem backend_decoded_nat_check_proof_agrees :
  forall backend spec p goal,
    backend_decoded_nat_check_proof_with_fuel
      backend
      spec
      (S (NC.code_depth (SC.encode_proof_object p)))
      (S (NC.code_depth (SC.encode_judgment goal)))
      (NC.encode_proof_object_nat p)
      (NC.encode_judgment_nat goal) =
    R.check_proof spec p goal.
Proof.
  intros backend spec p goal.
  rewrite backend_decoded_nat_check_proof_agrees_with_nat.
  apply NC.decoded_nat_check_proof_agrees.
Qed.

Theorem default_backend_decoded_nat_example_rule_checked :
  backend_decoded_nat_check_proof_with_fuel
    MRB.default_mr_decoder_backend
    R.example_rule_theory
    (S (NC.code_depth (SC.encode_proof_object R.example_rule_proof)))
    (S (NC.code_depth (SC.encode_judgment (R.rule_conclusion R.example_rule))))
    (NC.encode_proof_object_nat R.example_rule_proof)
    (NC.encode_judgment_nat (R.rule_conclusion R.example_rule)) = true.
Proof.
  rewrite backend_decoded_nat_check_proof_agrees.
  exact R.example_rule_checked.
Qed.

End FormalSystemFactoryMRStructuralDecoder.
