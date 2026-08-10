From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryPrimitiveRecursion.

Import ListNotations.

Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.

Module FormalSystemFactoryEPRPairing.

Definition double_code (c : EPR.EPRCode) : EPR.EPRCode :=
  EPR.EPRAdd c c.

Definition pair_step_code : EPR.EPRCode :=
  EPR.EPRSucc (double_code (EPR.EPRArg 0)).

Definition EPRPair (left right : EPR.EPRCode) : EPR.EPRCode :=
  EPR.EPRRec left (double_code right) pair_step_code.

Definition EPRPairArgs : EPR.EPRCode :=
  EPRPair (EPR.EPRArg 0) (EPR.EPRArg 1).

Definition pair_step_nat (acc : nat) : nat :=
  S (acc + acc).

Fixpoint pair_iter (fuel acc : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' => pair_iter fuel' (pair_step_nat acc)
  end.

Lemma pair_iter_step_commutes :
  forall fuel acc,
    pair_iter fuel (pair_step_nat acc) =
    pair_step_nat (pair_iter fuel acc).
Proof.
  induction fuel as [|fuel IH]; intros acc.
  - reflexivity.
  - simpl pair_iter.
    rewrite (IH (pair_step_nat acc)).
    reflexivity.
Qed.

Lemma pair_iter_matches_pair_nat :
  forall x y,
    pair_iter x (y + y) = NC.pair_nat x y.
Proof.
  induction x as [|x IH]; intros y; simpl.
  - lia.
  - rewrite pair_iter_step_commutes.
    rewrite IH.
    unfold pair_step_nat.
    lia.
Qed.

Lemma eval_EPRPair :
  forall left right env,
    EPR.eval_EPR (EPRPair left right) env =
    NC.pair_nat (EPR.eval_EPR left env) (EPR.eval_EPR right env).
Proof.
  intros left right env.
  unfold EPRPair, double_code, pair_step_code.
  simpl.
  change
    (pair_iter (EPR.eval_EPR left env)
       (EPR.eval_EPR right env + EPR.eval_EPR right env) =
     NC.pair_nat (EPR.eval_EPR left env) (EPR.eval_EPR right env)).
  apply pair_iter_matches_pair_nat.
Qed.

Lemma eval_EPRPairArgs :
  forall x y,
    EPR.eval_EPR EPRPairArgs [x; y] = NC.pair_nat x y.
Proof.
  intros x y.
  unfold EPRPairArgs.
  rewrite eval_EPRPair.
  reflexivity.
Qed.

Definition EPRCodeAtomPayload (atom : EPR.EPRCode) : EPR.EPRCode :=
  EPR.EPRSucc (EPRPair (EPR.EPRConst 0) atom).

Lemma eval_EPRCodeAtomPayload :
  forall atom env,
    EPR.eval_EPR (EPRCodeAtomPayload atom) env =
    S (NC.pair_nat 0 (EPR.eval_EPR atom env)).
Proof.
  intros atom env.
  unfold EPRCodeAtomPayload.
  change
    (S (EPR.eval_EPR (EPRPair (EPR.EPRConst 0) atom) env) =
     S (NC.pair_nat 0 (EPR.eval_EPR atom env))).
  rewrite eval_EPRPair.
  reflexivity.
Qed.

Definition EPRCodeNodePayload
           (tag children_payload : EPR.EPRCode) : EPR.EPRCode :=
  EPR.EPRSucc (EPRPair (EPR.EPRSucc tag) children_payload).

Lemma eval_EPRCodeNodePayload :
  forall tag children_payload env,
    EPR.eval_EPR (EPRCodeNodePayload tag children_payload) env =
    S (NC.pair_nat (S (EPR.eval_EPR tag env))
                   (EPR.eval_EPR children_payload env)).
Proof.
  intros tag children_payload env.
  unfold EPRCodeNodePayload.
  change
    (S (EPR.eval_EPR
          (EPRPair (EPR.EPRSucc tag) children_payload) env) =
     S (NC.pair_nat (S (EPR.eval_EPR tag env))
                    (EPR.eval_EPR children_payload env))).
  rewrite eval_EPRPair.
  reflexivity.
Qed.

Definition EPRCodeListNil : EPR.EPRCode :=
  EPR.EPRConst 0.

Definition EPRCodeListCons
           (head tail_payload : EPR.EPRCode) : EPR.EPRCode :=
  EPR.EPRSucc (EPRPair head tail_payload).

Lemma eval_EPRCodeListNil :
  forall env,
    EPR.eval_EPR EPRCodeListNil env = 0.
Proof.
  reflexivity.
Qed.

Lemma eval_EPRCodeListCons :
  forall head tail_payload env,
    EPR.eval_EPR (EPRCodeListCons head tail_payload) env =
    S (NC.pair_nat (EPR.eval_EPR head env)
                   (EPR.eval_EPR tail_payload env)).
Proof.
  intros head tail_payload env.
  unfold EPRCodeListCons.
  change
    (S (EPR.eval_EPR (EPRPair head tail_payload) env) =
     S (NC.pair_nat (EPR.eval_EPR head env)
                    (EPR.eval_EPR tail_payload env))).
  rewrite eval_EPRPair.
  reflexivity.
Qed.

Lemma eval_EPRPair_ge_left :
  forall left right env,
    EPR.eval_EPR left env <=
    EPR.eval_EPR (EPRPair left right) env.
Proof.
  intros left right env.
  rewrite eval_EPRPair.
  apply NC.pair_nat_ge_left.
Qed.

Lemma eval_EPRPair_ge_right :
  forall left right env,
    EPR.eval_EPR right env <=
    EPR.eval_EPR (EPRPair left right) env.
Proof.
  intros left right env.
  rewrite eval_EPRPair.
  apply NC.pair_nat_ge_right.
Qed.

End FormalSystemFactoryEPRPairing.
