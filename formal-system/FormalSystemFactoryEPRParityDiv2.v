From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryPrimitiveRecursion.

Import ListNotations.

Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.

Module FormalSystemFactoryEPRParityDiv2.

Definition EPREven (c : EPR.EPRCode) : EPR.EPRCode :=
  EPR.EPRRec c (EPR.EPRConst 1) (EPR.EPRNot (EPR.EPRArg 0)).

Definition toggle_nat (n : nat) : nat :=
  if negb (negb (Nat.eqb n 0)) then 1 else 0.

Fixpoint even_rec_loop (fuel acc : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' => even_rec_loop fuel' (toggle_nat acc)
  end.

Lemma even_rec_loop_correct_pair :
  forall n,
    even_rec_loop n 1 = (if Nat.even n then 1 else 0) /\
    even_rec_loop n 0 = (if Nat.even n then 0 else 1).
Proof.
  induction n as [|n IH].
  - split; reflexivity.
  - simpl even_rec_loop.
    destruct IH as [IH1 IH0].
    unfold toggle_nat.
    rewrite Nat.even_succ.
    rewrite <- Nat.negb_even.
    destruct (Nat.even n); split; assumption.
Qed.

Lemma even_rec_loop_one_correct :
  forall n, even_rec_loop n 1 = if Nat.even n then 1 else 0.
Proof.
  intro n.
  exact (proj1 (even_rec_loop_correct_pair n)).
Qed.

Lemma eval_EPREven :
  forall c env,
    EPR.eval_EPR (EPREven c) env =
    if Nat.even (EPR.eval_EPR c env) then 1 else 0.
Proof.
  intros c env.
  unfold EPREven.
  simpl.
  change
    (even_rec_loop (EPR.eval_EPR c env) 1 =
     if Nat.even (EPR.eval_EPR c env) then 1 else 0).
  apply even_rec_loop_one_correct.
Qed.

Lemma eval_EPREven_bool :
  forall c env,
    EPR.eval_EPR_bool (EPREven c) env =
    Nat.even (EPR.eval_EPR c env).
Proof.
  intros c env.
  unfold EPR.eval_EPR_bool.
  rewrite eval_EPREven.
  destruct (Nat.even (EPR.eval_EPR c env)); reflexivity.
Qed.

Definition EPRDiv2 (c : EPR.EPRCode) : EPR.EPRCode :=
  EPR.EPRRec
    c
    (EPR.EPRConst 0)
    (EPR.EPRIf
       (EPREven (EPR.EPRArg 1))
       (EPR.EPRArg 0)
       (EPR.EPRSucc (EPR.EPRArg 0))).

Fixpoint div2_rec_loop (fuel acc : nat) : nat :=
  match fuel with
  | 0 => acc
  | S fuel' =>
      div2_rec_loop fuel'
        (if negb (Nat.eqb (even_rec_loop fuel' 1) 0)
         then acc
         else S acc)
  end.

Lemma div2_rec_loop_matches_div2 :
  forall fuel acc,
    div2_rec_loop fuel acc = acc + Nat.div2 fuel.
Proof.
  induction fuel as [|fuel IH]; intros acc.
  - simpl; lia.
  - simpl div2_rec_loop.
    rewrite even_rec_loop_one_correct.
    destruct (Nat.even fuel) eqn:Heven.
    + apply Nat.even_spec in Heven.
      pose proof (Nat.Even_div2 fuel Heven) as Hdiv2.
      rewrite IH.
      rewrite <- Hdiv2.
      reflexivity.
    + assert (Hodd_bool : Nat.odd fuel = true).
      {
        rewrite <- Nat.negb_even.
        rewrite Heven.
        reflexivity.
      }
      apply Nat.odd_spec in Hodd_bool.
      pose proof (Nat.Odd_div2 fuel Hodd_bool) as Hdiv2.
      rewrite IH.
      simpl.
      change
        (S (acc + Nat.div2 fuel) =
         acc + Nat.div2 (S fuel)).
      rewrite <- Hdiv2.
      lia.
Qed.

Lemma eval_EPRDiv2 :
  forall c env,
    EPR.eval_EPR (EPRDiv2 c) env =
    Nat.div2 (EPR.eval_EPR c env).
Proof.
  intros c env.
  unfold EPRDiv2.
  simpl.
  change
    (div2_rec_loop (EPR.eval_EPR c env) 0 =
     Nat.div2 (EPR.eval_EPR c env)).
  rewrite div2_rec_loop_matches_div2.
  lia.
Qed.

Definition EPREvenArg : EPR.EPRCode := EPREven (EPR.EPRArg 0).

Definition EPRDiv2Arg : EPR.EPRCode := EPRDiv2 (EPR.EPRArg 0).

Lemma eval_EPREvenArg :
  forall n,
    EPR.eval_EPR_bool EPREvenArg [n] = Nat.even n.
Proof.
  intro n.
  unfold EPREvenArg.
  rewrite eval_EPREven_bool.
  reflexivity.
Qed.

Lemma eval_EPRDiv2Arg :
  forall n,
    EPR.eval_EPR EPRDiv2Arg [n] = Nat.div2 n.
Proof.
  intro n.
  unfold EPRDiv2Arg.
  rewrite eval_EPRDiv2.
  reflexivity.
Qed.

End FormalSystemFactoryEPRParityDiv2.
