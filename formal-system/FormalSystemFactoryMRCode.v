From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.

Require Import FormalSystemFactoryKernel.
Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryMRUnpair.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.
Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module MRU := FormalSystemFactoryMRUnpair.FormalSystemFactoryMRUnpair.

Module FormalSystemFactoryMRCode.

Inductive MRExpr : Type :=
| MRConst : nat -> MRExpr
| MRInput : nat -> MRExpr
| MRReg : nat -> MRExpr
| MRSucc : MRExpr -> MRExpr
| MRPair : MRExpr -> MRExpr -> MRExpr
| MREven : MRExpr -> MRExpr
| MRDiv2 : MRExpr -> MRExpr
| MRNot : MRExpr -> MRExpr
| MRIf : MRExpr -> MRExpr -> MRExpr -> MRExpr.

Fixpoint eval_MRExpr
         (inputs regs : list nat)
         (e : MRExpr) : nat :=
  match e with
  | MRConst n => n
  | MRInput i => K.nth_default inputs i
  | MRReg i => K.nth_default regs i
  | MRSucc a => S (eval_MRExpr inputs regs a)
  | MRPair a b =>
      NC.pair_nat (eval_MRExpr inputs regs a)
                  (eval_MRExpr inputs regs b)
  | MREven a =>
      if Nat.even (eval_MRExpr inputs regs a) then 1 else 0
  | MRDiv2 a => Nat.div2 (eval_MRExpr inputs regs a)
  | MRNot a =>
      if negb (K.nat_to_bool (eval_MRExpr inputs regs a)) then 1 else 0
  | MRIf guard then_expr else_expr =>
      if K.nat_to_bool (eval_MRExpr inputs regs guard)
      then eval_MRExpr inputs regs then_expr
      else eval_MRExpr inputs regs else_expr
  end.

Fixpoint eval_MRExprs
         (inputs regs : list nat)
         (es : list MRExpr) : list nat :=
  match es with
  | [] => []
  | e :: rest => eval_MRExpr inputs regs e :: eval_MRExprs inputs regs rest
  end.

Record MRProgram : Type := {
  mr_init_regs : list MRExpr;
  mr_step_regs : list MRExpr;
  mr_output_expr : MRExpr
}.

Fixpoint run_MRProgram_regs
         (p : MRProgram) (fuel : nat)
         (inputs regs : list nat) : list nat :=
  match fuel with
  | 0 => regs
  | S fuel' =>
      run_MRProgram_regs
        p fuel' inputs
        (eval_MRExprs inputs regs (mr_step_regs p))
  end.

Definition eval_MRProgram
           (p : MRProgram) (fuel : nat) (inputs : list nat) : nat :=
  let init_regs := eval_MRExprs inputs [] (mr_init_regs p) in
  let final_regs := run_MRProgram_regs p fuel inputs init_regs in
  eval_MRExpr inputs final_regs (mr_output_expr p).

Definition reg_done : MRExpr := MRReg 0.
Definition reg_left : MRExpr := MRReg 1.
Definition reg_current : MRExpr := MRReg 2.
Definition reg_right : MRExpr := MRReg 3.

Definition expr_zero : MRExpr := MRConst 0.
Definition expr_one : MRExpr := MRConst 1.
Definition input_current : MRExpr := MRInput 0.

Definition unpair_init_regs : list MRExpr :=
  [expr_zero; expr_zero; input_current; expr_zero].

Definition unpair_step_regs : list MRExpr :=
  let done := reg_done in
  let left := reg_left in
  let current := reg_current in
  let right := reg_right in
  let even_current := MREven current in
  [ MRIf done done (MRIf even_current expr_one expr_zero);
    MRIf done left (MRIf even_current left (MRSucc left));
    MRIf done current (MRIf even_current current (MRDiv2 current));
    MRIf done right (MRIf even_current (MRDiv2 current) expr_zero)
  ].

Definition unpair_output_expr : MRExpr :=
  MRIf reg_done
       (MRSucc (MRPair reg_left reg_right))
       expr_zero.

Definition mr_unpair_program : MRProgram :=
  {|
    mr_init_regs := unpair_init_regs;
    mr_step_regs := unpair_step_regs;
    mr_output_expr := unpair_output_expr
  |}.

Definition regs_of_state (s : MRU.UnpairState) : list nat :=
  [MRU.st_done s; MRU.st_left s; MRU.st_current s; MRU.st_right s].

Lemma eval_unpair_init_regs :
  forall current,
    eval_MRExprs [current] [] unpair_init_regs =
    regs_of_state (MRU.active_state 0 current).
Proof.
  intro current.
  reflexivity.
Qed.

Lemma eval_unpair_output_expr :
  forall inputs s,
    eval_MRExpr inputs (regs_of_state s) unpair_output_expr =
    MRU.unpair_state_output s.
Proof.
  intros inputs [done left current right].
  unfold unpair_output_expr, regs_of_state, MRU.unpair_state_output,
         MRU.state_is_done, reg_done, reg_left, reg_right, expr_zero.
  simpl.
  destruct done as [|done']; reflexivity.
Qed.

Lemma eval_unpair_step_regs :
  forall inputs s,
    eval_MRExprs inputs (regs_of_state s) unpair_step_regs =
    regs_of_state (MRU.unpair_state_step s).
Proof.
  intros inputs [done left current right].
  unfold unpair_step_regs, regs_of_state, MRU.unpair_state_step,
         MRU.state_is_done, MRU.done_state, MRU.active_state,
         reg_done, reg_left, reg_current, reg_right,
         expr_zero, expr_one.
  simpl.
  destruct done as [|done'].
  - destruct (Nat.even current); reflexivity.
  - reflexivity.
Qed.

Lemma run_mr_unpair_program_regs_state_correct :
  forall fuel inputs s,
    run_MRProgram_regs
      mr_unpair_program fuel inputs (regs_of_state s) =
    regs_of_state (MRU.run_unpair_state fuel s).
Proof.
  induction fuel as [|fuel IH]; intros inputs s.
  - reflexivity.
  - change
      (run_MRProgram_regs
         mr_unpair_program fuel inputs
         (eval_MRExprs inputs (regs_of_state s)
            (mr_step_regs mr_unpair_program)) =
       regs_of_state
         (MRU.run_unpair_state fuel (MRU.unpair_state_step s))).
    change (mr_step_regs mr_unpair_program) with unpair_step_regs.
    rewrite eval_unpair_step_regs.
    apply IH.
Qed.

Lemma run_mr_unpair_program_regs_correct :
  forall fuel current,
    run_MRProgram_regs
      mr_unpair_program fuel [current]
      (eval_MRExprs [current] [] (mr_init_regs mr_unpair_program)) =
    regs_of_state
      (MRU.run_unpair_state fuel (MRU.active_state 0 current)).
Proof.
  intros fuel current.
  rewrite eval_unpair_init_regs.
  apply run_mr_unpair_program_regs_state_correct.
Qed.

Theorem eval_mr_unpair_program_correct :
  forall fuel current,
    eval_MRProgram mr_unpair_program fuel [current] =
    MRU.mr_unpair_result_fuel fuel current.
Proof.
  intros fuel current.
  unfold eval_MRProgram, MRU.mr_unpair_result_fuel.
  rewrite run_mr_unpair_program_regs_correct.
  apply eval_unpair_output_expr.
Qed.

Theorem eval_mr_unpair_program_matches_unpair :
  forall fuel current,
    eval_MRProgram mr_unpair_program fuel [current] =
    FormalSystemFactoryEPRUnpairInterface.FormalSystemFactoryEPRUnpairInterface.unpair_result_fuel
      fuel current.
Proof.
  intros fuel current.
  rewrite eval_mr_unpair_program_correct.
  apply MRU.mr_unpair_result_fuel_correct.
Qed.

End FormalSystemFactoryMRCode.
