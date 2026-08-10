From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryPrimitiveRecursion.
Require Import FormalSystemFactoryMRCode.
Require Import FormalSystemFactoryMRExprEPRCompiler.

Import ListNotations.

Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.
Module MRC := FormalSystemFactoryMRCode.FormalSystemFactoryMRCode.
Module EX := FormalSystemFactoryMRExprEPRCompiler.FormalSystemFactoryMRExprEPRCompiler.

Module FormalSystemFactoryMRProgramEPRFragments.

Record MRProgramInputsBounded
       (input_count : nat) (program : MRC.MRProgram) : Prop := {
  mr_program_init_inputs_bounded :
    EX.mr_exprs_inputs_bounded input_count
      (MRC.mr_init_regs program);
  mr_program_step_inputs_bounded :
    EX.mr_exprs_inputs_bounded input_count
      (MRC.mr_step_regs program);
  mr_program_output_inputs_bounded :
    EX.mr_expr_inputs_bounded input_count
      (MRC.mr_output_expr program)
}.

Definition compile_MRProgram_init_to_EPR
           (input_count : nat) (program : MRC.MRProgram)
  : list EPR.EPRCode :=
  EX.compile_MRExprs_to_EPR input_count
    (MRC.mr_init_regs program).

Definition compile_MRProgram_step_to_EPR
           (input_count : nat) (program : MRC.MRProgram)
  : list EPR.EPRCode :=
  EX.compile_MRExprs_to_EPR input_count
    (MRC.mr_step_regs program).

Definition compile_MRProgram_output_to_EPR
           (input_count : nat) (program : MRC.MRProgram)
  : EPR.EPRCode :=
  EX.compile_MRExpr_to_EPR input_count
    (MRC.mr_output_expr program).

Theorem compile_MRProgram_init_to_EPR_correct :
  forall input_count program inputs,
    length inputs = input_count ->
    MRProgramInputsBounded input_count program ->
    EX.eval_EPR_codes
      (compile_MRProgram_init_to_EPR input_count program)
      (inputs ++ []) =
    MRC.eval_MRExprs inputs [] (MRC.mr_init_regs program).
Proof.
  intros input_count program inputs Hlen Hbounded.
  unfold compile_MRProgram_init_to_EPR.
  apply EX.compile_MRExprs_to_EPR_correct.
  - exact Hlen.
  - exact (mr_program_init_inputs_bounded input_count program Hbounded).
Qed.

Theorem compile_MRProgram_step_to_EPR_correct :
  forall input_count program inputs regs,
    length inputs = input_count ->
    MRProgramInputsBounded input_count program ->
    EX.eval_EPR_codes
      (compile_MRProgram_step_to_EPR input_count program)
      (inputs ++ regs) =
    MRC.eval_MRExprs inputs regs (MRC.mr_step_regs program).
Proof.
  intros input_count program inputs regs Hlen Hbounded.
  unfold compile_MRProgram_step_to_EPR.
  apply EX.compile_MRExprs_to_EPR_correct.
  - exact Hlen.
  - exact (mr_program_step_inputs_bounded input_count program Hbounded).
Qed.

Theorem compile_MRProgram_output_to_EPR_correct :
  forall input_count program inputs regs,
    length inputs = input_count ->
    MRProgramInputsBounded input_count program ->
    EPR.eval_EPR
      (compile_MRProgram_output_to_EPR input_count program)
      (inputs ++ regs) =
    MRC.eval_MRExpr inputs regs (MRC.mr_output_expr program).
Proof.
  intros input_count program inputs regs Hlen Hbounded.
  unfold compile_MRProgram_output_to_EPR.
  apply EX.compile_MRExpr_to_EPR_correct.
  - exact Hlen.
  - exact (mr_program_output_inputs_bounded input_count program Hbounded).
Qed.

Record MRProgramEPRFragmentCertificate
       (input_count : nat) (program : MRC.MRProgram) : Type := {
  mr_program_fragment_bounded :
    MRProgramInputsBounded input_count program;
  compiled_mr_program_init_codes : list EPR.EPRCode;
  compiled_mr_program_step_codes : list EPR.EPRCode;
  compiled_mr_program_output_code : EPR.EPRCode;
  compiled_mr_program_init_correct :
    forall inputs,
      length inputs = input_count ->
      EX.eval_EPR_codes compiled_mr_program_init_codes
        (inputs ++ []) =
      MRC.eval_MRExprs inputs [] (MRC.mr_init_regs program);
  compiled_mr_program_step_correct :
    forall inputs regs,
      length inputs = input_count ->
      EX.eval_EPR_codes compiled_mr_program_step_codes
        (inputs ++ regs) =
      MRC.eval_MRExprs inputs regs (MRC.mr_step_regs program);
  compiled_mr_program_output_correct :
    forall inputs regs,
      length inputs = input_count ->
      EPR.eval_EPR compiled_mr_program_output_code
        (inputs ++ regs) =
      MRC.eval_MRExpr inputs regs (MRC.mr_output_expr program)
}.

Definition compile_bounded_mr_program_fragments
           (input_count : nat)
           (program : MRC.MRProgram)
           (bounded : MRProgramInputsBounded input_count program)
  : MRProgramEPRFragmentCertificate input_count program :=
  {|
    mr_program_fragment_bounded := bounded;
    compiled_mr_program_init_codes :=
      compile_MRProgram_init_to_EPR input_count program;
    compiled_mr_program_step_codes :=
      compile_MRProgram_step_to_EPR input_count program;
    compiled_mr_program_output_code :=
      compile_MRProgram_output_to_EPR input_count program;
    compiled_mr_program_init_correct :=
      fun inputs Hlen =>
        compile_MRProgram_init_to_EPR_correct
          input_count program inputs Hlen bounded;
    compiled_mr_program_step_correct :=
      fun inputs regs Hlen =>
        compile_MRProgram_step_to_EPR_correct
          input_count program inputs regs Hlen bounded;
    compiled_mr_program_output_correct :=
      fun inputs regs Hlen =>
        compile_MRProgram_output_to_EPR_correct
          input_count program inputs regs Hlen bounded
  |}.

Lemma unpair_init_regs_inputs_bounded :
  EX.mr_exprs_inputs_bounded 1 MRC.unpair_init_regs.
Proof.
  unfold MRC.unpair_init_regs, MRC.expr_zero, MRC.input_current.
  simpl.
  repeat split; lia.
Qed.

Lemma unpair_step_regs_inputs_bounded :
  EX.mr_exprs_inputs_bounded 1 MRC.unpair_step_regs.
Proof.
  unfold MRC.unpair_step_regs, MRC.reg_done, MRC.reg_left,
         MRC.reg_current, MRC.reg_right, MRC.expr_zero, MRC.expr_one.
  simpl.
  repeat split.
Qed.

Lemma unpair_program_inputs_bounded :
  MRProgramInputsBounded 1 MRC.mr_unpair_program.
Proof.
  constructor; cbn.
  - exact unpair_init_regs_inputs_bounded.
  - exact unpair_step_regs_inputs_bounded.
  - exact EX.unpair_output_expr_inputs_bounded.
Qed.

Definition compiled_unpair_program_fragments
  : MRProgramEPRFragmentCertificate 1 MRC.mr_unpair_program :=
  compile_bounded_mr_program_fragments
    1 MRC.mr_unpair_program unpair_program_inputs_bounded.

Theorem compiled_unpair_init_regs_correct :
  forall current,
    EX.eval_EPR_codes
      (compiled_mr_program_init_codes
         1 MRC.mr_unpair_program compiled_unpair_program_fragments)
      ([current] ++ []) =
    MRC.eval_MRExprs
      [current] [] (MRC.mr_init_regs MRC.mr_unpair_program).
Proof.
  intro current.
  apply compiled_mr_program_init_correct.
  reflexivity.
Qed.

Theorem compiled_unpair_step_regs_correct :
  forall current regs,
    EX.eval_EPR_codes
      (compiled_mr_program_step_codes
         1 MRC.mr_unpair_program compiled_unpair_program_fragments)
      ([current] ++ regs) =
    MRC.eval_MRExprs
      [current] regs (MRC.mr_step_regs MRC.mr_unpair_program).
Proof.
  intros current regs.
  apply compiled_mr_program_step_correct.
  reflexivity.
Qed.

Theorem compiled_unpair_output_expr_correct :
  forall current regs,
    EPR.eval_EPR
      (compiled_mr_program_output_code
         1 MRC.mr_unpair_program compiled_unpair_program_fragments)
      ([current] ++ regs) =
    MRC.eval_MRExpr
      [current] regs (MRC.mr_output_expr MRC.mr_unpair_program).
Proof.
  intros current regs.
  apply compiled_mr_program_output_correct.
  reflexivity.
Qed.

End FormalSystemFactoryMRProgramEPRFragments.
