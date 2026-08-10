From Stdlib Require Import Lists.List.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.

Require Import FormalSystemFactoryKernel.
Require Import FormalSystemFactoryPrimitiveRecursion.
Require Import FormalSystemFactoryEPRPairing.
Require Import FormalSystemFactoryEPRParityDiv2.
Require Import FormalSystemFactoryMRCode.

Import ListNotations.

Module K := FormalSystemFactoryKernel.FormalSystemFactoryKernel.
Module EPR := FormalSystemFactoryPrimitiveRecursion.FormalSystemFactoryPrimitiveRecursion.
Module EP := FormalSystemFactoryEPRPairing.FormalSystemFactoryEPRPairing.
Module PD := FormalSystemFactoryEPRParityDiv2.FormalSystemFactoryEPRParityDiv2.
Module MRC := FormalSystemFactoryMRCode.FormalSystemFactoryMRCode.

Module FormalSystemFactoryMRExprEPRCompiler.

Fixpoint mr_expr_inputs_bounded
         (input_count : nat) (e : MRC.MRExpr) : Prop :=
  match e with
  | MRC.MRConst _ => True
  | MRC.MRInput i => i < input_count
  | MRC.MRReg _ => True
  | MRC.MRSucc a => mr_expr_inputs_bounded input_count a
  | MRC.MRPair a b =>
      mr_expr_inputs_bounded input_count a /\
      mr_expr_inputs_bounded input_count b
  | MRC.MREven a => mr_expr_inputs_bounded input_count a
  | MRC.MRDiv2 a => mr_expr_inputs_bounded input_count a
  | MRC.MRNot a => mr_expr_inputs_bounded input_count a
  | MRC.MRIf guard then_expr else_expr =>
      mr_expr_inputs_bounded input_count guard /\
      mr_expr_inputs_bounded input_count then_expr /\
      mr_expr_inputs_bounded input_count else_expr
  end.

Fixpoint compile_MRExpr_to_EPR
         (input_count : nat) (e : MRC.MRExpr) : EPR.EPRCode :=
  match e with
  | MRC.MRConst n => EPR.EPRConst n
  | MRC.MRInput i => EPR.EPRArg i
  | MRC.MRReg i => EPR.EPRArg (input_count + i)
  | MRC.MRSucc a => EPR.EPRSucc (compile_MRExpr_to_EPR input_count a)
  | MRC.MRPair a b =>
      EP.EPRPair
        (compile_MRExpr_to_EPR input_count a)
        (compile_MRExpr_to_EPR input_count b)
  | MRC.MREven a => PD.EPREven (compile_MRExpr_to_EPR input_count a)
  | MRC.MRDiv2 a => PD.EPRDiv2 (compile_MRExpr_to_EPR input_count a)
  | MRC.MRNot a => EPR.EPRNot (compile_MRExpr_to_EPR input_count a)
  | MRC.MRIf guard then_expr else_expr =>
      EPR.EPRIf
        (compile_MRExpr_to_EPR input_count guard)
        (compile_MRExpr_to_EPR input_count then_expr)
        (compile_MRExpr_to_EPR input_count else_expr)
  end.

Lemma nth_default_app_left :
  forall xs ys i,
    i < length xs ->
    K.nth_default (xs ++ ys) i = K.nth_default xs i.
Proof.
  induction xs as [|x xs IH]; intros ys i Hlt.
  - simpl in Hlt; lia.
  - destruct i as [|i].
    + reflexivity.
    + simpl in *.
      apply IH.
      lia.
Qed.

Lemma nth_default_app_right :
  forall xs ys i,
    K.nth_default (xs ++ ys) (length xs + i) =
    K.nth_default ys i.
Proof.
  induction xs as [|x xs IH]; intros ys i.
  - reflexivity.
  - simpl.
    apply IH.
Qed.

Theorem compile_MRExpr_to_EPR_correct :
  forall input_count e inputs regs,
    length inputs = input_count ->
    mr_expr_inputs_bounded input_count e ->
    EPR.eval_EPR
      (compile_MRExpr_to_EPR input_count e)
      (inputs ++ regs) =
    MRC.eval_MRExpr inputs regs e.
Proof.
  induction e; intros inputs regs Hlen Hbounded;
    cbn [compile_MRExpr_to_EPR MRC.eval_MRExpr
         mr_expr_inputs_bounded] in *.
  - reflexivity.
  - change (K.nth_default (inputs ++ regs) n = K.nth_default inputs n).
    rewrite nth_default_app_left.
    + reflexivity.
    + lia.
  - change
      (K.nth_default (inputs ++ regs) (input_count + n) =
       K.nth_default regs n).
    rewrite <- Hlen.
    apply nth_default_app_right.
  - change
      (S (EPR.eval_EPR
            (compile_MRExpr_to_EPR input_count e)
            (inputs ++ regs)) =
       S (MRC.eval_MRExpr inputs regs e)).
    rewrite (IHe inputs regs Hlen Hbounded).
    reflexivity.
  - destruct Hbounded as [Hleft Hright].
    rewrite EP.eval_EPRPair.
    rewrite (IHe1 inputs regs Hlen Hleft).
    rewrite (IHe2 inputs regs Hlen Hright).
    reflexivity.
  - rewrite PD.eval_EPREven.
    rewrite (IHe inputs regs Hlen Hbounded).
    reflexivity.
  - rewrite PD.eval_EPRDiv2.
    rewrite (IHe inputs regs Hlen Hbounded).
    reflexivity.
  - change
      (K.bool_to_nat
         (negb
            (K.nat_to_bool
               (EPR.eval_EPR
                  (compile_MRExpr_to_EPR input_count e)
                  (inputs ++ regs)))) =
       K.bool_to_nat
         (negb (K.nat_to_bool (MRC.eval_MRExpr inputs regs e)))).
    rewrite (IHe inputs regs Hlen Hbounded).
    reflexivity.
  - destruct Hbounded as [Hguard [Hthen Helse]].
    change
      ((if K.nat_to_bool
             (EPR.eval_EPR
                (compile_MRExpr_to_EPR input_count e1)
                (inputs ++ regs))
        then
          EPR.eval_EPR
            (compile_MRExpr_to_EPR input_count e2)
            (inputs ++ regs)
        else
          EPR.eval_EPR
            (compile_MRExpr_to_EPR input_count e3)
            (inputs ++ regs)) =
       (if K.nat_to_bool (MRC.eval_MRExpr inputs regs e1)
        then MRC.eval_MRExpr inputs regs e2
        else MRC.eval_MRExpr inputs regs e3)).
    rewrite (IHe1 inputs regs Hlen Hguard).
    destruct (K.nat_to_bool (MRC.eval_MRExpr inputs regs e1)).
    + rewrite (IHe2 inputs regs Hlen Hthen).
      reflexivity.
    + rewrite (IHe3 inputs regs Hlen Helse).
      reflexivity.
Qed.

Fixpoint mr_exprs_inputs_bounded
         (input_count : nat) (es : list MRC.MRExpr) : Prop :=
  match es with
  | [] => True
  | e :: rest =>
      mr_expr_inputs_bounded input_count e /\
      mr_exprs_inputs_bounded input_count rest
  end.

Fixpoint compile_MRExprs_to_EPR
         (input_count : nat) (es : list MRC.MRExpr) : list EPR.EPRCode :=
  match es with
  | [] => []
  | e :: rest =>
      compile_MRExpr_to_EPR input_count e ::
      compile_MRExprs_to_EPR input_count rest
  end.

Fixpoint eval_EPR_codes
         (codes : list EPR.EPRCode) (env : list nat) : list nat :=
  match codes with
  | [] => []
  | code :: rest => EPR.eval_EPR code env :: eval_EPR_codes rest env
  end.

Theorem compile_MRExprs_to_EPR_correct :
  forall input_count es inputs regs,
    length inputs = input_count ->
    mr_exprs_inputs_bounded input_count es ->
    eval_EPR_codes
      (compile_MRExprs_to_EPR input_count es)
      (inputs ++ regs) =
    MRC.eval_MRExprs inputs regs es.
Proof.
  induction es as [|e rest IH]; intros inputs regs Hlen Hbounded.
  - reflexivity.
  - destruct Hbounded as [He Hrest].
    simpl.
    rewrite compile_MRExpr_to_EPR_correct by assumption.
    rewrite IH by assumption.
    reflexivity.
Qed.

Record MRExprEPRCompilationCertificate
       (input_count : nat) (e : MRC.MRExpr) : Type := {
  compiled_mr_expr_code : EPR.EPRCode;
  compiled_mr_expr_bounded : mr_expr_inputs_bounded input_count e;
  compiled_mr_expr_correct :
    forall inputs regs,
      length inputs = input_count ->
      EPR.eval_EPR compiled_mr_expr_code (inputs ++ regs) =
      MRC.eval_MRExpr inputs regs e
}.

Definition compile_bounded_mr_expr_certificate
           (input_count : nat)
           (e : MRC.MRExpr)
           (bounded : mr_expr_inputs_bounded input_count e)
  : MRExprEPRCompilationCertificate input_count e :=
  {|
    compiled_mr_expr_code := compile_MRExpr_to_EPR input_count e;
    compiled_mr_expr_bounded := bounded;
    compiled_mr_expr_correct :=
      fun inputs regs Hlen =>
        compile_MRExpr_to_EPR_correct
          input_count e inputs regs Hlen bounded
  |}.

Lemma unpair_output_expr_inputs_bounded :
  mr_expr_inputs_bounded 1 MRC.unpair_output_expr.
Proof.
  unfold MRC.unpair_output_expr, MRC.reg_done, MRC.reg_left,
         MRC.reg_right.
  simpl.
  repeat split.
Qed.

Definition compiled_unpair_output_expr_certificate
  : MRExprEPRCompilationCertificate 1 MRC.unpair_output_expr :=
  compile_bounded_mr_expr_certificate
    1 MRC.unpair_output_expr unpair_output_expr_inputs_bounded.

End FormalSystemFactoryMRExprEPRCompiler.
