From Stdlib Require Import Lists.List.

Require Import FormalSystemFactoryNatCodec.
Require Import FormalSystemFactoryEPRUnpairInterface.
Require Import FormalSystemFactoryMRCode.

Import ListNotations.

Module NC := FormalSystemFactoryNatCodec.FormalSystemFactoryNatCodec.
Module UI := FormalSystemFactoryEPRUnpairInterface.FormalSystemFactoryEPRUnpairInterface.
Module MRC := FormalSystemFactoryMRCode.FormalSystemFactoryMRCode.

Module FormalSystemFactoryMRBackend.

Definition MRUnpairProgramSpec (program : MRC.MRProgram) : Prop :=
  forall fuel n,
    MRC.eval_MRProgram program fuel [n] =
    UI.unpair_result_fuel fuel n.

Record MRUnpairCertificate : Type := {
  mr_unpair_code : MRC.MRProgram;
  mr_unpair_correct : MRUnpairProgramSpec mr_unpair_code
}.

Definition mr_unpair_certificate : MRUnpairCertificate :=
  {|
    mr_unpair_code := MRC.mr_unpair_program;
    mr_unpair_correct := MRC.eval_mr_unpair_program_matches_unpair
  |}.

Definition eval_MRCanonicalUnpair
           (program : MRC.MRProgram) (n : nat) : nat :=
  MRC.eval_MRProgram program (S n) [n].

Definition MRCanonicalUnpairProgramSpec
           (program : MRC.MRProgram) : Prop :=
  forall n,
    eval_MRCanonicalUnpair program n = UI.unpair_result n.

Record MRCanonicalUnpairCertificate : Type := {
  mr_canonical_unpair_code : MRC.MRProgram;
  mr_canonical_unpair_correct :
    MRCanonicalUnpairProgramSpec mr_canonical_unpair_code
}.

Lemma mr_unpair_certificate_canonical_correct :
  MRCanonicalUnpairProgramSpec (mr_unpair_code mr_unpair_certificate).
Proof.
  intro n.
  unfold eval_MRCanonicalUnpair, UI.unpair_result.
  apply mr_unpair_correct.
Qed.

Definition mr_canonical_unpair_certificate
  : MRCanonicalUnpairCertificate :=
  {|
    mr_canonical_unpair_code := mr_unpair_code mr_unpair_certificate;
    mr_canonical_unpair_correct :=
      mr_unpair_certificate_canonical_correct
  |}.

Lemma mr_certified_unpair_on_pair :
  forall cert x y fuel,
    x < fuel ->
    MRC.eval_MRProgram
      (mr_unpair_code cert) fuel [NC.pair_nat x y] =
    S (NC.pair_nat x y).
Proof.
  intros cert x y fuel Hfuel.
  rewrite (mr_unpair_correct cert fuel (NC.pair_nat x y)).
  apply UI.unpair_result_fuel_pair.
  exact Hfuel.
Qed.

Lemma mr_certified_canonical_unpair_on_pair :
  forall cert x y,
    eval_MRCanonicalUnpair
      (mr_canonical_unpair_code cert) (NC.pair_nat x y) =
    S (NC.pair_nat x y).
Proof.
  intros cert x y.
  rewrite (mr_canonical_unpair_correct cert (NC.pair_nat x y)).
  apply UI.unpair_result_pair.
Qed.

Record MRDecoderBackend : Type := {
  backend_unpair_certificate : MRUnpairCertificate;
  backend_canonical_unpair_certificate : MRCanonicalUnpairCertificate
}.

Definition default_mr_decoder_backend : MRDecoderBackend :=
  {|
    backend_unpair_certificate := mr_unpair_certificate;
    backend_canonical_unpair_certificate :=
      mr_canonical_unpair_certificate
  |}.

Theorem default_backend_unpair_matches_unpair :
  forall fuel n,
    MRC.eval_MRProgram
      (mr_unpair_code
         (backend_unpair_certificate default_mr_decoder_backend))
      fuel [n] =
    UI.unpair_result_fuel fuel n.
Proof.
  intros fuel n.
  apply mr_unpair_correct.
Qed.

Theorem default_backend_canonical_unpair_matches_unpair :
  forall n,
    eval_MRCanonicalUnpair
      (mr_canonical_unpair_code
         (backend_canonical_unpair_certificate
            default_mr_decoder_backend))
      n =
    UI.unpair_result n.
Proof.
  intro n.
  apply mr_canonical_unpair_correct.
Qed.

Theorem default_backend_unpair_on_pair :
  forall x y fuel,
    x < fuel ->
    MRC.eval_MRProgram
      (mr_unpair_code
         (backend_unpair_certificate default_mr_decoder_backend))
      fuel [NC.pair_nat x y] =
    S (NC.pair_nat x y).
Proof.
  intros x y fuel Hfuel.
  apply mr_certified_unpair_on_pair.
  exact Hfuel.
Qed.

Theorem default_backend_canonical_unpair_on_pair :
  forall x y,
    eval_MRCanonicalUnpair
      (mr_canonical_unpair_code
         (backend_canonical_unpair_certificate
            default_mr_decoder_backend))
      (NC.pair_nat x y) =
    S (NC.pair_nat x y).
Proof.
  intros x y.
  apply mr_certified_canonical_unpair_on_pair.
Qed.

End FormalSystemFactoryMRBackend.
