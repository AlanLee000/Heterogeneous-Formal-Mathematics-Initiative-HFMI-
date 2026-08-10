(** Single checked entry point for the complete HRISS v3.2 formalization. *)

Require Export HRISS_v3_2
  HRISS_v3_2_Semantics
  HRISS_v3_2_Stability
  HRISS_v3_2_Theory
  HRISS_v3_2_Clauses
  HRISS_v3_2_Eval
  HRISS_v3_2_Certificates
  HRISS_v3_2_FiniteTrees
  HRISS_v3_2_CertCompleteness
  HRISS_v3_2_Identity
  HRISS_v3_2_Structural
  HRISS_v3_2_Equivariance
  HRISS_v3_2_EvalEquivariance
  HRISS_v3_2_System.

Definition HRISS_v3_2_checked_package := HRISS_system.
