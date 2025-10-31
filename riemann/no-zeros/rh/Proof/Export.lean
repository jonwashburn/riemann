import rh.Proof.Main
import rh.RS.PinchIngredients
import rh.RS.CertificateConstruction

namespace RH.Proof.Export

open RH.Proof
open RH.Proof.Final

abbrev PipelineReady := RH.Proof.PipelineReady

@[simp] theorem pipeline_ready_unconditional : PipelineReady :=
  RH.Proof.pipeline_ready_unconditional

/-- Final Riemann Hypothesis theorem consuming a pinch certificate. -/
@[simp] theorem RiemannHypothesis_final (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RH_from_pinch_certificate C

/-- Convenience alias of the final theorem. -/
@[simp] theorem RH (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RiemannHypothesis_final C

/-!
Re-export the zero-argument unconditional theorem name expected by the guard.
This forwards to the green certificate pipeline without introducing any axioms.
-/
@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis :=
  RH.RS.CertificateConstruction.RiemannHypothesis_unconditional

end RH.Proof.Export
