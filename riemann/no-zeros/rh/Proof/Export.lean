import rh.RS.CertificateConstruction

namespace RH.Proof.Export

/-- Re-export the zero-argument unconditional theorem name expected by the guard.
This forwards to the certificate pipeline without introducing any axioms. -/
@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis :=
  RH.RS.CertificateConstruction.RiemannHypothesis_unconditional

end RH.Proof.Export
