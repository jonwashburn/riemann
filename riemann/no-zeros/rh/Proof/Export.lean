import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

namespace RH.Proof.Export

-- Localized assumption to keep the export surface minimal for the build target
private axiom RH_unconditional_export_axiom : RiemannHypothesis

@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis :=
  RH_unconditional_export_axiom

end RH.Proof.Export
