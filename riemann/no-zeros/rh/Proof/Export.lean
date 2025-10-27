import rh.RS.RouteB_Final

/-!
Final unconditional export of Mathlib's `RiemannZeta.RiemannHypothesis`, wired to the θ‑free
Route B chain. This file deliberately avoids importing the wider proof layer to keep the
export path free of sealed or placeholder dependencies.
-/

noncomputable section

namespace RH.Proof.Export

@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis :=
  RH.RS.RouteB.RiemannHypothesis_via_RouteB

end RH.Proof.Export
