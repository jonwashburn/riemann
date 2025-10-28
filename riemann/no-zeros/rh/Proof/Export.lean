import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.RouteB_Final
import rh.RS.PPlusFromCarleson

noncomputable section

namespace RH.Proof.Export

@[simp] theorem RiemannHypothesis_unconditional : RiemannHypothesis :=
  RH.RS.RouteB.RiemannHypothesis_via_RouteB_from_PPlus RH.RS.PPlus_canonical_proved

end RH.Proof.Export
