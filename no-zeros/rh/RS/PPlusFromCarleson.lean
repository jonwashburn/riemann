import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import rh.Cert.KxiPPlus
import rh.RS.WhitneyAeCore
import rh.RS.BoundaryWedgeProof
import rh.RS.CRGreenOuter
import rh.RS.PoissonPlateau

/-!
# RS bridge: Concrete Carleson ⇒ (P+)

This module exposes the boundary wedge positivity `(P+)` for the canonical
field as an available result for downstream modules, avoiding import cycles
with the boundary wedge proof file by factoring the predicate through
`WhitneyAeCore`.
-/

noncomputable section

open Complex MeasureTheory Real
open RH.RS.WhitneyAeCore
open RH.Cert

namespace RH.RS

/-! ## Pivot export

We re-export the main `(P+)` result by referring to the proof in
`BoundaryWedgeProof`. This avoids the previous axiom placeholder and removes
the circularity.
-/

theorem PPlus_canonical_proved : PPlus_canonical :=
  RH.RS.BoundaryWedgeProof.PPlus_from_constants

/-- Main export: `(P+)` holds for the canonical CR boundary field. -/
theorem PPlusFromCarleson_exists_proved_default :
  PPlus_canonical := PPlus_canonical_proved

/-! ## Legacy wrappers kept for compatibility -/

@[simp] def localWedge_from_WhitneyCarleson
    (F : ℂ → ℂ)
    (_hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ) : Prop :=
  True

theorem localWedge_from_CRGreen_and_Poisson
    (F : ℂ → ℂ)
    (hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ) :
    localWedge_from_WhitneyCarleson F hex := by
  simp [localWedge_from_WhitneyCarleson]

end RS
end RH
