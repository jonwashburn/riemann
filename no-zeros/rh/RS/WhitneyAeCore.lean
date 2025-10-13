import rh.RS.CRGreenOuter
import rh.academic_framework.HalfPlaneOuterV2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Core (P+) predicate and Whitney a.e. facade shared by Route B and Boundary proof.

This small module isolates the boundary `(P+)` predicate for the canonical field
`F(z) := (2 : ℂ) * J_CR outer_exists z` and a trivial facade lemma that exposes
the a.e. boundary inequality from a `(P+)` witness. Keeping this separate allows
Route B and the boundary wedge module to depend on the same definition without
import cycles.
-/

namespace RH.RS.WhitneyAeCore

open Real Complex
open MeasureTheory
open RH.AcademicFramework.HalfPlaneOuterV2 (boundary)

/-- Boundary wedge (P+): `Re ((2) * J_CR O (boundary t)) ≥ 0` a.e. -/
def PPlus_holds (O : OuterOnOmega) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ ((2 : ℂ) * J_CR O (boundary t)).re

/-- Alias using the canonical outer `outer_exists`. -/
def PPlus_canonical : Prop := PPlus_holds outer_exists

/-- Facade: unwrap the `(P+)` proposition into the raw a.e. inequality. -/
theorem PPlus_canonical_ae :
  PPlus_canonical → (∀ᵐ t : ℝ, 0 ≤ ((2 : ℂ) * J_CR outer_exists (boundary t)).re) := by
  intro h; simpa [PPlus_canonical, PPlus_holds]

end RH.RS.WhitneyAeCore


