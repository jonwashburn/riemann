import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.academic_framework.HalfPlaneOuterV2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Core (P+) predicate and Whitney a.e. facade shared by Route B and Boundary proof.

This small module isolates the boundary `(P+)` predicate for the canonical field
`F(z) := (2 : ℂ) * J_pinch det2 O z` for a fixed outer `O` witnessing
`|O| = |det₂/ξ_ext|` on the boundary, and a facade lemma that exposes
the a.e. boundary inequality from a `(P+)` witness. Keeping this separate allows
Route B and the boundary wedge module to depend on the same definition without
import cycles.
-/

namespace RH.RS.WhitneyAeCore

open Real Complex
open MeasureTheory
open RH.AcademicFramework.HalfPlaneOuterV2 (boundary)

/-- Canonical outer choice for Route B: choose any RS `OuterHalfPlane` witness. -/
noncomputable def O : ℂ → ℂ :=
  RH.RS.OuterHalfPlane.choose_outer RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved

/-- Boundary wedge (P+): `Re (F_pinch det2 O (boundary t)) ≥ 0` a.e. -/
def PPlus_holds (O : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) (boundary t)).re

/-- Alias using the canonical chosen outer `O`. -/
def PPlus_canonical : Prop := PPlus_holds O

/-- Facade: unwrap the `(P+)` proposition into the raw a.e. inequality. -/
@[simp] theorem PPlus_canonical_ae :
  PPlus_canonical → (∀ᵐ t : ℝ,
    0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) (boundary t)).re) :=
  id

end RH.RS.WhitneyAeCore
