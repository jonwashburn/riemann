import rh.RS.Det2Outer
import rh.Cert.KxiPPlus
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CompletedXi

/-!
Core (P+) predicate and Whitney a.e. facade shared by Route B and Boundary proof.

This small module isolates the boundary `(P+)` predicate for the canonical field
`F(z) := (2 : ℂ) * J_pinch det2 O z` for a fixed outer `O` witnessing
`|O| = |det₂/ξ_ext|` on the boundary, and a facade lemma that exposes
the a.e. boundary inequality from a `(P+)` witness. Keeping this separate allows
Route B and the boundary wedge module to depend on the same definition without
import cycles.
-/

noncomputable section

namespace RH.RS.WhitneyAeCore

open Real Complex
open MeasureTheory
open RH.AcademicFramework.HalfPlaneOuterV2 (boundary)

/-- Canonical outer choice for Route B: choose any RS `OuterHalfPlane` witness. -/
noncomputable def O : ℂ → ℂ :=
  RH.RS.OuterHalfPlane.choose_outer RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext_proved

/-- (P+): nonnegativity of the boundary real part a.e. for
`F_pinch det2 O` along `boundary t`. -/
def PPlus_holds (O : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) (boundary t)).re

/-- Alias of `(P+)` using the canonical chosen outer `O`. -/
def PPlus_canonical : Prop := PPlus_holds O

/-- Facade: unwrap the `(P+)` proposition into the raw a.e. inequality. -/
@[simp] theorem PPlus_canonical_ae :
  PPlus_canonical → (∀ᵐ t : ℝ,
    0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) (boundary t)).re) :=
  id

/-- Bridge from certificate `(P+)` (stated using `Complex.mk (1/2) t`) to the
Whitney `(P+)` predicate that uses the AF boundary map. -/
theorem PPlus_canonical_of_cert :
  RH.Cert.PPlus (fun z => (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O) z)
  → PPlus_canonical := by
  intro hP
  -- rewrite boundary points into `boundary t` from `Complex.mk (1/2) t`
  have hb_mk_rev : ∀ t : ℝ,
      Complex.mk (1/2) t = boundary t := by
    intro t; apply Complex.ext <;> simp [boundary]
  -- transport the a.e. statement along the pointwise equality
  dsimp [PPlus_canonical, PPlus_holds]
  refine hP.mono ?_
  intro t ht
  -- Align boundary parameterizations; keep the function shape fixed
  have ht' := ht
  rw [hb_mk_rev t] at ht'
  exact ht'

/-- Alternate bridge: accept a certificate `(P+)` stated for `2·J_pinch` and
produce the Whitney `(P+)` predicate for the AF `F_pinch` without changing
the boundary parameterization. -/
theorem PPlus_canonical_of_cert_J :
  RH.Cert.PPlus (fun z => (2 : ℂ) * (RH.AcademicFramework.HalfPlaneOuterV2.J_pinch RH.RS.det2 O z))
  → PPlus_canonical := by
  intro hP
  -- rewrite boundary points into `boundary t` from `Complex.mk (1/2) t`
  have hb_mk_rev : ∀ t : ℝ,
      Complex.mk (1/2) t = boundary t := by
    intro t; apply Complex.ext <;> simp [boundary]
  -- transport and align shapes via the AF `F_pinch = 2·J_pinch` identity
  dsimp [PPlus_canonical, PPlus_holds]
  refine hP.mono ?_
  intro t ht
  -- Convert the hypothesis to the `F_pinch` form at the same point using definitional equality
  change 0 ≤ ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O)
                (Complex.mk (1/2) t)).re at ht
  -- Now rewrite the boundary representation and finish
  rw [hb_mk_rev t] at ht
  exact ht

end RH.RS.WhitneyAeCore
