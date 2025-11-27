import Riemann.RS.CRGreenOuter

noncomputable section

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
open RH.AcademicFramework

/-- Canonical outer function used throughout the Route B wiring. -/
def O : ℂ → ℂ := outer_exists.outer

/-- Boundary wedge (P+): `Re ((2) * J_CR O (boundary t)) ≥ 0` a.e. -/
def PPlus_holds (O : OuterOnOmega) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ ((2 : ℂ) * J_CR O (boundary t)).re

/-- Alias using the canonical outer `outer_exists`. -/
def PPlus_canonical : Prop := PPlus_holds outer_exists

/-- Facade: unwrap the `(P+)` proposition into the raw a.e. inequality. -/
theorem PPlus_canonical_ae :
  PPlus_canonical → (∀ᵐ t : ℝ, 0 ≤ ((2 : ℂ) * J_CR outer_exists (boundary t)).re) := by
  intro h; exact h

/-! ### Bridge to the AF boundary-positivity predicate

The academic-framework half‑plane layer uses the predicate
`BoundaryPositive F : Prop := ∀ᵐ t, 0 ≤ (F (boundary t)).re`.  For the
canonical pinch field
`F_pinch det2 outer_exists.outer = (2 : ℂ) * J_pinch det2 outer_exists.outer`,
this is definitionally the same as `(P+)` for `2 · J_CR outer_exists`,
since `J_CR outer_exists = J_pinch det2 outer_exists.outer` pointwise.

The lemma below packages this identification so that analytic Poisson
transport theorems stated in terms of `BoundaryPositive` can be fed
directly from a `PPlus_canonical` witness. -/

lemma boundaryPositive_pinch_from_PPlus_canonical
  (h : PPlus_canonical) :
  HalfPlaneOuterV2.BoundaryPositive
    (HalfPlaneOuterV2.F_pinch RH.RS.det2 outer_exists.outer) := by
  -- Unfold the AF boundary-positivity predicate.
  dsimp [HalfPlaneOuterV2.BoundaryPositive]
  -- `(P+)` gives a.e. nonnegativity for `Re(2·J_CR outer_exists (boundary t))`.
  have hAE :
      ∀ᵐ t : ℝ, 0 ≤ (((2 : ℂ) * J_CR outer_exists (boundary t))).re := by
    simpa [PPlus_canonical, PPlus_holds] using h
  -- Transport this along the pointwise identification
  -- `F_pinch det2 outer_exists.outer (boundary t) = 2·J_CR outer_exists (boundary t)`.
  refine hAE.mono ?_
  intro t ht
  have hF :
      HalfPlaneOuterV2.F_pinch RH.RS.det2 outer_exists.outer (boundary t)
        = (2 : ℂ) * J_CR outer_exists (boundary t) := by
    -- By expanding the definitions of `F_pinch`, `J_pinch`, and `J_CR`,
    -- both sides are definitionally the same expression.
    rfl
  -- Rewrite the inequality along this identity.
  simpa [hF] using ht


private lemma boundary_nonneg_AE
  (h : PPlus_canonical) :
  ∀ᵐ t : ℝ, 0 ≤ (J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re := by
  -- Unfold/identify boundary points once
  have hb_mk : ∀ t : ℝ, boundary t = Complex.mk (1/2) t := by
    intro t; apply Complex.ext <;> simp
  have hmk_add : ∀ t : ℝ, Complex.mk (1/2) t = ((1/2 : ℝ) + Complex.I * t) := by
    intro t; apply Complex.ext <;> simp
  -- Transport `(P+)` AE inequality along the boundary equality
  have h2 : ∀ᵐ t : ℝ,
      0 ≤ (((2 : ℂ) * J_CR outer_exists ((1/2 : ℝ) + Complex.I * t))).re := by
    refine h.mono ?_
    intro t ht; simpa [hb_mk t, hmk_add t] using ht
  -- Drop the positive real factor `2` on the real part
  have hpos : (0 : ℝ) < 2 := by norm_num
  refine h2.mono ?_
  intro t ht
  have hrewrite :
      (((2 : ℂ) * J_CR outer_exists ((1/2 : ℝ) + Complex.I * t))).re
        = (2 : ℝ) * (J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re := by
    simp [zero_mul, sub_eq_add_neg]
  have h2re : 0 ≤ (2 : ℝ) * (J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re := by
    simpa [hrewrite] using ht
  have hdiv : 0 ≤ ((2 : ℝ) * (J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re) / (2 : ℝ) :=
    div_nonneg h2re (le_of_lt hpos)
  have hcancel :
      ((2 : ℝ) * (J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re) / (2 : ℝ)
        = (J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re := by
    have :
        ((J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re * (2 : ℝ)) / (2 : ℝ)
          = (J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re := by
      simp
    simp
  simpa [hcancel] using hdiv

end RH.RS.WhitneyAeCore
