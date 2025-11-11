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
  intro h; exact h

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
    simpa [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_eq_add_neg]
      using (Complex.mul_re ((2 : ℂ)) (J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)))
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
      simpa using
        (mul_div_cancel ((J_CR outer_exists ((1/2 : ℝ) + Complex.I * t)).re)
          (by norm_num : (2 : ℝ) ≠ 0))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  simpa [hcancel] using hdiv

end RH.RS.WhitneyAeCore
