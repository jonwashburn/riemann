
import Riemann.Mathlib.Analysis.Complex.HardySpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Poisson Kernel for the Unit Disc

This file develops the theory of the Poisson kernel and Poisson integral
for harmonic functions on the unit disc.

## Main definitions

* `Complex.poissonKernel` : The Poisson kernel P_r(θ - φ)
* `Complex.poissonIntegral` : The Poisson integral of a function

## Main results

* `Complex.poissonKernel_pos` : The Poisson kernel is positive for r < 1
* `Complex.poissonKernel_max` : Upper bound (1+r)/(1-r)
* `Complex.poissonKernel_min` : Lower bound (1-r)/(1+r)

## References

* Stein, E.M., Shakarchi, R., "Complex Analysis", Chapter 5
-/

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped UnitDisc ENNReal NNReal Real

namespace Complex

/-! ### Poisson kernel infrastructure -/

/-- The Poisson kernel for the unit disc: P_r(θ) = (1 - r²) / (1 - 2r cos θ + r²).
This is the fundamental kernel for harmonic function theory on the disc. -/
def poissonKernel (r : ℝ) (θ φ : ℝ) : ℝ :=
  (1 - r^2) / (1 - 2*r*Real.cos (θ - φ) + r^2)

/-- The denominator of the Poisson kernel is always positive for r < 1. -/
lemma poissonKernel_denom_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    0 < 1 - 2*r*Real.cos (θ - φ) + r^2 := by
  have hcos : -1 ≤ Real.cos (θ - φ) ∧ Real.cos (θ - φ) ≤ 1 :=
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  nlinarith

/-- The Poisson kernel is non-negative for r < 1. -/
lemma poissonKernel_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    0 ≤ poissonKernel r θ φ := by
  unfold poissonKernel
  have h_num : 0 ≤ 1 - r^2 := by nlinarith
  exact div_nonneg h_num (le_of_lt (poissonKernel_denom_pos hr0 hr1 θ φ))

/-- The Poisson kernel is positive for 0 ≤ r < 1. -/
lemma poissonKernel_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    0 < poissonKernel r θ φ := by
  unfold poissonKernel
  have h_num : 0 < 1 - r^2 := by nlinarith
  exact div_pos h_num (poissonKernel_denom_pos hr0 hr1 θ φ)

/-- The Poisson kernel achieves its maximum: P_r(θ) ≤ (1+r)/(1-r). -/
lemma poissonKernel_max {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    poissonKernel r θ φ ≤ (1 + r) / (1 - r) := by
  have hnum_nonneg : 0 ≤ 1 - r ^ 2 := by
    have : r ^ 2 ≤ 1 := by nlinarith [hr0, hr1]
    exact sub_nonneg.mpr this
  have hden_pos :
      0 < 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 :=
    poissonKernel_denom_pos hr0 hr1 θ φ
  have hden_ge :
      (1 - r) ^ 2 ≤ 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 := by
    have hdecomp :
        1 - 2 * r * Real.cos (θ - φ) + r ^ 2
          = (1 - r) ^ 2 + 2 * r * (1 - Real.cos (θ - φ)) := by ring
    have hnonneg :
        0 ≤ 2 * r * (1 - Real.cos (θ - φ)) := by
      refine mul_nonneg (mul_nonneg (by norm_num) hr0)
        (sub_nonneg.mpr (Real.cos_le_one _))
    have :
        (1 - r) ^ 2 ≤
          (1 - r) ^ 2 + 2 * r * (1 - Real.cos (θ - φ)) :=
      le_add_of_nonneg_right hnonneg
    simpa [hdecomp] using this
  have hrec_le :
      1 / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2)
        ≤ 1 / (1 - r) ^ 2 := by
    have hpos : 0 < (1 - r) ^ 2 := by
      have h : 0 < 1 - r := sub_pos.mpr hr1
      simpa [pow_two] using sq_pos_of_pos h
    exact one_div_le_one_div_of_le hpos hden_ge
  have hineq :
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2)
        ≤ (1 - r ^ 2) / (1 - r) ^ 2 := by
    have : (1 - r ^ 2) * (1 / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2))
        ≤ (1 - r ^ 2) * (1 / (1 - r) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hrec_le hnum_nonneg
    simpa [poissonKernel] using this
  have hfrac_eq :
      (1 - r ^ 2) / (1 - r) ^ 2 = (1 + r) / (1 - r) := by
    have hne : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.ne'
    have hfactor : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    have hpow : (1 - r) ^ 2 = (1 - r) * (1 - r) := by simp [pow_two]
    simp_rw [hfactor, hpow]
    grind
  simpa [poissonKernel, hfrac_eq] using hineq

/-- The Poisson kernel achieves its minimum: (1-r)/(1+r) ≤ P_r(θ). -/
lemma poissonKernel_min {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    (1 - r) / (1 + r) ≤ poissonKernel r θ φ := by
  have hnum_nonneg : 0 ≤ 1 - r ^ 2 := by
    have : r ^ 2 ≤ 1 := by nlinarith [hr0, hr1]
    exact sub_nonneg.mpr this
  have hden_pos :
      0 < 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 :=
    poissonKernel_denom_pos hr0 hr1 θ φ
  have hden_le :
      1 - 2 * r * Real.cos (θ - φ) + r ^ 2 ≤ (1 + r) ^ 2 := by
    have hdecomp :
        1 - 2 * r * Real.cos (θ - φ) + r ^ 2 =
          (1 + r) ^ 2 - 2 * r * (1 + Real.cos (θ - φ)) := by ring
    have hnonneg :
        0 ≤ 2 * r * (1 + Real.cos (θ - φ)) := by
      refine mul_nonneg (mul_nonneg (by norm_num) hr0)
        (by linarith [Real.neg_one_le_cos (θ - φ)])
    have :
        (1 + r) ^ 2 - 2 * r * (1 + Real.cos (θ - φ))
          ≤ (1 + r) ^ 2 := by
      exact sub_le_self _ hnonneg
    simpa [hdecomp] using this
  have hrec_ge :
      1 / (1 + r) ^ 2 ≤
        1 / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2) := by
    have hpos :
        0 < 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 :=
      poissonKernel_denom_pos hr0 hr1 θ φ
    exact one_div_le_one_div_of_le hpos hden_le
  have hineq :
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2)
        ≥ (1 - r ^ 2) / (1 + r) ^ 2 := by
    have : (1 - r ^ 2) * (1 / (1 + r) ^ 2)
        ≤ (1 - r ^ 2) * (1 /
            (1 - 2 * r * Real.cos (θ - φ) + r ^ 2)) := by
      refine mul_le_mul_of_nonneg_left hrec_ge hnum_nonneg
    simpa [poissonKernel] using this
  have hfrac_eq :
      (1 - r ^ 2) / (1 + r) ^ 2 = (1 - r) / (1 + r) := by
    have hne : (1 + r) ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hr0)
    have hfactor : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    simp [pow_two]
    grind
  simpa [poissonKernel, hfrac_eq] using hineq

/-- The Poisson integral of a function. -/
def poissonIntegral (u : ℝ → ℝ) (r : ℝ) (θ : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * u φ

end Complex
