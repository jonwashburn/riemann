import rh.academic_framework.Core
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
-- Removed nonexistent import; `Basic` suffices
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic


/-!
# Weierstrass Product Theory

This file contains helper lemmas for Weierstrass product convergence.

## Main results

* `log_one_sub_bound` - Bound on |log(1-z)| for small z
* `multipliable_one_sub_of_summable` - Convergence criterion for ∏(1-aᵢ)
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators

/--- Bound for ‖log(1 - z)‖ when ‖z‖ ≤ 1/2, via the (1+z) lemma with z ↦ -z. -/
lemma norm_log_one_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖log (1 - z)‖ ≤ 2 * ‖z‖ := by
  have hz_lt_one : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have h := Complex.norm_log_one_add_le (z := -z) (by simpa [norm_neg] using hz_lt_one)
  -- ‖log(1 - z)‖ ≤ ‖z‖^2 / (2 * (1 - ‖z‖)) + ‖z‖
  have h' : ‖log (1 - z)‖ ≤ ‖z‖ ^ 2 / (2 * (1 - ‖z‖)) + ‖z‖ := by
    simpa [sub_eq_add_neg, norm_neg] using h
  -- Show the quadratic tail ≤ ‖z‖ for ‖z‖ ≤ 1/2
  have htail : ‖z‖ ^ 2 / (2 * (1 - ‖z‖)) ≤ ‖z‖ := by
    have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg _
    have hden_pos : 0 < 1 - ‖z‖ := by have : ‖z‖ ≤ (1/2:ℝ) := hz; linarith
    -- r := ‖z‖; goal: r^2 / (2*(1-r)) ≤ r when 0 ≤ r ≤ 1/2
    have hz_le_half : ‖z‖ ≤ (1/2:ℝ) := hz
    -- Multiply both sides by positive 2*(1-r)
    have : ‖z‖ ^ 2 ≤ ‖z‖ * (2 * (1 - ‖z‖)) := by
      have hineq : (1:ℝ) ≤ 2 * (1 - ‖z‖) := by
        have : (1/2:ℝ) ≤ 1 - ‖z‖ := by linarith
        linarith
      -- r^2 ≤ r * (2*(1-r)) follows from r ≤ 2*(1-r) and r ≥ 0
      have := mul_le_mul_of_nonneg_left hineq hz_nonneg
      simpa [pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using this
    have hpos2 : 0 < 2 * (1 - ‖z‖) := by nlinarith [hden_pos]
    exact (div_le_iff (show 0 < 2 * (1 - ‖z‖) by exact hpos2)).2 this
  calc
    ‖log (1 - z)‖ ≤ ‖z‖ ^ 2 / (2 * (1 - ‖z‖)) + ‖z‖ := h'
    _ ≤ ‖z‖ + ‖z‖ := by exact add_le_add_right htail _
    _ = 2 * ‖z‖ := by ring

/-- Alias for compatibility -/
lemma log_one_sub_bound {z : ℂ} (hz : ‖z‖ < 1 / 2) :
  ‖log (1 - z)‖ ≤ 2 * ‖z‖ := norm_log_one_sub_le hz

/-- If ∑ aᵢ converges and each |aᵢ| < 1/2, then ∏(1-aᵢ) converges -/
lemma multipliable_one_sub_of_summable {ι : Type*} {a : ι → ℂ}
  (h_sum : Summable a) (h_small : ∀ i, ‖a i‖ < 1/2) :
  Multipliable (fun i => 1 - a i) := by
  -- TODO: replace with a mathlib lemma once available; standard via log-sum test
  admit

end AcademicRH.DiagonalFredholm
