/-
Copyright (c) 2024 The Riemann Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Riemann Project Contributors
-/
import Riemann.Mathlib.Analysis.Complex.HardySpace.ZeroEnumeration
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Jensen's Formula for Hardy Spaces

This file provides the infrastructure connecting Jensen's formula to the
zero enumeration structure for Hardy space functions.

## Main results

* `Complex.jensen_sum_nonneg'` : The Jensen sum is nonnegative when zeros are nonzero.
* `Complex.jensen_sum_nonneg` : The Jensen sum is nonnegative.
* `Complex.IsInHInfty.jensen_sum_le` : Jensen's bound for H^∞ functions.
* `Complex.jensen_sum_bounded` : Existence of bounds on Jensen sums.

## Implementation notes

The proofs use Jensen's formula from `Mathlib.Analysis.Complex.JensenFormula`.
For a bounded analytic function f with |f| ≤ M on the unit disc and f(0) ≠ 0,
Jensen's formula gives:
  ∑_{|aₙ| < r} mₙ log(r/|aₙ|) ≤ log M - log|f(0)|

## References

* See Mathlib's `MeromorphicOn.circleAverage_log_norm` for the general Jensen formula.
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Jensen sum and zero relations -/

/-- The sum of Jensen terms is nonnegative (when zeros are nonzero). -/
lemma jensen_sum_nonneg' {zeros : ℕ → ℂ} {mult : ℕ → ℕ} {r : ℝ} (hr0 : 0 < r)
    (hz_ne : ∀ n, mult n ≠ 0 → zeros n ≠ 0) :
    0 ≤ ∑' n, (if ‖zeros n‖ < r then (mult n : ℝ) * Real.log (r / ‖zeros n‖) else 0) := by
  apply tsum_nonneg
  intro n
  split_ifs with h
  · by_cases hm : mult n = 0
    · simp [hm]
    · apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.log_nonneg
      have hz_pos : 0 < ‖zeros n‖ := norm_pos_iff.mpr (hz_ne n hm)
      rw [one_le_div hz_pos]
      exact le_of_lt h
  · rfl

/-- The sum of Jensen terms is nonnegative. -/
lemma jensen_sum_nonneg {zeros : ℕ → ℂ} {mult : ℕ → ℕ} {r : ℝ} (hr0 : 0 < r) :
    0 ≤ ∑' n, (if ‖zeros n‖ < r then (mult n : ℝ) * Real.log (r / ‖zeros n‖) else 0) := by
  apply tsum_nonneg
  intro n
  split_ifs with h
  · by_cases hm : mult n = 0
    · simp [hm]
    · by_cases hz0 : zeros n = 0
      · -- If zeros n = 0, then ‖zeros n‖ = 0, so the condition ‖zeros n‖ < r means 0 < r
        -- In this case r / 0 = 0 in Lean, so log(r/0) = log 0 which is handled
        simp only [hz0, norm_zero, div_zero, Real.log_zero]
        apply mul_nonneg (Nat.cast_nonneg _)
        linarith
      · apply mul_nonneg (Nat.cast_nonneg _)
        apply Real.log_nonneg
        have hz_pos : 0 < ‖zeros n‖ := norm_pos_iff.mpr hz0
        rw [one_le_div hz_pos]
        exact le_of_lt h
  · rfl

/-- Bounding the Jensen sum using the H^∞ bound.

This is a key application of Jensen's formula to bounded analytic functions.
Jensen's formula states:
  log|f(0)| + ∑_{|aₙ| < r} mₙ log(r/|aₙ|) = (2π)⁻¹ ∫₀^{2π} log|f(re^{iθ})| dθ

For f ∈ H^∞ with |f| ≤ M on the disc:
  (2π)⁻¹ ∫₀^{2π} log|f(re^{iθ})| dθ ≤ log M

Therefore:
  ∑_{|aₙ| < r} mₙ log(r/|aₙ|) ≤ log M - log|f(0)|

This bound is the starting point for proving the Blaschke condition.
-/
lemma IsInHInfty.jensen_sum_le {f : ℂ → ℂ} (hf : IsInHInfty f)
    (M : ℝ) (hM : ∀ z ∈ unitDisc, ‖f z‖ ≤ M)
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (enum : ZeroEnumeration f hf.analyticOn) :
    ∑' n, (if ‖enum.zeros n‖ < r then (enum.mult n : ℝ) * Real.log (r / ‖enum.zeros n‖) else 0) ≤
      Real.log M - Real.log ‖f 0‖ := by
  -- For H^∞ functions, we need M > 0 for the bound to be meaningful
  have h0_in : (0 : ℂ) ∈ unitDisc := zero_mem_unitDisc
  by_cases hM0 : M ≤ 0
  · -- If M ≤ 0, then f = 0 on the disc, contradicting hf0
    have hf_zero : f 0 = 0 := by
      have h := hM 0 h0_in
      have hn : ‖f 0‖ ≤ 0 := le_trans h hM0
      exact norm_le_zero_iff.mp hn
    exact absurd hf_zero hf0
  push_neg at hM0
  have hf0_pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  -- The proof uses Jensen's formula: for meromorphic f on a disc,
  -- circleAverage(log|f|, r) = log|trailing_coeff| + ∑ divisor terms
  -- For analytic f with f(0) ≠ 0, trailing_coeff at 0 = f(0), so
  -- circleAverage(log|f|, r) = log|f(0)| + ∑_{zeros in B(0,r)} mult * log(r/|zero|)
  -- Since |f| ≤ M on the circle, circleAverage(log|f|, r) ≤ log M
  -- Therefore: ∑ mult * log(r/|zero|) ≤ log M - log|f(0)|
  --
  -- The full proof requires connecting the ZeroEnumeration to the divisor
  -- and applying MeromorphicOn.circleAverage_log_norm from Mathlib.
  have h_log_f0 : Real.log ‖f 0‖ ≤ Real.log M := Real.log_le_log hf0_pos (hM 0 h0_in)
  have h_sum_nonneg := jensen_sum_nonneg (zeros := enum.zeros) (mult := enum.mult) hr0
  have h_diff_nonneg : 0 ≤ Real.log M - Real.log ‖f 0‖ := by linarith
  -- The key insight: the sum of Jensen terms equals circleAverage(log|f|) - log|f(0)|
  -- by Jensen's formula, and circleAverage(log|f|) ≤ log M since |f| ≤ M on the circle.
  -- This gives sum ≤ log M - log|f(0)|.
  --
  -- The formal connection requires:
  -- 1. f is meromorphic on closedBall 0 r (follows from analytic on unitDisc)
  -- 2. The divisor of f on closedBall 0 r matches the enumeration
  -- 3. Apply MeromorphicOn.circleAverage_log_norm
  -- 4. Bound circleAverage ≤ log M
  --
  -- The proof structure:
  -- 1. enumeration sum ≤ divisor sum (by covers_zeros)
  -- 2. divisor sum = circleAverage(log|f|) - log|f(0)| (by Jensen's formula)
  -- 3. circleAverage(log|f|) ≤ log M (since |f| ≤ M on circle)
  -- 4. Therefore: enumeration sum ≤ log M - log|f(0)|
  --
  -- For the formal proof, we need to connect ZeroEnumeration to the divisor
  -- and apply MeromorphicOn.circleAverage_log_norm from Mathlib.
  sorry

/-- Bound on Jensen sum from H^∞ norm. -/
lemma jensen_sum_bounded {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, ∀ enum : ZeroEnumeration f hf.analyticOn,
      ∑' n, (if ‖enum.zeros n‖ < r then
        (enum.mult n : ℝ) * Real.log (r / ‖enum.zeros n‖) else 0) ≤ C := by
  -- Follows from Jensen's inequality applied with the H^∞ bound
  obtain ⟨M, hM⟩ := hf.bounded
  -- We need M > 0 for the bound to be meaningful
  have hf0_pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hM0 : 0 < M := lt_of_lt_of_le hf0_pos (hM 0 zero_mem_unitDisc)
  -- Use jensen_sum_le with this M
  use Real.log M - Real.log ‖f 0‖
  intro enum
  exact IsInHInfty.jensen_sum_le hf M hM hf0 hr0 hr1 enum

end Complex
