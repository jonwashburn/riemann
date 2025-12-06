
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Additional lemmas for the positive part of the logarithm (log⁺)

This file provides additional infrastructure lemmas for `Real.log⁺` (also known as `posLog`),
particularly for handling quotients and inverses needed in Nevanlinna theory.

The main Mathlib API is in `Mathlib.Analysis.SpecialFunctions.Log.PosLog`.

## Main results

* `Real.posLog_inv_eq` : `log⁺ (a⁻¹) = max 0 (-log a)` for `a > 0`
* `Real.posLog_div_le` : `log⁺ (a / b) ≤ log⁺ a + log⁺ (b⁻¹)` for `a ≥ 0`, `b > 0`
* `Real.posLog_norm_div_le` : `log⁺ ‖a / b‖ ≤ log⁺ ‖a‖ + log⁺ ‖b‖⁻¹`

## References

* Hayman, W.K., "Meromorphic Functions", Chapter 1
* Nevanlinna, R., "Analytic Functions", Chapter II
-/

open Real

namespace Real

variable {a b : ℝ}

/-! ### Properties of log⁺ for inverses -/

/-- **log⁺ of inverse**: For `a > 0`, `log⁺ (a⁻¹) = max 0 (-log a)`. -/
lemma posLog_inv_eq (ha : 0 < a) : log⁺ a⁻¹ = max 0 (-log a) := by
  simp only [posLog_def, log_inv, max_comm]

/-- For `a ≥ 1`, `log⁺ (a⁻¹) = 0`. -/
lemma posLog_inv_of_one_le (ha : 1 ≤ a) : log⁺ a⁻¹ = 0 := by
  have ha_pos : 0 < a := lt_of_lt_of_le one_pos ha
  rw [posLog_inv_eq ha_pos]
  simp only [max_eq_left_iff, Left.neg_nonpos_iff]
  exact log_nonneg ha

/-- For `0 < a < 1`, `log⁺ (a⁻¹) = -log a = log (a⁻¹)`. -/
lemma posLog_inv_of_lt_one (ha_pos : 0 < a) (ha : a < 1) : log⁺ a⁻¹ = -log a := by
  rw [posLog_inv_eq ha_pos]
  simp only [max_eq_right_iff]
  have hlog : log a < 0 := log_neg ha_pos ha
  linarith

/-! ### Subadditivity for quotients -/

/-- **Subadditivity of log⁺ for quotients**: For `a ≥ 0` and `b > 0`,
    `log⁺ (a / b) ≤ log⁺ a + log⁺ (b⁻¹)`.

This follows from `posLog_mul` since `a / b = a * b⁻¹`. -/
lemma posLog_div_le (ha : 0 ≤ a) (hb : 0 < b) :
    log⁺ (a / b) ≤ log⁺ a + log⁺ b⁻¹ := by
  rw [div_eq_mul_inv]
  exact posLog_mul

/-- **Key estimate for quotients using -log**: For `a ≥ 0` and `b > 0`,
    `log⁺ (a / b) ≤ log⁺ a + max 0 (-log b)`. -/
lemma posLog_div_le' (ha : 0 ≤ a) (hb : 0 < b) :
    log⁺ (a / b) ≤ log⁺ a + max 0 (-log b) := by
  have h := posLog_div_le ha hb
  rw [posLog_inv_eq hb] at h
  exact h

/-! ### Norm versions for complex analysis -/

/-- `log⁺ ‖a / b‖ ≤ log⁺ ‖a‖ + log⁺ ‖b‖⁻¹` for complex numbers with `b ≠ 0`. -/
lemma posLog_norm_div_le {a b : ℂ} (hb : b ≠ 0) :
    log⁺ ‖a / b‖ ≤ log⁺ ‖a‖ + log⁺ ‖b‖⁻¹ := by
  rw [norm_div]
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  exact posLog_div_le (norm_nonneg a) hb'

/-- For bounded-type functions `g = G/H`, the log⁺ of the norm satisfies
    `log⁺ ‖G / H‖ ≤ log⁺ ‖G‖ + log⁺ ‖H‖⁻¹`. -/
lemma posLog_norm_ratio_le {G H : ℂ} (hH : H ≠ 0) :
    log⁺ ‖G / H‖ ≤ log⁺ ‖G‖ + log⁺ ‖H‖⁻¹ :=
  posLog_norm_div_le hH

/-! ### Circle average bounds -/

/-- If `f` is bounded pointwise by `C` on a set, then `log⁺ ‖f‖` is bounded by `log⁺ C`. -/
lemma posLog_norm_le_of_norm_le {E : Type*} [SeminormedAddCommGroup E] {α : Type*}
    {f : α → E} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, ‖f x‖ ≤ C) :
    ∀ x, log⁺ ‖f x‖ ≤ log⁺ C := by
  intro x
  exact posLog_le_posLog (norm_nonneg _) (hf x)

/-! ### Tendsto properties -/

/-- `log⁺` is continuous.
See also `ValueDistribution.continuous_posLog` in `Cartan.lean` for an alternative proof. -/
lemma continuous_posLog' : Continuous (fun x : ℝ => log⁺ x) := by
  -- log⁺ x = log (max 1 |x|)
  -- The function x ↦ max 1 |x| is continuous and always ≥ 1 > 0
  -- Hence log (max 1 |x|) is continuous.
  have h_eq : (fun x : ℝ => log⁺ x) = fun x => log (max 1 |x|) := by
    funext x
    have h1 : log⁺ |x| = log (max 1 |x|) := posLog_eq_log_max_one (abs_nonneg x)
    rw [posLog_abs] at h1
    exact h1
  rw [h_eq]
  refine Continuous.log ?_ ?_
  · exact continuous_const.max continuous_abs
  · intro x
    have : 1 ≤ max 1 |x| := le_max_left 1 |x|
    linarith

end Real
