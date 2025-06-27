import rh.academic_framework.Core
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RH.academic_framework.DiagonalFredholm.DiagOp
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.Polynomial


/-!
# Weierstrass Product Theory

This file contains helper lemmas for Weierstrass product convergence.

## Main results

* `log_one_sub_bound` - Bound on |log(1-z)| for small z
* `multipliable_one_sub_of_summable` - Convergence criterion for ∏(1-aᵢ)
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators

/-- Custom implementation of the logarithm bound for |z| < 1/2 -/
lemma norm_log_one_sub_le {z : ℂ} (hz : ‖z‖ < 1 / 2) : ‖log (1 - z)‖ ≤ 2 * ‖z‖ := by
  -- For |z| < 1/2, we use that log(1-z) = -∑_{n=1}^∞ z^n/n
  -- The series converges absolutely for |z| < 1
  have hz1 : ‖z‖ < 1 := by linarith
  -- Use the Taylor series: log(1-z) = -z - z²/2 - z³/3 - ...
  -- So |log(1-z)| ≤ |z| + |z|²/2 + |z|³/3 + ... = |z|/(1-|z|)
  -- When |z| < 1/2, we have 1/(1-|z|) ≤ 2
  have h_series : ‖log (1 - z)‖ ≤ ‖z‖ / (1 - ‖z‖) := by
    -- This is a standard bound for the logarithm series
    -- We use that |log(1-z)| ≤ ∑_{n=1}^∞ |z|^n/n ≤ ∑_{n=1}^∞ |z|^n = |z|/(1-|z|)
    sorry -- This requires the full Taylor series analysis
  have h_denom : (1 - ‖z‖)⁻¹ ≤ 2 := by
    -- We want to show (1 - ‖z‖)⁻¹ ≤ 2
    -- Since ‖z‖ < 1/2, we have 1 - ‖z‖ > 1/2
    -- So (1 - ‖z‖)⁻¹ < 2
    have h_pos : 0 < 1 - ‖z‖ := by linarith
    have h_bound : 1/2 ≤ 1 - ‖z‖ := by linarith
    -- (1 - ‖z‖)⁻¹ ≤ (1/2)⁻¹ = 2
    calc (1 - ‖z‖)⁻¹
      _ ≤ (1/2)⁻¹ := by exact inv_le_inv_of_le (by norm_num) h_bound
      _ = 2 := by norm_num
  calc ‖log (1 - z)‖
    _ ≤ ‖z‖ / (1 - ‖z‖) := h_series
    _ = ‖z‖ * (1 - ‖z‖)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ ‖z‖ * 2 := by gcongr
    _ = 2 * ‖z‖ := by ring

/-- Alias for compatibility -/
lemma log_one_sub_bound {z : ℂ} (hz : ‖z‖ < 1 / 2) :
  ‖log (1 - z)‖ ≤ 2 * ‖z‖ := norm_log_one_sub_le hz

/-- If ∑ aᵢ converges and each |aᵢ| < 1/2, then ∏(1-aᵢ) converges -/
lemma multipliable_one_sub_of_summable {ι : Type*} {a : ι → ℂ}
  (h_sum : Summable a) (h_small : ∀ i, ‖a i‖ < 1/2) :
  Multipliable (fun i => 1 - a i) := by
  -- The product ∏(1-aᵢ) converges iff ∑log(1-aᵢ) converges
  -- Since |log(1-aᵢ)| ≤ 2|aᵢ| and ∑|aᵢ| converges, we get convergence
  sorry -- This requires the full multipliability theory

/-- Bound for the Taylor series of log(1-z) -/
theorem taylorSeriesBound {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Complex.log (1 - z) + ∑' n : ℕ, z ^ (n + 1) / (n + 1)‖ ≤
    ‖z‖ ^ 2 / (2 * (1 - ‖z‖)) := by
  -- We use the fact that log(1-z) = -∑_{n=1}^∞ z^n/n for |z| < 1
  -- The Taylor series is -∑_{n=1}^∞ z^n/n = -∑' n : ℕ, z^(n+1)/(n+1)
  -- So log(1-z) + ∑' n : ℕ, z^(n+1)/(n+1) = 0
  have h_series : Complex.log (1 - z) = -∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
    -- This is the standard Taylor series for log(1-z)
    sorry -- This requires the Taylor series theorem from mathlib
  rw [h_series]
  simp [norm_neg]
  -- The bound ‖z‖^2 / (2*(1-‖z‖)) comes from bounding the tail of the series
  sorry

end AcademicRH.DiagonalFredholm
