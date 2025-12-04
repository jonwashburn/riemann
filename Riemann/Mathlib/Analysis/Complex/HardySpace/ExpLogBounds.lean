
import Riemann.Mathlib.Analysis.Complex.HardySpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exponential and Logarithm Bounds

Fundamental inequalities for exp and log needed for product convergence
in the theory of Hardy spaces and Blaschke products.

## Main results

* `Real.hasDerivAt_one_sub_mul_exp` : The derivative of (1-t)·exp(t)
* `Real.strictAntiOn_one_sub_mul_exp` : (1-t)·exp(t) is strictly decreasing on [0, ∞)
* `Real.one_sub_mul_exp_lt_one` : For x > 0, (1-x)·exp(x) < 1
* `Real.exp_lt_one_div_one_sub` : For 0 < x < 1, exp(x) < 1/(1-x)
* `Complex.norm_exp_sub_one_le_general` : |exp(w) - 1| ≤ |w|·exp(|w|)

## References

* Standard complex analysis texts on product convergence
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Derivative and monotonicity of (1-t)·exp(t) -/

/-- The function g(t) = (1-t) * exp(t) has derivative -t * exp(t). -/
lemma Real.hasDerivAt_one_sub_mul_exp (t : ℝ) :
    HasDerivAt (fun s => (1 - s) * Real.exp s) (-t * Real.exp t) t := by
  have h1 : HasDerivAt (fun s => 1 - s) (-1) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have h2 : HasDerivAt Real.exp (Real.exp t) t := Real.hasDerivAt_exp t
  convert h1.mul h2 using 1
  ring

/-- The function g(t) = (1-t) * exp(t) is strictly decreasing on [0, ∞). -/
lemma Real.strictAntiOn_one_sub_mul_exp :
    StrictAntiOn (fun t => (1 - t) * Real.exp t) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · exact ((continuous_const.sub continuous_id).mul Real.continuous_exp).continuousOn
  · intro x hx
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at hx
    rw [(Real.hasDerivAt_one_sub_mul_exp x).deriv]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hx) (Real.exp_pos x)

/-- For x > 0, we have (1-x) * exp(x) < 1. -/
lemma Real.one_sub_mul_exp_lt_one {x : ℝ} (hx : 0 < x) : (1 - x) * Real.exp x < 1 := by
  have h0 : (1 - (0 : ℝ)) * Real.exp 0 = 1 := by simp
  have h_mem_0 : (0 : ℝ) ∈ Ici 0 := left_mem_Ici
  have h_mem_x : x ∈ Ici 0 := le_of_lt hx
  calc (1 - x) * Real.exp x < (1 - 0) * Real.exp 0 :=
        Real.strictAntiOn_one_sub_mul_exp h_mem_0 h_mem_x hx
    _ = 1 := h0

/-- For 0 < x < 1, we have exp(x) < 1/(1-x).

This follows from (1-x)*exp(x) < 1 for x > 0, which is proved using
the fact that g(t) = (1-t)*exp(t) is strictly decreasing (g'(t) = -t*exp(t) < 0). -/
lemma Real.exp_lt_one_div_one_sub {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.exp x < 1 / (1 - x) := by
  have h1mx_pos : 0 < 1 - x := by linarith
  rw [lt_div_iff₀ h1mx_pos, mul_comm]
  exact Real.one_sub_mul_exp_lt_one hx0

/-! ### Complex exponential bounds -/

/-- The derivative of t ↦ exp(t • w) is w * exp(t • w). -/
lemma hasDerivAt_exp_smul (w : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • w)) (w * exp (t • w)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) • w) w t := by
    have := hasDerivAt_id t
    convert HasDerivAt.smul_const this w
    simp
  have h2 : HasDerivAt exp (exp (t • w)) ((t : ℂ) • w) :=
    hasDerivAt_exp _
  convert HasDerivAt.comp t h2 h1 using 1
  ring

/-- Bound on |exp(t • w)| for t ∈ [0, 1]: |exp(t • w)| ≤ exp(|w|). -/
lemma norm_exp_smul_le {w : ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖exp (t • w)‖ ≤ Real.exp ‖w‖ := by
  rw [norm_exp]
  apply Real.exp_le_exp_of_le
  simp only [smul_re]
  calc t * w.re ≤ t * |w.re| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0
    _ ≤ 1 * |w.re| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
    _ = |w.re| := one_mul _
    _ ≤ ‖w‖ := abs_re_le_norm w

/-- General exponential bound: |exp(w) - 1| ≤ |w| · exp(|w|).

This is a fundamental estimate for product convergence. The proof uses the
integral representation exp(w) - 1 = ∫₀¹ w · exp(t·w) dt from FTC. -/
lemma norm_exp_sub_one_le_general (w : ℂ) : ‖exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  by_cases hw : w = 0
  · simp [hw]
  · have h_deriv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => exp (s • w))
        (w * exp (t • w)) t := fun t _ => hasDerivAt_exp_smul w t
    have h_cont : Continuous (fun t : ℝ => w * exp (t • w)) :=
      continuous_const.mul (continuous_exp.comp (continuous_ofReal.smul continuous_const))
    have h_int : IntervalIntegrable (fun t => w * exp (t • w)) volume 0 1 :=
      h_cont.intervalIntegrable 0 1
    have h_ftc : ∫ t in (0 : ℝ)..1, w * exp (t • w) =
        exp ((1 : ℝ) • w) - exp ((0 : ℝ) • w) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
    simp only [one_smul, zero_smul, exp_zero] at h_ftc
    have h_bound : ∀ t ∈ Icc (0 : ℝ) 1, ‖w * exp (t • w)‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
      intro t ht
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
      exact norm_exp_smul_le ht.1 ht.2
    calc ‖exp w - 1‖ = ‖∫ t in (0:ℝ)..1, w * exp (t • w)‖ := by rw [h_ftc]
      _ ≤ ∫ t in (0:ℝ)..1, ‖w * exp (t • w)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith : (0:ℝ) ≤ 1)
      _ ≤ ∫ t in (0:ℝ)..1, ‖w‖ * Real.exp ‖w‖ := by
          apply intervalIntegral.integral_mono_on (by linarith : (0:ℝ) ≤ 1)
          · exact h_cont.norm.intervalIntegrable 0 1
          · exact continuous_const.intervalIntegrable 0 1
          · exact h_bound
      _ = ‖w‖ * Real.exp ‖w‖ := by simp

/-- For small |w|, |exp(w) - 1| ≤ 2|w|.

This follows from |exp(w) - 1| ≤ |w| · exp(|w|) and exp(1/2) < 2. -/
lemma norm_exp_sub_one_le_two_mul' {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖exp w - 1‖ ≤ 2 * ‖w‖ := by
  have h_exp_half_lt_two : Real.exp (1/2 : ℝ) < 2 := by
    have h_bound : Real.exp (1/2 : ℝ) < 1 / (1 - 1/2) :=
      Real.exp_lt_one_div_one_sub (by linarith : (0:ℝ) < 1/2) (by linarith : (1:ℝ)/2 < 1)
    calc Real.exp (1/2) < 1 / (1 - 1/2) := h_bound
      _ = 2 := by norm_num
  calc ‖exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := norm_exp_sub_one_le_general w
    _ ≤ ‖w‖ * Real.exp (1/2) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
        exact Real.exp_le_exp_of_le hw
    _ ≤ ‖w‖ * 2 := by
        apply mul_le_mul_of_nonneg_left (le_of_lt h_exp_half_lt_two) (norm_nonneg w)
    _ = 2 * ‖w‖ := by ring

end Complex
