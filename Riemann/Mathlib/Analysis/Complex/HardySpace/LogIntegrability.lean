
import Riemann.Mathlib.Analysis.Complex.HardySpace.Basic
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Integrability of log|f| for Hardy Functions

This file establishes the integrability of log|f| on circles for bounded analytic
functions on the unit disc.

## Main results

* `Complex.IsInHInfty.log_norm_circleIntegrable` : log|f| is integrable on circles
* `Complex.IsInHInfty.log_norm_continuousOn_of_ne_zero` : log|f| is continuous when f ≠ 0
* `Complex.IsInHInfty.jensen_inequality` : Jensen's inequality for H^∞ functions
* `Complex.IsInHInfty.circleAverage_log_norm_eq` : Mean value property for nonvanishing f

## References

* Duren, P.L., "Theory of H^p Spaces", Chapter 2
* Mathlib's `Mathlib.Analysis.Complex.JensenFormula`
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Circle integrability of log|f| -/

/-- For a bounded analytic function that is not identically zero,
log|f| is integrable on every circle of radius r < 1.

This uses the fact that analytic functions on connected open sets are meromorphic,
and log|f| is integrable for meromorphic functions (logarithmic singularities are integrable).
-/
lemma IsInHInfty.log_norm_circleIntegrable {f : ℂ → ℂ} (hf : IsInHInfty f)
    (_ : ∃ z ∈ unitDisc, f z ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    CircleIntegrable (fun z => Real.log ‖f z‖) 0 r := by
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz
    simp only [mem_unitDisc]
    calc ‖z‖ ≤ |r| := hz
      _ = r := hr_abs
      _ < 1 := hr1
  have hf_anNhd : AnalyticOnNhd ℂ f unitDisc := isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf.analyticOn
  have hf_merom : MeromorphicOn f (closedBall (0 : ℂ) |r|) := fun z hz =>
    (hf_anNhd z (h_subset hz)).meromorphicAt
  have h_sphere_subset : sphere (0 : ℂ) |r| ⊆ closedBall (0 : ℂ) |r| := sphere_subset_closedBall
  have hf_merom_sphere : MeromorphicOn f (sphere (0 : ℂ) |r|) := fun z hz => hf_merom z (h_sphere_subset hz)
  exact circleIntegrable_log_norm_meromorphicOn hf_merom_sphere

/-- For a bounded analytic nonvanishing function,
log|f| is continuous on the closed disc. -/
lemma IsInHInfty.log_norm_continuousOn_of_ne_zero {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf_ne : ∀ z ∈ unitDisc, f z ≠ 0) {r : ℝ} (hr1 : r < 1) :
    ContinuousOn (fun z => Real.log ‖f z‖) (closedDisc r) := by
  have h_subset := closedDisc_subset_unitDisc hr1
  have hf_cont := hf.continuousOn.mono h_subset
  have hf_ne' : ∀ z ∈ closedDisc r, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
  exact ContinuousOn.log (continuous_norm.comp_continuousOn hf_cont)
    (fun z hz => (norm_pos_iff.mpr (hf_ne' z hz)).ne')

/-! ### Jensen's inequality -/

/-- Jensen's inequality: for f ∈ H^∞ with f(0) ≠ 0,
log|f(0)| ≤ circleAverage (log|f|) 0 r for all r < 1.

This is a consequence of Jensen's formula: for analytic f, the circle average of log|f|
equals log|f(0)| plus a nonnegative contribution from zeros. -/
lemma IsInHInfty.jensen_inequality {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.log ‖f 0‖ ≤ circleAverage (fun z => Real.log ‖f z‖) 0 r := by
  have hr_ne : r ≠ 0 := ne_of_gt hr0
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz
    simp only [mem_unitDisc]
    calc ‖z‖ ≤ |r| := hz
      _ = r := hr_abs
      _ < 1 := hr1
  have hf_anNhd : AnalyticOnNhd ℂ f unitDisc := isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf.analyticOn
  have hf_merom : MeromorphicOn f (closedBall (0 : ℂ) |r|) := fun z hz =>
    (hf_anNhd z (h_subset hz)).meromorphicAt
  have hJ := MeromorphicOn.circleAverage_log_norm hr_ne hf_merom
  have hf_an_0 : AnalyticAt ℂ f 0 := hf_anNhd 0 zero_mem_unitDisc
  have h_trailing : meromorphicTrailingCoeffAt f 0 = f 0 :=
    AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero hf_an_0 hf0
  rw [hJ, h_trailing]
  have hf_an_ball : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) := fun z hz => hf_anNhd z (h_subset hz)
  have h_div_0_term : (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) 0 : ℤ) * Real.log r = 0 := by
    have h0_mem : (0 : ℂ) ∈ closedBall (0 : ℂ) |r| := by simp [hr_abs, hr0.le]
    rw [MeromorphicOn.divisor_apply hf_an_ball.meromorphicOn h0_mem]
    have hf_an_0' : AnalyticAt ℂ f 0 := hf_an_ball 0 h0_mem
    have h_order_0 : meromorphicOrderAt f 0 = 0 := by
      rw [hf_an_0'.meromorphicOrderAt_eq]
      simp [hf_an_0'.analyticOrderAt_eq_zero.mpr hf0]
    simp [h_order_0]
  have h_finsum_nonneg : 0 ≤ ∑ᶠ u, ↑(MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) u) *
      Real.log (r * ‖0 - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |r|
    · have h_div_u_nonneg : 0 ≤ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) u : ℤ) := by
        rw [MeromorphicOn.divisor_apply hf_an_ball.meromorphicOn hu]
        have h_ord := (hf_an_ball u hu).meromorphicOrderAt_nonneg
        exact WithTop.untop₀_nonneg.mpr h_ord
      have h_log_nonneg : 0 ≤ Real.log (r * ‖0 - u‖⁻¹) := by
        by_cases hu_zero : u = 0
        · simp only [hu_zero, sub_zero, norm_zero, inv_zero, mul_zero, Real.log_zero, le_refl]
        · have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu_zero
          have hu_in : ‖u‖ ≤ r := by simp only [mem_closedBall, dist_zero_right, hr_abs] at hu; exact hu
          have h_eq : ‖0 - u‖ = ‖u‖ := by simp
          rw [h_eq]
          apply Real.log_nonneg
          calc 1 = r * r⁻¹ := by field_simp
            _ ≤ r * ‖u‖⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hu_norm hu_in) hr0.le
      exact mul_nonneg (Int.cast_nonneg h_div_u_nonneg) h_log_nonneg
    · simp only [MeromorphicOn.divisor_def, hf_an_ball.meromorphicOn, hu, and_false, ite_false,
        Int.cast_zero, zero_mul, le_refl]
  linarith [h_div_0_term, h_finsum_nonneg]

/-! ### Mean value property -/

/-- For analytic nonvanishing f, the circle average of log|f| equals log|f(0)|.
This is the mean value property for harmonic functions (log|f| is harmonic when f ≠ 0). -/
lemma IsInHInfty.circleAverage_log_norm_eq {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf_ne : ∀ z ∈ unitDisc, f z ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    circleAverage (fun z => Real.log ‖f z‖) 0 r = Real.log ‖f 0‖ := by
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz
    simp only [mem_unitDisc]
    calc ‖z‖ ≤ |r| := hz
      _ = r := hr_abs
      _ < 1 := hr1
  have hf_ne' : ∀ z ∈ closedBall (0 : ℂ) |r|, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
  have hf_anNhd : AnalyticOnNhd ℂ f unitDisc := isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf.analyticOn
  have hf_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) := fun z hz => hf_anNhd z (h_subset hz)
  exact AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hf_an hf_ne'

end Complex

end
