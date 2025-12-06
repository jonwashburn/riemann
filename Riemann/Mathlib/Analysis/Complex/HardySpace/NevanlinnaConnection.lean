import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.MinimumModulus
import Riemann.Mathlib.Analysis.Complex.HardySpace.LogIntegrability

/-!
# Connection to Nevanlinna Theory

This file establishes the connection between Hardy space theory and Nevanlinna's
value distribution theory, particularly the proximity function.

## Main definitions

* `Complex.proximityFunction` : The Nevanlinna proximity function m(r, f)

## Main results

* `Complex.IsInHInfty.proximityFunction_bounded` : For H^∞ functions, m(r, f) is bounded
* `Complex.IsInHInfty.proximityFunction_inv_eq` : First Main Theorem identity for nonvanishing f

## References

* Nevanlinna, R., "Analytic Functions"
* Hayman, W.K., "Meromorphic Functions"
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Proximity function -/

/-- The proximity function m(r, f) for Hardy space functions.

This is the average of log⁺|f| on the circle of radius r, measuring how
close f gets to infinity on average. -/
def proximityFunction (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  circleAverage (fun z => log⁺ ‖f z‖) 0 r

/-- For bounded f, the proximity function is bounded.

If |f| ≤ M on the disc, then log⁺|f| ≤ log⁺ M pointwise, hence the
average is bounded by log⁺ M. -/
lemma IsInHInfty.proximityFunction_bounded {f : ℂ → ℂ} (hf : IsInHInfty f) :
    ∃ M : ℝ, ∀ r : ℝ, 0 < r → r < 1 → proximityFunction f r ≤ M := by
  obtain ⟨C, hC⟩ := hf.bounded
  use log⁺ C
  intro r hr0 hr1
  unfold proximityFunction
  have h_subset := closedDisc_subset_unitDisc hr1
  have h_pointwise : ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖f z‖ ≤ log⁺ C := by
    intro z hz
    have hz_disc : z ∈ unitDisc := by
      simp only [mem_unitDisc, Metric.mem_sphere, dist_zero_right, abs_of_pos hr0] at hz ⊢
      rw [hz]; exact hr1
    exact posLog_le_posLog (norm_nonneg _) (hC z hz_disc)
  have hInt : CircleIntegrable (fun z => log⁺ ‖f z‖) 0 r := by
    have hf_cont := hf.continuousOn.mono h_subset
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖f z‖) (closedDisc r) :=
      ValueDistribution.continuous_posLog.comp_continuousOn
        (continuous_norm.comp_continuousOn hf_cont)
    exact Nevanlinna.circleIntegrable_continuous_on_closedBall hr0 h_g_cont
  exact circleAverage_mono_on_of_le_circle hInt h_pointwise

/-- For bounded nonvanishing f, the proximity function of 1/f is related to that of f
by the First Main Theorem identity:
  m(r, 1/f) = m(r, f) - log|f(0)|

This is the elementary case of Nevanlinna's First Main Theorem for meromorphic functions.
-/
lemma IsInHInfty.proximityFunction_inv_eq {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf_ne : ∀ z ∈ unitDisc, f z ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    proximityFunction (fun z => (f z)⁻¹) r =
      proximityFunction f r - Real.log ‖f 0‖ := by
  unfold proximityFunction
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) r ⊆ unitDisc := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz
    simp only [mem_unitDisc]
    exact lt_of_le_of_lt hz hr1
  have hf_ne' : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
  have hf_anNhd : AnalyticOnNhd ℂ f unitDisc := isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf.analyticOn
  have hf_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) := fun z hz => hf_anNhd z (h_subset hz)
  have hf_ne_abs : ∀ z ∈ closedBall (0 : ℂ) |r|, f z ≠ 0 := by rwa [hr_abs]
  have hf_an_abs : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) := by rwa [hr_abs]
  have h_mv := AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hf_an_abs hf_ne_abs
  -- Pointwise identity: log⁺|f⁻¹| = log⁺|f| - log|f| for nonvanishing f
  have h_key : ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖(f z)⁻¹‖ = log⁺ ‖f z‖ - Real.log ‖f z‖ := by
    intro z hz
    have hz_disc : z ∈ unitDisc := by
      simp only [mem_sphere, dist_zero_right, hr_abs] at hz
      simp only [mem_unitDisc, hz, hr1]
    have hfz_ne : f z ≠ 0 := hf_ne z hz_disc
    have hfz_pos : 0 < ‖f z‖ := norm_pos_iff.mpr hfz_ne
    rw [norm_inv]
    have h := Real.posLog_sub_posLog_inv (x := ‖f z‖)
    linarith
  -- Circle integrability
  have h_int_f : CircleIntegrable (fun z => log⁺ ‖f z‖) 0 r := by
    have hf_cont := hf.continuousOn.mono h_subset
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖f z‖) (closedBall (0 : ℂ) r) :=
      ValueDistribution.continuous_posLog.comp_continuousOn
        (continuous_norm.comp_continuousOn hf_cont)
    exact Nevanlinna.circleIntegrable_continuous_on_closedBall hr0 h_g_cont
  have h_int_log : CircleIntegrable (fun z => Real.log ‖f z‖) 0 r :=
    hf.log_norm_circleIntegrable ⟨0, zero_mem_unitDisc, hf_ne 0 zero_mem_unitDisc⟩ hr0 hr1
  have h_int_inv : CircleIntegrable (fun z => log⁺ ‖(f z)⁻¹‖) 0 r := by
    have hf_inv_cont : ContinuousOn (fun z => (f z)⁻¹) (closedBall (0 : ℂ) r) :=
      ContinuousOn.inv₀ (hf.continuousOn.mono h_subset) hf_ne'
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖(f z)⁻¹‖) (closedBall (0 : ℂ) r) :=
      ValueDistribution.continuous_posLog.comp_continuousOn
        (continuous_norm.comp_continuousOn hf_inv_cont)
    exact Nevanlinna.circleIntegrable_continuous_on_closedBall hr0 h_g_cont
  have h_congr : circleAverage (fun z => log⁺ ‖(f z)⁻¹‖) 0 r =
      circleAverage (fun z => log⁺ ‖f z‖ - Real.log ‖f z‖) 0 r :=
    circleAverage_congr_sphere h_key
  have h_avg : circleAverage (fun z => log⁺ ‖f z‖ - Real.log ‖f z‖) 0 r =
      circleAverage (fun z => log⁺ ‖f z‖) 0 r - circleAverage (fun z => Real.log ‖f z‖) 0 r := by
    rw [← circleAverage_sub h_int_f h_int_log]
    rfl
  rw [h_congr, h_avg, h_mv]

end Complex

end
