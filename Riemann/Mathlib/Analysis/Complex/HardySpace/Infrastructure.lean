
import Riemann.Mathlib.Analysis.Complex.HardySpace.Basic
import Riemann.Mathlib.Analysis.Complex.HardySpace.PoissonKernel
import Riemann.Mathlib.Analysis.Complex.HardySpace.PowerSeriesBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Infrastructure Lemmas for Hardy Spaces

This file contains the core infrastructure lemmas for Hardy space theory.
These are deep analytical results that support the main theorems.

## Main results

* Helper inequalities for relating Blaschke sums to Jensen sums
* One-sub-conj-mul bounds for Blaschke factor convergence
* Partial log sum bounds
* Basic product convergence infrastructure

## References

* Duren, P.L., "Theory of H^p Spaces"
* Garnett, J.B., "Bounded Analytic Functions"
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Helper inequalities for the disc -/

/-- For |z| ≤ r < 1 and |a| < 1, we have |1 - āz| ≥ 1 - r. -/
lemma one_sub_conj_mul_norm_ge {a z : ℂ} (ha : ‖a‖ < 1) {r : ℝ} (_ : r < 1) (hz : ‖z‖ ≤ r)
    (hr_nn : 0 ≤ r) :
    1 - r ≤ ‖1 - starRingEnd ℂ a * z‖ := by
  have ha_nn : 0 ≤ ‖a‖ := norm_nonneg a
  have h1 : ‖starRingEnd ℂ a * z‖ ≤ ‖a‖ * r := by
    calc ‖starRingEnd ℂ a * z‖ = ‖starRingEnd ℂ a‖ * ‖z‖ := norm_mul _ _
      _ = ‖a‖ * ‖z‖ := by rw [Complex.norm_conj]
      _ ≤ ‖a‖ * r := mul_le_mul_of_nonneg_left hz ha_nn
  have h2 : ‖a‖ * r ≤ r := by
    calc ‖a‖ * r ≤ 1 * r := mul_le_mul_of_nonneg_right (le_of_lt ha) hr_nn
      _ = r := one_mul r
  have h3 : ‖starRingEnd ℂ a * z‖ ≤ r := le_trans h1 h2
  have h4 : 1 - ‖starRingEnd ℂ a * z‖ ≤ ‖1 - starRingEnd ℂ a * z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (starRingEnd ℂ a * z)
    simp only [norm_one] at h
    have h' : 1 - ‖starRingEnd ℂ a * z‖ ≤ |1 - ‖starRingEnd ℂ a * z‖| := le_abs_self _
    linarith
  linarith

/-- For |z| < 1 and |a| < 1, we have 1 - āz ≠ 0. -/
lemma one_sub_conj_mul_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - starRingEnd ℂ a * z ≠ 0 := by
  intro heq
  have h1 : starRingEnd ℂ a * z = 1 := (sub_eq_zero.mp heq).symm
  have h2 : ‖starRingEnd ℂ a * z‖ = 1 := by rw [h1]; simp
  rw [norm_mul, Complex.norm_conj] at h2
  have h3 : ‖a‖ * ‖z‖ < 1 := by nlinarith [norm_nonneg a, norm_nonneg z]
  linarith

/-! ### Re-exports from PowerSeriesBounds for convenience -/

-- The following are already defined in PowerSeriesBounds.lean:
-- * norm_tsum_pow_tail_le
-- * summable_pow_div_succ
-- * Real.tsum_pow_tail_eq
-- * partialLogSum and its bounds

/-! ### Approximate identity property of Poisson kernel -/

/-- Auxiliary: 1 - cos δ > 0 for δ ∈ (0, π]. -/
lemma one_sub_cos_pos_of_pos_of_le_pi {δ : ℝ} (hδ : 0 < δ) (hδ_pi : δ ≤ π) :
    1 - Real.cos δ > 0 := by
  by_cases h2 : δ < π
  · have hcos : Real.cos δ < Real.cos 0 := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (le_of_lt h2) hδ
    simp only [Real.cos_zero] at hcos
    linarith
  · push_neg at h2
    have heq : δ = π := le_antisymm hδ_pi h2
    rw [heq]
    norm_num

/-- The Poisson kernel acts as an approximate identity as r → 1.
This is the key property for proving Fatou's theorem. -/
lemma poissonKernel_approximate_identity {ε : ℝ} (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r₀ : ℝ, r₀ < 1 ∧ ∀ r, r₀ < r → r < 1 → ∀ θ φ,
      δ ≤ |θ - φ| → |θ - φ| ≤ π → poissonKernel r θ φ < ε := by
  set δ' := min δ π with hδ'_def
  have hδ'_pos : δ' > 0 := lt_min hδ pi_pos
  have hδ'_le_pi : δ' ≤ π := min_le_right δ π
  have hδ'_le_δ : δ' ≤ δ := min_le_left δ π
  have h_cos_bound : 1 - Real.cos δ' > 0 := one_sub_cos_pos_of_pos_of_le_pi hδ'_pos hδ'_le_pi
  set c := 1 - Real.cos δ' with hc_def
  have hc : c > 0 := h_cos_bound
  have hpos : 0 < 1 + ε * c := by positivity
  use 1 / (1 + ε * c)
  refine ⟨by rw [div_lt_one hpos]; linarith [mul_pos hε hc], ?_⟩
  intro r hr_lo hr_hi θ φ hδ_le hpi_le
  have hr_pos : 0 < r := lt_trans (by positivity) hr_lo
  have hδ'_le_abs : δ' ≤ |θ - φ| := le_trans hδ'_le_δ hδ_le
  have h_cos_le : Real.cos (θ - φ) ≤ Real.cos δ' := by
    rw [← Real.cos_abs (θ - φ)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi hδ'_pos.le hpi_le hδ'_le_abs
  have h_cos_diff : 1 - Real.cos (θ - φ) ≥ c := by linarith
  have h_denom_lower : 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 ≥ 2 * r * c := by
    have h1 : 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 =
        (1 - r) ^ 2 + 2 * r * (1 - Real.cos (θ - φ)) := by ring
    have h2 : 2 * r * (1 - Real.cos (θ - φ)) ≥ 2 * r * c := by
      have := mul_le_mul_of_nonneg_left h_cos_diff (by linarith : 0 ≤ 2 * r)
      linarith
    nlinarith [sq_nonneg (1 - r)]
  have h_denom_pos' : 2 * r * c > 0 := by positivity
  have hnum : 0 ≤ 1 - r ^ 2 := by
    have hr_sq_lt : r ^ 2 < 1 := by nlinarith
    linarith
  have h_bound : poissonKernel r θ φ ≤ (1 - r ^ 2) / (2 * r * c) := by
    unfold poissonKernel
    exact div_le_div_of_nonneg_left hnum h_denom_pos' h_denom_lower
  have h_final : (1 - r ^ 2) / (2 * r * c) < ε := by
    have h1 : (1 - r ^ 2) ≤ 2 * (1 - r) := by nlinarith
    have h2 : 2 * (1 - r) / (2 * r * c) = (1 - r) / (r * c) := by field_simp
    have h3 : (1 - r ^ 2) / (2 * r * c) ≤ (1 - r) / (r * c) := by
      calc (1 - r ^ 2) / (2 * r * c) ≤ 2 * (1 - r) / (2 * r * c) := by
            apply div_le_div_of_nonneg_right h1 h_denom_pos'.le
        _ = (1 - r) / (r * c) := h2
    have h4 : (1 - r) / (r * c) < ε := by
      rw [div_lt_iff₀ (by positivity : 0 < r * c)]
      have h5 : r * (1 + ε * c) > 1 := by rwa [gt_iff_lt, ← div_lt_iff₀ hpos]
      linarith
    linarith
  linarith

end Complex

end
