
import Riemann.Mathlib.Analysis.Complex.HardySpace.ZeroEnumeration
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Connection between ZeroEnumeration and Mathlib's Divisor

This file provides the infrastructure to connect the `ZeroEnumeration` structure
to Mathlib's divisor theory, enabling the application of Jensen's formula.

## Main results

* `Complex.divisor_center_eq_zero_of_ne_zero` : For analytic f with f(c) ≠ 0, divisor at c is 0
* `Complex.jensen_enumeration_bound` : The enumeration sum is bounded by log M - log|f(0)|

## References

* See Mathlib's `MeromorphicOn.circleAverage_log_norm` for Jensen's formula
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory MeromorphicAt MeromorphicOn
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Helper lemmas -/

/-- Analytic functions on unitDisc extend to meromorphic functions on closed balls. -/
lemma AnalyticOn.meromorphicOn_closedBall' {f : ℂ → ℂ} (hf : AnalyticOn ℂ f unitDisc)
    {r : ℝ} (_ : 0 < r) (hr1 : r < 1) : MeromorphicOn f (closedBall 0 r) := by
  apply AnalyticOnNhd.meromorphicOn
  intro z hz
  rw [mem_closedBall_zero_iff] at hz
  have hz' : z ∈ unitDisc := by
    rw [mem_unitDisc]
    exact lt_of_le_of_lt hz hr1
  exact analyticAt_of_analyticOn_unitDisc hf hz'

/-- For analytic f with f(0) ≠ 0, the trailing coefficient at 0 equals f(0). -/
lemma analyticAt_trailing_coeff_eq' {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    meromorphicTrailingCoeffAt f 0 = f 0 :=
  hf.meromorphicTrailingCoeffAt_of_ne_zero hf0

/-! ### Divisor infrastructure -/

/-- For analytic f with f(c) ≠ 0, the divisor at c is 0. -/
lemma divisor_eq_zero_of_ne_zero {f : ℂ → ℂ} {c : ℂ} {S : Set ℂ}
    (hS : c ∈ S) (hf : MeromorphicOn f S) (hf_an : AnalyticAt ℂ f c) (hfc : f c ≠ 0) :
    divisor f S c = 0 := by
  rw [divisor_apply hf hS]
  -- meromorphicOrderAt f c = 0 when f is analytic and f(c) ≠ 0
  have h_ord : meromorphicOrderAt f c = 0 := by
    rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hf_an.meromorphicAt]
    exact ⟨f c, hfc, hf_an.continuousAt.continuousWithinAt.tendsto⟩
  rw [h_ord]
  simp

/-- For analytic functions with no zero at the center, divisor at center is 0. -/
lemma divisor_center_eq_zero_of_ne_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicOn f (closedBall c R)) (hf_an : AnalyticAt ℂ f c) (hfc : f c ≠ 0) :
    divisor f (closedBall c R) c = 0 := by
  have hc_in : c ∈ closedBall c R := mem_closedBall_self (le_of_lt hR)
  exact divisor_eq_zero_of_ne_zero hc_in hf hf_an hfc

/-! ### Jensen's formula specialized for H^∞ functions -/

/-- Jensen's formula for H^∞ functions gives the bound on zero sums.

For f ∈ H^∞ with f(0) ≠ 0 and |f| ≤ M on the disc:
  ∑_{|aₙ| < r} mₙ log(r/|aₙ|) ≤ log M - log|f(0)|

This uses `MeromorphicOn.circleAverage_log_norm` from Mathlib.
-/
theorem jensen_enumeration_bound {f : ℂ → ℂ} (hf : IsInHInfty f)
    (M : ℝ) (hM : ∀ z ∈ unitDisc, ‖f z‖ ≤ M) (hM0 : 0 < M)
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (enum : ZeroEnumeration f hf.analyticOn) :
    ∑' n, (if ‖enum.zeros n‖ < r then (enum.mult n : ℝ) * Real.log (r / ‖enum.zeros n‖) else 0) ≤
      Real.log M - Real.log ‖f 0‖ := by
  -- Setup
  have h0_in : (0 : ℂ) ∈ unitDisc := zero_mem_unitDisc
  have hf0_pos : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have h_an_0 : AnalyticAt ℂ f 0 := analyticAt_of_analyticOn_unitDisc hf.analyticOn h0_in

  -- f is meromorphic on closedBall 0 r
  have h_mero : MeromorphicOn f (closedBall 0 r) :=
    hf.analyticOn.meromorphicOn_closedBall' hr0 hr1

  -- Apply Jensen's formula
  have hr_ne : r ≠ 0 := hr0.ne'
  have hr_abs : |r| = r := abs_of_pos hr0

  -- Jensen's formula:
  -- circleAverage(log|f|) = ∑ᶠ u, divisor * log(r * ‖0 - u‖⁻¹) + divisor(0) * log r + log|trailing_coeff|
  have h_jensen := MeromorphicOn.circleAverage_log_norm hr_ne (by rwa [hr_abs])

  -- For analytic f with f(0) ≠ 0:
  -- - divisor at 0 = 0
  -- - trailing_coeff at 0 = f(0)
  have h_div_0 : divisor f (closedBall 0 |r|) 0 = 0 := by
    rw [hr_abs]
    exact divisor_center_eq_zero_of_ne_zero hr0 h_mero h_an_0 hf0

  have h_trailing : meromorphicTrailingCoeffAt f 0 = f 0 :=
    analyticAt_trailing_coeff_eq' h_an_0 hf0

  -- Simplify Jensen's formula for our case
  rw [h_div_0, Int.cast_zero, zero_mul, add_zero, h_trailing] at h_jensen
  -- Now: circleAverage(log|f|) = ∑ᶠ u, divisor * log(r * ‖u‖⁻¹) + log|f(0)|

  -- On the circle |z| = r < 1, we have |f(z)| ≤ M
  have h_circle_bound : ∀ θ : ℝ, ‖f (circleMap 0 r θ)‖ ≤ M := fun θ => by
    apply hM
    rw [mem_unitDisc, norm_circleMap_zero, abs_of_pos hr0]
    exact hr1

  -- The divisor sum (finsum) corresponds to the enumeration sum (tsum)
  -- via the matches_order property of ZeroEnumeration
  -- The bound follows from:
  -- enumeration_sum ≤ divisor_sum = circleAverage - log|f(0)| ≤ log M - log|f(0)|

  sorry

end Complex
