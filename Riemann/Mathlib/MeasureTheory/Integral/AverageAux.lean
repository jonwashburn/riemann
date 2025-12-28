import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.Topology.MetricSpace.Basic

/-!
# Auxiliary Lemmas for Averages and Lower Semicontinuity

This file contains auxiliary lemmas relating Bochner averages to laverage and
lower semicontinuity of compositions with `toReal`.

## Main Results

* `average_abs_eq_laverage_enorm_toReal` - The Bochner average of |f| equals
  the toReal of the laverage of ‖f‖ₑ
* `ENNReal.lowerSemicontinuous_toReal_of_lt_top` - If f is lower semicontinuous
  and finite everywhere, then toReal ∘ f is lower semicontinuous

-/

open MeasureTheory MeasureTheory.Measure Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology

namespace ENNReal

/-- If f is lower semicontinuous and finite everywhere, then toReal ∘ f is
lower semicontinuous.

The proof uses that for c > 0, {y | c < (f y).toReal} = {y | ofReal c < f y},
and for c < 0, the set is all of X since toReal ≥ 0. -/
theorem lowerSemicontinuous_toReal_of_lt_top {X : Type*} [TopologicalSpace X]
    {f : X → ℝ≥0∞} (hf : LowerSemicontinuous f) (hfin : ∀ x, f x ≠ ⊤) :
    LowerSemicontinuous (fun x => (f x).toReal) := by
  intro x c hc
  by_cases hc0 : c < 0
  · -- If c < 0, the inequality is trivial since toReal ≥ 0 > c
    filter_upwards with y
    have h := toReal_nonneg (a := f y)
    linarith
  push_neg at hc0
  -- Now c ≥ 0, so we use that f is lower semicontinuous
  have hfx_pos : 0 < (f x).toReal := lt_of_le_of_lt hc0 hc
  have hc' : ENNReal.ofReal c < f x := by
    rw [← ENNReal.ofReal_toReal (hfin x)]
    exact (ENNReal.ofReal_lt_ofReal_iff hfx_pos).mpr hc
  filter_upwards [hf x (ENNReal.ofReal c) hc'] with y hy
  have hy_fin : f y ≠ ⊤ := hfin y
  rw [← ENNReal.toReal_ofReal hc0]
  exact (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hy_fin).mpr hy

end ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- The Bochner average of |f| equals the toReal of the laverage of ‖f‖ₑ,
when f is integrable on s. -/
theorem average_abs_eq_laverage_enorm_toReal {f : α → ℝ}
    (hf : IntegrableOn f s μ) :
    ⨍ x in s, |f x| ∂μ = (⨍⁻ x in s, ‖f x‖ₑ ∂μ).toReal := by
  -- For real numbers, |f x| = ‖f x‖ and the integral equals the lintegral.toReal
  have habs_int : IntegrableOn (fun x => |f x|) s μ := hf.norm
  have hint_eq : ∫ x in s, |f x| ∂μ = (∫⁻ x in s, ‖f x‖ₑ ∂μ).toReal := by
    have h := integral_norm_eq_lintegral_enorm habs_int.aestronglyMeasurable
    simp only [Real.norm_eq_abs, abs_abs] at h
    convert h using 2 with x
    simp only [Real.enorm_eq_ofReal_abs, abs_abs]
  rw [average_eq, laverage_eq, smul_eq_mul, hint_eq]
  simp only [Measure.restrict_apply_univ, measureReal_def]
  rw [ENNReal.toReal_div]
  ring

/-! ## Measure ratio bounds for nested balls

For uniformly locally doubling measures, we can bound the ratio of measures of
nested balls. The key API is `measure_mul_le_scalingConstantOf_mul` which gives:

  μ(closedBall x (t * r)) ≤ scalingConstantOf μ K * μ(closedBall x r)

for t ∈ (0, K] and r ≤ scalingScaleOf μ K.

We provide variants for open balls and different hypotheses.
-/

section MeasureRatio

open Metric

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [IsUnifLocDoublingMeasure μ]

omit [BorelSpace X] in
/-- For concentric closed balls, the measure ratio is bounded by the scaling constant.
This is the core bound from which other variants follow.

For r ≤ scalingScaleOf μ K and t ∈ (0, K]:
  μ(closedBall x (t * r)) ≤ scalingConstantOf μ K * μ(closedBall x r) -/
lemma measure_closedBall_le_scalingConstantOf_mul {x : X} {r K : ℝ}
    (hK : 0 < K) (hr_scale : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ K) :
    μ (closedBall x (K * r)) ≤
      IsUnifLocDoublingMeasure.scalingConstantOf μ K * μ (closedBall x r) := by
  have hK_mem : K ∈ Set.Ioc 0 K := Set.mem_Ioc.mpr ⟨hK, le_refl K⟩
  exact @IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul X _ _ μ _ K x K r hK_mem hr_scale

omit [BorelSpace X] in
/-- For nested closed balls (with the same center), the measure ratio is controlled.
This version works for small radii (r ≤ scalingScaleOf). -/
lemma measure_closedBall_ratio_le_scalingConstantOf {x : X} {r r₀ : ℝ}
    (hr : 0 < r) (hr₀ : 0 < r₀)
    (hr_scale : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (r₀ / r)) :
    μ (closedBall x r₀) ≤
      IsUnifLocDoublingMeasure.scalingConstantOf μ (r₀ / r) * μ (closedBall x r) := by
  have hK : 0 < r₀ / r := div_pos hr₀ hr
  have hK_mem : (r₀ / r) ∈ Set.Ioc 0 (r₀ / r) := Set.mem_Ioc.mpr ⟨hK, le_refl _⟩
  have hr₀_eq : r₀ = (r₀ / r) * r := by field_simp
  conv_lhs => rw [hr₀_eq]
  exact @IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul X _ _ μ _ (r₀/r) x (r₀/r) r hK_mem hr_scale

omit [BorelSpace X] in
/-- For nested balls B(x, r) ⊆ B(x₀, r₀), the larger ball's measure is bounded.

**Geometric insight**: If ball x r ⊆ ball x₀ r₀, then x ∈ ball x₀ r₀, so dist(x, x₀) < r₀.
By triangle inequality, ball x₀ r₀ ⊆ closedBall x (2r₀).

For small radii (r ≤ scalingScaleOf μ (2r₀/r)), we get:
  μ(ball x₀ r₀) ≤ scalingConstantOf μ (2r₀/r) * μ(closedBall x r)

Note: The RHS uses closedBall because that's what the doubling API provides. -/
lemma measure_ball_le_scalingConstantOf_mul_closedBall {x x₀ : X} {r r₀ : ℝ}
    (hr : 0 < r) (hr₀ : 0 < r₀) (h : ball x r ⊆ ball x₀ r₀)
    (hr_scale : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (2 * r₀ / r)) :
    μ (ball x₀ r₀) ≤
      IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * r₀ / r) * μ (closedBall x r) := by
  -- x ∈ ball x₀ r₀ from the containment
  have hx_in : x ∈ ball x₀ r₀ := h (mem_ball_self hr)
  have hdist : dist x x₀ < r₀ := mem_ball.mp hx_in
  -- ball x₀ r₀ ⊆ closedBall x (2r₀) by triangle inequality
  have hcontain : ball x₀ r₀ ⊆ closedBall x (2 * r₀) := by
    intro y hy
    rw [mem_ball] at hy
    rw [mem_closedBall]
    have hdist' : dist x₀ x < r₀ := by rw [dist_comm]; exact hdist
    have h1 : dist y x ≤ dist y x₀ + dist x₀ x := dist_triangle y x₀ x
    have h2 : dist y x₀ + dist x₀ x < r₀ + r₀ := by linarith [hy]
    linarith
  -- Apply the doubling bound
  set K := 2 * r₀ / r with hK_def
  have hK : 0 < K := by positivity
  have h2r₀ : 2 * r₀ = K * r := by simp only [hK_def]; field_simp [hr.ne']
  have hr_scale' : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ K := by
    simp only [hK_def] at hr_scale ⊢; exact hr_scale
  calc μ (ball x₀ r₀)
      ≤ μ (closedBall x (2 * r₀)) := measure_mono hcontain
    _ = μ (closedBall x (K * r)) := by rw [h2r₀]
    _ ≤ IsUnifLocDoublingMeasure.scalingConstantOf μ K * μ (closedBall x r) :=
        measure_closedBall_le_scalingConstantOf_mul (x := x) hK hr_scale'

end MeasureRatio

end MeasureTheory
