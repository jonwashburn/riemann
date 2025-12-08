import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Semicontinuous

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

end MeasureTheory
