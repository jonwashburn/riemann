import Riemann.Mathlib.Analysis.Harmonic.BMO.Defs
import Riemann.Mathlib.MeasureTheory.Covering.CalderonZygmund
import Riemann.Mathlib.MeasureTheory.Covering.JohnNirenberg
import Riemann.Mathlib.Analysis.Harmonic.BMOAux

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

 variable {α : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α] {μ : Measure α}

/-!
### John–Nirenberg inequality

This file is intended to contain the *nontrivial* John–Nirenberg exponential decay for BMO.

We keep the assumptions split so that later we can provide both:
- a **local-doubling** version (using `IsUnifLocDoublingMeasure`), and
- a **global-doubling** version (using `MeasureTheory.Measure.IsDoubling` from the Carleson library).
-/

variable [ProperSpace α] [IsUnifLocDoublingMeasure μ]
variable [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- **John–Nirenberg inequality**: exponential decay of the distribution function.

For a function `f` with bounded mean oscillation ≤ `M` on all balls, the superlevel sets
of `|f - f_B|` decay exponentially.

The constant is expressed in the canonical form with `Real.log 2` in the exponent.

(Implementation note: the proof is split across auxiliary lemmas in the surrounding covering/CZ API.) -/
theorem johnNirenberg_exponential_decay {f : α → ℝ} {x₀ : α} {r : ℝ} (hr : 0 < r)
    {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    {t : ℝ} (ht : 0 < t) :
    μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > t} ≤
      2 * μ (Metric.ball x₀ r) *
        ENNReal.ofReal (Real.exp (-(Real.log 2) * t / (2 * M))) := by
  -- TODO: implement via CZ/Vitali iteration step + geometric decay at linear thresholds.
  sorry

end MeasureTheory
