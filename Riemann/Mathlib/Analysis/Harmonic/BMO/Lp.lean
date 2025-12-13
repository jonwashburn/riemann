import Riemann.Mathlib.Analysis.Harmonic.BMO.JohnNirenberg

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α] {μ : Measure α}

variable [ProperSpace α] [IsUnifLocDoublingMeasure μ]
variable [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-!
### `L^p` consequences of John–Nirenberg

This file will house the layer-cake / distribution-function machinery needed to deduce
local `L^p` integrability and explicit constants.
-/

/-- BMO functions are locally in `L^p` for every `p < ∞`.

This should be proved from `johnNirenberg_exponential_decay` plus layer-cake formulas.
(We keep the statement in maximal generality: `p : ℝ≥0∞`, `1 ≤ p < ∞`.) -/
theorem bmo_memLp_loc {f : α → ℝ} {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    (hf_loc : LocallyIntegrable f μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {x₀ : α} {r : ℝ} (hr : 0 < r) :
    MemLp f p (μ.restrict (Metric.ball x₀ r)) := by
  -- TODO: layer-cake on `f - f_B`, then add back the constant average.
  sorry

/-- An explicit local `L^p` bound for oscillation on a ball.

This should be proved from the exponential tail bound using distribution formulas,
with constants expressed via `Real.Gamma` (preferred), or a simple explicit upper bound. -/
theorem bmo_Lp_bound {f : α → ℝ} {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    (hf_loc : LocallyIntegrable f μ)
    {p : ℝ} (hp : 1 ≤ p)
    {x₀ : α} {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => f x - ⨍ y in Metric.ball x₀ r, f y ∂μ) (ENNReal.ofReal p)
        (μ.restrict (Metric.ball x₀ r)) ≤
      ENNReal.ofReal (4 * p * M) * μ (Metric.ball x₀ r) ^ (1 / p) := by
  -- TODO: layer-cake with `johnNirenberg_exponential_decay`, then integrate.
  sorry

end MeasureTheory
