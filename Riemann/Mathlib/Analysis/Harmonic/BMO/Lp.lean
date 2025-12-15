import Riemann.Mathlib.Analysis.Harmonic.BMO.JohnNirenberg

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α] {μ : Measure α}

variable [ProperSpace α] [IsUnifLocDoublingMeasure μ]
variable [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]


/-!
### `L^p` consequences of John–Nirenberg

Full `L^p` consequences will be proved from John–Nirenberg once the stopping-time step
(`hstep`) is derived from the BMO hypothesis.

For now, we record the basic `L¹` facts that follow directly from local integrability and the
definition of BMO.
-/
omit [BorelSpace α] [IsUnifLocDoublingMeasure μ] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] in
/-- If `f` is locally integrable, then `f ∈ L¹` on every ball. -/
theorem memLp_one_ball_of_locallyIntegrable {f : α → ℝ} (hf_loc : LocallyIntegrable f μ)
    {x₀ : α} {r : ℝ} (_hr : 0 < r) :
    MemLp f (1 : ℝ≥0∞) (μ.restrict (Metric.ball x₀ r)) := by
  -- Integrability on a compact neighborhood, then restrict to the ball.
  have hf_int : IntegrableOn f (Metric.ball x₀ r) μ := by
    -- `closedBall x₀ r` is compact in a proper space.
    have hf_int' : IntegrableOn f (Metric.closedBall x₀ r) μ :=
      hf_loc.integrableOn_isCompact (k := Metric.closedBall x₀ r) (isCompact_closedBall (x := x₀) (r := r))
    exact hf_int'.mono_set Metric.ball_subset_closedBall
  -- Rewrite `MemLp 1` as integrability.
  simpa [MeasureTheory.IntegrableOn, memLp_one_iff_integrable] using hf_int

omit [BorelSpace α] [IsUnifLocDoublingMeasure μ] [μ.IsOpenPosMeasure] in

/-- A basic `L¹` bound for the oscillation on a ball, coming directly from the BMO hypothesis. -/
theorem bmo_L1_oscillation_memLp {f : α → ℝ} {M : ℝ} (_hM : 0 < M)
    (_hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    (hf_loc : LocallyIntegrable f μ)
    {x₀ : α} {r : ℝ} (_hr : 0 < r) :
    MemLp (fun x => f x - ⨍ y in Metric.ball x₀ r, f y ∂μ) (1 : ℝ≥0∞)
      (μ.restrict (Metric.ball x₀ r)) := by
  -- The `L¹` integrability of the oscillation follows from local integrability of `f`.
  have hμB : μ (Metric.ball x₀ r) ≠ ∞ :=
    (measure_ball_lt_top (μ := μ) (x := x₀) (r := r)).ne
  have hf_int : IntegrableOn f (Metric.ball x₀ r) μ := by
    have hf_int' : IntegrableOn f (Metric.closedBall x₀ r) μ :=
      hf_loc.integrableOn_isCompact (k := Metric.closedBall x₀ r) (isCompact_closedBall (x := x₀) (r := r))
    exact hf_int'.mono_set Metric.ball_subset_closedBall
  have hconst : IntegrableOn (fun _x : α => (⨍ y in Metric.ball x₀ r, f y ∂μ)) (Metric.ball x₀ r) μ :=
    integrableOn_const (hs := hμB)
  have hg_int : IntegrableOn (fun x => f x - ⨍ y in Metric.ball x₀ r, f y ∂μ) (Metric.ball x₀ r) μ :=
    hf_int.sub hconst
  simpa [MeasureTheory.IntegrableOn, memLp_one_iff_integrable] using hg_int

end MeasureTheory
