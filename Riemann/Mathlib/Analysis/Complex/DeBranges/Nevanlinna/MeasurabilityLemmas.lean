
import Mathlib
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.PosLogLemmas

/-!
# Measurability lemmas for Nevanlinna theory

This file provides measurability and strong measurability lemmas needed for
circle integrals and averages in value distribution theory.

## Main results

* `aestronglyMeasurable_of_continuous_on_disc` : Analytic functions on the disc
  compose with `circleMap` to give continuous (hence strongly measurable) functions.
* `circleIntegrable_of_bounded` : Bounded functions on the circle are integrable.

These support the `proximity_bounded` and related lemmas in the Nevanlinna theory.
-/

open MeasureTheory Filter Topology Set Real Complex

namespace Complex

variable {G : ℂ → ℂ}

/-! ### Strong measurability for compositions with circleMap -/

/-- If `G` is continuous on the closed ball of radius `r`, then the composition
    `θ ↦ G (circleMap 0 r θ)` is continuous, hence strongly measurable. -/
lemma continuousOn_closedBall_comp_circleMap {r : ℝ} (hr : 0 ≤ r)
    (hG : ContinuousOn G (Metric.closedBall 0 r)) :
    Continuous (fun θ : ℝ => G (circleMap 0 r θ)) := by
  apply ContinuousOn.comp_continuous hG (continuous_circleMap 0 r)
  intro θ
  simp only [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_nonneg hr]
  exact le_refl r

/-- For analytic `G` on the open unit disc and `r < 1`, the composition
    `θ ↦ G (circleMap 0 r θ)` is continuous. -/
lemma continuous_comp_circleMap_of_analyticOn {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hG : AnalyticOn ℂ G {z | ‖z‖ < 1}) :
    Continuous (fun θ : ℝ => G (circleMap 0 r θ)) := by
  -- The circle of radius r is contained in the open unit disc.
  have h_subset : Metric.closedBall (0 : ℂ) r ⊆ {z | ‖z‖ < 1} := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [mem_setOf_eq]
    exact lt_of_le_of_lt hz hr1
  -- G is analytic on a neighborhood of every point in the closed ball.
  have hG_cont : ContinuousOn G (Metric.closedBall 0 r) := by
    apply ContinuousOn.mono _ h_subset
    exact hG.continuousOn
  exact continuousOn_closedBall_comp_circleMap (le_of_lt hr0) hG_cont

/-- The composition `θ ↦ log⁺ ‖G (circleMap 0 r θ)‖` is continuous when G is
    analytic on the disc and r < 1. -/
lemma continuous_posLog_norm_comp_circleMap {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hG : AnalyticOn ℂ G {z | ‖z‖ < 1}) :
    Continuous (fun θ : ℝ => log⁺ ‖G (circleMap 0 r θ)‖) := by
  have h1 : Continuous (fun θ => G (circleMap 0 r θ)) :=
    continuous_comp_circleMap_of_analyticOn hr0 hr1 hG
  have h2 : Continuous (fun θ => ‖G (circleMap 0 r θ)‖) := continuous_norm.comp h1
  exact Real.continuous_posLog'.comp h2

/-- For bounded analytic G, the composition `θ ↦ log⁺ ‖G (circleMap 0 r θ)‖`
    is aestronglyMeasurable on the interval measure. -/
lemma aestronglyMeasurable_posLog_norm_comp_circleMap {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hG : AnalyticOn ℂ G {z | ‖z‖ < 1}) :
    AEStronglyMeasurable (fun θ : ℝ => log⁺ ‖G (circleMap 0 r θ)‖)
      (volume.restrict (Set.uIoc 0 (2 * π))) := by
  exact (continuous_posLog_norm_comp_circleMap hr0 hr1 hG).aestronglyMeasurable

/-! ### Circle integrability for bounded functions -/

/-- A continuous function on the circle is circle integrable. -/
lemma circleIntegrable_of_continuous {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf_cont : Continuous (fun θ => f (circleMap c R θ))) :
    CircleIntegrable f c R := by
  unfold CircleIntegrable
  exact hf_cont.intervalIntegrable 0 (2 * π)

/-- For analytic G on the disc and r < 1, the function `log⁺ ‖G ·‖`
    is circle integrable on the circle of radius r. -/
lemma circleIntegrable_posLog_norm_of_analyticOn {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hG : AnalyticOn ℂ G {z | ‖z‖ < 1}) :
    CircleIntegrable (fun z => log⁺ ‖G z‖) 0 r := by
  apply circleIntegrable_of_continuous
  exact continuous_posLog_norm_comp_circleMap hr0 hr1 hG

end Complex
