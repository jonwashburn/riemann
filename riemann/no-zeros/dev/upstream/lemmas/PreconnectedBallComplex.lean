import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.PathConnected

/-!
Lemma: open balls in `ℂ` are preconnected (generic Mathlib-style statement).
This is a good upstream candidate when not already covered by an existing lemma.
-/

open Metric

lemma isPreconnected_ball_complex (z : ℂ) (r : ℝ) : IsPreconnected (Metric.ball z r) := by
  -- Convex sets in real topological vector spaces are path connected, hence preconnected
  have hconv : Convex ℝ (Metric.ball z r) := by
    simpa using Metric.convex_ball z r
  exact hconv.isPathConnected.isPreconnected
