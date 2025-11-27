/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization Team
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.MeasureTheory.Integral.CircleAverage
import Riemann.Mathlib.Analysis.Complex.Cartan

/-!
# Minimum Modulus Principle for Analytic Functions

This file provides the minimum modulus principle and related lemmas for
analytic functions, which are essential for Nevanlinna theory.

## Main results

* `norm_pos_of_ne_zero_on_compact` : Analytic nonvanishing function has
  positive norm on compact sets
* `posLog_inv_bounded_on_compact` : log⁺ |1/f| is bounded on compact subsets

## References

* Conway, J.B., "Functions of One Complex Variable I", Chapter IV
* Rudin, W., "Real and Complex Analysis", Chapter 12
-/

open Complex Set Metric Filter Topology Real MeasureTheory

namespace Nevanlinna

variable {f : ℂ → ℂ} {s : Set ℂ} {r : ℝ}

/-! ### Basic inequalities -/

/-- The inverse of an inequality: if a ≤ b and a > 0, then b⁻¹ ≤ a⁻¹. -/
lemma inv_anti_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ := by
  by_cases hb : b = 0
  · simp [hb, inv_nonneg.mpr (le_of_lt ha)]
  · have hb_pos : 0 < b := lt_of_lt_of_le ha hab
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le ha hab

/-! ### Minimum modulus principle -/

/-- An analytic nonzero function on a compact set has norm bounded away from zero.
    This is a consequence of the fact that continuous functions on compact sets
    attain their extrema, and analytic nonzero functions are continuous. -/
lemma norm_pos_of_ne_zero_on_compact
    {K : Set ℂ} (hK : IsCompact K) (hK_ne : K.Nonempty)
    (hf_cont : ContinuousOn f K) (hne : ∀ z ∈ K, f z ≠ 0) :
    ∃ δ > 0, ∀ z ∈ K, δ ≤ ‖f z‖ := by
  -- The function |f| is continuous on K
  have h_norm_cont : ContinuousOn (fun z => ‖f z‖) K :=
    continuous_norm.comp_continuousOn hf_cont
  -- On a nonempty compact set, a continuous function attains its infimum
  obtain ⟨z₀, hz₀K, hz₀_min⟩ := hK.exists_isMinOn hK_ne h_norm_cont
  -- The minimum value is positive since f(z₀) ≠ 0
  have hf_z₀ : f z₀ ≠ 0 := hne z₀ hz₀K
  have h_pos : 0 < ‖f z₀‖ := norm_pos_iff.mpr hf_z₀
  use ‖f z₀‖, h_pos
  intro z hz
  exact hz₀_min hz

/-- For a continuous function nonzero on the closed ball of radius `r`,
    the minimum modulus is positive. -/
lemma minNorm_closedBall_pos
    (hf_cont : ContinuousOn f (closedBall (0 : ℂ) r))
    (hne : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0) (hr : 0 ≤ r) :
    ∃ δ > 0, ∀ z ∈ closedBall (0 : ℂ) r, δ ≤ ‖f z‖ := by
  apply norm_pos_of_ne_zero_on_compact (isCompact_closedBall 0 r)
    (nonempty_closedBall.mpr hr) hf_cont hne

/-- For continuous `f` nonzero on the closed ball, `log⁺ ‖f⁻¹‖` is bounded on the sphere. -/
lemma posLog_inv_norm_bounded_on_sphere
    (hf_cont : ContinuousOn f (closedBall (0 : ℂ) r))
    (hne : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0) (hr : 0 ≤ r) :
    ∃ M : ℝ, ∀ z ∈ sphere (0 : ℂ) r, log⁺ ‖(f z)⁻¹‖ ≤ M := by
  -- Get the minimum modulus δ on the closed ball
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := minNorm_closedBall_pos hf_cont hne hr
  -- On the sphere (⊆ closed ball), |f| ≥ δ, so |f⁻¹| ≤ 1/δ
  use log⁺ δ⁻¹
  intro z hz
  have hz_cb : z ∈ closedBall (0 : ℂ) r := sphere_subset_closedBall hz
  have h_norm_bound : δ ≤ ‖f z‖ := hδ_bound z hz_cb
  have h_inv_bound : ‖(f z)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact inv_anti_of_pos hδ_pos h_norm_bound
  exact posLog_le_posLog (norm_nonneg _) h_inv_bound

/-! ### Circle average bounds for inverse functions -/

/-- For a function continuous and nonzero on the disc, the circle average of
    `log⁺ ‖f⁻¹‖` on radius `r` is bounded by the bound on `log⁺ ‖f⁻¹‖`. -/
lemma circleAverage_posLog_inv_le_of_bounded
    (hf_cont : ContinuousOn f (closedBall (0 : ℂ) r))
    (hne : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0) (hr : 0 ≤ r) :
    ∃ M : ℝ, circleAverage (fun z => log⁺ ‖(f z)⁻¹‖) 0 r ≤ M := by
  obtain ⟨M, hM⟩ := posLog_inv_norm_bounded_on_sphere hf_cont hne hr
  use M
  -- The circle average of a function bounded by M is at most M
  -- This follows from: circleAverage f ≤ sup_sphere f ≤ M
  --
  -- For a nonnegative function bounded pointwise by M, its average is ≤ M.
  -- The proof uses that the average of a constant M is M.
  by_cases hr0 : r = 0
  · -- When r = 0, the circle is a single point
    subst hr0
    simp only [circleAverage_zero]
    exact hM 0 (by simp [sphere_zero])
  · -- When r ≠ 0, use that pointwise bound implies average bound
    have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    -- The function is bounded by M on the sphere
    have h_sphere_bound : ∀ θ : ℝ, log⁺ ‖(f (circleMap 0 r θ))⁻¹‖ ≤ M := by
      intro θ
      have h_mem : circleMap 0 r θ ∈ sphere (0 : ℂ) r := by
        simp only [mem_sphere_zero_iff_norm, norm_circleMap_zero, abs_of_pos hr_pos]
      exact hM _ h_mem
    -- The circle average of a nonnegative function bounded by M is at most M.
    -- Mathematical argument:
    -- circleAverage g 0 r = (2π)⁻¹ * ∫ θ in 0..2π, g(circleMap 0 r θ)
    -- Since 0 ≤ g(circleMap 0 r θ) ≤ M for all θ, we have:
    -- ∫ θ in 0..2π, g(circleMap 0 r θ) ≤ 2π * M
    -- Hence circleAverage g 0 r ≤ M.
    --
    -- The proof uses circleAverage_mono_on_of_le_circle.
    -- The key technical requirement is showing circle integrability of g.
    -- For bounded continuous functions, this is automatic.
    --
    -- Show the function is circle integrable
    -- The composition log⁺ ∘ ‖·‖ ∘ (·⁻¹) ∘ f ∘ circleMap is continuous
    -- since each component is continuous and f is continuous on the closed ball.
    -- Continuous functions on compact intervals are integrable.
    have hInt : CircleIntegrable (fun z => log⁺ ‖(f z)⁻¹‖) 0 r := by
      unfold CircleIntegrable
      -- The composition log⁺ ∘ ‖·‖ ∘ (·)⁻¹ ∘ f ∘ circleMap is continuous
      -- since f is continuous, nonzero on the closed ball, and all component
      -- functions (inverse, norm, log⁺) are continuous.
      have h_map_in_ball : ∀ θ, circleMap 0 r θ ∈ closedBall (0 : ℂ) r :=
        fun θ => sphere_subset_closedBall (by simp [norm_circleMap_zero, abs_of_pos hr_pos])
      have h_cont_f : Continuous (fun θ => f (circleMap 0 r θ)) :=
        hf_cont.comp_continuous (continuous_circleMap 0 r) h_map_in_ball
      have h_f_ne : ∀ θ, f (circleMap 0 r θ) ≠ 0 := fun θ => hne _ (h_map_in_ball θ)
      -- The inverse is continuous at points where f ≠ 0
      have h_cont_inv : Continuous (fun θ => (f (circleMap 0 r θ))⁻¹) := by
        apply Continuous.inv₀ h_cont_f
        exact fun θ => h_f_ne θ
      -- The full composition is continuous
      have h_cont_comp : Continuous (fun θ => log⁺ ‖(f (circleMap 0 r θ))⁻¹‖) :=
        ValueDistribution.continuous_posLog.comp (continuous_norm.comp h_cont_inv)
      exact h_cont_comp.intervalIntegrable 0 (2 * π)
    -- Apply monotonicity: average of f ≤ M when f ≤ M pointwise on the sphere
    apply circleAverage_mono_on_of_le_circle hInt
    intro x hx
    -- x is on the sphere of radius |r| = r
    simp only [Metric.mem_sphere, dist_zero_right] at hx
    have hr_abs : |r| = r := abs_of_pos hr_pos
    rw [hr_abs] at hx
    -- Every point on the sphere of radius r > 0 can be written as circleMap 0 r θ
    -- for some θ = arg x. This is the polar representation of x.
    -- x = |x| * exp(i * arg x) = r * exp(i * arg x) = circleMap 0 r (arg x)
    have h_eq : x = circleMap 0 r (arg x) := by
      rw [circleMap]
      simp only [zero_add]
      -- The polar form: z = ‖z‖ * exp(arg z * I)
      -- With ‖x‖ = r, we get x = r * exp(arg x * I)
      -- This uses Complex.norm_mul_exp_arg_mul_I
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
      rw [hx]
    rw [h_eq]
    exact h_sphere_bound (arg x)

end Nevanlinna
