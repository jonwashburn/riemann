/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.AbsMax
import PrimeNumberTheoremAnd.BorelCaratheodory

theorem derivativeBound {R M r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
  (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (f_zero_at_zero : f 0 = 0)
  (Mpos : 0 < M)
  (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
  (pos_r : 0 < r) (z_in_r : z ∈ Metric.closedBall 0 r)
  (r_le_r' : r < r') (r'_le_R : r' < R) :
  ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  have hRpos : 0 < R := lt_trans (lt_trans pos_r r_le_r') r'_le_R
  have hr'pos : 0 < r' := lt_trans pos_r r_le_r'
  have hrr'pos : 0 < r' - r := sub_pos.mpr r_le_r'
  have hz_norm : ‖z‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using z_in_r

  -- We apply the Cauchy formula for the derivative on the circle `|w| = r'`.
  set U : Set ℂ := Metric.ball (0 : ℂ) R
  have hUopen : IsOpen U := by simpa [U] using (Metric.isOpen_ball : IsOpen (Metric.ball (0 : ℂ) R))
  have hAnalU : AnalyticOn ℂ f U :=
    analytic_f.mono (by
      intro w hw
      exact Metric.ball_subset_closedBall hw)
  have hDiffU : DifferentiableOn ℂ f U := hAnalU.differentiableOn
  have hclosed : Metric.closedBall (0 : ℂ) r' ⊆ U := by
    intro w hw
    have hw' : ‖w‖ ≤ r' := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have : ‖w‖ < R := lt_of_le_of_lt hw' r'_le_R
    simpa [U, Metric.mem_ball, dist_zero_right] using this
  have hz_ball : z ∈ Metric.ball (0 : ℂ) r' := by
    have : ‖z‖ < r' := lt_of_le_of_lt hz_norm r_le_r'
    simpa [Metric.mem_ball, dist_zero_right] using this
  have hCauchy :=
    (Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      (E := ℂ) (U := U) hUopen (c := (0 : ℂ)) (w₀ := z) (R := r') hclosed hDiffU hz_ball)

  -- Borel–Carathéodory on the smaller closed ball `|w| ≤ r'` gives a bound for `‖f w‖` on the circle.
  have hfw : ∀ w ∈ Metric.sphere (0 : ℂ) r', ‖f w‖ ≤ (2 * M * r') / (R - r') := by
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) r' :=
      (Metric.sphere_subset_closedBall (x := (0 : ℂ)) (ε := r')) hw
    -- `closedBall 0 r' ⊆ closedBall 0 R` since `r' < R`.
    have hwR : w ∈ Metric.closedBall (0 : ℂ) R := by
      have hw_norm : ‖w‖ ≤ r' := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hw'
      have : ‖w‖ ≤ R := le_trans hw_norm (le_of_lt r'_le_R)
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    -- Apply the Borel–Carathéodory bound from `PrimeNumberTheoremAnd/BorelCaratheodory.lean`.
    have hAnal : AnalyticOn ℂ f (Metric.closedBall (0 : ℂ) R) := analytic_f
    have hRe : ∀ w ∈ Metric.closedBall (0 : ℂ) R, (f w).re ≤ M := re_f_le_M
    -- The theorem is stated for all points in the closed ball, in particular for `w`.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (borelCaratheodory_closedBall (M := M) (R := R) (r := r') (z := w)
        hRpos hAnal f_zero_at_zero Mpos hRe r'_le_R hw')

  -- Kernel bound on the circle: `‖((w-z)^2)⁻¹ • f w‖ ≤ ((r'-r)^2)⁻¹ * (2Mr'/(R-r'))`.
  have hker :
      ∀ w ∈ Metric.sphere (0 : ℂ) r', ‖((w - z) ^ 2)⁻¹ • f w‖ ≤ ((r' - r) ^ 2)⁻¹ * ((2 * M * r') / (R - r')) := by
    intro w hw
    have hw_norm : ‖w‖ = r' := by
      -- `dist w 0 = r'` on the sphere.
      simpa [Metric.mem_sphere, dist_zero_right] using (Metric.mem_sphere.mp hw)
    have hdist : r' - r ≤ ‖w - z‖ := by
      have hz_le : ‖z‖ ≤ r := hz_norm
      have : r' - r ≤ ‖w‖ - ‖z‖ := by
        -- use `‖w‖ = r'` and `‖z‖ ≤ r`
        have : r' - r ≤ r' - ‖z‖ := by linarith
        simpa [hw_norm] using this
      exact this.trans (norm_sub_norm_le w z)
    have hpow : (r' - r) ^ 2 ≤ ‖w - z‖ ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hrr'pos) hdist 2
    have hinv : (‖w - z‖ ^ 2)⁻¹ ≤ ((r' - r) ^ 2)⁻¹ := by
      have hpos : 0 < (r' - r) ^ 2 := sq_pos_of_pos hrr'pos
      have h := one_div_le_one_div_of_le hpos hpow
      simpa [one_div] using h
    have hinv' : ‖((w - z) ^ 2)⁻¹‖ ≤ ((r' - r) ^ 2)⁻¹ := by
      calc
        ‖((w - z) ^ 2)⁻¹‖ = (‖w - z‖ ^ 2)⁻¹ := by simp [norm_pow]
        _ ≤ ((r' - r) ^ 2)⁻¹ := hinv
    have hnonneg : 0 ≤ ((r' - r) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
    calc
      ‖((w - z) ^ 2)⁻¹ • f w‖ = ‖((w - z) ^ 2)⁻¹‖ * ‖f w‖ := by simp [norm_smul]
      _ ≤ ((r' - r) ^ 2)⁻¹ * ‖f w‖ := by
        exact mul_le_mul_of_nonneg_right hinv' (norm_nonneg _)
      _ ≤ ((r' - r) ^ 2)⁻¹ * ((2 * M * r') / (R - r')) := by
        exact mul_le_mul_of_nonneg_left (hfw w hw) hnonneg

  -- Apply the `(2πi)^{-1}` circle integral norm bound, then rewrite via the Cauchy formula.
  have hbound :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (f := fun w : ℂ => ((w - z) ^ 2)⁻¹ • f w) (c := (0 : ℂ)) (R := r') (hR := hr'pos.le)
      (hf := hker)
  have hbound' :
      ‖deriv f z‖ ≤ r' * (((r' - r) ^ 2)⁻¹ * ((2 * M * r') / (R - r'))) := by
    -- Rewrite the left-hand side using the Cauchy identity, without expanding the `smul` norm.
    have hnorm :
        ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ w in C((0 : ℂ), r'), ((w - z) ^ 2)⁻¹ • f w‖ = ‖deriv f z‖ := by
      -- `hCauchy` has the same identity; take norms.
      simpa [hCauchy] using congrArg norm hCauchy
    -- Now apply the bound.
    calc
      ‖deriv f z‖ =
          ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
              ∮ w in C((0 : ℂ), r'), ((w - z) ^ 2)⁻¹ • f w‖ := by
            simpa using hnorm.symm
      _ ≤ r' * (((r' - r) ^ 2)⁻¹ * ((2 * M * r') / (R - r'))) := hbound

  -- Simplify the RHS into the claimed expression.
  have hden1 : R - r' ≠ 0 := ne_of_gt (sub_pos.mpr r'_le_R)
  have hden2 : r' - r ≠ 0 := ne_of_gt hrr'pos
  -- `field_simp` is enough here (no need for a separate `ring` step).
  have hsimp :
      r' * (((r' - r) ^ 2)⁻¹ * ((2 * M * r') / (R - r')))
        = 2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) := by
    field_simp [div_eq_mul_inv, hden1, hden2]
  -- Conclude.
  simpa [hsimp] using hbound'
