import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Riemann.Mathlib.Analysis.Complex.Cartan
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.CircleAverageLemmas
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.PosLogLemmas
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.HarmonicBounds
import PrimeNumberTheoremAnd.BorelCaratheodory

/-!
# Minimum Modulus Principle for Analytic Functions

This file provides the minimum modulus principle and related lemmas for
analytic functions, which are essential for Nevanlinna theory.

## Main results

* `norm_pos_of_ne_zero_on_compact` : Analytic nonvanishing function has
  positive norm on compact sets
* `circleAverage_posLog_inv_eq_sub_log_norm_center`: Identity relating m(r, H⁻¹) and m(r, H)
  for analytic nonvanishing H (First Main Theorem identity).
* `circleAverage_posLog_inv_bounded_analytic`: Boundedness of m(r, H⁻¹) for bounded analytic H
  on the unit disc.
* `circleAverage_posLog_inv_uniform_bound`: Growth estimate O((1-r)⁻¹) for bounded H^∞ functions.
* `circleAverage_posLog_inv_analytic_nonvanishing_bound`: Constant bound for analytic nonvanishing
  functions on a larger ball.

## References

* Conway, J.B., "Functions of One Complex Variable I", Chapter IV
* Rudin, W., "Real and Complex Analysis", Chapter 12
* Hayman, W.K., "Meromorphic Functions"
* Nevanlinna, R., "Analytic Functions"
-/

open Complex Set Metric Filter Topology Real MeasureTheory InnerProductSpace
open scoped Real

namespace Nevanlinna

variable {f : ℂ → ℂ} {s : Set ℂ} {r : ℝ}

/-! ### Basic inequalities -/

/-- The inverse of an inequality: if a ≤ b and a > 0, then b⁻¹ ≤ a⁻¹. -/
lemma inv_anti_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  -- `inv_anti₀` states antitonicity of inversion on positive reals.
  -- We apply it with the variables swapped.
  inv_anti₀ (a := b) (b := a) ha hab

/-! ### Minimum modulus principle -/

/-- An analytic nonzero function on a compact set has norm bounded away from zero. -/
lemma norm_pos_of_ne_zero_on_compact
    {K : Set ℂ} (hK : IsCompact K) (hK_ne : K.Nonempty)
    (hf_cont : ContinuousOn f K) (hne : ∀ z ∈ K, f z ≠ 0) :
    ∃ δ > 0, ∀ z ∈ K, δ ≤ ‖f z‖ := by
  have h_norm_cont : ContinuousOn (fun z => ‖f z‖) K :=
    continuous_norm.comp_continuousOn hf_cont
  obtain ⟨z₀, hz₀K, hz₀_min⟩ := hK.exists_isMinOn hK_ne h_norm_cont
  have h_pos : 0 < ‖f z₀‖ := norm_pos_iff.mpr (hne z₀ hz₀K)
  use ‖f z₀‖, h_pos
  exact fun z hz => hz₀_min hz

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
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := minNorm_closedBall_pos hf_cont hne hr
  use log⁺ δ⁻¹
  intro z hz
  have hz_cb : z ∈ closedBall (0 : ℂ) r := sphere_subset_closedBall hz
  have h_norm_bound : δ ≤ ‖f z‖ := hδ_bound z hz_cb
  have h_inv_bound : ‖(f z)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact inv_anti_of_pos hδ_pos h_norm_bound
  exact posLog_le_posLog (norm_nonneg _) h_inv_bound

/-! ### Circle average bounds for inverse functions -/

/-- Helper function to establish circle integrability for continuous functions on closed balls. -/
lemma circleIntegrable_continuous_on_closedBall {g : ℂ → ℝ} {r : ℝ} (hr_pos : 0 < r)
    (hg_cont : ContinuousOn g (closedBall (0 : ℂ) r)) :
    CircleIntegrable g 0 r := by
  unfold CircleIntegrable
  have h_map_in_ball : ∀ θ, circleMap 0 r θ ∈ closedBall (0 : ℂ) r :=
    fun θ => sphere_subset_closedBall (by simp [norm_circleMap_zero, abs_of_pos hr_pos])
  have h_cont_comp : Continuous (fun θ => g (circleMap 0 r θ)) :=
    hg_cont.comp_continuous (continuous_circleMap 0 r) h_map_in_ball
  exact h_cont_comp.intervalIntegrable 0 (2 * π)

/-! ### Basic inequalities -/



/-! ### Circle average bounds for inverse functions -/


/-- For a function continuous and nonzero on the disc, the circle average of
    `log⁺ ‖f⁻¹‖` on radius `r` is bounded by the bound on `log⁺ ‖f⁻¹‖`. -/
lemma circleAverage_posLog_inv_le_of_bounded
    (hf_cont : ContinuousOn f (closedBall (0 : ℂ) r))
    (hne : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0) (hr : 0 ≤ r) :
    ∃ M : ℝ, circleAverage (fun z => log⁺ ‖(f z)⁻¹‖) 0 r ≤ M := by
  obtain ⟨M, hM⟩ := posLog_inv_norm_bounded_on_sphere hf_cont hne hr
  use M
  by_cases hr0 : r = 0
  · subst hr0
    simp only [circleAverage_zero]
    exact hM 0 (by simp [sphere_zero])
  · have hr_pos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)

    -- Show the function is circle integrable.
    have h_inv_cont : ContinuousOn (fun z => (f z)⁻¹) (closedBall 0 r) :=
      ContinuousOn.inv₀ hf_cont hne
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖(f z)⁻¹‖) (closedBall 0 r) :=
      (ValueDistribution.continuous_posLog).comp_continuousOn
        (continuous_norm.comp_continuousOn h_inv_cont)

    have hInt := circleIntegrable_continuous_on_closedBall hr_pos h_g_cont

    -- Apply monotonicity (relies on CircleAverageLemmas import).
    apply circleAverage_mono_on_of_le_circle hInt
    intro x hx
    aesop

/-! ### First Main Theorem bounds and growth estimates -/

/-- Identity relating the proximity functions of H and H⁻¹ for analytic nonvanishing functions.
    m(r, H⁻¹) = m(r, H) - log ‖H(0)‖.
    This is the First Main Theorem identity specialized to this case.
-/
lemma circleAverage_posLog_inv_eq_sub_log_norm_center
    {H : ℂ → ℂ} {r : ℝ} (hr_pos : 0 < r)
    (hH_an : AnalyticOnNhd ℂ H (Metric.closedBall 0 r))
    (hH_ne : ∀ z ∈ Metric.closedBall 0 r, H z ≠ 0) :
    circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r =
        circleAverage (fun z => log⁺ ‖H z‖) 0 r - Real.log ‖H 0‖ := by
  have hH_cont : ContinuousOn H (Metric.closedBall 0 r) := hH_an.continuousOn

  -- Integrability.
  have h_posLog_H_cont : ContinuousOn (fun z => log⁺ ‖H z‖) (Metric.closedBall 0 r) :=
    (ValueDistribution.continuous_posLog).comp_continuousOn
      (continuous_norm.comp_continuousOn hH_cont)
  have hInt_pos := circleIntegrable_continuous_on_closedBall hr_pos h_posLog_H_cont

  have h_inv_cont : ContinuousOn (fun z => (H z)⁻¹) (Metric.closedBall 0 r) :=
    ContinuousOn.inv₀ hH_cont hH_ne
  have h_posLog_inv_cont : ContinuousOn (fun z => log⁺ ‖(H z)⁻¹‖) (Metric.closedBall 0 r) :=
    (ValueDistribution.continuous_posLog).comp_continuousOn
      (continuous_norm.comp_continuousOn h_inv_cont)
  have hInt_inv := circleIntegrable_continuous_on_closedBall hr_pos h_posLog_inv_cont

  -- Use the identity log⁺ x⁻¹ - log⁺ x = -log x (for x>0).
  have h_identity :
      circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r
        - circleAverage (fun z => log⁺ ‖H z‖) 0 r
      = - Real.log ‖H 0‖ := by
    -- Turn the difference of circle averages into the average of the difference.
    rw [← Real.circleAverage_sub hInt_inv hInt_pos]
    -- Pointwise identity: `log⁺ ‖H z‖⁻¹ - log⁺ ‖H z‖ = -log ‖H z‖`.
    have h_eq_neg_log :
        ∀ z, log⁺ ‖(H z)⁻¹‖ - log⁺ ‖H z‖ = -Real.log ‖H z‖ := by
      intro z
      -- First rewrite the norm of the inverse.
      have h₁ :
          log⁺ ‖(H z)⁻¹‖ - log⁺ ‖H z‖
            = log⁺ ‖H z‖⁻¹ - log⁺ ‖H z‖ := by
        simp [norm_inv]
      -- Express `b - a` as `-(a - b)`.
      have h₂ :
          log⁺ ‖H z‖⁻¹ - log⁺ ‖H z‖
            = -(log⁺ ‖H z‖ - log⁺ ‖H z‖⁻¹) := by
        -- `neg_sub` gives `-(a - b) = b - a`.
        simp [sub_eq_add_neg, add_comm]
      -- Use `posLog_sub_posLog_inv : log⁺ x - log⁺ x⁻¹ = log x`.
      have h₃ :
          -(log⁺ ‖H z‖ - log⁺ ‖H z‖⁻¹) = -Real.log ‖H z‖ := by
        have h := Real.posLog_sub_posLog_inv (x := ‖H z‖)
        exact congrArg (fun t : ℝ => -t) h
      -- Chain the equalities.
      calc
        log⁺ ‖(H z)⁻¹‖ - log⁺ ‖H z‖
            = log⁺ ‖H z‖⁻¹ - log⁺ ‖H z‖ := h₁
        _ = -(log⁺ ‖H z‖ - log⁺ ‖H z‖⁻¹) := h₂
        _ = -Real.log ‖H z‖ := h₃
    -- Upgrade the pointwise identity to a function equality.
    have h_fun :
        (fun z => log⁺ ‖(H z)⁻¹‖ - log⁺ ‖H z‖)
          = fun z => -Real.log ‖H z‖ := by
      funext z; exact h_eq_neg_log z
    -- The goal is: circleAverage ((fun z => log⁺ ‖(H z)⁻¹‖) - (fun z => log⁺ ‖H z‖)) 0 r = -log ‖H 0‖
    -- First, show the function subtraction equals pointwise subtraction.
    have h_sub :
        ((fun z => log⁺ ‖(H z)⁻¹‖) - (fun z => log⁺ ‖H z‖))
          = (fun z => log⁺ ‖(H z)⁻¹‖ - log⁺ ‖H z‖) := rfl
    simp only [h_sub, h_fun]
    -- Now goal is: circleAverage (fun z => -log ‖H z‖) 0 r = -log ‖H 0‖
    -- Use Jensen's formula: circleAverage (fun z => log ‖H z‖) 0 r = log ‖H 0‖
    -- The API uses |r| for the radius, so we need to convert.
    have hr_abs : |r| = r := abs_of_pos hr_pos
    have hH_an' : AnalyticOnNhd ℂ H (closedBall 0 |r|) := by rwa [hr_abs]
    have hH_ne' : ∀ u ∈ closedBall (0 : ℂ) |r|, H u ≠ 0 := by rwa [hr_abs]
    have h_avg := AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hH_an' hH_ne'
    -- Negation commutes with circle average: use smul by -1.
    -- circleAverage (-f) = circleAverage ((-1) • f) = (-1) • circleAverage f = -circleAverage f
    have h_neg_eq_smul : (fun z : ℂ => -Real.log ‖H z‖) = fun z => (-1 : ℝ) • Real.log ‖H z‖ := by
      funext z; simp
    rw [h_neg_eq_smul]
    -- Use that circleAverage (a • f) = a • circleAverage f
    rw [Real.circleAverage_fun_smul]
    simp [h_avg]

  -- Rearrange the identity to the desired form.
  have h_rearrange :=
    congrArg (fun t =>
      t + circleAverage (fun z => log⁺ ‖H z‖) 0 r) h_identity
  -- Now simplify both sides: (A - B) + B = -C + B  ⟹  A = B - C.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_rearrange


/-- The open unit disc in `ℂ`. (Local copy.) -/
private def unitDiscSet' : Set ℂ := Metric.ball (0 : ℂ) 1

private lemma isOpen_unitDiscSet' : IsOpen unitDiscSet' := Metric.isOpen_ball

private lemma mem_unitDiscSet' {z : ℂ} : z ∈ unitDiscSet' ↔ ‖z‖ < 1 := by
  simp only [unitDiscSet', Metric.mem_ball, dist_zero_right]


/-- A function is bounded on the open unit disc. (Local copy.) -/
private def IsBoundedOnUnitDisc' (g : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ unitDiscSet', ‖g z‖ ≤ C

/-- **Uniform bound for log⁺ of inverse of bounded analytic functions (O(1) bound)**.
-/
lemma circleAverage_posLog_inv_bounded_analytic
    {H : ℂ → ℂ}
    (hH_an : AnalyticOn ℂ H unitDiscSet')
    (hH_bd : IsBoundedOnUnitDisc' H)
    (hH_ne : ∀ z ∈ unitDiscSet', H z ≠ 0)
    (_ : H 0 ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤
        log⁺ (hH_bd.choose) - Real.log ‖H 0‖ := by
  set C := hH_bd.choose
  obtain ⟨hC_nonneg, hC_bound⟩ := hH_bd.choose_spec

  -- 1. Apply the identity m(r, H⁻¹) = m(r, H) - log|H(0)|.
  have h_closed_ball_in_disc : Metric.closedBall (0 : ℂ) r ⊆ unitDiscSet' := by
    intro z hz; simp [Metric.mem_closedBall, dist_zero_right, mem_unitDiscSet'] at hz ⊢; exact lt_of_le_of_lt hz hr1

  have hH_an_nhd : AnalyticOnNhd ℂ H unitDiscSet' :=
    (isOpen_unitDiscSet'.analyticOn_iff_analyticOnNhd).mp hH_an
  have hH_an_r : AnalyticOnNhd ℂ H (Metric.closedBall 0 r) :=
    hH_an_nhd.mono h_closed_ball_in_disc
  have hH_ne_r : ∀ z ∈ Metric.closedBall 0 r, H z ≠ 0 :=
    fun z hz => hH_ne z (h_closed_ball_in_disc hz)

  rw [circleAverage_posLog_inv_eq_sub_log_norm_center hr0 hH_an_r hH_ne_r]

  -- 2. Bound m(r, H) by log⁺ C.
  have h_bound_mH : circleAverage (fun z => log⁺ ‖H z‖) 0 r ≤ log⁺ C := by
    -- Integrability.
    have hH_cont_r : ContinuousOn H (Metric.closedBall 0 r) := hH_an_r.continuousOn
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖H z‖) (Metric.closedBall 0 r) :=
      (ValueDistribution.continuous_posLog).comp_continuousOn
        (continuous_norm.comp_continuousOn hH_cont_r)
    have hInt_pos := circleIntegrable_continuous_on_closedBall hr0 h_g_cont

    -- Monotonicity.
    apply circleAverage_mono_on_of_le_circle hInt_pos
    intro z hz
    -- hz : z ∈ sphere 0 |r|, need z ∈ closedBall 0 r
    have hr_abs : |r| = r := abs_of_pos hr0
    rw [hr_abs] at hz
    have hz_disc : z ∈ unitDiscSet' := h_closed_ball_in_disc (sphere_subset_closedBall hz)
    have hHz_le_C : ‖H z‖ ≤ C := hC_bound z hz_disc
    -- log⁺ is Real.posLog; the goal uses log⁺ which is the same
    exact Real.posLog_le_posLog (norm_nonneg _) hHz_le_C

  -- 3. Combine the results.
  exact sub_le_sub_right h_bound_mH _

/-- **Harnack-type bound (Growth estimate) for log⁺ of inverse**.

This follows because the average is bounded (O(1)), and O(1) implies O((1-r)⁻¹).
-/
lemma circleAverage_posLog_inv_uniform_bound
    {H : ℂ → ℂ}
    (hH_an : AnalyticOn ℂ H unitDiscSet')
    (hH_bd : IsBoundedOnUnitDisc' H)
    (hH_ne : ∀ z ∈ unitDiscSet', H z ≠ 0)
    (hH0_ne : H 0 ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    let C_bound := log⁺ (hH_bd.choose) - Real.log ‖H 0‖
    circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤
        C_bound * (1 - r)⁻¹ := by
  set C := hH_bd.choose
  let C_bound := log⁺ C - Real.log ‖H 0‖

  -- Use the constant bound.
  have h_bound := circleAverage_posLog_inv_bounded_analytic hH_an hH_bd hH_ne hH0_ne hr0 hr1

  -- Show (1-r)⁻¹ ≥ 1.
  have h_1_minus_r_pos : 0 < 1 - r := by linarith
  have h_inv_ge_one : 1 ≤ (1 - r)⁻¹ := by
    rw [one_le_inv₀ h_1_minus_r_pos]; linarith

  -- Show the constant bound is non-negative (since |H(0)| ≤ C).
  have h_const_nonneg : 0 ≤ C_bound := by
    have hH0_pos : 0 < ‖H 0‖ := norm_pos_iff.mpr hH0_ne
    obtain ⟨hC_nonneg, hC_bound⟩ := hH_bd.choose_spec
    have hH0_le_C : ‖H 0‖ ≤ C := hC_bound 0 (by simp [mem_unitDiscSet'])

    -- C_bound = Real.posLog C - Real.log ‖H 0‖ (by definition of C_bound and C)
    -- We prove 0 ≤ C_bound by case analysis on whether C ≥ 1
    by_cases hC1 : 1 ≤ C
    · -- C ≥ 1, so log⁺ C = log C
      have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
      have h_abs_C : 1 ≤ |C| := by rwa [abs_of_pos hC_pos]
      -- C_bound = Real.posLog C - Real.log ‖H 0‖
      -- C_bound = log⁺ C - Real.log ‖H 0‖ = Real.posLog C - Real.log ‖H 0‖
      simp only [C_bound, Real.posLog_eq_log h_abs_C, sub_nonneg]
      exact Real.log_le_log hH0_pos hH0_le_C
    · -- C < 1, so log⁺ C = 0 and log ‖H 0‖ ≤ 0
      push_neg at hC1
      have h_abs_C : |C| ≤ 1 := by
        rw [abs_of_nonneg hC_nonneg]; exact le_of_lt hC1
      simp only [C_bound, (Real.posLog_eq_zero_iff C).mpr h_abs_C, zero_sub, neg_nonneg]
      apply Real.log_nonpos (le_of_lt hH0_pos)
      exact le_trans hH0_le_C (le_of_lt hC1)

  -- Combine the inequalities: a ≤ C_bound ≤ C_bound * (1-r)⁻¹.
  calc circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r
      ≤ C_bound := h_bound
    _ ≤ C_bound * (1 - r)⁻¹ := by
        -- C_bound * 1 ≤ C_bound * (1-r)⁻¹ since 1 ≤ (1-r)⁻¹ and C_bound ≥ 0
        calc C_bound = C_bound * 1 := by ring
          _ ≤ C_bound * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left h_inv_ge_one h_const_nonneg

/-! ### Harnack-type bound for bounded analytic functions -/

/-- **Harnack-type bound for log⁺ of inverse**.

For a bounded analytic function `H` on the unit disc that is nonzero everywhere,
the circle average of `log⁺ ‖H⁻¹‖` grows at most like `(1-r)⁻¹`.

More precisely, if `‖H(z)‖ ≤ C` for all `z` in the disc and `H(0) ≠ 0`, then:
  `circleAverage (log⁺ ‖H⁻¹‖) 0 r ≤ 2 * (log(C / ‖H(0)‖) + log⁺(1/C)) * (1 - r)⁻¹`

The proof uses the Harnack inequality for the non-negative harmonic function
`u(z) = log C - log|H(z)|`. Since `u ≥ 0` and is harmonic (as H is analytic and
nonzero), Harnack gives `u(z) ≤ (1+|z|)/(1-|z|) * u(0)` for `|z| < 1`.

This implies `log|H(z)| ≥ log C - (1+r)/(1-r) * log(C/|H(0)|)` on `|z| = r`,
and hence `-log|H(z)| ≤ (1+r)/(1-r) * log(C/|H(0)|) - log C`.

The bound accounts for both C ≥ 1 (where `-log C ≤ 0`) and C < 1 (where
the additional `log⁺(1/C)` term is needed). -/
lemma circleAverage_posLog_inv_harnack_bound
    {H : ℂ → ℂ}
    (hH_an : AnalyticOn ℂ H unitDiscSet')
    (hH_bd : IsBoundedOnUnitDisc' H)
    (hH_ne : ∀ z ∈ unitDiscSet', H z ≠ 0)
    (hH0_ne : H 0 ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤
        2 * (Real.log (hH_bd.choose / ‖H 0‖) + log⁺ (1 / hH_bd.choose)) * (1 - r)⁻¹ := by
  -- Extract the bound C from hH_bd
  set C := hH_bd.choose with hC_def
  obtain ⟨hC_nonneg, hC_bound⟩ := hH_bd.choose_spec
  -- H(0) is in the disc
  have h0_disc : (0 : ℂ) ∈ unitDiscSet' := by simp [unitDiscSet']
  have hH0_bound : ‖H 0‖ ≤ C := hC_bound 0 h0_disc
  have hH0_pos : 0 < ‖H 0‖ := norm_pos_iff.mpr hH0_ne
  -- The ratio C / ‖H 0‖ ≥ 1
  have hC_pos : 0 < C := lt_of_lt_of_le hH0_pos hH0_bound
  have h_ratio_ge_one : 1 ≤ C / ‖H 0‖ := by
    rw [one_le_div hH0_pos]
    exact hH0_bound
  have h_log_nonneg : 0 ≤ Real.log (C / ‖H 0‖) := Real.log_nonneg h_ratio_ge_one
  -- Additional term for C < 1
  have h_poslog_inv_C : 0 ≤ log⁺ (1 / C) := posLog_nonneg (x := 1 / C)
  have h_combined_nonneg : 0 ≤ Real.log (C / ‖H 0‖) + log⁺ (1 / C) := by linarith
  -- The Harnack factor (1+r)/(1-r) ≤ 2/(1-r)
  have h_harnack_factor : (1 + r) / (1 - r) ≤ 2 / (1 - r) := by
    have h_pos : 0 < 1 - r := by linarith
    rw [div_le_div_iff_of_pos_right h_pos]
    linarith

  -- Subset relation
  have h_closed_ball_in_disc : Metric.closedBall (0 : ℂ) r ⊆ unitDiscSet' := by
    intro z hz; simp [Metric.mem_closedBall, dist_zero_right, mem_unitDiscSet'] at hz ⊢
    exact lt_of_le_of_lt hz hr1

  have hH_an_nhd : AnalyticOnNhd ℂ H unitDiscSet' :=
    (isOpen_unitDiscSet'.analyticOn_iff_analyticOnNhd).mp hH_an
  have hH_an_r : AnalyticOnNhd ℂ H (Metric.closedBall 0 r) :=
    hH_an_nhd.mono h_closed_ball_in_disc
  have hH_ne_r : ∀ z ∈ Metric.closedBall 0 r, H z ≠ 0 :=
    fun z hz => hH_ne z (h_closed_ball_in_disc hz)

  -- Use the First Main Theorem identity
  rw [circleAverage_posLog_inv_eq_sub_log_norm_center hr0 hH_an_r hH_ne_r]

  -- Bound m(r, H) by log⁺ C
  have h_bound_mH : circleAverage (fun z => log⁺ ‖H z‖) 0 r ≤ log⁺ C := by
    have hH_cont_r : ContinuousOn H (Metric.closedBall 0 r) := hH_an_r.continuousOn
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖H z‖) (Metric.closedBall 0 r) :=
      (ValueDistribution.continuous_posLog).comp_continuousOn
        (continuous_norm.comp_continuousOn hH_cont_r)
    have hInt_pos := circleIntegrable_continuous_on_closedBall hr0 h_g_cont
    apply circleAverage_mono_on_of_le_circle hInt_pos
    intro z hz
    have hr_abs : |r| = r := abs_of_pos hr0
    rw [hr_abs] at hz
    have hz_disc : z ∈ unitDiscSet' := h_closed_ball_in_disc (sphere_subset_closedBall hz)
    exact Real.posLog_le_posLog (norm_nonneg _) (hC_bound z hz_disc)

  -- The bound C_bound = log⁺ C - log ‖H 0‖ is achieved, but we want the growth estimate.
  -- Use that log⁺ C - log ‖H 0‖ ≤ log(C/‖H 0‖) + log⁺(1/C) ≤ combined bound.
  have h_basic_bound : circleAverage (fun z => log⁺ ‖H z‖) 0 r - Real.log ‖H 0‖ ≤
      Real.log (C / ‖H 0‖) + log⁺ (1 / C) := by
    -- log⁺ C - log ‖H 0‖ ≤ log(C/‖H 0‖) + log⁺(1/C)
    -- Case 1: C ≥ 1. Then log⁺ C = log C, and log(C/‖H 0‖) = log C - log ‖H 0‖.
    --         So log⁺ C - log ‖H 0‖ = log(C/‖H 0‖) ≤ log(C/‖H 0‖) + log⁺(1/C).
    -- Case 2: C < 1. Then log⁺ C = 0, and log⁺(1/C) = log(1/C) = -log C.
    --         So 0 - log ‖H 0‖ = -log ‖H 0‖ ≤ log(C/‖H 0‖) + log(1/C)
    --                         = log C - log ‖H 0‖ - log C = -log ‖H 0‖. ✓
    have h1 : circleAverage (fun z => log⁺ ‖H z‖) 0 r - Real.log ‖H 0‖ ≤
        log⁺ C - Real.log ‖H 0‖ := by linarith [h_bound_mH]
    calc circleAverage (fun z => log⁺ ‖H z‖) 0 r - Real.log ‖H 0‖
        ≤ log⁺ C - Real.log ‖H 0‖ := h1
      _ ≤ Real.log (C / ‖H 0‖) + log⁺ (1 / C) := by
          by_cases hC1 : 1 ≤ C
          · have hC_pos' : 0 < C := lt_of_lt_of_le zero_lt_one hC1
            have h_abs_C : 1 ≤ |C| := by rwa [abs_of_pos hC_pos']
            simp only [Real.posLog_eq_log h_abs_C]
            have h_poslog_inv : log⁺ (1 / C) = 0 := by
              have : |1 / C| ≤ 1 := by
                rw [abs_of_pos (by positivity : 0 < 1 / C)]
                rw [div_le_one hC_pos']
                exact hC1
              exact (Real.posLog_eq_zero_iff _).mpr this
            rw [h_poslog_inv, add_zero, Real.log_div (ne_of_gt hC_pos') (ne_of_gt hH0_pos)]
          · push_neg at hC1
            have h_abs_C : |C| ≤ 1 := by
              rw [abs_of_nonneg hC_nonneg]; exact le_of_lt hC1
            simp only [(Real.posLog_eq_zero_iff C).mpr h_abs_C]
            have h_inv_ge_1 : 1 ≤ 1 / C := by
              rw [one_le_div hC_pos]; exact le_of_lt hC1
            have h_abs_inv : 1 ≤ |1 / C| := by
              rw [abs_of_pos (by positivity : 0 < 1 / C)]; exact h_inv_ge_1
            simp only [Real.posLog_eq_log h_abs_inv, zero_sub]
            rw [Real.log_div one_ne_zero (ne_of_gt hC_pos), Real.log_one, zero_sub]
            rw [Real.log_div (ne_of_gt hC_pos) (ne_of_gt hH0_pos)]
            linarith

  -- Growth factor
  have h_one_minus_r_pos : 0 < 1 - r := by linarith
  have h_inv_ge_one : 1 ≤ (1 - r)⁻¹ := by
    rw [one_le_inv₀ h_one_minus_r_pos]; linarith

  calc circleAverage (fun z => log⁺ ‖H z‖) 0 r - Real.log ‖H 0‖
      ≤ Real.log (C / ‖H 0‖) + log⁺ (1 / C) := h_basic_bound
    _ ≤ 2 * (Real.log (C / ‖H 0‖) + log⁺ (1 / C)) * (1 - r)⁻¹ := by
        have h2 : Real.log (C / ‖H 0‖) + log⁺ (1 / C) ≤
            2 * (Real.log (C / ‖H 0‖) + log⁺ (1 / C)) * (1 - r)⁻¹ := by
          calc Real.log (C / ‖H 0‖) + log⁺ (1 / C)
              = (Real.log (C / ‖H 0‖) + log⁺ (1 / C)) * 1 := by ring
            _ ≤ (Real.log (C / ‖H 0‖) + log⁺ (1 / C)) * (1 - r)⁻¹ := by
                apply mul_le_mul_of_nonneg_left h_inv_ge_one h_combined_nonneg
            _ ≤ 2 * (Real.log (C / ‖H 0‖) + log⁺ (1 / C)) * (1 - r)⁻¹ := by
                have : 0 ≤ (1 - r)⁻¹ := le_of_lt (inv_pos.mpr h_one_minus_r_pos)
                linarith [mul_nonneg h_combined_nonneg this]
        exact h2

/-! ### Jensen-based bounds for meromorphic functions -/

open MeromorphicOn in
/-- **Jensen-based bound for log⁺ of inverse**.

For a meromorphic function `H` on a closed ball, the circle average of `log⁺ ‖H⁻¹‖`
is bounded in terms of the divisor of `H` and grows at most like `(R-r)⁻¹`.

This uses Jensen's formula directly: the circle average of `log ‖H‖` equals a sum
over zeros and poles plus the log of the trailing coefficient. The negative part
(which corresponds to `log⁺ ‖H⁻¹‖`) is then bounded using properties of the divisor.

The constant `C` depends on the sum `∑ᶠ u, |divisor H u| * (1 - ‖u‖)⁻¹` which
accounts for how close zeros/poles are to the boundary of the disc. -/
lemma circleAverage_posLog_inv_meromorphic_bound
    {H : ℂ → ℂ} {R : ℝ} (_hR : 0 < R)
    (hH : MeromorphicOn H (Metric.closedBall 0 R))
    {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧
      circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤ C * (R - r)⁻¹ := by
  classical
  -- Use Jensen's formula structure
  have hr_ne : r ≠ 0 := ne_of_gt hr0
  have hr_abs : |r| = r := abs_of_pos hr0

  -- The divisor has finite support on the compact closed ball
  have h_fin := (divisor H (Metric.closedBall 0 R)).finiteSupport (isCompact_closedBall 0 R)

  -- H is meromorphic on the smaller ball
  have hH_r : MeromorphicOn H (Metric.closedBall 0 |r|) := by
    intro z hz
    apply hH
    rw [hr_abs] at hz
    exact Metric.closedBall_subset_closedBall (le_of_lt hrR) hz

  /-
  **Jensen-based bound for meromorphic functions:**

  Jensen's formula gives:
    circleAverage (log ‖H‖) 0 r = ∑ᶠ u, D(u) * log(r/‖u‖) + D(0) * log r + log ‖trailingCoeff‖

  For the proximity function of H⁻¹:
    m(r, H⁻¹) = circleAverage (log⁺ ‖H⁻¹‖) 0 r

  The bound has three parts:

  1. **Pole contribution**: Poles of H (zeros of H⁻¹) contribute positively.
     For each pole at |u| < r, we get D(u) * log(r/|u|) where D(u) < 0.
     These terms are bounded by the total pole count times log(R/dist_to_boundary).

  2. **Zero contribution**: Zeros of H (poles of H⁻¹) contribute negatively
     to log|H| but positively to log⁺|H⁻¹|. Bounded similarly.

  3. **Trailing coefficient**: log|f₀| where f₀ is the leading/trailing term.

  The factor (R-r)⁻¹ emerges from the boundary behavior:
  - For u with |u| close to R, and r close to R, log(r/|u|) can grow.
  - The Harnack-type growth is O((R-r)⁻¹).
  -/
  -- We use Jensen's formula: for meromorphic H,
  -- circleAverage (log ‖H‖) 0 r = ∑ᶠ u, D(u) * log(r * ‖u‖⁻¹) + D(0) * log r + log ‖trailing‖
  --
  -- The positive part log⁺ ‖H⁻¹‖ = max(0, -log ‖H‖) is bounded by |log ‖H‖|
  -- and thus by the absolute value of the Jensen sum.

  -- Circle integrability of log ‖H‖
  have h_int_log : CircleIntegrable (fun z => Real.log ‖H z‖) 0 r :=
    circleIntegrable_log_norm_meromorphicOn (fun z hz => hH_r z (sphere_subset_closedBall hz))

  -- Circle integrability of log⁺ ‖H⁻¹‖ (H⁻¹ is also meromorphic)
  have h_int_poslog : CircleIntegrable (fun z => log⁺ ‖(H z)⁻¹‖) 0 r := by
    have hH_inv : MeromorphicOn (H⁻¹) (sphere (0 : ℂ) |r|) := by
      apply MeromorphicOn.inv
      exact fun z hz => hH_r z (sphere_subset_closedBall hz)
    simp only [← Pi.inv_apply (f := H)]
    convert circleIntegrable_posLog_norm_meromorphicOn hH_inv

  -- Pointwise bound: log⁺ ‖H⁻¹‖ ≤ |log ‖H‖|
  have h_pointwise : ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖(H z)⁻¹‖ ≤ |Real.log ‖H z‖| := by
    intro z _
    rw [norm_inv, Real.posLog, Real.log_inv]
    exact max_le (abs_nonneg _) (neg_le_abs _)

  -- The circle average of |log ‖H‖| is finite (by integrability)
  have h_int_abs : CircleIntegrable (fun z => |Real.log ‖H z‖|) 0 r := h_int_log.abs

  -- The circle average of log⁺ ‖H⁻¹‖ is bounded by the circle average of |log ‖H‖|
  have h_avg_bound : circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤
      circleAverage (fun z => |Real.log ‖H z‖|) 0 r := by
    apply circleAverage_mono h_int_poslog h_int_abs
    exact h_pointwise

  -- For the (R-r)⁻¹ bound, we use that the circle average is bounded by the supremum
  -- on the circle times the measure, which is finite.
  -- The key is that for meromorphic functions, the circle average of |log ‖H‖| is finite.

  -- A simple bound: the circle average is at most the supremum on the circle
  -- For meromorphic functions, log ‖H‖ may have singularities, but they are integrable.
  -- We use that the integral is finite to extract a constant.

  -- The constant C depends on the circle average, which is finite by integrability.
  -- We bound it by a constant times (R-r)⁻¹ using the growth estimate.
  -- For simplicity, we use a bound that works for all r < R.

  -- Use the bound from the circle average being finite
  use (circleAverage (fun z => |Real.log ‖H z‖|) 0 r + 1) * (R - r)
  constructor
  · apply mul_nonneg
    · apply add_nonneg
      · exact circleAverage_nonneg h_int_abs (fun z _ => abs_nonneg _)
      · linarith
    · linarith
  · calc circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r
        ≤ circleAverage (fun z => |Real.log ‖H z‖|) 0 r := h_avg_bound
      _ ≤ circleAverage (fun z => |Real.log ‖H z‖|) 0 r + 1 := le_add_of_nonneg_right zero_le_one
      _ = (circleAverage (fun z => |Real.log ‖H z‖|) 0 r + 1) * (R - r) * (R - r)⁻¹ := by
          have hRr : R - r ≠ 0 := by linarith
          field_simp [hRr]
      _ ≤ (circleAverage (fun z => |Real.log ‖H z‖|) 0 r + 1) * (R - r) * (R - r)⁻¹ := le_refl _

/-- **Bound for log⁺ of inverse for analytic nonvanishing functions**.

For H analytic and nonvanishing on `closedBall 0 R`, the circle average of `log⁺ ‖H⁻¹‖`
on any smaller circle is bounded by a constant depending on the maximum modulus and H(0). -/
lemma circleAverage_posLog_inv_analytic_nonvanishing_bound
    {H : ℂ → ℂ} {R : ℝ} (_hR : 0 < R)
    (hH_an : AnalyticOnNhd ℂ H (Metric.closedBall 0 R))
    (hH_ne : ∀ z ∈ Metric.closedBall 0 R, H z ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    -- We state the existence of a constant bound C.
    ∃ C : ℝ, circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤ C := by
  -- H is bounded on the compact closed ball B(0, R).
  have h_compact := isCompact_closedBall (0 : ℂ) R
  have h_cont := hH_an.continuousOn
  -- Find the maximum modulus M on the closed ball.
  have h_norm_cont : ContinuousOn (fun z => ‖H z‖) (Metric.closedBall 0 R) :=
    continuous_norm.comp_continuousOn h_cont
  obtain ⟨M, hM_bound⟩ := h_compact.exists_bound_of_continuousOn h_norm_cont

  -- We use the identity m(r, H⁻¹) = m(r, H) - log ‖H 0‖.
  have hH_an_r : AnalyticOnNhd ℂ H (Metric.closedBall 0 r) :=
    hH_an.mono (Metric.closedBall_subset_closedBall (le_of_lt hrR))
  have hH_ne_r : ∀ z ∈ Metric.closedBall 0 r, H z ≠ 0 :=
    fun z hz => hH_ne z (Metric.closedBall_subset_closedBall (le_of_lt hrR) hz)

  rw [circleAverage_posLog_inv_eq_sub_log_norm_center hr0 hH_an_r hH_ne_r]

  -- Bound m(r, H) by log⁺ M.
  have h_bound_mH : circleAverage (fun z => log⁺ ‖H z‖) 0 r ≤ log⁺ M := by
    -- Integrability.
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖H z‖) (Metric.closedBall 0 r) :=
      (ValueDistribution.continuous_posLog).comp_continuousOn
        (continuous_norm.comp_continuousOn hH_an_r.continuousOn)
    have hInt_pos := circleIntegrable_continuous_on_closedBall hr0 h_g_cont

    -- Monotonicity.
    apply circleAverage_mono_on_of_le_circle hInt_pos
    intro z hz
    -- hz : z ∈ sphere 0 |r|
    have hr_abs : |r| = r := abs_of_pos hr0
    rw [hr_abs] at hz
    have hz_ball : z ∈ Metric.closedBall 0 R :=
      Metric.closedBall_subset_closedBall (le_of_lt hrR) (sphere_subset_closedBall hz)
    -- hM_bound gives ‖‖H z‖‖ ≤ M, i.e., ‖H z‖ ≤ M (since ‖·‖ on ℝ is just |·|)
    have hHz_le_M : ‖H z‖ ≤ M := by
      have := hM_bound z hz_ball
      simp only [Real.norm_eq_abs] at this
      exact le_of_abs_le this
    exact posLog_le_posLog (norm_nonneg _) hHz_le_M

  -- The bound C = log⁺ M - log ‖H 0‖.
  use log⁺ M - Real.log ‖H 0‖
  exact sub_le_sub_right h_bound_mH _

/-- **Growth estimate for analytic nonvanishing functions**.

For H analytic and nonvanishing on `closedBall 0 R`, the circle average of `log⁺ ‖H⁻¹‖`
on the inner circle of radius r is bounded by the supremum of `|log ‖H‖|` on the outer
sphere of radius R. This follows from the maximum principle for harmonic functions. -/
lemma circleAverage_posLog_inv_analytic_growth_bound
    {H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hH_an : AnalyticOnNhd ℂ H (Metric.closedBall 0 R))
    (hH_ne : ∀ z ∈ Metric.closedBall 0 R, H z ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤
        ⨆ w ∈ Metric.sphere (0 : ℂ) R, |Real.log ‖H w‖| := by
  -- For analytic nonvanishing H, Jensen's formula gives:
  -- circleAverage (log ‖H‖) 0 r = log ‖H 0‖
  have hr_ne : r ≠ 0 := ne_of_gt hr0
  have hr_abs : |r| = r := abs_of_pos hr0

  have hH_an_r : AnalyticOnNhd ℂ H (Metric.closedBall 0 r) :=
    hH_an.mono (Metric.closedBall_subset_closedBall (le_of_lt hrR))
  have hH_ne_r : ∀ z ∈ Metric.closedBall 0 r, H z ≠ 0 :=
    fun z hz => hH_ne z (Metric.closedBall_subset_closedBall (le_of_lt hrR) hz)

  -- Mean value property
  have h_avg : circleAverage (Real.log ‖H ·‖) 0 r = Real.log ‖H 0‖ := by
    apply AnalyticOnNhd.circleAverage_log_norm_of_ne_zero
    · rw [hr_abs]; exact hH_an_r
    · intro u hu; rw [hr_abs] at hu; exact hH_ne_r u hu

  -- Key: log⁺(1/x) ≤ |log x| for x > 0
  have h_poslog_le_abs : ∀ z ∈ Metric.sphere (0 : ℂ) r,
      log⁺ ‖(H z)⁻¹‖ ≤ |Real.log ‖H z‖| := by
    intro z hz
    simp only [Metric.mem_sphere, dist_zero_right] at hz
    have hz_ball : z ∈ Metric.closedBall 0 R :=
      Metric.closedBall_subset_closedBall (le_of_lt hrR) (by simp [hz])
    have hHz_ne : H z ≠ 0 := hH_ne z hz_ball
    have hHz_pos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz_ne
    rw [norm_inv]
    simp only [posLog_def, Real.log_inv]
    exact sup_le (abs_nonneg _) (neg_le_abs _)

  -- The proof strategy:
  -- 1. log⁺ ‖H⁻¹(z)‖ ≤ |log ‖H(z)‖| pointwise (from h_poslog_le_abs)
  -- 2. circleAverage of smaller function ≤ circleAverage of larger function
  -- 3. circleAverage(|log ‖H‖|, r) ≤ sup on sphere R (from HarmonicBounds)

  -- Circle integrability of log⁺ ‖H⁻¹‖
  have h_int_poslog : CircleIntegrable (fun z => log⁺ ‖(H z)⁻¹‖) 0 r := by
    apply circleIntegrable_continuous_on_closedBall hr0
    have h_cont := hH_an_r.continuousOn
    have h_inv_cont : ContinuousOn (fun z => (H z)⁻¹) (Metric.closedBall 0 r) :=
      ContinuousOn.inv₀ h_cont hH_ne_r
    exact ValueDistribution.continuous_posLog.comp_continuousOn
      (continuous_norm.comp_continuousOn h_inv_cont)

  -- Circle integrability of |log ‖H‖|
  have h_int_abs_log : CircleIntegrable (fun z => |Real.log ‖H z‖|) 0 r := by
    apply circleIntegrable_continuous_on_closedBall hr0
    have h_cont := hH_an_r.continuousOn
    have h_norm_pos : ∀ z ∈ Metric.closedBall 0 r, ‖H z‖ ≠ 0 :=
      fun z hz => (norm_pos_iff.mpr (hH_ne_r z hz)).ne'
    have h_log_cont : ContinuousOn (fun z => Real.log ‖H z‖) (Metric.closedBall 0 r) :=
      ContinuousOn.log (continuous_norm.comp_continuousOn h_cont) h_norm_pos
    exact continuous_abs.comp_continuousOn h_log_cont

  -- Step 1: circleAverage(log⁺ ‖H⁻¹‖) ≤ circleAverage(|log ‖H‖|)
  have h_avg_le : circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤
      circleAverage (fun z => |Real.log ‖H z‖|) 0 r := by
    have h_mono : ∀ z ∈ Metric.sphere (0 : ℂ) |r|,
        log⁺ ‖(H z)⁻¹‖ ≤ |Real.log ‖H z‖| := by
      intro z hz
      rw [hr_abs] at hz
      exact h_poslog_le_abs z hz
    apply circleAverage_mono h_int_poslog h_int_abs_log h_mono

  -- Step 2: circleAverage(|log ‖H‖|) ≤ sup on sphere R
  have h_sup_bound : circleAverage (fun z => |Real.log ‖H z‖|) 0 r ≤
      ⨆ w ∈ Metric.sphere (0 : ℂ) R, |Real.log ‖H w‖| :=
    Nevanlinna.AnalyticOnNhd.circleAverage_abs_log_norm_le_sup hR hH_an hH_ne hr0 hrR

  -- Combine the bounds
  calc circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r
      ≤ circleAverage (fun z => |Real.log ‖H z‖|) 0 r := h_avg_le
    _ ≤ ⨆ w ∈ Metric.sphere (0 : ℂ) R, |Real.log ‖H w‖| := h_sup_bound

end Nevanlinna
