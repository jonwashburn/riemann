/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathematical formalization
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Data.Real.StarOrdered

/-!
# Gamma function bounds for the Riemann Hypothesis framework

This file provides Stirling-type bounds for the Gamma function and the archimedean
factor `Γ_ℝ(s) = π^{-s/2} Γ(s/2)` (Deligne's normalization).

## Main Results

* `Complex.Gammaℝ.differentiableOn_halfplane`: `Γ_ℝ` is differentiable on `{s | 0 < Re s}`.
* `Complex.Gammaℝ.boundedHDerivOnStrip`: Derivative bound in vertical strips.
* `Gamma_stirling_core`: Core Stirling bound `|Γ(s)| ≤ exp(C|s| log(B|s|))`.

## Strategy

The Stirling bounds are proved via:

1. **Strip bound**: For `0 < a ≤ Re(w) ≤ 1`, split the Euler integral at `t = 1`:
   - On `[0,1]`: `∫₀¹ |t^{w-1}| dt ≤ ∫₀¹ t^{a-1} dt = 1/a`
   - On `[1,∞)`: `∫₁^∞ |t^{w-1} e^{-t}| dt ≤ e^{-1} < √π`

2. **Functional equation extension**: Use `Γ(s+1) = s·Γ(s)` to extend from
   the strip `[0,1]` to all of `Re(s) ≥ 0`.

3. **Cauchy estimates**: For derivative bounds, use Cauchy's integral formula
   on circles contained in the right half-plane.

4. **Stirling asymptotics**: For large `|s|`, use the asymptotic
   `log Γ(s) ≈ (s - 1/2) log s - s + O(1)`.
-/

noncomputable section

open Complex Real Set Metric MeasureTheory Filter Topology
open scoped Real Topology

namespace Complex

/-- Archimedean factor: Deligne's `Γ_ℝ(s) = π^{-s/2} Γ(s/2)`. -/
abbrev H (s : ℂ) : ℂ := Gammaℝ s

/-! ## Part 1: Strip bounds for Gamma function -/

namespace Gammaℝ

/-- Closed vertical strip `σ ∈ [σ0, 1]` as a subset of `ℂ`. -/
def strip (σ0 : ℝ) : Set ℂ := { s : ℂ | σ0 ≤ s.re ∧ s.re ≤ 1 }

/-- Uniform bound for `‖(d/ds)H(s)‖` on the closed strip `σ ∈ [σ0, 1]`. -/
def boundedHDerivOnStrip (σ0 : ℝ) (C : ℝ) : Prop :=
  (1 / 2 : ℝ) < σ0 ∧ σ0 ≤ 1 ∧ 0 ≤ C ∧
  ∀ ⦃σ t : ℝ⦄, σ0 ≤ σ → σ ≤ 1 →
    ‖deriv H (σ + t * I)‖ ≤ C

/-- Existence form for the strip bound. -/
def boundedHDerivOnStripExists (σ0 : ℝ) : Prop :=
  (1 / 2 : ℝ) < σ0 ∧ σ0 ≤ 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
    (∀ ⦃σ t : ℝ⦄, σ0 ≤ σ → σ ≤ 1 → ‖deriv H (σ + t * I)‖ ≤ C)

/-- Extract a nonnegative constant from an existence witness. -/
theorem existsConst_of_boundedHDerivOnStripExists
    {σ0 : ℝ} (h : boundedHDerivOnStripExists σ0) :
    ∃ C : ℝ, 0 ≤ C := by
  rcases h with ⟨_, _, ⟨C, hC0, _⟩⟩
  exact ⟨C, hC0⟩

/-! ### Analyticity of `Γ_ℝ` on the right half-plane -/

/-- `Γ_ℝ` is complex differentiable on the open half-plane `{s | 0 < re s}`. -/
lemma differentiableOn_halfplane :
    DifferentiableOn ℂ Gammaℝ {s : ℂ | 0 < s.re} := by
  intro s hs
  -- Factorization: Γ_ℝ(s) = (π : ℂ) ^ (-s/2) * Gamma (s/2)
  have h_cpow : DifferentiableAt ℂ (fun z : ℂ => (π : ℂ) ^ (-z / 2)) s := by
    refine ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow ?_)
    exact Or.inl (ofReal_ne_zero.mpr pi_ne_zero)
  have h_gamma : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s := by
    have hnot : ∀ m : ℕ, s / 2 ≠ -m := by
      intro m hsm
      have hre := congrArg Complex.re hsm
      have hdiv : s.re / 2 = -(m : ℝ) := by
        simpa [div_ofNat_re, Complex.ofReal_intCast] using hre
      have hsre_eq : s.re = -(2 * (m : ℝ)) := by
        have h' := congrArg (fun x : ℝ => x * 2) hdiv
        have hleft : (s.re / 2) * 2 = s.re := by simp
        simpa [hleft, mul_comm, neg_mul] using h'
      have hle : s.re ≤ 0 := by
        have : 0 ≤ (2 : ℝ) * (m : ℝ) := by positivity
        simp [hsre_eq]
      exact (not_le.mpr hs) hle
    have hg : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      (differentiableAt_id.div_const (2 : ℂ))
    exact (differentiableAt_Gamma (s := s / 2) hnot).comp s hg
  simpa [Gammaℝ, Gammaℝ_def] using (h_cpow.mul h_gamma).differentiableWithinAt

/-! ### Cauchy derivative bounds -/

/-- If `s = σ + it` with `σ ≥ σ0 > 0` and `r = σ0/2`, then the entire closed ball
`closedBall s r` lies in the right half-plane `{z | 0 < re z}`. -/
lemma closedBall_subset_halfplane_of_re_ge
    {σ0 σ t : ℝ} (hσ0 : 0 < σ0) (hσ : σ0 ≤ σ) :
    closedBall (σ + t * I) (σ0 / 2) ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  have hz' : ‖z - (σ + t * I)‖ ≤ σ0 / 2 := by simpa [dist_eq_norm] using hz
  have hre : (z - (σ + t * I)).re ≥ -‖z - (σ + t * I)‖ := by
    have := (abs_re_le_norm (z - (σ + t * I)))
    exact neg_le_of_abs_le this
  have hz_re : z.re ≥ σ - σ0 / 2 := by
    have h1 : z.re ≥ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := add_le_add_right hre ((σ + t * I).re)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 : (σ + t * I).re - (σ0 / 2) ≤ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := neg_le_neg hz'
      simpa [sub_eq_add_neg] using add_le_add_left this ((σ + t * I).re)
    have hzre_ge : (σ + t * I).re - (σ0 / 2) ≤ z.re := le_trans h2 h1
    simpa [sub_eq_add_neg] using hzre_ge
  have : 0 < z.re := by
    have hσpos : 0 < σ - σ0 / 2 := by linarith
    exact lt_of_lt_of_le hσpos (by simpa [ge_iff_le] using hz_re)
  simpa using this

/-- Circle bound for `Γ_ℝ`. -/
def circleBound (σ0 : ℝ) : ℝ := Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi)

/-- Circle bound is nonnegative for positive σ0. -/
lemma circleBound_nonneg {σ0 : ℝ} (hσ0 : 0 < σ0) : 0 ≤ circleBound σ0 := by
  unfold circleBound
  apply mul_nonneg
  · exact Real.rpow_nonneg (le_of_lt Real.pi_pos) _
  · apply add_nonneg
    · apply div_nonneg; norm_num
      exact le_of_lt hσ0
    · exact Real.sqrt_nonneg _

/-- Explicit Cauchy-route constant. -/
def cauchyHPrimeBoundConstant (σ0 : ℝ) : ℝ :=
  (16 / (σ0 ^ 2)) * Real.rpow Real.pi (-(σ0 / 4))

lemma cauchyHPrimeBoundConstant_nonneg (σ0 : ℝ) :
    0 ≤ cauchyHPrimeBoundConstant σ0 := by
  have hsq : 0 ≤ σ0 ^ 2 := sq_nonneg σ0
  have h₁ : 0 ≤ (16 / (σ0 ^ 2)) := div_nonneg (by norm_num) hsq
  have h₂ : 0 < Real.rpow Real.pi (-(σ0 / 4)) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  exact mul_nonneg h₁ (le_of_lt h₂)

/-- Cauchy derivative bound on strip using explicit constants. -/
theorem boundedHDerivOnStrip_via_explicit_bound
    {σ0 : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hσ1 : σ0 ≤ 1) :
    boundedHDerivOnStrip σ0 ((2 / σ0) * circleBound σ0) := by
  have hσ0_pos : 0 < σ0 := lt_trans (by norm_num : (0 : ℝ) < 1/2) hσ0
  refine ⟨hσ0, hσ1, ?_, ?_⟩
  · apply mul_nonneg
    · exact div_nonneg (by norm_num) (le_of_lt hσ0_pos)
    · exact circleBound_nonneg hσ0_pos
  · intro σ t hlo hhi
    -- Use the Cauchy derivative bound with circle radius σ0/2
    have hr : 0 < σ0 / 2 := half_pos hσ0_pos
    have hBall : closedBall (σ + t * I) (σ0 / 2) ⊆ {z : ℂ | 0 < z.re} :=
      closedBall_subset_halfplane_of_re_ge hσ0_pos hlo
    -- Bound H on the circle by circleBound σ0
    have hM : ∀ z ∈ sphere (σ + t * I) (σ0 / 2), ‖H z‖ ≤ circleBound σ0 := by
      intro z hz
      -- Points on the sphere have Re z ≥ σ - σ0/2 ≥ σ0/2
      have hz_dist : dist z (σ + t * I) = σ0 / 2 := mem_sphere.mp hz
      have hz_re : σ0 / 2 ≤ z.re := by
        have hnorm : ‖z - (σ + t * I)‖ = σ0 / 2 := by
          rw [dist_eq_norm] at hz_dist
          exact hz_dist
        have hre_bound : z.re ≥ σ - σ0 / 2 := by
          have h1 : (z - (σ + t * I)).re ≥ -‖z - (σ + t * I)‖ :=
            neg_le_of_abs_le (abs_re_le_norm _)
          have h2 : z.re = (σ + t * I).re + (z - (σ + t * I)).re := by ring_nf
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_zero] at h2
          calc z.re = σ + (z - (σ + t * I)).re := h2
            _ ≥ σ + (-‖z - (σ + t * I)‖) := add_le_add_left h1 σ
            _ = σ - ‖z - (σ + t * I)‖ := by ring
            _ = σ - σ0 / 2 := by rw [hnorm]
        linarith [hlo]
      -- Also z.re ≤ σ + σ0/2 ≤ 1 + 1/2 < 2
      have hz_re_ub : z.re ≤ 3/2 := by
        have hnorm : ‖z - (σ + t * I)‖ = σ0 / 2 := by
          rw [dist_eq_norm] at hz_dist; exact hz_dist
        have hre_bound : z.re ≤ σ + σ0 / 2 := by
          have h1 : (z - (σ + t * I)).re ≤ ‖z - (σ + t * I)‖ :=
            (abs_re_le_norm _).trans (le_abs_self _)
          have h2 : z.re = (σ + t * I).re + (z - (σ + t * I)).re := by ring
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_zero] at h2
          calc z.re = σ + (z - (σ + t * I)).re := h2
            _ ≤ σ + ‖z - (σ + t * I)‖ := add_le_add_left h1 σ
            _ = σ + σ0 / 2 := by rw [hnorm]
        calc z.re ≤ σ + σ0 / 2 := hre_bound
          _ ≤ 1 + 1 / 2 := by linarith [hhi, hσ0]
          _ = 3 / 2 := by norm_num
      -- Now bound ‖H z‖ using the definition of circleBound
      unfold circleBound H Gammaℝ
      rw [Gammaℝ_def, norm_mul]
      -- ‖π^{-z/2}‖ ≤ π^{-σ0/4}
      have hpi_bound : ‖(Real.pi : ℂ) ^ (-z / 2)‖ ≤ Real.rpow Real.pi (-(σ0 / 4)) := by
        rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        apply Real.rpow_le_rpow_of_exponent_le Real.one_le_pi
        simp only [neg_div, neg_re, div_ofNat_re]
        linarith [hz_re]
      -- ‖Γ(z/2)‖ ≤ 4/σ0 + √π
      have hgamma_bound : ‖Gamma (z / 2)‖ ≤ 4 / σ0 + Real.sqrt Real.pi := by
        have hz2_re : σ0 / 4 ≤ (z / 2).re := by
          simp only [div_ofNat_re]
          linarith [hz_re]
        have hz2_re_ub : (z / 2).re ≤ 1 := by
          simp only [div_ofNat_re]
          linarith [hz_re_ub]
        have ha : 0 < σ0 / 4 := by linarith
        calc ‖Gamma (z / 2)‖
            ≤ 1 / (σ0 / 4) + Real.sqrt Real.pi :=
              norm_Gamma_le_of_re_in_strip ha hz2_re hz2_re_ub
          _ = 4 / σ0 + Real.sqrt Real.pi := by ring
      calc ‖(Real.pi : ℂ) ^ (-z / 2)‖ * ‖Gamma (z / 2)‖
          ≤ Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi) := by
            apply mul_le_mul hpi_bound hgamma_bound (norm_nonneg _)
            exact Real.rpow_nonneg (le_of_lt Real.pi_pos) _
    -- Apply the Cauchy derivative bound
    have hderiv := deriv_bound_on_circle hr hBall hM
    calc ‖deriv H (σ + t * I)‖
        ≤ (σ0 / 2)⁻¹ * circleBound σ0 := hderiv
      _ = (2 / σ0) * circleBound σ0 := by rw [inv_div]; ring



/-! ## Part 2: Strip bound for Gamma norm -/

/-- **Key strip bound**: For `0 < a ≤ Re(w) ≤ 1`, `‖Γ(w)‖ ≤ 1/a + √π`. -/
theorem norm_Gamma_le_of_re_in_strip {w : ℂ} {a : ℝ}
    (ha : 0 < a) (hw_lo : a ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi := by
  -- Split the Euler integral at t = 1
  have hw_pos : 0 < w.re := lt_of_lt_of_le ha hw_lo
  have hGamma_eq : Gamma w = GammaIntegral w := Gamma_eq_integral hw_pos
  -- The integral ∫₀^∞ t^{w-1} e^{-t} dt splits as:
  -- - On [0,1]: |t^{w-1}| ≤ t^{a-1}, so integral ≤ 1/a
  -- - On [1,∞): |t^{w-1}| ≤ 1, so integral ≤ e^{-1} < √π
  sorry

/-! ## Part 3: Stirling core bound -/

/-- **Core Stirling bound** for the complex Gamma function in the right half-plane.

There exist absolute constants `C, A, B > 0` such that for all `s` with
`Re(s) ≥ 1/2` and `‖s‖ ≥ A` we have `‖Γ(s)‖ ≤ exp(C‖s‖ log(B‖s‖))`. -/
theorem Gamma_stirling_core :
    ∃ C A B : ℝ, 0 < C ∧ 0 < A ∧ 1 ≤ B ∧
      ∀ ⦃s : ℂ⦄, (1 / 2 : ℝ) ≤ s.re → A ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (B * ‖s‖)) := by
  -- Choose explicit constants
  use 3, 2, 2
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro s hs_re hs_norm

  -- For large |s|, use Stirling asymptotics:
  -- log|Γ(s)| ≈ (Re(s) - 1/2) log|s| - Re(s) + O(1)
  -- This gives |Γ(s)| ≤ |s|^{Re(s)-1/2} e^{-Re(s)} × polynomial factors
  -- ≤ |s|^{|s|} for large enough |s|
  -- ≤ exp(|s| log|s|)
  -- ≤ exp(C|s| log(B|s|)) for appropriate C, B

  by_cases h_re_ge_one : 1 ≤ s.re
  · -- Case: Re(s) ≥ 1 - use polynomial bound → exponential
    sorry
  · -- Case: 1/2 ≤ Re(s) < 1 - use strip bound
    push_neg at h_re_ge_one
    have h := norm_Gamma_le_of_re_in_strip (a := 1/2) (by norm_num) hs_re (le_of_lt h_re_ge_one)
    -- Show 1/(1/2) + √π ≤ 4 ≤ exp(3·2·log(2·2)) = exp(6 log 4) = 4^6
    have h_bound : 1 / (1/2 : ℝ) + Real.sqrt Real.pi ≤ 4 := by
      have hsqrt : Real.sqrt Real.pi < 2 := by
        have : Real.pi < 4 := Real.pi_lt_four
        have h4 : Real.sqrt 4 = 2 := by norm_num
        calc Real.sqrt Real.pi < Real.sqrt 4 :=
              Real.sqrt_lt_sqrt (le_of_lt Real.pi_pos) this
          _ = 2 := h4
      linarith
    have h_exp_large : (4 : ℝ) ≤ Real.exp (3 * 2 * Real.log (2 * 2)) := by
      rw [Real.exp_mul_log (by norm_num : (0 : ℝ) < 2 * 2)]
      norm_num
      -- 4 ≤ 4^6 = 4096
      have : (4 : ℝ) ^ 6 = 4096 := by norm_num
      linarith
    calc ‖Gamma s‖
        ≤ 1 / (1/2 : ℝ) + Real.sqrt Real.pi := h
      _ ≤ 4 := h_bound
      _ ≤ Real.exp (3 * 2 * Real.log (2 * 2)) := h_exp_large
      _ ≤ Real.exp (3 * ‖s‖ * Real.log (2 * ‖s‖)) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left hs_norm; norm_num
          · apply Real.log_le_log (by norm_num)
            apply mul_le_mul_of_nonneg_left hs_norm; norm_num
          · apply Real.log_nonneg; norm_num
          · apply mul_nonneg; norm_num; linarith

/-! ## Part 4: General Stirling bounds -/

/-- Stirling bound for `Γ(s)` when `Re(s) ≥ 0` and `‖s‖ ≥ 1`. -/
theorem Gamma_stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₀, A₀, B₀, hC₀, hA₀, hB₀, h_core⟩ := Gamma_stirling_core
  use max C₀ 10
  constructor
  · exact lt_max_of_lt_left hC₀
  intro s hs_re hs_norm
  -- Extend from Re(s) ≥ 1/2 to Re(s) ≥ 0 using functional equation
  by_cases h_half : (1/2 : ℝ) ≤ s.re
  · -- Use core bound
    by_cases h_A : A₀ ≤ ‖s‖
    · -- Large |s|
      have h := h_core h_half h_A
      calc ‖Gamma s‖
          ≤ Real.exp (C₀ * ‖s‖ * Real.log (B₀ * ‖s‖)) := h
        _ ≤ Real.exp (max C₀ 10 * ‖s‖ * Real.log (1 + ‖s‖)) := by
            apply Real.exp_le_exp.mpr
            apply mul_le_mul
            · apply mul_le_mul_of_nonneg_right (le_max_left _ _) hs_norm
            · apply Real.log_le_log
              · calc 0 < 1 := by norm_num
                  _ ≤ B₀ := hB₀
                  _ ≤ B₀ * ‖s‖ := by linarith [hs_norm, hB₀]
              · calc B₀ * ‖s‖ ≤ B₀ * ‖s‖ + 1 := by linarith
                  _ ≤ 1 + B₀ * ‖s‖ := by ring
                  _ ≤ 1 + ‖s‖ * ‖s‖ := by
                      apply add_le_add_left
                      calc B₀ * ‖s‖ ≤ ‖s‖ * ‖s‖ := by
                            apply mul_le_mul
                            · calc B₀ ≤ 2 := by linarith [hB₀]
                                _ ≤ ‖s‖ := hs_norm
                            · exact le_refl _
                            · exact norm_nonneg _
                            · exact norm_nonneg _
                  _ ≤ 1 + ‖s‖ := by linarith [hs_norm]
            · apply Real.log_nonneg; linarith [hs_norm]
            · apply mul_nonneg (le_max_of_le_left (le_of_lt hC₀)) hs_norm
    · -- Small |s|
      sorry
  · -- Case: 0 ≤ Re(s) < 1/2 - use functional equation Γ(s) = Γ(s+1)/s
    sorry

/-- Stirling bound for `Γ(s/2)` when `Re(s) ≥ 0` and `‖s‖ ≥ 1`. -/
theorem Gamma_half_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := Gamma_stirling_bound_re_ge_zero
  use 2 * C₀
  constructor
  · linarith
  intro s hs_re hs_norm
  by_cases h_large : 2 ≤ ‖s‖
  · -- |s| ≥ 2 implies |s/2| ≥ 1
    have h_half_re : 0 ≤ (s / 2).re := by simp [div_re]; linarith
    have h_half_norm : 1 ≤ ‖s / 2‖ := by
      rw [norm_div, Complex.norm_ofNat]
      linarith
    have h := hC₀ (s / 2) h_half_re h_half_norm
    calc ‖Gamma (s / 2)‖
        ≤ Real.exp (C₀ * ‖s / 2‖ * Real.log (1 + ‖s / 2‖)) := h
      _ ≤ Real.exp (C₀ * (‖s‖ / 2) * Real.log (1 + ‖s‖)) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul
          · rw [norm_div, Complex.norm_ofNat]
          · apply Real.log_le_log
            · calc 0 < 1 := by norm_num
                _ ≤ 1 + ‖s / 2‖ := by linarith [norm_nonneg (s / 2)]
            · calc 1 + ‖s / 2‖ = 1 + ‖s‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
                _ ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
          · apply Real.log_nonneg; linarith [norm_nonneg (s / 2)]
          · apply mul_nonneg (le_of_lt hC₀_pos)
            rw [norm_div, Complex.norm_ofNat]
            linarith [norm_nonneg s]
      _ = Real.exp ((C₀ / 2) * ‖s‖ * Real.log (1 + ‖s‖)) := by ring_nf
      _ ≤ Real.exp ((2 * C₀) * ‖s‖ * Real.log (1 + ‖s‖)) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_right; linarith; exact hs_norm
          · apply Real.log_nonneg; linarith [hs_norm]
  · -- 1 ≤ |s| < 2 - use compactness
    sorry

/-- Stirling bound for `Γ_ℝ(s)` when `Re(s) ≥ 0` and `‖s‖ ≥ 1`. -/
theorem Gammaℝ_stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gammaℝ s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := Gamma_half_bound_re_ge_zero
  use C₀ + 2
  constructor
  · linarith
  intro s hs_re hs_norm

  -- Gammaℝ s = π^{-s/2} * Gamma (s/2)
  have h_def : Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) := Gammaℝ_def s

  -- Bound |π^{-s/2}| ≤ 1 for Re(s) ≥ 0
  have h_pi_bound : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos Real.one_le_pi
    simp [neg_div, div_re]
    linarith [hs_re]

  calc ‖Gammaℝ s‖
      = ‖(Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2)‖ := by rw [h_def]
    _ = ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Gamma (s / 2)‖ := norm_mul _ _
    _ ≤ 1 * ‖Gamma (s / 2)‖ := mul_le_mul_of_nonneg_right h_pi_bound (norm_nonneg _)
    _ = ‖Gamma (s / 2)‖ := one_mul _
    _ ≤ Real.exp (C₀ * ‖s‖ * Real.log (1 + ‖s‖)) := hC₀ s hs_re hs_norm
    _ ≤ Real.exp ((C₀ + 2) * ‖s‖ * Real.log (1 + ‖s‖)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right; linarith; exact hs_norm
        · apply Real.log_nonneg; linarith [hs_norm]

end Complex

/-! ## Academic Framework Interface -/

namespace RH.AcademicFramework.GammaBounds

open Complex Real

/-- Prop-level interface for bounded derivative on strip. -/
def BoundedFGammaPrimeOnStrip (σ0 : ℝ) : Prop :=
  ∃ C : ℝ, Complex.Gammaℝ.boundedHDerivOnStrip σ0 C

/-- Extract constant from existence proof. -/
theorem exists_const_of_BoundedFGammaPrimeOnStrip
    {σ0 : ℝ} (h : BoundedFGammaPrimeOnStrip σ0) :
    ∃ C : ℝ, 0 ≤ C := by
  rcases h with ⟨C, hC⟩
  exact ⟨C, hC.2.2.1⟩

/-- Existence of bounded derivative on strip for σ0 > 1/2. -/
theorem boundedFGammaPrimeOnStrip_of
    {σ0 : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hσ1 : σ0 ≤ 1) :
    BoundedFGammaPrimeOnStrip σ0 := by
  refine ⟨(2 / σ0) * Complex.Gammaℝ.circleBound σ0, ?_⟩
  exact Complex.Gammaℝ.boundedHDerivOnStrip_via_explicit_bound hσ0 hσ1

end RH.AcademicFramework.GammaBounds

end
