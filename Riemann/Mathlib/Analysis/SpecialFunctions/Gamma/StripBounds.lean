import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Real.StarOrdered
import Riemann.Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gamma Function Bounds on Vertical Strips

This file provides explicit bounds for the complex Gamma function `Γ(s)` and the
Archimedean factor `H(s) = Γ_ℝ(s) = π^{-s/2} Γ(s/2)` in vertical strips.

## Main definitions

* `Complex.H` - The Archimedean factor `Γ_ℝ(s) = π^{-s/2} Γ(s/2)`
* `Complex.Gammaℝ.strip` - The vertical strip `{s | σ0 ≤ Re(s) ≤ 1}`
* `Complex.Gammaℝ.boundedHDerivOnStrip` - Uniform bound on `‖H'(s)‖` over a strip
* `Complex.Gammaℝ.circleBound` - Explicit circle bound for H

## Main results

* `Complex.Gammaℝ.differentiableOn_halfplane` - H is differentiable on Re(s) > 0
* `Complex.Gammaℝ.deriv_bound_on_circle` - Cauchy inequality for H' on circles
* `Complex.Gammaℝ.boundedHDerivOnStrip_via_explicit_bound` - Strip derivative bound
* `Complex.Gammaℝ.BoundedFGammaPrimeOnStrip` - Prop-level interface

## Mathematical background

The Euler integral `Γ(s) = ∫₀^∞ t^{s-1} e^{-t} dt` converges for `Re(s) > 0`.
For `0 < a ≤ Re(s) ≤ 1`, we split at `t = 1`:

1. **Integral on `[0,1]`**: Since `|t^{s-1}| = t^{Re(s)-1} ≤ t^{a-1}` for `t ∈ [0,1]`
   and `e^{-t} ≤ 1`, we have `∫₀¹ |t^{s-1} e^{-t}| dt ≤ ∫₀¹ t^{a-1} dt = 1/a`.

2. **Integral on `[1,∞)`**: Since `Re(s) ≤ 1`, we have `|t^{s-1}| ≤ 1` for `t ≥ 1`.
   The tail bound uses Gamma function convexity.

## References

* [Deligne, "Valeurs de fonctions L et périodes d'intégrales"]
* [NIST DLMF, Chapter 5]
-/

noncomputable section

open Complex Real Set Metric

namespace Complex

/-- Archimedean factor used throughout: Deligne's `Γ_ℝ(s) = π^{-s/2} Γ(s/2)`. -/
abbrev H (s : ℂ) : ℂ := Gammaℝ s

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
  -- Factorization: Γ_ℝ(s) = Γ_ℝ(s') * ∏(s-k) where s' is in (0,1]
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
        have hleft : (s.re / 2) * 2 = s.re := by
          have : s.re * (2 : ℝ) / 2 = s.re := by simp
          simp
        simpa [hleft, mul_comm, neg_mul] using h'
      have hle : s.re ≤ 0 := by
        have : 0 ≤ (2 : ℝ) * (m : ℝ) := by positivity
        simp [hsre_eq]
      exact (not_le.mpr hs) hle
    have hg : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      (differentiableAt_id.div_const (2 : ℂ))
    exact (differentiableAt_Gamma (s := s / 2) hnot).comp s hg
  simpa [Gammaℝ, Gammaℝ_def] using (h_cpow.mul h_gamma).differentiableWithinAt

/-! ### A Cauchy–derivative bound on a circle (exact, no placeholders)

We derive the standard Cauchy inequality for the derivative at a center `s` from the
Cauchy integral formula for the derivative, and a uniform bound on `‖H‖` along a circle. -/

/-- If `0 < r`, `closedBall s r ⊆ {z | 0 < re z}`, and `‖H z‖ ≤ M` for all `z` on the circle
`sphere s r`, then `‖deriv H s‖ ≤ r⁻¹ * M`. -/
theorem deriv_bound_on_circle
    {s : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hBall : closedBall s r ⊆ {z : ℂ | 0 < z.re})
    (hM : ∀ z ∈ sphere s r, ‖H z‖ ≤ M) :
    ‖deriv H s‖ ≤ r⁻¹ * M := by
  -- Cauchy integral formula for the derivative on a disk included in the half-plane
  have hUopen : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUdiff : DifferentiableOn ℂ H {z : ℂ | 0 < z.re} := differentiableOn_halfplane
  have hsub : closedBall s r ⊆ {z : ℂ | 0 < z.re} := hBall
  have hs_ball : s ∈ ball s r := by
    simp [mem_ball, dist_self, hr]
  -- Cauchy formula for derivative
  have hCauchy :
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • H z)
        = deriv H s := by
    -- use the derivative formula from RemovableSingularity
    simpa using
      (two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
        (E := ℂ) hUopen (c := s) (w₀ := s) (R := r) (hc := hsub)
        (hf := hUdiff) (hw₀ := by simpa [mem_ball, dist_self] using hr))
  have hker : ∀ z ∈ sphere s r, ‖((z - s) ^ 2)⁻¹ • H z‖ ≤ (r ^ 2)⁻¹ * M := by
    intro z hz
    have hzR : ‖z - s‖ = r := by simpa [dist_eq_norm] using hz
    have : ‖(z - s) ^ 2‖ = ‖z - s‖ ^ 2 := by simp [norm_pow]
    have : ‖(z - s) ^ 2‖ = r ^ 2 := by simp [hzR]
    calc
      ‖((z - s) ^ 2)⁻¹ • H z‖
          = ‖(z - s) ^ 2‖⁻¹ * ‖H z‖ := by simp [norm_inv]
      _ ≤ (r ^ 2)⁻¹ * M := by
        have hHM : ‖H z‖ ≤ M := hM z hz
        have hnonneg : 0 ≤ ‖(z - s) ^ 2‖⁻¹ := by
          exact inv_nonneg.mpr (norm_nonneg _)
        have hnormpow : ‖(z - s) ^ 2‖ = ‖z - s‖ ^ 2 := by simp [norm_pow]
        have hnorm : ‖(z - s) ^ 2‖ = r ^ 2 := by simp [hzR]
        have hinv : ‖(z - s) ^ 2‖⁻¹ = (r ^ 2)⁻¹ := by simp [hnorm]
        have hmul : ‖(z - s) ^ 2‖⁻¹ * ‖H z‖ ≤ ‖(z - s) ^ 2‖⁻¹ * M :=
          mul_le_mul_of_nonneg_left hHM hnonneg
        simp_rw [hinv]; aesop
  -- Apply the (2πi)^{-1}-smul integral norm bound
  have := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
              (c := s) (R := r) (hR := hr.le) (hf := hker)
  simp [mul_comm]
  -- Apply the (2πi)^{-1}-smul integral norm bound
  have hbound :
      ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • H z‖
        ≤ r * ((r ^ 2)⁻¹ * M) :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (c := s) (R := r) (hR := hr.le) (hf := hker)
  -- Use the Cauchy identity to rewrite the LHS, then simplify the RHS
  have hbound' : ‖deriv H s‖ ≤ r * ((r ^ 2)⁻¹ * M) :=
    calc
      ‖deriv H s‖
          = ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(s, r), ((z - s) ^ 2)⁻¹ • H z‖ := by
            simp_rw [hCauchy]
      _ ≤ r * ((r ^ 2)⁻¹ * M) := hbound
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hr
  have hrr : r * ((r ^ 2)⁻¹ * M) = M * r⁻¹ := by
    calc
      r * ((r ^ 2)⁻¹ * M) = (r * (r ^ 2)⁻¹) * M := by
        simp [mul_comm, mul_left_comm]
      _ = (r / r^2) * M := by simp [div_eq_mul_inv]
      _ = (1 / r) * M := by
        have : r / r^2 = 1 / r := by
          calc
            r / r^2 = r / (r * r) := by simp [pow_two]
            _ = (r / r) / r := by simp_rw [div_mul_eq_div_div]
            _ = 1 / r := by simp [hr0]
        simp [this]
      _ = M * r⁻¹ := by simp [one_div, mul_comm]
  have : ‖deriv H s‖ ≤ M * r⁻¹ := by simpa [hrr] using hbound'
  exact this

/-- If `s = σ + it` with `σ ≥ σ0 > 0` and `r = σ0/2`, then the entire closed ball `closedBall s r`
lies in the right half-plane `{z | 0 < re z}`. -/
lemma closedBall_subset_halfplane_of_re_ge
    {σ0 σ t : ℝ} (hσ0 : 0 < σ0) (hσ : σ0 ≤ σ) :
    closedBall (σ + t * I) (σ0 / 2) ⊆ {z : ℂ | 0 < z.re} := by
  intro z hz
  -- |Re(z - s)| ≤ ‖z - s‖ ≤ r ⇒ Re z ≥ Re s - r ≥ σ0 - σ0/2 = σ0/2 > 0
  have hz' : ‖z - (σ + t * I)‖ ≤ σ0 / 2 := by
    simpa [dist_eq_norm] using hz
  have hre : (z - (σ + t * I)).re ≥ -‖z - (σ + t * I)‖ := by
    -- |Re w| ≤ ‖w‖ ⇒ -‖w‖ ≤ Re w
    have := (abs_re_le_norm (z - (σ + t * I)))
    have : |(z - (σ + t * I)).re| ≤ ‖z - (σ + t * I)‖ := this
    exact neg_le_of_abs_le this
  have : z.re ≥ σ - σ0 / 2 := by
    -- z.re ≥ (σ+tI).re - ‖z-(σ+tI)‖
    have h1 : z.re ≥ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := add_le_add_right hre ((σ + t * I).re)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- (σ+tI).re - σ0/2 ≤ (σ+tI).re - ‖z-(σ+tI)‖
    have h2 : (σ + t * I).re - (σ0 / 2) ≤ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := neg_le_neg hz'
      simpa [sub_eq_add_neg] using add_le_add_left this ((σ + t * I).re)
    -- combine
    have hzre_ge : (σ + t * I).re - (σ0 / 2) ≤ z.re := le_trans h2 (h1)
    simpa [sub_eq_add_neg] using hzre_ge
  have : 0 < z.re := by
    have hσpos : 0 < σ - σ0 / 2 := by linarith
    exact lt_of_lt_of_le hσpos (by simpa [ge_iff_le] using this)
  simpa using this

/-- Circle-level Cauchy bound specialized to the strip: with `r = σ0/2`, if we have a uniform
bound `M` on `‖H‖` along each circle `sphere (σ + it) r` for `σ ∈ [σ0,1]`, then
`‖H' (σ + it)‖ ≤ (2/σ0)·M` on the strip. -/
theorem boundedHDerivOnStrip_of_uniform_circle_bound
    {σ0 M : ℝ}
    (hσ0 : (1 / 2 : ℝ) < σ0) (hσ1 : σ0 ≤ 1) (hM0 : 0 ≤ M)
    (hM : ∀ ⦃σ t : ℝ⦄, σ0 ≤ σ → σ ≤ 1 →
            ∀ z ∈ sphere (σ + t * I) (σ0 / 2), ‖H z‖ ≤ M) :
    boundedHDerivOnStrip σ0 ((2 / σ0) * M) := by
  refine ⟨hσ0, hσ1, ?_, ?_⟩
  · have : 0 ≤ 2 / σ0 := by
      have : 0 < σ0 := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ0)
      exact div_nonneg (by norm_num) this.le
    exact mul_nonneg this hM0
  · intro σ t hlo hhi
    -- radius r = σ0/2
    have hr : 0 < σ0 / 2 := by
      have : 0 < σ0 := (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ0)
      exact half_pos this
    have hBall :
        closedBall (σ + t * I) (σ0 / 2) ⊆ {z : ℂ | 0 < z.re} :=
      closedBall_subset_halfplane_of_re_ge
        ((lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hσ0)) hlo
    -- Cauchy derivative bound on the circle with uniform `M`
    have hMcircle : ∀ z ∈ sphere (σ + t * I) (σ0 / 2), ‖H z‖ ≤ M := hM hlo hhi
    have := deriv_bound_on_circle (s := σ + t * I) (r := σ0 / 2) (M := M)
                  hr hBall hMcircle
    -- r^{-1} * M = (2/σ0) * M
    simpa [inv_div, one_div, mul_comm, mul_left_comm, mul_assoc] using this

/-! ### Auxiliary lemmas for Gamma function bounds -/

/-- Integral of t^(a-1) from 0 to 1 equals 1/a for a > 0. -/
lemma integral_rpow_Ioc_zero_one {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioc 0 1, t ^ (a - 1) = 1 / a := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [integral_rpow (by simp [ha])]
  simp [ha.ne']

end Gammaℝ

end Complex

open Real Set MeasureTheory Filter Asymptotics
open scoped Real Topology

/-- If `a ≤ b` and `0 < c`, then `a / c ≤ b / c`. -/
lemma div_le_div_of_le_left' {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    a / c ≤ b / c := by
  exact div_le_div_of_nonneg_right hab hc.le

namespace Complex.Gammaℝ

/-- A uniform circle bound for `H(z) = π^{-z/2} Γ(z/2)` over the strip:
on each circle of radius `σ0/2` centered at `σ+it` with `σ ∈ [σ0,1]`, we have
`‖H z‖ ≤ π^{-(σ0/4)} * (4/σ0 + √π)`. -/
def circleBound (σ0 : ℝ) : ℝ := Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi)

lemma norm_H_on_sphere_le
    {σ0 σ t : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hlo : σ0 ≤ σ) (hhi : σ ≤ 1) :
    ∀ z ∈ sphere (σ + t * I) (σ0 / 2), ‖H z‖ ≤ circleBound σ0 := by
  intro z hz
  -- Re z ≥ σ - σ0/2 ≥ σ0/2
  have hz' : ‖z - (σ + t * I)‖ ≤ σ0 / 2 := by simpa [dist_eq_norm] using (mem_sphere.mp hz).le
  have h_re : (σ0 / 2) ≤ z.re := by
    -- z.re ≥ (σ+tI).re - ‖z-(σ+tI)‖ ≥ σ - σ0/2
    have hre : (z - (σ + t * I)).re ≥ -‖z - (σ + t * I)‖ := by
      have := (abs_re_le_norm (z - (σ + t * I)))
      exact (neg_le_of_abs_le this)
    have h1 : z.re ≥ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := add_le_add_right hre ((σ + t * I).re)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h2 : (σ + t * I).re - σ0 / 2 ≤ (σ + t * I).re - ‖z - (σ + t * I)‖ := by
      have := neg_le_neg hz'
      simpa [sub_eq_add_neg] using add_le_add_left this ((σ + t * I).re)
    have : (σ + t * I).re - σ0 / 2 ≤ z.re := le_trans h2 h1
    have : σ - σ0 / 2 ≤ z.re := by simpa [sub_eq_add_neg] using this
    exact (le_trans (by have := hlo; linarith) this)
  -- Split H and bound each factor
  have hπ : ‖(π : ℂ) ^ (-(z / 2))‖ ≤ Real.rpow Real.pi (-(σ0 / 4)) := by
    -- ‖π^{-(z/2)}‖ = π^{-Re(z)/2} ≤ π^{-σ0/4}
    have : Real.rpow Real.pi (-(z.re / 2)) ≤ Real.rpow Real.pi (-(σ0 / 4)) := by
      -- since z.re ≥ σ0/2
      have : (σ0 / 2) ≤ z.re := h_re
      -- monotonicity of x ↦ π^{-x/2}
      -- Since π > 1, Real.rpow π is monotone decreasing in negative exponents
      -- We have -(z.re/2) ≤ -(σ0/4) since z.re ≥ σ0/2
      have h_exp : -(z.re / 2) ≤ -(σ0 / 4) := by
        have : σ0 / 4 ≤ z.re / 2 := by linarith [h_re]
        linarith
      -- base > 1 for rpow monotonicity
      have hpi : (1 : ℝ) < Real.pi := by
        have : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      -- since z.re ≥ σ0/2, we have -(z.re/2) ≤ -(σ0/4)
      have hpow :
          Real.rpow Real.pi (-(z.re / 2)) ≤ Real.rpow Real.pi (-(σ0 / 4)) :=
        Real.rpow_le_rpow_of_exponent_le hpi.le h_exp
      exact hpow
    calc ‖(π : ℂ) ^ (-(z / 2))‖
        = Real.pi ^ (-(z / 2)).re := Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _
      _ = Real.pi ^ (-(z.re / 2)) := by simp [Complex.neg_re]
      _ ≤ Real.pi ^ (-(σ0 / 4)) := this
  let w := z / 2
  have hw_re : (σ0 / 4) ≤ w.re := by
    have : (σ0 / 2) ≤ z.re := h_re
    simpa [w, Complex.div_re] using
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
  -- Need to prove w.re ≤ 1 for the Gamma bound
  have hw_ub : w.re ≤ 1 := by
    -- z.re ≤ σ + σ0/2 ≤ 1 + 1/2 = 3/2, so w.re ≤ 3/4 < 1
    have h_z_ub : z.re ≤ σ + σ0 / 2 := by
      have : |z.re - σ| ≤ σ0 / 2 := by
        have := (abs_re_le_norm (z - (σ + t * I))).trans hz'
        simpa [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
                Complex.mul_re, Complex.I_re, mul_zero, add_zero] using this
      linarith [(abs_sub_le_iff.mp this).left]
    have : z.re ≤ 3/2 := by
      calc z.re
          ≤ σ + σ0 / 2 := h_z_ub
        _ ≤ 1 + 1 / 2 := by linarith [hhi, hσ0]
        _ = 3 / 2 := by norm_num
    calc w.re
        = z.re / 2 := by simp [w]
      _ ≤ (3/2) / 2 := div_le_div_of_le_left' this (by norm_num)
      _ = 3/4 := by norm_num
      _ ≤ 1 := by norm_num
  -- Classical integral bound on Γ on Re > 0: for w with Re w ≥ a,
  -- one has ‖Γ(w)‖ ≤ 1/a + √π (split the defining integral at 1 and bound).
  have hΓ : ‖Complex.Gamma w‖ ≤ 4 / σ0 + Real.sqrt Real.pi := by
    have ha : 0 < σ0 / 4 := by linarith [hσ0]
    calc ‖Complex.Gamma w‖
        ≤ 1 / (σ0 / 4) + Real.sqrt Real.pi :=
          norm_Complex_Gamma_le_of_re_ge ha hw_re hw_ub
      _ = 4 / σ0 + Real.sqrt Real.pi := by ring
  -- Combine both bounds
  have : ‖H z‖ ≤ Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi) := by
    calc ‖H z‖
        = ‖Complex.Gammaℝ z‖ := by rw [H]
      _ = ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ := by rw [Complex.Gammaℝ_def]
      _ = ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ := Complex.norm_mul _ _
      _ = ‖(π : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma w‖ := by rw [show z / 2 = w from rfl]
      _ ≤ Real.rpow Real.pi (-(σ0 / 4)) * ‖Complex.Gamma w‖ := by
        have : (π : ℂ) ^ (-z / 2) = (π : ℂ) ^ (-(z / 2)) := by ring_nf
        rw [this]
        exact mul_le_mul_of_nonneg_right hπ (norm_nonneg _)
      _ ≤ Real.rpow Real.pi (-(σ0 / 4)) * (4 / σ0 + Real.sqrt Real.pi) :=
        mul_le_mul_of_nonneg_left hΓ (Real.rpow_nonneg Real.pi_pos.le _)
  simpa [circleBound] using this

/-- Plug the explicit circle bound into the Cauchy route to get a strip-derivative bound. -/
theorem boundedHDerivOnStrip_via_explicit_bound
    {σ0 : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hσ1 : σ0 ≤ 1) :
    boundedHDerivOnStrip σ0 ((2 / σ0) * circleBound σ0) := by
  have h_nonneg : 0 ≤ circleBound σ0 := by
    have hσ0_pos : 0 < σ0 := by linarith
    unfold circleBound
    apply mul_nonneg
    · exact Real.rpow_nonneg Real.pi_pos.le _
    · apply add_nonneg
      · exact div_nonneg (by norm_num) hσ0_pos.le
      · exact Real.sqrt_nonneg _
  apply boundedHDerivOnStrip_of_uniform_circle_bound hσ0 hσ1 h_nonneg
  intro σ t hlo hhi z hz
  exact norm_H_on_sphere_le hσ0 hlo hhi z hz

/-! ### Optional: explicit constant from the "Cauchy route" (kept separate)

This section keeps your explicit numeric constant. We do not claim (here) that it is a
valid uniform circle bound; that proof belongs in a separate analytic file. -/

/-- A suggested explicit constant from the classical Cauchy-route heuristic:
`C(σ0) = (16 / σ0^2) · π^(−σ0/4)`. -/
def cauchyHPrimeBoundConstant (σ0 : ℝ) : ℝ :=
  (16 / (σ0 ^ 2)) * Real.rpow Real.pi (-(σ0 / 4))

lemma cauchyHPrimeBoundConstant_nonneg (σ0 : ℝ) :
    0 ≤ cauchyHPrimeBoundConstant σ0 := by
  have hsq : 0 ≤ σ0 ^ 2 := sq_nonneg σ0
  have h₁ : 0 ≤ (16 / (σ0 ^ 2)) := by exact div_nonneg (by norm_num) hsq
  have h₂ : 0 < Real.rpow Real.pi (-(σ0 / 4)) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  have h₂' : 0 ≤ Real.rpow Real.pi (-(σ0 / 4)) := le_of_lt h₂
  simpa [cauchyHPrimeBoundConstant] using mul_nonneg h₁ h₂'



/-- Prop-level interface: a uniform bound for the Archimedean factor derivative
`FΓ′(s)` on the closed strip `σ ∈ [σ0, 1]`, exposing the numeric constant `C ≥ 0`.

Interpretation note: In applications `C` dominates `sup_{σ∈[σ0,1], t∈ℝ} |H'(σ+it)|`
for `H(s) = π^{-s/2} Γ(s/2)`. We keep this at the Prop-level here; downstream bridges
extract the numeric witness. -/
def BoundedFGammaPrimeOnStrip (σ0 : ℝ) : Prop :=
  ∃ C : ℝ, Complex.Gammaℝ.boundedHDerivOnStrip σ0 C

/-- Convenience eliminator: extract the numeric bound `C` and its nonnegativity
from a `BoundedFGammaPrimeOnStrip σ0` hypothesis. -/
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

/-! ### Explicit Cauchy-route constant (Prop-level)

We expose an explicit σ₀-dependent constant from the Cauchy/Γ outline. -/
def cauchyHPrimeBoundConstant' (σ0 : ℝ) : ℝ :=
  (16 / (σ0 ^ 2)) * Real.rpow Real.pi (-(σ0 / 4))

lemma cauchyHPrimeBoundConstant_nonneg' (σ0 : ℝ) :
    0 ≤ cauchyHPrimeBoundConstant σ0 := by
  have hsq : 0 ≤ σ0 ^ 2 := sq_nonneg σ0
  have h₁ : 0 ≤ (16 / (σ0 ^ 2)) := by exact div_nonneg (by norm_num) hsq
  have h₂ : 0 < Real.rpow Real.pi (-(σ0 / 4)) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  have h₂' : 0 ≤ Real.rpow Real.pi (-(σ0 / 4)) := le_of_lt h₂
  simpa [cauchyHPrimeBoundConstant] using mul_nonneg h₁ h₂'

end Gammaℝ
end Complex

/-! ## Stirling-type bounds for the complex Gamma function

This section provides Stirling-type bounds on `Complex.Gamma` and the archimedean factor `Gammaℝ`
in regions of the complex plane that arise naturally in the analytic theory of
the completed zeta function, Hadamard factorization, and the Selberg class.
-/

namespace Real.Stirling

/-- For `x ≥ 1`, `log (1 + x) ≥ log 2`. -/
lemma log_one_add_ge_log_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ Real.log (1 + x) := by
  have h₂ : (0 : ℝ) < 2 := by norm_num
  have hle : (2 : ℝ) ≤ 1 + x := by linarith
  exact Real.log_le_log h₂ hle

/-- For `x ≥ 1`, `log (1 + x) > 0`. -/
lemma log_one_add_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < Real.log (1 + x) := Real.log_pos (by linarith)

/-- The simple inequality `x ≤ exp x` for all real `x`. -/
lemma le_exp_self (x : ℝ) : x ≤ Real.exp x :=
  le_trans (by linarith : x ≤ x + 1) (Real.add_one_le_exp x)

/-- A convenient bound `1 ≤ π`. -/
lemma one_le_pi : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num : (1:ℝ) ≤ 2) Real.two_le_pi

/-- `√π < 2`. -/
lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by norm_num
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le hπ4
    _ = 2 := h4

end Real.Stirling

namespace Complex.Gamma

open Real

/-- `Gamma` is bounded on any compact set that does not contain non-positive integers. -/
lemma norm_bounded_on_compact_of_no_poles {K : Set ℂ}
    (hK : IsCompact K)
    (h_poles : ∀ s ∈ K, ∀ n : ℕ, s ≠ -n) :
    ∃ M : ℝ, ∀ s ∈ K, ‖Gamma s‖ ≤ M := by
  have h_cont : ContinuousOn Gamma K := by
    refine continuousOn_of_forall_continuousAt ?_
    intro s hs
    exact (differentiableAt_Gamma s (h_poles s hs)).continuousAt
  rcases hK.exists_bound_of_continuousOn h_cont with ⟨M, hM⟩
  exact ⟨M, fun s hs => hM s hs⟩

/-- When `0 < a ≤ re w ≤ 1`, we have `‖Γ(w)‖ ≤ 1 / a + √π`. -/
theorem norm_le_strip {w : ℂ} {a : ℝ}
    (ha : 0 < a) (hw_lo : a ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi :=
  Complex.Gammaℝ.norm_Complex_Gamma_le_of_re_ge ha hw_lo hw_hi

/-- For `1/2 ≤ re w ≤ 1`, `‖Γ(w)‖ ≤ 4`. -/
lemma norm_le_four_of_re_half_to_one {w : ℂ}
    (hw_lo : (1 / 2 : ℝ) ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 4 := by
  have h := norm_le_strip (w := w) (a := (1 / 2 : ℝ)) (by norm_num) hw_lo hw_hi
  calc ‖Gamma w‖ ≤ 1 / (1 / 2 : ℝ) + Real.sqrt Real.pi := h
    _ = 2 + Real.sqrt Real.pi := by norm_num
    _ ≤ 2 + 2 := by linarith [Real.Stirling.sqrt_pi_lt_two]
    _ = 4 := by norm_num

/-- For `s : ℂ` and `n : ℕ`, the product
`∏ k ∈ Finset.range n, (s - (k + 1))` has norm at most `(‖s‖ + n)^n`. -/
lemma prod_sub_norm_le {s : ℂ} {n : ℕ} :
    ‖∏ k ∈ Finset.range n, (s - (k + 1))‖ ≤ (‖s‖ + n) ^ n := by
  calc ‖∏ k ∈ Finset.range n, (s - (k + 1))‖
      = ∏ k ∈ Finset.range n, ‖s - (k + 1)‖ := by simp
    _ ≤ ∏ _k ∈ Finset.range n, (‖s‖ + n) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro k _; exact norm_nonneg _
      · intro k hk
        have h1 : ‖s - (k + 1 : ℂ)‖ ≤ ‖s‖ + ‖(k + 1 : ℂ)‖ := norm_sub_le _ _
        have h2 : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by norm_cast
        have h3 : (k + 1 : ℝ) ≤ n := by
          have := Finset.mem_range.mp hk
          exact_mod_cast Nat.succ_le_of_lt this
        calc ‖s - (k + 1 : ℂ)‖ ≤ ‖s‖ + ‖(k + 1 : ℂ)‖ := h1
          _ = ‖s‖ + (k + 1 : ℝ) := by simp [h2]
          _ ≤ ‖s‖ + n := add_le_add_left h3 _
    _ = (‖s‖ + n) ^ n := by simp [Finset.prod_const, Finset.card_range]

/-- For any `s : ℂ`, the real part of `s' := s - ⌊Re(s)⌋` lies in `[0, 1)`. -/
lemma floor_shift_re_in_strip {s : ℂ} :
    let s' := s - (⌊s.re⌋ : ℂ)
    0 ≤ s'.re ∧ s'.re < 1 := by
  intro s'
  have h₁ : 0 ≤ s.re - (⌊s.re⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have h₂ : s.re - (⌊s.re⌋ : ℝ) < 1 := by
    have h := Int.lt_floor_add_one (s.re)
    exact (sub_lt_iff_lt_add).mpr (by simp [add_comm])
  constructor
  · simp [s']
  · simpa [s'] using h₂

/-- For `re s ≥ 1`, `‖Γ(s)‖` is bounded by a polynomial in `‖s‖`. -/
theorem norm_bound_re_ge_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖Gamma s‖ ≤ C * (1 + ‖s‖) ^ (‖s‖ + 1) := by
  use 5
  constructor
  · norm_num
  intro s hs_re
  -- The proof uses the functional equation and strip bounds
  sorry

/-- **Main Stirling bound** for `Re(s) ≥ 0`.

There exists a constant `C` such that for any `s` with `re s ≥ 0` and
`‖s‖ ≥ 1` we have `‖Γ(s)‖ ≤ exp (C · ‖s‖ · log (1 + ‖s‖))`. -/
theorem stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := norm_bound_re_ge_one
  use C₁ + 3
  constructor
  · linarith
  intro s hs_re hs_norm
  -- The proof uses polynomial bounds and the functional equation
  sorry

/-- Stirling bound specialized to `Γ(s/2)` for `re s ≥ 0`. -/
theorem half_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := stirling_bound_re_ge_zero
  use C₁ + 1
  constructor
  · linarith
  intro s hs_re hs_norm
  have hs2_re : 0 ≤ (s / 2).re := by simp; linarith
  -- The proof follows from the main Stirling bound
  sorry

end Complex.Gamma

namespace Complex.Gammaℝ.Stirling

open Real

/-- The norm of `π^{-s/2}` is at most `1` when `Re(s) ≥ 0`. -/
lemma norm_cpow_pi_neg_half_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi_pos]
  have h_re : (-s / 2).re = -s.re / 2 := by simp [Complex.neg_re]
  rw [h_re]
  have h_exp : -s.re / 2 ≤ 0 := by linarith
  have hpi_gt_1 : (1 : ℝ) < Real.pi := by
    calc (1 : ℝ) < 3 := by norm_num
      _ < Real.pi := Real.pi_gt_three
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_gt_1) h_exp

/-- **Stirling bound for the archimedean factor** `Γ_ℝ = π^{-s/2} · Γ(s/2)`. -/
theorem bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := Complex.Gamma.half_bound_re_ge_zero
  refine ⟨C₁ + 2, by linarith, ?_⟩
  intro s hs_re hs_norm
  have hdef : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    simp [Complex.Gammaℝ_def]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) :=
    hC₁ s hs_re hs_norm
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := norm_cpow_pi_neg_half_le_one hs_re
  have h1 : ‖Complex.Gammaℝ s‖ ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
    rw [hdef]; exact norm_mul_le _ _
  have h2 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := by
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * ‖Complex.Gamma (s / 2)‖ := mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
      _ = ‖Complex.Gamma (s / 2)‖ := by ring
      _ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := hΓ
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hnorm_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
  have hC_le : C₁ * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C₁ + 2) * ‖s‖ * Real.log (1 + ‖s‖) := by
    apply mul_le_mul_of_nonneg_right _ hlog_nonneg
    apply mul_le_mul_of_nonneg_right _ hnorm_nonneg
    linarith
  exact le_trans (le_trans h1 h2) (Real.exp_le_exp.mpr hC_le)

/-- Finite order bound for Γ_ℝ. -/
theorem finite_order :
    ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (A * ‖s‖ ^ B) := by
  obtain ⟨C, hC_pos, hC⟩ := bound_re_ge_zero
  use C + 1, 2
  refine ⟨by linarith, by norm_num, ?_⟩
  intro s hs_re hs_norm
  have h := hC s hs_re hs_norm
  apply le_trans h
  apply Real.exp_le_exp.mpr
  -- log(1 + |s|) ≤ |s| for |s| ≥ 1, so C|s|log(1+|s|) ≤ C|s|² ≤ (C+1)|s|²
  have h_log : Real.log (1 + ‖s‖) ≤ ‖s‖ := by
    have h1 : 0 < 1 + ‖s‖ := by linarith [norm_nonneg s]
    have h2 : ‖s‖ + 1 ≤ Real.exp ‖s‖ := Real.add_one_le_exp ‖s‖
    have h2' : 1 + ‖s‖ ≤ Real.exp ‖s‖ := by linarith
    rw [Real.log_le_iff_le_exp (by linarith [norm_nonneg s])]
    exact h2'
  have step1 : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ C * ‖s‖ * ‖s‖ := by
    apply mul_le_mul_of_nonneg_left h_log
    apply mul_nonneg (by linarith) (norm_nonneg s)
  have step2 : C * ‖s‖ * ‖s‖ = C * ‖s‖ ^ 2 := by ring
  have step3 : C * ‖s‖ ^ 2 ≤ (C + 1) * ‖s‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h_combined : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C + 1) * ‖s‖ ^ 2 := by
    calc C * ‖s‖ * Real.log (1 + ‖s‖)
        ≤ C * ‖s‖ * ‖s‖ := step1
      _ = C * ‖s‖ ^ 2 := step2
      _ ≤ (C + 1) * ‖s‖ ^ 2 := step3
  -- Convert from ℕ exponent (^ 2) to ℝ exponent (^ (2 : ℝ))
  -- The goal is (C + 1) * ‖s‖ ^ (2 : ℝ), which equals (C + 1) * ‖s‖ ^ (2 : ℕ)
  -- This type coercion is handled by norm_cast
  have hconv : (C + 1) * ‖s‖ ^ 2 = (C + 1) * ‖s‖ ^ (2 : ℝ) := by norm_cast
  rw [← hconv]
  exact h_combined

end Complex.Gammaℝ.Stirling
end
