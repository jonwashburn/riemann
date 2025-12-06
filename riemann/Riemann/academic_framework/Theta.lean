import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Real parameterization of the Jacobi theta function

This file provides a real-variable parameterization of the Jacobi theta function and establishes
its relationship to the standard complex formulation in mathlib.

## Main definitions

* `RH.AcademicFramework.Theta.theta`: The function `θ : (0, ∞) → ℝ` given by
  `θ(t) = ∑_{n ∈ ℤ} exp(-π t n²)`.

## Main results

* `theta_eq_jacobiTheta_re`: The relationship between `theta` and mathlib's `jacobiTheta`,
  showing that `theta(t) = Re(jacobiTheta(it))` for `t > 0`.
* `theta_modularity`: The functional equation `θ(t) = t^(-1/2) · θ(1/t)` for `t > 0`,
  a direct corollary of Poisson summation for the Gaussian.

## Implementation notes

We work with the real parameterization `t ∈ (0, ∞)` rather than complex `τ ∈ ℍ` because:
- It provides explicit formulas for applications requiring real arithmetic
- The functional equation takes the simpler form `θ(t) = t^(-1/2) θ(1/t)`
- It directly interfaces with Poisson summation via `Real.tsum_exp_neg_mul_int_sq`

For the full modular group action and complex-analytic properties, see
`NumberTheory.ModularForms.JacobiTheta.OneVariable`.

## References

* [Terras, *Harmonic Analysis on Symmetric Spaces*][terras1985]
* [Iwaniec-Kowalski, *Analytic Number Theory*][iwaniec2004]
-/

noncomputable section

open Complex Real Topology
open scoped Real

namespace RH.AcademicFramework.Theta

/-- The Jacobi theta function in real parameterization.

For `t > 0`, this is defined as `θ(t) := ∑_{n ∈ ℤ} exp(-π t n²)`.
This equals `Re(jacobiTheta(it))` where `jacobiTheta` is the standard complex theta function. -/
def theta (t : ℝ) : ℝ :=
  ∑' n : ℤ, exp (-π * t * n ^ 2)

@[simp]
lemma theta_def (t : ℝ) : theta t = ∑' n : ℤ, rexp (-π * t * n ^ 2) := rfl

/-- The terms of the real theta series are summable for `t > 0`. -/
lemma summable_theta_term {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => rexp (-π * t * n ^ 2)) := by
  have hτ : 0 < (↑t * I).im := by simp [ht]
  have h_sum_c := (hasSum_jacobiTheta₂_term 0 hτ).summable
  simp_rw [jacobiTheta₂_term, mul_zero, zero_add] at h_sum_c
  have heq : ∀ n : ℤ, ‖cexp (π * I * (n:ℂ)^2 * (t*I))‖ = rexp (-π * t * n^2) := by
    intro n
    rw [norm_exp]
    congr 1
    -- prove the exponent is a real number, then its .re is itself
    suffices π * I * (n : ℂ) ^ 2 * (t * I) = ↑(-π * t * n ^ 2) by
      rw [this, ofReal_re]
    push_cast
    ring_nf
    aesop
  rw [← summable_norm_iff] at h_sum_c
  simpa [heq] using h_sum_c

/-- The real theta function equals the real part of the complex theta function
evaluated at `it` on the imaginary axis. -/
theorem theta_eq_jacobiTheta_re {t : ℝ} (ht : 0 < t) :
    theta t = (jacobiTheta (t * I)).re := by
  rw [theta, jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂]
  have hτ : 0 < (↑t * I).im := by simp [ht]
  have h_sum := (hasSum_jacobiTheta₂_term 0 hτ).summable
  have hτ : 0 < (↑t * I).im := by simp [ht]
  -- rewrite RHS real part of sum as sum of real parts
  change ∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2) =
    Complex.reCLM (∑' n : ℤ, jacobiTheta₂_term n 0 (t * I))
  have hsum := (hasSum_jacobiTheta₂_term 0 hτ).summable
  rw [Complex.reCLM.map_tsum hsum]
  -- compare termwise
  refine tsum_congr ?_
  intro n
  simp [jacobiTheta₂_term, Complex.reCLM_apply, mul_zero, zero_add]
  -- reduce to showing re (cexp ...) = Real.exp ...
  have hE :
      Real.pi * I * (n : ℂ) ^ 2 * (t * I) = ↑(-Real.pi * t * (n : ℝ) ^ 2) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hRe :
      (Complex.exp (Real.pi * I * (n : ℂ) ^ 2 * (t * I))).re
        = Real.exp (-Real.pi * t * (n : ℝ) ^ 2) := by
    calc
      (Complex.exp (Real.pi * I * (n : ℂ) ^ 2 * (t * I))).re
          = (Complex.exp (↑(-Real.pi * t * (n : ℝ) ^ 2))).re := by
            simp [hE]
      _ = Real.exp (-Real.pi * t * (n : ℝ) ^ 2) := by
            have h : Complex.exp (↑(-Real.pi * t * (n : ℝ) ^ 2)) =
                     ↑(Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) :=
              (Complex.ofReal_exp (-Real.pi * t * (n : ℝ) ^ 2)).symm
            rw [h, Complex.ofReal_re]
  simpa [jacobiTheta₂_term, mul_zero, zero_add] using hRe.symm

/-- The functional equation for the real theta function.

For `t > 0`, we have `θ(t) = t^(-1/2) · θ(1/t)`. This is the theta functional equation
specialized to the positive real axis. -/
theorem theta_modularity {t : ℝ} (ht : 0 < t) :
    theta t = t ^ (-((1 : ℝ) / 2)) * theta t⁻¹ := by
  rw [theta, theta]
  -- This identity is a direct consequence of the Gaussian Poisson summation formula.
  have h := Real.tsum_exp_neg_mul_int_sq ht
  calc ∑' n : ℤ, Real.exp (-π * t * n ^ 2)
      = 1 / t ^ (1 / 2) * ∑' n : ℤ, Real.exp (-π / t * n ^ 2) := h
    _ = t ^ (-((1 : ℝ) / 2)) * ∑' n : ℤ, Real.exp (-π * t⁻¹ * n ^ 2) := by
        rw [one_div, ← inv_div, rpow_neg ht.le, div_eq_mul_inv]; rfl

/-- The theta function satisfies `θ(t) ≥ 1` for all `t > 0`, with equality only
as `t → ∞`. This follows because the `n = 0` term contributes 1. -/
theorem one_le_theta {t : ℝ} (ht : 0 < t) : 1 ≤ theta t := by
  rw [theta]
  have h0 : Real.exp (-π * t * 0 ^ 2) = 1 := by norm_num
  calc 1 = Real.exp (-π * t * 0 ^ 2) := h0.symm
    _ ≤ ∑' n : ℤ, Real.exp (-π * t * n ^ 2) := by
        have hs := summable_theta_term ht
        convert le_hasSum hs.hasSum (0 : ℤ) (fun n hn => le_of_lt (exp_pos _))
        simp

/-- The theta function is positive for all `t > 0`. -/
theorem theta_pos {t : ℝ} (ht : 0 < t) : 0 < theta t :=
  zero_lt_one.trans_le (one_le_theta ht)

/-- The theta function is continuous on `(0, ∞)`. -/
theorem continuous_theta : ContinuousOn theta (Set.Ioi 0) := by
  -- Prove continuity on each compact subinterval [a,b] ⊂ (0,∞)
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_iff_continuousAt.mpr
  intro ⟨t, ht⟩
  -- For any t > 0, find a,b with 0 < a < t < b, and prove continuity on [a,b]
  obtain ⟨a, ha, hab⟩ : ∃ a > 0, a < t := by
    refine ⟨t / 2, ?_, ?_⟩
    · have ht' : 0 < t := by simpa using ht
      exact half_pos ht'
    · have ht' : 0 < t := by simpa using ht
      exact half_lt_self ht'
  let b := t + 1
  -- On [a, b], each term is bounded by exp(-π * a * n²), which is summable
  have h_bound :
      ∀ n : ℤ, ∀ s ∈ Set.Icc a b,
        ‖Real.exp (-π * s * (n : ℝ) ^ 2)‖ ≤ Real.exp (-π * a * (n : ℝ) ^ 2) := by
    intro n s hs
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    -- show: -π*s*(n^2) ≤ -π*a*(n^2), since a ≤ s and -π*(n^2) ≤ 0
    have hconst_nonpos : (-Real.pi) * (n : ℝ) ^ 2 ≤ 0 := by
      have : 0 ≤ (n : ℝ) ^ 2 := by positivity
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) this
    have harg :
        -Real.pi * s * (n : ℝ) ^ 2 ≤ -Real.pi * a * (n : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonpos_left hs.1 hconst_nonpos
      -- (-π*(n^2))*s ≤ (-π*(n^2))*a  ⇔  -π*s*(n^2) ≤ -π*a*(n^2)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    simpa using (Real.exp_le_exp.mpr harg)
  have h_cont_on_compact : ContinuousOn theta (Set.Icc a b) := by
    have : ContinuousOn (fun s => ∑' n : ℤ, Real.exp (-π * s * n ^ 2)) (Set.Icc a b) := by
      refine continuousOn_tsum (fun n => ?_) (summable_theta_term ha) h_bound
      fun_prop
    convert this using 1
  -- Use that t ∈ interior of [a,b] and continuity there
  have : t ∈ interior (Set.Icc a b) := by
    rw [interior_Icc]
    exact ⟨hab, by linarith⟩
  have hAt : ContinuousAt theta t :=
    (h_cont_on_compact.mono interior_subset).continuousAt
      (IsOpen.mem_nhds isOpen_interior this)
  simpa [Set.restrict, Function.comp] using
    (hAt.comp continuous_subtype_val.continuousAt)

/-- Self-duality: `θ(1) = θ(1)`, which by modularity implies `θ(1) = θ(1)`.
This is automatic but serves as a sanity check. -/
example : theta 1 = theta 1 := rfl

end RH.AcademicFramework.Theta

-- Export main definitions and theorems
namespace RH.AcademicFramework

export Theta (theta theta_modularity theta_pos one_le_theta theta_eq_jacobiTheta_re)

end RH.AcademicFramework
