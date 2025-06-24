import rh.Common
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Riemann Zeta Function Zero Symmetry

This file proves that zeros of the Riemann zeta function in the critical strip
come in symmetric pairs: if ζ(s) = 0 then ζ(1-s) = 0.

This follows directly from the functional equation already in mathlib.
-/

namespace RH.ZetaFunctionalEquation

open Complex Real

/-- If ζ(s) = 0 in the critical strip, then ζ(1-s) = 0 by the functional equation -/
theorem zeta_zero_symmetry {s : ℂ} (h_strip : 0 < s.re ∧ s.re < 1)
    (hζ : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  -- Use the functional equation from mathlib:
  -- π^{-s/2} Γ(s/2) ζ(s) = π^{-(1-s)/2} Γ((1-s)/2) ζ(1-s)
  -- The functional equation from mathlib
  have hFE := riemannZeta.functional_equation s

  -- Since ζ(s) = 0, the left side is 0
  rw [hζ, mul_zero, mul_zero] at hFE

  -- The right side must also be 0
  -- We need to show that the Gamma and pi factors are non-zero

  -- Γ((1-s)/2) ≠ 0 in the critical strip
  have h_gamma_ne_zero : Complex.Gamma ((1 - s) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    -- (1-s)/2 is not a negative integer when 0 < Re(s) < 1
    intro ⟨n, hn⟩
    -- If (1-s)/2 = -n, then 1-s = -2n, so s = 1 + 2n
    have : s.re = 1 + 2 * n := by
      have h_eq : (1 - s) / 2 = -n := hn
      have : 1 - s = -2 * n := by
        rw [← h_eq]
        ring
      rw [Complex.sub_re, Complex.one_re] at this
      linarith
    -- But then Re(s) ≥ 1, contradicting Re(s) < 1
    linarith [h_strip.2]

  -- π^{-(1-s)/2} ≠ 0 (pi to any power is non-zero)
  have h_pi_ne_zero : Real.pi ^ (-(1 - s) / 2).re ≠ 0 := by
    exact Real.rpow_pos_of_pos Real.pi_pos _

  -- From 0 = π^{-(1-s)/2} * Γ((1-s)/2) * ζ(1-s) and the non-zero factors,
  -- we conclude ζ(1-s) = 0
  have h_prod : Real.pi ^ (-(1 - s) / 2).re * Complex.abs (Complex.Gamma ((1 - s) / 2)) *
                Complex.abs (riemannZeta (1 - s)) = 0 := by
    rw [← Complex.abs_mul, ← Complex.abs_mul]
    rw [← Complex.abs_ofReal]
    convert Complex.abs_zero
    exact hFE

  rw [mul_eq_zero, mul_eq_zero] at h_prod
  cases h_prod with
  | inl h => cases h with
    | inl h' => exact absurd h' h_pi_ne_zero
    | inr h' => exact absurd h' (Complex.abs.ne_zero h_gamma_ne_zero)
  | inr h => exact Complex.abs.eq_zero.mp h

end RH.ZetaFunctionalEquation
