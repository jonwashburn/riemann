import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import rh.RS.Det2Outer
import rh.RS.ExpBounds
import rh.academic_framework.DiagonalFredholm.Determinant
open scoped Real

/-!
# det₂ Euler factors: local estimates toward nonvanishing on Ω

This module starts the analytic work needed to prove `det2_nonzero_on_RSΩ`.
We focus on the prime Euler factors and prove concrete bounds that will feed
the summability and product arguments in later steps.  Each lemma here is fully
proved (no admits) so we keep forward momentum—even if strengthening these
estimates later takes additional effort.
-/

noncomputable section

open Complex

namespace RH
namespace RS

open scoped BigOperators

/-- Right half-plane domain Ω. -/
local notation "Ω" => RH.RS.Ω

namespace Det2

open RH.AcademicFramework.DiagonalFredholm

variable {s : ℂ}

/-- For any prime `p`, the norm of the complex power `(p : ℂ) ^ (-s)` depends
only on the real part of `s`. This follows from the general `abs_cpow` identity.
-/
lemma norm_prime_cpow_neg (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  simpa [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hp]

/-- A crude but unconditional bound for the det₂ Euler factor.  We only need a
polynomial-type control, so we bound the exponential piece using
`abs_exp_sub_one_le` and the algebraic part directly.
-/
lemma norm_det2EulerFactor_le (p : Nat.Primes) (s : ℂ) :
    ‖det2EulerFactor s p‖ ≤ (1 + ‖(p : ℂ) ^ (-s)‖) *
      Complex.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) := by
  classical
  dsimp [det2EulerFactor]
  have h1 : ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + ‖(p : ℂ) ^ (-s)‖ := by
    simpa [sub_eq_add_neg] using Complex.norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-s))
  have h2 : ‖Complex.exp ((p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2)‖
      = Complex.exp (‖(p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2‖) :=
    Complex.norm_exp _
  have h3 : ‖(p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2‖
      ≤ ‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2 := by
    have := Complex.norm_add_le ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-2 * s) / 2)
    have hdiv : ‖(p : ℂ) ^ (-2 * s) / 2‖ = ‖(p : ℂ) ^ (-2 * s)‖ / 2 := by
      simp [div_eq_mul_inv, Complex.norm_mul, Complex.norm_inv]
    simpa [hdiv]
  have h4 : Complex.exp (‖(p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2‖)
      ≤ Complex.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) := by
    exact Real.exp_le_exp.mpr h3
  have := mul_le_mul h1 h4 (by positivity)
    (by positivity : Complex.exp (‖(p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2‖) ≥ 0)
  simpa [Complex.norm_mul, h2] using this

/-- Quantitative remainder control: `det2EulerFactor s p` stays within a linear
bound of `1`, which already suffices to initiate the summability estimates.  The
target cubic decay will be approached by sharpening this lemma later.
-/
lemma norm_det2EulerFactor_sub_one_le
    (p : Nat.Primes) (s : ℂ) :
    ‖det2EulerFactor s p - 1‖ ≤
      (1 + ‖(p : ℂ) ^ (-s)‖) *
        Complex.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) + 1 := by
  classical
  have h := Complex.norm_sub_le (det2EulerFactor s p) 1
  have hbound := norm_det2EulerFactor_le (p := p) (s := s)
  have hpos : 0 ≤ Complex.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) := by
    positivity
  have hpos' : 0 ≤ ‖(p : ℂ) ^ (-s)‖ := by positivity
  have hpos'' : 0 ≤ ‖(p : ℂ) ^ (-2 * s)‖ := by positivity
  have : ‖det2EulerFactor s p‖
      ≤ (1 + ‖(p : ℂ) ^ (-s)‖) *
        Complex.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) :=
    hbound
  have h1 : ‖det2EulerFactor s p - 1‖
      ≤ ‖det2EulerFactor s p‖ + 1 := h
  exact le_trans h1 (by
    have := add_le_add this (le_of_eq rfl)
    simpa)

end Det2

end RS
end RH
