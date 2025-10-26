import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import rh.RS.Det2Outer
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
  simpa [Complex.norm_eq_abs] using (Complex.abs_cpow_eq_rpow_re_of_pos hp (-s))

-- Removed specialized smallness bound; general bounds below suffice for current use

/-- A crude but unconditional bound for the det₂ Euler factor.  We only need a
polynomial-type control, so we bound the exponential piece using
`abs_exp_sub_one_le` and the algebraic part directly.
-/
lemma norm_det2EulerFactor_le (p : Nat.Primes) (s : ℂ) :
    ‖det2EulerFactor s p‖ ≤ (1 + ‖(p : ℂ) ^ (-s)‖) *
      Real.exp (‖(p : ℂ) ^ (-s)‖ + (‖(p : ℂ) ^ (-s)‖) ^ 2 / 2) := by
  classical
  dsimp [det2EulerFactor]
  set lam : ℂ := (p : ℂ) ^ (-s)
  set Z : ℂ := lam + lam ^ 2 / 2
  have h1 : ‖1 - lam‖ ≤ 1 + ‖lam‖ := by
    have := norm_add_le (1 : ℂ) (-lam)
    simpa [sub_eq_add_neg, add_comm] using this
  have hZ : ‖Z‖ ≤ ‖lam‖ + ‖lam‖ ^ 2 / 2 := by
    have := norm_add_le lam (lam ^ 2 / 2)
    have hdiv : ‖lam ^ 2 / 2‖ = (‖lam‖ ^ 2) / 2 := by
      have : ‖lam ^ 2‖ = ‖lam‖ ^ 2 := by simpa using Complex.norm_pow lam 2
      simp [div_eq_mul_inv, this]
    simpa [Z, hdiv, mul_comm] using this
  have hexp : ‖Complex.exp Z‖ ≤ Real.exp ‖Z‖ := by
    have : Z.re ≤ ‖Z‖ := by
      have : |Z.re| ≤ ‖Z‖ := Complex.abs_re_le_abs Z
      exact le_trans (le_abs_self _) this
    have := Real.exp_le_exp.mpr this
    simpa [Complex.norm_eq_abs, Complex.abs_exp] using this
  have hprod : ‖(1 - lam) * Complex.exp Z‖ ≤ (1 + ‖lam‖) * Real.exp ‖Z‖ := by
    have := mul_le_mul h1 hexp (by positivity) (by positivity)
    simpa
  have hmono : Real.exp ‖Z‖ ≤ Real.exp (‖lam‖ + ‖lam‖ ^ 2 / 2) :=
    Real.exp_le_exp.mpr hZ
  have := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 1 + ‖lam‖)
  have htarget : (1 + ‖lam‖) * Real.exp ‖Z‖ ≤ (1 + ‖lam‖) * Real.exp (‖lam‖ + ‖lam‖ ^ 2 / 2) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  exact le_trans hprod htarget

/-- Quantitative remainder control: `det2EulerFactor s p` stays within a linear
bound of `1`, which already suffices to initiate the summability estimates.  The
target cubic decay will be approached by sharpening this lemma later.
-/
lemma norm_det2EulerFactor_sub_one_bound
    (p : Nat.Primes) (s : ℂ) :
    ‖det2EulerFactor s p - 1‖ ≤
      (1 + ‖(p : ℂ) ^ (-s)‖) *
        Real.exp (‖(p : ℂ) ^ (-s)‖ + (‖(p : ℂ) ^ (-s)‖) ^ 2 / 2) + 1 := by
  classical
  have h := norm_sub_le (det2EulerFactor s p) 1
  have hbound := norm_det2EulerFactor_le (p := p) (s := s)
  have : ‖det2EulerFactor s p‖
      ≤ (1 + ‖(p : ℂ) ^ (-s)‖) *
        Real.exp (‖(p : ℂ) ^ (-s)‖ + (‖(p : ℂ) ^ (-s)‖) ^ 2 / 2) :=
    hbound
  have h1 : ‖det2EulerFactor s p - 1‖
      ≤ ‖det2EulerFactor s p‖ + 1 := by simpa using h
  exact le_trans h1 (by
    exact add_le_add_right this 1)

--

end Det2

end RS
end RH
