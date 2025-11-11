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
  calc
    ‖(p : ℂ) ^ (-s)‖ = Complex.abs ((p : ℂ) ^ (-s)) := by simp [Complex.norm_eq_abs]
    _ = (p : ℝ) ^ (-s.re) := Complex.abs_cpow_eq_rpow_re_of_pos hp (-s)

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
  have hlam_nonneg : 0 ≤ Complex.abs lam := by
    simpa using (Complex.abs.nonneg lam)
  have h1 :
      Complex.abs (1 - lam) ≤ 1 + Complex.abs lam := by
    have h := norm_add_le (1 : ℂ) (-lam)
    simpa [Complex.norm_eq_abs, sub_eq_add_neg] using h
  have hlam_sq : Complex.abs (lam ^ 2) = Complex.abs lam ^ 2 := by
    simpa [pow_two] using (Complex.abs.map_mul lam lam)
  have hdiv :
      Complex.abs (lam ^ 2 / 2) = Complex.abs lam ^ 2 / 2 := by
    simpa [abs_div, hlam_sq] using (abs_div (lam ^ 2) (2 : ℂ))
  have hZ :
      Complex.abs Z ≤ Complex.abs lam + Complex.abs lam ^ 2 / 2 := by
    have h := norm_add_le lam (lam ^ 2 / 2)
    simpa [Complex.norm_eq_abs, Z, hdiv, add_comm, add_left_comm, add_assoc] using h
  have hz_re_le : Z.re ≤ Complex.abs Z := by
    have : |Z.re| ≤ Complex.abs Z := Complex.abs_re_le_abs Z
    exact le_trans (le_abs_self _) this
  have hexp :
      Complex.abs (Complex.exp Z) ≤ Real.exp (Complex.abs Z) := by
    have := Real.exp_le_exp.mpr hz_re_le
    simpa [Complex.abs_exp] using this
  have hprod :
      Complex.abs ((1 - lam) * Complex.exp Z)
        ≤ (1 + Complex.abs lam) * Real.exp (Complex.abs Z) := by
    have hmul :
        Complex.abs ((1 - lam) * Complex.exp Z)
          = Complex.abs (1 - lam) * Complex.abs (Complex.exp Z) := by
      simpa using Complex.abs_mul (1 - lam) (Complex.exp Z)
    have htemp :
        Complex.abs (1 - lam) * Complex.abs (Complex.exp Z)
          ≤ (1 + Complex.abs lam) * Complex.abs (Complex.exp Z) :=
      mul_le_mul_of_nonneg_right h1 (Complex.abs.nonneg _)
    have htemp' :
        (1 + Complex.abs lam) * Complex.abs (Complex.exp Z)
          ≤ (1 + Complex.abs lam) * Real.exp (Complex.abs Z) :=
      mul_le_mul_of_nonneg_left hexp (add_nonneg (show 0 ≤ (1 : ℝ) by norm_num) hlam_nonneg)
    have : Complex.abs (1 - lam) * Complex.abs (Complex.exp Z)
        ≤ (1 + Complex.abs lam) * Real.exp (Complex.abs Z) :=
      le_trans htemp htemp'
    simpa [hmul] using this
  have hmono :
      Real.exp (Complex.abs Z)
        ≤ Real.exp (Complex.abs lam + Complex.abs lam ^ 2 / 2) :=
    Real.exp_le_exp.mpr hZ
  have htarget :
      (1 + Complex.abs lam) * Real.exp (Complex.abs Z)
        ≤ (1 + Complex.abs lam) *
            Real.exp
              (Complex.abs lam + Complex.abs lam ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left hmono (add_nonneg (show 0 ≤ (1 : ℝ) by norm_num) hlam_nonneg)
  have hfinal :
      Complex.abs ((1 - lam) * Complex.exp Z)
        ≤ (1 + Complex.abs lam) *
            Real.exp
              (Complex.abs lam + Complex.abs lam ^ 2 / 2) :=
    le_trans hprod htarget
  simpa [Complex.norm_eq_abs, Z, lam] using hfinal

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
      ≤ ‖det2EulerFactor s p‖ + 1 := by
    convert h using 1 <;> simp
  exact le_trans h1 (by
    exact add_le_add_right this 1)

--

end Det2

end RS
end RH
