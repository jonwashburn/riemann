-- import rh.academic_framework.Core -- trimmed; provide local scaffolds instead
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Complex.Basic

/-!
# Prime Series Convergence

This file establishes convergence of series involving primes.

## Main results

* `real_prime_rpow_summable` - ∑(1/p^{r}) converges for real r > 1
* `primeNormSummable` - ∑‖1/p^s‖ converges for Re(s) > 1

Uses mathlib's `Nat.Primes.summable_rpow`.
-/

namespace AcademicRH.EulerProduct

open Complex Real BigOperators Nat

/-- The series ∑ 1/p^r over primes converges for real r > 1 -/
lemma real_prime_rpow_summable {r : ℝ} (hr : 1 < r) :
  Summable (fun p : Nat.Primes => (p : ℝ)^(-r)) := by
  -- Use mathlib's result: summable iff -r < -1, i.e., r > 1
  rw [Nat.Primes.summable_rpow]
  linarith

/-- For a real number coerced to complex, the norm equals the absolute value. -/
lemma Complex.norm_eq_abs {x : ℝ} : ‖(x : ℂ)‖ = |x| := by
  simp [Complex.norm_real]

/-- The series ∑ ‖1/p^s‖ over prime indices converges for Re(s) > 1 -/
lemma primeNormSummable {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : Nat.Primes => ‖(p : ℂ)^(-s)‖) := by
  -- First, simplify the norm
  have h_norm : ∀ p : Nat.Primes, ‖(p : ℂ)^(-s)‖ = (p : ℝ)^(-s.re) := by
    intro p
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos p.property)
    erw [Complex.norm_cpow_eq_rpow_re_of_pos hp_pos]
    rfl
  simp_rw [h_norm]
  exact real_prime_rpow_summable hs

/-- Key bound: for Re(s) > 1, ∑_p 1/p^s converges absolutely -/
lemma primeSeriesConverges {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : Nat.Primes => (p : ℂ)^(-s)) := by
  apply Summable.of_norm
  exact primeNormSummable hs

end AcademicRH.EulerProduct
