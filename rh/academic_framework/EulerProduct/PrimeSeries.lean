import rh.academic_framework.Core
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

/-- The series ∑ ‖1/p^s‖ over prime indices converges for Re(s) > 1 -/
lemma primeNormSummable {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) := by
  -- This follows from the convergence of ∑ 1/p^{Re(s)} for Re(s) > 1
  -- The implementation is complex due to type conversions
  -- First, simplify the norm
  have h_norm : ∀ p : PrimeIndex, ‖(p.val : ℂ)^(-s)‖ = (p.val : ℝ)^(-s.re) := by
    intro p
    -- For positive real base p and complex exponent -s, we have |p^(-s)| = p^(-Re(s))
    have hp_pos : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
    -- Use the fact that for positive real base, |a^b| = a^(Re(b))
    -- This is a standard property in complex analysis
    rw [Complex.norm_eq_abs, ← ofReal_natCast]
    exact Complex.abs_cpow_eq_rpow_re_of_pos hp_pos _

  -- Rewrite using h_norm
  simp_rw [h_norm]

  -- Use the equivalence between PrimeIndex and Nat.Primes
  have h_equiv : Summable (fun p : Nat.Primes => (p : ℝ)^(-s.re)) := by
    apply real_prime_rpow_summable hs

  -- Transport summability along the equivalence
  -- Convert from Nat.Primes to PrimeIndex
  -- The function on PrimeIndex is the same as the function on Nat.Primes
  -- composed with the equivalence
  have : (fun p : PrimeIndex => (p.val : ℝ)^(-s.re)) =
         (fun p : Nat.Primes => (p : ℝ)^(-s.re)) ∘ PrimeIndex.equivPrimes := by
    ext p
    simp [PrimeIndex.equivPrimes_apply_coe_coe]
  rw [this]
  exact Summable.comp_injective h_equiv PrimeIndex.equivPrimes.injective

/-- Key bound: for Re(s) > 1, ∑_p 1/p^s converges absolutely -/
lemma primeSeriesConverges {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : PrimeIndex => (p.val : ℂ)^(-s)) := by
  apply Summable.of_norm
  exact primeNormSummable hs

end AcademicRH.EulerProduct
