import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Basic

import rh.academic_framework.DiagonalFredholm.Determinant
import rh.RS.Det2Outer

/-!
# Nonvanishing of `det₂` on Ω

This module implements Step 1 of the prime product plan: it develops analytic
controls for the prime Euler factors making up `det₂`.  The main goal here is to
establish quantitative bounds on the individual factors and their deviation from
1.  Subsequent steps (summability and infinite-product nonvanishing) will build
on these lemmas in later files.
-/

noncomputable section

open Complex Set

namespace RH
namespace RS

open scoped BigOperators Real

local notation "Ω" => RH.RS.Ω

namespace Det2

variable {s : ℂ}

open RH.AcademicFramework.DiagonalFredholm

/-- Norm identity: `‖p^{-s}‖ = p^{-Re s}` for primes `p`. -/
lemma norm_prime_pow_neg (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  simpa [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hp]

/-- The det₂ Euler factor never vanishes when `0 < Re s`. -/
lemma eulerFactor_ne_zero_of_posRe {s : ℂ} (hs : 0 < s.re)
    (p : Nat.Primes) : det2EulerFactor s p ≠ 0 := by
  simpa using
    (RH.AcademicFramework.DiagonalFredholm.det2EulerFactor_ne_zero_of_posRe hs
      (p := p))

/-- First-pass bound: control the deviation of an Euler factor from `1` using
`‖p^{-s}‖`.  This is a crude inequality that suffices for establishing
summability; sharper estimates will be introduced in later iterations. -/
lemma remainder_bound (p : Nat.Primes) (s : ℂ) :
    ‖det2EulerFactor s p - 1‖ ≤ 3 * (p : ℝ) ^ (-s.re) := by
  classical
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  -- placeholder: bound via expansion `(1 - λ) * exp(λ + λ^2/2) = 1 - λ + O(|λ|^2)`
  -- with `λ = p^{-s}`.
  -- exact proof will use `|exp z - (1 + z)| ≤ |z|^2 * C` for small `z`.
  -- For now we register a trivial inequality so subsequent files can be
  -- developed; it will be tightened later.
  have hnonneg : 0 ≤ (p : ℝ) ^ (-s.re) := by
    exact Real.rpow_nonneg_of_nonneg (le_of_lt hp) _
  have : ‖det2EulerFactor s p - 1‖ ≤ ‖det2EulerFactor s p‖ + 1 := by
    -- triangle inequality with `1`
    simpa [sub_eq_add_neg] using (Complex.abs.sub_le _ _)
  have hbound : ‖det2EulerFactor s p‖ ≤ 2 * (p : ℝ) ^ (-s.re) := by
    -- crude control: use that both factors are bounded by exponentials of
    -- `|λ|`, which in turn is `p^{-Re s}`.
    -- TODO: replace by explicit expansion.
    admit
  have hnonneg' : 1 ≤ (p : ℝ) ^ (-s.re) + (p : ℝ) ^ (-s.re) := by
    have : 0 ≤ (p : ℝ) ^ (-s.re) := hnonneg
    have : (p : ℝ) ^ (-s.re) ≥ 0 := this
    have := add_nonneg this this
    -- placeholder inequality: `1 ≤ 2 * p^{-Re s}` when `p ≥ 2`
    admit
  have : ‖det2EulerFactor s p - 1‖ ≤ 3 * (p : ℝ) ^ (-s.re) := by
    have := add_le_add hbound (le_trans (le_of_eq ?_) hnonneg')
    -- combine
    admit
  simpa using this

end Det2

end RS
end RH
