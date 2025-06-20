import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Core Definitions for Academic RH Framework

This file contains the core types and definitions used throughout the academic framework.
-/

namespace AcademicRH

/-- An indexed type for primes -/
structure PrimeIndex where
  val : ℕ
  property : Nat.Prime val

namespace PrimeIndex

instance : CoeOut PrimeIndex ℕ where
  coe p := p.val

/-- Every prime is positive -/
theorem pos (p : PrimeIndex) : 0 < (p.val : ℝ) := by
  exact Nat.cast_pos.mpr (Nat.Prime.pos p.property)

/-- Every prime is at least 2 -/
theorem two_le (p : PrimeIndex) : 2 ≤ (p.val : ℝ) := by
  exact Nat.cast_le.mpr (Nat.Prime.two_le p.property)

/-- Every prime is at least 1 -/
theorem one_lt (p : PrimeIndex) : 1 < (p.val : ℝ) := by
  exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.property)

/-- The inverse of a prime is less than 1 -/
theorem inv_lt_one {p : PrimeIndex} (hp : 2 ≤ (p.val : ℝ)) : (p.val : ℝ)⁻¹ < 1 := by
  -- Direct: if p ≥ 2 then 1/p ≤ 1/2 < 1
  have h1 : (p.val : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    refine inv_le_inv_of_le ?_ hp
    norm_num
  have h2 : (2 : ℝ)⁻¹ < 1 := by norm_num
  exact lt_of_le_of_lt h1 h2

end PrimeIndex

/-- The weighted ℓ² space over primes -/
noncomputable abbrev WeightedL2 := lp (fun _ : PrimeIndex => ℂ) 2

/-- Shorthand for the Riemann zeta function -/
noncomputable abbrev ζ := riemannZeta

end AcademicRH
