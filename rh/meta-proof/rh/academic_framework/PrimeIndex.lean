import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prime Index Type

This file defines the PrimeIndex type used in the academic framework.
-/

namespace AcademicRH

/-- An indexed type for primes -/
structure PrimeIndex where
  val : ℕ
  property : Nat.Prime val

namespace PrimeIndex

instance : CoeOut PrimeIndex ℕ where
  coe p := p.val

instance : Countable PrimeIndex := by
  -- PrimeIndex is equivalent to {n : ℕ // Nat.Prime n}, which is countable
  refine Countable.of_equiv {n : ℕ // Nat.Prime n} ?_
  exact {
    toFun := fun ⟨n, h⟩ => ⟨n, h⟩
    invFun := fun p => ⟨p.val, p.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

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
  have h_pos : 0 < (p.val : ℝ) := lt_of_lt_of_le zero_lt_two hp
  rw [inv_lt_one_iff_of_pos h_pos]
  exact lt_of_lt_of_le one_lt_two hp

end PrimeIndex

end AcademicRH
