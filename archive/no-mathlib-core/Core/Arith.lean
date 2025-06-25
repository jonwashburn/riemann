/-
  Arithmetic Helpers
  ==================

  Small arithmetic lemmas used across the Recognition Science framework.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

namespace RecognitionScience.Arith

/-- Eight-specific modular arithmetic -/
@[simp]
theorem mod_eight_lt (k : Nat) : k % 8 < 8 :=
  Nat.mod_lt k (by decide : 0 < 8)

/-- Adding 8 doesn't change mod 8 value -/
@[simp]
theorem add_eight_mod_eight (k : Nat) : (k + 8) % 8 = k % 8 := by
  rw [Nat.add_mod, Nat.mod_self]
  simp

end RecognitionScience.Arith
