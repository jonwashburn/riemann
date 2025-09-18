import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp
import rh.academic_framework.Core

/-!
# Complex Logarithm Periodicity

This file contains lemmas about the periodicity of the complex logarithm.
-/

namespace AcademicRH

open Complex Real

/-- The principal branch of complex logarithm -/
noncomputable def principal_log (z : ℂ) (hz : z ≠ 0) : ℂ :=
  Complex.log z

/-- log is a left inverse of exp modulo 2πi -/
lemma log_exp (z : ℂ) : ∃ k : ℤ, log (exp z) = z - 2 * Real.pi * I * k := by
   -- Starting point: `exp (log (exp z)) = exp z`.
   have h_eq : exp (log (exp z)) = exp z := by
     simpa using Complex.exp_log (Complex.exp_ne_zero z)
   -- Apply the standard characterization of equality under `exp`.
   rcases (Complex.exp_eq_exp_iff_exists_int).1 h_eq with ⟨k, hk⟩
   -- Rearrange the conclusion to the desired shape using `k' = -k`.
   refine ⟨-k, ?_⟩
   have : log (exp z) = z + k * (2 * Real.pi * I) := hk
   -- Rewrite the right-hand side so that it uses subtraction and `-k`.
   simpa [mul_comm, mul_left_comm, mul_assoc, two_mul, sub_eq_add_neg] using this

end AcademicRH
