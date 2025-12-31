
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.BinetFormula
import Riemann.academic_framework.GammaStirlingAux

/-!
# Gamma Function Bounds via Functional Equation

This file provides bounds on the complex Gamma function using the functional
equation Γ(z+1) = z·Γ(z). These are used to establish Stirling-type bounds.

## Main Results

* `Complex.Gamma_functional_equation` : Γ(z+1) = z·Γ(z)
* `Complex.Gamma_iterate_functional` : Γ(z+n) = (∏_{k=0}^{n-1} (z+k))·Γ(z)
* `Complex.Gamma_bounded_strip_one_two` : |Γ(s)| ≤ 4 for 1 ≤ Re(s) ≤ 2
* `Complex.Gamma_polynomial_bound_re_large` : Polynomial bound for Re(s) ≥ 2

## Implementation Notes

The functional equation approach allows us to reduce bounds for large real part
to bounds in a fixed strip [1,2], which can be handled by Mathlib's existing
infrastructure for Gamma function properties.
-/

noncomputable section

open Complex Real Set Filter Topology Metric
open scoped Real BigOperators

namespace Complex

/-! ## Part 1: Functional Equation -/

/-- The functional equation Γ(z+1) = z·Γ(z) for Gamma. -/
lemma Gamma_add_one_eq (z : ℂ) (hz : z ≠ 0) : Gamma (z + 1) = z * Gamma z :=
  Gamma_add_one z hz

/-- Product formula from iterating the functional equation. -/
lemma Gamma_add_nat_eq (z : ℂ) (n : ℕ) (hz : ∀ k : ℕ, k < n → z + k ≠ 0) :
    Gamma (z + n) = (∏ k ∈ Finset.range n, (z + k)) * Gamma z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz_range : ∀ k : ℕ, k < n → z + k ≠ 0 := fun k hk => hz k (Nat.lt_succ_of_lt hk)
    have hz_n : z + n ≠ 0 := hz n (Nat.lt_succ_self n)
    rw [Nat.cast_succ, ← add_assoc]
    rw [Gamma_add_one_eq (z + n) hz_n]
    rw [ih hz_range]
    rw [Finset.prod_range_succ]
    ring

/-- Inverse form: Γ(z) = Γ(z+n) / ∏_{k=0}^{n-1} (z+k). -/
lemma Gamma_eq_div_prod (z : ℂ) (n : ℕ) (hz : ∀ k : ℕ, k < n → z + k ≠ 0)
    (hprod : ∏ k ∈ Finset.range n, (z + k) ≠ 0) :
    Gamma z = Gamma (z + n) / ∏ k ∈ Finset.range n, (z + k) := by
  have h := Gamma_add_nat_eq z n hz
  field_simp [hprod] at h ⊢
  aesop

/-! ## Part 2: Norm bounds in the strip [1, 2] -/

/-- For 1 ≤ Re(s) ≤ 2, the Gamma function is bounded. -/
theorem Gamma_norm_bounded_strip_one_two :
    ∃ M : ℝ, 0 < M ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → ‖Gamma s‖ ≤ M := by
  -- In `Riemann/Mathlib` we have the sharp strip bound `‖Γ(s)‖ ≤ 1` for `1 ≤ re s ≤ 2`.
  refine ⟨1, by norm_num, ?_⟩
  intro s hs_lo hs_hi
  simpa using (Binet.norm_Gamma_le_one (z := s) hs_lo hs_hi)

/-- Norm of Gamma at s = 1 is 1. -/
@[simp]
lemma Gamma_one_norm : ‖Gamma 1‖ = 1 := by
  rw [Gamma_one, norm_one]

/-- Norm of Gamma at s = 2 is 1. -/
@[simp]
lemma Gamma_two_norm : ‖Gamma 2‖ = 1 := by
  have h : Gamma 2 = Gamma (1 + 1) := by norm_num
  rw [h, Gamma_add_one 1 one_ne_zero, Gamma_one, mul_one, norm_one]

/-! ## Part 3: Polynomial bound for large real part -/

/-- Product of |s - k| for k = 1, ..., n is bounded by (|s| + n)^n. -/
lemma prod_sub_nat_norm_le (s : ℂ) (n : ℕ) :
    ‖∏ k ∈ Finset.range n, (s - (k + 1))‖ ≤ (‖s‖ + n) ^ n := by
  calc ‖∏ k ∈ Finset.range n, (s - (k + 1))‖
      = ∏ k ∈ Finset.range n, ‖s - (k + 1)‖ := by
          simp
    _ ≤ ∏ _k ∈ Finset.range n, (‖s‖ + n) := by
      apply Finset.prod_le_prod (fun k _ => norm_nonneg _)
      intro k hk
      have hk' : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      calc ‖s - (k + 1)‖ ≤ ‖s‖ + ‖(k + 1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖s‖ + (k + 1 : ℝ) := by
            -- `‖(k+1 : ℂ)‖ = k+1`
            simpa using (RCLike.norm_natCast (K := ℂ) (n := k + 1))
        _ ≤ ‖s‖ + n := by
            gcongr
            exact_mod_cast hk'
    _ = (‖s‖ + n) ^ n := by simp [Finset.prod_const, Finset.card_range]

/-- For Re(s) ≥ 2 and ‖s‖ ≥ 2, polynomial bound using functional equation. -/
theorem Gamma_polynomial_bound_re_ge_two {s : ℂ} (hs_re : 2 ≤ s.re) (hs_norm : 2 ≤ ‖s‖) :
    ‖Gamma s‖ ≤ Real.exp (‖s‖ * Real.log ‖s‖ + 3 * ‖s‖) := by
  -- This is already available (in a slightly more general form) in `GammaStirlingAux`.
  exact Stirling.GammaAux.norm_Gamma_polynomial_bound (s := s) (hs_re := by linarith) hs_norm

end Complex

/-! ## Part 4: Specialized bounds -/

namespace GammaBounds

open Complex Real

/-- For 1 < Re(s) ≤ 2, |Γ(s)| ≤ 4.

This fills in the sorry in StirlingB.lean. -/
theorem Gamma_bounded_on_one_to_two {s : ℂ} (hs_lo : 1 < s.re) (hs_hi : s.re ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 4 := by
  -- We have the sharper bound `‖Γ(s)‖ ≤ 1` on `[1,2]`.
  have h1 : ‖Complex.Gamma s‖ ≤ 1 := Binet.norm_Gamma_le_one (z := s) (le_of_lt hs_lo) hs_hi
  linarith

end GammaBounds

end
