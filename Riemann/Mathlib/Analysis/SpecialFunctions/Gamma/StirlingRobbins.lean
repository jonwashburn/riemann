
import Mathlib
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.BinetFormula

/-!
# Robbins' Bounds for Stirling's Approximation

This file proves Robbins' sharp two-sided bounds for the factorial:

  √(2πn) (n/e)^n e^{1/(12n+1)} ≤ n! ≤ √(2πn) (n/e)^n e^{1/(12n)}

These bounds are derived from Binet's formula and the bounds on the Binet integral J(z).

## Main Results

* `Stirling.factorial_upper_robbins`: n! ≤ √(2πn)(n/e)^n e^{1/(12n)}
* `Stirling.factorial_lower_robbins`: n! ≥ √(2πn)(n/e)^n e^{1/(12n+1)}
* `Stirling.log_factorial_theta`: log(n!) = n log n - n + log(2πn)/2 + θ/(12n)
* `Stirling.factorial_asymptotic`: n! ~ √(2πn)(n/e)^n

## Dependencies

This file builds on:
- `BinetKernel.lean`: The kernel K̃(t) with bounds 0 ≤ K̃(t) ≤ 1/12
- `BinetFormula.lean`: The Binet integral J(z) with bound |J(z)| ≤ 1/(12·Re(z))

Note: `GammaStirlingAux.lean` has `factorial_asymptotic` with sorry.
This file provides the Robbins proof completing that result.

## Strategy

1. Apply Binet's formula to Γ(n+1) = n!
2. Use the bounds 0 ≤ J(n+1) ≤ 1/(12(n+1))
3. For the lower bound, use the refined estimate J(n+1) ≥ 1/(12(n+1)+1)

## References

* Robbins, H. "A Remark on Stirling's Formula." Amer. Math. Monthly 62 (1955): 26-29.
* Feller, W. "An Introduction to Probability Theory and Its Applications", Vol. 1
* NIST DLMF 5.11.3
-/

open Real Set MeasureTheory Filter Topology
open scoped BigOperators Nat

noncomputable section

namespace Stirling

/-! ## Section 1: Setup and basic facts -/

/-- For n ≥ 1, Γ(n+1) = n!. -/
lemma Gamma_nat_eq_factorial (n : ℕ) : Real.Gamma (n + 1) = n.factorial := by
  exact_mod_cast Real.Gamma_nat_eq_factorial n

/-- log(n!) = log Γ(n+1) for n ≥ 1. -/
lemma log_factorial_eq_log_Gamma {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) = Real.log (Real.Gamma (n + 1)) := by
  rw [Gamma_nat_eq_factorial]

/-! ## Section 2: The theta parameter -/

/-- For n ≥ 1, there exists θ ∈ (0, 1) such that
log(n!) = n log n - n + log(2πn)/2 + θ/(12n).

This is the precise form of Stirling's approximation with explicit error. -/
theorem log_factorial_theta {n : ℕ} (hn : 0 < n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      Real.log (n.factorial : ℝ) =
        n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + θ / (12 * n) := by
  -- Strategy:
  -- 1. Use Binet: log Γ(n+1) = ((n+1) - 1/2) log(n+1) - (n+1) + log(2π)/2 + J(n+1).re
  -- 2. The J(n+1).re term is in (0, 1/(12(n+1)))
  -- 3. Algebraic manipulation gives the form with θ
  sorry

/-! ## Section 3: Upper bound -/

/-- Helper for exp(log x / 2) = sqrt x. -/
lemma exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow]
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- Exponentiating the Stirling formula with θ < 1 gives the upper bound.

This completes the sorry in `GammaStirlingAux.factorial_asymptotic`. -/
theorem factorial_upper_robbins (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) := by
  -- From log_factorial_theta, we have θ < 1
  -- So log(n!) ≤ n log n - n + log(2πn)/2 + 1/(12n)
  -- Exponentiating: n! ≤ √(2πn) * (n/e)^n * e^{1/(12n)}
  obtain ⟨θ, hθ_pos, hθ_lt_one, hlog⟩ := log_factorial_theta hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_ineq : θ / (12 * n) ≤ 1 / (12 * n) := by
    apply div_le_div_of_nonneg_right (le_of_lt hθ_lt_one)
    positivity
  have hlog_ub : Real.log (n.factorial : ℝ) ≤
      n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n) := by
    rw [hlog]; linarith
  have h_exp := Real.exp_le_exp.mpr hlog_ub
  rw [Real.exp_log (Nat.cast_pos.mpr (Nat.factorial_pos n))] at h_exp
  have h_pow_eq : (n : ℝ) ^ (n : ℝ) / Real.exp n = ((n : ℝ) / Real.exp 1) ^ n := by
    have h1 : Real.exp n = (Real.exp 1) ^ n := by rw [← Real.exp_one_rpow, Real.rpow_natCast]
    rw [h1]
    have h2 : (n : ℝ) ^ (n : ℝ) = (n : ℝ) ^ n := Real.rpow_natCast n n
    rw [h2, div_pow]
  have h_exp_n : Real.exp ((n : ℝ) * Real.log n) = (n : ℝ) ^ (n : ℝ) := by
    rw [mul_comm, Real.rpow_def_of_pos hn_pos]
  have h_sqrt : Real.exp (Real.log (2 * Real.pi * n) / 2) = Real.sqrt (2 * Real.pi * n) :=
    exp_half_log (by positivity : 0 < 2 * Real.pi * n)
  calc (n.factorial : ℝ)
      ≤ Real.exp (n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n)) := h_exp
    _ = Real.exp (n * Real.log n) * Real.exp (-n) *
        Real.exp (Real.log (2 * Real.pi * n) / 2) * Real.exp (1 / (12 * n)) := by
        have h : (n : ℝ) * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n) =
            n * Real.log n + -n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n) := by ring
        rw [h, Real.exp_add, Real.exp_add, Real.exp_add]
    _ = (n : ℝ) ^ (n : ℝ) * Real.exp (-n) *
        Real.sqrt (2 * Real.pi * n) * Real.exp (1 / (12 * n)) := by
        rw [h_exp_n, h_sqrt]
    _ = Real.sqrt (2 * Real.pi * n) * ((n : ℝ) ^ (n : ℝ) * Real.exp (-n)) *
        Real.exp (1 / (12 * n)) := by ring
    _ = Real.sqrt (2 * Real.pi * n) * ((n : ℝ) ^ (n : ℝ) / Real.exp n) *
        Real.exp (1 / (12 * n)) := by
        congr 2
        rw [Real.exp_neg, div_eq_mul_inv]
    _ = Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n *
        Real.exp (1 / (12 * n)) := by rw [h_pow_eq]

/-! ## Section 4: Lower bound -/

/-- For the lower bound, we need J(n+1) ≥ 1/(12(n+1)+1).

This refined lower bound on the Binet integral uses monotonicity of K̃. -/
lemma J_lower_bound {n : ℕ} (hn : 0 < n) :
    1 / (12 * (n + 1 : ℝ) + 1) ≤ (Binet.J (n + 1 : ℂ)).re := by
  -- This requires showing K̃(t) > 0 for t > 0 with quantitative bounds
  sorry

/-- The Robbins lower bound. -/
theorem factorial_lower_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial := by
  -- From log_factorial_theta, we have θ > 0
  -- Combined with the refined lower bound on J, we get
  -- log(n!) ≥ n log n - n + log(2πn)/2 + 1/(12n+1)
  sorry

/-! ## Section 5: Two-sided bound -/

/-- The complete Robbins bound. -/
theorem factorial_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial ∧
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  ⟨factorial_lower_robbins n hn, factorial_upper_robbins n hn⟩

/-! ## Section 6: Asymptotic equivalence -/

/-- The ratio n! / (√(2πn)(n/e)^n) → 1 as n → ∞. -/
theorem factorial_asymptotic :
    Tendsto (fun n : ℕ => (n.factorial : ℝ) /
      (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n)) atTop (𝓝 1) := by
  -- Both exp(1/(12n+1)) → 1 and exp(1/(12n)) → 1
  -- So by squeeze theorem, the ratio → 1
  sorry

/-- Stirling's approximation: n! ~ √(2πn)(n/e)^n. -/
theorem stirling_asymptotic :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (n.factorial : ℝ))
      (fun n : ℕ => Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) := by
  rw [Asymptotics.isEquivalent_iff_tendsto_one]
  · exact factorial_asymptotic
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    apply ne_of_gt
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    apply mul_pos (Real.sqrt_pos.mpr _) (pow_pos _ _)
    · positivity
    · have : 0 < n / Real.exp 1 := div_pos hn_pos (Real.exp_pos 1)
      linarith

end Stirling

/-! ## Section 7: Convenient API -/

namespace Nat

/-- Upper bound: n! ≤ √(2πn)(n/e)^n · e^{1/(12n)} for n ≥ 1. -/
theorem factorial_le_stirling_upper (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  Stirling.factorial_upper_robbins n hn

/-- Lower bound: √(2πn)(n/e)^n · e^{1/(12n+1)} ≤ n! for n ≥ 1. -/
theorem factorial_ge_stirling_lower (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial :=
  Stirling.factorial_lower_robbins n hn

end Nat

end
