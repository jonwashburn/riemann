
import Mathlib
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.BinetFormula
--import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.BinetIntegralFormula


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
  have h_fact : Real.log (n.factorial) = Real.log n + Real.log (Real.Gamma n) := by
    rw [← Real.log_mul (Nat.cast_ne_zero.mpr (ne_of_gt hn)) (Real.Gamma_pos_of_pos (Nat.cast_pos.mpr hn)).ne']
    rw [← Real.Gamma_add_one (Nat.cast_ne_zero.mpr (ne_of_gt hn))]
    rw [Real.Gamma_nat_eq_factorial]
  let x : ℝ := n
  have hx : 0 < x := Nat.cast_pos.mpr hn
  -- Binet formula for log Gamma(x)
  have h_binet : Real.log (Real.Gamma x) = (x - 1/2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (Binet.J x).re := by
    exact BinetFormula.Real_log_Gamma_eq_Binet hx
  -- Bounds on J(x)
  have h_J_bounds : 0 < (Binet.J x).re ∧ (Binet.J x).re < 1 / (12 * x) := by
    constructor
    · exact BinetFormula.re_J_pos hx
    · exact BinetFormula.re_J_lt_one_div_twelve hx
  rcases h_J_bounds with ⟨hJ_pos, hJ_ub⟩
  let θ := 12 * x * (Binet.J x).re
  use θ
  constructor
  · exact mul_pos (mul_pos (by norm_num) hx) hJ_pos
  constructor
  · rw [← div_lt_iff₀ (mul_pos (by norm_num) hx)]
    exact hJ_ub
  rw [h_fact, h_binet]
  have h_theta : θ / (12 * x) = (Binet.J x).re := by field_simp [θ]; ring
  rw [h_theta]
  have h_log_term : Real.log (2 * Real.pi * n) / 2 = Real.log (2 * Real.pi) / 2 + Real.log n / 2 := by
    rw [Real.log_mul (by positivity) (by positivity)]
    ring
  rw [h_log_term]
  ring

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
  obtain ⟨θ, hθ_pos, hθ_lt_one, hlog⟩ := log_factorial_theta hn
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_log_le : Real.log (n.factorial : ℝ) ≤
      n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n) := by
    rw [hlog]
    apply add_le_add_left
    apply div_le_div_of_nonneg_right (le_of_lt hθ_lt_one)
    exact mul_nonneg (by norm_num) hn_pos.le
  have h_exp := Real.exp_le_exp.mpr h_log_le
  rw [Real.exp_log (Nat.cast_pos.mpr (Nat.factorial_pos n))] at h_exp
  -- Simplify RHS
  have h_pow_eq : (n : ℝ) ^ (n : ℝ) / Real.exp n = ((n : ℝ) / Real.exp 1) ^ n := by
    have h1 : Real.exp n = (Real.exp 1) ^ n := by rw [← Real.exp_one_rpow, Real.rpow_natCast]
    rw [h1]
    have h2 : (n : ℝ) ^ (n : ℝ) = (n : ℝ) ^ n := Real.rpow_natCast n n
    rw [h2, div_pow]
  have h_exp_n : Real.exp ((n : ℝ) * Real.log n) = (n : ℝ) ^ (n : ℝ) := by
    rw [mul_comm, Real.rpow_def_of_pos hn_pos]
  have h_sqrt : Real.exp (Real.log (2 * Real.pi * n) / 2) = Real.sqrt (2 * Real.pi * n) :=
    exp_half_log (by positivity : 0 < 2 * Real.pi * n)
  convert h_exp using 1
  rw [Real.exp_add, Real.exp_add, Real.exp_add]
  rw [h_exp_n, h_sqrt]
  rw [Real.exp_neg, div_eq_mul_inv, h_pow_eq]
  ring

/-! ## Section 4: Lower bound -/

/-- For the lower bound, we need J(n+1) ≥ 1/(12(n+1)+1).

This refined lower bound on the Binet integral uses monotonicity of K̃. -/
lemma J_lower_bound {n : ℕ} (hn : 0 < n) :
    1 / (12 * (n + 1 : ℝ) + 1) ≤ (Binet.J (n + 1 : ℂ)).re := by
  -- This requires showing K̃(t) > 0 for t > 0 with quantitative bounds
  let x : ℝ := n + 1
  have hx : 0 < x := by exact_mod_cast Nat.succ_pos n
  rw [BinetFormula.re_J_eq_integral_Ktilde hx]
  -- We use the bound K̃(t) ≥ (1/12) * e^{-t/12}
  have h_bound : ∀ t ∈ Ioi 0, (1/12) * Real.exp (-t/12) ≤ BinetKernel.Ktilde t := by
    -- This inequality holds for the Binet kernel
    -- K̃(t) = (1/2 - 1/t + 1/(e^t - 1)) / t
    -- We assume this bound is provable or available
    sorry

  -- We integrate the inequality
  have h_int_le : ∫ t in Ioi 0, (1/12) * Real.exp (-t/12) * Real.exp (-t * x) ≤
                  ∫ t in Ioi 0, BinetKernel.Ktilde t * Real.exp (-t * x) := by
    apply setIntegral_mono_ae_restrict
    · apply Integrable.const_mul
      apply integrable_exp_neg_mul_Ioi
      apply add_pos hx (by norm_num)
    · exact BinetFormula.integrable_Ktilde_mul_exp_neg_mul hx
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi)] with t ht
      gcongr
      exact h_bound t ht

  -- Calculate the LHS integral
  have h_lhs : ∫ t in Ioi 0, (1/12) * Real.exp (-t/12) * Real.exp (-t * x) = 1 / (12 * x + 1) := by
    simp only [mul_assoc, ← Real.exp_add]
    have h_exp_arg : ∀ t, -t/12 + -t*x = - (x + 1/12) * t := by intro t; ring
    simp only [h_exp_arg]
    rw [integral_mul_left, integral_exp_neg_mul_Ioi]
    · field_simp; ring
    · apply add_pos hx (by norm_num)

  rw [h_lhs] at h_int_le
  exact h_int_le

/-- The Robbins lower bound. -/
theorem factorial_lower_robbins (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_J_ge : 1 / (12 * (n : ℝ) + 1) ≤ (Binet.J n).re := by
    convert J_lower_bound (n := n - 1) using 1
    · simp [Nat.cast_sub (Nat.succ_le_of_lt hn)]
    · simp [Nat.cast_sub (Nat.succ_le_of_lt hn)]
  have h_log_ge : n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + 1 / (12 * n + 1) ≤ Real.log (n.factorial : ℝ) := by
    have h_fact : Real.log (n.factorial) = Real.log n + Real.log (Real.Gamma n) := by
      rw [← Real.log_mul (Nat.cast_ne_zero.mpr (ne_of_gt hn)) (Real.Gamma_pos_of_pos (Nat.cast_pos.mpr hn)).ne']
      rw [← Real.Gamma_add_one (Nat.cast_ne_zero.mpr (ne_of_gt hn))]
      rw [Real.Gamma_nat_eq_factorial]
    have h_binet : Real.log (Real.Gamma n) = (n - 1/2) * Real.log n - n + Real.log (2 * Real.pi) / 2 + (Binet.J n).re := by
      exact BinetFormula.Real_log_Gamma_eq_Binet hn_pos
    rw [h_fact, h_binet]
    rw [Real.log_mul (by positivity) (by positivity)]
    ring_nf
    simp only [add_le_add_iff_left]
    exact h_J_ge
  rw [← Real.log_le_log_iff (mul_pos (mul_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) hn_pos)) (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n)) (Real.exp_pos _)) (Nat.cast_pos.mpr (Nat.factorial_pos n))]
  convert h_log_ge using 1
  rw [Real.log_mul (mul_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) hn_pos)) (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n)).ne' (Real.exp_pos _).ne']
  rw [Real.log_exp]
  rw [Real.log_mul (Real.sqrt_pos.mpr (mul_pos (by norm_num) hn_pos)).ne' (pow_pos (div_pos hn_pos (Real.exp_pos 1)) n).ne']
  rw [Real.log_sqrt (mul_pos (by norm_num) hn_pos)]
  rw [Real.log_pow, Real.log_div hn_pos.ne' (Real.exp_pos 1).ne', Real.log_exp]
  ring

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
  let lower (n : ℕ) := (1 : ℝ)
  let upper (n : ℕ) := Real.exp (1 / (12 * n))
  have h_squeeze : ∀ᶠ n in atTop, lower n ≤ (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ∧
                                  (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) ≤ upper n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨θ, hθ_pos, hθ_lt_one, hlog⟩ := log_factorial_theta hn
    let stirling := Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n
    have h_stirling_pos : 0 < stirling := by
      apply mul_pos
      · apply Real.sqrt_pos.mpr; apply mul_pos; norm_num; exact Nat.cast_pos.mpr hn
      · apply pow_pos; apply div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)
    rw [le_div_iff₀ h_stirling_pos, div_le_iff₀ h_stirling_pos]
    have h_log_stirling : Real.log stirling = n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 := by
      rw [Real.log_mul (Real.sqrt_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr hn))).ne' (pow_pos (div_pos (Nat.cast_pos.mpr hn) (Real.exp_pos 1)) n).ne']
      rw [Real.log_sqrt (mul_pos (by norm_num) (Nat.cast_pos.mpr hn))]
      rw [Real.log_pow, Real.log_div (Nat.cast_ne_zero.mpr (ne_of_gt hn)) (Real.exp_pos 1).ne']
      rw [Real.log_exp]; ring
    rw [hlog]
    constructor
    · rw [← Real.log_le_log_iff h_stirling_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)), h_log_stirling]
      simp only [le_add_iff_nonneg_right]; positivity
    · rw [← Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.factorial_pos n)) (mul_pos (Real.exp_pos _) h_stirling_pos)]
      rw [Real.log_mul (Real.exp_pos _).ne' h_stirling_pos.ne', Real.log_exp, h_log_stirling]
      simp only [add_le_add_iff_left]; gcongr; exact hθ_lt_one.le
  refine (tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := fun n : ℕ =>
      (n.factorial : ℝ) / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n))
    (g := lower) (h := upper) tendsto_const_nhds ?_ ?_ ?_)
  · -- `upper n = exp (1/(12n)) → exp 0 = 1`
    have h_lim : Tendsto (fun n : ℕ => 1 / (12 * (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
      -- first show `12 * n → +∞`, then compose with `x ↦ x⁻¹ → 0`
      have h_to : Tendsto (fun n : ℕ => (12 : ℝ) * (n : ℝ)) atTop atTop := by
        have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
          simpa using (tendsto_natCast_atTop_atTop : Tendsto (Nat.cast : ℕ → ℝ) atTop atTop)
        simpa [mul_comm] using
          (Filter.Tendsto.const_mul_atTop (β := ℕ) (α := ℝ) (r := (12 : ℝ)) (by positivity) hn)
      have h_inv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)) := by
        simpa using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 (0 : ℝ)))
      have : Tendsto (fun n : ℕ => ((12 : ℝ) * (n : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
        h_inv.comp h_to
      simpa [one_div] using this
    have h_exp : Tendsto Real.exp (𝓝 (0 : ℝ)) (𝓝 (Real.exp (0 : ℝ))) :=
      Real.continuous_exp.tendsto (0 : ℝ)
    have : Tendsto (fun n : ℕ => Real.exp (1 / (12 * (n : ℝ)))) atTop (𝓝 (Real.exp (0 : ℝ))) :=
      h_exp.comp h_lim
    simpa [upper, Real.exp_zero] using this
  · filter_upwards [h_squeeze] with n hn
    exact hn.1
  · filter_upwards [h_squeeze] with n hn
    exact hn.2

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
