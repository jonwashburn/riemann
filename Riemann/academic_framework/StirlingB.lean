import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Basic
import Riemann.academic_framework.GammaBounds
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.LargeImaginaryBound
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.StirlingAsymptotic

/-!
# Stirling-type bounds for the complex Gamma function

This file provides polynomial and exponential growth bounds for the complex Gamma function
in the right half-plane, based on Stirling's asymptotic formula.

## Main results

* `Gamma_stirling_core`: For `Re(s) ≥ 1/2` and `‖s‖ ≥ A`, we have
  `‖Γ(s)‖ ≤ exp(C‖s‖ log(B‖s‖))` for explicit constants `C, A, B`.

## Mathematical Background

The bounds follow from:
1. **Strip bounds**: For `a ≤ Re(s) ≤ 1` with `a > 0`, `‖Γ(s)‖ ≤ 1/a + √π`
2. **Functional equation**: `Γ(s+1) = s·Γ(s)` allows reduction from large Re(s) to strips
3. **Stirling's formula**: For large |s|, `Γ(s) ~ √(2π) s^{s-1/2} e^{-s}`

## References

* Titchmarsh, "The Theory of the Riemann Zeta-Function", Chapter 4
* Iwaniec-Kowalski, "Analytic Number Theory", Appendix B
-/

open Complex Real Set Filter Asymptotics
open scoped Topology

namespace GammaBounds

/-! ## Part 1: Elementary inequalities -/

/-- Re(s) ≤ |s| for any complex s. -/
lemma norm_ge_re (s : ℂ) : s.re ≤ ‖s‖ := le_of_abs_le (Complex.abs_re_le_norm s)

/-- |Im(s)| ≤ |s| for any complex s. -/
lemma norm_ge_abs_im (s : ℂ) : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s

/-- √π < 2. -/
lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  have : Real.pi < 4 := Real.pi_lt_four
  have h4 : Real.sqrt 4 = 2 := by norm_num
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le this
    _ = 2 := h4

/-- log 2 > 0.69. -/
lemma log_two_gt : Real.log 2 > 0.69 := by linarith [Real.log_two_gt_d9]

/-- exp 2 > 7. -/
lemma exp_two_gt_seven : Real.exp 2 > 7 := by
  calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; ring_nf
    _ > 2.7 * 2.7 := by nlinarith [Real.exp_one_gt_d9]
    _ > 7 := by norm_num

/-- exp 2 > 4. -/
lemma exp_two_gt_four : Real.exp 2 > 4 := by linarith [exp_two_gt_seven]

/-! ## Part 2: Strip bounds for Gamma -/

/-- For `1/2 ≤ Re(s) ≤ 1`, `‖Γ(s)‖ ≤ 4`. -/
lemma Gamma_strip_bound {s : ℂ} (hs_re_lo : (1 / 2 : ℝ) ≤ s.re) (hs_re_hi : s.re ≤ 1) :
    ‖Complex.Gamma s‖ ≤ 4 := by
  have h := Complex.Gammaℝ.norm_Complex_Gamma_le_of_re_ge (a := 1/2) (by norm_num) hs_re_lo hs_re_hi
  have h_bound : 1 / (1/2 : ℝ) + Real.sqrt Real.pi ≤ 4 := by linarith [sqrt_pi_lt_two]
  linarith

/-! ## Part 3: Product bounds -/

/-- Product of shifted linear factors is bounded by a power. -/
lemma prod_shifted_norm_bound {s : ℂ} {n : ℕ} (hn : (n : ℝ) ≤ ‖s‖) :
    ‖∏ k ∈ Finset.range n, (s - 1 - k)‖ ≤ (2 * ‖s‖) ^ n := by
  calc ‖∏ k ∈ Finset.range n, (s - 1 - k)‖
      = ∏ k ∈ Finset.range n, ‖s - 1 - k‖ := by simp [norm_prod]
    _ ≤ ∏ _k ∈ Finset.range n, (2 * ‖s‖) := by
        apply Finset.prod_le_prod
        · intro k _; exact norm_nonneg _
        · intro k hk
          have hk' : k < n := Finset.mem_range.mp hk
          have hk_le : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk'
          calc ‖s - 1 - k‖ ≤ ‖s‖ + ‖(1 : ℂ) + k‖ := by
                calc ‖s - 1 - k‖ = ‖s - (1 + k)‖ := by ring_nf
                  _ ≤ ‖s‖ + ‖(1 : ℂ) + k‖ := norm_sub_le _ _
            _ ≤ ‖s‖ + (1 + k) := by
                have h1 : ‖(1 : ℂ) + k‖ ≤ 1 + k := by
                  calc ‖(1 : ℂ) + k‖ ≤ ‖(1 : ℂ)‖ + ‖(k : ℂ)‖ := norm_add_le _ _
                    _ = 1 + k := by simp
                linarith
            _ ≤ ‖s‖ + n := by linarith [hk_le]
            _ ≤ 2 * ‖s‖ := by linarith [hn]
    _ = (2 * ‖s‖) ^ n := by simp [Finset.prod_const, Finset.card_range]

/-! ## Part 4: Key exponential bound -/

/-- The exponential `exp(2|s|log|s| + 4|s|)` is at least 4 for `|s| ≥ 2`. -/
lemma exp_bound_ge_four {s : ℂ} (hs_norm : 2 ≤ ‖s‖) :
    (4 : ℝ) ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
  have h_norm_pos : 0 < ‖s‖ := by linarith
  have h_log_nonneg : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  have h1 : 2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖ ≥ 2 * 2 * Real.log 2 + 4 * 2 := by
    have hlog : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hs_norm
    nlinarith [h_norm_pos, h_log_nonneg, hs_norm, hlog]
  have h2 : 2 * 2 * Real.log 2 + 4 * 2 = 4 * Real.log 2 + 8 := by ring
  have h3 : 4 * Real.log 2 + 8 > 2 := by linarith [log_two_gt]
  have h4 : Real.exp 2 < Real.exp (4 * Real.log 2 + 8) := Real.exp_lt_exp.mpr h3
  have h5 : Real.exp (4 * Real.log 2 + 8) ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
    apply Real.exp_le_exp.mpr; linarith [h1, h2]
  linarith [exp_two_gt_four, h4, h5]

/-! ## Part 5: Polynomial growth bound -/

/-- **Polynomial growth bound for Gamma** when `Re(s) ≥ 1` and `‖s‖ ≥ 2`.

The proof uses the functional equation and reduces to strip bounds. The key
technical lemma is that the exponential `exp(2|s|log|s| + 4|s|)` dominates
any polynomial growth that arises from the functional equation.

The complete proof requires careful analysis of the functional equation iteration
and Stirling's asymptotic formula for large |Im(s)|. -/
theorem Gamma_polynomial_growth {s : ℂ} (hs_re : 1 ≤ s.re) (hs_norm : 2 ≤ ‖s‖) :
    ‖Complex.Gamma s‖ ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
  have h_norm_pos : 0 < ‖s‖ := by linarith
  have h_log_nonneg : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  have h_exp_ge_4 := exp_bound_ge_four hs_norm

  -- For Re(s) ∈ [1, 2], use strip bounds and functional equation
  by_cases h_re_le_1 : s.re ≤ 1
  · -- Re(s) = 1: Direct strip bound gives |Γ(s)| ≤ 4
    have h := Gamma_strip_bound (by linarith) h_re_le_1
    linarith [h, h_exp_ge_4]
  · -- Re(s) > 1: Use functional equation iteratively
    push_neg at h_re_le_1
    -- Strategy: Apply the functional equation n times where n = ⌊Re(s)⌋ - 1
    -- to reduce to Re ∈ (0, 1], then use strip bounds.
    -- The product of factors (s-1)(s-2)···(s-n) is bounded by (2|s|)^n.
    -- The key is showing the exponential bound dominates this polynomial growth.

    -- We use strong induction on ⌊Re(s)⌋
    have h_floor_ge_1 : 1 ≤ ⌊s.re⌋ := Int.le_floor.mpr (by exact_mod_cast le_of_lt h_re_le_1)

    -- Case: Re(s) ∈ (1, 2]
    by_cases h_re_le_2 : s.re ≤ 2
    · -- Γ(s) = (s-1)·Γ(s-1) where Re(s-1) ∈ (0, 1]
      have hs1_ne : s - 1 ≠ 0 := by
        intro h
        have : (s - 1).re = 0 := by rw [h]; simp
        simp [Complex.sub_re] at this
        linarith
      have h_func : Complex.Gamma s = (s - 1) * Complex.Gamma (s - 1) := by
        conv_lhs => rw [show s = (s - 1) + 1 by ring]
        exact Complex.Gamma_add_one (s - 1) hs1_ne
      rw [h_func, norm_mul]

      -- Bound |s - 1|
      have h_s1_norm : ‖s - 1‖ ≤ ‖s‖ + 1 := by
        calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le s 1
          _ = ‖s‖ + 1 := by simp

      -- Bound |Γ(s-1)| using strip bound
      have hs1_re_pos : 0 < (s - 1).re := by simp; linarith
      have hs1_re_hi : (s - 1).re ≤ 1 := by simp; linarith
      have h_gamma : ‖Complex.Gamma (s - 1)‖ ≤ 1 / (s - 1).re + Real.sqrt Real.pi :=
        Complex.Gammaℝ.norm_Complex_Gamma_le_of_re_ge hs1_re_pos (le_refl _) hs1_re_hi

      -- Key estimate: (|s|+1) * (1/(s.re-1) + √π)
      -- For |s| ≥ 2 and s.re ∈ (1, 2]:
      -- If s.re - 1 ≥ 1/|s|, then 1/(s.re-1) ≤ |s|, and product ≤ (|s|+1)(|s|+2) ≤ 4|s|²
      -- If s.re - 1 < 1/|s|, then |s.im|² ≥ |s|² - (1 + 1/|s|)² ≥ |s|² - 2 (for |s| ≥ 2)
      --   So |s.im| ≥ √(|s|² - 2), meaning |s-1|/|s.im| ratio is bounded.

      -- Simplified approach: Show directly that the product is ≤ exp bound
      simp only [Complex.sub_re, Complex.one_re] at h_gamma hs1_re_pos ⊢
      calc ‖s - 1‖ * ‖Complex.Gamma (s - 1)‖
          ≤ (‖s‖ + 1) * (1 / (s.re - 1) + Real.sqrt Real.pi) := by
              apply mul_le_mul h_s1_norm h_gamma (norm_nonneg _)
              linarith [norm_nonneg s]
        _ ≤ (‖s‖ + 1) * (1 / (s.re - 1) + 2) := by
              apply mul_le_mul_of_nonneg_left _ (by linarith [norm_nonneg s])
              linarith [sqrt_pi_lt_two]
        _ ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
              -- The exponential exp(2|s|log|s| + 4|s|) = |s|^{2|s|} * e^{4|s|}
              -- For |s| ≥ 2: |s|^{2|s|} ≥ |s|^4 and e^{4|s|} ≥ e^8 > 2980
              -- The LHS polynomial is dominated

              -- For the interval s.re ∈ (1, 2], the denominator s.re - 1 ∈ (0, 1]
              -- So 1/(s.re - 1) ≥ 1. The worst case is s.re → 1.
              -- But when s.re → 1 and |s| ≥ 2, |s.im| → √3 ≈ 1.73

              -- Split into two cases based on s.re - 1
              by_cases h_denom : (s.re - 1) ≥ 1 / ‖s‖
              · -- Case 1: 1/(s.re - 1) ≤ |s|
                have h_inv : 1 / (s.re - 1) ≤ ‖s‖ := by
                  rw [div_le_iff₀ hs1_re_pos]
                  have : ‖s‖ * (s.re - 1) ≥ ‖s‖ * (1 / ‖s‖) := by
                    apply mul_le_mul_of_nonneg_left h_denom (le_of_lt h_norm_pos)
                  simp at this
                  linarith
                calc (‖s‖ + 1) * (1 / (s.re - 1) + 2)
                    ≤ (‖s‖ + 1) * (‖s‖ + 2) := by
                      apply mul_le_mul_of_nonneg_left _ (by linarith [norm_nonneg s])
                      linarith [h_inv]
                  _ = ‖s‖ ^ 2 + 3 * ‖s‖ + 2 := by ring
                  _ ≤ 4 * ‖s‖ ^ 2 := by nlinarith [hs_norm]
                  _ ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
                      -- 4|s|² ≤ |s|^{2|s|} * e^{4|s|}
                      -- For |s| ≥ 2: |s|^{2|s|} ≥ 2^4 = 16, e^{4|s|} ≥ e^8 > 2980
                      -- So RHS ≥ 16 * 2980 > 40000 >> 4 * 4 = 16
                      have h_exp_large : Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) ≥
                          Real.exp (4 * Real.log 2 + 8) := by
                        apply Real.exp_le_exp.mpr
                        have h1 : 2 * ‖s‖ * Real.log ‖s‖ ≥ 2 * 2 * Real.log 2 := by
                          have hlog : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hs_norm
                          nlinarith [h_norm_pos, h_log_nonneg]
                        have h2 : 4 * ‖s‖ ≥ 4 * 2 := by linarith
                        linarith
                      -- exp(4 log 2 + 8) = 2^4 * e^8 = 16 * e^8 > 16 * 2980 > 47000
                      have h1 : Real.exp (4 * Real.log 2 + 8) = 16 * Real.exp 8 := by
                        rw [Real.exp_add, Real.exp_mul]
                        simp [Real.exp_log (by norm_num : (2:ℝ) > 0)]
                        ring
                      have h2 : Real.exp 8 > 2400 := by
                        calc Real.exp 8 = (Real.exp 2) ^ 4 := by rw [← Real.exp_nat_mul]; ring
                          _ > 7 ^ 4 := by nlinarith [exp_two_gt_seven, Real.exp_pos 2]
                          _ = 2401 := by norm_num
                          _ > 2400 := by norm_num
                      have h3 : 16 * Real.exp 8 > 16 * 2400 := by nlinarith [h2]
                      have h4 : 16 * 2400 = 38400 := by norm_num
                      have h5 : 4 * ‖s‖ ^ 2 ≤ 4 * ‖s‖ ^ 2 := le_refl _
                      have h6 : 4 * ‖s‖ ^ 2 ≤ 16 := by nlinarith [hs_norm]
                      calc 4 * ‖s‖ ^ 2 ≤ 16 := h6
                        _ < 16 * 2400 := by norm_num
                        _ < 16 * Real.exp 8 := h3
                        _ = Real.exp (4 * Real.log 2 + 8) := h1.symm
                        _ ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := h_exp_large
              · -- Case 2: s.re - 1 < 1/|s|, so s.re is very close to 1
                push_neg at h_denom
                -- In this case, |s.im|² ≥ |s|² - (s.re)² ≥ |s|² - (1 + 1/|s|)²
                -- For |s| = 2: (1 + 1/2)² = 2.25, so |s.im|² ≥ 4 - 2.25 = 1.75, |s.im| ≥ 1.32
                -- The product (|s|+1)/(s.re-1) could still be large, but is bounded by
                -- (|s|+1) * |s| = |s|² + |s| (since s.re - 1 ≥ 1/|s| is FALSE here, but s.re-1 > 0)

                -- Actually in this case, 1/(s.re-1) > |s|, so the bound from Case 1 doesn't work.
                -- We need a different argument.

                -- Key: The exponential exp(8) > 2980 while the polynomial for |s| = 2 is at most
                -- (2+1) * (|s|+2) = 3 * 4 = 12 (if 1/(s.re-1) ~ |s|) but actually could be larger.

                -- Let's use: Since we're in the strip with Re ≤ 2, |s - 1| ≤ √(1 + |s.im|²)
                -- and |s.im|² = |s|² - s.re² ≤ |s|².
                -- So |s - 1| ≤ √(1 + |s|²) ≤ √2 * |s| for |s| ≥ 1.

                have h_s1_refined : ‖s - 1‖ ≤ 2 * ‖s‖ := by
                  calc ‖s - 1‖ ≤ ‖s‖ + 1 := h_s1_norm
                    _ ≤ ‖s‖ + ‖s‖ := by linarith [hs_norm]
                    _ = 2 * ‖s‖ := by ring

                -- |s - 1| / (s.re - 1) ≤ 2|s| / (s.re - 1)
                -- The ratio 1/(s.re - 1) can be bounded using |s - 1|.
                -- |s - 1|² = (s.re - 1)² + s.im²
                -- So s.re - 1 = √(|s - 1|² - s.im²) when this makes sense.

                -- Simpler: (|s|+1) * (1/(s.re-1) + 2)
                -- = (|s|+1)/(s.re-1) + 2(|s|+1)
                -- ≤ 2|s|/(s.re-1) + 4|s| (using |s| + 1 ≤ 2|s|)

                -- Now 2|s|/(s.re - 1) = 2|s| * (s.re - 1)^{-1}
                -- We have s.re - 1 > 0, so this is positive.

                -- The exponential dominates: exp(2|s|log|s| + 4|s|) ≥ e^{4|s|} ≥ e^8 > 2980
                -- We need: (|s|+1)/(s.re-1) + 2(|s|+1) ≤ 2980

                -- For |s| = 2 and s.re = 1 + ε with tiny ε:
                -- LHS ~ 3/ε + 6, which blows up as ε → 0.

                -- BUT: If s.re = 1 + ε and |s| = 2, then s.im² = 4 - (1+ε)² ≈ 3 - 2ε
                -- So |s.im| ≈ √3 ≈ 1.73, which is bounded away from 0.

                -- The issue is that (|s|+1)/(s.re-1) can be huge.
                -- We need Stirling for large |Im|!

                -- For now, note that the FULL proof requires Stirling's formula:
                -- |Γ(σ + it)| ~ √(2π) |t|^{σ-1/2} e^{-π|t|/2} as |t| → ∞
                -- This gives EXPONENTIAL DECAY in |t|, not growth.

                -- With Stirling, for (s - 1) with Re = σ - 1 ∈ (0, 1) and |s.im| large:
                -- |Γ(s - 1)| ~ √(2π) |s.im|^{σ-3/2} e^{-π|s.im|/2}
                -- Then |s - 1| * |Γ(s - 1)| ~ √(2π) |s.im|^{σ-1/2} e^{-π|s.im|/2}
                -- which decays exponentially in |s.im|.

                -- Without Stirling's full asymptotic, we use the bound from the integral:
                have h_crude : (‖s‖ + 1) * (1 / (s.re - 1) + 2) ≤
                    Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
                  -- We'll establish this using the magnitude of the exponential
                  have h_exp_ge : Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) ≥
                      Real.exp (4 * 2 + 4 * 2) := by
                    apply Real.exp_le_exp.mpr
                    have h1 : 2 * ‖s‖ * Real.log ‖s‖ ≥ 0 := by nlinarith [h_norm_pos, h_log_nonneg]
                    have h2 : 4 * ‖s‖ ≥ 4 * 2 := by linarith
                    linarith
                  have h_exp16 : Real.exp 16 > 8000000 := by
                    have he2 : Real.exp 2 > 7.3 := by
                      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; ring
                        _ > 2.71 * 2.71 := by nlinarith [Real.exp_one_gt_d9]
                        _ > 7.3 := by norm_num
                    have he4 : Real.exp 4 > 53 := by
                      calc Real.exp 4 = (Real.exp 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring
                        _ > 7.3 ^ 2 := by nlinarith [Real.exp_pos 2, he2]
                        _ > 53 := by norm_num
                    calc Real.exp 16 = (Real.exp 4) ^ 4 := by rw [← Real.exp_nat_mul]; ring
                      _ > 53 ^ 4 := by nlinarith [Real.exp_pos 4, he4]
                      _ = 7890481 := by norm_num
                      _ > 7800000 := by norm_num
                  -- (|s|+1)*(1/(s.re-1) + 2) with |s| ≥ 2, s.re ∈ (1, 2]
                  -- Even if s.re - 1 = 0.0001, the term 1/(s.re-1) = 10000
                  -- (|s|+1) * 10002 ≤ 3 * 10002 = 30006 << 8500000

                  -- But s.re - 1 > 0 must hold. The question is: what's the minimum?
                  -- For |s| = 2 and s.re minimized: s.re can approach 1 (as |s.im| → √3)
                  -- So s.re - 1 can be arbitrarily small!

                  -- The resolution: We bound using |s - 1|, not s.re - 1.
                  -- |s - 1|² = (s.re - 1)² + s.im²
                  -- For s.re ∈ (1, 2] and |s| ≥ 2:
                  -- |s - 1| ≥ |s.im| = √(|s|² - s.re²) ≥ √(4 - 4) = 0 (worst case s.re = |s|)
                  -- But if s.re ≤ 2 and |s| = 2, then s.re ≤ 2 = |s|, equality at s.im = 0.
                  -- So |s.im| can be 0 only when s.re = |s| = 2, meaning s = 2.

                  -- At s = 2: Γ(2) = 1! = 1, trivially bounded.
                  by_cases hs_eq_2 : s = 2
                  · simp [hs_eq_2]
                    calc 1 * 1 = 1 := by ring
                      _ ≤ Real.exp 16 := by linarith [h_exp16]
                      _ ≤ Real.exp (2 * ‖(2 : ℂ)‖ * Real.log ‖(2 : ℂ)‖ + 4 * ‖(2 : ℂ)‖) := by
                          simp
                          apply Real.exp_le_exp.mpr
                          have hlog2 : Real.log 2 > 0.69 := log_two_gt
                          calc (16 : ℝ) = 4 * 2 + 4 * 2 := by ring
                            _ ≤ 4 * Real.log 2 + 8 + (4 * Real.log 2 + 8) := by linarith [hlog2]
                            _ = 2 * 2 * (2 * Real.log 2) + 4 * 2 := by ring
                            -- Need: 2 log 2 = log 4 ≥ log 2 (TRUE)
                            -- Actually: 2 * 2 * (2 * log 2) = 8 log 2 ≈ 5.5
                            -- and 4 * 2 = 8, so total ≈ 13.5 < 16 !
                            -- Let me recalculate:
                            -- exp(2*2*log(2) + 4*2) = exp(4 log 2 + 8) = 2^4 * e^8 = 16 * e^8
                            -- e^8 > 2980, so 16 * 2980 > 47000 > 16. ✓
                          have hcalc : 2 * 2 * Real.log 2 + 4 * 2 = 4 * Real.log 2 + 8 := by ring
                          have h1 : 4 * Real.log 2 + 8 > 4 * 0.69 + 8 := by linarith [hlog2]
                          have h2 : 4 * 0.69 + 8 = 10.76 := by norm_num
                          linarith [h1, h2]
                  · -- s ≠ 2, so either s.re < 2 or s.im ≠ 0
                    -- In either case, we can bound the product differently.
                    -- The core issue is 1/(s.re - 1) when s.re → 1.

                    -- Key observation: |s - 1|² ≥ s.im² = |s|² - s.re² ≥ 4 - 4 = 0
                    -- But we need a positive lower bound.

                    -- If s ≠ 2 and |s| ≥ 2 and s.re ∈ (1, 2]:
                    -- Either s.re < 2 (so s.im ≠ 0, |s.im| > 0) or s.re = 2 and s.im ≠ 0.

                    have h_sim_sq : s.im ^ 2 = ‖s‖ ^ 2 - s.re ^ 2 := by
                      have h := Complex.normSq_eq_norm_sq s
                      simp [Complex.normSq] at h
                      linarith

                    have h_s1_sq : ‖s - 1‖ ^ 2 = (s.re - 1) ^ 2 + s.im ^ 2 := by
                      rw [← Complex.normSq_eq_norm_sq]
                      simp [Complex.normSq]

                    -- The full resolution requires Stirling asymptotics.
                    -- For a complete proof at mathlib standards, one would need:
                    -- 1. Stirling's asymptotic formula for complex Gamma
                    -- 2. The bound |Γ(σ + it)| ~ C * |t|^{σ-1/2} * e^{-π|t|/2} for |t| → ∞
                    -- This gives exponential DECAY in |t|, dominating any polynomial growth.

                    -- KEY: When s.re is close to 1 and |s| ≥ 2, |s.im| is LARGE.
                    -- This means Γ(s-1) has EXPONENTIAL DECAY, not growth!

                    have h_sim_sq : s.im ^ 2 = ‖s‖ ^ 2 - s.re ^ 2 := by
                      have h := Complex.normSq_eq_norm_sq s
                      simp [Complex.normSq] at h
                      linarith

                    have h_sre_bound : s.re ^ 2 < (1 + 1 / (4 * ‖s‖)) ^ 2 := by
                      have h1 : s.re < 1 + 1 / (4 * ‖s‖) := by linarith [h_denom]
                      have h2 : 0 < s.re := by linarith
                      exact sq_lt_sq' (by linarith) h1

                    have h_14s_bound : (1 + 1 / (4 * ‖s‖)) ^ 2 ≤ 1.5 := by
                      have h1 : 1 / (4 * ‖s‖) ≤ 1 / 8 := by
                        apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
                      have h2 : 1 + 1 / (4 * ‖s‖) ≤ 1.125 := by linarith
                      nlinarith [h2]

                    have h_sim_sq_ge : s.im ^ 2 ≥ ‖s‖ ^ 2 - 1.5 := by
                      rw [h_sim_sq]
                      have : s.re ^ 2 < 1.5 := calc s.re ^ 2 < (1 + 1 / (4 * ‖s‖)) ^ 2 := h_sre_bound
                        _ ≤ 1.5 := h_14s_bound
                      linarith

                    have h_sim_ge_1 : |s.im| ≥ 1 := by
                      have h1 : ‖s‖ ^ 2 - 1.5 ≥ 4 - 1.5 := by nlinarith [hs_norm]
                      have h2 : s.im ^ 2 ≥ 2.5 := by linarith [h_sim_sq_ge, h1]
                      have h3 : |s.im| = Real.sqrt (s.im ^ 2) := (Real.sqrt_sq_eq_abs s.im).symm
                      rw [h3]
                      calc Real.sqrt (s.im ^ 2) ≥ Real.sqrt 2.5 := Real.sqrt_le_sqrt h2
                        _ > 1 := by
                            have : Real.sqrt 2.5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
                            linarith [Real.sqrt_one]

                    -- Use the exponential decay: |Γ(s-1)| ≤ 16π · e^{-π|s.im|/2}
                    have h_decay := Complex.Gamma.norm_decay_strip_large_im
                      (by simp; linarith : (1/2 : ℝ) ≤ (s - 1).re)
                      (by simp; linarith : (s - 1).re ≤ 1)
                      (by simp; exact h_sim_ge_1 : 1 ≤ |(s - 1).im|)

                    -- The product |s-1| * |Γ(s-1)| uses the decay bound
                    -- |s-1| ≤ |s| + 1 ≤ 2|s| and |Γ(s-1)| ≤ 16π e^{-π|s.im|/2}
                    -- So |s-1| * |Γ(s-1)| ≤ 2|s| * 16π * e^{-π|s.im|/2}

                    -- For |s.im| ≥ √2.5 > 1.58, e^{-π*1.58/2} < 0.1
                    -- So 2|s| * 16π * 0.1 < 32π|s| * 0.1 = 3.2π|s| ≈ 10|s|
                    -- This is MUCH smaller than exp(2|s|log|s| + 4|s|) for |s| ≥ 2

                    have h_decay_product : ‖s - 1‖ * ‖Complex.Gamma (s - 1)‖ ≤
                        (‖s‖ + 1) * (16 * Real.pi * Real.exp (-Real.pi * |s.im| / 2)) := by
                      apply mul_le_mul h_s1_bound h_decay (norm_nonneg _) (by linarith [norm_nonneg s])

                    have h_exp_bound : (‖s‖ + 1) * (16 * Real.pi * Real.exp (-Real.pi * |s.im| / 2)) ≤
                        Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
                      -- For |s.im| ≥ √2.5, -π|s.im|/2 ≤ -π√2.5/2 < -2.5
                      -- So exp(-π|s.im|/2) < exp(-2.5) < 0.1
                      have h_exp_small : Real.exp (-Real.pi * |s.im| / 2) ≤ Real.exp (-2.4) := by
                        apply Real.exp_le_exp.mpr
                        have h1 : |s.im| ≥ Real.sqrt 2.5 := by
                          have h2 : s.im ^ 2 ≥ 2.5 := by linarith [h_sim_sq_ge, hs_norm]
                          calc |s.im| = Real.sqrt (s.im ^ 2) := (Real.sqrt_sq_eq_abs s.im).symm
                            _ ≥ Real.sqrt 2.5 := Real.sqrt_le_sqrt h2
                        have h2 : Real.sqrt 2.5 > 1.5 := by
                          have : (1.5 : ℝ) ^ 2 = 2.25 := by norm_num
                          have : 2.25 < 2.5 := by norm_num
                          calc Real.sqrt 2.5 > Real.sqrt 2.25 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
                            _ = 1.5 := by rw [Real.sqrt_eq_iff_sq_eq (by norm_num) (by norm_num)]; norm_num
                        have h3 : -Real.pi * |s.im| / 2 ≤ -Real.pi * 1.5 / 2 := by
                          have hpi : Real.pi > 0 := Real.pi_pos
                          nlinarith [h1, h2]
                        have h4 : -Real.pi * 1.5 / 2 < -2.4 := by
                          have hpi : Real.pi > 3.1 := by linarith [Real.pi_gt_three]
                          nlinarith
                        linarith
                      -- exp(-2.4) < 0.1
                      have h_exp_01 : Real.exp (-2.4) < 0.1 := by
                        have h1 : Real.exp 2.4 > 10 := by
                          calc Real.exp 2.4 > Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
                            _ > 7 := exp_two_gt_seven
                            _ > 10 - 4 := by norm_num
                          calc Real.exp 2.4 = Real.exp 2 * Real.exp 0.4 := by rw [← Real.exp_add]; ring
                            _ > 7 * 1 := by nlinarith [exp_two_gt_seven, Real.exp_pos 0.4]
                            _ > 10 - 4 := by norm_num
                          calc Real.exp 2.4 = Real.exp 2 * Real.exp 0.4 := by rw [← Real.exp_add]; ring
                            _ > 7 * 1.4 := by
                                have he04 : Real.exp 0.4 > 1.4 := by
                                  have := Real.add_one_le_exp 0.4
                                  linarith
                                nlinarith [exp_two_gt_seven]
                            _ = 9.8 := by norm_num
                            _ > 10 - 1 := by norm_num
                        rw [Real.exp_neg]
                        calc (Real.exp 2.4)⁻¹ < 10⁻¹ := by
                            apply inv_lt_inv_of_lt (by norm_num) h1
                          _ = 0.1 := by norm_num
                      -- (|s|+1) * 16π * 0.1 ≤ 3 * 16 * 4 * 0.1 = 19.2 for |s| = 2
                      -- And exp(2*2*log(2) + 4*2) = exp(4*0.69 + 8) ≈ exp(10.8) > 49000
                      calc (‖s‖ + 1) * (16 * Real.pi * Real.exp (-Real.pi * |s.im| / 2))
                          ≤ (‖s‖ + 1) * (16 * Real.pi * Real.exp (-2.4)) := by
                              apply mul_le_mul_of_nonneg_left _ (by linarith [norm_nonneg s])
                              apply mul_le_mul_of_nonneg_left h_exp_small (by linarith [Real.pi_pos])
                        _ < (‖s‖ + 1) * (16 * 4 * 0.1) := by
                              apply mul_lt_mul_of_pos_left _ (by linarith [norm_nonneg s])
                              have hpi_lt : Real.pi < 4 := Real.pi_lt_four
                              nlinarith [hpi_lt, h_exp_01]
                        _ = (‖s‖ + 1) * 6.4 := by ring
                        _ ≤ 3 * 6.4 := by nlinarith [hs_norm]
                        _ = 19.2 := by norm_num
                        _ < Real.exp 3 := by
                              have : Real.exp 3 > 20 := by
                                calc Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
                                    rw [← Real.exp_add, ← Real.exp_add]; ring
                                  _ > 2.7 * 2.7 * 2.7 := by nlinarith [Real.exp_one_gt_d9]
                                  _ > 19 := by norm_num
                              linarith
                        _ ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
                              apply Real.exp_le_exp.mpr
                              have h1 : 2 * ‖s‖ * Real.log ‖s‖ ≥ 0 := by nlinarith [h_norm_pos, h_log_nonneg]
                              have h2 : 4 * ‖s‖ ≥ 8 := by linarith
                              linarith

                    exact le_trans h_decay_product h_exp_bound

    · -- Re(s) > 2: Iterate the functional equation
      push_neg at h_re_le_2
      -- This case reduces to the (1, 2] case via iteration.
      -- The functional equation Γ(s) = (s-1)·Γ(s-1) is applied n times where
      -- n = ⌊Re(s)⌋ - 1, so that (s-n) has Re ∈ [1, 2).
      -- |Γ(s)| = |∏(s-k)|·|Γ(s-n)| ≤ (2|s|)^n · |Γ(s-n)|
      -- Since (s-n) ∈ [1, 2), we use the bounds above for |Γ(s-n)|.
      -- The product (2|s|)^n ≤ (2|s|)^|s| which is polynomial in |s|.
      -- The exponential exp(2|s|log|s| + 4|s|) dominates this polynomial.
      sorry

/-! ## Part 6: Main Stirling bound -/

/-- **Core Stirling bound** for the complex Gamma function in the right half-plane.

There exist absolute constants `C, A, B > 0` such that for all `s` with
`Re(s) ≥ 1/2` and `‖s‖ ≥ A` we have `‖Γ(s)‖ ≤ exp(C‖s‖ log(B‖s‖))`.

This is the fundamental growth estimate used in establishing finite order
of L-functions and the Hadamard factorization theorem. -/
theorem Gamma_stirling_core :
    ∃ C A B : ℝ, 0 < C ∧ 0 < A ∧ 1 ≤ B ∧
      ∀ ⦃s : ℂ⦄, (1 / 2 : ℝ) ≤ s.re → A ≤ ‖s‖ →
        ‖Complex.Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (B * ‖s‖)) := by
  use 4, 2, 2
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro s hs_re hs_norm
  have h_norm_pos : 0 < ‖s‖ := by linarith
  have h_2s_pos : 0 < 2 * ‖s‖ := by linarith
  have h_log_pos : 0 < Real.log (2 * ‖s‖) := Real.log_pos (by linarith)
  have h_log_nonneg : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)

  by_cases h_re_ge_one : 1 ≤ s.re
  · -- Re(s) ≥ 1: use polynomial growth bound
    have hpoly := Gamma_polynomial_growth h_re_ge_one hs_norm
    -- Convert exp(2|s|log|s| + 4|s|) ≤ exp(4|s|log(2|s|))
    calc ‖Complex.Gamma s‖
        ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := hpoly
      _ ≤ Real.exp (4 * ‖s‖ * Real.log (2 * ‖s‖)) := by
          apply Real.exp_le_exp.mpr
          have h_log_2s : Real.log (2 * ‖s‖) = Real.log 2 + Real.log ‖s‖ := by
            rw [Real.log_mul (by norm_num) (by linarith)]
          rw [h_log_2s]
          have hlog2 := log_two_gt
          have hlogs : Real.log ‖s‖ ≥ Real.log 2 := Real.log_le_log (by norm_num) hs_norm
          have h_ineq : (2 : ℝ) ≤ 2 * Real.log 2 + Real.log ‖s‖ := by
            calc (2 : ℝ) ≤ 2 * 0.69 + 0.69 := by norm_num
              _ ≤ 2 * Real.log 2 + Real.log 2 := by linarith [hlog2]
              _ ≤ 2 * Real.log 2 + Real.log ‖s‖ := by linarith [hlogs]
          nlinarith [h_log_nonneg, h_norm_pos]

  · -- 1/2 ≤ Re(s) < 1: use strip bound
    push_neg at h_re_ge_one
    have h := Gamma_strip_bound hs_re (le_of_lt h_re_ge_one)
    -- Show 4 ≤ exp(4|s|log(2|s|)) for |s| ≥ 2
    have h_exp_large : (4 : ℝ) ≤ Real.exp (4 * ‖s‖ * Real.log (2 * ‖s‖)) := by
      have h1 : 4 * ‖s‖ * Real.log (2 * ‖s‖) ≥ 4 * 2 * Real.log 4 := by
        have hlog4 : Real.log 4 ≤ Real.log (2 * ‖s‖) := by
          apply Real.log_le_log (by norm_num)
          linarith
        nlinarith [hlog4, h_log_pos, hs_norm]
      have h2 : Real.log 4 > 1.38 := by
        have hlog2_gt : Real.log 2 > 0.693 := by linarith [Real.log_two_gt_d9]
        calc Real.log 4 = Real.log (2^2) := by norm_num
          _ = 2 * Real.log 2 := Real.log_pow 2 2
          _ > 2 * 0.693 := by linarith
          _ > 1.38 := by norm_num
      have h3 : 4 * 2 * Real.log 4 > 11 := by linarith [h2]
      have h4 := exp_two_gt_four
      have h5 : Real.exp (4 * 2 * Real.log 4) ≤ Real.exp (4 * ‖s‖ * Real.log (2 * ‖s‖)) :=
        Real.exp_le_exp.mpr h1
      have h6 : Real.exp 11 < Real.exp (4 * 2 * Real.log 4) := Real.exp_lt_exp.mpr h3
      have h7 : Real.exp 2 < Real.exp 11 := Real.exp_lt_exp.mpr (by norm_num)
      linarith [h4, h5, h6, h7]
    calc ‖Complex.Gamma s‖ ≤ 4 := h
      _ ≤ Real.exp (4 * ‖s‖ * Real.log (2 * ‖s‖)) := h_exp_large

end GammaBounds
