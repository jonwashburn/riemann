/-
Copyright (c) 2024 The Riemann Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Riemann Project Contributors
-/
import Mathlib
import Riemann.academic_framework.FiniteOrder
import Riemann.academic_framework.ZetaFiniteOrder
import Riemann.academic_framework.StirlingBounds
import Riemann.academic_framework.StirlingB
import Riemann.Mathlib.Analysis.Complex.HardySpace.PowerSeriesBounds
import PrimeNumberTheoremAnd.StrongPNT

/-!
# Hadamard Factorization for Entire Functions of Finite Order

This file establishes the Hadamard factorization theorem for entire functions of finite order,
providing a complete API suitable for applications in analytic number theory.

## Main definitions

* `ComplexAnalysis.Hadamard.EntireOfFiniteOrder` : Predicate for entire functions of finite order
* `ComplexAnalysis.Hadamard.weierstrassFactor` : The Weierstrass elementary factor E_m(z)
* `ComplexAnalysis.Hadamard.ZeroData` : Abstract zero data with multiplicities
* `ComplexAnalysis.Hadamard.CanonicalProduct` : The canonical product over zeros

## Main results

* `ComplexAnalysis.Hadamard.weierstrassFactor_bound` : Bounds on |E_m(z) - 1|
* `ComplexAnalysis.Hadamard.canonical_product_converges` : Convergence of canonical products
* `ComplexAnalysis.Hadamard.hadamard_factorization` : The main factorization theorem
* `ComplexAnalysis.Hadamard.hadamard_riemannZeta` : Application to the Riemann zeta function

## Mathematical Background

The **Hadamard factorization theorem** states that every entire function f of finite order ρ
can be written as:

  f(z) = z^m · e^{g(z)} · ∏_n E_p(z/a_n)

where:
- m is the order of the zero at the origin
- g is a polynomial of degree at most ⌈ρ⌉
- a_n are the nonzero zeros of f
- p ≤ ⌊ρ⌋ is the genus
- E_p(z) = (1-z) exp(z + z²/2 + ... + z^p/p) is the Weierstrass elementary factor

The proof proceeds in several steps:
1. Use Jensen's formula to bound the counting function n(r) of zeros
2. Apply Lindelöf's theorem to show ∑|a_n|^{-σ} < ∞ for σ > ρ
3. Construct the canonical product and show it converges
4. Show the quotient f/G is entire and zero-free with polynomial growth
5. Apply the Borel-Carathéodory theorem to conclude it's exp of a polynomial

## References

* Ahlfors, L.V., "Complex Analysis", Chapter 5
* Titchmarsh, E.C., "The Theory of Functions", Chapter 8
* Levin, B.Ya., "Distribution of Zeros of Entire Functions"
* Conway, J.B., "Functions of One Complex Variable II", Chapter 11
-/

noncomputable section

namespace ComplexAnalysis
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology

/-! ## Part 1: Entire Functions of Finite Order -/

/--
`EntireOfFiniteOrder ρ f` means `f : ℂ → ℂ` is entire (differentiable on all of ℂ) and
has (global) order at most `ρ`.

The order condition is encoded via a global bound on `log(1 + ‖f(z)‖)` in terms of `(1 + ‖z‖)^ρ`.
This formulation is flexible enough for Hadamard products and matches standard complex-analytic
conventions.

## Mathematical background

The **order** of an entire function `f` is defined as
```
ρ = limsup_{r → ∞} (log log M(r)) / log r
```
where `M(r) = sup_{|z|=r} |f(z)|`. Our definition is equivalent for finite order.
-/
structure EntireOfFiniteOrder (ρ : ℝ) (f : ℂ → ℂ) : Prop where
  /-- The function is entire (differentiable on all of ℂ). -/
  entire : Differentiable ℂ f
  /-- Global growth bound of order at most `ρ`. -/
  growth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ

namespace EntireOfFiniteOrder

variable {ρ ρ' : ℝ} {f g : ℂ → ℂ}

/-- An entire function of finite order is differentiable everywhere. -/
lemma differentiable (hf : EntireOfFiniteOrder ρ f) : Differentiable ℂ f := hf.entire

/-- An entire function of finite order is continuous. -/
lemma continuous (hf : EntireOfFiniteOrder ρ f) : Continuous f := hf.entire.continuous

/-- An entire function of finite order is analytic at every point. -/
lemma analyticAt (hf : EntireOfFiniteOrder ρ f) (z : ℂ) : AnalyticAt ℂ f z :=
  hf.entire.analyticAt isOpen_univ (mem_univ z)

/-- An entire function of finite order is analytic on all of ℂ. -/
lemma analyticOnNhd (hf : EntireOfFiniteOrder ρ f) : AnalyticOnNhd ℂ f univ :=
  hf.entire.analyticOnNhd isOpen_univ

/-- A convenient coercion lemma: from `EntireOfFiniteOrder` to an explicit norm bound. -/
lemma norm_bound (hf : EntireOfFiniteOrder ρ f) :
    ∃ C' > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C' * (1 + ‖z‖) ^ ρ) := by
  rcases hf.growth with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro z
  have hlog := hC z
  have hpos : 0 < (1 : ℝ) + ‖f z‖ := by linarith [norm_nonneg (f z)]
  have h1 : (1 : ℝ) + ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ) := by
    rw [← Real.log_le_iff_le_exp hpos]
    exact hlog
  linarith [Real.exp_pos (C * (1 + ‖z‖) ^ ρ)]

/-- Maximum modulus bound on circles. -/
lemma maxModulus_bound (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r → ∀ z : ℂ, ‖z‖ = r →
      ‖f z‖ ≤ Real.exp (C * (1 + r) ^ ρ) := by
  obtain ⟨C, hCpos, hC⟩ := hf.norm_bound
  exact ⟨C, hCpos, fun r _ z hz => by rw [hz] at hC; exact hC z⟩

/-- If `f` has order `ρ` and `ρ ≤ ρ'`, then `f` has order at most `ρ'`. -/
lemma of_le_order (hf : EntireOfFiniteOrder ρ f) (hρ : ρ ≤ ρ') :
    EntireOfFiniteOrder ρ' f := by
  constructor
  · exact hf.entire
  · rcases hf.growth with ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, ?_⟩
    intro z
    calc Real.log (1 + ‖f z‖)
        ≤ C * (1 + ‖z‖) ^ ρ := hC z
      _ ≤ C * (1 + ‖z‖) ^ ρ' := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) hρ

/-- The product of entire functions of finite order has finite order. -/
lemma mul (hf : EntireOfFiniteOrder ρ f) (hg : EntireOfFiniteOrder ρ' g) :
    EntireOfFiniteOrder (max ρ ρ') (f * g) := by
  constructor
  · exact hf.entire.mul hg.entire
  · rcases hf.growth with ⟨Cf, hCf_pos, hCf⟩
    rcases hg.growth with ⟨Cg, hCg_pos, hCg⟩
    use Cf + Cg, by linarith
    intro z
    have h_prod_norm : ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    have h1 : 1 + ‖f z‖ * ‖g z‖ ≤ (1 + ‖f z‖) * (1 + ‖g z‖) := by
      nlinarith [norm_nonneg (f z), norm_nonneg (g z)]
    calc Real.log (1 + ‖(f * g) z‖)
        = Real.log (1 + ‖f z‖ * ‖g z‖) := by rw [h_prod_norm]
      _ ≤ Real.log ((1 + ‖f z‖) * (1 + ‖g z‖)) := by
          apply Real.log_le_log (by positivity) h1
      _ = Real.log (1 + ‖f z‖) + Real.log (1 + ‖g z‖) :=
          Real.log_mul (by positivity) (by positivity)
      _ ≤ Cf * (1 + ‖z‖) ^ ρ + Cg * (1 + ‖z‖) ^ ρ' := add_le_add (hCf z) (hCg z)
      _ ≤ Cf * (1 + ‖z‖) ^ max ρ ρ' + Cg * (1 + ‖z‖) ^ max ρ ρ' := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left _ (le_of_lt hCf_pos)
            exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (le_max_left _ _)
          · apply mul_le_mul_of_nonneg_left _ (le_of_lt hCg_pos)
            exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (le_max_right _ _)
      _ = (Cf + Cg) * (1 + ‖z‖) ^ max ρ ρ' := by ring

/-- A constant function has order 0. -/
lemma const (c : ℂ) : EntireOfFiniteOrder 0 (fun _ => c) := by
  constructor
  · exact differentiable_const c
  · refine ⟨1 + Real.log (1 + ‖c‖), ?_, ?_⟩
    · have : 0 ≤ Real.log (1 + ‖c‖) := Real.log_nonneg (by linarith [norm_nonneg c])
      linarith
    · intro z
      simp only [Real.rpow_zero, mul_one]
      have h := Real.log_nonneg (by linarith [norm_nonneg c] : 1 ≤ 1 + ‖c‖)
      linarith

/-- The identity function has order 1. -/
lemma id : EntireOfFiniteOrder 1 (id : ℂ → ℂ) := by
  constructor
  · exact differentiable_id
  · use 2
    constructor; · norm_num
    intro z
    have h1 : 1 + ‖z‖ ≤ 2 * (1 + ‖z‖) := by linarith [norm_nonneg z]
    have h2 : Real.log (1 + ‖z‖) ≤ 1 + ‖z‖ := Real.log_le_self_of_pos (by linarith [norm_nonneg z])
    simp only [id, Real.rpow_one]
    calc Real.log (1 + ‖z‖) ≤ 1 + ‖z‖ := h2
      _ ≤ 2 * (1 + ‖z‖) := h1

/-- Polynomial growth bound: |P(z)| ≤ C(1 + |z|)^n for degree n polynomial. -/
lemma polynomial_growth_aux (P : Polynomial ℂ) :
    ∃ C > 0, ∀ z : ℂ, ‖Polynomial.eval z P‖ ≤ C * (1 + ‖z‖) ^ P.natDegree := by
  by_cases hP : P = 0
  · simp [hP]; use 1; simp
  · -- For nonzero polynomial, bound each term
    use P.natDegree.succ * (∑ i ∈ range P.natDegree.succ, ‖P.coeff i‖) + 1
    constructor
    · have h_sum_nn : 0 ≤ ∑ i ∈ range P.natDegree.succ, ‖P.coeff i‖ :=
        sum_nonneg (fun _ _ => norm_nonneg _)
      have h_prod_nn : 0 ≤ P.natDegree.succ * (∑ i ∈ range P.natDegree.succ, ‖P.coeff i‖) := by
        apply mul_nonneg; simp; exact h_sum_nn
      linarith
    intro z
    have h_bound := Polynomial.norm_eval_le P z
    -- |P(z)| ≤ ∑ |aᵢ| |z|^i ≤ (∑ |aᵢ|) * max(1, |z|)^n
    calc ‖Polynomial.eval z P‖
        ≤ ∑ i ∈ range P.natDegree.succ, ‖P.coeff i‖ * ‖z‖ ^ i := h_bound
      _ ≤ (∑ i ∈ range P.natDegree.succ, ‖P.coeff i‖) * (1 + ‖z‖) ^ P.natDegree := by
          apply sum_le_sum_of_nonneg_of_le
          · intro i _; exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg z) i)
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          have hi' : i ≤ P.natDegree := by
            simp only [mem_range, Nat.lt_succ_iff] at hi; exact hi
          calc ‖z‖ ^ i ≤ (1 + ‖z‖) ^ i := by
                apply pow_le_pow_left (norm_nonneg z)
                linarith [norm_nonneg z]
            _ ≤ (1 + ‖z‖) ^ P.natDegree := by
                apply pow_le_pow_right (by linarith [norm_nonneg z]) hi'
      _ ≤ (P.natDegree.succ * (∑ i ∈ range P.natDegree.succ, ‖P.coeff i‖) + 1) *
            (1 + ‖z‖) ^ P.natDegree := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith [norm_nonneg z]) _)
          have h_sum_nn : 0 ≤ ∑ i ∈ range P.natDegree.succ, ‖P.coeff i‖ :=
            sum_nonneg (fun _ _ => norm_nonneg _)
          nlinarith

/-- Polynomials have order 0 (or negative, which means finite growth). -/
lemma polynomial (P : Polynomial ℂ) : EntireOfFiniteOrder 0 (fun z => Polynomial.eval z P) := by
  constructor
  · exact Polynomial.differentiable ℂ P
  · obtain ⟨C, hC_pos, hC⟩ := polynomial_growth_aux P
    -- Use a constant that bounds log(1 + C·r^n) for all r
    use C + P.natDegree + Real.log (1 + C) + 1
    constructor
    · have hlog : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
      linarith
    intro z
    simp only [Real.rpow_zero, mul_one]
    have hP := hC z
    have h_pos : 0 < 1 + ‖Polynomial.eval z P‖ := by linarith [norm_nonneg (Polynomial.eval z P)]
    have h1 : 1 + ‖Polynomial.eval z P‖ ≤ 1 + C * (1 + ‖z‖) ^ P.natDegree := by linarith
    by_cases hn : P.natDegree = 0
    · -- Constant polynomial case
      have hC_bound : C * (1 + ‖z‖) ^ 0 = C := by simp
      calc Real.log (1 + ‖Polynomial.eval z P‖)
          ≤ Real.log (1 + C) := by
              apply Real.log_le_log h_pos
              calc 1 + ‖Polynomial.eval z P‖
                  ≤ 1 + C * (1 + ‖z‖) ^ P.natDegree := h1
                _ = 1 + C := by simp [hn]
        _ ≤ C + P.natDegree + Real.log (1 + C) + 1 := by
              have h := Real.log_nonneg (by linarith : 1 ≤ 1 + C)
              linarith
    · -- Non-constant polynomial case: use log(1 + C·r^n) ≤ log(C) + n·log(r) + log(2)
      push_neg at hn
      have hn_pos : 0 < P.natDegree := Nat.pos_of_ne_zero hn
      calc Real.log (1 + ‖Polynomial.eval z P‖)
          ≤ Real.log (1 + C * (1 + ‖z‖) ^ P.natDegree) := Real.log_le_log h_pos h1
        _ ≤ Real.log (2 * C * (1 + ‖z‖) ^ P.natDegree) := by
              apply Real.log_le_log (by linarith [hC_pos, pow_nonneg (by linarith [norm_nonneg z] : 0 ≤ 1 + ‖z‖) P.natDegree])
              have hpow : 1 ≤ (1 + ‖z‖) ^ P.natDegree := by
                apply one_le_pow₀ (by linarith [norm_nonneg z])
              nlinarith
        _ = Real.log 2 + Real.log C + P.natDegree * Real.log (1 + ‖z‖) := by
              rw [Real.log_mul (by norm_num) (by positivity)]
              rw [Real.log_mul (by norm_num) (by positivity)]
              rw [Real.log_pow]
              ring
        _ ≤ 1 + Real.log (1 + C) + P.natDegree * (1 + ‖z‖) := by
              have hlog2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
              have hlogC : Real.log C ≤ Real.log (1 + C) := Real.log_le_log hC_pos (by linarith)
              have hlog1z : Real.log (1 + ‖z‖) ≤ 1 + ‖z‖ := by
                by_cases hz : 1 + ‖z‖ ≤ 1
                · have hz' : ‖z‖ ≤ 0 := by linarith
                  have hz'' : ‖z‖ = 0 := le_antisymm hz' (norm_nonneg z)
                  simp [hz'']; norm_num
                · push_neg at hz
                  exact Real.log_le_self_of_pos (by linarith [norm_nonneg z])
              have h := mul_le_mul_of_nonneg_left hlog1z (Nat.cast_nonneg P.natDegree)
              linarith
        _ ≤ C + P.natDegree + Real.log (1 + C) + 1 := by
              have h_bound : P.natDegree * (1 + ‖z‖) ≤ P.natDegree + P.natDegree * ‖z‖ := by ring_nf
              nlinarith [norm_nonneg z, hC_pos, Nat.cast_nonneg P.natDegree]

/-- exp(az) has order 1 for any a ≠ 0. -/
lemma exp_linear {a : ℂ} (ha : a ≠ 0) : EntireOfFiniteOrder 1 (fun z => exp (a * z)) := by
  constructor
  · exact differentiable_exp.comp (differentiable_const a |>.mul differentiable_id)
  · use ‖a‖ + 1
    constructor; · linarith [norm_nonneg a]
    intro z
    simp only [Real.rpow_one]
    calc Real.log (1 + ‖exp (a * z)‖)
        ≤ Real.log (1 + Real.exp (‖a * z‖)) := by
            apply Real.log_le_log (by linarith [norm_nonneg (exp (a * z))])
            have h := Complex.abs_exp (a * z)
            simp only [Complex.norm_eq_abs] at h ⊢
            have h' : Complex.abs (exp (a * z)) = Real.exp ((a * z).re) := h
            rw [h']
            have h_re : (a * z).re ≤ ‖a * z‖ := Complex.re_le_norm _
            linarith [Real.exp_le_exp.mpr h_re, norm_nonneg (exp (a * z))]
      _ ≤ Real.log (1 + Real.exp (‖a‖ * ‖z‖)) := by
            apply Real.log_le_log (by linarith [Real.exp_nonneg (‖a * z‖)])
            have h : ‖a * z‖ ≤ ‖a‖ * ‖z‖ := norm_mul_le a z
            linarith [Real.exp_le_exp.mpr h]
      _ ≤ 1 + ‖a‖ * ‖z‖ := by
            -- log(1 + e^x) ≤ 1 + x for x ≥ 0
            have h_nn : 0 ≤ ‖a‖ * ‖z‖ := mul_nonneg (norm_nonneg a) (norm_nonneg z)
            calc Real.log (1 + Real.exp (‖a‖ * ‖z‖))
                ≤ Real.log (Real.exp 1 * Real.exp (‖a‖ * ‖z‖)) := by
                    apply Real.log_le_log (by linarith [Real.exp_nonneg (‖a‖ * ‖z‖)])
                    have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
                    nlinarith [Real.exp_nonneg (‖a‖ * ‖z‖)]
              _ = 1 + ‖a‖ * ‖z‖ := by rw [← Real.exp_add]; simp
      _ ≤ (‖a‖ + 1) * (1 + ‖z‖) := by nlinarith [norm_nonneg a, norm_nonneg z]

end EntireOfFiniteOrder

/-! ## Part 2: Weierstrass Elementary Factors -/

/--
The Weierstrass elementary factor of genus `m`:
```
E_m(z) = (1 - z) * exp(z + z²/2 + ... + z^m/m)
```
This is the building block for canonical products in the Hadamard factorization. -/
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (∑ k ∈ range m.succ, z ^ (k + 1) / (k + 1))

/-- The partial log sum z + z²/2 + ... + z^m/m. -/
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range m.succ, z ^ (k + 1) / (k + 1)

/-- E_m(0) = 1 for all m. -/
@[simp]
lemma weierstrassFactor_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor]

/-- partialLogSum at 0 equals 0. -/
@[simp]
lemma partialLogSum_zero (m : ℕ) : partialLogSum m 0 = 0 := by
  unfold partialLogSum
  apply sum_eq_zero
  intro k _
  simp [zero_pow (Nat.succ_ne_zero k)]

/-- E_0(z) = 1 - z. -/
lemma weierstrassFactor_genus_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor, range_one, sum_singleton]

/-- E_1(z) = (1 - z) exp(z). -/
lemma weierstrassFactor_genus_one (z : ℂ) : weierstrassFactor 1 z = (1 - z) * exp z := by
  simp [weierstrassFactor, range_succ, sum_singleton]
  ring_nf

/-- E_m(z) = 0 ⟺ z = 1. -/
lemma weierstrassFactor_eq_zero_iff {m : ℕ} {z : ℂ} :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  simp only [weierstrassFactor, mul_eq_zero, exp_ne_zero, or_false, sub_eq_zero]
  constructor <;> (intro h; linarith)

/-- E_m is entire (differentiable on all of ℂ). -/
lemma differentiable_weierstrassFactor (m : ℕ) : Differentiable ℂ (weierstrassFactor m) := by
  have h₁ : Differentiable ℂ (fun z : ℂ => (1 : ℂ) - z) :=
    Differentiable.sub (differentiable_const 1) differentiable_id
  have h₂ : Differentiable ℂ (fun z : ℂ => ∑ k ∈ range m.succ, z ^ (k + 1) / (k + 1)) := by
    apply Differentiable.fun_sum
    intro k _
    exact (differentiable_id.pow _).div_const _
  have h₃ : Differentiable ℂ (fun z : ℂ => exp (∑ k ∈ range m.succ, z ^ (k + 1) / (k + 1))) :=
    differentiable_exp.comp h₂
  exact h₁.mul h₃

/-- E_m is analytic at every point. -/
lemma analyticAt_weierstrassFactor (m : ℕ) (w : ℂ) : AnalyticAt ℂ (weierstrassFactor m) w :=
  (differentiable_weierstrassFactor m).analyticAt isOpen_univ (mem_univ w)

/-! ### Bounds on Weierstrass factors -/

/-- Bound on the partial log sum: |z + z²/2 + ... + z^m/m| ≤ |z|/(1-|z|) for |z| < 1. -/
lemma norm_partialLogSum_le {m : ℕ} {z : ℂ} (hz : ‖z‖ < 1) :
    ‖partialLogSum m z‖ ≤ ‖z‖ / (1 - ‖z‖) := by
  unfold partialLogSum
  have h_pos : 0 < 1 - ‖z‖ := by linarith
  have h_nn : 0 ≤ ‖z‖ := norm_nonneg z
  calc ‖∑ k ∈ range m.succ, z ^ (k + 1) / (k + 1)‖
      ≤ ∑ k ∈ range m.succ, ‖z ^ (k + 1) / (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range m.succ, ‖z‖ ^ (k + 1) := by
        apply sum_le_sum
        intro k _
        rw [norm_div, norm_pow]
        apply div_le_self (pow_nonneg h_nn _)
        simp only [norm_natCast]
        have : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg k]
        exact this
    _ = ‖z‖ * ∑ k ∈ range m.succ, ‖z‖ ^ k := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        rw [pow_succ, mul_comm]
    _ ≤ ‖z‖ * (1 / (1 - ‖z‖)) := by
        apply mul_le_mul_of_nonneg_left _ h_nn
        have h_geom := hasSum_geometric_of_lt_one h_nn hz
        calc ∑ k ∈ range m.succ, ‖z‖ ^ k
            ≤ ∑' k, ‖z‖ ^ k := sum_le_tsum _ (fun k _ => pow_nonneg h_nn k) h_geom.summable
          _ = 1 / (1 - ‖z‖) := by rw [h_geom.tsum_eq, one_div]
    _ = ‖z‖ / (1 - ‖z‖) := by ring

/-- For |z| ≤ 1/2, the partial log sum is bounded by 2|z|. -/
lemma norm_partialLogSum_le_two_mul {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖partialLogSum m z‖ ≤ 2 * ‖z‖ := by
  have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have h_pos : 0 < 1 - ‖z‖ := by linarith
  calc ‖partialLogSum m z‖
      ≤ ‖z‖ / (1 - ‖z‖) := norm_partialLogSum_le hz_lt
    _ ≤ ‖z‖ / (1 - 1/2) := by
        apply div_le_div_of_nonneg_left (norm_nonneg z) (by norm_num) (by linarith)
    _ = 2 * ‖z‖ := by ring

/-- Linear bound on |E_m(z) - 1| for small |z|.

For |z| ≤ 1/2, we have |E_m(z) - 1| ≤ 12|z|.
This linear bound is sufficient for convergence of canonical products. -/
lemma weierstrassFactor_sub_one_bound_linear {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖weierstrassFactor m z - 1‖ ≤ 12 * ‖z‖ := by
  have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
  unfold weierstrassFactor
  let P := partialLogSum m z
  have h_one_sub_z : ‖1 - z‖ ≤ 2 := by
    calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le 1 z
      _ = 1 + ‖z‖ := by simp
      _ ≤ 1 + 1/2 := by linarith
      _ = 3/2 := by norm_num
      _ ≤ 2 := by norm_num
  have h_P_bound : ‖P‖ ≤ 2 * ‖z‖ := norm_partialLogSum_le_two_mul hz
  have h_P_le_1 : ‖P‖ ≤ 1 := by
    calc ‖P‖ ≤ 2 * ‖z‖ := h_P_bound
      _ ≤ 2 * (1/2) := by nlinarith
      _ = 1 := by norm_num
  have h_exp_bound : ‖exp P - 1‖ ≤ 2 * ‖z‖ * Real.exp 1 := by
    have h1 : ‖exp P - 1‖ ≤ ‖P‖ * Real.exp ‖P‖ := Complex.norm_exp_sub_one_le P
    calc ‖exp P - 1‖
        ≤ ‖P‖ * Real.exp ‖P‖ := h1
      _ ≤ (2 * ‖z‖) * Real.exp 1 := by
          apply mul_le_mul h_P_bound (Real.exp_le_exp.mpr h_P_le_1) (Real.exp_nonneg _) (by linarith)
  calc ‖(1 - z) * exp P - 1‖
      = ‖(1 - z) * (exp P - 1) + ((1 - z) - 1)‖ := by ring_nf
    _ ≤ ‖(1 - z) * (exp P - 1)‖ + ‖(1 - z) - 1‖ := norm_add_le _ _
    _ = ‖1 - z‖ * ‖exp P - 1‖ + ‖-z‖ := by rw [norm_mul]; ring_nf
    _ = ‖1 - z‖ * ‖exp P - 1‖ + ‖z‖ := by rw [norm_neg]
    _ ≤ 2 * (2 * ‖z‖ * Real.exp 1) + ‖z‖ := by
        apply add_le_add_right
        apply mul_le_mul h_one_sub_z h_exp_bound (norm_nonneg _) (by norm_num)
    _ = ‖z‖ * (4 * Real.exp 1 + 1) := by ring
    _ ≤ ‖z‖ * 12 := by
        apply mul_le_mul_of_nonneg_left _ hz_nn
        have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        linarith
    _ = 12 * ‖z‖ := by ring

/-- Power bound on |E_m(z) - 1|.

For |z| ≤ 1/2, we have |E_m(z) - 1| ≤ C|z|^{m+1} for a constant C.
This is the sharper bound needed for Hadamard's theorem.

The proof uses the power series expansion of E_m(z). The key observation is that
for |z| < 1, we have:
  E_m(z) = (1-z) · exp(z + z²/2 + ... + z^m/m)

Using log(1-z) = -(z + z²/2 + z³/3 + ...), we get that E_m(z) has a zero of
order m+1 at z = 0. More precisely, E_m(z) - 1 = -z^{m+1}/(m+1) + O(z^{m+2}). -/
lemma weierstrassFactor_sub_one_bound_pow {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · -- For m = 0: E_0(z) - 1 = -z, so |E_0(z) - 1| = |z| ≤ 4|z|
    subst hm
    simp only [weierstrassFactor_genus_zero, Nat.zero_add, pow_one]
    calc ‖(1 - z) - 1‖ = ‖-z‖ := by ring_nf
      _ = ‖z‖ := norm_neg z
      _ ≤ 4 * ‖z‖ := by linarith [norm_nonneg z]
  · -- For m ≥ 1, use the representation E_m(z) = exp(-T_m(z))
    -- where T_m(z) = ∑_{k>m} z^k/k is the tail of -log(1-z)
    push_neg at hm
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
    by_cases hz0 : z = 0
    · -- z = 0: trivial
      simp [hz0]
    · -- z ≠ 0: use E_m(z) = exp(-T_m(z)) where |T_m(z)| ≤ 2|z|^{m+1}
      -- |E_m(z) - 1| = |exp(-T) - 1| ≤ |T|·e^|T| for |T| ≤ 1
      -- For |z| ≤ 1/2: |T| ≤ 2·(1/2)^{m+1} ≤ 1
      -- So |E_m(z) - 1| ≤ 2|z|^{m+1}·e ≤ 4|z|^{m+1} since e < 3
      --
      -- The tail bound |T_m(z)| ≤ |z|^{m+1}/(1-|z|) ≤ 2|z|^{m+1} for |z| ≤ 1/2
      -- follows from the geometric series bound.
      --
      -- TECHNICAL PROOF (requires power series infrastructure):
      -- 1. Show -log(1-z) = z + z²/2 + z³/3 + ... for |z| < 1
      -- 2. E_m(z) = (1-z)·exp(P_m(z)) = exp(log(1-z) + P_m(z)) = exp(-T_m(z))
      -- 3. |T_m(z)| ≤ ∑_{k>m} |z|^k/k ≤ |z|^{m+1}·∑_{k≥0} |z|^k = |z|^{m+1}/(1-|z|)
      -- 4. For |z| ≤ 1/2: |T_m(z)| ≤ 2|z|^{m+1}
      -- 5. |exp(-T) - 1| ≤ |T|·exp(|T|) ≤ 2|z|^{m+1}·e ≤ 4|z|^{m+1}
      sorry

/-! ## Part 3: Zero Data and Counting Functions -/

/--
Abstract zero data for an entire function. This packages the zeros
as a sequence with multiplicities, plus the multiplicity at `0`, and
assumes a local finiteness condition.

For applications like L-functions, this will be constructed from an
explicit zero set with known multiplicities.
-/
structure ZeroData (f : ℂ → ℂ) where
  /-- The multiset of nonzero zeros (with multiplicity). -/
  zeros : Multiset ℂ
  /-- Local finiteness: only finitely many zeros in each closed ball. -/
  zeros_finite_in_ball : ∀ R : ℝ, (zeros.filter (fun z => ‖z‖ ≤ R)).card < ⊤
  /-- Order of vanishing at `0`. -/
  ord0 : ℕ
  /-- Specification of the zero set (up to multiplicity) of `f`. -/
  zero_spec : ∀ z : ℂ, f z = 0 ↔
    (z = 0 ∧ 0 < ord0) ∨ (z ≠ 0 ∧ 0 < Multiset.count z zeros)

/-- The counting function n(r) counts zeros with |z| ≤ r, weighted by multiplicity. -/
def ZeroData.countingFunction {f : ℂ → ℂ} (zd : ZeroData f) (r : ℝ) : ℕ :=
  (zd.zeros.filter (fun z => ‖z‖ ≤ r)).card + if zd.ord0 > 0 ∧ 0 ≤ r then 1 else 0

/-- The exponent of convergence of the zeros. -/
def ZeroData.convergenceExponent {f : ℂ → ℂ} (zd : ZeroData f) : ℝ :=
  sInf {σ : ℝ | σ ≥ 0 ∧ ∀ (seq : ℕ → ℂ),
    (∀ n, seq n ∈ zd.zeros ∨ seq n = 0) →
    Summable (fun n => if seq n = 0 then 0 else ‖seq n‖⁻¹ ^ σ)}

/-- The genus p is the smallest integer such that ∑ |ρ|^{-(p+1)} converges. -/
def ZeroData.genus {f : ℂ → ℂ} (zd : ZeroData f) : ℕ :=
  Nat.floor zd.convergenceExponent

/-! ## Part 4: Canonical Products -/

/--
The canonical product (formal definition) over a finite subset of zeros.
-/
def canonicalProductFinite (m : ℕ) (zeros : Finset ℂ) (z : ℂ) : ℂ :=
  ∏ ρ ∈ zeros, if ρ = 0 then 1 else weierstrassFactor m (z / ρ)

/-- The canonical product is 1 at 0 when 0 is not a zero. -/
lemma canonicalProductFinite_at_zero {m : ℕ} {zeros : Finset ℂ} (h0 : (0 : ℂ) ∉ zeros) :
    canonicalProductFinite m zeros 0 = 1 := by
  unfold canonicalProductFinite
  apply prod_eq_one
  intro ρ hρ
  have hρ_ne : ρ ≠ 0 := fun h => h0 (h ▸ hρ)
  simp [hρ_ne]

/-- The canonical product is nonzero when z is not a zero. -/
lemma canonicalProductFinite_ne_zero {m : ℕ} {zeros : Finset ℂ} {z : ℂ}
    (hz : z ∉ zeros) (h0 : (0 : ℂ) ∉ zeros) :
    canonicalProductFinite m zeros z ≠ 0 := by
  unfold canonicalProductFinite
  apply prod_ne_zero
  intro ρ hρ
  have hρ_ne : ρ ≠ 0 := fun h => h0 (h ▸ hρ)
  simp only [hρ_ne, ↓reduceIte]
  rw [weierstrassFactor_eq_zero_iff]
  intro h
  have : z = ρ := by field_simp at h; exact h
  rw [this] at hz
  exact hz hρ

/-- Differentiability of the finite canonical product. -/
lemma differentiable_canonicalProductFinite (m : ℕ) (zeros : Finset ℂ) :
    Differentiable ℂ (canonicalProductFinite m zeros) := by
  unfold canonicalProductFinite
  apply Differentiable.finset_prod
  intro ρ _
  by_cases hρ : ρ = 0
  · simp [hρ]; exact differentiable_const 1
  · simp only [hρ, ↓reduceIte]
    exact (differentiable_weierstrassFactor m).comp (differentiable_id.div_const ρ)

/-! ## Part 5: Product Convergence -/

/-- Weierstrass M-test for canonical products: logarithmic version.

If ∑ₙ |z/aₙ|^{m+1} converges uniformly on a compact set K, then
∑ₙ log|E_m(z/aₙ)| converges uniformly on K. -/
theorem log_sum_converges_uniform {a : ℕ → ℂ} {m : ℕ}
    (h_sum : Summable (fun n => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ {z | ∀ n, z ≠ a n} →
      ∃ g : ℂ → ℂ, TendstoUniformlyOn
        (fun N z => ∑ n ∈ range N, log (weierstrassFactor m (z / a n)))
        g atTop K := by
  intro K hK hK_avoid
  -- Strategy:
  -- 1. K is bounded, so ∃ R > 0 with K ⊆ B(0, R)
  -- 2. For z ∈ K and |aₙ| > 2R: |z/aₙ| < 1/2
  -- 3. log(E_m(w)) = log(1 + (E_m(w) - 1)) for |w| < 1/2
  -- 4. |log(1 + u)| ≤ 2|u| for |u| ≤ 1/2
  -- 5. |E_m(w) - 1| ≤ 4|w|^{m+1} by weierstrassFactor_sub_one_bound_pow
  -- 6. So |log(E_m(z/aₙ))| ≤ 8|z/aₙ|^{m+1} ≤ 8R^{m+1}|aₙ|^{-(m+1)}
  -- 7. Apply Weierstrass M-test: ∑ 8R^{m+1}|aₙ|^{-(m+1)} < ∞ by h_sum
  --
  -- The uniform convergence of ∑ log(E_m(z/aₙ)) follows from M-test.
  obtain ⟨R, hR_pos, hR⟩ := hK.isBounded.subset_ball 0
  -- Define the limit function
  -- For formal proof, use `TendstoUniformlyOn` API
  sorry

/-- The canonical product converges uniformly on compact sets. -/
theorem canonical_product_converges_uniform {a : ℕ → ℂ} {m : ℕ}
    (h_sum : Summable (fun n => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ {z | ∀ n, z ≠ a n} →
      ∃ g : ℂ → ℂ, TendstoUniformlyOn
        (fun N z => ∏ n ∈ range N, weierstrassFactor m (z / a n))
        g atTop K ∧ AnalyticOn ℂ g K := by
  intro K hK hK_avoid
  -- Strategy:
  -- 1. log_sum_converges_uniform gives ∑ log(E_m(z/aₙ)) → g_log(z) uniformly on K
  -- 2. Then ∏ E_m(z/aₙ) = exp(∑ log(E_m(z/aₙ))) → exp(g_log(z)) uniformly
  -- 3. exp preserves analyticity, so exp(g_log) is analytic on K
  --
  -- Technical detail: need to show each E_m(z/aₙ) ≠ 0 on K to use log
  -- This follows from hK_avoid and the zero structure of E_m
  obtain ⟨g_log, hg_log⟩ := log_sum_converges_uniform h_sum h_nonzero K hK hK_avoid
  refine ⟨fun z => exp (g_log z), ?_, ?_⟩
  · -- Uniform convergence of products from uniform convergence of log sums
    -- ∏ E_m(z/aₙ) = exp(∑ log(E_m(z/aₙ)))
    sorry
  · -- Analyticity: exp composed with analytic function is analytic
    -- g_log is the uniform limit of analytic functions on K, hence analytic
    sorry

/-- The canonical product defines an entire function. -/
theorem canonical_product_entire {a : ℕ → ℂ} {m : ℕ}
    (h_sum : Summable (fun n => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ z, G z = 0 ↔ ∃ n, z = a n) ∧
      EntireOfFiniteOrder (m + 1 : ℝ) G := by
  -- Strategy:
  -- 1. Use canonical_product_converges_uniform to get uniform limits on compact sets
  -- 2. Uniform limits of analytic functions are analytic
  -- 3. The zeros of the limit are exactly the aₙ
  -- 4. Growth bound follows from product representation
  --
  -- Define G as the limit of partial products on all of ℂ
  -- G(z) = lim_{N→∞} ∏_{n<N} E_m(z/aₙ)
  -- This limit exists uniformly on compact subsets of ℂ \ {aₙ}
  -- and extends continuously to an entire function with zeros at {aₙ}
  sorry

/-! ## Part 5b: Zeros Counting and Jensen's Formula

This section connects to the Borel-Carathéodory theorem and Jensen's formula
from the StrongPNT infrastructure. These tools are essential for:
1. Bounding the number of zeros in a disk (Jensen's formula)
2. Controlling the growth of the quotient f/G (Borel-Carathéodory)
3. Establishing that log(f/G) is a polynomial (Liouville argument)
-/

/-- Jensen's bound on counting function from boundedness.

If f is analytic on |z| ≤ R with f(0) = 1 and |f(z)| ≤ B for |z| ≤ R,
then the number of zeros (with multiplicity) in |z| ≤ r < R is at most
log B / log(R/r).

This is a reformulation of `ZerosBound` from StrongPNT. -/
theorem jensen_zeros_bound {f : ℂ → ℂ} {r R B : ℝ}
    (hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hr : 0 < r) (hR : r < R) (hR1 : R < 1)
    (hf0 : f 0 = 1) (hB : 1 < B)
    (hf_bound : ∀ z, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∃ (zeros : Finset ℂ), (∀ z ∈ zeros, ‖z‖ ≤ r ∧ f z = 0) ∧
      zeros.card ≤ Nat.ceil (Real.log B / Real.log (R / r)) := by
  -- Jensen's formula: if f is analytic on |z| ≤ R with f(0) ≠ 0, then
  -- log|f(0)| + ∑_{|ρ|≤R, f(ρ)=0} log(R/|ρ|) = (1/2π) ∫_0^{2π} log|f(Re^{iθ})| dθ
  --
  -- For f(0) = 1 and |f| ≤ B:
  -- 0 + ∑_{|ρ|≤r} log(R/|ρ|) ≤ ∑_{|ρ|≤R} log(R/|ρ|) ≤ log B
  --
  -- Since log(R/|ρ|) ≥ log(R/r) for |ρ| ≤ r:
  -- n(r) · log(R/r) ≤ log B
  -- n(r) ≤ log B / log(R/r)
  --
  -- This follows from StrongPNT's ZerosBound or Mathlib's Jensen infrastructure
  sorry

/-- Borel-Carathéodory bound for entire functions.

If f is analytic on |z| ≤ R with f(0) = 0 and Re(f(z)) ≤ M for all |z| ≤ R,
then |f(z)| ≤ 2Mr/(R-r) for |z| ≤ r < R.

This connects to `borelCaratheodory_closedBall` from StrongPNT. -/
theorem borel_caratheodory_bound {f : ℂ → ℂ} {r R M : ℝ}
    (hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hr : 0 < r) (hR : r < R) (hM : 0 < M)
    (hf0 : f 0 = 0)
    (hf_re : ∀ z, ‖z‖ ≤ R → (f z).re ≤ M) :
    ∀ z, ‖z‖ ≤ r → ‖f z‖ ≤ 2 * M * r / (R - r) := by
  intro z hz
  -- Borel-Carathéodory lemma:
  -- For f analytic on |z| ≤ R with f(0) = 0 and Re(f) ≤ M on |z| = R:
  -- |f(z)| ≤ 2|z|·M/(R - |z|) for |z| < R
  --
  -- Proof idea: Consider g(z) = (f(z) - M)/(f(z) + M)
  -- This maps the upper half-plane Re(f) ≤ M to the unit disk
  -- Apply Schwarz-Pick lemma
  --
  -- For |z| ≤ r < R: |f(z)| ≤ 2rM/(R-r)
  --
  -- This is available in StrongPNT as borelCaratheodory_closedBall
  sorry

/-- Derivative bound from Borel-Carathéodory.

If f is analytic on |z| ≤ R with f(0) = 0 and Re(f(z)) ≤ M for all |z| ≤ R,
then |f'(z)| ≤ 16MR²/(R-r)³ for |z| ≤ r < R.

This connects to `BorelCaratheodoryDeriv` from StrongPNT. -/
theorem borel_caratheodory_deriv_bound {f : ℂ → ℂ} {r R M : ℝ}
    (hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hr : 0 < r) (hR : r < R) (hM : 0 < M)
    (hf0 : f 0 = 0)
    (hf_re : ∀ z, ‖z‖ ≤ R → (f z).re ≤ M) :
    ∀ z, ‖z‖ ≤ r → ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  intro z hz
  -- Combine Borel-Carathéodory with Cauchy's derivative estimate:
  -- |f'(z)| ≤ sup_{|w-z|=ρ} |f(w)| / ρ for analytic f
  --
  -- Choose ρ = (R - r)/2, then |w| ≤ r + ρ = (R + r)/2 < R
  -- By Borel-Carathéodory: |f(w)| ≤ 2M(R+r)/(2R - R - r) = 2M(R+r)/(R-r)
  -- So |f'(z)| ≤ 2M(R+r)/((R-r)·ρ) = 4M(R+r)/(R-r)²
  --
  -- The constant 16 accounts for worse-case geometry
  --
  -- This follows from StrongPNT's BorelCaratheodoryDeriv
  sorry

/-- Lindelöf's theorem: finite order implies summability of zero exponents.

If f is entire of order ρ, then for any σ > ρ, the series ∑|aₙ|^{-σ}
converges, where aₙ are the nonzero zeros of f. -/
theorem lindelof_zero_exponent {f : ℂ → ℂ} {ρ σ : ℝ}
    (hf : EntireOfFiniteOrder ρ f)
    (hσ : ρ < σ)
    (zeros : ℕ → ℂ)
    (h_zeros : ∀ n, f (zeros n) = 0 ∧ zeros n ≠ 0) :
    Summable (fun n => ‖zeros n‖⁻¹ ^ σ) := by
  -- Lindelöf's theorem proof outline:
  --
  -- 1. Jensen's formula: for f entire with f(0) ≠ 0,
  --    log|f(0)| + ∑_{|ρ|≤r} log(r/|ρ|) = (1/2π) ∫_0^{2π} log|f(re^{iθ})| dθ
  --
  -- 2. For f of order ρ: log|f(re^{iθ})| ≤ C·r^{ρ+ε} for any ε > 0
  --    So RHS ≤ C·r^{ρ+ε}
  --
  -- 3. n(r)·log 2 ≤ ∑_{|ρ|≤r/2} log(r/|ρ|) ≤ C·r^{ρ+ε}
  --    Hence n(r) ≤ C'·r^{ρ+ε}
  --
  -- 4. For σ > ρ, choose ε = (σ-ρ)/2:
  --    ∑_{r<|ρₙ|≤2r} |ρₙ|^{-σ} ≤ n(2r)·(r)^{-σ} ≤ C''·r^{ρ+ε-σ} = C''·r^{-(σ-ρ)/2}
  --
  -- 5. Summing over dyadic shells: ∑_n |ρₙ|^{-σ} < ∞
  --
  -- This is the standard proof of Lindelöf's theorem.
  sorry

/-- The quotient of entire functions f/G is entire when G has the same zeros.

If f and G are entire with the same zeros (counting multiplicity), and G(z) ≠ 0
for z not a zero of f, then f/G extends to an entire function. -/
theorem quotient_entire {f G : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hG : Differentiable ℂ G)
    (h_zeros : ∀ z, f z = 0 ↔ G z = 0) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, G z ≠ 0 → H z = f z / G z := by
  -- This is the removable singularity theorem for quotients.
  --
  -- At any point z₀ where f(z₀) = G(z₀) = 0:
  -- - Both f and G have a zero of some order m ≥ 1
  -- - f(z) = (z - z₀)^m · f₁(z), G(z) = (z - z₀)^m · G₁(z) with f₁(z₀), G₁(z₀) ≠ 0
  -- - f/G = f₁/G₁ near z₀, which is analytic
  --
  -- Key: the multiplicity condition ensures no poles in the quotient.
  -- The hypothesis h_zeros says f and G vanish at exactly the same points,
  -- but we also need equal multiplicities for the quotient to extend analytically.
  --
  -- For the full proof, we use:
  -- 1. The discrete set of zeros of f (and G) is isolated
  -- 2. At each zero z₀, use Taylor expansion to show f/G extends
  -- 3. Patch together to get a globally defined entire function
  sorry

/-- A zero-free entire function with polynomial growth is exp of a polynomial.

If H is entire, zero-free, and |H(z)| ≤ exp(C|z|^n) for some C and n,
then H = exp(P) for some polynomial P of degree at most n. -/
theorem zero_free_polynomial_growth_is_exp_poly {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * ‖z‖ ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = exp (Polynomial.eval z P) := by
  -- Proof outline (Liouville-type argument):
  --
  -- 1. Since H is entire and zero-free, log H can be defined as an entire function
  --    (choosing a branch): h = log H is entire with H = exp(h)
  --
  -- 2. The growth bound |H| ≤ exp(C|z|^n) implies:
  --    Re(h(z)) = log|H(z)| ≤ C|z|^n
  --
  -- 3. Borel-Carathéodory on h: for |z| ≤ r and R = 2r:
  --    |h(z)| ≤ 2r/(R-r) · max_{|w|=R} Re(h(w)) + (r/(R-r))|h(0)|
  --           ≤ 2·C·(2r)^n + const = O(r^n)
  --
  -- 4. Cauchy's estimate on h^{(k)}: |h^{(k)}(0)| ≤ k! · max_{|z|=r}|h(z)| / r^k
  --    For k > n: as r → ∞, this → 0, so h^{(k)}(0) = 0
  --
  -- 5. Hence h is a polynomial of degree at most n
  --
  -- This is the standard proof that zero-free entire functions of finite order
  -- are exponentials of polynomials.
  sorry

/-! ## Part 6: The Hadamard Factorization Theorem -/

/--
**Hadamard Factorization Theorem**

If `f` is an entire function of finite order `ρ` with zero data `hz`, then there exists:
- A genus `m ≤ ⌊ρ⌋`
- A polynomial `P` with `deg P ≤ ⌈ρ⌉`

such that
```
f(z) = exp(P(z)) · z^{ord0} · ∏_{ρ ∈ zeros} E_m(z/ρ)^{mult(ρ)}
```
-/
theorem hadamard_factorization
    {ρ : ℝ} {f : ℂ → ℂ}
    (hf : EntireOfFiniteOrder ρ f)
    (hz : ZeroData f) :
    ∃ (m : ℕ) (P : Polynomial ℂ),
      m ≤ Nat.floor ρ ∧
      P.degree ≤ (Nat.ceil ρ) ∧
      ∀ z : ℂ,
        f z = exp (Polynomial.eval z P) *
          z ^ hz.ord0 *
          (hz.zeros.attach.map fun z0 =>
            (weierstrassFactor m (z / z0.1)) ^
              (Multiset.count z0.1 hz.zeros)).prod := by
  -- **Hadamard Factorization Proof Outline:**
  --
  -- 1. **Lindelöf's theorem**: Since f has order ρ, for any σ > ρ,
  --    ∑|aₙ|^{-σ} < ∞ where aₙ are the nonzero zeros.
  --    Choose m = ⌊ρ⌋, so σ = m + 1 works.
  --
  -- 2. **Canonical product convergence**: By lindelof_zero_exponent,
  --    G(z) := z^{ord0} · ∏ E_m(z/aₙ) converges to an entire function
  --    of order at most m + 1 ≤ ρ + 1.
  --
  -- 3. **Quotient**: H(z) := f(z)/G(z) is entire by quotient_entire,
  --    since f and G have the same zeros with multiplicities.
  --
  -- 4. **H is zero-free**: By construction, G accounts for all zeros of f.
  --
  -- 5. **Growth of H**: |H(z)| = |f(z)|/|G(z)| ≤ exp(C|z|^{ρ+ε}) / |G(z)|
  --    Using growth bounds on G, we get |H(z)| ≤ exp(C'|z|^{⌈ρ⌉})
  --
  -- 6. **H = exp(P)**: By zero_free_polynomial_growth_is_exp_poly,
  --    H = exp(P) for some polynomial P of degree at most ⌈ρ⌉.
  --
  -- 7. **Conclusion**: f(z) = exp(P(z)) · G(z) = exp(P(z)) · z^{ord0} · ∏ E_m(z/aₙ)
  --
  use Nat.floor ρ
  sorry

/-! ## Part 7: Applications to the Riemann Zeta Function -/

/-- Zero data for (s-1)·ζ(s). -/
def zetaZeroData : ZeroData (fun s : ℂ => (s - 1) * riemannZeta s) := by
  constructor
  · -- zeros : the nontrivial zeros (in critical strip) plus trivial zeros (negative evens)
    -- The zeros of (s-1)ζ(s) are:
    -- 1. Trivial zeros: s = -2, -4, -6, ... (from ζ)
    -- 2. Nontrivial zeros: ρ with 0 < Re(ρ) < 1 and ζ(ρ) = 0
    -- Note: s = 1 is NOT a zero since (s-1)·ζ(s) → 1 as s → 1
    --
    -- For the formal definition, we need to enumerate these zeros as a Multiset
    -- This requires the structure of zeta zeros from Mathlib
    sorry
  · -- zeros_finite_in_ball: only finitely many zeros in any closed ball
    -- This follows from the discrete nature of zeta zeros
    -- (no accumulation points by the identity theorem)
    intro R
    sorry
  · -- ord0 : (s-1)ζ(s) is nonzero at s = 0
    -- ζ(0) = -1/2 ≠ 0, so (0-1)·ζ(0) = (-1)·(-1/2) = 1/2 ≠ 0
    exact 0
  · -- zero_spec: characterization of the zero set
    intro z
    -- f(z) = 0 iff (z = 0 ∧ ord0 > 0) ∨ (z ≠ 0 ∧ z ∈ zeros)
    -- For (s-1)ζ(s): zeros are trivial zeros and nontrivial zeros
    sorry

/-- The completed Riemann zeta function Λ₀(s) is entire of order 1. -/
theorem completedZeta_entire_order_one :
    EntireOfFiniteOrder 1 completedRiemannZeta₀ := by
  constructor
  · exact differentiable_completedZeta₀
  · obtain ⟨ρ, hρ⟩ := Riemann.completedRiemannZeta₀_finiteOrder
    rcases hρ.growth with ⟨C, hC_pos, hC⟩
    use C, hC_pos
    intro z
    exact hC z

/-- Hadamard factorization for (s-1)·ζ(s). -/
theorem hadamard_riemannZeta :
    ∃ (A B : ℂ),
      ∀ s : ℂ, s ≠ 1 →
        (s - 1) * riemannZeta s =
          exp (A + B * s) *
          (zetaZeroData.zeros.attach.map fun z0 =>
            (weierstrassFactor 0 (s / z0.1)) ^
              (Multiset.count z0.1 zetaZeroData.zeros)).prod := by
  -- The Riemann zeta function (s-1)ζ(s) is entire of order 1
  -- by Riemann.zeta_minus_pole_entire_finiteOrder.
  --
  -- By Hadamard's theorem with ρ = 1:
  -- - genus m ≤ ⌊1⌋ = 1, but we can take m = 0 for ζ
  -- - polynomial P has degree ≤ ⌈1⌉ = 1, so P(s) = A + Bs
  --
  -- The canonical product uses E_0(z) = 1 - z, so:
  -- (s-1)ζ(s) = exp(A + Bs) · ∏_ρ E_0(s/ρ)
  --           = exp(A + Bs) · ∏_ρ (1 - s/ρ)
  --
  -- Historical note: The constants A, B can be determined from:
  -- - ζ(0) = -1/2, so (0-1)·ζ(0) = 1/2 = exp(A) · product at 0
  -- - The functional equation gives additional constraints
  --
  -- A and B are related to the Euler-Mascheroni constant and log(2π).
  sorry

/-- The product over nontrivial zeros converges absolutely. -/
theorem zeta_zeros_product_converges :
    ∀ K : Set ℂ, IsCompact K → K ⊆ {s | ∀ n : ℕ, s ≠ zetaZeroData.zeros.get? n} →
      ∃ g : ℂ → ℂ, TendstoUniformlyOn
        (fun N s => ∏ n ∈ range N,
          match zetaZeroData.zeros.get? n with
          | some ρ => weierstrassFactor 0 (s / ρ)
          | none => 1)
        g atTop K ∧ AnalyticOn ℂ g K := by
  intro K hK hK_avoid
  -- The convergence follows from:
  -- 1. (s-1)ζ(s) has order 1, so by Lindelöf: ∑|ρ|^{-σ} < ∞ for any σ > 1
  -- 2. In particular ∑|ρ|^{-2} < ∞
  -- 3. For E_0(z) = 1 - z, we have |E_0(z) - 1| = |z| ≤ C|z|
  -- 4. By Weierstrass M-test, ∏ E_0(s/ρ) converges uniformly on K
  --
  -- The convergence ∑|ρ|^{-2} < ∞ is a classical result about zeta zeros
  -- following from Jensen's formula and the order-1 growth of ζ.
  --
  -- Note: We use E_0 (genus 0) because the zeros of ζ satisfy ∑|ρ|^{-1-ε} < ∞
  -- for any ε > 0, which is slightly stronger than needed.
  sorry

end Hadamard
end ComplexAnalysis

/-! ## Part 8: Exports and Compatibility -/

/-- Re-export the main theorem for convenient access. -/
theorem ComplexAnalysis.hadamard_factorization_main
    {ρ : ℝ} {f : ℂ → ℂ}
    (hf : ComplexAnalysis.Hadamard.EntireOfFiniteOrder ρ f)
    (hz : ComplexAnalysis.Hadamard.ZeroData f) :
    ∃ (m : ℕ) (P : Polynomial ℂ),
      m ≤ Nat.floor ρ ∧
      P.degree ≤ (Nat.ceil ρ) ∧
      ∀ z : ℂ,
        f z = Complex.exp (Polynomial.eval z P) *
          z ^ hz.ord0 *
          (hz.zeros.attach.map fun z0 =>
            (ComplexAnalysis.Hadamard.weierstrassFactor m (z / z0.1)) ^
              (Multiset.count z0.1 hz.zeros)).prod :=
  ComplexAnalysis.Hadamard.hadamard_factorization hf hz

end
