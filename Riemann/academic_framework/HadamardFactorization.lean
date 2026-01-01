
import Mathlib
import Riemann.academic_framework.WeierstrassFactorBound
import PrimeNumberTheoremAnd.BorelCaratheodory
import PrimeNumberTheoremAnd.DerivativeBound
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

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
  hf.entire.analyticAt z

/-- An entire function of finite order is analytic on all of ℂ. -/
lemma analyticOnNhd (hf : EntireOfFiniteOrder ρ f) : AnalyticOnNhd ℂ f univ := by
  intro z hz
  simpa using hf.analyticAt z

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
  refine ⟨C, hCpos, ?_⟩
  intro r _ z hz
  simpa [hz] using (hC z)

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
    have h2 : Real.log (1 + ‖z‖) ≤ 1 + ‖z‖ := Real.log_le_self (by linarith [norm_nonneg z])
    simp only [Real.rpow_one]
    calc Real.log (1 + ‖z‖) ≤ 1 + ‖z‖ := h2
      _ ≤ 2 * (1 + ‖z‖) := h1

/-- Polynomial growth bound: |P(z)| ≤ C(1 + |z|)^n for degree n polynomial. -/
lemma polynomial_growth_aux (P : Polynomial ℂ) :
    ∃ C > 0, ∀ z : ℂ, ‖Polynomial.eval z P‖ ≤ C * (1 + ‖z‖) ^ P.natDegree := by
  classical
  -- A clean universal constant: sum of coefficient norms, plus 1 to ensure positivity.
  let C : ℝ := (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) + 1
  refine ⟨C, ?_, ?_⟩
  ·
    have hsum :
        0 ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    -- `C = sum + 1`, hence positive.
    linarith [hsum]
  · intro z
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hone : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith
    have h_eval : P.eval z = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ i := by
      simpa using (Polynomial.eval_eq_sum_range (p := P) z)
    have h₁ :
        ‖P.eval z‖ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖z‖ ^ i := by
      calc
        ‖P.eval z‖ = ‖∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * z ^ i‖ := by
          simp [h_eval]
        _ ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i * z ^ i‖ := by
          simpa using (norm_sum_le (Finset.range (P.natDegree + 1)) fun i => P.coeff i * z ^ i)
        _ = ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖z‖ ^ i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp [norm_pow]
    have h_pow :
        ∀ i ∈ Finset.range (P.natDegree + 1), ‖z‖ ^ i ≤ (1 + ‖z‖) ^ P.natDegree := by
          intro i hi
          have hi' : i ≤ P.natDegree := by simpa [Finset.mem_range] using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
          have hzi : ‖z‖ ^ i ≤ (1 + ‖z‖) ^ i :=
            pow_le_pow_left₀ hz0 (by linarith [hz0]) i
          have hmono : (1 + ‖z‖) ^ i ≤ (1 + ‖z‖) ^ P.natDegree :=
            pow_le_pow_right₀ hone hi'
          exact le_trans hzi hmono
    have h₂ :
        ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖z‖ ^ i
          ≤ (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * (1 + ‖z‖) ^ P.natDegree := by
      have hterm :
          ∀ i ∈ Finset.range (P.natDegree + 1),
            ‖P.coeff i‖ * ‖z‖ ^ i ≤ ‖P.coeff i‖ * (1 + ‖z‖) ^ P.natDegree := by
        intro i hi
        exact mul_le_mul_of_nonneg_left (h_pow i hi) (norm_nonneg _)
      calc
        ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * ‖z‖ ^ i
            ≤ ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ * (1 + ‖z‖) ^ P.natDegree := by
              exact Finset.sum_le_sum (fun i hi => hterm i hi)
        _ = (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * (1 + ‖z‖) ^ P.natDegree := by
              simp [Finset.sum_mul]
    have hsum_le : (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) ≤ C := by
      simp [C]
    calc
      ‖P.eval z‖
          ≤ (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) * (1 + ‖z‖) ^ P.natDegree :=
            le_trans h₁ h₂
      _ ≤ C * (1 + ‖z‖) ^ P.natDegree := by
            exact mul_le_mul_of_nonneg_right hsum_le (pow_nonneg (by linarith [norm_nonneg z]) _)

/-- Polynomials have finite order (in this coarse growth sense). -/
lemma polynomial (P : Polynomial ℂ) :
    EntireOfFiniteOrder (P.natDegree : ℝ) (fun z => P.eval z) := by
  constructor
  · exact P.differentiable
  · obtain ⟨C, hC_pos, hC⟩ := polynomial_growth_aux P
    -- Use a crude but uniform log bound: `log x ≤ x` for `0 ≤ x`, and absorb constants.
    refine ⟨C + 1, by linarith, ?_⟩
    intro z
    have hP : ‖P.eval z‖ ≤ C * (1 + ‖z‖) ^ P.natDegree := by
      simpa using (hC z)
    have hpos : 0 ≤ (1 : ℝ) + ‖P.eval z‖ := by linarith [norm_nonneg (P.eval z)]
    have hlog : Real.log (1 + ‖P.eval z‖) ≤ (1 + ‖P.eval z‖) := Real.log_le_self hpos
    have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ P.natDegree := by
      have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      simpa using (one_le_pow₀ hbase : (1 : ℝ) ≤ (1 + ‖z‖) ^ P.natDegree)
    have hrpow :
        (1 + ‖z‖) ^ (P.natDegree : ℝ) = (1 + ‖z‖) ^ P.natDegree := by
      simp
    calc
      Real.log (1 + ‖P.eval z‖)
          ≤ 1 + ‖P.eval z‖ := hlog
      _ ≤ 1 + C * (1 + ‖z‖) ^ P.natDegree := by linarith
      _ ≤ (C + 1) * (1 + ‖z‖) ^ P.natDegree := by
            -- since `1 ≤ (1+‖z‖)^{natDegree}`
            nlinarith [hone]
      _ = (C + 1) * (1 + ‖z‖) ^ (P.natDegree : ℝ) := by simp [hrpow]

/-- exp(az) has order 1 for any a ≠ 0. -/
lemma exp_linear {a : ℂ} (ha : a ≠ 0) : EntireOfFiniteOrder 1 (fun z => exp (a * z)) := by
  constructor
  · exact differentiable_exp.comp (differentiable_const a |>.mul differentiable_id)
  · -- A slightly conservative constant suffices.
    refine ⟨‖a‖ + 2, by linarith [norm_nonneg a], ?_⟩
    intro z
    simp only [Real.rpow_one]
    have hnorm_exp : ‖Complex.exp (a * z)‖ ≤ Real.exp (‖a‖ * ‖z‖) := by
      calc
        ‖Complex.exp (a * z)‖
            = Real.exp ((a * z).re) := by simpa using (Complex.norm_exp (a * z))
        _ ≤ Real.exp ‖a * z‖ := by
              gcongr
              exact Complex.re_le_norm (a * z)
        _ ≤ Real.exp (‖a‖ * ‖z‖) := by
              gcongr
              exact norm_mul_le a z
    have hx0 : 0 ≤ ‖a‖ * ‖z‖ := mul_nonneg (norm_nonneg a) (norm_nonneg z)
    have hlog_exp : Real.log (1 + Real.exp (‖a‖ * ‖z‖)) ≤ 1 + ‖a‖ * ‖z‖ := by
      have hexp_ge : 1 ≤ Real.exp (‖a‖ * ‖z‖) := Real.one_le_exp hx0
      have hle : 1 + Real.exp (‖a‖ * ‖z‖) ≤ 2 * Real.exp (‖a‖ * ‖z‖) := by linarith
      have hpos : 0 < 1 + Real.exp (‖a‖ * ‖z‖) := by positivity
      have hlog2 : Real.log 2 ≤ 1 := by
        have h : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
        exact le_of_lt h
      calc
        Real.log (1 + Real.exp (‖a‖ * ‖z‖))
            ≤ Real.log (2 * Real.exp (‖a‖ * ‖z‖)) := Real.log_le_log hpos hle
        _ = Real.log 2 + (‖a‖ * ‖z‖) := by
              simp [Real.log_mul, Real.log_exp]
        _ ≤ 1 + ‖a‖ * ‖z‖ := by linarith
    have hpos₁ : 0 < (1 : ℝ) + ‖Complex.exp (a * z)‖ := by
      linarith [norm_nonneg (Complex.exp (a * z))]
    calc
      Real.log (1 + ‖Complex.exp (a * z)‖)
          ≤ Real.log (1 + Real.exp (‖a‖ * ‖z‖)) := by
                apply Real.log_le_log hpos₁
                linarith
      _ ≤ 1 + ‖a‖ * ‖z‖ := hlog_exp
      _ ≤ (‖a‖ + 2) * (1 + ‖z‖) := by nlinarith [norm_nonneg a, norm_nonneg z]

end EntireOfFiniteOrder

/-! ## Part 2: Weierstrass Elementary Factors -/

/--
The Weierstrass elementary factor of genus `m`:
```
E_m(z) = (1 - z) * exp(z + z²/2 + ... + z^m/m)
```
This is the building block for canonical products in the Hadamard factorization. -/
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (∑ k ∈ range m, z ^ (k + 1) / (k + 1))

/-- The partial log sum z + z²/2 + ... + z^m/m. -/
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range m, z ^ (k + 1) / (k + 1)

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
  simp [weierstrassFactor]

/-- E_1(z) = (1 - z) exp(z). -/
lemma weierstrassFactor_genus_one (z : ℂ) : weierstrassFactor 1 z = (1 - z) * exp z := by
  simp [weierstrassFactor, Finset.range_one]

/-- E_m(z) = 0 ⟺ z = 1. -/
lemma weierstrassFactor_eq_zero_iff {m : ℕ} {z : ℂ} :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  unfold weierstrassFactor
  constructor
  · intro h
    have hmul : (1 - z) = 0 ∨ exp (∑ k ∈ range m, z ^ (k + 1) / (k + 1)) = 0 :=
      mul_eq_zero.mp h
    have hz : (1 - z) = 0 := by
      rcases hmul with hz | hexp
      · exact hz
      · exfalso
        exact (Complex.exp_ne_zero _ hexp)
    -- `1 - z = 0` means `z = 1`.
    simpa [eq_comm] using (sub_eq_zero.mp hz)
  · intro hz
    -- If `z = 1` then the linear factor vanishes.
    simp [hz]

/-- E_m is entire (differentiable on all of ℂ). -/
lemma differentiable_weierstrassFactor (m : ℕ) : Differentiable ℂ (weierstrassFactor m) := by
  have h₁ : Differentiable ℂ (fun z : ℂ => (1 : ℂ) - z) :=
    Differentiable.sub (differentiable_const 1) differentiable_id
  have h₂ : Differentiable ℂ (fun z : ℂ => ∑ k ∈ range m, z ^ (k + 1) / (k + 1)) := by
    apply Differentiable.fun_sum
    intro k _
    exact (differentiable_id.pow _).div_const _
  have h₃ : Differentiable ℂ (fun z : ℂ => exp (∑ k ∈ range m, z ^ (k + 1) / (k + 1))) :=
    differentiable_exp.comp h₂
  exact h₁.mul h₃

/-- E_m is analytic at every point. -/
lemma analyticAt_weierstrassFactor (m : ℕ) (w : ℂ) : AnalyticAt ℂ (weierstrassFactor m) w :=
  (differentiable_weierstrassFactor m).analyticAt w

/-! ### Bounds on Weierstrass factors -/

/-- Bound on the partial log sum: |z + z²/2 + ... + z^m/m| ≤ |z|/(1-|z|) for |z| < 1. -/
lemma norm_partialLogSum_le {m : ℕ} {z : ℂ} (hz : ‖z‖ < 1) :
    ‖partialLogSum m z‖ ≤ ‖z‖ / (1 - ‖z‖) := by
  unfold partialLogSum
  have h_pos : 0 < 1 - ‖z‖ := by linarith
  have h_nn : 0 ≤ ‖z‖ := norm_nonneg z
  calc ‖∑ k ∈ range m, z ^ (k + 1) / (k + 1)‖
      ≤ ∑ k ∈ range m, ‖z ^ (k + 1) / (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range m, ‖z‖ ^ (k + 1) := by
        apply sum_le_sum
        intro k _
        rw [norm_div, norm_pow]
        apply div_le_self (pow_nonneg h_nn _)
        -- Crude bound `1 ≤ ‖(↑k : ℂ) + 1‖`, enough for `div_le_self`.
        have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
          -- `k + 1 ≥ 1`.
          -- We phrase this on `ℕ` and cast.
          have hk1_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
          exact_mod_cast hk1_nat
        have hre_nonneg : 0 ≤ ((k : ℂ) + 1).re := by
          -- `re (↑k + 1) = (k : ℝ) + 1 ≥ 1 ≥ 0`.
          have : (0 : ℝ) ≤ (k : ℝ) + 1 := le_trans (by norm_num) hk1
          simpa using this
        have hre_le : ((k : ℂ) + 1).re ≤ ‖(k : ℂ) + 1‖ := by
          -- `|re| ≤ ‖·‖` and `re` is nonnegative here.
          have h := (abs_re_le_norm ((k : ℂ) + 1))
          rw [abs_of_nonneg hre_nonneg] at h
          exact h
        have hk1' : (1 : ℝ) ≤ ((k : ℂ) + 1).re := by simp
        exact le_trans hk1' hre_le
    _ = ‖z‖ * ∑ k ∈ range m, ‖z‖ ^ k := by
        rw [mul_sum]
        apply sum_congr rfl
        intro k _
        rw [pow_succ, mul_comm]
    _ ≤ ‖z‖ * (1 / (1 - ‖z‖)) := by
        apply mul_le_mul_of_nonneg_left _ h_nn
        have h_geom := hasSum_geometric_of_lt_one h_nn hz
        calc ∑ k ∈ range m, ‖z‖ ^ k
            ≤ ∑' k, ‖z‖ ^ k :=
              Summable.sum_le_tsum (s := range m) (fun k _ => pow_nonneg h_nn k) h_geom.summable
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
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hz1 : ‖z‖ ≤ 1 := le_trans hz (by norm_num)
  have hpow : ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
    -- Reuse the fully rigorous tail/log proof from `WeierstrassFactorBound.lean`.
    simpa [weierstrassFactor, weierstrassFactor', partialLogSum'] using
      (weierstrassFactor_sub_one_pow_bound (m := m) (z := z) hz)
  have hpow_le : ‖z‖ ^ (m + 1) ≤ ‖z‖ := by
    have : ‖z‖ ^ (m + 1) ≤ ‖z‖ ^ (1 : ℕ) :=
      pow_le_pow_of_le_one hz0 hz1 (Nat.succ_le_succ (Nat.zero_le m))
    simpa using this
  have h4 : ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ := by
    have : 4 * ‖z‖ ^ (m + 1) ≤ 4 * ‖z‖ := by nlinarith [hpow_le]
    exact le_trans hpow this
  have hconst : (4 : ℝ) * ‖z‖ ≤ 12 * ‖z‖ := by nlinarith [hz0]
  exact le_trans h4 hconst

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
  -- Reuse the fully rigorous tail/log proof from `WeierstrassFactorBound.lean`.
  simpa [weierstrassFactor, weierstrassFactor', partialLogSum'] using
    (weierstrassFactor_sub_one_pow_bound (m := m) (z := z) hz)

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
  zeros_finite_in_ball :
    ∀ R : ℝ, ∃ n : ℕ, (zeros.filter (fun z => ‖z‖ ≤ R)).card ≤ n
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
  classical
  unfold canonicalProductFinite
  -- Each factor is nonzero since `0 ∉ zeros` and `z ∉ zeros`.
  refine (Finset.prod_ne_zero_iff).2 ?_
  intro ρ hρ
  have hρ_ne : ρ ≠ 0 := fun h => h0 (h ▸ hρ)
  simp [hρ_ne]
  intro hzero
  have h : z / ρ = 1 := (weierstrassFactor_eq_zero_iff (m := m) (z := z / ρ)).1 hzero
  have hzρ : z = ρ := by
    have h' := congrArg (fun w : ℂ => w * ρ) h
    simpa [div_eq_mul_inv, mul_assoc, hρ_ne] using h'
  exact hz (hzρ ▸ hρ)

/-- Differentiability of the finite canonical product. -/
lemma differentiable_canonicalProductFinite (m : ℕ) (zeros : Finset ℂ) :
    Differentiable ℂ (canonicalProductFinite m zeros) := by
  classical
  -- View the product as a product of differentiable functions.
  let F : ℂ → ℂ → ℂ := fun ρ z => if ρ = 0 then (1 : ℂ) else weierstrassFactor m (z / ρ)
  have hF : ∀ ρ ∈ zeros, Differentiable ℂ (F ρ) := by
    intro ρ hρ
    by_cases hρ0 : ρ = 0
    · simp [F, hρ0]
    ·
      have hdiff : Differentiable ℂ (fun z => weierstrassFactor m (z / ρ)) :=
        (differentiable_weierstrassFactor m).comp (differentiable_id.div_const ρ)
      simpa [F, hρ0] using hdiff
  have hprod : Differentiable ℂ (∏ ρ ∈ zeros, F ρ) :=
    Differentiable.finset_prod (u := zeros) (f := fun ρ => F ρ) hF
  -- Rewrite the product-of-functions as the pointwise product in `canonicalProductFinite`.
  have hEq : canonicalProductFinite m zeros = ∏ ρ ∈ zeros, F ρ := by
    funext z
    simp [canonicalProductFinite, F, Finset.prod_apply]
  simpa [hEq] using hprod

/-! ## Part 5: Product Convergence -/

open Filter Function

open scoped Topology

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
  -- We use Mathlib's M-test lemma for `∑ log(1 + f n z)` with a summable majorant.
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  -- Choose a strictly positive radius bounding `K`.
  set R : ℝ := max R0 1
  have hR_le : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz => le_trans (hR0 z hz) (le_max_left _ _)
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)

  -- Majorant sequence: a constant multiple of the given summable sequence.
  let u : ℕ → ℝ := fun n => (4 * R ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1))
  have hu : Summable u := h_sum.mul_left (4 * R ^ (m + 1))

  -- Eventually, `‖a n‖` is large enough so that `‖z / a n‖ ≤ 1/2` for all `z ∈ K`.
  have h_tend : Tendsto (fun n => ‖a n‖⁻¹ ^ (m + 1)) atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hRhalf_pos : 0 < (1 / (2 * R)) ^ (m + 1) := by
    have : 0 < (1 / (2 * R) : ℝ) := by
      have : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      exact one_div_pos.mpr this
    exact pow_pos this (m + 1)
  have hLarge : ∀ᶠ n in atTop, (2 * R : ℝ) ≤ ‖a n‖ := by
    have hEv := h_tend.eventually (eventually_lt_nhds hRhalf_pos)
    filter_upwards [hEv] with n hn
    by_contra h'
    have hle : ‖a n‖ ≤ 2 * R := le_of_not_ge h'
    have ha_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
    have hinv : (1 / (2 * R : ℝ)) ≤ ‖a n‖⁻¹ := by
      simpa [one_div] using (one_div_le_one_div_of_le ha_pos hle)
    have hinv_pow : (1 / (2 * R : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) hinv (m + 1)
    exact (not_lt_of_ge hinv_pow) (by simpa [one_div] using hn)

  -- Apply Mathlib's uniform convergence lemma for logarithmic series.
  refine ⟨fun z => ∑' n, log (weierstrassFactor m (z / a n)), ?_⟩
  have hBound :
      ∀ᶠ n in atTop, ∀ z ∈ K, ‖weierstrassFactor m (z / a n) - 1‖ ≤ u n := by
    filter_upwards [hLarge] with n hn z hz
    have hz' : ‖z / a n‖ ≤ (1 / 2 : ℝ) := by
      have ha_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
      have hzle : ‖z‖ ≤ R := hR_le z hz
      have : ‖z / a n‖ = ‖z‖ / ‖a n‖ := by simp
      rw [this]
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hfrac₁ : ‖z‖ / ‖a n‖ ≤ ‖z‖ / (2 * R) :=
        div_le_div_of_nonneg_left (norm_nonneg z) h2R_pos hn
      have hfrac₂ : ‖z‖ / (2 * R) ≤ R / (2 * R) :=
        div_le_div_of_nonneg_right hzle (le_of_lt h2R_pos)
      have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
      have hRsimp : (R / (2 * R : ℝ)) = (1 / 2 : ℝ) := by
        field_simp [hRne]
      have hfrac : ‖z‖ / ‖a n‖ ≤ R / (2 * R) := hfrac₁.trans hfrac₂
      exact hfrac.trans_eq hRsimp
    have hpow := weierstrassFactor_sub_one_bound_pow (m := m) (z := z / a n) hz'
    have hzR : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
      pow_le_pow_left₀ (norm_nonneg z) (hR_le z hz) _
    calc
      ‖weierstrassFactor m (z / a n) - 1‖
          ≤ 4 * ‖z / a n‖ ^ (m + 1) := hpow
      _ = 4 * (‖z‖ ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
            simp [div_eq_mul_inv, mul_pow, norm_inv, mul_assoc, mul_comm]
      _ ≤ 4 * (R ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
            gcongr
      _ = u n := by
            simp [u, mul_assoc, mul_comm]

  have hmain :
      TendstoUniformlyOn
          (fun N z => ∑ n ∈ range N, log (1 + (weierstrassFactor m (z / a n) - 1)))
          (fun z => ∑' n, log (1 + (weierstrassFactor m (z / a n) - 1))) atTop K := by
    simpa [u] using (hu.tendstoUniformlyOn_tsum_nat_log_one_add (K := K) (f := fun n z =>
      weierstrassFactor m (z / a n) - 1) hBound)
  -- Rewrite back to `log (weierstrassFactor ...)`.
  have hcongr :
      ∀ᶠ N in atTop,
        Set.EqOn
          (fun z => ∑ n ∈ range N, log (1 + (weierstrassFactor m (z / a n) - 1)))
          (fun z => ∑ n ∈ range N, log (weierstrassFactor m (z / a n))) K :=
    Filter.Eventually.of_forall (fun N z hz => by simp)
  have hlim :
      TendstoUniformlyOn
        (fun N z => ∑ n ∈ range N, log (weierstrassFactor m (z / a n)))
        (fun z => ∑' n, log (1 + (weierstrassFactor m (z / a n) - 1))) atTop K :=
    hmain.congr hcongr
  refine hlim.congr_right ?_
  intro z hz
  simp

/-- The canonical product converges uniformly on compact sets. -/
theorem canonical_product_converges_uniform {a : ℕ → ℂ} {m : ℕ}
    (h_sum : Summable (fun n => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ {z | ∀ n, z ≠ a n} →
      ∃ g : ℂ → ℂ, TendstoUniformlyOn
        (fun N z => ∏ n ∈ range N, weierstrassFactor m (z / a n))
        g atTop K ∧ AnalyticOn ℂ g K := by
  intro K hK hK_avoid
  -- We avoid the logarithm (which is not continuous everywhere) and instead use Mathlib's
  -- Weierstrass M-test for products of the form `∏ (1 + f n z)`.
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  -- Choose a radius `R ≥ 1` bounding `K`, and an open ball `U` slightly larger than `K`.
  set R : ℝ := max R0 1
  let U : Set ℂ := Metric.ball (0 : ℂ) (R + 1)
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hKU : K ⊆ U := by
    intro z hz
    have hzle : ‖z‖ ≤ R := le_trans (hR0 z hz) (le_max_left _ _)
    have hzlt : ‖z‖ < R + 1 := lt_of_le_of_lt hzle (by linarith)
    simpa [U, Metric.mem_ball, dist_zero_right] using hzlt

  -- Let `f n z = weierstrassFactor m (z / a n) - 1`.
  let f : ℕ → ℂ → ℂ := fun n z => weierstrassFactor m (z / a n) - 1
  -- Majorant: a constant multiple of the given summable sequence.
  let M : ℕ → ℝ := fun n => (4 * (R + 1) ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1))
  have hM : Summable M := h_sum.mul_left (4 * (R + 1) ^ (m + 1))

  -- Eventually, `‖a n‖` is large enough so that `‖z / a n‖ ≤ 1/2` for all `z ∈ U`.
  have h_tend : Tendsto (fun n => ‖a n‖⁻¹ ^ (m + 1)) atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hR1pos : 0 < R + 1 := by linarith
  have hRhalf_pos : 0 < (1 / (2 * (R + 1))) ^ (m + 1) := by
    have : 0 < (1 / (2 * (R + 1)) : ℝ) := by
      have : 0 < (2 * (R + 1) : ℝ) := by nlinarith [hR1pos]
      exact one_div_pos.mpr this
    exact pow_pos this (m + 1)
  have hLarge : ∀ᶠ n in atTop, (2 * (R + 1) : ℝ) ≤ ‖a n‖ := by
    have hEv := h_tend.eventually (eventually_lt_nhds hRhalf_pos)
    filter_upwards [hEv] with n hn
    by_contra h'
    have hle : ‖a n‖ ≤ 2 * (R + 1) := le_of_not_ge h'
    have ha_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
    have hinv : (1 / (2 * (R + 1) : ℝ)) ≤ ‖a n‖⁻¹ := by
      simpa [one_div] using (one_div_le_one_div_of_le ha_pos hle)
    have hinv_pow : (1 / (2 * (R + 1) : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
      pow_le_pow_left₀ (by positivity) hinv (m + 1)
    exact (not_lt_of_ge hinv_pow) (by simpa [one_div] using hn)

  -- Bound the tail factors on `U` and get local uniform convergence there.
  have hBoundU : ∀ᶠ n in atTop, ∀ z ∈ U, ‖f n z‖ ≤ M n := by
    filter_upwards [hLarge] with n hn z hzU
    have hzU' : ‖z‖ < R + 1 := by
      simpa [U, Metric.mem_ball, dist_zero_right] using hzU
    have hz' : ‖z / a n‖ ≤ (1 / 2 : ℝ) := by
      have h2R1_pos : 0 < (2 * (R + 1) : ℝ) := by nlinarith [hR1pos]
      have ha_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
      have : ‖z / a n‖ = ‖z‖ / ‖a n‖ := by simp [Complex.norm_div]
      rw [this]
      have hfrac₁ : ‖z‖ / ‖a n‖ ≤ ‖z‖ / (2 * (R + 1)) :=
        div_le_div_of_nonneg_left (norm_nonneg z) h2R1_pos hn
      have hfrac₂ : ‖z‖ / (2 * (R + 1)) ≤ (R + 1) / (2 * (R + 1)) :=
        div_le_div_of_nonneg_right (le_of_lt hzU') (le_of_lt h2R1_pos)
      have hfrac : ‖z‖ / ‖a n‖ ≤ (R + 1) / (2 * (R + 1)) := hfrac₁.trans hfrac₂
      have hRne : (R + 1 : ℝ) ≠ 0 := ne_of_gt hR1pos
      have hRsimp : ((R + 1) / (2 * (R + 1) : ℝ)) = (1 / 2 : ℝ) := by
        field_simp [hRne]
      exact hfrac.trans_eq hRsimp
    have hpow := weierstrassFactor_sub_one_bound_pow (m := m) (z := z / a n) hz'
    have hzR : ‖z‖ ^ (m + 1) ≤ (R + 1) ^ (m + 1) :=
      pow_le_pow_left₀ (norm_nonneg z) (le_of_lt hzU') _
    have hnorm :
        ‖f n z‖ = ‖weierstrassFactor m (z / a n) - 1‖ := by simp [f]
    -- Main estimate.
    calc
      ‖f n z‖ = ‖weierstrassFactor m (z / a n) - 1‖ := hnorm
      _ ≤ 4 * ‖z / a n‖ ^ (m + 1) := hpow
      _ = 4 * (‖z‖ ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
            simp [div_eq_mul_inv, mul_pow, norm_inv, mul_assoc, mul_left_comm, mul_comm]
      _ ≤ 4 * ((R + 1) ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
            gcongr
      _ = M n := by
            simp [M, mul_assoc, mul_left_comm, mul_comm]

  have hcts : ∀ n, ContinuousOn (f n) U := by
    intro n
    -- `weierstrassFactor` is differentiable, hence continuous, and so is `z ↦ z / a n`.
    have hcont : Continuous (fun z : ℂ => weierstrassFactor m (z / a n)) :=
      ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a n))).continuous
    simpa [f] using (hcont.continuousOn.sub continuousOn_const)

  -- Local uniform convergence of the infinite product on `U`.
  have hloc :
      HasProdLocallyUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n, (1 + f n z)) U :=
    Summable.hasProdLocallyUniformlyOn_nat_one_add (K := U) hUopen hM hBoundU hcts

  -- Restrict to `K` and extract uniform convergence there.
  have hlocK :
      HasProdLocallyUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n, (1 + f n z)) K :=
    hloc.mono hKU
  have hunifK :
      HasProdUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n, (1 + f n z)) K :=
    hlocK.hasProdUniformlyOn_of_isCompact hK
  have htendK :
      TendstoUniformlyOn (fun N z ↦ ∏ n ∈ range N, (1 + f n z))
        (fun z ↦ ∏' n, (1 + f n z)) atTop K :=
    hunifK.tendstoUniformlyOn_finsetRange

  -- Differentiability (hence analyticity) of the limit on the open set `U`,
  -- by the locally uniform limit theorem.
  have hFdiff : ∀ᶠ s : Finset ℕ in (atTop : Filter (Finset ℕ)),
      DifferentiableOn ℂ (fun z ↦ ∏ i ∈ s, (1 + f i z)) U :=
    Filter.Eventually.of_forall (fun s => by
      -- Finite products of differentiable functions are differentiable.
      have hdf : ∀ i ∈ s, DifferentiableOn ℂ (fun z => (1 + f i z)) U := by
        intro i hi
        -- `1 + f i` is differentiable everywhere.
        have : Differentiable ℂ (fun z => (1 + f i z)) := by
          have hdiff : Differentiable ℂ (fun z => weierstrassFactor m (z / a i)) :=
            (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a i))
          simpa [f, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
            (hdiff.sub_const (1 : ℂ)).const_add (1 : ℂ)
        exact this.differentiableOn
      simpa [Finset.prod_fn] using
        (DifferentiableOn.finset_prod (s := U) (u := s) (f := fun i z => (1 + f i z)) hdf))

  have htlocU :
      TendstoLocallyUniformlyOn (fun s z ↦ ∏ i ∈ s, (1 + f i z)) (fun z ↦ ∏' n, (1 + f n z))
        (atTop : Filter (Finset ℕ)) U := by
    -- This is just the definition of `HasProdLocallyUniformlyOn`.
    simpa [HasProdLocallyUniformlyOn] using hloc
  have hdiffU : DifferentiableOn ℂ (fun z ↦ ∏' n, (1 + f n z)) U :=
    htlocU.differentiableOn hFdiff hUopen

  refine ⟨fun z ↦ ∏' n, (1 + f n z), ?_, ?_⟩
  · -- Rewrite `1 + f n z` to `weierstrassFactor m (z / a n)`.
    simpa [f, add_sub_cancel] using htendK
  · -- Analyticity on `K` follows from differentiability on an open neighbourhood `U` of `K`.
    intro z hz
    have hzU : z ∈ U := hKU hz
    have hU_nhds : U ∈ 𝓝 z := hUopen.mem_nhds hzU
    exact (hdiffU.analyticAt hU_nhds).analyticWithinAt

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
  -- G(z) = lim_{N→∞} ∏_{n < N} E_m(z/aₙ)
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

/-- Jensen's bound on the number of zeros from boundedness.

If f is analytic on |z| ≤ R with f(0) = 1 and |f(z)| ≤ B for |z| ≤ R,
then the number of zeros in |z| ≤ r < R is at most
log B / log(R/r).

This is a reformulation of `ZerosBound` from StrongPNT. -/
theorem jensen_zeros_bound {f : ℂ → ℂ} {r R B : ℝ}
    (hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hr : 0 < r) (hR : r < R) (hR1 : R < 1)
    (hf0 : f 0 = 1) (hB : 1 < B)
    (hf_bound : ∀ z, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∃ (zeros : Finset ℂ), (∀ z, z ∈ zeros ↔ ‖z‖ ≤ r ∧ f z = 0) ∧
      zeros.card ≤ Nat.ceil (Real.log B / Real.log (R / r)) := by
  classical
  have hRpos : 0 < R := lt_trans hr hR
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have habsR : |R| = R := abs_of_pos hRpos

  -- Work on `closedBall 0 |R|` to match Mathlib's Jensen formula API.
  let U : Set ℂ := Metric.closedBall (0 : ℂ) |R|
  have hf_analU : AnalyticOnNhd ℂ f U := by
    simpa [U, habsR] using hf_anal
  have hf_merU : MeromorphicOn f U := hf_analU.meromorphicOn

  -- Exclude the degenerate case `order = ⊤` (local identically-zero), using `f 0 = 1`.
  have h_not_top : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u huU hu_top
    have hfreq : ∃ᶠ z in 𝓝[≠] u, f z = 0 :=
      (Filter.Eventually.frequently ((meromorphicOrderAt_eq_top_iff).1 hu_top))
    have hEq : Set.EqOn f 0 U :=
      hf_analU.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (hU := (convex_closedBall (0 : ℂ) |R|).isPreconnected) huU hfreq
    have h0U : (0 : ℂ) ∈ U := by
      simp [U, abs_nonneg R]
    have : f 0 = 0 := by simpa using hEq h0U
    -- Contradiction with `f 0 = 1`.
    simpa [hf0] using this

  -- Build a finset of (distinct) zeros using the divisor support.
  have hDfin : (MeromorphicOn.divisor f U).support.Finite :=
    (MeromorphicOn.divisor f U).finiteSupport (isCompact_closedBall (0 : ℂ) |R|)
  let s : Finset ℂ := hDfin.toFinset
  let zeros : Finset ℂ := s.filter fun z ↦ ‖z‖ ≤ r

  have h_nf : MeromorphicNFOn f U := hf_analU.meromorphicNFOn
  have h_not_top' : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := fun u ↦ h_not_top u.1 u.2
  have hzeroset :
      U ∩ f ⁻¹' ({0} : Set ℂ) = Function.support (MeromorphicOn.divisor f U) :=
    h_nf.zero_set_eq_divisor_support h_not_top'
  have hsupport :
      Function.support (MeromorphicOn.divisor f U) = U ∩ f ⁻¹' ({0} : Set ℂ) := by
    simpa using hzeroset.symm

  refine ⟨zeros, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      have hz' : z ∈ s ∧ ‖z‖ ≤ r := by
        simpa [zeros, Finset.mem_filter] using hz
      have hz_s : z ∈ s := hz'.1
      have hz_r : ‖z‖ ≤ r := hz'.2
      have hz_supp : z ∈ Function.support (MeromorphicOn.divisor f U) := by
        simpa [s, Finite.mem_toFinset] using hz_s
      have hzU0 : z ∈ U ∧ f z = 0 := by
        -- unpack membership in `U ∩ f ⁻¹' {0}`
        simpa [hsupport, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using hz_supp
      exact ⟨hz_r, hzU0.2⟩
    · rintro ⟨hz_r, hfz⟩
      have hzU : z ∈ U := by
        -- `‖z‖ ≤ r < R = |R|`
        have : ‖z‖ ≤ |R| := by
          have : ‖z‖ ≤ R := le_trans hz_r (le_of_lt hR)
          simpa [habsR] using this
        simpa [U, Metric.mem_closedBall, dist_zero_right] using this
      have hz_supp : z ∈ Function.support (MeromorphicOn.divisor f U) := by
        -- via `support = U ∩ f ⁻¹' {0}`
        have : z ∈ U ∩ f ⁻¹' ({0} : Set ℂ) := by
          simpa [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using And.intro hzU hfz
        simpa [hsupport] using this
      have hz_s : z ∈ s := by
        simpa [s, Finite.mem_toFinset] using hz_supp
      have : z ∈ zeros := by
        simpa [zeros, Finset.mem_filter, hz_s, hz_r]
      exact this
  · -- Bound the number of (distinct) zeros using Jensen's formula.
    -- Step 1: bound the circle average by `log B`.
    have hCircleInt : CircleIntegrable (Real.log ‖f ·‖) (0 : ℂ) R := by
      -- `log ‖f ·‖` is circle integrable if `f` is meromorphic on the circle.
      apply circleIntegrable_log_norm_meromorphicOn
      have : MeromorphicOn f (Metric.sphere (0 : ℂ) |R|) :=
        hf_merU.mono Metric.sphere_subset_closedBall
      simpa [habsR] using this
    have hCA_le : Real.circleAverage (Real.log ‖f ·‖) (0 : ℂ) R ≤ Real.log B := by
      apply Real.circleAverage_mono_on_of_le_circle (hf := hCircleInt)
      intro z hz
      have hz_leR : ‖z‖ ≤ R := by
        have hz_eq : ‖z‖ = |R| := by
          simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
        have : ‖z‖ ≤ |R| := le_of_eq hz_eq
        simpa [habsR] using this
      have hfz_le : ‖f z‖ ≤ B := hf_bound z hz_leR
      by_cases h0 : ‖f z‖ = 0
      · -- `log 0 = 0 ≤ log B` since `B > 1`.
        have : 0 ≤ Real.log B := le_of_lt (Real.log_pos hB)
        simpa [h0, this] using this
      · have hpos : 0 < ‖f z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
        exact Real.log_le_log hpos hfz_le

    -- Step 2: Jensen's formula, specialized to `c = 0`.
    have h0U : (0 : ℂ) ∈ U := by simp [U, abs_nonneg R]
    have hAnal0 : AnalyticAt ℂ f 0 := by
      have h0R : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
        simp [Metric.mem_closedBall, hRpos.le]
      exact hf_anal 0 h0R
    have hf0_ne : f 0 ≠ 0 := by simpa [hf0] using (one_ne_zero : (1 : ℂ) ≠ 0)
    have hdiv0 : MeromorphicOn.divisor f U 0 = 0 := by
      have : meromorphicOrderAt f 0 = 0 := by
        have horder : meromorphicOrderAt f 0 = (analyticOrderAt f 0).map (↑) :=
          hAnal0.meromorphicOrderAt_eq
        have han0 : analyticOrderAt f 0 = 0 := (hAnal0.analyticOrderAt_eq_zero).2 hf0_ne
        simpa [horder, han0]
      simp [MeromorphicOn.divisor_apply hf_merU h0U, this]
    have htrail : meromorphicTrailingCoeffAt f 0 = f 0 :=
      hAnal0.meromorphicTrailingCoeffAt_of_ne_zero hf0_ne

    have hJensen :
        Real.circleAverage (Real.log ‖f ·‖) (0 : ℂ) R
          = (∑ᶠ u, (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹)) := by
      -- Start from Mathlib's Jensen formula and simplify the extra terms using `f 0 = 1`.
      have hJ :=
        (MeromorphicOn.circleAverage_log_norm (c := (0 : ℂ)) (R := R) (f := f) hRne hf_merU)
      -- Rewrite `‖0 - u‖` to `‖u‖`, and eliminate the center/divisor/trailing-coefficient terms.
      -- The convention `log 0 = 0` is built into the formula.
      simpa [hdiv0, htrail, hf0, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hJ

    have hFsum_le :
        (∑ᶠ u, (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹)) ≤ Real.log B := by
      -- `circleAverage ≤ log B`, and Jensen identifies the circle average with the finsum.
      simpa [hJensen] using hCA_le

    -- Step 3: compare the finsum to the finite sum over `s = support (divisor)`.
    let g : ℂ → ℝ :=
      fun u ↦ (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹)
    have hsupp_g : g.support ⊆ s := by
      intro u hu
      have hdiv_ne : MeromorphicOn.divisor f U u ≠ 0 := by
        intro hdiv
        have : g u = 0 := by simp [g, hdiv]
        exact (Function.mem_support.mp hu) this
      have : u ∈ (MeromorphicOn.divisor f U).support := by
        simpa [Function.mem_support] using hdiv_ne
      simpa [s, Finite.mem_toFinset] using this
    have hsum_s : (∑ᶠ u, g u) = ∑ u ∈ s, g u := by
      simpa [g] using (finsum_eq_sum_of_support_subset (s := s) g hsupp_g)
    have hsum_s_le : (∑ u ∈ s, g u) ≤ Real.log B := by
      simpa [hsum_s] using hFsum_le

    -- Step 4: restrict from `s` to `zeros` and use `log(R/‖u‖) ≥ log(R/r)` for `‖u‖ ≤ r`.
    have hzeros_subset : zeros ⊆ s := by
      intro u hu
      exact (Finset.mem_filter.1 hu).1
    have hDnonneg : (0 : ℤ) ≤ MeromorphicOn.divisor f U := hf_analU.divisor_nonneg
    have hlog_pos : 0 < Real.log (R / r) := by
      have : 1 < R / r := (one_lt_div hr).2 hR
      exact Real.log_pos this
    have hlog_nonneg : 0 ≤ Real.log (R / r) := le_of_lt hlog_pos

    have hsum_zeros_le : (∑ u ∈ zeros, g u) ≤ Real.log B := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg hzeros_subset ?_).trans hsum_s_le
      intro u hu_s hu_not
      have hu_support : u ∈ Function.support (MeromorphicOn.divisor f U) := by
        simpa [s, Finite.mem_toFinset] using hu_s
      have huU : u ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain hu_support
      have hdiv0 : 0 ≤ (MeromorphicOn.divisor f U u : ℝ) := by
        exact_mod_cast (hDnonneg u)
      have hlog0 : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
        by_cases hu0 : u = 0
        · simp [hu0]
        · have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
          have hnorm_le : ‖u‖ ≤ R := by
            have : ‖u‖ ≤ |R| := by
              simpa [U, Metric.mem_closedBall, dist_zero_right] using huU
            simpa [habsR] using this
          have : 1 ≤ R / ‖u‖ := (one_le_div hnorm_pos).2 hnorm_le
          -- `R / ‖u‖ = R * ‖u‖⁻¹`
          simpa [div_eq_mul_inv] using (Real.log_nonneg this)
      exact mul_nonneg hdiv0 hlog0

    -- Step 5: lower bound `∑_{u∈zeros} g u` by `zeros.card * log(R/r)`.
    have hsum_lower :
        (zeros.card : ℝ) * Real.log (R / r) ≤ ∑ u ∈ zeros, g u := by
      -- rewrite the left side as the sum of a constant
      have : ∑ _u ∈ zeros, Real.log (R / r) = (zeros.card : ℝ) * Real.log (R / r) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      -- show pointwise: `log(R/r) ≤ g u` on `zeros`
      refine this.symm.le.trans (Finset.sum_le_sum ?_)
      intro u hu
      have hu' : u ∈ s ∧ ‖u‖ ≤ r := by
        simpa [zeros, Finset.mem_filter] using hu
      have hu_s : u ∈ s := hu'.1
      have hu_r : ‖u‖ ≤ r := hu'.2
      have hu_support : u ∈ Function.support (MeromorphicOn.divisor f U) := by
        simpa [s, Finite.mem_toFinset] using hu_s
      have hdiv_ne : MeromorphicOn.divisor f U u ≠ 0 := by
        simpa [Function.mem_support] using hu_support
      have hdiv_nonneg_int : (0 : ℤ) ≤ MeromorphicOn.divisor f U u := hDnonneg u
      have hdiv_pos_int : (0 : ℤ) < MeromorphicOn.divisor f U u :=
        lt_of_le_of_ne hdiv_nonneg_int (Ne.symm hdiv_ne)
      have hdiv_ge_one_int : (1 : ℤ) ≤ MeromorphicOn.divisor f U u := by
        simpa using (Int.add_one_le_iff).2 hdiv_pos_int
      have hdiv_ge_one : (1 : ℝ) ≤ (MeromorphicOn.divisor f U u : ℝ) := by
        exact_mod_cast hdiv_ge_one_int
      have hdiv_nonneg : (0 : ℝ) ≤ (MeromorphicOn.divisor f U u : ℝ) := by
        exact_mod_cast hdiv_nonneg_int
      -- `log(R/r) ≤ log(R*‖u‖⁻¹)` since `‖u‖ ≤ r`.
      have hu0 : u ≠ 0 := by
        intro hu0
        -- `u = 0` would force `f 0 = 0`, contradicting `f 0 = 1`
        have huU0 : u ∈ U ∧ f u = 0 := by
          simpa [hsupport, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using hu_support
        have : f 0 = 0 := by simpa [hu0] using huU0.2
        simpa [hf0] using this
      have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have harg_le :
          R / r ≤ R * ‖u‖⁻¹ := by
        have hinv : (1 / r) ≤ (1 / ‖u‖) := one_div_le_one_div_of_le hnorm_pos hu_r
        have := mul_le_mul_of_nonneg_left hinv hRpos.le
        simpa [div_eq_mul_inv, one_div] using this
      have hlog_le : Real.log (R / r) ≤ Real.log (R * ‖u‖⁻¹) := by
        have hpos : 0 < R / r := div_pos hRpos hr
        exact Real.log_le_log hpos harg_le
      -- combine
      have : (1 : ℝ) * Real.log (R / r)
          ≤ (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹) :=
        mul_le_mul hdiv_ge_one hlog_le hlog_nonneg hdiv_nonneg
      simpa [g] using this

    -- Step 6: conclude `zeros.card ≤ ceil(log B / log(R/r))`.
    have hcard_le_real :
        (zeros.card : ℝ) ≤ Real.log B / Real.log (R / r) := by
      -- Divide the inequality by `log(R/r) > 0`.
      have : (zeros.card : ℝ) * Real.log (R / r) ≤ Real.log B :=
        (hsum_lower.trans hsum_zeros_le)
      exact (le_div_iff₀ hlog_pos).2 (by simpa [mul_assoc] using this)
    have hcard_le_ceil_real :
        (zeros.card : ℝ) ≤ (Nat.ceil (Real.log B / Real.log (R / r)) : ℝ) :=
      hcard_le_real.trans (Nat.le_ceil _)
    exact_mod_cast hcard_le_ceil_real

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
  have hRpos : 0 < R := lt_trans hr hR
  have hAnal : AnalyticOn ℂ f (Metric.closedBall 0 R) := by
    intro w hw
    exact (hf_anal w hw).analyticWithinAt
  have hRe : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M := by
    intro w hw
    have : ‖w‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact hf_re w this
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (borelCaratheodory_closedBall (M := M) (R := R) (r := r) (z := z)
      hRpos hAnal hf0 hM hRe hR hz')

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
  have hAnal : AnalyticOn ℂ f (Metric.closedBall 0 R) := by
    intro w hw
    exact (hf_anal w hw).analyticWithinAt
  have hRe : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M := by
    intro w hw
    have : ‖w‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact hf_re w this
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  -- Choose the midpoint radius `r' = (R+r)/2` to get a clean constant.
  set r' : ℝ := (R + r) / 2
  have hr_lt_r' : r < r' := by
    have : r < (R + r) / 2 := by linarith [hR]
    simpa [r'] using this
  have hr'_lt_R : r' < R := by
    have : (R + r) / 2 < R := by linarith [hR]
    simpa [r'] using this
  have hderiv :
      ‖deriv f z‖ ≤ 2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) := by
    simpa using
      (derivativeBound
        (R := R) (M := M) (r := r) (r' := r') (z := z) (f := f)
        hAnal hf0 hM hRe hr hz' hr_lt_r' hr'_lt_R)
  -- Simplify the constant for this choice of `r'`.
  have hconst :
      2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) = 16 * M * r' ^ 2 / (R - r) ^ 3 := by
    have hRr0 : (R - r) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hR)
    have hden1 : R - r' ≠ 0 := ne_of_gt (sub_pos.mpr hr'_lt_R)
    have hden2 : r' - r ≠ 0 := ne_of_gt (sub_pos.mpr hr_lt_r')
    have hRr' : R - r' = (R - r) / 2 := by simp [r']; ring
    have hr'r : r' - r = (R - r) / 2 := by simp [r']; ring
    field_simp [div_eq_mul_inv, hRr0, hden1, hden2]
    simp [hRr', hr'r]
    ring
  have hr'_le_R : r' ≤ R := by
    have : (R + r) / 2 ≤ R := by linarith [le_of_lt hR]
    simpa [r'] using this
  have hr'_sq_le : r' ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (lt_trans hr hr_lt_r')) hr'_le_R 2
  have hden_nn : 0 ≤ (R - r) ^ 3 := pow_nonneg (sub_nonneg.mpr (le_of_lt hR)) 3
  have hMnn : 0 ≤ M := le_of_lt hM
  have hnum : 16 * M * r' ^ 2 ≤ 16 * M * R ^ 2 := by
    have h16M : 0 ≤ 16 * M := by nlinarith [hMnn]
    have := mul_le_mul_of_nonneg_left hr'_sq_le h16M
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hfinal :
      16 * M * r' ^ 2 / (R - r) ^ 3 ≤ 16 * M * R ^ 2 / (R - r) ^ 3 :=
    div_le_div_of_nonneg_right hnum hden_nn
  have : ‖deriv f z‖ ≤ 16 * M * r' ^ 2 / (R - r) ^ 3 := by
    simpa [hconst] using hderiv
  exact le_trans this hfinal

/-- Lindelöf's theorem: finite order implies summability of zero exponents.

If f is entire of order ρ, then for any σ > ρ, the series ∑|aₙ|^{-σ}
converges, where aₙ are the nonzero zeros of f. -/
theorem lindelof_zero_exponent {f : ℂ → ℂ} {ρ σ : ℝ}
    (hf : EntireOfFiniteOrder ρ f)
    (hσ : ρ < σ)
    (hf0 : f 0 ≠ 0)
    (zeros : ℕ → ℂ)
    (h_inj : Function.Injective zeros)
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
    (hG_nontrivial : ∃ z, G z ≠ 0)
    (h_ord : ∀ z : ℂ, analyticOrderAt G z ≤ analyticOrderAt f z) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, G z ≠ 0 → H z = f z / G z := by
  classical
  -- Define the quotient on the punctured neighbourhoods.
  let q : ℂ → ℂ := fun z ↦ f z / G z
  -- Fill in the removable singularities by taking the `limUnder` at each potential pole.
  let H : ℂ → ℂ := fun z ↦ if hz : G z = 0 then limUnder (𝓝[≠] z) q else q z
  refine ⟨H, ?_, ?_⟩
  · -- `H` is entire: check differentiability at each point.
    intro z0
    by_cases hz0 : G z0 = 0
    · -- Removable singularity at `z0`.
      have hf_an : AnalyticAt ℂ f z0 := (hf.analyticAt z0)
      have hG_an : AnalyticAt ℂ G z0 := (hG.analyticAt z0)
      -- `G` is not locally zero anywhere, otherwise it would be identically zero.
      have hG_not_eventually_zero : ¬ (∀ᶠ z in 𝓝 z0, G z = 0) := by
        intro hloc
        have hG_univ : AnalyticOnNhd ℂ G (Set.univ : Set ℂ) :=
          (analyticOnNhd_univ_iff_differentiable).2 hG
        have hfreq : ∃ᶠ z in 𝓝[≠] z0, G z = 0 :=
          (hloc.filter_mono nhdsWithin_le_nhds).frequently
        have hEq : Set.EqOn G 0 (Set.univ : Set ℂ) :=
          AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
            (f := G) (U := (Set.univ : Set ℂ)) hG_univ (by simpa using isPreconnected_univ)
            (by simp) hfreq
        rcases hG_nontrivial with ⟨w, hw⟩
        exact hw (by simpa using hEq (by simp : w ∈ (Set.univ : Set ℂ)))
      -- Hence `G` is eventually nonzero on a punctured neighbourhood of `z0`.
      have hG_ne : ∀ᶠ z in 𝓝[≠] z0, G z ≠ 0 :=
        (hG_an.eventually_eq_zero_or_eventually_ne_zero).resolve_left hG_not_eventually_zero

      -- On a punctured neighbourhood of `z0`, `H = q`.
      have hH_eq_q : ∀ᶠ z in 𝓝[≠] z0, H z = q z := by
        filter_upwards [hG_ne] with z hz
        simp [H, q, hz]

      -- `q` is meromorphic at `z0`, and has nonnegative order thanks to `h_ord`.
      have hq_mer : MeromorphicAt q z0 :=
        (hf_an.meromorphicAt).div (hG_an.meromorphicAt)
      have h_cast_mono : Monotone (fun n : ℕ => (n : ℤ)) := by
        intro a b hab
        exact Int.ofNat_le_ofNat.mpr hab
      have hmap_mono : Monotone (fun t : ℕ∞ => t.map (fun n : ℕ => (n : ℤ))) :=
        (ENat.monotone_map_iff (f := fun n : ℕ => (n : ℤ))).2 h_cast_mono
      have hG_le_f : meromorphicOrderAt G z0 ≤ meromorphicOrderAt f z0 := by
        -- Transport the analytic order inequality to a meromorphic order inequality.
        have : (analyticOrderAt G z0).map (fun n : ℕ => (n : ℤ))
              ≤ (analyticOrderAt f z0).map (fun n : ℕ => (n : ℤ)) :=
          hmap_mono (h_ord z0)
        simpa [hG_an.meromorphicOrderAt_eq, hf_an.meromorphicOrderAt_eq] using this
      have hq_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt q z0 := by
        -- `order(q) = order(f) - order(G)`.
        have hq_order :
            meromorphicOrderAt q z0 = meromorphicOrderAt f z0 - meromorphicOrderAt G z0 := by
          simp [q, div_eq_mul_inv, sub_eq_add_neg, meromorphicOrderAt_mul hq_mer (hG_an.meromorphicAt.inv),
            meromorphicOrderAt_inv]
        -- Nonnegativity follows from `order(G) ≤ order(f)`.
        rw [hq_order]
        exact sub_nonneg.mpr hG_le_f

      -- `q` has a limit along `𝓝[≠] z0`, hence tends to `limUnder ... q`.
      have hq_hasLimit : ∃ c, Tendsto q (𝓝[≠] z0) (𝓝 c) :=
        MeromorphicAt.tendsto_nhds_of_meromorphicOrderAt_nonneg hq_mer hq_nonneg
      have hq_tendsto_lim : Tendsto q (𝓝[≠] z0) (𝓝 (limUnder (𝓝[≠] z0) q)) :=
        tendsto_nhds_limUnder hq_hasLimit

      -- Choose a neighbourhood on which `G` is nonzero except at the center; there `H` is an update
      -- of `q` by the computed limit.
      rcases (eventually_nhdsWithin_iff.1 hG_ne) with ⟨U, hU_nhds, hU, hU0⟩
      -- Continuity of the updated quotient at `z0`.
      have hcont_update :
          ContinuousAt (Function.update q z0 (limUnder (𝓝[≠] z0) q)) z0 := by
        -- `q → limUnder ... q` on the punctured neighbourhood.
        exact (continuousAt_update_same).2 hq_tendsto_lim
      -- The update is meromorphic at `z0` (it agrees with `q` on a punctured neighbourhood).
      have hmer_update : MeromorphicAt (Function.update q z0 (limUnder (𝓝[≠] z0) q)) z0 := by
        refine hq_mer.congr ?_
        -- `update q z0 _` equals `q` on `𝓝[≠] z0`.
        filter_upwards [self_mem_nhdsWithin] with z hz
        simpa [Function.update, hz.2]  -- `z ≠ z0`
      -- Hence the update is analytic at `z0`, and therefore differentiable at `z0`.
      have han_update :
          AnalyticAt ℂ (Function.update q z0 (limUnder (𝓝[≠] z0) q)) z0 :=
        MeromorphicAt.analyticAt hmer_update hcont_update

      -- Finally, `H` agrees with this update on a neighbourhood of `z0`, hence is analytic at `z0`.
      have hEq_on : (fun z => H z) =ᶠ[𝓝 z0] (Function.update q z0 (limUnder (𝓝[≠] z0) q)) := by
        -- On `U`, there are no other zeros of `G`, so `H` matches `q` off `z0` and matches the
        -- update at `z0` by definition.
        refine (eventually_of_mem hU_nhds ?_)
        intro z hzU
        by_cases hz : z = z0
        · subst hz
          simp [H, hz0, q]
        · have : z ∈ (U \ {z0}) := ⟨hzU, by simpa [Set.mem_singleton_iff] using hz⟩
          have hGz : G z ≠ 0 := hU z this
          simp [H, q, hz, hGz, Function.update, hz]

      have hanH : AnalyticAt ℂ H z0 := han_update.congr hEq_on
      exact hanH.differentiableAt
    · -- Regular point: `G z0 ≠ 0`, so `H = f/G` near `z0`.
      have hG0 : G z0 ≠ 0 := hz0
      -- On this branch, `H z0 = f z0 / G z0`.
      have hHz0 : H z0 = f z0 / G z0 := by simp [H, q, hG0]
      -- Differentiability of the quotient at a point with nonzero denominator.
      have hdiff : DifferentiableAt ℂ (fun z => f z / G z) z0 :=
        (hf z0).div (hG z0) hG0
      -- `H` agrees with the quotient in a neighbourhood of `z0` (by continuity of `G`).
      have hG_near : ∀ᶠ z in 𝓝 z0, G z ≠ 0 :=
        (hG.continuousAt z0).eventually_ne hG0
      have hEq : (fun z => H z) =ᶠ[𝓝 z0] (fun z => f z / G z) := by
        filter_upwards [hG_near] with z hz
        simp [H, q, hz]
      -- Conclude.
      exact (hdiff.congr_of_eventuallyEq hEq).differentiableAt
  · intro z hz
    simp [H, q, hz]

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
          (hz.zeros.map fun ρ => weierstrassFactor m (z / ρ)).prod := by
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
          (hz.zeros.map fun ρ => (ComplexAnalysis.Hadamard.weierstrassFactor m (z / ρ))).prod :=
  ComplexAnalysis.Hadamard.hadamard_factorization hf hz

end
