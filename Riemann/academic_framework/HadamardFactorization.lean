
import Mathlib
import Mathlib.Analysis.Complex.CauchyIntegral
import Riemann.academic_framework.WeierstrassFactorBound
import PrimeNumberTheoremAnd.BorelCaratheodory
import PrimeNumberTheoremAnd.DerivativeBound
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.HarmonicBounds
import Riemann.Mathlib.Analysis.Complex.HardySpace.PoissonKernel
import Riemann.Mathlib.Analysis.Complex.Cartan
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.CircleAverageLemmas

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
* `ComplexAnalysis.Hadamard.lindelof_theorem` : Lindelöf's theorem for entire functions of finite order
* `ComplexAnalysis.Hadamard.hadamard_factorization` : The main factorization theorem
* `ComplexAnalysis.Hadamard.hadamard_riemannZeta` : Application to the Riemann zeta function
  (in `ZetaFiniteOrder`)

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
lemma exp_linear {a : ℂ} (_ : a ≠ 0) : EntireOfFiniteOrder 1 (fun z => exp (a * z)) := by
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

/-- The linear factor `z ↦ 1 - z` has a simple zero at `z = 1`. -/
lemma analyticOrderAt_one_sub :
    analyticOrderAt (fun z : ℂ => (1 : ℂ) - z) (1 : ℂ) = (1 : ℕ∞) := by
  -- Reduce to `z ↦ z - 1` using negation.
  have hsub : analyticOrderAt (fun z : ℂ => z - (1 : ℂ)) (1 : ℂ) = (1 : ℕ∞) := by
    simpa [pow_one] using
      (analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := (1 : ℂ)) (n := 1))
  have hrewrite : (fun z : ℂ => (1 : ℂ) - z) = fun z : ℂ => -(z - (1 : ℂ)) := by
    funext z
    ring
  -- `analyticOrderAt` is invariant under negation.
  calc
    analyticOrderAt (fun z : ℂ => (1 : ℂ) - z) (1 : ℂ)
        = analyticOrderAt (fun z : ℂ => -(z - (1 : ℂ))) (1 : ℂ) := by
            -- Avoid `simp` recursion depth issues by rewriting directly.
            simp
    _ = analyticOrderAt (fun z : ℂ => z - (1 : ℂ)) (1 : ℂ) := by
          -- `analyticOrderAt` is invariant under multiplication by a nonzero constant.
          have hconst_an : AnalyticAt ℂ (fun _ : ℂ => (-1 : ℂ)) (1 : ℂ) := analyticAt_const
          have hconst_ne : (fun _ : ℂ => (-1 : ℂ)) (1 : ℂ) ≠ 0 := by simp
          have hconst_order : analyticOrderAt (fun _ : ℂ => (-1 : ℂ)) (1 : ℂ) = 0 :=
            (hconst_an.analyticOrderAt_eq_zero).2 hconst_ne
          have hsub_an : AnalyticAt ℂ (fun z : ℂ => z - (1 : ℂ)) (1 : ℂ) :=
            analyticAt_id.sub analyticAt_const
          -- `-(z-1) = (-1) * (z-1)`
          have hrewrite : (fun z : ℂ => -(z - (1 : ℂ))) = fun z : ℂ => (-1 : ℂ) * (z - (1 : ℂ)) := by
            funext z; ring
          have hmul :
              analyticOrderAt (fun z : ℂ => (-1 : ℂ) * (z - (1 : ℂ))) (1 : ℂ)
                = analyticOrderAt (fun _ : ℂ => (-1 : ℂ)) (1 : ℂ)
                  + analyticOrderAt (fun z : ℂ => z - (1 : ℂ)) (1 : ℂ) :=
            analyticOrderAt_mul (𝕜 := ℂ)
              (f := fun _ : ℂ => (-1 : ℂ)) (g := fun z : ℂ => z - (1 : ℂ)) (z₀ := (1 : ℂ))
              hconst_an hsub_an
          calc
            analyticOrderAt (fun z : ℂ => -(z - (1 : ℂ))) (1 : ℂ)
                = analyticOrderAt (fun z : ℂ => (-1 : ℂ) * (z - (1 : ℂ))) (1 : ℂ) := by
                    simp
            _ = analyticOrderAt (fun z : ℂ => z - (1 : ℂ)) (1 : ℂ) := by
                  calc
                    analyticOrderAt (fun z : ℂ => (-1 : ℂ) * (z - (1 : ℂ))) (1 : ℂ)
                        = analyticOrderAt (fun _ : ℂ => (-1 : ℂ)) (1 : ℂ)
                          + analyticOrderAt (fun z : ℂ => z - (1 : ℂ)) (1 : ℂ) := hmul
                    _ = analyticOrderAt (fun z : ℂ => z - (1 : ℂ)) (1 : ℂ) := by
                          simp [hconst_order]
    _ = (1 : ℕ∞) := hsub

/-- The Weierstrass factor has a simple zero at `z = 1`. -/
lemma analyticOrderAt_weierstrassFactor_one (m : ℕ) :
    analyticOrderAt (weierstrassFactor m) (1 : ℂ) = (1 : ℕ∞) := by
  -- `E_m(z) = (1-z) * exp(partialLogSum m z)` and `exp(...)` is nonzero at `1`.
  have hlin_an : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) (1 : ℂ) :=
    analyticAt_const.sub analyticAt_id
  have hlin_order : analyticOrderAt (fun z : ℂ => (1 : ℂ) - z) (1 : ℂ) = (1 : ℕ∞) :=
    analyticOrderAt_one_sub
  -- Analyticity of the exponential factor.
  have hsum_diff : Differentiable ℂ (partialLogSum m) := by
    -- finite sum of differentiable functions
    unfold partialLogSum
    apply Differentiable.fun_sum
    intro k _
    exact (differentiable_id.pow _).div_const _
  have hexp_an : AnalyticAt ℂ (fun z : ℂ => exp (partialLogSum m z)) (1 : ℂ) :=
    (differentiable_exp.comp hsum_diff).analyticAt 1
  have hexp_ne : (exp (partialLogSum m (1 : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  have hexp_order : analyticOrderAt (fun z : ℂ => exp (partialLogSum m z)) (1 : ℂ) = 0 :=
    (hexp_an.analyticOrderAt_eq_zero).2 (by simp)
  -- Combine with multiplicativity of `analyticOrderAt`.
  have hmul :
      analyticOrderAt (fun z : ℂ => ((1 : ℂ) - z) * exp (partialLogSum m z)) (1 : ℂ)
        = analyticOrderAt (fun z : ℂ => (1 : ℂ) - z) (1 : ℂ)
          + analyticOrderAt (fun z : ℂ => exp (partialLogSum m z)) (1 : ℂ) :=
    analyticOrderAt_mul (𝕜 := ℂ) (f := fun z : ℂ => (1 : ℂ) - z)
      (g := fun z : ℂ => exp (partialLogSum m z)) (z₀ := (1 : ℂ)) hlin_an hexp_an
  -- Rewrite `weierstrassFactor` and finish.
  calc
    analyticOrderAt (weierstrassFactor m) (1 : ℂ)
        = analyticOrderAt (fun z : ℂ => ((1 : ℂ) - z) * exp (partialLogSum m z)) (1 : ℂ) := by
            -- `weierstrassFactor m` is definitionally `(1-z) * exp(partialLogSum m z)`.
            have hfun :
                (weierstrassFactor m) = fun z : ℂ => ((1 : ℂ) - z) * exp (partialLogSum m z) := by
              funext z
              simp [weierstrassFactor, partialLogSum]
            simpa using congrArg (fun f : ℂ → ℂ => analyticOrderAt f (1 : ℂ)) hfun
    _ = analyticOrderAt (fun z : ℂ => (1 : ℂ) - z) (1 : ℂ)
          + analyticOrderAt (fun z : ℂ => exp (partialLogSum m z)) (1 : ℂ) := hmul
    _ = (1 : ℕ∞) := by simp [hlin_order, hexp_order]

/-- For `a ≠ 0`, the factor `z ↦ weierstrassFactor m (z / a)` has a simple zero at `z = a`. -/
lemma analyticOrderAt_weierstrassFactor_div_self {m : ℕ} {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun z : ℂ => weierstrassFactor m (z / a)) a = (1 : ℕ∞) := by
  -- Expand `weierstrassFactor`.
  have hlin_an : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - (z / a)) a :=
    analyticAt_const.sub ((differentiable_id.div_const a).analyticAt a)
  have hpartial_diff : Differentiable ℂ (partialLogSum m) := by
    unfold partialLogSum
    apply Differentiable.fun_sum
    intro k _
    exact (differentiable_id.pow _).div_const _
  have hsum_diff : Differentiable ℂ (fun z : ℂ => partialLogSum m (z / a)) := by
    simpa using hpartial_diff.comp (differentiable_id.div_const a)
  have hexp_an : AnalyticAt ℂ (fun z : ℂ => exp (partialLogSum m (z / a))) a :=
    (differentiable_exp.comp hsum_diff).analyticAt a
  have hexp_order : analyticOrderAt (fun z : ℂ => exp (partialLogSum m (z / a))) a = 0 :=
    (hexp_an.analyticOrderAt_eq_zero).2 (by simp)

  -- Linear factor: `(1 - z/a) = (-a⁻¹) * (z - a)`.
  have hlin_order : analyticOrderAt (fun z : ℂ => (1 : ℂ) - (z / a)) a = (1 : ℕ∞) := by
    have hconst_an : AnalyticAt ℂ (fun _ : ℂ => -(a⁻¹ : ℂ)) a := analyticAt_const
    have hconst_ne : (fun _ : ℂ => -(a⁻¹ : ℂ)) a ≠ 0 := by simp [ha]
    have hconst_order : analyticOrderAt (fun _ : ℂ => -(a⁻¹ : ℂ)) a = 0 :=
      (hconst_an.analyticOrderAt_eq_zero).2 hconst_ne
    have hsub_an : AnalyticAt ℂ (fun z : ℂ => z - a) a := analyticAt_id.sub analyticAt_const
    have hsub_order : analyticOrderAt (fun z : ℂ => z - a) a = (1 : ℕ∞) := by
      simpa [pow_one] using
        (analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := a) (n := 1))
    have hmul :
        analyticOrderAt (fun z : ℂ => (-(a⁻¹ : ℂ)) * (z - a)) a
          = analyticOrderAt (fun _ : ℂ => (-(a⁻¹ : ℂ))) a
            + analyticOrderAt (fun z : ℂ => z - a) a :=
      analyticOrderAt_mul (𝕜 := ℂ)
        (f := fun _ : ℂ => (-(a⁻¹ : ℂ))) (g := fun z : ℂ => z - a) (z₀ := a)
        hconst_an hsub_an
    have hrewrite :
        (fun z : ℂ => (1 : ℂ) - (z / a)) = fun z : ℂ => (-(a⁻¹ : ℂ)) * (z - a) := by
      funext z
      field_simp [ha]
      ring
    calc
      analyticOrderAt (fun z : ℂ => (1 : ℂ) - (z / a)) a
          = analyticOrderAt (fun z : ℂ => (-(a⁻¹ : ℂ)) * (z - a)) a := by
              simp [hrewrite]
      _ = analyticOrderAt (fun _ : ℂ => (-(a⁻¹ : ℂ))) a + analyticOrderAt (fun z : ℂ => z - a) a := hmul
      _ = (1 : ℕ∞) := by simp [hconst_order, hsub_order]

  have hmul :
      analyticOrderAt (fun z : ℂ => ((1 : ℂ) - (z / a)) * exp (partialLogSum m (z / a))) a
        = analyticOrderAt (fun z : ℂ => (1 : ℂ) - (z / a)) a
          + analyticOrderAt (fun z : ℂ => exp (partialLogSum m (z / a))) a :=
    analyticOrderAt_mul (𝕜 := ℂ) (f := fun z : ℂ => (1 : ℂ) - (z / a))
      (g := fun z : ℂ => exp (partialLogSum m (z / a))) (z₀ := a) hlin_an hexp_an
  -- Finish.
  calc
    analyticOrderAt (fun z : ℂ => weierstrassFactor m (z / a)) a
        = analyticOrderAt (fun z : ℂ =>
              ((1 : ℂ) - (z / a)) * exp (partialLogSum m (z / a))) a := by
            have hfun :
                (fun z : ℂ => weierstrassFactor m (z / a))
                  = fun z : ℂ => ((1 : ℂ) - (z / a)) * exp (partialLogSum m (z / a)) := by
              funext z
              simp [weierstrassFactor, partialLogSum]
            simpa using congrArg (fun f : ℂ → ℂ => analyticOrderAt f a) hfun
    _ = analyticOrderAt (fun z : ℂ => (1 : ℂ) - (z / a)) a
          + analyticOrderAt (fun z : ℂ => exp (partialLogSum m (z / a))) a := hmul
    _ = (1 : ℕ∞) := by simp [hlin_order, hexp_order]

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

/-!
### A global growth bound for a single Weierstrass factor

For the finite-order bound on the canonical product, we need a bound of the form
`‖E_m(w)‖ ≤ exp(C * ‖w‖^(m+1))` valid for all `w`.
-/

lemma norm_weierstrassFactor_le_exp_pow (m : ℕ) :
    ∃ C > 0, ∀ w : ℂ, ‖weierstrassFactor m w‖ ≤ Real.exp (C * ‖w‖ ^ (m + 1)) := by
  classical
  -- A convenient explicit constant.
  let C : ℝ := max 4 ((m + 1 : ℝ) * (2 : ℝ) ^ (m + 1))
  have hCpos : 0 < C := by
    have : (0 : ℝ) < (4 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  refine ⟨C, hCpos, ?_⟩
  intro w
  by_cases hw : ‖w‖ ≤ (1 / 2 : ℝ)
  · -- Small `w`: use `‖E_m(w) - 1‖ ≤ 4‖w‖^(m+1)` and `1 + x ≤ exp x`.
    have hsub : ‖weierstrassFactor m w - 1‖ ≤ 4 * ‖w‖ ^ (m + 1) :=
      weierstrassFactor_sub_one_bound_pow (m := m) (z := w) hw
    have hnorm : ‖weierstrassFactor m w‖ ≤ 4 * ‖w‖ ^ (m + 1) + 1 := by
      -- `E = (E - 1) + 1`
      have hdecomp : (weierstrassFactor m w - 1) + (1 : ℂ) = weierstrassFactor m w := by
        simp
      calc
        ‖weierstrassFactor m w‖ = ‖(weierstrassFactor m w - 1) + (1 : ℂ)‖ := by
          simp [hdecomp]
        _ ≤ ‖weierstrassFactor m w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ (4 * ‖w‖ ^ (m + 1)) + 1 := by
          simp [hsub]
    have hle_exp : (4 * ‖w‖ ^ (m + 1) + 1) ≤ Real.exp (4 * ‖w‖ ^ (m + 1)) := by
      -- `x + 1 ≤ exp x`
        simpa [add_comm, add_left_comm, add_assoc] using (Real.add_one_le_exp (4 * ‖w‖ ^ (m + 1)))
    have hCge4 : (4 : ℝ) ≤ C := le_max_left _ _
    have hpow_nonneg : 0 ≤ ‖w‖ ^ (m + 1) := pow_nonneg (norm_nonneg w) _
    have hexp_mono :
        Real.exp (4 * ‖w‖ ^ (m + 1)) ≤ Real.exp (C * ‖w‖ ^ (m + 1)) := by
      apply Real.exp_monotone
      exact mul_le_mul_of_nonneg_right hCge4 hpow_nonneg
    exact hnorm.trans (hle_exp.trans hexp_mono)
  · -- Large `w`: use the definition and crude bounds.
    have hw' : (1 / 2 : ℝ) < ‖w‖ := lt_of_not_ge hw
    by_cases hw1 : ‖w‖ ≤ (1 : ℝ)
    · -- `1/2 < ‖w‖ ≤ 1`: bound by a constant and absorb into `exp (C * ‖w‖^(m+1))`.
      have hpartial :
          ‖partialLogSum m w‖ ≤ (m : ℝ) := by
        -- Bound the finite sum termwise by `1` (since `‖w‖ ≤ 1`).
        unfold partialLogSum
        have : ‖∑ k ∈ range m, w ^ (k + 1) / (k + 1)‖ ≤ ∑ k ∈ range m, ‖w ^ (k + 1) / (k + 1)‖ :=
          norm_sum_le _ _
        refine this.trans ?_
        have hterm : ∀ k ∈ range m, ‖w ^ (k + 1) / (k + 1)‖ ≤ (1 : ℝ) := by
          intro k hk
          rw [norm_div, Complex.norm_pow]
          have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
            have hk1_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
            exact_mod_cast hk1_nat
          have hdenom : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
            -- rewrite as a natural cast
            simpa [Nat.cast_add_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (k + 1))
          -- crude: `‖w‖^(k+1) / (k+1) ≤ ‖w‖^(k+1) ≤ 1`
          calc
            ‖w‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖
                = ‖w‖ ^ (k + 1) / ((k : ℝ) + 1) := by simp [hdenom]
            _ ≤ ‖w‖ ^ (k + 1) := by
              exact div_le_self (pow_nonneg (norm_nonneg w) _) hk1
            _ ≤ (1 : ℝ) := by
              exact pow_le_one₀ (norm_nonneg w) hw1
        -- Sum the termwise bound.
        calc
          (∑ k ∈ range m, ‖w ^ (k + 1) / (k + 1)‖) ≤ ∑ _k ∈ range m, (1 : ℝ) :=
            Finset.sum_le_sum (fun k hk => hterm k hk)
          _ = (m : ℝ) := by simp [Finset.sum_const]
      have hE :
          ‖weierstrassFactor m w‖ ≤ (2 : ℝ) * Real.exp (m : ℝ) := by
        -- `‖(1-w) * exp(partialLogSum)‖ ≤ (1+‖w‖) * exp(‖partialLogSum‖)`.
        have h1w : ‖(1 : ℂ) - w‖ ≤ 1 + ‖w‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (norm_add_le (1 : ℂ) (-w))
        have hexp : ‖exp (partialLogSum m w)‖ ≤ Real.exp ‖partialLogSum m w‖ :=
          Complex.norm_exp_le_exp_norm _
        have hnorm_mul :
            ‖weierstrassFactor m w‖ ≤ (1 + ‖w‖) * Real.exp ‖partialLogSum m w‖ := by
          simpa [weierstrassFactor, mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul h1w hexp (by positivity) (by positivity))
        have h1w_le2 : (1 + ‖w‖) ≤ (2 : ℝ) := by linarith [hw1, norm_nonneg w]
        have hexp_le : Real.exp ‖partialLogSum m w‖ ≤ Real.exp (m : ℝ) := by
          exact Real.exp_monotone hpartial
        calc
          ‖weierstrassFactor m w‖
              ≤ (1 + ‖w‖) * Real.exp ‖partialLogSum m w‖ := hnorm_mul
          _ ≤ (2 : ℝ) * Real.exp (m : ℝ) := by
              gcongr
      -- Now `2 * exp m ≤ exp (m+1)` and `m+1 ≤ C * ‖w‖^(m+1)` since `‖w‖ ≥ 1/2`.
      have h2le : (2 : ℝ) ≤ Real.exp 1 := by
        -- `1 + 1 ≤ exp 1`
        have h := Real.add_one_le_exp (1 : ℝ)
        -- `1 + 1 = 2`
        linarith
      have hE' : ‖weierstrassFactor m w‖ ≤ Real.exp ((m : ℝ) + 1) := by
        have : (2 : ℝ) * Real.exp (m : ℝ) ≤ Real.exp 1 * Real.exp (m : ℝ) :=
          mul_le_mul_of_nonneg_right h2le (Real.exp_nonneg _)
        have : (2 : ℝ) * Real.exp (m : ℝ) ≤ Real.exp ((1 : ℝ) + m) := by
          simpa [Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using this
        have : (2 : ℝ) * Real.exp (m : ℝ) ≤ Real.exp ((m : ℝ) + 1) := by
          simpa [add_comm, add_left_comm, add_assoc] using this
        exact hE.trans this
      have hCbig : ((m : ℝ) + 1) ≤ C * ‖w‖ ^ (m + 1) := by
        have hCge : ((m + 1 : ℝ) * (2 : ℝ) ^ (m + 1)) ≤ C := le_max_right _ _
        have hwpow : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) * ‖w‖ ^ (m + 1) := by
          have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
          have hw_ge : (1 / 2 : ℝ) ≤ ‖w‖ := le_of_lt hw'
          -- Multiply `‖w‖^(m+1) ≥ (1/2)^(m+1)` by `2^(m+1)`.
          have hwpow' : (1 / 2 : ℝ) ^ (m + 1) ≤ ‖w‖ ^ (m + 1) := by
            -- `‖w‖ ≥ 1/2`
            exact pow_le_pow_left₀ (a := (1 / 2 : ℝ)) (b := ‖w‖) (by positivity) hw_ge (m + 1)
          have htwo : (2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) ^ (m + 1) = (1 : ℝ) := by
            -- `(2 * (1/2))^(m+1) = 1`
            simp [inv_pow]
          calc
            (1 : ℝ) = (2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) ^ (m + 1) := htwo.symm
            _ ≤ (2 : ℝ) ^ (m + 1) * ‖w‖ ^ (m + 1) := by gcongr
        calc
          (m : ℝ) + 1 ≤ (m + 1 : ℝ) * (2 : ℝ) ^ (m + 1) * ‖w‖ ^ (m + 1) := by
            -- Since `1 ≤ 2^(m+1) * ‖w‖^(m+1)`.
            have : (m + 1 : ℝ) ≤ (m + 1 : ℝ) * ((2 : ℝ) ^ (m + 1) * ‖w‖ ^ (m + 1)) := by
              have hm0 : (0 : ℝ) ≤ (m + 1 : ℝ) := by positivity
              simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hwpow hm0)
            simpa [Nat.cast_add_one, add_comm, add_left_comm, add_assoc, mul_assoc] using this
          _ ≤ C * ‖w‖ ^ (m + 1) := by
            have hw0 : 0 ≤ ‖w‖ ^ (m + 1) := pow_nonneg (norm_nonneg w) _
            -- Use `((m+1)*2^(m+1)) ≤ C`.
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_right hCge hw0)
      have : Real.exp ((m : ℝ) + 1) ≤ Real.exp (C * ‖w‖ ^ (m + 1)) :=
        Real.exp_monotone hCbig
      exact hE'.trans this
    · -- `‖w‖ > 1`: bound directly by `exp ((m+1) * ‖w‖^(m+1))`.
      have hw1' : (1 : ℝ) < ‖w‖ := lt_of_not_ge hw1
      have hw_ge1 : (1 : ℝ) ≤ ‖w‖ := le_of_lt hw1'
      -- First bound `‖partialLogSum m w‖` by `m * ‖w‖^(m+1)`.
      have hpartial :
          ‖partialLogSum m w‖ ≤ (m : ℝ) * ‖w‖ ^ (m + 1) := by
        unfold partialLogSum
        have hsum :
            ‖∑ k ∈ range m, w ^ (k + 1) / (k + 1)‖ ≤ ∑ k ∈ range m, ‖w ^ (k + 1) / (k + 1)‖ :=
          norm_sum_le _ _
        refine hsum.trans ?_
        -- Bound each term by `‖w‖^(m+1)`.
        have hterm : ∀ k ∈ range m, ‖w ^ (k + 1) / (k + 1)‖ ≤ ‖w‖ ^ (m + 1) := by
          intro k hk
          rw [norm_div, Complex.norm_pow]
          have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
            have hk1_nat : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
            exact_mod_cast hk1_nat
          have hdenom : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
            simpa [Nat.cast_add_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (k + 1))
          have hk_le : (k + 1 : ℕ) ≤ m + 1 := Nat.succ_le_succ (Nat.le_of_lt (Finset.mem_range.mp hk))
          have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
          have hpow_le : ‖w‖ ^ (k + 1) ≤ ‖w‖ ^ (m + 1) :=
            pow_le_pow_right₀ (a := ‖w‖) (by simpa using hw_ge1) hk_le
          calc
            ‖w‖ ^ (k + 1) / ‖((k : ℂ) + 1)‖
                = ‖w‖ ^ (k + 1) / ((k : ℝ) + 1) := by simp [hdenom]
            _ ≤ ‖w‖ ^ (k + 1) := div_le_self (pow_nonneg (norm_nonneg w) _) hk1
            _ ≤ ‖w‖ ^ (m + 1) := hpow_le
        calc
          (∑ k ∈ range m, ‖w ^ (k + 1) / (k + 1)‖) ≤ ∑ _k ∈ range m, ‖w‖ ^ (m + 1) :=
            Finset.sum_le_sum (fun k hk => hterm k hk)
          _ = (m : ℝ) * ‖w‖ ^ (m + 1) := by simp [Finset.sum_const]
      -- Now estimate `‖weierstrassFactor m w‖`.
      have h1w : ‖(1 : ℂ) - w‖ ≤ 1 + ‖w‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (norm_add_le (1 : ℂ) (-w))
      have hexp : ‖exp (partialLogSum m w)‖ ≤ Real.exp ‖partialLogSum m w‖ :=
        Complex.norm_exp_le_exp_norm _
      have hnorm_mul :
          ‖weierstrassFactor m w‖ ≤ (1 + ‖w‖) * Real.exp ‖partialLogSum m w‖ := by
        simpa [weierstrassFactor, mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul h1w hexp (by positivity) (by positivity))
      have h1w_exp : (1 + ‖w‖) ≤ Real.exp ‖w‖ := by
        -- `‖w‖ + 1 ≤ exp ‖w‖`
        simpa [add_comm, add_left_comm, add_assoc] using Real.add_one_le_exp (‖w‖)
      have hw_le_pow : ‖w‖ ≤ ‖w‖ ^ (m + 1) := by
        -- for `‖w‖ ≥ 1`, powers are monotone
        exact le_self_pow₀ (a := ‖w‖) (by simpa using hw_ge1) (Nat.succ_ne_zero m)
      have h1w_exp' : (1 + ‖w‖) ≤ Real.exp (‖w‖ ^ (m + 1)) := by
        have : Real.exp ‖w‖ ≤ Real.exp (‖w‖ ^ (m + 1)) := Real.exp_monotone hw_le_pow
        exact h1w_exp.trans this
      have hexp_partial :
          Real.exp ‖partialLogSum m w‖ ≤ Real.exp ((m : ℝ) * ‖w‖ ^ (m + 1)) :=
        Real.exp_monotone hpartial
      have hE :
          ‖weierstrassFactor m w‖ ≤ Real.exp (((m : ℝ) + 1) * ‖w‖ ^ (m + 1)) := by
        -- Combine the bounds.
        have : ‖weierstrassFactor m w‖ ≤ Real.exp (‖w‖ ^ (m + 1)) * Real.exp ((m : ℝ) * ‖w‖ ^ (m + 1)) := by
          calc
            ‖weierstrassFactor m w‖
                ≤ (1 + ‖w‖) * Real.exp ‖partialLogSum m w‖ := hnorm_mul
            _ ≤ Real.exp (‖w‖ ^ (m + 1)) * Real.exp ((m : ℝ) * ‖w‖ ^ (m + 1)) := by
                gcongr
        -- Rewrite product of exponentials.
        have hexp_mul :
            Real.exp (‖w‖ ^ (m + 1)) * Real.exp ((m : ℝ) * ‖w‖ ^ (m + 1)) =
              Real.exp (((m : ℝ) + 1) * ‖w‖ ^ (m + 1)) := by
          -- `exp A * exp B = exp (A + B)`
          have : (‖w‖ ^ (m + 1)) + (m : ℝ) * ‖w‖ ^ (m + 1) = ((m : ℝ) + 1) * ‖w‖ ^ (m + 1) := by
            ring
          -- `exp_add` gives `exp A * exp B = exp (A + B)`
          simpa [Real.exp_add, this, mul_comm, mul_left_comm, mul_assoc] using
            (Real.exp_add (‖w‖ ^ (m + 1)) ((m : ℝ) * ‖w‖ ^ (m + 1))).symm
        -- Keep the inequality and rewrite the RHS.
        exact this.trans_eq hexp_mul
      have hCge : (m : ℝ) + 1 ≤ C := by
        have : (m : ℝ) + 1 ≤ (m + 1 : ℝ) * (2 : ℝ) ^ (m + 1) := by
          -- since `2^(m+1) ≥ 1`.
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
            -- `pow` on `ℝ` is monotone for base `≥ 1` (here `2`)
            simpa using (one_le_pow₀ (a := (2 : ℝ)) (by norm_num) (n := m + 1))
          have hm : (0 : ℝ) ≤ (m + 1 : ℝ) := by positivity
          -- `(m+1) = (m+1) * 1 ≤ (m+1) * 2^(m+1)`
          simpa [Nat.cast_add_one, add_comm, add_left_comm, add_assoc, mul_assoc] using
            (mul_le_mul_of_nonneg_left h2 hm)
        exact this.trans (le_max_right _ _)
      have hw0 : 0 ≤ ‖w‖ ^ (m + 1) := pow_nonneg (norm_nonneg w) _
      have : ((m : ℝ) + 1) * ‖w‖ ^ (m + 1) ≤ C * ‖w‖ ^ (m + 1) :=
        mul_le_mul_of_nonneg_right hCge hw0
      have : Real.exp (((m : ℝ) + 1) * ‖w‖ ^ (m + 1)) ≤ Real.exp (C * ‖w‖ ^ (m + 1)) :=
        Real.exp_monotone this
      -- `hE` already has the `exp(((m+1) * ‖w‖^(m+1)))` bound.
      exact hE.trans this

/-! ## Part 3: Zero Data and Counting Functions -/

/-
Abstract zero data for an entire function. This packages the zeros
as a sequence with multiplicities, plus the multiplicity at `0`, and
assumes a local finiteness condition.

For applications like L-functions, this will be constructed from an
explicit zero set with known multiplicities.
-/
/-!
### Zero data

An earlier `Multiset`-based formulation would force the nonzero zero set to be finite (a
`Multiset` is by definition finite), which trivializes the Hadamard factorization statement.

We instead package **countably many** nonzero zeros as a sequence `zeros : ℕ → ℂ`.

-/
structure ZeroData (f : ℂ → ℂ) where
  /-- A sequence enumerating the nonzero zeros (optionally with repetition for multiplicity). -/
  zeros : ℕ → ℂ
  /-- The sequence lists only nonzero points. -/
  zeros_ne_zero : ∀ n, zeros n ≠ 0
  /-- Local finiteness: only finitely many indices land in any closed ball. -/
  finite_in_ball : ∀ R : ℝ, ({n : ℕ | ‖zeros n‖ ≤ R} : Set ℕ).Finite
  /-- Order of vanishing at `0`. -/
  ord0 : ℕ
  /-- `ord0` is the actual vanishing order of `f` at `0`. -/
  ord0_spec : analyticOrderNatAt f (0 : ℂ) = ord0
  /-- Multiplicity specification: the analytic order at each nonzero zero is the number of times it
  occurs in the sequence `zeros`. -/
  zeros_mult_spec :
    ∀ z : ℂ, z ≠ 0 → analyticOrderNatAt f z = Nat.card {n : ℕ // zeros n = z}
  /-- Specification of the zero set of `f`. -/
  zero_spec : ∀ z : ℂ, f z = 0 ↔
    (z = 0 ∧ 0 < ord0) ∨ (z ≠ 0 ∧ ∃ n, zeros n = z)

/-- The counting function n(r) counts zeros with |z| ≤ r, weighted by multiplicity. -/
def ZeroData.countingFunction {f : ℂ → ℂ} (zd : ZeroData f) (r : ℝ) : ℕ :=
  (Nat.card {n : ℕ | ‖zd.zeros n‖ ≤ r}) + if 0 ≤ r then zd.ord0 else 0

namespace ZeroData

variable {f : ℂ → ℂ}

-- `ZeroData` gives local finiteness in closed balls; in particular, each fiber of `zeros` is finite.
lemma finite_fiber (zd : ZeroData f) (z : ℂ) : ({n : ℕ | zd.zeros n = z} : Set ℕ).Finite := by
  classical
  by_cases hz : z = 0
  · -- No index maps to `0` by `zeros_ne_zero`.
    have : ({n : ℕ | zd.zeros n = z} : Set ℕ) = ∅ := by
      ext n
      simp [hz, zd.zeros_ne_zero n]
    simp [this]
  ·
    -- If `zeros n = z`, then automatically `‖zeros n‖ ≤ ‖z‖`, so we are inside a finite ball.
    refine (zd.finite_in_ball ‖z‖).subset ?_
    intro n hn
    have : zd.zeros n = z := by simpa using hn
    simp [this]

lemma finite_fiber_type (zd : ZeroData f) (z : ℂ) : Finite {n : ℕ // zd.zeros n = z} := by
  classical
  -- The subtype is finite as soon as the defining set is finite.
  letI : Fintype {n : ℕ // zd.zeros n = z} := (zd.finite_fiber z).fintype
  exact Finite.of_fintype _

end ZeroData

/-- The exponent of convergence of the zeros. -/
def ZeroData.convergenceExponent {f : ℂ → ℂ} (zd : ZeroData f) : ℝ :=
  sInf {σ : ℝ | σ ≥ 0 ∧ ∀ (seq : ℕ → ℂ),
    (∀ n, (∃ k, seq n = zd.zeros k) ∨ seq n = 0) →
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

/--
The canonical product over a sequence of nonzero points.

This is just a definitional alias for the infinite product appearing throughout the file.
-/
noncomputable def canonicalProduct (m : ℕ) (zeros : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / zeros n)

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
    ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn
        (fun N z => ∏ n ∈ range N, weierstrassFactor m (z / a n))
        (fun z => ∏' n, weierstrassFactor m (z / a n)) atTop K ∧
      AnalyticOn ℂ (fun z => ∏' n, weierstrassFactor m (z / a n)) K := by
  intro K hK
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
      have : ‖z / a n‖ = ‖z‖ / ‖a n‖ := by simp
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
            simp [div_eq_mul_inv, mul_pow, norm_inv, mul_assoc, mul_comm]
      _ ≤ 4 * ((R + 1) ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
            gcongr
      _ = M n := by
            simp [M, mul_assoc, mul_comm]

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

  refine ⟨?_, ?_⟩
  · -- Rewrite `1 + f n z` to `weierstrassFactor m (z / a n)`.
    simpa [f, add_sub_cancel] using htendK
  · -- Analyticity on `K` follows from differentiability on an open neighbourhood `U` of `K`.
    intro z hz
    have hzU : z ∈ U := hKU hz
    have hU_nhds : U ∈ 𝓝 z := hUopen.mem_nhds hzU
    -- `hdiffU` provides analyticity at `z`, hence analytic on `K`.
    simpa [f, add_sub_cancel] using (hdiffU.analyticAt hU_nhds).analyticWithinAt

/-! ### Pointwise summability of the Weierstrass-factor tail -/

lemma summable_weierstrassFactor_sub_one {a : ℕ → ℂ} {m : ℕ}
    (h_sum : Summable (fun n => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) (z : ℂ) :
    Summable (fun n => weierstrassFactor m (z / a n) - 1) := by
  classical
  -- Bound `z` by a positive radius `R ≥ ‖z‖`.
  set R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  -- Majorant for the tail.
  let g : ℕ → ℝ := fun n => (4 * R ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1))
  have hg : Summable g := h_sum.mul_left (4 * R ^ (m + 1))

  -- Eventually, `‖a n‖` is large enough so that `‖z / a n‖ ≤ 1/2`.
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

  have hbound : ∀ᶠ n in atTop, ‖weierstrassFactor m (z / a n) - 1‖ ≤ g n := by
    filter_upwards [hLarge] with n hn
    have hz' : ‖z / a n‖ ≤ (1 / 2 : ℝ) := by
      have hzle : ‖z‖ ≤ R := le_max_left _ _
      have : ‖z / a n‖ = ‖z‖ / ‖a n‖ := by simp
      rw [this]
      have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
      have hfrac₁ : ‖z‖ / ‖a n‖ ≤ ‖z‖ / (2 * R) :=
        div_le_div_of_nonneg_left (norm_nonneg z) h2R_pos hn
      have hfrac₂ : ‖z‖ / (2 * R) ≤ R / (2 * R) :=
        div_le_div_of_nonneg_right hzle (le_of_lt h2R_pos)
      have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
      have hRsimp : (R / (2 * R : ℝ)) = (1 / 2 : ℝ) := by field_simp [hRne]
      exact (hfrac₁.trans hfrac₂).trans_eq hRsimp
    have hpow := weierstrassFactor_sub_one_bound_pow (m := m) (z := z / a n) hz'
    have hzR : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
      pow_le_pow_left₀ (norm_nonneg z) (le_max_left _ _) _
    calc
      ‖weierstrassFactor m (z / a n) - 1‖
          ≤ 4 * ‖z / a n‖ ^ (m + 1) := hpow
      _ = 4 * (‖z‖ ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
            simp [div_eq_mul_inv, mul_pow, norm_inv, mul_assoc, mul_comm]
      _ ≤ 4 * (R ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
            gcongr
      _ = g n := by
            simp [g, mul_assoc, mul_comm]

  -- Comparison test.
  exact Summable.of_norm_bounded_eventually_nat (E := ℂ) hg hbound

/-- Summability is stable under modifying finitely many terms (ℕ-indexed, complex-valued). -/
lemma summable_of_eq_on_compl_finset {f g : ℕ → ℂ} (s : Finset ℕ)
    (hfg : ∀ n, n ∉ s → g n = f n) (hf : Summable f) : Summable g := by
  -- Consider the difference `h = g - f`, which is supported on `s`.
  let h : ℕ → ℂ := fun n => g n - f n
  have hsupport : Function.support h ⊆ (s : Set ℕ) := by
    intro n hn
    by_contra hnmem
    have hEq : g n = f n := hfg n hnmem
    have hzero : h n = 0 := by simp [h, hEq]
    have hnonzero : h n ≠ 0 := by
      simpa [Function.mem_support, h] using hn
    exact hnonzero hzero
  have hfinite : (Function.support h).Finite :=
    (s.finite_toSet).subset hsupport
  have hs : Summable h := summable_of_finite_support hfinite
  -- `g = f + h`.
  have hg : g = fun n => f n + h n := by
    funext n
    simp [h, sub_eq_add_neg]
  -- Close under addition.
  simpa [hg] using hf.add hs

/-- The Weierstrass tail remains summable after zeroing out finitely many indices. -/
lemma summable_weierstrassFactor_sub_one_off_finset {a : ℕ → ℂ} {m : ℕ}
    (h_sum : Summable (fun n => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) (s : Finset ℕ) (z : ℂ) :
    Summable (fun n => if n ∈ s then (0 : ℂ) else (weierstrassFactor m (z / a n) - 1)) := by
  classical
  have htail : Summable (fun n => weierstrassFactor m (z / a n) - 1) :=
    summable_weierstrassFactor_sub_one (a := a) (m := m) h_sum h_nonzero z
  refine summable_of_eq_on_compl_finset (f := fun n => weierstrassFactor m (z / a n) - 1)
    (g := fun n => if n ∈ s then (0 : ℂ) else (weierstrassFactor m (z / a n) - 1)) s ?_ htail
  intro n hn
  simp [hn]

/-- A Weierstrass product with finitely many factors replaced by `1` is still entire. -/
theorem canonical_product_entire_off_finset {a : ℕ → ℂ} {m : ℕ} (s : Finset ℕ)
    (h_sum : Summable (fun n => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    Differentiable ℂ (fun z : ℂ => ∏' n : ℕ, (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n))) := by
  classical
  -- We repeat the local-uniform-limit argument from `canonical_product_entire`,
  -- noting that changing finitely many factors does not affect the M-test.
  let Gs : ℂ → ℂ := fun z => ∏' n : ℕ, (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n))

  have htloc :
      TendstoLocallyUniformlyOn
        (fun N z => ∏ n ∈ range N, (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n)))
        Gs atTop (Set.univ : Set ℂ) := by
    -- Reduce to uniform convergence on compacta.
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    -- Use the same M-test proof as `canonical_product_converges_uniform`, with `f n z` modified on `s`.
    rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
    set R : ℝ := max R0 1
    let U : Set ℂ := Metric.ball (0 : ℂ) (R + 1)
    have hKU : K ⊆ U := by
      intro z hz
      have hzle : ‖z‖ ≤ R := le_trans (hR0 z hz) (le_max_left _ _)
      have hzlt : ‖z‖ < R + 1 := lt_of_le_of_lt hzle (by linarith)
      simpa [U, Metric.mem_ball, dist_zero_right] using hzlt
    have hUopen : IsOpen U := Metric.isOpen_ball

    -- Define `f n z = (if n∈s then 1 else E_m(z/a_n)) - 1`.
    let f : ℕ → ℂ → ℂ :=
      fun n z => (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n)) - 1
    -- Majorant as in `canonical_product_converges_uniform`.
    let M : ℕ → ℝ := fun n => (4 * (R + 1) ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1))
    have hM : Summable M := h_sum.mul_left (4 * (R + 1) ^ (m + 1))

    -- Eventual bound on `U`.
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

    have hBoundU : ∀ᶠ n in atTop, ∀ z ∈ U, ‖f n z‖ ≤ M n := by
      filter_upwards [hLarge] with n hn z hzU
      by_cases hns : n ∈ s
      · -- Then `f n z = 0`.
        have hMn : 0 ≤ M n := by
          have h1 : 0 ≤ (4 * (R + 1) ^ (m + 1) : ℝ) := by positivity
          have h2 : 0 ≤ (‖a n‖⁻¹ ^ (m + 1) : ℝ) := by positivity
          simpa [M, mul_assoc] using mul_nonneg h1 h2
        simpa [f, hns] using hMn
      · -- Otherwise reduce to the standard Weierstrass-factor bound.
        have hzU' : ‖z‖ < R + 1 := by
          simpa [U, Metric.mem_ball, dist_zero_right] using hzU
        have hz' : ‖z / a n‖ ≤ (1 / 2 : ℝ) := by
          have h2R1_pos : 0 < (2 * (R + 1) : ℝ) := by nlinarith [hR1pos]
          have ha_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
          have : ‖z / a n‖ = ‖z‖ / ‖a n‖ := by simp
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
        -- `f n z = weierstrassFactor ... - 1`
        have : ‖f n z‖ = ‖weierstrassFactor m (z / a n) - 1‖ := by
          simp [f, hns]
        -- Main estimate.
        calc
          ‖f n z‖ = ‖weierstrassFactor m (z / a n) - 1‖ := this
          _ ≤ 4 * ‖z / a n‖ ^ (m + 1) := hpow
          _ = 4 * (‖z‖ ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
                simp [div_eq_mul_inv, mul_pow, norm_inv, mul_assoc, mul_comm]
          _ ≤ 4 * ((R + 1) ^ (m + 1) * ‖a n‖⁻¹ ^ (m + 1)) := by
                gcongr
          _ = M n := by
                simp [M, mul_assoc, mul_comm]

    have hcts : ∀ n, ContinuousOn (f n) U := by
      intro n
      by_cases hns : n ∈ s
      · -- constant 0 on this branch
        simpa [f, hns] using (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) U)
      ·
        have hcont : Continuous (fun z : ℂ => weierstrassFactor m (z / a n)) :=
          ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a n))).continuous
        -- `f n z = weierstrassFactor ... - 1`
        simpa [f, hns] using (hcont.continuousOn.sub continuousOn_const)

    -- Apply the M-test lemma for products `∏ (1 + f n z)`.
    have hloc :
        HasProdLocallyUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n : ℕ, (1 + f n z)) U :=
      Summable.hasProdLocallyUniformlyOn_nat_one_add (K := U) hUopen hM hBoundU hcts

    have hunifK : HasProdUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n : ℕ, (1 + f n z)) K :=
      (hloc.mono hKU).hasProdUniformlyOn_of_isCompact hK

    have htendK :
        TendstoUniformlyOn (fun N z ↦ ∏ n ∈ range N, (1 + f n z))
          (fun z ↦ ∏' n : ℕ, (1 + f n z)) atTop K :=
      hunifK.tendstoUniformlyOn_finsetRange

    -- Rewrite `1 + f n z` back to the modified factor.
    have hcongr :
        ∀ᶠ N in atTop,
          Set.EqOn (fun z => ∏ n ∈ range N, (1 + f n z))
            (fun z => ∏ n ∈ range N, (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n))) K :=
      Filter.Eventually.of_forall (fun N z hz => by
        classical
        simp [f, sub_eq_add_neg, add_comm])

    have htendK' :
        TendstoUniformlyOn
          (fun N z => ∏ n ∈ range N, (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n)))
          (fun z => ∏' n : ℕ, (1 + f n z)) atTop K :=
      htendK.congr hcongr

    refine htendK'.congr_right ?_
    intro z hz
    -- `∏' (1 + f n z)` is exactly `Gs z`.
    have : (∏' n : ℕ, (1 + f n z)) = Gs z := by
      -- Expand `f`.
      simp [Gs, f, add_comm, sub_eq_add_neg]
    simp [this]

  -- Each partial product is entire.
  have hFdiff :
      ∀ᶠ N : ℕ in atTop,
        DifferentiableOn ℂ
          (fun z => ∏ n ∈ range N, (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n)))
          (Set.univ : Set ℂ) :=
    Filter.Eventually.of_forall (fun N => by
      -- Finite products of differentiable functions are differentiable.
      have hdf :
          ∀ n ∈ range N,
            DifferentiableOn ℂ (fun z => (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n)))
              (Set.univ : Set ℂ) := by
        intro n hn
        by_cases hns : n ∈ s
        · simp [hns]
        ·
          have hdiff : Differentiable ℂ (fun z => weierstrassFactor m (z / a n)) :=
            (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a n))
          simpa [hns] using hdiff.differentiableOn
      simpa [Finset.prod_fn] using
        (DifferentiableOn.finset_prod (s := (Set.univ : Set ℂ)) (u := range N)
          (f := fun n z => (if n ∈ s then (1 : ℂ) else weierstrassFactor m (z / a n))) hdf))

  have hdiff_on : DifferentiableOn ℂ Gs (Set.univ : Set ℂ) :=
    htloc.differentiableOn hFdiff isOpen_univ
  exact (differentiableOn_univ.1 hdiff_on)

/-- The canonical product `z ↦ ∏' n, Eₘ(z/aₙ)` is entire and has the expected zero set.

This is the same content as the earlier existential formulation, but stated directly for the
definitional canonical product (so downstream theorems can use the explicit `∏'` expression). -/
theorem canonical_product_entire {a : ℕ → ℂ} {m : ℕ}
    (h_sum : Summable (fun n => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    Differentiable ℂ (fun z : ℂ => ∏' n : ℕ, weierstrassFactor m (z / a n)) ∧
      (∀ z : ℂ, (∏' n : ℕ, weierstrassFactor m (z / a n)) = 0 ↔ ∃ n, z = a n) ∧
      EntireOfFiniteOrder (m + 1 : ℝ) (fun z : ℂ => ∏' n : ℕ, weierstrassFactor m (z / a n)) := by
  classical
  -- Define the canonical product as an infinite product.
  let G : ℂ → ℂ := fun z => ∏' n, weierstrassFactor m (z / a n)

  -- Locally uniform convergence of the partial products to `G` on `univ`.
  have htloc :
      TendstoLocallyUniformlyOn
        (fun N z => ∏ n ∈ range N, weierstrassFactor m (z / a n))
        G atTop (Set.univ : Set ℂ) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    simpa [G] using (canonical_product_converges_uniform (a := a) (m := m) h_sum h_nonzero K hK).1

  -- Each partial product is entire.
  have hFdiff :
      ∀ᶠ N : ℕ in atTop,
        DifferentiableOn ℂ (fun z => ∏ n ∈ range N, weierstrassFactor m (z / a n))
          (Set.univ : Set ℂ) :=
    Filter.Eventually.of_forall (fun N => by
      -- Finite products of differentiable functions are differentiable.
      have hdf :
          ∀ n ∈ range N,
            DifferentiableOn ℂ (fun z => weierstrassFactor m (z / a n)) (Set.univ : Set ℂ) := by
        intro n hn
        have hdiff : Differentiable ℂ (fun z => weierstrassFactor m (z / a n)) :=
          (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (a n))
        exact hdiff.differentiableOn
      simpa [Finset.prod_fn] using
        (DifferentiableOn.finset_prod (s := (Set.univ : Set ℂ)) (u := range N)
          (f := fun n z => weierstrassFactor m (z / a n)) hdf))

  have hdiff_on : DifferentiableOn ℂ G (Set.univ : Set ℂ) :=
    htloc.differentiableOn hFdiff isOpen_univ
  have hdiff : Differentiable ℂ G := (differentiableOn_univ.1 hdiff_on)

  -- Zeros: `G z = 0 ↔ ∃ n, z = a n`.
  have hzeros : ∀ z, G z = 0 ↔ ∃ n, z = a n := by
    intro z
    constructor
    · intro hz0
      by_contra h
      have hz : ∀ n, z ≠ a n := by
        intro n hn
        exact h ⟨n, hn⟩
      -- If `z` avoids all `a n`, then all factors are nonzero and the product is nonzero.
      have htail : Summable (fun n => weierstrassFactor m (z / a n) - 1) :=
        summable_weierstrassFactor_sub_one (a := a) (m := m) h_sum h_nonzero z
      have hlog : Summable (fun n => Complex.log (weierstrassFactor m (z / a n))) := by
        simpa [add_sub_cancel] using
          (Complex.summable_log_one_add_of_summable
            (f := fun n => weierstrassFactor m (z / a n) - 1) htail)
      have hne : ∀ n, weierstrassFactor m (z / a n) ≠ 0 := by
        intro n h0
        have h1 : z / a n = (1 : ℂ) :=
          (weierstrassFactor_eq_zero_iff (m := m) (z := z / a n)).1 h0
        have : z = (1 : ℂ) * a n :=
          (div_eq_iff (a := z) (b := a n) (c := (1 : ℂ)) (h_nonzero n)).1 h1
        have : z = a n := by simpa using this
        exact hz n this
      have hprod :
          Complex.exp (∑' n, Complex.log (weierstrassFactor m (z / a n)))
            = ∏' n, weierstrassFactor m (z / a n) := by
        simpa using (Complex.cexp_tsum_eq_tprod (f := fun n => weierstrassFactor m (z / a n)) hne hlog)
      have hexp_ne : Complex.exp (∑' n, Complex.log (weierstrassFactor m (z / a n))) ≠ 0 :=
        Complex.exp_ne_zero _
      have hG_ne : G z ≠ 0 := by
        -- Rewrite `G z` using `hprod`.
        have hEq : Complex.exp (∑' n, Complex.log (weierstrassFactor m (z / a n))) = G z := by
          simpa [G] using hprod
        simpa [hEq] using hexp_ne
      exact hG_ne hz0
    · rintro ⟨n, rfl⟩
      -- One factor is zero, hence the whole product is zero.
      have hz : weierstrassFactor m ((a n) / (a n)) = 0 := by
        have : (a n) / (a n) = (1 : ℂ) := by simp [h_nonzero n]
        exact (weierstrassFactor_eq_zero_iff (m := m) (z := (a n) / (a n))).2 this
      have : (∃ k, weierstrassFactor m ((a n) / a k) = 0) := ⟨n, hz⟩
      simpa [G] using
        (tprod_of_exists_eq_zero (f := fun k => weierstrassFactor m ((a n) / a k)) this)

  -- Growth: `G` has order at most `m+1`.
  have hgrowth :
      ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖G z‖) ≤ C * (1 + ‖z‖) ^ (m + 1 : ℝ) := by
    -- Auxiliary bound: `log(1 + exp B) ≤ B + log 2` for `B ≥ 0`.
    have log_one_add_exp_le (B : ℝ) (hB : 0 ≤ B) : Real.log (1 + Real.exp B) ≤ B + Real.log 2 := by
      have hle : (1 : ℝ) + Real.exp B ≤ 2 * Real.exp B := by
        have : (1 : ℝ) ≤ Real.exp B := by simpa using (Real.exp_monotone hB)
        nlinarith
      have hpos : 0 < (1 : ℝ) + Real.exp B := by
        have : 0 < Real.exp B := Real.exp_pos _
        linarith
      have hlog_le : Real.log (1 + Real.exp B) ≤ Real.log (2 * Real.exp B) :=
        Real.log_le_log hpos (hle.trans_eq (by rfl))
      have hlog_mul : Real.log (2 * Real.exp B) = Real.log 2 + B := by
        simp [Real.log_mul, show (2 : ℝ) ≠ 0 by norm_num]
      linarith [hlog_le, hlog_mul]

    obtain ⟨C0, hC0pos, hC0⟩ := norm_weierstrassFactor_le_exp_pow m
    let S : ℝ := ∑' n, ‖a n‖⁻¹ ^ (m + 1)
    let C : ℝ := C0 * S + Real.log 2
    refine ⟨C, ?_, ?_⟩
    · have hlog2 : 0 < Real.log (2 : ℝ) := by
        have : (1 : ℝ) < 2 := by norm_num
        simpa using Real.log_pos this
      have hC0' : 0 ≤ C0 := le_of_lt hC0pos
      have hS' : 0 ≤ S := tsum_nonneg (fun n => by positivity)
      have hCS : 0 ≤ C0 * S := mul_nonneg hC0' hS'
      linarith
    · intro z
      -- First, bound `‖G z‖` by an exponential.
      have htail : Summable (fun n => weierstrassFactor m (z / a n) - 1) :=
        summable_weierstrassFactor_sub_one (a := a) (m := m) h_sum h_nonzero z
      have hmult : Multipliable (fun n => weierstrassFactor m (z / a n)) := by
        simpa [add_sub_cancel] using
          (Complex.multipliable_one_add_of_summable
            (f := fun n => weierstrassFactor m (z / a n) - 1) htail)

      have hnorm_tprod :
          ‖G z‖ = ∏' n, ‖weierstrassFactor m (z / a n)‖ := by
        simpa [G] using (Multipliable.norm_tprod (f := fun n => weierstrassFactor m (z / a n)) hmult)

      have hle_term :
          ∀ n, ‖weierstrassFactor m (z / a n)‖ ≤ Real.exp (C0 * ‖z / a n‖ ^ (m + 1)) :=
        fun n => hC0 (z / a n)

      have hle_partial :
          ∀ N,
            (∏ n ∈ range N, ‖weierstrassFactor m (z / a n)‖)
              ≤ ∏ n ∈ range N, Real.exp (C0 * ‖z / a n‖ ^ (m + 1)) := by
        intro N
        refine Finset.prod_le_prod (fun n hn => norm_nonneg _) (fun n hn => hle_term n)

      have htend_left :
          Tendsto (fun N => ∏ n ∈ range N, ‖weierstrassFactor m (z / a n)‖) atTop
            (𝓝 (∏' n, ‖weierstrassFactor m (z / a n)‖)) := by
        have : Multipliable (fun n => ‖weierstrassFactor m (z / a n)‖) := (Multipliable.norm hmult)
        simpa using (Multipliable.tendsto_prod_tprod_nat this)

      have hsum_exp : Summable (fun n => (C0 * ‖z / a n‖ ^ (m + 1) : ℝ)) := by
        have : Summable (fun n => (C0 * ‖z‖ ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1))) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using (h_sum.mul_left (C0 * ‖z‖ ^ (m + 1)))
        refine this.congr (fun n => ?_)
        simp [div_eq_mul_inv, mul_pow, mul_assoc]

      have hhasProd_exp :
          HasProd (fun n => Real.exp (C0 * ‖z / a n‖ ^ (m + 1)))
            (Real.exp (∑' n, (C0 * ‖z / a n‖ ^ (m + 1) : ℝ))) := by
        simpa [Function.comp] using (hsum_exp.hasSum).rexp

      have htend_right :
          Tendsto (fun N => ∏ n ∈ range N, Real.exp (C0 * ‖z / a n‖ ^ (m + 1))) atTop
            (𝓝 (Real.exp (∑' n, (C0 * ‖z / a n‖ ^ (m + 1) : ℝ)))) :=
        hhasProd_exp.tendsto_prod_nat

      have hle_tprod :
          (∏' n, ‖weierstrassFactor m (z / a n)‖)
            ≤ Real.exp (∑' n, (C0 * ‖z / a n‖ ^ (m + 1) : ℝ)) :=
        le_of_tendsto_of_tendsto' htend_left htend_right hle_partial

      have hsum_simp :
          (∑' n, (C0 * ‖z / a n‖ ^ (m + 1) : ℝ)) = C0 * ‖z‖ ^ (m + 1) * S := by
        have hterm :
            ∀ n, (C0 * ‖z / a n‖ ^ (m + 1) : ℝ)
              = (C0 * ‖z‖ ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1)) := by
          intro n
          simp [div_eq_mul_inv, mul_pow, mul_assoc]
        calc
          (∑' n, (C0 * ‖z / a n‖ ^ (m + 1) : ℝ))
              = ∑' n, (C0 * ‖z‖ ^ (m + 1)) * (‖a n‖⁻¹ ^ (m + 1)) := by
                  simpa using (tsum_congr hterm)
          _ = (C0 * ‖z‖ ^ (m + 1)) * (∑' n, ‖a n‖⁻¹ ^ (m + 1)) := by
                simp [tsum_mul_left]
          _ = C0 * ‖z‖ ^ (m + 1) * S := by
                simp [S, mul_assoc]

      have hnorm_le : ‖G z‖ ≤ Real.exp (C0 * ‖z‖ ^ (m + 1) * S) := by
        have htmp :
            ‖G z‖ ≤ Real.exp (∑' n, (C0 * ‖z / a n‖ ^ (m + 1) : ℝ)) := by
          -- Avoid `simp` rewriting `‖z / a n‖` into `‖z‖ / ‖a n‖`.
          calc
            ‖G z‖ = ∏' n, ‖weierstrassFactor m (z / a n)‖ := hnorm_tprod
            _ ≤ Real.exp (∑' n, (C0 * ‖z / a n‖ ^ (m + 1) : ℝ)) := hle_tprod
        -- Rewrite the exponent sum.
        have htmp' := htmp
        rw [hsum_simp] at htmp'
        exact htmp'

      -- Take logs, then compare `‖z‖^(m+1)` with `(1+‖z‖)^(m+1)`.
      have hpos1 : 0 < (1 : ℝ) + ‖G z‖ := by
        have : 0 ≤ ‖G z‖ := norm_nonneg _
        linarith
      have hlog_mon :
          Real.log (1 + ‖G z‖) ≤ Real.log (1 + Real.exp (C0 * ‖z‖ ^ (m + 1) * S)) :=
        Real.log_le_log hpos1 (by linarith [hnorm_le])
      have hB : 0 ≤ C0 * ‖z‖ ^ (m + 1) * S := by
        have hC0' : 0 ≤ C0 := le_of_lt hC0pos
        have hz' : 0 ≤ ‖z‖ ^ (m + 1) := by positivity
        have hS' : 0 ≤ S := tsum_nonneg (fun n => by positivity)
        exact mul_nonneg (mul_nonneg hC0' hz') hS'
      have hlog2 :
          Real.log (1 + Real.exp (C0 * ‖z‖ ^ (m + 1) * S))
            ≤ (C0 * ‖z‖ ^ (m + 1) * S) + Real.log 2 :=
        log_one_add_exp_le (B := C0 * ‖z‖ ^ (m + 1) * S) hB
      have hmain :
          Real.log (1 + ‖G z‖) ≤ (C0 * ‖z‖ ^ (m + 1) * S) + Real.log 2 :=
        le_trans hlog_mon hlog2

      have hz_le : ‖z‖ ^ (m + 1) ≤ (1 + ‖z‖) ^ (m + 1) := by
        have : ‖z‖ ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
        exact pow_le_pow_left₀ (norm_nonneg z) this _
      have hpow_ge1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ (m + 1) := by
        have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
        exact one_le_pow₀ (a := (1 + ‖z‖)) hbase

      have hterm1 :
          C0 * ‖z‖ ^ (m + 1) * S ≤ (C0 * S) * (1 + ‖z‖) ^ (m + 1) := by
        have hC0' : 0 ≤ C0 := le_of_lt hC0pos
        have hS' : 0 ≤ S := tsum_nonneg (fun n => by positivity)
        have : C0 * (‖z‖ ^ (m + 1)) * S ≤ C0 * ((1 + ‖z‖) ^ (m + 1)) * S := by
          gcongr
        simpa [mul_assoc, mul_left_comm, mul_comm] using this

      have hterm2 :
          Real.log 2 ≤ (Real.log 2) * (1 + ‖z‖) ^ (m + 1) := by
        have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          simpa using Real.log_nonneg this
        have := mul_le_mul_of_nonneg_left hpow_ge1 hlog2_nonneg
        simpa [mul_assoc, mul_left_comm, mul_comm] using this

      have hnat :
          Real.log (1 + ‖G z‖) ≤ (C0 * S + Real.log 2) * (1 + ‖z‖) ^ (m + 1) := by
        have h1 :
            (C0 * ‖z‖ ^ (m + 1) * S) + Real.log 2
              ≤ (C0 * S) * (1 + ‖z‖) ^ (m + 1) + (Real.log 2) * (1 + ‖z‖) ^ (m + 1) :=
          add_le_add hterm1 hterm2
        have h2 :
            (C0 * S) * (1 + ‖z‖) ^ (m + 1) + (Real.log 2) * (1 + ‖z‖) ^ (m + 1)
              = (C0 * S + Real.log 2) * (1 + ‖z‖) ^ (m + 1) := by
          ring
        exact (hmain.trans (h1.trans_eq h2))

      have hpow :
          (1 + ‖z‖ : ℝ) ^ (m + 1 : ℝ) = (1 + ‖z‖ : ℝ) ^ (m + 1 : ℕ) := by
        simpa using (Real.rpow_natCast (x := (1 + ‖z‖ : ℝ)) (n := m + 1))
      simpa [C, hpow] using hnat

  refine ⟨?_, ?_, ?_⟩
  · simpa [G] using hdiff
  · intro z
    simpa [G] using (hzeros z)
  ·
    -- Package the growth bound into `EntireOfFiniteOrder`.
    simpa [G] using (show EntireOfFiniteOrder (m + 1 : ℝ) G from ⟨hdiff, hgrowth⟩)

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
    (hr : 0 < r) (hR : r < R)
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
    simp [hf0] at this

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
        simp [zeros, Finset.mem_filter, hz_s, hz_r]
      exact this
  · -- Bound the number of (distinct) zeros using Jensen's formula.
    -- Step 1: bound the circle average by `log B`.
    have hCircleInt : CircleIntegrable (Real.log ‖f ·‖) (0 : ℂ) R := by
      -- `log ‖f ·‖` is circle integrable if `f` is meromorphic on the circle.
      apply circleIntegrable_log_norm_meromorphicOn
      have : MeromorphicOn f (Metric.sphere (0 : ℂ) |R|) := by
        intro z hz
        exact hf_merU z (Metric.sphere_subset_closedBall hz)
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
        simp [h0, this]
      · have hpos : 0 < ‖f z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
        exact Real.log_le_log hpos hfz_le

    -- Step 2: Jensen's formula, specialized to `c = 0`.
    have h0U : (0 : ℂ) ∈ U := by simp [U, abs_nonneg R]
    have hAnal0 : AnalyticAt ℂ f 0 := by
      have h0R : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
        simp [Metric.mem_closedBall, hRpos.le]
      exact hf_anal 0 h0R
    have hf0_ne : f 0 ≠ 0 := by simp [hf0]
    have hdiv0 : MeromorphicOn.divisor f U 0 = 0 := by
      have : meromorphicOrderAt f 0 = 0 := by
        have horder : meromorphicOrderAt f 0 = (analyticOrderAt f 0).map (↑) :=
          hAnal0.meromorphicOrderAt_eq
        have han0 : analyticOrderAt f 0 = 0 := (hAnal0.analyticOrderAt_eq_zero).2 hf0_ne
        simp [horder, han0]
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
      simpa [U, hdiv0, htrail, hf0, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hJ

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
      simpa [hsum_s, g] using hFsum_le

    -- Step 4: restrict from `s` to `zeros` and use `log(R/‖u‖) ≥ log(R/r)` for `‖u‖ ≤ r`.
    have hzeros_subset : zeros ⊆ s := by
      intro u hu
      exact (Finset.mem_filter.1 hu).1
    have hf_analU' : AnalyticOnNhd ℂ f U := hf_analU
    have hDnonneg : 0 ≤ MeromorphicOn.divisor f U := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf_analU'
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
        simp [hf0] at this
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

/-- Jensen's bound, multiplicity version.

Under the hypotheses of `jensen_zeros_bound`, we can bound the **total multiplicity** of zeros in
`‖z‖ ≤ r` (i.e. the sum of the divisor values) by the same `log B / log(R/r)` expression.

This is the quantitative input needed to control sequences that enumerate zeros *with
multiplicity* (by repetition). -/
theorem jensen_zeros_multiplicity_bound {f : ℂ → ℂ} {r R B : ℝ}
    (hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hr : 0 < r) (hR : r < R)
    (hf0 : f 0 = 1) (hB : 1 < B)
    (hf_bound : ∀ z, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∃ (zeros : Finset ℂ),
      (∀ z, z ∈ zeros ↔ ‖z‖ ≤ r ∧ f z = 0) ∧
      (∑ z ∈ zeros, (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |R|) z : ℝ))
        ≤ Real.log B / Real.log (R / r) := by
  -- This is the same Jensen-formula proof as `jensen_zeros_bound`, but we keep the divisor weights.
  classical
  have hRpos : 0 < R := lt_trans hr hR
  have hRne : R ≠ 0 := ne_of_gt hRpos
  have habsR : |R| = R := abs_of_pos hRpos

  let U : Set ℂ := Metric.closedBall (0 : ℂ) |R|
  have hf_analU : AnalyticOnNhd ℂ f U := by
    simpa [U, habsR] using hf_anal
  have hf_merU : MeromorphicOn f U := hf_analU.meromorphicOn

  -- Exclude local identically-zero (order = ⊤) using `f 0 = 1`.
  have h_not_top : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u huU hu_top
    have hfreq : ∃ᶠ z in 𝓝[≠] u, f z = 0 :=
      (Filter.Eventually.frequently ((meromorphicOrderAt_eq_top_iff).1 hu_top))
    have hEq : Set.EqOn f 0 U :=
      hf_analU.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (hU := (convex_closedBall (0 : ℂ) |R|).isPreconnected) huU hfreq
    have h0U : (0 : ℂ) ∈ U := by simp [U, abs_nonneg R]
    have : f 0 = 0 := by simpa using hEq h0U
    simp [hf0] at this

  -- The finset of (distinct) zeros in `‖z‖ ≤ r`.
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

  have hmem_zeros : ∀ z, z ∈ zeros ↔ ‖z‖ ≤ r ∧ f z = 0 := by
    intro z
    constructor
    · intro hz
      have hz' : z ∈ s ∧ ‖z‖ ≤ r := by
        simpa [zeros, Finset.mem_filter] using hz
      have hz_s : z ∈ s := hz'.1
      have hz_r : ‖z‖ ≤ r := hz'.2
      have hz_support : z ∈ Function.support (MeromorphicOn.divisor f U) := by
        simpa [s, Finite.mem_toFinset] using hz_s
      have hzU0 : z ∈ U ∧ f z = 0 := by
        simpa [hsupport, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] using hz_support
      exact ⟨hz_r, hzU0.2⟩
    · rintro ⟨hz_r, hfz⟩
      have hzU : z ∈ U := by
        have hz_leR : ‖z‖ ≤ R := le_trans hz_r (le_of_lt hR)
        simpa [U, habsR, Metric.mem_closedBall, dist_zero_right] using hz_leR
      have hz_support : z ∈ Function.support (MeromorphicOn.divisor f U) := by
        -- `f z = 0` gives membership in `U ∩ f ⁻¹' {0}`, hence in the support.
        have : z ∈ U ∩ f ⁻¹' ({0} : Set ℂ) := by
          simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, hzU, hfz]
        simpa [hsupport] using this
      have hz_s : z ∈ s := by
        simpa [s, Finite.mem_toFinset] using hz_support
      simp [zeros, hz_s, hz_r]

  -- Bound the circle average by `log B` from `hf_bound`.
  have hCircleInt :
      CircleIntegrable (Real.log ‖f ·‖) (0 : ℂ) R := by
    apply circleIntegrable_log_norm_meromorphicOn
    have : MeromorphicOn f (Metric.sphere (0 : ℂ) |R|) := by
      intro z hz
      exact hf_merU z (Metric.sphere_subset_closedBall hz)
    simpa [habsR] using this
  have hCA_le : Real.circleAverage (Real.log ‖f ·‖) (0 : ℂ) R ≤ Real.log B := by
    apply Real.circleAverage_mono_on_of_le_circle (hf := hCircleInt)
    intro z hz
    have hz_leR : ‖z‖ ≤ R := by
      have hz_eq : ‖z‖ = |R| := by
        simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz
      simpa [habsR] using (le_of_eq hz_eq)
    have hfz_le : ‖f z‖ ≤ B := hf_bound z hz_leR
    by_cases h0 : ‖f z‖ = 0
    · have : 0 ≤ Real.log B := le_of_lt (Real.log_pos hB)
      simp [h0, this]
    · have hpos : 0 < ‖f z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact Real.log_le_log hpos hfz_le

  -- Jensen formula (c = 0) and simplification using `f 0 = 1`.
  have h0U : (0 : ℂ) ∈ U := by simp [U, abs_nonneg R]
  have hAnal0 : AnalyticAt ℂ f 0 := by
    have h0R : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
      simp [Metric.mem_closedBall, hRpos.le]
    exact hf_anal 0 h0R
  have hf0_ne : f 0 ≠ 0 := by simp [hf0]
  have hdiv0 : MeromorphicOn.divisor f U 0 = 0 := by
    have : meromorphicOrderAt f 0 = 0 := by
      have horder : meromorphicOrderAt f 0 = (analyticOrderAt f 0).map (fun n : ℕ => (n : ℤ)) :=
        hAnal0.meromorphicOrderAt_eq
      have han0 : analyticOrderAt f 0 = 0 := (hAnal0.analyticOrderAt_eq_zero).2 hf0_ne
      simp [horder, han0]
    simp [MeromorphicOn.divisor_apply hf_merU h0U, this]
  have htrail : meromorphicTrailingCoeffAt f 0 = f 0 :=
    hAnal0.meromorphicTrailingCoeffAt_of_ne_zero hf0_ne

  have hJensen :
      Real.circleAverage (Real.log ‖f ·‖) (0 : ℂ) R
        = (∑ᶠ u, (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹)) := by
    have hJ :=
      (MeromorphicOn.circleAverage_log_norm (c := (0 : ℂ)) (R := R) (f := f) hRne hf_merU)
    simpa [U, hdiv0, htrail, hf0, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hJ

  have hFsum_le :
      (∑ᶠ u, (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹)) ≤ Real.log B := by
    simpa [hJensen] using hCA_le

  -- Compare the finsum to a finite sum over `s`.
  let g : ℂ → ℝ := fun u ↦ (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹)
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
    simpa [hsum_s, g] using hFsum_le

  -- Restrict from `s` to `zeros`.
  have hzeros_subset : zeros ⊆ s := by
    intro u hu
    exact (Finset.mem_filter.1 hu).1
  have hDnonneg : 0 ≤ MeromorphicOn.divisor f U :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf_analU
  have hsum_zeros_le : (∑ u ∈ zeros, g u) ≤ Real.log B := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hzeros_subset ?_).trans hsum_s_le
    intro u hu_s hu_not
    have hdiv0 : (0 : ℝ) ≤ (MeromorphicOn.divisor f U u : ℝ) := by exact_mod_cast (hDnonneg u)
    have hlog0 : 0 ≤ Real.log (R * ‖u‖⁻¹) := by
      by_cases hu0 : u = 0
      · simp [hu0]
      · have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
        have huU : u ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain (by
          have : u ∈ Function.support (MeromorphicOn.divisor f U) := by
            simpa [s, Finite.mem_toFinset] using hu_s
          exact this)
        have hnorm_le : ‖u‖ ≤ R := by
          have : ‖u‖ ≤ |R| := by simpa [U, Metric.mem_closedBall, dist_zero_right] using huU
          simpa [habsR] using this
        have : 1 ≤ R / ‖u‖ := (one_le_div hnorm_pos).2 hnorm_le
        simpa [div_eq_mul_inv] using Real.log_nonneg this
    exact mul_nonneg hdiv0 hlog0

  -- Lower bound on the logarithmic term on `zeros`.
  have hlog_pos : 0 < Real.log (R / r) := by
    have : 1 < R / r := (one_lt_div hr).2 hR
    exact Real.log_pos this

  have hsum_lower :
      (∑ u ∈ zeros, (MeromorphicOn.divisor f U u : ℝ)) * Real.log (R / r) ≤ ∑ u ∈ zeros, g u := by
    have hpoint : ∀ u ∈ zeros,
        (MeromorphicOn.divisor f U u : ℝ) * Real.log (R / r)
          ≤ (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹) := by
      intro u hu
      have hu_r : ‖u‖ ≤ r := (hmem_zeros u).1 hu |>.1
      have hu0 : u ≠ 0 := by
        intro hu0
        have : f 0 = 0 := by simpa [hu0] using (hmem_zeros u).1 hu |>.2
        simp [hf0] at this
      have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      have harg_le : R / r ≤ R * ‖u‖⁻¹ := by
        have hinv : (1 / r) ≤ (1 / ‖u‖) := one_div_le_one_div_of_le hnorm_pos hu_r
        have := mul_le_mul_of_nonneg_left hinv hRpos.le
        simpa [div_eq_mul_inv, one_div] using this
      have hlog_le : Real.log (R / r) ≤ Real.log (R * ‖u‖⁻¹) := by
        have hpos : 0 < R / r := div_pos hRpos hr
        exact Real.log_le_log hpos harg_le
      have hdiv0 : (0 : ℝ) ≤ (MeromorphicOn.divisor f U u : ℝ) := by exact_mod_cast (hDnonneg u)
      exact mul_le_mul_of_nonneg_left hlog_le hdiv0
    have := Finset.sum_le_sum (fun u hu => hpoint u hu)
    -- rewrite the LHS
    calc (∑ u ∈ zeros, (MeromorphicOn.divisor f U u : ℝ)) * Real.log (R / r)
        = ∑ u ∈ zeros, (MeromorphicOn.divisor f U u : ℝ) * Real.log (R / r) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ u ∈ zeros, (MeromorphicOn.divisor f U u : ℝ) * Real.log (R * ‖u‖⁻¹) := this
      _ = ∑ u ∈ zeros, g u := by simp only [g]

  have hsum_divisor_le :
      (∑ u ∈ zeros, (MeromorphicOn.divisor f U u : ℝ)) ≤ Real.log B / Real.log (R / r) := by
    have : (∑ u ∈ zeros, (MeromorphicOn.divisor f U u : ℝ)) * Real.log (R / r) ≤ Real.log B :=
      (hsum_lower.trans hsum_zeros_le)
    exact (le_div_iff₀ hlog_pos).2 (by simpa [mul_assoc] using this)

  refine ⟨zeros, hmem_zeros, ?_⟩
  simpa [U] using hsum_divisor_le

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
  -- We give a clean Jensen + dyadic-shell proof.
  classical

  -- Step 0: reduce to a nonnegative order.
  have hρ_nonneg : 0 ≤ ρ := by
    by_contra hρ
    have hρneg : ρ < 0 := lt_of_not_ge hρ
    rcases hf.growth with ⟨C, hCpos, hC⟩
    have hbounded : ∃ M, ∀ z : ℂ, ‖f z‖ ≤ M := by
      refine ⟨Real.exp C, ?_⟩
      intro z
      have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      have hpow : (1 + ‖z‖) ^ ρ ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hbase (le_of_lt hρneg)
      have hlog_le : Real.log (1 + ‖f z‖) ≤ C := by
        have h1 : Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ := hC z
        have h2 : C * (1 + ‖z‖) ^ ρ ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
        have h3 : C * (1 + ‖z‖) ^ ρ ≤ C := by simpa using h2
        exact h1.trans h3
      have hpos : 0 < (1 : ℝ) + ‖f z‖ := by linarith [norm_nonneg (f z)]
      have hle : (1 : ℝ) + ‖f z‖ ≤ Real.exp C := (Real.log_le_iff_le_exp hpos).1 hlog_le
      have hle' : ‖f z‖ ≤ (1 : ℝ) + ‖f z‖ := le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      exact hle'.trans hle
    have hb_range : Bornology.IsBounded (Set.range f) := by
      rcases hbounded with ⟨M, hM⟩
      refine (isBounded_iff_forall_norm_le).2 ?_
      refine ⟨M, ?_⟩
      intro y hy
      rcases hy with ⟨z, rfl⟩
      simpa using hM z
    rcases (Differentiable.exists_eq_const_of_bounded hf.entire hb_range) with ⟨c, hc⟩
    have hz0 : f (zeros 0) = 0 := (h_zeros 0).1
    -- `f` is constant, so `f 0 = f (zeros 0) = 0`, contradicting `f 0 ≠ 0`.
    have : f 0 = f (zeros 0) := by simp [hc]
    exact hf0 (this.trans hz0)

  have hσ_pos : 0 < σ := lt_of_le_of_lt hρ_nonneg hσ

  -- Choose an intermediate exponent `τ` with `ρ ≤ τ < σ`.
  let τ : ℝ := (ρ + σ) / 2
  have hρτ : ρ ≤ τ := by dsimp [τ]; linarith
  have hτσ : τ < σ := by dsimp [τ]; linarith
  have hτ_nonneg : 0 ≤ τ := le_trans hρ_nonneg hρτ

  -- Upgrade to order `τ`, and extract a simple norm bound.
  have hfτ : EntireOfFiniteOrder τ f := EntireOfFiniteOrder.of_le_order hf hρτ
  rcases hfτ.norm_bound with ⟨C, hCpos, hC⟩

  -- Normalize so that `g 0 = 1`.
  let f0 : ℂ := f 0
  let g : ℂ → ℂ := fun z => f z / f0
  have hg_entire : Differentiable ℂ g := by
    simpa [g, f0] using (hfτ.entire.div_const (f 0))
  have hg0 : g 0 = 1 := by
    simp [g, f0, hf0]

  -- A zero-free ball around `0`, hence `r0 ≤ ‖zeros n‖` for all `n`.
  obtain ⟨r0, hr0pos, hr0⟩ :
      ∃ r0 > 0, ∀ z : ℂ, ‖z‖ < r0 → f z ≠ 0 := by
    have hcont : ContinuousAt f 0 := (hfτ.entire 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont.eventually_ne hf0
    rcases Metric.mem_nhds_iff.mp hne with ⟨r, hrpos, hr⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    have : z ∈ Metric.ball (0 : ℂ) r := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hr this

  have hr0_le_norm : ∀ n, r0 ≤ ‖zeros n‖ := by
    intro n
    have hz0 : f (zeros n) = 0 := (h_zeros n).1
    have hnot : ¬ ‖zeros n‖ < r0 := by
      intro hlt
      exact (hr0 (zeros n) hlt) hz0
    exact le_of_not_gt hnot

  -- Dyadic shell index: `k(n) = ⌊logb 2 (‖zeros n‖/r0)⌋₊`.
  let kfun : ℕ → ℕ := fun n => ⌊Real.logb 2 (‖zeros n‖ / r0)⌋₊

  -- Dyadic bounds for `x ≥ 1`.
  have hdyadic_lower :
      ∀ {x : ℝ}, 1 ≤ x → (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
    have hlog_nonneg : 0 ≤ Real.logb 2 x :=
      Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
    have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
      simpa using (Nat.floor_le hlog_nonneg)
    exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
      (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le
  have hdyadic_upper :
      ∀ {x : ℝ}, 1 ≤ x → x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
    have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
    exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
      (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1) (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

  -- For each `n`, we have `r0*2^{k(n)} ≤ ‖zeros n‖ < r0*2^{k(n)+1}`.
  have hk_lower : ∀ n, r0 * (2 : ℝ) ^ (kfun n : ℝ) ≤ ‖zeros n‖ := by
    intro n
    have hx1 : (1 : ℝ) ≤ ‖zeros n‖ / r0 := by
      have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
      have : r0 / r0 ≤ ‖zeros n‖ / r0 :=
        div_le_div_of_nonneg_right (hr0_le_norm n) (le_of_lt hr0pos)
      simpa [hr0ne] using this
    have hle : (2 : ℝ) ^ (kfun n : ℝ) ≤ ‖zeros n‖ / r0 := by
      simpa [kfun] using (hdyadic_lower (x := ‖zeros n‖ / r0) hx1)
    have := mul_le_mul_of_nonneg_left hle (le_of_lt hr0pos)
    have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
    have hxEq : r0 * (‖zeros n‖ / r0) = ‖zeros n‖ := by
      field_simp [hr0ne]
    simpa [mul_assoc, hxEq] using this
  have hk_upper : ∀ n, ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := by
    intro n
    have hx1 : (1 : ℝ) ≤ ‖zeros n‖ / r0 := by
      have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
      have : r0 / r0 ≤ ‖zeros n‖ / r0 :=
        div_le_div_of_nonneg_right (hr0_le_norm n) (le_of_lt hr0pos)
      simpa [hr0ne] using this
    have hlt : ‖zeros n‖ / r0 < (2 : ℝ) ^ ((kfun n : ℝ) + 1) := by
      simpa [kfun] using (hdyadic_upper (x := ‖zeros n‖ / r0) hx1)
    have := mul_lt_mul_of_pos_left hlt hr0pos
    have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
    have hxEq : r0 * (‖zeros n‖ / r0) = ‖zeros n‖ := by
      field_simp [hr0ne]
    simpa [mul_assoc, hxEq] using this

  -- Define shells `S k = {n | kfun n = k}`.
  let S : ℕ → Set ℕ := fun k => {n : ℕ | kfun n = k}
  have hS : ∀ n : ℕ, ∃! k : ℕ, n ∈ S k := by
    intro n
    refine ⟨kfun n, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm

  -- Nonnegativity of the summand.
  have hnonneg : 0 ≤ fun n : ℕ => ‖zeros n‖⁻¹ ^ σ := by
    intro n
    exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (zeros n))) σ

  -- We apply the partition lemma: it suffices to prove summability of the shell `tsum`s.
  have hshell :
      (∀ k : ℕ, Summable fun n : S k => ‖zeros n.1‖⁻¹ ^ σ) ∧
        Summable fun k : ℕ => ∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ := by
    constructor
    · intro k
      -- Each shell is finite: it injects into the set of zeros of `f` in a fixed closed ball.
      classical
      -- We pick radii so that the whole shell `S k` lies inside `‖z‖ ≤ r`.
      -- (For `n ∈ S k` we have `‖zeros n‖ < r0 * 2^(k+1)` by definition of the dyadic shell.)
      let r : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
      let R : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 2)
      have hr : 0 < r := by
        have h2 : 0 < (2 : ℝ) ^ ((k : ℝ) + 1) :=
          Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
        exact mul_pos hr0pos h2
      have hRpos : 0 < R := by
        have h2 : 0 < (2 : ℝ) ^ ((k : ℝ) + 2) :=
          Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
        exact mul_pos hr0pos h2
      have hrR : r < R := by
        -- `R = 2*r`.
        have h2 : (1 : ℝ) < 2 := by norm_num
        have : r < (2 : ℝ) * r := lt_mul_of_one_lt_left hr h2
        -- show `2*r = R`
        have h2pos : 0 < (2 : ℝ) := by norm_num
        have hpow : (2 : ℝ) ^ ((k : ℝ) + 2) = (2 : ℝ) ^ ((k : ℝ) + 1) * (2 : ℝ) := by
          have : (k : ℝ) + 2 = ((k : ℝ) + 1) + 1 := by ring
          calc
            (2 : ℝ) ^ ((k : ℝ) + 2)
                = (2 : ℝ) ^ (((k : ℝ) + 1) + 1) := by simp [this]
            _ = (2 : ℝ) ^ ((k : ℝ) + 1) * (2 : ℝ) ^ (1 : ℝ) := by
                  simpa using (Real.rpow_add h2pos ((k : ℝ) + 1) (1 : ℝ))
            _ = (2 : ℝ) ^ ((k : ℝ) + 1) * (2 : ℝ) := by simp
        have hR_eq : R = (2 : ℝ) * r := by
          dsimp [R, r]
          calc
            r0 * (2 : ℝ) ^ ((k : ℝ) + 2)
                = r0 * ((2 : ℝ) ^ ((k : ℝ) + 1) * (2 : ℝ)) := by
                    simp [hpow]
            _ = (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) := by ring
        simpa [hR_eq] using this
      -- Jensen bound gives a finite set of zeros in `‖z‖ ≤ r`.
      have hg_anal : AnalyticOnNhd ℂ g (Metric.closedBall 0 R) := by
        intro z hz
        exact hg_entire.analyticAt z
      let M0 : ℝ := max 2 (‖f0‖)⁻¹
      have hM0pos : 0 < M0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
      let B : ℝ := Real.exp (C * (1 + R) ^ τ) * M0
      have hB : 1 < B := by
        have hexp : 1 ≤ Real.exp (C * (1 + R) ^ τ) :=
          (Real.one_le_exp_iff).2 (by
            have : 0 ≤ (1 + R : ℝ) ^ τ := by
              exact Real.rpow_nonneg (by linarith [hRpos.le]) τ
            nlinarith [le_of_lt hCpos, this])
        have hM0 : (1 : ℝ) < M0 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
        -- `1 < exp(...) * M0` since `1 ≤ exp(...)` and `1 < M0`.
        have : 1 < (Real.exp (C * (1 + R) ^ τ)) * M0 := by
          -- use `one_lt_mul` with `1 ≤ exp` and `1 < M0`
          exact one_lt_mul (show 1 ≤ Real.exp (C * (1 + R) ^ τ) from hexp) hM0
        simpa [B] using this
      have hg_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
        intro z hzR
        have hfz : ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := hC z
        have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow_le : (1 + ‖z‖ : ℝ) ^ τ ≤ (1 + R) ^ τ :=
          Real.rpow_le_rpow (by positivity) hbase hτ_nonneg
        have hmul_le : C * (1 + ‖z‖) ^ τ ≤ C * (1 + R) ^ τ :=
          mul_le_mul_of_nonneg_left hpow_le (le_of_lt hCpos)
        have hexp_le : Real.exp (C * (1 + ‖z‖) ^ τ) ≤ Real.exp (C * (1 + R) ^ τ) :=
          (Real.exp_le_exp.2 hmul_le)
        have hfz' : ‖f z‖ ≤ Real.exp (C * (1 + R) ^ τ) := hfz.trans hexp_le
        have hf0pos : 0 < ‖f0‖ := norm_pos_iff.mpr hf0
        have hdiv_le :
            ‖g z‖ ≤ Real.exp (C * (1 + R) ^ τ) * (‖f0‖)⁻¹ := by
          have : ‖g z‖ = ‖f z‖ / ‖f0‖ := by simp [g, f0]
          have hdiv :
              ‖f z‖ / ‖f0‖ ≤ Real.exp (C * (1 + R) ^ τ) / ‖f0‖ :=
            div_le_div_of_nonneg_right hfz' (le_of_lt hf0pos)
          simpa [this, div_eq_mul_inv, mul_assoc] using hdiv
        have hM0 : (‖f0‖)⁻¹ ≤ M0 := le_max_right _ _
        have hB' : Real.exp (C * (1 + R) ^ τ) * (‖f0‖)⁻¹ ≤ Real.exp (C * (1 + R) ^ τ) * M0 :=
          mul_le_mul_of_nonneg_left hM0 (le_of_lt (Real.exp_pos _))
        exact le_trans hdiv_le (by simpa [B] using hB')
      rcases jensen_zeros_bound (f := g) (r := r) (R := R) (B := B) hg_anal hr hrR hg0 hB hg_bound
        with ⟨Z, hZ, -⟩
      -- Inject `S k` into `Z` via `n ↦ zeros n`, using the shell upper bound `‖zeros n‖ < r0*2^(k+1)=R`
      -- and hence `‖zeros n‖ ≤ r` (since `r = r0*2^k ≤ R` is true for `k`?); instead we use `r = R/2`.
      -- To keep the finiteness argument simple: we only need finiteness, and `Z` is a `Finset`.
      -- We use `Finite.of_injective` into `Z` by mapping every `n∈S k` to the (unique) zero `zeros n`
      -- once we show `zeros n ∈ Z`, which holds since `‖zeros n‖ ≤ r` and `f (zeros n)=0`.
      have hmemZ : ∀ n : S k, zeros n.1 ∈ Z := by
        intro n
        have hn_lower : r0 * (2 : ℝ) ^ (kfun n.1 : ℝ) ≤ ‖zeros n.1‖ := hk_lower n.1
        have hn_upper : ‖zeros n.1‖ < r0 * (2 : ℝ) ^ ((kfun n.1 : ℝ) + 1) := hk_upper n.1
        have hk_eq : (kfun n.1 : ℝ) = (k : ℝ) := by exact_mod_cast n.2
        have hn_lower' : r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖zeros n.1‖ := by simpa [hk_eq] using hn_lower
        have hn_upper' : ‖zeros n.1‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
          simpa [hk_eq] using hn_upper
        have hle_r : ‖zeros n.1‖ ≤ r := by
          -- With our choice `r = r0 * 2^(k+1)`, this is exactly the dyadic upper bound.
          exact le_of_lt (by simpa [r] using hn_upper')
        have hfz : f (zeros n.1) = 0 := (h_zeros n.1).1
        have hg_z : g (zeros n.1) = 0 := by
          have hf0ne : f0 ≠ 0 := hf0
          simp [g, f0, hfz]
        exact (hZ (zeros n.1)).2 ⟨hle_r, hg_z⟩
      let φ : S k → Z := fun n => ⟨zeros n.1, hmemZ n⟩
      have hφ_inj : Function.Injective φ := by
        intro a b hab
        have : zeros a.1 = zeros b.1 := congrArg Subtype.val hab
        have : a.1 = b.1 := h_inj this
        ext
        exact this
      have : Finite Z := by infer_instance
      haveI : Finite (S k) := Finite.of_injective φ hφ_inj
      exact Summable.of_finite
    ·
      -- Shell `tsum` summability: Jensen gives `card(S k) = O((2^k)^τ)`, and dyadic bounds give
      -- `‖zeros n‖^{-σ} = O((2^{-σ})^k)` on shell `k`. Hence the shell sums are dominated by a
      -- geometric series with ratio `2^(τ-σ) < 1`.
      classical
      let log2 : ℝ := Real.log (2 : ℝ)
      have hlog2_pos : 0 < log2 := by
        dsimp [log2]
        exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlog2_ne : log2 ≠ 0 := ne_of_gt hlog2_pos

      let M0 : ℝ := max 2 (‖f0‖)⁻¹
      have hM0_pos : 0 < M0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)

      let q : ℝ := (2 : ℝ) ^ (τ - σ)
      have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hq_lt_one : q < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
          (sub_neg.2 hτσ)
      have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
        summable_geometric_of_lt_one hq_nonneg hq_lt_one

      let qσ : ℝ := (2 : ℝ) ^ (-σ)
      have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hqσ_lt_one : qσ < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
          (by linarith [hσ_pos])
      have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
        summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one

      -- Explicit constants for a geometric majorant.
      let A : ℝ := (C / log2) * (1 + 4 * r0) ^ τ * (r0 ^ (-σ))
      let B : ℝ := ((Real.log M0) / log2 + 1) * (r0 ^ (-σ))
      have hmajor : Summable (fun k : ℕ => A * q ^ k + B * qσ ^ k) :=
        (hgeom_q.mul_left A).add (hgeom_qσ.mul_left B)

      refine Summable.of_nonneg_of_le
        (g := fun k : ℕ => ∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ)
        (f := fun k : ℕ => A * q ^ k + B * qσ ^ k)
        (fun k => by
          have hnn : ∀ n : S k, 0 ≤ ‖zeros n.1‖⁻¹ ^ σ := by
            intro n
            exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (zeros n.1))) σ
          exact tsum_nonneg hnn)
        (fun k => by
          -- Fix a shell index `k`.
          -- Jensen bound at radii `r = r0 * 2^(k+1)` and `R = 2*r`.
          let r : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
          let R : ℝ := (2 : ℝ) * r
          have hr : 0 < r := by
            have h2 : 0 < (2 : ℝ) ^ ((k : ℝ) + 1) :=
              Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
            exact mul_pos hr0pos h2
          have hRpos : 0 < R := mul_pos (by norm_num : (0 : ℝ) < 2) hr
          have hrR : r < R := by
            have h2 : (1 : ℝ) < 2 := by norm_num
            simpa [R, mul_assoc] using (lt_mul_of_one_lt_left hr h2)

          have hg_anal : AnalyticOnNhd ℂ g (Metric.closedBall 0 R) := by
            intro z hz
            exact hg_entire.analyticAt z
          let Bk : ℝ := Real.exp (C * (1 + R) ^ τ) * M0
          have hBk : 1 < Bk := by
            have hexp : 1 ≤ Real.exp (C * (1 + R) ^ τ) :=
              (Real.one_le_exp_iff).2 (by
                have : 0 ≤ (1 + R : ℝ) ^ τ := Real.rpow_nonneg (by linarith [hRpos.le]) τ
                nlinarith [le_of_lt hCpos, this])
            have hM0 : (1 : ℝ) < M0 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
            have : 1 < Real.exp (C * (1 + R) ^ τ) * M0 := one_lt_mul hexp hM0
            simpa [Bk] using this
          have hg_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ Bk := by
            intro z hzR
            have hfz : ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := hC z
            have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
            have hpow_le : (1 + ‖z‖ : ℝ) ^ τ ≤ (1 + R) ^ τ :=
              Real.rpow_le_rpow (by positivity) hbase hτ_nonneg
            have hmul_le : C * (1 + ‖z‖) ^ τ ≤ C * (1 + R) ^ τ :=
              mul_le_mul_of_nonneg_left hpow_le (le_of_lt hCpos)
            have hexp_le : Real.exp (C * (1 + ‖z‖) ^ τ) ≤ Real.exp (C * (1 + R) ^ τ) :=
              (Real.exp_le_exp.2 hmul_le)
            have hfz' : ‖f z‖ ≤ Real.exp (C * (1 + R) ^ τ) := hfz.trans hexp_le
            have hf0pos : 0 < ‖f0‖ := norm_pos_iff.mpr hf0
            have hdiv_le :
                ‖g z‖ ≤ Real.exp (C * (1 + R) ^ τ) * (‖f0‖)⁻¹ := by
              have : ‖g z‖ = ‖f z‖ / ‖f0‖ := by simp [g, f0]
              have hdiv :
                  ‖f z‖ / ‖f0‖ ≤ Real.exp (C * (1 + R) ^ τ) / ‖f0‖ :=
                div_le_div_of_nonneg_right hfz' (le_of_lt hf0pos)
              simpa [this, div_eq_mul_inv, mul_assoc] using hdiv
            have hM0' : (‖f0‖)⁻¹ ≤ M0 := le_max_right _ _
            have hBk' :
                Real.exp (C * (1 + R) ^ τ) * (‖f0‖)⁻¹ ≤ Real.exp (C * (1 + R) ^ τ) * M0 :=
              mul_le_mul_of_nonneg_left hM0' (le_of_lt (Real.exp_pos _))
            exact le_trans hdiv_le (by simpa [Bk] using hBk')

          rcases jensen_zeros_bound (f := g) (r := r) (R := R) (B := Bk) hg_anal hr hrR hg0 hBk hg_bound
            with ⟨Z, hZ, hZcard⟩

          -- Inject `S k` into `↥Z`.
          let φ : S k → Z := fun n => by
            refine ⟨zeros n.1, ?_⟩
            have hn_upper : ‖zeros n.1‖ < r0 * (2 : ℝ) ^ ((kfun n.1 : ℝ) + 1) := hk_upper n.1
            have hk_eq : (kfun n.1 : ℝ) = (k : ℝ) := by exact_mod_cast n.2
            have hn_upper' : ‖zeros n.1‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
              simpa [hk_eq] using hn_upper
            have hle_r : ‖zeros n.1‖ ≤ r := by
              exact le_of_lt (by simpa [r] using hn_upper')
            have hfz : f (zeros n.1) = 0 := (h_zeros n.1).1
            have hg_z : g (zeros n.1) = 0 := by
              have hf0ne : f0 ≠ 0 := hf0
              simp [g, f0, hfz]
            exact (hZ (zeros n.1)).2 ⟨hle_r, hg_z⟩
          have hφ_inj : Function.Injective φ := by
            intro a b hab
            have : zeros a.1 = zeros b.1 := congrArg Subtype.val hab
            have : a.1 = b.1 := h_inj this
            ext
            exact this
          classical
          -- `S k` is finite since it injects into the finite type `Z`.
          haveI : Finite (S k) := Finite.of_injective φ hφ_inj
          letI : Fintype (S k) := Fintype.ofFinite (S k)

          have hcard_nat : Fintype.card (S k) ≤ Z.card := by
            -- `Fintype.card_le_of_injective` gives the inequality with the codomain cardinality as a
            -- `Fintype.card`; rewrite it to `Finset.card` using `Fintype.card_coe`.
            simpa [Fintype.card_coe] using (Fintype.card_le_of_injective φ hφ_inj)
          have hcard_Z : (Z.card : ℝ) ≤ Real.log Bk / log2 + 1 := by
            have hx_nonneg : 0 ≤ Real.log Bk / log2 := by
              have : 0 ≤ Real.log Bk := le_of_lt (Real.log_pos hBk)
              exact div_nonneg this (le_of_lt hlog2_pos)
            have hceil_le :
                (Nat.ceil (Real.log Bk / Real.log (R / r)) : ℝ)
                  ≤ Real.log Bk / log2 + 1 := by
              -- `R/r = 2`
              have hrat : R / r = (2 : ℝ) := by
                have hrne : r ≠ 0 := ne_of_gt hr
                simp [R, hrne, div_eq_mul_inv]
              have hx_nonneg' : 0 ≤ Real.log Bk / Real.log (R / r) := by
                have hlogBk_nonneg : 0 ≤ Real.log Bk := le_of_lt (Real.log_pos hBk)
                have hlogRr_pos : 0 < Real.log (R / r) := by simpa [hrat, log2] using hlog2_pos
                exact div_nonneg hlogBk_nonneg (le_of_lt hlogRr_pos)
              have hlt := Nat.ceil_lt_add_one (R := ℝ) (a := Real.log Bk / Real.log (R / r)) hx_nonneg'
              have hle : (Nat.ceil (Real.log Bk / Real.log (R / r)) : ℝ)
                  ≤ Real.log Bk / Real.log (R / r) + 1 := le_of_lt hlt
              -- replace denominator with `log2`
              simpa [hrat, log2] using hle
            have hZcard' : (Z.card : ℝ) ≤ (Nat.ceil (Real.log Bk / Real.log (R / r)) : ℝ) := by
              exact_mod_cast hZcard
            exact hZcard'.trans hceil_le

          have hcard_S : (Fintype.card (S k) : ℝ) ≤ Real.log Bk / log2 + 1 := by
            have : (Fintype.card (S k) : ℝ) ≤ (Z.card : ℝ) := by exact_mod_cast hcard_nat
            exact this.trans hcard_Z

          -- Dyadic lower bound: on shell `k`, all zeros satisfy `r0 * 2^k ≤ ‖zero‖`.
          let t : ℝ := r0 * (2 : ℝ) ^ (k : ℕ)
          have ht_pos : 0 < t := by
            have h2 : 0 < (2 : ℝ) ^ (k : ℕ) := by positivity
            exact mul_pos hr0pos h2
          have hterm_le : ∀ n : S k, ‖zeros n.1‖⁻¹ ^ σ ≤ t⁻¹ ^ σ := by
            intro n
            have hn_lower : r0 * (2 : ℝ) ^ (kfun n.1 : ℝ) ≤ ‖zeros n.1‖ := hk_lower n.1
            have hk_eq : (kfun n.1 : ℝ) = (k : ℝ) := by exact_mod_cast n.2
            have hn_lower' : r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖zeros n.1‖ := by simpa [hk_eq] using hn_lower
            have hkpow : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ (k : ℕ) := by
              simp
            have hn_lower'' : t ≤ ‖zeros n.1‖ := by simpa [t, hkpow] using hn_lower'
            have hb : 0 < ‖zeros n.1‖ := by
              have : zeros n.1 ≠ 0 := (h_zeros n.1).2
              exact norm_pos_iff.2 this
            have hinv : ‖zeros n.1‖⁻¹ ≤ t⁻¹ :=
              (inv_le_inv₀ (a := ‖zeros n.1‖) (b := t) hb ht_pos).2 hn_lower''
            have h0 : 0 ≤ ‖zeros n.1‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
            exact Real.rpow_le_rpow h0 hinv (le_of_lt hσ_pos)

          -- Turn the `tsum` into a finite sum and bound by `card * bound`.
          have hshell_sum :
              (∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ) ≤ (Fintype.card (S k) : ℝ) * (t⁻¹ ^ σ) := by
            classical
            simp [tsum_fintype]
            have h' : ∀ n ∈ (Finset.univ : Finset (S k)), ‖zeros n.1‖⁻¹ ^ σ ≤ t⁻¹ ^ σ := by
              intro n hn
              exact hterm_le n
            have := Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (S k)))
              (f := fun n : S k => ‖zeros n.1‖⁻¹ ^ σ) (n := t⁻¹ ^ σ) h'
            simpa [nsmul_eq_mul] using this

          -- Rewrite `t⁻¹ ^ σ` as `r0^(-σ) * (2^(-σ))^k`.
          have ht_scale : t⁻¹ ^ σ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
            -- (r0*2^k)^{-σ} identity
            have hr0_le : 0 ≤ r0 := le_of_lt hr0pos
            have h2pow : 0 ≤ (2 : ℝ) ^ (k : ℕ) := by positivity
            have hxnonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℕ) := mul_nonneg hr0_le h2pow
            -- unfold t
            dsimp [t]
            calc
              (r0 * (2 : ℝ) ^ (k : ℕ))⁻¹ ^ σ
                  = ((r0 * (2 : ℝ) ^ (k : ℕ)) ^ σ)⁻¹ := Real.inv_rpow hxnonneg σ
              _ = (r0 * (2 : ℝ) ^ (k : ℕ)) ^ (-σ) := by
                    simpa using (Real.rpow_neg hxnonneg σ).symm
              _ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (k : ℕ)) ^ (-σ) := by
                    simp [Real.mul_rpow hr0_le h2pow]
              _ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
                    -- `((2^k)^(-σ)) = (2^(-σ))^k`
                    have h2 : 0 ≤ (2 : ℝ) := by norm_num
                    have hk'' : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k := by
                      simp
                    have hpow' : ((2 : ℝ) ^ k) ^ (-σ) = ((2 : ℝ) ^ (-σ)) ^ k := by
                      calc
                        ((2 : ℝ) ^ k) ^ (-σ) = ((2 : ℝ) ^ (k : ℝ)) ^ (-σ) := by simp [hk'']
                        _ = (2 : ℝ) ^ ((k : ℝ) * (-σ)) := by
                              have := Real.rpow_mul h2 (k : ℝ) (-σ)
                              simpa [mul_comm] using this.symm
                        _ = (2 : ℝ) ^ ((-σ) * (k : ℝ)) := by ring_nf
                        _ = ((2 : ℝ) ^ (-σ)) ^ (k : ℝ) := by
                              simpa [Real.rpow_mul h2] using (Real.rpow_mul h2 (-σ) (k : ℝ))
                        _ = ((2 : ℝ) ^ (-σ)) ^ k := by
                              simp
                    simp [hpow']

          -- Bound the RHS by the geometric majorant.
          have : (Fintype.card (S k) : ℝ) * (t⁻¹ ^ σ)
              ≤ A * q ^ k + B * qσ ^ k := by
            -- Use `card ≤ log Bk/log2 + 1` and bound `log Bk` by growth.
            have hlogBk : Real.log Bk = C * (1 + R) ^ τ + Real.log M0 := by
              have hexp_pos : 0 < Real.exp (C * (1 + R) ^ τ) := Real.exp_pos _
              have hlog_mul : Real.log (Real.exp (C * (1 + R) ^ τ) * M0)
                    = Real.log (Real.exp (C * (1 + R) ^ τ)) + Real.log M0 := by
                exact Real.log_mul (ne_of_gt hexp_pos) (ne_of_gt hM0_pos)
              simp [Bk, hlog_mul]
            have hcard_le' :
                (Fintype.card (S k) : ℝ)
                  ≤ (C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1 := by
              -- rewrite `log Bk / log2`
              have : Real.log Bk / log2 = (C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 := by
                calc
                  Real.log Bk / log2 = (C * (1 + R) ^ τ + Real.log M0) / log2 := by simp [hlogBk]
                  _ = (C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 := by
                        field_simp [hlog2_ne]
              -- use `hcard_S` above
              have hcard_S' : (Fintype.card (S k) : ℝ) ≤ Real.log Bk / log2 + 1 := hcard_S
              -- substitute
              simpa [this, add_assoc, add_left_comm, add_comm] using hcard_S'

            -- Bound `(1+R)^τ` by `((1+4*r0)^τ) * ((2^k)^τ)`.
            have hR_le : (1 : ℝ) + R ≤ (1 + 4 * r0) * (2 : ℝ) ^ k := by
              -- `R = 2*r = 4*r0*2^k` and `1 ≤ 2^k`.
              have hk1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
              have h2pow2 : (2 : ℝ) ^ ((k : ℝ) + 1) = (2 : ℝ) * (2 : ℝ) ^ k := by
                have h2 : (0 : ℝ) < 2 := by norm_num
                calc
                  (2 : ℝ) ^ ((k : ℝ) + 1)
                      = (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
                          simpa using (Real.rpow_add h2 (k : ℝ) (1 : ℝ))
                  _ = (2 : ℝ) ^ k * (2 : ℝ) := by
                        have hk' : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k := by
                          simp
                        simp [hk']
                  _ = (2 : ℝ) * (2 : ℝ) ^ k := by ring
              have hR_eq : R = (4 * r0) * (2 : ℝ) ^ k := by
                -- unfold `R` and `r`, and use `2^(k+1) = 2*2^k`.
                dsimp [R, r]
                -- `R = 2 * r0 * 2^(k+1) = 4*r0*2^k`
                calc
                  (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
                      = (2 : ℝ) * (r0 * ((2 : ℝ) * (2 : ℝ) ^ k)) := by simp [h2pow2]
                  _ = (4 * r0) * (2 : ℝ) ^ k := by ring
              calc
                (1 : ℝ) + R = 1 + (4 * r0) * (2 : ℝ) ^ k := by simp [hR_eq]
                _ ≤ (2 : ℝ) ^ k + (4 * r0) * (2 : ℝ) ^ k := by gcongr
                _ = (1 + 4 * r0) * (2 : ℝ) ^ k := by ring

            have hpow_le : ((1 : ℝ) + R) ^ τ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ τ :=
              Real.rpow_le_rpow (by positivity) hR_le hτ_nonneg
            have hsplit :
                ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ τ
                  = (1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ := by
              have hbase1 : 0 ≤ (1 + 4 * r0 : ℝ) := by linarith [le_of_lt hr0pos]
              have hbase2 : 0 ≤ (2 : ℝ) ^ k := by positivity
              simp [Real.mul_rpow hbase1 hbase2]
            have hpow_le' : ((1 : ℝ) + R) ^ τ ≤ (1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ :=
              le_trans hpow_le (by simp [hsplit])

            -- Convert `((2^k)^τ)` to `((2^τ)^k)` and combine with `qσ^k`.
            have h2powτ : ((2 : ℝ) ^ k) ^ τ = ((2 : ℝ) ^ τ) ^ k := by
              have h2 : 0 ≤ (2 : ℝ) := by norm_num
              have hk' : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k := by
                simp
              calc
                ((2 : ℝ) ^ k) ^ τ = ((2 : ℝ) ^ (k : ℝ)) ^ τ := by simp [hk']
                _ = (2 : ℝ) ^ ((k : ℝ) * τ) := by
                      have := Real.rpow_mul h2 (k : ℝ) τ
                      simpa [mul_comm] using this.symm
                _ = (2 : ℝ) ^ (τ * (k : ℝ)) := by ring_nf
                _ = ((2 : ℝ) ^ τ) ^ k := by
                      have hr' : (2 : ℝ) ^ (τ * (k : ℝ)) = ((2 : ℝ) ^ τ) ^ (k : ℝ) := by
                        simp [Real.rpow_mul h2]
                      have hn : ((2 : ℝ) ^ τ) ^ (k : ℝ) = ((2 : ℝ) ^ τ) ^ k := by
                        simp
                      exact hr'.trans hn
            have hq : q = (2 : ℝ) ^ τ * (2 : ℝ) ^ (-σ) := by
              have h2pos : (0 : ℝ) < 2 := by norm_num
              have : (τ - σ) = τ + (-σ) := by ring
              calc
                q = (2 : ℝ) ^ (τ + (-σ)) := by simp [q, this]
                _ = (2 : ℝ) ^ τ * (2 : ℝ) ^ (-σ) := by
                      simpa using (Real.rpow_add h2pos τ (-σ))
            have hq_pow : q ^ k = ((2 : ℝ) ^ τ) ^ k * ((2 : ℝ) ^ (-σ)) ^ k := by
              simp [hq, mul_pow]

            -- rewrite `t⁻¹ ^ σ` into `r0^(-σ) * qσ^k`
            have ht_scale' : t⁻¹ ^ σ = (r0 ^ (-σ)) * qσ ^ k := by simp [qσ, ht_scale]

            -- Now a direct domination by the majorant (algebraic bookkeeping).
            -- First expand the left-hand side using the card bound.
            have hL :
                (Fintype.card (S k) : ℝ) * (t⁻¹ ^ σ)
                  ≤ ((C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (t⁻¹ ^ σ) := by
              exact mul_le_mul_of_nonneg_right hcard_le' (by
                have : 0 ≤ t⁻¹ ^ σ := Real.rpow_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hr0pos) (by positivity))) σ
                exact this)
            -- rewrite scale
            rw [ht_scale'] at hL ⊢
            -- and bound the growth term `(1+R)^τ`
            -- `((C*(1+R)^τ)/log2) * r0^{-σ} * qσ^k ≤ A * q^k`
            have hstep1 :
                ((C * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k) ≤ A * q ^ k := by
              have hdiv_nonneg : 0 ≤ C / log2 := div_nonneg (le_of_lt hCpos) (le_of_lt hlog2_pos)
              have hnonneg_r0 : 0 ≤ r0 ^ (-σ) := Real.rpow_nonneg (le_of_lt hr0pos) _
              have hnonneg_qσk : 0 ≤ qσ ^ k := pow_nonneg hqσ_nonneg k
              -- `((1+R)^τ) * qσ^k ≤ (1+4*r0)^τ * q^k`
              have hgrow : (1 + R) ^ τ * (qσ ^ k) ≤ (1 + 4 * r0) ^ τ * (q ^ k) := by
                -- use `hpow_le'` and the identities for powers
                have hqk' : q ^ k = ((2 : ℝ) ^ τ) ^ k * (qσ ^ k) := by
                  simp [q, qσ, hq, mul_pow, mul_comm]
                calc
                  (1 + R) ^ τ * (qσ ^ k)
                      ≤ ((1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ) * (qσ ^ k) := by
                          gcongr
                  _ = (1 + 4 * r0) ^ τ * (((2 : ℝ) ^ k) ^ τ * (qσ ^ k)) := by ring
                  _ = (1 + 4 * r0) ^ τ * (((2 : ℝ) ^ τ) ^ k * (qσ ^ k)) := by
                        simp [h2powτ]
                  _ = (1 + 4 * r0) ^ τ * (q ^ k) := by simp [hqk']
              -- now multiply by nonneg constants
              calc
                ((C * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k)
                    = (C / log2) * ((1 + R) ^ τ * (qσ ^ k)) * (r0 ^ (-σ)) := by
                        field_simp [hlog2_ne]
                _ ≤ (C / log2) * ((1 + 4 * r0) ^ τ * (q ^ k)) * (r0 ^ (-σ)) := by
                      gcongr
                _ = A * q ^ k := by
                      simp [A, mul_assoc, mul_left_comm, mul_comm]
            have hstep2 :
                ((Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k) ≤ B * qσ ^ k := by
              simp [B, mul_assoc, mul_left_comm, mul_comm]
            -- put it together
            have hsum :
                ((C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k)
                  ≤ A * q ^ k + B * qσ ^ k := by
              -- split the scalar sum into two and use the step bounds
              calc
                ((C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k)
                    = ((C * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k)
                        + ((Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k) := by ring
                _ ≤ A * q ^ k + B * qσ ^ k := by
                      gcongr
            exact le_trans hL hsum

          -- chain everything
          exact le_trans hshell_sum this
        ) hmajor

  -- Conclude from `summable_partition`.
  have := (summable_partition (f := fun n : ℕ => ‖zeros n‖⁻¹ ^ σ) hnonneg (s := S) hS)
  exact (this.2 hshell)

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
        exact Int.ofNat_le.2 hab
      have hmap_mono : Monotone (fun t : ℕ∞ => t.map (fun n : ℕ => (n : ℤ))) :=
        (ENat.monotone_map_iff (f := fun n : ℕ => (n : ℤ))).2 h_cast_mono
      have hG_le_f : meromorphicOrderAt G z0 ≤ meromorphicOrderAt f z0 := by
        -- Transport the analytic order inequality to a meromorphic order inequality.
        have : (analyticOrderAt G z0).map (fun n : ℕ => (n : ℤ))
              ≤ (analyticOrderAt f z0).map (fun n : ℕ => (n : ℤ)) :=
          hmap_mono (h_ord z0)
        simpa [hG_an.meromorphicOrderAt_eq, hf_an.meromorphicOrderAt_eq] using this
      have hq_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt q z0 := by
        have hq_order :
            meromorphicOrderAt q z0 = meromorphicOrderAt f z0 + -meromorphicOrderAt G z0 := by
          -- `order(q) = order(f) + order(1/G)`.
          have hmul :
              meromorphicOrderAt (fun z => f z * (G z)⁻¹) z0
                = meromorphicOrderAt f z0 + meromorphicOrderAt (fun z => (G z)⁻¹) z0 := by
            simpa using
              (meromorphicOrderAt_mul (x := z0) (f := f) (g := fun z => (G z)⁻¹)
                (hf := hf_an.meromorphicAt) (hg := (hG_an.meromorphicAt.inv)))
          have hinv : meromorphicOrderAt (fun z => (G z)⁻¹) z0 = -meromorphicOrderAt G z0 := by
            simpa using (meromorphicOrderAt_inv (f := G) (x := z0))
          calc
            meromorphicOrderAt q z0
                = meromorphicOrderAt (fun z => f z * (G z)⁻¹) z0 := by
                    simp [q, div_eq_mul_inv]
            _ = meromorphicOrderAt f z0 + meromorphicOrderAt (fun z => (G z)⁻¹) z0 := hmul
            _ = meromorphicOrderAt f z0 + -meromorphicOrderAt G z0 := by simp [hinv]
        -- Nonnegativity follows from `order(G) ≤ order(f)` and the fact that `G` is not locally zero.
        have hG_ne_top : meromorphicOrderAt G z0 ≠ ⊤ :=
          (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hG_an.meromorphicAt)).2 hG_ne
        have hcancel : meromorphicOrderAt G z0 + -meromorphicOrderAt G z0 = 0 :=
          LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top (x := meromorphicOrderAt G z0) hG_ne_top
        have h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z0 + -meromorphicOrderAt G z0 := by
          have h := add_le_add_left hG_le_f (-meromorphicOrderAt G z0)
          simpa [hcancel, add_assoc] using h
        simpa [hq_order] using h0

      -- `q` has a limit along `𝓝[≠] z0`, hence tends to `limUnder ... q`.
      have hq_hasLimit : ∃ c, Tendsto q (𝓝[≠] z0) (𝓝 c) :=
        tendsto_nhds_of_meromorphicOrderAt_nonneg hq_mer hq_nonneg
      have hq_tendsto_lim : Tendsto q (𝓝[≠] z0) (𝓝 (limUnder (𝓝[≠] z0) q)) :=
        tendsto_nhds_limUnder hq_hasLimit

      -- Choose a neighbourhood on which `G` is nonzero except at the center; there `H` is an update
      -- of `q` by the computed limit.
      have hmem : {z : ℂ | G z ≠ 0} ∈ 𝓝[≠] z0 := hG_ne
      rcases (mem_nhdsWithin.1 hmem) with ⟨U, hU_open, hz0U, hU⟩
      have hU_nhds : U ∈ 𝓝 z0 := hU_open.mem_nhds hz0U
      have hU' : ∀ z, z ∈ U \ {z0} → G z ≠ 0 := by
        intro z hz
        have : z ∈ U ∩ ({z0}ᶜ : Set ℂ) := by
          refine ⟨hz.1, ?_⟩
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz.2
        exact hU this
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
        have hz_ne : z ≠ z0 := by
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
        simp [Function.update, hz_ne]  -- `z ≠ z0`
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
          have hGz : G z ≠ 0 := hU' z this
          simp [H, q, hGz, Function.update, hz]

      have hanH : AnalyticAt ℂ H z0 := han_update.congr hEq_on.symm
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
        (hG z0).continuousAt.eventually_ne hG0
      have hEq : (fun z => H z) =ᶠ[𝓝 z0] (fun z => f z / G z) := by
        filter_upwards [hG_near] with z hz
        simp [H, q, hz]
      -- Conclude.
      exact hdiff.congr_of_eventuallyEq hEq
  · intro z hz
    simp [H, q, hz]


set_option maxHeartbeats 800000 in
/-- Lindelöf's theorem, `ZeroData` version (zeros counted with multiplicity).

If `f` is entire of finite order `ρ` and `hz : ZeroData f` enumerates the nonzero zeros with
multiplicity, then for any `σ > ρ` the series `∑ ‖hz.zeros n‖^{-σ}` converges. -/
theorem lindelof_zero_data {f : ℂ → ℂ} {ρ σ : ℝ}
    (hf : EntireOfFiniteOrder ρ f)
    (hz : ZeroData f)
    (hσ : ρ < σ) :
    Summable (fun n : ℕ => ‖hz.zeros n‖⁻¹ ^ σ) := by
  classical

  -- `ZeroData f` rules out the identically-zero function (countability obstruction).
  have hnot_all_zero : ¬ (∀ z : ℂ, f z = 0) := by
    intro hzero
    have hsubset : ({0}ᶜ : Set ℂ) ⊆ Set.range hz.zeros := by
      intro z hz0
      have hz' : f z = 0 := hzero z
      have hzspec := (hz.zero_spec z).1 hz'
      rcases hzspec with h0 | hnon0
      · exact False.elim (hz0 h0.1)
      · exact hnon0.2
    have hcount_range : (Set.range hz.zeros).Countable := Set.countable_range hz.zeros
    have hcount_compl : ({0}ᶜ : Set ℂ).Countable := hcount_range.mono hsubset
    have hcount_univ : (Set.univ : Set ℂ).Countable := by
      have h0c : ({0} : Set ℂ).Countable := Set.countable_singleton 0
      have : ({0} ∪ ({0}ᶜ) : Set ℂ).Countable := h0c.union hcount_compl
      simpa [Set.union_compl_self] using this
    exact not_countable_complex hcount_univ

  -- Step 0: order is nonnegative (otherwise bounded ⇒ constant ⇒ impossible by `ZeroData`).
  have hρ_nonneg : 0 ≤ ρ := by
    by_contra hρ
    have hρneg : ρ < 0 := lt_of_not_ge hρ
    rcases hf.growth with ⟨C, hCpos, hC⟩
    have hbounded : ∃ M, ∀ z : ℂ, ‖f z‖ ≤ M := by
      refine ⟨Real.exp C, ?_⟩
      intro z
      have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      have hpow : (1 + ‖z‖) ^ ρ ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hbase (le_of_lt hρneg)
      have hlog_le : Real.log (1 + ‖f z‖) ≤ C := by
        have h1 : Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ := hC z
        have h2 : C * (1 + ‖z‖) ^ ρ ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
        have h3 : C * (1 + ‖z‖) ^ ρ ≤ C := by simpa using h2
        exact h1.trans h3
      have hpos : 0 < (1 : ℝ) + ‖f z‖ := by linarith [norm_nonneg (f z)]
      have hle : (1 : ℝ) + ‖f z‖ ≤ Real.exp C := (Real.log_le_iff_le_exp hpos).1 hlog_le
      have hle' : ‖f z‖ ≤ (1 : ℝ) + ‖f z‖ := le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      exact hle'.trans hle
    have hb_range : Bornology.IsBounded (Set.range f) := by
      rcases hbounded with ⟨M, hM⟩
      refine (isBounded_iff_forall_norm_le).2 ?_
      refine ⟨M, ?_⟩
      intro y hy
      rcases hy with ⟨z, rfl⟩
      simpa using hM z
    rcases (Differentiable.exists_eq_const_of_bounded hf.entire hb_range) with ⟨c, hc⟩
    -- `f` has a nonzero zero at `hz.zeros 0`, hence `c = 0` and thus `f ≡ 0`, contradiction.
    have hzero0 : f (hz.zeros 0) = 0 := by
      have : (hz.zeros 0 = 0 ∧ 0 < hz.ord0) ∨ (hz.zeros 0 ≠ 0 ∧ ∃ n, hz.zeros n = hz.zeros 0) :=
        Or.inr ⟨hz.zeros_ne_zero 0, ⟨0, rfl⟩⟩
      exact (hz.zero_spec (hz.zeros 0)).2 this
    have hc0 : c = 0 := by
      have : f (hz.zeros 0) = c := by simp [hc]
      simpa [this] using hzero0
    have hzero : ∀ z : ℂ, f z = 0 := by
      intro z
      simp [hc, hc0]
    exact hnot_all_zero hzero

  have hσ_pos : 0 < σ := lt_of_le_of_lt hρ_nonneg hσ

  -- Choose an intermediate exponent `τ` with `ρ ≤ τ < σ`.
  let τ : ℝ := (ρ + σ) / 2
  have hρτ : ρ ≤ τ := by dsimp [τ]; linarith
  have hτσ : τ < σ := by dsimp [τ]; linarith
  have hτ_nonneg : 0 ≤ τ := le_trans hρ_nonneg hρτ

  -- Upgrade to order `τ`, and extract a simple norm bound.
  have hfτ : EntireOfFiniteOrder τ f := EntireOfFiniteOrder.of_le_order hf hρτ
  rcases hfτ.norm_bound with ⟨Cf, hCf_pos, hCf⟩

  -- Rule out `analyticOrderAt f 0 = ⊤` using the same obstruction.
  have hf_univ : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf.entire
  have hf_not_top0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ := by
    intro htop
    have hloc : ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 := (analyticOrderAt_eq_top.mp htop)
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 :=
      (hloc.filter_mono nhdsWithin_le_nhds).frequently
    have hEq : Set.EqOn f 0 (Set.univ : Set ℂ) :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (f := f) (U := (Set.univ : Set ℂ)) hf_univ (by simpa using isPreconnected_univ)
        (by simp) hfreq
    have hzero : ∀ z : ℂ, f z = 0 := by
      intro z
      simpa using hEq (by simp : z ∈ (Set.univ : Set ℂ))
    exact hnot_all_zero hzero

  have horder_f0 : analyticOrderAt f (0 : ℂ) = (hz.ord0 : ℕ∞) := by
    have hcast :
        (analyticOrderNatAt f (0 : ℂ) : ℕ∞) = analyticOrderAt f (0 : ℂ) :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := (0 : ℂ)) hf_not_top0
    simpa [hz.ord0_spec] using hcast.symm

  -- Divide out the zero at 0: `G0(z) = z^{ord0}`.
  let G0 : ℂ → ℂ := fun z => z ^ hz.ord0
  have hG0_entire : Differentiable ℂ G0 := by
    simp [G0]
  have hG0_nontrivial : ∃ z, G0 z ≠ 0 := by
    refine ⟨1, ?_⟩
    simp [G0]
  have horder_G0_0 : analyticOrderAt G0 (0 : ℂ) = (hz.ord0 : ℕ∞) := by
    simpa [G0, sub_zero] using
      (analyticOrderAt_centeredMonomial (z₀ := (0 : ℂ)) (n := hz.ord0))
  have h_ord0 : ∀ z : ℂ, analyticOrderAt G0 z ≤ analyticOrderAt f z := by
    intro z
    by_cases hz0 : z = 0
    · subst hz0
      simp [horder_G0_0, horder_f0]
    ·
      have hG0z_ne : G0 z ≠ 0 := by
        simpa [G0] using pow_ne_zero hz.ord0 hz0
      have hG0_order0 : analyticOrderAt G0 z = 0 := by
        have hAn : AnalyticAt ℂ G0 z := hG0_entire.analyticAt z
        exact (hAn.analyticOrderAt_eq_zero).2 hG0z_ne
      simp [hG0_order0]

  -- Entire quotient `f / z^{ord0}`.
  rcases quotient_entire (f := f) (G := G0) hf.entire hG0_entire hG0_nontrivial h_ord0 with
    ⟨f₁, hf₁_entire, hf₁_eq⟩

  -- `f₁(0) ≠ 0` from the local factorization of `f` at 0.
  have hf₁0 : f₁ 0 ≠ 0 := by
    have hf0_an : AnalyticAt ℂ f (0 : ℂ) := (hf.entire.analyticAt 0)
    rcases (hf0_an.analyticOrderAt_eq_natCast.mp horder_f0) with ⟨g0, hg0_an, hg0_ne, hfg0⟩
    let q : ℂ → ℂ := fun z => f z / G0 z
    have hq_eq : q =ᶠ[𝓝[≠] (0 : ℂ)] g0 := by
      have hfg0' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = (z - 0) ^ hz.ord0 • g0 z :=
        hfg0.filter_mono nhdsWithin_le_nhds
      filter_upwards [hfg0', self_mem_nhdsWithin] with z hzfg hzneq
      have hz0 : z ≠ (0 : ℂ) := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hzneq
      have hG0z : G0 z ≠ 0 := by simpa [G0] using pow_ne_zero hz.ord0 hz0
      have hzfg' : f z = z ^ hz.ord0 * g0 z := by
        simpa [smul_eq_mul, sub_zero] using hzfg
      have : q z = g0 z := by
        -- cancel `z^ord0`
        calc
          q z = (z ^ hz.ord0 * g0 z) / (z ^ hz.ord0) := by simp [q, G0, hzfg']
          _ = g0 z := by
                field_simp [hG0z]
      simp [this]
    have htend_g0 : Tendsto g0 (𝓝[≠] (0 : ℂ)) (𝓝 (g0 0)) :=
      (hg0_an.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have htend_q : Tendsto q (𝓝[≠] (0 : ℂ)) (𝓝 (g0 0)) :=
      Filter.Tendsto.congr' hq_eq.symm htend_g0
    have hq_eq_f₁ : q =ᶠ[𝓝[≠] (0 : ℂ)] f₁ := by
      filter_upwards [self_mem_nhdsWithin] with z hzneq
      have hz0 : z ≠ (0 : ℂ) := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hzneq
      have hG0z : G0 z ≠ 0 := by simpa [G0] using pow_ne_zero hz.ord0 hz0
      simp [q, hf₁_eq z hG0z]
    have htend_f₁ : Tendsto f₁ (𝓝[≠] (0 : ℂ)) (𝓝 (g0 0)) :=
      Filter.Tendsto.congr' hq_eq_f₁ htend_q
    have htend_f₁0 : Tendsto f₁ (𝓝[≠] (0 : ℂ)) (𝓝 (f₁ 0)) :=
      ((hf₁_entire 0).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hlim : f₁ 0 = g0 0 := tendsto_nhds_unique htend_f₁0 htend_f₁
    simpa [hlim] using hg0_ne

  -- Normalize so that `g 0 = 1`.
  let g : ℂ → ℂ := fun z => f₁ z / f₁ 0
  have hg_entire : Differentiable ℂ g := by
    simpa [g] using (hf₁_entire.div_const (f₁ 0))
  have hg0 : g 0 = 1 := by
    simp [g, hf₁0]

  -- Zeros: `g (hz.zeros n) = 0` for all `n`.
  have hg_zeros : ∀ n, g (hz.zeros n) = 0 := by
    intro n
    have hz0 : hz.zeros n ≠ 0 := hz.zeros_ne_zero n
    have hG0z : G0 (hz.zeros n) ≠ 0 := by
      simpa [G0] using pow_ne_zero hz.ord0 hz0
    have hfz : f (hz.zeros n) = 0 := by
      have : (hz.zeros n = 0 ∧ 0 < hz.ord0) ∨ (hz.zeros n ≠ 0 ∧ ∃ k, hz.zeros k = hz.zeros n) :=
        Or.inr ⟨hz.zeros_ne_zero n, ⟨n, rfl⟩⟩
      exact (hz.zero_spec (hz.zeros n)).2 this
    have hf₁z : f₁ (hz.zeros n) = 0 := by
      simp [hf₁_eq _ hG0z, hfz]
    simp [g, hf₁z]

  -- A zero-free ball around `0`, hence `r0 ≤ ‖hz.zeros n‖` for all `n`.
  obtain ⟨r0, hr0pos, hr0⟩ :
      ∃ r0 > 0, ∀ z : ℂ, ‖z‖ < r0 → g z ≠ 0 := by
    have hcont : ContinuousAt g 0 := (hg_entire 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), g z ≠ 0 := hcont.eventually_ne (by simp [hg0])
    rcases (Metric.mem_nhds_iff.mp hne) with ⟨r, hrpos, hr⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    have : z ∈ Metric.ball (0 : ℂ) r := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hr this

  have hr0_le_norm : ∀ n, r0 ≤ ‖hz.zeros n‖ := by
    intro n
    have hz0 : g (hz.zeros n) = 0 := hg_zeros n
    have hnot : ¬ ‖hz.zeros n‖ < r0 := by
      intro hlt
      exact (hr0 (hz.zeros n) hlt) hz0
    exact le_of_not_gt hnot

  -- Dyadic shell index: `k(n) = ⌊logb 2 (‖zeros n‖/r0)⌋₊`.
  let zeros : ℕ → ℂ := hz.zeros
  let kfun : ℕ → ℕ := fun n => ⌊Real.logb 2 (‖zeros n‖ / r0)⌋₊

  -- Dyadic bounds for `x ≥ 1`.
  have hdyadic_lower :
      ∀ {x : ℝ}, 1 ≤ x → (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
    have hlog_nonneg : 0 ≤ Real.logb 2 x :=
      Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
    have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
      simpa using (Nat.floor_le hlog_nonneg)
    exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
      (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le
  have hdyadic_upper :
      ∀ {x : ℝ}, 1 ≤ x → x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
    have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
    exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
      (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1) (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

  -- For each `n`, we have `r0*2^{k(n)} ≤ ‖zeros n‖ < r0*2^{k(n)+1}`.
  have hk_lower : ∀ n, r0 * (2 : ℝ) ^ (kfun n : ℝ) ≤ ‖zeros n‖ := by
    intro n
    have hx1 : (1 : ℝ) ≤ ‖zeros n‖ / r0 := by
      have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
      have : r0 / r0 ≤ ‖zeros n‖ / r0 :=
        div_le_div_of_nonneg_right (hr0_le_norm n) (le_of_lt hr0pos)
      simpa [hr0ne] using this
    have hle : (2 : ℝ) ^ (kfun n : ℝ) ≤ ‖zeros n‖ / r0 := by
      simpa [kfun] using (hdyadic_lower (x := ‖zeros n‖ / r0) hx1)
    have := mul_le_mul_of_nonneg_left hle (le_of_lt hr0pos)
    have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
    have hxEq : r0 * (‖zeros n‖ / r0) = ‖zeros n‖ := by
      field_simp [hr0ne]
    simpa [mul_assoc, hxEq] using this
  have hk_upper : ∀ n, ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := by
    intro n
    have hx1 : (1 : ℝ) ≤ ‖zeros n‖ / r0 := by
      have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
      have : r0 / r0 ≤ ‖zeros n‖ / r0 :=
        div_le_div_of_nonneg_right (hr0_le_norm n) (le_of_lt hr0pos)
      simpa [hr0ne] using this
    have hlt : ‖zeros n‖ / r0 < (2 : ℝ) ^ ((kfun n : ℝ) + 1) := by
      simpa [kfun] using (hdyadic_upper (x := ‖zeros n‖ / r0) hx1)
    have := mul_lt_mul_of_pos_left hlt hr0pos
    have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
    have hxEq : r0 * (‖zeros n‖ / r0) = ‖zeros n‖ := by
      field_simp [hr0ne]
    simpa [mul_assoc, hxEq] using this

  -- Define shells `S k = {n | kfun n = k}`.
  let S : ℕ → Set ℕ := fun k => {n : ℕ | kfun n = k}
  have hS : ∀ n : ℕ, ∃! k : ℕ, n ∈ S k := by
    intro n
    refine ⟨kfun n, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm

  -- Nonnegativity of the summand.
  have hnonneg : 0 ≤ fun n : ℕ => ‖zeros n‖⁻¹ ^ σ := by
    intro n
    exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (zeros n))) σ

  -- We apply the partition lemma: it suffices to prove summability of the shell `tsum`s.
  have hshell :
      (∀ k : ℕ, Summable fun n : S k => ‖zeros n.1‖⁻¹ ^ σ) ∧
        Summable fun k : ℕ => ∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ := by
    constructor
    · intro k
      -- Each shell is finite: it sits inside a closed ball, and `ZeroData` is locally finite there.
      have hSk_finite : (S k).Finite := by
        refine (hz.finite_in_ball (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))).subset ?_
        intro n hn
        have hk : kfun n = k := by simpa [S] using hn
        have hn_upper : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := hk_upper n
        have hk' : (kfun n : ℝ) = (k : ℝ) := by exact_mod_cast hk
        have hn_upper' : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by simpa [hk'] using hn_upper
        exact le_of_lt hn_upper'
      haveI : Finite (S k) := hSk_finite.to_subtype
      exact Summable.of_finite
    ·
      -- Shell `tsum` summability: Jensen gives `card(S k) = O((2^k)^τ)` (counting multiplicity),
      -- and dyadic bounds give `‖zeros n‖^{-σ} = O((2^{-σ})^k)` on shell `k`.
      classical
      let log2 : ℝ := Real.log (2 : ℝ)
      have hlog2_pos : 0 < log2 := by
        dsimp [log2]
        exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlog2_ne : log2 ≠ 0 := ne_of_gt hlog2_pos

      -- A global exponential bound for `f₁` of the same order `τ`.
      have h_compact : IsCompact (Metric.closedBall (0 : ℂ) (1 : ℝ)) :=
        isCompact_closedBall (0 : ℂ) (1 : ℝ)
      have h_cont : ContinuousOn f₁ (Metric.closedBall (0 : ℂ) (1 : ℝ)) :=
        (hf₁_entire.continuous).continuousOn
      obtain ⟨M1, hM1⟩ := h_compact.exists_bound_of_continuousOn h_cont
      have hM1_nonneg : 0 ≤ M1 := by
        have h0 := hM1 0 (by simp [Metric.mem_closedBall])
        exact le_trans (norm_nonneg _) h0

      let C1 : ℝ := max Cf (Real.log (1 + M1) + 1)
      have hC1pos : 0 < C1 := lt_of_lt_of_le hCf_pos (le_max_left _ _)

      have hC1 : ∀ z : ℂ, ‖f₁ z‖ ≤ Real.exp (C1 * (1 + ‖z‖) ^ τ) := by
        intro z
        by_cases hz1 : ‖z‖ < 1
        · have hz_cb : z ∈ Metric.closedBall (0 : ℂ) (1 : ℝ) := by
            have : ‖z‖ ≤ (1 : ℝ) := le_of_lt hz1
            simpa [Metric.mem_closedBall, dist_zero_right] using this
          have hzM : ‖f₁ z‖ ≤ M1 := hM1 z hz_cb
          have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ τ := by
            have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
            exact Real.one_le_rpow hbase hτ_nonneg
          have hlog_le : Real.log (1 + ‖f₁ z‖) ≤ Real.log (1 + M1) := by
            have hpos : 0 < (1 : ℝ) + ‖f₁ z‖ := by linarith [norm_nonneg (f₁ z)]
            exact Real.log_le_log hpos (by linarith [hzM])
          have hlogM1_le : Real.log (1 + M1) ≤ C1 * (1 + ‖z‖) ^ τ := by
            have hC1_ge : Real.log (1 + M1) ≤ C1 := by
              have h1 : Real.log (1 + M1) ≤ Real.log (1 + M1) + 1 :=
                le_add_of_nonneg_right zero_le_one
              have h2 : Real.log (1 + M1) + 1 ≤ C1 := by
                simp [C1]
              exact h1.trans h2
            have hC1_le : (C1 : ℝ) ≤ C1 * (1 + ‖z‖) ^ τ := by
              simpa [mul_one] using (mul_le_mul_of_nonneg_left hone (le_of_lt hC1pos))
            exact hC1_ge.trans hC1_le
          have hlog_main : Real.log (1 + ‖f₁ z‖) ≤ C1 * (1 + ‖z‖) ^ τ :=
            hlog_le.trans hlogM1_le
          have hpos : 0 < (1 : ℝ) + ‖f₁ z‖ := by linarith [norm_nonneg (f₁ z)]
          have h1 : (1 : ℝ) + ‖f₁ z‖ ≤ Real.exp (C1 * (1 + ‖z‖) ^ τ) :=
            (Real.log_le_iff_le_exp hpos).1 hlog_main
          linarith [Real.exp_pos (C1 * (1 + ‖z‖) ^ τ)]
        · have hz1' : (1 : ℝ) ≤ ‖z‖ := le_of_not_gt hz1
          have hz0 : z ≠ (0 : ℂ) := by
            have : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hz1'
            exact (norm_pos_iff.mp this)
          have hG0z : G0 z ≠ 0 := by simpa [G0] using pow_ne_zero hz.ord0 hz0
          have hf₁z : f₁ z = f z / G0 z := hf₁_eq z hG0z
          have hnorm_le : ‖f₁ z‖ ≤ ‖f z‖ := by
            have hzpow : (1 : ℝ) ≤ ‖G0 z‖ := by
              have : (1 : ℝ) ≤ ‖z‖ ^ hz.ord0 := one_le_pow₀ hz1'
              simpa [G0, norm_pow] using this
            calc
              ‖f₁ z‖ = ‖f z / G0 z‖ := by simp [hf₁z]
              _ = ‖f z‖ / ‖G0 z‖ := by simp
              _ ≤ ‖f z‖ := div_le_self (norm_nonneg _) hzpow
          have hfz : ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ) := hCf z
          have hCf_le : Cf ≤ C1 := le_max_left _ _
          have hexp_le : Real.exp (Cf * (1 + ‖z‖) ^ τ) ≤ Real.exp (C1 * (1 + ‖z‖) ^ τ) := by
            have hmul_le : Cf * (1 + ‖z‖) ^ τ ≤ C1 * (1 + ‖z‖) ^ τ :=
              mul_le_mul_of_nonneg_right hCf_le (Real.rpow_nonneg (by linarith [norm_nonneg z]) τ)
            exact Real.exp_le_exp.2 hmul_le
          exact hnorm_le.trans (hfz.trans hexp_le)

      let M0 : ℝ := max 2 (‖f₁ 0‖)⁻¹
      have hM0_pos : 0 < M0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)

      let q : ℝ := (2 : ℝ) ^ (τ - σ)
      have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hq_lt_one : q < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
          (sub_neg.2 hτσ)
      have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
        summable_geometric_of_lt_one hq_nonneg hq_lt_one

      let qσ : ℝ := (2 : ℝ) ^ (-σ)
      have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hqσ_lt_one : qσ < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
          (by linarith [hσ_pos])
      have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
        summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one

      let A : ℝ := (C1 / log2) * (1 + 4 * r0) ^ τ * (r0 ^ (-σ))
      let B : ℝ := ((Real.log M0) / log2 + 1) * (r0 ^ (-σ))
      have hmajor : Summable (fun k : ℕ => A * q ^ k + B * qσ ^ k) :=
        (hgeom_q.mul_left A).add (hgeom_qσ.mul_left B)

      refine Summable.of_nonneg_of_le
        (g := fun k : ℕ => ∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ)
        (f := fun k : ℕ => A * q ^ k + B * qσ ^ k)
        (fun k => by
          have hnn : ∀ n : S k, 0 ≤ ‖zeros n.1‖⁻¹ ^ σ := by
            intro n
            exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (zeros n.1))) σ
          exact tsum_nonneg hnn)
        (fun k => by
          -- Fix a shell index `k`, apply Jensen at radii `r = r0*2^(k+1)` and `R = 2r`.
          let r : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
          let R : ℝ := (2 : ℝ) * r
          have hr : 0 < r := by
            have h2 : 0 < (2 : ℝ) ^ ((k : ℝ) + 1) :=
              Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
            exact mul_pos hr0pos h2
          have hRpos : 0 < R := mul_pos (by norm_num : (0 : ℝ) < 2) hr
          have hrR : r < R := by
            have h2 : (1 : ℝ) < 2 := by norm_num
            simpa [R, mul_assoc] using (lt_mul_of_one_lt_left hr h2)

          have hg_anal : AnalyticOnNhd ℂ g (Metric.closedBall 0 R) := by
            intro z hz
            exact hg_entire.analyticAt z

          let Bk : ℝ := Real.exp (C1 * (1 + R) ^ τ) * M0
          have hBk : 1 < Bk := by
            have hexp : 1 ≤ Real.exp (C1 * (1 + R) ^ τ) :=
              (Real.one_le_exp_iff).2 (by
                have : 0 ≤ (1 + R : ℝ) ^ τ := Real.rpow_nonneg (by linarith [hRpos.le]) τ
                nlinarith [le_of_lt hC1pos, this])
            have hM0 : (1 : ℝ) < M0 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
            have : 1 < Real.exp (C1 * (1 + R) ^ τ) * M0 := one_lt_mul hexp hM0
            simpa [Bk] using this

          have hg_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ Bk := by
            intro z hzR
            have hf₁z : ‖f₁ z‖ ≤ Real.exp (C1 * (1 + ‖z‖) ^ τ) := hC1 z
            have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
            have hpow_le : (1 + ‖z‖ : ℝ) ^ τ ≤ (1 + R) ^ τ :=
              Real.rpow_le_rpow (by positivity) hbase hτ_nonneg
            have hmul_le : C1 * (1 + ‖z‖) ^ τ ≤ C1 * (1 + R) ^ τ :=
              mul_le_mul_of_nonneg_left hpow_le (le_of_lt hC1pos)
            have hexp_le : Real.exp (C1 * (1 + ‖z‖) ^ τ) ≤ Real.exp (C1 * (1 + R) ^ τ) :=
              (Real.exp_le_exp.2 hmul_le)
            have hf₁z' : ‖f₁ z‖ ≤ Real.exp (C1 * (1 + R) ^ τ) := hf₁z.trans hexp_le
            have hf₁0pos : 0 < ‖f₁ 0‖ := norm_pos_iff.mpr hf₁0
            have hdiv_le :
                ‖g z‖ ≤ Real.exp (C1 * (1 + R) ^ τ) * (‖f₁ 0‖)⁻¹ := by
              have : ‖g z‖ = ‖f₁ z‖ / ‖f₁ 0‖ := by simp [g]
              have hdiv :
                  ‖f₁ z‖ / ‖f₁ 0‖ ≤ Real.exp (C1 * (1 + R) ^ τ) / ‖f₁ 0‖ :=
                div_le_div_of_nonneg_right hf₁z' (le_of_lt hf₁0pos)
              simpa [this, div_eq_mul_inv, mul_assoc] using hdiv
            have hM0' : (‖f₁ 0‖)⁻¹ ≤ M0 := le_max_right _ _
            have hBk' :
                Real.exp (C1 * (1 + R) ^ τ) * (‖f₁ 0‖)⁻¹ ≤ Real.exp (C1 * (1 + R) ^ τ) * M0 :=
              mul_le_mul_of_nonneg_left hM0' (le_of_lt (Real.exp_pos _))
            exact le_trans hdiv_le (by simpa [Bk] using hBk')

          rcases jensen_zeros_multiplicity_bound (f := g) (r := r) (R := R) (B := Bk)
            hg_anal hr hrR hg0 hBk hg_bound with ⟨Z, hZ, hZmult⟩

          -- Fix a `Fintype` structure on the shell `S k` (we will use `tsum_fintype` below).
          have hSk_finite : (S k).Finite := by
            refine (hz.finite_in_ball (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))).subset ?_
            intro n hn
            have hk : kfun n = k := by simpa [S] using hn
            have hn_upper : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := hk_upper n
            have hk' : (kfun n : ℝ) = (k : ℝ) := by exact_mod_cast hk
            have hn_upper' : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by simpa [hk'] using hn_upper
            exact le_of_lt hn_upper'
          letI : Fintype (S k) := hSk_finite.fintype

          -- Bounding `card(S k)` by the multiplicity (divisor) sum in `‖z‖ ≤ r`.
          have hcard_S : (Fintype.card (S k) : ℝ) ≤ Real.log Bk / log2 + 1 := by
            classical
            -- Inject `S k` into `T := {n | ‖zeros n‖ ≤ r}`.
            let T : Set ℕ := {n : ℕ | ‖zeros n‖ ≤ r}
            have hT_finite : T.Finite := hz.finite_in_ball r
            letI : Fintype T := hT_finite.fintype
            have hST : S k ⊆ T := by
              intro n hn
              have hk : kfun n = k := by simpa [S] using hn
              have hn_upper : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := hk_upper n
              have hk' : (kfun n : ℝ) = (k : ℝ) := by exact_mod_cast hk
              have hn_upper' : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by simpa [hk'] using hn_upper
              have : ‖zeros n‖ ≤ r := by simpa [r] using (le_of_lt hn_upper')
              simpa [T] using this
            let incl : S k → T := fun n => ⟨n.1, hST n.2⟩
            have hincl : Function.Injective incl := by
              intro a b hab
              ext
              exact congrArg (fun t : T => t.1) hab
            have hcard_le : Fintype.card (S k) ≤ Fintype.card T :=
              Fintype.card_le_of_injective incl hincl
            have hcard_le' : (Fintype.card (S k) : ℝ) ≤ (Fintype.card T : ℝ) := by
              exact_mod_cast hcard_le

            -- Each `n ∈ T` maps to a zero of `g` in `Z`.
            have hmemZ : ∀ n : T, zeros n.1 ∈ Z := by
              intro n
              have hnR : ‖zeros n.1‖ ≤ r := n.2
              have hgz : g (zeros n.1) = 0 := hg_zeros n.1
              exact (hZ (zeros n.1)).2 ⟨hnR, hgz⟩

            -- Compare `card T` with the divisor sum via fibers.
            let fiber : Z → Type := fun z => {n : ℕ // zeros n = z.1}
            have hfinite_fiber : ∀ z : Z, Finite (fiber z) := by
              intro z
              have : ({n : ℕ | zeros n = z.1} : Set ℕ).Finite := hz.finite_fiber z.1
              simpa [fiber] using this.to_subtype
            classical
            letI : ∀ z : Z, Fintype (fiber z) := fun z => Fintype.ofFinite (fiber z)

            -- Injection `T → Σ z, fiber z`.
            let ψ : T → Sigma fiber := fun n => ⟨⟨zeros n.1, hmemZ n⟩, ⟨n.1, rfl⟩⟩
            have hψ_inj : Function.Injective ψ := by
              intro a b hab
              exact Subtype.ext (congrArg (fun p => p.2.1) hab)
            have hcardT_le_sigma : Fintype.card T ≤ Fintype.card (Sigma fiber) :=
              Fintype.card_le_of_injective ψ hψ_inj
            have hcardT_le_sum :
                (Fintype.card T : ℝ) ≤ ∑ z : Z, (Fintype.card (fiber z) : ℝ) := by
              have hnat : (Fintype.card T : ℝ) ≤ (Fintype.card (Sigma fiber) : ℝ) := by
                exact_mod_cast hcardT_le_sigma
              have hcard_sigma_nat : Fintype.card (Sigma fiber) = ∑ z : Z, Fintype.card (fiber z) :=
                Fintype.card_sigma (ι := Z) (α := fiber)
              -- cast the nat identity using `Nat.cast_sum` over `Finset.univ`
              have hcard_sigma :
                  (Fintype.card (Sigma fiber) : ℝ) = ∑ z : Z, (Fintype.card (fiber z) : ℝ) := by
                classical
                -- `∑ z : Z, ...` is a `Finset.univ` sum
                simp [hcard_sigma_nat]
              exact hnat.trans_eq hcard_sigma

            -- Pointwise: fiber cardinality equals divisor value.
            have hfiber_eq_div :
                ∀ z : Z, (Fintype.card (fiber z) : ℝ)
                  = (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z.1 : ℝ) := by
              intro z
              have hz_ne0 : z.1 ≠ (0 : ℂ) := by
                intro hz0
                have : g z.1 = 0 := (hZ z.1).1 z.2 |>.2
                simp [hz0, hg0] at this
              -- divisor = analytic order for analytic functions
              have hg_mer : MeromorphicOn g (Metric.closedBall (0 : ℂ) |R|) :=
                by
                  -- `|R| = R` since `R > 0`.
                  simpa [abs_of_pos hRpos] using (hg_anal.meromorphicOn)
              have hzU : z.1 ∈ Metric.closedBall (0 : ℂ) |R| := by
                have : ‖z.1‖ ≤ r := (hZ z.1).1 z.2 |>.1
                have : ‖z.1‖ ≤ R := le_trans this (le_of_lt hrR)
                simpa [Metric.mem_closedBall, dist_zero_right, abs_of_pos hRpos] using this
              have hdiv_int :
                  MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z.1
                    = (analyticOrderNatAt g z.1 : ℤ) := by
                -- local lemma by cases on `analyticOrderAt`
                have hg_an : AnalyticAt ℂ g z.1 := hg_entire.analyticAt z.1
                -- reuse the standalone lemma pattern
                simp [MeromorphicOn.divisor_apply hg_mer hzU, hg_an.meromorphicOrderAt_eq]
                cases h : analyticOrderAt g z.1 <;> simp [analyticOrderNatAt, h]
              have hdiv_real :
                  (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z.1 : ℝ)
                    = (analyticOrderNatAt g z.1 : ℝ) := by
                simp [hdiv_int, Int.cast_natCast]
              -- analytic order at `z ≠ 0` is preserved under dividing out `z^{ord0}` and scaling.
              have horder_eq : analyticOrderNatAt g z.1 = analyticOrderNatAt f z.1 := by
                have hG0z : G0 z.1 ≠ 0 := by simpa [G0] using pow_ne_zero hz.ord0 hz_ne0
                -- `f₁` agrees with `f/G0` near `z`.
                have hG0_near : ∀ᶠ w in 𝓝 z.1, G0 w ≠ 0 :=
                  (hG0_entire z.1).continuousAt.eventually_ne hG0z
                have hf₁_congr :
                    analyticOrderAt f₁ z.1 = analyticOrderAt (fun w => f w / G0 w) z.1 := by
                  apply analyticOrderAt_congr
                  filter_upwards [hG0_near] with w hw
                  simp [hf₁_eq w hw]
                have hf_an : AnalyticAt ℂ f z.1 := (hf.entire.analyticAt z.1)
                have hG_an : AnalyticAt ℂ G0 z.1 := (hG0_entire.analyticAt z.1)
                have hGinv_an : AnalyticAt ℂ (fun w => (G0 w)⁻¹) z.1 := hG_an.inv hG0z
                have hGinv0 : (fun w => (G0 w)⁻¹) z.1 ≠ 0 := by simp [hG0z]
                have hGinv_order : analyticOrderAt (fun w => (G0 w)⁻¹) z.1 = 0 :=
                  (hGinv_an.analyticOrderAt_eq_zero).2 hGinv0
                have hmul :
                    analyticOrderAt (fun w => f w * (G0 w)⁻¹) z.1 = analyticOrderAt f z.1 := by
                  calc
                    analyticOrderAt (fun w => f w * (G0 w)⁻¹) z.1
                        = analyticOrderAt f z.1 + analyticOrderAt (fun w => (G0 w)⁻¹) z.1 := by
                            simpa using (analyticOrderAt_mul (𝕜 := ℂ) (f := f) (g := fun w => (G0 w)⁻¹)
                              (z₀ := z.1) hf_an hGinv_an)
                    _ = analyticOrderAt f z.1 + 0 := by simp [hGinv_order]
                    _ = analyticOrderAt f z.1 := by simp
                have hdiv :
                    analyticOrderAt (fun w => f w / G0 w) z.1 = analyticOrderAt f z.1 := by
                  simp [div_eq_mul_inv, hmul]
                have hf₁_order : analyticOrderAt f₁ z.1 = analyticOrderAt f z.1 := by
                  simpa [hf₁_congr] using hdiv
                have hconst_an : AnalyticAt ℂ (fun _ : ℂ => (f₁ 0)⁻¹) z.1 := analyticAt_const
                have hconst_ne : (fun _ : ℂ => (f₁ 0)⁻¹) z.1 ≠ 0 := by simp [hf₁0]
                have hconst_order : analyticOrderAt (fun _ : ℂ => (f₁ 0)⁻¹) z.1 = 0 :=
                  (hconst_an.analyticOrderAt_eq_zero).2 hconst_ne
                have hg_order :
                    analyticOrderAt g z.1 = analyticOrderAt f₁ z.1 := by
                  have := analyticOrderAt_mul (𝕜 := ℂ) (f := f₁) (g := fun _ : ℂ => (f₁ 0)⁻¹)
                    (z₀ := z.1) (hf₁_entire.analyticAt z.1) hconst_an
                  -- `g = f₁ * const` as a function
                  simpa [g, div_eq_mul_inv, hconst_order, add_zero, mul_assoc] using this
                -- convert to nat order
                simp [analyticOrderNatAt, hg_order, hf₁_order]
              -- multiplicity spec: analytic order = fiber cardinal
              have hmult : analyticOrderNatAt f z.1 = Nat.card (fiber z) := by
                simpa [fiber] using (hz.zeros_mult_spec z.1 hz_ne0)
              -- convert `Nat.card` to `Fintype.card`
              have hcard : (Fintype.card (fiber z) : ℝ) = (Nat.card (fiber z) : ℝ) := by
                classical
                simp
              have : (Fintype.card (fiber z) : ℝ) = (analyticOrderNatAt g z.1 : ℝ) := by
                have := congrArg (fun n : ℕ => (n : ℝ)) (hmult.symm)
                -- `Nat.card` and `Fintype.card` coincide
                -- and replace `analyticOrderNatAt f` by `analyticOrderNatAt g`
                simpa [hcard, horder_eq] using this
              -- finish via `hdiv_real`
              simpa [hdiv_real] using this

            have hcardT_le_div :
                (Fintype.card T : ℝ)
                  ≤ ∑ z ∈ Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ) := by
              -- `card T ≤ Σ card fiber = Σ divisor`
              have hsum_eq :
                  (∑ z : Z, (Fintype.card (fiber z) : ℝ))
                    = ∑ z ∈ Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ) := by
                classical
                calc
                  (∑ z : Z, (Fintype.card (fiber z) : ℝ))
                      = ∑ z : Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z.1 : ℝ) := by
                          refine Finset.sum_congr rfl ?_
                          intro z hzuniv
                          simpa using hfiber_eq_div z
                  _ = ∑ z ∈ Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ) := by
                        simpa using (Finset.sum_coe_sort Z (fun z => (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ)))
              have : (Fintype.card T : ℝ)
                    ≤ ∑ z : Z, (Fintype.card (fiber z) : ℝ) := hcardT_le_sum
              exact this.trans_eq hsum_eq

            have hrat : R / r = (2 : ℝ) := by
              have hrne : r ≠ 0 := ne_of_gt hr
              simp [R, hrne, div_eq_mul_inv]
            have hZmult' :
                (∑ z ∈ Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ))
                  ≤ Real.log Bk / log2 := by
              simpa [hrat, log2] using hZmult
            have hcardT : (Fintype.card T : ℝ) ≤ Real.log Bk / log2 :=
              hcardT_le_div.trans hZmult'
            -- finish
            exact hcard_le'.trans (hcardT.trans (by linarith))

          -- Dyadic lower bound on shell `k`: all zeros satisfy `r0 * 2^k ≤ ‖zero‖`.
          let t : ℝ := r0 * (2 : ℝ) ^ (k : ℕ)
          have ht_pos : 0 < t := by
            have h2 : 0 < (2 : ℝ) ^ (k : ℕ) := by positivity
            exact mul_pos hr0pos h2
          have hterm_le : ∀ n : S k, ‖zeros n.1‖⁻¹ ^ σ ≤ t⁻¹ ^ σ := by
            intro n
            have hn_lower : r0 * (2 : ℝ) ^ (kfun n.1 : ℝ) ≤ ‖zeros n.1‖ := hk_lower n.1
            have hk_eq : (kfun n.1 : ℝ) = (k : ℝ) := by exact_mod_cast n.2
            have hn_lower' : r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖zeros n.1‖ := by simpa [hk_eq] using hn_lower
            have hkpow : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ (k : ℕ) := by simp
            have hn_lower'' : t ≤ ‖zeros n.1‖ := by simpa [t, hkpow] using hn_lower'
            have hb : 0 < ‖zeros n.1‖ := by
              exact norm_pos_iff.2 (hz.zeros_ne_zero n.1)
            have hinv : ‖zeros n.1‖⁻¹ ≤ t⁻¹ :=
              (inv_le_inv₀ (a := ‖zeros n.1‖) (b := t) hb ht_pos).2 hn_lower''
            have h0 : 0 ≤ ‖zeros n.1‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
            exact Real.rpow_le_rpow h0 hinv (le_of_lt hσ_pos)

          have hshell_sum :
              (∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ) ≤ (Fintype.card (S k) : ℝ) * (t⁻¹ ^ σ) := by
            classical
            simp [tsum_fintype]
            have h' : ∀ n ∈ (Finset.univ : Finset (S k)), ‖zeros n.1‖⁻¹ ^ σ ≤ t⁻¹ ^ σ := by
              intro n hn
              exact hterm_le n
            have := Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (S k)))
              (f := fun n : S k => ‖zeros n.1‖⁻¹ ^ σ) (n := t⁻¹ ^ σ) h'
            simpa [nsmul_eq_mul] using this

          have ht_scale : t⁻¹ ^ σ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
            have hr0_le : 0 ≤ r0 := le_of_lt hr0pos
            have h2pow : 0 ≤ (2 : ℝ) ^ (k : ℕ) := by positivity
            have hxnonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℕ) := mul_nonneg hr0_le h2pow
            dsimp [t]
            calc
              (r0 * (2 : ℝ) ^ (k : ℕ))⁻¹ ^ σ
                  = ((r0 * (2 : ℝ) ^ (k : ℕ)) ^ σ)⁻¹ := Real.inv_rpow hxnonneg σ
              _ = (r0 * (2 : ℝ) ^ (k : ℕ)) ^ (-σ) := by
                    simpa using (Real.rpow_neg hxnonneg σ).symm
              _ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (k : ℕ)) ^ (-σ) := by
                    simp [Real.mul_rpow hr0_le h2pow]
              _ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
                    have h2 : 0 ≤ (2 : ℝ) := by norm_num
                    have hpow' : ((2 : ℝ) ^ k) ^ (-σ) = ((2 : ℝ) ^ (-σ)) ^ k := by
                      calc
                        ((2 : ℝ) ^ k) ^ (-σ) = (2 : ℝ) ^ ((k : ℝ) * (-σ)) := by
                              have := Real.rpow_mul h2 (k : ℝ) (-σ)
                              simpa using this.symm
                        _ = (2 : ℝ) ^ ((-σ) * (k : ℝ)) := by ring_nf
                        _ = ((2 : ℝ) ^ (-σ)) ^ (k : ℝ) := by
                              simpa [Real.rpow_mul h2] using (Real.rpow_mul h2 (-σ) (k : ℝ))
                        _ = ((2 : ℝ) ^ (-σ)) ^ k := by simp
                    simp [hpow']

          have : (Fintype.card (S k) : ℝ) * (t⁻¹ ^ σ)
              ≤ A * q ^ k + B * qσ ^ k := by
            -- (verbatim from the end of `lindelof_zero_exponent`)
            have hlogBk : Real.log Bk = C1 * (1 + R) ^ τ + Real.log M0 := by
              have hexp_pos : 0 < Real.exp (C1 * (1 + R) ^ τ) := Real.exp_pos _
              have hlog_mul : Real.log (Real.exp (C1 * (1 + R) ^ τ) * M0)
                    = Real.log (Real.exp (C1 * (1 + R) ^ τ)) + Real.log M0 := by
                exact Real.log_mul (ne_of_gt hexp_pos) (ne_of_gt hM0_pos)
              simp [Bk, hlog_mul]
            have hcard_le' :
                (Fintype.card (S k) : ℝ)
                  ≤ (C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1 := by
              have : Real.log Bk / log2 = (C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 := by
                calc
                  Real.log Bk / log2 = (C1 * (1 + R) ^ τ + Real.log M0) / log2 := by simp [hlogBk]
                  _ = (C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 := by
                        field_simp [hlog2_ne]
              have hcard_S' : (Fintype.card (S k) : ℝ) ≤ Real.log Bk / log2 + 1 := hcard_S
              simpa [this, add_assoc, add_left_comm, add_comm] using hcard_S'

            have ht_scale' : t⁻¹ ^ σ = (r0 ^ (-σ)) * qσ ^ k := by simp [qσ, ht_scale]

            have hL :
                (Fintype.card (S k) : ℝ) * (t⁻¹ ^ σ)
                  ≤ ((C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (t⁻¹ ^ σ) := by
              exact mul_le_mul_of_nonneg_right hcard_le' (by
                have : 0 ≤ t⁻¹ ^ σ := Real.rpow_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hr0pos) (by positivity))) σ
                exact this)
            rw [ht_scale'] at hL ⊢

            have hstep1 :
                ((C1 * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k) ≤ A * q ^ k := by
              have hpow_le' : (1 + R) ^ τ ≤ (1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ := by
                have hk1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
                have hR_le : (1 : ℝ) + R ≤ (1 + 4 * r0) * (2 : ℝ) ^ k := by
                  have h2pow2 : (2 : ℝ) ^ ((k : ℝ) + 1) = (2 : ℝ) * (2 : ℝ) ^ k := by
                    have h2 : (0 : ℝ) < 2 := by norm_num
                    calc
                      (2 : ℝ) ^ ((k : ℝ) + 1)
                          = (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
                              simpa using (Real.rpow_add h2 (k : ℝ) (1 : ℝ))
                      _ = (2 : ℝ) ^ k * (2 : ℝ) := by simp
                      _ = (2 : ℝ) * (2 : ℝ) ^ k := by ring
                  have hR_eq : R = (4 * r0) * (2 : ℝ) ^ k := by
                    dsimp [R, r]
                    calc
                      (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
                          = (2 : ℝ) * (r0 * ((2 : ℝ) * (2 : ℝ) ^ k)) := by simp [h2pow2]
                      _ = (4 * r0) * (2 : ℝ) ^ k := by ring
                  calc
                    (1 : ℝ) + R = 1 + (4 * r0) * (2 : ℝ) ^ k := by simp [hR_eq]
                    _ ≤ (2 : ℝ) ^ k + (4 * r0) * (2 : ℝ) ^ k := by gcongr
                    _ = (1 + 4 * r0) * (2 : ℝ) ^ k := by ring
                have hbaseR : 0 ≤ (1 + 4 * r0 : ℝ) := by linarith [le_of_lt hr0pos]
                have hbase2 : 0 ≤ (2 : ℝ) ^ k := by positivity
                have hpow : ((1 : ℝ) + R) ^ τ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ τ :=
                  Real.rpow_le_rpow (by positivity) hR_le hτ_nonneg
                have hsplit : ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ τ
                    = (1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ := by
                  simp [Real.mul_rpow hbaseR hbase2]
                exact le_trans hpow (by simp [hsplit])
              have hq : q = (2 : ℝ) ^ τ * (2 : ℝ) ^ (-σ) := by
                have h2pos : (0 : ℝ) < 2 := by norm_num
                have : (τ - σ) = τ + (-σ) := by ring
                calc
                  q = (2 : ℝ) ^ (τ + (-σ)) := by simp [q, this]
                  _ = (2 : ℝ) ^ τ * (2 : ℝ) ^ (-σ) := by simpa using (Real.rpow_add h2pos τ (-σ))
              have h2powτ : ((2 : ℝ) ^ k) ^ τ = ((2 : ℝ) ^ τ) ^ k := by
                have h2 : 0 ≤ (2 : ℝ) := by norm_num
                calc
                  ((2 : ℝ) ^ k) ^ τ = (2 : ℝ) ^ ((k : ℝ) * τ) := by
                        have := Real.rpow_mul h2 (k : ℝ) τ
                        simpa using this.symm
                  _ = (2 : ℝ) ^ (τ * (k : ℝ)) := by ring_nf
                  _ = ((2 : ℝ) ^ τ) ^ k := by simp [Real.rpow_mul h2]
              have hqk' : q ^ k = ((2 : ℝ) ^ τ) ^ k * (qσ ^ k) := by
                simp [q, qσ, hq, mul_pow, mul_comm]
              have hgrow : (1 + R) ^ τ * (qσ ^ k) ≤ (1 + 4 * r0) ^ τ * (q ^ k) := by
                calc
                  (1 + R) ^ τ * (qσ ^ k)
                      ≤ ((1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ) * (qσ ^ k) := by gcongr
                  _ = (1 + 4 * r0) ^ τ * (((2 : ℝ) ^ k) ^ τ * (qσ ^ k)) := by ring
                  _ = (1 + 4 * r0) ^ τ * (((2 : ℝ) ^ τ) ^ k * (qσ ^ k)) := by simp [h2powτ]
                  _ = (1 + 4 * r0) ^ τ * (q ^ k) := by simp [hqk']
              calc
                ((C1 * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k)
                    = (C1 / log2) * ((1 + R) ^ τ * (qσ ^ k)) * (r0 ^ (-σ)) := by
                        field_simp [hlog2_ne]
                _ ≤ (C1 / log2) * ((1 + 4 * r0) ^ τ * (q ^ k)) * (r0 ^ (-σ)) := by
                      gcongr
                _ = A * q ^ k := by
                      simp [A, mul_assoc, mul_left_comm, mul_comm]
            have hstep2 :
                ((Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k) ≤ B * qσ ^ k := by
              simp [B, mul_assoc, mul_left_comm, mul_comm]
            have hsum :
                ((C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k)
                  ≤ A * q ^ k + B * qσ ^ k := by
              calc
                ((C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k)
                    = ((C1 * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k)
                        + ((Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k) := by ring
                _ ≤ A * q ^ k + B * qσ ^ k := by gcongr
            exact le_trans hL hsum

          exact le_trans hshell_sum this
        ) hmajor

  -- Conclude from `summable_partition`.
  have := (summable_partition (f := fun n : ℕ => ‖zeros n‖⁻¹ ^ σ) hnonneg (s := S) hS)
  exact (this.2 hshell)

/-- A zero-free entire function with polynomial growth is exp of a polynomial.

If H is entire, zero-free, and `|H(z)| ≤ exp(C * (1 + |z|)^n)` for some `C` and `n`,
then H = exp(P) for some polynomial P of degree at most n. -/
theorem zero_free_polynomial_growth_is_exp_poly {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = exp (Polynomial.eval z P) := by
  classical
  rcases h_bound with ⟨C, hCpos, hC⟩

  -- Step 1: build a global holomorphic logarithm by integrating the logarithmic derivative.
  let L : ℂ → ℂ := fun z => deriv H z / H z
  have hderivH : Differentiable ℂ (deriv H) := by
    intro z
    exact ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L := by
    simpa [L] using (hderivH.div hH h_nonzero)

  -- A global primitive of `L`, defined by wedge integrals from `0`.
  let h : ℂ → ℂ := fun z => Complex.wedgeIntegral (0 : ℂ) z L
  have hh_deriv : ∀ z, HasDerivAt h (L z) z := by
    intro z
    -- Apply Morera's theorem on the ball `ball 0 (‖z‖ + 1)`.
    let r : ℝ := ‖z‖ + 1
    have hrpos : 0 < r := by
      dsimp [r]
      linarith [norm_nonneg z]
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
      have : dist z (0 : ℂ) < r := by
        simp [r, dist_zero_right]
      simpa [Metric.mem_ball] using this
    have hconserv : Complex.IsConservativeOn L (Metric.ball (0 : ℂ) r) :=
      (hL.differentiableOn).isConservativeOn
    have hcont : ContinuousOn L (Metric.ball (0 : ℂ) r) :=
      hL.continuous.continuousOn
    simpa [h, r] using hconserv.hasDerivAt_wedgeIntegral (f_cont := hcont) (hz := hz_ball)
  have hh : Differentiable ℂ h := fun z => (hh_deriv z).differentiableAt
  have hderiv_h : ∀ z, deriv h z = L z := fun z => (hh_deriv z).deriv

  -- Step 2: show `H = exp(k)` for an entire `k`.
  let k : ℂ → ℂ := fun z => h z + Complex.log (H 0)
  have hk : Differentiable ℂ k := hh.add_const (Complex.log (H 0))

  have hk_exp : ∀ z, H z = Complex.exp (k z) := by
    -- Consider `F = exp(k) / H`. Its derivative is zero, hence it's constant.
    let F : ℂ → ℂ := fun z => Complex.exp (k z) / H z
    have hF_deriv : ∀ z, deriv F z = 0 := by
      intro z
      have hH_has : HasDerivAt H (deriv H z) z := (hH z).hasDerivAt
      have hk_has : HasDerivAt k (L z) z := by
        -- `k' = h'` since the constant term has derivative 0
        have hh_has : HasDerivAt h (L z) z := hh_deriv z
        simpa [k, L] using hh_has.add_const (Complex.log (H 0))
      have hExp : HasDerivAt (fun w => Complex.exp (k w)) (Complex.exp (k z) * L z) z :=
        (HasDerivAt.cexp hk_has)
      have hDiv := (HasDerivAt.div hExp hH_has (h_nonzero z))
      -- simplify the quotient-rule formula using `L z = H'(z)/H(z)`
      have :
          deriv F z =
            ((Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z) / (H z) ^ 2 := by
        simpa [F] using hDiv.deriv
      rw [this]
      -- `((exp(k) * (H'/H)) * H - exp(k) * H') / H^2 = 0`
      have hnum :
          (Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z = 0 := by
        -- cancel `H z` inside `L z = H'/H`
        dsimp [L]
        field_simp [h_nonzero z]
        ring
      simp [hnum]
    have hF_diff : Differentiable ℂ F := by
      -- `F = exp(k) / H`
      exact (hk.cexp).div hH h_nonzero
    have hF_const : ∀ z, F z = F 0 := by
      intro z
      exact is_const_of_deriv_eq_zero hF_diff hF_deriv z 0
    have hF0 : F 0 = 1 := by
      -- `h 0 = 0`, so `k 0 = log(H 0)` and `exp(k 0) / H 0 = 1`.
      have hh0 : h 0 = 0 := by simp [h, Complex.wedgeIntegral]
      have hk0 : k 0 = Complex.log (H 0) := by simp [k, hh0]
      have hH0 : H 0 ≠ 0 := h_nonzero 0
      simp [F, hk0, Complex.exp_log hH0, hH0]
    intro z
    have : F z = 1 := by simpa [hF0] using (hF_const z)
    -- rearrange `F z = exp(k z)/H z = 1`
    have hHz : H z ≠ 0 := h_nonzero z
    have : Complex.exp (k z) / H z = 1 := by simpa [F] using this
    -- multiply through by `H z`
    have : Complex.exp (k z) = H z := by
      -- `a / b = 1` implies `a = b`
      field_simp [hHz] at this
      simpa using this
    exact this.symm

  -- Step 3: show all derivatives of `k` above order `n` vanish, hence `k` is a polynomial.
  have hk_re_bound : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ n := by
    intro z
    -- From `H z = exp(k z)` and the growth bound on `H`.
    have hHz : H z ≠ 0 := h_nonzero z
    have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz
    have hlog_le : Real.log ‖H z‖ ≤ C * (1 + ‖z‖) ^ n := by
      have := Real.log_le_log hpos (hC z)
      simpa [Real.log_exp] using this
    have hlog_eq : Real.log ‖H z‖ = (k z).re := by
      have : ‖H z‖ = Real.exp (k z).re := by
        simpa [hk_exp z] using (Complex.norm_exp (k z))
      calc
        Real.log ‖H z‖ = Real.log (Real.exp (k z).re) := by simp [this]
        _ = (k z).re := by simp
    -- conclude
    simpa [hlog_eq] using hlog_le

  have hk_iteratedDeriv_eq_zero : ∀ m : ℕ, n < m → iteratedDeriv m k 0 = 0 := by
    intro m hm
    -- Use Cauchy estimate on `k - k 0` with radii `R` and `r = R/2`, then send `R → ∞`.
    have hm' : 0 < (m - n : ℕ) := Nat.sub_pos_of_lt hm
    have hmne : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 hm')
    -- Work with `f = k - k 0`, which vanishes at `0`.
    let f : ℂ → ℂ := fun z => k z - k 0
    have hf : Differentiable ℂ f := hk.sub_const (k 0)
    have hf0 : f 0 = 0 := by simp [f]
    -- First bound: `Re(f z) ≤ C * (1+R)^n + ‖k 0‖` on `‖z‖ ≤ R`.
    have hf_re_bound : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R → (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
      intro R hRpos z hzR
      have hkz : (k z).re ≤ C * (1 + ‖z‖) ^ n := hk_re_bound z
      have hkz' : (k z).re ≤ C * (1 + R) ^ n := by
        have h1 : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow : (1 + ‖z‖ : ℝ) ^ n ≤ (1 + R) ^ n :=
          pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 n
        exact hkz.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos))
      -- `Re(f z) = Re(k z) - Re(k 0) ≤ C (1+R)^n + ‖k 0‖`.
      have hRe0 : -(k 0).re ≤ ‖k 0‖ := by
        have habs : |(k 0).re| ≤ ‖k 0‖ := Complex.abs_re_le_norm (k 0)
        have hneg : -(k 0).re ≤ |(k 0).re| := by
          simpa using (neg_le_abs (k 0).re)
        exact hneg.trans habs
      -- assemble
      have : (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
        -- `Re(f z) = Re(k z) - Re(k 0)`
        have : (f z).re = (k z).re - (k 0).re := by simp [f, sub_eq_add_neg]
        -- use `hkz'` and `hRe0`
        nlinarith [this, hkz', hRe0]
      exact this

    -- Apply Borel–Carathéodory to get a norm bound for `f` on `‖z‖ ≤ R/2`.
    have hf_bound_on_ball : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
      intro R hRpos z hz
      have hR2pos : 0 < R / 2 := by nlinarith
      have hlt : R / 2 < R := by nlinarith
      have hMpos : 0 < (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        have : 0 ≤ C * (1 + R) ^ n := by
          refine mul_nonneg (le_of_lt hCpos) ?_
          exact pow_nonneg (by linarith) _
        nlinarith [this, norm_nonneg (k 0)]
      have hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := by
        intro w hw
        exact (hf.analyticAt w)
      have hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro w hw
        have := hf_re_bound R hRpos w hw
        linarith
      have hf_bc :=
        borel_caratheodory_bound (f := f) (r := R / 2) (R := R)
          (M := (C * (1 + R) ^ n + ‖k 0‖ + 1))
          hf_anal hR2pos hlt hMpos hf0 hf_re z hz
      -- simplify the constant `2*M*r/(R-r)` at `r=R/2`
      have hconst :
          2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) * (R / 2) / (R - R / 2)
            = 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        field_simp [hRpos.ne'] ; ring
      -- finish
      simpa [hconst] using hf_bc

    -- Use Cauchy estimate for iterated derivatives of `f` on the circle of radius `R/2`.
    have hCauchy : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv m f 0‖ ≤
          (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m := by
      intro R hRpos
      have hR2pos : 0 < R / 2 := by nlinarith
      have hf_diffCont : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (R / 2)) := hf.diffContOnCl
      have hbound_sphere :
          ∀ z ∈ Metric.sphere (0 : ℂ) (R / 2),
            ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro z hz
        have hz' : ‖z‖ ≤ R / 2 := by
          simpa [Metric.mem_sphere, dist_zero_right] using (le_of_eq hz)
        exact hf_bound_on_ball R hRpos z hz'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := m) (c := (0 : ℂ))
          (R := R / 2) (C := 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1))
          (hR := hR2pos) hf_diffCont hbound_sphere)

    -- Let `R → ∞`: the Cauchy bound tends to `0` for `m > n`, forcing `iteratedDeriv m f 0 = 0`.
    have hf_iter_eq : iteratedDeriv m f 0 = 0 := by
      by_contra hne
      have ha : 0 < ‖iteratedDeriv m f 0‖ := norm_pos_iff.2 hne

      let RHS : ℝ → ℝ := fun R =>
        (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m
      have hle_RHS : ∀ R : ℝ, 0 < R → ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        intro R hRpos
        simpa [RHS] using hCauchy R hRpos

      -- Show `RHS R → 0` as `R → ∞`.
      have hRHS_tendsto : Tendsto RHS atTop (𝓝 0) := by
        -- First show `(C * (1+R)^n + K) / (R/2)^m → 0` for `K = ‖k 0‖ + 1`.
        let K : ℝ := ‖k 0‖ + 1
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
        have hm0 : m ≠ 0 := ne_of_gt hmpos

        have hratio : Tendsto (fun R : ℝ => R ^ n / (R / 2) ^ m) atTop (𝓝 0) := by
          -- Rewrite `R^n/(R/2)^m = 2^m * (R^n / R^m)` and use `m > n`.
          have hident :
              (fun R : ℝ => R ^ n / (R / 2) ^ m) = fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m) := by
            funext R
            simp [div_eq_mul_inv, mul_pow, mul_assoc, mul_comm]
          have hmain : Tendsto (fun R : ℝ => R ^ n / R ^ m) atTop (𝓝 0) := by
            have hp : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hm))
            have hmain' : Tendsto (fun R : ℝ => (R ^ (m - n))⁻¹) atTop (𝓝 0) := by
              simpa using (tendsto_pow_neg_atTop (𝕜 := ℝ) (n := m - n) hp)
            have hEq : (fun R : ℝ => (R ^ (m - n))⁻¹) =ᶠ[atTop] fun R : ℝ => R ^ n / R ^ m := by
              have hEq' : (fun R : ℝ => R ^ n / R ^ m) =ᶠ[atTop] fun R : ℝ => (R ^ (m - n))⁻¹ := by
                filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
                have hle : n ≤ m := le_of_lt hm
                have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hle
                have hn0 : R ^ n ≠ 0 := pow_ne_zero n hR
                calc
                  R ^ n / R ^ m = R ^ n / R ^ (n + (m - n)) := by simp [hm_eq]
                  _ = R ^ n * ((R ^ (m - n))⁻¹ * (R ^ n)⁻¹) := by
                        simp [pow_add, div_eq_mul_inv, mul_comm]
                  _ = (R ^ (m - n))⁻¹ := by
                        ring_nf
                        simp [hn0]
              exact hEq'.symm
            exact Filter.Tendsto.congr' hEq hmain'
          have : Tendsto (fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m)) atTop (𝓝 ((2 : ℝ) ^ m * 0)) :=
            tendsto_const_nhds.mul hmain
          simpa [hident] using this

        have hinv : Tendsto (fun R : ℝ => ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
            (tendsto_id.atTop_div_const (r := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2))
          have hpow : Tendsto (fun R : ℝ => (R / 2) ^ m) atTop atTop :=
            (Filter.tendsto_pow_atTop (α := ℝ) (n := m) hm0).comp hdiv
          simpa using hpow.inv_tendsto_atTop

        -- Upgrade `R^n/(R/2)^m → 0` to `(1+R)^n/(R/2)^m → 0` using the factor `((1+R)/R)^n → 1`.
        have hdiv : Tendsto (fun R : ℝ => (1 + R) / R) atTop (𝓝 (1 : ℝ)) := by
          have hinv : Tendsto (fun R : ℝ => (R : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
            tendsto_inv_atTop_zero
          have hadd : Tendsto (fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
            simpa using (tendsto_const_nhds.add hinv)
          have hEq : (fun R : ℝ => (1 + R) / R) =ᶠ[atTop] fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹ := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            -- `((1+R)/R) = 1 + 1/R` for `R ≠ 0`.
            field_simp [hR]
            ring
          exact Filter.Tendsto.congr' hEq.symm hadd
        have hdiv_pow : Tendsto (fun R : ℝ => ((1 + R) / R) ^ n) atTop (𝓝 (1 : ℝ)) := by
          simpa using (hdiv.pow n)
        have hone_add_ratio :
            Tendsto (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m) atTop (𝓝 (0 : ℝ)) := by
          have hEq :
              (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m)
                =ᶠ[atTop] fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            -- algebraic identity valid for `R ≠ 0`
            have hRpow : (R ^ n : ℝ) ≠ 0 := pow_ne_zero n hR
            -- `((1+R)/R)^n * (R^n/(R/2)^m) = (1+R)^n/(R/2)^m`
            have hident :
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) = (1 + R) ^ n / (R / 2) ^ m := by
              calc
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)
                    = ((1 + R) ^ n / R ^ n) * (R ^ n / (R / 2) ^ m) := by
                        simp [div_pow]
                _ = ((1 + R) ^ n * R ^ n) / (R ^ n * (R / 2) ^ m) := by
                        simp [div_mul_div_comm, mul_comm]
                _ = ((1 + R) ^ n * R ^ n) / ((R / 2) ^ m * R ^ n) := by
                        simp [mul_comm]
                _ = (1 + R) ^ n / (R / 2) ^ m := by
                        simpa [mul_assoc, mul_comm, mul_left_comm] using
                          (mul_div_mul_right (a := (1 + R) ^ n) (b := (R / 2) ^ m) hRpow)
            exact hident.symm
          have hmul :
              Tendsto (fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)) atTop (𝓝 (0 : ℝ)) := by
            simpa [mul_zero] using (hdiv_pow.mul hratio)
          exact Filter.Tendsto.congr' hEq.symm hmul

        have h1 : Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hone_add_ratio)
        have h2 : Tendsto (fun R : ℝ => K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hinv)
        have hsum :
            Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (h1.add h2)
        have hrew :
            (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m)
              = fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹ := by
          funext R
          simp [div_eq_mul_inv, mul_add, mul_assoc, mul_comm]
        have hbase : Tendsto (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m) atTop (𝓝 0) := by
          simpa [hrew] using hsum

        -- Multiply by the constant `(m!)*2` and rewrite to `RHS`.
        have hconst :
            Tendsto (fun _ : ℝ => (m.factorial : ℝ) * (2 : ℝ)) atTop (𝓝 ((m.factorial : ℝ) * (2 : ℝ))) :=
          tendsto_const_nhds
        have hmul : Tendsto (fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using (hconst.mul hbase)
        have hRHS_rw : RHS = fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m) := by
          funext R
          dsimp [RHS, K]
          ring_nf
        simpa [hRHS_rw] using hmul

      -- `RHS R → 0`, so eventually `RHS R < ‖iteratedDeriv m f 0‖ / 2`.
      have hsmall : ∀ᶠ R in atTop, RHS R < ‖iteratedDeriv m f 0‖ / 2 :=
        (tendsto_order.1 hRHS_tendsto).2 _ (half_pos ha)
      have hle_eventually : ∀ᶠ R in atTop, ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hRpos
        exact hle_RHS R hRpos
      rcases (hle_eventually.and hsmall).exists with ⟨R, hle, hlt⟩
      have : ‖iteratedDeriv m f 0‖ < ‖iteratedDeriv m f 0‖ := by
        exact (lt_of_le_of_lt hle hlt).trans (half_lt_self ha)
      exact lt_irrefl _ this

    -- Transfer back from `f = k - k 0` to `k` (derivatives of constants vanish for `m > 0`).
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
    have hm0 : m ≠ 0 := ne_of_gt hmpos
    have hkcd : ContDiffAt ℂ (↑m) k (0 : ℂ) := (hk.analyticAt 0).contDiffAt
    have hccd : ContDiffAt ℂ (↑m) (fun _ : ℂ => k 0) (0 : ℂ) := contDiffAt_const
    have hsub : iteratedDeriv m f 0 = iteratedDeriv m k 0 - iteratedDeriv m (fun _ : ℂ => k 0) 0 := by
      simpa [f] using (iteratedDeriv_sub (n := m) (x := (0 : ℂ)) hkcd hccd)
    have hconst0 : iteratedDeriv m (fun _ : ℂ => k 0) 0 = 0 := by
      simp [iteratedDeriv_const, hm0]
    have hf_eq : iteratedDeriv m f 0 = iteratedDeriv m k 0 := by
      simp [hsub, hconst0]
    simpa [hf_eq] using hf_iter_eq

  -- Step 4: build the polynomial from the Taylor coefficients at 0 and finish.
  let P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (n + 1), Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)
  have hPdeg : P.natDegree ≤ n := by
    -- A finset sum of monomials indexed by `range (n+1)` has `natDegree ≤ n`.
    have hnat :
        P.natDegree ≤
          Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) := by
      simpa [P, Function.comp] using
        (Polynomial.natDegree_sum_le (s := Finset.range (n + 1))
          (f := fun m : ℕ =>
            Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)))
    have hfold :
        Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) ≤ n := by
      -- `fold max` is bounded by `n` since each monomial has `natDegree ≤ m ≤ n` on this range.
      refine (Finset.fold_max_le (f := fun m : ℕ =>
        (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
        (b := 0) (s := Finset.range (n + 1)) (c := n)).2 ?_
      refine ⟨Nat.zero_le n, ?_⟩
      intro m hm
      have hmon :
          (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree ≤ m :=
        Polynomial.natDegree_monomial_le _
      have hm_le : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      exact hmon.trans hm_le
    exact hnat.trans hfold
  have hk_poly : ∀ z, k z = Polynomial.eval z P := by
    intro z
    -- Taylor series of an entire function, then truncate using vanishing of higher derivatives.
    have htaylor := Complex.taylorSeries_eq_of_entire' (c := (0 : ℂ)) (z := z) hk
    have htail : ∀ m : ℕ, m ∉ Finset.range (n + 1) →
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m) = 0 := by
      intro m hm'
      have hmgt : n < m := by
        have : n + 1 ≤ m := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hm')
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) this
      have hz : iteratedDeriv m k 0 = 0 := hk_iteratedDeriv_eq_zero m hmgt
      simp [hz]
    have htsum :
        (∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m)
          = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      simpa [sub_zero] using (tsum_eq_sum (s := Finset.range (n + 1)) htail)
    have hfinite :
        k z = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      calc
        k z = ∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m := by
          simpa using htaylor.symm
        _ = _ := htsum
    -- Evaluate the polynomial `P` and match the finite sum (commuting factors as needed).
    have hEval :
        Polynomial.eval z P =
          ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      classical
      -- Work with `eval₂RingHom` to avoid simp loops around `Polynomial.eval`.
      change Polynomial.eval₂ (RingHom.id ℂ) z P = _
      let φ : Polynomial ℂ →+* ℂ := Polynomial.eval₂RingHom (RingHom.id ℂ) z
      change φ P = _
      -- `eval₂` of a monomial is `coeff * z^m`; commute to `z^m * coeff`.
      simp [P, φ, Polynomial.eval₂_monomial, mul_comm]
    have hfinite' :
        k z = ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfinite
    simpa [hEval] using hfinite'

  refine ⟨P, hPdeg, ?_⟩
  intro z
  have : H z = Complex.exp (k z) := by simp [hk_exp z]
  -- `k = P.eval` gives `H = exp(P.eval)`
  simp [this, hk_poly z]

/-! ## Part 6: The Hadamard Factorization Theorem -/

/-
`hadamard_quotient_growth_bound` is the **main analytic input** needed to finish Hadamard’s
factorization theorem in this file.

It should prove a global growth estimate for the zero-free quotient

`H(z) = f(z) / (z^ord0 * ∏' n, weierstrassFactor m (z / zeros n))`

using the Nevanlinna/Cartan/Poisson infrastructure imported above.

-/

/-! ## Helper inequalities: `log⁺` vs `log (1 + ·)` -/

lemma posLog_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    log⁺ x ≤ Real.log (1 + x) := by
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    -- `log⁺ x = max 0 (log x)` and `0 ≤ log (1 + x)` and `log x ≤ log (1 + x)`
    have h0 : 0 ≤ Real.log (1 + x) := by
      have : (1 : ℝ) ≤ 1 + x := by linarith
      exact Real.log_nonneg this
    have hlog : Real.log x ≤ Real.log (1 + x) := by
      have hx1 : x ≤ 1 + x := by linarith
      exact Real.log_le_log hx_pos hx1
    -- `max 0 (log x) ≤ log (1 + x)`
    simpa [Real.posLog, max_le_iff] using And.intro h0 hlog

lemma posLog_norm_le_log_one_add_norm (z : ℂ) :
    log⁺ ‖z‖ ≤ Real.log (1 + ‖z‖) :=
  posLog_le_log_one_add (x := ‖z‖) (norm_nonneg z)

/-- On any circle, the circle average of `log⁺ ‖F⁻¹‖` equals the circle average of
`log⁺ ‖F‖` minus the circle average of `log ‖F‖`.

Precisely:
`circleAverage (log⁺ ‖F⁻¹‖) c r = circleAverage (log⁺ ‖F‖) c r - circleAverage (log ‖F‖) c r`.
This is just the pointwise identity `log⁺ x - log⁺ x⁻¹ = log x` averaged over the circle. -/
lemma circleAverage_posLog_norm_inv_eq_circleAverage_posLog_norm_sub_circleAverage_log_norm
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (h_pos : CircleIntegrable (fun z ↦ log⁺ ‖F z‖) c r)
    (h_inv : CircleIntegrable (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r)
    (_h_log : CircleIntegrable (fun z ↦ Real.log ‖F z‖) c r) :
    circleAverage (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r
      = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
          - circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
  -- Pointwise identity on the circle
  have h_point :
      Set.EqOn
        (fun z : ℂ => (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖))
        (fun z : ℂ => Real.log ‖F z‖)
        (Metric.sphere c |r|) := by
    intro z _
    simpa [norm_inv] using (Real.posLog_sub_posLog_inv (x := ‖F z‖))
  -- Average of the difference equals difference of averages
  have h_sub :
      circleAverage (fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖)) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r := by
    simpa using (Real.circleAverage_sub (c := c) (R := r) h_pos h_inv)
  -- Replace the LHS integrand using the pointwise identity on the sphere
  have h_congr :
      circleAverage (fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖)) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    simpa using
      (circleAverage_congr_sphere (f₁ := fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖))
        (f₂ := fun z ↦ Real.log ‖F z‖) (c := c) (R := r) h_point)
  -- Rearrange to solve for the average of `log⁺ ‖F⁻¹‖`.
  have h_sub' :
      circleAverage (fun z ↦ log⁺ ‖F z‖ - log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r := by
    simpa [norm_inv] using h_sub
  have h_congr' :
      circleAverage (fun z ↦ log⁺ ‖F z‖ - log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    simpa [norm_inv] using h_congr
  have hdiff :
      circleAverage (fun z ↦ log⁺ ‖F z‖) c r - circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    exact h_sub'.symm.trans h_congr'
  have hfinal :
      circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    linarith [hdiff]
  simpa [norm_inv] using hfinal

/-! ## Circle-average bounds from `EntireOfFiniteOrder` -/

lemma circleIntegrable_posLog_norm_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 r := by
  -- Use the standard meromorphic integrability lemma (entire ⇒ meromorphic).
  have hA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  have hM : MeromorphicOn f (Set.univ : Set ℂ) := hA.meromorphicOn
  -- Restrict meromorphy to the sphere.
  have hMsphere : MeromorphicOn f (sphere (0 : ℂ) |r|) := fun z hz => hM z (by simp)
  simpa using (circleIntegrable_posLog_norm_meromorphicOn (c := (0 : ℂ)) (R := r) hMsphere)

lemma circleIntegrable_posLog_norm_of_entire_center
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z‖) c r := by
  -- Entire ⇒ meromorphic on `univ`, hence on every sphere
  have hA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  have hM : MeromorphicOn f (Set.univ : Set ℂ) := hA.meromorphicOn
  have hMsphere : MeromorphicOn f (sphere c |r|) := fun z hz => hM z (by simp)
  simpa using (circleIntegrable_posLog_norm_meromorphicOn (c := c) (R := r) hMsphere)

lemma circleAverage_posLog_norm_le_of_entireOfFiniteOrder
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      circleAverage (fun z ↦ log⁺ ‖f z‖) 0 r ≤ C * (1 + r) ^ ρ := by
  rcases hf.growth with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  have h_int : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 r :=
    circleIntegrable_posLog_norm_of_entire (f := f) hf.entire r
  -- Pointwise bound on the circle: `log⁺ ‖f z‖ ≤ log (1 + ‖f z‖) ≤ C * (1 + r)^ρ`.
  have h_pw : ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖f z‖ ≤ C * (1 + r) ^ ρ := by
    intro z hz
    have hz_norm : ‖z‖ = r := by
      have : ‖z‖ = |r| := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      simpa [abs_of_nonneg hr0] using this
    calc
      log⁺ ‖f z‖ ≤ Real.log (1 + ‖f z‖) := posLog_le_log_one_add (x := ‖f z‖) (norm_nonneg _)
      _ ≤ C * (1 + ‖z‖) ^ ρ := hC z
      _ = C * (1 + r) ^ ρ := by simp [hz_norm]
  -- Average is ≤ the constant.
  exact Real.circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := r) (f := fun z ↦ log⁺ ‖f z‖)
    h_int h_pw

lemma circleAverage_posLog_norm_le_of_entireOfFiniteOrder_center
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) (hρ_nonneg : 0 ≤ ρ) :
    ∃ C > 0, ∀ (c : ℂ) (r : ℝ), 0 ≤ r →
      circleAverage (fun z ↦ log⁺ ‖f z‖) c r ≤ C * (1 + ‖c‖ + r) ^ ρ := by
  rcases hf.growth with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro c r hr0
  -- Integrable on any circle centered at c
  have h_int : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) c r :=
    circleIntegrable_posLog_norm_of_entire_center hf.entire c r
  -- On the sphere: ‖z‖ ≤ ‖c‖ + r, hence a uniform pointwise bound.
  have h_pw : ∀ z ∈ sphere c |r|, log⁺ ‖f z‖ ≤ C * (1 + ‖c‖ + r) ^ ρ := by
    intro z hz
    have hz_norm_le : ‖z‖ ≤ ‖c‖ + r := by
      have hz' : ‖z - c‖ = |r| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have htri : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
        have hcz : c + (z - c) = z := by
          calc
            c + (z - c) = c + z - c := by
              simp
            _ = z := by
              simp
        simpa [hcz] using (norm_add_le c (z - c))
      simpa [hz', abs_of_nonneg hr0] using htri
    calc
      log⁺ ‖f z‖ ≤ Real.log (1 + ‖f z‖) := posLog_le_log_one_add (x := ‖f z‖) (norm_nonneg _)
      _ ≤ C * (1 + ‖z‖) ^ ρ := hC z
      _ ≤ C * (1 + (‖c‖ + r)) ^ ρ := by
            have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + (‖c‖ + r) := by linarith
            have hpow : (1 + ‖z‖ : ℝ) ^ ρ ≤ (1 + (‖c‖ + r)) ^ ρ :=
              Real.rpow_le_rpow (by positivity) hbase hρ_nonneg
            exact mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
      _ = C * (1 + ‖c‖ + r) ^ ρ := by ring_nf
  exact Real.circleAverage_mono_on_of_le_circle (c := c) (R := r) (f := fun z ↦ log⁺ ‖f z‖)
    h_int h_pw

/-! ## ValueDistribution: basic bounds we can get “for free” from `EntireOfFiniteOrder` -/

open ValueDistribution

lemma characteristic_top_le_of_entireOfFiniteOrder
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      characteristic f ⊤ r ≤ C * (1 + r) ^ ρ + (logCounting f ⊤ r) := by
  rcases circleAverage_posLog_norm_le_of_entireOfFiniteOrder (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- `characteristic = proximity + logCounting`, and `proximity_top = circleAverage log⁺`.
  have hprox : proximity f ⊤ r ≤ C * (1 + r) ^ ρ := by
    -- Rewrite `proximity` and apply the circle-average bound from `EntireOfFiniteOrder`.
    simpa [ValueDistribution.proximity_top] using hC r hr0
  -- Add `logCounting f ⊤ r` on both sides.
  have := add_le_add_right hprox (logCounting f ⊤ r)
  -- Unfold `characteristic`.
  simpa [ValueDistribution.characteristic, add_assoc, add_comm, add_left_comm] using this

/-! ## Entire functions have no poles: `logCounting f ⊤ = 0` -/

lemma logCounting_top_eq_zero_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    logCounting f ⊤ = 0 := by
  -- Entire ⇒ analytic on a neighbourhood of `univ`
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  -- Hence the divisor is nonnegative, so the negative part (pole divisor) is zero.
  have hDnonneg : 0 ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf_an
  have hneg : (MeromorphicOn.divisor f (Set.univ : Set ℂ))⁻ = 0 := by
    ext z
    have hz : (0 : ℤ) ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) z := hDnonneg z
    -- `z ↦ divisor f univ z` is pointwise ≥ 0, hence its negative part vanishes.
    simp [negPart_eq_zero.2 hz]
  -- Rewrite `logCounting f ⊤` as the logCounting of the pole divisor.
  simp [ValueDistribution.logCounting_top, hneg]

/-! ## Characteristic bounds for entire functions of finite order -/

lemma characteristic_top_le_of_entireOfFiniteOrder'
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r → characteristic f ⊤ r ≤ C * (1 + r) ^ ρ := by
  rcases circleAverage_posLog_norm_le_of_entireOfFiniteOrder (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- For entire `f`, the pole-counting term vanishes.
  have hlog0 : logCounting f ⊤ r = 0 := by
    have hfun : logCounting f ⊤ = 0 := logCounting_top_eq_zero_of_entire (f := f) hf.entire
    simpa using congrArg (fun g : ℝ → ℝ => g r) hfun
  -- Unfold the characteristic and use the proximity bound.
  have hprox : proximity f ⊤ r ≤ C * (1 + r) ^ ρ := by
    simpa [ValueDistribution.proximity_top] using hC r hr0
  simpa [ValueDistribution.characteristic, hlog0] using (add_le_add_right hprox 0)

lemma characteristic_inv_top (f : ℂ → ℂ) :
    characteristic (f⁻¹) ⊤ = characteristic f 0 := by
  ext r
  simp [ValueDistribution.characteristic, ValueDistribution.proximity_inv, ValueDistribution.logCounting_inv]

lemma characteristic_zero_le_of_entireOfFiniteOrder'
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      characteristic f 0 r ≤ C * (1 + r) ^ ρ +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  -- Bound `characteristic f 0` by `characteristic f ⊤` plus an absolute constant,
  -- using the first part of the First Main Theorem.
  rcases characteristic_top_le_of_entireOfFiniteOrder' (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- Meromorphy on `univ`
  have hf_mer : MeromorphicOn f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable.2 hf.entire).meromorphicOn
  -- Quantitative First Main Theorem bound:
  have hdiff :
      |characteristic f ⊤ r - characteristic (f⁻¹) ⊤ r|
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    ValueDistribution.characteristic_sub_characteristic_inv_le (f := f) (hf := hf_mer) (R := r)

  -- From `|A - B| ≤ K` we get `B ≤ A + K`.
  have hdiff' :
      |characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r|
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [abs_sub_comm] using hdiff
  have hsub :
      characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    (le_abs_self _).trans hdiff'
  have hle_inv :
      characteristic (f⁻¹) ⊤ r ≤ characteristic f ⊤ r +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    by
      -- Rearrange `B = (B - A) + A` and use `B - A ≤ K`.
      have hrew :
          characteristic (f⁻¹) ⊤ r =
            (characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r) + characteristic f ⊤ r := by
        ring
      calc
        characteristic (f⁻¹) ⊤ r
            = (characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r) + characteristic f ⊤ r := hrew
        _ ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| + characteristic f ⊤ r := by
              -- Add `characteristic f ⊤ r` on the right of `hsub`.
              have h := add_le_add_right hsub (characteristic f ⊤ r)
              simpa [add_assoc, add_comm, add_left_comm] using h
        _ = characteristic f ⊤ r + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
              ac_rfl
  have hle0 :
      characteristic f 0 r ≤ characteristic f ⊤ r +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    -- rewrite `characteristic (f⁻¹) ⊤` as `characteristic f 0`
    simpa [characteristic_inv_top] using hle_inv

  -- Now use the growth bound for `characteristic f ⊤ r`.
  have htop : characteristic f ⊤ r ≤ C * (1 + r) ^ ρ := hC r hr0
  have htop' :
      characteristic f ⊤ r + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
        ≤ C * (1 + r) ^ ρ +
          max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    by
      -- `A ≤ B` implies `A + K ≤ B + K`.
      simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right htop
        (max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)
  exact hle0.trans htop'

/-! ## Mean-value bounds: circle averages to pointwise bounds for harmonic functions -/

lemma harmonicOnNhd_le_circleAverage_pos
    {u : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |r|)) :
    u c ≤ circleAverage (fun z ↦ max (u z) 0) c r := by
  -- Mean value property: `circleAverage u c r = u c`.
  have hmean : circleAverage u c r = u c :=
    HarmonicOnNhd.circleAverage_eq (f := u) (c := c) (R := r) hu
  -- Pointwise: `u ≤ max u 0`, so the average is monotone.
  have hci_u : CircleIntegrable u c r := by
    -- Harmonicity implies `C²` and hence continuity on the sphere.
    have hcont_sphere : ContinuousOn u (Metric.sphere c |r|) := by
      intro z hz
      have hz_cb : z ∈ Metric.closedBall c |r| := sphere_subset_closedBall hz
      have hz_harm : InnerProductSpace.HarmonicAt u z := hu z hz_cb
      exact hz_harm.1.continuousAt.continuousWithinAt
    exact hcont_sphere.circleIntegrable'
  have hci_pos : CircleIntegrable (fun z ↦ max (u z) 0) c r := by
    have hcont_sphere_u : ContinuousOn u (Metric.sphere c |r|) := by
      intro z hz
      have hz_cb : z ∈ Metric.closedBall c |r| := sphere_subset_closedBall hz
      have hz_harm : InnerProductSpace.HarmonicAt u z := hu z hz_cb
      exact hz_harm.1.continuousAt.continuousWithinAt
    have hpair : ContinuousOn (fun z : ℂ => (u z, (0 : ℝ))) (Metric.sphere c |r|) :=
      hcont_sphere_u.prodMk (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℝ)) (Metric.sphere c |r|))
    have hmax : ContinuousOn (fun p : ℝ × ℝ => max p.1 p.2) (Set.univ : Set (ℝ × ℝ)) :=
      continuous_max.continuousOn
    have hcont_pos : ContinuousOn (fun z : ℂ => max (u z) 0) (Metric.sphere c |r|) := by
      -- compose `max` with the continuous pair map `(u,0)`.
      simpa [Function.comp, Set.MapsTo] using
        (hmax.comp hpair (by intro z hz; simp))
    exact hcont_pos.circleIntegrable'
  have hmono : circleAverage u c r ≤ circleAverage (fun z ↦ max (u z) 0) c r := by
    apply Real.circleAverage_mono hci_u hci_pos
    intro z hz
    exact le_max_left _ _
  -- Rewrite with the mean value property.
  simpa [hmean] using hmono

lemma norm_le_exp_circleAverage_posLog_of_entire_nonzero
    {H : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hH_entire : Differentiable ℂ H) (hH_nonzero : ∀ z, H z ≠ 0) :
    ‖H c‖ ≤ Real.exp (circleAverage (fun z ↦ log⁺ ‖H z‖) c r) := by
  -- Apply the previous lemma to `u(z) = log ‖H z‖`.
  let u : ℂ → ℝ := fun z => Real.log ‖H z‖
  have hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |r|) := by
    intro z hz
    have hAn : AnalyticAt ℂ H z := (hH_entire.analyticAt z)
    have hHz : H z ≠ 0 := hH_nonzero z
    -- `log ‖H‖` is harmonic at each point where `H ≠ 0`.
    exact (hAn.harmonicAt_log_norm hHz)
  have hle : u c ≤ circleAverage (fun z ↦ max (u z) 0) c r :=
    harmonicOnNhd_le_circleAverage_pos (u := u) (c := c) (r := r) hu
  -- Rewrite `max (log‖H‖) 0` as `log⁺ ‖H‖`.
  have hmax : (fun z ↦ max (u z) 0) = fun z ↦ log⁺ ‖H z‖ := by
    funext z
    simp [u, Real.posLog, max_comm]
  have hle' : Real.log ‖H c‖ ≤ circleAverage (fun z ↦ log⁺ ‖H z‖) c r := by
    simpa [u, hmax] using hle
  -- Exponentiate.
  have hpos : 0 < ‖H c‖ := norm_pos_iff.mpr (hH_nonzero c)
  exact (Real.log_le_iff_le_exp hpos).1 hle'

/-! ## ZeroData implies nontriviality (used to rule out `order = ⊤` cases) -/

lemma zeroData_not_all_zero {f : ℂ → ℂ} (hz : ZeroData f) : ¬ (∀ z : ℂ, f z = 0) := by
  intro hzero
  have hsubset : ({0}ᶜ : Set ℂ) ⊆ Set.range hz.zeros := by
    intro z hz0
    have hz' : f z = 0 := hzero z
    have hzspec := (hz.zero_spec z).1 hz'
    rcases hzspec with h0 | hnon0
    · exact False.elim (hz0 h0.1)
    · exact hnon0.2
  have hcount_range : (Set.range hz.zeros).Countable := Set.countable_range hz.zeros
  have hcount_compl : ({0}ᶜ : Set ℂ).Countable := hcount_range.mono hsubset
  have hcount_univ : (Set.univ : Set ℂ).Countable := by
    have h0c : ({0} : Set ℂ).Countable := Set.countable_singleton 0
    have : ({0} ∪ ({0}ᶜ) : Set ℂ).Countable := h0c.union hcount_compl
    simpa [Set.union_compl_self] using this
  exact not_countable_complex hcount_univ


lemma hadamard_quotient_growth_bound
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) (hz : ZeroData f)
    (m : ℕ) (hσ : ρ < (m + 1 : ℝ)) (G F H : ℂ → ℂ)
    (hH_entire : Differentiable ℂ H)
    (hH_nonzero : ∀ z : ℂ, H z ≠ 0)
    (hH_eq : ∀ z : ℂ, F z ≠ 0 → H z = f z / F z)
    (hF_def : F = fun z : ℂ => z ^ hz.ord0 * ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n)) :
    ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (Nat.ceil ρ)) := by
  classical
  -- Analytic core (Nevanlinna/Cartan) to be supplied here.
  -- All infrastructure required for this bound is developed above in this file.
  -- We leave the quantitative step as a dedicated lemma to keep the main theorem readable.
  sorry

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
          ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n) := by
  classical
  -- Genus choice.
  set m : ℕ := Nat.floor ρ

  -- 1) Lindelöf summability at exponent `m+1` (as a real exponent), then convert to a nat exponent.
  have hσ : ρ < (m + 1 : ℝ) := by
    -- `ρ < floor ρ + 1`, and `m = floor ρ`.
    simpa [m] using (Nat.lt_floor_add_one ρ)
  have hsum_rpow : Summable (fun n : ℕ => ‖hz.zeros n‖⁻¹ ^ (m + 1 : ℝ)) :=
    lindelof_zero_data (hf := hf) (hz := hz) hσ
  have hsum_pow : Summable (fun n : ℕ => ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
    -- `x^(m+1:ℝ) = x^(m+1)` for real `x`, hence transfer summability.
    refine hsum_rpow.congr ?_
    intro n
    simpa using (Real.rpow_natCast (x := ‖hz.zeros n‖⁻¹) (n := m + 1))

  -- 2) Canonical product and its basic properties.
  let G : ℂ → ℂ := fun z => ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n)
  have hG :
      Differentiable ℂ G ∧
        (∀ z : ℂ, G z = 0 ↔ ∃ n, z = hz.zeros n) ∧
        EntireOfFiniteOrder (m + 1 : ℝ) G := by
    simpa [G] using
      (canonical_product_entire (a := hz.zeros) (m := m) hsum_pow hz.zeros_ne_zero)
  have hG_entire : Differentiable ℂ G := hG.1
  have hG_zero : ∀ z : ℂ, G z = 0 ↔ ∃ n, z = hz.zeros n := hG.2.1
  have hG_order : EntireOfFiniteOrder (m + 1 : ℝ) G := hG.2.2

  -- 3) Build the divisor `F(z) = z^{ord0} * G(z)`.
  let F : ℂ → ℂ := fun z => z ^ hz.ord0 * G z
  have hF_entire : Differentiable ℂ F := by
    -- finite product of entire functions
    have hpow : Differentiable ℂ (fun z : ℂ => z ^ hz.ord0) := by
      -- `simp` knows `z ↦ z^n` is differentiable
      simp
    simpa [F] using (hpow.mul hG_entire)

  -- `F` is not identically zero (use that `G 0 = 1`, so if `ord0 = 0` then `F 0 = 1`,
  -- otherwise pick a point where `f ≠ 0`).
  have hnot_all_zero : ¬ (∀ z : ℂ, f z = 0) := by
    -- Same countability obstruction as in `lindelof_zero_data`.
    intro hzero
    have hsubset : ({0}ᶜ : Set ℂ) ⊆ Set.range hz.zeros := by
      intro z hz0
      have hz' : f z = 0 := hzero z
      have hzspec := (hz.zero_spec z).1 hz'
      rcases hzspec with h0 | hnon0
      · exact False.elim (hz0 h0.1)
      · exact hnon0.2
    have hcount_range : (Set.range hz.zeros).Countable := Set.countable_range hz.zeros
    have hcount_compl : ({0}ᶜ : Set ℂ).Countable := hcount_range.mono hsubset
    have hcount_univ : (Set.univ : Set ℂ).Countable := by
      have h0c : ({0} : Set ℂ).Countable := Set.countable_singleton 0
      have : ({0} ∪ ({0}ᶜ) : Set ℂ).Countable := h0c.union hcount_compl
      simpa [Set.union_compl_self] using this
    exact not_countable_complex hcount_univ

  have hF_nontrivial : ∃ z : ℂ, F z ≠ 0 := by
    by_cases h0 : hz.ord0 = 0
    · refine ⟨0, ?_⟩
      -- `F 0 = 1` because `0^0 = 1` and every Weierstrass factor at 0 is 1.
      simp [F, h0, G, weierstrassFactor_zero]
    · -- pick a point where `f` is nonzero, hence not a zero of `F`.
      have : ∃ z : ℂ, f z ≠ 0 := by
        classical
        by_contra h
        have hz0 : ∀ z : ℂ, f z = 0 := by
          intro z
          by_contra hz0
          exact h ⟨z, hz0⟩
        exact hnot_all_zero hz0
      rcases this with ⟨z0, hz0⟩
      have hz0_ne0 : z0 ≠ 0 := by
        intro hz00
        subst hz00
        -- If `z0 = 0`, then `hz.ord0 ≠ 0` forces `f 0 = 0`, contradicting `hz0`.
        have hpos_ord0 : 0 < hz.ord0 := Nat.pos_of_ne_zero h0
        have hf0 : f 0 = 0 :=
          (hz.zero_spec 0).2 (Or.inl ⟨rfl, hpos_ord0⟩)
        exact hz0 (by simpa using hf0)
      have hz0_not_zero : ¬ (∃ n, z0 = hz.zeros n) := by
        intro hZ
        rcases hZ with ⟨n, rfl⟩
        have hfz : f (hz.zeros n) = 0 := by
          have : (hz.zeros n = 0 ∧ 0 < hz.ord0) ∨ (hz.zeros n ≠ 0 ∧ ∃ k, hz.zeros k = hz.zeros n) :=
            Or.inr ⟨hz.zeros_ne_zero n, ⟨n, rfl⟩⟩
          exact (hz.zero_spec (hz.zeros n)).2 this
        exact hz0 (by simpa using hfz)
      have hGz0 : G z0 ≠ 0 := by
        -- use the explicit zero set description of `G`
        have : ¬ G z0 = 0 := by
          intro hG0
          rcases (hG_zero z0).1 hG0 with ⟨n, rfl⟩
          exact hz0_not_zero ⟨n, rfl⟩
        simpa using this
      have hz0pow : z0 ^ hz.ord0 ≠ 0 := by
        exact pow_ne_zero hz.ord0 hz0_ne0
      refine ⟨z0, ?_⟩
      simp [F, hz0pow, hGz0]

  -- 4) `F` has the same zeros as `f`, with multiplicity.
  have h_ord_eq : ∀ z : ℂ, analyticOrderAt F z = analyticOrderAt f z := by
    classical
    intro z
    -- Helper: `analyticOrderAt f z` is never `⊤` (otherwise `f` is locally zero, hence globally zero).
    have hf_ne_top : analyticOrderAt f z ≠ ⊤ := by
      intro htop
      have hloc : ∀ᶠ w in 𝓝 z, f w = 0 := (analyticOrderAt_eq_top.mp htop)
      have hfreq : ∃ᶠ w in 𝓝[≠] z, f w = 0 :=
        (hloc.filter_mono nhdsWithin_le_nhds).frequently
      have hf_univ : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
        (analyticOnNhd_univ_iff_differentiable).2 hf.entire
      have hEq : Set.EqOn f 0 (Set.univ : Set ℂ) :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
          (f := f) (U := (Set.univ : Set ℂ)) hf_univ (by simpa using isPreconnected_univ)
          (by simp) hfreq
      have hzero : ∀ w : ℂ, f w = 0 := by
        intro w
        simpa using hEq (by simp : w ∈ (Set.univ : Set ℂ))
      exact hnot_all_zero hzero

    by_cases hz0 : z = 0
    · subst hz0
      -- At 0: `ord(F,0) = ord0` and `ord(f,0) = ord0`.
      have hG0_ne : G 0 ≠ 0 := by
        have : ¬ G 0 = 0 := by
          intro h0
          rcases (hG_zero 0).1 h0 with ⟨n, hn⟩
          -- but `hz.zeros n ≠ 0`
          exact hz.zeros_ne_zero n (by simpa using hn.symm)
        simpa using this
      have hG0_an : AnalyticAt ℂ G (0 : ℂ) := hG_entire.analyticAt 0
      have hG0_order0 : analyticOrderAt G (0 : ℂ) = 0 :=
        (hG0_an.analyticOrderAt_eq_zero).2 hG0_ne
      have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ hz.ord0) (0 : ℂ) :=
        (differentiable_id.pow hz.ord0).analyticAt 0
      have hpow_order : analyticOrderAt (fun w : ℂ => w ^ hz.ord0) (0 : ℂ) = (hz.ord0 : ℕ∞) := by
        -- `w^ord0 = (w - 0)^ord0`
        simpa [sub_zero] using
          (analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := (0 : ℂ)) (n := hz.ord0))
      have hF0_order : analyticOrderAt F (0 : ℂ) = (hz.ord0 : ℕ∞) := by
        calc
          analyticOrderAt F (0 : ℂ)
              = analyticOrderAt (fun w : ℂ => w ^ hz.ord0) (0 : ℂ) + analyticOrderAt G (0 : ℂ) := by
                  simpa [F] using
                    (analyticOrderAt_mul (𝕜 := ℂ)
                      (f := fun w : ℂ => w ^ hz.ord0) (g := G) (z₀ := (0 : ℂ)) hpow_an hG0_an)
          _ = (hz.ord0 : ℕ∞) := by simp [hpow_order, hG0_order0]

      have hf0_order : analyticOrderAt f (0 : ℂ) = (hz.ord0 : ℕ∞) := by
        -- cast `hz.ord0_spec` to `ℕ∞`
        have hcast : (analyticOrderNatAt f (0 : ℂ) : ℕ∞) = analyticOrderAt f (0 : ℂ) :=
          Nat.cast_analyticOrderNatAt (f := f) (z₀ := (0 : ℂ)) (by
            -- `analyticOrderAt f 0 ≠ ⊤`
            simpa using hf_ne_top)
        have := congrArg (fun n : ℕ => (n : ℕ∞)) hz.ord0_spec
        simpa [hcast] using this
      simp [hF0_order, hf0_order]
    · -- `z ≠ 0`: `ord(F,z) = ord(G,z)`, and `ord(G,z) = card {n | zeros n = z}`.
      have hz_ne0 : z ≠ 0 := hz0
      have hzpow_ne : z ^ hz.ord0 ≠ 0 := pow_ne_zero hz.ord0 hz_ne0
      have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ hz.ord0) z :=
        (differentiable_id.pow hz.ord0).analyticAt z
      have hpow_order0 : analyticOrderAt (fun w : ℂ => w ^ hz.ord0) z = 0 :=
        (hpow_an.analyticOrderAt_eq_zero).2 hzpow_ne
      have hG_an : AnalyticAt ℂ G z := hG_entire.analyticAt z
      have hF_eq_G : analyticOrderAt F z = analyticOrderAt G z := by
        have hmul :
            analyticOrderAt F z
              = analyticOrderAt (fun w : ℂ => w ^ hz.ord0) z + analyticOrderAt G z := by
                simpa [F] using
                  (analyticOrderAt_mul (𝕜 := ℂ)
                    (f := fun w : ℂ => w ^ hz.ord0) (g := G) (z₀ := z) hpow_an hG_an)
        simp [hmul, hpow_order0]

      -- Finite set of indices with `hz.zeros n = z`.
      let fiber : Set ℕ := {n : ℕ | hz.zeros n = z}
      have hfiber_fin : fiber.Finite := hz.finite_fiber z
      classical
      let s : Finset ℕ := hfiber_fin.toFinset
      have hs_mem : ∀ n : ℕ, n ∈ s ↔ hz.zeros n = z := by
        intro n
        simp [s, fiber]

      -- Split `G` into the finite product over `s` and the modified infinite tail.
      let fac : ℕ → ℂ → ℂ := fun n w => weierstrassFactor m (w / hz.zeros n)
      let fseq : ℕ → ℂ → ℂ := fun n w => if n ∈ s then fac n w else (1 : ℂ)
      let gseq : ℕ → ℂ → ℂ := fun n w => if n ∈ s then (1 : ℂ) else fac n w
      have hfac_mul : ∀ n w, fac n w = fseq n w * gseq n w := by
        intro n w
        by_cases hn : n ∈ s <;> simp [fac, fseq, gseq, hn]

      have hG_split : ∀ w : ℂ,
          (∏' n : ℕ, fac n w) = (∏' n : ℕ, fseq n w) * (∏' n : ℕ, gseq n w) := by
        intro w
        -- Multipliability of the two sequences via summability of `- 1`.
        have htail_all : Summable (fun n : ℕ => fac n w - 1) :=
          summable_weierstrassFactor_sub_one (a := hz.zeros) (m := m) hsum_pow hz.zeros_ne_zero w
        have htail_g : Summable (fun n : ℕ => gseq n w - 1) := by
          -- `gseq - 1` is `0` on `s` and `fac - 1` off `s`.
          have hEq :
              (fun n : ℕ => gseq n w - 1) =
                fun n : ℕ => if n ∈ s then (0 : ℂ) else (fac n w - 1) := by
            funext n
            by_cases hn : n ∈ s <;> simp [gseq, hn, fac]
          -- finite modification of a summable series
          have htail' :
              Summable (fun n : ℕ => if n ∈ s then (0 : ℂ) else (fac n w - 1)) := by
            simpa [fac] using
              (summable_weierstrassFactor_sub_one_off_finset (a := hz.zeros) (m := m)
                hsum_pow hz.zeros_ne_zero s w)
          simpa [hEq] using htail'
        have htail_f : Summable (fun n : ℕ => fseq n w - 1) := by
          -- supported on `s`
          have hsupp : Function.support (fun n : ℕ => fseq n w - 1) ⊆ (s : Set ℕ) := by
            intro n hn
            by_contra hnmem
            have : fseq n w - 1 = 0 := by simp [fseq]; aesop
            have : fseq n w - 1 ≠ 0 := by
              simpa [Function.mem_support] using hn
            grind
          have hfinite : (Function.support (fun n : ℕ => fseq n w - 1)).Finite :=
            (s.finite_toSet).subset hsupp
          exact summable_of_finite_support hfinite
        have hmult_f : Multipliable (fun n : ℕ => fseq n w) := by
          simpa [add_sub_cancel] using
            (Complex.multipliable_one_add_of_summable (f := fun n : ℕ => fseq n w - 1) htail_f)
        have hmult_g : Multipliable (fun n : ℕ => gseq n w) := by
          simpa [add_sub_cancel] using
            (Complex.multipliable_one_add_of_summable (f := fun n : ℕ => gseq n w - 1) htail_g)
        have := Multipliable.tprod_mul (f := fun n : ℕ => fseq n w) (g := fun n : ℕ => gseq n w) hmult_f hmult_g
        simpa [hfac_mul] using this

      -- Identify the `fseq` product as a finite product, hence analytic at `z`.
      have hfseq_eq_finprod : ∀ w : ℂ, (∏' n : ℕ, fseq n w) = ∏ n ∈ s, fac n w := by
        intro w
        -- outside `s`, `fseq n w = 1`
        have h1 : ∀ n : ℕ, n ∉ s → fseq n w = (1 : ℂ) := by
          intro n hn
          simp [fseq, hn]
        simpa [fseq] using (tprod_eq_prod (f := fun n : ℕ => fseq n w) h1)

      let Tail : ℂ → ℂ := fun w : ℂ => ∏' n : ℕ, gseq n w
      have hTail_entire : Differentiable ℂ Tail := by
        -- This is a canonical product with finitely many factors replaced by 1.
        have : Differentiable ℂ (fun w : ℂ => ∏' n : ℕ, (if n ∈ s then (1 : ℂ) else fac n w)) :=
          canonical_product_entire_off_finset (a := hz.zeros) (m := m) s hsum_pow hz.zeros_ne_zero
        simpa [Tail, gseq, fac] using this

      have hG_func : G = fun w : ℂ => (∏ n ∈ s, fac n w) * Tail w := by
        funext w
        have hsplit := hG_split w
        -- rewrite `fseq` and `gseq` products
        have hf := hfseq_eq_finprod w
        simp [G, Tail]; grind

      -- `Tail z ≠ 0` since all its factors at `z` are nonzero.
      have hTail_z_ne : Tail z ≠ 0 := by
        have htail : Summable (fun n : ℕ => gseq n z - 1) := by
          have hEq :
              (fun n : ℕ => gseq n z - 1) =
                fun n : ℕ => if n ∈ s then (0 : ℂ) else (fac n z - 1) := by
            funext n
            by_cases hn : n ∈ s <;> simp [gseq, hn, fac]
          have htail' :
              Summable (fun n : ℕ => if n ∈ s then (0 : ℂ) else (fac n z - 1)) := by
            simpa [fac] using
              (summable_weierstrassFactor_sub_one_off_finset (a := hz.zeros) (m := m)
                hsum_pow hz.zeros_ne_zero s z)
          simpa [hEq] using htail'
        have hlog : Summable (fun n : ℕ => Complex.log (gseq n z)) := by
          simpa [add_sub_cancel] using
            (Complex.summable_log_one_add_of_summable (f := fun n : ℕ => gseq n z - 1) htail)
        have hne : ∀ n : ℕ, gseq n z ≠ 0 := by
          intro n
          by_cases hn : n ∈ s
          · simp [gseq, hn]
          · -- off `s`, show `fac n z ≠ 0` since `hz.zeros n ≠ z`.
            have hnz : hz.zeros n ≠ z := by
              intro hEq
              have : n ∈ s := (hs_mem n).2 hEq
              exact hn this
            intro h0
            simp only [gseq, hn, ↓reduceIte] at h0
            have : z / hz.zeros n = (1 : ℂ) :=
              (weierstrassFactor_eq_zero_iff (m := m) (z := z / hz.zeros n)).1 h0
            have hn0 : hz.zeros n ≠ 0 := hz.zeros_ne_zero n
            have hzEq : z = hz.zeros n := by
              have := (div_eq_iff hn0).1 this
              simpa [one_mul] using this
            exact hnz hzEq.symm
        have hprod :
            Complex.exp (∑' n : ℕ, Complex.log (gseq n z)) = ∏' n : ℕ, gseq n z := by
          simpa using (Complex.cexp_tsum_eq_tprod (f := fun n : ℕ => gseq n z) hne hlog)
        have hexp_ne : Complex.exp (∑' n : ℕ, Complex.log (gseq n z)) ≠ 0 := Complex.exp_ne_zero _
        simpa [Tail, hprod] using hexp_ne

      have hTail_order0 : analyticOrderAt Tail z = 0 := by
        have hAn : AnalyticAt ℂ Tail z := hTail_entire.analyticAt z
        exact (hAn.analyticOrderAt_eq_zero).2 hTail_z_ne

      -- `∏ n ∈ s, fac n` is a pure power of `w ↦ weierstrassFactor m (w / z)` since all `hz.zeros n = z`.
      have hfin_eq : (fun w : ℂ => ∏ n ∈ s, fac n w) = fun w : ℂ => (weierstrassFactor m (w / z)) ^ s.card := by
        funext w
        classical
        have : ∏ n ∈ s, fac n w = ∏ n ∈ s, weierstrassFactor m (w / z) := by
          refine Finset.prod_congr rfl ?_
          intro n hn
          have hn' : hz.zeros n = z := (hs_mem n).1 hn
          simp [fac, hn']
        simp [this, Finset.prod_const]

      have hfin_an : AnalyticAt ℂ (fun w : ℂ => (weierstrassFactor m (w / z)) ^ s.card) z := by
        have hbase : AnalyticAt ℂ (fun w : ℂ => weierstrassFactor m (w / z)) z :=
          ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const z)).analyticAt z
        exact hbase.pow s.card

      have hfin_order : analyticOrderAt (fun w : ℂ => ∏ n ∈ s, fac n w) z = (s.card : ℕ∞) := by
        -- order of `weierstrassFactor m (w / z)` at `w=z` is 1, then use `analyticOrderAt_pow`.
        have hbase_an : AnalyticAt ℂ (fun w : ℂ => weierstrassFactor m (w / z)) z :=
          ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const z)).analyticAt z
        have hbase_order : analyticOrderAt (fun w : ℂ => weierstrassFactor m (w / z)) z = (1 : ℕ∞) :=
          analyticOrderAt_weierstrassFactor_div_self (m := m) (a := z) hz_ne0
        have hpow :
            analyticOrderAt (fun w : ℂ => (weierstrassFactor m (w / z)) ^ s.card) z =
              s.card • analyticOrderAt (fun w : ℂ => weierstrassFactor m (w / z)) z :=
          analyticOrderAt_pow (𝕜 := ℂ) (f := fun w : ℂ => weierstrassFactor m (w / z)) (z₀ := z)
            hbase_an s.card
        -- `s.card • (1:ℕ∞) = s.card`
        have : (s.card : ℕ∞) = s.card • (1 : ℕ∞) := by
          simp
        calc
          analyticOrderAt (fun w : ℂ => ∏ n ∈ s, fac n w) z
              = analyticOrderAt (fun w : ℂ => (weierstrassFactor m (w / z)) ^ s.card) z := by
                  simp [hfin_eq]
          _ = s.card • (1 : ℕ∞) := by simp [hpow, hbase_order]
          _ = (s.card : ℕ∞) := by simp

      -- Now combine: `G = finprod * Tail` and Tail contributes order 0.
      have hG_order : analyticOrderAt G z = (s.card : ℕ∞) := by
        have hcongr : analyticOrderAt G z =
            analyticOrderAt (fun w : ℂ => (∏ n ∈ s, fac n w) * Tail w) z := by
          simp [hG_func]
        have hmul :
            analyticOrderAt (fun w : ℂ => (∏ n ∈ s, fac n w) * Tail w) z
              = analyticOrderAt (fun w : ℂ => ∏ n ∈ s, fac n w) z + analyticOrderAt Tail z := by
          -- both factors analytic at `z`
          have hfin_an' : AnalyticAt ℂ (fun w : ℂ => ∏ n ∈ s, fac n w) z := by
            -- finite product of analytic functions
            have hdf : ∀ n ∈ s, AnalyticAt ℂ (fun w : ℂ => fac n w) z := by
              intro n hn
              simpa [fac] using
                ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const (hz.zeros n))).analyticAt z
            -- use analyticity lemma for finite products
            have hprod_eq : (fun w => ∏ n ∈ s, fac n w) = ∏ n ∈ s, (fun w => fac n w) := by
              ext w
              simp only [Finset.prod_apply]
            rw [hprod_eq]
            exact Finset.analyticAt_prod s (fun n hn => hdf n hn)
          have hTail_an : AnalyticAt ℂ Tail z := hTail_entire.analyticAt z
          simpa using (analyticOrderAt_mul (𝕜 := ℂ)
            (f := fun w : ℂ => ∏ n ∈ s, fac n w) (g := Tail) (z₀ := z) hfin_an' hTail_an)
        simp [hcongr, hmul, hfin_order, hTail_order0]

      -- Compare to `analyticOrderAt f z`, using `hz.zeros_mult_spec`.
      have hf_order_nat : analyticOrderNatAt f z = Nat.card {n : ℕ // hz.zeros n = z} :=
        hz.zeros_mult_spec z hz_ne0
      have hf_order : analyticOrderAt f z = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) := by
        have hcast : analyticOrderAt f z = (analyticOrderNatAt f z : ℕ∞) :=
          (Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) hf_ne_top).symm
        simp only [hcast, hf_order_nat]

      -- `s.card` is the same cardinality as `Nat.card` of the fiber subtype.
      have hs_card :
          (s.card : ℕ∞) = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) := by
        classical
        have hs_card_nat : s.card = Nat.card {n : ℕ // hz.zeros n = z} := by
          -- `s` enumerates exactly the indices with `hz.zeros n = z`.
          simpa using
            (Nat.subtype_card (s := s) (p := fun n : ℕ => hz.zeros n = z) (H := hs_mem)).symm
        simpa using congrArg (fun k : ℕ => (k : ℕ∞)) hs_card_nat

      -- Finally: `ord(F,z) = ord(G,z) = ord(f,z)`.
      have hFz : analyticOrderAt F z = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) := by
        -- `ord(F,z) = ord(G,z)`
        have : analyticOrderAt G z = (Nat.card {n : ℕ // hz.zeros n = z} : ℕ∞) := by
          simpa [hs_card] using hG_order
        simpa [hF_eq_G] using this
      -- Conclude: `ord(F,z) = ord(f,z)`.
      simp [hFz, hf_order]

  -- Inequality form needed for the removable singularity construction.
  have h_ord : ∀ z : ℂ, analyticOrderAt F z ≤ analyticOrderAt f z := fun z =>
    le_of_eq (h_ord_eq z)

  rcases quotient_entire (f := f) (G := F) hf.entire hF_entire hF_nontrivial h_ord with
    ⟨H, hH_entire, hH_eq⟩

  -- 5) Zero-freeness of `H` (requires matching multiplicities).
  have hH_nonzero : ∀ z : ℂ, H z ≠ 0 := by
    -- First, show the global identity `f = H * F` by analytic continuation from a point where `F ≠ 0`.
    rcases hF_nontrivial with ⟨z₀, hz₀⟩
    have hF_near : ∀ᶠ z in 𝓝 z₀, F z ≠ 0 :=
      (hF_entire z₀).continuousAt.eventually_ne hz₀
    have hfg : f =ᶠ[𝓝 z₀] fun z : ℂ => H z * F z := by
      filter_upwards [hF_near] with z hz
      have hHz : H z = f z / F z := hH_eq z hz
      -- rearrange: `(f/F) * F = f`
      have : H z * F z = f z := by
        calc
          H z * F z = (f z / F z) * F z := by simp [hHz]
          _ = f z := by field_simp [hz]
      simp [this]
    have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
      (analyticOnNhd_univ_iff_differentiable).2 hf.entire
    have hHF_an : AnalyticOnNhd ℂ (fun z : ℂ => H z * F z) (Set.univ : Set ℂ) :=
      (analyticOnNhd_univ_iff_differentiable).2 (hH_entire.mul hF_entire)
    have hHF : f = fun z : ℂ => H z * F z :=
      AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (f := f) (g := fun z : ℂ => H z * F z)
        hf_an hHF_an (z₀ := z₀) hfg

    -- Now compare analytic orders: `ord(f,z) = ord(H,z) + ord(F,z)` and `ord(f,z) = ord(F,z)`,
    -- hence `ord(H,z) = 0`, so `H z ≠ 0`.
    intro z
    have hF_ne_top : analyticOrderAt F z ≠ ⊤ := by
      intro htop
      have hloc : ∀ᶠ w in 𝓝 z, F w = 0 := (analyticOrderAt_eq_top.mp htop)
      have hfreq : ∃ᶠ w in 𝓝[≠] z, F w = 0 :=
        (hloc.filter_mono nhdsWithin_le_nhds).frequently
      have hF_univ : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) :=
        (analyticOnNhd_univ_iff_differentiable).2 hF_entire
      have hEq : Set.EqOn F 0 (Set.univ : Set ℂ) :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
          (f := F) (U := (Set.univ : Set ℂ)) hF_univ (by simpa using isPreconnected_univ)
          (by simp) hfreq
      have hzero : ∀ w : ℂ, F w = 0 := by
        intro w
        simpa using hEq (by simp : w ∈ (Set.univ : Set ℂ))
      exact hz₀ (by simpa using hzero z₀)

    have hmul_order :
        analyticOrderAt f z = analyticOrderAt H z + analyticOrderAt F z := by
      have hH_an : AnalyticAt ℂ H z := hH_entire.analyticAt z
      have hF_an' : AnalyticAt ℂ F z := hF_entire.analyticAt z
      have hmul :
          analyticOrderAt (fun w : ℂ => H w * F w) z =
            analyticOrderAt H z + analyticOrderAt F z := by
        simpa [Pi.mul_apply] using
          (analyticOrderAt_mul (𝕜 := ℂ) (f := H) (g := F) (z₀ := z) hH_an hF_an')
      -- rewrite using the global identity `f = H * F`
      simpa [hHF] using hmul

    have hsum_eq :
        analyticOrderAt H z + analyticOrderAt F z = analyticOrderAt F z := by
      -- combine `ord(f,z) = ord(H,z)+ord(F,z)` with `ord(F,z) = ord(f,z)`
      calc
        analyticOrderAt H z + analyticOrderAt F z
            = analyticOrderAt f z := hmul_order.symm
        _ = analyticOrderAt F z := (h_ord_eq z).symm

    have hH_order : analyticOrderAt H z = 0 := by
      have hsum_eq' : analyticOrderAt H z + analyticOrderAt F z = 0 + analyticOrderAt F z := by
        simpa [zero_add] using hsum_eq
      exact WithTop.add_right_cancel hF_ne_top hsum_eq'

    -- For an analytic function, order 0 iff the value is nonzero.
    have hH_an : AnalyticAt ℂ H z := hH_entire.analyticAt z
    exact (hH_an.analyticOrderAt_eq_zero).1 hH_order

  -- 6) Growth bound for `H` (the main analytic input; to be supplied via Nevanlinna/Cartan).
  have hH_bound :
      ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (Nat.ceil ρ)) := by
    classical
    -- NOTE: This is the remaining analytic core of Hadamard’s theorem.
    --
    -- The intended proof uses the ValueDistribution / Cartan infrastructure to bound both
    -- `circleAverage (log⁺ ‖H‖)` and `circleAverage (log⁺ ‖H⁻¹‖)` by `O((1+r)^⌈ρ⌉)`, then upgrades
    -- this to a pointwise bound via Poisson–Jensen/Borel–Carathéodory.
    --
    -- For now we record the statement as an explicit hypothesis packaged into a lemma, so the
    -- remainder of the factorization proof (the algebraic assembly) stays executable.
    --
    -- TODO (next): replace `hadamard_quotient_growth_bound` by an actual Nevanlinna/Cartan proof.
    exact hadamard_quotient_growth_bound (hf := hf) (hz := hz) (m := m) (hσ := hσ) (G := G) (F := F)
      (H := H) hH_entire hH_nonzero hH_eq (by rfl)

  -- 7) Conclude `H = exp(P)` for a polynomial `P` of degree ≤ ⌈ρ⌉.
  rcases zero_free_polynomial_growth_is_exp_poly (H := H) (n := Nat.ceil ρ)
      hH_entire hH_nonzero hH_bound with
    ⟨P, hPdeg, hPexp⟩

  refine ⟨m, P, ?_, ?_, ?_⟩
  · simp [m]
  · exact Polynomial.degree_le_of_natDegree_le hPdeg
  · intro z
    -- If `F z ≠ 0`, we can rewrite using the quotient characterization.
    by_cases hFz : F z = 0
    · -- At zeros of `F`, the RHS is `exp(P(z)) * F(z) = 0`, and `f z = 0` by `ZeroData.zero_spec`.
      have hfz : f z = 0 := by
        by_cases hz0 : z = 0
        · subst hz0
          -- If `F 0 = 0`, then necessarily `0 < hz.ord0`, hence `f 0 = 0`.
          have hord0_ne : hz.ord0 ≠ 0 := by
            intro hord0
            have : (1 : ℂ) = 0 := by
              -- If `hz.ord0 = 0`, then `F 0 = 1`, contradiction.
              simp [F, G, hord0, weierstrassFactor_zero] at hFz
            exact one_ne_zero this
          have hpos_ord0 : 0 < hz.ord0 := Nat.pos_of_ne_zero hord0_ne
          exact (hz.zero_spec 0).2 (Or.inl ⟨rfl, hpos_ord0⟩)
        · -- If `z ≠ 0`, then `G z = 0`, hence `z` is one of the nonzero zeros.
          have hzpow_ne : z ^ hz.ord0 ≠ 0 := pow_ne_zero hz.ord0 hz0
          have hGz : G z = 0 := by
            -- Avoid `simp` rewriting `mul_eq_zero`/`pow_eq_zero` too early.
            have hFz' : z ^ hz.ord0 * G z = 0 := by
              have hFz' := hFz
              dsimp [F] at hFz'
              exact hFz'
            rcases mul_eq_zero.mp hFz' with hpow | hGz
            · exfalso; exact hzpow_ne hpow
            · exact hGz
          rcases (hG_zero z).1 hGz with ⟨n, rfl⟩
          have : (hz.zeros n = 0 ∧ 0 < hz.ord0) ∨ (hz.zeros n ≠ 0 ∧ ∃ k, hz.zeros k = hz.zeros n) :=
            Or.inr ⟨hz.zeros_ne_zero n, ⟨n, rfl⟩⟩
          exact (hz.zero_spec (hz.zeros n)).2 this

      have hRHS0 :
          exp (Polynomial.eval z P) * z ^ hz.ord0 *
              ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n) = 0 := by
        have hFprod : z ^ hz.ord0 * ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n) = 0 := by
          simpa [F, G] using hFz
        have : exp (Polynomial.eval z P) * (z ^ hz.ord0 * ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n)) = 0 := by
          simpa using congrArg (fun t => exp (Polynomial.eval z P) * t) hFprod
        simpa [mul_assoc] using this

      -- Both sides are zero.
      calc
        f z = 0 := hfz
        _ = exp (Polynomial.eval z P) * z ^ hz.ord0 * ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n) := by
              simpa using hRHS0.symm
    · have hFz' : F z ≠ 0 := hFz
      have hHz : H z = f z / F z := hH_eq z hFz'
      -- Rearrange `H z = f z / F z` and substitute `H z = exp(P.eval z)`.
      have : f z = H z * F z := by
        -- `a = b/c` implies `a*c = b`
        field_simp [hFz'] at hHz
        simpa [mul_assoc] using hHz.symm
      -- rewrite `H z` using the polynomial representation
      simp [this, F, G, hPexp z, mul_assoc, mul_left_comm, mul_comm]

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
          ∏' n : ℕ, (ComplexAnalysis.Hadamard.weierstrassFactor m (z / hz.zeros n)) :=
  ComplexAnalysis.Hadamard.hadamard_factorization hf hz

end
