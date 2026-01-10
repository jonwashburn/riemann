import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Riemann.academic_framework.WeierstrassFactorBound


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
* `ComplexAnalysis.Hadamard.hadamard_factorization` : The main factorization theorem (in `Lemmas` )
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

/-
An earlier `Multiset`-based formulation would force the nonzero zero set to be finite (a
`Multiset` is by definition finite), which trivializes the Hadamard factorization statement.

We instead package **countably many** nonzero zeros as a sequence `zeros : ℕ → ℂ`.

-/
structure ZeroData' (f : ℂ → ℂ) where
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
    (z = 0 ∧ 0 < ord0) ∨ (z ≠ 0 ∧ ∃ n, zeros n = z)-/

/--
**Refined ZeroData**
We modify `ZeroData` to allow `zeros` to take the value `0`.
These `0` entries act as "padding" for functions with finitely many zeros.
The canonical product naturally ignores them since `E_m(z/0) = E_m(0) = 1` in Lean.
-/
structure ZeroData (f : ℂ → ℂ) where
  /-- A sequence enumerating the nonzero zeros. Values of `0` are ignored/padding. -/
  zeros : ℕ → ℂ
  /-- Local finiteness: only finitely many *nonzero* zeros land in any closed ball. -/
  finite_in_ball : ∀ R : ℝ, ({n : ℕ | zeros n ≠ 0 ∧ ‖zeros n‖ ≤ R} : Set ℕ).Finite
  /-- Order of vanishing at `0`. -/
  ord0 : ℕ
  /-- `ord0` is the actual vanishing order of `f` at `0`. -/
  ord0_spec : analyticOrderNatAt f 0 = ord0
  /-- Multiplicity specification: the analytic order at each nonzero zero is the count in the sequence. -/
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

-- `ZeroData` gives local finiteness in closed balls **away from 0**; in particular, each nonzero
-- fiber of `zeros` is finite (the fiber over `0` may be infinite because `0` is allowed as padding).
lemma finite_fiber (zd : ZeroData f) {z : ℂ} (hz : z ≠ 0) :
    ({n : ℕ | zd.zeros n = z} : Set ℕ).Finite := by
  classical
  -- If `zeros n = z` with `z ≠ 0`, then `n` lies in the finite set of nonzero zeros in the ball
  -- of radius `‖z‖`.
  refine (zd.finite_in_ball ‖z‖).subset ?_
  intro n hn
  have hEq : zd.zeros n = z := by simpa using hn
  have hne : zd.zeros n ≠ 0 := by simpa [hEq] using hz
  have hnorm : ‖zd.zeros n‖ ≤ ‖z‖ := by simp [hEq]
  exact ⟨hne, hnorm⟩

lemma finite_fiber_type (zd : ZeroData f) {z : ℂ} (hz : z ≠ 0) :
    Finite {n : ℕ // zd.zeros n = z} := by
  classical
  -- The subtype is finite as soon as the defining set is finite.
  letI : Fintype {n : ℕ // zd.zeros n = z} := (zd.finite_fiber (z := z) hz).fintype
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

/-
/--
The canonical product over a sequence of nonzero points.
-/
noncomputable def canonicalProduct' (m : ℕ) (zeros : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / zeros n)-/

/--
**Canonical Product**
Defined using the refined `ZeroData`. Lean's division by zero (`z / 0 = 0`) and
`weierstrassFactor m 0 = 1` ensure that padding zeros do not affect the product.
-/
noncomputable def canonicalProduct (m : ℕ) (zeros : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n, weierstrassFactor m (z / zeros n)

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

end Hadamard
end ComplexAnalysis
end
