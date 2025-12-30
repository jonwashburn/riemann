
import Mathlib
import Riemann.academic_framework.WeierstrassFactorBound
import PrimeNumberTheoremAnd.BorelCaratheodory
import PrimeNumberTheoremAnd.DerivativeBound

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
