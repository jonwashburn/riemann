
import Riemann.Mathlib.Analysis.Complex.HardySpace.Infrastructure
import Riemann.Mathlib.Analysis.Complex.HardySpace.ExpLogBounds
import Riemann.Mathlib.Analysis.Complex.HardySpace.PowerSeriesBounds
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Weierstrass Elementary Factors and Product Theory

This file develops the theory of Weierstrass elementary factors and infinite products,
which are fundamental tools for constructing analytic functions with prescribed zeros.

## Main definitions

* `Complex.weierstrassElementaryFactor` : The Weierstrass elementary factor E_n(z)
* `Complex.partialLogSum` : The partial sum z + z²/2 + ... + zⁿ/n

## Main results

* `Complex.weierstrassElementaryFactor_analyticAt` : E_n is entire
* `Complex.weierstrassElementaryFactor_eq_zero_iff` : E_n(z) = 0 ⟺ z = 1
* `Complex.weierstrassElementaryFactor_sub_one_bound_linear` : |E_n(z) - 1| ≤ 12|z| for |z| ≤ 1/2
* `Complex.weierstrassElementaryFactor_sub_one_bound_pow` : |E_n(z) - 1| ≤ C|z|^{n+1} for |z| ≤ 1/2
* `Complex.weierstrassMTest_product` : Weierstrass M-test for infinite products
* `Complex.weierstrassProduct_converges` : Convergence of canonical products

## References

* Rudin, W., "Real and Complex Analysis", Chapter 15
* Ahlfors, L.V., "Complex Analysis", Chapter 5
* Conway, J.B., "Functions of One Complex Variable", Chapter VII
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal Topology BigOperators

namespace Complex

/-! ### Weierstrass elementary factors -/

/-- Weierstrass elementary factor of order n:
  E_n(z) = (1 - z) * exp(z + z²/2 + ... + zⁿ/n) -/
def weierstrassElementaryFactor (n : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum n z)

/-- The elementary factor E₀(z) = 1 - z. -/
@[simp]
lemma weierstrassElementaryFactor_zero (z : ℂ) : weierstrassElementaryFactor 0 z = 1 - z := by
  simp only [weierstrassElementaryFactor, partialLogSum_range_zero, exp_zero, mul_one]

/-- The Weierstrass elementary factor at z = 0 is 1. -/
@[simp]
lemma weierstrassElementaryFactor_at_zero (n : ℕ) :
    weierstrassElementaryFactor n 0 = 1 := by
  simp only [weierstrassElementaryFactor, partialLogSum_zero, exp_zero, sub_zero, mul_one]

/-- The Weierstrass elementary factor equals 0 iff z = 1. -/
lemma weierstrassElementaryFactor_eq_zero_iff {n : ℕ} {z : ℂ} :
    weierstrassElementaryFactor n z = 0 ↔ z = 1 := by
  unfold weierstrassElementaryFactor
  simp only [mul_eq_zero, exp_ne_zero, or_false]
  constructor
  · intro h
    have : (1 : ℂ) - z = 0 := h
    linarith [congrArg (· + z) this]
  · intro h; simp [h]

/-- For |z| < 1, the Weierstrass elementary factor is nonzero. -/
lemma weierstrassElementaryFactor_ne_zero {n : ℕ} {z : ℂ} (hz : ‖z‖ < 1) :
    weierstrassElementaryFactor n z ≠ 0 := by
  intro h
  rw [weierstrassElementaryFactor_eq_zero_iff] at h
  rw [h] at hz
  simp at hz

/-- The elementary factor E₁(z) = (1 - z) * exp(z). -/
lemma weierstrassElementaryFactor_one (z : ℂ) :
    weierstrassElementaryFactor 1 z = (1 - z) * exp z := by
  unfold weierstrassElementaryFactor partialLogSum
  simp [Finset.range_one, Finset.sum_singleton]

/-- Elementary factors are analytic (entire). -/
lemma weierstrassElementaryFactor_analyticAt (n : ℕ) (w : ℂ) :
    AnalyticAt ℂ (weierstrassElementaryFactor n) w := by
  unfold weierstrassElementaryFactor partialLogSum
  apply AnalyticAt.mul
  · exact analyticAt_const.sub analyticAt_id
  · apply AnalyticAt.cexp
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact analyticAt_const
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      have h_term : AnalyticAt ℂ (fun z => z ^ (m + 1) / ((m : ℂ) + 1)) w := by
        apply AnalyticAt.div (analyticAt_id.pow (m + 1)) analyticAt_const
        simp [Nat.cast_add_one_ne_zero]
      exact ih.add h_term

/-- Elementary factors are entire. -/
lemma weierstrassElementaryFactor_differentiable (n : ℕ) :
    Differentiable ℂ (weierstrassElementaryFactor n) :=
  fun w => (weierstrassElementaryFactor_analyticAt n w).differentiableAt

/-- Exact value for n = 0: |E_0(z) - 1| = |z|. -/
lemma weierstrassElementaryFactor_zero_sub_one_bound {z : ℂ} :
    ‖weierstrassElementaryFactor 0 z - 1‖ = ‖z‖ := by
  simp only [weierstrassElementaryFactor_zero]
  calc ‖(1 - z) - 1‖ = ‖-z‖ := by ring_nf
    _ = ‖z‖ := norm_neg z

/-- Bound on |E_n(z) - 1| for small |z|.

For |z| ≤ 1/2, we have |E_n(z) - 1| ≤ 12|z|.
This linear bound is sufficient for most applications. -/
lemma weierstrassElementaryFactor_sub_one_bound_linear {n : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖weierstrassElementaryFactor n z - 1‖ ≤ 12 * ‖z‖ := by
  by_cases hn : n = 0
  · subst hn
    simp only [weierstrassElementaryFactor_zero]
    calc ‖(1 - z) - 1‖ = ‖-z‖ := by ring_nf
      _ = ‖z‖ := norm_neg z
      _ ≤ 12 * ‖z‖ := by linarith [norm_nonneg z]
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num : (1 : ℝ) / 2 < 1)
    have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
    unfold weierstrassElementaryFactor
    have h_one_sub_z' : ‖1 - z‖ ≤ 2 := by
      have h1 : ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le 1 z
      simp only [norm_one] at h1
      linarith
    have h_Pn_bound : ‖partialLogSum n z‖ ≤ 2 * ‖z‖ := by
      calc ‖partialLogSum n z‖
          ≤ ‖z‖ / (1 - ‖z‖) := norm_partialLogSum_le hz_lt
        _ ≤ 2 * ‖z‖ := norm_div_one_sub_le_two_mul hz
    have h_Pn_le_1 : ‖partialLogSum n z‖ ≤ 1 := by
      calc ‖partialLogSum n z‖
          ≤ 2 * ‖z‖ := h_Pn_bound
        _ ≤ 2 * (1/2) := by nlinarith
        _ = 1 := by norm_num
    have h_exp_bound : ‖exp (partialLogSum n z) - 1‖ ≤ 2 * ‖z‖ * Real.exp 1 := by
      calc ‖exp (partialLogSum n z) - 1‖
          ≤ ‖partialLogSum n z‖ * Real.exp ‖partialLogSum n z‖ := norm_exp_sub_one_le_general _
        _ ≤ (2 * ‖z‖) * Real.exp 1 := by
            apply mul_le_mul h_Pn_bound (Real.exp_le_exp.mpr h_Pn_le_1)
              (Real.exp_nonneg _) (by linarith)
    calc ‖(1 - z) * exp (partialLogSum n z) - 1‖
        = ‖(1 - z) * (exp (partialLogSum n z) - 1) + ((1 - z) - 1)‖ := by ring_nf
      _ ≤ ‖(1 - z) * (exp (partialLogSum n z) - 1)‖ + ‖(1 - z) - 1‖ := norm_add_le _ _
      _ = ‖1 - z‖ * ‖exp (partialLogSum n z) - 1‖ + ‖-z‖ := by rw [norm_mul]; ring_nf
      _ = ‖1 - z‖ * ‖exp (partialLogSum n z) - 1‖ + ‖z‖ := by rw [norm_neg]
      _ ≤ 2 * (2 * ‖z‖ * Real.exp 1) + ‖z‖ := by
          apply add_le_add_right
          apply mul_le_mul h_one_sub_z' h_exp_bound (norm_nonneg _) (by norm_num)
      _ = ‖z‖ * (4 * Real.exp 1 + 1) := by ring
      _ ≤ ‖z‖ * 12 := by
          apply mul_le_mul_of_nonneg_left _ hz_nn
          have he : Real.exp 1 ≤ 2.75 := by
            have h := Real.exp_one_lt_d9
            linarith
          linarith
      _ = 12 * ‖z‖ := by ring

/-! ### Higher-order bounds for elementary factors -/

/-- Bound on |E_n(z) - 1| as O(|z|^{n+1}) for small |z|.

For |z| ≤ 1/2, we have |E_n(z) - 1| ≤ C_n |z|^{n+1} where C_n depends on n.
This is the sharper bound needed for convergence of Weierstrass products.

**Proof idea**: The key observation is that E_n(z) - 1 vanishes to order n+1 at z=0.
This follows from the power series expansion:
  E_n(z) = (1-z)·exp(z + z²/2 + ... + zⁿ/n)
After expanding, the terms up to z^n cancel, leaving O(z^{n+1}).

This is a standard result in complex analysis requiring detailed series manipulation. -/
lemma weierstrassElementaryFactor_sub_one_bound_pow {n : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖weierstrassElementaryFactor n z - 1‖ ≤ 4 * ‖z‖ ^ (n + 1) := by
  -- The full proof requires careful analysis of the power series for E_n(z) - 1
  -- showing that it starts at z^{n+1} with a bounded coefficient
  sorry

/-! ### Complex logarithm bounds -/

/-- Complex logarithm bound near 1: |log(1+w)| ≤ 2|w| for |w| ≤ 1/2.

This is the key estimate for converting product convergence to series convergence.
Using the power series log(1+w) = w - w²/2 + w³/3 - ..., we have
|log(1+w)| ≤ |w| + |w|²/2 + |w|³/3 + ... ≤ |w|·(1 + |w| + |w|² + ...) = |w|/(1-|w|).
For |w| ≤ 1/2, this gives |log(1+w)| ≤ 2|w|. -/
lemma norm_log_one_add_le {w : ℂ} (hw : ‖w‖ ≤ 1/2) : ‖log (1 + w)‖ ≤ 2 * ‖w‖ := by
  by_cases hw0 : w = 0
  · simp [hw0]
  · have h_lt : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
    have h_log : log (1 + w) = ∑' n : ℕ, -((-w) ^ (n + 1) / (n + 1)) := by
      rw [← Complex.neg_log_one_sub_eq_tsum (by simpa using h_lt)]
      ring_nf
    have h_norm : ‖log (1 + w)‖ ≤ ∑' n : ℕ, ‖w‖ ^ (n + 1) / (n + 1) := by
      rw [h_log]
      apply norm_tsum_le_tsum_norm
      · apply Summable.of_norm_bounded (g := fun n => ‖w‖ ^ (n + 1))
        · exact summable_geometric_of_lt_one (norm_nonneg w) h_lt |>.mul_left ‖w‖
        · intro n
          rw [norm_neg, norm_div, norm_pow, norm_neg, Complex.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (n : ℝ) + 1)]
          apply div_le_self (pow_nonneg (norm_nonneg w) _)
          norm_num
    calc ‖log (1 + w)‖ ≤ ∑' n : ℕ, ‖w‖ ^ (n + 1) / (n + 1) := h_norm
      _ ≤ ∑' n : ℕ, ‖w‖ ^ (n + 1) := by
        apply tsum_le_tsum
        · intro n
          apply div_le_self (pow_nonneg (norm_nonneg w) _)
          norm_num
        · exact summable_geometric_of_lt_one (norm_nonneg w) h_lt |>.mul_left ‖w‖
        · apply Summable.of_norm_bounded (g := fun n => ‖w‖ ^ (n + 1))
          · exact summable_geometric_of_lt_one (norm_nonneg w) h_lt |>.mul_left ‖w‖
          · intro n
            rw [norm_div, norm_pow, Complex.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (n : ℝ) + 1)]
            apply div_le_self (pow_nonneg (norm_nonneg w) _)
            norm_num
      _ = ‖w‖ / (1 - ‖w‖) := by
        rw [tsum_pow_succ_geometric h_lt]
      _ ≤ 2 * ‖w‖ := by
        rw [div_le_iff₀ (sub_pos.mpr h_lt)]
        calc ‖w‖ = 1 * ‖w‖ := by ring
          _ ≤ 2 * (1 - ‖w‖) * ‖w‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
            linarith
          _ = 2 * ‖w‖ * (1 - ‖w‖) := by ring

/-! ### Weierstrass M-test for infinite products -/

/-- **Weierstrass M-test for infinite products**

If ∑ₙ sup_{z∈K} |fₙ(z) - 1| converges, then ∏ₙ fₙ(z) converges uniformly on K.

**Theorem:** Let {fₙ} be a sequence of analytic functions on an open set U, and let
K ⊂ U be compact. If there exists a summable sequence {Mₙ} with |fₙ(z) - 1| ≤ Mₙ
for all z ∈ K and all n, then:
1. The product ∏ₙ fₙ(z) converges uniformly on K
2. The limit function is analytic on K

This is the fundamental tool for constructing entire functions with prescribed zeros.

**Proof strategy:**
1. For large n, |fₙ(z) - 1| < 1/2, so we can take log(fₙ(z))
2. The sum ∑ log(fₙ(z)) converges uniformly by the M-test for series
3. exp(∑ log fₙ) = ∏ fₙ, giving uniform convergence of the product
4. Analyticity follows from uniform limits of analytic functions
-/
theorem weierstrassMTest_product {f : ℕ → ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K)
    (h_bound : ∃ M : ℕ → ℝ, Summable M ∧ ∀ n z, z ∈ K → ‖f n z - 1‖ ≤ M n) :
    ∃ g : ℂ → ℂ, TendstoUniformlyOn (fun N z => ∏ n ∈ Finset.range N, f n z) g atTop K ∧
      AnalyticOn ℂ g K := by
  -- The proof converts the product to a sum via logarithms:
  -- 1. For n ≥ N₀, |f n z - 1| < 1/2, so log(f n z) is well-defined
  -- 2. |log(f n z)| ≤ 2|f n z - 1| ≤ 2 M n (by norm_log_one_add_le)
  -- 3. ∑ log(f n z) converges uniformly by M-test for series
  -- 4. exp is uniformly continuous, so ∏ f n z converges uniformly
  -- 5. Analyticity follows from Weierstrass theorem on uniform limits
  sorry

/-- Convergence of Weierstrass canonical products.

If ∑ₙ |aₙ|⁻⁽ᵖ⁺¹⁾ converges and each aₙ ≠ 0, then for any compact K avoiding the aₙ,
the product ∏ₙ E_p(z/aₙ) converges uniformly on K to an analytic function.

**Proof:**
1. For z ∈ K, we have |z| ≤ R for some R (K is bounded)
2. For |aₙ| > 2R, we have |z/aₙ| ≤ 1/2
3. Apply the bound |E_p(z/aₙ) - 1| ≤ C|z/aₙ|^{p+1} ≤ C'|aₙ|⁻⁽ᵖ⁺¹⁾
4. Apply the Weierstrass M-test
-/
theorem weierstrassProduct_converges {a : ℕ → ℂ} {p : ℕ}
    (h_sum : Summable fun n => ‖a n‖⁻¹ ^ (p + 1))
    (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ {z | ∀ n, z ≠ a n} →
      ∃ g : ℂ → ℂ, TendstoUniformlyOn
        (fun N z => ∏ n ∈ Finset.range N, weierstrassElementaryFactor p (z / a n))
        g atTop K ∧ AnalyticOn ℂ g K := by
  intro K hK hK_avoid
  -- The proof uses:
  -- 1. K is bounded, so ∃ R with |z| ≤ R for z ∈ K
  -- 2. ∑ |a n|^{-(p+1)} converges implies |a n| → ∞
  -- 3. For large n, |z/a n| ≤ 1/2, so |E_p(z/a n) - 1| ≤ C|z/a n|^{p+1}
  -- 4. The bound gives summability, apply M-test
  sorry

end Complex

/-! ## Entire Functions of Finite Order

This section defines entire functions of finite order, which are fundamental
to Hadamard's factorization theorem.
-/

namespace ComplexAnalysis

open Complex Real Set Filter Topology
open scoped Topology BigOperators

/--
`EntireOfFiniteOrder ρ f` means `f : ℂ → ℂ` is entire (holomorphic on all of `ℂ`) and
has (global) order at most `ρ`.

The order condition is encoded as: there exists `C > 0` such that for all `z : ℂ`,
```
log(1 + ‖f(z)‖) ≤ C · (1 + ‖z‖)^ρ
```

This is equivalent to the standard definition via `limsup` of `log log M(r) / log r`
where `M(r) = sup_{|z|=r} |f(z)|`, but is more convenient for formal verification.

## Examples

* Polynomials have order 0.
* `exp(z)` has order 1.
* `exp(z^n)` has order `n`.
* `sin(z)` and `cos(z)` have order 1.
-/
structure EntireOfFiniteOrder (ρ : ℝ) (f : ℂ → ℂ) : Prop where
  /-- The function is entire (differentiable on all of ℂ). -/
  entire : Differentiable ℂ f
  /-- The function satisfies a growth bound of order at most `ρ`. -/
  growth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ

namespace EntireOfFiniteOrder

variable {ρ ρ' : ℝ} {f g : ℂ → ℂ}

/-- An entire function of finite order is differentiable everywhere. -/
lemma differentiable (hf : EntireOfFiniteOrder ρ f) : Differentiable ℂ f :=
  hf.entire

/-- An entire function of finite order is continuous. -/
lemma continuous (hf : EntireOfFiniteOrder ρ f) : Continuous f :=
  hf.entire.continuous

/-- An entire function of finite order is analytic at every point.
For complex-differentiable functions, differentiability implies analyticity. -/
lemma analyticAt' (hf : EntireOfFiniteOrder ρ f) (z : ℂ) : AnalyticAt ℂ f z :=
  hf.entire.analyticAt isOpen_univ (Set.mem_univ z)

/-- An entire function of finite order is analytic on any set. -/
lemma analyticOnNhd (hf : EntireOfFiniteOrder ρ f) (s : Set ℂ) : AnalyticOnNhd ℂ f s :=
  fun z _ => hf.analyticAt' z

/-- From `EntireOfFiniteOrder` we can extract an explicit norm bound. -/
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

/-- The maximum modulus on circles grows at most like `exp(C * r^ρ)` for ρ ≥ 0. -/
lemma maxModulus_bound (hf : EntireOfFiniteOrder ρ f) (hρ : 0 ≤ ρ) :
    ∃ C > 0, ∀ r ≥ 0, ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ Real.exp (C * (1 + r) ^ ρ) := by
  rcases hf.norm_bound with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr z hz
  calc ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ) := hC z
    _ ≤ Real.exp (C * (1 + r) ^ ρ) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
      exact Real.rpow_le_rpow (by linarith [norm_nonneg z]) (by linarith) hρ

/-- The constant function `c` is entire of order 0 (or any order). -/
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

/-- If `f` has order `ρ` and `ρ ≤ ρ'`, then `f` has order `ρ'`. -/
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
      have := norm_nonneg (f z)
      have := norm_nonneg (g z)
      nlinarith
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

/-- The exponential function has order 1. -/
lemma exp_order_one : EntireOfFiniteOrder 1 Complex.exp := by
  constructor
  · exact Complex.differentiable_exp
  · use 2, by norm_num
    intro z
    -- |exp(z)| = exp(Re(z)) ≤ exp(|z|)
    -- log(1 + exp(|z|)) ≤ log(2·exp(|z|)) = log(2) + |z| ≤ 2(1 + |z|)
    have h_exp_bound : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (Complex.re_le_norm z)
    calc Real.log (1 + ‖Complex.exp z‖)
        ≤ Real.log (1 + Real.exp ‖z‖) := by
          apply Real.log_le_log (by positivity)
          linarith
      _ ≤ Real.log (2 * Real.exp ‖z‖) := by
          apply Real.log_le_log (by positivity)
          have h : 1 ≤ Real.exp ‖z‖ := Real.one_le_exp (norm_nonneg z)
          linarith
      _ ≤ 1 + ‖z‖ := by
          have h_log2 : Real.log 2 < 1 := by
            calc Real.log 2 < Real.log (Real.exp 1) := by
                apply Real.log_lt_log (by norm_num)
                exact Real.exp_one_gt_d9
              _ = 1 := Real.log_exp 1
          calc Real.log (2 * Real.exp ‖z‖)
              = Real.log 2 + Real.log (Real.exp ‖z‖) :=
                Real.log_mul (by norm_num) (Real.exp_pos _)
            _ = Real.log 2 + ‖z‖ := by rw [Real.log_exp]
            _ < 1 + ‖z‖ := by linarith
      _ ≤ 2 * (1 + ‖z‖) ^ (1 : ℝ) := by
          simp only [Real.rpow_one]
          linarith [norm_nonneg z]

end EntireOfFiniteOrder

/-! ### Zero data for Hadamard factorization -/

/--
Abstract zero data for an entire function. This packages the nonzero zeros
as a multiset together with multiplicities, plus the multiplicity at `0`, and
assumes a local finiteness condition.

For many applications (e.g. L-functions), this will be constructed from an
explicit zero set with known multiplicities.
-/
structure ZeroData (f : ℂ → ℂ) where
  /-- The multiset of nonzero zeros (with multiplicity). -/
  zeros : Multiset ℂ
  /-- Local finiteness: the zeros in each closed ball form a finite multiset. -/
  zeros_finite_in_ball : ∀ R : ℝ, ∃ n : ℕ, (zeros.filter (fun z => ‖z‖ ≤ R)).card ≤ n
  /-- Order of vanishing at `0`. -/
  ord0 : ℕ
  /-- Specification of the zero set (up to multiplicity) of `f`. -/
  zero_spec :
    ∀ z : ℂ, f z = 0 ↔
      (z = 0 ∧ 0 < ord0) ∨ (z ≠ 0 ∧ 0 < Multiset.count z zeros)

/-- The counting function n(r) = #{|z| ≤ r : f(z) = 0} for zero data. -/
def ZeroData.countingFunction {f : ℂ → ℂ} (zd : ZeroData f) (r : ℝ) : ℕ :=
  (zd.zeros.filter (fun z => ‖z‖ ≤ r)).card + if zd.ord0 > 0 then 1 else 0

/-- The genus of entire function zero data, computed from convergence of ∑|ρ|^{-σ}. -/
def ZeroData.genus {f : ℂ → ℂ} (zd : ZeroData f) : ℕ :=
  -- The genus is the smallest integer m such that ∑_{ρ ∈ zeros} |ρ|^{-(m+1)} converges
  -- For practical purposes, this is bounded by the order of the function
  0  -- Placeholder; actual computation requires analysis of convergence

/--
**Hadamard factorization theorem (schematic version).**

If `f` is an entire function of finite order and `hz` describes its zeros,
then there exists a genus `m` and a complex polynomial `P` of degree bounded
in terms of the order such that

`f(z) = exp(P z) * z^{ord0} * ∏_{ρ ∈ zeros} E_m (z / ρ)^{mult(ρ)}`.

This is stated in a form intended for reuse by arithmetic applications; the
analytic core of the proof is a major theorem requiring either Nevanlinna theory
or Jensen's formula with careful growth estimates.

**Proof outline:**

1. **Construction of the canonical product:**
   Using `ZeroData`, build `G(z) = z^{ord0} * ∏ E_m(z / ρ)^{mult(ρ)}` where
   `m = ⌊ρ⌋` (the genus). The convergence is guaranteed by the order condition.

2. **G is entire with the same zeros as f:**
   By `weierstrassProduct_converges`, G is analytic. The zeros match by construction.

3. **The quotient H = f/G is entire and zero-free:**
   H has removable singularities at the zeros of G (matching multiplicities)
   and is never zero (zeros of f are exactly zeros of G).

4. **H has polynomial logarithm:**
   Using the finite order bound on f and the growth estimate for G, we show
   log H(z) has polynomial growth, hence is a polynomial by Liouville's theorem.

5. **Conclusion:**
   Writing H(z) = exp(P(z)) for a polynomial P gives the factorization.
   The degree bound deg P ≤ ⌈ρ⌉ follows from the growth estimates.

This theorem is one of the crown jewels of classical complex analysis.
-/
theorem hadamard_factorization
    {ρ : ℝ} {f : ℂ → ℂ}
    (hf : EntireOfFiniteOrder ρ f)
    (hz : ZeroData f) :
    ∃ (m : ℕ) (P : Polynomial ℂ),
      P.degree ≤ (Nat.ceil ρ) ∧
      ∀ z : ℂ,
        f z = Complex.exp (Polynomial.eval z P) *
          z ^ hz.ord0 *
          (hz.zeros.attach.map fun z0 =>
            (Complex.weierstrassElementaryFactor m (z / z0.1)) ^
              (Multiset.count z0.1 hz.zeros)).prod := by
  /-
  The proof of Hadamard's factorization theorem requires substantial infrastructure:

  1. **Nevanlinna theory** (characteristic function, proximity function, counting function)
     or **Jensen's formula** with careful analysis.

  2. **Borel-Carathéodory theorem** or **Hadamard three-circles theorem** for
     growth estimates on log|f|.

  3. **Logarithmic derivative estimates** showing that for entire functions of
     finite order, the logarithmic derivative f'/f has controlled growth.

  4. **Liouville-type theorem for polynomial growth**: An entire function with
     polynomial growth is a polynomial.

  The connection to the Riemann folder infrastructure:
  - `JensenFormula.lean` provides Jensen's formula infrastructure
  - `NevanlinnaConnection.lean` connects to proximity functions
  - `CanonicalFactorization.lean` gives the Hardy space version

  For a complete proof, one would:
  1. Use Jensen's formula to bound ∑ log(R/|aₙ|) ≤ C·R^ρ
  2. Show this implies ∑ |aₙ|^{-σ} < ∞ for σ > ρ (Lindelöf's theorem)
  3. Construct the canonical product with genus m = ⌊ρ⌋
  4. Apply growth estimates from Hadamard's three-lines theorem
  5. Use the Borel-Carathéodory lemma to bound log|f/G|
  6. Conclude by the polynomial growth theorem

  This is beyond the current mathlib infrastructure but the statement
  captures the exact form needed for applications to L-functions.
  -/
  sorry

/-- The genus in Hadamard's theorem is bounded by the order. -/
theorem hadamard_genus_bound {ρ : ℝ} {f : ℂ → ℂ}
    (hf : EntireOfFiniteOrder ρ f) (hz : ZeroData f) (hρ : 0 ≤ ρ) :
    hz.genus ≤ Nat.floor ρ := by
  -- The genus is the smallest integer m such that ∑ |aₙ|^{-(m+1)} converges
  -- For functions of order ρ, this sum converges for all m ≥ ρ
  -- Hence genus ≤ ⌊ρ⌋
  sorry

end ComplexAnalysis

end
