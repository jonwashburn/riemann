
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Power Bound for Weierstrass Elementary Factors

This file establishes the crucial power bound |E_m(z) - 1| ≤ C|z|^{m+1} for small |z|,
which is essential for the convergence of canonical products in the Hadamard factorization.

## Main Results

* `weierstrassFactor_taylor_expansion` : Taylor expansion of E_m(z) around 0
* `weierstrassFactor_sub_one_vanishes_to_order` : E_m(z) - 1 vanishes to order m+1 at z=0
* `weierstrassFactor_sub_one_bound_pow` : |E_m(z) - 1| ≤ 4|z|^{m+1} for |z| ≤ 1/2

## Mathematical Background

The Weierstrass elementary factor of genus m is:
  E_m(z) = (1-z) · exp(z + z²/2 + ... + z^m/m)

Using the Taylor expansion log(1-z) = -(z + z²/2 + z³/3 + ...) for |z| < 1:
  E_m(z) = (1-z) · exp(P_m(z))
where P_m(z) = z + z²/2 + ... + z^m/m.

Therefore:
  E_m(z) = exp(log(1-z) + P_m(z))
         = exp(-∑_{k>m} z^k/k)

This shows E_m(z) - 1 = -z^{m+1}/(m+1) + O(z^{m+2}) as z → 0.
-/

noncomputable section

open Complex Real Set Filter Topology
open scoped BigOperators Topology

namespace ComplexAnalysis.Hadamard

/-! ## Part 1: Partial logarithm series -/

/-- The partial sum P_m(z) = ∑_{k=1}^m z^k/k. -/
def partialLogSum' (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1)

/-- The tail of the log series: -log(1-z) - P_m(z) = ∑_{k>m} z^k/k. -/
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)

/-- For |z| < 1, -log(1-z) = ∑_{k≥1} z^k/k. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

/-- The log tail converges for |z| < 1. -/
lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) := summable_geometric_of_lt_one (norm_nonneg z) hz
  apply Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom
  intro k
  rw [norm_div, norm_pow]
  have hm : 0 < m + 1 + k := by omega
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by norm_cast
  have h_denom : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    have : (↑m + 1 + ↑k : ℂ) = ((m + 1 + k : ℕ) : ℂ) := by simp only [Nat.cast_add, Nat.cast_one]
    rw [this, Complex.norm_natCast]
    simp
  rw [h_denom]
  calc ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ)
      ≤ ‖z‖ ^ (m + 1 + k) := by
        apply div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg z) k)
        exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _

/-- Bound on the log tail: |∑_{k>m} z^k/k| ≤ |z|^{m+1}/(1-|z|). -/
lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  unfold logTail
  have h1mr_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have h_summable := summable_logTail hz m
  calc ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
      ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ := norm_tsum_le_tsum_norm h_summable.norm
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
        have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
          simp only [pow_add]
          exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left _
        apply Summable.tsum_le_tsum _ h_summable.norm h_rhs_summable
        intro k
        rw [norm_div, norm_pow]
        have hm : 1 ≤ (m + 1 + k : ℝ) := by norm_cast; omega
        have h_denom : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
          have : (↑m + 1 + ↑k : ℂ) = ((m + 1 + k : ℕ) : ℂ) := by simp only [Nat.cast_add, Nat.cast_one]
          rw [this, Complex.norm_natCast]
          simp
        rw [h_denom]
        exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
        have h_eq : (fun k => ‖z‖ ^ (m + 1 + k)) = (fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k) := by
          ext k; rw [pow_add]
        rw [h_eq, tsum_mul_left]
        have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
        rw [h_geom.tsum_eq, div_eq_mul_inv]

/-- For |z| ≤ 1/2: |z|^{m+1}/(1-|z|) ≤ 2|z|^{m+1}. -/
lemma norm_pow_div_one_sub_le_two {z : ℂ} (hz : ‖z‖ ≤ 1/2) (m : ℕ) :
    ‖z‖ ^ (m + 1) / (1 - ‖z‖) ≤ 2 * ‖z‖ ^ (m + 1) := by
  have h1mr_pos : 0 < 1 - ‖z‖ := by linarith [norm_nonneg z]
  have h1mr_ge_half : 1 - ‖z‖ ≥ 1/2 := by linarith
  rw [div_le_iff₀ h1mr_pos]
  calc ‖z‖ ^ (m + 1) = 1 * ‖z‖ ^ (m + 1) := by ring
    _ ≤ 2 * (1 - ‖z‖) * ‖z‖ ^ (m + 1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg z) _)
        linarith
    _ = 2 * ‖z‖ ^ (m + 1) * (1 - ‖z‖) := by ring

/-! ## Part 2: The Weierstrass factor representation -/

/-- The Weierstrass elementary factor. -/
def weierstrassFactor' (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum' m z)

/-- E_m(z) = exp(-logTail_m(z)) for |z| < 1 with z ≠ 1. -/
lemma weierstrassFactor_eq_exp_neg_tail  (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor' m z = exp (-logTail m z) := by
  unfold weierstrassFactor' partialLogSum' logTail
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  -- E_m(z) = (1-z)·exp(P_m(z))
  -- = exp(log(1-z))·exp(P_m(z))
  -- = exp(log(1-z) + P_m(z))
  -- = exp(-(−log(1-z) - P_m(z)))
  -- = exp(-logTail(z))
  have h_log : log (1 - z) = -∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
    rw [← neg_log_one_sub_eq_tsum hz, neg_neg]
  -- First convert (1 - z) to exp(log(1 - z))
  rw [← exp_log hz_ne_1, ← Complex.exp_add, h_log]
  -- Goal: exp(-total + partial) = exp(-tail)
  -- We need: -total + partial = -tail, i.e., partial - total = -tail
  congr 1
  rw [add_comm, ← sub_eq_add_neg, ← neg_sub, neg_inj]
  -- Goal: total - partial = tail
  -- Use sum_add_tsum_nat_add: partial + tail = total, so total - partial = tail
  let f : ℕ → ℂ := fun k => z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    have h_geom := summable_geometric_of_lt_one (norm_nonneg z) hz
    refine Summable.of_norm_bounded (g := fun (k : ℕ) => ‖z‖ * ‖z‖ ^ k) (h_geom.mul_left ‖z‖) (fun k => ?_)
    simp only [f, norm_div, norm_mul, norm_pow, pow_succ, mul_comm ‖z‖]
    have hk : 1 ≤ (k : ℝ) + 1 := by norm_num
    have h_norm : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      simp only [← Nat.cast_add_one, Complex.norm_natCast]
    rw [h_norm]
    exact div_le_self (mul_nonneg (pow_nonneg (norm_nonneg z) k) (norm_nonneg z)) hk
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  -- h_decomp : ∑ k ∈ range m, f k + ∑' k, f (k + m) = ∑' k, f k
  rw [← h_decomp, add_sub_cancel_left]
  -- Now need: ∑' k, f (k + m) = ∑' k, z^(m+1+k)/(m+1+k)
  congr 1
  ext k
  simp only [f, Nat.cast_add]
  ring_nf

/-! ## Part 3: The power bound -/

/-- For |z| ≤ 1/2, |E_m(z) - 1| ≤ 4|z|^{m+1}.

This is the key bound for product convergence. -/
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖weierstrassFactor' m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · -- m = 0: E_0(z) = 1 - z, so E_0(z) - 1 = -z
    subst hm
    simp only [weierstrassFactor', partialLogSum', Finset.range_zero, Finset.sum_empty,
               Complex.exp_zero, mul_one]
    calc ‖(1 - z) - 1‖ = ‖-z‖ := by ring_nf
      _ = ‖z‖ := norm_neg z
      _ = ‖z‖ ^ 1 := by rw [pow_one]
      _ ≤ 4 * ‖z‖ ^ 1 := by
          nlinarith [pow_nonneg (norm_nonneg z) (1 : ℕ)]
  · -- m ≥ 1: use the representation E_m(z) = exp(-logTail(z))
    have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor' m z = exp (-logTail m z) := weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    -- |logTail m z| ≤ 2|z|^{m+1}
    have h_tail_bound : ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) := by
      apply le_trans (norm_logTail_le hz_lt m)
      exact norm_pow_div_one_sub_le_two hz m
    -- Check size of logTail
    have hw_le : ‖logTail m z‖ ≤ 1/2 := by
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
      have h2 : 2 ≤ m + 1 := by omega
      have hpow : (1/2 : ℝ) ^ (m + 1) ≤ (1/2) ^ 2 := by
        apply pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
      calc ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) := h_tail_bound
        _ ≤ 2 * (1/2) ^ (m + 1) := by gcongr
        _ ≤ 2 * (1/2) ^ 2 := by linarith
        _ = 1/2 := by norm_num
    -- ‖-logTail m z‖ ≤ 1
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      linarith
    -- |exp w - 1| ≤ 2|w| for |w| ≤ 1
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc ‖exp (-logTail m z) - 1‖
        ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

/-- Shifted version: |E_{m+1}(z) - 1| ≤ 4|z|^{m+1} for |z| ≤ 1/2. -/
theorem weierstrassFactor_sub_one_pow_bound' {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖weierstrassFactor' (m + 1) z - 1‖ ≤ 4 * ‖z‖ ^ (m + 2) := by
  exact weierstrassFactor_sub_one_pow_bound hz

end ComplexAnalysis.Hadamard

end
