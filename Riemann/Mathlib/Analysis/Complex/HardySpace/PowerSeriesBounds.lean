import Riemann.Mathlib.Analysis.Complex.HardySpace.ExpLogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Power Series Bounds

Bounds on power series needed for Weierstrass products and Blaschke product convergence.

## Main results

* `norm_tsum_pow_tail_le` : Geometric series tail bound
* `Complex.summable_pow_div_succ` : Summability of z^{k+1}/(k+1)
* `Complex.norm_tsum_pow_div_succ_tail_le` : Tail bound for log series
* `Complex.log_one_sub_eq_neg_tsum` : log(1-z) = -∑ z^k/k

## References

* Standard complex analysis texts
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Geometric series bounds -/

/-- Geometric series tail bound: |∑_{k≥0} z^{n+k}| ≤ |z|^n / (1 - |z|) for |z| < 1. -/
lemma norm_tsum_pow_tail_le {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    ‖∑' k, z ^ (n + k)‖ ≤ ‖z‖ ^ n / (1 - ‖z‖) := by
  have h1mr_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have h_geom : HasSum (fun k => z ^ k) (1 - z)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hz
  have h_shift : HasSum (fun k => z ^ (n + k)) (z ^ n * (1 - z)⁻¹) := by
    convert h_geom.mul_left (z ^ n) using 1
    ext k; rw [pow_add]
  have h_ne : 1 - z ≠ 0 := by
    intro heq
    have : ‖(1 : ℂ) - z‖ = 0 := by rw [heq]; simp
    have h1 : ‖(1 : ℂ) - z‖ ≥ 1 - ‖z‖ := by
      calc ‖(1 : ℂ) - z‖ ≥ |‖(1 : ℂ)‖ - ‖z‖| := abs_norm_sub_norm_le 1 z
        _ ≥ ‖(1 : ℂ)‖ - ‖z‖ := le_abs_self _
        _ = 1 - ‖z‖ := by simp
    linarith
  have h_denom_bound : 1 - ‖z‖ ≤ ‖1 - z‖ := by
    calc 1 - ‖z‖ = ‖(1 : ℂ)‖ - ‖z‖ := by simp
      _ ≤ |‖(1 : ℂ)‖ - ‖z‖| := le_abs_self _
      _ ≤ ‖(1 : ℂ) - z‖ := abs_norm_sub_norm_le 1 z
  calc ‖∑' k, z ^ (n + k)‖ = ‖z ^ n * (1 - z)⁻¹‖ := by
        rw [h_shift.tsum_eq]
    _ = ‖z ^ n‖ * ‖(1 - z)⁻¹‖ := norm_mul _ _
    _ = ‖z‖ ^ n * ‖(1 - z)⁻¹‖ := by rw [norm_pow]
    _ = ‖z‖ ^ n * (‖1 - z‖⁻¹) := by rw [norm_inv]
    _ = ‖z‖ ^ n / ‖1 - z‖ := by ring
    _ ≤ ‖z‖ ^ n / (1 - ‖z‖) := by
        apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg z) n) h1mr_pos h_denom_bound

/-- The power series ∑_{k≥0} z^{k+1}/(k+1) converges absolutely for |z| < 1. -/
lemma summable_pow_div_succ {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => z ^ (k + 1) / (k + 1)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) := summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have hk_pos : (0 : ℝ) < (k : ℕ) + 1 := Nat.cast_add_one_pos k
  have h_norm_eq : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    have h1 : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by simp
    rw [h1, norm_natCast]
    simp
  rw [h_norm_eq]
  have h1 : ‖z‖ ^ (k + 1) / ((k : ℕ) + 1) ≤ ‖z‖ ^ (k + 1) := by
    apply div_le_self (pow_nonneg (norm_nonneg z) _)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc ‖z‖ ^ (k + 1) / ((k : ℕ) + 1) ≤ ‖z‖ ^ (k + 1) := h1
    _ = ‖z‖ ^ k * ‖z‖ := by ring
    _ ≤ ‖z‖ ^ k * 1 := mul_le_mul_of_nonneg_left (le_of_lt hz) (pow_nonneg (norm_nonneg z) k)
    _ = ‖z‖ ^ k := mul_one _

/-- Tail bound for the geometric series: ∑_{k≥0} r^{n+1+k} = r^{n+1}/(1-r) for 0 ≤ r < 1. -/
lemma Real.tsum_pow_tail_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑' k, r ^ (n + 1 + k) = r ^ (n + 1) / (1 - r) := by
  have h1mr_pos : 0 < 1 - r := sub_pos.mpr hr1
  have h_geom := hasSum_geometric_of_lt_one hr0 hr1
  have h_eq : (fun k => r ^ (n + 1 + k)) = (fun k => r ^ (n + 1) * r ^ k) := by
    funext k; rw [← pow_add, add_comm]
  rw [h_eq, tsum_mul_left, h_geom.tsum_eq, div_eq_mul_inv]

/-- Bound on norm of power divided by index. -/
lemma norm_pow_div_nat_le {z : ℂ} (m : ℕ) (hm : 0 < m) :
    ‖z ^ m / (m : ℂ)‖ ≤ ‖z‖ ^ m := by
  rw [norm_div, norm_pow, norm_natCast]
  exact div_le_self (pow_nonneg (norm_nonneg z) m) (Nat.one_le_cast.mpr hm)

/-- Summability of power series with factorial-like denominators. -/
lemma summable_pow_div_add {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    Summable (fun k => z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) := summable_geometric_of_lt_one (norm_nonneg z) hz
  apply Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom
  intro k
  have hm : 0 < n + 1 + k := by omega
  calc ‖z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖
      ≤ ‖z‖ ^ (n + 1 + k) := norm_pow_div_nat_le (n + 1 + k) hm
    _ = ‖z‖ ^ (n + 1) * ‖z‖ ^ k := by rw [show n + 1 + k = (n + 1) + k by omega, pow_add]
    _ ≤ 1 * ‖z‖ ^ k := mul_le_mul_of_nonneg_right
        (pow_le_one₀ (norm_nonneg z) (le_of_lt hz)) (pow_nonneg (norm_nonneg z) k)
    _ = ‖z‖ ^ k := one_mul _

/-- Tail bound for the log series: |∑_{k≥0} z^{n+1+k}/(n+1+k)| ≤ |z|^{n+1}/(1-|z|) for |z| < 1. -/
lemma norm_tsum_pow_div_succ_tail_le {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    ‖∑' k, z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖ ≤ ‖z‖ ^ (n + 1) / (1 - ‖z‖) := by
  have h1mr_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  by_cases hz0 : z = 0
  · simp [hz0]
  · have h_summable := summable_pow_div_add hz n
    have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) := summable_geometric_of_lt_one (norm_nonneg z) hz
    have h_term_bound : ∀ k, ‖z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖ ≤ ‖z‖ ^ (n + 1 + k) := by
      intro k
      exact norm_pow_div_nat_le (n + 1 + k) (by omega)
    have h_geom_summable : Summable (fun k => ‖z‖ ^ (n + 1 + k)) := by
      refine h_geom.mul_left (‖z‖ ^ (n + 1)) |>.congr ?_
      intro k
      simp only [pow_add, mul_comm]
    calc ‖∑' k, z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖
        ≤ ∑' k, ‖z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖ := norm_tsum_le_tsum_norm h_summable.norm
      _ ≤ ∑' k, ‖z‖ ^ (n + 1 + k) := h_summable.norm.tsum_le_tsum h_term_bound h_geom_summable
      _ = ‖z‖ ^ (n + 1) / (1 - ‖z‖) := Real.tsum_pow_tail_eq (norm_nonneg z) hz n

set_option maxHeartbeats 800000 in
/-- The complex logarithm series: log(1-z) = -∑_{k≥1} z^k/k for |z| < 1. -/
lemma log_one_sub_eq_neg_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    log (1 - z) = -∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
  have h_hasSum := hasSum_taylorSeries_neg_log hz
  have h1 : log (1 - z) = -(∑' n : ℕ, z ^ n / (n : ℂ)) := by
    rw [h_hasSum.tsum_eq]; ring
  rw [h1]
  congr 1
  have h_eq := h_hasSum.summable.tsum_eq_zero_add
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add] at h_eq
  convert h_eq using 2 <;> simp only [Nat.cast_add, Nat.cast_one]

/-! ### Additional bounds for small |z| -/

/-- The partial sum of z^k/k for k = 1 to n. -/
def partialLogSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, z ^ (k + 1) / (k + 1)

/-- The partial log sum at 0 is 0. -/
lemma partialLogSum_zero (n : ℕ) : partialLogSum n 0 = 0 := by
  unfold partialLogSum
  apply Finset.sum_eq_zero
  intro k _
  simp only [zero_pow (Nat.succ_ne_zero k), zero_div]

/-- The partial log sum for n = 0 is 0. -/
lemma partialLogSum_range_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  unfold partialLogSum
  simp only [Finset.range_zero, Finset.sum_empty]

/-- Bound on partial log sum: |P_n(z)| ≤ |z|/(1-|z|) for |z| < 1. -/
lemma norm_partialLogSum_le {n : ℕ} {z : ℂ} (hz : ‖z‖ < 1) :
    ‖partialLogSum n z‖ ≤ ‖z‖ / (1 - ‖z‖) := by
  unfold partialLogSum
  have h1mr_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
  have h_term_bound : ∀ k : ℕ, ‖z ^ (k + 1) / ((k : ℂ) + 1)‖ ≤ ‖z‖ ^ (k + 1) := fun k => by
    rw [norm_div, norm_pow]
    apply div_le_self (pow_nonneg (norm_nonneg z) _)
    have hk : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      have h1 : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [h1, norm_natCast]; simp
    rw [hk]
    have hk_pos : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact hk_pos
  calc ‖∑ k ∈ Finset.range n, z ^ (k + 1) / (k + 1)‖
      ≤ ∑ k ∈ Finset.range n, ‖z ^ (k + 1) / ((k : ℂ) + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, ‖z‖ ^ (k + 1) := Finset.sum_le_sum (fun k _ => h_term_bound k)
    _ = ‖z‖ * ∑ k ∈ Finset.range n, ‖z‖ ^ k := by
        rw [Finset.mul_sum]
        congr 1
        ext k
        rw [pow_succ, mul_comm]
    _ ≤ ‖z‖ * (1 / (1 - ‖z‖)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
        have h_le : ∑ k ∈ Finset.range n, ‖z‖ ^ k ≤ ∑' k, ‖z‖ ^ k :=
          h_geom.summable.sum_le_tsum (Finset.range n) (fun k _ => pow_nonneg (norm_nonneg z) k)
        calc ∑ k ∈ Finset.range n, ‖z‖ ^ k ≤ ∑' k, ‖z‖ ^ k := h_le
          _ = 1 / (1 - ‖z‖) := by rw [h_geom.tsum_eq, one_div]
    _ = ‖z‖ / (1 - ‖z‖) := by ring

/-- For x ≤ 1/2 with x ≥ 0, we have 1/(1-x) ≤ 2. -/
lemma one_div_one_sub_le_two {x : ℝ} (hx : x ≤ 1/2) (hx_nn : 0 ≤ x) :
    1 / (1 - x) ≤ 2 := by
  have h1mx_pos : 0 < 1 - x := by linarith
  rw [div_le_iff₀ h1mx_pos]
  linarith

/-- For |z| ≤ 1/2, we have |z|/(1-|z|) ≤ 2|z|. -/
lemma norm_div_one_sub_le_two_mul {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖z‖ / (1 - ‖z‖) ≤ 2 * ‖z‖ := by
  have h1mr_pos : 0 < 1 - ‖z‖ := by
    have := norm_nonneg z
    linarith
  rw [div_le_iff₀ h1mr_pos]
  calc ‖z‖ = 1 * ‖z‖ := by ring
    _ ≤ 2 * (1 - ‖z‖) * ‖z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
        have h1mx : 1 - ‖z‖ ≥ 1/2 := by linarith
        linarith
    _ = 2 * ‖z‖ * (1 - ‖z‖) := by ring

/-- For |z| ≤ 1/2, we have |z|^{n+1}/(1-|z|) ≤ 2|z|^{n+1}. -/
lemma norm_pow_div_one_sub_le {z : ℂ} {n : ℕ} (hz : ‖z‖ ≤ 1/2) :
    ‖z‖ ^ (n + 1) / (1 - ‖z‖) ≤ 2 * ‖z‖ ^ (n + 1) := by
  have h1mr_pos : 0 < 1 - ‖z‖ := by
    have := norm_nonneg z
    linarith
  rw [div_le_iff₀ h1mr_pos]
  have h_bound : 1 ≤ 2 * (1 - ‖z‖) := by linarith
  calc ‖z‖ ^ (n + 1) = 1 * ‖z‖ ^ (n + 1) := by ring
    _ ≤ 2 * (1 - ‖z‖) * ‖z‖ ^ (n + 1) := by
        apply mul_le_mul_of_nonneg_right h_bound (pow_nonneg (norm_nonneg z) _)
    _ = 2 * ‖z‖ ^ (n + 1) * (1 - ‖z‖) := by ring

/-- For |z| ≤ 1/2, we have |z|^{n+1} ≤ 1/4 when n ≥ 1. -/
lemma norm_pow_succ_le_quarter {z : ℂ} {n : ℕ} (hz : ‖z‖ ≤ 1/2) (hn : 1 ≤ n) :
    ‖z‖ ^ (n + 1) ≤ 1/4 := by
  have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
  have hz_le1 : ‖z‖ ≤ 1 := le_trans hz (by norm_num)
  have hn2 : 2 ≤ n + 1 := by omega
  have h1 : ‖z‖ ^ (n + 1) ≤ ‖z‖ ^ 2 := by
    rcases eq_or_lt_of_le hz_nn with hz0 | hz_pos
    · simp [← hz0]
    · have hz_lt1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
      rw [pow_le_pow_iff_right_of_lt_one₀ hz_pos hz_lt1]
      exact hn2
  have h2 : ‖z‖ ^ 2 ≤ (1/2 : ℝ) ^ 2 := by
    apply sq_le_sq' (by linarith) hz
  linarith [h1, h2]

/-- Bound on the tail of the log series: |∑_{k≥n+1} z^k/k| ≤ |z|^{n+1}/(1-|z|). -/
lemma norm_log_tail_le {z : ℂ} (hz : ‖z‖ < 1) (n : ℕ) :
    ‖∑' k : ℕ, z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖ ≤ ‖z‖ ^ (n + 1) / (1 - ‖z‖) :=
  norm_tsum_pow_div_succ_tail_le hz n

/-- For |z| ≤ 1/2, the tail bound simplifies to 2|z|^{n+1}. -/
lemma norm_log_tail_le_two_mul {z : ℂ} (hz : ‖z‖ ≤ 1/2) (n : ℕ) :
    ‖∑' k : ℕ, z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖ ≤ 2 * ‖z‖ ^ (n + 1) := by
  have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  calc ‖∑' k : ℕ, z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖
      ≤ ‖z‖ ^ (n + 1) / (1 - ‖z‖) := norm_log_tail_le hz_lt n
    _ ≤ 2 * ‖z‖ ^ (n + 1) := norm_pow_div_one_sub_le hz

/-- For |z| ≤ 1/2 and n ≥ 1, the tail bound is at most 1/2. -/
lemma norm_log_tail_le_half {z : ℂ} (hz : ‖z‖ ≤ 1/2) {n : ℕ} (hn : 1 ≤ n) :
    ‖∑' k : ℕ, z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖ ≤ 1/2 := by
  have h1 : ‖∑' k : ℕ, z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖ ≤ 2 * ‖z‖ ^ (n + 1) :=
    norm_log_tail_le_two_mul hz n
  have h2 : ‖z‖ ^ (n + 1) ≤ 1/4 := norm_pow_succ_le_quarter hz hn
  calc ‖∑' k : ℕ, z ^ (n + 1 + k) / ((n + 1 + k : ℕ) : ℂ)‖
      ≤ 2 * ‖z‖ ^ (n + 1) := h1
    _ ≤ 2 * (1/4) := by nlinarith [pow_nonneg (norm_nonneg z) (n+1)]
    _ = 1/2 := by norm_num

end Complex
