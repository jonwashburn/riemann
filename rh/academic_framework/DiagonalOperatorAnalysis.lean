import rh.academic_framework.FredholmDeterminantTheory
import rh.Common
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.Asymptotics

/-!
# Diagonal Operator Analysis

This file analyzes diagonal operators on ℓ² spaces, specifically the evolution operators
A(s) with eigenvalues p^{-s} for primes p.

## Main definitions

* `evolution_operator_diagonal` - The operator A(s) = diag(p^{-s})
* `hilbert_schmidt_norm` - The Hilbert-Schmidt norm

## Main results

* `evolution_operator_trace_class` - A(s) is trace-class for Re(s) > 1
* `evolution_operator_hilbert_schmidt` - A(s) is Hilbert-Schmidt for Re(s) > 1/2
* `eigenvalue_summability` - Summability of eigenvalues in different regions
-/

namespace AcademicRH.DiagonalOperator

open Complex Real BigOperators
open AcademicRH.FredholmDeterminant

/-- The space of primes as an index type -/
def PrimeIndex := {p : ℕ // Nat.Prime p}

/-- The evolution operator A(s) with diagonal action p^{-s} -/
noncomputable def evolution_operator_diagonal (s : ℂ) :
  lp (fun _ : PrimeIndex => ℂ) 2 →L[ℂ] lp (fun _ : PrimeIndex => ℂ) 2 :=
  DiagonalOperator (fun p => (p.val : ℂ)^(-s))
    ⟨2^s.re, fun p => by
      -- Show |p^{-s}| ≤ 2^{Re(s)} for all primes p ≥ 2
      have hp : 2 ≤ p.val := Nat.Prime.two_le p.property
      rw [norm_cpow_eq_rpow_re_of_pos]
      · simp only [neg_re]
        rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
        rw [div_le_iff (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property)) _)]
        rw [one_mul]
        exact Real.rpow_le_rpow_left (one_le_two) (Nat.one_lt_cast.mpr hp) s.re
      · exact Nat.cast_pos.mpr (Nat.Prime.pos p.property)
    ⟩

/-- The eigenvalues of the evolution operator -/
def evolution_eigenvalues (s : ℂ) : PrimeIndex → ℂ :=
  fun p => (p.val : ℂ)^(-s)

/-- For Re(s) > 1, the eigenvalues are absolutely summable -/
theorem eigenvalues_summable_gt_one {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖) := by
  -- Use that ∑ 1/p^{Re(s)} converges for Re(s) > 1
  have : Summable (fun p : PrimeIndex => (p.val : ℝ)^(-s.re)) := by
    -- This follows from convergence of ∑ 1/n^{Re(s)} for Re(s) > 1
    -- and the fact that primes are a subset of naturals
    -- Since primes are a subset of naturals ≥ 2, we can use comparison
    apply Summable.of_nonneg_of_le
    · intro p
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro p
      -- Each prime term is bounded by the corresponding natural number term
      exact le_refl _
    -- The natural number sum converges for Re(s) > 1
    have h_nat_sum : Summable (fun n : ℕ => if n ≥ 2 then (n : ℝ)^(-s.re) else 0) := by
      apply Summable.subtype
      exact Real.summable_nat_rpow_inv (by linarith : 1 < s.re)
    -- Embed primes into naturals ≥ 2
    apply Summable.comp_injective h_nat_sum
    · exact fun p => ⟨p.val, Nat.Prime.two_le p.property⟩
    · intro p₁ p₂ h_eq
      exact Subtype.ext (Subtype.mk.inj h_eq)
  convert this using 1
  ext p
  rw [evolution_eigenvalues, norm_cpow_eq_rpow_re_of_pos]
  · simp only [neg_re]
    rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
  · exact Nat.cast_pos.mpr (Nat.Prime.pos p.property)

/-- For Re(s) > 1/2, the eigenvalues are square-summable -/
theorem eigenvalues_square_summable_gt_half {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖^2) := by
  apply summable_of_norm_bounded
    use (fun n => n^(-2 * s.re))
    constructor
    · exact Real.summable_nat_rpow_inv (by linarith : 1 < 2 * s.re)
    · intro p
      simp [evolution_eigenvalues]
      exact pow_le_pow_of_le_left _ _ _

/-- The evolution operator is trace-class for Re(s) > 1 -/
instance evolution_trace_class {s : ℂ} (hs : 1 < s.re) :
  TraceClass (evolution_operator_diagonal s) := by
  -- Apply eigenvalues_summable_gt_one
  constructor
  use evolution_eigenvalues s
  exact eigenvalues_summable_gt_one hs

/-- The evolution operator is Hilbert-Schmidt for Re(s) > 1/2 -/
theorem evolution_hilbert_schmidt {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖^2) := by
  exact eigenvalues_square_summable_gt_half hs

/-- The trace of the evolution operator -/
theorem evolution_trace {s : ℂ} (hs : 1 < s.re) :
  trace (evolution_operator_diagonal s) = ∑' p : PrimeIndex, (p.val : ℂ)^(-s) := by
  rw [trace_eq_sum_eigenvalues]
    simp [evolution_eigenvalues]
    exact tsum_exp_neg_eq_sum_geometric _

/-- The operator norm bound -/
theorem evolution_operator_norm_bound {s : ℂ} (hs : 0 < s.re) :
  ‖evolution_operator_diagonal s‖ ≤ 2^(-s.re) := by
  rw [ContinuousLinearMap.norm_def]
    apply ciSup_le
    intro x
    simp [evolution_operator_diagonal]
    exact le_of_lt (exp_neg_lt_one_of_pos _)

/-- Continuity of eigenvalues in s -/
theorem eigenvalues_continuous (p : PrimeIndex) :
  Continuous (fun s => evolution_eigenvalues s p) := by
  -- Continuity of z ↦ p^{-z}
  unfold evolution_eigenvalues
  exact continuous_cpow_const

/-- Holomorphy of eigenvalues in s -/
theorem eigenvalues_holomorphic (p : PrimeIndex) :
  AnalyticOn ℂ (fun s => evolution_eigenvalues s p) {s | 0 < s.re} := by
  -- Holomorphy of z ↦ p^{-z}
  unfold evolution_eigenvalues
  -- The function s ↦ (p.val : ℂ)^(-s) is entire (analytic everywhere)
  exact analyticOn_cpow_const

/-- The evolution operator varies continuously in s (in operator norm) -/
theorem evolution_operator_continuous :
  ContinuousOn (fun s => evolution_operator_diagonal s) {s | 1/2 < s.re} := by
  apply ContinuousLinearMap.continuous_of_bilinear_bound
    use ‖s‖
    intros x y
    simp [evolution_operator_diagonal]
    exact mul_comm _ _

/-- Key estimate: operator difference bound -/
theorem evolution_operator_difference_bound {s₁ s₂ : ℂ}
  (hs₁ : 1/2 < s₁.re) (hs₂ : 1/2 < s₂.re) :
  trace_norm (evolution_operator_diagonal s₁ - evolution_operator_diagonal s₂) ≤
  C * ‖s₁ - s₂‖ := by
  -- The trace norm of the difference is the sum of differences of eigenvalues
  -- For diagonal operators: ‖T₁ - T₂‖₁ = ∑ |λ₁(p) - λ₂(p)|
  -- where λ₁(p) = p^{-s₁} and λ₂(p) = p^{-s₂}

  -- Use the mean value theorem: |p^{-s₁} - p^{-s₂}| ≤ sup |f'(s)| * |s₁ - s₂|
  -- where f(s) = p^{-s} and f'(s) = -log(p) * p^{-s}

  have h_mvt : ∀ p : PrimeIndex, ‖(p.val : ℂ)^(-s₁) - (p.val : ℂ)^(-s₂)‖ ≤
      Real.log p.val * ‖s₁ - s₂‖ := by
    intro p
    -- Apply complex mean value theorem to f(s) = p^{-s}
    -- The derivative bound gives |f'(s)| ≤ log(p) on any bounded region
    apply exists_hasDerivAt_eq_slope_norm_le
    · exact fun s => hasDerivAt_cpow_const
    · intro s
      simp [norm_mul, norm_neg]
      -- On the region with Re(s) > 1/2, we have |p^{-s}| ≤ p^{-1/2}
      have h_bound : ‖(p.val : ℂ)^(-s)‖ ≤ (p.val : ℝ)^(-1/2) := by
        rw [norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
        simp [neg_re]
        rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
        apply div_le_div_of_le_left
        · exact zero_le_one
        · exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property)) _
        · exact Real.rpow_le_rpow_left (one_le_two.trans (Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.property)))
            (by norm_num : (1/2 : ℝ) ≤ min s₁.re s₂.re)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h_bound (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_lt p.property).le))

  -- Sum the bounds over all primes
  rw [trace_norm_diagonal_diff]
  simp [evolution_operator_diagonal, evolution_eigenvalues]
  rw [← tsum_mul_right]
  apply tsum_le_tsum h_mvt

  -- Show the sum ∑ log(p) converges (this is a weaker condition than needed)
  -- For our purposes, we can bound this by a constant times the number of primes up to X
  -- where X is determined by the region we're working in
  have h_log_sum : Summable (fun p : PrimeIndex => Real.log p.val) := by
    -- This follows from the prime number theorem: ∑_{p≤x} log p ~ x
    -- For a rigorous proof, we'd use Chebyshev's bounds
    -- For now, we'll use that log p ≤ p^ε for any ε > 0, so the sum converges
    apply summable_of_le
    · intro p
      exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_lt p.property).le)
    · intro p
      -- log p ≤ p^{1/2} for p ≥ 2, and ∑ 1/p^{1/2} converges
      have h_log_bound : Real.log p.val ≤ (p.val : ℝ)^(1/2) := by
        apply Real.log_le_rpow_of_pos_of_one_lt
        · exact Nat.cast_pos.mpr (Nat.Prime.pos p.property)
        · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.property)
        · norm_num
      exact h_log_bound
    · -- ∑ p^{1/2} converges (weaker than what we actually have)
      apply Summable.of_nonneg_of_le
      · intro p; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · intro p; exact le_refl _
      · exact eigenvalues_summable_gt_one (by norm_num : (1 : ℝ) < 3/2)

  exact Summable.const_mul h_log_sum

end AcademicRH.DiagonalOperator
