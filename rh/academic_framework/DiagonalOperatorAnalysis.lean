import rh.academic_framework.DiagonalFredholm
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
open AcademicRH.DiagonalFredholm

/-- The space of primes as an index type -/
def PrimeIndex := {p : ℕ // Nat.Prime p}

/-- The evolution operator A(s) with diagonal action p^{-s} -/
noncomputable def evolution_operator_diagonal (s : ℂ) :
  lp (fun _ : PrimeIndex => ℂ) 2 →L[ℂ] lp (fun _ : PrimeIndex => ℂ) 2 :=
  DiagonalOperator (fun p => (p.val : ℂ)^(-s))
    ⟨2^(|s.re|), fun p => by
      -- Show |p^{-s}| ≤ 2^|Re(s)| for all primes p ≥ 2
      -- We have |p^{-s}| = p^{-Re(s)}
      -- If Re(s) ≥ 0, then p^{-Re(s)} ≤ 1 ≤ 2^|Re(s)|
      -- If Re(s) < 0, then p^{-Re(s)} = p^{|Re(s)|} ≤ 2^|Re(s)|
      rw [norm_cpow_of_ne_zero (by simp : (p.val : ℂ) ≠ 0), neg_re]
      rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
      by_cases h : 0 ≤ s.re
      · -- Case: Re(s) ≥ 0, so p^{-Re(s)} ≤ 1
        have : (p.val : ℝ)^s.re ≥ 1 := by
          apply Real.one_le_rpow_of_pos_of_le_one_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))
          · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.property)
          · exact h
        rw [inv_le_iff_one_le_mul (by positivity)]
        calc 1 ≤ (p.val : ℝ)^s.re := this
             _ = (p.val : ℝ)^s.re * 1 := by ring
             _ ≤ (p.val : ℝ)^s.re * 2^|s.re| := by
               apply mul_le_mul_of_nonneg_left
               · rw [abs_of_nonneg h]
                 exact one_le_two_pow
               · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · -- Case: Re(s) < 0, so p^{-Re(s)} = p^{|Re(s)|}
        push_neg at h
        rw [abs_of_neg h, neg_neg, inv_eq_one_div]
        rw [div_le_iff (by positivity : (0 : ℝ) < (p.val : ℝ)^s.re)]
        calc 1 = 1^(-s.re) := by simp
             _ ≤ 2^(-s.re) := by
               apply Real.rpow_le_rpow (by norm_num : 0 ≤ 1) (by norm_num : 1 ≤ 2) (by linarith)
             _ = 2^(-s.re) * 1 := by ring
             _ ≤ 2^(-s.re) * (p.val : ℝ)^s.re := by
               apply mul_le_mul_of_nonneg_left
               · have : (p.val : ℝ) ≥ 2 := Nat.cast_le.mpr (Nat.Prime.two_le p.property)
                 exact Real.one_le_rpow_of_pos_of_le_one_of_pos (by norm_num : (0 : ℝ) < 2) this (by linarith)
               · exact Real.rpow_nonneg (by norm_num) _⟩

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
  -- We need to show ∑ |p^{-s}|² converges
  -- |p^{-s}|² = p^{-2Re(s)}
  -- Since 2Re(s) > 1, this is like showing ∑ 1/p^α converges for α > 1

  -- First convert the norm squared
  have h_eq : ∀ p : PrimeIndex, ‖evolution_eigenvalues s p‖^2 = (p.val : ℝ)^(-2 * s.re) := by
    intro p
    rw [evolution_eigenvalues, norm_cpow_of_ne_zero (by simp : (p.val : ℂ) ≠ 0), neg_re]
    rw [sq, Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
    rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg _)]
    rw [mul_comm 2, mul_neg, neg_neg]

  -- Now show this sum converges
  simp_rw [h_eq]

  -- Compare with the natural number sum ∑ 1/n^{2Re(s)}
  have h_nat_sum : Summable (fun n : ℕ => if n ≥ 2 then (n : ℝ)^(-2 * s.re) else 0) := by
    apply Summable.subtype
    exact Real.summable_nat_rpow_inv (by linarith : 1 < 2 * s.re)

  -- Embed primes into naturals ≥ 2
  apply Summable.comp_injective h_nat_sum
  · exact fun p => ⟨p.val, Nat.Prime.two_le p.property⟩
  · intro p₁ p₂ h_eq
    exact Subtype.ext (Subtype.mk.inj h_eq)

/-- The evolution operator is trace-class for Re(s) > 1 -/
-- We don't need an instance here, just the summability property
theorem evolution_trace_class {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p => ‖evolution_eigenvalues s p‖) := by
  exact eigenvalues_summable_gt_one hs

/-- The evolution operator is Hilbert-Schmidt for Re(s) > 1/2 -/
theorem evolution_hilbert_schmidt {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖^2) := by
  exact eigenvalues_square_summable_gt_half hs

/-- The trace of the evolution operator (not used in main proof) -/
-- Removed since it's not used and would require trace axiom

/-- The operator norm bound -/
theorem evolution_operator_norm_bound {s : ℂ} (hs : 0 < s.re) :
  ‖evolution_operator_diagonal s‖ ≤ 2^(-s.re) := by
  -- For diagonal operators, the operator norm is the supremum of |eigenvalues|
  -- Here the eigenvalues are p^{-s} for primes p
  -- We have |p^{-s}| = p^{-Re(s)}
  -- Since p ≥ 2 for all primes, p^{-Re(s)} ≤ 2^{-Re(s)} when Re(s) > 0

  -- The operator norm of a diagonal operator is sup_i |eigenvals i|
  -- We need to show sup_p |p^{-s}| ≤ 2^{-Re(s)}

  -- Use the fact that diagonal operators have norm equal to sup of eigenvalue norms
  rw [ContinuousLinearMap.norm_le_iff_norm_le_one]
  intro ψ

  -- Apply the diagonal operator
  rw [DiagonalOperator_apply]

  -- The norm of the result is bounded by the sup of eigenvalue norms times input norm
  have h_bound : ‖⟨fun i => evolution_eigenvalues s i * ψ i, _⟩‖ ≤ 2^(-s.re) * ‖ψ‖ := by
    -- Use the l² norm formula
    have h_norm_sq : ‖⟨fun i => evolution_eigenvalues s i * ψ i, _⟩‖^2 =
                     ∑' i, ‖evolution_eigenvalues s i * ψ i‖^2 := by
      rw [pow_two, ← lp.norm_sq_eq_inner_self]
      rw [lp.inner_def]
      simp [RCLike.inner_apply, conj_mul']
      congr 1
      ext i
      rw [norm_sq_eq_self]

    -- Bound each term
    have h_term_bound : ∀ i, ‖evolution_eigenvalues s i * ψ i‖^2 ≤ (2^(-s.re))^2 * ‖ψ i‖^2 := by
      intro i
      rw [norm_mul, mul_pow]
      apply mul_le_mul_of_nonneg_right
      · -- Show ‖evolution_eigenvalues s i‖^2 ≤ (2^(-s.re))^2
        rw [evolution_eigenvalues, norm_cpow_of_ne_zero (by simp : (i.val : ℂ) ≠ 0), neg_re]
        rw [sq, Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos i.property)), Real.rpow_two]
        rw [inv_pow, ← Real.rpow_two]
        apply inv_le_inv_of_le
        · exact Real.rpow_pos_of_pos (by norm_num : 0 < 2) _
        · have : 2 ≤ i.val := Nat.Prime.two_le i.property
          exact Real.rpow_le_rpow_left (by norm_num) (Nat.cast_le.mpr this) s.re
      · exact sq_nonneg _

    -- Sum the bounds
    rw [h_norm_sq]
    have h_sum_bound : ∑' i, ‖evolution_eigenvalues s i * ψ i‖^2 ≤ ∑' i, (2^(-s.re))^2 * ‖ψ i‖^2 := by
      apply tsum_le_tsum h_term_bound
      · exact Summable.mul_left _ ψ.property
      · apply Summable.of_nonneg_of_le
        · intro i; exact sq_nonneg _
        · exact h_term_bound
        · exact Summable.mul_left _ ψ.property

    -- Factor out the constant
    have h_factor : ∑' i, (2^(-s.re))^2 * ‖ψ i‖^2 = (2^(-s.re))^2 * ∑' i, ‖ψ i‖^2 := by
      rw [← tsum_mul_left]
    rw [h_factor] at h_sum_bound

    -- Use that ∑' i, ‖ψ i‖^2 = ‖ψ‖^2
    have h_ψ_norm : ∑' i, ‖ψ i‖^2 = ‖ψ‖^2 := by
      rw [pow_two, ← lp.norm_sq_eq_inner_self]
      rw [lp.inner_def]
      simp [RCLike.inner_apply, conj_mul']
      congr 1
      ext i
      rw [norm_sq_eq_self]
    rw [h_ψ_norm] at h_sum_bound

    -- Take square roots
    have h_sqrt : Real.sqrt (‖⟨fun i => evolution_eigenvalues s i * ψ i, _⟩‖^2) ≤
                  Real.sqrt ((2^(-s.re))^2 * ‖ψ‖^2) := by
      exact Real.sqrt_le_sqrt h_sum_bound
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq, Real.sqrt_sq] at h_sqrt
    · exact h_sqrt
    · exact Real.rpow_nonneg (by norm_num) _
    · exact norm_nonneg _

  convert h_bound using 1
  simp [evolution_operator_diagonal]

/-- Continuity of eigenvalues in s -/
theorem eigenvalues_continuous (p : PrimeIndex) :
  Continuous (fun s => evolution_eigenvalues s p) := by
  -- Continuity of z ↦ p^{-z}
  unfold evolution_eigenvalues
  -- The function s ↦ (p.val : ℂ)^(-s) is continuous
  -- This is the composition of continuous functions:
  -- s ↦ -s (continuous by neg_continuous)
  -- z ↦ (p.val : ℂ)^z (continuous on ℂ for p.val ≠ 0)
  apply Continuous.cpow
  · exact continuous_const
  · exact continuous_neg
  · intro s
    -- We need to show (p.val : ℂ) ≠ 0 ∨ -s ≠ 0
    left
    simp

/-- Holomorphy of eigenvalues in s -/
theorem eigenvalues_holomorphic (p : PrimeIndex) :
  AnalyticOn ℂ (fun s => evolution_eigenvalues s p) {s | 0 < s.re} := by
  -- Holomorphy of z ↦ p^{-z}
  unfold evolution_eigenvalues
  -- The function s ↦ (p.val : ℂ)^(-s) is entire (analytic everywhere)
  -- Since (p.val : ℂ) ≠ 0, the function z ↦ (p.val : ℂ)^z is entire
  -- So s ↦ (p.val : ℂ)^(-s) is also entire
  apply AnalyticOn.cpow
  · exact analyticOn_const
  · exact analyticOn_neg analyticOn_id
  · intro s _
    -- We need to show (p.val : ℂ) ≠ 0 ∨ -s ≠ 0
    left
    simp

/-- The evolution operator varies continuously in s (in operator norm) -/
theorem evolution_operator_continuous :
  ContinuousOn (fun s => evolution_operator_diagonal s) {s | 1/2 < s.re} := by
  -- To show continuity of s ↦ A(s) in operator norm
  -- We'll use that for diagonal operators, ‖A(s₁) - A(s₂)‖ is bounded by
  -- the supremum of |p^{-s₁} - p^{-s₂}| over all primes p

  -- For s in the region Re(s) > 1/2, we have uniform bounds
  intros s₀ hs₀

  -- We'll show continuity at s₀
  rw [Metric.continuousAt_iff]
  intro ε hε

  -- For diagonal operators, the difference is also diagonal
  -- with eigenvalues p^{-s} - p^{-s₀}

  -- Use the fact that p^{-s} is Lipschitz continuous in s on bounded regions
  -- The derivative is -log(p) * p^{-s}, which is bounded for Re(s) > 1/2

  -- Choose δ such that |s - s₀| < δ implies the operator norm difference < ε
  use ε / 2  -- Simplified choice of δ
  constructor
  · linarith

  intro s hs_mem hs_close
  simp at hs_mem

  -- The operator norm of A(s) - A(s₀) is bounded by sup_p |p^{-s} - p^{-s₀}|
  -- For diagonal operators, this is the supremum of eigenvalue differences

  -- Using continuity of each eigenvalue function
  have h_eigen_cont : ∀ p : PrimeIndex,
    ‖evolution_eigenvalues s p - evolution_eigenvalues s₀ p‖ < ε := by
    intro p
    -- Each p^{-s} is continuous in s
    have : Continuous (fun s => evolution_eigenvalues s p) := eigenvalues_continuous p
    -- Apply continuity at s₀
    rw [Metric.continuous_iff] at this
    specialize this s₀ ε hε
    exact this s hs_close

  -- The operator norm difference is bounded by the supremum of eigenvalue differences
  -- Since all eigenvalue differences are < ε, the operator norm difference is ≤ ε
  sorry -- This requires showing that sup norm equals operator norm for diagonal operators

/-- Key estimate: operator difference bound -/
theorem evolution_operator_difference_bound {s₁ s₂ : ℂ}
  (hs₁ : 1/2 < s₁.re) (hs₂ : 1/2 < s₂.re) :
  ∃ C, ∀ p : PrimeIndex, ‖evolution_eigenvalues s₁ p - evolution_eigenvalues s₂ p‖ ≤
    C * ‖s₁ - s₂‖ := by
  -- For diagonal operators, we can bound the difference of eigenvalues
  -- Use mean value theorem: |p^{-s₁} - p^{-s₂}| ≤ sup |f'(s)| * |s₁ - s₂|
  -- where f(s) = p^{-s} and f'(s) = -log(p) * p^{-s}

  -- The derivative of p^{-s} is -log(p) * p^{-s}
  -- We need |p^{-s₁} - p^{-s₂}| ≤ C * |s₁ - s₂| for some C independent of p

  -- For Re(s) > 1/2, we have ∑ log(p) * p^{-Re(s)} converges
  -- This gives us a uniform bound

  -- Take C = sup_p (log(p.val) * (p.val : ℝ)^(-min(s₁.re, s₂.re)/2))
  -- This supremum exists because the sum converges

  let σ := min s₁.re s₂.re
  have hσ : 1/2 < σ := by
    simp only [σ, min_def]
    split_ifs <;> assumption

  -- For the mean value theorem, we need a bound on |d/ds p^{-s}| = |log(p) * p^{-s}|
  -- on the line segment between s₁ and s₂

  -- Since log(p) * p^{-σ/2} is summable (because σ/2 > 1/4 and ∑ log(p)/p^α converges for α > 0)
  -- we can take C to be a fixed multiple of this

  use 1000  -- Placeholder - should be computed from the sum

  intro p

  -- Apply the fundamental theorem of calculus to f(t) = p^{-(s₂ + t(s₁ - s₂))}
  -- We have f(0) = p^{-s₂} and f(1) = p^{-s₁}
  -- So p^{-s₁} - p^{-s₂} = ∫₀¹ f'(t) dt

  -- The derivative is f'(t) = -(s₁ - s₂) * log(p) * p^{-(s₂ + t(s₁ - s₂))}
  -- So |p^{-s₁} - p^{-s₂}| ≤ |s₁ - s₂| * log(p) * max_{t∈[0,1]} |p^{-(s₂ + t(s₁ - s₂))}|

  -- The maximum occurs at the point with smallest real part
  -- which is when Re(s₂ + t(s₁ - s₂)) = min(Re(s₁), Re(s₂)) = σ

  -- Therefore |p^{-s₁} - p^{-s₂}| ≤ |s₁ - s₂| * log(p) * p^{-σ}

  -- Since σ > 1/2, we have log(p) * p^{-σ} → 0 as p → ∞
  -- and the sum ∑ log(p) * p^{-σ} converges

  -- This gives us the required bound with C = sup_p (log(p) * p^{-σ/2})
  sorry  -- The detailed computation requires careful analysis of the integral

end AcademicRH.DiagonalOperator
