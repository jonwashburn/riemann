import rh.academic_framework.DiagonalFredholm
import rh.academic_framework.Common
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.Asymptotics
import rh.academic_framework.EulerProduct.PrimeSeries

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

-- PrimeIndex is already defined in Core.lean

/-- The evolution operator A(s) with diagonal action p^{-s} -/
noncomputable def evolution_operator_diagonal (s : ℂ) :
  lp (fun _ : PrimeIndex => ℂ) 2 →L[ℂ] lp (fun _ : PrimeIndex => ℂ) 2 :=
  DiagonalOperator' (fun p => (p.val : ℂ)^(-s))

/-- The eigenvalues of the evolution operator -/
noncomputable def evolution_eigenvalues (s : ℂ) : PrimeIndex → ℂ :=
  fun p => (p.val : ℂ)^(-s)

/-- For Re(s) > 1, the eigenvalues are absolutely summable -/
theorem eigenvalues_summable_gt_one {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖) := by
  -- Use that ∑ 1/p^{Re(s)} converges for Re(s) > 1
  rw [show (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖) =
      (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) by
    ext p
    rfl]
  -- Use the existing result from PrimeSeries
  exact AcademicRH.EulerProduct.primeNormSummable hs

/-- For Re(s) > 1/2, the eigenvalues are square-summable -/
theorem eigenvalues_square_summable_gt_half {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖^2) := by
  -- We need to show ∑ |p^{-s}|² converges
  -- |p^{-s}|² = p^{-2Re(s)}
  -- Since 2Re(s) > 1, this is like showing ∑ 1/p^α converges for α > 1

  -- First convert the norm squared
  have h_eq : ∀ p : PrimeIndex, ‖evolution_eigenvalues s p‖^2 = (p.val : ℝ)^(-2 * s.re) := by
    intro p
    rw [evolution_eigenvalues]
    -- |p^{-s}|² = p^{-2Re(s)}
    -- Use the fact that for a positive real number a and complex number z, |a^z|² = a^(2*Re(z))
    have hp_pos : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
    -- For the squared norm, we use the fact that ‖z‖² = |z|²
    rw [norm_sq_eq_def]
    -- |p^{-s}| = p^{-Re(s)} for positive real p
    have h_abs : Complex.abs ((p.val : ℂ)^(-s)) = (p.val : ℝ)^(-s.re) := by
      rw [← ofReal_natCast]
      exact Complex.abs_cpow_eq_rpow_re_of_pos hp_pos (-s)
    rw [h_abs]
    -- So |p^{-s}|² = (p^{-Re(s)})² = p^{-2*Re(s)}
    -- Since (a^b)² = a^(2b) for positive a
    rw [Real.rpow_natCast]
    -- Now we have (p^{-Re(s)})² = p^{2*(-Re(s))} = p^{-2*Re(s)}
    have : (p.val : ℝ)^(-s.re) ^ 2 = (p.val : ℝ)^(-2 * s.re) := by
      rw [← Real.rpow_natCast]
      simp only [Real.rpow_two]
      rw [Real.rpow_mul (le_of_lt hp_pos)]
      simp only [Nat.cast_ofNat]
      ring
    exact this

  -- Now show this sum converges
  simp_rw [h_eq]

  -- Compare with the natural number sum ∑ 1/n^{2Re(s)}
  -- Since 2Re(s) > 1, this sum converges
  have h_conv : 1 < 2 * s.re := by linarith
  -- The sum over primes converges since it's bounded by the sum over naturals
  -- We can reuse primeNormSummable with 2*Re(s) > 1
  -- First create a complex number with real part 2*Re(s)
  let s' : ℂ := ⟨2 * s.re, 0⟩
  have hs' : 1 < s'.re := by simp [s', h_conv]
  -- Apply primeNormSummable to s'
  have h_summable : Summable (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s')‖) :=
    AcademicRH.EulerProduct.primeNormSummable hs'
  -- Now show this equals our desired sum
  convert h_summable
  ext p
  -- Show ‖(p.val : ℂ)^(-s')‖ = (p.val : ℝ)^(-2 * s.re)
  have hp_pos : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
  rw [Complex.norm_eq_abs, ← ofReal_natCast]
  rw [Complex.abs_cpow_eq_rpow_re_of_pos hp_pos]
  simp [s', neg_mul]

/-- The evolution operator is trace-class for Re(s) > 1 -/
-- We don't need an instance here, just the summability property
theorem evolution_trace_class {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p => ‖evolution_eigenvalues s p‖) := by
  exact eigenvalues_summable_gt_one hs

/-- The evolution operator is Hilbert-Schmidt for Re(s) > 1/2 -/
theorem evolution_hilbert_schmidt {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => ‖evolution_eigenvalues s p‖^2) := by
  exact eigenvalues_square_summable_gt_half hs

-- The trace of the evolution operator is not used in main proof

/-- The operator norm bound -/
theorem evolution_operator_norm_bound {s : ℂ} (hs : 0 < s.re) :
  ‖evolution_operator_diagonal s‖ ≤ 2^(-s.re) := by
  -- For diagonal operators, the operator norm is the supremum of |eigenvalues|
  -- Here the eigenvalues are p^{-s} for primes p
  -- We have |p^{-s}| = p^{-Re(s)}
  -- Since p ≥ 2 for all primes, p^{-Re(s)} ≤ 2^{-Re(s)} when Re(s) > 0
  -- The operator norm of a diagonal operator is the supremum of |eigenvalues|
  have h_bound : ∀ p : PrimeIndex, ‖evolution_eigenvalues s p‖ ≤ 2^(-s.re) := by
    intro p
    rw [evolution_eigenvalues]
    -- |p^{-s}| = p^{-Re(s)} ≤ 2^{-Re(s)} since p ≥ 2
    -- Use the fact that |z^w| = |z|^Re(w) for z ≠ 0
    have hp_ne_zero : (p.val : ℂ) ≠ 0 := by
      norm_cast
      exact Nat.Prime.ne_zero p.property
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
    simp only [neg_re]
    rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
    -- Since p ≥ 2, we have (p.val : ℝ)^s.re ≥ 2^s.re
    -- Therefore 1/(p.val : ℝ)^s.re ≤ 1/2^s.re = 2^(-s.re)
    have hp_ge_two : 2 ≤ (p.val : ℝ) := Nat.cast_le.mpr (Nat.Prime.two_le p.property)
    have h_rpow_le : 2^s.re ≤ (p.val : ℝ)^s.re := by
      exact Real.rpow_le_rpow_left (le_of_lt hs) hp_ge_two s.re
    exact inv_le_inv_of_le (Real.rpow_pos_of_pos (by norm_num) _) h_rpow_le

  -- Apply the diagonal operator norm characterization
  rw [evolution_operator_diagonal]
  -- For diagonal operators, the norm is the supremum of eigenvalues
  -- We need to show ‖DiagonalOperator' (fun p => (p.val : ℂ)^(-s))‖ ≤ 2^(-s.re)
  -- This follows from the fact that all eigenvalues are bounded by 2^(-s.re)
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  · intro ψ
    -- For diagonal operators, ‖Dψ‖ ≤ sup_p |eigenvalue_p| * ‖ψ‖
    -- Use the bound h_bound for each eigenvalue
    have h_eigenvalue_bound : ∀ p : PrimeIndex, ‖(p.val : ℂ)^(-s) * ψ p‖ ≤ 2^(-s.re) * ‖ψ p‖ := by
      intro p
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (h_bound p) (norm_nonneg _)
    -- For DiagonalOperator', the action is pointwise multiplication
    -- so ‖DiagonalOperator' μ ψ‖ = ‖⟨μ i * ψ i⟩‖
    -- By the definition of lp norm, this is (∑' i, |μ i * ψ i|²)^(1/2)
    -- ≤ (∑' i, (sup |μ i|)² * |ψ i|²)^(1/2) = sup |μ i| * ‖ψ‖
    calc ‖DiagonalOperator' (fun p => (p.val : ℂ)^(-s)) ψ‖
      = ‖(⟨fun p => (p.val : ℂ)^(-s) * ψ p, by
          -- We need to show this is in lp 2
          have h_mem : Memℓp (fun p => (p.val : ℂ)^(-s) * ψ p) 2 := by
            -- Since each eigenvalue is bounded and ψ ∈ lp 2, the product is in lp 2
            have h_bounded_eigenvals : ∃ C, ∀ p, ‖(p.val : ℂ)^(-s)‖ ≤ C := by
              use 2^(-s.re)
              exact h_bound
            exact Memℓp.const_mul h_bounded_eigenvals ψ.property
          exact h_mem⟩ : lp (fun _ => ℂ) 2)‖ := by
        rw [diagonal_operator_apply']
      _ ≤ 2^(-s.re) * ‖ψ‖ := by
        -- Use the bound for lp norms with pointwise multiplication
        apply lp.norm_le_of_forall_le h_eigenvalue_bound

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
    -- (p.val : ℂ) ≠ 0 because p is prime
    norm_cast
    exact Nat.Prime.pos p.property

/-- Holomorphy of eigenvalues in s -/
theorem eigenvalues_holomorphic (p : PrimeIndex) :
  AnalyticOn ℂ (fun s => evolution_eigenvalues s p) {s | 0 < s.re} := by
  -- Holomorphy of z ↦ p^{-z}
  unfold evolution_eigenvalues
  -- The function s ↦ (p.val : ℂ)^(-s) is entire (analytic everywhere)
  -- Since (p.val : ℂ) ≠ 0, the function z ↦ (p.val : ℂ)^z is entire
  -- So s ↦ (p.val : ℂ)^(-s) is also entire
  -- The function s ↦ (p.val : ℂ)^(-s) is entire (analytic everywhere)
  -- Since we're only asked for analyticity on {s | 0 < s.re}, we can use this subset
  intro s hs
  -- The function s ↦ (p.val : ℂ)^(-s) is entire (analytic everywhere)
  -- For a fixed nonzero complex number a, the function z ↦ a^z is entire
  -- This is because a^z = exp(z * log(a)) and both exp and log are well-defined
  -- Since (p.val : ℂ) ≠ 0, we can apply this result to (p.val : ℂ)^(-s)
  have hp_ne_zero : (p.val : ℂ) ≠ 0 := by
    norm_cast
    exact Nat.Prime.ne_zero p.property
  -- The function s ↦ (p.val : ℂ)^(-s) is the composition of:
  -- 1. s ↦ -s (which is entire)
  -- 2. z ↦ (p.val : ℂ)^z (which is entire for nonzero base)
  -- Therefore the composition is entire
  -- Since we only need analyticity on {s | 0 < s.re}, which is a subset of ℂ,
  -- we can use the fact that an entire function is analytic on any subset
  apply AnalyticOn.analyticAt
  -- For complex power functions with nonzero base, the function z ↦ a^z is entire
  -- This follows from the definition a^z = exp(z * log(a))
  -- Since exp is entire and log(a) is well-defined for a ≠ 0, the composition is entire
  have h_analytic : AnalyticOn ℂ (fun z => (p.val : ℂ)^z) Set.univ := by
    -- The function z ↦ a^z is entire for nonzero a
    -- This is a standard result: since a^z = exp(z * log(a)) and both exp and multiplication
    -- by the constant log(a) are entire, the composition is entire
    apply AnalyticOn.cpow_const
    exact hp_ne_zero
  -- Now apply this to our function s ↦ (p.val : ℂ)^(-s)
  -- This is the composition of the entire function z ↦ (p.val : ℂ)^z with s ↦ -s
  have h_neg_analytic : AnalyticOn ℂ (fun s => -s) Set.univ := by
    -- The function s ↦ -s is entire (it's linear)
    apply AnalyticOn.neg
    exact analyticOn_id
  -- The composition of entire functions is entire
  have h_comp : AnalyticOn ℂ (fun s => (p.val : ℂ)^(-s)) Set.univ := by
    apply AnalyticOn.comp h_analytic h_neg_analytic
    -- The image of the negation function is all of ℂ
    intro s _
    simp
  -- Since the function is entire, it's analytic at any point s
  exact h_comp.analyticAt (Set.mem_univ s)

/- Commented out: These lemmas are not used in the main proof
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

  -- For diagonal operators, ‖A - B‖ = sup_i |a_i - b_i|
  -- where a_i, b_i are the eigenvalues

  -- We need to show ‖evolution_operator_diagonal s - evolution_operator_diagonal s₀‖ < ε

  -- The difference of diagonal operators is diagonal with eigenvalues the differences
  have h_diff_diagonal : evolution_operator_diagonal s - evolution_operator_diagonal s₀ =
    DiagonalOperator (fun p => evolution_eigenvalues s p - evolution_eigenvalues s₀ p) _ := by
    -- This follows from linearity of DiagonalOperator construction

    -- Both operators are diagonal with eigenvalues p^{-s} and p^{-s₀}
    -- Their difference is diagonal with eigenvalues p^{-s} - p^{-s₀}

    -- First show the boundedness condition for the difference eigenvalues
    have h_bounded : ∃ C, ∀ p, ‖evolution_eigenvalues s p - evolution_eigenvalues s₀ p‖ ≤ C := by
      -- Use that both s and s₀ have Re > 1/2
      -- So both p^{-s} and p^{-s₀} are bounded by 2^{-1/2} < 1
      -- Therefore their difference is bounded by 2
      use 2
      intro p
      have h1 : ‖evolution_eigenvalues s p‖ ≤ 1 := by
        rw [evolution_eigenvalues, norm_cpow_of_ne_zero (by simp : (p.val : ℂ) ≠ 0), neg_re]
        rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
        apply inv_le_one
        have : 1 ≤ (p.val : ℝ)^s.re := by
          apply Real.one_le_rpow_of_pos_of_le_one_of_pos
          · exact Nat.cast_pos.mpr (Nat.Prime.pos p.property)
          · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.property)
          · linarith [hs_mem]
        exact this
      have h2 : ‖evolution_eigenvalues s₀ p‖ ≤ 1 := by
        rw [evolution_eigenvalues, norm_cpow_of_ne_zero (by simp : (p.val : ℂ) ≠ 0), neg_re]
        rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
        apply inv_le_one
        have : 1 ≤ (p.val : ℝ)^s₀.re := by
          apply Real.one_le_rpow_of_pos_of_le_one_of_pos
          · exact Nat.cast_pos.mpr (Nat.Prime.pos p.property)
          · exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt p.property)
          · linarith [hs₀]
        exact this
      calc ‖evolution_eigenvalues s p - evolution_eigenvalues s₀ p‖
          ≤ ‖evolution_eigenvalues s p‖ + ‖evolution_eigenvalues s₀ p‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add h1 h2
        _ = 2 := by norm_num

    -- Now use that DiagonalOperator is linear in the eigenvalues
    ext ψ
    simp [evolution_operator_diagonal, DiagonalOperator_apply]
    ext p
    simp [evolution_eigenvalues]
    ring

  -- For bounded diagonal operators, the operator norm equals the supremum of |eigenvalues|
  -- Since each |evolution_eigenvalues s p - evolution_eigenvalues s₀ p| < ε
  -- and there exists a uniform bound, the operator norm is at most ε

  -- Apply the operator norm bound for diagonal operators
  rw [dist_eq_norm]

  -- Use that for diagonal operators with bounded eigenvalues,
  -- the norm is the supremum of eigenvalue norms
  -- Since all eigenvalue differences are < ε, the norm is ≤ ε

  -- This completes the continuity proof
  rw [h_diff_diagonal]

  -- The norm of a diagonal operator is the supremum of eigenvalue norms
  -- Since we have a uniform bound of 2 on all eigenvalues (from h_bounded)
  -- and each difference is < ε (from h_eigen_cont)
  -- the operator norm is at most ε

  -- Use that for diagonal operators on l², if all eigenvalues satisfy |λ_i| < ε
  -- and are uniformly bounded, then ‖DiagonalOperator λ‖ ≤ ε

  have h_norm_bound : ‖DiagonalOperator (fun p => evolution_eigenvalues s p - evolution_eigenvalues s₀ p) _‖ < ε := by
    -- The operator norm of a diagonal operator is sup_i |eigenvalue_i|
    -- We know each |eigenvalue_i| < ε from h_eigen_cont
    -- This gives us the bound

    -- For a diagonal operator D with eigenvalues λ_i, we have ‖D‖ = sup_i |λ_i|
    -- Since each |λ_i| < ε and there's a uniform bound, we get ‖D‖ ≤ ε

    -- Apply the operator norm characterization
    rw [ContinuousLinearMap.norm_le_iff_norm_le_one]
    intro ψ

    -- Apply the diagonal operator
    rw [DiagonalOperator_apply]

    -- The norm squared of the result
    have h_norm_sq : ‖⟨fun i => (evolution_eigenvalues s i - evolution_eigenvalues s₀ i) * ψ i, _⟩‖^2 =
                     ∑' i, ‖(evolution_eigenvalues s i - evolution_eigenvalues s₀ i) * ψ i‖^2 := by
      rw [pow_two, ← lp.norm_sq_eq_inner_self]
      rw [lp.inner_def]
      simp [RCLike.inner_apply, conj_mul']
      congr 1
      ext i
      rw [norm_sq_eq_self]

    -- Bound each term using h_eigen_cont
    have h_term_bound : ∀ i, ‖(evolution_eigenvalues s i - evolution_eigenvalues s₀ i) * ψ i‖^2 < ε^2 * ‖ψ i‖^2 := by
      intro i
      rw [norm_mul, mul_pow]
      apply mul_lt_mul_of_nonneg_right
      · rw [sq_lt_sq' (by linarith : -ε < 0) (norm_nonneg _)]
        exact h_eigen_cont i
      · exact sq_nonneg _

    -- Since we have strict inequality for each term, and convergence,
    -- the sum is at most ε^2 * ‖ψ‖^2
    rw [h_norm_sq]

    -- We need to be careful here - we have strict inequality for each term
    -- but need to conclude something about the sum
    -- Since the sum converges, we can bound it

    have h_sum_le : ∑' i, ‖(evolution_eigenvalues s i - evolution_eigenvalues s₀ i) * ψ i‖^2 ≤ ε^2 * ‖ψ‖^2 := by
      -- Each term is < ε^2 * ‖ψ i‖^2
      -- So the sum is ≤ ε^2 * ∑' i, ‖ψ i‖^2 = ε^2 * ‖ψ‖^2
      have h_le : ∀ i, ‖(evolution_eigenvalues s i - evolution_eigenvalues s₀ i) * ψ i‖^2 ≤ ε^2 * ‖ψ i‖^2 := by
        intro i
        exact le_of_lt (h_term_bound i)

      have h_sum : ∑' i, ‖(evolution_eigenvalues s i - evolution_eigenvalues s₀ i) * ψ i‖^2 ≤
                   ∑' i, ε^2 * ‖ψ i‖^2 := by
        apply tsum_le_tsum h_le
        · -- Summability of LHS
          apply Summable.of_nonneg_of_le
          · intro i; exact sq_nonneg _
          · exact h_le
          · exact Summable.mul_left _ ψ.property
        · -- Summability of RHS
          exact Summable.mul_left _ ψ.property

      rw [← tsum_mul_left] at h_sum
      rw [← pow_two, ← lp.norm_sq_eq_inner_self] at h_sum
      rw [lp.inner_def] at h_sum
      simp [RCLike.inner_apply, conj_mul', norm_sq_eq_self] at h_sum
      exact h_sum

    -- Take square roots
    have h_sqrt : ‖⟨fun i => (evolution_eigenvalues s i - evolution_eigenvalues s₀ i) * ψ i, _⟩‖ ≤ ε * ‖ψ‖ := by
      rw [← Real.sqrt_le_sqrt_iff (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith : 0 ≤ ε),
          Real.sqrt_sq (norm_nonneg _)]
      exact h_sqrt

    -- So the operator norm is at most ε
    -- But we need strict inequality
    -- This follows from h_eigen_cont being strict and continuity

    -- Actually, let's be more careful. We have ‖D‖ ≤ ε
    -- To get strict inequality, use that the supremum of values all < ε is ≤ ε
    -- and if it equals ε, there would be a sequence approaching ε
    -- But all values are bounded away from ε

    -- Since all eigenvalue differences are < ε, and the operator is bounded
    -- The operator norm is the supremum of eigenvalue norms
    -- Since each eigenvalue difference has norm < ε, the supremum is ≤ ε
    -- For diagonal operators with finite rank approximation, strict inequality holds
    apply ContinuousLinearMap.opNorm_le_bound
    · linarith
    · intro ψ
      rw [h_diff_diagonal, DiagonalOperator_apply]
      have h_bound : ∀ i, ‖(evolution_eigenvalues s i - evolution_eigenvalues s₀ i) * ψ i‖ ≤ ε * ‖ψ i‖ := by
        intro i
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right
        · exact le_of_lt (h_eigen_cont i)
        · exact norm_nonneg _
      -- Use the lp norm bound for pointwise products
      apply lp.norm_le_of_forall_le h_bound

  exact h_norm_bound

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

  -- More explicitly, we use the mean value theorem for complex functions
  -- For the function f(s) = p^{-s}, we have f'(s) = -log(p) * p^{-s}

  -- By the mean value inequality for holomorphic functions:
  -- |f(s₁) - f(s₂)| ≤ |s₁ - s₂| * sup{|f'(s)| : s on line segment [s₁, s₂]}

  -- On the line segment, the real part varies between s₁.re and s₂.re
  -- So |p^{-s}| ≤ p^{-min(s₁.re, s₂.re)} = p^{-σ}

  -- Therefore |f'(s)| ≤ log(p) * p^{-σ} on the line segment

  -- This gives us |p^{-s₁} - p^{-s₂}| ≤ |s₁ - s₂| * log(p) * p^{-σ}

  -- Since σ > 1/2, we have ∑ log(p) * p^{-σ} < ∞
  -- So we can take C = some fixed constant that bounds log(p) * p^{-σ/2} for all p

  -- For the explicit bound, note that log(p) * p^{-σ/2} is decreasing for large p
  -- since d/dp[log(p) * p^{-α}] = p^{-α-1}[1 - α*log(p)] < 0 for p large enough

  -- So the maximum is achieved at p = 2, giving C ≈ log(2) * 2^{-1/4} < 1000

  -- Apply the mean value theorem
  rw [evolution_eigenvalues, evolution_eigenvalues]

  -- We need to show |p^{-s₁} - p^{-s₂}| ≤ 1000 * |s₁ - s₂|

  -- Using the fundamental theorem of calculus for complex functions:
  -- f(s₁) - f(s₂) = ∫[s₂,s₁] f'(t) dt
  -- where f(s) = p^{-s} and f'(s) = -log(p) * p^{-s}

  -- The integral is over the line segment from s₂ to s₁
  -- |∫[s₂,s₁] f'(t) dt| ≤ |s₁ - s₂| * max{|f'(t)| : t on segment}

  -- We've shown |f'(t)| ≤ log(p) * p^{-σ} where σ = min(Re(s₁), Re(s₂))
  -- And log(p) * p^{-σ/2} is bounded by a constant since σ > 1/2

  -- The precise bound depends on the smallest prime p = 2:
  -- log(2) * 2^{-1/4} ≈ 0.693 * 0.841 ≈ 0.583 < 1000

  -- For all primes p ≥ 2, the function log(p) * p^{-σ/2} is decreasing
  -- when σ > 1/2, so the maximum is at p = 2

  -- Apply the complex mean value theorem for holomorphic functions
  -- For f(s) = p^(-s), we have f'(s) = -log(p) * p^(-s)
  -- By the mean value inequality: |f(s₁) - f(s₂)| ≤ |s₁ - s₂| * sup{|f'(s)| : s ∈ [s₁,s₂]}
  -- On the line segment, Re(s) varies between s₁.re and s₂.re
  -- So |p^(-s)| = p^(-Re(s)) ≤ p^(-σ) where σ = min(s₁.re, s₂.re)
  -- Therefore |f'(s)| = log(p) * |p^(-s)| ≤ log(p) * p^(-σ)
  -- This gives |p^(-s₁) - p^(-s₂)| ≤ |s₁ - s₂| * log(p) * p^(-σ)
  -- Since σ > 1/2, we have log(p) * p^(-σ/2) bounded, so we can take C = 1000
  have hp_pos : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
  have h_derivative_bound : log (p.val : ℝ) * (p.val : ℝ)^(-σ) ≤ 1000 := by
    -- For p ≥ 2 and σ > 1/2, this is bounded
    -- The function log(x) * x^(-σ) is decreasing for large x when σ > 1/2
    -- So the maximum occurs at x = 2
    have h_two_bound : log 2 * 2^(-1/2) ≤ 1000 := by norm_num
    -- Since p ≥ 2 and log(x) * x^(-σ) is eventually decreasing for σ > 1/2
    cases' Nat.Prime.eq_two_or_odd p.property with h_two h_odd
    · rw [h_two]
      norm_cast
      exact h_two_bound
    · -- For p > 2, use that log(x) * x^(-σ) is decreasing for large x
      have h_decreasing : log (p.val : ℝ) * (p.val : ℝ)^(-σ) ≤ log 2 * 2^(-σ) := by
        -- This follows from the fact that d/dx[log(x) * x^(-α)] < 0 for large x, α > 0
        -- Specifically, d/dx[log(x) * x^(-α)] = x^(-α-1) * (1 - α*log(x))
        -- For α > 0 and x > e^(1/α), this derivative is negative
        -- Since σ > 1/2 and p ≥ 3 > e^(1/σ), the function is decreasing
        have h_gt_two : 2 < (p.val : ℝ) := by
          have h_odd_ge_three : 3 ≤ p.val := Nat.Prime.odd_iff_ne_two.mp h_odd
          exact Nat.cast_lt.mpr (Nat.lt_of_succ_le h_odd_ge_three)
        -- Use monotonicity of log(x) * x^(-σ) for x ≥ 2 when σ > 1/2
        apply log_mul_rpow_decreasing_of_ge_two
        · exact h_gt_two
        · exact hσ
      calc log (p.val : ℝ) * (p.val : ℝ)^(-σ)
        ≤ log 2 * 2^(-σ) := h_decreasing
        _ ≤ log 2 * 2^(-1/2) := by
          apply mul_le_mul_of_nonneg_left
          · apply Real.rpow_le_rpow_of_exponent_le
            · norm_num
            · exact neg_le_neg (le_of_lt hσ)
          · exact Real.log_nonneg (by norm_num : 1 ≤ 2)
        _ ≤ 1000 := h_two_bound
  -- Now apply the bound
  calc ‖evolution_eigenvalues s₁ p - evolution_eigenvalues s₂ p‖
    = ‖(p.val : ℂ)^(-s₁) - (p.val : ℂ)^(-s₂)‖ := by rfl
    _ ≤ ‖s₁ - s₂‖ * (log (p.val : ℝ) * (p.val : ℝ)^(-σ)) := by
      -- Apply mean value theorem for complex analytic functions
      exact complex_mvt_bound hp_pos
    _ ≤ ‖s₁ - s₂‖ * 1000 := by
      apply mul_le_mul_of_nonneg_left h_derivative_bound (norm_nonneg _)
    _ = 1000 * ‖s₁ - s₂‖ := mul_comm _ _
-/

/-- Norm bound theorem: If all eigenvalues have norm ≤ 1, then the operator norm ≤ 1 -/
theorem norm_le_one_of_norm_eigenvalue_bound {I : Type*} [DecidableEq I] [Countable I]
  (μ : I → ℂ) (h : ∀ i, ‖μ i‖ ≤ 1) :
  ‖DiagonalOperator' μ‖ ≤ 1 := by
  -- For diagonal operators, the norm is the supremum of eigenvalue norms
  -- If all eigenvalues have norm ≤ 1, then the supremum is ≤ 1

  -- First, establish the norm formula
  have h_norm : ‖DiagonalOperator' μ‖ = ⨆ i, ‖μ i‖ := by
    -- This requires that the eigenvalues are bounded
    have h_bdd : BddAbove (Set.range fun i ↦ ‖μ i‖) := by
      use 1
      intro x hx
      obtain ⟨i, hi⟩ := hx
      rw [←hi]
      exact h i
    exact diagonal_operator_norm' μ h_bdd

  rw [h_norm]

  -- Now show that the supremum of eigenvalue norms is ≤ 1
  apply iSup_le
  exact h

/-- Norm squared equality for diagonal operators -/
theorem norm_squared_equality {I : Type*} [DecidableEq I] [Countable I]
  (μ : I → ℂ) (h : Summable fun i ↦ ‖μ i‖^2) :
  ‖DiagonalOperator' μ‖^2 = ⨆ i, ‖μ i‖^2 := by
  -- For diagonal operators, the norm squared equals the supremum of eigenvalue norms squared

  -- First, get the norm formula
  have h_norm : ‖DiagonalOperator' μ‖ = ⨆ i, ‖μ i‖ := by
    -- This requires that the eigenvalues are bounded
    have h_bdd : BddAbove (Set.range fun i ↦ ‖μ i‖) := by
      -- Since the squared norms are summable, the norms must be bounded
      -- Use the fact that if ∑ ‖μ i‖² < ∞, then ∀ i, ‖μ i‖² ≤ M for some M
      have h_eventually : ∀ᶠ i in cofinite, ‖μ i‖^2 ≤ 1 := by
        apply Summable.tendsto_cofinite_zero h
        simp only [Function.comp_apply]
        apply eventually_of_forall
        intro i
        exact sq_nonneg _
      -- Extract a bound from the summability
      obtain ⟨M, hM⟩ := h.bddAbove_range_partial_sum
      use Real.sqrt M
      intro x hx
      obtain ⟨i, hi⟩ := hx
      rw [←hi]
      -- Use the fact that ‖μ i‖² appears in the sum
      have h_le_sum : ‖μ i‖^2 ≤ ∑' j, ‖μ j‖^2 := by
        apply le_tsum_of_ne_zero
        · exact h
        · simp only [sq_nonneg]
        · simp only [pow_pos_iff, norm_pos_iff, ne_eq]
          intro h_zero
          simp [h_zero]
      -- Therefore ‖μ i‖ ≤ √(∑' j, ‖μ j‖²)
      exact Real.sqrt_le_sqrt_iff.mp (by simp only [Real.sq_sqrt (norm_nonneg _)]; exact h_le_sum)
    exact diagonal_operator_norm' μ h_bdd

  -- Now square both sides
  rw [h_norm]

  -- Use the fact that (⨆ i, ‖μ i‖)² = ⨆ i, ‖μ i‖²
  -- This follows from the continuity of the square function
  conv_lhs => rw [← Real.sq_sqrt (iSup_nonneg _)]
  simp only [Real.sq_sqrt]

  -- Show that ⨆ i, ‖μ i‖² = (⨆ i, ‖μ i‖)²
  have h_sq_sup : (⨆ i, ‖μ i‖)^2 = ⨆ i, ‖μ i‖^2 := by
    -- This is a standard result about suprema and monotonic functions
    have h_mono : Monotone (fun x : ℝ => x^2) := by
      intro x y h
      exact sq_le_sq' (neg_le_neg h) h
    -- For non-negative functions, sup(f²) = (sup f)²
    have h_nonneg : ∀ i, 0 ≤ ‖μ i‖ := fun i => norm_nonneg _
    -- Use the fact that x ↦ x² is monotone on [0, ∞)
    rw [← iSup_comp_le_iff_le_iSup]
    exact le_refl _

  exact h_sq_sup.symm

end AcademicRH.DiagonalOperator
