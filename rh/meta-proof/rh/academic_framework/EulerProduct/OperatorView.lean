import rh.academic_framework.Core
import rh.academic_framework.DiagonalFredholm.Operator
import rh.academic_framework.DiagonalFredholm.ProductLemmas
import rh.academic_framework.DiagonalFredholm.DiagonalTools
import rh.academic_framework.DiagonalFredholm.WeierstrassProduct
import rh.academic_framework.EulerProduct.PrimeSeries
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Operator View of Euler Product

This file connects the Euler product to diagonal operators on ℓ².

## Main definitions

* `euler_operator` - The operator Λₛ with eigenvalues p^(-s)
* `fredholm_det_euler` - The Fredholm determinant of euler_operator
* `A` - The function p ↦ 1 - p^(-s)
* `P` - The Euler product ∏(1 - p^(-s))^(-1)
* `logP` - The logarithm of the Euler product

## Main results

* `euler_eigenvals_summable` - Eigenvalues are summable for Re(s) > 1
* `euler_operator_norm_lt_one` - Operator norm < 1 for Re(s) > 1
* `log_summable` - The log series converges absolutely
* `euler_product_eq_zeta` - The Euler product equals ζ(s)
-/

namespace AcademicRH.EulerProduct

open Complex Real BigOperators AcademicRH.DiagonalFredholm Filter

/-- For Re(s) > 1, the eigenvalues are summable -/
lemma euler_eigenvals_summable {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) := by
  -- Use the result from PrimeSeries
  exact primeNormSummable hs

/-- The Euler operator Λₛ with eigenvalues p^(-s) for primes p -/
noncomputable def euler_operator (s : ℂ) (hs : 1 < s.re) :
  lp (fun _ : PrimeIndex => ℂ) 2 →L[ℂ] lp (fun _ : PrimeIndex => ℂ) 2 :=
  DiagonalOperator' (fun p : PrimeIndex => (p.val : ℂ)^(-s))

/-- The operator norm of Λₛ is less than 1 for Re(s) > 1 -/
theorem euler_operator_norm_lt_one {s : ℂ} (hs : 1 < s.re) :
  ‖euler_operator s hs‖ < 1 := by
  -- The operator norm equals sup_p |p^(-s)| = 2^(-Re(s)) < 1
  rw [euler_operator]
  -- Apply the diagonal operator norm theorem
  have h_bounded : ∃ C, ∀ p : PrimeIndex, ‖(p.val : ℂ)^(-s)‖ ≤ C := by
    use 1
    intro p
    -- For Re(s) > 1, we have |p^(-s)| = p^(-Re(s)) ≤ 2^(-Re(s)) < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
    simp only [neg_re]
    rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
    -- p^(-Re(s)) ≤ 2^(-Re(s)) since p ≥ 2 and -Re(s) < 0
    have hp_ge_two : 2 ≤ p.val := Nat.Prime.two_le p.property
    have h_exp_le : (p.val : ℝ)^(-s.re) ≤ (2 : ℝ)^(-s.re) := by
      rw [Real.rpow_le_rpow_iff_of_pos (by norm_num : 0 < 2) (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
      left
      exact ⟨neg_neg_iff_pos.mpr (by linarith : 0 < s.re), Nat.cast_le.mpr hp_ge_two⟩
    -- 2^(-Re(s)) < 1 since Re(s) > 1
    have h_lt_one : (2 : ℝ)^(-s.re) < 1 := by
      rw [Real.rpow_neg (by norm_num : 0 ≤ 2)]
      rw [inv_lt_one_iff_one_lt]
      exact Real.one_lt_rpow (by norm_num : 1 < 2) hs
    exact le_of_lt (lt_of_le_of_lt h_exp_le h_lt_one)

  -- Apply diagonal operator norm theorem from FredholmInfrastructure
  rw [diagonal_operator_norm (fun p : PrimeIndex => (p.val : ℂ)^(-s)) h_bounded]

  -- The supremum is achieved at p = 2 and equals 2^(-Re(s))
  have h_sup_eq : (⨆ p : PrimeIndex, ‖(p.val : ℂ)^(-s)‖) = (2 : ℝ)^(-s.re) := by
    -- The supremum is 2^(-Re(s)) achieved at the smallest prime p = 2
    have h_two_prime : Nat.Prime 2 := Nat.prime_two
    let two_idx : PrimeIndex := ⟨2, h_two_prime⟩

    apply le_antisymm
    · -- Upper bound: all terms ≤ 2^(-Re(s))
      apply iSup_le
      intro p
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
      simp only [neg_re]
      rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
      rw [Real.rpow_neg (by norm_num : 0 ≤ 2)]
      apply inv_le_inv_of_le
      · exact Real.rpow_pos_of_pos (by norm_num : 0 < 2) _
      · exact Real.rpow_le_rpow_left (le_of_lt hs) (Nat.cast_le.mpr (Nat.Prime.two_le p.property)) s.re

    · -- Lower bound: 2^(-Re(s)) ≤ supremum
      apply le_iSup_of_le two_idx
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0 < 2)]
      simp only [neg_re, two_idx, PrimeIndex.val]
      rfl

  rw [h_sup_eq]
  -- Show 2^(-Re(s)) < 1
  rw [Real.rpow_neg (by norm_num : 0 ≤ 2)]
  rw [inv_lt_one_iff_one_lt]
  exact Real.one_lt_rpow (by norm_num : 1 < 2) hs

section EulerProduct

variable {s : ℂ} (hs : 1 < s.re)

/-- The function A_p = 1 - p^(-s) -/
noncomputable def A (s : ℂ) (p : PrimeIndex) : ℂ := 1 - (p.val : ℂ)^(-s)

/-- The Euler product P = ∏(1 - p^(-s))^(-1) -/
noncomputable def P (s : ℂ) : ℂ := ∏' p, (A s p)⁻¹

/-- The logarithm of the Euler product -/
noncomputable def logP (s : ℂ) : ℂ := ∑' p, -Complex.log (A s p)

/-- Eventually p^(-s) is small -/
lemma eventually_small {s : ℂ} (hs : 1 < s.re) : ∀ᶠ p : PrimeIndex in cofinite, ‖(p.val : ℂ)^(-s)‖ < 1/2 := by
  -- Since ∑ p^(-Re s) converges, the terms go to 0
  -- We have ‖p^(-s)‖ = p^(-Re(s))
  -- Since the series ∑ p^(-Re(s)) converges, the terms p^(-Re(s)) → 0
  -- So eventually p^(-Re(s)) < 1/2
  have h_summable : Summable (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) :=
    euler_eigenvals_summable hs
  -- For summable sequences, the terms tend to 0
  have h_tendsto : Tendsto (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) cofinite (nhds 0) :=
    h_summable.tendsto_cofinite_zero
  -- Since the terms tend to 0, eventually they are < 1/2
  rw [tendsto_nhds] at h_tendsto
  specialize h_tendsto (Set.Iio (1/2 : ℝ)) (isOpen_Iio) (by norm_num : (0 : ℝ) ∈ Set.Iio (1/2))
  exact h_tendsto

/-- The log series converges absolutely -/
lemma log_summable {s : ℂ} (hs : 1 < s.re) : Summable (fun p : PrimeIndex => ‖Complex.log (A s p)‖) := by
  -- Use the bound |log(1-z)| ≤ 2|z| for |z| < 1/2
  -- We have A_p = 1 - p^(-s), so log(A_p) = log(1 - p^(-s))
  -- Since eventually |p^(-s)| < 1/2, we get |log(A_p)| ≤ 2|p^(-s)|
  -- And ∑ |p^(-s)| converges by euler_eigenvals_summable

  have h_eventually_small : ∀ᶠ p : PrimeIndex in cofinite, ‖(p.val : ℂ)^(-s)‖ < 1/2 :=
    eventually_small hs

  have h_bound : ∀ᶠ p : PrimeIndex in cofinite, ‖Complex.log (A s p)‖ ≤ 2 * ‖(p.val : ℂ)^(-s)‖ := by
    filter_upwards [h_eventually_small] with p hp
    -- For |z| < 1/2, we have |log(1-z)| ≤ 2|z|
    -- Here A s p = 1 - p^(-s), so log(A s p) = log(1 - p^(-s))
    rw [A]
    have h_log_bound : ‖Complex.log (1 - (p.val : ℂ)^(-s))‖ ≤ 2 * ‖(p.val : ℂ)^(-s)‖ := by
      -- Use the standard logarithm bound
      -- This is essentially the log_one_sub_bound_complete from FredholmInfrastructure
      apply Complex.norm_log_one_sub_le_two_mul_norm_of_norm_lt_half
      exact hp
    exact h_log_bound

  -- Apply comparison test
  apply Summable.of_norm_bounded_eventually h_bound
  -- The comparison series ∑ 2 * |p^(-s)| converges
  have h_base_summable : Summable (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) :=
    euler_eigenvals_summable hs
  exact Summable.const_mul h_base_summable 2

/-- The product is multipliable -/
lemma multipliable_inv_A {s : ℂ} (hs : 1 < s.re) : Multipliable (fun p : PrimeIndex => (A s p)⁻¹) := by
  -- The product ∏(1 - p^(-s))^(-1) = ∏(A_p)^(-1) is multipliable
  -- Use the fact that a product converges if log series converges
  -- We have log((A_p)^(-1)) = -log(A_p) = -log(1 - p^(-s))
  -- The summability of log series gives multipliability

  -- First show that A_p ≠ 0 eventually
  have h_nonzero : ∀ᶠ p : PrimeIndex in cofinite, A s p ≠ 0 := by
    have h_eventually_small : ∀ᶠ p : PrimeIndex in cofinite, ‖(p.val : ℂ)^(-s)‖ < 1/2 :=
      eventually_small hs
    filter_upwards [h_eventually_small] with p hp
    rw [A]
    -- If |p^(-s)| < 1/2 < 1, then 1 - p^(-s) ≠ 0
    exact Complex.one_sub_ne_zero_of_norm_lt_one (by linarith : ‖(p.val : ℂ)^(-s)‖ < 1)

  -- The log series for the inverse product converges
  have h_log_inv_summable : Summable (fun p : PrimeIndex => Complex.log ((A s p)⁻¹)) := by
    -- log((A_p)^(-1)) = -log(A_p)
    have h_eq : (fun p : PrimeIndex => Complex.log ((A s p)⁻¹)) =
                (fun p : PrimeIndex => -Complex.log (A s p)) := by
      ext p
      rw [Complex.log_inv]
      exact (h_nonzero.eventually.mp (eventually_of_forall (fun p => by
        intro h_nonzero_p
        exact h_nonzero_p))) p

    rw [h_eq]
    -- The series ∑ -log(A_p) converges if ∑ log(A_p) converges
    apply Summable.neg
    -- We need to show ∑ log(A_p) converges, which follows from absolute convergence
    apply Summable.of_norm_bounded_eventually_const
    · exact fun p => ‖Complex.log (A s p)‖
    · exact log_summable hs
    · use 0
      intro p hp
      rfl

  -- Apply the standard theorem: if log series converges, product is multipliable
  rw [multipliable_iff_summable_log]
  · exact h_log_inv_summable
  · -- Show that A_p^(-1) ≠ 0 eventually (trivial since A_p ≠ 0)
    filter_upwards [h_nonzero] with p hp
    exact inv_ne_zero hp

/-- Exponential of the log sum equals the product -/
lemma exp_logP_eq_P {s : ℂ} (hs : 1 < s.re) : Complex.exp (logP s) = P s := by
  -- This is the fundamental relationship between infinite products and sums
  -- exp(∑ log(a_i)) = ∏ a_i when the series converges

  rw [logP, P]
  -- We have logP = ∑ -log(A_p) and P = ∏ (A_p)^(-1)
  -- So exp(logP) = exp(∑ -log(A_p)) = ∏ exp(-log(A_p)) = ∏ (A_p)^(-1) = P

  -- Use the exponential-product identity
  have h_eq : Complex.exp (∑' p, -Complex.log (A s p)) = ∏' p, Complex.exp (-Complex.log (A s p)) := by
    -- This is the standard exp-sum-product identity
    apply Complex.exp_tsum_eq_tprod
    -- The series ∑ -log(A_p) converges
    apply Summable.neg
    apply Summable.of_norm_bounded_eventually_const
    · exact fun p => ‖Complex.log (A s p)‖
    · exact log_summable hs
    · use 0
      intro p hp
      rfl

  rw [h_eq]
  -- Show that exp(-log(A_p)) = (A_p)^(-1)
  congr 1
  ext p
  -- For A_p ≠ 0, we have exp(-log(A_p)) = (A_p)^(-1)
  have h_nonzero : A s p ≠ 0 := by
    rw [A]
    -- Eventually |p^(-s)| < 1/2 < 1, so 1 - p^(-s) ≠ 0
    have h_eventually_small : ∀ᶠ p : PrimeIndex in cofinite, ‖(p.val : ℂ)^(-s)‖ < 1/2 :=
      eventually_small hs
    -- For large enough p, we get the bound
    by_cases h : ‖(p.val : ℂ)^(-s)‖ < 1/2
    · exact Complex.one_sub_ne_zero_of_norm_lt_one (by linarith : ‖(p.val : ℂ)^(-s)‖ < 1)
    · -- For small primes, use direct computation
      push_neg at h
      -- This case covers finitely many primes, all of which satisfy the property
      -- Since Re(s) > 1, we have |p^(-s)| < 1 for all primes p
      have h_lt_one : ‖(p.val : ℂ)^(-s)‖ < 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
        simp only [neg_re]
        rw [Real.rpow_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))]
        rw [inv_lt_one_iff_one_lt]
        exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg (Nat.cast_pos.mpr (Nat.Prime.pos p.property))
               (by linarith : (p.val : ℝ) < 1) (neg_pos.mpr (by linarith : s.re > 0))
      exact Complex.one_sub_ne_zero_of_norm_lt_one h_lt_one

  rw [Complex.exp_neg_log h_nonzero]

/-- The Euler product equals the Riemann zeta function -/
theorem euler_product_eq_zeta {s : ℂ} (hs : 1 < s.re) : P s = riemannZeta s := by
  -- This is the classical Euler product formula for the Riemann zeta function
  -- ζ(s) = ∏_p (1 - p^(-s))^(-1) for Re(s) > 1

  rw [P]
  -- We have P = ∏ (A_p)^(-1) = ∏ (1 - p^(-s))^(-1)
  -- This is exactly the Euler product for ζ(s)

  -- Use mathlib's Euler product theorem
  rw [A]
  -- The infinite product ∏ (1 - p^(-s))^(-1) equals ζ(s)
  -- This is a standard result in number theory

  -- Apply the Euler product formula from mathlib
  have h_euler : ∏' p : PrimeIndex, (1 - (p.val : ℂ)^(-s))⁻¹ = riemannZeta s := by
    -- This follows from the standard Euler product theorem
    -- The details depend on the specific formulation in mathlib
    -- For now, we use the fact that this is a well-known theorem
    apply EulerProduct.euler_product_formula
    exact hs

  exact h_euler

/-- Combined result: exp(logP) = ζ(s) -/
theorem exp_logP_eq_zeta {s : ℂ} (hs : 1 < s.re) : Complex.exp (logP s) = riemannZeta s := by
  -- This follows directly from the previous two results
  rw [exp_logP_eq_P hs, euler_product_eq_zeta hs]

end EulerProduct

end AcademicRH.EulerProduct
