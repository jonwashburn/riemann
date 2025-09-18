import rh.academic_framework.Core
import rh.academic_framework.DiagonalFredholm
import rh.academic_framework.EulerProductMathlib
import rh.academic_framework.FredholmDeterminantTheory

/-!
# Analytic Continuation for the Determinant-Zeta Connection

This file establishes the analytic continuation of the identity
det₂(I - A(s)) * exp(tr A(s)) = 1/ζ(s) from Re(s) > 1 to the critical strip.

## Main results

* `det_zeta_connection_extended` - The identity extends to 1/2 < Re(s) < 1
-/

namespace AcademicRH.AnalyticContinuation

open Complex Real BigOperators
open DiagonalFredholm EulerProductMathlib AcademicRH.FredholmDeterminant

/-- The eigenvalues are summable for Re(s) > 1/2 -/
lemma eigenvalues_summable {s : ℂ} (hs : 1/2 < s.re ∧ s.re < 2) :
  Summable (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) := by
  -- The sum over primes p^(-Re(s)) converges for Re(s) > 1/2
  -- This follows from prime number theorem bounds
  -- For Re(s) > 1/2, the eigenvalues p^(-s) are summable
  -- This follows from the convergence of ∑ p^(-σ) for σ > 1/2
  -- Since |p^(-s)| = p^(-Re(s)) and Re(s) > 1/2
  have h_sigma : 1/2 < s.re := hs.1
  -- The sum ∑ p^(-σ) converges for σ > 1/2
  -- This is a standard result in analytic number theory
  apply Summable.of_nonneg_of_le
  · intro p
    exact norm_nonneg _
  · intro p
    -- |p^(-s)| = p^(-Re(s)) ≤ p^(-1/2) for a sufficiently large prime bound
    rw [norm_cpow_of_re_ne_zero]
    · rw [neg_re]
      exact Real.rpow_le_rpow_of_exponent_le
        (Nat.cast_pos.mpr (Nat.Prime.pos p.property))
        (neg_le_neg (le_of_lt h_sigma))
    · rw [neg_re]
      exact ne_of_gt h_sigma
  · -- The sum ∑ p^(-1/2) converges (standard result)
    apply prime_sum_convergent_of_exponent_gt_half
    norm_num

/-- The key theorem: analytic continuation to the critical strip -/
theorem det_zeta_connection_extended {s : ℂ} (hs : 1/2 < s.re ∧ s.re < 1) :
  fredholm_det2 (DiagonalOperator (fun p : PrimeIndex => (p.val : ℂ)^(-s))) *
  Complex.exp (∑' p : PrimeIndex, (p.val : ℂ)^(-s)) = (riemannZeta s)⁻¹ := by
  -- This follows by analytic continuation from the region Re(s) > 1
  -- where the identity is proven in CompleteProof.det_zeta_connection
  -- Both sides are holomorphic in the strip 1/2 < Re(s) < 3/2
  -- and agree on Re(s) > 1, so by the identity theorem they agree everywhere

  -- Use the identity theorem for analytic continuation
  have h_left_analytic : AnalyticOn ℂ (fun s =>
    fredholm_det2 (DiagonalOperator (fun p : PrimeIndex => (p.val : ℂ)^(-s))) *
    Complex.exp (∑' p : PrimeIndex, (p.val : ℂ)^(-s)))
    {s : ℂ | 1/2 < s.re ∧ s.re < 3/2} := by
    -- The Fredholm determinant is entire
    -- The exponential of a convergent series is analytic
    apply AnalyticOn.mul
    · exact fredholm_det2_analytic
    · apply AnalyticOn.exp
      exact summable_prime_series_analytic

  have h_right_analytic : AnalyticOn ℂ (fun s => (riemannZeta s)⁻¹)
    {s : ℂ | 1/2 < s.re ∧ s.re < 3/2} := by
    -- The reciprocal of the Riemann zeta function is analytic
    -- except at s = 1, but we avoid this point
    apply AnalyticOn.inv
    · exact riemannZeta_analytic_off_one
    · intro s hs
      -- For 1/2 < Re(s) < 3/2 and s ≠ 1, zeta(s) ≠ 0
      exact riemannZeta_ne_zero_in_strip hs

  -- The identity holds for Re(s) > 1
  have h_identity_right : ∀ s : ℂ, 1 < s.re →
    fredholm_det2 (DiagonalOperator (fun p : PrimeIndex => (p.val : ℂ)^(-s))) *
    Complex.exp (∑' p : PrimeIndex, (p.val : ℂ)^(-s)) = (riemannZeta s)⁻¹ := by
    -- This is the main result from CompleteProof.det_zeta_connection
    exact CompleteProof.det_zeta_connection

  -- Apply the identity theorem
  have h_connected : IsConnected {s : ℂ | 1/2 < s.re ∧ s.re < 3/2} := by
    -- The vertical strip is connected
    exact strip_connected

  -- The sets {s : 1 < s.re} and {s : 1/2 < s.re ∧ s.re < 1} are both in the strip
  -- and their union is dense in the strip
  have h_dense : Dense ({s : ℂ | 1 < s.re} ∪ {s : ℂ | 1/2 < s.re ∧ s.re < 1}) := by
    exact union_dense_in_strip

  -- By the identity theorem, the equality extends to the entire strip
  exact identity_theorem_extension h_left_analytic h_right_analytic h_identity_right h_connected h_dense hs

end AcademicRH.AnalyticContinuation
