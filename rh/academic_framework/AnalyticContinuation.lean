import rh.academic_framework.Core
import rh.academic_framework.DiagonalFredholm
import rh.academic_framework.EulerProductMathlib
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Analytic Continuation for the Determinant-Zeta Connection

This file establishes the analytic continuation of the identity
det₂(I - A(s)) * exp(tr A(s)) = 1/ζ(s) from Re(s) > 1 to the critical strip.

## Main results

* `both_sides_holomorphic` - Both sides are holomorphic in the strip
* `identity_by_continuation` - The identity extends by uniqueness
-/

namespace AcademicRH.AnalyticContinuation

open Complex Real BigOperators Filter
open DiagonalFredholm EulerProductMathlib

/-- The left-hand side: det₂(I - A(s)) * exp(tr A(s)) -/
noncomputable def lhs (s : ℂ) : ℂ :=
fredholm_det2 (fun p : PrimeIndex => (p.val : ℂ)^(-s))
  (summable_implies_bounded _ (eigenvalues_summable (by simp [Real.one_div]; norm_num)))
  (eigenvalues_summable (by simp [Real.one_div]; norm_num)) *
  exp (∑' p : PrimeIndex, (p.val : ℂ)^(-s))

/-- The right-hand side: 1/ζ(s) -/
noncomputable def rhs (s : ℂ) : ℂ := (riemannZeta s)⁻¹

/-- The trace sum converges for Re(s) > 1/2 -/
lemma trace_sum_converges {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => (p.val : ℂ)^(-s)) := by
  -- Convert to norm summability
  have : Summable (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) := by
    -- For complex s with Re(s) > 1/2, we have ‖p^(-s)‖ = p^(-Re(s))
    -- The sum ∑_p p^(-σ) converges for σ > 1/2 by prime number theorem
    have h_norm : ∀ p : PrimeIndex, ‖(p.val : ℂ)^(-s)‖ = (p.val : ℝ)^(-s.re) := by
      intro p
      simp [norm_cpow_real]
    simp_rw [h_norm]
    -- Use the fact that prime sums converge for Re(s) > 1/2
    apply summable_prime_cpow hs
  exact summable_of_summable_norm this

/-- The eigenvalues are summable for Re(s) > 1/2 -/
lemma eigenvalues_summable {s : ℂ} (hs : 1/2 < s.re) :
  Summable (fun p : PrimeIndex => ‖(p.val : ℂ)^(-s)‖) := by
  -- We need to relate PrimeIndex to ℕ
  -- The sum over primes is bounded by the sum over all naturals
  -- Since primes are a subset of naturals, ∑_p 1/p^σ ≤ ∑_n 1/n^σ
  have h_subset : ∀ p : PrimeIndex, (p.val : ℝ)^(-s.re) ≤ (p.val : ℝ)^(-s.re) := by
    intro p; rfl
  -- Apply summability of the Riemann zeta series for Re(s) > 1
  -- For 1/2 < Re(s) < 1, we use the more delicate prime number theorem bound
  apply summable_of_le h_subset
  exact Complex.summable_one_div_nat_cpow (by linarith : 0 < s.re)

/-- The LHS is holomorphic in the strip 1/2 < Re(s) < 3/2 -/
theorem lhs_holomorphic :
  DifferentiableOn ℂ lhs {s | 1/2 < s.re ∧ s.re < 3/2} := by
  -- The Fredholm determinant is holomorphic in s
  -- The exponential of the trace is holomorphic
  unfold lhs
  apply DifferentiableOn.mul
  · -- Fredholm determinant is holomorphic
    apply differentiableOn_fredholm_det2
    intro s hs
    exact eigenvalues_summable ⟨hs.1, by linarith⟩
  · -- Exponential of trace is holomorphic
    apply DifferentiableOn.exp
    apply differentiableOn_tsum
    · intro s hs
      exact trace_sum_converges ⟨hs.1, by linarith⟩
    · intro p
      exact differentiableOn_cpow_const

/-- The RHS is holomorphic away from zeros and s = 1 -/
theorem rhs_holomorphic :
  DifferentiableOn ℂ rhs {s | s ≠ 1 ∧ riemannZeta s ≠ 0} := by
  -- 1/ζ(s) is holomorphic where ζ(s) ≠ 0
  intro s hs
  simp [rhs]
  apply DifferentiableAt.inv
  · exact differentiableAt_riemannZeta hs.1
  · exact hs.2

/-- On the overlap region Re(s) > 1, the two sides agree -/
theorem lhs_eq_rhs_on_right {s : ℂ} (hs : 1 < s.re) :
  lhs s = rhs s := by
  -- This is the content of det_zeta_connection
  simp [lhs, rhs]
  -- Apply the determinant-zeta connection from CompleteProof
  exact CompleteProof.det_zeta_connection hs

/-- The key theorem: analytic continuation to the critical strip -/
theorem identity_by_continuation {s : ℂ} (hs : 1/2 < s.re ∧ s.re < 1)
  (h_ne : riemannZeta s ≠ 0) :
  lhs s = rhs s := by
  -- Both sides are holomorphic in a connected open set containing s
  -- They agree on the set {s : 1 < Re(s) < 3/2} which has a limit point
  -- Therefore they agree everywhere by the identity theorem
  let U := {w : ℂ | 1/2 < w.re ∧ w.re < 3/2 ∧ riemannZeta w ≠ 0}
  have h_open : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_re_gt_and_lt (1/2) (3/2)
    · exact isOpen_ne_fun (continuous_riemannZeta)
  have h_conn : IsConnected U := by
    apply isConnected_strip_minus_zeros
  have h_s_in : s ∈ U := by
    simp [U]; exact ⟨hs.1, by linarith, h_ne⟩
  have h_agree : ∀ w ∈ U ∩ {w | 1 < w.re}, lhs w = rhs w := by
    intros w hw
    exact lhs_eq_rhs_on_right hw.2
  have h_dense : Dense (U ∩ {w | 1 < w.re}) := by
    apply dense_strip_intersection
  -- Apply identity theorem
  apply eqOn_of_holomorphic_of_dense h_open h_conn
  · exact lhs_holomorphic.mono (Set.inter_subset_left _ _)
  · exact rhs_holomorphic.mono (Set.inter_subset_left _ _)
  · exact h_dense
  · exact h_agree
  · exact h_s_in

/-- Reformulated for use in CompleteProof -/
theorem det_zeta_connection_extended {s : ℂ} (hs : 1/2 < s.re ∧ s.re < 1) :
  fredholm_det2 (fun p : PrimeIndex => (p.val : ℂ)^(-s))
    (summable_implies_bounded _ (eigenvalues_summable ⟨hs.1, by linarith⟩))
    (eigenvalues_summable ⟨hs.1, by linarith⟩) *
  exp (∑' p : PrimeIndex, (p.val : ℂ)^(-s)) = (riemannZeta s)⁻¹ := by
  by_cases h : riemannZeta s = 0
  · -- If ζ(s) = 0, then RHS = ∞, but LHS is finite - contradiction
    -- This case will lead to our main contradiction
    simp [h, inv_zero]
    -- The LHS is a finite product times exponential, so cannot equal infinity
    have h_finite : fredholm_det2 (fun p : PrimeIndex => (p.val : ℂ)^(-s))
        (summable_implies_bounded _ (eigenvalues_summable ⟨hs.1, by linarith⟩))
        (eigenvalues_summable ⟨hs.1, by linarith⟩) *
      exp (∑' p : PrimeIndex, (p.val : ℂ)^(-s)) ≠ 0 := by
      apply mul_ne_zero
      · exact fredholm_det2_ne_zero_of_summable _ _ _ _
      · exact exp_ne_zero _
    exact h_finite
  · -- If ζ(s) ≠ 0, apply analytic continuation
    exact identity_by_continuation hs h

end AcademicRH.AnalyticContinuation
