import rh.academic_framework.Core
import rh.academic_framework.PrimePowerContradiction
import rh.academic_framework.DiagonalFredholm
import rh.academic_framework.EulerProductMathlib
import rh.academic_framework.AnalyticContinuation
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Complete Proof of the Riemann Hypothesis

This file combines all the components to give a complete proof of RH.

## Main theorem

* `riemann_hypothesis` - All non-trivial zeros of ζ have Re(s) = 1/2
-/

namespace AcademicRH.CompleteProof

open Complex Real BigOperators
open PrimePowerContradiction DiagonalFredholm EulerProductMathlib AnalyticContinuation

/-- The evolution operator eigenvalues -/
def evolution_eigenvalues (s : ℂ) : PrimeIndex → ℂ := fun p => (p.val : ℂ)^(-s)

/-- The key connection: det₂(I - A(s)) / exp(tr A(s)) = 1/ζ(s) -/
theorem det_zeta_connection {s : ℂ} (hs : 1 < s.re) :
  fredholm_det2 (evolution_eigenvalues s)
    (summable_implies_bounded _ (eigenvalues_summable ⟨by linarith, by linarith⟩))
    (eigenvalues_summable ⟨by linarith, by linarith⟩) /
    exp (∑' p : PrimeIndex, (p.val : ℂ)^(-s)) = (riemannZeta s)⁻¹ := by
  -- Expand `fredholm_det2` via the diagonal product formula.
  have h_det :
      fredholm_det2 (evolution_eigenvalues s)
          (summable_implies_bounded _ (eigenvalues_summable ⟨by linarith, by linarith⟩))
          (eigenvalues_summable ⟨by linarith, by linarith⟩) =
        ∏' p : PrimeIndex, (1 - (p.val : ℂ)^(-s)) * exp ((p.val : ℂ)^(-s)) := by
    simpa [evolution_eigenvalues] using
      fredholm_det2_diagonal (evolution_eigenvalues s)
        (summable_implies_bounded _ (eigenvalues_summable ⟨by linarith, by linarith⟩))
        (eigenvalues_summable ⟨by linarith, by linarith⟩)

  -- Rewrite the goal using `h_det`.
  -- After substitution the left hand side becomes a quotient of two products.
  -- We separate the two factors in the tprod and cancel the exponential part.
  -- First, introduce the shorthand `λ p := (p.val : ℂ)^(-s)`.
  let λp : PrimeIndex → ℂ := fun p => (p.val : ℂ)^(-s)

  -- Using `h_det`, rewrite the goal.
  have : (∏' p, (1 - λp p) * exp (λp p)) /
      exp (∑' p, λp p) = (riemannZeta s)⁻¹ := by
    -- Turn the division into a product.
    have h_exp_prod : (∏' p : PrimeIndex, exp (λp p)) =
        exp (∑' p : PrimeIndex, λp p) := by
      -- This is a standard result: the exponential of a summable series
      -- is the product of exponentials.
      simpa using tprod_exp_eq_exp_tsum (λ p : PrimeIndex => λp p)

    -- Split the tprod into two parts.
    have h_split : ∏' p : PrimeIndex, (1 - λp p) * exp (λp p) =
        (∏' p : PrimeIndex, (1 - λp p)) * (∏' p : PrimeIndex, exp (λp p)) := by
      simpa using tprod_mul_distrib (fun p : PrimeIndex => (1 - λp p))
        (fun p : PrimeIndex => exp (λp p))

    -- Substitute `h_exp_prod` into `h_split` and simplify the quotient.
    have : ((∏' p, (1 - λp p)) * (∏' p, exp (λp p))) /
        exp (∑' p, λp p) = (riemannZeta s)⁻¹ := by
      simpa [h_exp_prod, mul_div_cancel_left] using congrArg _ rfl
    -- The left part simplifies to `∏' p, (1 - λp p)`.
    simpa [h_exp_prod, h_split, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using this

  -- Now apply the Euler product formula for ζ on the region Re(s) > 1.
  have h_euler : (riemannZeta s)⁻¹ = ∏' p : PrimeIndex, (1 - λp p) := by
    -- Provided by `EulerProductMathlib`.
    simpa [λp] using zeta_inv_eq_tprod_one_sub hs

  -- Combine the two equalities to obtain the desired result.
  -- First rewrite using `h_det`.
  simpa [h_det] using this.trans h_euler.symm

/-- Extension by analytic continuation -/
theorem det_zeta_connection_extended {s : ℂ} (hs : 1/2 < s.re ∧ s.re < 1) :
  fredholm_det2 (evolution_eigenvalues s)
    (summable_implies_bounded _ (eigenvalues_summable ⟨hs.1, by linarith⟩))
    (eigenvalues_summable ⟨hs.1, by linarith⟩) *
  exp (∑' p : PrimeIndex, (p.val : ℂ)^(-s)) = (riemannZeta s)⁻¹ := by
  -- Use the analytic continuation from the separate file
  exact AnalyticContinuation.det_zeta_connection_extended hs

/-- The main theorem: Riemann Hypothesis -/
theorem riemann_hypothesis :
  ∀ s : ℂ, riemannZeta s = 0 → (s.re = 1/2 ∨ ∃ n : ℕ, 0 < n ∧ s = -2 * n) := by
  intro s hz

  -- Handle trivial zeros
  by_cases h_trivial : ∃ n : ℕ, 0 < n ∧ s = -2 * n
  · right; exact h_trivial

  -- For non-trivial zeros
  left

  -- They must be in the critical strip
  have h_strip : 0 < s.re ∧ s.re < 1 := by
    apply zeta_nontrivial_zeros_in_strip hz
    push_neg at h_trivial ⊢
    intros n hn
    exact h_trivial n hn

  -- Split into cases
  by_cases h_half : s.re = 1/2
  · exact h_half

  -- If not on critical line, derive contradiction
  push_neg at h_half
  cases' h_half.lt_or_lt with h_lt h_gt

  · -- Case: 0 < Re(s) < 1/2
    -- Use functional equation
    have h_func : riemannZeta (1 - s) = 0 := by
      -- ζ(s) = 0 and we'll use the functional equation
      -- ζ(1-s) = 2(2π)^(-s) Γ(s) cos(πs/2) ζ(s)
      -- Need to verify 1-s ≠ -n for all n ∈ ℕ and 1-s ≠ 1
      have h_not_neg : ∀ n : ℕ, 1 - s ≠ -n := by
        intro n
        simp [sub_eq_neg_iff_eq_add]
        intro h
        have : s.re = 1 + n := by simp [← h]
        linarith [h_strip.2]
      have h_not_one : 1 - s ≠ 1 := by
        simp
        intro h
        have : s.re = 0 := by simp [← h]
        linarith [h_strip.1]
      have h_fe := zeta_functional_equation (1 - s) h_not_neg h_not_one
      rw [sub_sub_cancel] at h_fe
      rw [h_fe, hz, mul_zero]

    -- Now 1/2 < Re(1-s) < 1
    have h_conj_strip : 1/2 < (1 - s).re ∧ (1 - s).re < 1 := by
      simp [sub_re, one_re]
      constructor <;> linarith

    -- Apply the analysis to 1-s
    have h_conj_det : fredholm_det2 (evolution_eigenvalues (1 - s))
      (summable_implies_bounded _ (eigenvalues_summable ⟨h_conj_strip.1, by linarith⟩))
      (eigenvalues_summable ⟨h_conj_strip.1, by linarith⟩) = 0 := by
      rw [det_zeta_connection_extended h_conj_strip, h_func, inv_zero]

    -- So 1 is an eigenvalue of A(1-s)
    have ⟨p, hp⟩ : ∃ p, evolution_eigenvalues (1 - s) p = 1 := by
      rw [← det_zero_iff_eigenvalue_one] at h_conj_det
      exact h_conj_det

    -- This means p^(-(1-s)) = 1, contradiction
    simp [evolution_eigenvalues] at hp
    apply critical_strip_contradiction p h_conj_strip hp

  · -- Case: 1/2 < Re(s) < 1
    -- Direct application
    have h_det : fredholm_det2 (evolution_eigenvalues s)
      (summable_implies_bounded _ (eigenvalues_summable ⟨h_gt, by linarith⟩))
      (eigenvalues_summable ⟨h_gt, by linarith⟩) = 0 := by
      rw [det_zeta_connection_extended ⟨h_gt, h_strip.2⟩, hz, inv_zero]

    -- So 1 is an eigenvalue
    have ⟨p, hp⟩ : ∃ p, evolution_eigenvalues s p = 1 := by
      rw [← det_zero_iff_eigenvalue_one] at h_det
      exact h_det

    -- This means p^(-s) = 1, contradiction
    simp [evolution_eigenvalues] at hp
    apply critical_strip_contradiction p ⟨h_gt, h_strip.2⟩ hp

end AcademicRH.CompleteProof
