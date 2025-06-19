import rh.Common
import rh.FredholmDeterminant
import DiagonalArithmeticHamiltonianProof1
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Simple Proof of hamiltonian_self_adjoint

This file provides a direct proof that H is self-adjoint by using the fact that
diagonal operators with real eigenvalues are automatically self-adjoint on l².

## Key insight:
For ψ, φ in the domain where all sums converge, we have:
⟪Hψ, φ⟫ = Σ_p (log p) ψ(p) * conj(φ(p))
⟪ψ, Hφ⟫ = Σ_p ψ(p) * conj((log p) φ(p)) = Σ_p (log p) ψ(p) * conj(φ(p))

These are equal because log p is real.
-/

namespace RH.DiagonalArithmeticHamiltonianProof2Simple

open Complex Real Infrastructure RH.FredholmDeterminant

-- The key insight: for functions in domainH, the weighted sums converge
lemma domain_ensures_convergence (ψ : WeightedL2) (hψ : ψ ∈ WeightedL2.domainH) :
    Summable fun p => ‖ψ p‖^2 * (Real.log p.val)^2 := by
  -- This is exactly the definition of domainH
  exact hψ

-- For diagonal operators on l², we can compute inner products componentwise
-- when the sums converge
lemma diagonal_inner_product_formula
    (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ)
    (h_bounded : ∃ C : ℝ, ∀ p, ‖eigenvalues p‖ ≤ C)
    (ψ φ : WeightedL2)
    (h_converge : Summable fun p => eigenvalues p * ψ p * conj (φ p)) :
    ⟪DiagonalOperator eigenvalues h_bounded ψ, φ⟫_ℂ =
    ∑' p, eigenvalues p * ψ p * conj (φ p) := by
  -- The inner product on l² is defined as Σ_p f(p) * conj(g(p))
  -- DiagonalOperator multiplies component p by eigenvalues p
  -- So ⟪DiagonalOperator eigenvalues ψ, φ⟫ = Σ_p (eigenvalues p * ψ p) * conj(φ p)
  rw [inner_def]
  simp only [DiagonalArithmeticHamiltonianProof1.diagonal_operator_apply]
  -- The sum converges by assumption
  exact tsum_congr (fun p => rfl)

-- Main theorem: H is self-adjoint on domainH
theorem hamiltonian_self_adjoint_simple_proof
    (ψ φ : WeightedL2) (hψ : ψ ∈ WeightedL2.domainH) (hφ : φ ∈ WeightedL2.domainH) :
    let H := FredholmDeterminant.DiagonalOperator
      (fun p => (Real.log p.val : ℂ))
      ⟨1, fun p => by simp; exact abs_log_le_self_of_one_le (Nat.one_le_cast.mpr (Nat.Prime.one_lt p.prop))⟩
    ⟪H ψ, φ⟫_ℂ = ⟪ψ, H φ⟫_ℂ := by
  -- Strategy: Show both sides equal the same sum
  -- Both converge because ψ, φ ∈ domainH

  -- We'll show both sides equal Σ_p (log p) ψ(p) conj(φ(p))
  have key_sum : ∑' p, (Real.log p.val : ℂ) * ψ p * conj (φ p) =
                 ∑' p, ψ p * conj ((Real.log p.val : ℂ) * φ p) := by
    congr 1
    ext p
    -- Need to show: (log p) * ψ(p) * conj(φ(p)) = ψ(p) * conj((log p) * φ(p))
    rw [map_mul]
    -- = ψ(p) * conj(log p) * conj(φ(p))
    -- Since log p is real: conj(log p) = log p
    have h_real : conj (Real.log p.val : ℂ) = (Real.log p.val : ℂ) := by
      simp only [conj_of_real]
    rw [h_real]
    ring

  -- Now we need to verify convergence to apply the formula
  -- This requires showing the weighted sums converge, which follows from domain membership
  -- For brevity, we'll state this as a hypothesis
  have h_conv1 : Summable fun p => (Real.log p.val : ℂ) * ψ p * conj (φ p) := by
    -- Use Cauchy-Schwarz: |∑ a_n b_n| ≤ (∑ |a_n|²)^{1/2} (∑ |b_n|²)^{1/2}
    -- Here: a_p = (log p)^β ψ(p), b_p = (log p)^β conj(φ(p))
    -- So |log p · ψ(p) · conj(φ(p))| ≤ |(log p)^β ψ(p)| · |(log p)^β conj(φ(p))|
    apply Summable.of_nonneg_of_le
    · intro p
      exact norm_nonneg _
    · intro p
      -- Bound using Cauchy-Schwarz pointwise
      have h_cs_bound : ‖(Real.log p.val : ℂ) * ψ p * conj (φ p)‖ ≤
          (‖ψ p‖ * (Real.log p.val)) * (‖φ p‖ * (Real.log p.val)) := by
        rw [norm_mul, norm_mul, norm_conj]
        rw [Complex.norm_real]
        have h_log_nonneg : 0 ≤ Real.log p.val := by
          apply Real.log_nonneg
          have hp_ge_two : 2 ≤ p.val := Nat.Prime.two_le p.prop
          exact Nat.one_le_cast.mpr (le_trans (by norm_num) hp_ge_two)
        rw [abs_of_nonneg h_log_nonneg]
        ring
      exact le_of_lt (lt_of_le_of_lt h_cs_bound (by ring_nf; exact le_refl _))
    · -- The right side is summable by domain conditions
      have h_factor : ∀ p, (‖ψ p‖ * Real.log p.val) * (‖φ p‖ * Real.log p.val) =
          ‖ψ p‖ * ‖φ p‖ * (Real.log p.val)^2 := by
        intro p; ring
      simp only [h_factor]
      -- Use Cauchy-Schwarz for series: ∑ a_n b_n ≤ (∑ a_n²)^{1/2} (∑ b_n²)^{1/2}
      -- Since both ψ and φ are in domainH, we have summability of weighted sums
      apply Summable.of_norm_bounded _ (summable_mul_of_summable hψ hφ)
      intro p
      -- Apply Cauchy-Schwarz: |a·b| ≤ (a² + b²)/2
      calc ‖ψ p‖ * ‖φ p‖ * (Real.log p.val)^2
        ≤ (‖ψ p‖^2 + ‖φ p‖^2) / 2 * (Real.log p.val)^2 := by
          rw [← div_mul_eq_mul_div]
          apply mul_le_mul_of_nonneg_right
          · exact Real.geom_mean_le_arith_mean2_weighted (norm_nonneg _) (norm_nonneg _)
          · exact sq_nonneg _
        _ = (‖ψ p‖^2 * (Real.log p.val)^2 + ‖φ p‖^2 * (Real.log p.val)^2) / 2 := by ring
        _ ≤ max (‖ψ p‖^2 * (Real.log p.val)^2) (‖φ p‖^2 * (Real.log p.val)^2) := by
          apply div_le_iff_le_mul_of_pos_right (by norm_num)
          rw [mul_comm 2]
          exact add_le_two_mul_max _ _
      where summable_mul_of_summable {f g : {p : ℕ // Nat.Prime p} → ℝ} (hf : Summable fun p => f p) (hg : Summable fun p => g p) :
        Summable fun p => max (f p) (g p) := by
        apply Summable.of_nonneg_of_le (fun _ => le_max_left _ _)
        · intro p; exact le_max_left _ _
        · exact Summable.add hf hg

  have h_conv2 : Summable fun p => ψ p * conj ((Real.log p.val : ℂ) * φ p) := by
    rw [← key_sum]
    exact h_conv1

  -- Apply the diagonal inner product formula
  rw [diagonal_inner_product_formula _ _ _ _ h_conv1]
  rw [diagonal_inner_product_formula _ _ _ _ h_conv2]
  exact key_sum

end RH.DiagonalArithmeticHamiltonianProof2Simple
