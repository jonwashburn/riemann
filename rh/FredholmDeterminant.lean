import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import rh.Common

/-!
# Fredholm Determinant Theory

This file develops the theory of Fredholm determinants for diagonal operators.
-/

namespace RH.FredholmDeterminant

open Complex Real RH

/-- The eigenvalues of the evolution operator -/
noncomputable def evolutionEigenvalues (s : ℂ) : {p : ℕ // Nat.Prime p} → ℂ :=
  fun p => (p.val : ℂ)^(-s)

/-- A diagonal operator with given eigenvalues -/
noncomputable def DiagonalOperator (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ)
    (h_bounded : ∃ C : ℝ, ∀ p, ‖eigenvalues p‖ ≤ C) : WeightedL2 →L[ℂ] WeightedL2 := by
  -- Define the underlying linear map acting coordinate‐wise.
  let L : WeightedL2 →ₗ[ℂ] WeightedL2 :=
    {
      toFun := fun ψ =>
        -- Build the function point-wise and package it as an element of `WeightedL2`.
        ⟨(fun p : {p : ℕ // Nat.Prime p} => eigenvalues p * ψ p), by
          -- The required `Memℓp` proof follows from boundedness of `eigenvalues` and the
          -- fact that `ψ` is already in `ℓ²`.
          -- Since eigenvalues are bounded and ψ ∈ l², their product is in l²
          -- For bounded eigenvalues |λ_p| ≤ C and ψ ∈ l², we have |λ_p ψ_p|² ≤ C² |ψ_p|²
          -- Therefore ∑ |λ_p ψ_p|² ≤ C² ∑ |ψ_p|² < ∞, so λψ ∈ l²
          obtain ⟨C, hC⟩ := h_bounded
          -- Use the fact that bounded pointwise multiplication preserves l² membership
          apply Memℓp.of_exponent_ge
          -- Show that the function is in l²
          have h_bound : ∀ p, ‖eigenvalues p * ψ p‖^2 ≤ C^2 * ‖ψ p‖^2 := by
            intro p
            rw [norm_mul, mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_right (norm_nonneg _) (hC p) 2) (sq_nonneg _)
          -- The sum is bounded by C² times the l² norm of ψ
          exact Memℓp.of_bounded ψ.property (C^2) h_bound⟩,
      map_add' := by
        intro ψ φ
        -- linearity proof (pointwise multiplication distributes over addition)
        ext p
        simp only [lp.coeFn_add, Pi.add_apply]
        ring,
      map_smul' := by
        intro c ψ
        -- compatibility with scalar multiplication
        ext p
        simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        -- eigenvalues p * (c • ψ p) = c • (eigenvalues p * ψ p)
        -- The key insight: c • ψ p = c * ψ p for complex numbers
        simp only [smul_eq_mul]
        -- Now we have: eigenvalues p * (c * ψ p) = c * (eigenvalues p * ψ p)
        ring
    };
  -- Use the bound coming from `h_bounded` to upgrade to a continuous map.
  have h_cont : ∃ C : ℝ, ∀ ψ : WeightedL2, ‖L ψ‖ ≤ C * ‖ψ‖ := by
    rcases h_bounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro ψ
    -- Apply the helper lemma providing the bound.
    have h_bound : ∃ (ψ' : WeightedL2), (∀ p, ψ' p = eigenvalues p * ψ p) ∧ ‖ψ'‖ ≤ C * ‖ψ‖ := by
      -- Use the proof from FredholmDeterminantProofs
      exact FredholmDeterminantProofs.diagonal_operator_continuous_proof eigenvalues C hC ψ
    rcases h_bound with ⟨ψ', hψ', h_norm⟩
    -- Identify `ψ'` with `L ψ` to transfer the bound.
    have : ψ' = L ψ := by
      ext p; simpa using hψ' p
    simpa [this] using h_norm
  -- Upgrade to a `ContinuousLinearMap`.
  exact L.mkContinuousOfExistsBound h_cont

/-- The evolution operator from eigenvalues -/
noncomputable def evolutionOperatorFromEigenvalues (s : ℂ) : WeightedL2 →L[ℂ] WeightedL2 :=
  DiagonalOperator (evolutionEigenvalues s)
    ⟨(2 : ℝ)^s.re, fun p => by
      -- Use the proof from FredholmDeterminantProofs
      exact FredholmDeterminantProofs.evolution_eigenvalue_bound_proof s p⟩

/-- A(s) acts diagonally on basis vectors with eigenvalues p^{-s}. -/
@[simp]
lemma evolution_diagonal_action (s : ℂ) (p : {p : ℕ // Nat.Prime p}) :
    evolutionOperatorFromEigenvalues s (WeightedL2.deltaBasis p) =
      (p.val : ℂ)^(-s) • WeightedL2.deltaBasis p := by
  -- This follows from the definition of the diagonal operator
  unfold evolutionOperatorFromEigenvalues
  -- DiagonalOperator is defined as a term, not a definition we can unfold
  -- Instead, we work directly with the constructed continuous linear map
  simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  ext q
  simp only [WeightedL2.deltaBasis, lp.single_apply, evolutionEigenvalues]
  by_cases h : q = p
  · simp [h, Pi.smul_apply, smul_eq_mul]
  · simp [h, Pi.smul_apply, mul_zero, smul_zero]

/-- The regularized Fredholm determinant for diagonal operators -/
noncomputable def fredholmDet2Diagonal (eigenvalues : {p : ℕ // Nat.Prime p} → ℂ) : ℂ :=
  ∏' p : {p : ℕ // Nat.Prime p}, (1 - eigenvalues p) * Complex.exp (eigenvalues p)

/-- The determinant identity specialized to our evolution eigenvalues. -/
theorem fredholm_det2_diagonal (s : ℂ) (hs : 1/2 < s.re) :
    fredholmDet2Diagonal (evolutionEigenvalues s) =
      ∏' p : {p : ℕ // Nat.Prime p}, (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s)) := by
  -- This is just the definition unfolded
  unfold fredholmDet2Diagonal evolutionEigenvalues
  rfl

end RH.FredholmDeterminant
