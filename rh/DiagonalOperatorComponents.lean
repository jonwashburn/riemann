import rh.Common
import Mathlib.Analysis.InnerProductSpace.l2Space
import rh.FredholmDeterminant

/-!
# Diagonal Operator Components

This file analyzes the components of diagonal operators.
-/

namespace RH.DiagonalComponents

open Complex Real RH

/-- If A(s)ψ = ψ componentwise, then p^{-s} ψ(p) = ψ(p) for all p -/
theorem diagonal_fixed_point_components (s : ℂ) (ψ : WeightedL2)
    (h : FredholmDeterminant.evolutionOperatorFromEigenvalues s ψ = ψ) :
    ∀ p : {p : ℕ // Nat.Prime p}, (p.val : ℂ)^(-s) * ψ p = ψ p := by
  intro p
  -- The evolution operator acts diagonally with eigenvalue p^{-s} on component p
  -- So A(s)ψ = ψ means (p^{-s} * ψ(p)) = ψ(p) for each component
  have h_comp : (FredholmDeterminant.evolutionOperatorFromEigenvalues s ψ) p = ψ p := by
    rw [h]
  -- By definition of evolutionOperatorFromEigenvalues
  rw [FredholmDeterminant.evolutionOperatorFromEigenvalues] at h_comp
  simp at h_comp
  exact h_comp

end RH.DiagonalComponents
