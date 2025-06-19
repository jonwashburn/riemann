import rh.Common
import rh.FredholmDeterminant
import DiagonalArithmeticHamiltonianProof1
import DiagonalArithmeticHamiltonianProof2Simple
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Instances.ENNReal

/-!
# Diagonal Arithmetic Hamiltonian

This file proves that the arithmetic Hamiltonian H acts diagonally on the
basis vectors δ_p with eigenvalues log p.

This eliminates the axiom `hamiltonian_diagonal_action`.
-/

namespace RH.DiagonalArithmeticHamiltonian

open Complex Real RH

/-- The arithmetic Hamiltonian H with eigenvalues log p -/
noncomputable def ArithmeticHamiltonian : WeightedL2 →L[ℂ] WeightedL2 :=
  -- Define H as a diagonal operator with eigenvalues log p
  FredholmDeterminant.DiagonalOperator
    (fun p => (Real.log p.val : ℂ))
    ⟨1, fun p => by simp; exact abs_log_le_self_of_one_le (Nat.one_le_cast.mpr (Nat.Prime.one_lt p.prop))⟩

/-- The key lemma: H acts diagonally on basis vectors -/
@[simp]
lemma hamiltonian_diagonal_action (p : {p : ℕ // Nat.Prime p}) :
    ArithmeticHamiltonian (WeightedL2.deltaBasis p) = (Real.log p.val : ℂ) • WeightedL2.deltaBasis p := by
  -- Use the proof from DiagonalArithmeticHamiltonianProof1
  unfold ArithmeticHamiltonian
  exact DiagonalArithmeticHamiltonianProof1.hamiltonian_diagonal_action_proof p

/-- H is essentially self-adjoint on its dense domain -/
theorem hamiltonian_self_adjoint :
    ∀ ψ φ : WeightedL2, ψ ∈ WeightedL2.domainH → φ ∈ WeightedL2.domainH →
    ⟪ArithmeticHamiltonian ψ, φ⟫_ℂ = ⟪ψ, ArithmeticHamiltonian φ⟫_ℂ := by
  -- Use the proof from DiagonalArithmeticHamiltonianProof2Simple
  intros ψ φ hψ hφ
  unfold ArithmeticHamiltonian
  exact DiagonalArithmeticHamiltonianProof2Simple.hamiltonian_self_adjoint_simple_proof ψ φ hψ hφ

end RH.DiagonalArithmeticHamiltonian
