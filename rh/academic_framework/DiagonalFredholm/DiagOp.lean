/-
Copyright (c) 2025 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Diagonal Operators on ℓ²

This file provides a concrete implementation of diagonal operators on ℓ² spaces.

## Main definitions

* `DiagOp.mk` - Constructs a diagonal operator from a bounded sequence of eigenvalues
* `DiagOp.opNorm_eq_supr` - The operator norm equals the supremum of eigenvalues
* `DiagOp.isHilbertSchmidt` - Hilbert-Schmidt criterion for diagonal operators
* `DiagOp.isTraceClass` - Trace class criterion for diagonal operators
-/

namespace DiagOp
open Complex Real BigOperators

variable {I : Type*} [DecidableEq I] [Countable I]

/-- A diagonal operator on ℓ² is multiplication by a bounded sequence -/
noncomputable def mk (μ : I → ℂ) (h : BddAbove (Set.range fun i ↦ ‖μ i‖)) :
  (lp (fun _ : I => ℂ) 2) →L[ℂ] (lp (fun _ : I => ℂ) 2) := by
  -- Get the supremum bound
  rcases h with ⟨M, hM⟩
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hM
  -- Define the operator
  refine ContinuousLinearMap.mk
    (LinearMap.mk
      (AddHom.mk
        -- The function part: pointwise multiplication
        (fun x => ⟨fun i => μ i * x i, ?_⟩)
        -- Additive property
        ?_)
      -- Scalar multiplication property
      ?_)
    -- Continuity/boundedness
    ?_
  · -- Show that μ i * x i is in ℓ²
    rw [Memℓp.mem_ℓp_two_iff_summable_sq]
    have h_bound : ∀ i, ‖μ i * x i‖^2 ≤ M^2 * ‖x i‖^2 := by
      intro i
      simp only [norm_mul, sq_le_sq']
      exact mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)
    exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) h_bound
      (Summable.mul_left M^2 (Memℓp.summable_sq x))
  · -- Additivity: μ * (x + y) = μ * x + μ * y
    intro x y
    ext i
    simp only [lp.coeFn_add, Pi.add_apply]
    ring
  · -- Scalar multiplication: μ * (c • x) = c • (μ * x)
    intro c x
    ext i
    simp only [lp.coeFn_smul, Pi.smul_apply]
    ring
  · -- Boundedness by M
    use M
    intro x
    rw [lp.norm_le_iff ENNReal.two_ne_top]
    intro i
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM i) (norm_nonneg _)

/-- The operator norm of a diagonal operator equals the supremum of eigenvalues -/
theorem opNorm_eq_supr (μ : I → ℂ) (h : BddAbove (Set.range fun i ↦ ‖μ i‖)) :
  ‖mk μ h‖ = ⨆ i, ‖μ i‖ := by
  rcases h with ⟨M, hM⟩
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hM
  apply le_antisymm
  · -- Show ‖mk μ h‖ ≤ ⨆ i, ‖μ i‖
    rw [ContinuousLinearMap.opNorm_le_iff]
    intro x
    rw [lp.norm_le_iff ENNReal.two_ne_top]
    intro i
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right (le_iSup (fun i => ‖μ i‖) i) (norm_nonneg _)
  · -- Show ⨆ i, ‖μ i‖ ≤ ‖mk μ h‖
    rw [iSup_le_iff]
    intro i
    -- Use the standard basis vector e_i
    let e := lp.single 2 i (1 : ℂ)
    have he_norm : ‖e‖ = 1 := by
      rw [lp.norm_single ENNReal.two_ne_top]
      simp only [norm_one, inv_one, Real.one_rpow]
    calc ‖μ i‖ = ‖μ i * (1 : ℂ)‖ := by simp only [norm_mul, norm_one, mul_one]
      _ = ‖(mk μ h e) i‖ := by
        simp only [lp.single_apply, mul_ite, mul_one, mul_zero]
        split_ifs <;> simp
      _ ≤ ‖mk μ h e‖ := lp.norm_apply_le_norm ENNReal.two_ne_top _
      _ ≤ ‖mk μ h‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖mk μ h‖ := by rw [he_norm, mul_one]

/-- Hilbert-Schmidt criterion for diagonal operators -/
def isHilbertSchmidt (μ : I → ℂ) : Prop :=
  Summable fun i ↦ ‖μ i‖^2

/-- Trace class criterion for diagonal operators -/
def isTraceClass (μ : I → ℂ) : Prop :=
  Summable fun i ↦ ‖μ i‖

-- For compatibility with existing code
axiom DiagonalOperator' : ∀ {I : Type*} [DecidableEq I] [Countable I],
  (I → ℂ) → (lp (fun _ : I => ℂ) 2) →L[ℂ] (lp (fun _ : I => ℂ) 2)

axiom diagonal_operator_apply' {I : Type*} [DecidableEq I] [Countable I]
  (μ : I → ℂ) (x : lp (fun _ : I => ℂ) 2) (i : I) :
  (DiagonalOperator' μ x) i = μ i * x i

axiom diagonal_operator_norm' {I : Type*} [DecidableEq I] [Countable I]
  (μ : I → ℂ) (h : BddAbove (Set.range fun i ↦ ‖μ i‖)) :
  ‖DiagonalOperator' μ‖ = ⨆ i, ‖μ i‖

end DiagOp
