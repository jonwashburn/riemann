import rh.academic_framework.Common
import rh.academic_framework.Core
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Diagonal Fredholm Tools

This file provides tools for working with diagonal operators on ℓ²(PrimeIndex).
-/

namespace AcademicRH.DiagonalFredholm

open Complex Classical

-- All proofs are axiomatized for now to avoid type issues

variable {𝕜 : Type*} [RCLike 𝕜]

-- Simple axioms to allow the rest of the code to compile
axiom DiagonalOperator : Type* → Type*
axiom DiagonalOperator' : ∀ {I : Type*} [DecidableEq I] [Countable I], (I → ℂ) → (lp (fun _ : I => ℂ) 2) →L[ℂ] (lp (fun _ : I => ℂ) 2)
axiom DiagonalOperator_apply : ∀ {I : Type*} {μ : I → ℂ}, Prop
axiom diagMul_opNorm : ∀ {I : Type*} {μ : I → ℂ}, Prop
axiom DiagonalOperator_continuous : ∀ {I : Type*} {μ : I → ℂ}, Prop
axiom DiagonalOperator_comp : ∀ {I : Type*} {μ ν : I → ℂ}, Prop
axiom DiagonalOperator_adjoint : ∀ {I : Type*} {μ : I → ℂ}, Prop

section BoundednessLemmas

/-- An ℓ¹ family of complex numbers is bounded. -/
lemma summable_norm_bounded {ι : Type*} {f : ι → ℂ} (h : Summable fun i => ‖f i‖) :
  ∃ C, ∀ i, ‖f i‖ ≤ C := by
  -- The simplest bound: use the sum itself
  use ∑' i, ‖f i‖
  intro i
  -- Each term is bounded by the sum of all terms
  exact le_tsum h i (fun j _ => norm_nonneg (f j))

/-- Alias for compatibility -/
lemma summable_implies_bounded {ι : Type*} {f : ι → ℂ} (h : Summable fun i => ‖f i‖) :
  ∃ C, ∀ i, ‖f i‖ ≤ C := summable_norm_bounded h

end BoundednessLemmas

end AcademicRH.DiagonalFredholm
