/-
Copyright (c) 2025 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import rh.academic_framework.DiagonalFredholm.DiagonalTools

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
open AcademicRH.DiagonalFredholm

/-- A diagonal operator on ℓ² is multiplication by a bounded sequence -/
noncomputable def mk (μ : I → ℂ) (_h : BddAbove (Set.range fun i ↦ ‖μ i‖)) :
  (lp (fun _ : I => ℂ) 2) →L[ℂ] (lp (fun _ : I => ℂ) 2) :=
  DiagonalOperator' μ

/-/ The operator norm identity is provided elsewhere in the framework. -/

/-- Hilbert-Schmidt criterion for diagonal operators -/
def isHilbertSchmidt (μ : I → ℂ) : Prop :=
  Summable fun i ↦ ‖μ i‖^2

/-- Trace class criterion for diagonal operators -/
def isTraceClass (μ : I → ℂ) : Prop :=
  Summable fun i ↦ ‖μ i‖


end DiagOp
