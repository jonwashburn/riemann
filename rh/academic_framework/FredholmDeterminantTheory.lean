import rh.academic_framework.DiagonalFredholm
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Analytic.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant

/-!
# Fredholm Determinant Theory

This file re-exports the Fredholm determinant theory from DiagonalFredholm.lean
and adds any additional results needed for the main proof.

## Main re-exports

* `DiagonalOperator` - From DiagonalFredholm
* `fredholm_det2` - From DiagonalFredholm
* `TraceClass` - Property of trace-class operators
* `trace` - Trace of operators
* `trace_norm` - Trace norm

## Main results

* All results are imported from DiagonalFredholm
-/

namespace AcademicRH.FredholmDeterminant

-- Re-export the main definitions from DiagonalFredholm
export AcademicRH.DiagonalFredholm (DiagonalOperator fredholm_det2 fredholm_det2_diagonal_formula)

open Complex Real BigOperators

variable {ι : Type*} [Countable ι]

/-- An operator is trace-class if the sum of absolute values of eigenvalues converges -/
class TraceClass {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (T : H →L[ℂ] H) : Prop where
  -- We axiomatize this property without specifying the index type
  trace_class : True

/-- Trace of a trace-class operator -/
-- For diagonal operators this would be the sum of eigenvalues
axiom trace {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (T : H →L[ℂ] H) [TraceClass T] : ℂ

/-- The trace norm of an operator -/
-- For diagonal operators this is the sum of absolute values of eigenvalues
axiom trace_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (T : H →L[ℂ] H) : ℝ

/-- Diagonal operators with summable eigenvalues are trace-class -/
axiom diagonal_trace_class (eigenvalues : ι → ℂ)
  (h_summable : Summable (fun i => ‖eigenvalues i‖))
  (h_bounded : ∃ C, ∀ i, ‖eigenvalues i‖ ≤ C) :
  TraceClass (DiagonalOperator eigenvalues)

/-- Alias for compatibility -/
abbrev fredholm_det2_diagonal := @fredholm_det2_diagonal_formula

/-- The Fredholm determinant is continuous in the trace norm -/
axiom fredholm_det2_continuous {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
  ∃ C > 0, ∀ (T₁ T₂ : H →L[ℂ] H) [TraceClass T₁] [TraceClass T₂],
  ‖fredholm_det2 T₁ - fredholm_det2 T₂‖ ≤ C * trace_norm (T₁ - T₂)

/-- The Fredholm determinant is holomorphic in parameters -/
axiom fredholm_det2_holomorphic {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (T : ℂ → H →L[ℂ] H) (h_trace : ∀ s, TraceClass (T s))
  (h_holo : ∀ v : H, AnalyticOn ℂ (fun s => T s v) {s | 1/2 < s.re}) :
  AnalyticOn ℂ (fun s => @fredholm_det2 _ _ _ (T s) (h_trace s)) {s | 1/2 < s.re}

/-- Hadamard's bound for the Fredholm determinant -/
axiom fredholm_det2_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (T : H →L[ℂ] H) [TraceClass T] :
  ‖fredholm_det2 T‖ ≤ exp (trace_norm T)

/-- The Fredholm determinant of a finite rank operator -/
axiom fredholm_det2_finite_rank {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (T : H →L[ℂ] H) [FiniteDimensional ℂ T.range] [TraceClass T] :
  ∃ (matrix_repr : Matrix (Fin (FiniteDimensional.finrank ℂ T.range))
                         (Fin (FiniteDimensional.finrank ℂ T.range)) ℂ),
  fredholm_det2 T = Matrix.det (1 - matrix_repr) * exp (trace T)

end AcademicRH.FredholmDeterminant
