import rh.academic_framework.DiagonalOperatorAnalysis
import rh.academic_framework.FredholmInfrastructure
import rh.academic_framework.OperatorPositivity
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Birman-Schwinger Principle

This file provides the Birman-Schwinger principle connecting eigenvalues
and zeros of Fredholm determinants.

## Main results

* `birman_schwinger_principle` - 1 is an eigenvalue iff Fredholm determinant is zero
-/

namespace AcademicRH.BirmanSchwingerPrinciple

open Complex Real BigOperators
open AcademicRH.DiagonalOperator AcademicRH.FredholmInfrastructure

/-- The Birman-Schwinger principle: 1 is in spectrum(Λ_s) iff det(I - Λ_s) = 0 -/
theorem birman_schwinger_principle {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    1 ∈ spectrum ℂ (euler_operator_strip s hs) ↔
    fredholm_det (1 - euler_operator_strip s hs) = 0 := by
  sorry

/-- Connection to zeta zeros -/
theorem zeta_zeros_iff_eigenvalue {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
    riemannZeta s = 0 ↔ 1 ∈ spectrum ℂ (euler_operator_strip s hs) := by
  sorry

end AcademicRH.BirmanSchwingerPrinciple
