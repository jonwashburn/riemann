import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.academic_framework.CompletedXi
import rh.academic_framework.ZetaFunctionalEquation

/-!
Zero-symmetry for `riemannXi_ext` from the functional equation.
-/

noncomputable section

open Complex

namespace RH.AcademicFramework.CompletedXi

/-- Zero symmetry derived from a supplied functional equation. -/
theorem zero_symmetry_from_fe
    (f : ℂ → ℂ)
    (funcEq : ∀ s, f s = f (1 - s)) :
    ∀ ρ, f ρ = 0 → f (1 - ρ) = 0 := by
  intro ρ hρ
  -- Avoid simp: use transitivity with the functional equation
  have h := funcEq ρ  -- f ρ = f (1 - ρ)
  have : f (1 - ρ) = f ρ := h.symm
  exact Eq.trans this hρ

/-- Functional equation for `riemannXi_ext`. -/
theorem xi_ext_functional_equation : ∀ s, riemannXi_ext s = riemannXi_ext (1 - s) := by
  intro s
  -- Avoid simp: change goal to the completed zeta FE directly
  change completedRiemannZeta s = completedRiemannZeta (1 - s)
  exact RH.AcademicFramework.zeta_functional_equation s

@[simp] theorem xi_ext_zero_symmetry : ∀ ρ, riemannXi_ext ρ = 0 → riemannXi_ext (1 - ρ) = 0 := by
  refine zero_symmetry_from_fe riemannXi_ext ?h
  intro s; exact xi_ext_functional_equation s

end RH.AcademicFramework.CompletedXi
