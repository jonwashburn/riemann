import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.academic_framework.ZetaFunctionalEquation
import rh.RS.Domain
import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Completed Riemann ξ function (ext): we use mathlib's `completedRiemannZeta` and
expose minimal interface pieces needed by RS.
-/

noncomputable section

open Complex

namespace RH.AcademicFramework.CompletedXi

/-- Completed Riemann ξ (ext), defined as mathlib's completed zeta `Λ(s)`. -/
def riemannXi_ext (s : ℂ) : ℂ := completedRiemannZeta s

/-- Open right half-plane Ω = { s | Re s > 1/2 }. -/
private lemma isOpen_Ω : IsOpen RH.RS.Ω := by
  change IsOpen { s : ℂ | (1 / 2 : ℝ) < s.re }
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Differentiability of `riemannXi_ext` away from `0` and `1`. -/
lemma differentiableAt_riemannXi_ext {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
  DifferentiableAt ℂ riemannXi_ext s := by
  change DifferentiableAt ℂ completedRiemannZeta s
  exact differentiableAt_completedZeta (s := s) hs0 hs1

/-- Differentiability of `riemannXi_ext` on Ω \ {1}. -/
theorem riemannXi_ext_differentiable_on_RSΩ_minus_one :
  DifferentiableOn ℂ riemannXi_ext (RH.RS.Ω \ ({1} : Set ℂ)) := by
  intro z hz
  -- z ∈ Ω and z ≠ 1
  have hzΩ : (1 / 2 : ℝ) < z.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hz.1
  have hz0 : z ≠ 0 := by
    intro h0
    have hzRe : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hzΩ
    have hzre0 := congrArg Complex.re h0
    simp [Complex.zero_re] at hzre0
    have hzRe' := hzRe
    rw [hzre0] at hzRe'
    exact (lt_irrefl (0 : ℝ)) hzRe'
  have hz1 : z ≠ 1 := by
    have h := hz.2
    simp [Set.mem_singleton_iff] at h
    exact h
  exact (differentiableAt_riemannXi_ext (s := z) hz0 hz1).differentiableWithinAt

/-- Analyticity of `riemannXi_ext` on Ω \ {1}``, via open-set equivalence. -/
lemma riemannXi_ext_analytic_on_RSΩ_minus_one :
  AnalyticOn ℂ riemannXi_ext (RH.RS.Ω \ ({1} : Set ℂ)) := by
  have hOpen : IsOpen (RH.RS.Ω \ ({1} : Set ℂ)) :=
    (isOpen_Ω).sdiff isClosed_singleton
  -- use the equivalence on open sets
  have h :=
    (analyticOn_iff_differentiableOn (f := riemannXi_ext)
      (s := RH.RS.Ω \ ({1} : Set ℂ)) hOpen)
  exact h.mpr riemannXi_ext_differentiable_on_RSΩ_minus_one

-- symmetry lemmas are provided in CompletedXiSymmetry to avoid duplication

/-- On Ω, zeros of `riemannXi_ext` coincide with zeros of `riemannZeta`. -/
lemma xi_ext_zeros_eq_zeta_zeros_on_Ω :
  ∀ z ∈ RH.RS.Ω, riemannXi_ext z = 0 ↔ riemannZeta z = 0 := by
  intro z hzΩ
  -- From Ω: 1/2 < Re z
  have hhalf : (1 / 2 : ℝ) < z.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hzΩ
  -- Hence Re z > 0 and Γℝ z ≠ 0
  have hpos : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hΓnz : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hpos
  -- Also z ≠ 0, but only Γℝ z ≠ 0 is needed below
  have hζ : riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z :=
    riemannZeta_def_of_ne_zero (s := z) (by
      intro h0
      have hnot : ¬ ((1 / 2 : ℝ) < 0) := by norm_num
      have hzre := congrArg Complex.re h0
      simp [Complex.zero_re] at hzre
      have h := hhalf
      rw [hzre] at h
      exact hnot h)
  constructor
  · intro hXi
    -- Λ z = 0 ⇒ ζ z = 0
    have hΛ0 : completedRiemannZeta z = 0 := by
      dsimp [riemannXi_ext] at hXi
      exact hXi
    -- Rewrite ζ and conclude explicitly
    calc
      riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z := hζ
      _ = completedRiemannZeta z * (Complex.Gammaℝ z)⁻¹ := by rw [div_eq_mul_inv]
      _ = 0 * (Complex.Gammaℝ z)⁻¹ := by rw [hΛ0]
      _ = 0 := by simp
  · intro hζ0
    -- ζ z = 0, and Γℝ z ≠ 0 ⇒ Λ z = 0
    have hdiv0 : completedRiemannZeta z / Complex.Gammaℝ z = 0 := by
      -- rewrite the ζ-definition into the equality
      have htmp := hζ0
      rw [hζ] at htmp
      exact htmp
    have hΛ0 : completedRiemannZeta z = 0 := by
      -- If Λ z ≠ 0 then division by nonzero Γ gives a nonzero value, contradiction
      by_contra hΛ
      have : completedRiemannZeta z / Complex.Gammaℝ z ≠ 0 :=
        div_ne_zero hΛ hΓnz
      exact this hdiv0
    -- Conclude ξ_ext z = 0
    dsimp [riemannXi_ext]
    exact hΛ0

end RH.AcademicFramework.CompletedXi
