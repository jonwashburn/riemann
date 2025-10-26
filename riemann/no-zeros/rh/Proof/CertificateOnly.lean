import rh.RS.PinchCertificate
import rh.RS.PinchIngredients
import rh.RS.Cayley
import rh.academic_framework.CompletedXi
import rh.academic_framework.CompletedXiSymmetry
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
Certificate route core theorems - extracted to avoid CR-outer dependencies.

This file contains ONLY the certificate route, independent of CRGreenOuter/Whitney modules.
-/

namespace RH.Proof.Certificate

open RH.AcademicFramework.CompletedXi RH.RS Complex Set

/-- Core RH from symmetry and no-right-zeros. -/
theorem RH_core
    {Ξ : ℂ → ℂ}
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0)
    (sym : ∀ ρ, Ξ ρ = 0 → Ξ (1 - ρ) = 0) :
    ∀ ρ, Ξ ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  intro ρ h0
  rcases lt_trichotomy ρ.re (1 / 2 : ℝ) with hlt | heq | hgt
  · have hgt' : (1 / 2 : ℝ) < 1 - ρ.re := by linarith
    have hΩσ : (1 - ρ) ∈ RH.RS.Ω := by
      have : (1 / 2 : ℝ) < (1 - ρ).re := by simpa [Complex.sub_re, Complex.one_re] using hgt'
      simpa [RH.RS.Ω, Set.mem_setOf_eq] using this
    have h0σ : Ξ (1 - ρ) = 0 := sym ρ h0
    exfalso; exact (noRightZeros (1 - ρ) hΩσ) h0σ
  · exact heq
  · have hΩ : ρ ∈ RH.RS.Ω := by simpa [RH.RS.Ω, Set.mem_setOf_eq] using hgt
    exact False.elim ((noRightZeros ρ hΩ) h0)

/-- RH for riemannXi. -/
theorem RH_riemannXi
    (riemannXi : ℂ → ℂ)
    (noRightZeros : ∀ ρ ∈ RH.RS.Ω, riemannXi ρ ≠ 0)
    (sym : ∀ ρ, riemannXi ρ = 0 → riemannXi (1 - ρ) = 0) :
    ∀ ρ, riemannXi ρ = 0 → ρ.re = (1 / 2 : ℝ) := by
  exact (RH_core (Ξ := riemannXi) noRightZeros sym)

/-- Pinch route: no-right-zeros from removable extension assignment. -/
theorem no_right_zeros_from_pinch_assign
    (Ξ Θ : ℂ → ℂ)
    (hSchur : RH.RS.IsSchurOn Θ (RH.RS.Ω \ {z | Ξ z = 0}))
    (assign : ∀ ρ, ρ ∈ RH.RS.Ω → Ξ ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | Ξ z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          Set.EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
    : ∀ ρ ∈ RH.RS.Ω, Ξ ρ ≠ 0 := by
  intro ρ hΩ hΞρ
  rcases assign ρ hΩ hΞρ with
    ⟨U, hUopen, hUconn, hUsub, hρU, hUZeq, g, hg, hΘU, hExt, hval, z0, hz0U, hneq⟩
  have hρZ : ρ ∈ ({z | Ξ z = 0} : Set ℂ) := by simpa [Set.mem_setOf_eq] using hΞρ
  have hUminusSub : (U \ {ρ}) ⊆ (RH.RS.Ω \ ({z | Ξ z = 0})) := by
    intro x hx
    have hxU : x ∈ U := hx.1
    have hxNe : x ≠ ρ := by intro h; exact hx.2 (by simpa [h])
    have hxNotZ : x ∉ ({z | Ξ z = 0} : Set ℂ) := by
      intro hxZ
      have hxInCap : x ∈ (U ∩ {z | Ξ z = 0}) := ⟨hxU, hxZ⟩
      have hxSingleton : x ∈ ({ρ} : Set ℂ) := by simpa [hUZeq] using hxInCap
      have : x = ρ := by simpa using hxSingleton
      exact hxNe this
    exact ⟨hUsub hxU, hxNotZ⟩
  have hg_one : ∀ w ∈ U, g w = 1 :=
    RH.RS.GlobalizeAcrossRemovable ({z | Ξ z = 0}) Θ hSchur
      U hUopen hUconn hUsub ρ hΩ hρU hρZ g hg hΘU hUminusSub hExt hval
  have : g z0 = 1 := hg_one z0 hz0U
  exact (hneq this).elim

/-- Final certificate-driven RH theorem. -/
theorem RH_from_pinch_certificate (C : RH.RS.PinchCertificateExt) : RiemannHypothesis := by
  -- Θ from certificate and its Schur bound off Z(Ξ_ext)
  have hSchur : RH.RS.IsSchurOn (RH.RS.Θ_cert C)
      RH.AcademicFramework.HalfPlaneOuterV2.offXi :=
    RH.RS.Θ_cert_Schur_offXi C
  -- Need to extend Schur from offXi to Ω \ {zeros}
  have hSchur' : RH.RS.IsSchurOn (RH.RS.Θ_cert C)
      (RH.RS.Ω \ {z | riemannXi_ext z = 0}) := by
    intro z hz
    -- If z ∈ Ω \ {zeros}, is z ∈ offXi?
    -- offXi = Ω ∧ z ≠ 1 ∧ z ≠ 0 for ξ
    -- If z = 1, then ξ(1) has a pole (not zero), so z ∉ Ω \ {zeros} is false
    -- Actually, ξ_ext(1) is defined but we need to check...
    sorry -- Need to show z ≠ 1 or handle the Schur bound at z = 1
  -- Xi-assign from the certificate's removable existence
  let assignXi : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ (RH.RS.Θ_cert C) (U \ ({ρ} : Set ℂ)) ∧
          Set.EqOn (RH.RS.Θ_cert C) g (U \ ({ρ} : Set ℂ)) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 :=
    fun ρ hΩ hXi => C.existsRemXi ρ hΩ hXi
  -- Get no-right-zeros from pinch
  have noRightZeros : ∀ ρ ∈ RH.RS.Ω, riemannXi_ext ρ ≠ 0 :=
    no_right_zeros_from_pinch_assign riemannXi_ext (RH.RS.Θ_cert C) hSchur' assignXi
  -- Symmetry from FE
  have symXi : ∀ ρ, riemannXi_ext ρ = 0 → riemannXi_ext (1 - ρ) = 0 := by
    intro ρ hρ
    have fe := RH.AcademicFramework.CompletedXi.xi_ext_functional_equation ρ
    rw [hρ] at fe
    have : riemannXi_ext (1 - ρ) = 0 := by simp [←fe]
    exact this
  -- Get RH
  have Hxi : ∀ ρ, riemannXi_ext ρ = 0 → ρ.re = (1 / 2 : ℝ) :=
    RH_riemannXi riemannXi_ext noRightZeros symXi
  -- Convert to mathlib's RiemannHypothesis (this part needs more work but the core is here)
  sorry -- Conversion to mathlib's RiemannHypothesis (requires completedRiemannZeta = ξ_ext connection)

end RH.Proof.Certificate
