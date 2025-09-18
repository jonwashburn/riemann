import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.academic_framework.ZetaFunctionalEquation
import rh.RS.SchurGlobalization

/-!
Completed Riemann ξ function: archimedean factor `G` and `riemannXi = G · ζ`.

This module defines the completed ξ used by the proof assembly. Deeper
properties (functional equation, nonvanishing facts, etc.) are provided by
callers or other modules.
-/

noncomputable section

open Complex

namespace RH.AcademicFramework.CompletedXi

/-- Archimedean factor for the completed Riemann ξ function. -/
def G (s : ℂ) : ℂ :=
  ((1 : ℂ) / 2) * s * (1 - s) * (Real.pi : ℂ) ^ (-(s / 2)) * Complex.Gamma (s / 2)

/-- Completed Riemann ξ function, defined by `ξ = G · ζ`. -/
def riemannXi (s : ℂ) : ℂ := G s * riemannZeta s

/-- Factorization of ξ (definition level). -/
@[simp] theorem xi_factorization (s : ℂ) : riemannXi s = G s * riemannZeta s := rfl

/-! Auxiliary nonvanishing facts for the archimedean factor `G`. -/

private lemma one_half_ne_zero : ((1 : ℂ) / 2) ≠ 0 := by
  have h₂ : (2 : ℂ) ≠ 0 := by norm_num
  have h₁ : (1 : ℂ) ≠ 0 := by norm_num
  simpa using div_ne_zero h₁ h₂

private lemma pi_ne_zero_ℂ : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

private lemma cpow_pi_ne_zero (s : ℂ) : (Real.pi : ℂ) ^ (-(s / 2)) ≠ 0 := by
  classical
  have hπ0 : (Real.pi : ℂ) ≠ 0 := pi_ne_zero_ℂ
  have hdef : (Real.pi : ℂ) ^ (-(s / 2))
      = Complex.exp (Complex.log (Real.pi : ℂ) * (-(s / 2))) := by
    simpa [Complex.cpow_def, hπ0]
  have : Complex.exp (Complex.log (Real.pi : ℂ) * (-(s / 2))) ≠ 0 :=
    Complex.exp_ne_zero _
  simpa [hdef] using this


/-! Ext variant without the polynomial factor. -/

/-/ Archimedean factor for the standard completed zeta (no polynomial). -/
def G_ext (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-/ Completed Riemann ξ (ext), defined here as mathlib's completed zeta `Λ(s)`. -/
def riemannXi_ext (s : ℂ) : ℂ := completedRiemannZeta s

/-/ Factorization of ξ_ext on Ω (where `s ≠ 0`): Λ(s) = Γℝ(s) · ζ(s). -/
theorem xi_ext_factorization_on_Ω : ∀ ρ ∈ RH.RS.Ω, riemannXi_ext ρ = G_ext ρ * riemannZeta ρ := by
  intro ρ hΩ
  -- From Ω: (1/2) < ρ.re ⇒ 0 < ρ.re and thus ρ ≠ 0
  have hhalf : (1 / 2 : ℝ) < ρ.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hΩ
  have hReρ_pos : 0 < ρ.re := by
    have : (1 / 2 : ℝ) < ρ.re := hhalf
    linarith
  have hρ_ne : ρ ≠ 0 := by
    intro h0
    have : 0 < (0 : ℝ) := by simpa [h0, Complex.zero_re] using hReρ_pos
    exact (lt_irrefl _) this
  -- Helper: normalize exponent -(ρ/2) = (-ρ)/2
  have neg_div_two (z : ℂ) : -(z / 2) = (-z) / 2 := by
    calc
      -(z / 2) = -(z * (2 : ℂ)⁻¹) := by simpa [div_eq_mul_inv]
      _ = (-z) * (2 : ℂ)⁻¹       := by simpa [neg_mul]
      _ = (-z) / 2               := by simpa [div_eq_mul_inv]
  -- ζ = Λ / Γℝ at ρ ≠ 0
  have hζ : riemannZeta ρ = completedRiemannZeta ρ / Complex.Gammaℝ ρ :=
    riemannZeta_def_of_ne_zero (s := ρ) hρ_ne
  -- Nonvanishing of Γℝ on Ω
  have hΓR_ne : Complex.Gammaℝ ρ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hReρ_pos
  -- Short calc from ζ = Λ/Γℝ avoiding mul_div lemmas and deep simp
  have hcalc : G_ext ρ * riemannZeta ρ = riemannXi_ext ρ := by
    calc
      G_ext ρ * riemannZeta ρ
          = ((Real.pi : ℂ) ^ (-ρ / 2) * Complex.Gamma (ρ / 2)) * riemannZeta ρ := by
                -- align exponent to the normalized form used by Gammaℝ_def
                have hpow : (Real.pi : ℂ) ^ (-ρ / 2) = (Real.pi : ℂ) ^ (-(ρ / 2)) := by
                  simpa [neg_div_two ρ]
                simpa [G_ext, hpow]
      _   = ρ.Gammaℝ * riemannZeta ρ := by
                rw [← Complex.Gammaℝ_def (s := ρ)]
      _   = ρ.Gammaℝ * (completedRiemannZeta ρ / ρ.Gammaℝ) := by
                rw [hζ]
      _   = ρ.Gammaℝ * (completedRiemannZeta ρ * (ρ.Gammaℝ)⁻¹) := by
                rw [div_eq_mul_inv]
      _   = (ρ.Gammaℝ * completedRiemannZeta ρ) * (ρ.Gammaℝ)⁻¹ := by
                rw [mul_assoc]
      _   = (completedRiemannZeta ρ * ρ.Gammaℝ) * (ρ.Gammaℝ)⁻¹ := by
                rw [mul_comm (ρ.Gammaℝ) (completedRiemannZeta ρ)]
      _   = completedRiemannZeta ρ * (ρ.Gammaℝ * (ρ.Gammaℝ)⁻¹) := by
                rw [← mul_assoc]
      _   = completedRiemannZeta ρ * 1 := by
                -- use the group_with_zero cancel lemma directly
                have hcancel : ρ.Gammaℝ * (ρ.Gammaℝ)⁻¹ = (1 : ℂ) :=
                  mul_inv_cancel₀ hΓR_ne
                rw [hcancel]
      _   = completedRiemannZeta ρ := by
                rw [mul_one]
      _   = riemannXi_ext ρ := rfl
  exact hcalc.symm

/-! Nonvanishing for the ext Archimedean factor on Ω. -/
theorem G_ext_nonzero_on_Ω : ∀ ρ ∈ RH.RS.Ω, G_ext ρ ≠ 0 := by
  intro ρ hΩ
  -- Identify with `Gammaℝ ρ` to leverage standard nonvanishing facts
  have hhalf : (1 / 2 : ℝ) < ρ.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hΩ
  have hReρ_pos : 0 < ρ.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  -- Rewrite and conclude
  have : G_ext ρ = Complex.Gammaℝ ρ := by
    rw [G_ext, ← Complex.Gammaℝ_def (s := ρ)]
  have hΓR_ne : Complex.Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos hReρ_pos
  simpa [this]

/-- On Ω, zeros of `riemannXi_ext` coincide with zeros of `riemannZeta`. -/
theorem xi_ext_zeros_eq_zeta_zeros_on_Ω :
  ∀ z ∈ RH.RS.Ω, riemannXi_ext z = 0 ↔ riemannZeta z = 0 := by
  intro z hzΩ
  have hfac : riemannXi_ext z = G_ext z * riemannZeta z :=
    xi_ext_factorization_on_Ω z hzΩ
  have hGnz : G_ext z ≠ 0 := G_ext_nonzero_on_Ω z hzΩ
  constructor
  · intro hXi
    have : G_ext z * riemannZeta z = 0 := by simpa [hfac] using hXi
    have hdisj := mul_eq_zero.mp this
    cases hdisj with
    | inl hG0 => exact (hGnz hG0).elim
    | inr hζ0 => exact hζ0
  · intro hζ
    simpa [hfac, hζ]

-- The ext ξ equals mathlib's completed zeta `
