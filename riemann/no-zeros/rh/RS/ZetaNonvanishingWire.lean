import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.Det2Outer
import rh.RS.OffZerosBridge
import rh.RS.SchurGlobalization
import rh.academic_framework.CompletedXi

noncomputable section

open Set Complex Filter RH.RS RH.AcademicFramework.CompletedXi

namespace RH
namespace RS

/-- Given the Cayley-based data and removable assignment across ξ, conclude ζ ≠ 0 on Ω. -/
theorem zeta_nonzero_on_Ω_from_cayley
  (det2 O G J : ℂ → ℂ)
  (hdet2A : AnalyticOn ℂ det2 Ω)
  (hOA : AnalyticOn ℂ O Ω)
  (hGA : AnalyticOn ℂ G Ω)
  (hXiA : AnalyticOn ℂ riemannXi_ext Ω)
  (hO_ne : ∀ {s}, s ∈ Ω → O s ≠ 0)
  (hdet2_ne : ∀ {s}, s ∈ Ω → det2 s ≠ 0)
  (hG_ne_offζ : ∀ {s}, s ∈ (Ω \ {z | riemannZeta z = 0}) → G s ≠ 0)
  (hJ_def_offXi : ∀ {s}, s ∈ (Ω \ {z | riemannXi_ext z = 0}) → J s = det2 s / (O s * riemannXi_ext s))
  (hXi_eq_Gζ : ∀ {s}, s ∈ Ω → riemannXi_ext s = G s * riemannZeta s)
  (hΘSchur : IsSchurOn (fun s => (((2 : ℂ) * J s) - 1) / (((2 : ℂ) * J s) + 1)) Ω)
  (hΘA_offXi : AnalyticOn ℂ (fun s => (((2 : ℂ) * J s) - 1) / (((2 : ℂ) * J s) + 1)) (Ω \ {z | riemannXi_ext z = 0}))
  (hΘ_lim1_at_ξzero : ∀ {ρ}, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      Tendsto (fun s => (((2 : ℂ) * J s) - 1) / (((2 : ℂ) * J s) + 1)) (nhdsWithin ρ (Ω \ {z | riemannXi_ext z = 0})) (nhds (1 : ℂ)))
  (hN_ne_off_assm : ∀ {s}, s ∈ (Ω \ {z | riemannZeta z = 0}) →
      (let Θ := fun u => (((2 : ℂ) * J u) - 1) / (((2 : ℂ) * J u) + 1);
       (Θ s) * G s / riemannXi_ext s ≠ 0))
  (existsRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ (fun s => (((2 : ℂ) * J s) - 1) / (((2 : ℂ) * J s) + 1)) (U \ {ρ}) ∧
        EqOn (fun s => (((2 : ℂ) * J s) - 1) / (((2 : ℂ) * J s) + 1)) g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : ∀ ρ ∈ Ω, riemannZeta ρ ≠ 0 := by
  -- Define Θ
  let Θ : ℂ → ℂ := fun s => (((2 : ℂ) * J s) - 1) / (((2 : ℂ) * J s) + 1)
  -- Build the Schur decomposition data via the provided constructor
  let data := OffZeros.ZetaSchurDecompositionOffZeros.ofEqOffZeros
    det2 O G J hdet2A hOA hGA hXiA hO_ne hdet2_ne hG_ne_offζ hJ_def_offXi hXi_eq_Gζ
    (by simpa [Θ] using hΘSchur)
    (by simpa [Θ] using hΘA_offXi)
    (by simpa [Θ] using hΘ_lim1_at_ξzero)
    (by
      intro s hs
      have := hN_ne_off_assm (s := s) hs
      simpa [Θ] using this)
  -- Convert the ξ-removable existence into a ζ-assignment
  have hZerosEq : ∀ z ∈ Ω, riemannXi_ext z = 0 ↔ riemannZeta z = 0 := by
    intro z hz; constructor
    · intro hξ
      have hG : G z ≠ 0 := hG_ne_offζ ⟨hz, by simpa [Set.mem_setOf_eq, hξ]⟩
      have h := hXi_eq_Gζ (s := z) hz
      have : G z * riemannZeta z = 0 := by simpa [h, hξ]
      rcases mul_eq_zero.mp this with hG0 | hζ0
      · exact False.elim (hG hG0)
      · exact hζ0
    · intro hζ
      have h := hXi_eq_Gζ (s := z) hz
      simpa [h, hζ]
  let assignζ := OffZeros.assign_fromXiRemovable_exists (riemannZeta := riemannZeta)
    (Θ := Θ) hZerosEq existsRemXi
  -- Apply globalization to conclude nonvanishing on Ω
  exact no_offcritical_zeros_from_schur data.Θ
    (by
      -- data.hΘSchur is on Ω; restrict to Ω \ Z(ζ)
      intro z hz; exact data.hΘSchur z hz.1)
    (by
      intro ρ hρΩ hζρ; exact assignζ ρ hρΩ hζρ)

end RS
end RH
