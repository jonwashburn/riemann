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
  classical
  let Θ : ℂ → ℂ := fun s => (((2 : ℂ) * J s) - 1) / (((2 : ℂ) * J s) + 1)
  have hO_ne_off : ∀ ⦃s : ℂ⦄, s ∈ OffZeros.Ω → O s ≠ 0 := by
    intro s hs
    have hsΩ : s ∈ Ω := by
      change (1 / 2 : ℝ) < s.re
      simpa [OffZeros.Ω] using hs
    exact hO_ne hsΩ
  have hdet2_ne_off : ∀ ⦃s : ℂ⦄, s ∈ OffZeros.Ω → det2 s ≠ 0 := by
    intro s hs
    have hsΩ : s ∈ Ω := by
      change (1 / 2 : ℝ) < s.re
      simpa [OffZeros.Ω] using hs
    exact hdet2_ne hsΩ
  have hXi_eq_Gζ_off : ∀ ⦃s : ℂ⦄, s ∈ OffZeros.Ω → riemannXi_ext s = G s * riemannZeta s := by
    intro s hs
    have hsΩ : s ∈ Ω := by
      change (1 / 2 : ℝ) < s.re
      simpa [OffZeros.Ω] using hs
    exact hXi_eq_Gζ hsΩ
  have hΘSchur_off : OffZeros.IsSchurOn Θ OffZeros.Ω := by
    intro s hs
    have hsΩ : s ∈ Ω := by
      change (1 / 2 : ℝ) < s.re
      simpa [OffZeros.Ω] using hs
    simpa [Θ] using hΘSchur s hsΩ
  have hΘA_offXi_off :
      AnalyticOn ℂ Θ (OffZeros.Ω \ OffZeros.Z riemannXi_ext) := by
    simpa [Θ, OffZeros.Ω, OffZeros.Z, Ω] using hΘA_offXi
  have hΘ_lim1_off :
      ∀ ⦃ρ : ℂ⦄,
        ρ ∈ OffZeros.Ω → riemannXi_ext ρ = 0 →
          Tendsto Θ
            (nhdsWithin ρ (OffZeros.Ω \ OffZeros.Z riemannXi_ext))
            (nhds (1 : ℂ)) := by
    intro ρ hρ hξρ
    have hρΩ : ρ ∈ Ω := by
      change (1 / 2 : ℝ) < ρ.re
      simpa [OffZeros.Ω] using hρ
    have := hΘ_lim1_at_ξzero (ρ := ρ) hρΩ hξρ
    simpa [Θ, OffZeros.Ω, OffZeros.Z, Ω] using this
  have hN_ne_off_assm_off :
      ∀ ⦃s : ℂ⦄,
        s ∈ (OffZeros.Ω \ OffZeros.Z riemannZeta) →
          (Θ s * G s / riemannXi_ext s) ≠ 0 := by
    intro s hs
    have hsΩ : s ∈ Ω := by
      change (1 / 2 : ℝ) < s.re
      simpa [OffZeros.Ω] using hs.1
    have hsNot : s ∉ {z | riemannZeta z = 0} := by
      simpa [OffZeros.Z, Set.mem_setOf_eq] using hs.2
    have h := hN_ne_off_assm (s := s) ⟨hsΩ, hsNot⟩
    simpa [Θ] using h
  -- Build the Schur decomposition data via the provided constructor
  let data :=
    OffZeros.ZetaSchurDecompositionOffZeros.ofEqOffZeros
      (riemannZeta := riemannZeta) (riemannXi := riemannXi_ext)
      det2 O G J
      (by simpa [OffZeros.Ω, Ω] using hdet2A)
      (by simpa [OffZeros.Ω, Ω] using hOA)
      (by simpa [OffZeros.Ω, Ω] using hGA)
      (by simpa [OffZeros.Ω, Ω] using hXiA)
      hO_ne_off
      hdet2_ne_off
      (by
        intro s hs
        -- align OffZeros domain to the global `Ω \ {z | ζ z = 0}`
        have hsΩ : s ∈ Ω := by
          change (1 / 2 : ℝ) < s.re
          simpa [OffZeros.Ω] using hs.1
        have hsNot : s ∉ {z | riemannZeta z = 0} := by
          simpa [OffZeros.Z, Set.mem_setOf_eq] using hs.2
        exact hG_ne_offζ ⟨hsΩ, hsNot⟩)
      (by
        intro s hs
        have hsΩ : s ∈ Ω := by
          change (1 / 2 : ℝ) < s.re
          simpa [OffZeros.Ω] using hs.1
        have hsNot : s ∉ {z | riemannXi_ext z = 0} := by
          simpa [OffZeros.Z, Set.mem_setOf_eq] using hs.2
        exact hJ_def_offXi (s := s) ⟨hsΩ, hsNot⟩)
      hXi_eq_Gζ_off
      hΘSchur_off
      hΘA_offXi_off
      hΘ_lim1_off
      (by
        intro s hs
        exact hN_ne_off_assm_off (s := s) hs)
  -- Convert the ξ-removable existence into a ζ-assignment
  have hZerosEq : ∀ z ∈ Ω, riemannXi_ext z = 0 ↔ riemannZeta z = 0 := by
    intro z hz; constructor
    · intro hξ
      -- Use ξ = G·ζ on Ω and close by cases on the product
      have hXi_eq : riemannXi_ext z = G z * riemannZeta z := hXi_eq_Gζ (s := z) hz
      have hProd : G z * riemannZeta z = 0 := by simpa [hXi_eq] using hξ
      rcases mul_eq_zero.mp hProd with hG0 | hζ0
      · -- if G z = 0, then ζ z must be 0 else contradict nonvanishing of G off ζ-zeros
        by_cases hzeta : riemannZeta z = 0
        · exact hzeta
        · have hGne : G z ≠ 0 := hG_ne_offζ ⟨hz, by simpa [Set.mem_setOf_eq] using hzeta⟩
          exact (hGne hG0).elim
      · exact hζ0
    · intro hζ
      have h := hXi_eq_Gζ (s := z) hz
      simpa [h, hζ]
  let assignζ :=
    OffZeros.assign_fromXiRemovable_exists
      (riemannZeta := riemannZeta) (riemannXi := riemannXi_ext)
      (Θ := Θ) hZerosEq existsRemXi
  -- Apply globalization to conclude nonvanishing on Ω
  exact no_offcritical_zeros_from_schur data.Θ
    (by
      -- data.hΘSchur is on Ω; restrict to Ω \ Z(ζ)
      intro z hz
      have hzΩ : z ∈ OffZeros.Ω := by
        change (1 / 2 : ℝ) < z.re
        simpa [Ω] using hz.1
      exact data.hΘSchur hzΩ)
    (by
      intro ρ hρΩ hζρ
      have hρΩ' : ρ ∈ OffZeros.Ω := by
        change (1 / 2 : ℝ) < ρ.re
        simpa [Ω] using hρΩ
      exact assignζ ρ hρΩ' hζρ)

end RS
end RH
