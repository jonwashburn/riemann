import rh.Proof.Main
import rh.RS.PinchIngredients

/-!
Final wiring exports: clean, stable entry points that expose Mathlib's
`RiemannZeta.RiemannHypothesis` through the assembled RS/AF routes.

These theorems do not introduce any new assumptions beyond those
appearing in `rh/Proof/Main.lean`. They are placed in a thin wrapper
module so downstream users can import only this file for the final API.
-/

open RH.AcademicFramework.CompletedXi

namespace RH.Proof.Export

open RH.Proof
open RH.Proof.Final


-- Unconditional pipeline readiness via the certificate layer
abbrev PipelineReady := RH.Proof.PipelineReady

theorem pipeline_ready_unconditional : PipelineReady := RH.Proof.pipeline_ready_unconditional

-- Final certificate-driven alias to Mathlib's RiemannHypothesis
@[simp] theorem RiemannHypothesis_final (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RH_from_pinch_certificate C

@[simp] theorem RH (C : RH.RS.PinchCertificateExt) : RiemannHypothesis :=
  RiemannHypothesis_final C

-- Certificate route variants re-exported for convenience
@[simp] theorem RiemannHypothesis_from_certificate_route
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hTrans : ∀ z ∈ RH.RS.Ω,
      0 ≤ ((2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) z)).re)
  (hKxi : RH.Cert.KxiWhitney.KxiBound (α := (3 : ℝ) / 5) (c := (1 : ℝ)))
  (hPinned : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ (Θ_analytic_off_rho : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (U \ {ρ}))
          (u : ℂ → ℂ)
          (hEq : Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}))
          (hu0 : Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)))
          (z_nontrivial : ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) z ≠ 1),
          True)
  : RiemannHypothesis :=
  by
    -- Repackage pinned data into the shape expected by the theorem
    let hPinned' : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
        ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
          (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
          AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (U \ {ρ}) ∧
          ∃ u : ℂ → ℂ,
            Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
              (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
            Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
            ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) z ≠ 1 := by
      intro ρ hΩ hXi
      rcases hPinned ρ hΩ hXi with
        ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
         Θ_analytic_off_rho, u, hEq, hu0, z_nontrivial, _triv⟩
      rcases z_nontrivial with ⟨z, hzU, hzNe, hΘz⟩
      exact ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
        Θ_analytic_off_rho,
        ⟨u, hEq, hu0, ⟨z, hzU, hzNe, hΘz⟩⟩⟩
    exact RiemannHypothesis_from_poisson_and_pinned' hOuterExist hTrans hPinned'

-- Subset-representation route
@[simp] theorem RiemannHypothesis_from_certificate_rep_on_via_cov
  (hOuterExist : RH.RS.OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hPoisson : ∀ z ∈ RH.RS.Ω,
      0 ≤ ((2 : ℂ) * (RH.RS.J_pinch RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist) z)).re)
  (hKxi : RH.Cert.KxiWhitney.KxiBound (α := (3 : ℝ) / 5) (c := (1 : ℝ)))
  (hPinned : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ (Θ_analytic_off_rho : AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (U \ {ρ}))
          (u : ℂ → ℂ)
          (hEq : Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}))
          (hu0 : Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)))
          (z_nontrivial : ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) z ≠ 1),
          True)
  : RiemannHypothesis :=
  by
    -- Repackage pinned data into the expected conjunctive form
    let hPinned' : ∀ ρ, ρ ∈ RH.RS.Ω → riemannXi_ext ρ = 0 →
        ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ RH.RS.Ω ∧ ρ ∈ U ∧
          (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
          AnalyticOn ℂ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) (U \ {ρ}) ∧
          ∃ u : ℂ → ℂ,
            Set.EqOn (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist))
              (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
            Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
            ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Θ_pinch_of RH.RS.det2 (RH.RS.OuterHalfPlane.choose_outer hOuterExist)) z ≠ 1 := by
      intro ρ hΩ hXi
      rcases hPinned ρ hΩ hXi with
        ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
         Θ_analytic_off_rho, u, hEq, hu0, z_nontrivial, _triv⟩
      rcases z_nontrivial with ⟨z, hzU, hzNe, hΘz⟩
      exact ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
        Θ_analytic_off_rho,
        ⟨u, hEq, hu0, ⟨z, hzU, hzNe, hΘz⟩⟩⟩
    exact RiemannHypothesis_from_poisson_and_pinned' hOuterExist hPoisson hPinned'

/-
-- Minimal API export to Mathlib wrapper from CR-outer route (commented out - requires CRGreenOuter)
@[simp] theorem RiemannHypothesis_mathlib_from_CR_outer_ext
  (choose : ∀ ρ, ρ ∈ RH.RS.Ω → riemannZeta ρ = 0 →
      RH.RS.OffZeros.LocalData (riemannZeta := riemannZeta)
        (Θ := RH.RS.Θ_of RH.RS.CRGreenOuterData) (ρ := ρ))
  (hGnz : ∀ ρ ∈ RH.RS.Ω, G_ext ρ ≠ 0)
  : RiemannHypothesis :=
  RH.Proof.Final.RiemannHypothesis_mathlib_from_CR_outer_ext choose hGnz
-/

namespace RH
namespace Proof
namespace Final

-- Re-export the certificate-to-RH final wrapper for convenience
export RH.RS (certificate_from_pinch_ingredients)

end Final
end Proof
end RH
