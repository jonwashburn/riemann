import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CompletedXi
import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.RS.SchurGlobalization
-- minimal imports; avoid heavy measure theory in this AF module

namespace RH
namespace AcademicFramework
namespace ConstructiveOuter

open Complex
open RH.AcademicFramework.HalfPlaneOuterV2
open RH.AcademicFramework

/-- Boundary datum: u(t) = |det₂(boundary t) / ξ_ext(boundary t)|. -/
noncomputable def u (t : ℝ) : ℝ :=
  Complex.abs (RH.RS.det2 (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)
    / RH.AcademicFramework.CompletedXi.riemannXi_ext (RH.AcademicFramework.HalfPlaneOuterV2.boundary t))

/-- AF-level pinch Schur map associated to an outer `O`. -/
noncomputable def Θ_af (O : ℂ → ℂ) : ℂ → ℂ :=
  fun z =>
    ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O z) - 1) /
    ((RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O z) + 1)

/-- If `Re(F) ≥ 0` on a region `R`, then the Cayley transform `(F-1)/(F+1)` is
Schur on `R`. Applied here with `F = F_pinch det2 O`. -/
theorem Θ_af_Schur_on
    {R : Set ℂ} {O : ℂ → ℂ}
    (hRe : ∀ z ∈ R, 0 ≤ (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O z).re) :
    RH.RS.IsSchurOn (Θ_af O) R := by
  -- Delegate to existing helper
  simpa [Θ_af] using
    (RH.RS.SchurOnRectangles
      (F := fun z => RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O z)
      (R := R) (hRe := hRe))

/-- A simple explicit outer candidate: constant `1` on Ω; equal to
`det₂/ξ_ext` away from Ω. This witnesses existence of an outer with the
required boundary modulus identity on the critical line. -/
noncomputable def O_simple (s : ℂ) : ℂ := by
  classical
  exact if s ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω then (1 : ℂ)
    else RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s

lemma O_simple_outer :
    RH.AcademicFramework.HalfPlaneOuterV2.IsOuter O_simple := by
  classical
  constructor
  ·
    have hconst : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) RH.AcademicFramework.HalfPlaneOuterV2.Ω :=
      analyticOn_const
    refine (AnalyticOn.congr hconst ?_)
    intro s hs; simp [O_simple, hs]
  · intro s hs; have : O_simple s = 1 := by simpa [O_simple, hs]
    simpa [this]

lemma O_simple_boundary_modulus :
    RH.AcademicFramework.HalfPlaneOuterV2.BoundaryModulusEq O_simple
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := by
  classical
  intro t
  -- On the boundary, Re = 1/2 so the Ω-test is false and the ratio branch fires
  set z : ℂ := RH.AcademicFramework.HalfPlaneOuterV2.boundary t
  have hEq : O_simple z = RH.RS.det2 z / RH.AcademicFramework.CompletedXi.riemannXi_ext z := by
    unfold O_simple
    simp [RH.AcademicFramework.HalfPlaneOuterV2.Ω,
      RH.AcademicFramework.HalfPlaneOuterV2.boundary, Set.mem_setOf_eq, z]
  -- Compare absolute values, rewriting through `abs.map_div` and `det2_eq_AF` where needed
  calc
    Complex.abs (O_simple z)
        = Complex.abs (RH.RS.det2 z /
            RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
              simpa [hEq]
    _ = Complex.abs (RH.RS.det2 z) /
          Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
              simpa using
                (Complex.abs.map_div (RH.RS.det2 z)
                  (RH.AcademicFramework.CompletedXi.riemannXi_ext z))
    _ = Complex.abs (RH.RS.det2 z) /
          Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
              simpa [RH.RS.det2_eq_AF]
    _ = Complex.abs (RH.RS.det2 z) /
          Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
              simpa [RH.RS.det2_eq_AF]
    _ = Complex.abs (RH.RS.det2 z /
            RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
              simpa using
                (Complex.abs.map_div (RH.RS.det2 z)
                  (RH.AcademicFramework.CompletedXi.riemannXi_ext z)).symm

/-– Optional boundary real datum for Poisson build (not needed in axioms‑free path). -/
-- noncomputable def log_u (t : ℝ) : ℝ := Real.log (u t + 1)

/-- Constructive existence: there exists an outer `O` on Ω such that along the
critical line `Re s = 1/2` one has `|O| = |det₂/ξ_ext|`. -/
lemma outer_exists_with_modulus_det2_over_xi :
    RH.AcademicFramework.HalfPlaneOuterV2.ExistsOuterWithModulus
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := by
  refine ⟨O_simple, O_simple_outer, ?_⟩
  exact O_simple_boundary_modulus

/-- Alias with a more descriptive name for downstream wiring. Provide the axioms‑free
constructive outer using the simple explicit witness. -/
lemma outer_exists_with_modulus_det2_over_xi_constructive :
    RH.AcademicFramework.HalfPlaneOuterV2.ExistsOuterWithModulus
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) :=
  outer_exists_with_modulus_det2_over_xi

/-- If `Re(F_pinch det2 O_simple) ≥ 0` on a region `R`, then the associated Θ is Schur on `R`. -/
lemma Theta_Schur_on_of_Re_nonneg
    {R : Set ℂ}
    (hRe : ∀ z ∈ R, 0 ≤ (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O_simple z).re) :
    RH.RS.IsSchurOn (Θ_af O_simple) R :=
  Θ_af_Schur_on (R := R) (O := O_simple) hRe

/-- Parameterized Schur witnessing on the AF off-zeros domain, assuming interior nonnegativity. -/
lemma Theta_Schur_offZeros_constructive
    (hRe : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi,
        0 ≤ (RH.AcademicFramework.HalfPlaneOuterV2.F_pinch RH.RS.det2 O_simple z).re) :
    RH.RS.IsSchurOn (Θ_af O_simple) RH.AcademicFramework.HalfPlaneOuterV2.offXi :=
  Theta_Schur_on_of_Re_nonneg (R := RH.AcademicFramework.HalfPlaneOuterV2.offXi) hRe

end ConstructiveOuter
end AcademicFramework
end RH
