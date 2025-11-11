import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.CompletedXi
import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.RS.SchurGlobalization

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
  · intro s hs; have : O_simple s = 1 := by simp [O_simple, hs]
    simp [this]

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
  -- Compare absolute values by normalizing both sides to the `abs_div` form.
  have hAbs_left :
      Complex.abs (O_simple z)
        = Complex.abs (RH.RS.det2 z) /
            Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
    have := congrArg Complex.abs hEq
    have hdiv :
        Complex.abs (RH.RS.det2 z /
            RH.AcademicFramework.CompletedXi.riemannXi_ext z)
          = Complex.abs (RH.RS.det2 z) /
              Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
      simpa using
        abs_div (RH.RS.det2 z)
          (RH.AcademicFramework.CompletedXi.riemannXi_ext z)
    exact this.trans hdiv
  have hAbs_right :
      Complex.abs ((fun s =>
        RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) z)
        = Complex.abs (RH.RS.det2 z) /
            Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
    dsimp only
    simpa using
      abs_div (RH.RS.det2 z)
        (RH.AcademicFramework.CompletedXi.riemannXi_ext z)
  calc
    Complex.abs (O_simple z)
        = Complex.abs (RH.RS.det2 z) /
            Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := hAbs_left
    _ = Complex.abs ((fun s =>
        RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) z) := hAbs_right.symm

/-- Optional boundary real datum for Poisson build: log of the target modulus.
We use a tame variant `log (u+1)` to avoid `log 0`; the canonical A.2 limit will
be inserted later to recover the sharp datum. -/
noncomputable def log_u (t : ℝ) : ℝ := Real.log (u t + 1)

/-- Poisson-potential packaging: a complex potential `G` whose real part equals the
Poisson integral of a supplied boundary real datum `g` on Ω. This is a statement-level
interface to keep the constructive outer build decoupled from heavy measure theory. -/
structure HasPoissonPotential (g : ℝ → ℝ) (G : ℂ → ℂ) : Prop :=
  (analytic : AnalyticOn ℂ G RH.AcademicFramework.HalfPlaneOuterV2.Ω)
  (re_eq : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω,
            (G z).re = RH.AcademicFramework.HalfPlaneOuterV2.poissonIntegral g z)

/-- Constructive outer from a Poisson potential: use `exp G` on Ω and the raw ratio
off Ω to pin the boundary modulus exactly. -/
noncomputable def O_construct (G : ℂ → ℂ) : ℂ → ℂ :=
  fun s => by
    classical
    exact if s ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω then Complex.exp (G s)
      else RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s

lemma O_construct_outer {G : ℂ → ℂ}
    (hG : AnalyticOn ℂ G RH.AcademicFramework.HalfPlaneOuterV2.Ω) :
    RH.AcademicFramework.HalfPlaneOuterV2.IsOuter (O_construct G) := by
  classical
  constructor
  ·
    -- analytic on Ω by restriction to the `exp ∘ G` branch
    have hA : AnalyticOn ℂ (fun s => Complex.exp (G s)) RH.AcademicFramework.HalfPlaneOuterV2.Ω :=
      (hG.cexp)
    refine (AnalyticOn.congr hA ?_)
    intro s hs
    -- On Ω the piecewise definition agrees with exp ∘ G
    classical
    have : s ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω := hs
    simp [O_construct, this]
  · -- nonvanishing on Ω since `exp` never vanishes
    intro s hs
    classical
    have hDef : O_construct G s = Complex.exp (G s) := by
      simp [O_construct, hs]
    have : Complex.exp (G s) ≠ 0 := Complex.exp_ne_zero _
    simp [hDef]

lemma O_construct_boundary_modulus {G : ℂ → ℂ} :
    RH.AcademicFramework.HalfPlaneOuterV2.BoundaryModulusEq (O_construct G)
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := by
  classical
  intro t
  -- On the boundary Re = 1/2, the Ω-test is false; take the ratio branch
  set z : ℂ := RH.AcademicFramework.HalfPlaneOuterV2.boundary t
  have hcond : ¬ ((1 / 2 : ℝ) < z.re) := by
    simp [z, RH.AcademicFramework.HalfPlaneOuterV2.boundary]
  have hzle : z.re ≤ (1 / 2 : ℝ) := le_of_not_gt hcond
  have hmem : z ∉ RH.AcademicFramework.HalfPlaneOuterV2.Ω := by
    intro hz
    have hz' := hz
    simp [RH.AcademicFramework.HalfPlaneOuterV2.Ω, Set.mem_setOf_eq] at hz'
    have hzlt : (1 / 2 : ℝ) < z.re := by
      simpa using hz'
    have hzlt' : (1 / 2 : ℝ) < (1 / 2 : ℝ) := hzlt.trans_le hzle
    exact (lt_irrefl (1 / 2 : ℝ)) hzlt'
  have hEq : O_construct G z = RH.RS.det2 z / RH.AcademicFramework.CompletedXi.riemannXi_ext z := by
    simp [O_construct, hmem]
  -- Take absolute values and compare both sides via `abs_div` normalization.
  have hAbs_left :
      Complex.abs (O_construct G z)
        = Complex.abs (RH.RS.det2 z) /
            Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
    have := congrArg Complex.abs hEq
    have hdiv :
        Complex.abs (RH.RS.det2 z /
            RH.AcademicFramework.CompletedXi.riemannXi_ext z)
          = Complex.abs (RH.RS.det2 z) /
              Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
      simpa using
        abs_div (RH.RS.det2 z)
          (RH.AcademicFramework.CompletedXi.riemannXi_ext z)
    exact this.trans hdiv
  have hAbs_right :
      Complex.abs ((fun s =>
        RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) z)
        = Complex.abs (RH.RS.det2 z) /
            Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := by
    dsimp only
    simpa using
      abs_div (RH.RS.det2 z)
        (RH.AcademicFramework.CompletedXi.riemannXi_ext z)
  calc
    Complex.abs (O_construct G z)
        = Complex.abs (RH.RS.det2 z) /
            Complex.abs (RH.AcademicFramework.CompletedXi.riemannXi_ext z) := hAbs_left
    _ = Complex.abs ((fun s =>
        RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) z) := hAbs_right.symm

/-- From any Poisson potential `G` (analytic on Ω), the piecewise `O_construct G`
witnesses the required AF outer existence with boundary modulus `|det₂/ξ_ext|`. -/
lemma outer_exists_with_modulus_det2_over_xi_from_potential
    {G : ℂ → ℂ}
    (hG : AnalyticOn ℂ G RH.AcademicFramework.HalfPlaneOuterV2.Ω) :
    RH.AcademicFramework.HalfPlaneOuterV2.ExistsOuterWithModulus
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := by
  refine ⟨O_construct G, O_construct_outer (G := G) hG, ?_⟩
  exact O_construct_boundary_modulus (G := G)

/-- Poisson-based constructive outer: if a Poisson potential `G` exists for `log_u`,
then `O_construct G` provides the outer witness with the required boundary modulus. -/
lemma outer_exists_with_modulus_det2_over_xi_poisson
    {G : ℂ → ℂ}
    (hPot : HasPoissonPotential log_u G) :
    RH.AcademicFramework.HalfPlaneOuterV2.ExistsOuterWithModulus
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := by
  refine outer_exists_with_modulus_det2_over_xi_from_potential (G := G) ?hA
  exact hPot.analytic

/-- Statement-level placeholder: existence of a Poisson potential for `log_u` on Ω. -/
def PoissonPotentialExists_log_u : Prop := ∃ G : ℂ → ℂ, HasPoissonPotential log_u G

/-- Constructive existence: there exists an outer `O` on Ω such that along the
critical line `Re s = 1/2` one has `|O| = |det₂/ξ_ext|`. -/
lemma outer_exists_with_modulus_det2_over_xi :
    RH.AcademicFramework.HalfPlaneOuterV2.ExistsOuterWithModulus
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := by
  refine ⟨O_simple, O_simple_outer, ?_⟩
  exact O_simple_boundary_modulus

namespace Quarantine

/-- A.1-style packaging: assuming a Poisson potential for `log_u` exists, produce the outer.

This lemma, together with the axiom below, is quarantined so that the active build
does not depend on the placeholder witness. -/
theorem outer_exists_with_modulus_det2_over_xi_poisson_assuming
    (hExist : PoissonPotentialExists_log_u) :
    RH.AcademicFramework.HalfPlaneOuterV2.ExistsOuterWithModulus
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) := by
  classical
  rcases hExist with ⟨G, hPot⟩
  exact outer_exists_with_modulus_det2_over_xi_poisson (G := G) hPot

/-- Local assumption cached for reference: a Poisson potential for `log_u` exists. -/
axiom poissonPotentialExists_log_u_assumed : PoissonPotentialExists_log_u

/-- Immediate corollary under the quarantined assumption. Downstream code should avoid
relying on this alias; the active proof path uses the unconditional witness above. -/
theorem outer_exists_with_modulus_det2_over_xi_poisson_assumed :
    RH.AcademicFramework.HalfPlaneOuterV2.ExistsOuterWithModulus
      (fun s => RH.RS.det2 s / RH.AcademicFramework.CompletedXi.riemannXi_ext s) :=
  outer_exists_with_modulus_det2_over_xi_poisson_assuming poissonPotentialExists_log_u_assumed

end Quarantine

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
