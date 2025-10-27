import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.RS.PinchCertificate
-- KxiPPlus provides the abstract `(P+)` predicate; kept minimal
import rh.Cert.KxiPPlus
-- import rh.RS.PinchIngredients -- unused here; keep wrappers lightweight
import rh.academic_framework.CompletedXi
-- avoid pulling the full proof main in RS wrappers to keep dev build light
-- keep packaging decoupled to avoid cycles; consumers can import XiExtBridge directly if needed
import rh.academic_framework.HalfPlaneOuterV2

/-!
# Pinch wrappers: encode manuscript implications and feed the builder

This file provides light wrappers encoding the two manuscript implications:

- (Wedge → Poisson) interior positivity on `Ω \ Z(ξ_ext)` for
  `F := 2 · J_pinch` (we take the Poisson passage as an input statement);
- (Pinned removable) existence of a removable extension `g` across each
  `ξ_ext` zero with `g ρ = 1` and nontriviality.

These wrappers then feed directly into the `buildPinchCertificate` constructor
and the final `RH` conclusion wrapper.
-/

noncomputable section

namespace RH
namespace RS

open Complex Set RH.AcademicFramework.CompletedXi
open RH.AcademicFramework.HalfPlaneOuterV2

local notation "Ω" => RH.RS.Ω

/-- From Poisson interior positivity for
`F := 2 · J_pinch det2 O` on `Ω`, deduce the restricted off-zeros form. -/
def hRe_offXi_from_poisson
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (hPoisson : ∀ z ∈ Ω,
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re)
  : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi,
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re := by
  intro z hz
  exact hPoisson z (RH.AcademicFramework.HalfPlaneOuterV2.offXi_subset_Ω hz)
/-! ## Wiring (P+) to interior positivity via Poisson transport -/

/-- Bridge: convert certificate `(P+)` to the AF boundary-positivity predicate. -/
private def boundaryPositive_of_PPlus
  (F : ℂ → ℂ) (hP : RH.Cert.PPlus F) :
  RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive F :=
  by
    -- `BoundaryPositive` uses `boundary t = (1/2 : ℝ) + I * (t : ℂ)`
    -- Cert's `(P+)` uses `Complex.mk (1/2) t`
    have hcert : ∀ᵐ t : ℝ, 0 ≤ (F (Complex.mk (1/2) t)).re := hP
    -- Prove pointwise equality: Complex.mk (1/2) t = (1/2 : ℝ) + I * (t : ℂ)
    have mk_eq : ∀ t, Complex.mk (1/2) t = (1/2 : ℝ) + I * (t : ℂ) := by
      intro t
      apply Complex.ext
      · simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re]
      · simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im]
    -- Transport the a.e. statement
    have hbd : ∀ᵐ t : ℝ, 0 ≤ (F (RH.AcademicFramework.HalfPlaneOuterV2.boundary t)).re := by
      refine hcert.mono ?_
      intro t ht
      -- boundary t is definitionally (1/2 : ℝ) + I * (t : ℂ)
      have hb : RH.AcademicFramework.HalfPlaneOuterV2.boundary t = (1/2 : ℝ) + I * (t : ℂ) := rfl
      -- Rewrite ht using mk_eq
      have ht' : 0 ≤ (F ((1/2 : ℝ) + I * (t : ℂ))).re := by
        rw [← mk_eq t]
        exact ht
      rw [← hb] at ht'
      exact ht'
    simpa [RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive] using hbd

/-- From (P+) and a Poisson representation on the off-zeros set, deduce
interior nonnegativity of `F := 2·J_pinch det2 O` on `offXi`. -/
def hRe_offXi_from_PPlus_via_transport
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (hRepOn : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn (F_pinch det2 (Classical.choose hOuter))
              RH.AcademicFramework.HalfPlaneOuterV2.offXi)
  (hPPlus : RH.Cert.PPlus (fun z => (2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)))
  : ∀ z ∈ RH.AcademicFramework.HalfPlaneOuterV2.offXi,
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re := by
  have hBP : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive (F_pinch det2 (Classical.choose hOuter)) :=
    boundaryPositive_of_PPlus _ hPPlus
  have hTrans := RH.AcademicFramework.HalfPlaneOuterV2.poissonTransportOn
    (F := F_pinch det2 (Classical.choose hOuter)) hRepOn hBP
  intro z hz
  simpa [F_pinch] using hTrans z hz

/-- Build a pinch certificate using (P+) threaded through Poisson transport on the
off-zeros set, plus pinned–removable data. -/
def pinch_certificate_from_PPlus_transport_and_pinned
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (hRepOn : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn (F_pinch det2 (Classical.choose hOuter))
              RH.AcademicFramework.HalfPlaneOuterV2.offXi)
  (hPPlus : RH.Cert.PPlus (fun z => (2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)))
  (hPinned : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) z ≠ 1)
  : PinchCertificateExt := by
  classical
  -- Ingredient 1: interior positivity on offXi via transport
  let hRe_offXi := hRe_offXi_from_PPlus_via_transport hOuter hRepOn hPPlus
  -- Ingredient 2: pinned–removable across each ξ_ext zero (packaged)
  let hRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
    intro ρ hΩ hXi
    rcases hPinned ρ hΩ hXi with
      ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi,
       hThetaU, u, hEq, hu0, z, hzU, hzneq, hThetaz⟩
    classical
    let Theta : ℂ → ℂ := RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))
    let g : ℂ → ℂ := Function.update Theta ρ (1 : ℂ)
    have hEqOn : Set.EqOn Theta g (U \ {ρ}) := by
      intro w hw; simp [g, Function.update_noteq hw.2]
    have hval : g ρ = 1 := by simp [g]
    have hgU : AnalyticOn ℂ g U :=
      RH.RS.analyticOn_update_from_pinned (U := U) (ρ := ρ) (Θ := Theta) (u := u)
        hUopen hρU hThetaU hEq hu0
    -- Nontriviality: since z ≠ ρ and Theta z ≠ 1, we get g z ≠ 1
    have hgz_ne1 : g z ≠ 1 := by
      have : g z = Theta z := by simp [g, Function.update_noteq hzneq]
      intro hz1; exact hThetaz (by simpa [this] using hz1)
    exact ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi,
      ⟨g, hgU, hThetaU, hEqOn, hval, z, hzU, hgz_ne1⟩⟩
  -- Build the certificate
  exact RH.RS.buildPinchCertificate hOuter hRe_offXi hRemXi


/-- Pass pinned–removable local data for
`Theta := Theta_of_J (J_pinch det2 (choose O))` directly as the `existsRemXi` ingredient. -/
def hRemXi_from_pinned
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  -- Pinned data: for each ξ_ext-zero ρ pick isolating U, Theta-analytic off ρ,
  -- and a u-function with Theta = (1-u)/(1+u) on U\{ρ} and u → 0 on 𝓝[U\{ρ}] ρ,
  -- plus a nontrivial Theta z ≠ 1.
  (hPinned : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter)))
            (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) z ≠ 1)
  : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) (U \ {ρ}) ∧
          Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hXi
  -- Unpack pinned data, then use the removable-update lemma to build g
  rcases hPinned ρ hΩ hXi with
    ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, hThetaU, u, hEq, hu0, z, hzU, hzneq, hThetaz⟩
  classical
  let Theta : ℂ → ℂ := RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))
  let g : ℂ → ℂ := Function.update Theta ρ (1 : ℂ)
  have hEqOn : Set.EqOn Theta g (U \ {ρ}) := by
    intro w hw; simp [g, Function.update_noteq hw.2]
  have hval : g ρ = 1 := by simp [g]
  have hgU : AnalyticOn ℂ g U :=
    RH.RS.analyticOn_update_from_pinned (U := U) (ρ := ρ) (Θ := Theta) (u := u)
      hUopen hρU hThetaU hEq hu0
  -- Nontriviality: since z ≠ ρ and Theta z ≠ 1, we get g z ≠ 1
  have hgz_ne1 : g z ≠ 1 := by
    have : g z = Theta z := by simp [g, Function.update_noteq hzneq]
    intro hz1; exact hThetaz (by simpa [this] using hz1)
  exact ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi,
    ⟨g, hgU, hThetaU, hEqOn, hval, z, hzU, hgz_ne1⟩⟩

/-- Build the pinch certificate from: outer existence; (P+) on the boundary
for `F := 2 · J_pinch`; a Poisson interior positivity statement; and a pinned–
removable assignment across each `ξ_ext` zero. The (P+) hypothesis is threaded
for provenance but not used analytically here. -/
def pinch_certificate_from_PPlus_and_pinned
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (_hPPlus : RH.Cert.PPlus (fun z => (2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)))
  (hPoisson : ∀ z ∈ Ω,
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re)
  (hPinned : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (RH.RS.Theta_of_J (RH.RS.J_pinch RH.RS.det2 (Classical.choose hOuter))) z ≠ 1)
  : PinchCertificateExt := by
  classical
  -- Ingredient 1: interior positivity on Ω \ Z(ξ_ext)
  let hRe_offXi := hRe_offXi_from_poisson hOuter hPoisson
  -- Ingredient 2: pinned–removable across each ξ_ext zero
  let hRemXi := hRemXi_from_pinned hOuter hPinned
  -- Build the certificate
  exact RH.RS.buildPinchCertificate hOuter hRe_offXi hRemXi

-- Removed top-level RH wrappers to keep RS layer independent of proof layer.

end RS
end RH
