import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.RS.PinchCertificate
import rh.RS.PinchIngredients
import rh.RS.RouteB_Final
import rh.academic_framework.CompletedXi
import rh.Proof.Main
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
open RH.RS.RouteB

local notation "Ω" => RH.RS.Ω

/-- Wrapper: from a Poisson interior positivity statement for
`F := 2 · J_pinch det2 O` on `Ω`, we obtain the exact ingredient shape needed
by the pinch certificate on `Ω \ Z(ξ_ext)` (simple restriction). -/
def hRe_offXi_from_poisson
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (hPoisson : ∀ z ∈ Ω,
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re)
  : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re := by
  intro z hz
  exact hPoisson z hz.1
/-! ## Wiring (P+) to interior positivity via Poisson transport -/

/-- Bridge: convert certificate `(P+)` to the AF boundary-positivity predicate. -/
private def boundaryPositive_of_PPlus
  (F : ℂ → ℂ) (hP : RH.Cert.PPlus F) :
  RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive F :=
  -- Coerce the certificate-level boundary positivity to the AF predicate.
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
  : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re := by
  have hBP : RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive (F_pinch det2 (Classical.choose hOuter)) :=
    boundaryPositive_of_PPlus _ hPPlus
  have hTrans := RH.AcademicFramework.HalfPlaneOuterV2.poissonTransportOn
    (F := F_pinch det2 (Classical.choose hOuter)) hRepOn hBP
  intro z hz
  simpa [F_pinch] using hTrans z hz

/-- Build pinch certificate using (P+) threaded through Poisson transport on the
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
        AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter)) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (Θ_pinch_of det2 (Classical.choose hOuter)) z ≠ 1)
  : PinchCertificateExt := by
  classical
  -- Ingredient 1: interior positivity on offXi via transport
  let hRe_offXi := hRe_offXi_from_PPlus_via_transport hOuter hRepOn hPPlus
  -- Ingredient 2: pinned–removable across each ξ_ext zero (packaged)
  let hRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter)) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
    intro ρ hΩ hXi
    rcases hPinned ρ hΩ hXi with
      ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi,
       hΘU, u, hEq, hu0, z, hzU, hzneq, hΘz⟩
    classical
    let Θ : ℂ → ℂ := Θ_pinch_of det2 (Classical.choose hOuter)
    let g : ℂ → ℂ := Function.update Θ ρ (1 : ℂ)
    have hEqOn : Set.EqOn Θ g (U \ {ρ}) := by
      intro w hw; simp [g, Function.update_noteq hw.2]
    have hval : g ρ = 1 := by simp [g]
    have hgU : AnalyticOn ℂ g U :=
      RH.RS.analyticOn_update_from_pinned (U := U) (ρ := ρ) (Θ := Θ) (u := u)
        hUopen hρU hΘU hEq hu0
    -- Nontriviality: since z ≠ ρ and Θ z ≠ 1, we get g z ≠ 1
    have hgz_ne1 : g z ≠ 1 := by
      have : g z = Θ z := by simp [g, Function.update_noteq hzneq]
      intro hz1; exact hΘz (by simpa [this] using hz1)
    exact ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi,
      ⟨g, hgU, hΘU, hEqOn, hval, z, hzU, hgz_ne1⟩⟩
  -- Build the certificate
  exact RH.RS.buildPinchCertificate hOuter hRe_offXi hRemXi

/-- Final wrapper: from (P+), Poisson representation on the off-zeros set,
and pinned–removable data, conclude `RiemannHypothesis`. -/
def RH_from_PPlus_transport_and_pinned
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (hRepOn : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn (F_pinch det2 (Classical.choose hOuter))
              RH.AcademicFramework.HalfPlaneOuterV2.offXi)
  (hPPlus : RH.Cert.PPlus (fun z => (2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)))
  (hPinned : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter)) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (Θ_pinch_of det2 (Classical.choose hOuter)) z ≠ 1)
  : RiemannHypothesis := by
  classical
  let C := pinch_certificate_from_PPlus_transport_and_pinned hOuter hRepOn hPPlus hPinned
  exact RH.Proof.Final.RH_from_pinch_certificate C

/-- Wrapper: pass pinned–removable local data for
`Θ := Θ_pinch_of det2 (choose O)` directly as the `existsRemXi` ingredient. -/
def hRemXi_from_pinned
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  -- Pinned data: for each ξ_ext-zero ρ pick isolating U, Θ-analytic off ρ,
  -- and a u-function with Θ = (1-u)/(1+u) on U\{ρ} and u → 0 on 𝓝[U\{ρ}] ρ,
  -- plus a nontrivial Θ z ≠ 1.
  (hPinned : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter))
            (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (Θ_pinch_of det2 (Classical.choose hOuter)) z ≠ 1)
  : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter)) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hXi
  -- Unpack pinned data, then use the removable-update lemma to build g
  rcases hPinned ρ hΩ hXi with
    ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, hΘU, u, hEq, hu0, z, hzU, hzneq, hΘz⟩
  classical
  let Θ : ℂ → ℂ := Θ_pinch_of det2 (Classical.choose hOuter)
  let g : ℂ → ℂ := Function.update Θ ρ (1 : ℂ)
  have hEqOn : Set.EqOn Θ g (U \ {ρ}) := by
    intro w hw; simp [g, Function.update_noteq hw.2]
  have hval : g ρ = 1 := by simp [g]
  have hgU : AnalyticOn ℂ g U :=
    RH.RS.analyticOn_update_from_pinned (U := U) (ρ := ρ) (Θ := Θ) (u := u)
      hUopen hρU hΘU hEq hu0
  -- Nontriviality: since z ≠ ρ and Θ z ≠ 1, we get g z ≠ 1
  have hgz_ne1 : g z ≠ 1 := by
    have : g z = Θ z := by simp [g, Function.update_noteq hzneq]
    intro hz1; exact hΘz (by simpa [this] using hz1)
  exact ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi,
    ⟨g, hgU, hΘU, hEqOn, hval, z, hzU, hgz_ne1⟩⟩

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
        AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter)) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (Θ_pinch_of det2 (Classical.choose hOuter)) z ≠ 1)
  : PinchCertificateExt := by
  classical
  -- Ingredient 1: interior positivity on Ω \ Z(ξ_ext)
  let hRe_offXi := hRe_offXi_from_poisson hOuter hPoisson
  -- Ingredient 2: pinned–removable across each ξ_ext zero
  let hRemXi := hRemXi_from_pinned hOuter hPinned
  -- Build the certificate
  exact RH.RS.buildPinchCertificate hOuter hRe_offXi hRemXi

/-- Final wrapper: from (P+), Poisson interior positivity, and pinned–removable
data (together with the outer existence), conclude mathlib's `RiemannHypothesis`.
-/
def RH_from_PPlus_and_pinned
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (_hPPlus : RH.Cert.PPlus (fun z => (2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)))
  (hPoisson : ∀ z ∈ Ω,
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re)
  (hPinned : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter)) (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (Θ_pinch_of det2 (Classical.choose hOuter)) z ≠ 1)
  : RiemannHypothesis := by
  classical
  let C := pinch_certificate_from_PPlus_and_pinned hOuter _hPPlus hPoisson hPinned
  exact RH.Proof.Final.RH_from_pinch_certificate C

/-
## Canonical instantiations via Route B exports
-/

/-- Canonical outer existence witness supplied by Route B. -/
def canonical_outer_exists :
    ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s) :=
  ⟨RH.RS.RouteB.O, (RH.RS.RouteB.O_spec).1, (RH.RS.RouteB.O_spec).2⟩

lemma canonical_hasPoissonRepOn :
    RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRepOn
      (F_pinch det2 (Classical.choose canonical_outer_exists))
      (Ω \ {z | riemannXi_ext z = 0}) := by
  have hChoose : Classical.choose canonical_outer_exists = RH.RS.RouteB.O := rfl
  simpa [canonical_outer_exists, hChoose] using RH.RS.RouteB.F_pinch_has_poisson_rep

lemma canonical_pinned_data
    (hCanon : RH.RS.WhitneyAeCore.PPlus_canonical) :
    ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose canonical_outer_exists)) (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          Set.EqOn (Θ_pinch_of det2 (Classical.choose canonical_outer_exists))
            (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ (Θ_pinch_of det2 (Classical.choose canonical_outer_exists)) z ≠ 1 := by
  classical
  have hChoose : Classical.choose canonical_outer_exists = RH.RS.RouteB.O := rfl
  intro ρ hΩ hXi
  obtain ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hΘU, u, hEq, hu0, z, hzU, hzNe, hΘz⟩ :=
    RH.RS.RouteB.pinned_removable_data
      (hRe := RH.RS.RouteB.interior_positive_offXi hCanon)
      ρ hΩ hXi
  refine ⟨U, hUopen, hUconn, hUsub, hρU, hIso,
    ?_, u, ?_, hu0, z, hzU, hzNe, ?_⟩
  · simpa [canonical_outer_exists, hChoose] using hΘU
  · simpa [canonical_outer_exists, hChoose] using hEq
  · simpa [canonical_outer_exists, hChoose] using hΘz

/-- Build the pinch certificate directly from the canonical `(P+)`. -/
noncomputable def pinch_certificate_from_canonical
    (hCanon : RH.RS.WhitneyAeCore.PPlus_canonical) :
    PinchCertificateExt :=
  pinch_certificate_from_PPlus_transport_and_pinned
    canonical_outer_exists
    canonical_hasPoissonRepOn
    (RH.RS.RouteB.boundary_positive hCanon)
    (canonical_pinned_data hCanon)

/-- Conclude RH from the canonical `(P+)` witness alone. -/
def RH_from_PPlus_canonical
    (hCanon : RH.RS.WhitneyAeCore.PPlus_canonical) :
    RiemannHypothesis :=
  RH_from_PPlus_transport_and_pinned
    canonical_outer_exists
    canonical_hasPoissonRepOn
    (RH.RS.RouteB.boundary_positive hCanon)
    (canonical_pinned_data hCanon)

end RS
end RH
