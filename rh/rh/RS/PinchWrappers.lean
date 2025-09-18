import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.RS.PinchCertificate
import rh.RS.PinchIngredients
import rh.academic_framework.CompletedXi
import rh.Proof.Main
-- keep packaging decoupled to avoid cycles; consumers can import XiExtBridge directly if needed
import rh.RS.BoundaryWedge

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

end RS
end RH
