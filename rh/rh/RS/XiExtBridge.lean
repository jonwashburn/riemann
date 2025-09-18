import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Complex.RemovableSingularity
import rh.academic_framework.CompletedXi

/-!
# Xi_ext bridge: local removable packaging and ζ‑assignment via zeros equivalence

This module specializes RS packaging to the completed ξ_ext and provides:

- `LocalDataXiExt` and a chooser at `ξ_ext` zeros in `Ω`
- A builder `assignXi_ext_fromLocal` that produces the RS export assignment shape
  expected by the pinch route from a chooser
- A bridge `assign_fromXiExtRemovable` that converts removable data at `ξ_ext` zeros
  to the ζ‑assignment on `Ω` using `xi_ext_zeros_eq_zeta_zeros_on_Ω`

No circular imports: we import `CompletedXi` here, and this file is not imported by
`SchurGlobalization`.
-/

noncomputable section

namespace RH
namespace RS

open Set Complex RH.AcademicFramework.CompletedXi Filter Topology

-- Right half‑plane domain Ω is already defined in RS; we reuse `Ω` from this namespace.

/-- Local data for a removable singularity of `Θ` at a `riemannXi_ext` zero `ρ`.
This matches the RS export shape used by the pinch route. -/
structure LocalDataXiExt (Θ : ℂ → ℂ) (ρ : ℂ) : Type where
  U : Set ℂ
  hUopen : IsOpen U
  hUconn : IsPreconnected U
  hUsub : U ⊆ Ω
  hρU : ρ ∈ U
  hIsoXi : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ)
  g : ℂ → ℂ
  hg : AnalyticOn ℂ g U
  hΘU : AnalyticOn ℂ Θ (U \ {ρ})
  hExt : EqOn Θ g (U \ {ρ})
  hval : g ρ = 1
  hWitness : ∃ z, z ∈ U ∧ g z ≠ 1

/-- A chooser for `LocalDataXiExt` at each `riemannXi_ext` zero in `Ω`. -/
abbrev LocalChooserXiExt (Θ : ℂ → ℂ) : Type :=
  ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 → LocalDataXiExt Θ ρ

/-- Build the RS‑shaped assignment at `ξ_ext` zeros from a local chooser. -/
def assignXi_ext_fromLocal {Θ : ℂ → ℂ}
    (choose : LocalChooserXiExt Θ)
    : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hXi
  classical
  let data := choose ρ hΩ hXi
  refine ⟨data.U, data.hUopen, data.hUconn, ?_, data.hρU, data.hIsoXi, ?_⟩
  · intro z hz; exact data.hUsub hz
  · exact ⟨data.g, data.hg, data.hΘU, data.hExt, data.hval, data.hWitness⟩

/-- Bridge: from removable extension data at `ξ_ext` zeros to the ζ‑assignment on `Ω`,
using `xi_ext_zeros_eq_zeta_zeros_on_Ω`. -/
def assign_fromXiExtRemovable {Θ : ℂ → ℂ}
  (assignXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : ∀ ρ, ρ ∈ Ω → riemannZeta ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
        EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hΩ hζ
  -- Convert ζ‑zero to ξ_ext‑zero on Ω
  have hXi : riemannXi_ext ρ = 0 := (xi_ext_zeros_eq_zeta_zeros_on_Ω ρ hΩ).mpr hζ
  rcases assignXi ρ hΩ hXi with
    ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, g, hg, hΘU, hExt, hval, z, hzU, hgzne⟩
  -- Transport the isolating property across zeros equivalence
  have hIsoZeta : (U ∩ {z | riemannZeta z = 0}) = ({ρ} : Set ℂ) := by
    ext x; constructor
    · intro hx
      have hxU : x ∈ U := hx.1
      have hxζ : riemannZeta x = 0 := by simpa [Set.mem_setOf_eq] using hx.2
      have hxΩ : x ∈ Ω := hUsub hxU
      have hxXi : riemannXi_ext x = 0 := (xi_ext_zeros_eq_zeta_zeros_on_Ω x hxΩ).mpr hxζ
      have hxInXi : x ∈ (U ∩ {z | riemannXi_ext z = 0}) := ⟨hxU, by simpa [Set.mem_setOf_eq] using hxXi⟩
      have hxSingleton : x ∈ ({ρ} : Set ℂ) := by simpa [hIsoXi] using hxInXi
      simpa using hxSingleton
    · intro hx
      have hxρ : x = ρ := by simpa using hx
      have hxU : x ∈ U := by simpa [hxρ] using hρU
      have hζρ : riemannZeta ρ = 0 := hζ
      exact ⟨hxU, by simpa [Set.mem_setOf_eq, hxρ] using hζρ⟩
  exact ⟨U, hUopen, hUconn, hUsub, hρU, hIsoZeta, g, hg, hΘU, hExt, hval, z, hzU, hgzne⟩

/-- Pinned–limit packaging (u–trick): from local data at a `ξ_ext` zero `ρ` showing
that on an isolating open set `U ⊆ Ω` one has
`Θ = (1 - u)/(1 + u)` on `U \ {ρ}` with `u → 0` along `𝓝[U \ {ρ}] ρ`, we produce the
removable–extension assignment expected by the pinch route.

This lemma is designed to be called with `Θ := Θ_pinch_of det2 O`. -/
lemma assignXi_ext_from_pinned
    {Θ : ℂ → ℂ}
    (ρ : ℂ) (hρΩ : ρ ∈ Ω) (hρXi : riemannXi_ext ρ = 0)
    (U : Set ℂ) (hUopen : IsOpen U) (hUconn : IsPreconnected U) (hUsub : U ⊆ Ω)
    (hρU : ρ ∈ U) (hIsoXi : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
    (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
    (u : ℂ → ℂ)
    (hEq : EqOn Θ (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}))
    (hu0 : Filter.Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)))
    (hWitness : ∃ z, z ∈ U ∧ z ≠ ρ ∧ Θ z ≠ 1)
    : ∃ (U' : Set ℂ), IsOpen U' ∧ IsPreconnected U' ∧ U' ⊆ Ω ∧ ρ ∈ U' ∧
        (U' ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U' ∧ AnalyticOn ℂ Θ (U' \ {ρ}) ∧
          EqOn Θ g (U' \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U' ∧ g z ≠ 1 := by
  classical
  -- Limit Θ → 1 on the punctured neighborhood via the u–trick
  have hEq_ev : (fun z => Θ z) =ᶠ[nhdsWithin ρ (U \ {ρ})]
      (fun z => (1 - u z) / (1 + u z)) := by
    -- direct: EqOn on U\{ρ} yields eventuallyEq on 𝓝[U\{ρ}] ρ
    simpa using Set.EqOn.eventuallyEq_nhdsWithin (s := (U \ {ρ})) hEq
  have hΘ_lim1 : Filter.Tendsto Θ (nhdsWithin ρ (U \ {ρ})) (nhds (1 : ℂ)) :=
    (RH.RS.Theta_pinned_limit_from_N2 (U := U \ {ρ}) (ρ := ρ) (Θ := Θ) (u := u) hEq_ev hu0)
  -- Removable singularity at ρ: build analytic extension g on U with g ρ = 1 and EqOn on U \ {ρ}
  -- Use mathlib's removable theorem via the update construction and equality on the punctured set
  have hDiff : DifferentiableOn ℂ Θ (U \ {ρ}) := by
    -- analytic on punctured implies differentiable there
    have hOpen : IsOpen (U \ {ρ}) := IsOpen.sdiff hUopen isClosed_singleton
    have hA : AnalyticOn ℂ Θ (U \ {ρ}) := by simpa using hΘU
    exact (analyticOn_iff_differentiableOn (f := Θ) (s := U \ {ρ}) hOpen).1 hA
  -- (Optional) continuity of Θ at ρ is not needed below
  -- Define the extension g and record properties
  let g : ℂ → ℂ := Function.update Θ ρ (1 : ℂ)
  have hEqOn : EqOn Θ g (U \ {ρ}) := by
    intro z hz
    have hzne : z ≠ ρ := by exact hz.2
    simpa [g, Function.update_noteq hzne] using rfl
  -- Analyticity of g on U from the removable singularity update lemma
  have hgU : AnalyticOn ℂ g U := by
    -- delegate to the centralized removable-update lemma in OffZerosBridge
    exact RH.RS.analyticOn_update_from_pinned U ρ Θ u hUopen hρU hΘU hEq hu0
  have hval : g ρ = 1 := by simp [g]
  -- Nontriviality passes to g at a witness point z ∈ U
  rcases hWitness with ⟨z, hzU, hzneq, hΘz⟩
  have hzU' : z ∈ U := hzU
  have hgz_ne1 : g z ≠ 1 := by
    -- since z ≠ ρ, g agrees with Θ on U \ {ρ}
    have hzIn : z ∈ (U \ {ρ}) := ⟨hzU, by simpa [Set.mem_singleton_iff, hzneq]⟩
    have hg_eq : g z = Θ z := by simpa [g, Function.update_noteq hzneq] using rfl
    exact fun h => hΘz (by simpa [hg_eq] using h)
  -- Package in the expected RS export shape
  refine ⟨U, hUopen, hUconn, hUsub, hρU, hIsoXi, ⟨g, hgU, hΘU, ?hExt, hval, z, hzU', hgz_ne1⟩⟩
  -- EqOn Θ g on U \ {ρ}
  intro w hw
  exact hEqOn hw

/-- Existential assignment from a pinned–limit chooser: for each `ξ_ext` zero `ρ`,
supply local data `(U,u)` as in `assignXi_ext_from_pinned` and obtain the
removable–extension assignment shape expected by the pinch route for `Θ`. -/
def assignXi_ext_from_pinnedChooser
    {Θ : ℂ → ℂ}
    (choose : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        AnalyticOn ℂ Θ (U \ {ρ}) ∧
        ∃ u : ℂ → ℂ,
          EqOn Θ (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}) ∧
          Tendsto u (nhdsWithin ρ (U \ {ρ})) (𝓝 (0 : ℂ)) ∧
          ∃ z, z ∈ U ∧ z ≠ ρ ∧ Θ z ≠ 1)
    : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ Θ (U \ {ρ}) ∧
          EqOn Θ g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1 := by
  intro ρ hρΩ hρXi
  classical
  rcases choose ρ hρΩ hρXi with
    ⟨U, hUopen, hUconn, hUsub, hρU, hIso, hΘU, u, hEq, hu0, z, hzU, hzneq, hΘz⟩
  -- Apply the pinned packaging on the chosen data, forwarding a strengthened witness z ≠ ρ
  refine assignXi_ext_from_pinned (Θ := Θ) ρ hρΩ hρXi U hUopen hUconn hUsub hρU hIso hΘU u hEq hu0 ⟨z, hzU, hzneq, hΘz⟩

end RS
end RH
