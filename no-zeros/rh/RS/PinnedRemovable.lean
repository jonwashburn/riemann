import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Basic
import rh.RS.OffZerosBridge

/-!
# Pinned removability via the u-trick (Cayley form)

This module packages a lightweight, mathlib-only "pinned removability" helper
that turns u-trick data for a function `Θ` on a punctured neighborhood into a
global analytic extension `g` on the neighborhood with `g ρ = 1` and `g = Θ`
off `ρ`, together with a nontriviality witness.

It reuses the pinned-limit and removable-update lemmas already provided in
`rh/RS/OffZerosBridge.lean`:
  - `RH.RS.Theta_pinned_limit_from_N2`
  - `RH.RS.analyticOn_update_from_pinned`

No new axioms and no sorrys are introduced.
-/

noncomputable section

namespace RH
namespace RS

open Complex Set Filter

/-- Convenience alias for the Cayley transform on ℂ. -/
@[simp] def cayley (w : ℂ) : ℂ := (1 - w) / (1 + w)

/-- Pinned removability packaging for `Θ` at a point `ρ` inside an open set `U`.

Fields:
- `g` is analytic on `U`
- `g = Θ` on the punctured set `U \ {ρ}`
- `g ρ = 1`
- there exists a point in `U` where `g ≠ 1` (nontriviality witness)
-/
structure RemovablePinned (Θ : ℂ → ℂ) (U : Set ℂ) (ρ : ℂ) where
  U_open  : IsOpen U
  ρ_mem   : ρ ∈ U
  g       : ℂ → ℂ
  g_analytic : AnalyticOn ℂ g U
  eq_off  : EqOn Θ g (U \ {ρ})
  g_at    : g ρ = 1
  exists_ne1 : ∃ z ∈ U, z ≠ ρ ∧ g z ≠ 1

/-- Pinned removability from u-trick data.

Inputs:
- `U` open with `ρ ∈ U`
- `Θ` analytic on `U \ {ρ}`
- an analytic `u` on `U` with `u → 0` along `𝓝[U \ {ρ}] ρ`
- Cayley equality on the punctured set: `Θ = (1 - u)/(1 + u)`
- a nontriviality witness: a point `z0 ∈ U`, `z0 ≠ ρ`, at which `Θ z0 ≠ 1`

Output: a `RemovablePinned` structure witnessing the removable extension `g`.
-/
def removable_pinned_from_u_trick
    (Θ u : ℂ → ℂ)
    (U : Set ℂ) (ρ : ℂ)
    (hUopen : IsOpen U) (hρU : ρ ∈ U)
    (hΘU : AnalyticOn ℂ Θ (U \ {ρ}))
    (huA : AnalyticOn ℂ u U)
    (hEq : EqOn Θ (fun z => (1 - u z) / (1 + u z)) (U \ {ρ}))
    (hu0 : Tendsto u (nhdsWithin ρ (U \ {ρ})) (nhds (0 : ℂ)))
    (z0 : ℂ) (hz0U : z0 ∈ U) (hz0ne : z0 ≠ ρ) (hΘz0ne : Θ z0 ≠ 1)
    : RemovablePinned Θ U ρ := by
  -- Build analytic extension g := update Θ ρ 1 using the pinned removable lemma
  have hgU : AnalyticOn ℂ (Function.update Θ ρ (1 : ℂ)) U :=
    RH.RS.analyticOn_update_from_pinned
      (U := U) (ρ := ρ) (Θ := Θ) (u := u)
      hUopen hρU hΘU hEq hu0
  -- Off ρ, the update agrees with Θ
  have hEqOn : EqOn Θ (Function.update Θ ρ (1 : ℂ)) (U \ {ρ}) := by
    intro z hz
    by_cases hzρ : z = ρ
    · exfalso; exact hz.2 hzρ
    · simp [Function.update, hzρ]
  -- Define the witness structure
  refine {
    U_open := hUopen
    , ρ_mem := hρU
    , g := (Function.update Θ ρ (1 : ℂ))
    , g_analytic := hgU
    , eq_off := hEqOn
    , g_at := by simp [Function.update]
    , exists_ne1 := ?_ }
  -- Nontriviality passes to g at z0 since z0 ≠ ρ ⇒ g z0 = Θ z0
  have hgz0 : (Function.update Θ ρ (1 : ℂ)) z0 = Θ z0 := by
    simp [Function.update, hz0ne]
  exact ⟨z0, hz0U, hz0ne, by simpa [hgz0] using hΘz0ne⟩

end RS
end RH
