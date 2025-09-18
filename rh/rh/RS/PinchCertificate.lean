import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Basic
import rh.academic_framework.CompletedXi
import rh.RS.Det2Outer
import rh.RS.Cayley

/-!
# Pinch certificate builder for the ext ξ route

This module packages the two load-bearing ingredients required to construct
an RS-side pinch certificate for `riemannXi_ext`:

- interior positivity: `0 ≤ Re(2 · J_pinch)` on `Ω \ Z(ξ_ext)`; and
- removable-extension existence for the Cayley transform `Θ := Θ_pinch_of det2 O`
  across each zero of `ξ_ext`.

Given these two inputs, together with the statement-level outer existence
`OuterHalfPlane.ofModulus_det2_over_xi`, we produce a concrete
`PinchCertificateExt` suitable for the final pinch wrapper.

All heavy analysis remains outside: this file only rewraps the two
assumptions into the certificate structure via `PinchCertificateExt.of_pinch`.
-/

noncomputable section

namespace RH
namespace RS

open Complex RH.AcademicFramework.CompletedXi

/-- Shorthand for the right half–plane domain. -/
local notation "Ω" => RH.RS.Ω

/-- Build a `PinchCertificateExt` from:

1) a statement-level outer existence `O` for the boundary modulus `|det2/ξ_ext|`;
2) an interior-positivity witness for `2·J_pinch` off `Z(ξ_ext)`; and
3) a removable-extension witness for the associated `Θ := Θ_pinch_of det2 O`
   at each zero of `ξ_ext`.

This is a thin constructor that uses `PinchCertificateExt.of_pinch` under the hood.
-/
def buildPinchCertificate
  (hOuter : ∃ O : ℂ → ℂ, OuterHalfPlane O ∧
      BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (hRe_offXi : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
      0 ≤ ((2 : ℂ) * (J_pinch det2 (Classical.choose hOuter) z)).re)
  (hRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
      ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
        (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
        ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
          AnalyticOn ℂ (Θ_pinch_of det2 (Classical.choose hOuter)) (U \ {ρ}) ∧
          Set.EqOn (Θ_pinch_of det2 (Classical.choose hOuter)) g (U \ {ρ}) ∧
          g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : PinchCertificateExt := by
  classical
  -- Choose an outer `O` from the existence witness
  let O : ℂ → ℂ := Classical.choose hOuter
  -- Package the two ingredients using the paper's `J_pinch` choice
  exact PinchCertificateExt.of_pinch det2 O
    (by
      intro z hz
      simpa using (hRe_offXi z hz))
    (by
      intro ρ hΩ hXi
      simpa [Θ_pinch_of] using (hRemXi ρ hΩ hXi))

end RS
end RH
