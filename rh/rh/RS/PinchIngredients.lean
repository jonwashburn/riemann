import rh.RS.Cayley
import rh.RS.Det2Outer
import rh.academic_framework.CompletedXi
import rh.RS.PinchCertificate

/-!
# Minimal entry builder for supplying pinch ingredients

This file provides a single builder that consumes the two hard ingredients for
the pinch route (interior positivity off `Z(ξ_ext)` and removable extension at
each `ξ_ext` zero), together with the statement-level outer existence, and
returns a concrete `PinchCertificateExt`.

Use this when the analytic inputs are available externally (as in the paper):
- boundary wedge + Poisson ⇒ `0 ≤ Re(2·J_pinch)` on `Ω \ Z(ξ_ext)`; and
- the u-trick/pinned-limit ⇒ removable extension of `Θ := Cayley(2·J_pinch)`
  across each `ξ_ext` zero with value `1` and a nontriviality point.

The final conversion from the certificate to `RiemannHypothesis` is provided
in `rh/Proof/Main.lean` to avoid import cycles.
-/

noncomputable section

namespace RH
namespace RS

open Complex RH.AcademicFramework.CompletedXi

local notation "Ω" => RH.RS.Ω

/-- Build a `PinchCertificateExt` from the outer existence, interior positivity,
and removable-extension assignment at `ξ_ext` zeros. -/
def certificate_from_pinch_ingredients
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
  exact RH.RS.buildPinchCertificate hOuter hRe_offXi hRemXi

end RS
end RH
