import Mathlib.Data.Complex.Basic
import rh.RS.SchurGlobalization
import rh.RS.Det2Outer
import rh.academic_framework.CompletedXi

/-!
# Cayley interface for Θ := Cayley(2·J)

This file provides a lightweight interface to build a Schur function
`Θ := (2·J − 1) / (2·J + 1)` on any set where `Re(2·J) ≥ 0`.
It reuses the general helper `SchurOnRectangles` from `SchurGlobalization`.
-/

namespace RH
namespace RS

open Complex Set RH.AcademicFramework.CompletedXi

noncomputable section

/-- Cayley(2·J): define `Θ := (2·J − 1) / (2·J + 1)`. -/
def Theta_of_J (J : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ((2 : ℂ) * J z - 1) / ((2 : ℂ) * J z + 1)

/-- Schur bound for `Θ := Cayley(2·J)` on any set where `Re(2·J) ≥ 0`. -/
lemma Theta_Schur_of_Re_nonneg_on
    (J : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ ((2 : ℂ) * J z).re) :
    IsSchurOn (Theta_of_J J) S := by
  -- Apply the general Cayley→Schur helper with `F := 2·J`.
  have : IsSchurOn (fun z => ((2 : ℂ) * J z - 1) / ((2 : ℂ) * J z + 1)) S :=
    SchurOnRectangles (F := fun z => (2 : ℂ) * J z) (R := S) (hRe := hRe)
  simpa [Theta_of_J] using this

/-- Convenience specialization to `Ω \ {ζ = 0}`. -/
lemma Theta_Schur_of_Re_nonneg_on_Ω_offZeta
    (J : ℂ → ℂ)
    (hRe : ∀ z ∈ (Ω \ {z | riemannZeta z = 0}), 0 ≤ ((2 : ℂ) * J z).re) :
    IsSchurOn (Theta_of_J J) (Ω \ {z | riemannZeta z = 0}) :=
  Theta_Schur_of_Re_nonneg_on J (S := (Ω \ {z | riemannZeta z = 0})) hRe

/-- Convenience specialization to `Ω \\ {ξ_ext = 0}`. -/
lemma Theta_Schur_of_Re_nonneg_on_Ω_offXi
    (J : ℂ → ℂ)
    (hRe : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), 0 ≤ ((2 : ℂ) * J z).re) :
    IsSchurOn (Theta_of_J J) (Ω \ {z | riemannXi_ext z = 0}) :=
  Theta_Schur_of_Re_nonneg_on J (S := (Ω \ {z | riemannXi_ext z = 0})) hRe

/-! Pinch outer data specialized to the ext ξ. -/

/-- Outer data for the pinch route specialized to `riemannXi_ext`.
It supplies a boundary field `J` whose double has nonnegative real part
on `Ω \ {ξ_ext = 0}`. -/
structure PinchOuterExt where
  J : ℂ → ℂ
  hRe_offXi : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), 0 ≤ ((2 : ℂ) * J z).re

/-- The pinch Θ associated to a `PinchOuterExt` via the Cayley transform. -/
def Θ_pinch (P : PinchOuterExt) : ℂ → ℂ := Theta_of_J P.J

/-- Schur bound for the pinch Θ on `Ω \ {ξ_ext = 0}`. -/
lemma Θ_pinch_Schur_offXi (P : PinchOuterExt) :
    IsSchurOn (Θ_pinch P) (Ω \ {z | riemannXi_ext z = 0}) := by
  simpa [Θ_pinch] using Theta_Schur_of_Re_nonneg_on_Ω_offXi P.J P.hRe_offXi

/-! A stronger certificate that also includes the pinned-limit → removable
construction at each `ξ_ext` zero, for a concrete `J`. -/

/-- Pinch certificate specialized to `riemannXi_ext` on Ω. It records:
- `J` and the nonnegativity of `Re(2·J)` off `Z(ξ_ext)` (to get Schur)
- an existence-style removable extension of `Θ := Θ_of_J J` across each `ξ_ext` zero. -/
structure PinchCertificateExt where
  J : ℂ → ℂ
  hRe_offXi : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), 0 ≤ ((2 : ℂ) * J z).re
  existsRemXi : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ (Theta_of_J J) (U \ {ρ}) ∧
        EqOn (Theta_of_J J) g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1

/-- Θ attached to a pinch certificate. -/
def Θ_cert (C : PinchCertificateExt) : ℂ → ℂ := Theta_of_J C.J

/-- Schur bound on `Ω \ {ξ_ext=0}` from the certificate. -/
lemma Θ_cert_Schur_offXi (C : PinchCertificateExt) :
    IsSchurOn (Θ_cert C) (Ω \ {z | riemannXi_ext z = 0}) := by
  simpa [Θ_cert] using Theta_Schur_of_Re_nonneg_on_Ω_offXi C.J C.hRe_offXi

/-! Concrete pinch choice and certificate builder. -/

/-- Paper choice: define `J_pinch := det₂ / (O · ξ_ext)` on Ω. -/
def J_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun s => det2 s / (O s * riemannXi_ext s)

/-- Associated Θ: `Θ_pinch_of det2 O := Θ_of_J (J_pinch det2 O)`. -/
def Θ_pinch_of (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  Theta_of_J (J_pinch det2 O)

/-- Build a `PinchCertificateExt` from the paper `J_pinch` once the two
key facts are supplied:
1) interior positivity `0 ≤ Re(2·J_pinch)` on `Ω \ {ξ_ext=0}`;
2) removable-extension existence for `Θ := Θ_of_J J_pinch` at each `ξ_ext` zero. -/
def PinchCertificateExt.of_pinch (det2 O : ℂ → ℂ)
  (hRe : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
            0 ≤ ((2 : ℂ) * (J_pinch det2 O z)).re)
  (hRem : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧ AnalyticOn ℂ (Θ_pinch_of det2 O) (U \ {ρ}) ∧
        EqOn (Θ_pinch_of det2 O) g (U \ {ρ}) ∧ g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : PinchCertificateExt :=
{ J := J_pinch det2 O
, hRe_offXi := by
    intro z hz; simpa using (hRe z hz)
, existsRemXi := by
    intro ρ hΩ hξ; simpa [Θ_pinch_of] using (hRem ρ hΩ hξ) }

/-- Build a pinch certificate from Det2OnOmega, OuterHalfPlane existence, and the
two key mathematical inputs (interior positivity and removability). -/
def PinchCertificateExt.of_interfaces
  (hDet2 : Det2OnOmega)
  (hOuter : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hRe : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
            0 ≤ ((2 : ℂ) * (J_pinch det2 (OuterHalfPlane.choose_outer hOuter) z)).re)
  (hRem : ∀ ρ, ρ ∈ Ω → riemannXi_ext ρ = 0 →
    ∃ (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ Ω ∧ ρ ∈ U ∧
      (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ) ∧
      ∃ g : ℂ → ℂ, AnalyticOn ℂ g U ∧
        AnalyticOn ℂ (Θ_pinch_of det2 (OuterHalfPlane.choose_outer hOuter)) (U \ {ρ}) ∧
        EqOn (Θ_pinch_of det2 (OuterHalfPlane.choose_outer hOuter)) g (U \ {ρ}) ∧
        g ρ = 1 ∧ ∃ z, z ∈ U ∧ g z ≠ 1)
  : PinchCertificateExt :=
  PinchCertificateExt.of_pinch det2 (OuterHalfPlane.choose_outer hOuter) hRe hRem

/-! ### Alias: Herglotz → Schur via Cayley (for roadmap and readability)

This thin wrapper exposes the roadmap name `schur_of_herglotz`, delegating
to `SchurOnRectangles`. -/

lemma schur_of_herglotz {F : ℂ → ℂ} {S : Set ℂ}
    (hRe : ∀ z ∈ S, 0 ≤ (F z).re) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) S :=
  SchurOnRectangles (F := F) (R := S) hRe

end

end RS
end RH
