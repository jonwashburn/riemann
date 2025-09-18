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

/-- On the boundary line Re s = 1/2, assuming the boundary modulus equality
`|O(1/2+it)| = |det2/ξ_ext(1/2+it)|`, the pinch field has unit modulus:
`|J_pinch det2 O (1/2+it)| = 1`, provided `O(1/2+it)` and `ξ_ext(1/2+it)` are nonzero. -/
lemma boundary_abs_J_pinch_eq_one
  {O : ℂ → ℂ}
  (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (t : ℝ)
  (hO : O (boundary t) ≠ 0)
  (hXi : riemannXi_ext (boundary t) ≠ 0) :
  Complex.abs (J_pinch det2 O (boundary t)) = 1 := by
  classical
  -- From boundary modulus eq: |O| = |det2/ξ|
  have hOabs : Complex.abs (O (boundary t))
      = Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t)) := hBME t
  -- First, relate |O|·|ξ| = |det2|
  have hprod : Complex.abs (O (boundary t)) * Complex.abs (riemannXi_ext (boundary t))
      = Complex.abs (det2 (boundary t)) := by
    -- multiply both sides of hOabs by |ξ|
    have hmul :
        Complex.abs ((det2 (boundary t)) / (riemannXi_ext (boundary t)) * (riemannXi_ext (boundary t)))
          = Complex.abs (det2 (boundary t)) := by
      -- algebraic identity (z / w) * w = z
      have : (det2 (boundary t)) / (riemannXi_ext (boundary t)) * (riemannXi_ext (boundary t))
            = det2 (boundary t) := by
        field_simp [div_eq_mul_inv, hXi]
      simpa [this]
    have hmul_abs :
        Complex.abs ((det2 (boundary t)) / (riemannXi_ext (boundary t)) * (riemannXi_ext (boundary t)))
          = Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t)) *
            Complex.abs (riemannXi_ext (boundary t)) := by
      simpa using (Complex.abs.mul
        ((det2 (boundary t)) / (riemannXi_ext (boundary t))) (riemannXi_ext (boundary t)))
    -- rewrite |O| using hOabs
    have : Complex.abs (O (boundary t)) * Complex.abs (riemannXi_ext (boundary t))
          = Complex.abs (det2 (boundary t) / riemannXi_ext (boundary t)) *
            Complex.abs (riemannXi_ext (boundary t)) := by simpa [hOabs]
    exact this.trans (hmul_abs.trans hmul)
  -- Next, show |J| * (|O|·|ξ|) = |det2|
  have hden_ne : (O (boundary t)) * (riemannXi_ext (boundary t)) ≠ 0 := mul_ne_zero hO hXi
  have hJmul :
      Complex.abs (J_pinch det2 O (boundary t))
        * (Complex.abs (O (boundary t)) * Complex.abs (riemannXi_ext (boundary t)))
      = Complex.abs (det2 (boundary t)) := by
    -- Use the algebraic identity det2 = J_pinch * (O*ξ)
    have : J_pinch det2 O (boundary t) * (O (boundary t) * riemannXi_ext (boundary t))
          = det2 (boundary t) := by
      simp [J_pinch, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have := congrArg Complex.abs this
    simpa [Complex.abs.mul] using this
  -- Denominator positivity
  have hden_pos : 0 < Complex.abs (O (boundary t)) * Complex.abs (riemannXi_ext (boundary t)) := by
    have h1 : 0 < Complex.abs (O (boundary t)) := Complex.abs.pos.mpr hO
    have h2 : 0 < Complex.abs (riemannXi_ext (boundary t)) := Complex.abs.pos.mpr hXi
    exact mul_pos h1 h2
  -- Divide the equalities to conclude |J| = 1
  have : Complex.abs (J_pinch det2 O (boundary t))
      = Complex.abs (det2 (boundary t)) /
        (Complex.abs (O (boundary t)) * Complex.abs (riemannXi_ext (boundary t))) := by
    exact (eq_div_iff_mul_eq hden_pos.ne').mpr hJmul
  -- Replace numerator with denominator via hprod and simplify
  simpa [this, hprod]

/-- Boundary bound for the pinch field: on Re s = 1/2, under the boundary
modulus equality and nonvanishing at that boundary point, we have
`|(F_pinch det2 O)(1/2+it).re| ≤ 2`. -/
lemma boundary_Re_F_pinch_le_two
  {O : ℂ → ℂ}
  (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (t : ℝ)
  (hO : O (boundary t) ≠ 0)
  (hXi : riemannXi_ext (boundary t) ≠ 0) :
  |((F_pinch det2 O) (boundary t)).re| ≤ (2 : ℝ) := by
  classical
  -- |Re w| ≤ |w|
  have h1 : |((F_pinch det2 O) (boundary t)).re| ≤ Complex.abs ((F_pinch det2 O) (boundary t)) := by
    exact Complex.abs_re_le_abs _
  -- |F_pinch| = |2·J_pinch| = 2·|J_pinch| = 2
  have hJ : Complex.abs (J_pinch det2 O (boundary t)) = 1 :=
    boundary_abs_J_pinch_eq_one (O := O) hBME t hO hXi
  have hF : Complex.abs ((F_pinch det2 O) (boundary t)) = 2 := by
    simpa [F_pinch, hJ, Complex.abs.mul, Complex.abs.two, mul_one]
  -- conclude
  simpa [hF]
/-- Analyticity of `J_pinch det2 O` on the off-zeros set `Ω \\ {ξ_ext = 0}`.

Requires: `det2` analytic on `Ω`, `O` analytic and zero-free on `Ω`, and
`riemannXi_ext` analytic on `Ω` (available from the academic framework since
`riemannXi_ext = completedRiemannZeta`). -/
lemma J_pinch_analytic_on_offXi
  (hDet2 : Det2OnOmega) {O : ℂ → ℂ} (hO : OuterHalfPlane O)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  : AnalyticOn ℂ (J_pinch det2 O) (Ω \\ {z | riemannXi_ext z = 0}) := by
  -- Work on the off-zeros set S ⊆ Ω
  let S : Set ℂ := (Ω \\ {z | riemannXi_ext z = 0})
  have hSsub : S ⊆ Ω := by
    intro z hz; exact hz.1
  -- Analyticity of numerator and factors on S
  have hDet2_S : AnalyticOn ℂ det2 S := (hDet2.analytic.mono hSsub)
  have hO_S : AnalyticOn ℂ O S := (hO.analytic.mono hSsub)
  have hXi_S : AnalyticOn ℂ riemannXi_ext S := (hXi.mono hSsub)
  -- Denominator is nonzero on S: O(z) ≠ 0 on Ω and ξ_ext(z) ≠ 0 on S
  have hDen_ne : ∀ z ∈ S, (O z * riemannXi_ext z) ≠ 0 := by
    intro z hz
    have hzΩ : z ∈ Ω := hz.1
    have hO_ne : O z ≠ 0 := hO.nonzero (by exact hzΩ)
    have hXi_ne : riemannXi_ext z ≠ 0 := by
      -- z ∉ {ξ_ext = 0}
      have : z ∉ {w | riemannXi_ext w = 0} := by
        intro hzero; exact hz.2 (by simpa [Set.mem_setOf_eq] using hzero)
      -- so value is nonzero
      by_contra h0
      exact this (by simpa [Set.mem_setOf_eq, h0])
    exact mul_ne_zero hO_ne hXi_ne
  -- Analytic inverse of the denominator on S
  have hInv : AnalyticOn ℂ (fun z => (O z * riemannXi_ext z)⁻¹) S := by
    -- product analytic, then invert using nonvanishing on S
    have hProd : AnalyticOn ℂ (fun z => O z * riemannXi_ext z) S := by
      simpa using hO_S.mul hXi_S
    exact AnalyticOn.inv hProd hDen_ne
  -- Assemble J_pinch = det2 * (O * ξ_ext)^{-1}
  have : AnalyticOn ℂ (fun z => det2 z * (O z * riemannXi_ext z)⁻¹) S := by
    simpa using hDet2_S.mul hInv
  -- Conclude via definal equality on S
  refine (this.congr ?_)
  intro z hz
  simp [J_pinch, div_eq_mul_inv]

/-- Specialization of `J_pinch_analytic_on_offXi` to the chosen outer
from `OuterHalfPlane.ofModulus_det2_over_xi_ext`. Uses
`OuterHalfPlane.choose_outer_spec` to supply analyticity/nonvanishing for `O`. -/
lemma J_pinch_analytic_on_offXi_choose
  (hDet2 : Det2OnOmega)
  (hOuterExist : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  : AnalyticOn ℂ (J_pinch det2 (OuterHalfPlane.choose_outer hOuterExist))
      (Ω \\ {z | riemannXi_ext z = 0}) :=
  J_pinch_analytic_on_offXi (hDet2 := hDet2)
    (hO := (OuterHalfPlane.choose_outer_spec hOuterExist).1) (hXi := hXi)

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
