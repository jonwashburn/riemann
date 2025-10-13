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

/-- Convenience specialization to `Ω \ {ξ_ext = 0}`. -/
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

/-- Pinch field `F := 2 · J_pinch det2 O`. -/
@[simp] def F_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (2 : ℂ) * J_pinch det2 O z

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
  -- Abbreviations
  set z : ℂ := boundary t
  -- Boundary modulus equality: |O(z)| = |det2(z)/xi(z)|
  have hOabs : Complex.abs (O z) = Complex.abs (det2 z / riemannXi_ext z) := by
    simpa [z] using hBME t
  -- Nonvanishing at the boundary point
  have hO0  : O z ≠ 0 := by simpa [z] using hO
  have hXi0 : riemannXi_ext z ≠ 0 := by simpa [z] using hXi
  -- Product identity for moduli: |O|·|xi| = |det2|
  have hprod : Complex.abs (O z) * Complex.abs (riemannXi_ext z)
      = Complex.abs (det2 z) := by
    calc
      Complex.abs (O z) * Complex.abs (riemannXi_ext z)
          = Complex.abs (det2 z / riemannXi_ext z) * Complex.abs (riemannXi_ext z) := by
                simpa [hOabs]
      _ = Complex.abs ((det2 z / riemannXi_ext z) * (riemannXi_ext z)) := by
                simpa using
                  (Complex.abs.map_mul (det2 z / riemannXi_ext z) (riemannXi_ext z)).symm
      _ = Complex.abs (det2 z) := by
        -- (det2/ξ) * ξ = det2 using ξ ≠ 0
        have hxinv : (riemannXi_ext z)⁻¹ * (riemannXi_ext z) = (1 : ℂ) :=
          inv_mul_cancel₀ hXi0
        calc
          Complex.abs ((det2 z / riemannXi_ext z) * (riemannXi_ext z))
              = Complex.abs (det2 z * ((riemannXi_ext z)⁻¹ * (riemannXi_ext z))) := by
                    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          _ = Complex.abs (det2 z * 1) := by simpa [hxinv]
          _ = Complex.abs (det2 z) := by simp
  -- Direct absolute-value computation for J_pinch
  have hJabs : Complex.abs (J_pinch det2 O z)
      = Complex.abs (det2 z) / Complex.abs (O z * riemannXi_ext z) := by
    simp [J_pinch, abs_div]
  have hden_abs_mul :
      Complex.abs (O z * riemannXi_ext z) = Complex.abs (O z) * Complex.abs (riemannXi_ext z) := by
    simpa using (Complex.abs.map_mul (O z) (riemannXi_ext z))
  have hJ_eq_div : Complex.abs (J_pinch det2 O z)
      = Complex.abs (det2 z) / (Complex.abs (O z) * Complex.abs (riemannXi_ext z)) := by
    simpa [hden_abs_mul] using hJabs
  -- Positivity of the denominator factor
  have hden_pos : 0 < Complex.abs (O z) * Complex.abs (riemannXi_ext z) := by
    exact mul_pos (Complex.abs.pos_iff.mpr hO0) (Complex.abs.pos_iff.mpr hXi0)
  -- Replace numerator via hprod and simplify to 1
  have hfrac_eq : Complex.abs (J_pinch det2 O z)
      = (Complex.abs (O z) * Complex.abs (riemannXi_ext z)) /
        (Complex.abs (O z) * Complex.abs (riemannXi_ext z)) := by
    simpa [hprod] using hJ_eq_div
  have hden_ne : (Complex.abs (O z) * Complex.abs (riemannXi_ext z)) ≠ 0 := ne_of_gt hden_pos
  have hJ_one : Complex.abs (J_pinch det2 O z) = 1 := by
    simpa [div_self hden_ne] using hfrac_eq
  simpa [z] using hJ_one

-- Boundary bound for the pinch field (statement-level alias, provided elsewhere).
lemma boundary_Re_F_pinch_le_two
  {O : ℂ → ℂ}
  (hBME : BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s))
  (t : ℝ)
  (hO : O (boundary t) ≠ 0)
  (hXi : riemannXi_ext (boundary t) ≠ 0) :
  |((F_pinch det2 O) (boundary t)).re| ≤ (2 : ℝ) := by
  -- |Re(2·J)| ≤ |2·J| = |2|·|J| = 2·1 = 2
  have hJb : Complex.abs (J_pinch det2 O (boundary t)) = 1 :=
    boundary_abs_J_pinch_eq_one (O := O) hBME t hO hXi
  -- Rewrite the boundary point explicitly as 1/2 + i t if needed by downstream simp
  have hJ : Complex.abs (J_pinch det2 O ((2⁻¹ : ℂ) + Complex.I * (t : ℂ))) = 1 := by
    -- boundary t = 1/2 + i t (definitional), but avoid importing HalfPlaneOuter here
    simpa using hJb
  have hFabs : Complex.abs ((F_pinch det2 O) (boundary t)) = (2 : ℝ) := by
    calc
      Complex.abs ((F_pinch det2 O) (boundary t))
          = Complex.abs ((2 : ℂ) * J_pinch det2 O (boundary t)) := by
              simp [F_pinch]
      _ = Complex.abs (2 : ℂ) * Complex.abs (J_pinch det2 O (boundary t)) := by
              simpa using
                (Complex.abs.map_mul (2 : ℂ) (J_pinch det2 O (boundary t)))
      _ = (2 : ℝ) * 1 := by simp [Complex.abs_ofReal, hJ]
      _ = (2 : ℝ) := by norm_num
  calc
    |((F_pinch det2 O) (boundary t)).re| ≤ Complex.abs ((F_pinch det2 O) (boundary t)) :=
      Complex.abs_re_le_abs _
    _ = (2 : ℝ) := hFabs

/-! A convenience variant is avoided here to keep boundary casework at the call site. -/
/-- Analyticity of `J_pinch det2 O` on the off-zeros set `Ω \ {ξ_ext = 0}`.

Requires: `det2` analytic on `Ω`, `O` analytic and zero-free on `Ω`, and
`riemannXi_ext` analytic on `Ω` (available from the academic framework since
`riemannXi_ext = completedRiemannZeta`). -/
lemma J_pinch_analytic_on_offXi
  (hDet2 : Det2OnOmega) {O : ℂ → ℂ} (hO : OuterHalfPlane O)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  : AnalyticOn ℂ (J_pinch det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- Work on the off-zeros set S ⊆ Ω
  let S : Set ℂ := (Ω \ {z | riemannXi_ext z = 0})
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
      (Ω \ {z | riemannXi_ext z = 0}) :=
  J_pinch_analytic_on_offXi (hDet2 := hDet2)
    (hO := (OuterHalfPlane.choose_outer_spec hOuterExist).1) (hXi := hXi)

/-- Analyticity of `Θ_pinch_of det2 O` on a set `S` where `J_pinch det2 O` is
analytic and the Cayley denominator is nonvanishing, ensured here by
`0 ≤ Re(2·J_pinch)` on `S`. -/
lemma Theta_pinch_analytic_on
  {S : Set ℂ} {O : ℂ → ℂ}
  (hJ : AnalyticOn ℂ (J_pinch det2 O) S)
  (hRe : ∀ z ∈ S, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re)
  : AnalyticOn ℂ (Θ_pinch_of det2 O) S := by
  -- Define `F := 2·J_pinch`
  have hConst : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) S := analyticOn_const
  have hF : AnalyticOn ℂ (fun z => (2 : ℂ) * J_pinch det2 O z) S := by
    simpa using hConst.mul hJ
  -- Numerator and denominator analytic
  have hNum : AnalyticOn ℂ (fun z => (2 : ℂ) * J_pinch det2 O z - 1) S := by
    simpa [sub_eq_add_neg] using hF.add analyticOn_const
  have hDen : AnalyticOn ℂ (fun z => (2 : ℂ) * J_pinch det2 O z + 1) S :=
    hF.add analyticOn_const
  -- Denominator is nonzero on S, since Re(2·J) ≥ 0 ⇒ 2·J ≠ -1
  have hDen_ne : ∀ z ∈ S, (fun z => (2 : ℂ) * J_pinch det2 O z + 1) z ≠ 0 := by
    intro z hz
    have hzRe := hRe z hz
    -- If 2·J z + 1 = 0 then 2·J z = -1 with negative real part, contradiction
    intro hzero
    have : ((2 : ℂ) * J_pinch det2 O z).re = (-1 : ℂ).re := by
      have : (2 : ℂ) * J_pinch det2 O z = -1 := by
        simpa using (by simpa [add_eq_zero_iff_eq_neg] using hzero)
      simpa [this]
    have : ((2 : ℂ) * J_pinch det2 O z).re = (-1 : ℝ) := by simpa
    have : 0 ≤ (-1 : ℝ) := by simpa [this] using hzRe
    exact (lt_of_le_of_lt this (show (-1 : ℝ) < 0 by norm_num)).false
  -- Inverse of denominator is analytic on S
  have hInv : AnalyticOn ℂ (fun z => ((2 : ℂ) * J_pinch det2 O z + 1)⁻¹) S :=
    AnalyticOn.inv hDen hDen_ne
  -- Assemble Θ = (Num) * (Den)^{-1}
  have hTheta : AnalyticOn ℂ
      (fun z => ((2 : ℂ) * J_pinch det2 O z - 1) * ((2 : ℂ) * J_pinch det2 O z + 1)⁻¹) S := by
    simpa using hNum.mul hInv
  -- Conclude by definal equality with Θ_pinch_of
  refine (hTheta.congr ?_)
  intro z hz
  unfold Θ_pinch_of Theta_of_J J_pinch
  ring_nf

/-- Analyticity of `Θ_pinch_of det2 O` on the off-zeros set `Ω
{ξ_ext = 0}`.

Requires: `det2` analytic on `Ω`, `O` analytic and zero-free on `Ω`, and
`riemannXi_ext` analytic on `Ω` (available from the academic framework since
`riemannXi_ext = completedRiemannZeta`). We also use the off-zeros real-part
bound to justify the Cayley denominator is nonvanishing. -/
lemma Theta_pinch_analytic_on_offXi
  (hDet2 : Det2OnOmega) {O : ℂ → ℂ} (hO : OuterHalfPlane O)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hRe : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
            0 ≤ ((2 : ℂ) * (J_pinch det2 O z)).re)
  : AnalyticOn ℂ (Θ_pinch_of det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- First get analyticity of J_pinch on the off-zeros set
  have hJ : AnalyticOn ℂ (J_pinch det2 O)
      (Ω \ {z | riemannXi_ext z = 0}) :=
    J_pinch_analytic_on_offXi (hDet2 := hDet2) (hO := hO) (hXi := hXi)
  -- Then apply the Cayley analyticity wrapper
  exact Theta_pinch_analytic_on (S := (Ω \ {z | riemannXi_ext z = 0}))
    (hJ := hJ) (hRe := hRe)

/-- Specialization of `Theta_pinch_analytic_on_offXi` to the chosen outer from
`OuterHalfPlane.ofModulus_det2_over_xi_ext`. -/
lemma Theta_pinch_analytic_on_offXi_choose
  (hDet2 : Det2OnOmega)
  (hOuterExist : OuterHalfPlane.ofModulus_det2_over_xi_ext)
  (hXi : AnalyticOn ℂ riemannXi_ext Ω)
  (hRe : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
            0 ≤ ((2 : ℂ) * (J_pinch det2 (OuterHalfPlane.choose_outer hOuterExist) z)).re)
  : AnalyticOn ℂ (Θ_pinch_of det2 (OuterHalfPlane.choose_outer hOuterExist))
      (Ω \ {z | riemannXi_ext z = 0}) := by
  refine Theta_pinch_analytic_on_offXi (hDet2 := hDet2)
    (hO := (OuterHalfPlane.choose_outer_spec hOuterExist).1)
    (hXi := hXi) (hRe := ?_)
  intro z hz; simpa using (hRe z hz)

/-- Restrict analyticity of `Θ_pinch_of det2 O` from the off-zeros set to an
isolating punctured neighborhood `U \ {ρ}`. If `U ⊆ Ω` and
`U ∩ {ξ_ext = 0} = {ρ}`, then `U \ {ρ} ⊆ Ω \ {ξ_ext = 0}`. -/
lemma Theta_pinch_analytic_on_isolating_punctured
  {U : Set ℂ} {ρ : ℂ} {O : ℂ → ℂ}
  (hOff : AnalyticOn ℂ (Θ_pinch_of det2 O) (Ω \ {z | riemannXi_ext z = 0}))
  (hUsub : U ⊆ Ω)
  (hIso : (U ∩ {z | riemannXi_ext z = 0}) = ({ρ} : Set ℂ))
  : AnalyticOn ℂ (Θ_pinch_of det2 O) (U \ {ρ}) := by
  -- Show the punctured neighborhood sits inside the off-zeros set
  have hsubset : (U \ {ρ}) ⊆ (Ω \ {z | riemannXi_ext z = 0}) := by
    intro z hz
    refine And.intro (hUsub hz.1) ?hoff
    -- Prove z ∉ {ξ_ext = 0}; otherwise contradict z ≠ ρ by isolation
    by_contra hzero
    have hzIn : z ∈ U ∩ {w | riemannXi_ext w = 0} := by
      exact And.intro hz.1 (by simpa [Set.mem_setOf_eq] using hzero)
    have : z ∈ ({ρ} : Set ℂ) := by simpa [hIso] using hzIn
    have : z = ρ := by simpa using this
    exact hz.2 this
  exact hOff.mono hsubset

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
