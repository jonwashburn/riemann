
import Riemann.RS.Det2Outer
import Riemann.academic_framework.CompletedXi

/-!
# The analytic reciprocal field `G`

This file isolates the function `G := (O · ξ_ext) / det₂`, its natural domain
on the half-plane `Ω = {Re > 1/2}`, and the partial logarithm used by the
CR–Green layer.  Everything is expressed relative to:
* a `Det2OnOmega` witness (analytic and nonvanishing determinant);
* an outer function `O` on Ω (zero-free, analytic);
* analyticity of `ξ_ext` on `Ω \ {1}` (available from the academic framework).

the GField refactor is structurally correct (we now have an analytic, zero-free object on ΩoffXi),
but any future claim that “U_field := Re (logG …) is harmonic/analytic” must be justified either by
constructing a genuine holomorphic log of G on each region, or by working entirely in the
Poisson/outer framework without relying on Complex.log.
-/

open Complex Set RH.AcademicFramework.CompletedXi

namespace RH
namespace RS

noncomputable section

local notation "Ω" => RH.RS.Ω

/-- Raw reciprocal field `(O · ξ_ext) / det₂`. -/
@[simp] def G_core (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun s => (O s * riemannXi_ext s) / det2 s

/-- Off-zero domain for `G`: points of Ω where `ξ_ext` does not vanish. -/
@[simp] def ΩoffXi : Set ℂ := Ω \ {z | riemannXi_ext z = 0}

lemma G_core_nonzero_on_ΩoffXi
    {det2 O : ℂ → ℂ}
    (hDet2 : AnalyticOn ℂ det2 Ω)
    (hDet2_ne : ∀ {s}, s ∈ Ω → det2 s ≠ 0)
    (hO : OuterHalfPlane O) :
    ∀ {s}, s ∈ ΩoffXi → G_core det2 O s ≠ 0 := by
  intro s hs
  rcases hs with ⟨hsΩ, hsNotZero⟩
  have hdet : det2 s ≠ 0 := hDet2_ne hsΩ
  have hO'  : O s ≠ 0   := hO.nonzero hsΩ
  have hXi  : riemannXi_ext s ≠ 0 := by
    intro hZero
    -- `hsNotZero` : s ∉ {z | riemannXi_ext z = 0}
    exact hsNotZero (by simpa [Set.mem_setOf_eq] using hZero)
  have hNum : O s * riemannXi_ext s ≠ 0 := mul_ne_zero hO' hXi
  exact div_ne_zero hNum hdet

lemma G_core_analytic_on
    {det2 O : ℂ → ℂ}
    (hDet2 : AnalyticOn ℂ det2 Ω)   -- <--- Changed from `Det2OnOmega`
    (hDet2_ne : ∀ {s}, s ∈ Ω → det2 s ≠ 0) -- <--- Add explicitly if needed for consistency, though this lemma only uses analyticity
    (hO : OuterHalfPlane O)
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ))) :
    AnalyticOn ℂ (G_core det2 O) (Ω \ ({1} : Set ℂ)) := by
  let S : Set ℂ := Ω \ ({1} : Set ℂ)
  have hSsubΩ : S ⊆ Ω := by
    intro z hz; exact hz.1
  have hDet2_S : AnalyticOn ℂ det2 S := hDet2.mono hSsubΩ -- <--- Fixed line
  have hO_S : AnalyticOn ℂ O S := hO.analytic.mono hSsubΩ
  have hXi_S : AnalyticOn ℂ riemannXi_ext S := hXi
  -- ... rest of proof ...
  -- Analytic numerator
  have hNum : AnalyticOn ℂ (fun s => O s * riemannXi_ext s) S := by
    simpa using hO_S.mul hXi_S
  -- Denominator is zero-free on S because `S ⊆ Ω`
  have hDen_ne : ∀ z ∈ S, det2 z ≠ 0 := by
    intro z hz; exact hDet2_ne (hSsubΩ hz)
  have hInv : AnalyticOn ℂ (fun s => (det2 s)⁻¹) S :=
    AnalyticOn.inv hDet2_S hDen_ne
  -- Assemble `(O·ξ) * det₂⁻¹`
  have h := hNum.mul hInv
  convert h using 1

/-- Canonical outer witness from the existing `OuterHalfPlane.ofModulus_det2_over_xi_ext`. -/
def O_canonical : ℂ → ℂ :=
  OuterHalfPlane.choose_outer outer_limit_locally_uniform

lemma O_canonical_outer :
    OuterHalfPlane O_canonical :=
  (OuterHalfPlane.choose_outer_spec outer_limit_locally_uniform).1

/-- Canonical reciprocal field used by the RH route. -/
@[simp] def G_canonical : ℂ → ℂ :=
  G_core det2 O_canonical

@[simp] lemma G_canonical_def :
    G_canonical = fun s => (O_canonical s * riemannXi_ext s) / det2 s := rfl

/-- `G_canonical` is analytic on `Ω \ {1}` (uses ξ analyticity from the academic framework). -/
lemma G_canonical_analytic_on
    (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ))) :
    AnalyticOn ℂ G_canonical (Ω \ ({1} : Set ℂ)) := by
  let hDet2 := det2_on_Ω_proved det2_analytic_on_RSΩ det2_nonzero_on_RSΩ
  simpa using
    (G_core_analytic_on (det2 := det2) (O := O_canonical)
      hDet2.analytic   -- Pass the analytic field
      hDet2.nonzero    -- Pass the nonzero field
      O_canonical_outer
      hXi)

/-- `G_canonical` is zero-free on `ΩoffXi`. -/
lemma G_canonical_nonzero_on :
    ∀ {s}, s ∈ ΩoffXi → G_canonical s ≠ 0 := by
  let hDet2 := det2_on_Ω_proved det2_analytic_on_RSΩ det2_nonzero_on_RSΩ
  intro s hs  -- <--- Introduce s and the hypothesis explicitly
  exact G_core_nonzero_on_ΩoffXi
    (det2 := det2) (O := O_canonical)
    hDet2.analytic
    hDet2.nonzero
    O_canonical_outer
    hs

/-- Partial logarithm of `G` on the off-zero domain (as a function on the subtype). -/
@[simp] def logG (z : {s // s ∈ ΩoffXi}) : ℂ :=
  Complex.log (G_canonical z)

/-- Convenience re-expression on terms of the raw field. -/
lemma logG_def (z : {s // s ∈ ΩoffXi}) :
    logG z = Complex.log ((O_canonical z) * riemannXi_ext z / det2 z) := rfl

/-- `logG` is well-defined because `G_canonical` never vanishes on `ΩoffXi`. -/
lemma logG_well_defined (z : {s // s ∈ ΩoffXi}) :
    G_canonical z ≠ 0 :=
  G_canonical_nonzero_on z.property

end

end RS
end RH
