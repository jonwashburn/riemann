import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.academic_framework.EulerProductMathlib

noncomputable section

open Complex Set

namespace RH.AcademicFramework.DiagonalFredholm

/-!
Diagonal Fredholm det₂ for the prime–diagonal family A(s) and typed properties.

This module records the typed entry points we use elsewhere:
- det₂ continuity w.r.t. s on the right half-plane
- det₂ analyticity for the diagonal family
- the convergent-region identity on Re(s) > 1
- an analytic continuation form (existence of a holomorphic normalizer)

We model the diagonal det₂ by the inverse Euler product, which agrees with ζ⁻¹
on Re(s) > 1. The normalizer can be taken as 1 in the convergent region.
-/

open scoped BigOperators

/-- Diagonal det₂ for the prime–diagonal model on `Re(s) > 1`:
`diagDet2(s) := (∏ₚ (1 - p^{-s})⁻¹)⁻¹`, i.e. the inverse Euler product. -/
noncomputable def diagDet2 (s : ℂ) : ℂ :=
  (∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹)⁻¹

/-- Renormalizer for the diagonal model on the convergent region. For the
Euler-product definition of `diagDet2`, this is `1`. -/
noncomputable def renormE (_s : ℂ) : ℂ := 1

/-- Convergent-region identity (formal statement): on the half-plane
`Re(s) > 1`, the diagonal Fredholm product times a prime-side normalizer
agrees with the Euler product for `ζ⁻¹`.

This records the precise equality shape we use elsewhere; proofs live in
this module via mathlib's Euler product. -/
def Det2IdentityReGtOne : Prop :=
  ∀ s : ℂ, 1 < s.re → diagDet2 s * renormE s = (riemannZeta s)⁻¹

/-- Analytic continuation (existence form): there exists a holomorphic
normalizer `E` on `ℂ \\ {1}` such that `diagDet2 · * E · = ζ⁻¹` there. -/
def Det2IdentityExtended : Prop :=
  ∃ E : ℂ → ℂ,
    AnalyticOn ℂ E {s : ℂ | s ≠ (1 : ℂ)} ∧
    (∀ s : ℂ, s ≠ (1 : ℂ) → diagDet2 s * E s = (riemannZeta s)⁻¹)

/-- Convergent-region identity: on `Re(s) > 1`, `diagDet2 · * renormE · = ζ⁻¹`. -/
theorem det2_identity_Re_gt_one_available : Det2IdentityReGtOne := by
  intro s hs
  have hEuler : riemannZeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ :=
    RH.AcademicFramework.EPM.euler_product_wrapper s hs
  -- Unfold definitions and use the Euler product
  simp [diagDet2, renormE, hEuler]

/-- Analyticity of `diagDet2` on the convergent region `Re(s) > 1`. -/
theorem det2_analytic : AnalyticOn ℂ diagDet2 {s : ℂ | 1 < s.re} := by
  -- On `Re(s) > 1`, we have `diagDet2 = (riemannZeta)⁻¹`
  have hid : EqOn diagDet2 (fun s => (riemannZeta s)⁻¹) {s : ℂ | 1 < s.re} := by
    intro s hs
    have := det2_identity_Re_gt_one_available s hs
    simpa [renormE] using this
  -- ζ is analytic on `s ≠ 1`, hence on `Re(s) > 1`; and nonvanishing there
  have hζ_an : AnalyticOn ℂ riemannZeta {s : ℂ | s ≠ (1 : ℂ)} :=
    analyticOn_riemannZeta
  have hsubset : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | s ≠ (1 : ℂ)} := by
    intro s hs; exact by
      have : s.re ≠ (1 : ℝ) := ne_of_gt hs
      intro h; simpa [h, Complex.one_re] using this
  have hζ_an' : AnalyticOn ℂ riemannZeta {s : ℂ | 1 < s.re} :=
    hζ_an.mono hsubset
  have hζ_ne : ∀ s ∈ {s : ℂ | 1 < s.re}, riemannZeta s ≠ 0 := by
    intro s hs; exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hs)
  have h_inv : AnalyticOn ℂ (fun s => (riemannZeta s)⁻¹) {s : ℂ | 1 < s.re} := by
    refine AnalyticOn.inv ?hζ hζ_ne
    exact hζ_an'
  -- Conclude by congruence on the region
  exact h_inv.congr (by
    intro s hs; exact (hid s hs).symm)

/-- Continuity of `diagDet2` on `Re(s) > 1` (follows from analyticity). -/
theorem det2_continuous : ContinuousOn diagDet2 {s : ℂ | 1 < s.re} :=
  det2_analytic.continuousOn

end RH.AcademicFramework.DiagonalFredholm
