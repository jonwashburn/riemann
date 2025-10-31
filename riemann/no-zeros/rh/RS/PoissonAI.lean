import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import rh.academic_framework.HalfPlaneOuterV2
import rh.academic_framework.PoissonCayley
import rh.academic_framework.CayleyAdapters
import rh.academic_framework.CompletedXi
import rh.RS.Det2Outer
import rh.RS.RouteB_Final

/-!
Helpers to assemble the θ‑free Poisson real‑part identity on `offXi` for the
pinch field and turn it into a half‑plane Poisson representation using the AF
and Route B builders. No axioms are introduced.
-/

noncomputable section

namespace RH.RS
namespace PoissonAI

open RH.AcademicFramework
open RH.AcademicFramework.HalfPlaneOuterV2
open RH.AcademicFramework.PoissonCayley
open RH.AcademicFramework.CayleyAdapters
open RH.AcademicFramework.CompletedXi
open RH.RS
open MeasureTheory

/-! θ‑free identity from Cayley, under pullback rep and alignment equalities. -/
/-- Given:
- `H : ℂ → ℂ`
- a pullback subset Poisson representation for `H ∘ toDisk` on `offXi`, and
- alignment equalities between the interior/boundary values of the pinch field
  `F := F_pinch det2 RouteB.O` and the Cayley transports of `H`,
produce the θ‑free half‑plane real‑part identity for `F` on `offXi`.

This is a thin wrapper over the AF theorem `pinch_theta_free_ReEqOn_offXi`.
-/
theorem thetaFree_hReEqOn_offXi_from_cayley
  (H : ℂ → ℂ)
  (hRepPull : HasPoissonRepOn (fun z => H (toDisk z)) offXi)
  (hEqInterior : Set.EqOn (F_pinch det2 RH.RS.RouteB.O)
                   (fun z => H (toDisk z)) offXi)
  (hEqBoundary : PoissonCayley.EqOnBoundary (F_pinch det2 RH.RS.RouteB.O) H)
  : PoissonCayley.HasHalfPlanePoissonReEqOn (F_pinch det2 RH.RS.RouteB.O) offXi := by
  -- transport via the AF θ‑free Cayley bridge
  exact pinch_theta_free_ReEqOn_offXi (det2 := det2) (O := RH.RS.RouteB.O) (H := H)
    (hEqInt := hEqInterior) (hEqBd := hEqBoundary) (hRepPull := hRepPull)

/-! Build the pinch Poisson rep on `offXi` from a θ‑free identity and boundary measurability. -/
/-- If we have the θ‑free half‑plane real‑part identity on `offXi` for the pinch
field, and boundary measurability of the ingredients, then the Route B builder
produces a subset Poisson representation for the pinch field on `offXi`.
-/
theorem build_pinch_rep_from_thetaFree
  (hDet2 : Det2OnOmega)
  (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)))
  (hDet_meas : Measurable (fun t : ℝ => det2 (HalfPlaneOuterV2.boundary t)))
  (hO_meas   : Measurable (fun t : ℝ => RH.RS.RouteB.O (HalfPlaneOuterV2.boundary t)))
  (hXi_meas  : Measurable (fun t : ℝ => riemannXi_ext (HalfPlaneOuterV2.boundary t)))
  (hReEqOn   : PoissonCayley.HasHalfPlanePoissonReEqOn (F_pinch det2 RH.RS.RouteB.O) offXi)
  : HasPoissonRepOn (F_pinch det2 RH.RS.RouteB.O) offXi := by
  -- Delegate to the Route B exposure theorem, coercing the identity by simpa
  exact RH.RS.RouteB.F_pinch_has_poisson_rep (hDet2 := hDet2) (hXi := hXi)
    (hDet_meas := hDet_meas) (hO_meas := hO_meas) (hXi_meas := hXi_meas)
    (hReEqOn := by
      intro z hz
      simpa using hReEqOn z hz)

/-- Canonical Cayley pullback for the pinch field. -/
def H_pinch (w : ℂ) : ℂ := F_pinch det2 RH.RS.RouteB.O (CayleyAdapters.fromDisk w)

@[simp] lemma H_pinch_def : ∀ w, H_pinch w = F_pinch det2 RH.RS.RouteB.O (CayleyAdapters.fromDisk w) := by
  intro w; rfl

/-- Interior equality on `offXi`: `F(z) = H_pinch(toDisk z)`. -/
lemma hEqInterior_pinch :
  Set.EqOn (F_pinch det2 RH.RS.RouteB.O)
    (fun z => H_pinch (toDisk z)) offXi := by
  intro z hz
  have hzΩ : z ∈ Ω := offXi_subset_Ω hz
  -- F_pinch z = F_pinch (fromDisk (toDisk z))
  simpa [H_pinch] using
    (map_fromDisk_toDisk (F := fun u => F_pinch det2 RH.RS.RouteB.O u) hzΩ).symm

/-- Boundary alignment: `F(boundary t) = H_pinch(boundaryToDisk t)` for all real t. -/
lemma hEqBoundary_pinch :
  PoissonCayley.EqOnBoundary (F_pinch det2 RH.RS.RouteB.O) H_pinch := by
  intro t
  -- F_pinch (boundary t) = F_pinch (fromDisk (boundaryToDisk t))
  simpa [H_pinch] using
    (map_fromDisk_boundaryToDisk (F := fun u => F_pinch det2 RH.RS.RouteB.O u) t).symm

/-- θ‑free half‑plane real‑part identity on `offXi` using the canonical `H_pinch`,
assuming a pullback subset Poisson representation for `H_pinch ∘ toDisk`. -/
theorem pinch_hReEqOn_from_pullbackRep
  (hRepPull : HasPoissonRepOn (fun z => H_pinch (toDisk z)) offXi)
  : PoissonCayley.HasHalfPlanePoissonReEqOn (F_pinch det2 RH.RS.RouteB.O) offXi := by
  exact thetaFree_hReEqOn_offXi_from_cayley (H := H_pinch) hRepPull hEqInterior_pinch hEqBoundary_pinch

/-- From a pullback subset Poisson representation for `H_pinch ∘ toDisk` on `offXi`,
and the boundary measurability hypotheses, produce a half‑plane subset Poisson
representation for the pinch field on `offXi`. -/
theorem pinch_rep_from_pullbackRep_and_meas
  (hDet2 : Det2OnOmega)
  (hXi : AnalyticOn ℂ riemannXi_ext (Ω \ ({1} : Set ℂ)))
  (hDet_meas : Measurable (fun t : ℝ => det2 (HalfPlaneOuterV2.boundary t)))
  (hO_meas   : Measurable (fun t : ℝ => RH.RS.RouteB.O (HalfPlaneOuterV2.boundary t)))
  (hXi_meas  : Measurable (fun t : ℝ => riemannXi_ext (HalfPlaneOuterV2.boundary t)))
  (hRepPull : HasPoissonRepOn (fun z => H_pinch (toDisk z)) offXi)
  : HasPoissonRepOn (F_pinch det2 RH.RS.RouteB.O) offXi := by
  have hReEqOn := pinch_hReEqOn_from_pullbackRep hRepPull
  exact build_pinch_rep_from_thetaFree hDet2 hXi hDet_meas hO_meas hXi_meas hReEqOn

end PoissonAI
end RH.RS
