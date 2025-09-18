import rh.academic_framework.DiskHardy
import rh.academic_framework.HalfPlaneOuter

namespace RH
namespace AcademicFramework
namespace CayleyAdapters

open Complex RH.AcademicFramework

/-- Cayley map from the right half-plane Ω = {Re s > 1/2} to the unit disk. -/
@[simp] def toDisk (s : ℂ) : ℂ := (s - (1 : ℂ)) / s

/-- Inverse Cayley map from the unit disk to the right half-plane Ω. -/
@[simp] def toHalf (w : ℂ) : ℂ := 1 / (1 - w)

/-- Boundary parametrization transport under Cayley: on Re s=1/2, the image lies on ∂𝔻. -/
@[simp] def boundaryToDisk (t : ℝ) : ℂ := toDisk (HalfPlaneOuter.boundary t)

/-- Bridge (packaging form): Given the Cayley relation between `F` and a disk-side
transform `Hdisk`, together with half-plane analyticity, boundary integrability,
and the Poisson identity on Ω, produce the half-plane Poisson representation
record. This removes internal admits; callers supply the analytic facts. -/
def HalfPlanePoisson_from_Disk
  (F : ℂ → ℂ)
  (Hdisk : ℂ → ℂ)
  (hRel : Set.EqOn F (fun z => Hdisk (toDisk z)) HalfPlaneOuter.Ω)
  (hAnalytic : AnalyticOn ℂ F HalfPlaneOuter.Ω)
  (hIntegrable : ∀ z ∈ HalfPlaneOuter.Ω,
    Integrable (fun t : ℝ => (F (HalfPlaneOuter.boundary t)).re * HalfPlaneOuter.poissonKernel z t))
  (hReEq : ∀ z ∈ HalfPlaneOuter.Ω,
    (F z).re = HalfPlaneOuter.P (fun t : ℝ => (F (HalfPlaneOuter.boundary t)).re) z)
  : HalfPlaneOuter.HasHalfPlanePoissonRepresentation F := by
  -- Package the provided half-plane facts directly; no internal admits.
  exact {
    analytic := hAnalytic
  , integrable := hIntegrable
  , re_eq := hReEq }

end CayleyAdapters
end AcademicFramework
end RH
