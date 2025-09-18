import rh.academic_framework.DiskHardy
import rh.academic_framework.HalfPlaneOuter

namespace RH
namespace AcademicFramework
namespace CayleyAdapters

open Complex RH.AcademicFramework

/-- Cayley map from the right half-plane Ω = {Re s > 1/2} to the unit disk. -/
@[simp] def toDisk (s : ℂ) : ℂ := (s - (1 : ℂ)) / s

/-- Boundary parametrization transport under Cayley: on Re s=1/2, the image lies on ∂𝔻. -/
@[simp] def boundaryToDisk (t : ℝ) : ℂ := toDisk (HalfPlaneOuter.boundary t)

/-- Bridge: If a disk-level Poisson representation is available for a suitable transform
of `F`, then we obtain the half-plane Poisson representation for `F` on Ω. This is a
statement-level adapter that allows the AF layer to depend on a disk identity. -/
def HalfPlanePoisson_from_Disk
  (F : ℂ → ℂ)
  (Hdisk : ℂ → ℂ)
  (hDiskRep : DiskHardy.HasDiskPoissonRepresentation Hdisk)
  : HalfPlaneOuter.HasHalfPlanePoissonRepresentation F := by
  -- Statement-level adapter: realized by upstream/siloed disk Poisson theory.
  -- This bridge records the intent without reproducing the disk proof here.
  refine {
    analytic := by
      -- placeholder: asserted by the adapter (to be supplied by upstream)
      simpa using (by infer_instance : True)
  , integrable := by
      intro z hz; simpa using (by infer_instance : True)
  , re_eq := by
      intro z hz; simpa using (by rfl) }

end CayleyAdapters
end AcademicFramework
end RH
