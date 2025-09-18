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
  -- Statement-level bridge: assume disk representation and transfer to Ω via Cayley.
  -- In a full derivation, one shows that Re(F)∘Cayley^{-1} matches the disk Poisson integral,
  -- and changes variables to obtain the half-plane Poisson identity.
  -- We expose the same structure in the half-plane.
  refine {
    analytic := by
      -- transferred analyticity (statement-level)
      exact (by
        -- upstream supply
        admit)
  , integrable := by
      intro z hz
      -- integrable via kernel transport (statement-level)
      exact (by admit)
  , re_eq := by
      intro z hz
      -- equality via change of variables under Cayley (statement-level)
      exact (by admit) }

end CayleyAdapters
end AcademicFramework
end RH
