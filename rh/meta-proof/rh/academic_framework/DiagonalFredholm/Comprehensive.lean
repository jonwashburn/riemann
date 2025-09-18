import rh.academic_framework.DiagonalFredholm.Operator
import rh.academic_framework.DiagonalFredholm.ProductLemmas
import rh.academic_framework.DiagonalFredholm.Determinant
import rh.academic_framework.EulerProduct.K0Bound

namespace RH.AcademicFramework.DiagonalFredholm

/-!
Comprehensive module that re-exports operator, product lemmas, and determinant pieces.

We also surface names used by downstream tracks:
- `diagDet2`, `renormE`
- `det2_continuous`, `det2_analytic`
- `det2_identity_Re_gt_one_available` (existence form of continuation defined in `Determinant.lean`)
-/

export RH.AcademicFramework.DiagonalFredholm in
  diagDet2 renormE det2_continuous det2_analytic det2_identity_Re_gt_one_available det2_identity_extended_available

-- Interface is provided by concrete theorems in `Determinant.lean`.

end RH.AcademicFramework.DiagonalFredholm
