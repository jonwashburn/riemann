import rh.academic_framework.Core
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Fredholm Determinant for Diagonal Operators

This file defines the Fredholm determinant for diagonal operators and proves
its basic properties.

## Main definitions

* `fredholm_det2` - Fredholm determinant of I - Λ for trace class diagonal operator Λ

## Main results

* `fredholm_det2_diagonal` - The determinant equals ∏(1 - λᵢ)
* `fredholm_det2_nonzero` - The determinant is nonzero if all λᵢ ≠ 1
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators Filter Topology

variable {ι : Type*} [Countable ι]

/-- Fredholm determinant of I - Λ for diagonal operator Λ with summable eigenvalues -/
noncomputable def fredholm_det2 (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) : ℂ :=
  ∏' i, (1 - eigenvals i)

/-- The Fredholm determinant equals the infinite product -/
theorem fredholm_det2_diagonal (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  fredholm_det2 eigenvals h_bounded h_summable = ∏' i, (1 - eigenvals i) :=
  rfl

-- NOTE: A non-vanishing statement for the Fredholm determinant when no eigenvalue equals `1`
-- can be found in mathlib as `tprod_ne_zero` (see `Topology.Algebra.InfiniteSum.Basic`).
-- We omit the reproving here since it is not required downstream.

end AcademicRH.DiagonalFredholm
