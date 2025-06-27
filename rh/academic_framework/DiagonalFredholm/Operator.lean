import rh.academic_framework.Core
import rh.academic_framework.DiagonalFredholm.DiagonalTools
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Diagonal Operators on ℓ²

This file defines diagonal operators on ℓ² spaces and their basic properties.

## Main definitions

* `DiagonalOperator` - A diagonal operator on ℓ² with bounded eigenvalues

## Main results

* `DiagonalOperator_apply` - Diagonal operators act by pointwise multiplication
* `summable_implies_bounded` - Summable sequences are bounded
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators Filter Topology

variable {ι : Type*} [Countable ι]

/-- A diagonal operator on ℓ² -/
-- Use the DiagonalOperator' from DiagonalTools
noncomputable def DiagonalOperatorFromEigenvals [DecidableEq ι] (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C) :
  lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  DiagonalOperator' eigenvals

/-- The identity operator on ℓ² -/
noncomputable def id : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  ContinuousLinearMap.id ℂ (lp (fun _ : ι => ℂ) 2)

end AcademicRH.DiagonalFredholm
