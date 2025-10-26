import rh.academic_framework.DiagonalFredholm.Operator
import rh.academic_framework.DiagonalFredholm.ProductLemmas
import rh.academic_framework.DiagonalFredholm.Determinant
import rh.academic_framework.EulerProduct.K0Bound

namespace RH.AcademicFramework.DiagonalFredholm

/-! Comprehensive module that bundles the DF components. -/

-- Re-exports can be added here if needed; kept minimal to avoid self-export issues.

noncomputable section

open Complex Set

/-!
Field-notation on predicates and modern infinite-product bridges
===============================================================

This module provides tiny, typed wrappers that (1) use field-notation
like `s.re` in predicates appearing in DF statements, and (2) expose
the modern `HasProd`/`Multipliable`-based infinite product lemmas from
`ProductLemmas` without pulling in extra typeclass assumptions.
-/

/-- Extended identity: analytic off the pole at `s = 1`. -/
def extended_identity_off_pole : Prop := Det2IdentityExtended

/-- Convenience wrapper to use the modern product API (`tprod_mul`).
Requires only `[Countable ι]` (no `DecidableEq`). -/
theorem tprod_mul' {ι : Type*} [Countable ι]
    (f g : ι → ℂ) (hf : Multipliable f) (hg : Multipliable g) :
    (∏' i, f i * g i) = (∏' i, f i) * (∏' i, g i) :=
  tprod_mul f g hf hg

/-- Convenience wrapper: from `Multipliable f` to a concrete `HasProd` witness. -/
theorem hasProd_of_multipliable' {ι : Type*} [Countable ι]
    {f : ι → ℂ} (hf : Multipliable f) : HasProd f (∏' i, f i) :=
  hasProd_of_multipliable (ι := ι) (f := f) hf

end

end RH.AcademicFramework.DiagonalFredholm
