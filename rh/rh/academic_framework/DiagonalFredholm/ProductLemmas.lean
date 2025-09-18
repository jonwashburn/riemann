import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Complex.Basic

namespace RH.AcademicFramework.DiagonalFredholm

/-!
Replace deprecated `tprod_*` lemmas with modern `HasProd`/`Multipliable` bridges.
- Provide only neutral bridges; no `cexp`/summation-dependent helpers here.
-/

open Complex
open scoped BigOperators

/-- Bridge: from `Multipliable f` to a concrete `HasProd` witness. -/
theorem hasProd_of_multipliable {ι : Type*} [Countable ι]
    {f : ι → ℂ} (hf : Multipliable f) : HasProd f (∏' i, f i) := by
  simpa using hf.hasProd

/-- Infinite product of pointwise products (modern API).
Prefer this to deprecated `tprod_mul` forms. -/
theorem tprod_mul {ι : Type*} [Countable ι]
    (f g : ι → ℂ) (hf : Multipliable f) (hg : Multipliable g) :
    (∏' i, f i * g i) = (∏' i, f i) * (∏' i, g i) := by
  -- Modern proof via `HasProd.mul` → equality of `tprod`.
  have hfg : HasProd (fun i => f i * g i) ((∏' i, f i) * (∏' i, g i)) :=
    (hf.hasProd.mul hg.hasProd)
  simpa using hfg.tprod_eq

end RH.AcademicFramework.DiagonalFredholm
