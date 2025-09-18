import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Complex.Basic

namespace RH.AcademicFramework.DiagonalFredholm

/-! Replace deprecated `tprod_*` lemmas with modern `HasProd`/`Multipliable` bridges.
    This file intentionally avoids `cexp`/sum-dependent helpers. -/

open Complex
open scoped BigOperators

/-!
Replace deprecated `tprod` lemmas with modern `HasProd`/`Multipliable` bridges.
-/

/-- Bridge: from `Multipliable f` to a concrete `HasProd` witness. -/
theorem hasProd_of_multipliable {ι : Type*} [Countable ι]
    {f : ι → ℂ} (hf : Multipliable f) : HasProd f (∏' i, f i) := by
  simpa using hf.hasProd

/-- Product of pointwise products (modern API).
Prefer this to deprecated `tprod_mul` forms. -/
theorem tprod_mul {ι : Type*} [Countable ι]
    (f g : ι → ℂ) (hf : Multipliable f) (hg : Multipliable g) :
    (∏' i, f i * g i) = (∏' i, f i) * (∏' i, g i) := by
  have hfg : HasProd (fun i => f i * g i) ((∏' i, f i) * (∏' i, g i)) :=
    (hf.hasProd.mul hg.hasProd)
  simpa using hfg.tprod_eq

-- Intentionally no `cexp` bridge here per DF‑WP policy.

-- Historical wrappers around drifting API are omitted to maintain stability.

/-! Finite modifications of a product require hypotheses beyond a mere
finite difference set if zeros are allowed. We rely instead on
`multipliable_of_finite_mulSupport` in concrete situations, rather than a
global lemma here. -/

end RH.AcademicFramework.DiagonalFredholm
