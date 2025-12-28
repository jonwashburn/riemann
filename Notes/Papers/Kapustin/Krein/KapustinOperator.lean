/--
Kapustin-style operators as rank-one perturbations in Krein spaces.

This file implements the next layer above `Krein/RankOne.lean`: given

* a fundamental symmetry `J` (hence a Krein inner product `[x,y] = ⟪J x, y⟫`),
* a bounded operator `A`, and
* a vector `u`,

we define the **Kapustin perturbation**

`T := A - P_u`,  where  `P_u x = [x,u] u`.

The key result is that if `A` is Krein-selfadjoint then `T` is Krein-selfadjoint.
This isolates the purely Krein-theoretic algebra that appears in Kapustin’s
Krein–Hilbert–Pólya constructions, independent of the later analytic input
(Hardy space/Mellin transform estimates, etc.).
-/

import KapustinFormalization.Krein.RankOne

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-!
## Kapustin rank-one perturbation

We keep the definition *bounded* at this layer: the unbounded case (multiplication by a symbol,
Schrödinger operators, etc.) is handled later by moving to an `UnboundedOperator` API (PhysLean
or mathlib’s unbounded-operator development, depending on the target).
-/

/-- The (bounded) Kapustin perturbation `A - [·,u]u` implemented as `A - rankOne u (J u)`.

This is the canonical bounded-operator layer underlying Kapustin’s HPO-in-Krein-spaces paper,
and also the rank-one part of the canonical-system perturbations in the earlier work.
-/
noncomputable def mkKapustinOperator (A : E →L[𝕜] E) (u : E) : E →L[𝕜] E :=
  A - kreinRankOne (K := K) u

@[simp] lemma mkKapustinOperator_apply (A : E →L[𝕜] E) (u x : E) :
    (mkKapustinOperator (K := K) A u) x = A x - (⟪K.J u, x⟫_𝕜) • u := by
  -- Expand `mkKapustinOperator` and `kreinRankOne`.
  simp [mkKapustinOperator, kreinRankOne, rankOne_apply]

/-!
## Krein selfadjointness

At this level, we only require that the *unperturbed* operator `A` is Krein-selfadjoint.
The perturbation `P_u` is always Krein-selfadjoint by `isKreinSelfAdjoint_kreinRankOne`.

Therefore `A - P_u` is Krein-selfadjoint by linearity of the Krein adjoint.
-/

theorem isKreinSelfAdjoint_mkKapustinOperator
    (A : E →L[𝕜] E) (u : E)
    (hA : IsKreinSelfAdjoint (K := K) A) :
    IsKreinSelfAdjoint (K := K) (mkKapustinOperator (K := K) A u) := by
  -- `T# = (A - P)# = A# - P# = A - P`.
  unfold mkKapustinOperator FundamentalSymmetry.IsKreinSelfAdjoint
  -- Use additivity and the fact that the rank-one perturbation is Krein-selfadjoint.
  simpa [kreinAdjoint_sub, hA, isKreinSelfAdjoint_kreinRankOne (K := K) u]

end FundamentalSymmetry

end Krein
