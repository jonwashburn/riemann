/--
Packaging the Sherman–Morrison inversion as a `ContinuousLinearEquiv`.

The previous file `Krein/RankOneInverse.lean` constructs an explicit candidate inverse
`invSubRankOne A u v : E →L[𝕜] E` and proves the two-sided inverse identities

* `(A - |u⟩⟨v|) ∘ invSubRankOne = I`
* `invSubRankOne ∘ (A - |u⟩⟨v|) = I`

under the scalar nondegeneracy condition

`δ := 1 - ⟪v, A⁻¹ u⟫ ≠ 0`.

For downstream spectral/resolvent theory (and for avoiding repeated manual rewriting), it is
convenient to *package* these identities as an actual bounded equivalence

`E ≃L[𝕜] E`.

This file does exactly that, in a way that is independent of any analytic model.
-/

import KapustinFormalization.Krein.RankOneInverse

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-- The rank-one perturbation `A - |u⟩⟨v|` as a bounded equivalence, under the Sherman–Morrison
nondegeneracy condition `δ = 1 - ⟪v, A⁻¹ u⟫ ≠ 0`.

The inverse is the explicit Sherman–Morrison operator `invSubRankOne`.
-/
noncomputable def subRankOneEquiv
    (A : E ≃L[𝕜] E) (u v : E)
    (hδ : ((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜) ≠ 0) :
    E ≃L[𝕜] E := by
  classical
  refine ContinuousLinearEquiv.ofContinuousLinearMap
    (A.toContinuousLinearMap - rankOne (K := K) u v)
    (invSubRankOne (K := K) A u v)
    (sub_rankOne_comp_invSubRankOne (K := K) (A := A) (u := u) (v := v) hδ)
    (invSubRankOne_comp_sub_rankOne (K := K) (A := A) (u := u) (v := v) hδ)

@[simp] lemma subRankOneEquiv_toContinuousLinearMap
    (A : E ≃L[𝕜] E) (u v : E)
    (hδ : ((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜) ≠ 0) :
    (subRankOneEquiv (K := K) A u v hδ).toContinuousLinearMap
      = (A.toContinuousLinearMap - rankOne (K := K) u v) := rfl

@[simp] lemma subRankOneEquiv_symm_toContinuousLinearMap
    (A : E ≃L[𝕜] E) (u v : E)
    (hδ : ((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜) ≠ 0) :
    (subRankOneEquiv (K := K) A u v hδ).symm.toContinuousLinearMap
      = invSubRankOne (K := K) A u v := rfl

@[simp] lemma subRankOneEquiv_apply
    (A : E ≃L[𝕜] E) (u v x : E)
    (hδ : ((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜) ≠ 0) :
    subRankOneEquiv (K := K) A u v hδ x
      = (A x) - (⟪v, x⟫_𝕜) • u := by
  -- Purely pointwise expansion.
  simp [subRankOneEquiv, ContinuousLinearMap.sub_apply, rankOne_apply]

@[simp] lemma subRankOneEquiv_symm_apply
    (A : E ≃L[𝕜] E) (u v x : E)
    (hδ : ((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜) ≠ 0) :
    (subRankOneEquiv (K := K) A u v hδ).symm x = invSubRankOne (K := K) A u v x := by
  -- By construction, the inverse map *is* `invSubRankOne`.
  rfl

/-- Explicit pointwise formula for the inverse of `A - |u⟩⟨v|`.

This is a repackaging of `invSubRankOne_apply` under the `subRankOneEquiv` name.
-/
@[simp] lemma subRankOneEquiv_symm_apply_formula
    (A : E ≃L[𝕜] E) (u v x : E)
    (hδ : ((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜) ≠ 0) :
    (subRankOneEquiv (K := K) A u v hδ).symm x =
      (A.symm x) + (((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜)⁻¹) • (⟪v, A.symm x⟫_𝕜) • (A.symm u) := by
  -- `invSubRankOne_apply` already provides this formula.
  simp [subRankOneEquiv, FundamentalSymmetry.invSubRankOne_apply]

end FundamentalSymmetry

end Krein
