/--
Sherman–Morrison inversion for a rank-one perturbation of a *boundedly invertible* operator.

This file extends `Krein/RankOneResolvent.lean`.

Given a boundedly invertible operator `A : E ≃L[𝕜] E` and vectors `u v : E`, consider

`T := A - rankOne u v`.

Factoring

`T = A ∘ (I - rankOne (A⁻¹ u) v)`

reduces invertibility of `T` to the basic Sherman–Morrison identity for `I - rankOne`.

If `δ := 1 - ⟪v, A⁻¹ u⟫` is nonzero, then

`T⁻¹ = (I + δ⁻¹ • rankOne (A⁻¹ u) v) ∘ A⁻¹`.

We record this as a pair of left/right inverse lemmas, keeping the development purely algebraic
and independent of any analytic model.
-/

import KapustinFormalization.Krein.RankOneResolvent

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

section

/-- Factorization of a rank-one perturbation of an invertible operator.

`A - |u⟩⟨v| = A ∘ (I - |A⁻¹ u⟩⟨v|)`.

This identity is the entry point for applying the basic Sherman–Morrison inversion of
`I - rankOne`.
-/
lemma sub_rankOne_eq_comp_id_sub
    (A : E ≃L[𝕜] E) (u v : E) :
    (A.toContinuousLinearMap - rankOne (K := K) u v)
      = A.toContinuousLinearMap.comp
          (ContinuousLinearMap.id 𝕜 E - rankOne (K := K) (A.symm u) v) := by
  ext x
  -- Pointwise:
  --   (A - |u⟩⟨v|)x = A x - ⟪v,x⟫u
  --   A ( (I - |A⁻¹ u⟩⟨v|) x ) = A x - ⟪v,x⟫ A(A⁻¹ u) = A x - ⟪v,x⟫ u.
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, rankOne_apply,
    map_sub, map_smul]

/-- Candidate inverse in the Sherman–Morrison formula for `A - rankOne u v`.

We deliberately return a bounded operator `E →L[𝕜] E`; the two-sided inverse property is
proved in lemmas below.
-/
noncomputable def invSubRankOne
    (A : E ≃L[𝕜] E) (u v : E) : E →L[𝕜] E :=
  (ContinuousLinearMap.id 𝕜 E
      + (((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜)⁻¹) • rankOne (K := K) (A.symm u) v)
    .comp A.symm.toContinuousLinearMap

@[simp] lemma invSubRankOne_apply
    (A : E ≃L[𝕜] E) (u v x : E) :
    invSubRankOne (K := K) A u v x =
      (A.symm x) + (((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜)⁻¹) • (⟪v, A.symm x⟫_𝕜) • (A.symm u) := by
  -- Purely pointwise.
  simp [invSubRankOne, ContinuousLinearMap.comp_apply, rankOne_apply, add_smul, smul_smul,
    mul_assoc]

/-- Right inverse: `(A - rankOne u v) ∘ invSubRankOne = I` under the scalar nondegeneracy
condition.
-/
lemma sub_rankOne_comp_invSubRankOne
    (A : E ≃L[𝕜] E) (u v : E)
    (hδ : ((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜) ≠ 0) :
    (A.toContinuousLinearMap - rankOne (K := K) u v).comp (invSubRankOne (K := K) A u v)
      = ContinuousLinearMap.id 𝕜 E := by
  classical
  -- Abbreviate the rank-one map appearing after factoring out `A`.
  set P : E →L[𝕜] E := rankOne (K := K) (A.symm u) v
  set δ : 𝕜 := (1 : 𝕜) - ⟪v, A.symm u⟫_𝕜
  set c : 𝕜 := δ⁻¹

  have hSM :
      ( (ContinuousLinearMap.id 𝕜 E - P).comp
          (ContinuousLinearMap.id 𝕜 E + c • P) )
        = ContinuousLinearMap.id 𝕜 E := by
    -- This is exactly the basic Sherman–Morrison identity for `I - P`.
    -- Note that `δ = 1 - ⟪v, A⁻¹ u⟫` is the required scalar.
    simpa [P, δ, c] using
      (id_sub_rankOne_comp_id_add (K := K) (u := A.symm u) (v := v) (hδ := hδ))

  -- Factor `A - |u⟩⟨v| = A ∘ (I - P)` and rewrite the candidate inverse.
  have hfac :
      (A.toContinuousLinearMap - rankOne (K := K) u v)
        = A.toContinuousLinearMap.comp (ContinuousLinearMap.id 𝕜 E - P) := by
    simpa [P] using (sub_rankOne_eq_comp_id_sub (K := K) A u v)

  have hinv :
      invSubRankOne (K := K) A u v
        = (ContinuousLinearMap.id 𝕜 E + c • P).comp A.symm.toContinuousLinearMap := by
    simp [invSubRankOne, P, δ, c]

  -- Now compute:
  --   (A ∘ (I - P)) ∘ ((I + cP) ∘ A⁻¹) = A ∘ ((I - P) ∘ (I + cP)) ∘ A⁻¹ = I.
  calc
    (A.toContinuousLinearMap - rankOne (K := K) u v).comp (invSubRankOne (K := K) A u v)
        = (A.toContinuousLinearMap.comp (ContinuousLinearMap.id 𝕜 E - P)).comp
            ((ContinuousLinearMap.id 𝕜 E + c • P).comp A.symm.toContinuousLinearMap) := by
          simp [hfac, hinv, ContinuousLinearMap.comp_assoc]
    _ = A.toContinuousLinearMap.comp ((ContinuousLinearMap.id 𝕜 E - P).comp
            (ContinuousLinearMap.id 𝕜 E + c • P)).comp A.symm.toContinuousLinearMap := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = A.toContinuousLinearMap.comp (ContinuousLinearMap.id 𝕜 E).comp A.symm.toContinuousLinearMap := by
          simp [hSM]
    _ = A.toContinuousLinearMap.comp A.symm.toContinuousLinearMap := by
          simp
    _ = ContinuousLinearMap.id 𝕜 E := by
          ext x
          simp

/-- Left inverse: `invSubRankOne ∘ (A - rankOne u v) = I` under the scalar nondegeneracy
condition.
-/
lemma invSubRankOne_comp_sub_rankOne
    (A : E ≃L[𝕜] E) (u v : E)
    (hδ : ((1 : 𝕜) - ⟪v, A.symm u⟫_𝕜) ≠ 0) :
    (invSubRankOne (K := K) A u v).comp (A.toContinuousLinearMap - rankOne (K := K) u v)
      = ContinuousLinearMap.id 𝕜 E := by
  classical
  set P : E →L[𝕜] E := rankOne (K := K) (A.symm u) v
  set δ : 𝕜 := (1 : 𝕜) - ⟪v, A.symm u⟫_𝕜
  set c : 𝕜 := δ⁻¹

  have hSM :
      ( (ContinuousLinearMap.id 𝕜 E + c • P).comp
          (ContinuousLinearMap.id 𝕜 E - P) )
        = ContinuousLinearMap.id 𝕜 E := by
    simpa [P, δ, c] using
      (id_add_comp_id_sub_rankOne (K := K) (u := A.symm u) (v := v) (hδ := hδ))

  have hfac :
      (A.toContinuousLinearMap - rankOne (K := K) u v)
        = A.toContinuousLinearMap.comp (ContinuousLinearMap.id 𝕜 E - P) := by
    simpa [P] using (sub_rankOne_eq_comp_id_sub (K := K) A u v)

  have hinv :
      invSubRankOne (K := K) A u v
        = (ContinuousLinearMap.id 𝕜 E + c • P).comp A.symm.toContinuousLinearMap := by
    simp [invSubRankOne, P, δ, c]

  calc
    (invSubRankOne (K := K) A u v).comp (A.toContinuousLinearMap - rankOne (K := K) u v)
        = ((ContinuousLinearMap.id 𝕜 E + c • P).comp A.symm.toContinuousLinearMap)
            .comp (A.toContinuousLinearMap.comp (ContinuousLinearMap.id 𝕜 E - P)) := by
          simp [hinv, hfac, ContinuousLinearMap.comp_assoc]
    _ = (ContinuousLinearMap.id 𝕜 E + c • P).comp
          (A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap).comp
            (ContinuousLinearMap.id 𝕜 E - P) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (ContinuousLinearMap.id 𝕜 E + c • P).comp (ContinuousLinearMap.id 𝕜 E).comp
            (ContinuousLinearMap.id 𝕜 E - P) := by
          -- `A⁻¹ ∘ A = I`.
          simp
    _ = (ContinuousLinearMap.id 𝕜 E + c • P).comp (ContinuousLinearMap.id 𝕜 E - P) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = ContinuousLinearMap.id 𝕜 E := by
          simpa using hSM

end

end FundamentalSymmetry

end Krein
