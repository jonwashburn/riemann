/--
Sherman–Morrison inversion for the *Kapustin perturbation*

`T := A - [·,u]u = A - rankOne u (J u)`

in the fundamental-symmetry model of a Krein space.

This file specializes `Krein/RankOneInverse.lean` to the canonical choice `v = J u`.

It isolates the scalar *Kapustin nondegeneracy* condition

`δ := 1 - ⟪J u, A⁻¹ u⟫ ≠ 0`,

which appears throughout Kapustin’s resolvent computations.
-/

import KapustinFormalization.Krein.RankOneInverse
import KapustinFormalization.Krein.KapustinOperator
import KapustinFormalization.Krein.KapustinResolvent

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-- The scalar `δ = 1 - ⟪J u, A⁻¹ u⟫` controlling invertibility of the Kapustin perturbation. -/
noncomputable def kapustinDelta (A : E ≃L[𝕜] E) (u : E) : 𝕜 :=
  (1 : 𝕜) - ⟪K.J u, A.symm u⟫_𝕜

/-- The Sherman–Morrison candidate inverse for the bounded Kapustin perturbation

`A - [·,u]u = A - rankOne u (J u)`.
-/
noncomputable def invKapustin
    (A : E ≃L[𝕜] E) (u : E) : E →L[𝕜] E :=
  invSubRankOne (K := K) A u (K.J u)

/-- Right inverse for the Kapustin perturbation, under `kapustinDelta ≠ 0`. -/
lemma kapustin_comp_invKapustin
    (A : E ≃L[𝕜] E) (u : E)
    (hδ : kapustinDelta (K := K) A u ≠ 0) :
    (mkKapustinOperator (K := K) A.toContinuousLinearMap u).comp (invKapustin (K := K) A u)
      = ContinuousLinearMap.id 𝕜 E := by
  -- `mkKapustinOperator A u = A - rankOne u (J u)`.
  simpa [mkKapustinOperator, kreinRankOne, kapustinDelta, invKapustin] using
    (sub_rankOne_comp_invSubRankOne (K := K) (A := A) (u := u) (v := K.J u) (hδ := by
      simpa [kapustinDelta] using hδ))

/-- Left inverse for the Kapustin perturbation, under `kapustinDelta ≠ 0`. -/
lemma invKapustin_comp_kapustin
    (A : E ≃L[𝕜] E) (u : E)
    (hδ : kapustinDelta (K := K) A u ≠ 0) :
    (invKapustin (K := K) A u).comp (mkKapustinOperator (K := K) A.toContinuousLinearMap u)
      = ContinuousLinearMap.id 𝕜 E := by
  simpa [mkKapustinOperator, kreinRankOne, kapustinDelta, invKapustin] using
    (invSubRankOne_comp_sub_rankOne (K := K) (A := A) (u := u) (v := K.J u) (hδ := by
      simpa [kapustinDelta] using hδ))

/-- Kernel vector for the Kapustin perturbation: if `⟪J u, A⁻¹ u⟫ = 1`, then `A⁻¹ u` lies in the
kernel of `A - [·,u]u`.

This is the scalar condition used in Kapustin's eigenvalue computations.
-/
lemma kapustin_apply_symm_u_eq_zero'
    (A : E ≃L[𝕜] E) (u : E)
    (h : ⟪K.J u, A.symm u⟫_𝕜 = 1) :
    (mkKapustinOperator (K := K) A.toContinuousLinearMap u) (A.symm u) = 0 := by
  -- This is already available as `kapustin_apply_symm_u_eq_zero` in `Krein/KapustinResolvent.lean`.
  simpa using (kapustin_apply_symm_u_eq_zero (K := K) (A := A) (u := u) h)

end FundamentalSymmetry

end Krein
