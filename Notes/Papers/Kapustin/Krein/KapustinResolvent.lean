/--
Resolvent / kernel calculus for the bounded Kapustin perturbation.

This file specializes `Krein/RankOneResolvent.lean` to the canonical Kapustin operator

`T := A - [·,u]u = A - kreinRankOne u`.

At the bounded level (where `A` is a bounded operator), Kapustin’s eigenvector ansatz
is the observation that if `A` is invertible and `T x = 0`, then necessarily

`x = ⟪J u, x⟫ · A⁻¹ u`.

In particular, if `⟪J u, A⁻¹ u⟫ = 1`, then `A⁻¹ u` is a kernel vector.

These statements are the algebraic core behind the analytic work in Kapustin’s papers:
once the candidate eigenvector is constructed and shown to lie in the relevant domain,
one reduces the eigenvalue condition to the scalar identity `⟪J u, A⁻¹ u⟫ = 1`.
-/

import Mathlib.Tactic
import KapustinFormalization.Krein.KapustinOperator
import KapustinFormalization.Krein.RankOneResolvent

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-- If `A` is boundedly invertible and `x` lies in the kernel of `A - [·,u]u`, then
`x` is colinear with `A⁻¹ u`.

This is the bounded Kapustin eigenvector ansatz.
-/
lemma eq_smul_symm_u_of_kapustin_apply_eq_zero
    (A : E ≃L[𝕜] E) (u x : E)
    (hx : (mkKapustinOperator (K := K) A.toContinuousLinearMap u) x = 0) :
    x = (⟪K.J u, x⟫_𝕜) • (A.symm u) := by
  -- `mkKapustinOperator A u = A - rankOne u (J u)`.
  -- Apply the general rank-one kernel lemma with `v := J u`.
  simpa [mkKapustinOperator, kreinRankOne, rankOne_apply] using
    (eq_smul_symm_u_of_sub_rankOne_apply_eq_zero (K := K)
      (A := A) (u := u) (v := K.J u) (x := x) (hx := by
        simpa [mkKapustinOperator, kreinRankOne] using hx))

/-- If the Kapustin scalar condition holds, then `A⁻¹ u` is in the kernel of
`A - [·,u]u`.
-/
lemma kapustin_apply_symm_u_eq_zero
    (A : E ≃L[𝕜] E) (u : E)
    (h : ⟪K.J u, A.symm u⟫_𝕜 = 1) :
    (mkKapustinOperator (K := K) A.toContinuousLinearMap u) (A.symm u) = 0 := by
  -- Specialize the general kernel-vector lemma to `v := J u`.
  simpa [mkKapustinOperator, kreinRankOne] using
    (sub_rankOne_apply_symm_u_eq_zero (K := K)
      (A := A) (u := u) (v := K.J u) h)

end FundamentalSymmetry

end Krein
