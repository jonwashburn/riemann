/--
Packaging the bounded Kapustin perturbation into a `ContinuousLinearEquiv`.

The file `Krein/KapustinInverse.lean` specializes the abstract Sherman–Morrison theory
(`Krein/RankOneInverse.lean`) to the canonical Kapustin perturbation

`T := A - [·,u]u = A - |u⟩⟨J u|`.

It provides explicit left/right inverse identities for the candidate inverse `invKapustin`
under the scalar nondegeneracy condition

`δ := 1 - ⟪J u, A⁻¹ u⟫ ≠ 0`.

For downstream work (notably resolvent identities and spectral statements), it is convenient to
package those identities as an actual bounded equivalence `E ≃L[𝕜] E`.

This file:

* defines `kapustinEquiv` as that equivalence;
* provides simplification lemmas identifying its forward and inverse maps;
* proves the complementary *singular* statement: if `δ = 0`, then `A - [·,u]u` is not injective.
-/

import KapustinFormalization.Krein.KapustinInverse

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-- The bounded Kapustin perturbation `A - [·,u]u` as a `ContinuousLinearEquiv`,
under the nondegeneracy condition `kapustinDelta A u ≠ 0`.

The inverse map is the Sherman–Morrison operator `invKapustin`.
-/
noncomputable def kapustinEquiv
    (A : E ≃L[𝕜] E) (u : E)
    (hδ : kapustinDelta (K := K) A u ≠ 0) :
    E ≃L[𝕜] E := by
  classical
  refine ContinuousLinearEquiv.ofContinuousLinearMap
    (mkKapustinOperator (K := K) A.toContinuousLinearMap u)
    (invKapustin (K := K) A u)
    (kapustin_comp_invKapustin (K := K) (A := A) (u := u) hδ)
    (invKapustin_comp_kapustin (K := K) (A := A) (u := u) hδ)

@[simp] lemma kapustinEquiv_toContinuousLinearMap
    (A : E ≃L[𝕜] E) (u : E)
    (hδ : kapustinDelta (K := K) A u ≠ 0) :
    (kapustinEquiv (K := K) A u hδ).toContinuousLinearMap
      = mkKapustinOperator (K := K) A.toContinuousLinearMap u := rfl

@[simp] lemma kapustinEquiv_symm_toContinuousLinearMap
    (A : E ≃L[𝕜] E) (u : E)
    (hδ : kapustinDelta (K := K) A u ≠ 0) :
    (kapustinEquiv (K := K) A u hδ).symm.toContinuousLinearMap
      = invKapustin (K := K) A u := rfl

@[simp] lemma kapustinEquiv_apply
    (A : E ≃L[𝕜] E) (u x : E)
    (hδ : kapustinDelta (K := K) A u ≠ 0) :
    kapustinEquiv (K := K) A u hδ x
      = (A x) - (⟪K.J u, x⟫_𝕜) • u := by
  simp [kapustinEquiv, mkKapustinOperator, kreinRankOne, rankOne_apply,
    ContinuousLinearMap.sub_apply]

@[simp] lemma kapustinEquiv_symm_apply
    (A : E ≃L[𝕜] E) (u x : E)
    (hδ : kapustinDelta (K := K) A u ≠ 0) :
    (kapustinEquiv (K := K) A u hδ).symm x = invKapustin (K := K) A u x := rfl

/-- A convenient rewrite: `kapustinDelta = 0` iff the Kapustin scalar inner product equals `1`.

This is the scalar condition that forces the kernel vector `A⁻¹ u`.
-/
lemma kapustinDelta_eq_zero_iff_inner_eq_one
    (A : E ≃L[𝕜] E) (u : E) :
    kapustinDelta (K := K) A u = 0 ↔ ⟪K.J u, A.symm u⟫_𝕜 = 1 := by
  unfold kapustinDelta
  constructor
  · intro h
    have : (1 : 𝕜) = ⟪K.J u, A.symm u⟫_𝕜 := (sub_eq_zero.mp h)
    exact this.symm
  · intro h
    exact (sub_eq_zero.mpr h.symm)

/-- **Singular Kapustin case:** if `kapustinDelta A u = 0`, then the Kapustin perturbation
`A - [·,u]u` is not injective.

Proof idea:
* `kapustinDelta = 0` implies `⟪J u, A⁻¹ u⟫ = 1`.
* by the kernel lemma, `A⁻¹ u` is sent to `0`.
* injectivity would force `A⁻¹ u = 0`, contradicting the scalar condition.
-/
lemma not_injective_mkKapustinOperator_of_kapustinDelta_eq_zero
    (A : E ≃L[𝕜] E) (u : E)
    (hδ0 : kapustinDelta (K := K) A u = 0) :
    ¬ Function.Injective (mkKapustinOperator (K := K) A.toContinuousLinearMap u) := by
  intro hinj
  have hinner : ⟪K.J u, A.symm u⟫_𝕜 = 1 :=
    (kapustinDelta_eq_zero_iff_inner_eq_one (K := K) (A := A) (u := u)).1 hδ0

  have hker : (mkKapustinOperator (K := K) A.toContinuousLinearMap u) (A.symm u) = 0 := by
    simpa using (kapustin_apply_symm_u_eq_zero' (K := K) (A := A) (u := u) hinner)

  have hAinv : A.symm u = 0 := by
    have h0 : (mkKapustinOperator (K := K) A.toContinuousLinearMap u) (0 : E) = 0 := by
      simp [mkKapustinOperator]
    exact hinj (by simpa [h0] using hker)

  have : (0 : 𝕜) = 1 := by
    simpa [hAinv] using hinner
  exact zero_ne_one this

end FundamentalSymmetry

end Krein
