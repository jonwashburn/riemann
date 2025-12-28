/--
Transport of Kapustin/Krein constructions under unitary equivalences.

The analytic part of Kapustin’s program (Hardy/Mellin models, Sonin spaces, de Branges spaces,
Schrödinger/Morse realizations) repeatedly identifies two Hilbert spaces by a *unitary* map that
intertwines the relevant fundamental symmetries.

At the purely algebraic/bounded level, this file packages the corresponding transport rules:

* conjugation of bounded operators by a continuous linear equivalence;
* compatibility with the rank-one operator `rankOne` under unitary equivalences;
* compatibility with the Krein rank-one operator `kreinRankOne` (requires intertwining);
* compatibility with Kapustin’s bounded perturbation `mkKapustinOperator` (requires intertwining);
* invariance of Kapustin’s non-real eigenvalue scalar condition under such transports.

This file is designed as the final “model-independent” layer before injecting heavy analytic input.
-/

import Mathlib.Analysis.InnerProductSpace.LinearMap
import KapustinFormalization.Krein.Intertwining
import KapustinFormalization.Krein.KapustinEigenvalue

namespace Krein

universe u v

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-!
## Conjugation of bounded operators

We keep this as a standalone definition rather than relying on any bundled action on
`E →L[𝕜] E`; this keeps the downstream simp-normal forms predictable.
-/

/-- Conjugate a bounded operator by a continuous linear equivalence:

`conjCLM U A = U ∘L A ∘L U⁻¹`.
-/
noncomputable def conjCLM (U : E ≃L[𝕜] F) (A : E →L[𝕜] E) : F →L[𝕜] F :=
  U.toContinuousLinearMap.comp (A.comp U.symm.toContinuousLinearMap)

@[simp] lemma conjCLM_apply (U : E ≃L[𝕜] F) (A : E →L[𝕜] E) (x : F) :
    conjCLM (U := U) A x = U (A (U.symm x)) := by
  simp [conjCLM, ContinuousLinearMap.comp_apply]

@[simp] lemma conjCLM_id (U : E ≃L[𝕜] F) :
    conjCLM (U := U) (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 F := by
  ext x
  simp [conjCLM, ContinuousLinearMap.comp_apply]

@[simp] lemma conjCLM_one (U : E ≃L[𝕜] F) : conjCLM (U := U) (1 : E →L[𝕜] E) = 1 := by
  ext x
  simp [conjCLM, ContinuousLinearMap.comp_apply]

@[simp] lemma conjCLM_add (U : E ≃L[𝕜] F) (A B : E →L[𝕜] E) :
    conjCLM (U := U) (A + B) = conjCLM (U := U) A + conjCLM (U := U) B := by
  ext x
  simp [conjCLM, ContinuousLinearMap.comp_apply]

@[simp] lemma conjCLM_sub (U : E ≃L[𝕜] F) (A B : E →L[𝕜] E) :
    conjCLM (U := U) (A - B) = conjCLM (U := U) A - conjCLM (U := U) B := by
  ext x
  simp [conjCLM, ContinuousLinearMap.comp_apply]

@[simp] lemma conjCLM_smul (U : E ≃L[𝕜] F) (c : 𝕜) (A : E →L[𝕜] E) :
    conjCLM (U := U) (c • A) = c • conjCLM (U := U) A := by
  ext x
  simp [conjCLM, ContinuousLinearMap.comp_apply]

@[simp] lemma conjCLM_comp (U : E ≃L[𝕜] F) (A B : E →L[𝕜] E) :
    conjCLM (U := U) (A.comp B) = (conjCLM (U := U) A).comp (conjCLM (U := U) B) := by
  ext x
  simp [conjCLM, ContinuousLinearMap.comp_apply]

/-- Conjugate a continuous linear equivalence `e` by `U`:

`conjEquiv U e = U ∘ e ∘ U⁻¹`.
-/
noncomputable def conjEquiv (U : E ≃L[𝕜] F) (e : E ≃L[𝕜] E) : F ≃L[𝕜] F :=
  (U.symm.trans e).trans U

@[simp] lemma conjEquiv_apply (U : E ≃L[𝕜] F) (e : E ≃L[𝕜] E) (x : F) :
    conjEquiv (U := U) e x = U (e (U.symm x)) := by
  simp [conjEquiv, ContinuousLinearEquiv.trans_apply]

@[simp] lemma conjEquiv_symm_apply (U : E ≃L[𝕜] F) (e : E ≃L[𝕜] E) (x : F) :
    (conjEquiv (U := U) e).symm x = U (e.symm (U.symm x)) := by
  simp [conjEquiv, ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.trans_apply]

@[simp] lemma conjEquiv_toContinuousLinearMap (U : E ≃L[𝕜] F) (e : E ≃L[𝕜] E) :
    (conjEquiv (U := U) e).toContinuousLinearMap = conjCLM (U := U) e.toContinuousLinearMap := by
  ext x
  simp [conjCLM, conjEquiv, ContinuousLinearEquiv.trans_apply, ContinuousLinearMap.comp_apply]

@[simp] lemma conjEquiv_symm_apply_of_apply (U : E ≃L[𝕜] F) (e : E ≃L[𝕜] E) (x : E) :
    (conjEquiv (U := U) e).symm (U x) = U (e.symm x) := by
  simp [conjEquiv_symm_apply]

/-!
## Rank-one operators under unitary changes of model
-/

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E) (K' : FundamentalSymmetry 𝕜 F)

/-- Conjugation transports the rank-one operator under a *unitary* equivalence.

This is the precise statement needed to transport Kapustin rank-one perturbations between
analytic models.
-/
@[simp] lemma conjCLM_rankOne
    (U : E ≃ₗᵢ[𝕜] F) (u v : E) :
    conjCLM (U := U.toContinuousLinearEquiv) (rankOne (K := K) u v)
      = rankOne (K := K') (U u) (U v) := by
  ext x
  have hinner : (⟪v, U.symm x⟫_𝕜) = ⟪U v, x⟫_𝕜 := by
    -- `inner_map_eq_flip` reads `⟪U v, x⟫ = ⟪v, U⁻¹ x⟫`.
    simpa using (U.inner_map_eq_flip v x).symm
  simp [conjCLM, rankOne_apply, ContinuousLinearMap.comp_apply, hinner]

/-- Conjugation transports the Krein rank-one operator provided the unitary intertwines the
fundamental symmetries.
-/
@[simp] lemma conjCLM_kreinRankOne
    (U : E ≃ₗᵢ[𝕜] F)
    (hU : Intertwines (K := K) (K' := K') (U.toContinuousLinearEquiv.toContinuousLinearMap))
    (u : E) :
    conjCLM (U := U.toContinuousLinearEquiv) (kreinRankOne (K := K) u)
      = kreinRankOne (K := K') (U u) := by
  have hJU : U (K.J u) = K'.J (U u) := by
    -- `intertwines_apply` gives `K'.J (U u) = U (K.J u)`.
    simpa using
      (intertwines_apply (K := K) (K' := K')
        (U := U.toContinuousLinearEquiv.toContinuousLinearMap) hU u).symm
  simpa [kreinRankOne, hJU] using
    (conjCLM_rankOne (K := K) (K' := K') (U := U) u (K.J u))

/-- Transport of Kapustin’s bounded perturbation under a unitary intertwining equivalence. -/
@[simp] lemma conjCLM_mkKapustinOperator
    (U : E ≃ₗᵢ[𝕜] F)
    (hU : Intertwines (K := K) (K' := K') (U.toContinuousLinearEquiv.toContinuousLinearMap))
    (A : E →L[𝕜] E) (u : E) :
    conjCLM (U := U.toContinuousLinearEquiv) (mkKapustinOperator (K := K) A u)
      = mkKapustinOperator (K := K') (conjCLM (U := U.toContinuousLinearEquiv) A) (U u) := by
  -- Expand `mkKapustinOperator` and use linearity of `conjCLM`.
  simp [mkKapustinOperator, conjCLM_sub,
    conjCLM_kreinRankOne (K := K) (K' := K') (U := U) hU u]

/-!
## Transport of the Kapustin non-real eigenvalue scalar condition

For the non-real spectral parameter `z`, Kapustin’s eigenvalue condition for the rank-one
perturbation can be written entirely in terms of the unperturbed resolvent `(A - z I)⁻¹`.

The scalar condition is invariant under unitary equivalences intertwining the fundamental
symmetries.
-/

/-- The `shift` operator `A - z I` is compatible with conjugation. -/
@[simp] lemma conjCLM_shift
    (U : E ≃L[𝕜] F) (A : E →L[𝕜] E) (z : 𝕜) :
    conjCLM (U := U) (shift (K := K) A z)
      = shift (K := K') (conjCLM (U := U) A) z := by
  -- `shift A z` is definitionally `A - z • ContinuousLinearMap.id`.
  simp [shift, conjCLM_sub, conjCLM_smul, conjCLM_id]

/-- Krein inner product is preserved by a unitary intertwining equivalence. -/
lemma kreinInner_map_map
    (U : E ≃ₗᵢ[𝕜] F)
    (hU : Intertwines (K := K) (K' := K') (U.toContinuousLinearEquiv.toContinuousLinearMap))
    (x y : E) :
    ⟪U x, U y⟫[K'] = ⟪x, y⟫[K] := by
  have hJU : K'.J (U x) = U (K.J x) :=
    intertwines_apply (K := K) (K' := K')
      (U := U.toContinuousLinearEquiv.toContinuousLinearMap) hU x
  simpa [FundamentalSymmetry.kreinInner, hJU] using (U.inner_map_map (K.J x) y)

/-- Transport of the scalar coefficient appearing in Kapustin’s eigenvalue criterion.

This is the model-independent core statement: it only uses that `U` is unitary and intertwines
fundamental symmetries.
-/
lemma kapustinScalar_map
    (U : E ≃ₗᵢ[𝕜] F)
    (hU : Intertwines (K := K) (K' := K') (U.toContinuousLinearEquiv.toContinuousLinearMap))
    (u : E) (Az : E ≃L[𝕜] E) :
    ⟪K'.J (U u), (conjEquiv (U := U.toContinuousLinearEquiv) Az).symm (U u)⟫_𝕜
      = ⟪K.J u, Az.symm u⟫_𝕜 := by
  -- Identify the transported resolvent on `U u`.
  have hAzSymm : (conjEquiv (U := U.toContinuousLinearEquiv) Az).symm (U u)
      = U (Az.symm u) := by
    simpa using
      (conjEquiv_symm_apply_of_apply (U := U.toContinuousLinearEquiv) (e := Az) u)
  -- Intertwining gives the transport of `J`.
  have hJU : K'.J (U u) = U (K.J u) :=
    intertwines_apply (K := K) (K' := K')
      (U := U.toContinuousLinearEquiv.toContinuousLinearMap) hU u
  -- Conclude by unitary invariance of the Hilbert inner product.
  simpa [hJU, hAzSymm] using (U.inner_map_map (K.J u) (Az.symm u))

/-- Invariance of Kapustin’s scalar eigenvalue condition `⟪J u, (A - zI)⁻¹ u⟫ = 1`.

The statement is written in terms of the abstract resolvent equivalence `Az` implementing the
shift `(A - zI)`; in analytic models, `Az` will typically be produced from resolvent estimates.
-/
theorem kapustinScalar_eq_one_iff
    (U : E ≃ₗᵢ[𝕜] F)
    (hU : Intertwines (K := K) (K' := K') (U.toContinuousLinearEquiv.toContinuousLinearMap))
    (u : E) (Az : E ≃L[𝕜] E) :
    (⟪K.J u, Az.symm u⟫_𝕜 = 1)
      ↔ (⟪K'.J (U u), (conjEquiv (U := U.toContinuousLinearEquiv) Az).symm (U u)⟫_𝕜 = 1) := by
  constructor
  · intro h
    have h' := kapustinScalar_map (K := K) (K' := K') (U := U) hU u Az
    -- Rewrite the target using `h'`.
    simpa [h'] using h
  · intro h
    have h' := kapustinScalar_map (K := K) (K' := K') (U := U) hU u Az
    -- Rewrite the source using `h'`.
    simpa [h'] using h

/-- Full transport of Kapustin’s non-real eigenvalue criterion.

Once you have a unitary equivalence between two analytic realizations that intertwines the
fundamental symmetries, the eigenvalue criterion transfers.
-/
theorem exists_nonzero_eigenvector_kapustin_iff
    (U : E ≃ₗᵢ[𝕜] F)
    (hU : Intertwines (K := K) (K' := K') (U.toContinuousLinearEquiv.toContinuousLinearMap))
    (A : E →L[𝕜] E) (u : E) (z : 𝕜)
    (Az : E ≃L[𝕜] E) (hAz : Az.toContinuousLinearMap = shift (K := K) A z) :
    (∃ x : E, x ≠ 0 ∧ mkKapustinOperator (K := K) A u x = z • x)
      ↔ (∃ y : F, y ≠ 0 ∧
        mkKapustinOperator (K := K')
          (conjCLM (U := U.toContinuousLinearEquiv) A) (U u) y = z • y) := by
  -- Kapustin’s criterion in `E`.
  have hE := exists_nonzero_eigenvector_kapustin_iff_inner_eq_one
    (K := K) (A := A) (u := u) (z := z) (Az := Az) hAz
  -- Build the transported shift equivalence in `F`.
  let A' : F →L[𝕜] F := conjCLM (U := U.toContinuousLinearEquiv) A
  let Az' : F ≃L[𝕜] F := conjEquiv (U := U.toContinuousLinearEquiv) Az
  have hAz' : Az'.toContinuousLinearMap = shift (K := K') A' z := by
    -- Rewrite `Az'.toCLM` as a conjugation of `Az.toCLM`, then use compatibility with `shift`.
    have h1 : Az'.toContinuousLinearMap = conjCLM (U := U.toContinuousLinearEquiv) Az.toContinuousLinearMap := by
      simpa [Az'] using (conjEquiv_toContinuousLinearMap (U := U.toContinuousLinearEquiv) (e := Az))
    -- Chain the rewrites explicitly so simp does not have to guess the intended direction.
    calc
      Az'.toContinuousLinearMap
          = conjCLM (U := U.toContinuousLinearEquiv) Az.toContinuousLinearMap := h1
      _   = conjCLM (U := U.toContinuousLinearEquiv) (shift (K := K) A z) := by simpa [hAz]
      _   = shift (K := K') A' z := by
            simpa [A'] using
              (conjCLM_shift (K := K) (K' := K') (U := U.toContinuousLinearEquiv) (A := A) (z := z))
  -- Kapustin’s criterion in `F`.
  have hF := exists_nonzero_eigenvector_kapustin_iff_inner_eq_one
    (K := K') (A := A') (u := U u) (z := z) (Az := Az') hAz'
  -- The scalar condition is invariant.
  have hScalar : (⟪K.J u, Az.symm u⟫_𝕜 = 1) ↔
      (⟪K'.J (U u), Az'.symm (U u)⟫_𝕜 = 1) := by
    -- First rewrite the RHS in terms of `conjEquiv` (definition of `Az'`).
    simpa [Az'] using
      (kapustinScalar_eq_one_iff (K := K) (K' := K') (U := U) hU u Az)
  -- Glue.
  exact hE.trans (hScalar.trans hF.symm)

end FundamentalSymmetry

end Krein
