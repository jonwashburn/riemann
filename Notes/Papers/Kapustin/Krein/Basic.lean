
/-
  Krein spaces in the "fundamental symmetry" model.

  Design principle:
  A (Hilbertizable) Krein space is represented as a Hilbert space `E` together with a bounded
  selfadjoint involution `J : E →L[𝕜] E`. The indefinite inner product is then

      [x, y] := ⟪J x, y⟫.

  This representation maximally reuses mathlib's Hilbert space topology and operator theory
  (adjoints, spectrum, rank-one operators, L₂, etc.), and matches the representation used in
  Kapustin's Krein-space Hilbert–Pólya constructions.

  This file is intended to be upstreamable to mathlib (or, at minimum, to avoid any duplication):
  it introduces only the minimal core API needed by Kapustin-style operator constructions.

  Next layers (separate files) should cover:
  * Pontryagin spaces (finite negative index),
  * J-unitary maps, Krein-isometries,
  * Krein orthogonal complements,
  * rank-one perturbation calculus and resolvent identities,
  * (eventually) spectral theory in Pontryagin spaces.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib

open scoped ComplexConjugate

namespace Krein

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A *fundamental symmetry* on a Hilbert space: a bounded selfadjoint involution `J`. -/
structure FundamentalSymmetry (𝕜 : Type*) (E : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] where
  /-- The fundamental symmetry. -/
  J : E →L[𝕜] E
  /-- Selfadjointness of `J`. -/
  isSelfAdjoint_J : IsSelfAdjoint J
  /-- Involution property `J ∘ J = id`. -/
  involutive_J : J.comp J = ContinuousLinearMap.id 𝕜 E

attribute [simp] FundamentalSymmetry.involutive_J

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

@[simp] lemma J_comp_J : K.J.comp K.J = ContinuousLinearMap.id 𝕜 E := K.involutive_J

/-- The Krein inner product induced by `J`. -/
noncomputable def kreinInner (x y : E) : 𝕜 := ⟪K.J x, y⟫_𝕜

notation3 "⟪" x ", " y "⟫[" K "]" => FundamentalSymmetry.kreinInner (K := K) x y

/-- Conjugate symmetry of the Krein inner product. -/
lemma kreinInner_conj_symm (x y : E) :
    IsROrC.conj (⟪x, y⟫[K]) = ⟪y, x⟫[K] := by
  -- `conj_inner_symm` swaps arguments, then `J`-symmetry swaps `J` to the other slot.
  have hsymm : (K.J.toLinearMap).IsSymmetric := by
    -- `IsSelfAdjoint` implies `IsSymmetric` for bounded operators.
    simpa using K.isSelfAdjoint_J.isSymmetric
  -- Expand, swap via `conj_inner_symm`, then apply symmetry.
  simp [FundamentalSymmetry.kreinInner, conj_inner_symm, hsymm _ _]

/-- The Krein adjoint of a bounded operator: `T^# = J ∘ T† ∘ J`. -/
noncomputable def kreinAdjoint (T : E →L[𝕜] E) : E →L[𝕜] E :=
  K.J.comp (T.adjoint.comp K.J)

notation3 T "†[" K "]" => FundamentalSymmetry.kreinAdjoint (K := K) T

/-- Krein selfadjointness: `T = T^#` (i.e. selfadjoint for the indefinite inner product). -/
def IsKreinSelfAdjoint (T : E →L[𝕜] E) : Prop := T†[K] = T

/-!
## Basic algebra of the Krein adjoint

The map `T ↦ T†[K]` is a *conjugation* of the usual Hilbert adjoint by the fundamental symmetry
`J`. Consequently it inherits the standard `★`-algebra identities.

We record the ones that are repeatedly used downstream (rank-one perturbations, resolvent calculus
in Pontryagin spaces, etc.).

These lemmas are designed to be upstreamable to mathlib as part of a general “Krein spaces via
fundamental symmetries” API.
-/

@[simp] lemma kreinAdjoint_add (A B : E →L[𝕜] E) :
    (A + B)†[K] = A†[K] + B†[K] := by
  -- Pointwise proof avoids relying on any particular `map_add` simp lemma.
  ext x
  simp [FundamentalSymmetry.kreinAdjoint, ContinuousLinearMap.comp_apply, map_add]

@[simp] lemma kreinAdjoint_sub (A B : E →L[𝕜] E) :
    (A - B)†[K] = A†[K] - B†[K] := by
  ext x
  simp [FundamentalSymmetry.kreinAdjoint, ContinuousLinearMap.comp_apply, map_sub]

@[simp] lemma kreinAdjoint_comp (A B : E →L[𝕜] E) :
    (A.comp B)†[K] = B†[K].comp A†[K] := by
  -- `adjoint_comp` flips order; conjugation by `J` respects order.
  simp [FundamentalSymmetry.kreinAdjoint, ContinuousLinearMap.comp_assoc]

@[simp] lemma kreinAdjoint_kreinAdjoint (A : E →L[𝕜] E) :
    (A†[K])†[K] = A := by
  -- Expand and use involutivity of the Hilbert adjoint and `J`.
  simp [FundamentalSymmetry.kreinAdjoint, ContinuousLinearMap.comp_assoc,
    K.isSelfAdjoint_J, K.involutive_J]

/-- If `T` is Hilbert-selfadjoint and commutes with `J`, then it is Krein-selfadjoint. -/
lemma isKreinSelfAdjoint_of_commute_of_isSelfAdjoint
    (T : E →L[𝕜] E)
    (hT : IsSelfAdjoint T)
    (hcomm : T.comp K.J = K.J.comp T) :
    IsKreinSelfAdjoint (K := K) T := by
  -- Algebra in the `ContinuousLinearMap` star-algebra:
  --   T†[K] = J ∘ T† ∘ J = J ∘ T ∘ J = (J ∘ J) ∘ T = T
  -- where `T† = T` and `T ∘ J = J ∘ T`.
  classical
  unfold IsKreinSelfAdjoint FundamentalSymmetry.kreinAdjoint
  -- reduce via the star and comp simp-lemmas from `Mathlib.Analysis.InnerProductSpace.Adjoint`.
  -- `simp` should close after rewriting `hcomm` and using `K.involutive_J`.
  -- (In some mathlib versions, you may need `simp [hT, hcomm, K.involutive_J]`.)
  simpa [hT, hcomm, K.involutive_J]

end FundamentalSymmetry

end Krein
