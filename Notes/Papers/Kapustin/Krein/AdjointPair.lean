/--
Adjoint-pair characterization of the Krein adjoint.

In the fundamental-symmetry model, a Krein space is represented by a Hilbert space `E` together with
a bounded selfadjoint involution `J` (a *fundamental symmetry*). The induced indefinite Hermitian
form is

`[x,y] := ⟪J x, y⟫`.

The Krein adjoint of a bounded operator is defined algebraically by

`T†[K] := J ∘ T† ∘ J`.

This file proves:

* `kreinInner_apply_eq_kreinInner_kreinAdjoint`:
    `⟪T x, y⟫[K] = ⟪x, (T†[K]) y⟫[K]`;
* `IsKreinAdjointPair` as the canonical adjoint-pair predicate for `[·,·]`;
* uniqueness: an adjoint pair is uniquely determined, hence
    `IsKreinAdjointPair T S ↔ S = T†[K]`;
* a symmetry characterization of Krein selfadjointness.

These lemmas are the canonical interface for transporting results from Hilbert adjoints to
indefinite inner product spaces, and will be used downstream when importing analytic information
from Kapustin’s Hardy/Mellin/Sonin models.
-/

import KapustinFormalization.Krein.Basic

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-- Pointwise involutivity of the fundamental symmetry. -/
lemma J_apply_J (x : E) : K.J (K.J x) = x := by
  have hx := congrArg (fun T : E →L[𝕜] E => T x) K.involutive_J
  simpa [ContinuousLinearMap.comp_apply] using hx

/--
A robust form of the Hilbert adjoint identity.

Mathlib provides `adjoint_inner_right`; we re-derive the corresponding statement from
`adjoint_inner_left` and Hermitian symmetry in order to minimize dependency on lemma names.
-/
lemma inner_adjoint_right (T : E →L[𝕜] E) (x y : E) :
    ⟪x, T.adjoint y⟫_𝕜 = ⟪T x, y⟫_𝕜 := by
  -- Apply conjugation and use `conj_inner_symm`.
  apply IsROrC.conj_injective
  -- After conjugation, both sides become the standard `adjoint_inner_left` identity.
  simpa [conj_inner_symm] using (T.adjoint_inner_left y x)

/--
**Fundamental adjointness property of the Krein adjoint.**

For all `x y`,

`[T x, y] = [x, T†[K] y]`.
-/
lemma kreinInner_apply_eq_kreinInner_kreinAdjoint
    (T : E →L[𝕜] E) (x y : E) :
    ⟪T x, y⟫[K] = ⟪x, (T†[K]) y⟫[K] := by
  classical
  -- Expand the Krein bracket and Krein adjoint.
  unfold FundamentalSymmetry.kreinInner FundamentalSymmetry.kreinAdjoint
  -- Symmetry of `J` as a linear map.
  have hsymm : (K.J.toLinearMap).IsSymmetric := by
    simpa using K.isSelfAdjoint_J.isSymmetric
  -- Pointwise involution `J (J z) = z`.
  have hJ2 : ∀ z : E, K.J (K.J z) = z := by
    intro z
    simpa using (J_apply_J (K := K) z)
  -- Now compute.
  calc
    ⟪K.J (T x), y⟫_𝕜
        = ⟪T x, K.J y⟫_𝕜 := by
            simpa using (hsymm (T x) y)
    _   = ⟪x, T.adjoint (K.J y)⟫_𝕜 := by
            simpa using (inner_adjoint_right (K := K) T x (K.J y)).symm
    _   = ⟪K.J x, K.J (T.adjoint (K.J y))⟫_𝕜 := by
            have htmp := hsymm x (K.J (T.adjoint (K.J y)))
            -- `htmp` is the forward direction; we need the reverse.
            simpa [hJ2 (T.adjoint (K.J y))] using htmp.symm
    _   = ⟪K.J x, (K.J.comp (T.adjoint.comp K.J)) y⟫_𝕜 := by
            simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_assoc]

/--
`IsKreinAdjointPair T S` means that `S` is an adjoint of `T` with respect to the Krein bracket.

This is the natural interface for reasoning about Krein adjoints in the same style as
`LinearMap.IsAdjointPair` in the sesquilinear-form API.
-/
def IsKreinAdjointPair (T S : E →L[𝕜] E) : Prop :=
  ∀ x y, ⟪T x, y⟫[K] = ⟪x, S y⟫[K]

/-- The Krein adjoint is an adjoint for the Krein bracket. -/
lemma isKreinAdjointPair_kreinAdjoint (T : E →L[𝕜] E) :
    IsKreinAdjointPair (K := K) T (T†[K]) := by
  intro x y
  simpa using (kreinInner_apply_eq_kreinInner_kreinAdjoint (K := K) T x y)

/--
**Uniqueness** of the Krein adjoint.

If `S` satisfies the adjoint-pair identity with respect to the Krein bracket, then necessarily
`S = T†[K]`.

The proof reduces to Hilbert-space adjoint uniqueness via `ContinuousLinearMap.eq_adjoint_iff`.
-/
lemma kreinAdjoint_eq_of_isKreinAdjointPair
    (T S : E →L[𝕜] E)
    (h : IsKreinAdjointPair (K := K) T S) :
    S = T†[K] := by
  classical
  -- Pointwise involution `J (J z) = z`.
  have hJ2 : ∀ z : E, K.J (K.J z) = z := fun z => J_apply_J (K := K) z

  -- Conjugate `T` by `J` on the *right* so that the hypothesis becomes a Hilbert adjoint relation.
  let A : E →L[𝕜] E := K.J.comp (T.comp K.J)

  have hA : ∀ x y, ⟪A x, y⟫_𝕜 = ⟪x, S y⟫_𝕜 := by
    intro x y
    -- Use the Krein adjoint-pair identity with `x := J x`.
    have hxy := h (K.J x) y
    -- Expand the Krein bracket on both sides.
    -- The right-hand side simplifies using `J² = id`.
    simpa [IsKreinAdjointPair, FundamentalSymmetry.kreinInner, A,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_assoc, hJ2 x] using hxy

  -- Identify `A` as the Hilbert adjoint of `S`.
  have hEq : A = S.adjoint := by
    refine (ContinuousLinearMap.eq_adjoint_iff (A := A) (B := S)).2 ?_
    intro x y
    exact hA x y

  -- Hence `S = A†`.
  have hEq' : A.adjoint = S := by
    have := congrArg ContinuousLinearMap.adjoint hEq
    -- `simp` turns `S.adjoint.adjoint` into `S`.
    simpa using this

  -- Compute `A† = J ∘ T† ∘ J`.
  calc
    S = A.adjoint := by simpa using hEq'.symm
    _ = T†[K] := by
          -- Expand `A` and simplify using `adjoint_comp` and `J† = J`.
          simp [A, FundamentalSymmetry.kreinAdjoint, ContinuousLinearMap.comp_assoc,
            K.isSelfAdjoint_J]

/-- `IsKreinAdjointPair` characterizes the Krein adjoint. -/
lemma isKreinAdjointPair_iff_eq_kreinAdjoint (T S : E →L[𝕜] E) :
    IsKreinAdjointPair (K := K) T S ↔ S = T†[K] := by
  constructor
  · intro h
    exact kreinAdjoint_eq_of_isKreinAdjointPair (K := K) (T := T) (S := S) h
  · intro h
    subst h
    exact isKreinAdjointPair_kreinAdjoint (K := K) T

/-- Krein selfadjointness is symmetry with respect to the Krein bracket. -/
lemma isKreinSelfAdjoint_iff_forall_kreinInner (T : E →L[𝕜] E) :
    IsKreinSelfAdjoint (K := K) T ↔ ∀ x y, ⟪T x, y⟫[K] = ⟪x, T y⟫[K] := by
  constructor
  · intro hT x y
    -- Use the adjoint-pair identity with `T†[K]` and rewrite by `hT`.
    simpa [FundamentalSymmetry.IsKreinSelfAdjoint, hT] using
      (kreinInner_apply_eq_kreinInner_kreinAdjoint (K := K) T x y)
  · intro h
    -- View the right-hand side as `IsKreinAdjointPair T T` and use uniqueness.
    have hpair : IsKreinAdjointPair (K := K) T T := h
    have hEq : T = T†[K] :=
      kreinAdjoint_eq_of_isKreinAdjointPair (K := K) (T := T) (S := T) hpair
    -- The definition uses `T†[K] = T`.
    simpa [FundamentalSymmetry.IsKreinSelfAdjoint] using hEq.symm

end FundamentalSymmetry

end Krein
