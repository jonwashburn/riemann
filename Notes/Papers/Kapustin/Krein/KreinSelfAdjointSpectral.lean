/--
Spectral and eigenvector structure for bounded Krein-selfadjoint operators.

This file formalizes the *model-independent* (purely algebraic) facts about eigenpairs of
bounded operators that are selfadjoint with respect to the Krein bracket

`[x,y] := ⟪J x, y⟫`.

The key results are:

1. **Equivalence with a Hilbert selfadjoint operator**: `T` is Krein-selfadjoint iff `J ∘ T`
   is Hilbert-selfadjoint.

2. **Krein orthogonality of eigenvectors**: if `T x = μ x` and `T y = ν y`, then

   `(conj μ - ν) * [x,y] = 0`.

   In particular, if `ν ≠ conj μ` then `[x,y]=0`. When `μ,ν` are real and `μ ≠ ν`, this is the
   expected orthogonality statement.

3. **Non-real eigenvalues have neutral eigenvectors**: if `T x = μ x` and `[x,x] ≠ 0`, then
   necessarily `conj μ = μ`.

These are canonical lemmas in Krein space spectral theory and are used downstream in Kapustin’s
framework to control possible non-real spectrum.
-/

import KapustinFormalization.Krein.AdjointPair

namespace Krein

open scoped ComplexConjugate

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-!
## Krein selfadjointness as Hilbert selfadjointness of `J ∘ T`

The algebraic identity `T†[K] = J ∘ T† ∘ J` implies that Krein selfadjointness is equivalent to
Hilbert selfadjointness of the composite `J ∘ T`. This is a standard and extremely useful
normal form.
-/

/-- If `T` is Krein-selfadjoint, then `T† ∘ J = J ∘ T`. -/
lemma adjoint_comp_J_eq_J_comp
    (T : E →L[𝕜] E)
    (hT : IsKreinSelfAdjoint (K := K) T) :
    T.adjoint.comp K.J = K.J.comp T := by
  -- Compose the defining identity `J ∘ T† ∘ J = T` on the left by `J`.
  have h := congrArg (fun S : E →L[𝕜] E => K.J.comp S) hT
  -- Simplify `J ∘ (J ∘ T† ∘ J)` using involutivity of `J`.
  simpa [FundamentalSymmetry.kreinAdjoint, ContinuousLinearMap.comp_assoc, K.involutive_J]
    using h

/-- If `T` is Krein-selfadjoint, then `J ∘ T` is Hilbert-selfadjoint. -/
lemma isSelfAdjoint_J_comp_of_isKreinSelfAdjoint
    (T : E →L[𝕜] E)
    (hT : IsKreinSelfAdjoint (K := K) T) :
    IsSelfAdjoint (K.J.comp T) := by
  -- Expand `(J ∘ T)† = T† ∘ J† = T† ∘ J` and use `T† ∘ J = J ∘ T`.
  have hcomm := adjoint_comp_J_eq_J_comp (K := K) (T := T) hT
  -- `IsSelfAdjoint` is definitional equality with the adjoint.
  -- `simp` uses `K.isSelfAdjoint_J` to rewrite `J† = J`.
  simpa [IsSelfAdjoint, ContinuousLinearMap.adjoint_comp, K.isSelfAdjoint_J] using hcomm

/-- If `J ∘ T` is Hilbert-selfadjoint, then `T` is Krein-selfadjoint. -/
lemma isKreinSelfAdjoint_of_isSelfAdjoint_J_comp
    (T : E →L[𝕜] E)
    (hJT : IsSelfAdjoint (K.J.comp T)) :
    IsKreinSelfAdjoint (K := K) T := by
  -- Start from `(J ∘ T)† = J ∘ T`.
  have hEq : (K.J.comp T).adjoint = K.J.comp T := hJT
  -- Rewrite the adjoint of the composite to isolate `T† ∘ J = J ∘ T`.
  have hcomm : T.adjoint.comp K.J = K.J.comp T := by
    simpa [ContinuousLinearMap.adjoint_comp, K.isSelfAdjoint_J] using hEq
  -- Now compute the Krein adjoint:
  -- `T†[K] = J ∘ T† ∘ J = J ∘ (J ∘ T) = T`.
  unfold FundamentalSymmetry.IsKreinSelfAdjoint FundamentalSymmetry.kreinAdjoint
  -- Replace `T† ∘ J` using `hcomm`.
  calc
    K.J.comp (T.adjoint.comp K.J)
        = K.J.comp (K.J.comp T) := by simpa [hcomm]
    _ = (K.J.comp K.J).comp T := by simp [ContinuousLinearMap.comp_assoc]
    _ = (ContinuousLinearMap.id 𝕜 E).comp T := by simp [K.involutive_J]
    _ = T := by simp

/-- **Canonical normal form**: `T` is Krein-selfadjoint iff `J ∘ T` is Hilbert-selfadjoint. -/
theorem isKreinSelfAdjoint_iff_isSelfAdjoint_J_comp (T : E →L[𝕜] E) :
    IsKreinSelfAdjoint (K := K) T ↔ IsSelfAdjoint (K.J.comp T) := by
  constructor
  · intro hT
    exact isSelfAdjoint_J_comp_of_isKreinSelfAdjoint (K := K) (T := T) hT
  · intro hJT
    exact isKreinSelfAdjoint_of_isSelfAdjoint_J_comp (K := K) (T := T) hJT

/-!
## Eigenvector orthogonality and realness constraints

We phrase “eigenpair” statements in the same style as the Kapustin rank-one files: `T x = μ • x`
with a nonzero vector `x`.

The core algebraic identity is

`(conj μ - ν) * [x,y] = 0`.

It is derived by applying Krein symmetry

`[T x, y] = [x, T y]`

and using sesquilinearity of the bracket.
-/

/-- Scalar identity relating the Krein bracket of two eigenvectors of a Krein-selfadjoint operator.

If `T x = μ x` and `T y = ν y`, then

`(conj μ - ν) * [x,y] = 0`.
-/
lemma sub_mul_kreinInner_eq_zero_of_isKreinSelfAdjoint_of_eigenpairs
    (T : E →L[𝕜] E) (μ ν : 𝕜) (x y : E)
    (hT : IsKreinSelfAdjoint (K := K) T)
    (hx : T x = μ • x) (hy : T y = ν • y) :
    (IsROrC.conj μ - ν) * ⟪x, y⟫[K] = 0 := by
  -- Krein symmetry: `[T x, y] = [x, T y]`.
  have hsymm : ∀ a b, ⟪T a, b⟫[K] = ⟪a, T b⟫[K] :=
    (isKreinSelfAdjoint_iff_forall_kreinInner (K := K) T).1 hT
  have hxy : ⟪T x, y⟫[K] = ⟪x, T y⟫[K] := hsymm x y
  -- Rewrite both sides using the eigenvalue hypotheses and sesquilinearity.
  have hscalar : IsROrC.conj μ * ⟪x, y⟫[K] = ν * ⟪x, y⟫[K] := by
    -- Expand the Krein bracket and simplify.
    -- Left: `[μx,y] = conj μ * [x,y]`.
    -- Right: `[x,νy] = ν * [x,y]`.
    simpa [FundamentalSymmetry.kreinInner, hx, hy, map_smul, inner_smul_left, inner_smul_right]
      using hxy
  -- Convert `conj μ * a = ν * a` to `(conj μ - ν) * a = 0`.
  have : IsROrC.conj μ * ⟪x, y⟫[K] - ν * ⟪x, y⟫[K] = 0 := sub_eq_zero.mpr hscalar
  simpa [sub_mul] using this

/-- If `ν ≠ conj μ`, then eigenvectors for `μ` and `ν` are Krein-orthogonal. -/
lemma kreinInner_eq_zero_of_isKreinSelfAdjoint_of_eigenpairs_of_ne
    (T : E →L[𝕜] E) (μ ν : 𝕜) (x y : E)
    (hT : IsKreinSelfAdjoint (K := K) T)
    (hx : T x = μ • x) (hy : T y = ν • y)
    (hμν : IsROrC.conj μ ≠ ν) :
    ⟪x, y⟫[K] = 0 := by
  have hmul :=
    sub_mul_kreinInner_eq_zero_of_isKreinSelfAdjoint_of_eigenpairs (K := K)
      (T := T) (μ := μ) (ν := ν) (x := x) (y := y) hT hx hy
  have hne : IsROrC.conj μ - ν ≠ 0 := sub_ne_zero.mpr hμν
  exact (mul_eq_zero.mp hmul).resolve_left hne

/-- If `T x = μ x` and `[x,x] ≠ 0`, then `μ` must be real in the sense `conj μ = μ`. -/
lemma conj_eq_of_isKreinSelfAdjoint_of_eigenpair_of_kreinInner_self_ne_zero
    (T : E →L[𝕜] E) (μ : 𝕜) (x : E)
    (hT : IsKreinSelfAdjoint (K := K) T)
    (hx : T x = μ • x)
    (hxx : ⟪x, x⟫[K] ≠ 0) :
    IsROrC.conj μ = μ := by
  have hmul :=
    sub_mul_kreinInner_eq_zero_of_isKreinSelfAdjoint_of_eigenpairs (K := K)
      (T := T) (μ := μ) (ν := μ) (x := x) (y := x) hT hx hx
  -- From `(conj μ - μ) * [x,x] = 0` and `[x,x] ≠ 0`, deduce `conj μ - μ = 0`.
  have hzero : IsROrC.conj μ - μ = 0 := (mul_eq_zero.mp hmul).resolve_right hxx
  exact sub_eq_zero.mp hzero

/-- Non-real eigenvalues force neutral eigenvectors: if `conj μ ≠ μ` and `T x = μ x`, then
`[x,x] = 0`. -/
lemma kreinInner_self_eq_zero_of_isKreinSelfAdjoint_of_eigenpair_of_conj_ne
    (T : E →L[𝕜] E) (μ : 𝕜) (x : E)
    (hT : IsKreinSelfAdjoint (K := K) T)
    (hx : T x = μ • x)
    (hμ : IsROrC.conj μ ≠ μ) :
    ⟪x, x⟫[K] = 0 := by
  -- Apply the orthogonality lemma with `y = x` and `ν = μ`.
  simpa using
    (kreinInner_eq_zero_of_isKreinSelfAdjoint_of_eigenpairs_of_ne (K := K)
      (T := T) (μ := μ) (ν := μ) (x := x) (y := x) hT hx hx hμ)

end FundamentalSymmetry

end Krein
