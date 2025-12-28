
/-
  Rank-one perturbations in Krein spaces.

  This file is designed to support constructions of the form
      T := M - [·,u] u
  where `M` is a (typically multiplication) operator and `[·,·]` is the Krein inner product.

  The key fact (to be proved once the appropriate simp-lemmas are available in your environment)
  is that `x ↦ [x,u] u` is Krein-selfadjoint, i.e. equals its Krein adjoint.
  In Hilbert language, this is the rank-one operator `rankOne u (J u)`.

  NOTE:
  mathlib already contains a rank-one bounded operator `ContinuousLinearMap.rankOne` (and usually
  simp lemmas for its adjoint). If your local mathlib version uses a different name or API,
  adapt the alias below.
-/

import Mathlib.Analysis.InnerProductSpace.RankOne
import KapustinFormalization.Krein.Basic

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

-- Alias to the mathlib rank-one operator.
-- (If mathlib does not provide `ContinuousLinearMap.rankOne` in your version, define it as
--  `x ↦ ⟪v, x⟫ • u` and prove boundedness.)
abbrev rankOne (u v : E) : E →L[𝕜] E := ContinuousLinearMap.rankOne 𝕜 u v

/-!
## Basic calculus for `rankOne`

We provide a small set of lemmas about composing bounded operators with rank-one maps.

While mathlib already contains a rich API for `ContinuousLinearMap.rankOne`, these lemmas are
*intentionally re-proved* here in a way that is robust across minor API changes, and to keep the
Kapustin/Krein layer self-contained.

All statements are purely algebraic consequences of the defining formula

`rankOne u v x = ⟪v, x⟫ • u`.
-/

@[simp] lemma rankOne_apply (u v x : E) :
    (rankOne (K := K) u v) x = (⟪v, x⟫_𝕜) • u := by
  rfl

@[simp] lemma comp_rankOne (T : E →L[𝕜] E) (u v : E) :
    T.comp (rankOne (K := K) u v) = rankOne (K := K) (T u) v := by
  ext x
  simp [ContinuousLinearMap.comp_apply, map_smul]

@[simp] lemma rankOne_adjoint (u v : E) :
    (rankOne (K := K) u v).adjoint = rankOne (K := K) v u := by
  classical
  -- Use the characterization of the adjoint via matrix coefficients.
  --
  -- `eq_adjoint_iff` is robust and avoids relying on a specific lemma name for the adjoint of
  -- `rankOne` (which has changed across some mathlib versions).
  -- We first show the equivalent symmetric statement
  -- `rankOne v u = (rankOne u v)†`, then finish by symmetry.
  have h : rankOne (K := K) v u = (rankOne (K := K) u v).adjoint := by
    refine (ContinuousLinearMap.eq_adjoint_iff
      (A := rankOne (K := K) v u) (B := rankOne (K := K) u v)).2 ?_
    intro x y
    -- Unfold `rankOne` and reduce to inner-product algebra.
    simp [rankOne_apply, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]
  simpa using h.symm

@[simp] lemma rankOne_comp (T : E →L[𝕜] E) (u v : E) :
    (rankOne (K := K) u v).comp T = rankOne (K := K) u (T.adjoint v) := by
  ext x
  -- Use the defining property of the adjoint:
  --   ⟪v, T x⟫ = ⟪T† v, x⟫.
  -- (available in mathlib as either `adjoint_inner_left` or the method form
  --  `T.adjoint_inner_left`/`ContinuousLinearMap.adjoint_inner_left` depending on version)
  simpa [ContinuousLinearMap.comp_apply] using (T.adjoint_inner_left v x)

/-- The Krein rank-one operator `x ↦ [x,u] u`. -/
noncomputable def kreinRankOne (u : E) : E →L[𝕜] E :=
  rankOne (K := K) u (K.J u)

lemma kreinRankOne_apply (u x : E) :
    (kreinRankOne (K := K) u) x = (⟪K.J u, x⟫_𝕜) • u := by
  rfl

lemma kreinRankOne_apply_conj (u x : E) :
    (kreinRankOne (K := K) u) x = IsROrC.conj (⟪x, K.J u⟫_𝕜) • u := by
  -- `conj_inner_symm` says `conj ⟪x, y⟫ = ⟪y, x⟫`.
  -- Apply it with `y := J u`.
  simpa [kreinRankOne_apply (K := K) u x, conj_inner_symm]

/-!
## Krein selfadjointness of the basic rank-one perturbation

The Kapustin / Krein–Hilbert–Pólya constructions repeatedly use the rank-one operator

`P_u : x ↦ [x,u] u`.

In the fundamental-symmetry model, the Krein bracket is
`[x,u] = ⟪J x, u⟫ = ⟪x, J u⟫` (the second equality uses `J`-selfadjointness).
Hence

`P_u x = IsROrC.conj (⟪x, J u⟫) • u`.

The conjugation is expected: in mathlib, `⟪·,·⟫` is conjugate-linear in the *first* argument and
linear in the *second*, so the functional `x ↦ [x,u]` is linear (hence defines a bounded operator)
precisely when expressed using the Hilbert inner product with `x` as the second argument.

Indeed, by `conj_inner_symm` we have

`⟪J u, x⟫ = IsROrC.conj (⟪x, J u⟫)`,

so the operator `P_u` is exactly mathlib’s rank-one operator `rankOne u (J u)`.

The key point: **no extra hypothesis on `u` is required** for `P_u` to be Krein-selfadjoint.
-/

@[simp] lemma kreinAdjoint_rankOne (u v : E) :
    (rankOne (K := K) u v)†[K] = rankOne (K := K) (K.J v) (K.J u) := by
  classical
  -- Expand the Krein adjoint and then reduce everything to explicit `rankOne_apply` formulas.
  --
  -- This is robust: it needs only the standard fact `(rankOne u v)† = rankOne v u` from mathlib
  -- plus the elementary composition lemmas proved above.
  unfold FundamentalSymmetry.kreinAdjoint
  -- First turn the Hilbert adjoint into a swapped rank-one map, then push `J` through on both
  -- sides using `comp_rankOne` and `rankOne_comp`.
  -- Finally use `J† = J` (selfadjointness) and `J ∘ J = id` (involution).
  simp [rankOne, comp_rankOne, rankOne_comp, K.isSelfAdjoint_J, K.involutive_J]

lemma isKreinSelfAdjoint_kreinRankOne (u : E) :
    IsKreinSelfAdjoint (K := K) (kreinRankOne (K := K) u) := by
  classical
  -- `P_u = rankOne u (J u)` and its Krein adjoint is itself.
  unfold FundamentalSymmetry.IsKreinSelfAdjoint kreinRankOne
  -- Reduce to the `kreinAdjoint_rankOne` lemma and `J² = id`.
  simpa [kreinAdjoint_rankOne (K := K), K.involutive_J]

end FundamentalSymmetry

end Krein
