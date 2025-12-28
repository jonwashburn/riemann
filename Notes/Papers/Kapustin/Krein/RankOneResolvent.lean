/--
Rank-one resolvent calculus (Sherman–Morrison) for bounded operators.

This file is the **next structural layer** after `Krein/RankOne.lean`.

Kapustin’s constructions repeatedly use explicit inverses / resolvents of operators of the form

`A - rankOne u v`,

and, in particular, the special case `A - [·,u]u` where
`[x,u] u = (rankOne u (J u)) x` in the fundamental-symmetry model.

At the bounded-operator level, the relevant algebra is the Sherman–Morrison formula:
if `δ := 1 - ⟪v,u⟫` is nonzero, then

`(I - rankOne u v)⁻¹ = I + δ⁻¹ • rankOne u v`.

We also record a convenient kernel/eigenvector computation for
`A - rankOne u v` when `A : E ≃L[𝕜] E` is a boundedly invertible operator.

All results are stated in a way that avoids any dependence on a particular analytic model
(weighted `L²`, Hardy spaces, etc.).
-/

import Mathlib.Tactic
import KapustinFormalization.Krein.RankOne

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

section RankOneAlgebra

/-- Composition of two rank-one maps.

This is the Hilbert-space identity

`(|u⟩⟨v|) ∘ (|u'⟩⟨v'|) = ⟪v,u'⟫ · |u⟩⟨v'|`.

It is the algebraic heart of the Sherman–Morrison inversion.
-/
@[simp] lemma rankOne_comp_rankOne (u v u' v' : E) :
    (rankOne (K := K) u v).comp (rankOne (K := K) u' v')
      = (⟪v, u'⟫_𝕜) • (rankOne (K := K) u v') := by
  ext x
  simp [ContinuousLinearMap.comp_apply, rankOne_apply, inner_smul_right,
    smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- The square of a rank-one map is a scalar multiple of itself. -/
@[simp] lemma rankOne_sq (u v : E) :
    (rankOne (K := K) u v).comp (rankOne (K := K) u v)
      = (⟪v, u⟫_𝕜) • (rankOne (K := K) u v) := by
  simpa using rankOne_comp_rankOne (K := K) u v u v

end RankOneAlgebra

section ShermanMorrison

/-- Right inverse in the Sherman–Morrison formula.

If `δ := 1 - ⟪v,u⟫ ≠ 0`, then

`(I - rankOne u v) ∘ (I + δ⁻¹ • rankOne u v) = I`.
-/
lemma id_sub_rankOne_comp_id_add (u v : E)
    (hδ : ((1 : 𝕜) - ⟪v, u⟫_𝕜) ≠ 0) :
    ( (ContinuousLinearMap.id 𝕜 E - rankOne (K := K) u v).comp
        (ContinuousLinearMap.id 𝕜 E + (((1 : 𝕜) - ⟪v, u⟫_𝕜)⁻¹) • rankOne (K := K) u v) )
      = ContinuousLinearMap.id 𝕜 E := by
  classical
  -- Abbreviations.
  set P : E →L[𝕜] E := rankOne (K := K) u v
  set δ : 𝕜 := (1 : 𝕜) - ⟪v, u⟫_𝕜
  set c : 𝕜 := δ⁻¹

  -- Scalar identity: `(c - 1) - c*⟪v,u⟫ = 0`.
  have hcoeff : (c - (1 : 𝕜)) - c * ⟪v, u⟫_𝕜 = 0 := by
    calc
      (c - (1 : 𝕜)) - c * ⟪v, u⟫_𝕜 = c * ((1 : 𝕜) - ⟪v, u⟫_𝕜) - 1 := by
        -- commutative ring arithmetic
        ring
      _ = c * δ - 1 := by simp [δ]
      _ = (1 : 𝕜) - 1 := by
        -- `c*δ = 1` since `c = δ⁻¹`.
        have : c * δ = (1 : 𝕜) := by
          -- `simp` uses `inv_mul_cancel`.
          simpa [c] using (inv_mul_cancel hδ)
        simp [this]
      _ = 0 := by simp

  -- Main computation, pointwise.
  ext x
  -- Expand the composition, reduce to the scalar coefficient computed above.
  -- The only nontrivial algebraic step is `P (P x) = ⟪v,u⟫ • P x`.
  have hP2 : P (P x) = (⟪v, u⟫_𝕜) • P x := by
    -- from `rankOne_sq`, evaluated at `x`.
    simpa [P] using congrArg (fun T : E →L[𝕜] E => T x) (rankOne_sq (K := K) u v)

  -- Now unfold and simplify.
  -- We keep the proof robust by doing the computation in `E` directly.
  --
  -- `(I - P)(I + cP)x = x + ((c-1) - c⟪v,u⟫) • P x`.
  simp [ContinuousLinearMap.comp_apply, P, c, δ, map_add, map_sub, map_smul, hP2,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add, add_smul, smul_smul,
    mul_assoc, mul_left_comm, mul_comm, hcoeff]

/-- Left inverse in the Sherman–Morrison formula.

If `δ := 1 - ⟪v,u⟫ ≠ 0`, then

`(I + δ⁻¹ • rankOne u v) ∘ (I - rankOne u v) = I`.
-/
lemma id_add_comp_id_sub_rankOne (u v : E)
    (hδ : ((1 : 𝕜) - ⟪v, u⟫_𝕜) ≠ 0) :
    ( (ContinuousLinearMap.id 𝕜 E + (((1 : 𝕜) - ⟪v, u⟫_𝕜)⁻¹) • rankOne (K := K) u v).comp
        (ContinuousLinearMap.id 𝕜 E - rankOne (K := K) u v) )
      = ContinuousLinearMap.id 𝕜 E := by
  classical
  -- Same proof as the right-inverse, with the factors swapped.
  -- The scalar identity is identical.
  set P : E →L[𝕜] E := rankOne (K := K) u v
  set δ : 𝕜 := (1 : 𝕜) - ⟪v, u⟫_𝕜
  set c : 𝕜 := δ⁻¹

  have hcoeff : (c - (1 : 𝕜)) - c * ⟪v, u⟫_𝕜 = 0 := by
    calc
      (c - (1 : 𝕜)) - c * ⟪v, u⟫_𝕜 = c * ((1 : 𝕜) - ⟪v, u⟫_𝕜) - 1 := by
        ring
      _ = c * δ - 1 := by simp [δ]
      _ = (1 : 𝕜) - 1 := by
        have : c * δ = (1 : 𝕜) := by
          simpa [c] using (inv_mul_cancel hδ)
        simp [this]
      _ = 0 := by simp

  ext x
  have hP2 : P (P x) = (⟪v, u⟫_𝕜) • P x := by
    simpa [P] using congrArg (fun T : E →L[𝕜] E => T x) (rankOne_sq (K := K) u v)

  simp [ContinuousLinearMap.comp_apply, P, c, δ, map_add, map_sub, map_smul, hP2,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add, add_smul, smul_smul,
    mul_assoc, mul_left_comm, mul_comm, hcoeff]

end ShermanMorrison

section KernelAndEigenvector

/-- Kernel computation for a rank-one perturbation of an invertible operator.

Let `A` be a boundedly invertible operator (`A : E ≃L[𝕜] E`).
If `x` satisfies

`(A - rankOne u v) x = 0`,

then necessarily

`x = ⟪v,x⟫ • A⁻¹ u`.

This is Kapustin’s basic eigenvector ansatz: any kernel vector must be colinear with `A⁻¹ u`.
-/
lemma eq_smul_symm_u_of_sub_rankOne_apply_eq_zero
    (A : E ≃L[𝕜] E) (u v x : E)
    (hx : (A.toContinuousLinearMap - rankOne (K := K) u v) x = 0) :
    x = (⟪v, x⟫_𝕜) • (A.symm u) := by
  -- Apply `A⁻¹` to the equation `A x - ⟪v,x⟫ u = 0`.
  have hx' := congrArg (fun y => A.symm y) hx
  -- Simplify `A.symm 0` and distribute `A.symm` across subtraction and scalar multiplication.
  -- Then use `A.symm_apply_apply`.
  --
  -- Result: `x - ⟪v,x⟫ • A.symm u = 0`.
  have : x - (⟪v, x⟫_𝕜) • (A.symm u) = 0 := by
    -- The following `simp` line is intentionally explicit: it works across minor API changes
    -- as long as `ContinuousLinearEquiv` has the standard simp-lemmas.
    simpa [ContinuousLinearMap.sub_apply, rankOne_apply, map_sub, map_smul] using hx'
  -- Rearrange.
  simpa [sub_eq_zero] using this

/-- Existence of a nontrivial kernel vector when the scalar condition holds.

If `⟪v, A⁻¹ u⟫ = 1`, then `A⁻¹ u` lies in the kernel of `A - rankOne u v`.
-/
lemma sub_rankOne_apply_symm_u_eq_zero
    (A : E ≃L[𝕜] E) (u v : E)
    (h : ⟪v, A.symm u⟫_𝕜 = 1) :
    (A.toContinuousLinearMap - rankOne (K := K) u v) (A.symm u) = 0 := by
  -- Direct computation: `A (A⁻¹ u) = u` and `rankOne u v (A⁻¹ u) = ⟪v,A⁻¹ u⟫ u`.
  simp [ContinuousLinearMap.sub_apply, rankOne_apply, h]

end KernelAndEigenvector

end FundamentalSymmetry

end Krein
