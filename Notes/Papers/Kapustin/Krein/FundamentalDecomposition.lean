/--
Fundamental decomposition associated with a fundamental symmetry.

If `K : FundamentalSymmetry 𝕜 E` is a bounded selfadjoint involution on a Hilbert space `E`, then
`K.J` has only eigenvalues `±1` and induces canonical *positive* and *negative* subspaces

* `E₊ = {x | J x = x}`
* `E₋ = {x | J x = -x}`

with the standard decomposition

`x = (1/2)(x + Jx) + (1/2)(x - Jx)`.

This is the structural input for Pontryagin/Krein space theory, and it is the right level of
abstraction for Kapustin-style constructions: it keeps the analytic model (weighted `L²`, Hardy
spaces, etc.) entirely separate from the indefinite metric structure.

The results here are formulated to be upstreamable to mathlib as a *fundamental-symmetry* API.
-/

import Mathlib.LinearAlgebra.Dimension
import Mathlib.LinearAlgebra.FiniteDimensional

import KapustinFormalization.Krein.Basic

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-!
### Pointwise involutivity

We will repeatedly use the pointwise identity `J (J x) = x`, derived from the bundled
composition identity `J.comp J = id`.
-/

@[simp] lemma J_apply_J_apply (x : E) : K.J (K.J x) = x := by
  -- Evaluate `J.comp J = id` at `x`.
  have h := congrArg (fun T : E →L[𝕜] E => T x) K.involutive_J
  simpa [ContinuousLinearMap.comp_apply] using h

/-!
## Positive / negative subspaces

These are the `±1` eigenspaces of `J`. We define them directly as submodules (rather than using
`LinearMap.fixedPoints` / kernels) to minimize dependence on any particular mathlib naming.
-/

/-- The `(+1)`-eigenspace of `J`, i.e. `{x | J x = x}`.

This is the canonical maximal positive subspace for the Krein form `⟪x,y⟫[K] = ⟪Jx,y⟫`.
-/
def posSubspace : Submodule 𝕜 E where
  carrier := {x | K.J x = x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp [map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    simp [map_smul, hx]

/-- The `(-1)`-eigenspace of `J`, i.e. `{x | J x = -x}`.

This is the canonical maximal negative subspace for the Krein form.
-/
def negSubspace : Submodule 𝕜 E where
  carrier := {x | K.J x = -x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp [map_add, hx, hy, add_comm, add_left_comm, add_assoc]
  smul_mem' := by
    intro a x hx
    simp [map_smul, hx, smul_neg]

@[simp] lemma mem_posSubspace_iff (x : E) : x ∈ posSubspace (K := K) ↔ K.J x = x := Iff.rfl
@[simp] lemma mem_negSubspace_iff (x : E) : x ∈ negSubspace (K := K) ↔ K.J x = -x := Iff.rfl

/-!
## Orthogonality

The `±1` eigenspaces of a selfadjoint involution are orthogonal for the Hilbert inner product.
-/

/-- Elements of `E₊` and `E₋` are orthogonal in the underlying Hilbert space. -/
lemma inner_eq_zero_of_mem_pos_of_mem_neg
    {x y : E}
    (hx : x ∈ posSubspace (K := K))
    (hy : y ∈ negSubspace (K := K)) :
    ⟪x, y⟫_𝕜 = 0 := by
  -- Use symmetry of `J`.
  have hsymm : (K.J.toLinearMap).IsSymmetric := by
    simpa using K.isSelfAdjoint_J.isSymmetric
  -- `⟪Jx,y⟫ = ⟪x,Jy⟫`.
  have hJ : ⟪K.J x, y⟫_𝕜 = ⟪x, K.J y⟫_𝕜 := hsymm x y
  -- Replace `Jx = x` and `Jy = -y`.
  have hx' : K.J x = x := hx
  have hy' : K.J y = -y := hy
  -- Conclude `⟪x,y⟫ = -⟪x,y⟫`.
  have hneg : ⟪x, y⟫_𝕜 = - ⟪x, y⟫_𝕜 := by
    -- Start from `hJ` and rewrite both sides.
    calc
      ⟪x, y⟫_𝕜 = ⟪K.J x, y⟫_𝕜 := by simpa [hx']
      _ = ⟪x, K.J y⟫_𝕜 := hJ
      _ = ⟪x, -y⟫_𝕜 := by simpa [hy']
      _ = -⟪x, y⟫_𝕜 := by simp

  -- Now `a = -a` implies `a = 0` (over a field of characteristic ≠ 2).
  have ha : ⟪x, y⟫_𝕜 + ⟪x, y⟫_𝕜 = 0 := by
    -- Add `a` to both sides of `a = -a`.
    have := congrArg (fun t : 𝕜 => t + ⟪x, y⟫_𝕜) hneg
    -- RHS simplifies to `0`.
    simpa [add_assoc, add_left_comm, add_comm] using this
  have hmul : (2 : 𝕜) * ⟪x, y⟫_𝕜 = 0 := by
    simpa [two_mul] using ha
  -- Since `2 ≠ 0` in `IsROrC`, we can cancel.
  exact (mul_eq_zero.mp hmul).resolve_left (two_ne_zero : (2 : 𝕜) ≠ 0)

/-!
## Canonical projections and the fundamental decomposition

We define the usual idempotents

* `P₊ = (1/2)(I + J)`
* `P₋ = (1/2)(I - J)`

and use them to prove that `E = E₊ ⊕ E₋`.
-/

/-- Projection onto `E₊`: `P₊ = (1/2)(I + J)`. -/
noncomputable def projPos : E →L[𝕜] E := ((1 : 𝕜) / 2) • (ContinuousLinearMap.id 𝕜 E + K.J)

/-- Projection onto `E₋`: `P₋ = (1/2)(I - J)`. -/
noncomputable def projNeg : E →L[𝕜] E := ((1 : 𝕜) / 2) • (ContinuousLinearMap.id 𝕜 E - K.J)

@[simp] lemma projPos_apply (x : E) :
    projPos (K := K) x = ((1 : 𝕜) / 2) • (x + K.J x) := by
  simp [projPos, ContinuousLinearMap.add_apply]

@[simp] lemma projNeg_apply (x : E) :
    projNeg (K := K) x = ((1 : 𝕜) / 2) • (x - K.J x) := by
  simp [projNeg, ContinuousLinearMap.sub_apply]

/-- `P₊ x` belongs to the positive subspace. -/
lemma projPos_mem_posSubspace (x : E) :
    projPos (K := K) x ∈ posSubspace (K := K) := by
  -- Show `J (P₊ x) = P₊ x`.
  change K.J (projPos (K := K) x) = projPos (K := K) x
  -- Compute using `J² = I`.
  simp [projPos_apply, map_smul, map_add, J_apply_J_apply (K := K),
    add_assoc, add_left_comm, add_comm]

/-- `P₋ x` belongs to the negative subspace. -/
lemma projNeg_mem_negSubspace (x : E) :
    projNeg (K := K) x ∈ negSubspace (K := K) := by
  -- Show `J (P₋ x) = - P₋ x`.
  change K.J (projNeg (K := K) x) = - projNeg (K := K) x
  simp [projNeg_apply, map_smul, map_sub, J_apply_J_apply (K := K),
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Pointwise decomposition: `x = P₊ x + P₋ x`. -/
lemma projPos_add_projNeg (x : E) :
    projPos (K := K) x + projNeg (K := K) x = x := by
  -- Expand, cancel the `Jx` terms, and use `1/2 + 1/2 = 1`.
  --
  -- We keep the proof explicit to make it robust across simp-set changes.
  set c : 𝕜 := (1 : 𝕜) / 2
  have hc : c + c = (1 : 𝕜) := by
    simp [c]
  calc
    projPos (K := K) x + projNeg (K := K) x
        = c • (x + K.J x) + c • (x - K.J x) := by
            simp [projPos_apply, projNeg_apply, c]
    _ = (c • x + c • (K.J x)) + (c • x - c • (K.J x)) := by
            simp [sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm, c]
    _ = (c • x + c • x) := by
            -- The `c•(Jx)` terms cancel.
            -- We only use commutativity/associativity of `+`.
            calc
              (c • x + c • (K.J x)) + (c • x - c • (K.J x))
                  = (c • x + c • (K.J x)) + (c • x + (-c • (K.J x))) := by
                      simp [sub_eq_add_neg]
              _ = (c • x + c • x) + (c • (K.J x) + (-c • (K.J x))) := by
                      ac_rfl
              _ = (c • x + c • x) := by
                      simp
    _ = (c + c) • x := by
            simp [add_smul]
    _ = x := by
            simpa [hc]

/-- The `±1`-eigenspaces of `J` form a complementary pair: `E = E₊ ⊕ E₋`. -/
theorem isCompl_posSubspace_negSubspace :
    IsCompl (posSubspace (K := K)) (negSubspace (K := K)) := by
  classical
  refine ⟨?_, ?_⟩

  · -- `E₊ ⊓ E₋ = ⊥`.
    ext x
    constructor
    · intro hx
      have hxpos : K.J x = x := hx.1
      have hxneg : K.J x = -x := hx.2
      -- From `x = Jx = -x`, conclude `x = 0`.
      have hxeq : x = -x := by
        calc
          x = K.J x := hxpos.symm
          _ = -x := hxneg
      have h2 : (2 : 𝕜) • x = 0 := by
        -- Add `x` to both sides: `x + x = 0`, then rewrite as `2•x = 0`.
        have hxadd : x + x = 0 := by
          have := congrArg (fun t : E => t + x) hxeq
          simpa [add_assoc, add_left_comm, add_comm] using this
        simpa [two_smul] using hxadd
      -- Cancel the invertible scalar `2`.
      have : x = ((1 : 𝕜) / 2) • ((2 : 𝕜) • x) := by
        -- `((1/2)*2) = 1`.
        simp [smul_smul, mul_assoc]
      -- Finish.
      simpa [this, h2]
    · intro hx
      -- `x ∈ ⊥` means `x = 0`.
      simpa using hx

  · -- `E₊ ⊔ E₋ = ⊤`.
    ext x
    constructor
    · intro hx
      simp
    · intro _
      -- Use the explicit decomposition `x = P₊x + P₋x`.
      refine (Submodule.mem_sup).2 ?_
      refine ⟨projPos (K := K) x, projPos_mem_posSubspace (K := K) x,
        projNeg (K := K) x, projNeg_mem_negSubspace (K := K) x, ?_⟩
      simpa [projPos_add_projNeg (K := K) x, add_comm, add_left_comm, add_assoc]

/-!
## Krein form on the positive/negative subspaces

On `E₊`, the Krein form coincides with the Hilbert inner product.
On `E₋`, it is its negative.
-/

lemma kreinInner_eq_inner_of_mem_pos
    {x : E} (hx : x ∈ posSubspace (K := K)) (y : E) :
    ⟪x, y⟫[K] = ⟪x, y⟫_𝕜 := by
  have hx' : K.J x = x := hx
  simp [FundamentalSymmetry.kreinInner, hx']

lemma kreinInner_eq_neg_inner_of_mem_neg
    {x : E} (hx : x ∈ negSubspace (K := K)) (y : E) :
    ⟪x, y⟫[K] = - ⟪x, y⟫_𝕜 := by
  have hx' : K.J x = -x := hx
  -- `⟪Jx,y⟫ = ⟪-x,y⟫ = -⟪x,y⟫`.
  simp [FundamentalSymmetry.kreinInner, hx']

/-!
## (Coarse) index invariants

For a fundamental symmetry, the *negative index* is the dimension of the negative eigenspace.
We expose both the cardinal-valued invariant (always defined) and the finite-dimensional
specialization.

This is the starting point for a Pontryagin-space layer:
`FiniteDimensional 𝕜 (negSubspace K)` means that the Krein space has finite negative index.
-/

/-- The negative index as a cardinal: `rank(E₋)`. -/
noncomputable def negIndexCard : Cardinal := Module.rank 𝕜 (negSubspace (K := K))

/-- The Pontryagin property: finite-dimensional negative subspace. -/
def IsPontryagin : Prop := FiniteDimensional 𝕜 (negSubspace (K := K))

/-- The negative index as a natural number, under `IsPontryagin`. -/
noncomputable def negIndexNat [IsPontryagin (K := K)] : ℕ :=
  FiniteDimensional.finrank 𝕜 (negSubspace (K := K))

end FundamentalSymmetry

end Krein
