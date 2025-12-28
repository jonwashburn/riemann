/--
Invertibility of multiplication operators on weighted `L²` Krein spaces.

This file provides the *operator-theoretic bridge* between `L∞` multipliers and
`ContinuousLinearEquiv`s on the Hilbert space `L²(α, |p|·μ)`.

It is the key extra ingredient needed to instantiate the abstract Sherman–Morrison inversion
(`Krein/RankOneInverse.lean`, `Krein/KapustinInverse.lean`) in the concrete weighted `L²` model.

In Kapustin's constructions one repeatedly studies resolvents of the form

`(M_m - [·,u]u - z I)⁻¹`,

which at the bounded level is reduced to Sherman–Morrison by first knowing that
`M_{m-z}` is a boundedly invertible operator.

The present file isolates exactly the part that belongs to the `L∞`-multiplier calculus:
if `m` has a two-sided inverse `mInv` in `L∞`, we package multiplication by `m` as
a `ContinuousLinearEquiv`.
-/

import Mathlib.Tactic
import KapustinFormalization.Krein.WeightedL2Kapustin

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

/-!
## Multipliers as equivalences

We work on the weighted Hilbert space `L²(α, |p|·μ)` from `Krein/WeightedL2.lean`.
The bounded multiplication operator is defined in `Krein/WeightedL2Kapustin.lean` as `mulOp`.

The only additional input needed to build a `ContinuousLinearEquiv` is the existence of
`mInv ∈ L∞` satisfying `m * mInv = 1` and `mInv * m = 1`.
-/

/-- Multiplication by the constant function `1` is the identity operator. -/
@[simp] lemma mulOp_one (p : α → ℝ) :
    mulOp (μ := μ) (𝕜 := 𝕜) p
        (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
      = ContinuousLinearMap.id 𝕜 (L2 (μ := μ) 𝕜 p) := by
  ext f
  simp [mulOp, mulL∞]

/-- Multiplication by an `L∞` symbol, as a `ContinuousLinearEquiv`.

Assumptions:
* `m` and `mInv` are `L∞` functions on `(α, |p|·μ)`;
* they are inverse to each other in the `L∞` algebra.

Then `mulEquiv p m mInv` is the boundedly invertible operator `f ↦ m • f`.

This is formulated at the level of `L∞` elements (rather than pointwise representatives)
so that downstream proofs can remain purely algebraic.
-/
noncomputable def mulEquiv (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1)
    (h₂ : mInv * m = 1) :
    (L2 (μ := μ) 𝕜 p) ≃L[𝕜] (L2 (μ := μ) 𝕜 p) := by
  classical
  -- Use the standard constructor packaging mutual inverses of continuous linear maps.
  refine ContinuousLinearEquiv.ofContinuousLinearMap
    (mulOp (μ := μ) (𝕜 := 𝕜) p m)
    (mulOp (μ := μ) (𝕜 := 𝕜) p mInv)
    ?_ ?_
  · -- Right inverse: `M_m ∘ M_mInv = I`.
    calc
      (mulOp (μ := μ) (𝕜 := 𝕜) p m).comp (mulOp (μ := μ) (𝕜 := 𝕜) p mInv)
          = mulOp (μ := μ) (𝕜 := 𝕜) p (m * mInv) := by
              simpa using (mulOp_comp (μ := μ) (𝕜 := 𝕜) (p := p) (m₁ := m) (m₂ := mInv))
      _ = mulOp (μ := μ) (𝕜 := 𝕜) p (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) := by
              simpa [h₁]
      _ = ContinuousLinearMap.id 𝕜 (L2 (μ := μ) 𝕜 p) := by
              simpa using (mulOp_one (μ := μ) (𝕜 := 𝕜) (p := p))
  · -- Left inverse: `M_mInv ∘ M_m = I`.
    calc
      (mulOp (μ := μ) (𝕜 := 𝕜) p mInv).comp (mulOp (μ := μ) (𝕜 := 𝕜) p m)
          = mulOp (μ := μ) (𝕜 := 𝕜) p (mInv * m) := by
              simpa using (mulOp_comp (μ := μ) (𝕜 := 𝕜) (p := p) (m₁ := mInv) (m₂ := m))
      _ = mulOp (μ := μ) (𝕜 := 𝕜) p (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) := by
              simpa [h₂]
      _ = ContinuousLinearMap.id 𝕜 (L2 (μ := μ) 𝕜 p) := by
              simpa using (mulOp_one (μ := μ) (𝕜 := 𝕜) (p := p))

@[simp] lemma mulEquiv_apply (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (f : L2 (μ := μ) 𝕜 p) :
    mulEquiv (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ f = m • f := by
  -- `mulEquiv` was built from `mulOp`, whose action is pointwise multiplication.
  rfl

@[simp] lemma mulEquiv_symm_apply (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (f : L2 (μ := μ) 𝕜 p) :
    (mulEquiv (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂).symm f = mInv • f := by
  -- The inverse of `mulEquiv` is the multiplier by `mInv` by construction.
  rfl

end WeightedL2

end Krein
