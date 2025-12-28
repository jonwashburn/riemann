/--
Algebraic API for weighted `L²` multiplication operators.

The file `Krein/WeightedL2Kapustin.lean` defines the multiplication operator

`mulOp p m : L²(α,|p|·μ) →L L²(α,|p|·μ)`

for a bounded symbol `m ∈ L∞(α,|p|·μ)`.

For resolvent and eigenvalue work one needs to manipulate *shifts* and linear combinations
of multiplication operators.

This file records the linearity of `mulOp` in its symbol and isolates the key identity

`mulOp p (m - c·1) = mulOp p m - c·I`.

These lemmas are intentionally stated in a way that is robust to minor API changes in
`MeasureTheory.Lp` and the `L∞` action on `L²`.
-/

import KapustinFormalization.Krein.WeightedL2MulEquiv

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

/-!
## Linearity of `mulOp` in the symbol

The action of `m ∈ L∞` on `f ∈ L²` is written `m • f`. All results below are pointwise
consequences of the `SMul` axioms.
-/

@[simp] lemma mulOp_zero (p : α → ℝ) :
    mulOp (μ := μ) (𝕜 := 𝕜) p
        (0 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
      = 0 := by
  ext f
  simp [mulOp]

@[simp] lemma mulOp_add (p : α → ℝ)
    (m₁ m₂ : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    mulOp (μ := μ) (𝕜 := 𝕜) p (m₁ + m₂)
      = mulOp (μ := μ) (𝕜 := 𝕜) p m₁ + mulOp (μ := μ) (𝕜 := 𝕜) p m₂ := by
  ext f
  simp [mulOp, add_smul]

@[simp] lemma mulOp_neg (p : α → ℝ)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    mulOp (μ := μ) (𝕜 := 𝕜) p (-m)
      = - mulOp (μ := μ) (𝕜 := 𝕜) p m := by
  ext f
  simp [mulOp]

@[simp] lemma mulOp_sub (p : α → ℝ)
    (m₁ m₂ : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    mulOp (μ := μ) (𝕜 := 𝕜) p (m₁ - m₂)
      = mulOp (μ := μ) (𝕜 := 𝕜) p m₁ - mulOp (μ := μ) (𝕜 := 𝕜) p m₂ := by
  ext f
  simp [mulOp, sub_eq_add_neg, add_smul]

@[simp] lemma mulOp_smul (p : α → ℝ)
    (c : 𝕜)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    mulOp (μ := μ) (𝕜 := 𝕜) p (c • m)
      = c • (mulOp (μ := μ) (𝕜 := 𝕜) p m) := by
  ext f
  simp [mulOp, smul_smul]

/-!
## Constant symbols

The constant function `c` on `α` is represented by `c • (1 : L∞)`.
-/

@[simp] lemma mulOp_smul_one (p : α → ℝ) (c : 𝕜) :
    mulOp (μ := μ) (𝕜 := 𝕜) p (c • (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)))
      = c • (ContinuousLinearMap.id 𝕜 (L2 (μ := μ) 𝕜 p)) := by
  ext f
  simp [mulOp, smul_smul]

/-!
## The shift identity `M_{m-c} = M_m - cI`
-/

@[simp] lemma mulOp_sub_smul_one (p : α → ℝ)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (c : 𝕜) :
    mulOp (μ := μ) (𝕜 := 𝕜) p (m - c • (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)))
      = mulOp (μ := μ) (𝕜 := 𝕜) p m - c • (ContinuousLinearMap.id 𝕜 (L2 (μ := μ) 𝕜 p)) := by
  -- `mulOp` is linear in the symbol and `mulOp (c•1) = c•I`.
  simp [mulOp_sub, mulOp_smul_one]

end WeightedL2

end Krein
