/--
A concrete `ContinuousLinearEquiv` for invertible Kapustin perturbations on weighted `L²`.

The file `Krein/WeightedL2KapustinInverse.lean` provides explicit left/right inverse identities
for the bounded Kapustin perturbation

`M_m - [·,u]u`

on the weighted `L²` Krein model, under the hypotheses:

* `m` is invertible in `L∞` (witnessed by an inverse symbol `mInv`), and
* the Kapustin scalar `δ = 1 - ⟪J u, (M_m)⁻¹ u⟫` is nonzero.

For resolvent-level work, it is convenient to package this as a genuine bounded equivalence.
-/

import KapustinFormalization.Krein.WeightedL2KapustinInverse

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

/-- The weighted-model Kapustin perturbation `M_m - [·,u]u` as a `ContinuousLinearEquiv`,
under the invertibility and nondegeneracy hypotheses.

The inverse is the explicit Sherman–Morrison operator `invKapustinMul`.
-/
noncomputable def kapustinMulEquiv (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u : L2 (μ := μ) 𝕜 p)
    (hδ : kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u ≠ 0) :
    (L2 (μ := μ) 𝕜 p) ≃L[𝕜] (L2 (μ := μ) 𝕜 p) := by
  classical
  refine ContinuousLinearEquiv.ofContinuousLinearMap
    (kapustinMul (μ := μ) (𝕜 := 𝕜) p m u)
    (invKapustinMul (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u)
    (kapustinMul_comp_invKapustinMul (μ := μ) (𝕜 := 𝕜)
      (p := p) (m := m) (mInv := mInv) (h₁ := h₁) (h₂ := h₂) (u := u) hδ)
    (invKapustinMul_comp_kapustinMul (μ := μ) (𝕜 := 𝕜)
      (p := p) (m := m) (mInv := mInv) (h₁ := h₁) (h₂ := h₂) (u := u) hδ)

@[simp] lemma kapustinMulEquiv_toContinuousLinearMap (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u : L2 (μ := μ) 𝕜 p)
    (hδ : kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u ≠ 0) :
    (kapustinMulEquiv (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u hδ).toContinuousLinearMap
      = kapustinMul (μ := μ) (𝕜 := 𝕜) p m u := rfl

@[simp] lemma kapustinMulEquiv_symm_toContinuousLinearMap (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u : L2 (μ := μ) 𝕜 p)
    (hδ : kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u ≠ 0) :
    (kapustinMulEquiv (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u hδ).symm.toContinuousLinearMap
      = invKapustinMul (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u := rfl

@[simp] lemma kapustinMulEquiv_symm_apply (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u x : L2 (μ := μ) 𝕜 p)
    (hδ : kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u ≠ 0) :
    (kapustinMulEquiv (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u hδ).symm x
      = invKapustinMul (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u x := by
  rfl

/-- Pointwise formula for the inverse map of `kapustinMulEquiv`.

This is the `WeightedL2` specialization of the general Sherman–Morrison formula.
-/
@[simp] lemma kapustinMulEquiv_symm_apply_formula (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u f : L2 (μ := μ) 𝕜 p)
    (hδ : kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u ≠ 0) :
    (kapustinMulEquiv (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u hδ).symm f =
      (mInv • f)
        + ((kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u)⁻¹)
            • (⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, (mInv • f)⟫_𝕜)
            • (mInv • u) := by
  -- `invKapustinMul_apply` already states this.
  simp [kapustinMulEquiv, invKapustinMul_apply]

end WeightedL2

end Krein
