/--
Sherman–Morrison inversion for Kapustin perturbations of *invertible multiplication operators*
on weighted `L²` Krein spaces.

This is the first fully concrete instance of the abstract algebraic results:

* `Krein/RankOneInverse.lean` (general rank-one perturbation)
* `Krein/KapustinInverse.lean` (Kapustin case `v = J u`)

in the canonical analytic model `L²(α, |p|·μ)` with fundamental symmetry
`J = multiplication by sign(p)`.

The main output is a ready-to-use inversion statement:

if `m` admits a two-sided inverse `mInv` in `L∞(α, |p|·μ)` and the Kapustin scalar
`δ = 1 - ⟪J u, (M_m)⁻¹ u⟫` is nonzero, then

`(M_m - [·,u]u)⁻¹ = invKapustinMul`

with an explicit formula given at the level of bounded operators.
-/

import KapustinFormalization.Krein.KapustinInverse
import KapustinFormalization.Krein.WeightedL2MulEquiv

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

/-!
## Inversion of `kapustinMul` under an `L∞` invertibility hypothesis
-/

/-- The boundedly invertible multiplier `M_m` packaged as a `ContinuousLinearEquiv`.

This is a thin wrapper around `WeightedL2.mulEquiv` to keep the namespace local.
-/
noncomputable def mulEquivOp (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1) :
    (L2 (μ := μ) 𝕜 p) ≃L[𝕜] (L2 (μ := μ) 𝕜 p) :=
  mulEquiv (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂

@[simp] lemma mulEquivOp_apply (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (f : L2 (μ := μ) 𝕜 p) :
    mulEquivOp (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ f = m • f := by
  rfl

@[simp] lemma mulEquivOp_symm_apply (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (f : L2 (μ := μ) 𝕜 p) :
    (mulEquivOp (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂).symm f = mInv • f := by
  rfl

/-- The Kapustin scalar `δ = 1 - ⟪J u, (M_m)⁻¹ u⟫` specialized to the weighted `L²` model,
assuming an `L∞` inverse symbol.
-/
noncomputable def kapustinMulDelta (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u : L2 (μ := μ) 𝕜 p) : 𝕜 :=
  FundamentalSymmetry.kapustinDelta
    (K := K (μ := μ) (𝕜 := 𝕜) p)
    (A := mulEquivOp (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂)
    u

/-- The Sherman–Morrison candidate inverse of the Kapustin perturbation
`M_m - [·,u]u` in the weighted `L²` model.
-/
noncomputable def invKapustinMul (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u : L2 (μ := μ) 𝕜 p) :
    (L2 (μ := μ) 𝕜 p) →L[𝕜] (L2 (μ := μ) 𝕜 p) :=
  FundamentalSymmetry.invKapustin
    (K := K (μ := μ) (𝕜 := 𝕜) p)
    (A := mulEquivOp (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂)
    u

/-- Explicit pointwise formula for `invKapustinMul`.

This is the direct specialization of `invSubRankOne_apply` to
`A = M_m` (invertible) and `v = J u`.
-/
@[simp] lemma invKapustinMul_apply (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u f : L2 (μ := μ) 𝕜 p) :
    invKapustinMul (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u f =
      (mInv • f)
        + ((kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u)⁻¹)
            • (⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, (mInv • f)⟫_𝕜)
            • (mInv • u) := by
  -- Expand `invKapustinMul` and apply the general formula for `invSubRankOne`.
  -- The only nontrivial identifications are:
  --   * `(M_m)⁻¹ = M_{mInv}`
  --   * `δ = 1 - ⟪J u, (M_m)⁻¹ u⟫`.
  simp [invKapustinMul, kapustinMulDelta, FundamentalSymmetry.invKapustin,
    FundamentalSymmetry.kapustinDelta, mulEquivOp, mulEquivOp_apply, mulEquivOp_symm_apply,
    FundamentalSymmetry.invSubRankOne_apply, FundamentalSymmetry.invSubRankOne]

/-- **Right inverse** for the weighted Kapustin perturbation.

If `m` is invertible in `L∞` and the Kapustin scalar `δ` is nonzero, then

`(M_m - [·,u]u) ∘ invKapustinMul = I`.
-/
theorem kapustinMul_comp_invKapustinMul (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u : L2 (μ := μ) 𝕜 p)
    (hδ : kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u ≠ 0) :
    (kapustinMul (μ := μ) (𝕜 := 𝕜) p m u).comp
        (invKapustinMul (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u)
      = ContinuousLinearMap.id 𝕜 (L2 (μ := μ) 𝕜 p) := by
  -- This is exactly `FundamentalSymmetry.kapustin_comp_invKapustin` instantiated with
  -- `A = mulEquivOp`.
  simpa [kapustinMul, invKapustinMul, kapustinMulDelta, mulEquivOp]
    using (FundamentalSymmetry.kapustin_comp_invKapustin
      (K := K (μ := μ) (𝕜 := 𝕜) p)
      (A := mulEquivOp (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂)
      (u := u) hδ)

/-- **Left inverse** for the weighted Kapustin perturbation.

If `m` is invertible in `L∞` and the Kapustin scalar `δ` is nonzero, then

`invKapustinMul ∘ (M_m - [·,u]u) = I`.
-/
theorem invKapustinMul_comp_kapustinMul (p : α → ℝ)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (h₁ : m * mInv = 1) (h₂ : mInv * m = 1)
    (u : L2 (μ := μ) 𝕜 p)
    (hδ : kapustinMulDelta (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u ≠ 0) :
    (invKapustinMul (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂ u).comp
        (kapustinMul (μ := μ) (𝕜 := 𝕜) p m u)
      = ContinuousLinearMap.id 𝕜 (L2 (μ := μ) 𝕜 p) := by
  simpa [kapustinMul, invKapustinMul, kapustinMulDelta, mulEquivOp]
    using (FundamentalSymmetry.invKapustin_comp_kapustin
      (K := K (μ := μ) (𝕜 := 𝕜) p)
      (A := mulEquivOp (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂)
      (u := u) hδ)

end WeightedL2

end Krein
