import Riemann.Mathlib.Probability.Distributions.Gaussian_IBP_Hilbert

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators InnerProductSpace

open PhysLean.Probability.GaussianIBP

namespace Probability.ApproxIBP

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [MeasurableSpace H] [BorelSpace H]

-- Expectation notation
local notation3 (prettyPrint := false) "𝔼[" e "]" => ∫ ω, e ∂(ℙ : Measure Ω)

/-!
## Approximate Gaussian integration-by-parts (Hilbert/operator form)

This file packages the abstract *approximate IBP* pattern used in CW/Arguin/Burnol:

- prove an exact IBP identity for a Gaussian surrogate `G` in Hilbert space (already in mathlib/PhysLean),
- compare the needed expectations for `X` vs `G`,
- conclude an approximate IBP identity for `X` by a triangle inequality.

Crucially, the comparison step is kept **abstract** (it can come from blockwise Lindeberg,
Dirichlet-polynomial mean-value transfer, prime-graph expansion, etc.).
-/

theorem approx_ibp_of_compare_to_gaussian
    {X G : Ω → H} (hG : IsGaussianHilbert G)
    (h : H)
    {F : H → ℝ} (hF_diff : ContDiff ℝ 1 F) (hF_growth : HasModerateGrowth F)
    {δ₁ δ₂ : ℝ}
    (hcomp_left :
      |𝔼[(fun ω => ⟪X ω, h⟫_ℝ * F (X ω))] - 𝔼[(fun ω => ⟪G ω, h⟫_ℝ * F (G ω))]| ≤ δ₁)
    (hcomp_right :
      |𝔼[(fun ω => (fderiv ℝ F (X ω)) ((covOp (g := G) hG) h))]
          - 𝔼[(fun ω => (fderiv ℝ F (G ω)) ((covOp (g := G) hG) h))]| ≤ δ₂) :
    |𝔼[(fun ω => ⟪X ω, h⟫_ℝ * F (X ω))]
        - 𝔼[(fun ω => (fderiv ℝ F (X ω)) ((covOp (g := G) hG) h))]|
      ≤ δ₁ + δ₂ := by
  -- Name the four expectations to keep the algebra stable (and avoid unfolding `covOp`).
  set A : ℝ := 𝔼[(fun ω => ⟪X ω, h⟫_ℝ * F (X ω))] with hA
  set B : ℝ := 𝔼[(fun ω => ⟪G ω, h⟫_ℝ * F (G ω))] with hB
  set C : ℝ := 𝔼[(fun ω => (fderiv ℝ F (X ω)) ((covOp (g := G) hG) h))] with hC
  set D : ℝ := 𝔼[(fun ω => (fderiv ℝ F (G ω)) ((covOp (g := G) hG) h))] with hD

  -- Exact Gaussian IBP for the surrogate `G`: `B = D`.
  have hIBP : B = D := by
    simpa [B, D] using
      (PhysLean.Probability.GaussianIBP.ProbabilityTheory.gaussian_integration_by_parts_hilbert_cov_op
        (Ω := Ω) (H := H) (g := G) (hg := hG) (h := h) (F := F) hF_diff hF_growth)

  -- Decompose `A - C` into a sum of two comparison errors.
  have hdecomp : A - C = (A - B) + (D - C) := by
    have : A - C = (A - B) + (B - C) := by ring
    simp [this, hIBP, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]  -- keep simp robust

  have hcomp_left' : |A - B| ≤ δ₁ := by
    simpa [A, B] using hcomp_left

  have hcomp_right' : |D - C| ≤ δ₂ := by
    -- `|D - C| = |C - D|` and we have a bound on the latter.
    simpa [C, D, abs_sub_comm] using hcomp_right

  -- Finish by triangle inequality.
  have :
      |A - C| ≤ |A - B| + |D - C| := by
    simpa [hdecomp] using (abs_add_le (A - B) (D - C))
  have : |A - C| ≤ δ₁ + δ₂ := by
    exact this.trans (add_le_add hcomp_left' hcomp_right')
  simpa [A, B, C, D] using this

end

end Probability.ApproxIBP
