import TwoChart_SchurOperatorComposition

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# L² norm bounds from Schur kernel bounds

This file upgrades the `l2Energy`-based Schur estimates to explicit `L²`-norm
inequalities.  This is the bridge needed to turn kernel estimates into
operator bounds usable in Neumann-series / invertibility arguments.

The core result is the sharp inequality

```
‖KernelOp K u‖₂ ≤ sqrt(A*B) * ‖u‖₂,
```

where `A,B` are the row/column Schur constants of the kernel.

No axioms, `sorry`, or placeholders are used.
-/

namespace TwoChartEgorov

open MeasureTheory

noncomputable section

section L2Norm

variable {μ : Measure ℝ}

/-- Nonnegativity of `l2Energy`. -/
lemma l2Energy_nonneg (u : ℝ → ℂ) : 0 ≤ l2Energy μ u := by
  refine integral_nonneg ?_
  refine (ae_of_all _)
  intro t
  exact sq_nonneg (‖u t‖)

/-- `L²`-norm associated to `l2Energy`: `‖u‖₂ = sqrt (∫ ‖u‖²)`. -/
def l2Norm (u : ℝ → ℂ) : ℝ := Real.sqrt (l2Energy μ u)

lemma l2Norm_nonneg (u : ℝ → ℂ) : 0 ≤ l2Norm (μ := μ) u := by
  simp [l2Norm]

lemma l2Norm_sq (u : ℝ → ℂ) : (l2Norm (μ := μ) u) ^ 2 = l2Energy μ u := by
  have hE : 0 ≤ l2Energy μ u := l2Energy_nonneg (μ := μ) u
  -- `(sqrt E)^2 = E` when `E ≥ 0`.
  simp [l2Norm, pow_two, Real.mul_self_sqrt hE]

/-- The Schur `L²` bound constant `sqrt(A*B)`. -/
def schurConst {K : ℝ → ℝ → ℂ} (d : SchurData μ K) : ℝ := Real.sqrt (d.A * d.B)

lemma schurConst_nonneg {K : ℝ → ℝ → ℂ} (d : SchurData μ K) : 0 ≤ schurConst (μ := μ) d := by
  simp [schurConst]

/-- **Schur test in `L²`-norm form.**

This is the square-root version of `schur_l2Energy_le`.
-/
theorem schur_l2Norm_le
    {K : ℝ → ℝ → ℂ} (d : SchurData μ K)
    {u : ℝ → ℂ}
    (hu2 : Integrable (fun s : ℝ => ‖u s‖ ^ 2) μ)
    (hInt : ∀ t : ℝ, Integrable (fun s : ℝ => K t s * u s) μ)
    (hInt_wu2 : ∀ t : ℝ, Integrable (fun s : ℝ => ‖K t s‖ * ‖u s‖ ^ 2) μ)
    (hProd : Integrable (fun p : ℝ × ℝ => ‖K p.1 p.2‖ * ‖u p.2‖ ^ 2) (μ.prod μ)) :
    l2Norm (μ := μ) (KernelOp μ K u)
      ≤ Real.sqrt (d.A * d.B) * l2Norm (μ := μ) u := by
  -- Energy bound.
  have hE : l2Energy μ (KernelOp μ K u) ≤ (d.A * d.B) * l2Energy μ u :=
    schur_l2Energy_le (μ := μ) (K := K) (d := d)
      hu2 hInt hInt_wu2 hProd

  have hE_u : 0 ≤ l2Energy μ u := l2Energy_nonneg (μ := μ) u
  have hAB : 0 ≤ d.A * d.B := mul_nonneg d.Anonneg d.Bnonneg

  -- Take square roots and split the product under the square root.
  have hsqrt : Real.sqrt (l2Energy μ (KernelOp μ K u))
      ≤ Real.sqrt ((d.A * d.B) * l2Energy μ u) := by
    exact Real.sqrt_le_sqrt hE

  -- Rewrite in terms of `l2Norm`.
  simpa [l2Norm, Real.sqrt_mul hAB hE_u, mul_assoc] using hsqrt

/-- **Schur test: `L²` bound for a composed kernel operator**

This is the `L²`-norm version of `SchurOperatorComposition.schur_l2Energy_le_comp'`.
-/
theorem schur_l2Norm_le_comp'
    {K₁ K₂ : ℝ → ℝ → ℂ} (d₁ : SchurData μ K₁) (d₂ : SchurData μ K₂)
    {u : ℝ → ℂ}
    (hu2 : Integrable (fun s : ℝ => ‖u s‖ ^ 2) μ)
    (hInt₂ : ∀ t : ℝ, Integrable (fun s : ℝ => K₂ t s * u s) μ)
    (hInt₁ : ∀ t : ℝ, Integrable (fun s : ℝ => K₁ t s * (KernelOp μ K₂ u) s) μ)
    (hInt_wu2₂ : ∀ t : ℝ, Integrable (fun s : ℝ => ‖K₂ t s‖ * ‖u s‖ ^ 2) μ)
    (hInt_wu2₁ : ∀ t : ℝ,
        Integrable (fun s : ℝ => ‖K₁ t s‖ * ‖(KernelOp μ K₂ u) s‖ ^ 2) μ)
    (hProd₂ : Integrable (fun p : ℝ × ℝ => ‖K₂ p.1 p.2‖ * ‖u p.2‖ ^ 2) (μ.prod μ))
    (hProd₁ : Integrable (fun p : ℝ × ℝ => ‖K₁ p.1 p.2‖ * ‖(KernelOp μ K₂ u) p.2‖ ^ 2)
        (μ.prod μ)) :
    l2Norm (μ := μ) (KernelOp μ K₁ (KernelOp μ K₂ u))
      ≤ (Real.sqrt (d₁.A * d₁.B) * Real.sqrt (d₂.A * d₂.B)) * l2Norm (μ := μ) u := by
  -- Energy bound for the composite.
  have hE :
      l2Energy μ (KernelOp μ K₁ (KernelOp μ K₂ u))
        ≤ (d₁.A * d₁.B) * (d₂.A * d₂.B) * l2Energy μ u :=
    SchurOperatorComposition.schur_l2Energy_le_comp' (μ := μ)
      (K₁ := K₁) (K₂ := K₂) (d₁ := d₁) (d₂ := d₂) (u := u)
      hu2 hInt₂ hInt₁ hInt_wu2₂ hInt_wu2₁ hProd₂ hProd₁

  have hE_u : 0 ≤ l2Energy μ u := l2Energy_nonneg (μ := μ) u
  have hAB₁ : 0 ≤ d₁.A * d₁.B := mul_nonneg d₁.Anonneg d₁.Bnonneg
  have hAB₂ : 0 ≤ d₂.A * d₂.B := mul_nonneg d₂.Anonneg d₂.Bnonneg
  have hAB₁₂ : 0 ≤ (d₁.A * d₁.B) * (d₂.A * d₂.B) := mul_nonneg hAB₁ hAB₂

  -- Take square roots.
  have hsqrt :
      Real.sqrt (l2Energy μ (KernelOp μ K₁ (KernelOp μ K₂ u)))
        ≤ Real.sqrt ((d₁.A * d₁.B) * (d₂.A * d₂.B) * l2Energy μ u) := by
    exact Real.sqrt_le_sqrt hE

  -- First convert to an `l2Norm` inequality.
  have hnorm :
      l2Norm (μ := μ) (KernelOp μ K₁ (KernelOp μ K₂ u))
        ≤ Real.sqrt ((d₁.A * d₁.B) * (d₂.A * d₂.B)) * l2Norm (μ := μ) u := by
    -- Split `sqrt((AB₁₂)*E)` as `sqrt(AB₁₂)*sqrt(E)`.
    simpa [l2Norm, Real.sqrt_mul hAB₁₂ hE_u, mul_assoc] using hsqrt

  -- Split `sqrt(AB₁*AB₂)`.
  have hsqrtAB :
      Real.sqrt ((d₁.A * d₁.B) * (d₂.A * d₂.B))
        = Real.sqrt (d₁.A * d₁.B) * Real.sqrt (d₂.A * d₂.B) := by
    -- `Real.sqrt_mul` applies since both factors are nonnegative.
    simpa [mul_assoc, mul_left_comm, mul_comm] using (Real.sqrt_mul hAB₁ hAB₂)

  -- Substitute.
  simpa [hsqrtAB, mul_assoc] using hnorm

end L2Norm

end TwoChartEgorov
