import TwoChart_KernelComposition
import TwoChart_SchurTest

import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.Tactic

/-!
# Schur-data stability under kernel composition

This file implements the standard closure property of Schur row/column bounds under
kernel composition.

Given kernels `K₁ K₂ : ℝ → ℝ → ℂ`, define the composition kernel

`(K₁ ⋆ K₂)(t,t') = ∫ s, K₁(t,s) * K₂(s,t') ds`.

Assuming:
* `K₁` and `K₂` satisfy Schur row/column bounds (as `SchurData`),
* the integrability hypotheses needed to use Bochner's inequality and Fubini,

we prove that `K₁ ⋆ K₂` also satisfies Schur row/column bounds with explicit constants.

This is the analytic backbone for treating Schur-bounded kernels as a multiplicative
class and is used later when composing parametrices / remainders.
-/

namespace TwoChartEgorov

open MeasureTheory

noncomputable section

section SchurComposition

variable {μ : Measure ℝ}

/-- Schur bounds are stable under composition of kernels.

If `K₁` has Schur constants `(A₁,B₁)` and `K₂` has Schur constants `(A₂,B₂)`, then
`compKernel μ K₁ K₂` has Schur constants `(A₁*A₂, B₁*B₂)`.

The statement is formulated with explicit `Integrable` hypotheses that justify
Bochner/Fubini manipulations.
-/
theorem SchurData.compKernel
    [SigmaFinite μ]
    {K₁ K₂ : ℝ → ℝ → ℂ}
    (d₁ : SchurData μ K₁) (d₂ : SchurData μ K₂)
    (hInt : ∀ t tp : ℝ, Integrable (fun s : ℝ => K₁ t s * K₂ s tp) μ)
    (hProdRow : ∀ t : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ t p.1‖ : ℝ) * ‖K₂ p.1 p.2‖) (μ.prod μ))
    (hProdCol : ∀ tp : ℝ,
      Integrable (fun p : ℝ × ℝ => (‖K₁ p.1 p.2‖ : ℝ) * ‖K₂ p.2 tp‖) (μ.prod μ)) :
    SchurData μ (compKernel μ K₁ K₂) := by
  classical
  refine
    { A := d₁.A * d₂.A
      B := d₁.B * d₂.B
      A_nonneg := mul_nonneg d₁.A_nonneg d₂.A_nonneg
      B_nonneg := mul_nonneg d₁.B_nonneg d₂.B_nonneg
      row_integrable := ?_
      col_integrable := ?_
      row_bound := ?_
      col_bound := ?_ }

  · intro t
    -- Majorant produced by Bochner's inequality.
    have hMajInt :
        Integrable (fun tp : ℝ => ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) μ := by
      -- Integrability of the product on `μ.prod μ` implies integrability of the sliced integral.
      -- (Function of the second coordinate after integrating the first.)
      simpa using (hProdRow t).integral_prod_right

    -- Pointwise domination: `‖∫ f‖ ≤ ∫ ‖f‖`.
    have hAE :
        (fun tp : ℝ => ‖compKernel μ K₁ K₂ t tp‖)
          ≤ᵐ[μ] (fun tp : ℝ => ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) := by
      refine (ae_of_all _)
      intro tp
      have h0 :
          ‖compKernel μ K₁ K₂ t tp‖ ≤ ∫ s : ℝ, ‖K₁ t s * K₂ s tp‖ ∂μ := by
        simpa [compKernel] using
          (MeasureTheory.norm_integral_le_integral_norm (hInt t tp))
      have h1 :
          (∫ s : ℝ, ‖K₁ t s * K₂ s tp‖ ∂μ)
            = ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        refine (ae_of_all _)
        intro s
        simp [norm_mul]
      exact le_trans h0 (by simpa [h1])

    exact hMajInt.mono' hAE

  · intro tp
    -- Majorant for the column slice.
    have hMajInt :
        Integrable (fun t : ℝ => ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) μ := by
      -- Here we view the product integrand as a function of `(t,s)` and integrate over `s`.
      simpa [mul_comm, mul_left_comm, mul_assoc] using (hProdCol tp).integral_prod_left

    have hAE :
        (fun t : ℝ => ‖compKernel μ K₁ K₂ t tp‖)
          ≤ᵐ[μ] (fun t : ℝ => ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) := by
      refine (ae_of_all _)
      intro t
      have h0 :
          ‖compKernel μ K₁ K₂ t tp‖ ≤ ∫ s : ℝ, ‖K₁ t s * K₂ s tp‖ ∂μ := by
        simpa [compKernel] using
          (MeasureTheory.norm_integral_le_integral_norm (hInt t tp))
      have h1 :
          (∫ s : ℝ, ‖K₁ t s * K₂ s tp‖ ∂μ)
            = ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        refine (ae_of_all _)
        intro s
        simp [norm_mul]
      exact le_trans h0 (by simpa [h1])

    exact hMajInt.mono' hAE

  · intro t
    -- Bochner majorization gives `∫ ‖K₁⋆K₂‖ ≤ ∫∫ ‖K₁‖‖K₂‖`.
    have hAE :
        (fun tp : ℝ => ‖compKernel μ K₁ K₂ t tp‖)
          ≤ᵐ[μ] (fun tp : ℝ => ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) := by
      refine (ae_of_all _)
      intro tp
      have h0 :
          ‖compKernel μ K₁ K₂ t tp‖ ≤ ∫ s : ℝ, ‖K₁ t s * K₂ s tp‖ ∂μ := by
        simpa [compKernel] using
          (MeasureTheory.norm_integral_le_integral_norm (hInt t tp))
      have h1 :
          (∫ s : ℝ, ‖K₁ t s * K₂ s tp‖ ∂μ)
            = ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        refine (ae_of_all _)
        intro s
        simp [norm_mul]
      exact le_trans h0 (by simpa [h1])

    have h1 :
        (∫ tp : ℝ, ‖compKernel μ K₁ K₂ t tp‖ ∂μ)
          ≤ ∫ tp : ℝ, (∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ := by
      exact integral_le_integral_of_ae_le hAE

    -- Swap the integrals via Fubini.
    have hswap :
        (∫ tp : ℝ, (∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ)
          = ∫ s : ℝ, (∫ tp : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ := by
      -- Use `integral_integral_swap` on the product integrand.
      have hFub :=
        (MeasureTheory.integral_integral_swap
          (f := fun p : ℝ × ℝ => (‖K₁ t p.1‖ : ℝ) * ‖K₂ p.1 p.2‖)
          (hProdRow t))
      -- `hFub` is `∫ s, ∫ tp = ∫ tp, ∫ s`; take `.symm`.
      simpa using hFub.symm

    -- Evaluate the inner integral and apply the row bound for `K₂`.
    have hinner_le :
        (∫ s : ℝ, (∫ tp : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ)
          ≤ ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * d₂.A ∂μ := by
      have hAE2 :
          (fun s : ℝ => (∫ tp : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ))
            ≤ᵐ[μ] (fun s : ℝ => (‖K₁ t s‖ : ℝ) * d₂.A) := by
        refine (ae_of_all _)
        intro s
        -- Pull out the constant `‖K₁ t s‖`.
        have hconst :
            (∫ tp : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ)
              = (‖K₁ t s‖ : ℝ) * (∫ tp : ℝ, ‖K₂ s tp‖ ∂μ) := by
          simpa using (integral_mul_left (‖K₁ t s‖ : ℝ) (fun tp : ℝ => ‖K₂ s tp‖))
        -- Apply the row bound for `K₂` at row `s`.
        have hrow : (∫ tp : ℝ, ‖K₂ s tp‖ ∂μ) ≤ d₂.A := d₂.row_bound s
        have hnonneg : 0 ≤ (‖K₁ t s‖ : ℝ) := norm_nonneg _
        -- Multiply by the nonnegative factor.
        have := mul_le_mul_of_nonneg_left hrow hnonneg
        -- Rewrite.
        simpa [hconst, mul_assoc] using this
      exact integral_le_integral_of_ae_le hAE2

    -- Pull out the constant `d₂.A` and apply the row bound for `K₁`.
    have hfinal :
        (∫ s : ℝ, (‖K₁ t s‖ : ℝ) * d₂.A ∂μ) ≤ d₁.A * d₂.A := by
      -- Commute the scalar to the left.
      have hA :
          (∫ s : ℝ, (‖K₁ t s‖ : ℝ) * d₂.A ∂μ)
            = d₂.A * (∫ s : ℝ, (‖K₁ t s‖ : ℝ) ∂μ) := by
        -- rewrite `‖K₁ t s‖ * d₂.A` as `d₂.A * ‖K₁ t s‖`.
        have : (fun s : ℝ => (‖K₁ t s‖ : ℝ) * d₂.A) = fun s : ℝ => d₂.A * (‖K₁ t s‖ : ℝ) := by
          funext s
          ring
        -- then pull out by `integral_mul_left`.
        simpa [this, mul_assoc] using (integral_mul_left d₂.A (fun s : ℝ => (‖K₁ t s‖ : ℝ)))
      -- Now apply `d₁.row_bound t`.
      have hrow1 : (∫ s : ℝ, (‖K₁ t s‖ : ℝ) ∂μ) ≤ d₁.A := d₁.row_bound t
      -- multiply.
      have := mul_le_mul_of_nonneg_left hrow1 d₂.A_nonneg
      -- rearrange.
      -- `d₂.A * d₁.A = d₁.A * d₂.A`.
      simpa [hA, mul_comm, mul_left_comm, mul_assoc] using this

    -- Combine.
    have :
        (∫ tp : ℝ, ‖compKernel μ K₁ K₂ t tp‖ ∂μ) ≤ d₁.A * d₂.A := by
      calc
        (∫ tp : ℝ, ‖compKernel μ K₁ K₂ t tp‖ ∂μ)
            ≤ ∫ tp : ℝ, (∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ := h1
        _ = ∫ s : ℝ, (∫ tp : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ := hswap
        _ ≤ ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * d₂.A ∂μ := hinner_le
        _ ≤ d₁.A * d₂.A := hfinal
    exact this

  · intro tp
    have hAE :
        (fun t : ℝ => ‖compKernel μ K₁ K₂ t tp‖)
          ≤ᵐ[μ] (fun t : ℝ => ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) := by
      refine (ae_of_all _)
      intro t
      have h0 :
          ‖compKernel μ K₁ K₂ t tp‖ ≤ ∫ s : ℝ, ‖K₁ t s * K₂ s tp‖ ∂μ := by
        simpa [compKernel] using
          (MeasureTheory.norm_integral_le_integral_norm (hInt t tp))
      have h1 :
          (∫ s : ℝ, ‖K₁ t s * K₂ s tp‖ ∂μ)
            = ∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ := by
        refine MeasureTheory.integral_congr_ae ?_
        refine (ae_of_all _)
        intro s
        simp [norm_mul]
      exact le_trans h0 (by simpa [h1])

    have h1 :
        (∫ t : ℝ, ‖compKernel μ K₁ K₂ t tp‖ ∂μ)
          ≤ ∫ t : ℝ, (∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ := by
      exact integral_le_integral_of_ae_le hAE

    have hswap :
        (∫ t : ℝ, (∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ)
          = ∫ s : ℝ, (∫ t : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ := by
      have hFub :=
        (MeasureTheory.integral_integral_swap
          (f := fun p : ℝ × ℝ => (‖K₁ p.1 p.2‖ : ℝ) * ‖K₂ p.2 tp‖)
          (hProdCol tp))
      simpa using hFub.symm

    have hinner_le :
        (∫ s : ℝ, (∫ t : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ)
          ≤ ∫ s : ℝ, d₁.B * (‖K₂ s tp‖ : ℝ) ∂μ := by
      have hAE2 :
          (fun s : ℝ => (∫ t : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ))
            ≤ᵐ[μ] (fun s : ℝ => d₁.B * (‖K₂ s tp‖ : ℝ)) := by
        refine (ae_of_all _)
        intro s
        -- Pull out `‖K₂ s tp‖` (constant in `t`).
        have hconst :
            (∫ t : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ)
              = (∫ t : ℝ, (‖K₁ t s‖ : ℝ) ∂μ) * (‖K₂ s tp‖ : ℝ) := by
          -- Rewrite as `‖K₂ s tp‖ * ‖K₁ t s‖` and pull out on the left.
          have : (fun t : ℝ => (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖)
              = fun t : ℝ => (‖K₂ s tp‖ : ℝ) * (‖K₁ t s‖ : ℝ) := by
            funext t
            ring
          -- Now `integral_mul_left`.
          -- We then commute back.
          calc
            (∫ t : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ)
                = ∫ t : ℝ, (‖K₂ s tp‖ : ℝ) * (‖K₁ t s‖ : ℝ) ∂μ := by
                    simp [this]
            _ = (‖K₂ s tp‖ : ℝ) * (∫ t : ℝ, (‖K₁ t s‖ : ℝ) ∂μ) := by
                    simpa using
                      (integral_mul_left (‖K₂ s tp‖ : ℝ) (fun t : ℝ => (‖K₁ t s‖ : ℝ)))
            _ = (∫ t : ℝ, (‖K₁ t s‖ : ℝ) ∂μ) * (‖K₂ s tp‖ : ℝ) := by
                    ring
        have hcol1 : (∫ t : ℝ, (‖K₁ t s‖ : ℝ) ∂μ) ≤ d₁.B := d₁.col_bound s
        have hnonneg : 0 ≤ (‖K₂ s tp‖ : ℝ) := norm_nonneg _
        have := mul_le_mul_of_nonneg_right hcol1 hnonneg
        -- Rewrite.
        simpa [hconst, mul_assoc] using this
      exact integral_le_integral_of_ae_le hAE2

    have hfinal :
        (∫ s : ℝ, d₁.B * (‖K₂ s tp‖ : ℝ) ∂μ) ≤ d₁.B * d₂.B := by
      -- Pull out `d₁.B` and apply column bound for `K₂`.
      have hpull :
          (∫ s : ℝ, d₁.B * (‖K₂ s tp‖ : ℝ) ∂μ)
            = d₁.B * (∫ s : ℝ, (‖K₂ s tp‖ : ℝ) ∂μ) := by
        simpa using (integral_mul_left d₁.B (fun s : ℝ => (‖K₂ s tp‖ : ℝ)))
      have hcol2 : (∫ s : ℝ, (‖K₂ s tp‖ : ℝ) ∂μ) ≤ d₂.B := d₂.col_bound tp
      have := mul_le_mul_of_nonneg_left hcol2 d₁.B_nonneg
      simpa [hpull, mul_assoc] using this

    have :
        (∫ t : ℝ, ‖compKernel μ K₁ K₂ t tp‖ ∂μ) ≤ d₁.B * d₂.B := by
      calc
        (∫ t : ℝ, ‖compKernel μ K₁ K₂ t tp‖ ∂μ)
            ≤ ∫ t : ℝ, (∫ s : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ := h1
        _ = ∫ s : ℝ, (∫ t : ℝ, (‖K₁ t s‖ : ℝ) * ‖K₂ s tp‖ ∂μ) ∂μ := hswap
        _ ≤ ∫ s : ℝ, d₁.B * (‖K₂ s tp‖ : ℝ) ∂μ := hinner_le
        _ ≤ d₁.B * d₂.B := hfinal
    exact this

end SchurComposition

end TwoChartEgorov
