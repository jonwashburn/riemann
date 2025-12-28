import TwoChart_SchurAndRemainder

import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.MeasureTheory.Function.Lp
import Mathlib.Tactic

/-!
# Schur test on `L²` (kernel-first form)

The previous files introduced:

* `KernelOp μ K u` — the integral operator induced by a kernel `K`.
* `SchurData μ K` — row/column `L¹` bounds on `‖K‖`.

This file proves a Schur-test `L²` energy inequality

`∫ ‖(KernelOp μ K u)(t)‖² dt ≤ (A*B) * ∫ ‖u(t)‖² dt`.

The statement is expressed at the level of representatives (plain functions),
matching the kernel-first approach used in this development.
-/

namespace TwoChartEgorov

open scoped Real
open MeasureTheory

noncomputable section

/-- Squared `L²` norm ("energy") of a complex-valued function. -/
def l2Energy (μ : Measure ℝ) (u : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖u x‖ ^ (2:ℕ) ∂μ

lemma l2Energy_nonneg (μ : Measure ℝ) (u : ℝ → ℂ) :
    0 ≤ l2Energy μ u := by
  classical
  simp [l2Energy]

section WeightedCS

variable {μ : Measure ℝ}

/-- Weighted Cauchy–Schwarz in the form used by Schur.

For nonnegative `w`,

`|∫ w(s) * f(s) ds|^2 ≤ (∫ w(s) ds) * (∫ w(s) * f(s)^2 ds)`.
-/
lemma abs_integral_mul_sq_le_integral_mul_integral_mul_sq
    {w f : ℝ → ℝ}
    (hw : ∀ s, 0 ≤ w s)
    (hInt_w : Integrable w μ)
    (hInt_wf2 : Integrable (fun s => w s * (f s) ^ (2:ℕ)) μ) :
    |∫ s, w s * f s ∂μ| ^ (2:ℕ)
      ≤ (∫ s, w s ∂μ) * (∫ s, w s * (f s) ^ (2:ℕ) ∂μ) := by
  -- Cauchy–Schwarz with `g = sqrt(w)` and `h = sqrt(w) * f`.
  let g : ℝ → ℝ := fun s => Real.sqrt (w s)
  let h : ℝ → ℝ := fun s => Real.sqrt (w s) * f s

  have hgh : (fun s => g s * h s) = fun s => w s * f s := by
    funext s
    simp [g, h, mul_assoc, Real.sqrt_mul_self (hw s)]

  have hg_sq : (fun s => ‖g s‖ ^ (2:ℕ)) = fun s => w s := by
    funext s
    simp [g, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), pow_two, Real.sq_sqrt (hw s)]

  have hh_sq : (fun s => ‖h s‖ ^ (2:ℕ)) = fun s => w s * (f s) ^ (2:ℕ) := by
    funext s
    simp [h, pow_two, mul_assoc, mul_left_comm, mul_comm, Real.sq_sqrt (hw s)]

  -- Library `L²` Cauchy–Schwarz: `|∫ g*h| ≤ ‖g‖₂ ‖h‖₂`.
  have hCS : |∫ s, g s * h s ∂μ|
      ≤ MeasureTheory.L2Norm g μ * MeasureTheory.L2Norm h μ := by
    simpa using (MeasureTheory.abs_integral_mul_le_L2Norm_mul_L2Norm (μ := μ) g h)

  have hCS2 : |∫ s, g s * h s ∂μ| ^ (2:ℕ)
      ≤ (MeasureTheory.L2Norm g μ * MeasureTheory.L2Norm h μ) ^ (2:ℕ) := by
    exact pow_le_pow_of_le_left (abs_nonneg _) hCS 2

  -- Expand `‖g‖₂²` and `‖h‖₂²` as integrals.
  have hgL2 : (MeasureTheory.L2Norm g μ) ^ (2:ℕ) = ∫ s, w s ∂μ := by
    simp [MeasureTheory.L2Norm, pow_two, hg_sq]

  have hhL2 : (MeasureTheory.L2Norm h μ) ^ (2:ℕ) = ∫ s, w s * (f s) ^ (2:ℕ) ∂μ := by
    simp [MeasureTheory.L2Norm, pow_two, hh_sq]

  have hRHS : (MeasureTheory.L2Norm g μ * MeasureTheory.L2Norm h μ) ^ (2:ℕ)
      = (∫ s, w s ∂μ) * (∫ s, w s * (f s) ^ (2:ℕ) ∂μ) := by
    calc
      (MeasureTheory.L2Norm g μ * MeasureTheory.L2Norm h μ) ^ (2:ℕ)
          = (MeasureTheory.L2Norm g μ) ^ (2:ℕ) * (MeasureTheory.L2Norm h μ) ^ (2:ℕ) := by
              simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = (∫ s, w s ∂μ) * (∫ s, w s * (f s) ^ (2:ℕ) ∂μ) := by
              simp [hgL2, hhL2]

  have hleft : |∫ s, w s * f s ∂μ| ^ (2:ℕ) = |∫ s, g s * h s ∂μ| ^ (2:ℕ) := by
    simp [hgh]

  calc
    |∫ s, w s * f s ∂μ| ^ (2:ℕ)
        = |∫ s, g s * h s ∂μ| ^ (2:ℕ) := hleft
    _ ≤ (MeasureTheory.L2Norm g μ * MeasureTheory.L2Norm h μ) ^ (2:ℕ) := hCS2
    _ = (∫ s, w s ∂μ) * (∫ s, w s * (f s) ^ (2:ℕ) ∂μ) := hRHS

end WeightedCS

section Schur

variable {μ : Measure ℝ} [SigmaFinite μ]
variable {K : ℝ → ℝ → ℂ}

/-- Schur test as an `L²`-energy inequality on representatives.

We assume the standard integrability conditions required by Bochner integration and Fubini.
In the intended applications (Weyl kernels with explicit decay), these hypotheses are discharged
from the kernel bounds.
-/
theorem schur_l2Energy_le
    (d : SchurData μ K)
    {u : ℝ → ℂ}
    (hu2 : Integrable (fun s => ‖u s‖ ^ (2:ℕ)) μ)
    (hInt : ∀ t, Integrable (fun s => K t s * u s) μ)
    (hInt_wu2 : ∀ t, Integrable (fun s => (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ)) μ)
    (hProd : Integrable (fun p : ℝ × ℝ => (‖K p.1 p.2‖ : ℝ) * ‖u p.2‖ ^ (2:ℕ)) (μ.prod μ)) :
    l2Energy μ (KernelOp μ K u) ≤ (d.A * d.B) * l2Energy μ u := by
  -- Abbreviate `Tu`.
  set Tu : ℝ → ℂ := KernelOp μ K u

  -- Pointwise Schur estimate:
  -- `‖Tu(t)‖² ≤ A * ∫ ‖K(t,s)‖ ‖u(s)‖² ds`.
  have hpoint : ∀ t : ℝ,
      ‖Tu t‖ ^ (2:ℕ) ≤ d.A * (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) := by
    intro t
    -- Triangle inequality for the Bochner integral.
    have htri : ‖Tu t‖ ≤ ∫ s, ‖K t s‖ * ‖u s‖ ∂μ := by
      have hnorm : ‖Tu t‖ ≤ ∫ s, ‖K t s * u s‖ ∂μ := by
        simpa [Tu, KernelOp] using (MeasureTheory.norm_integral_le_integral_norm (hInt t))
      have hmul : (∫ s, ‖K t s * u s‖ ∂μ) = ∫ s, ‖K t s‖ * ‖u s‖ ∂μ := by
        refine integral_congr_ae ?_
        refine (ae_of_all _)
        intro s
        simp [norm_mul]
      simpa [hmul] using hnorm

    have hsq : ‖Tu t‖ ^ (2:ℕ) ≤ (∫ s, ‖K t s‖ * ‖u s‖ ∂μ) ^ (2:ℕ) := by
      exact pow_le_pow_of_le_left (by exact norm_nonneg _) htri 2

    -- Weighted CS.
    have hcs : (∫ s, ‖K t s‖ * ‖u s‖ ∂μ) ^ (2:ℕ)
        ≤ (∫ s, (‖K t s‖ : ℝ) ∂μ) * (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) := by
      have hcs_abs := abs_integral_mul_sq_le_integral_mul_integral_mul_sq
        (μ := μ)
        (w := fun s => (‖K t s‖ : ℝ))
        (f := fun s => ‖u s‖)
        (hw := fun s => norm_nonneg _)
        (hInt_w := d.row_integrable t)
        (hInt_wf2 := hInt_wu2 t)

      -- Drop the absolute value (integrand is nonnegative).
      have hnonneg : 0 ≤ ∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ∂μ := by
        refine integral_nonneg ?_
        intro s
        exact mul_nonneg (norm_nonneg _) (norm_nonneg _)

      have habs : |∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ∂μ| ^ (2:ℕ)
          = (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ∂μ) ^ (2:ℕ) := by
        simp [Real.abs_of_nonneg hnonneg]

      simpa [habs] using hcs_abs

    -- Insert row bound `∫ ‖K(t,s)‖ ds ≤ A`.
    have hrow : (∫ s, (‖K t s‖ : ℝ) ∂μ) ≤ d.A := d.row_bound t
    have hwu2_nonneg : 0 ≤ (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) := by
      refine integral_nonneg ?_
      intro s
      exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)

    have hmulA :
        (∫ s, (‖K t s‖ : ℝ) ∂μ) * (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ)
          ≤ d.A * (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) := by
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hrow hwu2_nonneg)

    exact le_trans (le_trans hsq hcs) hmulA

  -- Integrate `hpoint` over `t`.
  have hI :
      (∫ t : ℝ, ‖Tu t‖ ^ (2:ℕ) ∂μ)
        ≤ ∫ t : ℝ, d.A * (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) ∂μ := by
    -- Use `integral_le_integral_of_ae_le`.
    have hAE :
        (fun t : ℝ => ‖Tu t‖ ^ (2:ℕ))
          ≤ᵐ[μ] (fun t : ℝ => d.A * (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ)) := by
      refine (ae_of_all _)
      intro t
      exact hpoint t
    exact integral_le_integral_of_ae_le hAE

  -- Pull out the constant `d.A`.
  have hconst :
      (∫ t : ℝ, d.A * (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) ∂μ)
        = d.A * (∫ t : ℝ, (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) ∂μ) := by
    simpa using (integral_mul_left d.A (fun t => (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ)))

  -- Fubini swap, using product integrability.
  have hswap :
      (∫ t : ℝ, (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) ∂μ)
        = ∫ s : ℝ, (∫ t, (‖K t s‖ : ℝ) ∂μ) * (‖u s‖ ^ (2:ℕ) : ℝ) ∂μ := by
    have hFub :=
      (MeasureTheory.integral_integral_swap
        (f := fun p : ℝ × ℝ => (‖K p.1 p.2‖ : ℝ) * ‖u p.2‖ ^ (2:ℕ)) hProd)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hFub.symm

  -- Column bound `∫ ‖K(t,s)‖ dt ≤ B`.
  have hcol : ∀ s, (∫ t, (‖K t s‖ : ℝ) ∂μ) ≤ d.B := d.col_bound

  have hu2_nonneg : ∀ s, 0 ≤ (‖u s‖ ^ (2:ℕ) : ℝ) := by
    intro s
    exact pow_nonneg (norm_nonneg _) _

  have hpt : ∀ s,
      (∫ t, (‖K t s‖ : ℝ) ∂μ) * (‖u s‖ ^ (2:ℕ) : ℝ)
        ≤ d.B * (‖u s‖ ^ (2:ℕ) : ℝ) := by
    intro s
    exact mul_le_mul_of_nonneg_right (hcol s) (hu2_nonneg s)

  have hIcol :
      (∫ s : ℝ, (∫ t, (‖K t s‖ : ℝ) ∂μ) * (‖u s‖ ^ (2:ℕ) : ℝ) ∂μ)
        ≤ ∫ s : ℝ, d.B * (‖u s‖ ^ (2:ℕ) : ℝ) ∂μ := by
    have hAE :
        (fun s : ℝ => (∫ t, (‖K t s‖ : ℝ) ∂μ) * (‖u s‖ ^ (2:ℕ) : ℝ))
          ≤ᵐ[μ] (fun s : ℝ => d.B * (‖u s‖ ^ (2:ℕ) : ℝ)) := by
      refine (ae_of_all _)
      intro s
      exact hpt s
    exact integral_le_integral_of_ae_le hAE

  have hBpull :
      (∫ s : ℝ, d.B * (‖u s‖ ^ (2:ℕ) : ℝ) ∂μ)
        = d.B * (∫ s : ℝ, ‖u s‖ ^ (2:ℕ) ∂μ) := by
    simpa using (integral_mul_left d.B (fun s => (‖u s‖ ^ (2:ℕ) : ℝ)))

  -- Combine everything.
  have hmain :
      (∫ t : ℝ, ‖Tu t‖ ^ (2:ℕ) ∂μ)
        ≤ (d.A * d.B) * (∫ s : ℝ, ‖u s‖ ^ (2:ℕ) ∂μ) := by
    calc
      (∫ t : ℝ, ‖Tu t‖ ^ (2:ℕ) ∂μ)
          ≤ ∫ t : ℝ, d.A * (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) ∂μ := hI
      _ = d.A * (∫ t : ℝ, (∫ s, (‖K t s‖ : ℝ) * ‖u s‖ ^ (2:ℕ) ∂μ) ∂μ) := hconst
      _ = d.A * (∫ s : ℝ, (∫ t, (‖K t s‖ : ℝ) ∂μ) * (‖u s‖ ^ (2:ℕ) : ℝ) ∂μ) := by
            simp [hswap]
      _ ≤ d.A * (∫ s : ℝ, d.B * (‖u s‖ ^ (2:ℕ) : ℝ) ∂μ) := by
            exact mul_le_mul_of_nonneg_left hIcol d.A_nonneg
      _ = d.A * (d.B * (∫ s : ℝ, ‖u s‖ ^ (2:ℕ) ∂μ)) := by
            simp [hBpull, mul_assoc]
      _ = (d.A * d.B) * (∫ s : ℝ, ‖u s‖ ^ (2:ℕ) ∂μ) := by
            ring

  simpa [l2Energy, Tu] using hmain

end Schur

end TwoChartEgorov
