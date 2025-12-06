import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Poisson Kernel Analysis Helpers (minimal)

Small lemmas used by dyadic Schur bounds. We avoid heavy calculus here.
-/

noncomputable section
open Classical MeasureTheory

namespace RH
namespace RS
namespace PoissonKernelAnalysis

/-- Cauchy/Poisson kernel: K_σ(x) = σ / (x^2 + σ^2). -/
@[simp] def Ksigma (σ x : ℝ) : ℝ := σ / (x^2 + σ^2)

lemma Ksigma_nonneg {σ x : ℝ} (hσ : 0 ≤ σ) : 0 ≤ Ksigma σ x := by
  unfold Ksigma
  have hden : 0 ≤ x ^ 2 + σ ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact div_nonneg hσ hden

lemma Ksigma_mul_nonneg {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (t a b : ℝ) :
  0 ≤ (Ksigma σ (t - a)) * (Ksigma τ (t - b)) := by
  exact mul_nonneg (Ksigma_nonneg (σ := σ) (x := t - a) hσ)
    (Ksigma_nonneg (σ := τ) (x := t - b) hτ)

lemma Ksigma_le_inv_sigma {σ x : ℝ} (hσ : 0 < σ) : Ksigma σ x ≤ 1 / σ := by
  unfold Ksigma
  have hden : σ ^ 2 ≤ x ^ 2 + σ ^ 2 := le_add_of_nonneg_left (sq_nonneg x)
  have hσ2pos : 0 < σ ^ 2 := by exact pow_pos hσ 2
  have hone : 1 / (x ^ 2 + σ ^ 2) ≤ 1 / σ ^ 2 := one_div_le_one_div_of_le hσ2pos hden
  have hmul := mul_le_mul_of_nonneg_left hone hσ.le
  have hEq : σ / σ ^ 2 = 1 / σ := by
    have hne : σ ≠ 0 := ne_of_gt hσ
    calc
      σ / σ ^ 2 = σ / (σ * σ) := by simp [pow_two]
      _ = (σ / σ) / σ := by simpa using (div_mul_eq_div_div σ σ σ)
      _ = 1 / σ := by simp [hne]
  exact (le_trans (by simpa [div_eq_mul_inv] using hmul) (le_of_eq hEq))

lemma Ksigma_le_sigma_div_sq {σ x : ℝ} (hσ : 0 ≤ σ) (hx : x ≠ 0) :
  Ksigma σ x ≤ σ / x^2 := by
  unfold Ksigma
  have hden : x ^ 2 ≤ x ^ 2 + σ ^ 2 := le_add_of_nonneg_right (sq_nonneg σ)
  have hxpos : 0 < x ^ 2 := by simpa using (sq_pos_of_ne_zero hx)
  have hone : 1 / (x ^ 2 + σ ^ 2) ≤ 1 / x ^ 2 := one_div_le_one_div_of_le hxpos hden
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hone hσ

/-- Triangle-type separation: |t − b| ≥ |a − b| − |t − a|. -/
lemma sep_lower_bound (t a b : ℝ) : |t - b| ≥ |a - b| - |t - a| := by
  -- Triangle inequality in the form |a - b| ≤ |t - b| + |t - a|
  have h : |a - b| ≤ |t - b| + |t - a| := by
    simpa [abs_sub_comm, add_comm] using (abs_sub_le a t b)
  -- Rearrange to the desired inequality
  exact (sub_le_iff_le_add).2 h

-- Monotonicity-of-integral notes: kept local to dyadic file to avoid heavy imports here.

end PoissonKernelAnalysis
end RS
end RH
