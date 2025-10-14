import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Poisson Kernel Analysis Helpers

Non-asymptotic lemmas used by the KD Schur analysis. We avoid deep Fourier
machinery here, but provide general-purpose inequalities that are immediately
useful to bound restricted integrals of nonnegative kernels by their full-line
integrals, and basic properties of the Cauchy/Poisson kernel.
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
  have hden : 0 ≤ x^2 + σ^2 := by
    have : 0 ≤ x^2 := sq_nonneg x
    have : 0 ≤ x^2 + σ^2 := add_nonneg this (sq_nonneg σ)
    exact this
  exact div_nonneg hσ hden

lemma Ksigma_sq_nonneg {σ x : ℝ} (hσ : 0 ≤ σ) : 0 ≤ (Ksigma σ x) ^ 2 := by
  exact pow_two_nonneg _

/-- For any nonnegative integrand on ℝ, the integral over a measurable subset S
is bounded by the integral over the whole line. -/
lemma integral_restrict_mono_of_nonneg
  {f : ℝ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (S : Set ℝ) (hS : MeasurableSet S) :
  (∫ x in S, f x) ≤ (∫ x, f x) := by
  -- Rewrite RHS as integral over the whole measure and compare via restriction
  have hAE : (fun x => f x)
      =ᵐ[Measure.restrict volume S] (fun x => f x) := by
    -- trivial a.e. equality
    simp
  -- Monotonicity for nonnegative integrands under restriction vs full measure
  -- Use the fact that ∫_S f ≤ ∫ f when f ≥ 0
  have h_nonneg : 0 ≤ᵐ[Measure.restrict volume S] (fun x => f x) := by
    exact Filter.Eventually.of_forall (by intro x; exact hf_nonneg x)
  -- integral over restricted measure ≤ integral over full measure for nonneg
  simpa using integral_mono_measure (μ := Measure.restrict volume S) (ν := volume)
    (f := fun x => f x) (g := fun x => f x) (by intro x; simp) (by intro x; simp)
    (by simp [hS]) (by simp) (le_of_eq (by simp)) h_nonneg

/-- Nonnegativity of Kσ·Kτ. -/
lemma Ksigma_mul_nonneg {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (t a b : ℝ) :
  0 ≤ (Ksigma σ (t - a)) * (Ksigma τ (t - b)) := by
  have h1 := Ksigma_nonneg (x := t - a) hσ
  have h2 := Ksigma_nonneg (x := t - b) hτ
  exact mul_nonneg h1 h2

/-- Pointwise bound: Kσ(x) ≤ 1/σ for σ > 0. -/
lemma Ksigma_le_inv_sigma {σ x : ℝ} (hσ : 0 < σ) : Ksigma σ x ≤ 1 / σ := by
  unfold Ksigma
  have hden : σ^2 ≤ x^2 + σ^2 := by
    have : 0 ≤ x^2 := sq_nonneg _
    exact le_add_of_nonneg_left this
  have hpos : 0 < x^2 + σ^2 := by
    have : 0 < σ^2 := by exact sq_pos_of_ne_zero _ (ne_of_gt hσ)
    exact lt_of_le_of_lt (by have := sq_nonneg x; exact add_nonneg_of_nonneg_of_nonneg this (le_of_lt hσ)) (by
      have hx2 : 0 ≤ x^2 := sq_nonneg _; exact lt_of_le_of_lt (add_le_add_left hσ.le _) (by simpa))
  -- Use monotonicity of division by a positive denominator
  have := (div_le_div_of_nonneg_left (show (0:ℝ) ≤ σ by exact hσ.le) hden (by exact le_of_lt hpos))
  -- rearrange: σ/(x^2+σ^2) ≤ σ/σ^2 = 1/σ
  simpa [one_div, inv_eq_one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

/-- Pointwise bound: for x ≠ 0, Kσ(x) ≤ σ / x^2. -/
lemma Ksigma_le_sigma_div_sq {σ x : ℝ} (hx : x ≠ 0) : Ksigma σ x ≤ σ / x^2 := by
  unfold Ksigma
  have hden : x^2 ≤ x^2 + σ^2 := by
    have : 0 ≤ σ^2 := sq_nonneg _
    exact le_add_of_nonneg_right this
  have hpos : 0 < x^2 := by
    have : 0 ≤ x^2 := sq_nonneg _
    exact lt_of_le_of_ne' this hx
  -- division monotonicity on positive denominators
  have : σ / (x^2 + σ^2) ≤ σ / x^2 := by exact (div_le_div_of_nonneg_left (by exact le_of_eq rfl) hden (le_of_lt hpos))
  simpa using this

/-- Triangle-type separation: |t − b| ≥ |a − b| − |t − a|. -/
lemma sep_lower_bound (t a b : ℝ) : |t - b| ≥ |a - b| - |t - a| := by
  have := abs_sub_le (t) (a) (b)
  -- |t - b| ≥ |a - b| - |t - a| is equivalent to |a - b| ≤ |t - b| + |t - a|
  -- which is the triangle inequality in disguise.
  -- Use |a - b| = |(a - t) + (t - b)| ≤ |a - t| + |t - b|.
  have : |a - b| ≤ |a - t| + |t - b| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, abs_sub_comm] using abs_add (a - t) (t - b)
  -- Rearrange
  have := sub_le_iff_le_add'.mpr this
  simpa [sub_eq_add_neg, abs_sub_comm] using this

/-!
Future targets (to be proven):
- Convolution identity on ℝ:
  ∫_ℝ Kσ(t−a)·Kτ(t−b) dt = Real.pi · K(σ+τ)(a−b)
- Full-line L² norm: ∫_ℝ Kσ(t)^2 dt = Real.pi / (2σ)

These will allow sharp Schur bounds on dyadic annuli.
-/

end PoissonKernelAnalysis
end RS
end RH
