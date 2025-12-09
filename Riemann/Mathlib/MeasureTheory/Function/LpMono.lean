import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Lp Space Monotonicity with Finite Measure Support

This file provides lemmas for relating different Lp norms when functions have
finite-measure support. The key insight is that `L^∞ ∩ (finite support) ⊆ L^p`
for all `1 ≤ p < ∞`.

## Main Results

* `MemLp.of_bound_support`: Bounded function with finite-measure support is in `L^p`.
* `snorm_le_of_bdd_support`: `L^p` norm bound for bounded functions.
* `Lp_of_Linfty_finite_support`: `L^∞` with finite support embeds into `L^p`.

## Implementation Notes

These results are essential for:
1. Atomic decomposition of H¹
2. Showing atoms belong to all L^p spaces
3. Interpolation arguments

## Tags

Lp space, exponent monotonicity, finite measure, bounded support
-/

open MeasureTheory Measure Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section LpMonotonicity

omit [NormedSpace ℝ E] in
/-- A bounded function with finite-measure support belongs to `L^p` for all `p ∈ [1, ∞)`.

The key estimate is: `‖f‖_p^p = ∫ ‖f‖^p ≤ M^p · μ(S) < ∞`. -/
theorem Memℒp.of_bdd_support {f : α → E} {M : ℝ} {S : Set α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hM : ∀ x, ‖f x‖ ≤ M) (hM_pos : 0 ≤ M)
    (hsupp : Function.support f ⊆ S) (hS : μ S < ⊤)
    (hmeas : AEStronglyMeasurable f μ) : MemLp f p μ := by
  refine ⟨hmeas, ?_⟩
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (one_pos.trans_le hp).ne' hp_top]
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le one_pos hp)) hp_top
  have h_zero_outside : ∀ x ∉ S, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal = 0 := fun x hx => by
    have : x ∉ Function.support f := fun h => hx (hsupp h)
    simp only [Function.mem_support, ne_eq, not_not] at this
    simp [this, ENNReal.zero_rpow_of_pos hp_pos]
  have hbound : ∀ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ≤
      S.indicator (fun _ => (M.toNNReal : ℝ≥0∞) ^ p.toReal) x := fun x => by
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
      apply ENNReal.rpow_le_rpow _ hp_pos.le
      simp only [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
        Real.coe_toNNReal _ hM_pos]
      exact hM x
    · simp only [Set.indicator_of_notMem hx, h_zero_outside x hx, le_refl]
  calc ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ
      ≤ ∫⁻ x, S.indicator (fun _ => (M.toNNReal : ℝ≥0∞) ^ p.toReal) x ∂μ := lintegral_mono hbound
    _ ≤ (M.toNNReal : ℝ≥0∞) ^ p.toReal * μ S := lintegral_indicator_const_le S _
    _ < ⊤ := ENNReal.mul_lt_top
               (ENNReal.rpow_ne_top_of_nonneg hp_pos.le ENNReal.coe_ne_top).lt_top hS

omit [NormedSpace ℝ E] in
/-- `L^p` norm bound for bounded functions with finite-measure support.

`‖f‖_p ≤ M · μ(S)^(1/p)` when `|f| ≤ M` and `support f ⊆ S`. -/
theorem eLpNorm_le_of_bdd_support {f : α → E} {M : ℝ} {S : Set α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hM : ∀ x, ‖f x‖ ≤ M) (hM_pos : 0 ≤ M)
    (hsupp : Function.support f ⊆ S) (_ : μ S < ⊤)
    (_ : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ≤ M.toNNReal * (μ S) ^ (1 / p.toReal) := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le one_pos hp)) hp_top
  have h_zero_outside : ∀ x ∉ S, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal = 0 := fun x hx => by
    have : x ∉ Function.support f := fun h => hx (hsupp h)
    simp only [Function.mem_support, ne_eq, not_not] at this
    simp [this, ENNReal.zero_rpow_of_pos hp_pos]
  have hbound : ∀ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ≤
      S.indicator (fun _ => (M.toNNReal : ℝ≥0∞) ^ p.toReal) x := fun x => by
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
      apply ENNReal.rpow_le_rpow _ hp_pos.le
      simp only [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
        Real.coe_toNNReal _ hM_pos]
      exact hM x
    · simp only [Set.indicator_of_notMem hx, h_zero_outside x hx, le_refl]
  calc eLpNorm f p μ
      = (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm (one_pos.trans_le hp).ne' hp_top]
        simp only [enorm_eq_nnnorm]
    _ ≤ ((M.toNNReal : ℝ≥0∞) ^ p.toReal * μ S) ^ (1 / p.toReal) := by
        apply ENNReal.rpow_le_rpow _ (by positivity)
        calc ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ
            ≤ ∫⁻ x, S.indicator (fun _ => (M.toNNReal : ℝ≥0∞) ^ p.toReal) x ∂μ := lintegral_mono hbound
          _ ≤ (M.toNNReal : ℝ≥0∞) ^ p.toReal * μ S := lintegral_indicator_const_le S _
    _ = (M.toNNReal : ℝ≥0∞) ^ (p.toReal * (1 / p.toReal)) * (μ S) ^ (1 / p.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        congr 1
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hp_pos.ne', ENNReal.rpow_one]
    _ = M.toNNReal * (μ S) ^ (1 / p.toReal) := by
        rw [mul_one_div_cancel hp_pos.ne', ENNReal.rpow_one]

omit [NormedSpace ℝ E] in
/-- An `L^∞` function with finite-measure support is in `L^p` for all `1 ≤ p < ∞`.

This is key for showing H¹ atoms belong to L^p. -/
theorem Memℒp.of_memℒp_top_finite_support {f : α → E} {S : Set α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hf : MemLp f ⊤ μ)
    (hsupp : Function.support f ⊆ S) (hS : μ S < ⊤) : MemLp f p μ := by
  -- Get the essential supremum bound
  have hbound := MemLp.eLpNorm_lt_top hf
  rw [eLpNorm_exponent_top] at hbound
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos (one_pos.trans_le hp).ne' hp_top
  -- Show the Lp norm is finite using the essSup bound and finite support
  have h_zero_outside : ∀ x ∉ S, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal = 0 := fun x hx => by
    have : x ∉ Function.support f := fun h => hx (hsupp h)
    simp only [Function.mem_support, ne_eq, not_not] at this
    simp [this, ENNReal.zero_rpow_of_pos hp_pos]
  -- Use the a.e. bound: ‖f x‖ₑ ≤ eLpNormEssSup f μ a.e.
  have hae_bound : ∀ᵐ x ∂μ, (‖f x‖₊ : ℝ≥0∞) ≤ eLpNormEssSup f μ := by
    have := enorm_ae_le_eLpNormEssSup f μ
    filter_upwards [this] with x hx
    simp only [enorm_eq_nnnorm] at hx
    exact hx
  refine ⟨hf.1, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (one_pos.trans_le hp).ne' hp_top]
  simp only [enorm_eq_nnnorm]
  -- Combine a.e. bound with support constraint
  have hae_bound' : ∀ᵐ x ∂μ, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ≤
      S.indicator (fun _ => (eLpNormEssSup f μ) ^ p.toReal) x := by
    filter_upwards [hae_bound] with x hx
    by_cases hxS : x ∈ S
    · simp only [Set.indicator_of_mem hxS]
      exact ENNReal.rpow_le_rpow hx hp_pos.le
    · simp only [Set.indicator_of_notMem hxS, h_zero_outside x hxS, le_refl]
  calc ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ
      ≤ ∫⁻ x, S.indicator (fun _ => (eLpNormEssSup f μ) ^ p.toReal) x ∂μ :=
          lintegral_mono_ae hae_bound'
    _ ≤ (eLpNormEssSup f μ) ^ p.toReal * μ S := lintegral_indicator_const_le S _
    _ < ⊤ := ENNReal.mul_lt_top
               (ENNReal.rpow_ne_top_of_nonneg hp_pos.le hbound.ne).lt_top hS

end LpMonotonicity

section Interpolation

omit [NormedSpace ℝ E] in
/-- Hölder interpolation: if `f ∈ L^p ∩ L^q` then `f ∈ L^r` for `p ≤ r ≤ q`.

This is a simplified version focusing on finite measure support. -/
theorem Memℒp.interpolate_of_finite_support {f : α → E} {S : Set α}
    {p q r : ℝ≥0∞}
    (_ : 1 ≤ p) (_ : p ≤ q) (_ : p ≤ r) (hrq : r ≤ q)
    (_ : MemLp f p μ) (hfq : MemLp f q μ)
    (hsupp : Function.support f ⊆ S) (hS : μ S < ⊤) : MemLp f r μ := by
  -- f is zero outside S
  have hf_zero : ∀ x, x ∉ S → f x = 0 := fun x hx =>
    Function.notMem_support.mp (fun h => hx (hsupp h))
  -- Use monotonicity: L^q ⊂ L^r for r ≤ q on sets of finite measure
  exact hfq.mono_exponent_of_measure_support_ne_top hf_zero hS.ne hrq

end Interpolation

end MeasureTheory
