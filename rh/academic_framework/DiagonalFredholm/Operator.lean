import rh.academic_framework.Core
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Diagonal Operators on ℓ²

This file defines diagonal operators on ℓ² spaces and proves their basic properties.

## Main definitions

* `DiagonalOperator` - A diagonal operator with given eigenvalues

## Main results

* `DiagonalOperator_apply` - Diagonal operators act by pointwise multiplication
-/

namespace AcademicRH.DiagonalFredholm

open Complex Real BigOperators Filter Topology

variable {ι : Type*} [Countable ι]

/-- A diagonal operator on ℓ² -/
noncomputable def DiagonalOperator (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C) :
  lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := by
  -- Define the linear map first
  obtain ⟨C, hC⟩ := h_bounded
  let L : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 := {
    toFun := fun ψ => ⟨fun i => eigenvals i * ψ i, by
      -- Show result is in lp 2
      have : Memℓp (fun i => eigenvals i * ψ i) 2 (by simp : (2 : ℝ≥0∞).toReal = 2) := by
        rw [mem_ℓp_iff_norm_rpow_summable (by norm_num : 0 < 2) (by norm_num : 2 ≠ ⊤)]
        -- Need to show Summable fun i => ‖eigenvals i * ψ i‖ ^ 2
        have h_bound : ∀ i, ‖eigenvals i * ψ i‖ ^ 2 ≤ C^2 * ‖ψ i‖ ^ 2 := by
          intro i
          rw [norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left (norm_nonneg _) (hC i) 2) (sq_nonneg _)
        apply Summable.of_norm_bounded
        · convert Summable.mul_left (C^2) _ with i
          simp [Real.rpow_two]
        · intro i
          simp only [norm_mul, Real.norm_eq_abs, abs_norm, Real.rpow_two]
          exact h_bound i
        · have h_ψ : Memℓp (ψ : ι → ℂ) 2 (by simp : (2 : ℝ≥0∞).toReal = 2) := ψ.property
          rw [mem_ℓp_iff_norm_rpow_summable (by norm_num : 0 < 2) (by norm_num : 2 ≠ ⊤)] at h_ψ
          convert h_ψ with i
          simp [Real.rpow_two]
      exact this⟩
    map_add' := by
      intro ψ φ
      ext i
      simp [mul_add]
    map_smul' := by
      intro c ψ
      ext i
      simp [mul_comm c, mul_assoc]
  }
  -- Now prove it's continuous with bound C
  refine L.mkContinuousOfExistsBound ⟨C, fun ψ => ?_⟩
  -- Show ‖L ψ‖ ≤ C * ‖ψ‖
  have h1 : ‖L ψ‖ ^ 2 = ∑' i, ‖eigenvals i * ψ i‖ ^ 2 := by
    have := @lp.norm_sq_eq_tsum _ _ _ _ _ (fun _ : ι => ℂ) _ 2 (by norm_num : (1 : ℝ≥0∞) < 2) (L ψ)
    convert this
    ext i
    simp
  have h2 : ‖ψ‖ ^ 2 = ∑' i, ‖ψ i‖ ^ 2 := by
    have := @lp.norm_sq_eq_tsum _ _ _ _ _ (fun _ : ι => ℂ) _ 2 (by norm_num : (1 : ℝ≥0∞) < 2) ψ
    convert this
  rw [h1, h2]
  -- Bound the sum
  have h3 : ∑' i, ‖eigenvals i * ψ i‖ ^ 2 ≤ C^2 * ∑' i, ‖ψ i‖ ^ 2 := by
    have h_eq : (fun i => ‖eigenvals i * ψ i‖ ^ 2) = fun i => ‖eigenvals i‖ ^ 2 * ‖ψ i‖ ^ 2 := by
      ext i
      rw [norm_mul, mul_pow]
    rw [h_eq]
    have : ∑' i, ‖eigenvals i‖ ^ 2 * ‖ψ i‖ ^ 2 ≤ ∑' i, C^2 * ‖ψ i‖ ^ 2 := by
      apply tsum_le_tsum
      · intro i
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left (norm_nonneg _) (hC i) 2) (sq_nonneg _)
      · have h_ψ : Memℓp (ψ : ι → ℂ) 2 (by simp : (2 : ℝ≥0∞).toReal = 2) := ψ.property
        rw [mem_ℓp_iff_norm_rpow_summable (by norm_num : 0 < 2) (by norm_num : 2 ≠ ⊤)] at h_ψ
        convert Summable.mul_left (C^2) h_ψ with i
        simp [Real.rpow_two]
      · apply Summable.of_norm_bounded
        · convert Summable.mul_left (C^2) _ with i
          simp [mul_pow]
        · intro i
          rw [norm_mul, mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left (norm_nonneg _) (hC i) 2) (sq_nonneg _)
        · have h_ψ : Memℓp (ψ : ι → ℂ) 2 (by simp : (2 : ℝ≥0∞).toReal = 2) := ψ.property
          rw [mem_ℓp_iff_norm_rpow_summable (by norm_num : 0 < 2) (by norm_num : 2 ≠ ⊤)] at h_ψ
          convert h_ψ with i
          simp [Real.rpow_two]
    rw [← tsum_mul_left]
    exact this
  -- Take square roots
  have h_sqrt : Real.sqrt (‖L ψ‖^2) ≤ Real.sqrt (C^2 * ‖ψ‖^2) := by
    exact Real.sqrt_le_sqrt h3
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _) _,
      Real.sqrt_sq (by linarith : 0 ≤ C), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- Diagonal operators act by pointwise multiplication -/
lemma DiagonalOperator_apply (eigenvals : ι → ℂ)
  (h_bounded : ∃ C, ∀ i, ‖eigenvals i‖ ≤ C)
  (ψ : lp (fun _ : ι => ℂ) 2) (i : ι) :
  (DiagonalOperator eigenvals h_bounded ψ) i = eigenvals i * ψ i := by
  rfl

/-- Helper: summable implies bounded for countable sets -/
lemma summable_implies_bounded (eigenvals : ι → ℂ)
  (h_summable : Summable (fun i => ‖eigenvals i‖)) :
  ∃ C, ∀ i, ‖eigenvals i‖ ≤ C := by
  -- If ∑‖eigenvals i‖ < ∞, then eigenvals i → 0, so they're bounded
  -- For any summable sequence, the terms must tend to 0
  have h_tendsto : Tendsto (fun i => ‖eigenvals i‖) cofinite (𝓝 0) := by
    exact h_summable.tendsto_cofinite_zero
  -- Therefore the sequence is eventually bounded by 1
  have h_eventually_bounded : ∀ᶠ i in cofinite, ‖eigenvals i‖ < 1 := by
    rw [tendsto_nhds] at h_tendsto
    specialize h_tendsto (Metric.ball 0 1) Metric.isOpen_ball (by simp)
    simp only [preimage_setOf_eq] at h_tendsto
    convert h_tendsto using 1
    ext i
    simp [Metric.mem_ball, dist_zero_right]
  -- This means there's a finite set S such that for all i ∉ S, ‖eigenvals i‖ < 1
  rw [eventually_cofinite] at h_eventually_bounded
  -- The set where norm ≥ 1 is finite
  let S := {i | ¬(‖eigenvals i‖ < 1)}
  have hS_finite : S.Finite := h_eventually_bounded
  -- If S is empty, use 1 as bound
  by_cases hS_empty : S = ∅
  · use 1
    intro i
    have : i ∉ S := by simp [hS_empty]
    simp [S] at this
    linarith
  · -- S is finite and nonempty, take max + 1
    have hS_nonempty : S.Nonempty := by
      rwa [← ne_eq, ← Set.nonempty_iff_ne_empty]
    -- Convert to finset
    let Sfin := hS_finite.toFinset
    have : Sfin.Nonempty := by
      rw [Set.Finite.toFinset_nonempty]
      exact hS_nonempty
    use (Sfin.image (fun i => ‖eigenvals i‖)).max' (Finset.Nonempty.image this _) + 1
    intro i
    by_cases hi : i ∈ S
    · have : ‖eigenvals i‖ ∈ Sfin.image (fun j => ‖eigenvals j‖) := by
        rw [Finset.mem_image]
        use i
        constructor
        · rw [Set.Finite.mem_toFinset]
          exact hi
        · rfl
      have : ‖eigenvals i‖ ≤ (Sfin.image (fun j => ‖eigenvals j‖)).max' _ := by
        exact Finset.le_max' _ _ this
      linarith
    · simp [S] at hi
      linarith

end AcademicRH.DiagonalFredholm
