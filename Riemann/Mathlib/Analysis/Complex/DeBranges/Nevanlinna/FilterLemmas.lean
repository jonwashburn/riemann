/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization Team
-/
import Mathlib

/-!
# Filter lemmas for Nevanlinna theory

This file provides infrastructure lemmas for working with filters and limits,
particularly for the filter that captures `r → 1⁻` in the unit disc context.

## Main definitions

* `Filter.towardsOne` : The filter for `r → 1⁻` (approaching 1 from below)

## Main results

* `tendsto_one_sub_mul_of_bounded` : If `g` is bounded, then `(1-r) * g r → 0`
* `limsup_one_sub_mul_eq_zero` : Key result for meanTypeDisc

These are essential for proving that bounded-type functions have zero mean type.
-/

open Filter Topology Set

namespace Filter

/-! ### Filter for r → 1⁻ -/

/-- The filter for `r → 1⁻` (approaching 1 from below).
This is `𝓝[<] 1`, the left neighborhood filter at 1. -/
def towardsOne : Filter ℝ := 𝓝[<] 1

/-- For `r ∈ towardsOne`, we have `r < 1`. -/
lemma towardsOne_lt_one : ∀ᶠ r in towardsOne, r < 1 :=
  eventually_nhdsWithin_of_forall fun _ hr => hr

/-- For `r ∈ towardsOne`, we have `0 < 1 - r`. -/
lemma towardsOne_one_sub_pos : ∀ᶠ r in towardsOne, 0 < 1 - r := by
  filter_upwards [towardsOne_lt_one] with r hr
  linarith

/-- `towardsOne` is not the bottom filter. -/
instance towardsOne_neBot : towardsOne.NeBot := by
  rw [towardsOne]
  infer_instance

/-- Eventually `r > 0` in `towardsOne`. -/
lemma towardsOne_pos : ∀ᶠ r in towardsOne, 0 < r := by
  have : Ioo (0 : ℝ) 1 ∈ 𝓝[<] 1 := Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)
  filter_upwards [this] with r ⟨hr, _⟩
  exact hr

/-! ### Tendsto lemmas -/

/-- If `g r` is bounded and `(1 - r) → 0` as `r → 1⁻`, then `(1 - r) * g r → 0`. -/
lemma tendsto_one_sub_mul_of_bounded {g : ℝ → ℝ} {M : ℝ} (hM : 0 < M)
    (hg : ∀ r, 0 < r → r < 1 → |g r| ≤ M) :
    Tendsto (fun r => (1 - r) * g r) towardsOne (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεM : 0 < ε / M := div_pos hε hM
  have h1 : ∀ᶠ r in towardsOne, 1 - r < ε / M := by
    have hIoo : Ioo (1 - ε / M) 1 ∈ 𝓝[<] 1 :=
      Ioo_mem_nhdsLT (by linarith : 1 - ε / M < 1)
    filter_upwards [hIoo] with r ⟨hr_left, _⟩
    linarith
  filter_upwards [h1, towardsOne_pos, towardsOne_lt_one] with r hr1 hr_pos hr_lt
  simp only [Real.dist_eq, sub_zero]
  have h_bound : |g r| ≤ M := hg r hr_pos hr_lt
  have h_one_sub_pos : 0 < 1 - r := by linarith
  calc |((1 : ℝ) - r) * g r|
      = |1 - r| * |g r| := abs_mul _ _
    _ = (1 - r) * |g r| := by rw [abs_of_pos h_one_sub_pos]
    _ ≤ (1 - r) * M := mul_le_mul_of_nonneg_left h_bound (le_of_lt h_one_sub_pos)
    _ < (ε / M) * M := mul_lt_mul_of_pos_right hr1 hM
    _ = ε := by field_simp

/-- If `g r` is bounded and nonnegative for `r ∈ (0, 1)`, then
    `(1-r) * g r → 0` as `r → 1⁻`, and hence the limsup is 0.

This is a key lemma for showing that bounded analytic functions on the disc
have zero mean type. -/
lemma limsup_one_sub_mul_eq_zero {g : ℝ → ℝ} {M : ℝ} (hM : 0 < M)
    (hg_nn : ∀ r, 0 < r → r < 1 → 0 ≤ g r)
    (hg : ∀ r, 0 < r → r < 1 → g r ≤ M) :
    limsup (fun r => (1 - r) * g r) towardsOne = 0 := by
  -- The function tends to 0, so limsup = lim = 0.
  have h_tendsto : Tendsto (fun r => (1 - r) * g r) towardsOne (𝓝 0) := by
    apply tendsto_one_sub_mul_of_bounded hM
    intro r hr0 hr1
    rw [abs_le]
    exact ⟨by linarith [hg_nn r hr0 hr1], hg r hr0 hr1⟩
  -- When a function tends to a limit, the limsup equals that limit.
  -- This uses `Tendsto.limsup_eq` or equivalent.
  exact h_tendsto.limsup_eq

end Filter
