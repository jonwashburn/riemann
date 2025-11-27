
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

/-- The limsup over `atTop.comap (fun r => (1 - r)⁻¹)` of a bounded nonnegative
function equals 0. This is the key result for meanTypeDisc.

The filter `atTop.comap (fun r => (1 - r)⁻¹)` captures `r → 1⁻` because as
`(1-r)⁻¹ → ∞`, we have `r → 1⁻`. For a function bounded by `(1-r) * M`,
this tends to 0, so the limsup is 0. -/
lemma limsup_comap_one_sub_mul_eq_zero {g : ℝ → ℝ} {M : ℝ}
    (hg_nn : ∀ r, 0 < r → r < 1 → 0 ≤ (1 - r) * g r)
    (hg_bd : ∀ r, 0 < r → r < 1 → (1 - r) * g r ≤ (1 - r) * M) :
    limsup (fun r => (1 - r) * g r) (atTop.comap (fun r => (1 - r)⁻¹)) = 0 := by
  -- The function is squeezed between 0 and (1-r)*M, both tending to 0.
  -- By the squeeze theorem, the limsup is 0.
  --
  -- Strategy: Show the function tends to 0 on the comap filter, then limsup = lim = 0.
  -- The comap filter `atTop.comap (fun r => (1 - r)⁻¹)` captures r → 1⁻ because
  -- as (1-r)⁻¹ → ∞, we have 1-r → 0⁺, hence r → 1⁻.
  --
  -- Key observation: On the comap filter, we have:
  -- - (1-r)⁻¹ is eventually large, hence 1-r is eventually small
  -- - The function (1-r) * g r is squeezed between 0 and (1-r) * M → 0
  --
  -- The proof uses the squeeze theorem for Tendsto and then Tendsto.limsup_eq.
  have h_neBot : (atTop.comap (fun (r : ℝ) => (1 - r)⁻¹)).NeBot := by
    rw [Filter.comap_neBot_iff]
    intro s hs
    rw [Filter.mem_atTop_sets] at hs
    obtain ⟨N, hN⟩ := hs
    -- Pick r = 1 - (max N 1 + 1)⁻¹, then (1-r)⁻¹ = max N 1 + 1 ≥ N
    use 1 - (max N 1 + 1)⁻¹
    have hmax_pos : (0 : ℝ) < max N 1 + 1 := by
      have : (1 : ℝ) ≤ max N 1 := le_max_right N 1
      linarith
    have h_inv_pos : 0 < (max N 1 + 1)⁻¹ := inv_pos.mpr hmax_pos
    have h_sub : 1 - (1 - (max N 1 + 1)⁻¹) = (max N 1 + 1)⁻¹ := by ring
    rw [h_sub, inv_inv]
    apply hN
    have : (1 : ℝ) ≤ max N 1 := le_max_right N 1
    have : N ≤ max N 1 := le_max_left N 1
    linarith
  have h_tendsto : Tendsto (fun r => (1 - r) * g r) (atTop.comap (fun r => (1 - r)⁻¹)) (𝓝 0) := by
    -- The filter captures r → 1⁻, and (1-r) * (bounded) → 0.
    -- We use Tendsto definition: for each neighborhood of 0, eventually in comap filter.
    rw [Tendsto, map_le_iff_le_comap]
    intro s hs
    rw [mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    rw [Metric.mem_nhds_iff] at ht
    obtain ⟨ε, hε, hball⟩ := ht
    -- Need to find a set in atTop whose preimage under (1-r)⁻¹ maps into s.
    -- Use max to ensure threshold > 1 so that 0 < r < 1 is guaranteed
    let N := max ((|M| + 1) / ε) 2
    use Set.Ici N
    constructor
    · exact Ici_mem_atTop _
    · intro r hr
      -- hr: N ≤ (1 - r)⁻¹
      apply hts
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      -- Need |(1-r) * g r| < ε
      have hN_ge_2 : N ≥ 2 := le_max_right _ _
      have hN_pos : 0 < N := by linarith
      have h_1mr_pos : 0 < 1 - r := by
        by_contra h
        push_neg at h
        have hinv_nonpos : (1 - r)⁻¹ ≤ 0 := by
          rcases eq_or_lt_of_le h with hzero | hneg
          · simp [hzero]
          · exact (inv_lt_zero.mpr hneg).le
        have hle : N ≤ 0 := le_trans hr hinv_nonpos
        linarith
      have hr1 : r < 1 := by linarith
      have hr0 : 0 < r := by
        -- Since N ≥ 2 and (1-r)⁻¹ ≥ N, we have (1-r)⁻¹ ≥ 2, so 1-r ≤ 1/2, so r ≥ 1/2 > 0
        have hinv_ge_2 : (1 - r)⁻¹ ≥ 2 := le_trans hN_ge_2 hr
        have h1mr_le_half : 1 - r ≤ 1/2 := by
          rw [← inv_inv (1 - r)]
          have : (2 : ℝ)⁻¹ = 1/2 := by norm_num
          rw [← this]
          exact inv_anti₀ (by norm_num : (0 : ℝ) < 2) hinv_ge_2
        linarith
      have h_nn := hg_nn r hr0 hr1
      have h_bound := hg_bd r hr0 hr1
      rw [abs_of_nonneg h_nn]
      have hN_ge_eps : N ≥ (|M| + 1) / ε := le_max_left _ _
      have h_1mr_le_eps : 1 - r ≤ ε / (|M| + 1) := by
        have h1 : (1 - r)⁻¹ ≥ (|M| + 1) / ε := le_trans hN_ge_eps hr
        have h2 : 0 < (|M| + 1) / ε := by positivity
        have h3 : (1 - r) ≤ ((|M| + 1) / ε)⁻¹ := by
          rw [← inv_inv (1 - r)]
          exact inv_anti₀ h2 h1
        simp only [inv_div] at h3
        exact h3
      calc (1 - r) * g r ≤ (1 - r) * M := h_bound
        _ ≤ (1 - r) * |M| := by
            by_cases hM : 0 ≤ M
            · rw [abs_of_nonneg hM]
            · push_neg at hM
              have hgr_nn : 0 ≤ g r := by
                have := h_nn
                rw [mul_nonneg_iff] at this
                rcases this with ⟨_, hgr⟩ | ⟨h1mr_neg, _⟩
                · exact hgr
                · linarith
              have hgr_le_M : g r ≤ M := by
                have := h_bound
                rw [mul_le_mul_iff_of_pos_left h_1mr_pos] at this
                exact this
              have hgr_zero : g r = 0 := by linarith
              calc (1 - r) * M ≤ 0 := by
                    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt h_1mr_pos) (le_of_lt hM)
                _ ≤ (1 - r) * |M| := by
                    apply mul_nonneg (le_of_lt h_1mr_pos) (abs_nonneg M)
        _ ≤ (ε / (|M| + 1)) * |M| := by
            apply mul_le_mul_of_nonneg_right h_1mr_le_eps (abs_nonneg M)
        _ < ε := by
            have h_ratio : |M| / (|M| + 1) < 1 := by
              rw [div_lt_one (by linarith [abs_nonneg M] : 0 < |M| + 1)]
              linarith
            calc (ε / (|M| + 1)) * |M| = ε * |M| / (|M| + 1) := by ring
              _ = ε * (|M| / (|M| + 1)) := by rw [mul_div_assoc]
              _ < ε * 1 := by apply mul_lt_mul_of_pos_left h_ratio hε
              _ = ε := mul_one ε
  exact h_tendsto.limsup_eq

end Filter
