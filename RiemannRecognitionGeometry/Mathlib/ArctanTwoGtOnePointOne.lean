/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# A concrete lower bound on `Real.arctan 2`

We prove the numerical inequality `(1.1 : ℝ) < Real.arctan 2`
using the Taylor series for `arctan` at `0`, together with elementary
alternating‑series bounds and standard bounds on `π`.

Adapted from jonwashburn/riemann repository.
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

open scoped BigOperators Topology
open Filter

namespace Real

noncomputable section

/-- The `n`‑th Taylor term for `arctan x` at `0`:
`(-1)^n * x^(2n+1) / (2n+1)`. -/
def arctanSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ (2 * n + 1) / (2 * n + 1)

/-- Partial sums of the Taylor series for `arctan x` at `0`. -/
def arctanPartialSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, arctanSeriesTerm x i

/-- Specialize `Real.hasSum_arctan` to the notation above. -/
lemma hasSum_arctan_series {x : ℝ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => arctanSeriesTerm x n) (Real.arctan x) := by
  simpa [arctanSeriesTerm] using Real.hasSum_arctan (x := x) hx

/-- The sequence of absolute Taylor terms at `x = 1/2`. -/
def arctanHalfTerm (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (2 * n + 1) / (2 * n + 1)

lemma HasSum.congr' {α β : Type*} [AddCommMonoid β] [TopologicalSpace β]
    {f g : α → β} {a b : β} (hf : HasSum f a) (hfg : ∀ x, f x = g x) (hab : a = b) :
    HasSum g b := by
  rw [← hab]
  convert hf using 2
  ext x
  rw [hfg]

/-- For `x = 1/2`, the Taylor series for `arctan` is an alternating series
with terms `arctanHalfTerm n`. -/
lemma arctan_half_series :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n * arctanHalfTerm n) (Real.arctan ((1 : ℝ) / 2)) := by
  have hx : ‖(1 : ℝ) / 2‖ < (1 : ℝ) := by simp; norm_num
  have h := hasSum_arctan_series (x := (1 : ℝ) / 2) hx
  refine HasSum.congr' h ?_ ?_
  · intro n
    unfold arctanSeriesTerm arctanHalfTerm
    ring
  · rfl

/-- The sequence of Taylor coefficients for `x = 1/2` is antitone (decreasing). -/
lemma arctanHalfTerm_antitone : Antitone arctanHalfTerm := by
  have h_succ_le : ∀ n : ℕ, arctanHalfTerm (n + 1) ≤ arctanHalfTerm n := by
    intro n
    have hpos_denom₁ : (0 : ℝ) < (2 * n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos _)
    have hpos_denom₂ : (0 : ℝ) < (2 * n + 3 : ℝ) := by exact_mod_cast (Nat.succ_pos _)
    have hpos_pow : 0 < ((1 : ℝ) / 2) ^ (2 * n + 1) := by
      have : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
      exact pow_pos this _
    have h_ratio :
        arctanHalfTerm (n + 1) / arctanHalfTerm n =
          ((2 * n + 1 : ℝ) / (2 * n + 3 : ℝ)) / 4 := by
      unfold arctanHalfTerm
      have hexp : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
      rw [hexp, pow_add, pow_two, one_div, ← one_div, one_div]
      field_simp
      ring
    have h_ratio_le_one : arctanHalfTerm (n + 1) / arctanHalfTerm n ≤ 1 := by
      have h_main : ((2 * n + 1 : ℝ) / (2 * n + 3 : ℝ)) / 4 ≤ 1 := by
        have h_poly : (2 * n + 1 : ℝ) ≤ 4 * (2 * n + 3 : ℝ) := by
          have h_diff : 4 * (2 * n + 3 : ℝ) - (2 * n + 1 : ℝ) = (6 : ℝ) * n + 11 := by ring
          have h_nonneg : (0 : ℝ) ≤ (6 : ℝ) * n + 11 := by
            have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le _)
            have h6n : (0 : ℝ) ≤ (6 : ℝ) * n := mul_nonneg (by norm_num) hn
            linarith
          have h_sub : (0 : ℝ) ≤ 4 * (2 * n + 3 : ℝ) - (2 * n + 1 : ℝ) := by
            simpa [h_diff] using h_nonneg
          exact sub_nonneg.mp h_sub
        have hden_pos : 0 < (4 : ℝ) * (2 * n + 3 : ℝ) := by
          have h4 : (0 : ℝ) < 4 := by norm_num
          exact mul_pos h4 hpos_denom₂
        have hdiv : (2 * n + 1 : ℝ) / (4 * (2 * n + 3 : ℝ)) ≤ 1 := by
          refine (div_le_iff₀ hden_pos).2 ?_
          simpa [mul_comm, mul_left_comm, mul_assoc] using h_poly
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      simpa [h_ratio] using h_main
    have hfn_pos : 0 < arctanHalfTerm n := by
      unfold arctanHalfTerm
      have : 0 < ((1 : ℝ) / 2) ^ (2 * n + 1) := by
        have : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
        exact pow_pos this _
      have hpos_coeff : (0 : ℝ) < (2 * n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos _)
      exact div_pos this hpos_coeff
    have hmul := (mul_le_mul_of_nonneg_right h_ratio_le_one (le_of_lt hfn_pos))
    have h_ne : arctanHalfTerm n ≠ 0 := ne_of_gt hfn_pos
    have h_final : arctanHalfTerm (n + 1) ≤ arctanHalfTerm n := by
      have h_cancel : arctanHalfTerm (n + 1) / arctanHalfTerm n * arctanHalfTerm n = arctanHalfTerm (n + 1) := by
        rw [div_mul_cancel₀]
        exact h_ne
      rw [← h_cancel]
      simpa [one_mul] using hmul
    exact h_final
  exact antitone_nat_of_succ_le h_succ_le

/-- The limit of the alternating Taylor series at `x = 1/2` is squeezed between
partial sums with 4 and 5 terms. -/
lemma arctan_half_between_partial_sums :
    arctanPartialSum ((1 : ℝ) / 2) (2 * 2) ≤
      Real.arctan ((1 : ℝ) / 2) ∧
      Real.arctan ((1 : ℝ) / 2) ≤
        arctanPartialSum ((1 : ℝ) / 2) (2 * 2 + 1) := by
  have h_series :
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * arctanHalfTerm i)
        atTop (𝓝 (Real.arctan ((1 : ℝ) / 2))) :=
    arctan_half_series.tendsto_sum_nat
  have hfl :
      Tendsto (fun n : ℕ =>
          ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * arctanHalfTerm i)
        atTop (𝓝 (Real.arctan ((1 : ℝ) / 2))) := h_series
  have h_lower :
      ∑ i ∈ Finset.range (2 * 2), (-1 : ℝ) ^ i * arctanHalfTerm i
        ≤ Real.arctan ((1 : ℝ) / 2) :=
    Antitone.alternating_series_le_tendsto
      (l := Real.arctan ((1 : ℝ) / 2))
      (f := arctanHalfTerm)
      (k := 2)
      (hfl := hfl)
      (hfa := arctanHalfTerm_antitone)
  have h_upper :
      Real.arctan ((1 : ℝ) / 2)
        ≤ ∑ i ∈ Finset.range (2 * 2 + 1), (-1 : ℝ) ^ i * arctanHalfTerm i :=
    Antitone.tendsto_le_alternating_series
      (l := Real.arctan ((1 : ℝ) / 2))
      (f := arctanHalfTerm)
      (k := 2)
      (hfl := hfl)
      (hfa := arctanHalfTerm_antitone)
  have h_eq_even :
      arctanPartialSum ((1 : ℝ) / 2) (2 * 2) =
        ∑ i ∈ Finset.range (2 * 2), (-1 : ℝ) ^ i * arctanHalfTerm i := by
    unfold arctanPartialSum
    apply Finset.sum_congr rfl
    intro i _
    unfold arctanSeriesTerm arctanHalfTerm
    ring
  have h_eq_odd :
      arctanPartialSum ((1 : ℝ) / 2) (2 * 2 + 1) =
        ∑ i ∈ Finset.range (2 * 2 + 1), (-1 : ℝ) ^ i * arctanHalfTerm i := by
    unfold arctanPartialSum
    apply Finset.sum_congr rfl
    intro i _
    unfold arctanSeriesTerm arctanHalfTerm
    ring
  constructor
  · rw [h_eq_even]; exact h_lower
  · rw [h_eq_odd]; exact h_upper

/-- Explicit closed form for the 5‑term Taylor partial sum at `x = 1/2`. -/
lemma arctanPartialSum_half_5 :
    arctanPartialSum ((1 : ℝ) / 2) 5 =
      (1 : ℝ) / 2 - 1 / 24 + 1 / 160 - 1 / 896 + 1 / 4608 := by
  unfold arctanPartialSum arctanSeriesTerm
  have : (Finset.range 5 : Finset ℕ) = {0,1,2,3,4} := by decide
  simp [this, pow_succ, pow_add, two_mul] ; ring

/-- A simple numerical upper bound: `arctan (1/2) < 0.464`. -/
lemma arctan_half_lt_0464 : Real.arctan ((1 : ℝ) / 2) < (464 : ℝ) / 1000 := by
  obtain ⟨_, h_upper⟩ := arctan_half_between_partial_sums
  have h_eval :
      arctanPartialSum ((1 : ℝ) / 2) 5
        = (74783 : ℝ) / 161280 := by
    have := arctanPartialSum_half_5
    have : (1 : ℝ) / 2 - 1 / 24 + 1 / 160 - 1 / 896 + 1 / 4608
        = (74783 : ℝ) / 161280 := by norm_num
    calc arctanPartialSum ((1 : ℝ) / 2) 5
        = (1 : ℝ) / 2 - 1 / 24 + 1 / 160 - 1 / 896 + 1 / 4608 := arctanPartialSum_half_5
      _ = (74783 : ℝ) / 161280 := this
  have h_upper' :
      Real.arctan ((1 : ℝ) / 2) ≤ (74783 : ℝ) / 161280 := by
    rw [← h_eval]
    exact h_upper
  have h_rat : (74783 : ℝ) / 161280 < (464 : ℝ) / 1000 := by norm_num
  exact lt_of_le_of_lt h_upper' h_rat

/-- A concrete lower bound on `π/2 - arctan (1/2)`. -/
lemma one_point_one_lt_pi_over_two_sub_arctan_half :
    (1.1 : ℝ) < Real.pi / 2 - Real.arctan ((1 : ℝ) / 2) := by
  have h_arctan : Real.arctan ((1 : ℝ) / 2) < (464 : ℝ) / 1000 := arctan_half_lt_0464
  have h_target :
      (1.1 : ℝ) + (464 : ℝ) / 1000 < Real.pi / 2 := by
    have h_eq : (1.1 : ℝ) + (464 : ℝ) / 1000 = (1564 : ℝ) / 1000 := by norm_num
    have h_rat : (3128 : ℝ) / 1000 < (3140 : ℝ) / 1000 := by norm_num
    have h_pi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
    have h_pi' : (3140 : ℝ) / 1000 < Real.pi := by convert h_pi using 1; norm_num
    have h_lt_pi : (3128 : ℝ) / 1000 < Real.pi := lt_trans h_rat h_pi'
    have h_pos_two : (0 : ℝ) < 2 := by norm_num
    have h_div : (1564 : ℝ) / 1000 < Real.pi / 2 := by
      have := div_lt_div_of_pos_right h_lt_pi h_pos_two
      convert div_lt_div_of_pos_right h_lt_pi h_pos_two using 1
      norm_num
    simpa [h_eq] using h_div
  have h_sum :
      (1.1 : ℝ) + Real.arctan ((1 : ℝ) / 2) < (1.1 : ℝ) + (464 : ℝ) / 1000 :=
    add_lt_add_left h_arctan _
  have := lt_trans h_sum h_target
  linarith

/-- **Final numerical inequality**: `arctan 2 > 1.1`. -/
theorem arctan_two_gt_one_point_one : (1.1 : ℝ) < Real.arctan 2 := by
  have h_inv :
      Real.arctan (2 : ℝ) = Real.pi / 2 - Real.arctan ((1 : ℝ) / 2) := by
    have hpos : (0 : ℝ) < ((1 : ℝ) / 2) := by norm_num
    have := Real.arctan_inv_of_pos hpos
    have hx : ((1 : ℝ) / 2)⁻¹ = (2 : ℝ) := by field_simp
    simpa [hx] using this
  have h_main := one_point_one_lt_pi_over_two_sub_arctan_half
  rw [h_inv]
  exact h_main

/-- Corollary: `0.5 < arctan 2` (weaker but useful bound). -/
theorem arctan_two_gt_half : (0.5 : ℝ) < Real.arctan 2 := by
  have h := arctan_two_gt_one_point_one
  linarith

/-- Lower bound: `arctan (1/2) > 2/5 = 0.4`.

    From the Taylor series: arctan(1/2) > 1/2 - 1/24 + 1/160 - 1/896
                                        = (448 - 37.33 + 5.6 - 1)/896
                                        ≈ 0.464 > 0.4 -/
theorem arctan_half_gt_two_fifths : (2 : ℝ) / 5 < Real.arctan ((1 : ℝ) / 2) := by
  obtain ⟨h_lower, _⟩ := arctan_half_between_partial_sums
  -- The 4-term partial sum is a lower bound
  -- Sum = 1/2 - 1/24 + 1/160 - 1/896
  have h_eval : arctanPartialSum ((1 : ℝ) / 2) 4 = 1/2 - 1/24 + 1/160 - 1/896 := by
    unfold arctanPartialSum arctanSeriesTerm
    have : (Finset.range 4 : Finset ℕ) = {0,1,2,3} := by decide
    simp [this, pow_succ, pow_add, two_mul]; ring
  have h_lower' : 1/2 - 1/24 + 1/160 - 1/896 ≤ Real.arctan ((1 : ℝ) / 2) := by
    rw [← h_eval]; exact h_lower
  -- Now prove 2/5 < 1/2 - 1/24 + 1/160 - 1/896
  have h_num : (2 : ℝ) / 5 < 1/2 - 1/24 + 1/160 - 1/896 := by norm_num
  linarith

/-- The sum of arctan(1/3) and arctan(1/2) equals π/4.
    This follows from the arctan addition formula since (1/3)*(1/2) = 1/6 < 1
    and (1/3 + 1/2)/(1 - 1/6) = (5/6)/(5/6) = 1. -/
theorem arctan_third_add_arctan_half : arctan (1/3) + arctan (1/2) = Real.pi / 4 := by
  have h_prod : (1:ℝ)/3 * (1/2) < 1 := by norm_num
  have h_add := arctan_add h_prod
  have h_eq : ((1:ℝ)/3 + 1/2) / (1 - 1/3 * (1/2)) = 1 := by norm_num
  rw [h_eq] at h_add
  rw [arctan_one] at h_add
  exact h_add

/-- arctan(1/3) > 0.31. This follows from arctan(1/3) = π/4 - arctan(1/2)
    and the bounds π > 3.14 and arctan(1/2) < 464/1000. -/
theorem arctan_third_gt_point_three_one : arctan ((1:ℝ)/3) > 31/100 := by
  have h_sum := arctan_third_add_arctan_half
  have h_arctan_half_upper : arctan (1/2) < 464/1000 := arctan_half_lt_0464
  -- π > 3.14, so π/4 > 0.785
  have h_pi_quarter_lower : Real.pi / 4 > 785/1000 := by
    have h_pi := Real.pi_gt_d2  -- π > 3.14
    linarith
  -- arctan(1/3) = π/4 - arctan(1/2) > 0.785 - 0.464 = 0.321 > 0.31
  linarith

/-- Two times arctan(1/3) is greater than L_rec = arctan(2)/2.
    Since arctan(1/3) > 0.31, we have 2*arctan(1/3) > 0.62.
    And arctan(2) = π/2 - arctan(1/2) < 1.58 - 0.4 = 1.18,
    so arctan(2)/2 < 0.59 < 0.62. -/
theorem two_arctan_third_gt_half_arctan_two : arctan 2 / 2 < 2 * arctan (1/3) := by
  have h_arctan_third : arctan (1/3) > 31/100 := arctan_third_gt_point_three_one
  have h_arctan_half_lower : arctan (1/2) > 2/5 := arctan_half_gt_two_fifths
  have h_pi_half : Real.pi / 2 < 158/100 := by linarith [Real.pi_lt_d2]

  -- Use arctan(x⁻¹) = π/2 - arctan(x) for x > 0
  have h_complement : arctan (2⁻¹) = Real.pi / 2 - arctan 2 := by
    exact arctan_inv_of_pos (by norm_num : (0:ℝ) < 2)

  -- arctan(1/2) = π/2 - arctan(2), so arctan(2) = π/2 - arctan(1/2)
  have h_arctan_two_eq : arctan 2 = Real.pi / 2 - arctan (1/2) := by
    have h_inv : (2:ℝ)⁻¹ = 1/2 := by norm_num
    rw [h_inv] at h_complement
    linarith

  -- arctan(2) = π/2 - arctan(1/2) < 1.58 - 0.4 = 1.18
  have h_arctan_two_upper : arctan 2 < 118/100 := by
    rw [h_arctan_two_eq]
    linarith

  -- 2 * 0.31 = 0.62 > 1.18/2 = 0.59 > arctan(2)/2
  linarith

/-- 2 * arctan(1/5) = arctan(5/12) using the arctan addition formula. -/
theorem two_arctan_fifth_eq : 2 * arctan ((1:ℝ)/5) = arctan (5/12) := by
  have h_prod : (1:ℝ)/5 * (1/5) < 1 := by norm_num
  have h_add := arctan_add h_prod
  have h_eq : ((1:ℝ)/5 + 1/5) / (1 - 1/5 * (1/5)) = 5/12 := by norm_num
  rw [h_eq] at h_add
  linarith

/-- 4 * arctan(1/5) = arctan(120/119) using the arctan addition formula. -/
theorem four_arctan_fifth_eq : 4 * arctan ((1:ℝ)/5) = arctan (120/119) := by
  have h1 := two_arctan_fifth_eq
  have h_prod : (5:ℝ)/12 * (5/12) < 1 := by norm_num
  have h_add := arctan_add h_prod
  have h_eq : ((5:ℝ)/12 + 5/12) / (1 - 5/12 * (5/12)) = 120/119 := by norm_num
  rw [h_eq] at h_add
  calc 4 * arctan (1/5)
      = 2 * (2 * arctan (1/5)) := by ring
    _ = 2 * arctan (5/12) := by rw [h1]
    _ = arctan (120/119) := by linarith

/-- arctan(120/119) > arctan(2)/2.
    Since 120/119 > 1 and arctan(2) < π/2, we have arctan(2)/2 < π/4 = arctan(1) < arctan(120/119). -/
theorem arctan_120_119_gt_half_arctan_two : arctan 2 / 2 < arctan (120/119) := by
  -- arctan(120/119) > arctan(1) = π/4 since 120/119 > 1
  have h1 : arctan (120/119) > arctan 1 := arctan_lt_arctan (by norm_num : (1:ℝ) < 120/119)
  have h2 : arctan 1 = Real.pi / 4 := arctan_one
  -- arctan(2) < π/2, so arctan(2)/2 < π/4
  have h3 : arctan 2 < Real.pi / 2 := arctan_lt_pi_div_two 2
  have h4 : arctan 2 / 2 < Real.pi / 4 := by linarith
  -- Combine: arctan(2)/2 < π/4 = arctan(1) < arctan(120/119)
  calc arctan 2 / 2
      < Real.pi / 4 := h4
    _ = arctan 1 := h2.symm
    _ < arctan (120/119) := h1

/-- Four times arctan(1/5) is greater than L_rec = arctan(2)/2.
    This is used for the mixed-sign phase bound. -/
theorem four_arctan_fifth_gt_L_rec : 4 * arctan ((1:ℝ)/5) > arctan 2 / 2 := by
  rw [four_arctan_fifth_eq]
  exact arctan_120_119_gt_half_arctan_two

end

end Real
