import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan


/-!
# A concrete lower bound on `Real.arctan 2`

We prove the numerical inequality

`(1.1 : ℝ) < Real.arctan 2`

using the Taylor series for `arctan` at `0` (already available in mathlib as a
convergent power series on `|x| < 1`), together with elementary alternating‑series
bounds and standard bounds on `π`.
-/

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
  -- This is exactly `Real.hasSum_arctan` from `Complex/Arctan.lean`.
  simpa [arctanSeriesTerm] using Real.hasSum_arctan (x := x) hx

/-- The sequence of absolute Taylor terms at `x = 1/2`. -/
def arctanHalfTerm (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ (2 * n + 1) / (2 * n + 1)

lemma HasSum.congr {α β : Type*} [AddCommMonoid β] [TopologicalSpace β]
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
  -- `‖1/2‖ < 1`
  have hx : ‖(1 : ℝ) / 2‖ < (1 : ℝ) := by
    simp; norm_num
  -- rewrite the generic statement to our specialized form
  have h := hasSum_arctan_series (x := (1 : ℝ) / 2) hx
  -- unfold and match definitions
  refine HasSum.congr h ?_ ?_
  · intro n
    unfold arctanSeriesTerm arctanHalfTerm
    ring
  · rfl
/-- The sequence of Taylor coefficients for `x = 1/2` is antitone (decreasing). -/
lemma arctanHalfTerm_antitone : Antitone arctanHalfTerm := by
  -- We show `arctanHalfTerm (n+1) ≤ arctanHalfTerm n` for all `n`
  -- and then use `antitone_nat_of_succ_le`.
  have h_succ_le : ∀ n : ℕ, arctanHalfTerm (n + 1) ≤ arctanHalfTerm n := by
    intro n
    -- Work with explicit formulas
    have hpos_denom₁ : (0 : ℝ) < (2 * n + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_pos _)
    have hpos_denom₂ : (0 : ℝ) < (2 * n + 3 : ℝ) := by
      exact_mod_cast (Nat.succ_pos _)
    have hpos_pow : 0 < ((1 : ℝ) / 2) ^ (2 * n + 1) := by
      have : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
      exact pow_pos this _
    -- Express the ratio `arctanHalfTerm (n+1) / arctanHalfTerm n`.
    -- We will show this ratio ≤ 1.
    have h_ratio :
        arctanHalfTerm (n + 1) / arctanHalfTerm n =
          ((2 * n + 1 : ℝ) / (2 * n + 3 : ℝ)) / 4 := by
      -- Expand definitions and simplify.
      unfold arctanHalfTerm
      -- exponents: 2*(n+1)+1 = 2n+3 = (2n+1)+2
      have hexp : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
      rw [hexp, pow_add, pow_two, one_div, ← one_div, one_div]
      field_simp
      -- After `field_simp` we are left with a simple linear identity in `n`.
      -- Prove the equivalent version with `2^2` replaced by `4` using `ring`,
      -- then rewrite back.
      have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
      have : (↑n * 2 + 3) * 4 = (1 + (↑n + 1) * 2) * 4 := by
        ring
      simp [h2]; ring_nf


    -- Now bound the ratio.
    have h_ratio_le_one : arctanHalfTerm (n + 1) / arctanHalfTerm n ≤ 1 := by
      -- Using the explicit formula:
      have h_main :
          ((2 * n + 1 : ℝ) / (2 * n + 3 : ℝ)) / 4 ≤ 1 := by
        -- First prove the linear inequality `2n+1 ≤ 4(2n+3)`
        have h_poly : (2 * n + 1 : ℝ) ≤ 4 * (2 * n + 3 : ℝ) := by
          have h_diff :
              4 * (2 * n + 3 : ℝ) - (2 * n + 1 : ℝ) = (6 : ℝ) * n + 11 := by
            ring
          have h_nonneg : (0 : ℝ) ≤ (6 : ℝ) * n + 11 := by
            have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le _)
            have h6n : (0 : ℝ) ≤ (6 : ℝ) * n := mul_nonneg (by norm_num) hn
            have : (0 : ℝ) ≤ (6 : ℝ) * n + 11 := by linarith
            exact this
          have h_sub : (0 : ℝ) ≤ 4 * (2 * n + 3 : ℝ) - (2 * n + 1 : ℝ) := by
            simpa [h_diff] using h_nonneg
          exact sub_nonneg.mp h_sub
        -- Denominator `4 * (2n+3)` is positive
        have hden_pos : 0 < (4 : ℝ) * (2 * n + 3 : ℝ) := by
          have h4 : (0 : ℝ) < 4 := by norm_num
          exact mul_pos h4 hpos_denom₂
        -- From `h_poly`, deduce `(2n+1)/(4(2n+3)) ≤ 1`
        have hdiv : (2 * n + 1 : ℝ) / (4 * (2 * n + 3 : ℝ)) ≤ 1 := by
          refine (div_le_iff₀ hden_pos).2 ?_
          simpa [mul_comm, mul_left_comm, mul_assoc] using h_poly
        -- Rewrite `((2n+1)/(2n+3))/4` as `(2n+1)/(4(2n+3))`
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      -- Finally, combine with `h_ratio` to get the desired bound
      simpa [h_ratio] using h_main
    -- Finally, multiply by the positive term `arctanHalfTerm n` to get the desired inequality.
    have hfn_pos : 0 < arctanHalfTerm n := by
      unfold arctanHalfTerm
      have : 0 < ((1 : ℝ) / 2) ^ (2 * n + 1) := by
        have : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
        exact pow_pos this _
      have hpos_coeff : (0 : ℝ) < (2 * n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos _)
      exact div_pos this hpos_coeff

    have hmul :=
      (mul_le_mul_of_nonneg_right h_ratio_le_one (le_of_lt hfn_pos))

    -- LHS: (arctanHalfTerm (n+1) / arctanHalfTerm n) * arctanHalfTerm n = arctanHalfTerm (n+1)
    -- RHS: 1 * arctanHalfTerm n = arctanHalfTerm n
    have h_ne : arctanHalfTerm n ≠ 0 := ne_of_gt hfn_pos
    have h_final : arctanHalfTerm (n + 1) ≤ arctanHalfTerm n := by
      have h_cancel : arctanHalfTerm (n + 1) / arctanHalfTerm n * arctanHalfTerm n = arctanHalfTerm (n + 1) := by
        rw [div_mul_cancel₀]
        exact h_ne
      rw [← h_cancel]
      simpa [one_mul] using hmul

    exact h_final
  -- Upgrade to `Antitone`
  exact antitone_nat_of_succ_le h_succ_le

/-- The limit of the alternating Taylor series at `x = 1/2` is squeezed between
partial sums with 4 and 5 terms. -/
lemma arctan_half_between_partial_sums :
    arctanPartialSum ((1 : ℝ) / 2) (2 * 2) ≤
      Real.arctan ((1 : ℝ) / 2) ∧
      Real.arctan ((1 : ℝ) / 2) ≤
        arctanPartialSum ((1 : ℝ) / 2) (2 * 2 + 1) := by
  -- Express `arctanPartialSum` in terms of `arctanHalfTerm`.
  have h_series :
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * arctanHalfTerm i)
        atTop (𝓝 (Real.arctan ((1 : ℝ) / 2))) :=
    arctan_half_series.tendsto_sum_nat
  -- Rewrite to match the lemmas' expected shape.
  have hfl :
      Tendsto (fun n : ℕ =>
          ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * arctanHalfTerm i)
        atTop (𝓝 (Real.arctan ((1 : ℝ) / 2))) := h_series
  -- Lower bound from even partial sum (2k terms) for an alternating antitone series.
  have h_lower :
      ∑ i ∈ Finset.range (2 * 2), (-1 : ℝ) ^ i * arctanHalfTerm i
        ≤ Real.arctan ((1 : ℝ) / 2) :=
    Antitone.alternating_series_le_tendsto
      (l := Real.arctan ((1 : ℝ) / 2))
      (f := arctanHalfTerm)
      (k := 2)
      (hfl := hfl)
      (hfa := arctanHalfTerm_antitone)
  -- Upper bound from odd partial sum (2k+1 terms).
  have h_upper :
      Real.arctan ((1 : ℝ) / 2)
        ≤ ∑ i ∈ Finset.range (2 * 2 + 1), (-1 : ℝ) ^ i * arctanHalfTerm i :=
    Antitone.tendsto_le_alternating_series
      (l := Real.arctan ((1 : ℝ) / 2))
      (f := arctanHalfTerm)
      (k := 2)
      (hfl := hfl)
      (hfa := arctanHalfTerm_antitone)
  -- Identify these partial sums with `arctanPartialSum (1/2)`.
  have h_eq_even :
      arctanPartialSum ((1 : ℝ) / 2) (2 * 2) =
        ∑ i ∈ Finset.range (2 * 2), (-1 : ℝ) ^ i * arctanHalfTerm i := by
    unfold arctanPartialSum
    apply Finset.sum_congr rfl
    intro i hi
    unfold arctanSeriesTerm arctanHalfTerm
    ring
  have h_eq_odd :
      arctanPartialSum ((1 : ℝ) / 2) (2 * 2 + 1) =
        ∑ i ∈ Finset.range (2 * 2 + 1), (-1 : ℝ) ^ i * arctanHalfTerm i := by
    unfold arctanPartialSum
    apply Finset.sum_congr rfl
    intro i hi
    unfold arctanSeriesTerm arctanHalfTerm
    ring
  constructor
  · -- lower bound
    rw [h_eq_even]
    exact h_lower
  · -- upper bound
    rw [h_eq_odd]
    exact h_upper

/-- Explicit closed form for the 5‑term Taylor partial sum at `x = 1/2`. -/
lemma arctanPartialSum_half_5 :
    arctanPartialSum ((1 : ℝ) / 2) 5 =
      (1 : ℝ) / 2 - 1 / 24 + 1 / 160 - 1 / 896 + 1 / 4608 := by
  -- Expand the definition and simplify.
  unfold arctanPartialSum arctanSeriesTerm
  -- `range 5` has elements 0,1,2,3,4
  have : (Finset.range 5 : Finset ℕ) = {0,1,2,3,4} := by
    decide
  -- Use the explicit sum
  simp [this, pow_succ, pow_add, two_mul] ; ring

/-- A simple numerical upper bound: `arctan (1/2) < 0.464`. -/
lemma arctan_half_lt_0464 : Real.arctan ((1 : ℝ) / 2) < (464 : ℝ) / 1000 := by
  -- From `arctan_half_between_partial_sums` we know `arctan (1/2) ≤` the 5‑term sum.
  obtain ⟨_, h_upper⟩ := arctan_half_between_partial_sums
  -- Replace the partial sum by its explicit rational value.
  have h_eval :
      arctanPartialSum ((1 : ℝ) / 2) 5
        = (74783 : ℝ) / 161280 := by
    -- This is just arithmetic: 1/2 - 1/24 + 1/160 - 1/896 + 1/4608 = 74783/161280.
    have := arctanPartialSum_half_5
    -- Let `norm_num` do the heavy lifting on rationals.
    have : (1 : ℝ) / 2 - 1 / 24 + 1 / 160 - 1 / 896 + 1 / 4608
        = (74783 : ℝ) / 161280 := by
      norm_num
    calc arctanPartialSum ((1 : ℝ) / 2) 5
        = (1 : ℝ) / 2 - 1 / 24 + 1 / 160 - 1 / 896 + 1 / 4608 := arctanPartialSum_half_5
      _ = (74783 : ℝ) / 161280 := this
  -- So `arctan (1/2) ≤ 74783/161280`.
  have h_upper' :
      Real.arctan ((1 : ℝ) / 2) ≤ (74783 : ℝ) / 161280 := by
    rw [← h_eval]
    exact h_upper
  -- And `74783/161280 < 464/1000`.
  have h_rat : (74783 : ℝ) / 161280 < (464 : ℝ) / 1000 := by
    norm_num
  -- Combine.
  exact lt_of_le_of_lt h_upper' h_rat

/-- A concrete lower bound on `π/2 - arctan (1/2)`. -/
lemma one_point_one_lt_pi_over_two_sub_arctan_half :
    (1.1 : ℝ) < Real.pi / 2 - Real.arctan ((1 : ℝ) / 2) := by
  -- It suffices to show `π/2 > 1.1 + arctan(1/2)`.
  have h_arctan : Real.arctan ((1 : ℝ) / 2) < (464 : ℝ) / 1000 :=
    arctan_half_lt_0464
  have h_target :
      (1.1 : ℝ) + (464 : ℝ) / 1000 < Real.pi / 2 := by
    -- Compute the rational sum 1.1 + 0.464 = 1564/1000.
    have h_eq : (1.1 : ℝ) + (464 : ℝ) / 1000 = (1564 : ℝ) / 1000 := by
      norm_num
    -- Show this rational is < π/2 using `pi_gt_d2 : 3.14 < π`.
    -- Concretely: 2 * (1564/1000) = 3128/1000 < 3.14 = 3140/1000.
    have h_rat : (3128 : ℝ) / 1000 < (3140 : ℝ) / 1000 := by
      norm_num
    have h_pi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
    -- Convert 3.14 to the same form as h_rat
    have h_pi' : (3140 : ℝ) / 1000 < Real.pi := by
      convert h_pi using 1
      norm_num
    have h_lt_pi : (3128 : ℝ) / 1000 < Real.pi :=
      lt_trans h_rat h_pi'
    -- Divide by 2>0.
    have h_pos_two : (0 : ℝ) < 2 := by norm_num
    have h_div : (1564 : ℝ) / 1000 < Real.pi / 2 := by
      have := div_lt_div_of_pos_right h_lt_pi h_pos_two
      -- We have: (3128/1000) / 2 = 1564/1000 < π / 2
      convert div_lt_div_of_pos_right h_lt_pi h_pos_two using 1
      norm_num
    -- Rewrite back to the decimal expression.
    simpa [h_eq] using h_div
  -- Now use monotonicity to absorb `arctan(1/2)`.
  -- We have: π/2 > 1.1 + 0.464 and `arctan(1/2) < 0.464`,
  -- hence π/2 > 1.1 + arctan(1/2).
  have h_sum :
      (1.1 : ℝ) + Real.arctan ((1 : ℝ) / 2) < (1.1 : ℝ) + (464 : ℝ) / 1000 :=
    add_lt_add_left h_arctan _
  have := lt_trans h_sum h_target
  -- Rearrange: a < b - c ↔ a + c < b.
  have : (1.1 : ℝ) < Real.pi / 2 - Real.arctan ((1 : ℝ) / 2) :=
    by
      -- `this` is `(1.1 + atan(1/2)) < π/2`; rearrange to `1.1 < π/2 - atan(1/2)`.
      linarith
  exact this

/-- Final numerical inequality: `arctan 2 > 1.1`. -/
theorem arctan_two_gt_one_point_one : (1.1 : ℝ) < Real.arctan 2 := by
  -- Use the identity `arctan (1/x) = π/2 - arctan x` for `x > 0`, with `x = 1/2`.
  have h_inv :
      Real.arctan (2 : ℝ) = Real.pi / 2 - Real.arctan ((1 : ℝ) / 2) := by
    have hpos : (0 : ℝ) < ((1 : ℝ) / 2) := by norm_num
    -- `arctan_inv_of_pos (h : 0 < x)` gives `arctan x⁻¹ = π/2 - arctan x`.
    have := Real.arctan_inv_of_pos hpos
    -- Rewrite `x⁻¹` as `2`.
    have hx : ((1 : ℝ) / 2)⁻¹ = (2 : ℝ) := by field_simp
    simpa [hx] using this
  -- Combine with the lower bound on `π/2 - arctan (1/2)`.
  have h_main := one_point_one_lt_pi_over_two_sub_arctan_half
  rw [h_inv]
  exact h_main

end

end Real
