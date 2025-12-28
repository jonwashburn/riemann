import TwoChart_ParametrixInvertibility

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Small-parameter lemmas for the parametrix upgrade

This file provides the quantitative “choose `h` small enough” bridge between
analytic remainder bounds and the Banach-algebra Neumann-series inversion.

Main ingredients:

* a monotonicity lemma for powers on the interval `0 ≤ h ≤ 1`;
* a convenient bound: if `‖E‖ ≤ C * h^κ` with `κ ≥ 1` and
  `h ≤ min 1 (1/(2C))`, then `‖E‖ ≤ 1/2 < 1`;
* a family-level parametrix upgrade lemma producing an explicit `h₁ > 0` such
  that `P(h)` is a unit for all `0 < h ≤ h₁`.

The last statement is exactly the “Banach-algebra” step used in the paper after
one has established polynomial remainder bounds.
-/

namespace TwoChartEgorov

open scoped BigOperators Real

noncomputable section

namespace Parametrix

namespace SmallH

/-! ## Powers on `[0,1]` -/

/-- If `0 ≤ h ≤ 1`, then `h^(n+1) ≤ h^n`. -/
lemma pow_succ_le_pow {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (n : ℕ) :
    h ^ (n + 1) ≤ h ^ n := by
  -- `h^(n+1) = h^n * h` and `h ≤ 1`.
  have hn0 : 0 ≤ h ^ n := pow_nonneg hh0 n
  -- Multiply the inequality `h ≤ 1` by the nonnegative factor `h^n`.
  have := mul_le_mul_of_nonneg_left hh1 hn0
  -- Simplify.
  simpa [pow_succ, mul_assoc] using this

/-- If `0 ≤ h ≤ 1` and `1 ≤ k`, then `h^k ≤ h`. -/
lemma pow_le_self_of_le_one {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) {k : ℕ}
    (hk : 1 ≤ k) : h ^ k ≤ h := by
  cases k with
  | zero =>
      cases hk
  | succ n =>
      -- We prove `h^(n+1) ≤ h` by induction on `n`.
      induction n with
      | zero =>
          simp
      | succ n ih =>
          -- `h^(n+2) ≤ h^(n+1) ≤ h`.
          have hstep : h ^ (n + 2) ≤ h ^ (n + 1) := by
            -- Apply the previous lemma with exponent `n+1`.
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (pow_succ_le_pow (h := h) hh0 hh1 (n := n + 1))
          exact le_trans hstep ih

/-! ## Turning polynomial smallness into a uniform `< 1` bound -/

/-- If `C > 0` and `h ≤ 1/(2C)`, then `C*h ≤ 1/2`. -/
lemma mul_le_half_of_le_inv {C h : ℝ} (hC : 0 < C) (hh : h ≤ 1 / (2 * C)) :
    C * h ≤ (1/2 : ℝ) := by
  have hC0 : 0 ≤ C := le_of_lt hC
  have hmul : C * h ≤ C * (1 / (2 * C)) := by
    -- Multiply by the nonnegative scalar `C`.
    simpa [mul_assoc] using (mul_le_mul_of_nonneg_left hh hC0)
  -- Simplify the right-hand side.
  have hcalc : C * (1 / (2 * C)) = (1/2 : ℝ) := by
    have hne : (C : ℝ) ≠ 0 := ne_of_gt hC
    field_simp [hne]
  simpa [hcalc] using hmul

/-- Convenience bound used throughout the parametrix argument.

If `‖E‖ ≤ C*h^κ` with `κ ≥ 1` and `h` is small enough so that
`h ≤ 1` and `h ≤ 1/(2C)`, then `‖E‖ ≤ 1/2`.
-/
lemma norm_le_half_of_bound {R : Type*} [NormedRing R]
    {E : R} {C h : ℝ} {κ : ℕ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hC : 0 < C) (hκ : 1 ≤ κ)
    (hE : ‖E‖ ≤ C * h ^ κ) (hhC : h ≤ 1 / (2 * C)) :
    ‖E‖ ≤ (1/2 : ℝ) := by
  have hp : h ^ κ ≤ h := pow_le_self_of_le_one (h := h) hh0 hh1 hκ
  have hC0 : 0 ≤ C := le_of_lt hC
  have hmul : C * h ^ κ ≤ C * h := by
    exact mul_le_mul_of_nonneg_left hp hC0
  have hlin : C * h ≤ (1/2 : ℝ) := mul_le_half_of_le_inv (C := C) (h := h) hC hhC
  exact le_trans hE (le_trans hmul hlin)

/-- A convenient formulation: under the same hypotheses as
`norm_le_half_of_bound`, we get the small-norm condition `‖E‖ < 1`.
-/
lemma norm_lt_one_of_bound {R : Type*} [NormedRing R]
    {E : R} {C h : ℝ} {κ : ℕ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hC : 0 < C) (hκ : 1 ≤ κ)
    (hE : ‖E‖ ≤ C * h ^ κ) (hhC : h ≤ 1 / (2 * C)) :
    ‖E‖ < 1 := by
  have hhalf : ‖E‖ ≤ (1/2 : ℝ) :=
    norm_le_half_of_bound (E := E) (C := C) (h := h) (κ := κ) hh0 hh1 hC hκ hE hhC
  have : (1/2 : ℝ) < 1 := by norm_num
  exact lt_of_le_of_lt hhalf this

end SmallH

/-! ## A family-level parametrix upgrade with an explicit `h₁`

This is the “next step” after obtaining polynomial operator-norm bounds for the
remainder terms: we package the choice of `h₁` and the deduction that `P(h)` is
a unit for all `0 < h ≤ h₁`.
-/

section Family

open Neumann

variable {R : Type*} [NormedRing R] [CompleteSpace R]

/-- A concrete (and robust) choice of smallness threshold.

We deliberately avoid extracting roots: requiring `h ≤ 1/(2C)` is enough because
for `h ≤ 1` and `κ ≥ 1` we have `h^κ ≤ h`.
-/
def hSmall (h0 CE CF : ℝ) : ℝ :=
  min h0 (min 1 (min (1 / (2 * CE)) (1 / (2 * CF))))

lemma hSmall_pos {h0 CE CF : ℝ} (hh0 : 0 < h0) (hCE : 0 < CE) (hCF : 0 < CF) :
    0 < hSmall h0 CE CF := by
  -- Each component in the `min` is strictly positive.
  have h1 : 0 < (1 : ℝ) := by norm_num
  have hCEpos : 0 < 1 / (2 * CE) := by
    have : 0 < (2 * CE : ℝ) := by nlinarith
    simpa [one_div] using (inv_pos.2 this)
  have hCFpos : 0 < 1 / (2 * CF) := by
    have : 0 < (2 * CF : ℝ) := by nlinarith
    simpa [one_div] using (inv_pos.2 this)
  have hmin3 : 0 < min (1 / (2 * CE)) (1 / (2 * CF)) := lt_min hCEpos hCFpos
  have hmin2 : 0 < min 1 (min (1 / (2 * CE)) (1 / (2 * CF))) := lt_min h1 hmin3
  have hmin1 : 0 < min h0 (min 1 (min (1 / (2 * CE)) (1 / (2 * CF)))) := lt_min hh0 hmin2
  simpa [hSmall] using hmin1

lemma hSmall_le_h0 (h0 CE CF : ℝ) : hSmall h0 CE CF ≤ h0 :=
  le_min_left _ _

lemma hSmall_le_one (h0 CE CF : ℝ) : hSmall h0 CE CF ≤ 1 := by
  -- `hSmall ≤ min 1 ... ≤ 1`.
  have : hSmall h0 CE CF ≤ min 1 (min (1 / (2 * CE)) (1 / (2 * CF))) :=
    le_min_right _ _
  exact le_trans this (le_min_left _ _)

lemma hSmall_le_invCE (h0 CE CF : ℝ) : hSmall h0 CE CF ≤ 1 / (2 * CE) := by
  have : hSmall h0 CE CF ≤ min 1 (min (1 / (2 * CE)) (1 / (2 * CF))) :=
    le_min_right _ _
  have : hSmall h0 CE CF ≤ min (1 / (2 * CE)) (1 / (2 * CF)) :=
    le_trans this (le_min_right _ _)
  exact le_trans this (le_min_left _ _)

lemma hSmall_le_invCF (h0 CE CF : ℝ) : hSmall h0 CE CF ≤ 1 / (2 * CF) := by
  have : hSmall h0 CE CF ≤ min 1 (min (1 / (2 * CE)) (1 / (2 * CF))) :=
    le_min_right _ _
  have : hSmall h0 CE CF ≤ min (1 / (2 * CE)) (1 / (2 * CF)) :=
    le_trans this (le_min_right _ _)
  exact le_trans this (le_min_right _ _)

/-- **Family-level parametrix-to-invertibility upgrade.**

Assume a two-sided parametrix identity holds for all `h ∈ (0,h0]`:

* `P(h) * B(h) = 1 + E(h)` and `B(h) * P(h) = 1 + F(h)`,

and that the errors are polynomially small:

* `‖E(h)‖ ≤ CE * h^κ` and `‖F(h)‖ ≤ CF * h^κ`,

with `κ ≥ 1`. Then there exists an explicit `h₁ > 0` such that for every
`0 < h ≤ h₁`, the element `P(h)` is a unit (hence invertible).

The chosen `h₁` is the minimum of the various smallness constraints.
-/
theorem isUnit_of_twoSided_parametrix_family_of_polyBound
    {P B E F : ℝ → R}
    {h0 CE CF : ℝ} (hh0 : 0 < h0)
    {κ : ℕ} (hκ : 1 ≤ κ)
    (hCE : 0 < CE) (hCF : 0 < CF)
    (hPB : ∀ {h : ℝ}, 0 < h → h ≤ h0 → P h * B h = 1 + E h)
    (hBP : ∀ {h : ℝ}, 0 < h → h ≤ h0 → B h * P h = 1 + F h)
    (hEbound : ∀ {h : ℝ}, 0 < h → h ≤ h0 → ‖E h‖ ≤ CE * h ^ κ)
    (hFbound : ∀ {h : ℝ}, 0 < h → h ≤ h0 → ‖F h‖ ≤ CF * h ^ κ) :
    ∃ h1 : ℝ, 0 < h1 ∧ ∀ {h : ℝ}, 0 < h → h ≤ h1 → IsUnit (P h) := by
  refine ⟨hSmall h0 CE CF, hSmall_pos (h0 := h0) (CE := CE) (CF := CF) hh0 hCE hCF, ?_⟩
  intro h hhpos hhle

  -- Unpack the consequences of `h ≤ hSmall ...`.
  have hh0le : h ≤ h0 := le_trans hhle (hSmall_le_h0 (h0 := h0) (CE := CE) (CF := CF))
  have hhle1 : h ≤ 1 := le_trans hhle (hSmall_le_one (h0 := h0) (CE := CE) (CF := CF))
  have hhleCE : h ≤ 1 / (2 * CE) := le_trans hhle (hSmall_le_invCE (h0 := h0) (CE := CE) (CF := CF))
  have hhleCF : h ≤ 1 / (2 * CF) := le_trans hhle (hSmall_le_invCF (h0 := h0) (CE := CE) (CF := CF))
  have hh0nonneg : 0 ≤ h := le_of_lt hhpos

  -- Show the Neumann-series hypotheses `‖E(h)‖ < 1` and `‖F(h)‖ < 1`.
  have hEnorm : ‖E h‖ < 1 :=
    SmallH.norm_lt_one_of_bound (E := E h) (C := CE) (h := h) (κ := κ)
      hh0nonneg hhle1 hCE hκ (hEbound hhpos hh0le) hhleCE
  have hFnorm : ‖F h‖ < 1 :=
    SmallH.norm_lt_one_of_bound (E := F h) (C := CF) (h := h) (κ := κ)
      hh0nonneg hhle1 hCF hκ (hFbound hhpos hh0le) hhleCF

  -- Apply the abstract two-sided parametrix upgrade.
  exact Parametrix.isUnit_of_twoSided_parametrix'
    (P := P h) (B := B h) (E := E h) (F := F h)
    (hPB := hPB hhpos hh0le) (hBP := hBP hhpos hh0le)
    hEnorm hFnorm

end Family

end Parametrix

end TwoChartEgorov
