/-
  TwoChart_NeumannSeries

  Neumann-series inversion in a complete normed ring.

  This file provides the standard geometric-series inverse for `1 + x` under the
  small-norm condition `‖x‖ < 1`, together with explicit left/right inverse
  identities and a quantitative norm bound.

  In the paper’s parametrix construction, this is the algebraic step that
  upgrades an *approximate inverse* of the form

      P * B = 1 + E,

  with `‖E‖ < 1`, into an *actual* right inverse

      P * (B * (∑' n, (-E)^n)) = 1.

  No axioms and no placeholders are introduced here; all statements are proved
  from Mathlib’s geometric-series lemmas.
-/

import Mathlib.Analysis.SpecificLimits.Normed

namespace TwoChartEgorov

open scoped BigOperators

noncomputable section

namespace Neumann

section CompleteNormedRing

variable {R : Type*} [NormedRing R] [CompleteSpace R]

/-- The Neumann-series candidate for `(1 + x)^{-1}`: `∑_{n≥0} (-x)^n`. -/
@[simp] def invOneAdd (x : R) : R := ∑' n : ℕ, (-x) ^ n

/-- Right-inverse identity: `invOneAdd x * (1 + x) = 1` for `‖x‖ < 1`. -/
 theorem invOneAdd_mul_one_add (x : R) (hx : ‖x‖ < 1) :
    invOneAdd x * (1 + x) = 1 := by
  -- `geom_series_mul_neg` gives `(∑' n, y^n) * (1 - y) = 1`.
  -- Apply with `y = -x`.
  simpa [invOneAdd, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (geom_series_mul_neg (-x) (by simpa [norm_neg] using hx))

/-- Left-inverse identity: `(1 + x) * invOneAdd x = 1` for `‖x‖ < 1`. -/
 theorem one_add_mul_invOneAdd (x : R) (hx : ‖x‖ < 1) :
    (1 + x) * invOneAdd x = 1 := by
  -- `mul_neg_geom_series` gives `(1 - y) * (∑' n, y^n) = 1`.
  -- Apply with `y = -x`.
  simpa [invOneAdd, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (mul_neg_geom_series (-x) (by simpa [norm_neg] using hx))

/-- `(1 + x)` is a unit for `‖x‖ < 1`, with inverse explicitly given by `invOneAdd x`. -/
 theorem isUnit_one_add_of_norm_lt_one (x : R) (hx : ‖x‖ < 1) : IsUnit (1 + x) := by
  refine ⟨⟨(1 + x), invOneAdd x, ?_, ?_⟩, rfl⟩
  · -- `(1 + x) * invOneAdd x = 1`
    exact one_add_mul_invOneAdd (x := x) hx
  · -- `invOneAdd x * (1 + x) = 1`
    exact invOneAdd_mul_one_add (x := x) hx

/-! ### Convenience wrappers

In applications, one frequently proves a bound of the form `‖E‖ ≤ r` with `r < 1`.
The following lemmas package the corresponding `‖E‖ < 1` hypotheses.
-/

/-- If `‖x‖ ≤ r` and `r < 1`, then `1 + x` is a unit. -/
theorem isUnit_one_add_of_norm_le {x : R} {r : ℝ} (hx : ‖x‖ ≤ r) (hr : r < 1) :
    IsUnit (1 + x) :=
  isUnit_one_add_of_norm_lt_one (x := x) (lt_of_le_of_lt hx hr)

omit [CompleteSpace R] in
/-- Quantitative bound on the Neumann-series inverse.

This is the bound from Mathlib’s `tsum_geometric_le_of_norm_lt_one`.
It does *not* assume `‖1‖ = 1`.
-/
 theorem norm_invOneAdd_le (x : R) (hx : ‖x‖ < 1) :
    ‖invOneAdd x‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹ := by
  -- Apply the geometric-series norm bound to `-x`.
  simpa [invOneAdd, norm_neg] using
    (tsum_geometric_le_of_norm_lt_one (-x) (by simpa [norm_neg] using hx))

omit [CompleteSpace R] in
/-- In a `NormOneClass`, the previous bound simplifies to `‖invOneAdd x‖ ≤ (1 - ‖x‖)⁻¹`. -/
 theorem norm_invOneAdd_le_inv_one_sub_norm
    (x : R) (hx : ‖x‖ < 1) [NormOneClass R] :
    ‖invOneAdd x‖ ≤ (1 - ‖x‖)⁻¹ := by
  have h := norm_invOneAdd_le (x := x) hx
  -- `‖(1:R)‖ = 1`, so the additive term `‖1‖ - 1` vanishes.
  simpa [NormOneClass.norm_one] using h

/-- Parametrix upgrade (right-inverse form):

If `P * B = 1 + E` and `‖E‖ < 1`, then `P * (B * invOneAdd E) = 1`.

This is the exact algebraic pattern used after bounding the remainder operator.
-/
 theorem rightInverse_of_mul_eq_one_add
    {P B E : R} (hPB : P * B = 1 + E) (hE : ‖E‖ < 1) :
    P * (B * invOneAdd E) = 1 := by
  calc
    P * (B * invOneAdd E) = (P * B) * invOneAdd E := by
      simp [mul_assoc]
    _ = (1 + E) * invOneAdd E := by
      simp [hPB]
    _ = 1 := one_add_mul_invOneAdd (x := E) hE

/-- Parametrix upgrade (left-inverse form):

If `B * P = 1 + E` and `‖E‖ < 1`, then `(invOneAdd E * B) * P = 1`.
-/
 theorem leftInverse_of_mul_eq_one_add
    {P B E : R} (hBP : B * P = 1 + E) (hE : ‖E‖ < 1) :
    (invOneAdd E * B) * P = 1 := by
  calc
    (invOneAdd E * B) * P = invOneAdd E * (B * P) := by
      simp [mul_assoc]
    _ = invOneAdd E * (1 + E) := by
      simp [hBP]
    _ = 1 := invOneAdd_mul_one_add (x := E) hE

end CompleteNormedRing

end Neumann

end
end TwoChartEgorov
