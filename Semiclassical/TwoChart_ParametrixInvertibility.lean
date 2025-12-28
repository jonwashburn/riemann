/******************************************************************************
  TwoChart_ParametrixInvertibility

  Next step after:
  * the Schur/kernel machinery that yields quantitative bounds on remainder
    operators, and
  * `TwoChart_NeumannSeries`, which provides the Neumann-series inverse for
    `1 + E` under the small-norm hypothesis `‖E‖ < 1`.

  Paper correspondence
  --------------------

  In the paper’s parametrix argument, once one has constructed an *approximate*
  inverse `B` for an operator/symbol `P` and shown

      P * B = 1 + E,      B * P = 1 + F,

  together with bounds that make both `E` and `F` small in operator norm (for
  sufficiently small `h`), one upgrades to a genuine inverse by inserting the
  Neumann-series inverses of `(1 + E)` and `(1 + F)`.

  This file formalizes that Banach-algebra upgrade in a complete normed ring.

  There are **no axioms**, **no placeholders**, and **no `sorry`** in this file.
*******************************************************************************/

import TwoChart_NeumannSeries

namespace TwoChartEgorov

open scoped BigOperators

noncomputable section

namespace Parametrix

open Neumann

section CompleteNormedRing

variable {R : Type*} [NormedRing R] [CompleteSpace R]

/-- In any monoid, a left inverse and a right inverse of the same element coincide. -/
lemma leftInv_eq_rightInv {P invL invR : R}
    (hL : invL * P = 1) (hR : P * invR = 1) : invL = invR := by
  calc
    invL = invL * (P * invR) := by simp [hR]
    _ = (invL * P) * invR := by simp [mul_assoc]
    _ = 1 * invR := by simp [hL]
    _ = invR := by simp

/-- If `P` admits both a left inverse and a right inverse, then `P` is a unit. -/
theorem isUnit_of_left_right_inverse {P invL invR : R}
    (hL : invL * P = 1) (hR : P * invR = 1) : IsUnit P := by
  have hinv : invR * P = 1 := by
    -- Replace the left inverse by the right inverse using uniqueness.
    have hEq : invL = invR := leftInv_eq_rightInv (P := P) (invL := invL) (invR := invR) hL hR
    simpa [hEq] using hL
  refine ⟨⟨P, invR, hR, hinv⟩, rfl⟩

/-- Two-sided parametrix upgrade (unit form).

Assume

* `P * B = 1 + E` and `‖E‖ < 1` (a *right* parametrix), and
* `B * P = 1 + F` and `‖F‖ < 1` (a *left* parametrix).

Then `P` is a unit with explicit inverse

    P⁻¹ = B * invOneAdd E.

Moreover, the same inverse can be written as `invOneAdd F * B`.
-/
theorem isUnit_of_twoSided_parametrix
    {P B E F : R}
    (hPB : P * B = 1 + E) (hBP : B * P = 1 + F)
    (hE : ‖E‖ < 1) (hF : ‖F‖ < 1) :
    ∃ u : Units R,
      (u : R) = P ∧
      (↑(u⁻¹) : R) = B * invOneAdd E ∧
      (↑(u⁻¹) : R) = invOneAdd F * B := by
  -- Build a right inverse of `P` from the Neumann series for `1+E`.
  have hRight : P * (B * invOneAdd E) = 1 :=
    rightInverse_of_mul_eq_one_add (P := P) (B := B) (E := E) hPB hE

  -- Build a left inverse of `P` from the Neumann series for `1+F`.
  have hLeft : (invOneAdd F * B) * P = 1 :=
    leftInverse_of_mul_eq_one_add (P := P) (B := B) (E := F) hBP hF

  -- Uniqueness forces the two inverses to coincide.
  have hEqInv : invOneAdd F * B = B * invOneAdd E := by
    -- `invOneAdd F * B` is a left inverse and `B * invOneAdd E` is a right inverse.
    -- Hence they are equal.
    exact leftInv_eq_rightInv (P := P)
      (invL := invOneAdd F * B) (invR := B * invOneAdd E) hLeft hRight

  -- Conclude that `B * invOneAdd E` is a two-sided inverse.
  have hLeft' : (B * invOneAdd E) * P = 1 := by
    simpa [hEqInv] using hLeft

  refine ⟨⟨P, B * invOneAdd E, hRight, hLeft'⟩, rfl, rfl, ?_⟩
  -- Also identify the inverse as `invOneAdd F * B`.
  simpa [hEqInv]

/-- A convenient corollary: if `P * B = 1 + E` and `B * P = 1 + F` with
`‖E‖, ‖F‖ < 1`, then `P` is a unit. -/
theorem isUnit_of_twoSided_parametrix'
    {P B E F : R}
    (hPB : P * B = 1 + E) (hBP : B * P = 1 + F)
    (hE : ‖E‖ < 1) (hF : ‖F‖ < 1) : IsUnit P := by
  rcases isUnit_of_twoSided_parametrix (P := P) (B := B) (E := E) (F := F) hPB hBP hE hF with
    ⟨u, hu, - , -⟩
  exact ⟨u, hu⟩

/-- Quantitative norm bound for the inverse in a `NormOneClass`.

If `P` is inverted via the parametrix formula

    P⁻¹ = B * invOneAdd E,

and `‖E‖ < 1`, then

    ‖P⁻¹‖ ≤ ‖B‖ * (1 - ‖E‖)⁻¹.

This is the bound used in the paper after one has a uniform estimate on `‖B‖`
(and makes `‖E‖` sufficiently small by choosing `h` small).
-/
theorem norm_inv_le_mul_inv_one_sub_norm
    [NormOneClass R]
    {P B E : R}
    (hPB : P * B = 1 + E) (hE : ‖E‖ < 1)
    {invP : R} (hinv : P * invP = 1) (hinvDef : invP = B * invOneAdd E) :
    ‖invP‖ ≤ ‖B‖ * (1 - ‖E‖)⁻¹ := by
  -- Reduce to the Neumann-series norm bound.
  subst hinvDef
  calc
    ‖B * invOneAdd E‖ ≤ ‖B‖ * ‖invOneAdd E‖ := by
      -- `NormedRing` only provides submultiplicativity of the norm.
      simpa using (norm_mul_le B (invOneAdd E))
    _ ≤ ‖B‖ * (1 - ‖E‖)⁻¹ := by
      gcongr
      exact norm_invOneAdd_le_inv_one_sub_norm (x := E) hE

end CompleteNormedRing

end Parametrix

end TwoChartEgorov
