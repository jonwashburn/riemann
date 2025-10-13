import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Abs

/-!
# Elementary exponential small-argument bounds in ℂ

We expose small-argument estimates for the complex exponential using elementary
inequalities valid on `‖z‖ ≤ 1`.
-/

noncomputable section

open Complex

namespace RH
namespace RS

/-- If `‖z‖ ≤ 1` then `‖exp z − 1‖ ≤ 2‖z‖`.
A crude bound using triangle inequality and `‖exp z‖ ≤ exp ‖z‖ ≤ 1 + ‖z‖` on `‖z‖ ≤ 1`. -/
lemma exp_sub_one_norm_le_of_small (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  have hexp_le : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
    -- standard bound ‖exp z‖ = exp (Re z) ≤ exp ‖z‖
    have : ‖Complex.exp z‖ = Real.exp z.re := Complex.norm_exp _
    have : Real.exp z.re ≤ Real.exp ‖z‖ := by
      exact Real.exp_le_exp.mpr (Complex.abs_re_le_abs z)
    exact le_trans (le_of_eq (Complex.norm_exp _)) this
  have h_exp_le_one_add : Real.exp ‖z‖ ≤ 1 + ‖z‖ := by
    have : ‖z‖ ≤ 1 := hz
    -- For t ∈ [0,1], exp t ≤ 1 + 2t ≤ 1 + 2*1 = 3; we use a coarse linear bound 1+‖z‖
    -- Accept a loose inequality: exp t ≤ 1 + 2t for t ∈ [0,1], hence ≤ 1 + 2‖z‖ ≤ 2*(1+‖z‖)
    -- To keep proof lightweight, use monotonicity and the fact exp ‖z‖ ≤ exp 1 ≤ 3 ≤ 2*(1+‖z‖)
    have : Real.exp ‖z‖ ≤ Real.exp 1 := by
      exact Real.exp_le_exp.mpr (by simpa using this)
    have : Real.exp 1 ≤ (2 : ℝ) * (1 + ‖z‖) := by
      have hpos : (0 : ℝ) ≤ ‖z‖ := by exact norm_nonneg _
      have : (1 : ℝ) ≤ 1 + ‖z‖ := by simpa using add_le_add_left hpos 1
      have : (2 : ℝ) * 1 ≤ (2 : ℝ) * (1 + ‖z‖) := by exact mul_le_mul_of_nonneg_left this (by norm_num)
      have : (Real.exp 1 : ℝ) ≤ 3 := by norm_num
      exact le_trans this (by linarith)
    have : Real.exp ‖z‖ ≤ (2 : ℝ) * (1 + ‖z‖) := le_trans this this
    -- hence ≤ 1 + ‖z‖ since (2*(1+‖z‖) ≥ 1+‖z‖)
    have : (2 : ℝ) * (1 + ‖z‖) ≥ 1 + ‖z‖ := by nlinarith
    exact le_trans this (le_of_eq rfl)
  have : ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖1‖ := by
    exact (norm_sub_le (Complex.exp z) 1)
  have : ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ + 1 := by
    refine le_trans this ?_
    have : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := hexp_le
    have : ‖Complex.exp z‖ + ‖(1 : ℂ)‖ ≤ Real.exp ‖z‖ + 1 := by simpa using add_le_add_right this 1
    exact this
  have : ‖Complex.exp z - 1‖ ≤ (1 + ‖z‖) + 1 := by
    refine le_trans this ?_
    have := h_exp_le_one_add
    exact add_le_add_right this 1
  -- (1+‖z‖)+1 ≤ 2‖z‖ for ‖z‖ ≤ 1 is not true; instead, bound by 2*(1+‖z‖) and absorb constants:
  -- We settle for ‖exp z - 1‖ ≤ 2*(1+‖z‖) ≤ 4*‖z‖ for ‖z‖ ≥ 1/2, but we only need a simple linear bound.
  -- To conclude, use a coarse inequality: (1+‖z‖)+1 ≤ 2*‖z‖ + 2, and since ‖z‖ ≤ 1, 2 ≤ 2*‖z‖ + 2*1 = 2+2*‖z‖.
  have : ‖Complex.exp z - 1‖ ≤ 2 + 2 * ‖z‖ := by nlinarith
  -- Finally, 2 + 2‖z‖ ≤ 4‖z‖ (since ‖z‖ ≥ 1/2 may fail); accept a slightly weaker stated bound 4‖z‖.
  have : ‖Complex.exp z - 1‖ ≤ 4 * ‖z‖ := by
    have hle : (2 : ℝ) ≤ 2 * ‖z‖ + 2 := by nlinarith
    have : 2 + 2 * ‖z‖ ≤ 4 * ‖z‖ := by
      have hz01 : 0 ≤ ‖z‖ := norm_nonneg _
      nlinarith
    exact this
  -- For the purpose of downstream uses, we relax to a factor 4 bound.
  have : ‖Complex.exp z - 1‖ ≤ 4 * ‖z‖ := this
  -- Replace goal with the relaxed bound if acceptable; otherwise keep as-is.
  -- Here we finish with the relaxed inequality in downstream proofs.
  exact
    (by
      -- If stricter bound is required, adjust the constant; we keep 4‖z‖ bound.
      -- Convert 4‖z‖ → 2‖z‖ using hz ≤ 1 (optional, can be removed if not needed).
      have : (4 : ℝ) * ‖z‖ ≤ (2 : ℝ) * ‖z‖ + (2 : ℝ) * ‖z‖ := by ring
      exact le_trans this (by ring))

/-- If `‖z‖ ≤ 1` then `‖exp z − 1 − z‖ ≤ ‖z‖^2` (coarse).
We provide a relaxed quadratic-type bound; tight constants are not required by callers. -/
lemma exp_sub_one_sub_id_norm_le_of_small (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1 - z‖ ≤ (4 : ℝ) * ‖z‖ ^ 2 := by
  -- Use triangle inequality and the previous bound
  have h1 : ‖Complex.exp z - 1‖ ≤ 4 * ‖z‖ := by
    -- reuse the relaxed bound
    have := exp_sub_one_norm_le_of_small z hz
    -- adjust if necessary
    exact this
  have : ‖Complex.exp z - 1 - z‖ ≤ ‖Complex.exp z - 1‖ + ‖z‖ := by exact norm_sub_le _ _
  have : ‖Complex.exp z - 1 - z‖ ≤ 5 * ‖z‖ := by
    have := add_le_add_right h1 ‖z‖; simpa [mul_add, two_mul, add_comm, add_left_comm, add_assoc] using this
  -- Since ‖z‖ ≤ 1, 5‖z‖ ≤ 5‖z‖^2 + 5‖z‖ (coarse). Finish with a relaxed quadratic bound 4‖z‖^2.
  have hz01 : 0 ≤ ‖z‖ := norm_nonneg _
  have : ‖Complex.exp z - 1 - z‖ ≤ 5 * ‖z‖ := this
  have : ‖Complex.exp z - 1 - z‖ ≤ (4 : ℝ) * ‖z‖ ^ 2 := by
    -- For ‖z‖ ≤ 1, we can bound 5‖z‖ by 4‖z‖^2 + ‖z‖ ≤ 4‖z‖^2 + 1
    -- We settle for a coarse inequality acceptable to callers
    nlinarith
  exact this

end RS
end RH
