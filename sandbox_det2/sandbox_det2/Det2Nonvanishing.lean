import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Basic
import sandbox_det2.ExpBounds

noncomputable section

open Complex

namespace sandbox_det2

/-- Example: package a simple quadratic-exponential remainder bound for
`(1 - λ)·exp(λ + λ^2/2) - 1`. This mirrors the structure used in the main repo.
-/
lemma eulerFactor_remainder_quadratic_exp (λ : ℂ) :
    let w : ℂ := λ + λ ^ 2 / 2
    in ‖(1 - λ) * Complex.exp w - 1‖
       ≤ ((‖w‖ ^ 2) + ‖λ‖ * ‖w‖ + (‖λ‖ ^ 2) / 2) * Real.exp ‖w‖ := by
  classical
  intro w
  let E := Complex.exp w
  have hstart : ‖(1 - λ) * E - 1‖ = ‖E - 1 - λ * E‖ := by
    simp [mul_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hdecomp : E - 1 - λ * E = (E - 1 - w) + (w - λ) - λ * (E - 1) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    ring
  have htri1 : ‖(E - 1 - w) + (w - λ) - λ * (E - 1)‖
      ≤ ‖(E - 1 - w) + (w - λ)‖ + ‖λ * (E - 1)‖ := by
    simpa [sub_eq_add_neg] using Complex.norm_sub_le ((E - 1 - w) + (w - λ)) (λ * (E - 1))
  have htri2 : ‖(E - 1 - w) + (w - λ)‖ ≤ ‖E - 1 - w‖ + ‖w - λ‖ :=
    Complex.norm_add_le _ _
  have hmul : ‖λ * (E - 1)‖ = ‖λ‖ * ‖E - 1‖ := by simpa using Complex.norm_mul λ (E - 1)
  have hsum : ‖E - 1 - λ * E‖
      ≤ ‖E - 1 - w‖ + ‖w - λ‖ + ‖λ‖ * ‖E - 1‖ := by
    have := le_trans htri1 (add_le_add_right htri2 _)
    simpa [hmul, add_comm, add_left_comm, add_assoc, hdecomp]
      using this
  have h1 : ‖E - 1 - w‖ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by
    simpa [E] using sandbox_det2.norm_exp_sub_one_sub_id_le w
  have h2 : ‖E - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
    simpa [E] using sandbox_det2.norm_exp_sub_one_le_norm_mul_exp_norm w
  have hwλ : w - λ = λ ^ 2 / 2 := by
    simp [w, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have h3 : ‖w - λ‖ = ‖λ‖ ^ 2 / 2 := by
    have : ‖λ ^ 2 / (2 : ℂ)‖ = ‖λ‖ ^ 2 / 2 := by
      simp [Complex.norm_div, Complex.norm_pow, Complex.norm_ofReal]
    simpa [hwλ]
  have h3' : ‖w - λ‖ ≤ (‖λ‖ ^ 2 / 2) * Real.exp ‖w‖ := by
    have := mul_le_mul_of_nonneg_right (le_of_eq h3) (by positivity : 0 ≤ Real.exp ‖w‖)
    simpa [mul_comm] using this
  have hsum' := add_le_add (add_le_add h1 h3') (mul_le_mul_of_nonneg_left h2 (by positivity))
  simpa [hstart, mul_add, add_comm, add_left_comm, add_assoc]
    using hsum'

end sandbox_det2
