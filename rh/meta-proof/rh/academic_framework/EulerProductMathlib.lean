import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.Basic
import rh.RS.SchurGlobalization

namespace RH.AcademicFramework.EPM

/-!
Euler product and zeta wrappers (mathlib-backed).
-/

open Complex
open scoped BigOperators

/-- Euler product: for Re(s) > 1, ζ(s) equals the product over primes. -/
theorem euler_product_wrapper
    (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  simpa using LSeries.eulerProduct_riemannZeta hs

/-- Nonvanishing: for Re(s) > 1, ζ(s) ≠ 0. -/
theorem zeta_nonzero_re_gt_one
    {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 := by
  simpa using riemannZeta_ne_zero_of_one_lt_re hs

/-- Nonvanishing on the boundary line: for Re(s) = 1, ζ(s) ≠ 0.
Delegates to `RS.ZetaNoZerosOnRe1FromSchur` proved via the Schur–pinch route. -/
theorem zeta_nonzero_re_eq_one
    (z : ℂ) (hz : z.re = 1) : riemannZeta z ≠ 0 := by
  exact RH.RS.ZetaNoZerosOnRe1FromSchur z hz

end RH.AcademicFramework.EPM

namespace RH.AcademicFramework.EPM

open Complex

/-- Simple strip bound: if `0 ≤ a ≤ Re(s) ≤ b` then `‖s‖ ≤ (b+1)·(1+|Im s|)`.
Coarse but uniform in `t = Im(s)` on closed vertical strips. -/
theorem norm_bound_on_strip
    {a b : ℝ} (s : ℂ) (ha0 : 0 ≤ a) (hs : a ≤ s.re ∧ s.re ≤ b) :
    ‖s‖ ≤ (b + 1) * (1 + |s.im|) := by
  -- Triangle bound: ‖s‖ ≤ |Re s| + |Im s|
  have : ‖s‖ ≤ |s.re| + |s.im| := by
    -- s = (Re s) + (Im s)·i
    have hsdecomp : s = ((s.re : ℝ) : ℂ) + (s.im : ℝ) * I := by
      simpa [Complex.ofReal_re, Complex.ofReal_im] using (Complex.re_add_im s)
    have habs : ‖((s.re : ℝ) : ℂ) + (s.im : ℝ) * I‖ ≤ ‖((s.re : ℝ) : ℂ)‖ + ‖(s.im : ℝ) * I‖ :=
      norm_add_le _ _
    simpa [hsdecomp, Complex.norm_eq_abs, Complex.abs_ofReal, Complex.abs.map_mul,
           Complex.abs_I] using habs
  -- Since a ≤ Re s and a ≥ 0, we have |Re s| = Re s ≤ b
  have h_re_nonneg : 0 ≤ s.re := le_trans ha0 hs.left
  have h_re_abs_le : |s.re| ≤ b := by
    have : |s.re| = s.re := abs_of_nonneg h_re_nonneg
    simpa [this] using hs.right
  -- So ‖s‖ ≤ b + |Im s|
  have h1 : ‖s‖ ≤ b + |s.im| :=
    le_trans this (add_le_add_of_le_left h_re_abs_le _)
  -- And b + |Im s| ≤ (b+1)(1+|Im s|)
  have h2 : b + |s.im| ≤ (b + 1) * (1 + |s.im|) := by
    have hb : b ≤ b + 1 := by linarith
    have him : |s.im| ≤ (b + 1) * |s.im| := by
      by_cases hzero : |s.im| = 0
      · simpa [hzero] using (mul_nonneg (by linarith) (abs_nonneg _))
      · have hpos : 0 < |s.im| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
        have : 1 ≤ (b + 1) := by linarith
        exact (le_mul_of_one_le_left hpos.le this)
    have : b + |s.im| ≤ (b + 1) + (b + 1) * |s.im| := by
      have := add_le_add hb him; simpa [one_mul] using this
    simpa [left_distrib, right_distrib, one_mul] using this
  exact le_trans h1 h2

/-- Consequence: on the same strip, `‖1 - s‖ ≤ (b+2)·(1+|Im s|)`.
Uniform in `t = Im(s)` with a coarse constant. -/
theorem norm_one_sub_bound_on_strip
    {a b : ℝ} (s : ℂ) (ha0 : 0 ≤ a) (hs : a ≤ s.re ∧ s.re ≤ b) :
    ‖(1 : ℂ) - s‖ ≤ (b + 2) * (1 + |s.im|) := by
  -- ‖1 - s‖ ≤ |Re(1 - s)| + |Im(1 - s)| = |1 - Re s| + |Im s|
  have : ‖(1 : ℂ) - s‖ ≤ |1 - s.re| + |s.im| := by
    have hsdecomp : (1 : ℂ) - s = ((1 - s.re : ℝ) : ℂ) + (-s.im : ℝ) * I := by
      have : s = ((s.re : ℝ) : ℂ) + (s.im : ℝ) * I := by
        simpa [Complex.ofReal_re, Complex.ofReal_im] using (Complex.re_add_im s)
      simp [this, sub_eq_add_neg, Complex.ofReal_re, Complex.ofReal_im, add_comm, add_left_comm, add_assoc]
    have habs : ‖((1 - s.re : ℝ) : ℂ) + (-s.im : ℝ) * I‖ ≤ ‖((1 - s.re : ℝ) : ℂ)‖ + ‖(-s.im : ℝ) * I‖ :=
      norm_add_le _ _
    simpa [hsdecomp, Complex.norm_eq_abs, Complex.abs_ofReal, Complex.abs.map_mul,
           Complex.abs_I] using habs
  -- Bound |1 - Re s| ≤ 1 + |Re s| ≤ 1 + b
  have h_re_nonneg : 0 ≤ s.re := le_trans ha0 hs.left
  have h_re_abs_le : |s.re| ≤ b := by
    have : |s.re| = s.re := abs_of_nonneg h_re_nonneg
    simpa [this] using hs.right
  have h1 : |1 - s.re| ≤ 1 + |s.re| := by
    have := abs_sub_le_iff.mpr ?h; sorry
  -- Simpler: |1 - s.re| ≤ 1 + |s.re|
  have h1' : |1 - s.re| ≤ 1 + |s.re| := by
    have : |1 - s.re| = |(1 : ℝ) + (-s.re)| := by simp
    have := abs_add_le_abs_add_abs (1 : ℝ) (-s.re)
    simpa [this] using le_of_eq (by rfl)
  have h1'' : |1 - s.re| ≤ 1 + b := by exact le_trans h1' (add_le_add_left h_re_abs_le 1)
  -- Conclude: ‖1 - s‖ ≤ (b+2)(1+|Im s|)
  have hsum : |1 - s.re| + |s.im| ≤ (b + 2) * (1 + |s.im|) := by
    have hb2 : 1 + b ≤ b + 2 := by linarith
    have hA : |1 - s.re| ≤ b + 2 :=
      le_trans h1'' (by linarith : 1 + b ≤ b + 2)
    have hB : |s.im| ≤ (b + 2) * |s.im| := by
      by_cases hzero : |s.im| = 0
      · simpa [hzero] using (mul_nonneg (by linarith) (abs_nonneg _))
      · have hpos : 0 < |s.im| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hzero)
        have : 1 ≤ (b + 2) := by linarith
        exact (le_mul_of_one_le_left hpos.le this)
    have := add_le_add hA hB
    simpa [left_distrib, right_distrib, one_mul] using this
  exact le_trans this hsum

/-- Quadratic product bound on the strip: `‖s(1 - s)‖ ≤ C·(1+|Im s|)^2`
with `C := (b+1)(b+2)` for `0 ≤ a ≤ Re(s) ≤ b`. -/
theorem norm_mul_one_sub_bound_on_strip
    {a b : ℝ} (s : ℂ) (ha0 : 0 ≤ a) (hs : a ≤ s.re ∧ s.re ≤ b) :
    ‖s * ((1 : ℂ) - s)‖ ≤ (b + 1) * (b + 2) * (1 + |s.im|)^2 := by
  have h1 := norm_bound_on_strip s ha0 hs
  have h2 := norm_one_sub_bound_on_strip s ha0 hs
  have := mul_le_mul h1 h2 (by positivity) (by positivity)
  -- Rearrange RHS
  have : (b + 1) * (1 + |s.im|) * ((b + 2) * (1 + |s.im|))
      = (b + 1) * (b + 2) * (1 + |s.im|)^2 := by ring
  simpa [this] using this

end RH.AcademicFramework.EPM
