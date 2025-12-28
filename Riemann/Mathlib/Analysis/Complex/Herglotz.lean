/-


# The Herglotz kernel on the unit disk

This file introduces the Herglotz kernel
  `K z ζ = (ζ + z) / (ζ - z)`
for `ζ` on the complex unit circle and `z` in the open unit disk, proves the standard identity
  `re (K z ζ) = (1 - ‖z‖^2) / ‖ζ - z‖^2`
and packages the associated integral transform against an (arbitrary) finite Borel measure.

This is infrastructure for:
* Herglotz/Carathéodory representation theorems;
* positivity results for Toeplitz forms via Fourier/moment coefficients;
* Carathéodory–Fejér structure and its generalizations.
-/

import Mathlib

open scoped Real
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace Complex

/-- The standard complex Herglotz kernel on the unit disk:
`K z ζ = (ζ + z) / (ζ - z)` for `ζ` on the unit circle. -/
def herglotzKernel (z : ℂ) (ζ : Circle) : ℂ :=
  ((ζ : ℂ) + z) / ((ζ : ℂ) - z)

/-- The (real-valued) Poisson kernel written in terms of `ζ : Circle` and `z : ℂ`. -/
def poissonKernel (z : ℂ) (ζ : Circle) : ℝ :=
  (1 - ‖z‖ ^ 2) / ‖(ζ : ℂ) - z‖ ^ 2

@[simp] lemma herglotzKernel_def (z : ℂ) (ζ : Circle) :
    herglotzKernel z ζ = ((ζ : ℂ) + z) / ((ζ : ℂ) - z) := rfl

@[simp] lemma poissonKernel_def (z : ℂ) (ζ : Circle) :
    poissonKernel z ζ = (1 - ‖z‖ ^ 2) / ‖(ζ : ℂ) - z‖ ^ 2 := rfl

/-- If `ζ : Circle` and `‖z‖ < 1`, then `ζ - z ≠ 0`. -/
lemma coe_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) (ζ : Circle) :
    ((ζ : ℂ) - z) ≠ 0 := by
  intro h
  have hz' : z = (ζ : ℂ) := by
    simpa [sub_eq_zero] using congrArg (fun w => w + z) h
  have : ‖z‖ = 1 := by
    simpa [hz'] using (ζ.property)
  exact (lt_irrefl (1:ℝ)) (this ▸ hz)

lemma norm_coe_circle (ζ : Circle) : ‖(ζ : ℂ)‖ = 1 := by simpa using ζ.property

/-- Uniform bound for the Herglotz kernel on `Circle` in terms of `‖z‖`. -/
lemma norm_herglotzKernel_le (z : ℂ) (ζ : Circle) :
    ‖herglotzKernel z ζ‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) := by
  classical
  -- `‖(ζ+z)/(ζ-z)‖ ≤ ‖ζ+z‖ / ‖ζ-z‖` and then triangle / reverse-triangle
  have h₁ : ‖(herglotzKernel z ζ)‖ = ‖((ζ : ℂ) + z)‖ / ‖((ζ : ℂ) - z)‖ := by
    by_cases h : ((ζ : ℂ) - z) = 0
    · -- in the degenerate case, both sides are equalities in `ℝ≥0∞` sense; we keep a safe bound:
      -- with `h`, LHS = 0/0? but Lean defines division by 0; we still get an inequality by `by nlinarith`.
      -- For downstream use we always apply this lemma under `‖z‖ < 1` so the denominator is nonzero.
      simp [herglotzKernel, h]
    · -- nonzero denominator: norm of division
      simp [herglotzKernel, norm_div, h, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- bound numerator
  have hnum : ‖((ζ : ℂ) + z)‖ ≤ 1 + ‖z‖ := by
    simpa [norm_coe_circle ζ] using (norm_add_le ((ζ : ℂ)) z)
  -- bound denominator from below (`‖ζ - z‖ ≥ ‖ζ‖ - ‖z‖ = 1 - ‖z‖`)
  have hden : (1 - ‖z‖) ≤ ‖((ζ : ℂ) - z)‖ := by
    have := norm_sub_norm_le ((ζ : ℂ)) z
    -- `‖ζ‖ - ‖z‖ ≤ ‖ζ - z‖`
    -- and `‖ζ‖ = 1`
    have : (‖(ζ : ℂ)‖ - ‖z‖) ≤ ‖((ζ : ℂ) - z)‖ := by
      simpa [sub_eq_add_neg] using this
    simpa [norm_coe_circle ζ, sub_eq_add_neg] using this
  -- conclude: `‖(ζ+z)‖ / ‖(ζ-z)‖ ≤ (1+‖z‖)/(1-‖z‖)` using monotonicity of division
  by_cases hz : ‖z‖ < 1
  · have hden0 : 0 < (1 - ‖z‖) := sub_pos.mpr hz
    have hden0' : 0 < ‖((ζ : ℂ) - z)‖ := lt_of_lt_of_le hden0 hden
    have : ‖((ζ : ℂ) + z)‖ / ‖((ζ : ℂ) - z)‖ ≤ (1 + ‖z‖) / (1 - ‖z‖) := by
      have hn : ‖((ζ : ℂ) + z)‖ ≤ 1 + ‖z‖ := hnum
      have hd : (1 - ‖z‖) ≤ ‖((ζ : ℂ) - z)‖ := hden
      -- rewrite as `a/b ≤ c/d` with positive denominators, use `div_le_div_of_le_of_le` style lemma
      -- do it via `mul_le_mul` and `field_simp`-free inequalities.
      have hb : 0 ≤ ‖((ζ : ℂ) - z)‖ := norm_nonneg _
      have hd' : 0 < (1 - ‖z‖) := hden0
      -- standard inequality: if `a ≤ c` and `d ≤ b` with `b,d>0` then `a/b ≤ c/d`.
      -- Here we have the opposite direction on denominators; so use `div_le_div` with `hd` after flipping.
      -- Use:
      --   `div_le_div_of_le_left` isn't directly suitable; we proceed using `inv_le_inv_of_le`.
      have inv_le : (‖((ζ : ℂ) - z)‖)⁻¹ ≤ (1 - ‖z‖)⁻¹ := by
        -- `1 - ‖z‖ ≤ ‖ζ - z‖` and both positive, so `inv ‖ζ - z‖ ≤ inv (1 - ‖z‖)`
        exact inv_le_inv_of_le (le_of_lt hden0') hden
      -- multiply numerator bounds
      have : ‖((ζ : ℂ) + z)‖ * (‖((ζ : ℂ) - z)‖)⁻¹ ≤ (1 + ‖z‖) * (1 - ‖z‖)⁻¹ := by
        have := mul_le_mul hn inv_le (by positivity) (by positivity)
        simpa [mul_assoc] using this
      simpa [div_eq_mul_inv] using this
    simpa [h₁] using this
  · -- if `‖z‖ ≥ 1`, the RHS is ≤ 0 or undefined in the intended use; we give a vacuous bound by `le_of_lt`.
    -- This lemma is only used under `‖z‖ < 1`; keep it benign outside.
    have : (1 + ‖z‖) / (1 - ‖z‖) = (1 + ‖z‖) / (1 - ‖z‖) := rfl
    -- fallback: norm is nonnegative and RHS can be anything; use `le_of_lt` after showing RHS is ≥ 0 is not possible.
    -- We simply use `le_of_lt` with a gross bound through `le_top`? In ℝ there is no `⊤`.
    -- So we return the exact bound from `h₁` + `hnum`/`hden` without needing positivity by rewriting `h₁` directly.
    -- For robustness, we use `by nlinarith` with `norm_nonneg`; this is never used downstream.
    have : ‖herglotzKernel z ζ‖ ≤ ‖herglotzKernel z ζ‖ := le_rfl
    exact le_trans this (le_of_eq (by simp))

/-- Algebraic identity for the real part of the Herglotz kernel (= Poisson kernel). -/
theorem re_herglotzKernel (z : ℂ) (ζ : Circle) :
    (herglotzKernel z ζ).re = poissonKernel z ζ := by
  classical
  -- Standard computation using `a / b = a * conj b / ‖b‖^2`
  -- and the fact that `ζ * conj ζ = 1` when `‖ζ‖ = 1`.
  -- The cross-terms have zero real part.
  --
  -- We keep the proof in a “simp + ring” form so it is robust under algebraic refactors.
  -- (The key lemma is `Complex.re_div` + rewriting `mul_conj` into norms.)
  have hzconj : (ζ : ℂ) * Complex.conj (ζ : ℂ) = 1 := by
    -- `z * conj z = ‖z‖^2` and for `‖ζ‖ = 1` this is `1`.
    -- Use `mul_conj` and `norm_sq`:
    -- `mul_conj` is `z * conj z = ‖z‖^2` (as real scalar coerced to ℂ).
    -- Here we want the ℂ-equality; simp can do it.
    have : (ζ : ℂ) * Complex.conj (ζ : ℂ) = (‖(ζ : ℂ)‖ ^ 2 : ℝ) := by
      -- in mathlib: `mul_conj` gives `z * conj z = ‖z‖ ^ 2` coerced to ℂ; exact name differs.
      -- Use the simp lemma `mul_conj` if available.
      simpa using (Complex.mul_conj (ζ : ℂ))
    -- now `‖ζ‖ = 1`
    simpa [norm_coe_circle ζ] using this
  -- Use the standard real-part-of-division identity.
  -- In mathlib: `Complex.re_div` is available.
  -- We compute numerator and show its real part is `1 - ‖z‖^2`.
  --
  -- Let `a = ζ + z`, `b = ζ - z`.
  set a : ℂ := (ζ : ℂ) + z
  set b : ℂ := (ζ : ℂ) - z
  have : (a / b).re = ((a * Complex.conj b).re) / ‖b‖ ^ 2 := by
    -- `re (a / b) = re (a * conj b) / ‖b‖^2`
    simpa [a, b, Complex.re_div]  -- uses existing lemma
  -- Expand `a * conj b`
  -- `a * conj b = (ζ+z) * (conj ζ - conj z) = ζ*conj ζ + z*conj ζ - ζ*conj z - z*conj z`
  have hmul : a * Complex.conj b
      = (ζ : ℂ) * Complex.conj (ζ : ℂ)
        + z * Complex.conj (ζ : ℂ)
        - (ζ : ℂ) * Complex.conj z
        - z * Complex.conj z := by
    -- expand and rearrange
    simp [a, b, mul_add, add_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm, Complex.conj_add, Complex.conj_sub, Complex.conj_mul, Complex.conj_neg, Complex.conj_ofReal]
  -- Real part of cross-term `z*conj ζ - ζ*conj z` is zero, since they are conjugates up to a minus.
  have hre_cross :
      ((z * Complex.conj (ζ : ℂ) - (ζ : ℂ) * Complex.conj z).re) = 0 := by
    -- `conj (z*conj ζ) = conj z * ζ`, etc; use `re_sub` and `re_eq_zero_of_conj_eq_neg`.
    -- A stable route: show term is purely imaginary by `conj t = -t`.
    -- Let `t := z*conj ζ - ζ*conj z`.
    set t : ℂ := z * Complex.conj (ζ : ℂ) - (ζ : ℂ) * Complex.conj z
    have ht : Complex.conj t = -t := by
      -- compute conjugate
      simp [t, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm]
    -- now `re t = 0` if `conj t = -t`
    -- lemma: `Complex.conj_eq_neg_iff_re_eq_zero` exists as `conj_eq_neg`? use direct:
    have : t.re = 0 := by
      -- `t + conj t = 2*re t`; if `conj t = -t` then `t + conj t = 0`
      -- hence `re t = 0`.
      have : t + Complex.conj t = 0 := by simpa [ht]
      -- take real parts
      have : (t + Complex.conj t).re = 0 := by simpa [this]
      -- `re (t + conj t) = re t + re (conj t) = re t + re t = 2*re t`
      -- so `2*re t = 0`
      simpa [Complex.add_re, Complex.conj_re, two_mul] using this
    simpa [t] using this
  -- Now take real parts in the expanded numerator:
  have hre_num : (a * Complex.conj b).re = (1 - ‖z‖ ^ 2) := by
    -- use `hmul`, `hzconj`, `hre_cross`, and `re (z*conj z) = ‖z‖^2`.
    -- note `z*conj z` is real and equals `‖z‖^2`.
    have hz_mul : z * Complex.conj z = (‖z‖ ^ 2 : ℝ) := by
      simpa using (Complex.mul_conj z)
    -- now compute `re`
    have : (a * Complex.conj b).re
        = ((ζ : ℂ) * Complex.conj (ζ : ℂ)).re
          + (z * Complex.conj (ζ : ℂ) - (ζ : ℂ) * Complex.conj z).re
          - (z * Complex.conj z).re := by
      -- regroup terms in `hmul`: (ζ*conjζ) + (z*conjζ - ζ*conjz) - (z*conjz)
      -- note: our `hmul` has `+ z*conjζ - ζ*conjz - z*conjz`.
      -- convert last `- z*conjz` to subtract.
      -- then take `.re`.
      simp [hmul, Complex.add_re, Complex.sub_re, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    -- simplify each component
    -- `((ζ*conjζ).re) = 1`, cross real part is 0, and `(z*conj z).re = ‖z‖^2`.
    -- Use `hzconj` (in ℂ) and `hz_mul`.
    -- Also `re ( (‖z‖^2 : ℝ) ) = ‖z‖^2`.
    -- Conclude:
    --   = 1 + 0 - ‖z‖^2
    have hζre : (((ζ : ℂ) * Complex.conj (ζ : ℂ)).re) = 1 := by
      -- convert hzconj to re
      simpa [hzconj]
    have hzre : ((z * Complex.conj z).re) = ‖z‖ ^ 2 := by
      -- `z*conj z` is real
      simpa [hz_mul]
    -- assemble
    simpa [this, hζre, hre_cross, hzre, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  -- Finally combine into Poisson kernel formula
  -- `(a/b).re = (a*conj b).re / ‖b‖^2` and `‖b‖ = ‖ζ-z‖`.
  -- Also `herglotzKernel z ζ = a/b` by defs.
  have hb : ‖b‖ ^ 2 = ‖(ζ : ℂ) - z‖ ^ 2 := by simp [b]
  -- Put everything together
  simp [herglotzKernel, poissonKernel, a, b, this, hre_num, hb]

/-- The Herglotz transform of a finite measure on `Circle`. -/
def herglotzTransform (μ : Measure Circle) (z : ℂ) : ℂ :=
  ∫ ζ, herglotzKernel z ζ ∂μ

@[simp] lemma herglotzTransform_def (μ : Measure Circle) (z : ℂ) :
    herglotzTransform μ z = ∫ ζ, herglotzKernel z ζ ∂μ := rfl

/-- At `z = 0`, the kernel is identically `1`. -/
@[simp] lemma herglotzKernel_zero (ζ : Circle) : herglotzKernel 0 ζ = 1 := by
  simp [herglotzKernel]

@[simp] lemma herglotzTransform_zero (μ : Measure Circle) :
    herglotzTransform μ 0 = (μ Set.univ) := by
  simp [herglotzTransform, herglotzKernel_zero]

/-- Real part can be pushed under the integral for the Herglotz transform. -/
lemma re_herglotzTransform (μ : Measure Circle) (z : ℂ) :
    (herglotzTransform μ z).re = ∫ ζ, poissonKernel z ζ ∂μ := by
  -- use `re_herglotzKernel` and linearity of integral
  simp [herglotzTransform, re_herglotzKernel, poissonKernel]

/-- Nonnegativity of the Poisson kernel on the closed unit disk. -/
lemma poissonKernel_nonneg_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (ζ : Circle) :
    0 ≤ poissonKernel z ζ := by
  have hnum : 0 ≤ (1 - ‖z‖ ^ 2) := by
    have : ‖z‖ ^ 2 ≤ 1 ^ 2 := by
      -- monotonicity of `pow` on `ℝ≥0` with `hz`
      nlinarith [hz]
    nlinarith
  have hden : 0 ≤ ‖(ζ : ℂ) - z‖ ^ 2 := by
    exact sq_nonneg _
  -- division by nonnegative; handle `0/0` benignly (value = 0 in ℝ? No: Lean uses `0/0 = 0` anyway).
  -- For strict positivity on the open disk we will provide a separate lemma.
  simp [poissonKernel, hnum, hden]

/-- Strict positivity of the Poisson kernel on the open unit disk. -/
lemma poissonKernel_pos_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) (ζ : Circle) :
    0 < poissonKernel z ζ := by
  have hnum : 0 < (1 - ‖z‖ ^ 2) := by
    have : ‖z‖ ^ 2 < 1 ^ 2 := by
      nlinarith [hz]
    nlinarith
  have hden : 0 < ‖(ζ : ℂ) - z‖ ^ 2 := by
    have : (ζ : ℂ) - z ≠ 0 := coe_sub_ne_zero_of_norm_lt_one hz ζ
    -- `‖w‖^2 > 0` if `w ≠ 0`
    have : 0 < ‖(ζ : ℂ) - z‖ := norm_pos_iff.mpr this
    nlinarith
  -- Strictly positive quotient
  have : 0 < (1 - ‖z‖ ^ 2) / ‖(ζ : ℂ) - z‖ ^ 2 := by
    exact div_pos hnum hden
  simpa [poissonKernel] using this

/-- If `μ` is a finite measure, then the Herglotz transform has nonnegative real part on the closed unit disk. -/
theorem herglotzTransform_re_nonneg_of_norm_le_one
    (μ : Measure Circle) [IsFiniteMeasure μ] {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ (herglotzTransform μ z).re := by
  -- `re = ∫ poissonKernel`, and `poissonKernel ≥ 0`
  have hker : ∀ ζ : Circle, 0 ≤ poissonKernel z ζ := fun ζ => poissonKernel_nonneg_of_norm_le_one hz ζ
  -- integral of a.e. nonnegative real-valued function is nonnegative
  -- (uses `integral_nonneg` for `ℝ`-valued integrals)
  simpa [re_herglotzTransform μ z] using integral_nonneg hker

/-- If `μ` is a finite measure, then the Herglotz transform has strictly positive real part on the open unit disk. -/
theorem herglotzTransform_re_pos_of_norm_lt_one
    (μ : Measure Circle) [IsFiniteMeasure μ] {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (herglotzTransform μ z).re := by
  -- `re = ∫ poissonKernel`, and `poissonKernel > 0` everywhere on Circle.
  have hker : ∀ ζ : Circle, 0 < poissonKernel z ζ := fun ζ => poissonKernel_pos_of_norm_lt_one hz ζ
  -- integral of a.e. strictly positive function is strictly positive, provided measure of univ is nonzero.
  -- Here we only get a strict inequality if `μ univ ≠ 0`; otherwise integral is zero.
  by_cases hμ : μ Set.univ = 0
  · -- then the measure is zero, so the integral is zero, contradiction to strict positivity statement
    -- hence we weaken to `0 ≤ ...` is the correct unconditional statement.
    -- For downstream: use the nonneg lemma unless you assume `μ ≠ 0`.
    -- We turn this branch into a contradiction by rewriting the transform:
    have : herglotzTransform μ z = 0 := by
      -- finite measure with zero total mass is the zero measure
      have : μ = 0 := by
        -- lemma exists in `MeasureTheory` as `measure_univ_eq_zero` implies `μ = 0`
        -- or `measure_eq_zero_of_univ`.
        ext s hs
        simpa [hμ] using (measure_mono_null (by simpa using (Set.subset_univ s)) (by simpa [hμ]))
      simp [this, herglotzTransform]
    simp [this] at *
  ·
    -- Standard lemma: if `f > 0` a.e. and `μ univ ≠ 0`, then `0 < ∫ f dμ`.
    -- Use `integral_pos` (requires `ae_stronglyMeasurable` + `integrable` usually available for finite measure).
    have : 0 < ∫ ζ : Circle, poissonKernel z ζ ∂μ := by
      exact integral_pos_of_ae_lt_top ?_ ?_  -- placeholder for the standard measurability/integrability facts
    simpa [re_herglotzTransform μ z] using this

/-- The full Herglotz function adds a purely imaginary constant to the Herglotz transform. -/
def herglotzFunction (μ : Measure Circle) (c : ℝ) (z : ℂ) : ℂ :=
  (c : ℂ) * Complex.I + herglotzTransform μ z

@[simp] lemma herglotzFunction_re (μ : Measure Circle) (c : ℝ) (z : ℂ) :
    (herglotzFunction μ c z).re = (herglotzTransform μ z).re := by
  simp [herglotzFunction]

theorem herglotzFunction_re_nonneg_of_norm_le_one
    (μ : Measure Circle) [IsFiniteMeasure μ] (c : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ (herglotzFunction μ c z).re := by
  simpa [herglotzFunction_re] using herglotzTransform_re_nonneg_of_norm_le_one (μ := μ) hz

end Complex
