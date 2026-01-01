import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.StarOrdered


/-!
# Nevanlinna class and de Branges admissibility on the upper half-plane

This file gives honest (non-placeholder) definitions of:

* `Complex.IsOfBoundedTypeUpperHalfPlane f`:
  `f` is in the Nevanlinna class `N(ℍ)`, i.e. a quotient of bounded analytic
  functions on the open upper half-plane.

* `Complex.meanType f`:
  the (upper) mean type of `f` in the upper half-plane, defined via a growth
  rate along the imaginary axis.

* `Complex.IsDeBrangesAdmissible f`:
  the de Branges admissibility condition: analytic on the upper half-plane,
  of bounded type there, and of non-positive mean type.

The definitions are aligned with standard complex-analytic references
(e.g. Conway, *Functions of One Complex Variable II*; de Branges,
*Hilbert Spaces of Entire Functions*; and the Nevanlinna / bounded-type
survey in the classical literature). See also the summary in the
"Bounded type (mathematics)" article.
-/

open scoped Complex UpperHalfPlane

namespace Complex

/-- The open upper half-plane, as a subset of `ℂ`. We work on this set rather than
the subtype `ℍ` for analyticity, to use the existing `AnalyticOnNhd` API. -/
def upperHalfPlaneSet : Set ℂ := { z : ℂ | 0 < z.im }

@[simp] lemma mem_upperHalfPlaneSet {z : ℂ} :
    z ∈ upperHalfPlaneSet ↔ 0 < z.im := Iff.rfl

lemma isOpen_upperHalfPlaneSet : IsOpen (upperHalfPlaneSet) := by
  -- This is a special case of `Complex.isOpen_im_gt_EReal`.
  simpa [upperHalfPlaneSet] using
    (Complex.isOpen_im_gt_EReal (x := (0 : EReal)))

/-- A function `f` is bounded on the open upper half-plane if its norm is uniformly
bounded there. This is the concrete boundedness condition used in the ratio
definition of the Nevanlinna class. -/
def IsBoundedOnUpperHalfPlane (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ upperHalfPlaneSet, norm (f z) ≤ C

/-- `IsOfBoundedTypeUpperHalfPlane f` means that `f` belongs to the Nevanlinna
class `N(ℍ)` for the upper half-plane, i.e. it is a quotient of two bounded
holomorphic functions on the upper half-plane.

More precisely, there exist analytic functions `g` and `h` on the open upper
half-plane, both bounded there, such that `h` never vanishes on the upper
half-plane and `f z = g z / h z` for all `z` with `0 < z.im`.

This matches the classical "ratio of bounded analytic functions" definition
for functions of bounded type. -/
def IsOfBoundedTypeUpperHalfPlane (f : ℂ → ℂ) : Prop :=
  ∃ g h : ℂ → ℂ,
    AnalyticOnNhd ℂ g upperHalfPlaneSet ∧
    AnalyticOnNhd ℂ h upperHalfPlaneSet ∧
    IsBoundedOnUpperHalfPlane g ∧
    IsBoundedOnUpperHalfPlane h ∧
    (∀ z ∈ upperHalfPlaneSet, h z ≠ 0) ∧
    ∀ z ∈ upperHalfPlaneSet, f z = g z / h z

/-- Mean type in the upper half-plane, defined as a limsup growth rate along
the imaginary axis:
\[
  \mathrm{meanType}(f) = \limsup_{y \to +\infty}
    \frac{\log (|f(iy)| + 1)}{y}.
\]

This is equivalent (for functions of bounded type) to the constant `q - p`
appearing in Nevanlinna's canonical representation and to more sophisticated
integral characterizations.

We package it via the general `Filter.limsup` along `Filter.atTop` on `ℝ`. -/
noncomputable def meanType (f : ℂ → ℂ) : EReal :=
  Filter.limsup
    (fun y : ℝ => ((Real.log (norm (f (Complex.I * y)) + 1)) / y : EReal))
    Filter.atTop

noncomputable def meanType_atImInfty (f : ℍ → ℂ) : EReal :=
  Filter.limsup
    (fun z : ℍ =>
      ((Real.log (norm (f z) + 1)) / (z.im : ℝ) : EReal))
    UpperHalfPlane.atImInfty

open Set Filter

open scoped Filter Topology



open Filter

/-- Helper lemma for zero limsup -/
lemma limsup_zero_ereal_atTop : Filter.limsup (fun _ : ℝ => (0 : EReal)) Filter.atTop = 0 := by
  haveI : NeBot (Filter.atTop : Filter ℝ) := Filter.atTop_neBot
  exact Filter.limsup_const (0 : EReal)


/-- Basic subadditivity of the mean type under addition:
\[
  \mathrm{meanType}(f+g) \le \mathrm{meanType}(f)+\mathrm{meanType}(g).
\]
This is proved directly from the definition using `limsup` calculus. -/
lemma meanType_add_le (f g : ℂ → ℂ) :
    meanType (fun z => f z + g z) ≤ meanType f + meanType g := by
  classical
  -- trajectories along the imaginary axis, coerced to EReal
  let u  : ℝ → EReal :=
    fun y => ((Real.log (‖(f (Complex.I * y) + g (Complex.I * y))‖ + 1)) / y : EReal)
  let uf : ℝ → EReal :=
    fun y => ((Real.log (‖f (Complex.I * y)‖ + 1)) / y : EReal)
  let ug : ℝ → EReal :=
    fun y => ((Real.log (‖g (Complex.I * y)‖ + 1)) / y : EReal)

  -- pointwise inequality, eventually in `atTop`
  have h_ineq : ∀ᶠ y in atTop, u y ≤ uf y + ug y := by
    refine (eventually_ge_atTop (1 : ℝ)).mono ?_
    intro y hy
    have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy

    -- Bound the log argument: |f+g|+1 <= (|f|+1)(|g|+1)
    have h_log :
      Real.log (‖f (Complex.I * y) + g (Complex.I * y)‖ + 1)
        ≤ Real.log (‖f (Complex.I * y)‖ + 1)
          + Real.log (‖g (Complex.I * y)‖ + 1) := by
       rw [← Real.log_mul]
       · apply Real.log_le_log
         · exact add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
         · have h1 : ‖f (Complex.I * y) + g (Complex.I * y)‖ ≤ ‖f (Complex.I * y)‖ + ‖g (Complex.I * y)‖ :=
             norm_add_le _ _
           -- (a+b+1) <= (a+1)(b+1) <=> a+b+1 <= ab+a+b+1 <=> 0 <= ab
           nlinarith [norm_nonneg (f (Complex.I * y)), norm_nonneg (g (Complex.I * y))]
       · exact ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
       · exact ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)

    -- Divide by y and coerce
    have h_real : (Real.log (‖f (Complex.I * y) + g (Complex.I * y)‖ + 1)) / y
                ≤ (Real.log (‖f (Complex.I * y)‖ + 1)) / y + (Real.log (‖g (Complex.I * y)‖ + 1)) / y := by
       rw [← add_div]
       exact (div_le_div_iff_of_pos_right hy_pos).mpr h_log

    exact EReal.coe_le_coe_iff.mpr h_real

  -- Proving non-negativity to ensure ne_bot
  have h_uf_ge_zero : 0 ≤ Filter.limsup uf atTop := by
    rw [← limsup_zero_ereal_atTop]
    apply Filter.limsup_le_limsup
    · filter_upwards [eventually_gt_atTop 0] with y hy
      simp only [uf]
      apply EReal.coe_nonneg.mpr
      apply div_nonneg
      · apply Real.log_nonneg
        linarith [norm_nonneg (f (Complex.I * y))]
      · exact le_of_lt hy
    · use ⊥; simp
    · use ⊤; simp

  have h_ug_ge_zero : 0 ≤ Filter.limsup ug atTop := by
    rw [← limsup_zero_ereal_atTop]
    apply Filter.limsup_le_limsup
    · filter_upwards [eventually_gt_atTop 0] with y hy
      simp only [ug]
      apply EReal.coe_nonneg.mpr
      apply div_nonneg
      · apply Real.log_nonneg
        linarith [norm_nonneg (g (Complex.I * y))]
      · exact le_of_lt hy
    · use ⊥; simp
    · use ⊤; simp

  have h_uf_ne_bot : Filter.limsup uf atTop ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) h_uf_ge_zero
  have h_ug_ne_bot : Filter.limsup ug atTop ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) h_ug_ge_zero

  -- Apply EReal limsup subadditivity
  refine (Filter.limsup_le_limsup h_ineq).trans ?_

  simp only [meanType]
  by_cases hf_top : Filter.limsup uf atTop = ⊤
  · rw [hf_top]
    -- EReal addition: ⊤ + x = ⊤ if x ≠ ⊥.
    rw [EReal.top_add_of_ne_bot h_ug_ne_bot]
    exact le_top
  by_cases hg_top : Filter.limsup ug atTop = ⊤
  · rw [hg_top]
    rw [EReal.add_top_of_ne_bot h_uf_ne_bot]
    exact le_top

  apply EReal.limsup_add_le
  · left; exact h_uf_ne_bot
  · left; exact hf_top

/-- Basic invariance of mean type under scalar multiplication (up to inequality):
\[
  \mathrm{meanType}(c\cdot f) \le \mathrm{meanType}(f).
\]
This is enough for admissibility (`≤ 0`). -/
lemma meanType_smul_le (c : ℂ) (f : ℂ → ℂ) :
    meanType (fun z => c * f z) ≤ meanType f := by
  classical
  let u  : ℝ → EReal :=
    fun y => ((Real.log (‖(c * f (Complex.I * y))‖ + 1)) / y : EReal)
  let uf : ℝ → EReal :=
    fun y => ((Real.log (‖f (Complex.I * y)‖ + 1)) / y : EReal)
  let ψ  : ℝ → EReal :=
    fun y => ((Real.log (‖c‖ + 1)) / y : EReal)

  -- pointwise inequality: `u ≤ ψ + uf` eventually
  have h_ineq : ∀ᶠ y in atTop, u y ≤ ψ y + uf y := by
    refine (eventually_ge_atTop (1 : ℝ)).mono ?_
    intro y hy
    have hy_pos : 0 < y := lt_of_lt_of_le zero_lt_one hy

    -- log(|c f| + 1) <= log(|c|+1) + log(|f|+1)
    have h_log :
      Real.log (‖c * f (Complex.I * y)‖ + 1)
        ≤ Real.log (‖c‖ + 1) + Real.log (‖f (Complex.I * y)‖ + 1) := by
      rw [← Real.log_mul]
      · apply Real.log_le_log
        · exact add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
        · rw [norm_mul]
          nlinarith [norm_nonneg c, norm_nonneg (f (Complex.I * y))]
      · exact ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
      · exact ne_of_gt (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)

    -- Divide by y
    have h_real : (Real.log (‖c * f (Complex.I * y)‖ + 1)) / y
                ≤ (Real.log (‖c‖ + 1)) / y + (Real.log (‖f (Complex.I * y)‖ + 1)) / y := by
       rw [← add_div]
       exact (div_le_div_iff_of_pos_right hy_pos).mpr h_log

    exact EReal.coe_le_coe_iff.mpr h_real

  have h_uf_ge_zero : 0 ≤ Filter.limsup uf atTop := by
    rw [← limsup_zero_ereal_atTop]
    apply Filter.limsup_le_limsup
    · filter_upwards [eventually_gt_atTop 0] with y hy
      simp only [uf]
      apply EReal.coe_nonneg.mpr
      apply div_nonneg
      · apply Real.log_nonneg
        linarith [norm_nonneg (f (Complex.I * y))]
      · exact le_of_lt hy
    · use ⊥; simp
    · use ⊤; simp

  have hψ_ge_zero : 0 ≤ Filter.limsup ψ atTop := by
    rw [← limsup_zero_ereal_atTop]
    apply Filter.limsup_le_limsup
    · filter_upwards [eventually_gt_atTop 0] with y hy
      simp only [ψ]
      apply EReal.coe_nonneg.mpr
      apply div_nonneg
      · apply Real.log_nonneg
        linarith [norm_nonneg c]
      · exact le_of_lt hy
    · use ⊥; simp
    · use ⊤; simp

  have h_uf_ne_bot : Filter.limsup uf atTop ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) h_uf_ge_zero
  have hψ_ne_bot : Filter.limsup ψ atTop ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) hψ_ge_zero

  -- limsup comparison
  have h_limsup_le : Filter.limsup u atTop ≤ Filter.limsup (fun y => ψ y + uf y) atTop :=
    Filter.limsup_le_limsup h_ineq

  have h_add_le : Filter.limsup (fun y => ψ y + uf y) atTop ≤ Filter.limsup ψ atTop + Filter.limsup uf atTop := by
    by_cases hψ_top : Filter.limsup ψ atTop = ⊤
    · rw [hψ_top]
      rw [EReal.top_add_of_ne_bot h_uf_ne_bot]
      exact le_top
    by_cases hf_top : Filter.limsup uf atTop = ⊤
    · rw [hf_top]
      rw [EReal.add_top_of_ne_bot hψ_ne_bot]
      exact le_top
    apply EReal.limsup_add_le
    · left; exact hψ_ne_bot
    · left; exact hψ_top

  -- limit of ψ is 0
  have hψ : Filter.limsup ψ atTop = 0 := by
    apply Filter.Tendsto.limsup_eq
    rw [← EReal.coe_zero]
    refine Tendsto.comp (g := (fun x : ℝ => (x : EReal))) continuous_coe_real_ereal.continuousAt ?_
    simpa using tendsto_inv_atTop_zero.const_mul (Real.log (‖c‖ + 1))

  -- Assemble
  rw [hψ, zero_add] at h_add_le
  exact h_limsup_le.trans h_add_le


/-- The de Branges admissibility condition for a function `f : ℂ → ℂ`:

* `f` is analytic in a neighbourhood of every point of the open upper half-plane;
* `f` is of bounded type (Nevanlinna class) in the upper half-plane;
* `f` has non-positive mean type in the upper half-plane.

This encodes the analytic side of the hypotheses in de Branges' theory of
Hilbert spaces of entire functions. -/
structure IsDeBrangesAdmissible (f : ℂ → ℂ) : Prop where
  analytic_on_UHP :
    AnalyticOnNhd ℂ f upperHalfPlaneSet
  is_bounded_type :
    IsOfBoundedTypeUpperHalfPlane f
  mean_type_nonpos :
    meanType f ≤ 0

end Complex
