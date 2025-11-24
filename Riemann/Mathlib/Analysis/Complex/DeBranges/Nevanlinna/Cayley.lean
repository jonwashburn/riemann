import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-
# Cayley transport between the upper half-plane and the unit disc

This file records the basic analytic geometry needed to shuttle statements
between the classical upper half-plane `UpperHalfPlane` and the unit disc `𝔻`.  The Cayley
transform
\[
  \mathcal{C}(z) = \frac{z - i}{z + i}
\]
is a biholomorphism from `UpperHalfPlane` onto `𝔻`; its inverse is
\[
  \mathcal{C}^{-1}(w) = i \frac{1 + w}{1 - w}.
\]

We verify the elementary estimates that will later allow the Nevanlinna theory
arguments in `NevanlinnaGrowth.lean` to be reduced to Mathlib's global
ValueDistribution statements on the plane/disc.
-/

noncomputable section

open Complex
open scoped ComplexOrder UnitDisc

namespace Complex
namespace UpperHalfPlane

/-- A convenient algebraic identity measuring how much closer a point of the
upper half-plane is to `-i` than to `i`. -/
lemma normSq_add_I_sub_normSq_sub_I (z : ℂ) :
    Complex.normSq (z + Complex.I) - Complex.normSq (z - Complex.I) =
      4 * z.im := by
  have h₁ :
      Complex.normSq (z + Complex.I) =
        z.re ^ 2 + (z.im + 1) ^ 2 := by
    simp [Complex.normSq, pow_two]
  have h₂ :
      Complex.normSq (z - Complex.I) =
        z.re ^ 2 + (z.im - 1) ^ 2 := by
    simp [Complex.normSq, sub_eq_add_neg, pow_two]
  have h_diff :
      (z.re ^ 2 + (z.im + 1) ^ 2) - (z.re ^ 2 + (z.im - 1) ^ 2) = 4 * z.im := by
    ring
  simpa [h₁, h₂] using h_diff

open scoped Complex.UpperHalfPlane

lemma normSq_sub_I_lt_normSq_add_I  (z : UpperHalfPlane) :
    Complex.normSq ((z : ℂ) - Complex.I) <
      Complex.normSq ((z : ℂ) + Complex.I) := by
  have him : 0 < (z : ℂ).im := z.property
  have hpos : 0 < Complex.normSq ((z : ℂ) + Complex.I) -
        Complex.normSq ((z : ℂ) - Complex.I) := by
    have : 0 < 4 * (z : ℂ).im := by
      have h4 : 0 < (4 : ℝ) := by norm_num
      exact mul_pos h4 him
    simpa [normSq_add_I_sub_normSq_sub_I] using this
  exact sub_pos.mp hpos

lemma cayley_normSq_lt_one (z : UpperHalfPlane) :
    Complex.normSq (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) < 1 := by
  have hplus_ne : (z : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hz : (z : ℂ) = -Complex.I := by
      simpa using eq_neg_of_add_eq_zero_left h
    have hz_im : (z : ℂ).im = -1 := by
      simpa using congrArg Complex.im hz
    have hpos : 0 < (z : ℂ).im := z.property
    have : (0 : ℝ) < -1 := by aesop
    have hfalse : ¬ (0 : ℝ) < -1 := by norm_num
    exact hfalse this
  have hden_pos :
      0 < Complex.normSq ((z : ℂ) + Complex.I) := by
    have hden_ne : Complex.normSq ((z : ℂ) + Complex.I) ≠ 0 := by
      refine mt Complex.normSq_eq_zero.mp ?_
      exact fun hz => hplus_ne (by simpa using hz)
    exact lt_of_le_of_ne (Complex.normSq_nonneg _) hden_ne.symm
  have hratio :
      Complex.normSq (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) =
        Complex.normSq ((z : ℂ) - Complex.I) /
          Complex.normSq ((z : ℂ) + Complex.I) := by
    simp [div_eq_mul_inv, Complex.normSq_mul]
  have hlt :=
      (div_lt_one hden_pos).2 (normSq_sub_I_lt_normSq_add_I z)
  simpa [hratio] using hlt

end UpperHalfPlane
end Complex

namespace UpperHalfPlane
open Complex

/-- Auxiliary lemma: `‖w‖ < 1` once its squared norm is `< 1`. -/
lemma norm_lt_one_of_normSq_lt_one {w : ℂ}
    (h : Complex.normSq w < 1) : ‖w‖ < 1 := by
  have hsqrt := Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) h
  simpa [norm, Real.sqrt_one] using hsqrt

/-- The Cayley transform from the upper half-plane to the unit disc. -/
def toUnitDisc (z : UpperHalfPlane) : Complex.UnitDisc :=
  ⟨((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I),
    by
  have h := Complex.UpperHalfPlane.cayley_normSq_lt_one z
  have h' :
      Complex.normSq (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I) - 0) < 1 := by
    simpa [sub_eq_add_neg] using h
  exact norm_lt_one_of_normSq_lt_one h'⟩

@[simp, norm_cast]
lemma coe_toUnitDisc (z : UpperHalfPlane) :
    ((toUnitDisc z : Complex.UnitDisc) : ℂ) =
      ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I) := rfl

end UpperHalfPlane
