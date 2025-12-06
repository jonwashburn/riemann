import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Riemann.academic_framework.DiskHardy

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
  aesop

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

section Inverses

open scoped ComplexOrder

lemma re_cayley_disk (w : Complex.UnitDisc) :
    ((1 + (w : ℂ)) / (1 - (w : ℂ))).re =
      (1 - Complex.normSq (w : ℂ)) /
        Complex.normSq (1 - (w : ℂ)) := by
  set z : ℂ := (w : ℂ)
  have hRe :
      ((1 + z) / (1 - z)).re =
        (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    have hdiv := Complex.div_re (1 + z) (1 - z)
    simp only [add_re, one_re, sub_re, add_im, one_im, zero_add, sub_im, zero_sub] at hdiv
    rw [hdiv]
    simp only [Complex.normSq]
    ring_nf
    simp; grind
  aesop

lemma re_cayley_disk_pos (w : Complex.UnitDisc) :
    0 < ((1 + (w : ℂ)) / (1 - (w : ℂ))).re := by
  have hnum : 0 < 1 - Complex.normSq (w : ℂ) := by
    have hlt : Complex.normSq (w : ℂ) < 1 := by
      simpa using w.normSq_lt_one
    exact sub_pos.mpr hlt
  have hden : 0 < Complex.normSq (1 - (w : ℂ)) := by
    have : (1 - (w : ℂ)) ≠ 0 := sub_ne_zero.mpr
      (by simpa [ne_comm] using w.coe_ne_one)
    exact (Complex.normSq_pos).2 this
  have := div_pos hnum hden
  simpa [re_cayley_disk w] using this

/-- The Cayley inverse from the unit disc to the upper half-plane. -/
def fromUnitDisc (w : Complex.UnitDisc) : UpperHalfPlane :=
  ⟨Complex.I * ((1 + (w : ℂ)) / (1 - (w : ℂ))),
    by
      have := re_cayley_disk_pos w
      have hm : (Complex.I * ((1 + (w : ℂ)) / (1 - (w : ℂ)))).im =
          ((1 + (w : ℂ)) / (1 - (w : ℂ))).re := by
        simp
      simpa [UpperHalfPlane.im, hm] using this⟩

@[simp, norm_cast]
lemma coe_fromUnitDisc (w : Complex.UnitDisc) :
    ((fromUnitDisc w : UpperHalfPlane) : ℂ) =
      Complex.I * ((1 + (w : ℂ)) / (1 - (w : ℂ))) := rfl

lemma mobius_round_trip (w : ℂ) (hw : w ≠ 1) :
    (((1 + w) / (1 - w)) - 1) / (((1 + w) / (1 - w)) + 1) = w := by
  have hw' : (1 - w) ≠ 0 := sub_ne_zero.mpr (by simpa [ne_comm] using hw)
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  field_simp [hw', htwo, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  ring

lemma cayley_comp_from (w : ℂ) (hw : w ≠ 1) :
    ((Complex.I * (1 + w) / (1 - w) - Complex.I) /
        (Complex.I * (1 + w) / (1 - w) + Complex.I)) = w := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hnum :
      Complex.I * ((1 + w) / (1 - w)) - Complex.I =
        Complex.I * (((1 + w) / (1 - w)) - 1) := by ring
  have hden :
      Complex.I * ((1 + w) / (1 - w)) + Complex.I =
        Complex.I * (((1 + w) / (1 - w)) + 1) := by ring
  have hrewrite :
      ((Complex.I * (1 + w) / (1 - w) - Complex.I) /
          (Complex.I * (1 + w) / (1 - w) + Complex.I)) =
        (((1 + w) / (1 - w)) - 1) / (((1 + w) / (1 - w)) + 1) := by
    field_simp [hnum, hden, hI]
  simpa [hrewrite] using mobius_round_trip w hw

lemma from_comp_cayley (z : ℂ) (hz : z + Complex.I ≠ 0) :
    Complex.I * (1 + ((z - Complex.I) / (z + Complex.I))) /
        (1 - ((z - Complex.I) / (z + Complex.I))) = z := by
  have hnum :
      1 + ((z - Complex.I) / (z + Complex.I)) =
        (2 * z) / (z + Complex.I) := by
    field_simp [hz]; grind
  have hden :
      1 - ((z - Complex.I) / (z + Complex.I)) =
        (2 * Complex.I) / (z + Complex.I) := by
    field_simp [hz]; grind
  have hinv :
      Complex.I * (1 + ((z - Complex.I) / (z + Complex.I))) /
          (1 - ((z - Complex.I) / (z + Complex.I))) =
        Complex.I * ((2 * z) / (z + Complex.I)) /
          ((2 * Complex.I) / (z + Complex.I)) := by
    simp [hnum, hden]
  have hcalc :
      Complex.I * ((2 * z) / (z + Complex.I)) /
          ((2 * Complex.I) / (z + Complex.I)) = z := by
    field_simp [hz, Complex.I_ne_zero, mul_comm, mul_left_comm,
      mul_assoc]
  simpa [hinv] using hcalc

@[simp]
lemma toUnitDisc_fromUnitDisc (w : Complex.UnitDisc) :
    UpperHalfPlane.toUnitDisc (fromUnitDisc w) = w := by
  apply Subtype.ext
  -- first, restate `cayley_comp_from` with the desired parentheses
  have h' :
      ((Complex.I * ((1 + (w : ℂ)) / (1 - (w : ℂ))) - Complex.I) /
        (Complex.I * ((1 + (w : ℂ)) / (1 - (w : ℂ))) + Complex.I)) = (w : ℂ) := by
    -- rewrite the original lemma into this form
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      cayley_comp_from (w : ℂ) w.coe_ne_one
  -- now unfold the Cayley maps and use `h'`
  simpa [UpperHalfPlane.toUnitDisc, fromUnitDisc] using h'

@[simp]
lemma fromUnitDisc_toUnitDisc (z : UpperHalfPlane) :
    fromUnitDisc (UpperHalfPlane.toUnitDisc z) = z := by
  apply Subtype.ext
  have him : 0 < (z : ℂ).im := z.property
  have hden : (z : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hz : (z : ℂ) = -Complex.I := by
      simpa using eq_neg_of_add_eq_zero_left h
    have hz_im : (z : ℂ).im = -1 := by
      simp [hz]
    have : (0 : ℝ) < -1 := by
      simp_all
    have hfalse : ¬ (0 : ℝ) < -1 := by norm_num
    exact hfalse this
  -- rewrite `from_comp_cayley` into the same shape as `fromUnitDisc ∘ toUnitDisc`
  have h' :
      Complex.I * ((1 + ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) /
        (1 - ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I))) = (z : ℂ) := by
    simpa [mul_div_assoc] using
      from_comp_cayley ((z : ℂ)) hden
  -- now the left-hand side is exactly the complex value of `fromUnitDisc (toUnitDisc z)`
  simpa [UpperHalfPlane.toUnitDisc, fromUnitDisc] using h'

end Inverses


/-
## Poisson transport along the Cayley transform

As a first application, we record a simple transport lemma: if a function `F` on the
unit disc has a Poisson representation in the sense of `HasDiskPoissonRepresentation`,
then its pullback along the Cayley transform inherits a Poisson representation, with
the same boundary data and kernel evaluated at `toUnitDisc z`.

This mirrors the `pinch_hasPoissonRepOn_from_cayley` pattern in
`Riemann/RS/HalfPlaneOuterV2.lean`, but specialized to the classical unit disc /
upper half‑plane setting and the disk‑level Poisson representation API from
`Riemann/academic_framework/DiskHardy.lean`.
-/

section PoissonTransport

open MeasureTheory

namespace Complex

/-- Pull back a disk‑function `F` to the upper half‑plane via the Cayley transform. -/
def cayleyPullback (F : ℂ → ℂ) (z : UpperHalfPlane) : ℂ :=
  F ((UpperHalfPlane.toUnitDisc z : Complex.UnitDisc))

@[simp]
lemma cayleyPullback_re (F : ℂ → ℂ) (z : UpperHalfPlane) :
    (cayleyPullback F z).re =
      (F (UpperHalfPlane.toUnitDisc z : Complex.UnitDisc)).re := rfl

/-- Disk Poisson representation transported to the upper half‑plane along the Cayley map.

If `F` has a Poisson representation on the unit disc, then the pullback
`z ↦ F (toUnitDisc z)` satisfies the *same* Poisson formula, with the Poisson
kernel evaluated at `toUnitDisc z`.  This is just a reparametrization of the
disk Poisson formula. -/
lemma HasDiskPoissonRepresentation.cayleyPullback_re_eq
    {F : ℂ → ℂ} (hF : HasDiskPoissonRepresentation F) (z : UpperHalfPlane) :
    (cayleyPullback F z).re =
      ∫ θ in Set.Icc 0 (2 * Real.pi),
        (F (Circle.exp θ)).re *
          Complex.poissonKernel (UpperHalfPlane.toUnitDisc z) θ ∂(volume) := by
  -- By definition, `cayleyPullback F z = F (toUnitDisc z)`, so this is just
  -- the disk Poisson formula specialized to the point `toUnitDisc z : 𝔻`.
  simpa [cayleyPullback] using hF.re_eq (UpperHalfPlane.toUnitDisc z)

end Complex

end PoissonTransport
