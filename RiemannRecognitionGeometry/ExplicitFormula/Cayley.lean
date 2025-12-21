import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Cayley transform: `Re z ≥ 0` ⇒ `|(z-1)/(z+1)| ≤ 1`

This is the classical “Carathéodory/Herglotz → Schur” algebraic lemma:
if a complex number has nonnegative real part, then its Cayley transform lies in the closed unit disk.

Route 3 (explicit-formula / Weil–Li) uses this as a reusable *bridge shape*:
positivity of a real part can be converted into a unit-disk bound after a Cayley transform.

This file is intentionally independent of any old-route Carleson/BMO/Whitney infrastructure.
-/

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex

namespace Cayley

/-- Cayley transform sending the right half-plane to the unit disk. -/
def theta (z : ℂ) : ℂ := (z - 1) / (z + 1)

@[simp] lemma theta_def (z : ℂ) : theta z = (z - 1) / (z + 1) := rfl

/-- A minimal “Schur on a set” predicate: pointwise unit-disk bound. -/
def IsSchurOn (Θ : ℂ → ℂ) (S : Set ℂ) : Prop :=
  ∀ z ∈ S, norm (Θ z) ≤ 1

lemma normSq_sub_one_le_normSq_add_one {z : ℂ} (hz : 0 ≤ z.re) :
    Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) := by
  -- Reduce to the real inequality `(a-1)^2 ≤ (a+1)^2` for `a = z.re`.
  have hdiff : 0 ≤ (z.re + 1) ^ 2 - (z.re - 1) ^ 2 := by
    -- `(a+1)^2 - (a-1)^2 = 4a`
    have hId : (z.re + 1) ^ 2 - (z.re - 1) ^ 2 = 4 * z.re := by ring
    -- `0 ≤ 4*z.re` from `0 ≤ z.re`
    have hz4 : 0 ≤ (4 : ℝ) * z.re := by nlinarith
    simpa [hId] using hz4
  have hreal : (z.re - 1) ^ 2 ≤ (z.re + 1) ^ 2 :=
    (sub_nonneg).1 hdiff
  -- Now lift to `normSq` by adding the common `im^2` term.
  have hcore :
      (z.re - 1) * (z.re - 1) + z.im * z.im ≤ (z.re + 1) * (z.re + 1) + z.im * z.im := by
    have hmul : (z.re - 1) * (z.re - 1) ≤ (z.re + 1) * (z.re + 1) := by
      simpa [pow_two] using hreal
    exact add_le_add_right hmul (z.im * z.im)
  -- Rewrite both sides as `normSq` expressions.
  have h1 : Complex.normSq (z - 1) = (z.re - 1) * (z.re - 1) + z.im * z.im := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  have h2 : Complex.normSq (z + 1) = (z.re + 1) * (z.re + 1) + z.im * z.im := by
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
  simpa [h1, h2] using hcore

lemma abs_sub_one_le_abs_add_one {z : ℂ} (hz : 0 ≤ z.re) :
    norm (z - 1) ≤ norm (z + 1) := by
  -- `abs z = sqrt (normSq z)` and `sqrt` is monotone.
  have hnorm : Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) :=
    normSq_sub_one_le_normSq_add_one (z := z) hz
  simpa [norm] using Real.sqrt_le_sqrt hnorm

/--
Core Cayley inequality: if `Re z ≥ 0` then the Cayley transform lies in the closed unit disk.
-/
lemma abs_theta_le_one_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    norm (theta z) ≤ 1 := by
  -- `| (z-1)/(z+1) | = |z-1|/|z+1| ≤ 1` because `|z-1| ≤ |z+1|`.
  have hle : norm (z - 1) ≤ norm (z + 1) :=
    abs_sub_one_le_abs_add_one (z := z) hz
  -- Use `div_le_one_of_le₀` (works even if the denominator is `0` by field conventions).
  have hdiv : norm (z - 1) / norm (z + 1) ≤ 1 :=
    div_le_one_of_le₀ (by simpa using hle) (by exact norm_nonneg (z + 1))
  -- Rewrite the LHS as the absolute value of the quotient.
  simpa [theta, abs_div] using hdiv

/--
Scaled Cayley inequality in the form used in the other repo: `Θ(z) = ((2·J z)-1)/((2·J z)+1)`.
-/
def thetaOfJ (J : ℂ → ℂ) (z : ℂ) : ℂ := theta ((2 : ℂ) * J z)

lemma abs_thetaOfJ_le_one_of_re_nonneg (J : ℂ → ℂ) {z : ℂ}
    (hz : 0 ≤ (((2 : ℂ) * J z).re)) :
    norm (thetaOfJ J z) ≤ 1 := by
  simpa [thetaOfJ] using (abs_theta_le_one_of_re_nonneg (z := (2 : ℂ) * J z) hz)

/-- “Cayley → Schur” on any set where `Re(2·J) ≥ 0` holds. -/
lemma Theta_Schur_of_Re_nonneg_on (J : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ (((2 : ℂ) * J z).re)) :
    IsSchurOn (thetaOfJ J) S := by
  intro z hz
  exact abs_thetaOfJ_le_one_of_re_nonneg (J := J) (z := z) (hRe z hz)

end Cayley

end ExplicitFormula
end RiemannRecognitionGeometry
