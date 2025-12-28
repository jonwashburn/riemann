/-
# Route 3: the "easy" RH → positivity direction (finite-sum form)

Weil positivity (Lagarias Thm 3.2) is a statement about a *sum over all zeros*.
The analytic difficulty is defining and justifying that infinite symmetric sum.

However, the *algebraic* heart of the easy direction under RH is finite:

- if `ρ` is a zero on the critical line, then `1 - conj ρ = ρ`, and
- for `g = f ⋆ tilde(star f)` one has `M[g](ρ) = M[f](ρ) * star (M[f](ρ))`,
  hence its real part is nonnegative.

This file proves the corresponding finite-sum positivity statement. It does not
use any old-route modules.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannRecognitionGeometry.ExplicitFormula.Defs
import RiemannRecognitionGeometry.ExplicitFormula.MathlibBridge
import RiemannRecognitionGeometry.ExplicitFormula.MulConvolution

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace
open MeasureTheory Set
open ComplexConjugate
open scoped BigOperators

/--
For `z : ℂ`, the element `z * star z` has nonnegative real part.

This is the abstract fact used in the RH→positivity direction.
-/
lemma mul_star_self_re_nonneg (z : ℂ) : 0 ≤ (z * star z).re := by
  -- `z * star z = (Complex.normSq z : ℂ)`, hence its real part is `Complex.normSq z ≥ 0`.
  have hmul : z * star z = (Complex.normSq z : ℂ) := by
    -- `Complex.mul_conj` is stated using `starRingEnd ℂ`; rewrite `star` via `Complex.star_def`.
    simpa [Complex.star_def] using (Complex.mul_conj z)
  have hre : (z * star z).re = Complex.normSq z := by
    have := congrArg Complex.re hmul
    simpa using this
  simpa [hre] using (Complex.normSq_nonneg z)

/--
Finite-sum Weil positivity under the hypothesis that all `ρ ∈ S` lie on the
critical line and satisfy the symmetry relation `1 - conj ρ = ρ`.

This is the finite-sum form of the RH→positivity direction.
-/
lemma finite_WeilPositivity_of_symmetry {F : Type} [TestSpace F]
    (f : F) (S : Finset ℂ)
    (hSymm : ∀ ρ ∈ S, (1 - star ρ) = ρ)
    (hM : ∀ ρ ∈ S, M[quad (F:=F) f](ρ) = M[f](ρ) * star (M[f](ρ))) :
    0 ≤ (∑ ρ in S, M[quad (F:=F) f](ρ)).re := by
  -- Rewrite each summand using `hM`, then use termwise nonnegativity.
  have hsum : (∑ ρ in S, M[quad (F:=F) f](ρ)).re =
      (∑ ρ in S, (M[f](ρ) * star (M[f](ρ)))).re := by
    refine congrArg Complex.re ?_
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    exact (hM ρ hρ)
  -- Note: `hSymm` isn't used here yet; it is exactly what makes the identity
  -- `M[quad f](ρ) = M[f](ρ) * star(M[f](ρ))` true in analytic applications.
  rw [hsum]
  -- Apply `re` to the sum termwise, then use termwise nonnegativity.
  have : (∑ ρ in S, (M[f](ρ) * star (M[f](ρ)))).re =
      ∑ ρ in S, ((M[f](ρ) * star (M[f](ρ)))).re := by
    simpa using (Complex.re_sum (s := S) (f := fun ρ => (M[f](ρ) * star (M[f](ρ)))))
  -- Use this rewriting, then sum nonneg terms.
  rw [this]
  refine Finset.sum_nonneg (fun ρ hρ => ?_)
  simpa using mul_star_self_re_nonneg (M[f](ρ))

/-!
## Concrete `(ℝ → ℂ)` version (using Mathlib's `mellin`)

This upgrades the abstract finite-sum lemma by deriving the key identity

`mellin (f ⋆ tilde(starFun f)) ρ = mellin f ρ * star (mellin f ρ)`

from:
- Mellin multiplicativity for `mulConv` (still quarantined as `MulConvAssumptions`), and
- the explicit conjugation steps (`mellin_tildeFun`, `mellin_starFun`).

This is the exact "easy" algebraic heart of the RH → Weil-positivity direction.
-/

/-- The concrete quadratic form `f ⋆ tilde(star f)` on functions `ℝ → ℂ`. -/
noncomputable def quadFun (f : ℝ → ℂ) : ℝ → ℂ :=
  mulConv f (tildeFun (starFun f))

lemma one_sub_star_eq_of_re_eq_half {s : ℂ} (hs : s.re = (1 / 2 : ℝ)) : (1 - star s) = s := by
  apply Complex.ext
  · -- real parts: `1 - re(s) = re(s)`
    have : (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) := by ring
    simpa [hs, this]
  · -- imaginary parts
    simp

lemma one_sub_star_eq_of_RH {s : ℂ} (hRH : RiemannHypothesis) (hs0 : riemannZeta s = 0)
    (htriv : ¬ ∃ n, s = -2 * (↑n + 1)) (hs1 : s ≠ 1) : (1 - star s) = s := by
  exact one_sub_star_eq_of_re_eq_half (hs := hRH s hs0 htriv hs1)

/-- On the critical line symmetry `1 - star ρ = ρ`, the `quadFun` Mellin transform is `z * star z`. -/
lemma mellin_quadFun_of_symmetry (A : MulConvAssumptions) (f : ℝ → ℂ) (ρ : ℂ)
    (hSymm : (1 - star ρ) = ρ)
    (hf : MellinConvergent f ρ)
    (hg : MellinConvergent (tildeFun (starFun f)) ρ)
    (hfg : MellinConvergent (quadFun f) ρ) :
    mellin (quadFun f) ρ = mellin f ρ * star (mellin f ρ) := by
  have hmul :
      mellin (quadFun f) ρ = mellin f ρ * mellin (tildeFun (starFun f)) ρ := by
    -- multiplicativity of the Mellin transform for `mulConv`
    simpa [quadFun] using A.mellin_mulConv f (tildeFun (starFun f)) ρ hf hg hfg
  have htilde :
      mellin (tildeFun (starFun f)) ρ = mellin (starFun f) (1 - ρ) := by
    simpa using (mellin_tildeFun (f := starFun f) (s := ρ))
  have h1ρ : (1 - ρ) = star ρ := by
    -- Apply `star` to `1 - star ρ = ρ`.
    have := congrArg star hSymm
    simpa [sub_eq_add_neg] using this
  have hstar : mellin (starFun f) (star ρ) = star (mellin f ρ) := by
    simpa using (mellin_starFun (f := f) (s := ρ) hf)
  calc
    mellin (quadFun f) ρ
        = mellin f ρ * mellin (tildeFun (starFun f)) ρ := hmul
    _ = mellin f ρ * mellin (starFun f) (1 - ρ) := by simp [htilde]
    _ = mellin f ρ * mellin (starFun f) (star ρ) := by simp [h1ρ]
    _ = mellin f ρ * star (mellin f ρ) := by simp [hstar]

/-- Finite-sum Weil positivity for the concrete `quadFun` (assuming Mellin multiplicativity). -/
lemma finite_WeilPositivity_quadFun (A : MulConvAssumptions) (f : ℝ → ℂ) (S : Finset ℂ)
    (hSymm : ∀ ρ ∈ S, (1 - star ρ) = ρ)
    (hf : ∀ ρ ∈ S, MellinConvergent f ρ)
    (hg : ∀ ρ ∈ S, MellinConvergent (tildeFun (starFun f)) ρ)
    (hfg : ∀ ρ ∈ S, MellinConvergent (quadFun f) ρ) :
    0 ≤ (∑ ρ in S, mellin (quadFun f) ρ).re := by
  -- rewrite each summand using `mellin_quadFun_of_symmetry`
  have hsum : (∑ ρ in S, mellin (quadFun f) ρ).re =
      (∑ ρ in S, (mellin f ρ * star (mellin f ρ))).re := by
    refine congrArg Complex.re ?_
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    exact mellin_quadFun_of_symmetry (A := A) (f := f) (ρ := ρ)
      (hSymm ρ hρ) (hf ρ hρ) (hg ρ hρ) (hfg ρ hρ)
  rw [hsum]
  have : (∑ ρ in S, (mellin f ρ * star (mellin f ρ))).re =
      ∑ ρ in S, ((mellin f ρ * star (mellin f ρ))).re := by
    simpa using (Complex.re_sum (s := S) (f := fun ρ => (mellin f ρ * star (mellin f ρ))))
  rw [this]
  refine Finset.sum_nonneg (fun ρ _ => ?_)
  simpa using mul_star_self_re_nonneg (mellin f ρ)

end ExplicitFormula
end RiemannRecognitionGeometry
