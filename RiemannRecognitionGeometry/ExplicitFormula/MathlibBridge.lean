/-
# Route 3: Mathlib integration (Mellin transform)

This file connects the abstract Route 3 `TestSpace` interface to Mathlib's
actual `mellin` definition (`Mathlib.Analysis.MellinTransform`).

Convention check:
- Route 3 (Lagarias): M[f](s) = ∫₀^∞ f(x) x^s dx/x
- Mathlib: mellin f s = ∫ (t : ℝ) in Ioi 0, t^(s-1) • f t

These are equivalent: t^(s-1) dt = t^s (dt/t) = x^s (dx/x).
-/

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.Complex.Basic
import RiemannRecognitionGeometry.ExplicitFormula.Defs

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory Set Filter Asymptotics TopologicalSpace
open ComplexConjugate

/--
The concrete Mellin transform on functions `f : ℝ → ℂ`, using Mathlib's definition.
This matches Lagarias' normalization M[f](s) = ∫₀^∞ f(x) x^s dx/x.
-/
def concreteMellin (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin f s

/--
Verifies that `concreteMellin` is chemically compatible with `TestSpace.Mellin`.
(This doesn't prove the `TestSpace` axioms yet, just defines the operation).
-/
lemma concreteMellin_eq_mathlib_mellin (f : ℝ → ℂ) (s : ℂ) :
    concreteMellin f s = mellin f s := rfl

/-!
## The Lagarias involution on `(0,∞)` and its Mellin intertwining

Lagarias' involution on test functions is:
`~f(x) = (1/x) f(1/x)`.

In Mathlib's Mellin normalization, the key identity is
`mellin (~f) s = mellin f (1 - s)`.

This is a change-of-variables statement and follows from two generic Mellin lemmas:
- `mellin_cpow_smul` (multiplying by `t^a` shifts the Mellin variable by `a`), and
- `mellin_comp_inv` (inverting the input sends `s ↦ -s`).
-/

/-- Lagarias' involution on functions `f : ℝ → ℂ` (values on `t ≤ 0` are irrelevant). -/
def tildeFun (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ((t : ℂ) ^ (-1 : ℂ)) • f t⁻¹

lemma mellin_tildeFun (f : ℝ → ℂ) (s : ℂ) :
    mellin (tildeFun f) s = mellin f (1 - s) := by
  -- Expand `tildeFun` and use the generic Mellin shift and inversion lemmas.
  unfold tildeFun
  -- First: pull out the `t^(-1)` factor, shifting `s` by `-1`.
  have h1 :
      mellin (fun t : ℝ => ((t : ℂ) ^ (-1 : ℂ)) • f t⁻¹) s =
        mellin (fun u : ℝ => f u⁻¹) (s - 1) := by
    -- `mellin_cpow_smul` shifts `s` by the exponent `a`.
    simpa [sub_eq_add_neg] using
      (mellin_cpow_smul (f := fun u : ℝ => f u⁻¹) (s := s) (a := (-1 : ℂ)))
  -- Second: invert the input, sending `(s-1) ↦ -(s-1) = 1-s`.
  have h2 : mellin (fun u : ℝ => f u⁻¹) (s - 1) = mellin f (1 - s) := by
    -- `mellin_comp_inv f (s-1)` gives `= mellin f (-(s-1)) = mellin f (1-s)`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (mellin_comp_inv (f := f) (s := s - 1))
  exact h1.trans h2

/-!
## Conjugation (`star`) and the Mellin transform

For the RH → Weil-positivity direction we need the standard identity (for convergent Mellin
integrals)

`mellin (starFun f) (star s) = star (mellin f s)`.

This is a Bochner-integral fact: complex conjugation is an ℝ-linear continuous linear map, hence
commutes with integration, and it commutes with `t ↦ (t : ℂ) ^ (s - 1)` for `t > 0`.
-/

/-- Pointwise complex conjugation (`star`) on functions `ℝ → ℂ`. -/
def starFun (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => star (f t)

/-- For `t > 0`, conjugation commutes with `((t:ℂ)^(s-1))` in the exponent. -/
lemma star_ofReal_cpow {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) (s : ℂ) :
    star ((t : ℂ) ^ (s - 1)) = (t : ℂ) ^ (star s - 1) := by
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  have harg : ((t : ℂ).arg) = 0 := Complex.arg_ofReal_of_nonneg ht0
  have hx : (t : ℂ).arg ≠ Real.pi := by
    -- arg is 0, and `Real.pi ≠ 0`.
    simpa [harg] using (Real.pi_ne_zero.symm)
  -- Start from `Complex.conj_cpow`, simplify `conj (t:ℂ) = (t:ℂ)`, then conjugate both sides.
  have h := Complex.conj_cpow (x := (t : ℂ)) (n := (s - 1)) hx
  have h' : (t : ℂ) ^ (s - 1) = conj ((t : ℂ) ^ (conj (s - 1))) := by
    simpa [Complex.conj_ofReal] using h
  have : conj ((t : ℂ) ^ (s - 1)) = (t : ℂ) ^ (conj (s - 1)) := by
    simpa using congrArg conj h'
  -- Rewrite `conj` as `star`.
  simpa [map_sub, map_one] using this

/--
If the Mellin transform of `f` converges at `s`, then conjugation commutes with the Mellin
transform at `s`.
-/
lemma mellin_starFun (f : ℝ → ℂ) (s : ℂ) (hf : MellinConvergent f s) :
    mellin (starFun f) (star s) = star (mellin f s) := by
  -- Unfold `mellin` as an integral on `Ioi 0`.
  unfold mellin
  -- Use `ContinuousLinearMap.integral_comp_comm` for the ℝ-linear map `conj`.
  have hφ :
      Integrable (fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) (volume.restrict (Ioi (0 : ℝ))) := by
    simpa [MellinConvergent, IntegrableOn] using hf
  have hconj :
      (∫ t : ℝ, conj ((t : ℂ) ^ (s - 1) • f t) ∂(volume.restrict (Ioi (0 : ℝ))))
        = conj (∫ t : ℝ, (t : ℂ) ^ (s - 1) • f t ∂(volume.restrict (Ioi (0 : ℝ)))) := by
    simpa using
      (ContinuousLinearMap.integral_comp_comm (μ := (volume.restrict (Ioi (0 : ℝ))))
        (L := (↑(Complex.conjCLE) : ℂ →L[ℝ] ℂ)) (φ := fun t : ℝ => (t : ℂ) ^ (s - 1) • f t) hφ)
  -- Rewrite the conjugated integrand into the Mellin integrand for `starFun f` at `star s`.
  have hIntegrand :
      EqOn (fun t : ℝ => (t : ℂ) ^ (star s - 1) • starFun f t)
        (fun t : ℝ => conj ((t : ℂ) ^ (s - 1) • f t)) (Ioi (0 : ℝ)) := by
    intro t ht
    unfold starFun
    -- On `ℂ`, scalar multiplication is multiplication. After rewriting, `simp` reduces the goal
    -- to a benign disjunction arising from canceling the common factor `conj (f t)`; we solve it
    -- by the left disjunct using `star_ofReal_cpow`.
    have hmul : conj (((t : ℂ) ^ (s - 1)) * f t) =
        conj ((t : ℂ) ^ (s - 1)) * conj (f t) := by
      simp
    have hcpow : conj ((t : ℂ) ^ (s - 1)) = (t : ℂ) ^ (star s - 1) := by
      simpa using (star_ofReal_cpow (t := t) ht s)
    -- Rewrite the RHS into the same normal form as the LHS.
    simp [smul_eq_mul, hmul, hcpow, mul_assoc]
  have hEq :
      (∫ t : ℝ in Ioi (0 : ℝ), (t : ℂ) ^ (star s - 1) • starFun f t)
        = (∫ t : ℝ in Ioi (0 : ℝ), conj ((t : ℂ) ^ (s - 1) • f t)) :=
    setIntegral_congr_fun measurableSet_Ioi hIntegrand
  -- Finish by combining the integrand rewrite with `hconj`, and rewriting `conj` as `star`.
  simpa [starFun, Complex.star_def] using hEq.trans hconj

end ExplicitFormula
end RiemannRecognitionGeometry
