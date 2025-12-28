/-
# Route 3: multiplicative convolution on `(0,∞)` (Lagarias)

Lagarias' multiplicative convolution (on test functions on `(0,∞)`) is

  (f ⋆ g)(x) := ∫₀^∞ f(x / y) g(y) dy / y.

The Mellin transform (Mathlib's `mellin`) satisfies the expected identity

  mellin (f ⋆ g) s = mellin f s * mellin g s,

under suitable integrability hypotheses (Fubini/Tonelli + change of variables).

In this file we:
- define the convolution operation `mulConv`, and
- record the Mellin-multiplicativity statement as an explicit *assumption package*
  (to be discharged later by a genuine proof).

This is the exact analytic lemma needed to upgrade Route 3 from an abstract
`TestSpace` interface to a concrete function-space instance.
-/

import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Basic

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory Set

/-- Multiplicative convolution on `(0,∞)` written as an integral over `Ioi 0`. -/
noncomputable def mulConv (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∫ y : ℝ in Ioi 0, f (x / y) * g y / y

/--
Assumptions for the multiplicative-convolution/Mellin-multiplicativity identity.

This is intentionally quarantined: proving it requires a careful Fubini/Tonelli
argument, and is the main analytic bridge needed for U3.
-/
structure MulConvAssumptions where
  mellin_mulConv :
    ∀ (f g : ℝ → ℂ) (s : ℂ),
      MellinConvergent f s →
      MellinConvergent g s →
      MellinConvergent (mulConv f g) s →
      mellin (mulConv f g) s = mellin f s * mellin g s

/-!
## A provable Mellin-multiplicativity lemma (under explicit Fubini hypotheses)

The field `MulConvAssumptions.mellin_mulConv` quarantines the analytic content needed for
`mellin (mulConv f g) s = mellin f s * mellin g s`.

Here we prove a *version that follows directly from Fubini/Tonelli* under an explicit integrability
hypothesis on the uncurried two-variable integrand. This narrows the remaining analytic gap to:

> For the chosen test-function class, prove the required `Integrable` hypothesis.

This is strictly stronger than the abstract `MellinConvergent` hypotheses, but it is a concrete,
standard condition that can be attacked inside Mathlib.
-/

namespace MulConv

open scoped BigOperators

abbrev μ0 : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

instance : SFinite μ0 := by
  delta μ0
  infer_instance

lemma mellin_comp_mul_right_one_div (f : ℝ → ℂ) (s : ℂ) (y : ℝ) (hy : 0 < y) :
    (∫ x : ℝ in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * f (x / y))
      = ((1 / y : ℝ) : ℂ) ^ (-s) * mellin f s := by
  have hy' : 0 < (1 / y : ℝ) := one_div_pos.mpr hy
  have h := mellin_comp_mul_right (f := f) (s := s) (a := (1 / y : ℝ)) hy'
  simp [mellin, smul_eq_mul, div_eq_mul_inv, one_div] at h
  simpa [div_eq_mul_inv, one_div] using h

lemma one_div_cpow_neg_mul_inv_of_pos (y : ℝ) (hy : 0 < y) (s : ℂ) :
    ((1 / y : ℝ) : ℂ) ^ (-s) * ((y : ℂ)⁻¹) = (y : ℂ) ^ (s - 1) := by
  have hy0 : y ≠ 0 := hy.ne'
  have hyC0 : (y : ℂ) ≠ 0 := by
    exact_mod_cast hy0
  -- `(1/y : ℂ) = (y : ℂ)⁻¹`.
  have h1 : ((1 / y : ℝ) : ℂ) = (y : ℂ)⁻¹ := by
    simp [one_div, hy0]
  -- For `y > 0`, `arg (y : ℂ) = 0 ≠ π`, so `((y : ℂ)⁻¹)^(-s) = (y : ℂ)^s`.
  have harg : (y : ℂ).arg ≠ Real.pi := by
    have : (y : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hy.le
    simpa [this] using (Real.pi_ne_zero.symm)
  have hinv : ((y : ℂ)⁻¹) ^ (-s) = (y : ℂ) ^ s := by
    have h := Complex.inv_cpow_eq_ite (x := (y : ℂ)) (n := (-s))
    simp [harg] at h
    calc
      ((y : ℂ)⁻¹) ^ (-s) = ((y : ℂ) ^ (-s))⁻¹ := h
      _ = (y : ℂ) ^ s := by simp [Complex.cpow_neg]
  have hs : s - 1 = s + (-1 : ℂ) := by ring
  have hadd := Complex.cpow_add (x := (y : ℂ)) (y := s) (z := (-1 : ℂ)) hyC0
  calc
    ((1 / y : ℝ) : ℂ) ^ (-s) * ((y : ℂ)⁻¹)
        = ((y : ℂ)⁻¹) ^ (-s) * ((y : ℂ)⁻¹) := by simp [h1]
    _ = (y : ℂ) ^ s * ((y : ℂ)⁻¹) := by simp [hinv]
    _ = (y : ℂ) ^ (s - 1) := by
          -- `y^(s-1) = y^s * y^(-1)` and `y^(-1) = y⁻¹`.
          simpa [hs, Complex.cpow_neg_one, mul_assoc] using hadd.symm

/--
Mellin-multiplicativity for `mulConv`, assuming an explicit product-measure integrability hypothesis
that justifies Fubini/Tonelli.

This is the key analytic identity needed for a concrete `TestSpace` instance on `(0,∞)`.
-/
lemma mellin_mulConv_of_integrable (f g : ℝ → ℂ) (s : ℂ)
    (hF : Integrable (fun z : ℝ × ℝ =>
      ((z.1 : ℂ) ^ (s - 1)) * (f (z.1 / z.2) * g z.2 / z.2)) (μ0.prod μ0)) :
    mellin (mulConv f g) s = mellin f s * mellin g s := by
  -- Expand `mellin` and `mulConv`.
  simp [mellin, mulConv, smul_eq_mul]

  -- Rewrite `x^(s-1) * ∫_y (...)` as an iterated integral `∫_x ∫_y x^(s-1) * (...)`.
  have hLHS :
      (∫ x : ℝ in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * ∫ y : ℝ in Ioi (0 : ℝ), f (x / y) * g y / y)
        = ∫ x : ℝ in Ioi (0 : ℝ), ∫ y : ℝ in Ioi (0 : ℝ),
            (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simpa using
      (MeasureTheory.integral_mul_left (μ := μ0) (r := (x : ℂ) ^ (s - 1))
        (f := fun y : ℝ => f (x / y) * g y / y)).symm
  rw [hLHS]

  -- Swap integrals using Fubini.
  have hswap :
      (∫ x : ℝ in Ioi (0 : ℝ), ∫ y : ℝ in Ioi (0 : ℝ),
          (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y))
        = ∫ y : ℝ in Ioi (0 : ℝ), ∫ x : ℝ in Ioi (0 : ℝ),
          (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y) := by
    simpa [μ0, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.integral_integral_swap (μ := μ0) (ν := μ0)
        (f := fun x y => (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y)) hF)
  rw [hswap]

  -- Compute the inner integral pointwise for `y > 0` and rewrite under the outer integral.
  have hInner :
      EqOn
        (fun y : ℝ => ∫ x : ℝ in Ioi (0 : ℝ),
          (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y))
        (fun y : ℝ => (y : ℂ) ^ (s - 1) * g y * mellin f s)
        (Ioi (0 : ℝ)) := by
    intro y hy
    have hy' : 0 < y := hy
    -- Pull out the constant `(g y / y)` from the `x`-integral.
    have hpull :
        (∫ x : ℝ in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y))
          = (g y / y) * (∫ x : ℝ in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * f (x / y)) := by
      have hreorder :
          (∫ x : ℝ in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y))
            = ∫ x : ℝ in Ioi (0 : ℝ), (g y / y) * ((x : ℂ) ^ (s - 1) * f (x / y)) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        ring_nf
      have hconst :
          (∫ x : ℝ in Ioi (0 : ℝ), (g y / y) * ((x : ℂ) ^ (s - 1) * f (x / y)))
            = (g y / y) * (∫ x : ℝ in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * f (x / y)) := by
        simpa [μ0] using
          (MeasureTheory.integral_mul_left (μ := μ0) (r := (g y / y))
            (f := fun x : ℝ => (x : ℂ) ^ (s - 1) * f (x / y)))
      exact hreorder.trans hconst

    -- Scale the remaining integral using `mellin_comp_mul_right`.
    have hscale := mellin_comp_mul_right_one_div (f := f) (s := s) (y := y) hy'
    have hmul : ((1 / y : ℝ) : ℂ) ^ (-s) * ((y : ℂ)⁻¹) = (y : ℂ) ^ (s - 1) :=
      one_div_cpow_neg_mul_inv_of_pos (y := y) hy' s

    calc
      (∫ x : ℝ in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y))
          = (g y / y) * (((1 / y : ℝ) : ℂ) ^ (-s) * mellin f s) := by
              simp [hpull, hscale, mul_assoc]
      _ = ((g y / (y : ℂ)) * ((1 / y : ℝ) : ℂ) ^ (-s)) * mellin f s := by
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ = (g y * (((1 / y : ℝ) : ℂ) ^ (-s) * ((y : ℂ)⁻¹))) * mellin f s := by
            -- regroup to match `hmul`
            ring_nf
      _ = (g y * (y : ℂ) ^ (s - 1)) * mellin f s := by
            exact congrArg (fun t => (g y * t) * mellin f s) hmul
      _ = (y : ℂ) ^ (s - 1) * g y * mellin f s := by
            ring_nf

  have hOuter :
      (∫ y : ℝ in Ioi (0 : ℝ),
        (∫ x : ℝ in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * (f (x / y) * g y / y)))
        = ∫ y : ℝ in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * g y * mellin f s := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hInner
  rw [hOuter]

  -- Pull out the constant `mellin f s`.
  have hpullOut :
      (∫ y : ℝ in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * g y * mellin f s)
        = (∫ y : ℝ in Ioi (0 : ℝ), (y : ℂ) ^ (s - 1) * g y) * mellin f s := by
    simpa [μ0, mul_assoc] using
      (MeasureTheory.integral_mul_right (μ := μ0) (r := (mellin f s))
        (f := fun y : ℝ => (y : ℂ) ^ (s - 1) * g y))
  rw [hpullOut]

  -- Rewrite `mellin g s` and commute factors in `ℂ`.
  simp [mellin, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

end MulConv

end ExplicitFormula
end RiemannRecognitionGeometry
