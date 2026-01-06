import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.RingTheory.SimpleRing.Principal
import Riemann.Mathlib.Analysis.Complex.Cartan
/-!
# Poisson Kernel for the Unit Disc

This file develops the theory of the Poisson kernel and Poisson integral
for harmonic functions on the unit disc.

## Main definitions

* `Complex.poissonKernel` : The Poisson kernel P_r(θ - φ)
* `Complex.poissonIntegral` : The Poisson integral of a function

## Main results

* `Complex.poissonKernel_pos` : The Poisson kernel is positive for r < 1
* `Complex.poissonKernel_max` : Upper bound (1+r)/(1-r)
* `Complex.poissonKernel_min` : Lower bound (1-r)/(1+r)

## References

* Stein, E.M., Shakarchi, R., "Complex Analysis", Chapter 5
-/

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped UnitDisc ENNReal NNReal Real

namespace Complex

/-! ### Poisson kernel infrastructure -/



/-- The Poisson kernel for the unit disc: P_r(θ) = (1 - r²) / (1 - 2r cos θ + r²).
This is the fundamental kernel for harmonic function theory on the disc. -/
def poissonKernel (r : ℝ) (θ φ : ℝ) : ℝ :=
  (1 - r^2) / (1 - 2*r*Real.cos (θ - φ) + r^2)

/-- Squared-norm identity for points on the unit circle:
`‖exp(θ i) - r‖^2 = 1 - 2r cos θ + r^2`. -/
lemma norm_exp_ofReal_mul_I_sub_ofReal_sq (r θ : ℝ) :
    ‖Complex.exp (θ * Complex.I) - (r : ℂ)‖ ^ 2 = 1 - 2 * r * Real.cos θ + r ^ 2 := by
  -- Rewrite `exp(θ i) - r` as `(cos θ - r) + (sin θ) i` and compute the squared norm.
  have hw :
      Complex.exp (θ * Complex.I) - (r : ℂ)
        = ((Real.cos θ - r : ℝ) : ℂ) + (Real.sin θ : ℝ) * Complex.I := by
    -- Use `exp_mul_I` and then rewrite complex `cos`/`sin` at real inputs back to `Real.cos`/`Real.sin`.
    calc
      Complex.exp (θ * Complex.I) - (r : ℂ)
          = (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) - (r : ℂ) := by
              simp [Complex.exp_mul_I]
      _ = ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) - (r : ℂ) := by
              -- `cos (θ:ℂ) = (Real.cos θ : ℂ)`, similarly for `sin`.
              rw [← Complex.ofReal_cos θ, ← Complex.ofReal_sin θ]
      _ = ((Real.cos θ - r : ℝ) : ℂ) + (Real.sin θ : ℝ) * Complex.I := by
              push_cast
              ring
  have hsq :
      ‖Complex.exp (θ * Complex.I) - (r : ℂ)‖ ^ 2
        = (Real.cos θ - r) ^ 2 + (Real.sin θ) ^ 2 := by
    have hnonneg : 0 ≤ (Real.cos θ - r) ^ 2 + (Real.sin θ) ^ 2 := by nlinarith
    -- `simp` needs the nonneg proof to rewrite `((√a)^2)`.
    rw [hw, Complex.norm_add_mul_I]
    simp only [pow_two]
    ring_nf; grind
  have htrig : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  -- Finish using `sin^2 + cos^2 = 1`.
  nlinarith [hsq, htrig]

/-- The denominator of the Poisson kernel is always positive for r < 1. -/
lemma poissonKernel_denom_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    0 < 1 - 2*r*Real.cos (θ - φ) + r^2 := by
  have hcos : -1 ≤ Real.cos (θ - φ) ∧ Real.cos (θ - φ) ≤ 1 :=
    ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  nlinarith

/-- The Poisson kernel is non-negative for r < 1. -/
lemma poissonKernel_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    0 ≤ poissonKernel r θ φ := by
  unfold poissonKernel
  have h_num : 0 ≤ 1 - r^2 := by nlinarith
  exact div_nonneg h_num (le_of_lt (poissonKernel_denom_pos hr0 hr1 θ φ))

/-- The Poisson kernel is positive for 0 ≤ r < 1. -/
lemma poissonKernel_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    0 < poissonKernel r θ φ := by
  unfold poissonKernel
  have h_num : 0 < 1 - r^2 := by nlinarith
  exact div_pos h_num (poissonKernel_denom_pos hr0 hr1 θ φ)

/-- The Poisson kernel achieves its maximum: P_r(θ) ≤ (1+r)/(1-r). -/
lemma poissonKernel_max {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    poissonKernel r θ φ ≤ (1 + r) / (1 - r) := by
  have hnum_nonneg : 0 ≤ 1 - r ^ 2 := by
    have : r ^ 2 ≤ 1 := by nlinarith [hr0, hr1]
    exact sub_nonneg.mpr this
  have hden_pos :
      0 < 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 :=
    poissonKernel_denom_pos hr0 hr1 θ φ
  have hden_ge :
      (1 - r) ^ 2 ≤ 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 := by
    have hdecomp :
        1 - 2 * r * Real.cos (θ - φ) + r ^ 2
          = (1 - r) ^ 2 + 2 * r * (1 - Real.cos (θ - φ)) := by ring
    have hnonneg :
        0 ≤ 2 * r * (1 - Real.cos (θ - φ)) := by
      refine mul_nonneg (mul_nonneg (by norm_num) hr0)
        (sub_nonneg.mpr (Real.cos_le_one _))
    have :
        (1 - r) ^ 2 ≤
          (1 - r) ^ 2 + 2 * r * (1 - Real.cos (θ - φ)) :=
      le_add_of_nonneg_right hnonneg
    simpa [hdecomp] using this
  have hrec_le :
      1 / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2)
        ≤ 1 / (1 - r) ^ 2 := by
    have hpos : 0 < (1 - r) ^ 2 := by
      have h : 0 < 1 - r := sub_pos.mpr hr1
      simpa [pow_two] using sq_pos_of_pos h
    exact one_div_le_one_div_of_le hpos hden_ge
  have hineq :
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2)
        ≤ (1 - r ^ 2) / (1 - r) ^ 2 := by
    have : (1 - r ^ 2) * (1 / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2))
        ≤ (1 - r ^ 2) * (1 / (1 - r) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hrec_le hnum_nonneg
    simpa [poissonKernel] using this
  have hfrac_eq :
      (1 - r ^ 2) / (1 - r) ^ 2 = (1 + r) / (1 - r) := by
    have hne : 1 - r ≠ 0 := sub_ne_zero.mpr hr1.ne'
    have hfactor : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    have hpow : (1 - r) ^ 2 = (1 - r) * (1 - r) := by simp [pow_two]
    simp_rw [hfactor, hpow]
    grind
  simpa [poissonKernel, hfrac_eq] using hineq

/-- The Poisson kernel achieves its minimum: (1-r)/(1+r) ≤ P_r(θ). -/
lemma poissonKernel_min {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ φ : ℝ) :
    (1 - r) / (1 + r) ≤ poissonKernel r θ φ := by
  have hnum_nonneg : 0 ≤ 1 - r ^ 2 := by
    have : r ^ 2 ≤ 1 := by nlinarith [hr0, hr1]
    exact sub_nonneg.mpr this
  have hden_pos :
      0 < 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 :=
    poissonKernel_denom_pos hr0 hr1 θ φ
  have hden_le :
      1 - 2 * r * Real.cos (θ - φ) + r ^ 2 ≤ (1 + r) ^ 2 := by
    have hdecomp :
        1 - 2 * r * Real.cos (θ - φ) + r ^ 2 =
          (1 + r) ^ 2 - 2 * r * (1 + Real.cos (θ - φ)) := by ring
    have hnonneg :
        0 ≤ 2 * r * (1 + Real.cos (θ - φ)) := by
      refine mul_nonneg (mul_nonneg (by norm_num) hr0)
        (by linarith [Real.neg_one_le_cos (θ - φ)])
    have :
        (1 + r) ^ 2 - 2 * r * (1 + Real.cos (θ - φ))
          ≤ (1 + r) ^ 2 := by
      exact sub_le_self _ hnonneg
    simpa [hdecomp] using this
  have hrec_ge :
      1 / (1 + r) ^ 2 ≤
        1 / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2) := by
    have hpos :
        0 < 1 - 2 * r * Real.cos (θ - φ) + r ^ 2 :=
      poissonKernel_denom_pos hr0 hr1 θ φ
    exact one_div_le_one_div_of_le hpos hden_le
  have hineq :
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (θ - φ) + r ^ 2)
        ≥ (1 - r ^ 2) / (1 + r) ^ 2 := by
    have : (1 - r ^ 2) * (1 / (1 + r) ^ 2)
        ≤ (1 - r ^ 2) * (1 /
            (1 - 2 * r * Real.cos (θ - φ) + r ^ 2)) := by
      refine mul_le_mul_of_nonneg_left hrec_ge hnum_nonneg
    simpa [poissonKernel] using this
  have hfrac_eq :
      (1 - r ^ 2) / (1 + r) ^ 2 = (1 - r) / (1 + r) := by
    have hne : (1 + r) ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hr0)
    have hfactor : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    simp [pow_two]
    grind
  simpa [poissonKernel, hfrac_eq] using hineq

/-- The Poisson integral of a function. -/
def poissonIntegral (u : ℝ → ℝ) (r : ℝ) (θ : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * u φ

/-- The Poisson kernel is continuous in all variables. -/
lemma poissonKernel_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun p : ℝ × ℝ => poissonKernel r p.1 p.2) := by
  unfold poissonKernel
  refine Continuous.div continuous_const ?_ ?_
  · have h1 : Continuous (fun p : ℝ × ℝ => 1 - 2*r*cos (p.1 - p.2) + r^2) := by
      continuity
    continuity
  · intro p
    exact (poissonKernel_denom_pos hr0 hr1 p.1 p.2).ne'

/-!
### A note on the Poisson kernel integral

In classical analysis one can compute integrals of the form
`\(\int_0^{2\pi} \frac{d\varphi}{a - b\cos\varphi}\)` explicitly via the Weierstrass substitution.

For the purposes of Hardy space theory we only need the special case that the Poisson kernel has
total mass `2π`.  We prove that directly below using complex contour integration on the unit circle,
avoiding improper integrals.
-/

/-- The integral of the Poisson kernel over the boundary does not depend on the angular shift. -/
lemma poissonKernel_integral_eq_base {r : ℝ} (θ : ℝ) :
    ∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ =
      ∫ φ in (0 : ℝ)..2 * π, poissonKernel r 0 φ := by
  let kernel : ℝ → ℝ :=
    fun x => (1 - r ^ 2) /
      (1 - 2 * r * Real.cos x + r ^ 2)
  have hker :
      ∀ θ φ, poissonKernel r θ φ = kernel (θ - φ) := by
    intro θ' φ'
    simp [kernel, poissonKernel, sub_eq_add_neg]
  have hperiodic : Function.Periodic kernel (2 * π) := by
    intro x
    simp [kernel]
  have h_sub :
      (∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ) =
        ∫ φ in (θ - 2 * π)..θ, kernel φ := by
    have :=
      intervalIntegral.integral_comp_sub_left
        (f := kernel) (a := (0 : ℝ)) (b := 2 * π) (d := θ)
    simp [hker]
  have h_periodic_int :
      ∫ φ in (θ - 2 * π)..θ, kernel φ =
        ∫ φ in (0 : ℝ)..2 * π, kernel φ := by
    simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hperiodic.intervalIntegral_add_eq (t := θ - 2 * π) (s := 0)
  aesop

/-- The Poisson kernel integrates to 2π over [0, 2π].

This fundamental result follows from the Weierstrass substitution formula for
integrals of the form ∫ 1/(a - b cos φ) dφ. The Poisson kernel
P_r(φ) = (1 - r²)/(1 - 2r cos φ + r²) can be rewritten as (1 - r²) · 1/((1+r²) - 2r cos φ),
and applying the formula with a = 1 + r² and b = 2r gives the result.

Note: a² - b² = (1+r²)² - 4r² = (1-r²)², so √(a² - b²) = 1 - r². -/
lemma poissonKernel_integral_eq_two_pi {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ φ in (0 : ℝ)..2 * π, poissonKernel r 0 φ = 2 * π := by
  by_cases hr : r = 0
  · -- At r = 0, the kernel is identically 1
    simp only [hr, poissonKernel, pow_two, mul_zero, sub_zero, zero_mul, add_zero, div_one]
    simp
  ·
    -- For `0 < r < 1`, compute the integral by converting to a contour integral on the unit circle.
    have hr_pos : 0 < r := hr0.lt_of_ne' hr
    have hr_lt_one : r < 1 := hr1

    -- Let `z = exp(θ i)` be the unit-circle parametrization.
    -- We use the identity
    -- `poissonKernel r 0 θ = (1 - r^2) / ‖exp(θ i) - r‖^2`
    -- and the change of variables `z = exp(θ i)` to rewrite the integral as a circle integral.
    have hden (θ : ℝ) :
        (1 - 2 * r * Real.cos θ + r ^ 2)
          = ‖Complex.exp (θ * Complex.I) - (r : ℂ)‖ ^ 2 := by
      -- Rewrite `exp(θ i) - r` as `(cos θ - r) + (sin θ) i` and compute the squared norm.
      have hw :
          Complex.exp (θ * Complex.I) - (r : ℂ)
            = ((Real.cos θ - r : ℝ) : ℂ) + (Real.sin θ : ℝ) * Complex.I := by
        -- Use `exp_mul_I` and then rewrite complex `cos`/`sin` at real inputs back to `Real.cos`/`Real.sin`.
        calc
          Complex.exp (θ * Complex.I) - (r : ℂ)
              = (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) - (r : ℂ) := by
                  simp [Complex.exp_mul_I]
          _ = ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) - (r : ℂ) := by
                  -- `cos (θ:ℂ) = (Real.cos θ : ℂ)`, similarly for `sin`
                  rw [← Complex.ofReal_cos θ, ← Complex.ofReal_sin θ]
          _ = ((Real.cos θ - r : ℝ) : ℂ) + (Real.sin θ : ℝ) * Complex.I := by
                  push_cast
                  ring
      -- Use `‖x + y i‖ = √(x^2 + y^2)` and square both sides.
      have hsq :
          ‖Complex.exp (θ * Complex.I) - (r : ℂ)‖ ^ 2
            = (Real.cos θ - r) ^ 2 + (Real.sin θ) ^ 2 := by
        have hnonneg : 0 ≤ (Real.cos θ - r) ^ 2 + (Real.sin θ) ^ 2 := by nlinarith
        -- `simp` needs the nonneg proof to rewrite `((√a)^2)`.
        rw [hw, Complex.norm_add_mul_I]
        simp only [pow_two]
        ring_nf; grind
      -- Finish using `sin^2 + cos^2 = 1`.
      have htrig : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      -- Now `nlinarith` closes the algebra.
      nlinarith [hsq, htrig]
    -- Define the holomorphic integrand whose circle integral equals the real integral.
    let g : ℂ → ℂ :=
      fun z => ((1 - r ^ 2 : ℝ) : ℂ) / (Complex.I * (z - (r : ℂ)) * (1 - (r : ℂ) * z))

    have h_circle :
        (∫ θ in (0 : ℝ)..2 * π, (poissonKernel r 0 θ : ℂ)) =
          circleIntegral g 0 1 := by
      -- Unfold `circleIntegral` and show equality of integrands pointwise on `[0, 2π]`.
      simp [circleIntegral]
      refine intervalIntegral.integral_congr ?_
      intro θ hθ
      -- Put `z = exp(θ i)` on the unit circle.
      set z : ℂ := Complex.exp (θ * Complex.I)
      have hz0 : z ≠ 0 := by simp [z]
      have hz_norm : ‖z‖ = 1 := by simp [z]

      -- Key algebra on the unit circle: `z / ((z-r) * (1-rz)) = 1 / ‖z-r‖^2`.
      have hmul :
          (z - (r : ℂ)) * (1 - (r : ℂ) * z) = z * (‖z - (r : ℂ)‖ ^ 2 : ℂ) := by
        have hstar : star z = z⁻¹ := (Complex.inv_eq_conj hz_norm).symm
        have hz_mul_star : z * star z = (1 : ℂ) := by
          simp [hstar, hz0]
        have hz_mul_star' : z * (starRingEnd ℂ) z = (1 : ℂ) := by
          simpa using hz_mul_star
        have h1 : 1 - (r : ℂ) * z = z * (star z - (r : ℂ)) := by
          -- Prove the reverse direction (starting from the RHS) and then `symm`.
          have : z * (star z - (r : ℂ)) = 1 - (r : ℂ) * z := by
            simp [mul_sub, hz_mul_star', mul_comm]
          exact this.symm
        have hnorm :
            (z - (r : ℂ)) * (star z - (r : ℂ)) = (‖z - (r : ℂ)‖ ^ 2 : ℂ) := by
          -- `star (z - r) = star z - r` since `r` is real.
          simpa [star_sub, conj_ofReal] using (Complex.mul_conj' (z - (r : ℂ)))
        calc
          (z - (r : ℂ)) * (1 - (r : ℂ) * z)
              = (z - (r : ℂ)) * (z * (star z - (r : ℂ))) := by simp [h1]
          _ = z * ((z - (r : ℂ)) * (star z - (r : ℂ))) := by
              simp [mul_left_comm]
          _ = z * (‖z - (r : ℂ)‖ ^ 2 : ℂ) := by
              -- Avoid `simp` turning `z * a = z * b` into a disjunction; use `congrArg` instead.
              simpa using congrArg (fun t : ℂ => z * t) hnorm

      have hfrac :
          z / ((z - (r : ℂ)) * (1 - (r : ℂ) * z)) = (1 : ℂ) / (‖z - (r : ℂ)‖ ^ 2) := by
        calc
          z / ((z - (r : ℂ)) * (1 - (r : ℂ) * z))
              = z / (z * (‖z - (r : ℂ)‖ ^ 2 : ℂ)) := by simp [hmul]
          _ = z / z / (‖z - (r : ℂ)‖ ^ 2) := by simp [div_mul_eq_div_div]
          _ = (1 : ℂ) / (‖z - (r : ℂ)‖ ^ 2) := by simp [hz0]

      have hden' : (1 - 2 * r * Real.cos θ + r ^ 2) = ‖z - (r : ℂ)‖ ^ 2 := by
        simpa [z] using hden θ

      -- Now the desired integrand identity.
      have hLHS :
          (poissonKernel r 0 θ : ℂ) = ((1 - r ^ 2 : ℝ) : ℂ) / (‖z - (r : ℂ)‖ ^ 2) := by
        -- `poissonKernel r 0 θ = (1 - r²)/(1 - 2r cos θ + r²)`.
        simp only [poissonKernel]
        simp [hden']

      have hRHS :
          deriv (circleMap 0 1) θ • g (circleMap 0 1 θ)
            = ((1 - r ^ 2 : ℝ) : ℂ) / (‖z - (r : ℂ)‖ ^ 2) := by
        -- Use `circleMap 0 1 θ = exp(θ i) = z`.
        have hz : circleMap 0 1 θ = z := by simp [z, circleMap_zero]
        -- Cancel the `I` from `deriv circleMap` against the `I` in `g`,
        -- then use `hfrac` to turn the rational expression into `1/‖z-r‖²`.
        have hderiv : deriv (circleMap 0 1) θ = z * Complex.I := by
          simp [z, circleMap]
        calc
          deriv (circleMap 0 1) θ • g (circleMap 0 1 θ)
              = (z * Complex.I) * g z := by simp [smul_eq_mul, hz, hderiv]
          _ = ((1 - r ^ 2 : ℝ) : ℂ) * (z / ((z - (r : ℂ)) * (1 - (r : ℂ) * z))) := by
              -- unfold `g` and cancel the factor `I`
              simp only [g, div_eq_mul_inv]
              field_simp
          _ = ((1 - r ^ 2 : ℝ) : ℂ) * ((1 : ℂ) / (‖z - (r : ℂ)‖ ^ 2)) := by
              simp [hfrac]
          _ = ((1 - r ^ 2 : ℝ) : ℂ) / (‖z - (r : ℂ)‖ ^ 2) := by
              ring
      -- `simp [circleIntegral]` rewrites the integrand using `deriv_circleMap`,
      -- so we finish by translating `deriv (circleMap …) θ • …` to `circleMap … θ * I * …`.
      have hderiv :
          deriv (circleMap 0 1) θ • g (circleMap 0 1 θ)
            = (circleMap 0 1 θ) * I * g (circleMap 0 1 θ) := by
        simp [deriv_circleMap, smul_eq_mul, mul_assoc]
      exact (hLHS.trans hRHS.symm).trans hderiv

    -- Compute the circle integral of `g` by splitting into a principal part at `z = r`
    -- and a holomorphic part. The algebraic decomposition is valid on the unit circle
    -- (where the denominators are nonzero).
    have hg_decomp_sphere :
        EqOn g
          (fun z =>
            (-Complex.I) * ((z - (r : ℂ))⁻¹ + (r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
          (Metric.sphere (0 : ℂ) (1 : ℝ)) := by
      intro z hz
      have hz_norm : ‖z‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hz
      have hr_abs : |r| < (1 : ℝ) := by
        simpa [abs_of_nonneg hr0] using hr_lt_one
      have hr_norm_lt : ‖(r : ℂ)‖ < 1 := by
        simpa [Complex.norm_real] using hr_abs
      have hz_sub_ne : z - (r : ℂ) ≠ 0 := by
        intro hzr
        have : ‖z‖ = ‖(r : ℂ)‖ := by
          simp [sub_eq_zero.mp hzr]
        have : (1 : ℝ) < 1 := by
          have : ‖z‖ < 1 := by simpa [this] using hr_norm_lt
          simp [hz_norm] at this
        exact lt_irrefl _ this
      have hz_one_sub_ne : (1 - (r : ℂ) * z) ≠ 0 := by
        intro hz0'
        have hz1 : (r : ℂ) * z = 1 := (sub_eq_zero.mp hz0').symm
        have hnorm1 : ‖(r : ℂ) * z‖ = 1 := by simp [hz1]
        have hnormlt : ‖(r : ℂ) * z‖ < 1 := by
          -- `‖r*z‖ = ‖r‖ * ‖z‖ = ‖r‖ < 1`
          simpa [norm_mul, hz_norm] using hr_norm_lt
        exact lt_irrefl _ (hnorm1 ▸ hnormlt)
      -- Now the algebraic identity holds (no `grind` needed since denominators are nonzero).
      dsimp [g]
      -- Clear denominators.
      field_simp [hz_sub_ne, hz_one_sub_ne, Complex.I_ne_zero]
      -- Reduce powers of `I` and close by normalization.
      simp [Complex.I_sq]
      -- There can still be a residual `(1 - r*z)⁻¹`; clear it using the non-vanishing proof on the sphere.
      field_simp [hz_one_sub_ne]
      ring_nf

    have hI : circleIntegral g 0 1 = (2 * π : ℂ) := by
      -- Use the decomposition and compute the two terms separately.
      have hcongr :
          circleIntegral g 0 1 =
            circleIntegral
              (fun z =>
                (-Complex.I) * ((z - (r : ℂ))⁻¹ + (r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
              0 1 := by
        -- We can replace the integrand by an equal one on the circle.
        refine circleIntegral.integral_congr (c := (0 : ℂ)) (R := (1 : ℝ)) (hR := by norm_num) ?_
        -- unfold `g` so the left side matches the expected explicit integrand
        simpa [g, sub_eq_add_neg, pow_two] using hg_decomp_sphere
      -- Work with the decomposed integrand.
      rw [hcongr]
      have hr_mem : (r : ℂ) ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
        have : |r| < (1 : ℝ) := by simpa [abs_of_nonneg hr0] using hr_lt_one
        simpa [Metric.mem_ball, dist_zero_right, Complex.norm_real] using this
      -- First term: integral of `(z - r)⁻¹` is `2π i`.
      have h_main :
          circleIntegral (fun z => (-Complex.I) * (z - (r : ℂ))⁻¹) 0 1 = (2 * π : ℂ) := by
        -- Pull out the constant `-I` and use `∮ (z-r)⁻¹ = 2π i`.
        calc
          circleIntegral (fun z => (-Complex.I) * (z - (r : ℂ))⁻¹) 0 1
              = (-Complex.I) * circleIntegral (fun z => (z - (r : ℂ))⁻¹) 0 1 := by
                  simpa [circleIntegral] using
                    (circleIntegral.integral_const_mul (-Complex.I) (fun z => (z - (r : ℂ))⁻¹) 0 1)
          _ = (-Complex.I) * (2 * π * Complex.I : ℂ) := by
                  simp [circleIntegral.integral_sub_inv_of_mem_ball hr_mem]
          _ = (2 * π : ℂ) := by
                  ring_nf; aesop
      -- Second term: the integrand is holomorphic on a neighborhood of the closed unit disk, so its circle integral is zero.
      have h_aux :
          circleIntegral (fun z => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹)) 0 1 = 0 := by
        -- We show this integrand is a derivative on the circle, hence integrates to zero.
        have hR : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
        -- Choose a radius `R > 1` with `R < 1 / r` so that `1 - r z ≠ 0` on `ball 0 R`.
        let R : ℝ := (1 + (1 / r)) / 2
        have hR1 : 1 < R := by
          have h1div : (1 : ℝ) < 1 / r := one_lt_one_div hr_pos hr_lt_one
          dsimp [R]; linarith
        have hRlt : R < 1 / r := by
          have h1div : (1 : ℝ) < 1 / r := one_lt_one_div hr_pos hr_lt_one
          dsimp [R]; linarith
        have hne : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) R → (1 - (r : ℂ) * z) ≠ 0 := by
          intro z hz
          have hz' : ‖z‖ < R := by
            simpa [Metric.mem_ball, dist_zero_right] using hz
          have hnorm_lt : ‖(r : ℂ) * z‖ < 1 := by
            -- `‖r*z‖ = ‖r‖ * ‖z‖ < r * R < 1`
            have hrR : r * R < 1 := by
              have : r * R < r * (1 / r) := mul_lt_mul_of_pos_left hRlt hr_pos
              -- `r * (1 / r) = 1` since `r ≠ 0`
              simpa [one_div, hr_pos.ne'] using this
            have hrnorm : ‖(r : ℂ)‖ = r := by
              simp [Complex.norm_real, abs_of_nonneg hr0]
            have h1 : ‖(r : ℂ)‖ * ‖z‖ < ‖(r : ℂ)‖ * R := mul_lt_mul_of_pos_left hz' (by
              -- `‖(r:ℂ)‖ = r > 0`
              simp only [hrnorm]
              exact hr_pos)
            have h2 : ‖(r : ℂ)‖ * ‖z‖ < r * R := by rw [hrnorm] at h1; exact lt_of_eq_of_lt (congrFun (congrArg HMul.hMul hrnorm) ‖z‖) h1
            -- convert to `‖(r:ℂ) * z‖ < 1`
            have h3 : ‖(r : ℂ) * z‖ < r * R := by rw [norm_mul]; exact h2
            exact h3.trans hrR
          -- If `1 - r*z = 0` then `‖r*z‖ = 1`, contradiction.
          intro hzero
          have hz1 : (r : ℂ) * z = 1 := (sub_eq_zero.mp hzero).symm
          have hEq : ‖(r : ℂ) * z‖ = 1 := by simp [hz1]
          linarith [hEq, hnorm_lt]
        -- The function is differentiable on `ball 0 R`.
        have hdiff :
            DifferentiableOn ℂ (fun z : ℂ => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
              (Metric.ball (0 : ℂ) R) := by
          intro z hz
          have hz_ne : (1 - (r : ℂ) * z) ≠ 0 := hne z hz
          -- Prove differentiability explicitly (so we can feed `hz_ne` to the inversion lemma).
          have haff : DifferentiableAt ℂ (fun w : ℂ => 1 - (r : ℂ) * w) z := by
            fun_prop
          have hinv : DifferentiableAt ℂ (fun w : ℂ => (1 - (r : ℂ) * w)⁻¹) z :=
            (haff.inv hz_ne)
          have hmul : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) * (1 - (r : ℂ) * w)⁻¹) z :=
            hinv.const_mul (r : ℂ)
          have hfinal :
              DifferentiableAt ℂ (fun w : ℂ => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * w)⁻¹)) z :=
            hmul.const_mul (-Complex.I)
          exact hfinal.differentiableWithinAt
        -- Obtain a primitive on the ball.
        have hexact : Complex.IsExactOn (fun z : ℂ => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
            (Metric.ball (0 : ℂ) R) :=
          (hdiff.isExactOn_ball)
        rcases hexact with ⟨F, hF⟩
        -- Restrict to the unit circle (which is contained in the ball since `1 < R`).
        have hF_circle : ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ),
            HasDerivWithinAt F ((-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹)) (Metric.sphere (0 : ℂ) (1 : ℝ)) z := by
          intro z hz
          have hz_ball : z ∈ Metric.ball (0 : ℂ) R := by
            have : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
            have : ‖z‖ < R := by simpa [this] using hR1
            simpa [Metric.mem_ball, dist_zero_right] using this
          exact (hF z hz_ball).hasDerivWithinAt
        -- Apply the circle integral lemma for derivatives.
        simpa [circleIntegral, mul_assoc, mul_left_comm, mul_comm] using
          (circleIntegral.integral_eq_zero_of_hasDerivWithinAt (E := ℂ) (f := F)
            (f' := fun z => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
            (c := (0 : ℂ)) (R := (1 : ℝ)) hR hF_circle)
      -- Combine the two parts.
      -- Use linearity of the circle integral (no `linarith`: these are complex-valued integrals).
      have hf :
          CircleIntegrable (fun z => (-Complex.I) * (z - (r : ℂ))⁻¹) (0 : ℂ) (1 : ℝ) := by
        -- `(z - r)⁻¹` is integrable on the circle since `r` is in the open unit ball.
        have hr_not_sphere : (r : ℂ) ∉ Metric.sphere (0 : ℂ) (1 : ℝ) := by
          intro hr_s
          have hr_eq : ‖(r : ℂ)‖ = 1 := by
            simpa [Metric.mem_sphere, dist_zero_right] using hr_s
          have hr_lt : ‖(r : ℂ)‖ < 1 := by
            simpa [Metric.mem_ball, dist_zero_right] using hr_mem
          exact (lt_irrefl (1 : ℝ)) (hr_eq ▸ hr_lt)
        have hbase :
            CircleIntegrable (fun z : ℂ => (z - (r : ℂ))⁻¹) (0 : ℂ) (1 : ℝ) := by
          -- use the characterization lemma
          simpa using (circleIntegrable_sub_inv_iff (c := (0 : ℂ)) (w := (r : ℂ)) (R := (1 : ℝ))).2
            (Or.inr (by simpa using hr_not_sphere))
        -- multiply by the constant `-I`
        simpa [smul_eq_mul] using (CircleIntegrable.const_smul (a := (-Complex.I)) hbase)

      have hg :
          CircleIntegrable (fun z => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹)) (0 : ℂ) (1 : ℝ) := by
        -- This function is continuous on the unit circle (denominator never vanishes as `‖r‖ < 1`).
        have hcont :
            ContinuousOn (fun z : ℂ => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
              (Metric.sphere (0 : ℂ) (1 : ℝ)) := by
          have hden0 :
              ∀ z ∈ Metric.sphere (0 : ℂ) (1 : ℝ), (1 - (r : ℂ) * z) ≠ 0 := by
            intro z hz
            -- If `1 - r*z = 0`, then `‖r*z‖ = 1` but also `‖r*z‖ = ‖r‖ < 1`.
            have hz_norm : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
            have hr_lt : ‖(r : ℂ)‖ < 1 := by
              simpa [Metric.mem_ball, dist_zero_right] using hr_mem
            intro hzero
            have hz1 : (r : ℂ) * z = 1 := (sub_eq_zero.mp hzero).symm
            have hnorm1 : ‖(r : ℂ) * z‖ = 1 := by simp [hz1]
            have hnormlt : ‖(r : ℂ) * z‖ < 1 := by simpa [norm_mul, hz_norm] using hr_lt
            exact (lt_irrefl (1 : ℝ)) (hnorm1 ▸ hnormlt)
          -- build continuity using `inv₀`
          have hinner :
              ContinuousOn (fun z : ℂ => (1 - (r : ℂ) * z)⁻¹) (Metric.sphere (0 : ℂ) (1 : ℝ)) := by
            exact (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).inv₀ hden0
          -- Build continuity without relying on `simpa` guessing the right normal form.
          have : ContinuousOn (fun z : ℂ => (r : ℂ) * (1 - (r : ℂ) * z)⁻¹) (Metric.sphere (0 : ℂ) (1 : ℝ)) :=
            continuousOn_const.mul hinner
          have : ContinuousOn (fun z : ℂ => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
              (Metric.sphere (0 : ℂ) (1 : ℝ)) :=
            continuousOn_const.mul this
          simpa [mul_assoc] using this
        exact hcont.circleIntegrable (by norm_num)

      have hsplit :
          (fun z =>
              (-Complex.I) * ((z - (r : ℂ))⁻¹ + (r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
            =
          (fun z =>
              (-Complex.I) * (z - (r : ℂ))⁻¹ + (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹)) := by
        funext z; ring

      -- Now add the two known integrals.
      have hsplit_int :
          circleIntegral
              (fun z => (-Complex.I) * ((z - (r : ℂ))⁻¹ + (r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
              0 1
            =
          circleIntegral
              (fun z =>
                (-Complex.I) * (z - (r : ℂ))⁻¹ + (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
              0 1 := by
        simpa using congrArg (fun f : (ℂ → ℂ) => circleIntegral f 0 1) hsplit
      calc
        circleIntegral (fun z => (-Complex.I) * ((z - (r : ℂ))⁻¹ + (r : ℂ) * (1 - (r : ℂ) * z)⁻¹)) 0 1
            = circleIntegral
                (fun z =>
                  (-Complex.I) * (z - (r : ℂ))⁻¹ + (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
                0 1 := hsplit_int
        _ = circleIntegral (fun z => (-Complex.I) * (z - (r : ℂ))⁻¹) 0 1
              + circleIntegral (fun z => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹)) 0 1 := by
                simpa using (circleIntegral.integral_add (c := (0 : ℂ)) (R := (1 : ℝ)) hf hg)
        _ = (2 * π : ℂ) := by
              -- rewrite by the two computed integrals and simplify
              rw [h_main, h_aux]
              simp

    -- Finish: translate back to the real integral.
    have hC : (∫ θ in (0 : ℝ)..2 * π, (poissonKernel r 0 θ : ℂ)) = (2 * π : ℂ) :=
      h_circle.trans hI
    -- Convert the complex statement to a real one.
    -- First rewrite the LHS as `↑(∫ ... poissonKernel ...)`.
    rw [intervalIntegral.integral_ofReal] at hC
    -- Now take real parts: `re (↑a) = a`.
    have hre : (∫ θ in (0 : ℝ)..2 * π, poissonKernel r 0 θ) = 2 * π := by
      simpa using congrArg Complex.re hC
    exact hre

/-- The Poisson integral of a constant is that constant. -/
lemma poissonIntegral_const {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (c : ℝ) (θ : ℝ) :
    poissonIntegral (fun _ => c) r θ = c := by
  unfold poissonIntegral
  have h1 : ∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * c =
      c * ∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext φ; ring
  simp only [h1]
  -- Use the shift-invariance to reduce to θ = 0, then apply the integral formula
  rw [poissonKernel_integral_eq_base θ, poissonKernel_integral_eq_two_pi hr0 hr1]
  -- Now we have (2π)⁻¹ * (c * 2π) = c
  field_simp [Real.pi_ne_zero]

/-- A coarse bound on the Poisson integral in terms of the \(L^1\) norm of the boundary data.

This is the inequality
\[
  |P_r u(\theta)| \le \frac{1+r}{1-r}\cdot \frac{1}{2\pi}\int_0^{2\pi} |u(\varphi)|\,d\varphi,
\]
using the pointwise bound `poissonKernel_max`.

We state it under a global continuity assumption on `u` to avoid integrability bookkeeping; this is
exactly what we need when `u` is built from continuous boundary data like `log ‖f‖`.
-/
lemma abs_poissonIntegral_le_poissonKernel_max_mul_intervalIntegral_abs
    {u : ℝ → ℝ} (hu : Continuous u) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    |poissonIntegral u r θ|
      ≤ ((1 + r) / (1 - r)) * ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, |u φ|) := by
  -- Pull out the nonnegative scalar `(2π)⁻¹`.
  have h0 : (0 : ℝ) ≤ 2 * π := by
    simpa [two_mul, mul_assoc] using (Real.two_pi_pos.le)
  have hInv : 0 ≤ (2 * π : ℝ)⁻¹ := inv_nonneg.mpr h0

  -- Interval integrability of the relevant integrands follows from continuity.
  have hInt_uabs : IntervalIntegrable (fun φ : ℝ => |u φ|) volume (0 : ℝ) (2 * π) :=
    (continuous_abs.comp hu).intervalIntegrable 0 (2 * π)
  have hInt_pk_uabs :
      IntervalIntegrable (fun φ : ℝ => poissonKernel r θ φ * |u φ|) volume (0 : ℝ) (2 * π) := by
    have hcont_pk : Continuous fun φ : ℝ => poissonKernel r θ φ := by
      -- `poissonKernel` is smooth on `[0, 2π]` for fixed `r,θ` (no singularities for `r < 1`).
      -- We use the explicit continuity lemma already in this file.
      have h2 : Continuous (fun p : ℝ × ℝ => poissonKernel r p.1 p.2) :=
        poissonKernel_continuous (r := r) hr0 hr1
      -- specialize the continuous function to the slice `(θ, φ)`
      simpa [Function.uncurry] using (h2.comp (continuous_const.prodMk continuous_id))
    have hcont : Continuous fun φ : ℝ => poissonKernel r θ φ * |u φ| :=
      hcont_pk.mul (continuous_abs.comp hu)
    exact hcont.intervalIntegrable 0 (2 * π)
  have hInt_pk_u :
      IntervalIntegrable (fun φ : ℝ => poissonKernel r θ φ * u φ) volume (0 : ℝ) (2 * π) := by
    have hcont_pk : Continuous fun φ : ℝ => poissonKernel r θ φ := by
      have h2 : Continuous (fun p : ℝ × ℝ => poissonKernel r p.1 p.2) :=
        poissonKernel_continuous (r := r) hr0 hr1
      simpa [Function.uncurry] using (h2.comp (continuous_const.prodMk continuous_id))
    have hcont : Continuous fun φ : ℝ => poissonKernel r θ φ * u φ := hcont_pk.mul hu
    exact hcont.intervalIntegrable 0 (2 * π)

  -- Start from the definition and use `|∫ f| ≤ ∫ |f|`.
  unfold poissonIntegral
  have h_abs_int :
      |∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * u φ|
        ≤ ∫ φ in (0 : ℝ)..2 * π, |poissonKernel r θ φ * u φ| :=
    intervalIntegral.abs_integral_le_integral_abs (a := (0 : ℝ)) (b := 2 * π) h0

  -- Pointwise: `|P*u| = P*|u|` since `P ≥ 0`.
  have h_abs_point :
      (fun φ : ℝ => |poissonKernel r θ φ * u φ|)
        = fun φ : ℝ => poissonKernel r θ φ * |u φ| := by
    funext φ
    have hPk_nonneg : 0 ≤ poissonKernel r θ φ := poissonKernel_nonneg (r := r) hr0 hr1 θ φ
    simp [abs_mul, abs_of_nonneg hPk_nonneg]

  -- Bound the integral of `P*|u|` by pulling out the sup bound on `P`.
  have h_pk_le :
      ∀ φ ∈ Set.Icc (0 : ℝ) (2 * π),
        poissonKernel r θ φ * |u φ| ≤ ((1 + r) / (1 - r)) * |u φ| := by
    intro φ hφ
    have hk : poissonKernel r θ φ ≤ (1 + r) / (1 - r) :=
      poissonKernel_max (r := r) hr0 hr1 θ φ
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)

  have h_int_le :
      (∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * |u φ|)
        ≤ ∫ φ in (0 : ℝ)..2 * π, ((1 + r) / (1 - r)) * |u φ| := by
    refine intervalIntegral.integral_mono_on h0 hInt_pk_uabs ?_ ?_
    · -- RHS integrable
      have hcont : Continuous fun φ : ℝ => ((1 + r) / (1 - r)) * |u φ| :=
        continuous_const.mul (continuous_abs.comp hu)
      exact hcont.intervalIntegrable 0 (2 * π)
    · intro φ hφ
      exact h_pk_le φ hφ

  -- Put everything together and simplify constants.
  have h_main :
      |(2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * u φ|
        ≤ (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, ((1 + r) / (1 - r)) * |u φ| := by
    -- multiply the `|∫|` inequality by the nonnegative scalar `(2π)⁻¹`
    have h_abs_point' : ∀ φ, |poissonKernel r θ φ| * |u φ| = poissonKernel r θ φ * |u φ| := by
      intro φ
      have hPk_nonneg : 0 ≤ poissonKernel r θ φ := poissonKernel_nonneg (r := r) hr0 hr1 θ φ
      simp [abs_of_nonneg hPk_nonneg]
    have h_abs_int' : |∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * u φ|
        ≤ ∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * |u φ| := by
      calc |∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * u φ|
          ≤ ∫ φ in (0 : ℝ)..2 * π, |poissonKernel r θ φ * u φ| := h_abs_int
        _ = ∫ φ in (0 : ℝ)..2 * π, |poissonKernel r θ φ| * |u φ| := by simp [abs_mul]
        _ = ∫ φ in (0 : ℝ)..2 * π, poissonKernel r θ φ * |u φ| := by simp [h_abs_point']
    have :=
      mul_le_mul_of_nonneg_left
        (h_abs_int'.trans h_int_le)
        hInv
    -- and rewrite `|a*b|` with `a ≥ 0`
    have hPi_pos : (0 : ℝ) < π := Real.pi_pos
    simpa [abs_mul, abs_of_nonneg hInv, abs_of_pos hPi_pos, mul_assoc] using this

  -- Factor the constant `((1+r)/(1-r))` out of the RHS integral.
  have h_const :
      (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, ((1 + r) / (1 - r)) * |u φ|
        = ((1 + r) / (1 - r)) * ((2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, |u φ|) := by
    -- pull the constant out of the interval integral, then commute scalars
    rw [intervalIntegral.integral_const_mul]
    ring

  -- Finish.
  simpa [h_const, mul_assoc, mul_left_comm, mul_comm] using h_main

end Complex

/-! ## Unit Disc formulation using `𝔻`

This section provides an alternative formulation using the typed unit disc `𝔻 = UnitDisc`
from Mathlib. The normalization includes the `1/(2π)` factor.
-/

namespace Complex.UnitDisc

open MeasureTheory Complex
open scoped UnitDisc MeasureTheory

/-- The Poisson kernel for the unit disk, normalized by `1/(2π)`.

For a point `z` in the unit disk `𝔻` and a boundary point `e^{iθ}`, this gives:
P(z, e^{iθ}) = (1 - ‖z‖²) / (2π · ‖e^{iθ} - z‖²)

The normalization ensures that `∫ θ in [0, 2π], P(z, e^{iθ}) dθ = 1` for all `z ∈ 𝔻`.

This kernel appears in the Poisson integral formula for harmonic functions on the disk. -/
def poissonKernelNormalized (z : 𝔻) (θ : ℝ) : ℝ :=
  (1 - ‖(z : ℂ)‖ ^ 2) / ((2 * Real.pi) * ‖Complex.exp (θ * Complex.I) - (z : ℂ)‖ ^ 2)

@[simp]
theorem poissonKernelNormalized_zero (θ : ℝ) :
    poissonKernelNormalized 0 θ = 1 / (2 * Real.pi) := by
  simp [poissonKernelNormalized, UnitDisc.coe_zero]

theorem poissonKernelNormalized_nonneg (z : 𝔻) (θ : ℝ) :
    0 ≤ poissonKernelNormalized z θ := by
  apply div_nonneg
  · have h : ‖(z : ℂ)‖ < 1 := z.norm_lt_one
    have : ‖(z : ℂ)‖ ^ 2 < 1 := by aesop
    linarith
  · positivity

/-- A function `F : ℂ → ℂ` has a Poisson representation on the unit disk if:
1. It is analytic on the open unit disk,
2. The Poisson integral is integrable for each point in the disk, and
3. The real part of `F` equals its Poisson integral representation.

This structure packages the data needed for harmonic extension and Hardy space theory. -/
structure HasDiskPoissonRepresentation (F : ℂ → ℂ) : Prop where
  /-- `F` is analytic on the open unit disk -/
  analytic : AnalyticOn ℂ F {z : ℂ | ‖z‖ < 1}
  /-- The Poisson integrand is integrable for each point in the disk -/
  integrable (z : 𝔻) :
    IntegrableOn (fun θ : ℝ => (F (Circle.exp θ)).re * poissonKernelNormalized z θ)
                 (Set.Icc 0 (2 * Real.pi))
                 volume
  /-- The real part satisfies the Poisson integral formula -/
  re_eq (z : 𝔻) :
    (F z).re =
      ∫ θ in Set.Icc 0 (2 * Real.pi),
        (F (Circle.exp θ)).re * poissonKernelNormalized z θ ∂volume

/-- Constructor for `HasDiskPoissonRepresentation` from explicit data.

This is a convenience lemma that constructs the structure directly from its three components.
It can be useful when the components are already available as hypotheses. -/
lemma hasDiskPoissonRepresentation_of_data
    {F : ℂ → ℂ}
    (hA : AnalyticOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hI : ∀ z : 𝔻,
            IntegrableOn (fun θ : ℝ => (F (Circle.exp θ)).re * poissonKernelNormalized z θ)
                         (Set.Icc 0 (2 * Real.pi))
                         volume)
    (hEq : ∀ z : 𝔻,
            (F z).re =
              ∫ θ in Set.Icc 0 (2 * Real.pi),
                (F (Circle.exp θ)).re * poissonKernelNormalized z θ ∂volume) :
    HasDiskPoissonRepresentation F :=
  ⟨hA, hI, hEq⟩

/-- Convert between the normalized and unnormalized Poisson kernels. -/
lemma poissonKernelNormalized_eq_poissonKernel_div (z : 𝔻) (θ : ℝ) :
    poissonKernelNormalized z θ =
      (1 / (2 * Real.pi)) * ((1 - ‖(z : ℂ)‖ ^ 2) / ‖Complex.exp (θ * Complex.I) - (z : ℂ)‖ ^ 2) := by
  -- This is just rewriting the definition to factor out the `1/(2π)` normalization.
  unfold poissonKernelNormalized
  ring

end Complex.UnitDisc
