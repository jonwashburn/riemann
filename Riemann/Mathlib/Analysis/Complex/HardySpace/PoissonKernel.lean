
import Riemann.Mathlib.Analysis.Complex.HardySpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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
      -- Expand `exp(θ i)` as `cos θ + sin θ i` and compute the norm.
      simp [Complex.exp_mul_I, pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    -- Define the holomorphic integrand whose circle integral equals the real integral.
    let g : ℂ → ℂ :=
      fun z => ((1 - r ^ 2 : ℝ) : ℂ) / (Complex.I * (z - (r : ℂ)) * (1 - (r : ℂ) * z))

    have h_circle :
        (∫ θ in (0 : ℝ)..2 * π, (poissonKernel r 0 θ : ℂ)) =
          circleIntegral g 0 1 := by
      -- Unfold `circleIntegral` and compute the integrand.
      simp [circleIntegral, g, poissonKernel, circleMap_zero, Complex.exp_mul_I,
        mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, add_assoc]

    -- Compute the circle integral of `g` by splitting into a principal part at `z = r` and a holomorphic part.
    have hg_decomp :
        g = fun z =>
          (-Complex.I) * ((z - (r : ℂ))⁻¹ + (r : ℂ) * (1 - (r : ℂ) * z)⁻¹) := by
      funext z
      -- algebraic identity: `(1-r^2)/((z-r)(1-rz)) = 1/(z-r) + r/(1-rz)`
      have h1 :
          ((1 - r ^ 2 : ℝ) : ℂ) / ((z - (r : ℂ)) * (1 - (r : ℂ) * z)) =
            (z - (r : ℂ))⁻¹ + (r : ℂ) * (1 - (r : ℂ) * z)⁻¹ := by
        field_simp [hr.ne']
        ring
      -- divide by `I` (i.e. multiply by `-I`)
      simp [g, div_eq_mul_inv, h1, mul_add, mul_assoc, mul_left_comm, mul_comm]

    have hI : circleIntegral g 0 1 = (2 * π : ℂ) := by
      -- Use the decomposition and compute the two terms separately.
      have hr_mem : (r : ℂ) ∈ Metric.ball (0 : ℂ) (1 : ℝ) := by
        simpa [Metric.mem_ball, dist_zero_right] using hr_lt_one
      -- First term: integral of `(z - r)⁻¹` is `2π i`.
      have h_main :
          circleIntegral (fun z => (-Complex.I) * (z - (r : ℂ))⁻¹) 0 1 = (2 * π : ℂ) := by
        -- Pull out the constant `-I`.
        simp [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball hr_mem]
      -- Second term: the integrand is holomorphic on a neighborhood of the closed unit disk, so its circle integral is zero.
      have h_aux :
          circleIntegral (fun z => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹)) 0 1 = 0 := by
        -- We show this integrand is a derivative on the circle, hence integrates to zero.
        have hR : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
        -- Choose a radius `R > 1` with `R < 1 / r` so that `1 - r z ≠ 0` on `ball 0 R`.
        let R : ℝ := (1 + (1 / r)) / 2
        have hR1 : 1 < R := by
          have : (1 : ℝ) < 1 / r := by
            have : r < 1 := hr_lt_one
            have hr_pos' : 0 < r := hr_pos
            -- invert the inequality `r < 1`
            have : 1 < 1 / r := by
              simpa [one_div] using (one_div_lt_one_div_of_lt hr_pos' this).trans_eq (by ring)
            exact this
          dsimp [R]; linarith
        have hRlt : R < 1 / r := by
          dsimp [R]; linarith
        have hne : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) R → (1 - (r : ℂ) * z) ≠ 0 := by
          intro z hz
          have hz' : ‖z‖ < R := by
            simpa [Metric.mem_ball, dist_zero_right] using hz
          have : ‖(r : ℂ) * z‖ < 1 := by
            -- `‖r*z‖ < r*R < 1`
            have : ‖(r : ℂ)‖ * ‖z‖ < 1 := by
              have hrR : r * R < 1 := by
                have : r * (1 / r) = 1 := by field_simp [hr.ne']
                have : r * R < r * (1 / r) := by
                  nlinarith [hRlt, hr_pos]
                simpa [this] using this
              simpa [norm_mul, Complex.norm_real, abs_of_pos hr_pos] using
                (mul_lt_mul_of_pos_left hz' hr_pos).trans hrR
            simpa [norm_mul] using this
          -- If `1 - r*z = 0` then `‖r*z‖ = 1`, contradiction.
          intro hzero
          have : ‖(r : ℂ) * z‖ = 1 := by
            have : (r : ℂ) * z = 1 := by
              have : 1 - (r : ℂ) * z = 0 := by simpa using hzero
              linarith
            simpa [this]
          exact (ne_of_lt this) this
        -- The function is differentiable on `ball 0 R`.
        have hdiff :
            DifferentiableOn ℂ (fun z : ℂ => (-Complex.I) * ((r : ℂ) * (1 - (r : ℂ) * z)⁻¹))
              (Metric.ball (0 : ℂ) R) := by
          intro z hz
          have hz_ne : (1 - (r : ℂ) * z) ≠ 0 := hne z hz
          have h_inv : DifferentiableAt ℂ (fun z => (1 - (r : ℂ) * z)⁻¹) z := by
            simpa using ((differentiable_const.sub ((differentiable_const.mul differentiable_id))).inv hz_ne).differentiableAt
          -- products/constants preserve differentiability
          simpa [mul_assoc] using (differentiableAt_const.mul (differentiableAt_const.mul h_inv)).differentiableWithinAt
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
      simpa [hg_decomp, circleIntegral, add_assoc, add_left_comm, add_comm] using
        (by
          -- Use linearity of the integral.
          simp [hg_decomp, circleIntegral, h_main, h_aux])

    -- Finish: translate back to the real integral.
    have hC : (∫ θ in (0 : ℝ)..2 * π, (poissonKernel r 0 θ : ℂ)) = (2 * π : ℂ) :=
      h_circle.trans hI
    -- Extract the real statement.
    -- Use `intervalIntegral.integral_ofReal` to compare real and complex integrals.
    exact_mod_cast hC

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
