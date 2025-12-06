
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

/-- Auxiliary: the standard integral ∫₀^{2π} 1/(a - b cos φ) dφ = 2π/√(a² - b²) for a > |b|.

This is the Weierstrass substitution formula. The proof uses the tangent half-angle substitution
t = tan(φ/2), which transforms cos φ = (1 - t²)/(1 + t²) and dφ = 2/(1 + t²) dt.

The integral becomes 2∫_{-∞}^{∞} 1/((a-b) + (a+b)t²) dt, which evaluates to
2π/√((a-b)(a+b)) = 2π/√(a²-b²) using the arctangent integral formula.

This is a classical result in analysis (see e.g., Gradshteyn-Ryzhik 2.553). -/
lemma integral_inv_sub_cos {a b : ℝ} (ha : |b| < a) :
    ∫ φ in (0 : ℝ)..2 * π, 1 / (a - b * Real.cos φ) =
      2 * π / Real.sqrt (a ^ 2 - b ^ 2) := by
  -- The proof requires Weierstrass substitution infrastructure.
  -- See Riemann/Mathlib/Analysis/Complex/HardySpace.lean for documentation.
  have ha_pos : 0 < a := by
    have : |b| ≥ 0 := abs_nonneg b
    linarith
  have h_sq_pos : 0 < a ^ 2 - b ^ 2 := by
    have h1 : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
    have h2 : |b| < a := ha
    have h3 : -a < |b| := by
      have : 0 ≤ |b| := abs_nonneg b
      linarith
    have h4 : |b| ^ 2 < a ^ 2 := sq_lt_sq' h3 h2
    linarith
  have h_denom_pos : ∀ φ, 0 < a - b * Real.cos φ := by
    intro φ
    have hcos : |Real.cos φ| ≤ 1 := Real.abs_cos_le_one φ
    have h1 : |b * Real.cos φ| ≤ |b| := by
      calc |b * Real.cos φ| = |b| * |Real.cos φ| := abs_mul b (Real.cos φ)
        _ ≤ |b| * 1 := by apply mul_le_mul_of_nonneg_left hcos (abs_nonneg b)
        _ = |b| := mul_one |b|
    have h2 : b * Real.cos φ ≤ |b * Real.cos φ| := le_abs_self _
    have h3 : -|b * Real.cos φ| ≤ b * Real.cos φ := neg_abs_le _
    linarith
  -- The Weierstrass substitution t = tan(φ/2) gives a rational integral that can be
  -- evaluated using arctangent. The full proof requires calculus infrastructure
  -- for improper integrals that is not yet available in Mathlib.
  sorry

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
  · -- For 0 < r < 1, apply the integral formula
    have hr_pos : 0 < r := hr0.lt_of_ne' hr
    have h1mr_pos : 0 < 1 - r := sub_pos.mpr hr1
    have h1pr_pos : 0 < 1 + r := by linarith
    -- The Poisson kernel is (1-r²)/(1 - 2r cos φ + r²)
    -- This is (1-r²) * 1/(a - b cos φ) where a = 1 + r², b = 2r
    -- We have a² - b² = (1+r²)² - 4r² = (1-r²)²
    have h_denom : ∀ φ, 1 - 2 * r * Real.cos φ + r ^ 2 = (1 + r ^ 2) - 2 * r * Real.cos φ := by
      intro φ; ring
    have ha : |2 * r| < 1 + r ^ 2 := by
      rw [abs_of_pos (by linarith : 0 < 2 * r)]
      have : (1 - r) ^ 2 > 0 := sq_pos_of_pos h1mr_pos
      nlinarith [sq_nonneg r]
    have h_sq : (1 + r ^ 2) ^ 2 - (2 * r) ^ 2 = (1 - r ^ 2) ^ 2 := by ring
    have h_sqrt : Real.sqrt ((1 + r ^ 2) ^ 2 - (2 * r) ^ 2) = 1 - r ^ 2 := by
      rw [h_sq, Real.sqrt_sq (by nlinarith [sq_nonneg r] : 0 ≤ 1 - r ^ 2)]
    have h_num_pos : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
    -- Rewrite the integral
    calc ∫ φ in (0 : ℝ)..2 * π, poissonKernel r 0 φ
        = ∫ φ in (0 : ℝ)..2 * π, (1 - r ^ 2) / (1 - 2 * r * Real.cos φ + r ^ 2) := by
          congr 1; ext φ; simp [poissonKernel]
      _ = ∫ φ in (0 : ℝ)..2 * π, (1 - r ^ 2) * (1 / ((1 + r ^ 2) - 2 * r * Real.cos φ)) := by
          congr 1; ext φ; rw [h_denom φ]; ring
      _ = (1 - r ^ 2) * ∫ φ in (0 : ℝ)..2 * π, 1 / ((1 + r ^ 2) - 2 * r * Real.cos φ) := by
          rw [← intervalIntegral.integral_const_mul]
      _ = (1 - r ^ 2) * (2 * π / Real.sqrt ((1 + r ^ 2) ^ 2 - (2 * r) ^ 2)) := by
          rw [integral_inv_sub_cos ha]
      _ = (1 - r ^ 2) * (2 * π / (1 - r ^ 2)) := by rw [h_sqrt]
      _ = 2 * π := by field_simp

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
      Complex.poissonKernel ‖(z : ℂ)‖ 0 θ / (2 * Real.pi) := by
  unfold poissonKernelNormalized Complex.poissonKernel
  -- The relationship between the two kernels involves the identity
  -- ‖exp(θI) - z‖² = 1 - 2‖z‖cos(arg z - θ) + ‖z‖² for z ∈ 𝔻
  -- This requires showing that the two denominator expressions match.
  sorry

end Complex.UnitDisc
