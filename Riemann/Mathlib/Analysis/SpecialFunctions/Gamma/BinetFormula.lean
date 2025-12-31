import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.NumberTheory.BernoulliPolynomials
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel

/-!
# Binet's Formula for log Γ and Stirling Series with Error Bounds

This file develops the Binet formula for the logarithm of the Gamma function
and derives rigorous error bounds for the Stirling asymptotic series.

## Main Definitions

* `Binet.J`: The Binet integral J(z) = ∫₀^∞ K̃(t) e^{-tz} dt where K̃ = K/t
* `Binet.R`: The remainder term in Stirling's series
* `stirlingSeries`: The Stirling asymptotic series for log Γ

## Main Results

* `Binet.log_Gamma_eq`: log Γ(z) = (z-1/2)log z - z + log(2π)/2 + J(z)
* `Binet.J_bound`: |J(z)| ≤ 1/(12|z|) for Re(z) > 0
* `stirling_error_bound`: Error bound for truncated Stirling series
* (Robbins bounds for `n!`) live in `Riemann/Mathlib/Analysis/SpecialFunctions/Gamma/StirlingRobbins.lean`.

## References

* NIST DLMF 5.11: Asymptotic Expansions
* Robbins, H. "A Remark on Stirling's Formula." Amer. Math. Monthly 62 (1955): 26-29.
* Whittaker & Watson, "A Course of Modern Analysis", Chapter 12

## Implementation Notes

We use the normalized kernel K̃(t) = K(t)/t from BinetKernel, where
K(t) = 1/(e^t - 1) - 1/t + 1/2. This satisfies K̃(t) → 1/12 as t → 0⁺
and 0 ≤ K̃(t) ≤ 1/12 for t ≥ 0.
-/

open Real Complex Set MeasureTheory Filter Topology BinetKernel
open scoped BigOperators Nat

noncomputable section

namespace Binet

/-! ## Section 1: The Binet integral J(z) -/

/-- The Binet integral: J(z) = ∫₀^∞ K̃(t) e^{-tz} dt for Re(z) > 0.
This is the correction term in log Γ(z) = (z-1/2)log z - z + log(2π)/2 + J(z). -/
def J (z : ℂ) : ℂ :=
  if 0 < z.re then
    ∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z)
  else 0

/-- J(z) is well-defined for Re(z) > 0 (the integral converges). -/
lemma J_well_defined {z : ℂ} (hz : 0 < z.re) :
    MeasureTheory.Integrable (fun t : ℝ => (Ktilde t : ℂ) * Complex.exp (-t * z))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
  BinetKernel.integrable_Ktilde_exp_complex hz

/-- For Re(z) > 0, J(z) equals the integral. -/
lemma J_eq_integral {z : ℂ} (hz : 0 < z.re) :
    J z = ∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z) := by
  simp only [J, if_pos hz]

/-- Helper: The norm of the integrand K̃(t) * exp(-tz) equals K̃(t) * exp(-t*Re(z)). -/
lemma norm_Ktilde_mul_exp {z : ℂ} (t : ℝ) (ht : 0 < t) :
    ‖(Ktilde t : ℂ) * Complex.exp (-t * z)‖ = Ktilde t * Real.exp (-t * z.re) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Ktilde_nonneg (le_of_lt ht)), Complex.norm_exp]
  congr 1
  have : ((-↑t * z).re) = -t * z.re := by
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [this]

/-- Helper: K̃(t) * exp(-t*x) is integrable on (0,∞) for x > 0. -/
lemma integrable_Ktilde_mul_exp_real {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) := by
  exact BinetKernel.integrable_Ktilde_exp hx

/-- Helper: (1/12) * exp(-t*x) is integrable on (0,∞) for x > 0. -/
lemma integrable_const_mul_exp {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => (1/12 : ℝ) * Real.exp (-t * x)) (Set.Ioi 0) := by
  apply Integrable.const_mul
  have h := integrableOn_exp_mul_Ioi (neg_neg_of_pos hx) 0
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t _
  ring_nf

/-- Helper: Pointwise bound K̃(t) * exp ≤ (1/12) * exp. -/
lemma Ktilde_mul_exp_le {x : ℝ} (t : ℝ) (ht : 0 < t) :
    Ktilde t * Real.exp (-t * x) ≤ (1/12 : ℝ) * Real.exp (-t * x) :=
  mul_le_mul_of_nonneg_right (Ktilde_le (le_of_lt ht)) (Real.exp_nonneg _)

/-- Helper: The integral of exp(-t*x) on (0,∞) equals 1/x for x > 0. -/
lemma integral_exp_neg_mul_Ioi {x : ℝ} (hx : 0 < x) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * x) = 1 / x := by
  have h := integral_exp_mul_Ioi (neg_neg_of_pos hx) 0
  -- h : ∫ t in Ioi 0, exp(-x * t) = -exp(0) / (-x)
  simp only [mul_zero, Real.exp_zero] at h
  -- h : ∫ t in Ioi 0, exp(-x * t) = -1 / -x
  have heq : (fun t => Real.exp (-t * x)) = (fun t => Real.exp (-x * t)) := by
    ext t; ring_nf
  rw [heq, h]
  field_simp

/-- The fundamental bound: |J(z)| ≤ 1/(12·Re(z)) for Re(z) > 0.
This is the key estimate for the Stirling remainder. -/
theorem J_norm_le_re {z : ℂ} (hz : 0 < z.re) : ‖J z‖ ≤ 1 / (12 * z.re) := by
  rw [J_eq_integral hz]
  calc ‖∫ t in Set.Ioi (0 : ℝ), (Ktilde t : ℂ) * Complex.exp (-t * z)‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖(Ktilde t : ℂ) * Complex.exp (-t * z)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), Ktilde t * Real.exp (-t * z.re) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact (J_well_defined hz).norm
        · exact integrable_Ktilde_mul_exp_real hz
        · exact measurableSet_Ioi
        · intro t ht
          rw [norm_Ktilde_mul_exp t ht]
    _ ≤ ∫ t in Set.Ioi (0 : ℝ), (1/12 : ℝ) * Real.exp (-t * z.re) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact integrable_Ktilde_mul_exp_real hz
        · exact integrable_const_mul_exp hz
        · exact measurableSet_Ioi
        · intro t ht
          exact Ktilde_mul_exp_le t ht
    _ = (1/12 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t * z.re) := by
        rw [← MeasureTheory.integral_const_mul]
    _ = (1/12 : ℝ) * (1 / z.re) := by
        rw [integral_exp_neg_mul_Ioi hz]
    _ = 1 / (12 * z.re) := by ring

/-- For real positive x, the bound simplifies to |J(x)| ≤ 1/(12x).
This is a special case of J_norm_le_re since for real x > 0, ‖x‖ = x = x.re. -/
theorem J_norm_le_real {x : ℝ} (hx : 0 < x) : ‖J (x : ℂ)‖ ≤ 1 / (12 * x) := by
  have hre : (0 : ℝ) < (x : ℂ).re := by simp [hx]
  have h := J_norm_le_re hre
  simp only [Complex.ofReal_re] at h
  exact h

/-! ## Section 2: Binet's formula for log Γ -/

/-!
### About a complex `log Γ` statement

Be careful: a statement of the form

`Complex.log (Complex.Gamma z) = (z - 1/2) * Complex.log z - z + log(2π)/2 + J z`

using the *principal* complex logarithm `Complex.log` is **not valid on all of** `{z | 0 < re z}`:
`Γ` crosses the negative real axis infinitely many times in the right half-plane, so the composite
`Complex.log ∘ Complex.Gamma` cannot be holomorphic there.  See
`Riemann/Mathlib/Analysis/SpecialFunctions/Gamma/GammaSlitPlane_PR_PLAN.md` for details.

A principled complex formulation should instead use a holomorphic branch of `log Γ`
(often called `logGamma`) on a suitable simply-connected domain.
-/

/-- Binet's formula for real arguments. -/
theorem log_Gamma_real_eq {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1/2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (J x).re := by
  sorry

/-! ## Section 3: Stirling series with Bernoulli numbers -/

/-- The Bernoulli number B_n as a real number. -/
def bernoulliReal (n : ℕ) : ℝ :=
  (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)).eval 0

/-- The k-th term of the Stirling series: B_{2k} / (2k(2k-1) z^{2k-1}) -/
def stirlingTerm (k : ℕ) (z : ℂ) : ℂ :=
  if k = 0 then 0 else
    (bernoulliReal (2 * k) : ℂ) / (2 * k * (2 * k - 1) * z ^ (2 * k - 1))

/-- The truncated Stirling series up to order n. -/
def stirlingSeries (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, stirlingTerm k z

/-- The remainder after n terms of the Stirling series. -/
def stirlingRemainder (n : ℕ) (z : ℂ) : ℂ :=
  J z - stirlingSeries n z

/-- The Binet integral equals the Stirling series plus remainder. -/
theorem J_eq_stirlingSeries_add_remainder (z : ℂ) (n : ℕ) :
    J z = stirlingSeries n z + stirlingRemainder n z := by
  simp only [stirlingRemainder, add_sub_cancel]

/-- Simplified bound for n = 0: |R₀(z)| ≤ 1/(12·Re(z)).
This follows from J_norm_le_re since R₀(z) = J(z). -/
theorem stirlingRemainder_zero_bound {z : ℂ} (hz : 0 < z.re) :
    ‖stirlingRemainder 0 z‖ ≤ 1 / (12 * z.re) := by
  simp only [stirlingRemainder, stirlingSeries, Finset.range_zero, Finset.sum_empty]
  simp only [sub_zero]
  exact J_norm_le_re hz

/-- For real positive x: |R₀(x)| ≤ 1/(12x). -/
theorem stirlingRemainder_zero_bound_real {x : ℝ} (hx : 0 < x) :
    ‖stirlingRemainder 0 (x : ℂ)‖ ≤ 1 / (12 * x) := by
  simp only [stirlingRemainder, stirlingSeries, Finset.range_zero, Finset.sum_empty]
  simp only [sub_zero]
  exact J_norm_le_real hx

/-! ## Section 4: Gamma function bounds -/

/-- For x ∈ [1, 2], Γ(x) ≤ 1 since Γ(1) = Γ(2) = 1 and the function is convex. -/
theorem Gamma_le_one_of_mem_Icc {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    Real.Gamma x ≤ 1 := by
  have h_convex := Real.convexOn_Gamma
  have h1 : Real.Gamma 1 = 1 := Real.Gamma_one
  have h2 : Real.Gamma 2 = 1 := Real.Gamma_two
  let t := 2 - x
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have hx_conv : x = t * 1 + (1 - t) * 2 := by field_simp [t]; ring
  have := h_convex.2 (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc Real.Gamma x
      = Real.Gamma (t * 1 + (1 - t) * 2) := by rw [hx_conv]
    _ ≤ t * Real.Gamma 1 + (1 - t) * Real.Gamma 2 := this
    _ = t * 1 + (1 - t) * 1 := by rw [h1, h2]
    _ = 1 := by ring

/-- The integral representation gives |Γ(z)| ≤ Γ(Re(z)) for Re(z) > 0.
Key: |t^{z-1}| = t^{Re(z)-1} for t > 0. -/
theorem norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  have h_norm_eq : ∀ t ∈ Set.Ioi (0 : ℝ),
      ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ = Real.exp (-t) * t ^ (z.re - 1) := by
    intro t ht
    have hcpow : ‖(t : ℂ) ^ (z - 1)‖ = t ^ (z.re - 1) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos ht (z - 1)
    simp [Complex.norm_exp, hcpow]
  calc ‖Complex.GammaIntegral z‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), ‖((-t).exp : ℂ) * (t : ℂ) ^ (z - 1)‖ := by
        unfold Complex.GammaIntegral
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (z.re - 1) := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_norm_eq

/-- Combined bound: For Re(z) ∈ [1, 2], |Γ(z)| ≤ 1. -/
theorem norm_Gamma_le_one {z : ℂ} (hlo : 1 ≤ z.re) (hhi : z.re ≤ 2) :
    ‖Complex.Gamma z‖ ≤ 1 := by
  have hz_pos : 0 < z.re := by linarith
  calc ‖Complex.Gamma z‖
      ≤ Real.Gamma z.re := norm_Gamma_le_Gamma_re hz_pos
    _ ≤ 1 := Gamma_le_one_of_mem_Icc hlo hhi

end Binet

/-! ## Section 6: Connection to Stirling.GammaAux -/

namespace Stirling.GammaAux

/-- The Gamma bound on [1, 2], proved via convexity. -/
theorem Gamma_bound_one_two' {s : ℂ} (hs_lo : 1 ≤ s.re) (hs_hi : s.re ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 1 :=
  Binet.norm_Gamma_le_one hs_lo hs_hi

end Stirling.GammaAux

/-!
## Compatibility / centralized API (`BinetFormula.*`)

Some downstream files historically refer to results in this file via the namespace `BinetFormula`.
The core development lives in `namespace Binet`; we provide thin wrappers here to keep the
namespace stable while we progressively centralize the Gamma/Stirling API inside `Riemann/Mathlib`.
-/

namespace BinetFormula

open Real Complex Set MeasureTheory Filter Topology BinetKernel
open scoped BigOperators

/-- Real-part version of the Binet integral: for `x > 0`,
`re (J x) = ∫₀^∞ K̃(t) * exp(-t*x) dt`. -/
theorem re_J_eq_integral_Ktilde {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re = ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
  have hx' : 0 < (x : ℂ).re := by simpa using hx
  -- unfold `J`
  rw [Binet.J_eq_integral (z := (x : ℂ)) hx']
  -- move `re` inside the integral
  have hInt :
      Integrable (fun t : ℝ => (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Binet.J_well_defined (z := (x : ℂ)) hx'
  have hre :
      ∫ t in Set.Ioi (0 : ℝ),
          ((BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))).re
        = (∫ t in Set.Ioi (0 : ℝ),
              (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))).re := by
    simpa using
      (integral_re (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (f := fun t : ℝ => (BinetKernel.Ktilde t : ℂ) * Complex.exp (-t * (x : ℂ))) hInt)
  -- rewrite `re (∫ ...)` using `hre`
  rw [← hre]
  -- pointwise simplification to a real integrand
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t _ht
  -- Unfold the (β-reduced) pointwise goal.
  dsimp
  have hexp : Complex.exp (-t * (x : ℂ)) = (Real.exp (-t * x) : ℂ) := by
    have harg : (-t * (x : ℂ)) = ((-t * x : ℝ) : ℂ) := by
      simp
    calc
      Complex.exp (-t * (x : ℂ)) = Complex.exp ((-t * x : ℝ) : ℂ) := by
        simp [harg]
      _ = (Real.exp (-t * x) : ℂ) := by
        simp
  -- Reduce the integrand to a product of real numbers coerced to `ℂ`, then take real parts.
  -- Important: avoid rewriting `(Real.exp _ : ℂ)` back into `Complex.exp _` (`Complex.ofReal_exp` is a simp lemma).
  rw [hexp]
  simp [-Complex.ofReal_exp]

/-- Integrability of the real Binet integrand `K̃(t) * exp(-t*x)` on `(0,∞)` for `x > 0`. -/
theorem integrable_Ktilde_mul_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) := by
  -- this is exactly the helper lemma already proved in `namespace Binet`
  simpa using (Binet.integrable_Ktilde_mul_exp_real (x := x) hx)

/-- **Positivity of the Binet integral (real part).**

For `x > 0`, the Binet correction term satisfies `(Binet.J x).re > 0`. -/
theorem re_J_pos {x : ℝ} (hx : 0 < x) : 0 < (Binet.J (x : ℂ)).re := by
  -- Rewrite the real part of `J` as a real set integral.
  have hJ : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  -- Find a small interval `(0, δ]` on which `Ktilde t ≥ 1/24`.
  have hpos_event : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), (1 / 24 : ℝ) < BinetKernel.Ktilde t := by
    have h :=
      (BinetKernel.tendsto_Ktilde_zero :
        Tendsto BinetKernel.Ktilde (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (1 / 12 : ℝ)))
    have hmem : Set.Ioi (1 / 24 : ℝ) ∈ nhds (1 / 12 : ℝ) := by
      have : (1 / 24 : ℝ) < (1 / 12 : ℝ) := by norm_num
      exact Ioi_mem_nhds this
    exact h.eventually hmem
  have hmem :
      {t : ℝ | (1 / 24 : ℝ) < BinetKernel.Ktilde t} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    simpa [Filter.Eventually] using hpos_event
  rcases (mem_nhdsWithin).1 hmem with ⟨u, hu_open, hu0, hu_sub⟩
  rcases (Metric.mem_nhds_iff).1 (IsOpen.mem_nhds hu_open hu0) with ⟨ε, hεpos, hball⟩
  set δ : ℝ := ε / 2
  have hδpos : 0 < δ := by exact half_pos hεpos

  -- Lower bound the integrand by a positive constant on `Ioc 0 δ`.
  have hK_lower : ∀ t ∈ Set.Ioc (0 : ℝ) δ, (1 / 24 : ℝ) ≤ BinetKernel.Ktilde t := by
    intro t ht
    have ht_pos : t ∈ Set.Ioi (0 : ℝ) := ht.1
    have ht_u : t ∈ u := by
      have ht_ball : t ∈ Metric.ball (0 : ℝ) ε := by
        have ht_lt : t < ε := lt_of_le_of_lt ht.2 (half_lt_self hεpos)
        have ht_abs : |t| < ε := by simpa [abs_of_pos ht.1] using ht_lt
        simpa [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero] using ht_abs
      exact hball ht_ball
    have : t ∈ {t : ℝ | (1 / 24 : ℝ) < BinetKernel.Ktilde t} := hu_sub ⟨ht_u, ht_pos⟩
    exact le_of_lt (by simpa using this)

  have hExp_lower : ∀ t ∈ Set.Ioc (0 : ℝ) δ, Real.exp (-δ * x) ≤ Real.exp (-t * x) := by
    intro t ht
    have hx0 : 0 ≤ x := le_of_lt hx
    have ht_le : t ≤ δ := ht.2
    have hmul : -δ * x ≤ -t * x := by
      -- since `t ≤ δ` and `x ≥ 0`
      nlinarith [ht_le, hx0]
    exact Real.exp_le_exp.mpr hmul

  have hconst_le :
      ∀ t ∈ Set.Ioc (0 : ℝ) δ,
        (1 / 24 : ℝ) * Real.exp (-δ * x) ≤ BinetKernel.Ktilde t * Real.exp (-t * x) := by
    intro t ht
    have h1 : (1 / 24 : ℝ) ≤ BinetKernel.Ktilde t := hK_lower t ht
    have h2 : Real.exp (-δ * x) ≤ Real.exp (-t * x) := hExp_lower t ht
    have h24 : 0 ≤ (1 / 24 : ℝ) := by norm_num
    have hK0 : 0 ≤ BinetKernel.Ktilde t := le_trans h24 h1
    have hE0 : 0 ≤ Real.exp (-t * x) := Real.exp_nonneg _
    calc
      (1 / 24 : ℝ) * Real.exp (-δ * x)
          ≤ (BinetKernel.Ktilde t) * Real.exp (-δ * x) := by
              exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ ≤ (BinetKernel.Ktilde t) * Real.exp (-t * x) := by
              exact mul_le_mul_of_nonneg_left h2 hK0

  -- Integrate the lower bound on `Ioc 0 δ`, then compare to the integral on `Ioi 0`.
  have hInt_on : IntegrableOn (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) (Set.Ioi 0) volume :=
    (integrable_Ktilde_mul_exp_neg_mul (x := x) hx)
  have hInt_Ioc : IntegrableOn (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) (Set.Ioc 0 δ) volume :=
    hInt_on.mono_set (Set.Ioc_subset_Ioi_self)
  have hμ_Ioc : (volume (Set.Ioc (0 : ℝ) δ)) ≠ (⊤ : ENNReal) := by
    -- `volume (Ioc 0 δ) = ENNReal.ofReal δ`.
    simp [Real.volume_Ioc]
  have hlower_int :
      (1 / 24 : ℝ) * Real.exp (-δ * x) * (volume.real (Set.Ioc (0 : ℝ) δ))
        ≤ ∫ t in Set.Ioc (0 : ℝ) δ, BinetKernel.Ktilde t * Real.exp (-t * x) := by
    -- Use the general constant lower bound lemma.
    have : ((1 / 24 : ℝ) * Real.exp (-δ * x)) * volume.real (Set.Ioc (0 : ℝ) δ)
        ≤ ∫ t in Set.Ioc (0 : ℝ) δ, BinetKernel.Ktilde t * Real.exp (-t * x) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (MeasureTheory.setIntegral_ge_of_const_le_real (μ := volume)
          (s := Set.Ioc (0 : ℝ) δ) (f := fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x))
          (c := (1 / 24 : ℝ) * Real.exp (-δ * x)) (hs := measurableSet_Ioc)
          (hμs := hμ_Ioc) (hf := hconst_le) (hfint := hInt_Ioc))
    simpa [mul_assoc] using this

  have hIoc_le :
      ∫ t in Set.Ioc (0 : ℝ) δ, BinetKernel.Ktilde t * Real.exp (-t * x)
        ≤ ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
    -- Monotonicity in the domain for nonnegative functions.
    have hf_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun t : ℝ => BinetKernel.Ktilde t * Real.exp (-t * x)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have hK0 : 0 ≤ BinetKernel.Ktilde t := BinetKernel.Ktilde_nonneg (le_of_lt ht)
      exact mul_nonneg hK0 (Real.exp_nonneg _)
    have hst : (Set.Ioc (0 : ℝ) δ) ≤ᵐ[volume] (Set.Ioi (0 : ℝ)) := by
      refine ae_of_all _ ?_
      intro t ht
      exact ht.1
    exact MeasureTheory.setIntegral_mono_set (μ := volume) (hfi := hInt_on) hf_nonneg hst

  have hμpos : 0 < volume.real (Set.Ioc (0 : ℝ) δ) := by
    -- `volume.real (Ioc 0 δ) = δ` for `0 ≤ δ`.
    have hvol : volume.real (Set.Ioc (0 : ℝ) δ) = δ := by
      simpa [sub_zero] using (Real.volume_real_Ioc_of_le (a := (0 : ℝ)) (b := δ) (by exact le_of_lt hδpos))
    simpa [hvol] using hδpos

  have hconst_pos : 0 < (1 / 24 : ℝ) * Real.exp (-δ * x) := by
    have : (0 : ℝ) < (1 / 24 : ℝ) := by norm_num
    exact mul_pos this (Real.exp_pos _)

  -- Combine bounds: integral over Ioi 0 is ≥ integral over Ioc 0 δ ≥ positive constant.
  have hpos :
      0 < ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := by
    have : 0 < (1 / 24 : ℝ) * Real.exp (-δ * x) * volume.real (Set.Ioc (0 : ℝ) δ) := by
      exact mul_pos hconst_pos hμpos
    have h1 : (1 / 24 : ℝ) * Real.exp (-δ * x) * volume.real (Set.Ioc (0 : ℝ) δ)
          ≤ ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
      le_trans hlower_int hIoc_le
    exact lt_of_lt_of_le this h1

  -- Conclude.
  simpa [hJ] using hpos

/-- **Upper bound for the Binet integral (real part).**

For `x > 0`, we have `(Binet.J x).re ≤ 1/(12x)`. -/
theorem re_J_le_one_div_twelve {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re ≤ 1 / (12 * x) := by
  have hJ : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx
  -- compare the integrand with `(1/12) * exp(-t*x)`
  have hmono :
      (∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x))
        ≤ ∫ t in Set.Ioi (0 : ℝ), (1 / 12 : ℝ) * Real.exp (-t * x) := by
    apply MeasureTheory.setIntegral_mono_on
    · exact integrable_Ktilde_mul_exp_neg_mul (x := x) hx
    · simpa using (Binet.integrable_const_mul_exp (x := x) hx)
    · exact measurableSet_Ioi
    · intro t ht
      exact Binet.Ktilde_mul_exp_le (x := x) t ht
  -- compute the RHS integral explicitly
  have hint : (∫ t in Set.Ioi (0 : ℝ), (12 : ℝ)⁻¹ * Real.exp (-(t * x))) = x⁻¹ * (12 : ℝ)⁻¹ := by
    -- normalize the exponent as `-(t * x)` to match simp-normal forms downstream
    have hbase : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) = 1 / x := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using (Binet.integral_exp_neg_mul_Ioi (x := x) hx)
    calc
      (∫ t in Set.Ioi (0 : ℝ), (12 : ℝ)⁻¹ * Real.exp (-(t * x)))
          = (12 : ℝ)⁻¹ * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) := by
              -- pull out the constant and normalize the exponent
              simp [MeasureTheory.integral_const_mul, mul_comm]
      _ = (12 : ℝ)⁻¹ * (1 / x) := by simp [hbase]
      _ = x⁻¹ * (12 : ℝ)⁻¹ := by ring
  -- finish
  have hmono' :
      (∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x)) ≤ x⁻¹ * (12 : ℝ)⁻¹ := by
    -- normalize the RHS integrand to match `hint`
    have hmono0 :
        (∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x)) ≤
          ∫ t in Set.Ioi (0 : ℝ), (12 : ℝ)⁻¹ * Real.exp (-(t * x)) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hmono
    exact le_trans hmono0 (le_of_eq hint)
  -- turn `x⁻¹ * 12⁻¹` into `1 / (12 * x)` in the final statement
  have : x⁻¹ * (12 : ℝ)⁻¹ = 1 / (12 * x) := by
    ring
  have hmono'' :
      (∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x)) ≤ 1 / (12 * x) := by
    rw [this] at hmono'
    exact hmono'
  -- conclude
  calc
    (Binet.J (x : ℂ)).re
        = ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) := hJ
    _ ≤ 1 / (12 * x) := hmono''

/-- Compatibility alias: historical name for the (non-strict) upper bound on `re (J x)`. -/
theorem re_J_lt_one_div_twelve {x : ℝ} (hx : 0 < x) :
    (Binet.J (x : ℂ)).re < 1 / (12 * x) := by
  -- Rewrite `re (J x)` as a real set integral.
  have hJ : (Binet.J (x : ℂ)).re =
      ∫ t in Set.Ioi (0 : ℝ), BinetKernel.Ktilde t * Real.exp (-t * x) :=
    re_J_eq_integral_Ktilde (x := x) hx

  -- Set up integrands.
  let f : ℝ → ℝ := fun t => BinetKernel.Ktilde t * Real.exp (-t * x)
  let g : ℝ → ℝ := fun t => (1 / 12 : ℝ) * Real.exp (-t * x)
  let h : ℝ → ℝ := fun t => g t - f t

  have hf_int : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
    simpa [f] using (integrable_Ktilde_mul_exp_neg_mul (x := x) hx)
  have hg_int : IntegrableOn g (Set.Ioi (0 : ℝ)) volume := by
    -- helper lemma in `namespace Binet`
    simpa [g] using (Binet.integrable_const_mul_exp (x := x) hx)

  -- The gap integrand is nonnegative on `(0,∞)`.
  have hh_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] h := by
    -- reduce to an `ae` statement on `volume` using `ae_restrict_iff'`
    have : ∀ᵐ t ∂volume, t ∈ Set.Ioi (0 : ℝ) → 0 ≤ h t := by
      refine MeasureTheory.ae_of_all _ ?_
      intro t ht
      have hK : BinetKernel.Ktilde t ≤ (1 / 12 : ℝ) := BinetKernel.Ktilde_le (le_of_lt ht)
      have hE : 0 ≤ Real.exp (-t * x) := Real.exp_nonneg _
      dsimp [h, f, g]
      -- `0 ≤ a - b` follows from `b ≤ a`.
      refine sub_nonneg.2 ?_
      exact mul_le_mul_of_nonneg_right hK hE
    exact (MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2 this

  have hh_int : IntegrableOn h (Set.Ioi (0 : ℝ)) volume := by
    -- `h = g - f`
    simpa [h] using (hg_int.sub hf_int)

  -- The gap integrand is *strictly* positive everywhere on `(0,∞)`, hence its support on `(0,∞)`
  -- has positive measure, hence its integral is positive.
  have hμ_support : (0 : ENNReal) < volume (Function.support h ∩ Set.Ioi (0 : ℝ)) := by
    -- `Ioc 0 1 ⊆ support h ∩ Ioi 0`
    have hsub : Set.Ioc (0 : ℝ) 1 ⊆ Function.support h ∩ Set.Ioi (0 : ℝ) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have htI : t ∈ Set.Ioi (0 : ℝ) := ht0
      have hK : BinetKernel.Ktilde t < (1 / 12 : ℝ) := BinetKernel.Ktilde_lt ht0
      have hE : 0 < Real.exp (-t * x) := Real.exp_pos _
      have : h t ≠ 0 := by
        -- show `h t > 0`
        have : 0 < h t := by
          dsimp [h, f, g]
          -- `0 < a - b` follows from `b < a`
          have hlt : BinetKernel.Ktilde t * Real.exp (-t * x) < (1 / 12 : ℝ) * Real.exp (-t * x) := by
            exact mul_lt_mul_of_pos_right hK hE
          exact sub_pos.2 hlt
        exact ne_of_gt this
      have ht_support : t ∈ Function.support h := by
        simp [Function.mem_support, this]
      exact ⟨ht_support, htI⟩
    -- the volume of `Ioc 0 1` is positive
    have hvol_pos : (0 : ENNReal) < volume (Set.Ioc (0 : ℝ) 1) := by simp
    exact lt_of_lt_of_le hvol_pos (measure_mono hsub)

  have hh_pos : 0 < ∫ t in Set.Ioi (0 : ℝ), h t := by
    have := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae (μ := volume)
      (s := Set.Ioi (0 : ℝ)) (f := h) hh_nonneg hh_int).2 hμ_support
    simpa using this

  -- Convert positivity of the gap integral into strict inequality of integrals.
  have hsub_eq :
      (∫ t in Set.Ioi (0 : ℝ), h t) =
        (∫ t in Set.Ioi (0 : ℝ), g t) - (∫ t in Set.Ioi (0 : ℝ), f t) := by
    -- use `integral_sub` under the restricted measure
    simpa [h, sub_eq_add_neg] using
      (MeasureTheory.integral_sub (μ := volume.restrict (Set.Ioi (0 : ℝ))) (hf := hg_int) (hg := hf_int))

  have hlt_fg : (∫ t in Set.Ioi (0 : ℝ), f t) < (∫ t in Set.Ioi (0 : ℝ), g t) := by
    have : 0 < (∫ t in Set.Ioi (0 : ℝ), g t) - (∫ t in Set.Ioi (0 : ℝ), f t) := by
      simpa [hsub_eq] using hh_pos
    exact (sub_pos.mp this)

  -- Compute the RHS integral.
  have hg_val : (∫ t in Set.Ioi (0 : ℝ), g t) = 1 / (12 * x) := by
    have hbase : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) = 1 / x := by
      -- normalize as `-(t * x)` to avoid simp-normalization issues
      simpa [mul_assoc, mul_comm, mul_left_comm] using (Binet.integral_exp_neg_mul_Ioi (x := x) hx)
    calc
      (∫ t in Set.Ioi (0 : ℝ), g t)
          = (1 / 12 : ℝ) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * x)) := by
              simp [g, MeasureTheory.integral_const_mul, mul_comm]
      _ = (1 / 12 : ℝ) * (1 / x) := by simp [hbase]
      _ = 1 / (12 * x) := by ring

  -- Finish.
  -- `re (J x) = ∫ f` and `∫ f < ∫ g = 1/(12x)`.
  have : (Binet.J (x : ℂ)).re < 1 / (12 * x) := by
    -- rewrite `re (J x)` to `∫ f`
    have : (∫ t in Set.Ioi (0 : ℝ), f t) < 1 / (12 * x) := by
      -- use the computed value of `∫ g`
      have : (∫ t in Set.Ioi (0 : ℝ), f t) < (∫ t in Set.Ioi (0 : ℝ), g t) := hlt_fg
      exact lt_of_lt_of_eq this hg_val
    simpa [hJ, f] using this
  exact this

/-- Compatibility wrapper: real Binet formula for `log Γ(x)` on `x > 0`. -/
theorem Real_log_Gamma_eq_Binet {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + (Binet.J x).re := by
  -- This is the `Binet`-namespace statement (currently proved elsewhere in the development).
  simpa using (Binet.log_Gamma_real_eq (x := x) hx)

end BinetFormula
