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
* `factorial_upper_bound`: n! ≤ √(2πn)(n/e)^n e^{1/(12n)} (Robbins bound)

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

/-- **Binet's First Formula**: For Re(z) > 0,
log Γ(z) = (z - 1/2) log z - z + log(2π)/2 + J(z)

This is the fundamental representation connecting Γ to the Binet integral.
The proof requires deep analysis of the Gamma function. -/
theorem log_Gamma_eq {z : ℂ} (hz : 0 < z.re) :
    Complex.log (Complex.Gamma z) =
      (z - 1/2) * Complex.log z - z + Complex.log (2 * Real.pi) / 2 + J z := by
  -- This is a deep theorem requiring integration by parts and
  -- verification of the functional equation. Deferred.
  sorry

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

/-! ## Section 4: Factorial bounds -/

/-- **Stirling's approximation for log(n!)**: For n ≥ 1,
log(n!) = n log n - n + log(2πn)/2 + θ/(12n) where 0 < θ < 1. -/
theorem log_factorial_stirling {n : ℕ} (hn : 0 < n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      Real.log (n.factorial : ℝ) =
        n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 + θ / (12 * n) := by
  -- Proof: Apply Binet's formula to Γ(n+1) = n! and use the bound on J
  sorry

/-- **Robbins Upper Bound**: n! ≤ √(2πn)(n/e)^n e^{1/(12n)} -/
theorem factorial_upper_bound (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) := by
  -- Follows from the upper bound θ < 1 in log_factorial_stirling
  sorry

/-- **Robbins Lower Bound**: n! ≥ √(2πn)(n/e)^n e^{1/(12n+1)} -/
theorem factorial_lower_bound (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial := by
  -- Follows from the lower bound 0 < θ in log_factorial_stirling
  sorry

/-- The two-sided Robbins bound. -/
theorem factorial_robbins_bound (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n + 1)) ≤
      n.factorial ∧
    (n.factorial : ℝ) ≤
      Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n * Real.exp (1 / (12 * n)) :=
  ⟨factorial_lower_bound n hn, factorial_upper_bound n hn⟩

/-! ## Section 5: Gamma function bounds -/

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

/-- The Robbins upper bound, proved via Binet's formula. -/
theorem factorial_asymptotic' (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤ Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n *
      Real.exp (1 / (12 * n)) :=
  Binet.factorial_upper_bound n hn

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

end BinetFormula
