
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import PrimeNumberTheoremAnd
import StrongPNT

/-!
# Weil's Explicit Formula for the Riemann Zeta Function

This file defines the structural components of Weil's Explicit Formula, relating
a sum over the nontrivial zeros of the Riemann Zeta function (Spectral Side)
to a sum over prime powers and analytical terms (Geometric Side).

## Main Definitions

* `WeilTestFunction`: A structure bundling the properties required for the test function `g`.
* `weilTransform`: The analytic transform `Φ(s) = ∫ g(x) e^{(s - 1/2)x} dx`.
* `spectralSide`: The sum `∑ Φ(ρ)` over nontrivial zeros.
* `geometricSide`: The sum over primes, archimedean terms, and boundary terms.

## Notation

We utilize the normalization where the critical line is `Re(s) = 1/2`.
-/

noncomputable section

open scoped BigOperators Real Complex
open Complex Real MeasureTheory SchwartzMap Topology Filter Set ArithmeticFunction Asymptotics
open ArithmeticFunction (vonMangoldt)

namespace NumberTheory.WeilExplicit

/--
A Weil test function is a Schwartz function on ℝ satisfying specific symmetry
and decay properties allowing for the convergence of the Explicit Formula.
-/
class IsWeilTestFunction (g : SchwartzMap ℝ ℂ) : Prop where
  /-- The function must be even, corresponding to the symmetry of the functional equation. -/
  even : ∀ x, g x = g (-x)
  /-- Strong decay ensures the transform `Φ(s)` is entire or analytic in a wide strip. -/
  decay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖g x‖ ≤ C * Real.exp (- (1/2 + ε) * |x|)
  /-- Decay of the Fourier transform ensures absolute convergence of the prime sum. -/
  ft_decay : ∃ (C' ε' : ℝ), 0 < ε' ∧ ∀ ξ, ‖fourierTransformCLM ℂ g ξ‖ ≤ C' * Real.exp (- (1/2 + ε') * |ξ|)

variable (g : SchwartzMap ℝ ℂ) [IsWeilTestFunction g]

/-! ### The Analytic Transform -/

/--
The Weil transform `Φ(s)`.
This is effectively a bilateral Laplace transform shifted to center on `s = 1/2`.
`Φ(s) = ∫_{-∞}^{∞} g(x) e^{(s - 1/2)x} dx`
-/
def weilTransform (s : ℂ) : ℂ :=
  ∫ x : ℝ, g x * Complex.exp ((s - 0.5) * x)

lemma integrable_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => Real.exp (-ε * |x|)) := by
  sorry

lemma weilTransform_integrable_strip
    (s : ℂ) (h_strip : |s.re - (1 / 2)| < 1 / 2) :
    Integrable (fun x : ℝ => g x * Complex.exp ((s - 1 / 2) * x)) := by
  obtain ⟨C, ε, hε, hdecay⟩ := IsWeilTestFunction.decay (g := g)
  have h_int :
    Integrable (fun x : ℝ => C * Real.exp (-ε * |x|)) :=
    (integrable_exp_neg_mul_abs hε).const_mul C
  apply MeasureTheory.AECover.integrable_of_integral_norm_bounded _
    ((integrable_mul_exp_neg_mul_sq hε).const_mul C)
  intro x
  specialize hdecay x
  rw [norm_mul, Complex.norm_eq_abs, Complex.abs_exp]
  refine le_trans (mul_le_mul_of_nonneg_right hdecay (Real.exp_nonneg _)) ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  -- Exponent: -(1/2 + ε)|x| + (Re s - 1/2)x
  have h_real : s.re - 1/2 = (s.re - 0.5) := by norm_num
  rw [h_real]
  rcases le_or_lt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    linarith [abs_le_of_abs_le_abs_sub_sub h_strip]
  · rw [abs_of_neg hx]
    linarith [abs_le_of_abs_le_abs_sub_sub h_strip]

lemma weilTransform_holomorphic_strip :
    DifferentiableOn ℂ (fun s => weilTransform g s)
      {s : ℂ | |s.re - (1 / 2)| < 1 / 2} := by
  apply differentiableOn_integral_of_dominated_complex
  · exact measurableSet_setOf_lt (continuous_abs.comp (continuous_re.sub continuous_const)) continuous_const
  · -- Dominated by C * exp(-ε|x|) locally
    intro s₀ hs₀
    obtain ⟨C, ε, hε, hdecay⟩ := IsWeilTestFunction.decay
    -- Find a small neighborhood of s₀ inside the strip
    obtain ⟨δ, hδ, h_ball⟩ := Metric.isOpen_iff.mp (isOpen_lt (continuous_abs.comp (continuous_re.sub continuous_const)) continuous_const) s₀ hs₀
    refine ⟨fun x => C * Real.exp (-ε * |x|), (integrable_exp_neg_mul_abs hε).const_mul _, 0, ?_⟩
    refine eventually_of_forall fun t ht => ?_
    -- Use essentially the same bound as above, but for all t in the ball
    sorry -- uniform bound on neighborhood

lemma summable_log_mul_rpow_of_one_lt {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-p)) := by
  have : (fun n : ℕ => Real.log n * (n : ℝ) ^ (-p)) =O[atTop] (fun n => (n : ℝ) ^ (-(1 + (p - 1) / 2))) := by
    refine IsBigO.of_bound 1 (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg (Nat.one_le_cast.2 hn)),
        Real.abs_rpow_of_nonneg (Nat.cast_nonneg n), one_mul]
    -- Reduce to log n ≤ n^((p-1)/2)
    sorry -- standard growth bound
  refine this.summable (Real.summable_nat_rpow_inv.2 ?_)
  linarith

lemma primeTerm_summable :
    Summable (fun n : ℕ =>
      if n = 0 then 0 else
        ((vonMangoldt n : ℂ) / Real.sqrt n) *
          (g (Real.log n) + g (-Real.log n))) := by
  obtain ⟨C, ε, hε, hdecay⟩ := IsWeilTestFunction.decay
  apply Summable.of_norm_bounded_eventually_nat (fun n => (2 * C) * (Real.log n * (n : ℝ) ^ (-(1 + ε))))
  · exact (summable_log_mul_rpow_of_one_lt (by linarith)).const_mul _
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [norm_if_pos (Nat.ne_of_gt hn), norm_mul, norm_div, Complex.norm_eq_abs (Real.sqrt _),
        Real.abs_sqrt (Nat.cast_nonneg _)]
    -- Bound von Mangoldt
    have hΛ := vonMangoldt_complex_norm_le_log n
    -- Bound g terms
    have hg : ‖g (Real.log n) + g (-Real.log n)‖ ≤ 2 * C * (n : ℝ) ^ (-(1/2 + ε)) := by
      have h_log_pos : 0 ≤ Real.log n := Real.log_nonneg (Nat.one_le_cast.2 hn)
      specialize hdecay (Real.log n)
      rw [Real.abs_log_natCast, abs_of_nonneg h_log_pos] at hdecay
      specialize g.even (Real.log n)
      rw [norm_add_le, ← g.even, ← Real.exp_mul, neg_mul, Real.exp_neg,
          Real.exp_mul, Real.exp_log (Nat.cast_pos.2 hn), Real.rpow_def_of_pos (Nat.cast_pos.2 hn)] at hdecay ⊢
      linarith
    -- Combine
    calc ‖(vonMangoldt n : ℂ) / Real.sqrt n * (g (Real.log n) + g (-Real.log n))‖
      _ = ‖(vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-(1/2 : ℝ)) * ‖g (Real.log n) + g (-Real.log n)‖ := by
          rw [norm_mul, norm_div, Complex.norm_eq_abs, Real.abs_sqrt (Nat.cast_nonneg _),
              Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
      _ ≤ Real.log n * (n : ℝ) ^ (-(1/2 : ℝ)) * (2 * C * (n : ℝ) ^ (-(1/2 + ε))) := by
          gcongr
      _ = (2 * C) * (Real.log n * ((n : ℝ) ^ (-(1/2 : ℝ)) * (n : ℝ) ^ (-(1/2 + ε)))) := by ring
      _ = (2 * C) * (Real.log n * (n : ℝ) ^ (-(1 + ε))) := by
          rw [← Real.rpow_add (Nat.cast_pos.2 hn), neg_add_neg]
          congr; ring



/-! ### The Spectral Side (Zeros) -/

/-- Predicate for nontrivial zeros of Riemann Zeta in the critical strip. -/
def IsZetaNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

lemma spectralSide_summable :
    Summable (fun ρ : {s // IsZetaNontrivialZero s} => weilTransform g ρ) := by
  sorry

/--
The spectral side of the Explicit Formula: `∑_ρ Φ(ρ)`.
Note: Convergence of this sum depends on the density of zeros and decay of `Φ`.
-/
def spectralSide : ℂ :=
  ∑' (ρ : {s // IsZetaNontrivialZero s}), weilTransform g ρ

/-! ### The Geometric Side (Primes + Archimedean) -/

lemma vonMangoldt_complex_norm_le_log (n : ℕ) :
    ‖(vonMangoldt n : ℂ)‖ ≤ Real.log n := by
  have hΛ_nonneg : 0 ≤ (vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  simpa [Complex.norm_real, abs_of_nonneg hΛ_nonneg]
    using (ArithmeticFunction.vonMangoldt_le_log (n := n))

/--
The contribution from prime powers `p^k`.
`Sum_{n} Λ(n)/√n * (g(log n) + g(-log n))`
-/
def primeTerm : ℂ :=
  - ∑' n : ℕ, if n = 0 then 0 else
    ((vonMangoldt n : ℂ) / Real.sqrt n) *
      (g (Real.log n) + g (-Real.log n))

/--
The Archimedean contribution arising from the Gamma factor in the functional equation.
`1/2π ∫ g(x) Re(Ψ(1/4 + ix/2)) dx` ... (simplified form for definition)
-/
def GammaLogDeriv (s : ℂ) : ℂ :=
  (logDeriv Complex.Gamma) s

def archimedeanTerm : ℂ :=
  let h := fourierTransformCLM ℂ g
  let term1 :=
    (1 / (2 * π)) *
      ∫ x : ℝ,
        g x *
          (GammaLogDeriv (1 / 4 + (x / 2) * Complex.I) +
            GammaLogDeriv (1 / 4 - (x / 2) * Complex.I))
  let term2 := - h 0 * Real.log π
  term1 + term2

/--
The boundary terms arising from the poles of the L-function (at s=0 and s=1).
For Riemann Zeta, this is `Φ(0) + Φ(1)`.
-/
def boundaryTerm : ℂ :=
  weilTransform g 0 + weilTransform g 1

/--
The geometric side of the Explicit Formula.
-/
def geometricSide : ℂ :=
  boundaryTerm g + primeTerm g + archimedeanTerm g

/-! ### Main Theorem Statement -/

namespace NumberTheory.WeilExplicit

variable (g : SchwartzMap ℝ ℂ) [IsWeilTestFunction g]

/-- `-ζ'/ζ`, the logarithmic derivative of the Riemann zeta function. -/
def zetaLogDeriv (s : ℂ) : ℂ :=
  - deriv riemannZeta s / riemannZeta s

/-- Integrand `Φ(s) · (-ζ'/ζ)(s)` used in the explicit formula contour integral. -/
def explicitIntegrand (s : ℂ) : ℂ :=
  weilTransform g s * zetaLogDeriv s

/-- Integral of `explicitIntegrand` along the vertical line `Re s = σ`, truncated at height `T`. -/
def verticalLineIntegral (σ T : ℝ) : ℂ :=
  ∫ t in -T..T, explicitIntegrand g (σ + t * Complex.I) * Complex.I

/-- Truncated spectral side: only zeros with `|Im ρ| ≤ T`. -/
def spectralSideTrunc (T : ℝ) : ℂ :=
  ∑' (ρ : {s // IsZetaNontrivialZero s}),
    if |(ρ : ℂ).im| ≤ T then weilTransform g ρ else 0

/-- Contour‑integral / residue decomposition for a tall rectangle:
difference of the two vertical integrals equals the sum of residues from
nontrivial zeros and the poles at `0` and `1`. -/
lemma rectangle_integral_residue_decomposition
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_half : ε < 1 / 2)
    (T : ℝ) (hT : 1 ≤ T) :
    verticalLineIntegral g (1 + ε) T -
      verticalLineIntegral g (1 - ε) T =
      (2 * π * Complex.I) *
        (spectralSideTrunc g T + boundaryTerm g) := by
  sorry

/-- The integral on the *right* vertical line `Re s = 1 + ε` tends, as `T → ∞`,
to the geometric side `boundary + prime + archimedean`.  This is where you use
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` plus vertical decay. -/
lemma right_verticalLineIntegral_tendsto_geometricSide
    (ε : ℝ) (hε_pos : 0 < ε) :
    Tendsto (fun T : ℝ => verticalLineIntegral g (1 + ε) T)
      atTop (𝓝 (geometricSide g)) := by
  sorry

/-- The contribution from the horizontal segments (top and bottom of the rectangle)
vanishes as `T → ∞`, so the limiting difference of the two vertical integrals
is entirely given by the residue sum.  This is the analytic decay estimate
along `Im s = ±T`. -/
lemma verticalLineIntegral_difference_tendsto_residue_sum
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_half : ε < 1 / 2) :
    Tendsto (fun T : ℝ =>
      verticalLineIntegral g (1 + ε) T -
        verticalLineIntegral g (1 - ε) T)
      atTop
      (𝓝 ((2 * π * Complex.I) * (spectralSide g + boundaryTerm g))) := by
  sorry

/-- Truncated spectral sum converges to the full spectral side as `T → ∞`.
This uses `spectralSide_summable`. -/
lemma spectralSideTrunc_tendsto_spectralSide :
    Tendsto (fun T : ℝ => spectralSideTrunc g T)
      atTop (𝓝 (spectralSide g)) := by
  sorry

/--
**Weil's Explicit Formula for the Riemann Zeta Function**.

Given a suitable test function `g` (even, Schwartz, exp decay), the sum over the
nontrivial zeros of `ζ(s)` equals the sum over prime powers plus analytical terms.
-/
theorem weil_explicit_formula
    (g : SchwartzMap ℝ ℂ) [IsWeilTestFunction g] :
    spectralSide g = geometricSide g := by
  -- choose ε with 0 < ε < 1/2
  -- use `right_verticalLineIntegral_tendsto_geometricSide`
  -- and `verticalLineIntegral_difference_tendsto_residue_sum`
  -- plus `spectralSideTrunc_tendsto_spectralSide`
  -- and basic algebra of limits
  sorry

end NumberTheory.WeilExplicit
