import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
-- Assuming these are available from the context or mocked if necessary
import PrimeNumberTheoremAnd
import StrongPNT

/-!
# Weil's Explicit Formula for the Riemann Zeta Function

This file defines the structural components of Weil's Explicit Formula, relating
a sum over the nontrivial zeros of the Riemann Zeta function (Spectral Side)
to a sum over prime powers and analytical terms (Geometric Side).

## Main Definitions

* `IsWeilTestFunction`: A structure bundling the properties required for the test function `g`.
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

open Set

/-- For any real `a`, the sets `(-∞, a]` and `(a, ∞)` partition `ℝ`. -/
lemma union_Iic_Ioi (a : ℝ) :
    (Iic a : Set ℝ) ∪ Ioi a = (Set.univ : Set ℝ) := by
  ext x; constructor
  · intro hx; exact trivial
  · intro _; by_cases h : x ≤ a
    · left; exact h
    · right; exact lt_of_not_ge h

/-- A function integrable on `(-∞, 0]` and `(0, ∞)` is integrable on `ℝ`. -/
lemma integrable_of_integrable_on_Iic_of_integrable_on_Ioi {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (h_le : IntegrableOn f (Iic 0)) (h_gt : IntegrableOn f (Ioi 0)) :
    Integrable f := by
  -- Use the standard `IntegrableOn.union` lemma plus the partition of ℝ
  have h_union : (Iic (0 : ℝ) : Set ℝ) ∪ Ioi 0 = Set.univ := union_Iic_Ioi 0
  -- rewrite the goal using this partition
  have h_int : IntegrableOn f ((Iic 0 : Set ℝ) ∪ Ioi 0) := by
    exact IntegrableOn.union h_le h_gt
  simpa [IntegrableOn, h_union] using h_int

/-- `x ↦ exp (-ε x)` is integrable on `(0, ∞)` for `ε > 0`. -/
lemma integrableOn_exp_neg_mul_Ioi {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => Real.exp (-ε * x)) (Ioi 0) := by
  have h : IntegrableOn (fun x ↦ Real.exp (-x)) (Ioi 0) := by
    simpa using Real.GammaIntegral_convergent zero_lt_one
  have : (fun x : ℝ => Real.exp (-ε * x)) = (fun x => Real.exp (-(ε * x))) := by
    ext x; ring_nf
  rw [this, integrableOn_Ioi_comp_mul_left_iff (fun y => Real.exp (-y)) 0 hε]
  simp only [mul_zero]
  exact h

/-- `x ↦ exp (-ε x)` is integrable on `(0, ∞)` for `ε > 0`. -/

lemma integrable_exp_neg_mul_abs {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => Real.exp (-ε * |x|)) := by
  refine integrable_of_integrable_on_Iic_of_integrable_on_Ioi ?_ ?_
  · have : IntegrableOn (fun x ↦ Real.exp (ε * x)) (Iic 0) volume := by
      exact integrableOn_exp_mul_Iic hε 0
    apply this.congr_fun
    · intro x hx
      simp only [mem_Iic] at hx
      simp only []
      rw [abs_of_nonpos hx]
      ring_nf
    · exact measurableSet_Iic

  · have : IntegrableOn (fun x ↦ Real.exp (-ε * x)) (Ioi 0) volume := by
      exact integrableOn_exp_neg_mul_Ioi hε
    apply this.congr_fun
    · intro x hx
      simp only [mem_Ioi] at hx
      simp only [abs_of_nonneg (le_of_lt hx)]
    · exact measurableSet_Ioi

lemma weilTransform_integrable_strip
    (s : ℂ) (h_strip : |s.re - (1 / 2)| < 1 / 2) :
    Integrable (fun x : ℝ => g x * Complex.exp ((s - 1 / 2) * x)) := by
  obtain ⟨C, ε, hε, hdecay⟩ := IsWeilTestFunction.decay (g := g)
  let bound := fun x : ℝ => C * Real.exp (-ε * |x|)
  have h_int : Integrable bound := (integrable_exp_neg_mul_abs hε).const_mul C
  have h_meas : AEStronglyMeasurable (fun x : ℝ => g x * Complex.exp ((s - 1 / 2) * x)) volume := by
    apply Continuous.aestronglyMeasurable
    exact g.continuous.mul (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal))
  refine Integrable.mono' h_int h_meas ?_
  filter_upwards with x
  specialize hdecay x
  rw [norm_mul, norm_exp]
  refine le_trans (mul_le_mul_of_nonneg_right hdecay (Real.exp_nonneg _)) ?_
  rw [mul_assoc, ← Real.exp_add]
  unfold bound
  gcongr
  -- Exponent: -(1/2 + ε)|x| + (Re s - 1/2)x ≤ -ε * |x|
  have h_real : (s - 1/2).re = s.re - 0.5 := by simp; norm_num
  rw [h_real]
  rcases le_or_lt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    rw [abs_lt] at h_strip
    linarith
  · rw [abs_of_neg hx]
    rw [abs_lt] at h_strip
    linarith

lemma weilTransform_holomorphic_strip :
    DifferentiableOn ℂ (fun s => weilTransform g s)
      {s : ℂ | |s.re - (1 / 2)| < 1 / 2} := by
  apply differentiableOn_integral_of_dominated_complex
  · exact measurableSet_setOf_lt (continuous_abs.comp (continuous_re.sub continuous_const)) continuous_const
  · -- Dominated by C * exp(-ε'|x|) locally
    intro s₀ hs₀
    obtain ⟨C, ε, hε, hdecay⟩ := IsWeilTestFunction.decay (g := g)
    -- Find a small neighborhood of s₀ inside the strip
    obtain ⟨δ, hδ, h_ball⟩ := Metric.isOpen_iff.mp (isOpen_lt (continuous_abs.comp (continuous_re.sub continuous_const)) continuous_const) s₀ hs₀
    -- We need to pick an ε' < ε such that the domination holds for all s in the ball
    -- The exponent is -(1/2 + ε)|x| + (Re s - 1/2)x
    -- We need -(1/2 + ε)|x| + (Re s - 1/2)x ≤ -ε'|x|
    -- This requires (Re s - 1/2)x ≤ (1/2 + ε - ε')|x|
    -- Let's just use the fact that Re s is bounded in the ball.
    let σ_max := s₀.re + δ
    let σ_min := s₀.re - δ
    -- We know -ε < σ_min - 1/2 and σ_max - 1/2 < ε because the ball is in the strip (0, 1)
    -- and the decay allows for a strip of width 2ε around 1/2.
    -- Actually, IsWeilTestFunction.decay gives decay e^{-(1/2+ε)|x|}.
    -- The integral has e^{(s-1/2)x}.
    -- Total exponent: -(1/2+ε)|x| + (Re s - 1/2)x.
    -- If x > 0: (Re s - 1 - ε)x. We need Re s < 1 + ε.
    -- If x < 0: (Re s + ε)x. We need Re s > -ε.
    -- The strip is 0 < Re s < 1, so this is always satisfied with room to spare.
    let margin := min (1 + ε - σ_max) (σ_min - (-ε))
    have h_margin : 0 < margin := by
      -- Proof that the ball is well within the convergence strip (-ε, 1+ε)
      sorry
    refine ⟨fun x => C * Real.exp (- (margin/2) * |x|), (integrable_exp_neg_mul_abs (by linarith)).const_mul _, 0, ?_⟩
    refine eventually_of_forall fun t ht => ?_
    -- Uniform bound proof
    sorry

lemma summable_log_mul_rpow_of_one_lt {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => Real.log n * (n : ℝ) ^ (-p)) := by
  -- Let p = 1 + 2δ
  let δ := (p - 1) / 2
  have hδ : 0 < δ := by linarith
  have : (fun n : ℕ => Real.log n * (n : ℝ) ^ (-p)) =O[atTop] (fun n => (n : ℝ) ^ (-(1 + δ))) := by
    refine IsBigO.of_bound 1 (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg (Nat.one_le_cast.2 hn)),
        Real.abs_rpow_of_nonneg (Nat.cast_nonneg n), one_mul]
    rw [neg_add, Real.rpow_add (Nat.cast_pos.2 hn), Real.rpow_neg (Nat.cast_nonneg _)]
    rw [mul_comm, ← mul_assoc, ← div_eq_mul_inv]
    -- We need log n * n^(-p) ≤ n^(-1-δ)
    -- log n * n^(-(1+2δ)) ≤ n^(-1-δ)
    -- log n * n^(-1) * n^(-2δ) ≤ n^(-1) * n^(-δ)
    -- log n * n^(-δ) ≤ 1
    -- log n ≤ n^δ. This is true eventually.
    have h_growth : Real.log n ≤ (n : ℝ) ^ δ := by
      -- Standard calculus: log x < x^δ for large x
      sorry
    calc Real.log n * (n : ℝ) ^ (-p)
      _ = Real.log n * (n : ℝ) ^ (-(1 + 2 * δ)) := by congr; linarith
      _ = (Real.log n * (n : ℝ) ^ (-δ)) * (n : ℝ) ^ (-(1 + δ)) := by
          rw [Real.rpow_add (Nat.cast_pos.2 hn), Real.rpow_mul (Nat.cast_nonneg _)]; ring_nf; rfl
      _ ≤ 1 * (n : ℝ) ^ (-(1 + δ)) := by
          gcongr
          rw [Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv]
          exact (div_le_one (Real.rpow_pos_of_pos (Nat.cast_pos.2 hn) _)).mpr h_growth
  refine this.summable (Real.summable_nat_rpow_inv.2 ?_)
  linarith

lemma primeTerm_summable :
    Summable (fun n : ℕ =>
      if n = 0 then 0 else
        ((vonMangoldt n : ℂ) / Real.sqrt n) *
          (g (Real.log n) + g (-Real.log n))) := by
  obtain ⟨C, ε, hε, hdecay⟩ := IsWeilTestFunction.decay (g := g)
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

/--
Convergence of the spectral side requires estimates on the vertical density of zeros.
Specifically, N(T) ~ T log T.
Without this deep number-theoretic input, we cannot prove summability for general Schwartz functions.
We mark this as a `sorry` to indicate the dependency on the Zero Density Theorem.
-/
lemma spectralSide_summable :
    Summable (fun ρ : {s // IsZetaNontrivialZero s} => weilTransform g ρ) := by
  -- Requires N(T) = |{ρ | 0 < Im ρ < T}| ~ (T/2π) log T
  -- and rapid decay of weilTransform g (which is entire and Schwartz on vertical lines)
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
  -- This requires the Residue Theorem for a rectangle.
  -- The poles inside the rectangle [1-ε, 1+ε] x [-T, T] are:
  -- 1. The pole of ζ(s) at s=1 (residue 1 for -ζ'/ζ, so residue Φ(1) for integrand)
  -- 2. The pole of ζ(s) at s=0 (from functional equation, residue Φ(0))
  -- 3. The nontrivial zeros ρ of ζ(s) (residue Φ(ρ))
  -- Note: We assume T is not the ordinate of a zero.
  sorry

/-- The integral on the *right* vertical line `Re s = 1 + ε` tends, as `T → ∞`,
to the geometric side `boundary + prime + archimedean`.  This is where you use
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div` plus vertical decay. -/
lemma right_verticalLineIntegral_tendsto_geometricSide
    (ε : ℝ) (hε_pos : 0 < ε) :
    Tendsto (fun T : ℝ => verticalLineIntegral g (1 + ε) T)
      atTop (𝓝 (geometricSide g)) := by
  -- 1. Expand -ζ'/ζ as Dirichlet series ∑ Λ(n) n^{-s}
  -- 2. Swap integral and sum (justified by absolute convergence due to g's decay)
  -- 3. Recognize ∫ g(x) e^{(1+ε+it-1/2)x} dt as Fourier transform related terms
  -- 4. This yields the primeTerm
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
  -- Requires bounds on ζ'/ζ on horizontal lines (standard PNT bounds)
  -- and rapid decay of weilTransform g.
  sorry

/-- Truncated spectral sum converges to the full spectral side as `T → ∞`.
This uses `spectralSide_summable`. -/
lemma spectralSideTrunc_tendsto_spectralSide :
    Tendsto (fun T : ℝ => spectralSideTrunc g T)
      atTop (𝓝 (spectralSide g)) := by
  -- Immediate from summability
  sorry

/--
**Weil's Explicit Formula for the Riemann Zeta Function**.

Given a suitable test function `g` (even, Schwartz, exp decay), the sum over the
nontrivial zeros of `ζ(s)` equals the sum over prime powers plus analytical terms.
-/
theorem weil_explicit_formula
    (g : SchwartzMap ℝ ℂ) [IsWeilTestFunction g] :
    spectralSide g = geometricSide g := by
  -- The proof strategy combines the lemmas above:
  -- 1. Contour integration gives relation between vertical lines and residues (spectral + boundary).
  -- 2. Right vertical line converges to geometric side (prime terms).
  -- 3. Left vertical line is related to right via functional equation (archimedean terms).
  -- 4. Horizontal integrals vanish.
  sorry

end NumberTheory.WeilExplicit

/-
The current draft targets the Riemann Zeta function specifically. While the file is titled WeilExplicitFormula, Weil's formalism is powerful precisely because it unifies number fields, function fields, and automorphic L-functions (as detailed in Tao.md).

Critique:

Generality: A "SOTA formalization in full generality" should ideally define the Explicit Formula for a generic motivic L-function or at least the Selberg class. Hardcoding riemannZeta restricts the result to the classical case.
Archimedean Factors: The definition of archimedeanTerm uses GammaLogDeriv at 1/4 + ix/2. This corresponds to the
Γ
(
s
/
2
)
Γ(s/2) factor in the functional equation
ξ
(
s
)
=
π
−
s
/
2
Γ
(
s
/
2
)
ζ
(
s
)
ξ(s)=π
−s/2
 Γ(s/2)ζ(s). This is correct for
ζ
(
s
)
ζ(s), but a general implementation would require a vector of Gamma factors.
Spectral Convergence: The spectralSide_summable lemma is non-trivial. It depends on the vertical density of zeros
N
(
T
)
∼
T
2
π
log
⁡
T
N(T)∼
2π
T
​
 logT. Without this estimate (which is not yet in Mathlib), the unconditional convergence of the spectral side for general Schwartz functions is unprovable.
 -/
