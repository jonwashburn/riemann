/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn, Gemini
-/
import RiemannRecognitionGeometry.ExplicitFormula.WeilTestFunctionProofs
import RiemannRecognitionGeometry.ExplicitFormula.Defs

/-!
# Concrete Test Function Space for Route 3

This file defines `WeilTestFunction`, a concrete candidate for the Route 3 test-function space.

## Status
- **Reflection and conjugation**: Fully proved (closure under `f(-·)` and `conj ∘ f`).
- **Decay preservation**: Fully proved for both function and Fourier transform decay.
- **Fourier transform identities**: Fully proved (`ℱ[f(-·)](ξ) = ℱ[f](-ξ)` and
  `ℱ[conj ∘ f](ξ) = conj(ℱ[f](-ξ))`).
- **Convolution**: Fully defined and proved to preserve the decay conditions.
- **Transform identities**: `weilTransform_reflection` is proved; convolution multiplicativity
  is proved on the critical strip `0 ≤ Re(s) ≤ 1` by discharging the Fubini/Tonelli integrability
  hypothesis from the exponential decay bounds.
-/

noncomputable section

open scoped BigOperators Real Complex
open Complex Real MeasureTheory SchwartzMap Topology Filter Set Asymptotics

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

/--
A Weil test function is a Schwartz function on ℝ satisfying specific decay properties allowing for
the convergence of Explicit Formula terms.

This matches earlier `IsWeilTestFunction` development but without an `even` constraint.
-/
structure WeilTestFunction where
  /-- The underlying Schwartz function. -/
  toSchwartz : SchwartzMap ℝ ℂ
  /-- Strong decay ensures the transform `Φ(s)` is analytic in a wide strip. -/
  decay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖toSchwartz x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|)
  /-- Decay of the Fourier transform ensures absolute convergence of prime sums. -/
  ft_decay :
    ∃ (C' ε' : ℝ),
      0 < ε' ∧ ∀ ξ, ‖fourierTransformCLM ℂ toSchwartz ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|)

namespace WeilTestFunction

/-- Coercion to function. -/
instance : CoeFun WeilTestFunction (fun _ => ℝ → ℂ) where
  coe f := f.toSchwartz

variable (f g : WeilTestFunction)

/--
The Weil transform `Φ(s)`.

This is effectively a bilateral Laplace transform shifted to center on `s = 1/2`:
`Φ(s) = ∫_{-∞}^{∞} g(x) e^{(s - 1/2)x} dx`.
-/
def weilTransform (s : ℂ) : ℂ :=
  ∫ x : ℝ, f.toSchwartz x * Complex.exp ((s - 0.5) * x)

/-- Additive convolution of Weil test functions (closed in the class). -/
def convolution (f g : WeilTestFunction) : WeilTestFunction where
  toSchwartz := schwartzConv f.toSchwartz g.toSchwartz
  decay := decay_preserved_by_convolution (f := f.toSchwartz) (g := g.toSchwartz) f.decay g.decay
  ft_decay :=
    ft_decay_preserved_by_convolution (f := f.toSchwartz) (g := g.toSchwartz) f.ft_decay g.ft_decay

/-- Reflection `f(-x)`: proved using `reflectSchwartz` and decay preservation lemmas. -/
def reflection (f : WeilTestFunction) : WeilTestFunction where
  toSchwartz := reflectSchwartz f.toSchwartz
  decay := decay_preserved_by_reflection f.decay
  ft_decay := ft_decay_preserved_by_reflection f.ft_decay

/-- Complex conjugation `conj(f(x))`: proved using `conjSchwartz` and decay preservation lemmas. -/
def conjugation (f : WeilTestFunction) : WeilTestFunction where
  toSchwartz := conjSchwartz f.toSchwartz
  decay := decay_preserved_by_conjugation f.decay
  ft_decay := ft_decay_preserved_by_conjugation f.ft_decay

/-! ### Analytic properties -/

/-- A helper bound: if `0 ≤ σ ≤ 1` then `|σ - 1/2| ≤ 1/2`. -/
lemma abs_sub_half_le_half {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    |σ - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by
  refine (abs_le).2 ?_
  constructor
  · -- `-(1/2) ≤ σ - 1/2`
    have : (0 : ℝ) - (1 / 2 : ℝ) ≤ σ - (1 / 2 : ℝ) := sub_le_sub_right h0 (1 / 2 : ℝ)
    simpa using this
  · -- `σ - 1/2 ≤ 1/2` since `σ ≤ 1`
    have hsum : σ ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
      calc
        σ ≤ (1 : ℝ) := h1
        _ = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by ring_nf
    exact (sub_le_iff_le_add).2 hsum

/--
The product-measure integrability needed for the convolution theorem on the critical strip.

This is the missing "Fubini justification" step: it is discharged using the exponential decay bounds.
-/
lemma integrable_weilTransform_convolution_integrand (f g : WeilTestFunction) (s : ℂ)
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    Integrable
      (Function.uncurry fun x t : ℝ =>
        f.toSchwartz t * g.toSchwartz (x - t) * Complex.exp ((s - 0.5) * x))
      (volume.prod volume) := by
  -- Choose decay constants and a common epsilon.
  obtain ⟨Cf, εf, hεf, hfBound⟩ := f.decay
  obtain ⟨Cg, εg, hεg, hgBound⟩ := g.decay
  let ε : ℝ := min εf εg
  have hε : 0 < ε := lt_min hεf hεg
  have hεf' : ε ≤ εf := min_le_left _ _
  have hεg' : ε ≤ εg := min_le_right _ _

  -- Nonnegativity of the decay constants.
  have hCf0 : 0 ≤ Cf := by
    have h0 : ‖f.toSchwartz 0‖ ≤ Cf := by simpa using (hfBound 0)
    exact le_trans (norm_nonneg _) h0
  have hCg0 : 0 ≤ Cg := by
    have h0 : ‖g.toSchwartz 0‖ ≤ Cg := by simpa using (hgBound 0)
    exact le_trans (norm_nonneg _) h0

  -- The envelope `t ↦ exp(-ε|t|)` is integrable.
  let h : ℝ → ℝ := fun t => Real.exp (-ε * |t|)
  have hh_int : Integrable h := integrable_exp_neg_mul_abs ε hε

  -- Integrable envelope on `ℝ × ℝ` via the convolution-integrand lemma.
  have henv_int :
      Integrable (fun p : ℝ × ℝ => (Cf * Cg) * (h p.2 * h (p.1 - p.2))) (volume.prod volume) := by
    have hconv :
        Integrable (fun p : ℝ × ℝ =>
          ((ContinuousLinearMap.mul ℝ ℝ) (h p.2)) (h (p.1 - p.2))) (volume.prod volume) :=
      (MeasureTheory.Integrable.convolution_integrand
        (L := ContinuousLinearMap.mul ℝ ℝ) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        hh_int hh_int)
    have hconv' :
        Integrable (fun p : ℝ × ℝ => h p.2 * h (p.1 - p.2)) (volume.prod volume) := by
      simpa using hconv
    simpa [mul_assoc] using (hconv'.const_mul (Cf * Cg))

  -- A.e. strong measurability from continuity on `ℝ × ℝ`.
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry fun x t : ℝ =>
          f.toSchwartz t * g.toSchwartz (x - t) * Complex.exp ((s - 0.5) * x))
        (volume.prod volume) := by
    have hcont :
        Continuous (fun p : ℝ × ℝ =>
          f.toSchwartz p.2 * g.toSchwartz (p.1 - p.2) *
            Complex.exp ((s - 0.5) * (p.1 : ℂ))) := by
      have hf : Continuous (fun p : ℝ × ℝ => f.toSchwartz p.2) :=
        f.toSchwartz.continuous.comp continuous_snd
      have hg : Continuous (fun p : ℝ × ℝ => g.toSchwartz (p.1 - p.2)) := by
        have hsub : Continuous (fun p : ℝ × ℝ => p.1 - p.2) := continuous_fst.sub continuous_snd
        exact g.toSchwartz.continuous.comp hsub
      have hexp : Continuous (fun p : ℝ × ℝ => Complex.exp ((s - 0.5) * (p.1 : ℂ))) := by
        have h1 : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ)) :=
          (RCLike.continuous_ofReal : Continuous (fun x : ℝ => (x : ℂ))).comp continuous_fst
        have h2 : Continuous (fun p : ℝ × ℝ => (s - 0.5) * (p.1 : ℂ)) := continuous_const.mul h1
        exact Complex.continuous_exp.comp h2
      simpa [mul_assoc] using (hf.mul (hg.mul hexp))
    simpa [Function.uncurry, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      hcont.aestronglyMeasurable

  -- Pointwise domination by the integrable envelope (for `0 ≤ Re(s) ≤ 1`).
  have hdom :
      ∀ p : ℝ × ℝ,
        ‖(Function.uncurry fun x t : ℝ =>
            f.toSchwartz t * g.toSchwartz (x - t) * Complex.exp ((s - 0.5) * x)) p‖
          ≤ (Cf * Cg) * (h p.2 * h (p.1 - p.2)) := by
    rintro ⟨x, t⟩
    have hf' := hfBound t
    have hg' := hgBound (x - t)

    -- Bound the exponential factor using `0 ≤ s.re ≤ 1`.
    have hhalf : (0.5 : ℂ) = (1 / 2 : ℂ) := by norm_num
    have hs_abs : |s.re - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) :=
      abs_sub_half_le_half (h0 := hs0) (h1 := hs1)
    have hExp :
        ‖Complex.exp ((s - 0.5) * (x : ℂ))‖ ≤ Real.exp ((1 / 2 : ℝ) * |x|) := by
      have hn :
          ‖Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))‖ = Real.exp ((s.re - 1 / 2) * x) := by
        simp [Complex.abs_exp, Complex.norm_eq_abs, Complex.mul_re]
      have hx :
          (s.re - (1 / 2 : ℝ)) * x ≤ (1 / 2 : ℝ) * |x| := by
        have hx1 : (s.re - (1 / 2 : ℝ)) * x ≤ |(s.re - (1 / 2 : ℝ)) * x| := le_abs_self _
        have hx2 : |(s.re - (1 / 2 : ℝ)) * x| = |s.re - (1 / 2 : ℝ)| * |x| := by
          simpa [abs_mul] using (abs_mul (s.re - (1 / 2 : ℝ)) x)
        have hx3 : |s.re - (1 / 2 : ℝ)| * |x| ≤ (1 / 2 : ℝ) * |x| :=
          mul_le_mul_of_nonneg_right hs_abs (abs_nonneg x)
        have hx2' : |(s.re - (1 / 2 : ℝ)) * x| ≤ (1 / 2 : ℝ) * |x| := by
          calc
            |(s.re - (1 / 2 : ℝ)) * x| = |s.re - (1 / 2 : ℝ)| * |x| := hx2
            _ ≤ (1 / 2 : ℝ) * |x| := hx3
        exact le_trans hx1 hx2'
      have hExpReal :
          Real.exp ((s.re - (1 / 2 : ℝ)) * x) ≤ Real.exp ((1 / 2 : ℝ) * |x|) :=
        Real.exp_le_exp.2 hx
      calc
        ‖Complex.exp ((s - 0.5) * (x : ℂ))‖ = ‖Complex.exp ((s - (1 / 2 : ℂ)) * (x : ℂ))‖ := by
          simpa [hhalf]
        _ = Real.exp ((s.re - 1 / 2) * x) := hn
        _ ≤ Real.exp ((1 / 2 : ℝ) * |x|) := hExpReal

    -- Exponential domination: absorb `exp((1/2)|x|)` using `|x| ≤ |t| + |x-t|`.
    have habs : |x| ≤ |t| + |x - t| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (abs_add t (x - t))
    have hexp_dom :
        Real.exp (- (1 / 2 + εf) * |t|) * Real.exp (- (1 / 2 + εg) * |x - t|) *
            Real.exp ((1 / 2 : ℝ) * |x|) ≤
          Real.exp (-ε * |t|) * Real.exp (-ε * |x - t|) := by
      -- This is the `ε`-buffer inequality.
      have ht0 : 0 ≤ |t| := abs_nonneg _
      have hxt0 : 0 ≤ |x - t| := abs_nonneg _
      have hfcoeff : (1 / 2 : ℝ) * |t| ≤ (1 / 2 + εf - ε) * |t| := by
        have : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) + (εf - ε) :=
          le_add_of_nonneg_right (sub_nonneg.2 hεf')
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (mul_le_mul_of_nonneg_right this ht0)
      have hgcoeff : (1 / 2 : ℝ) * |x - t| ≤ (1 / 2 + εg - ε) * |x - t| := by
        have : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) + (εg - ε) :=
          le_add_of_nonneg_right (sub_nonneg.2 hεg')
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (mul_le_mul_of_nonneg_right this hxt0)
      have hC : (1 / 2 : ℝ) * |x| ≤ (1 / 2 + εf - ε) * |t| + (1 / 2 + εg - ε) * |x - t| := by
        have h1 : (1 / 2 : ℝ) * |x| ≤ (1 / 2 : ℝ) * (|t| + |x - t|) :=
          mul_le_mul_of_nonneg_left habs (by norm_num)
        have h2 : (1 / 2 : ℝ) * (|t| + |x - t|) = (1 / 2 : ℝ) * |t| + (1 / 2 : ℝ) * |x - t| := by ring
        have h1' : (1 / 2 : ℝ) * |x| ≤ (1 / 2 : ℝ) * |t| + (1 / 2 : ℝ) * |x - t| :=
          le_trans h1 (le_of_eq h2)
        have h3 :
            (1 / 2 : ℝ) * |t| + (1 / 2 : ℝ) * |x - t| ≤
              (1 / 2 + εf - ε) * |t| + (1 / 2 + εg - ε) * |x - t| :=
          add_le_add hfcoeff hgcoeff
        exact le_trans h1' h3
      have hsum' :
          (- (1 / 2 + εf) * |t|) + (- (1 / 2 + εg) * |x - t|) + (1 / 2 : ℝ) * |x| ≤
            (- (1 / 2 + εf) * |t|) + (- (1 / 2 + εg) * |x - t|) +
              ((1 / 2 + εf - ε) * |t| + (1 / 2 + εg - ε) * |x - t|) := by
        have := add_le_add_left hC ((- (1 / 2 + εf) * |t|) + (- (1 / 2 + εg) * |x - t|))
        simpa [add_assoc, add_left_comm, add_comm] using this
      have hsum :
          (- (1 / 2 + εf) * |t|) + (- (1 / 2 + εg) * |x - t|) + (1 / 2 : ℝ) * |x| ≤
            (-ε * |t|) + (-ε * |x - t|) := by
        have :
            (- (1 / 2 + εf) * |t|) + (- (1 / 2 + εg) * |x - t|) +
                ((1 / 2 + εf - ε) * |t| + (1 / 2 + εg - ε) * |x - t|) =
              (-ε * |t|) + (-ε * |x - t|) := by
          ring_nf
        exact hsum'.trans_eq this
      have hexp := Real.exp_le_exp.2 hsum
      simpa [Real.exp_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hexp

    -- Final domination.
    have hnorm :
        ‖f.toSchwartz t * g.toSchwartz (x - t) * Complex.exp ((s - 0.5) * (x : ℂ))‖ =
          ‖f.toSchwartz t‖ * ‖g.toSchwartz (x - t)‖ * ‖Complex.exp ((s - 0.5) * (x : ℂ))‖ := by
      simp [mul_assoc, norm_mul]
    have hfg :
        ‖f.toSchwartz t‖ * ‖g.toSchwartz (x - t)‖ ≤
          (Cf * Real.exp (- (1 / 2 + εf) * |t|)) * (Cg * Real.exp (- (1 / 2 + εg) * |x - t|)) := by
      refine mul_le_mul hf' hg' (norm_nonneg _) ?_
      exact mul_nonneg hCf0 (le_of_lt (Real.exp_pos _))
    have hfg_nonneg :
        0 ≤ (Cf * Real.exp (- (1 / 2 + εf) * |t|)) * (Cg * Real.exp (- (1 / 2 + εg) * |x - t|)) := by
      have hfpos : 0 ≤ Cf * Real.exp (- (1 / 2 + εf) * |t|) :=
        mul_nonneg hCf0 (le_of_lt (Real.exp_pos _))
      have hgpos : 0 ≤ Cg * Real.exp (- (1 / 2 + εg) * |x - t|) :=
        mul_nonneg hCg0 (le_of_lt (Real.exp_pos _))
      exact mul_nonneg hfpos hgpos
    have hprod :
        (‖f.toSchwartz t‖ * ‖g.toSchwartz (x - t)‖) * ‖Complex.exp ((s - 0.5) * (x : ℂ))‖ ≤
          ((Cf * Real.exp (- (1 / 2 + εf) * |t|)) * (Cg * Real.exp (- (1 / 2 + εg) * |x - t|))) *
            Real.exp ((1 / 2 : ℝ) * |x|) := by
      refine mul_le_mul hfg hExp (norm_nonneg _) hfg_nonneg
    have hconst : 0 ≤ Cf * Cg := mul_nonneg hCf0 hCg0
    have hblock := mul_le_mul_of_nonneg_left hexp_dom hconst
    have hfinal :
        ‖f.toSchwartz t‖ * ‖g.toSchwartz (x - t)‖ * ‖Complex.exp ((s - 0.5) * (x : ℂ))‖ ≤
          (Cf * Cg) * (Real.exp (-ε * |t|) * Real.exp (-ε * |x - t|)) := by
      -- `hprod` gives the intermediate bound; then `hblock` absorbs the extra exponential.
      have htmp :
          ‖f.toSchwartz t‖ * ‖g.toSchwartz (x - t)‖ * ‖Complex.exp ((s - 0.5) * (x : ℂ))‖ ≤
            (Cf * Cg) *
              (Real.exp (- (1 / 2 + εf) * |t|) * Real.exp (- (1 / 2 + εg) * |x - t|) *
                Real.exp ((1 / 2 : ℝ) * |x|)) := by
        have : ((Cf * Real.exp (- (1 / 2 + εf) * |t|)) * (Cg * Real.exp (- (1 / 2 + εg) * |x - t|))) *
              Real.exp ((1 / 2 : ℝ) * |x|) =
            (Cf * Cg) *
              (Real.exp (- (1 / 2 + εf) * |t|) * Real.exp (- (1 / 2 + εg) * |x - t|) *
                Real.exp ((1 / 2 : ℝ) * |x|)) := by
          ring_nf
        exact (by simpa [mul_assoc, mul_left_comm, mul_comm, this] using hprod)
      exact htmp.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hblock)
    -- Conclude and rewrite the envelope.
    have : ‖f.toSchwartz t * g.toSchwartz (x - t) * Complex.exp ((s - 0.5) * (x : ℂ))‖ ≤
        (Cf * Cg) * (Real.exp (-ε * |t|) * Real.exp (-ε * |x - t|)) := by
      simpa [hnorm, mul_assoc] using hfinal
    simpa [Function.uncurry, h, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using this

  -- Finish by domination.
  refine MeasureTheory.Integrable.mono' henv_int hmeas ?_
  exact Filter.Eventually.of_forall hdom

/-- Convolution theorem for the Weil transform, under a product-measure integrability hypothesis. -/
theorem weilTransform_convolution_of_integrable (f g : WeilTestFunction) (s : ℂ)
    (hF :
      Integrable
        (Function.uncurry fun x t : ℝ =>
          f.toSchwartz t * g.toSchwartz (x - t) * Complex.exp ((s - 0.5) * x))
        (volume.prod volume)) :
    (convolution f g).weilTransform s = f.weilTransform s * g.weilTransform s := by
  -- Reduce to the Schwartz-level theorem (which is proved under the same hypothesis).
  simpa [WeilTestFunction.weilTransform, convolution, ExplicitFormula.weilTransform, schwartzConv_apply] using
    (ExplicitFormula.weilTransform_schwartzConv_of_integrable (f := f.toSchwartz) (g := g.toSchwartz) (s := s) hF)

/--
Convolution theorem for the Weil transform on the critical strip `0 ≤ Re(s) ≤ 1`.

This is the unconditional (no-extra-hypotheses) version used in Route 3: the needed Fubini/Tonelli
integrability is discharged from the exponential decay axioms in `WeilTestFunction.decay`.
-/
theorem weilTransform_convolution (f g : WeilTestFunction) (s : ℂ)
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    (convolution f g).weilTransform s = f.weilTransform s * g.weilTransform s := by
  refine weilTransform_convolution_of_integrable (f := f) (g := g) (s := s) ?_
  exact integrable_weilTransform_convolution_integrand (f := f) (g := g) (s := s) hs0 hs1

/-- Reflection intertwines the Weil transform by `s ↦ 1 - s`.
    Proved: uses change of variables `u = -x`. -/
theorem weilTransform_reflection (f : WeilTestFunction) (s : ℂ) :
    (reflection f).weilTransform s = f.weilTransform (1 - s) := by
  simp only [weilTransform, reflection]
  -- The Schwartz-level proof gives us most of the work
  exact ExplicitFormula.weilTransform_reflection f.toSchwartz s

end WeilTestFunction

end ExplicitFormula
end RiemannRecognitionGeometry
