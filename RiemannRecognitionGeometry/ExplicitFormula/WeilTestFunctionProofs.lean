/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.VitaliCaratheodory
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Proof Components for WeilTestFunction

This file provides the proofs that `WeilTestFunction` is closed under
reflection and conjugation, along with the corresponding transform identities.

## Main Results

* `reflectSchwartz` - Reflection of a Schwartz function is Schwartz
* `conjSchwartz` - Complex conjugation of a Schwartz function is Schwartz
* `decay_preserved_by_reflection` - Exponential decay is preserved under reflection
* `decay_preserved_by_conjugation` - Exponential decay is preserved under conjugation
* `weilTransform_reflection` - The Weil transform satisfies `Φ(f(-·))(s) = Φ(f)(1-s)`

## Status

- **Reflection and conjugation**: Fully proved for Schwartz functions.
- **Decay preservation**: Fully proved for both function and Fourier decay.
- **Fourier transform identities**: Fully proved (`ℱ[f(-·)](ξ) = ℱ[f](-ξ)` and
  `ℱ[conj ∘ f](ξ) = conj(ℱ[f](-ξ))`).
- **Convolution**: Not proved here; requires separate development.
-/

noncomputable section

open scoped BigOperators Real Complex FourierTransform Convolution
open Complex Real MeasureTheory SchwartzMap Topology Filter Set Asymptotics

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

/-! ## Basic Definitions -/

/-- The reflection equivalence on ℝ: x ↦ -x -/
def negEquiv : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.neg ℝ

/-- Key identity: `starRingEnd ℂ` equals `Complex.conjCLE` as functions. -/
lemma starRingEnd_eq_conjCLE : (starRingEnd ℂ : ℂ → ℂ) = Complex.conjCLE := rfl

/-! ## Schwartz Function Constructions -/

/-- Complex conjugation of a Schwartz function: `f ↦ conj ∘ f`.

This is proved by showing that `Complex.conjCLE` (complex conjugation as a
continuous ℝ-linear equivalence) preserves smoothness and decay properties. -/
def conjSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := {
  toFun := fun x => starRingEnd ℂ (f x)
  smooth' := by
    refine ContDiff.comp ?_ f.smooth'
    exact Complex.conjCLE.contDiff
  decay' := fun k n => by
    obtain ⟨C, hC⟩ := f.decay' k n
    use C
    intro x
    have hsmooth_at := f.smooth'.contDiffAt (x := x)
    have heq : (fun x => starRingEnd ℂ (f x)) = (Complex.conjCLE : ℂ → ℂ) ∘ f.toFun := rfl
    rw [heq]
    have hn_le : (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have hderiv := ContinuousLinearMap.iteratedFDeriv_comp_left
        Complex.conjCLE.toContinuousLinearMap hsmooth_at (i := n) hn_le
    simp only [ContinuousLinearEquiv.coe_coe] at hderiv
    rw [hderiv]
    calc ‖x‖ ^ k * ‖Complex.conjCLE.toContinuousLinearMap.compContinuousMultilinearMap
            (iteratedFDeriv ℝ n f.toFun x)‖
        ≤ ‖x‖ ^ k * (‖Complex.conjCLE.toContinuousLinearMap‖ *
            ‖iteratedFDeriv ℝ n f.toFun x‖) := by
          gcongr
          exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ ‖x‖ ^ k * (1 * ‖iteratedFDeriv ℝ n f.toFun x‖) := by
          gcongr
          have : ‖Complex.conjCLE.toContinuousLinearMap‖ ≤ 1 := by
            rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
            intro z
            simp [Complex.abs_conj]
          exact this
      _ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖ := by ring
      _ ≤ C := hC x
}

/-- Reflection of a Schwartz function: `f ↦ f(-·)`.

This uses `compCLMOfContinuousLinearEquiv` with the negation equivalence. -/
def reflectSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f

/-- Evaluation lemma for reflected Schwartz functions. -/
lemma reflectSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    reflectSchwartz f x = f (-x) := by
  simp only [reflectSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
             ContinuousLinearEquiv.neg_apply, ContinuousLinearEquiv.coe_coe]
  rfl

/-- Evaluation lemma for conjugated Schwartz functions. -/
lemma conjSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    conjSchwartz f x = starRingEnd ℂ (f x) := rfl

/-! ## Weil Transform -/

/-- The Weil transform `Φ(s)`: a bilateral Laplace transform centered at `s = 1/2`. -/
def weilTransform (f : SchwartzMap ℝ ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, f x * Complex.exp ((s - 0.5) * x)

/-- Reflection intertwines the Weil transform by `s ↦ 1 - s`.

This is the key transform identity: `Φ(f(-·))(s) = Φ(f)(1 - s)`.

The proof uses the substitution `u = -x` and the fact that
`(s - 1/2) * (-u) = (1 - s - 1/2) * u`. -/
lemma weilTransform_reflection (f : SchwartzMap ℝ ℂ) (s : ℂ) :
    weilTransform (reflectSchwartz f) s = weilTransform f (1 - s) := by
  simp only [weilTransform]
  have h1 : ∀ x, reflectSchwartz f x = f (-x) := reflectSchwartz_apply f
  simp only [h1]
  have h2 : ∫ (x : ℝ), f (-x) * Complex.exp ((s - 0.5) * ↑x) =
            ∫ (u : ℝ), f u * Complex.exp ((s - 0.5) * ↑(-u)) := by
    rw [← integral_neg_eq_self (fun u => f u * Complex.exp ((s - 0.5) * ↑(-u)))]
    simp only [neg_neg]
  rw [h2]
  congr 1
  ext u
  congr 1
  simp only [Complex.ofReal_neg, mul_neg]
  ring

/-! ## Decay Preservation -/

/-- Reflection preserves exponential decay. -/
lemma decay_preserved_by_reflection {f : SchwartzMap ℝ ℂ}
    (hdecay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|)) :
    ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖reflectSchwartz f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|) := by
  obtain ⟨C, ε, hε, hbound⟩ := hdecay
  refine ⟨C, ε, hε, ?_⟩
  intro x
  rw [reflectSchwartz_apply]
  have h := hbound (-x)
  simp only [abs_neg] at h
  exact h

/-- Conjugation preserves exponential decay. -/
lemma decay_preserved_by_conjugation {f : SchwartzMap ℝ ℂ}
    (hdecay : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|)) :
    ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖conjSchwartz f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|) := by
  obtain ⟨C, ε, hε, hbound⟩ := hdecay
  refine ⟨C, ε, hε, ?_⟩
  intro x
  rw [conjSchwartz_apply]
  rw [Complex.norm_eq_abs, Complex.abs_conj, ← Complex.norm_eq_abs]
  exact hbound x

/-! ## Fourier Transform Properties

The following lemmas relate Fourier transforms of reflected/conjugated functions.
These are standard results in Fourier analysis:
- `ℱ[f(-·)](ξ) = ℱ[f](-ξ)`
- `ℱ[conj ∘ f](ξ) = conj(ℱ[f](-ξ))`
-/

/-- The Fourier integral of a reflected function equals the Fourier integral at the negated frequency.
This is a key property: `ℱ[f(-·)](w) = ℱ[f](-w)`.
The proof uses the substitution `u = -v` and the invariance of Lebesgue measure under negation. -/
lemma Real_fourierIntegral_comp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (w : ℝ) :
    Real.fourierIntegral (f ∘ Neg.neg) w = Real.fourierIntegral f (-w) := by
  simp only [Real.fourierIntegral, VectorFourier.fourierIntegral, Function.comp_apply]
  -- Use substitution u = -v, which is valid since Lebesgue measure is invariant under negation
  have h : ∫ (v : ℝ), Real.fourierChar (-((innerₗ ℝ) v) w) • f (-v) =
           ∫ (u : ℝ), Real.fourierChar (-((innerₗ ℝ) (-u)) w) • f u := by
    rw [← integral_neg_eq_self]
    simp only [neg_neg]
  rw [h]
  congr 1
  ext u
  congr 1
  congr 1
  -- The key algebraic identity: -(innerₗ ℝ (-u) w) = -(innerₗ ℝ u (-w))
  -- Both equal inner u w since inner is bilinear and we have double negation
  simp only [innerₗ_apply, inner_neg_left, inner_neg_right, neg_neg]

/-- The Fourier transform of a reflected Schwartz function. -/
lemma fourierTransform_reflect (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierTransformCLM ℂ (reflectSchwartz f) ξ = fourierTransformCLM ℂ f (-ξ) := by
  simp only [fourierTransformCLM_apply]
  -- Show that reflectSchwartz gives f ∘ neg
  have h : (reflectSchwartz f : ℝ → ℂ) = (f : ℝ → ℂ) ∘ Neg.neg := by
    ext x
    simp only [reflectSchwartz, compCLMOfContinuousLinearEquiv_apply,
               ContinuousLinearEquiv.neg_apply, ContinuousLinearEquiv.coe_coe,
               Function.comp_apply]
  rw [h]
  exact Real_fourierIntegral_comp_neg (f : ℝ → ℂ) ξ

/-- Fourier decay is preserved under reflection. -/
lemma ft_decay_preserved_by_reflection {f : SchwartzMap ℝ ℂ}
    (hft_decay : ∃ (C' ε' : ℝ), 0 < ε' ∧
      ∀ ξ, ‖fourierTransformCLM ℂ f ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|)) :
    ∃ (C' ε' : ℝ), 0 < ε' ∧
      ∀ ξ, ‖fourierTransformCLM ℂ (reflectSchwartz f) ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|) := by
  obtain ⟨C', ε', hε', hbound⟩ := hft_decay
  refine ⟨C', ε', hε', ?_⟩
  intro ξ
  rw [fourierTransform_reflect]
  have h := hbound (-ξ)
  simp only [abs_neg] at h
  exact h

/-- For elements on the unit circle, complex conjugation equals the inverse.
This follows from the fact that `z * conj(z) = |z|² = 1` for `|z| = 1`. -/
lemma Real_fourierChar_conj (t : ℝ) :
    starRingEnd ℂ (Real.fourierChar t : ℂ) = Real.fourierChar (-t) := by
  have h := Circle.coe_inv_eq_conj (Real.fourierChar t)
  rw [← h]
  congr 1
  exact (Real.fourierChar.map_neg_eq_inv t).symm

/-- The Fourier integral of a conjugated function.
The key identity is `ℱ[conj ∘ f](w) = conj(ℱ[f](-w))`.
This uses that `conj(e^{2πit}) = e^{-2πit}` and that conjugation commutes with integration. -/
lemma Real_fourierIntegral_conj (f : ℝ → ℂ) (w : ℝ) :
    Real.fourierIntegral (starRingEnd ℂ ∘ f) w = starRingEnd ℂ (Real.fourierIntegral f (-w)) := by
  simp only [Real.fourierIntegral, VectorFourier.fourierIntegral, Function.comp_apply]
  simp only [Circle.smul_def, smul_eq_mul]
  -- Key step: show the integrands are related by conjugation
  have heq : ∀ v, (Real.fourierChar (-(innerₗ ℝ v w)) : ℂ) * (starRingEnd ℂ (f v)) =
             starRingEnd ℂ ((Real.fourierChar (-(innerₗ ℝ v (-w))) : ℂ) * f v) := by
    intro v
    rw [map_mul]
    congr 1
    -- The character transforms: conj(e^{2πi(vw)}) = e^{-2πi(vw)} = e^{2πi(-(vw))}
    rw [Real_fourierChar_conj (-(innerₗ ℝ v (-w)))]
    simp only [innerₗ_apply, inner_neg_right, neg_neg]
  simp only [heq]
  -- Conjugation commutes with integration
  rw [← integral_conj]

/-- The Fourier transform of a conjugated Schwartz function.
This is proved using `Real_fourierIntegral_conj`. -/
lemma fourierTransform_conj (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    fourierTransformCLM ℂ (conjSchwartz f) ξ = starRingEnd ℂ (fourierTransformCLM ℂ f (-ξ)) := by
  simp only [fourierTransformCLM_apply]
  have h : (conjSchwartz f : ℝ → ℂ) = starRingEnd ℂ ∘ (f : ℝ → ℂ) := by
    ext x; exact conjSchwartz_apply f x
  rw [h]
  exact Real_fourierIntegral_conj (f : ℝ → ℂ) ξ

/-- Fourier decay is preserved under conjugation. -/
lemma ft_decay_preserved_by_conjugation {f : SchwartzMap ℝ ℂ}
    (hft_decay : ∃ (C' ε' : ℝ), 0 < ε' ∧
      ∀ ξ, ‖fourierTransformCLM ℂ f ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|)) :
    ∃ (C' ε' : ℝ), 0 < ε' ∧
      ∀ ξ, ‖fourierTransformCLM ℂ (conjSchwartz f) ξ‖ ≤ C' * Real.exp (- (1 / 2 + ε') * |ξ|) := by
  obtain ⟨C', ε', hε', hbound⟩ := hft_decay
  refine ⟨C', ε', hε', ?_⟩
  intro ξ
  rw [fourierTransform_conj]
  simp only [RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.norm_eq_abs, Complex.abs_conj]
  have h := hbound (-ξ)
  simp only [abs_neg, Complex.norm_eq_abs] at h
  exact h

/-! ## Convolution

The additive convolution `(f ⋆ g)(x) = ∫ f(t) g(x-t) dt` is fundamental for the
Weil transform. The key theorem is that the Weil transform converts convolution
to pointwise multiplication.

**Note**: Proving that convolution of Schwartz functions is Schwartz, and that
it preserves the specific exponential decay conditions of WeilTestFunction,
requires substantial analytical machinery. The key results are sketched here.
-/

/-- Additive convolution of two Schwartz functions at a point.
This is the standard definition: `(f ⋆ g)(x) = ∫ f(t) g(x-t) dt`. -/
def schwartzConvAt (f g : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, f t * g (x - t)

/-!
### Pointwise multiplication and Fourier-defined convolution on Schwartz space

Mathlib provides:
- a continuous linear equivalence `SchwartzMap.fourierTransformCLE` on Schwartz functions, and
- a construction `SchwartzMap.bilinLeftCLM` to apply a continuous bilinear map pointwise against a
  function of temperate growth.

We use these to define a **Schwartz-valued convolution** by transporting pointwise multiplication
through the Fourier transform. This gives a Schwartz function automatically, and we later prove it
agrees pointwise with the usual integral convolution `schwartzConvAt`.
-/

/-- Any Schwartz function has temperate growth (polynomial bounds on all derivatives). -/
lemma schwartz_hasTemperateGrowth (f : SchwartzMap ℝ ℂ) : Function.HasTemperateGrowth (f : ℝ → ℂ) := by
  refine ⟨f.smooth', ?_⟩
  intro n
  obtain ⟨C, hC⟩ := f.decay' 0 n
  refine ⟨0, C, ?_⟩
  intro x
  have hx := hC x
  -- `‖x‖^0 = 1`.
  simpa [pow_zero, one_mul] using hx

/-- Pointwise multiplication of Schwartz functions as a Schwartz function. -/
noncomputable def schwartzMul (f g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (SchwartzMap.bilinLeftCLM (𝕜 := ℂ) (D := ℝ) (E := ℂ) (F := ℂ) (G := ℂ)
      (B := ContinuousLinearMap.mul ℂ ℂ) (g := fun x : ℝ => g x)
      (schwartz_hasTemperateGrowth g)) f

@[simp] lemma schwartzMul_apply (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzMul f g x = f x * g x := by
  -- Unfold through `bilinLeftCLM`/`mkCLM`: evaluation is definitional.
  rfl

/-- Fourier-defined convolution on Schwartz functions: `𝓕⁻¹(𝓕 f · 𝓕 g)`. -/
noncomputable def schwartzConv (f g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (E := ℂ) (V := ℝ)).symm
    (schwartzMul (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) f)
                 (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) g))

@[simp] lemma fourierTransform_schwartzConv (f g : SchwartzMap ℝ ℂ) :
    SchwartzMap.fourierTransformCLM (𝕜 := ℂ) (schwartzConv f g) =
      schwartzMul (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) f)
                  (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) g) := by
  -- Work with the continuous linear equivalence `fourierTransformCLE` directly:
  -- `e (e.symm h) = h`. Then unfold `e` as `fourierTransformCLM`.
  have hEq :
      (SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (E := ℂ) (V := ℝ)) (schwartzConv f g) =
        schwartzMul (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) f)
          (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) g) := by
    -- This is definitional after unfolding `schwartzConv`.
    simpa [schwartzConv]
  -- Rewrite the left-hand side using `fourierTransformCLE_apply`.
  simpa [SchwartzMap.fourierTransformCLE_apply] using hEq

/-- Schwartz functions are bounded. -/
lemma schwartz_bounded (g : SchwartzMap ℝ ℂ) : ∃ M, ∀ y, ‖g y‖ ≤ M := by
  obtain ⟨C, hC⟩ := g.decay' 0 0
  use C
  intro y
  specialize hC y
  simp only [pow_zero, one_mul] at hC
  -- The decay' condition gives bounds on iteratedFDeriv, which at n=0 is the function itself
  have h : ‖iteratedFDeriv ℝ 0 g.toFun y‖ = ‖g y‖ := by
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply, LinearIsometryEquiv.norm_map]
    rfl
  rwa [h] at hC

/-- The convolution integrand is integrable for Schwartz functions.
This follows from the rapid decay of Schwartz functions. -/
lemma schwartzConv_integrable (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    Integrable (fun t => f t * g (x - t)) := by
  -- f is integrable and g is bounded, so the product is integrable
  have hf_int : Integrable (f : ℝ → ℂ) := f.integrable
  obtain ⟨M, hM⟩ := schwartz_bounded g
  have hM_pos : 0 ≤ M := by
    have := hM 0
    exact le_trans (norm_nonneg _) this
  -- Use Integrable.mono: bound ‖f(t) * g(x-t)‖ ≤ M * ‖f(t)‖
  have hf_norm_int : Integrable (fun t => M * ‖f t‖) := hf_int.norm.const_mul M
  apply Integrable.mono' hf_norm_int
  · exact hf_int.aestronglyMeasurable.mul
      (g.continuous.aestronglyMeasurable.comp_measurable (measurable_const.sub measurable_id))
  · filter_upwards with t
    calc ‖f t * g (x - t)‖ = ‖f t‖ * ‖g (x - t)‖ := norm_mul _ _
      _ ≤ ‖f t‖ * M := by gcongr; exact hM _
      _ = M * ‖f t‖ := mul_comm _ _

/-- Fourier convolution theorem (function-level): `𝓕(f ⋆ g) = 𝓕 f · 𝓕 g` for Schwartz functions. -/
theorem fourierIntegral_schwartzConvAt (f g : SchwartzMap ℝ ℂ) (w : ℝ) :
    Real.fourierIntegral (fun x : ℝ => schwartzConvAt f g x) w =
      Real.fourierIntegral (f : ℝ → ℂ) w * Real.fourierIntegral (g : ℝ → ℂ) w := by
  -- Unfold `Real.fourierIntegral` into the kernel form and distribute the kernel inside.
  have hK_norm : ∀ t : ℝ, ‖(Real.fourierChar t : ℂ)‖ = 1 := by
    intro t
    simpa using (Circle.abs_coe (Real.fourierChar t))
  -- Start from the definition.
  simp [Real.fourierIntegral, VectorFourier.fourierIntegral, schwartzConvAt,
    Circle.smul_def, smul_eq_mul, innerₗ_apply]
  -- Distribute the kernel into the inner integral.
  have h_distr :
      ∀ x : ℝ,
        (Real.fourierChar (-(x * w)) : ℂ) * (∫ t : ℝ, f t * g (x - t)) =
          ∫ t : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t)) := by
    intro x
    simpa [mul_assoc] using
      (MeasureTheory.integral_mul_left (μ := (volume : Measure ℝ))
        (r := (Real.fourierChar (-(x * w)) : ℂ))
        (f := fun t : ℝ => f t * g (x - t))).symm
  simp_rw [h_distr]

  -- Swap integrals using Fubini/Tonelli; prove product-measure integrability via the convolution integrand.
  have hf_int : Integrable (f : ℝ → ℂ) := f.integrable
  have hg_int : Integrable (g : ℝ → ℂ) := g.integrable
  have hbase :
      Integrable
        (Function.uncurry fun x t : ℝ => f t * g (x - t))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    -- This is the standard integrability statement for the convolution integrand.
    simpa [Function.uncurry, ContinuousLinearMap.mul_apply] using
      (hf_int.convolution_integrand (L := ContinuousLinearMap.mul ℂ ℂ)
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) hg_int)
  have hF :
      Integrable
        (Function.uncurry fun x t : ℝ =>
          (Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t)))
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    -- Multiply the integrable convolution integrand by a bounded kernel of norm 1.
    refine MeasureTheory.Integrable.mono hbase ?_ ?_
    · -- measurability
      have hmeasK :
          AEStronglyMeasurable (fun p : ℝ × ℝ => (Real.fourierChar (-(p.1 * w)) : ℂ))
            ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
        -- This kernel is continuous (hence measurable), so it is a.e.-strongly measurable.
        have hcont : Continuous (fun p : ℝ × ℝ => (Real.fourierChar (-(p.1 * w)) : ℂ)) := by
          -- continuity of `p ↦ -(p.1 * w)` and of `Real.fourierChar`, and of the coercion `Circle → ℂ`.
          have h1 : Continuous (fun p : ℝ × ℝ => -(p.1 * w)) :=
            (continuous_fst.mul continuous_const).neg
          have h2 : Continuous (fun x : ℝ => (Real.fourierChar x : ℂ)) := by
            simpa using (continuous_subtype_val.comp Real.continuous_fourierChar)
          exact h2.comp h1
        exact hcont.aestronglyMeasurable
      exact hmeasK.mul hbase.aestronglyMeasurable
    · -- norm bound
      filter_upwards with p
      rcases p with ⟨x, t⟩
      have hnorm : ‖(Real.fourierChar (-(x * w)) : ℂ)‖ = 1 := hK_norm (-(x * w))
      calc
        ‖(Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t))‖
            = ‖(Real.fourierChar (-(x * w)) : ℂ)‖ * ‖f t * g (x - t)‖ := by
                simpa [norm_mul]
        _ = ‖f t * g (x - t)‖ := by simp [hnorm]
        _ = ‖Function.uncurry (fun x t : ℝ => f t * g (x - t)) (x, t)‖ := by
              rfl
        _ ≤ ‖Function.uncurry (fun x t : ℝ => f t * g (x - t)) (x, t)‖ := by
              exact le_rfl

  have hswap :
      (∫ x : ℝ, ∫ t : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t))) =
        ∫ t : ℝ, ∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t)) := by
    simpa [Function.uncurry] using
      (MeasureTheory.integral_integral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (f := fun x t : ℝ => (Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t))) hF)
  rw [hswap]

  -- Compute the inner integral by translation invariance and factorization of the Fourier character.
  have h_inner :
      ∀ t : ℝ,
        (∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t))) =
          (f t * (Real.fourierChar (-(t * w)) : ℂ)) * Real.fourierIntegral (g : ℝ → ℂ) w := by
    intro t
    -- Pull out the constant `f t` from the `x`-integral.
    have h_pull :
        (∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t))) =
          f t * ∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * g (x - t) := by
      -- reassociate to expose `f t` as a constant factor
      have :
          (fun x : ℝ => (Real.fourierChar (-(x * w)) : ℂ) * (f t * g (x - t))) =
            fun x : ℝ => (f t) * ((Real.fourierChar (-(x * w)) : ℂ) * g (x - t)) := by
        funext x
        ring_nf
      simp [this, MeasureTheory.integral_mul_left]
    rw [h_pull]

    -- Change variables `x ↦ x - t` using translation invariance.
    have h_sub :
        (∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * g (x - t)) =
          ∫ x : ℝ, (Real.fourierChar (-((x + t) * w)) : ℂ) * g x := by
      -- Let `H x := fourierChar(-((x+t)*w)) * g x`. Then `H (x - t) = fourierChar(-(x*w)) * g(x - t)`.
      have h_eq :
          (fun x : ℝ => (Real.fourierChar (-(x * w)) : ℂ) * g (x - t)) =
            fun x : ℝ => (fun u : ℝ => (Real.fourierChar (-((u + t) * w)) : ℂ) * g u) (x - t) := by
        funext x
        simp [sub_add_cancel, add_mul, mul_add]
      simpa [h_eq] using
        (MeasureTheory.integral_sub_right_eq_self
          (μ := (volume : Measure ℝ))
          (f := fun u : ℝ => (Real.fourierChar (-((u + t) * w)) : ℂ) * g u) t)
    rw [h_sub]

    -- Factor the character: `χ(-(x+t)w) = χ(-xw) * χ(-tw)`.
    have h_char :
        (fun x : ℝ => (Real.fourierChar (-((x + t) * w)) : ℂ) * g x) =
          fun x : ℝ => ((Real.fourierChar (-(x * w)) : ℂ) * (Real.fourierChar (-(t * w)) : ℂ)) * g x := by
      funext x
      -- Use that `fourierChar` is an additive character: `𝐞(a+b)=𝐞(a)*𝐞(b)`.
      have hadd : -((x + t) * w) = (-(x * w)) + (-(t * w)) := by ring
      have hmulC :
          (Real.fourierChar (-((x + t) * w)) : ℂ) =
            (Real.fourierChar (-(x * w)) : ℂ) * (Real.fourierChar (-(t * w)) : ℂ) := by
        -- Start from the `Circle` identity and coerce to `ℂ`.
        have hmul : Real.fourierChar (-(x * w) + -(t * w)) =
            Real.fourierChar (-(x * w)) * Real.fourierChar (-(t * w)) :=
          Real.fourierChar.map_add_eq_mul (-(x * w)) (-(t * w))
        -- Rewrite the argument using `hadd` and coerce to `ℂ`.
        -- Coercion `Circle → ℂ` is a monoid hom, so `simp` will turn products into products.
        simpa [hadd] using congrArg (fun z : Circle => (z : ℂ)) hmul
      -- Multiply both sides by `g x` and reassociate.
      -- Some simp-normal forms use `w * x` instead of `x * w`; normalize before closing.
      have hmulC' :
          (Real.fourierChar (-(w * (x + t))) : ℂ) =
            (Real.fourierChar (-(w * x)) : ℂ) * (Real.fourierChar (-(w * t)) : ℂ) := by
        -- commute to match `hmulC`
        simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using hmulC
      simpa [hmulC', mul_assoc, mul_left_comm, mul_comm]
    -- Pull out the constant `fourierChar (-(t*w))`.
    have h_pull2 :
        (∫ x : ℝ, (Real.fourierChar (-((x + t) * w)) : ℂ) * g x) =
          (Real.fourierChar (-(t * w)) : ℂ) * ∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * g x := by
      -- Rewrite the integrand using `h_char`, then pull out the constant factor.
      have h1 :
          (∫ x : ℝ, (Real.fourierChar (-((x + t) * w)) : ℂ) * g x) =
            ∫ x : ℝ, ((Real.fourierChar (-(x * w)) : ℂ) * (Real.fourierChar (-(t * w)) : ℂ)) * g x := by
        simpa [h_char]
      -- Rearrange so the `t`-dependent factor is on the left, then use `integral_mul_left`.
      have h2 :
          (∫ x : ℝ, ((Real.fourierChar (-(x * w)) : ℂ) * (Real.fourierChar (-(t * w)) : ℂ)) * g x) =
            (Real.fourierChar (-(t * w)) : ℂ) * ∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * g x := by
        -- commute and reassociate inside the integral
        -- `(a*b)*c = b*(a*c)` since `ℂ` is commutative.
        have h_reassoc :
            (fun x : ℝ =>
                ((Real.fourierChar (-(x * w)) : ℂ) * (Real.fourierChar (-(t * w)) : ℂ)) * g x) =
              fun x : ℝ =>
                (Real.fourierChar (-(t * w)) : ℂ) * ((Real.fourierChar (-(x * w)) : ℂ) * g x) := by
          funext x
          ring_nf
        simp [h_reassoc, MeasureTheory.integral_mul_left]
      exact h1.trans h2
    -- Finish the computation: recognize the remaining integral as `Real.fourierIntegral g w`.
    -- In simp-normal form, the kernel may appear as `-(w * x)`; rewrite using commutativity.
    have h_pull2' :
        (∫ x : ℝ, (Real.fourierChar (-(w * (x + t))) : ℂ) * g x) =
          (Real.fourierChar (-(w * t)) : ℂ) * ∫ x : ℝ, (Real.fourierChar (-(w * x)) : ℂ) * g x := by
      -- Rewrite `w * (x+t)` as `(x+t) * w`, etc., then use `h_pull2`.
      simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h_pull2
    simp [h_pull2', Real.fourierIntegral, VectorFourier.fourierIntegral, Circle.smul_def,
      smul_eq_mul, innerₗ_apply, mul_assoc, mul_left_comm, mul_comm]

  -- Substitute the inner computation and separate integrals.
  simp_rw [h_inner]
  -- Pull out `Real.fourierIntegral g w` (constant in `t`).
  have h_out :
      (∫ t : ℝ, (f t * (Real.fourierChar (-(t * w)) : ℂ)) * Real.fourierIntegral (g : ℝ → ℂ) w) =
        (∫ t : ℝ, (Real.fourierChar (-(t * w)) : ℂ) * f t) * Real.fourierIntegral (g : ℝ → ℂ) w := by
    -- Commute factors to match the Fourier integral definition, then use `integral_mul_right`.
    have hswap' :
        (fun t : ℝ => (f t * (Real.fourierChar (-(t * w)) : ℂ)) * Real.fourierIntegral (g : ℝ → ℂ) w) =
          fun t : ℝ => ((Real.fourierChar (-(t * w)) : ℂ) * f t) * Real.fourierIntegral (g : ℝ → ℂ) w := by
      funext t
      ring_nf
    -- Now pull out the constant `Real.fourierIntegral g w`.
    simpa [hswap'] using
      (MeasureTheory.integral_mul_right (μ := (volume : Measure ℝ))
        (r := Real.fourierIntegral (g : ℝ → ℂ) w)
        (f := fun t : ℝ => (Real.fourierChar (-(t * w)) : ℂ) * f t))
  -- Conclude by identifying the first integral as `Real.fourierIntegral f w`.
  simpa [Real.fourierIntegral, VectorFourier.fourierIntegral, Circle.smul_def, smul_eq_mul,
    innerₗ_apply, mul_assoc, mul_left_comm, mul_comm] using h_out

/-- The Fourier-defined Schwartz convolution agrees pointwise with the usual integral convolution. -/
theorem schwartzConv_apply (f g : SchwartzMap ℝ ℂ) (x : ℝ) :
    schwartzConv f g x = schwartzConvAt f g x := by
  -- Use Fourier inversion on the continuous integrable function `x ↦ schwartzConvAt f g x`.
  let h : ℝ → ℂ := fun x : ℝ => schwartzConvAt f g x
  have h_cont : Continuous h := by
    -- `h` is a convolution of an integrable function with a bounded continuous function.
    have hf_int : Integrable (f : ℝ → ℂ) := f.integrable
    obtain ⟨M, hM⟩ := schwartz_bounded g
    have hbg : BddAbove (Set.range fun y : ℝ => ‖(g : ℝ → ℂ) y‖) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact hM y
    -- Express `h` as a `MeasureTheory.convolution` to use the continuity lemma.
    have : h = (fun x : ℝ =>
        ((f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] (g : ℝ → ℂ)) x) := by
      funext x
      simp [h, schwartzConvAt, MeasureTheory.convolution_mul]
    -- Apply the general continuity theorem for convolution.
    have hcont' :
        Continuous ((f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] (g : ℝ → ℂ)) := by
      simpa using
        (BddAbove.continuous_convolution_right_of_integrable (L := ContinuousLinearMap.mul ℂ ℂ)
          (μ := (volume : Measure ℝ)) (f := (f : ℝ → ℂ)) (g := (g : ℝ → ℂ))
          hbg hf_int g.continuous)
    simpa [this] using hcont'
  have h_int : Integrable h := by
    -- `h` is integrable as a convolution of two integrable functions.
    have hf_int : Integrable (f : ℝ → ℂ) := f.integrable
    have hg_int : Integrable (g : ℝ → ℂ) := g.integrable
    -- Use `Integrable.integrable_convolution`.
    have : Integrable ((f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, (volume : Measure ℝ)] (g : ℝ → ℂ))
        (volume : Measure ℝ) := by
      simpa using
        (MeasureTheory.Integrable.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ)
          (μ := (volume : Measure ℝ)) (f := (f : ℝ → ℂ)) (g := (g : ℝ → ℂ)) hf_int hg_int)
    -- Identify `h` with this convolution.
    simpa [h, schwartzConvAt, MeasureTheory.convolution_mul] using this
  have hF_int : Integrable (Real.fourierIntegral h) := by
    -- Use the Fourier convolution theorem and boundedness of `𝓕 g`.
    have hEq : Real.fourierIntegral h = fun w : ℝ =>
        Real.fourierIntegral (f : ℝ → ℂ) w * Real.fourierIntegral (g : ℝ → ℂ) w := by
      funext w
      simpa [h] using fourierIntegral_schwartzConvAt f g w
    -- `𝓕 f` is integrable and `𝓕 g` is bounded, so the product is integrable.
    have hfF_int : Integrable (Real.fourierIntegral (f : ℝ → ℂ)) := by
      simpa using (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) f).integrable
    obtain ⟨M, hM⟩ := schwartz_bounded (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) g)
    have h_prod_int : Integrable (fun w : ℝ =>
        Real.fourierIntegral (f : ℝ → ℂ) w * Real.fourierIntegral (g : ℝ → ℂ) w) := by
      -- Bound the product by `M * ‖𝓕 f‖`.
      have hf_norm_int : Integrable (fun w : ℝ => M * ‖Real.fourierIntegral (f : ℝ → ℂ) w‖) :=
        hfF_int.norm.const_mul M
      refine MeasureTheory.Integrable.mono' hf_norm_int ?_ ?_
      · exact (hfF_int.aestronglyMeasurable.mul
          ((SchwartzMap.fourierTransformCLM (𝕜 := ℂ) g).continuous.aestronglyMeasurable))
      · filter_upwards with w
        have hMw : ‖Real.fourierIntegral (g : ℝ → ℂ) w‖ ≤ M := by
          -- Rewrite `Real.fourierIntegral g w` as the Schwartz Fourier transform evaluation.
          simpa [SchwartzMap.fourierTransformCLM_apply] using hM w
        calc
          ‖Real.fourierIntegral (f : ℝ → ℂ) w * Real.fourierIntegral (g : ℝ → ℂ) w‖
              = ‖Real.fourierIntegral (f : ℝ → ℂ) w‖ * ‖Real.fourierIntegral (g : ℝ → ℂ) w‖ := by
                  simpa [norm_mul]
          _ ≤ ‖Real.fourierIntegral (f : ℝ → ℂ) w‖ * M := by gcongr
          _ = M * ‖Real.fourierIntegral (f : ℝ → ℂ) w‖ := by ring_nf
    simpa [hEq] using h_prod_int
  -- Fourier inversion gives `𝓕⁻ (𝓕 h) = h`.
  have hinv : Real.fourierIntegralInv (Real.fourierIntegral h) x = h x := by
    have := Continuous.fourier_inversion (f := h) h_cont h_int hF_int
    exact congrArg (fun F : ℝ → ℂ => F x) this
  -- Rewrite the left-hand side as `schwartzConv f g x`, and the right-hand side as `schwartzConvAt`.
  -- First, compute `Real.fourierIntegral h` via the convolution theorem.
  have hEq : Real.fourierIntegral h = fun w : ℝ =>
      Real.fourierIntegral (f : ℝ → ℂ) w * Real.fourierIntegral (g : ℝ → ℂ) w := by
    funext w
    simpa [h] using fourierIntegral_schwartzConvAt f g w
  -- Now unfold `schwartzConv` as an inverse Fourier transform of the product.
  -- `fourierTransformCLE_symm_apply` identifies the inverse with `Real.fourierIntegralInv`.
  have hConv :
      schwartzConv f g x = Real.fourierIntegralInv (Real.fourierIntegral h) x := by
    -- Reduce to `Real.fourierIntegralInv` of the pointwise product.
    -- This is exactly `𝓕⁻ (⇑(schwartzMul (𝓕 f) (𝓕 g)))`, and `hEq` identifies `𝓕 h`.
    -- We rewrite both sides to the same function before applying `rfl`.
    have hsame :
        Real.fourierIntegralInv (fun w : ℝ =>
            Real.fourierIntegral (f : ℝ → ℂ) w * Real.fourierIntegral (g : ℝ → ℂ) w) x =
          Real.fourierIntegralInv (Real.fourierIntegral h) x := by
      simp [hEq]
    -- Unfold `schwartzConv` to `𝓕⁻` of the Schwartz product and use `hsame`.
    simpa [schwartzConv, SchwartzMap.fourierTransformCLE_symm_apply,
      SchwartzMap.fourierTransformCLM_apply, schwartzMul_apply, hsame]
  -- `schwartzMul` is pointwise multiplication, so its coercion agrees with the raw product.
  have hMulFun :
      (fun w : ℝ =>
        (schwartzMul (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) f)
            (SchwartzMap.fourierTransformCLM (𝕜 := ℂ) g)) w) =
        fun w : ℝ => Real.fourierIntegral (f : ℝ → ℂ) w * Real.fourierIntegral (g : ℝ → ℂ) w := by
    funext w
    simp [schwartzMul_apply, SchwartzMap.fourierTransformCLM_apply]
  -- Finish.
  -- Rewrite the inverse Fourier integrals using `hMulFun`.
  simpa [h, hConv, hEq, hMulFun] using hinv

/-!
### Exponential decay is preserved under convolution

If `f` and `g` satisfy the Route-3 exponential decay bound

`‖f x‖ ≤ C * exp (-(1/2+ε) * |x|)`,

then their convolution also satisfies such a bound (with a possibly smaller `ε`).
-/

/-- `exp (-a * |t|)` is integrable on `ℝ` for `a > 0`. -/
lemma integrable_exp_neg_mul_abs (a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => Real.exp (-a * |t|)) := by
  -- Split ℝ into `(-∞,0] ∪ (0,∞)` and use exponential integrability on each side.
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Set.Ioi 0) (volume : Measure ℝ) := by
    -- On `(0,∞)`, `|t| = t`.
    have hbase :
        IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Set.Ioi 0) (volume : Measure ℝ) := by
      simpa using (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) (b := a) ha)
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 ≤ t := le_of_lt ht
    have htabs : |t| = t := abs_of_nonneg ht0
    simp [htabs]

  have hIio : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Set.Iio 0) (volume : Measure ℝ) := by
    -- Transfer integrability from `(0,∞)` using negation.
    have hpos :
        IntegrableOn (fun u : ℝ => Real.exp (-a * u)) (Set.Ioi 0) (volume : Measure ℝ) := by
      simpa using (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) (b := a) ha)
    -- Negation is measure-preserving for Lebesgue measure.
    have hcomp_pre :
        IntegrableOn ((fun u : ℝ => Real.exp (-a * u)) ∘ fun x : ℝ => -x)
          ((fun x : ℝ => -x) ⁻¹' (Set.Ioi 0)) (volume : Measure ℝ) := by
      exact
        (MeasureTheory.MeasurePreserving.integrableOn_comp_preimage
          (Measure.measurePreserving_neg (volume : Measure ℝ))
          (Homeomorph.neg ℝ).measurableEmbedding (f := fun u : ℝ => Real.exp (-a * u))
          (s := Set.Ioi 0)).2 hpos
    have hpre : (fun x : ℝ => -x) ⁻¹' (Set.Ioi (0 : ℝ)) = Set.Iio 0 := by
      ext x; simp
    have hcomp :
        IntegrableOn ((fun u : ℝ => Real.exp (-a * u)) ∘ fun x : ℝ => -x)
          (Set.Iio 0) (volume : Measure ℝ) := by
      simpa [hpre] using hcomp_pre
    -- Rewrite the integrand to `t ↦ exp(-a*|t|)` on `Iio 0`.
    refine hcomp.congr_fun (fun t ht => ?_) measurableSet_Iio
    have ht0 : t ≤ 0 := le_of_lt ht
    have htabs : |t| = -t := abs_of_nonpos ht0
    simp [Function.comp, htabs, mul_assoc, mul_left_comm, mul_comm]

  have hIic : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Set.Iic 0) (volume : Measure ℝ) := by
    -- `Iic 0` differs from `Iio 0` by a null set.
    exact (integrableOn_Iic_iff_integrableOn_Iio (μ := (volume : Measure ℝ))
      (f := fun t : ℝ => Real.exp (-a * |t|)) (b := (0 : ℝ))).2 hIio

  -- Combine the two halves: `Iic 0 ∪ Ioi 0 = univ`.
  have huniv : (Set.Iic (0 : ℝ) ∪ Set.Ioi 0) = (Set.univ : Set ℝ) := by
    ext x
    by_cases hx : x ≤ 0
    · simp [hx]
    · have hx' : 0 < x := lt_of_not_ge hx
      simp [hx, hx']
  have hU : IntegrableOn (fun t : ℝ => Real.exp (-a * |t|)) (Set.univ : Set ℝ) (volume : Measure ℝ) := by
    have := hIic.union hIoi
    simpa [huniv] using this
  -- `IntegrableOn` over `univ` is `Integrable`.
  simpa [MeasureTheory.IntegrableOn, Set.indicator_univ] using hU

/-- Exponential decay is preserved under convolution (Schwartz-level). -/
lemma decay_preserved_by_convolution {f g : SchwartzMap ℝ ℂ}
    (hf : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖f x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|))
    (hg : ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖g x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|)) :
    ∃ (C ε : ℝ), 0 < ε ∧ ∀ x, ‖schwartzConv f g x‖ ≤ C * Real.exp (- (1 / 2 + ε) * |x|) := by
  obtain ⟨Cf, εf, hεf, hfBound⟩ := hf
  obtain ⟨Cg, εg, hεg, hgBound⟩ := hg
  -- Choose a smaller epsilon to make the algebra work uniformly.
  let ε : ℝ := (min εf εg) / 2
  have hε : 0 < ε := by
    have hmin : 0 < min εf εg := lt_min hεf hεg
    have : (0 : ℝ) < (2 : ℝ) := by norm_num
    simpa [ε, div_eq_mul_inv] using (mul_pos hmin (inv_pos.2 this))
  -- The integrable kernel `t ↦ exp(-ε |t|)`.
  have hKint : Integrable (fun t : ℝ => Real.exp (-ε * |t|)) :=
    integrable_exp_neg_mul_abs ε hε
  let K : ℝ := ∫ t : ℝ, Real.exp (-ε * |t|)
  have hK_nonneg : 0 ≤ K := by
    have hnonneg : (∀ᵐ t ∂(volume : Measure ℝ), 0 ≤ Real.exp (-ε * |t|)) :=
      Filter.Eventually.of_forall (fun _ => le_of_lt (Real.exp_pos _))
    simpa [K] using (MeasureTheory.integral_nonneg_of_ae hnonneg)
  -- Build the new constant.
  refine ⟨Cf * Cg * K, ε, hε, ?_⟩
  intro x
  -- Rewrite the Fourier-defined convolution as the usual integral convolution.
  rw [schwartzConv_apply, schwartzConvAt]
  -- Bound the norm of the integral by the integral of the norm.
  have hint : Integrable (fun t : ℝ => f t * g (x - t)) := schwartzConv_integrable f g x
  have hnorm :
      ‖∫ t : ℝ, f t * g (x - t)‖ ≤ ∫ t : ℝ, ‖f t * g (x - t)‖ := by
    exact norm_integral_le_integral_norm _
  refine hnorm.trans ?_
  -- Pointwise bound the integrand norm by an integrable exponential envelope.
  have hCf0 : 0 ≤ Cf := by
    have h0 : ‖f 0‖ ≤ Cf := by
      simpa using (hfBound 0)
    exact le_trans (norm_nonneg _) h0
  have hCg0 : 0 ≤ Cg := by
    have h0 : ‖g 0‖ ≤ Cg := by
      simpa using (hgBound 0)
    exact le_trans (norm_nonneg _) h0
  have hpoint :
      ∀ t : ℝ,
        ‖f t * g (x - t)‖ ≤
          (Cf * Cg * Real.exp (- (1 / 2 + ε) * |x|)) * Real.exp (-ε * |t|) := by
    intro t
    -- Start from the decay bounds for `f` and `g`.
    have hf' := hfBound t
    have hg' := hgBound (x - t)
    -- Use `‖a*b‖ = ‖a‖*‖b‖` and combine the bounds.
    calc
      ‖f t * g (x - t)‖ = ‖f t‖ * ‖g (x - t)‖ := by simp [norm_mul]
      _ ≤ (Cf * Real.exp (- (1 / 2 + εf) * |t|)) *
            (Cg * Real.exp (- (1 / 2 + εg) * |x - t|)) := by
            -- multiply the two one-sided bounds
            refine mul_le_mul hf' hg' (norm_nonneg _) ?_
            exact mul_nonneg hCf0 (le_of_lt (Real.exp_pos _))
      _ = (Cf * Cg) *
            (Real.exp (- (1 / 2 + εf) * |t|) * Real.exp (- (1 / 2 + εg) * |x - t|)) := by
            ring_nf
      _ ≤ (Cf * Cg) *
            (Real.exp (- (1 / 2 + ε) * |x|) * Real.exp (-ε * |t|)) := by
            -- Compare exponentials via a coefficient/triple-inequality argument.
            have h2ε : (2 : ℝ) * ε ≤ εf := by
              have hmul : (2 : ℝ) * ε = min εf εg := by
                -- `2 * (min/2) = min`
                simpa [ε] using (mul_div_cancel₀ (b := (2 : ℝ)) (a := (min εf εg)) (by norm_num))
              simpa [hmul] using (min_le_left εf εg)
            have hεg : ε ≤ εg := by
              have hmin0 : 0 ≤ min εf εg := le_of_lt (lt_min hεf hεg)
              have hdiv : (min εf εg) / 2 ≤ min εf εg := by
                exact div_le_self hmin0 (by norm_num : (1 : ℝ) ≤ 2)
              exact le_trans (by simpa [ε] using hdiv) (min_le_right εf εg)
            have hcoeff_t : (1 / 2 + ε) + ε ≤ (1 / 2 + εf) := by
              -- this is `1/2 + 2ε ≤ 1/2 + εf`
              linarith [h2ε]
            have hcoeff_xt : (1 / 2 + ε) ≤ (1 / 2 + εg) := by
              linarith [hεg]
            have habs : |x| ≤ |t| + |x - t| := by
              -- `x = t + (x - t)`
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (abs_add t (x - t))
            have hexp :
                Real.exp (- (1 / 2 + εf) * |t|) * Real.exp (- (1 / 2 + εg) * |x - t|) ≤
                  Real.exp (- (1 / 2 + ε) * |x|) * Real.exp (-ε * |t|) := by
              -- Reduce to an inequality of exponents and use monotonicity of `exp`.
              have hsum :
                  (- (1 / 2 + εf) * |t|) + (- (1 / 2 + εg) * |x - t|) ≤
                    (- (1 / 2 + ε) * |x|) + (-ε * |t|) := by
                have ht0 : 0 ≤ |t| := abs_nonneg _
                have hxt0 : 0 ≤ |x - t| := abs_nonneg _
                have h1 : (1 / 2 + εf) * |t| ≥ ((1 / 2 + ε) + ε) * |t| :=
                  mul_le_mul_of_nonneg_right hcoeff_t ht0
                have h2 : (1 / 2 + εg) * |x - t| ≥ (1 / 2 + ε) * |x - t| :=
                  mul_le_mul_of_nonneg_right hcoeff_xt hxt0
                have h3 : (1 / 2 + ε) * (|t| + |x - t|) ≥ (1 / 2 + ε) * |x| :=
                  mul_le_mul_of_nonneg_left habs (by linarith)
                have :
                    (1 / 2 + εf) * |t| + (1 / 2 + εg) * |x - t| ≥
                      (1 / 2 + ε) * |x| + ε * |t| := by
                  have : (1 / 2 + εf) * |t| + (1 / 2 + εg) * |x - t| ≥
                      ((1 / 2 + ε) * |t| + ε * |t|) + (1 / 2 + ε) * |x - t| := by
                    linarith [h1, h2]
                  have : ((1 / 2 + ε) * |t| + ε * |t|) + (1 / 2 + ε) * |x - t| =
                      (1 / 2 + ε) * (|t| + |x - t|) + ε * |t| := by ring
                  linarith [this, h3]
                linarith
              have := Real.exp_le_exp.2 hsum
              simpa [Real.exp_add, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using this
            exact mul_le_mul_of_nonneg_left hexp (mul_nonneg hCf0 hCg0)
      _ = (Cf * Cg * Real.exp (- (1 / 2 + ε) * |x|)) * Real.exp (-ε * |t|) := by ring_nf
  -- Integrate the pointwise bound.
  have h_integrable_rhs :
      Integrable (fun t : ℝ => (Cf * Cg * Real.exp (- (1 / 2 + ε) * |x|)) * Real.exp (-ε * |t|)) := by
    -- constant times an integrable function
    exact hKint.const_mul _
  have h_integrable_lhs :
      Integrable (fun t : ℝ => ‖f t * g (x - t)‖) := hint.norm
  have hmono :
      (∫ t : ℝ, ‖f t * g (x - t)‖) ≤
        ∫ t : ℝ, (Cf * Cg * Real.exp (- (1 / 2 + ε) * |x|)) * Real.exp (-ε * |t|) := by
    refine MeasureTheory.integral_mono h_integrable_lhs h_integrable_rhs ?_
    intro t
    exact hpoint t
  refine hmono.trans ?_
  -- Evaluate the right-hand integral and rearrange factors.
  have hcalc :
      (∫ t : ℝ, (Cf * Cg * Real.exp (- (1 / 2 + ε) * |x|)) * Real.exp (-ε * |t|)) =
        (Cf * Cg * Real.exp (- (1 / 2 + ε) * |x|)) * K := by
    simp [K, MeasureTheory.integral_mul_left]
  have hcomm :
      (Cf * Cg * Real.exp (- (1 / 2 + ε) * |x|)) * K =
        (Cf * Cg * K) * Real.exp (- (1 / 2 + ε) * |x|) := by
    ring_nf
  have hEq :
      (∫ t : ℝ, (Cf * Cg * Real.exp (- (1 / 2 + ε) * |x|)) * Real.exp (-ε * |t|)) =
        (Cf * Cg * K) * Real.exp (- (1 / 2 + ε) * |x|) :=
    hcalc.trans hcomm
  exact le_of_eq hEq

/-!
### Fourier decay is preserved under convolution

Using the Fourier-defined convolution, the Fourier transform becomes pointwise multiplication,
so exponential decay of the Fourier transform is preserved immediately.
-/

lemma ft_decay_preserved_by_convolution {f g : SchwartzMap ℝ ℂ}
    (hf : ∃ (C ε : ℝ), 0 < ε ∧
      ∀ ξ, ‖fourierTransformCLM ℂ f ξ‖ ≤ C * Real.exp (- (1 / 2 + ε) * |ξ|))
    (hg : ∃ (C ε : ℝ), 0 < ε ∧
      ∀ ξ, ‖fourierTransformCLM ℂ g ξ‖ ≤ C * Real.exp (- (1 / 2 + ε) * |ξ|)) :
    ∃ (C ε : ℝ), 0 < ε ∧
      ∀ ξ, ‖fourierTransformCLM ℂ (schwartzConv f g) ξ‖ ≤ C * Real.exp (- (1 / 2 + ε) * |ξ|) := by
  obtain ⟨Cf, εf, hεf, hfBound⟩ := hf
  obtain ⟨Cg, εg, hεg, hgBound⟩ := hg
  -- The product has stronger exponential decay: exponent adds.
  refine ⟨Cf * Cg, (1 / 2 + εf + εg), by linarith, ?_⟩
  intro ξ
  have hCf0 : 0 ≤ Cf := by
    have h0 : ‖fourierTransformCLM ℂ f 0‖ ≤ Cf := by
      simpa using (hfBound 0)
    exact le_trans (norm_nonneg _) h0
  have hCg0 : 0 ≤ Cg := by
    have h0 : ‖fourierTransformCLM ℂ g 0‖ ≤ Cg := by
      simpa using (hgBound 0)
    exact le_trans (norm_nonneg _) h0
  -- Fourier transform of Schwartz convolution is pointwise multiplication.
  have hFT := congrArg (fun h : SchwartzMap ℝ ℂ => ‖h ξ‖) (fourierTransform_schwartzConv (f := f) (g := g))
  -- Unpack the equality and bound.
  simp only [SchwartzMap.fourierTransformCLM_apply, schwartzMul_apply, norm_mul] at hFT
  -- Use the given bounds and combine exponentials.
  have hfξ := hfBound ξ
  have hgξ := hgBound ξ
  calc
    ‖fourierTransformCLM ℂ (schwartzConv f g) ξ‖
        = ‖fourierTransformCLM ℂ f ξ‖ * ‖fourierTransformCLM ℂ g ξ‖ := by
            -- from the pointwise product identity
            simpa using hFT.symm
    _ ≤ (Cf * Real.exp (- (1 / 2 + εf) * |ξ|)) * (Cg * Real.exp (- (1 / 2 + εg) * |ξ|)) := by
          -- multiply the two bounds
          refine mul_le_mul hfξ hgξ (norm_nonneg _) ?_
          exact mul_nonneg hCf0 (le_of_lt (Real.exp_pos _))
    _ = (Cf * Cg) * Real.exp (- (1 / 2 + (1 / 2 + εf + εg)) * |ξ|) := by
          -- regroup constants and combine exponentials
          have hexp :
              Real.exp (- (1 / 2 + εf) * |ξ|) * Real.exp (- (1 / 2 + εg) * |ξ|) =
                Real.exp ((- (1 / 2 + εf) * |ξ|) + (- (1 / 2 + εg) * |ξ|)) := by
            simpa [Real.exp_add] using
              (Real.exp_add (- (1 / 2 + εf) * |ξ|) (- (1 / 2 + εg) * |ξ|)).symm
          -- normalize the exponent and finish.
          calc
            (Cf * Real.exp (- (1 / 2 + εf) * |ξ|)) * (Cg * Real.exp (- (1 / 2 + εg) * |ξ|))
                = (Cf * Cg) * (Real.exp (- (1 / 2 + εf) * |ξ|) * Real.exp (- (1 / 2 + εg) * |ξ|)) := by
                    ring_nf
            _ = (Cf * Cg) * Real.exp ((- (1 / 2 + εf) * |ξ|) + (- (1 / 2 + εg) * |ξ|)) := by
                    rw [hexp]
            _ = (Cf * Cg) * Real.exp (- ((1 / 2 + (1 / 2 + εf + εg)) * |ξ|)) := by
                    ring_nf
            _ = (Cf * Cg) * Real.exp (- (1 / 2 + (1 / 2 + εf + εg)) * |ξ|) := by
                    -- rewrite `(-a) * b` as `-(a * b)` inside the exponent
                    have hneg :
                        (- (1 / 2 + (1 / 2 + εf + εg)) * |ξ|) =
                          - ((1 / 2 + (1 / 2 + εf + εg)) * |ξ|) := by
                      simpa using (neg_mul (1 / 2 + (1 / 2 + εf + εg)) |ξ|)
                    rw [hneg]

/-- The Weil transform of convolution as a double integral.
This is the first step towards the convolution theorem. -/
lemma weilTransform_convAt_eq (f g : SchwartzMap ℝ ℂ) (s : ℂ) :
    (∫ x : ℝ, schwartzConvAt f g x * Complex.exp ((s - 0.5) * x)) =
    ∫ x : ℝ, (∫ t : ℝ, f t * g (x - t)) * Complex.exp ((s - 0.5) * x) := by
  rfl

/-- The convolution theorem for the Weil transform (at function level).
`∫∫ f(t)g(x-t)e^{(s-1/2)x} dt dx = (∫ f(t)e^{(s-1/2)t} dt) * (∫ g(u)e^{(s-1/2)u} du)`

This is a standard result in harmonic analysis. The proof uses:
1. Fubini's theorem to swap the order of integration
2. Translation invariance of Lebesgue measure: `∫ h(x-t) dx = ∫ h(u) du`
3. The factorization `e^{(s-½)(u+t)} = e^{(s-½)u} · e^{(s-½)t}`
4. Separation of the double integral

**Key integrability requirement**: The integrand `f(t) · g(x-t) · e^{(s-½)x}` must be
integrable on ℝ × ℝ. For Schwartz functions f, g, this follows from:
- The function `x ↦ ∫_t ‖f(t) · g(x-t)‖ dt` is the convolution `‖f‖ ⋆ ‖g‖`.
- Since ‖f‖, ‖g‖ ∈ L¹(ℝ), their convolution is in L¹(ℝ) by Young's inequality.
- The exponential factor is controlled when `s` is in the strip of absolute convergence.

**Status**: This is a mathematically standard result. The formalization requires
showing product-measure integrability using `integrable_prod_iff` and the convolution
properties of L¹ functions in Mathlib.
-/
theorem weilTransform_schwartzConv_of_integrable (f g : SchwartzMap ℝ ℂ) (s : ℂ)
    (hF :
      Integrable
        (Function.uncurry fun x t : ℝ =>
          f t * g (x - t) * Complex.exp ((s - 0.5) * x))
        (volume.prod volume)) :
    (∫ x : ℝ, schwartzConvAt f g x * Complex.exp ((s - 0.5) * x)) =
      weilTransform f s * weilTransform g s := by
  -- Expand the definitions and distribute the exponential inside the inner integral.
  simp only [weilTransform, schwartzConvAt]
  have h_distr :
      ∀ x : ℝ,
        (∫ t : ℝ, f t * g (x - t)) * Complex.exp ((s - 0.5) * x) =
          ∫ t : ℝ, f t * g (x - t) * Complex.exp ((s - 0.5) * x) := by
    intro x
    -- `Complex.exp ((s-1/2) * x)` is constant in `t`.
    simpa [mul_assoc] using
      (integral_mul_right (μ := (volume : Measure ℝ))
        (f := fun t : ℝ => f t * g (x - t)) (r := Complex.exp ((s - 0.5) * x))).symm
  simp_rw [h_distr]

  -- Swap the order of integration using Fubini/Tonelli.
  have hswap :
      (∫ x : ℝ, ∫ t : ℝ, f t * g (x - t) * Complex.exp ((s - 0.5) * x)) =
        ∫ t : ℝ, ∫ x : ℝ, f t * g (x - t) * Complex.exp ((s - 0.5) * x) := by
    -- `integral_integral_swap` is stated for curried functions; use `Function.uncurry`.
    simpa [Function.uncurry] using
      (integral_integral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (f := fun x t : ℝ => f t * g (x - t) * Complex.exp ((s - 0.5) * x)) hF)
  rw [hswap]

  -- Compute the inner integral by a translation change of variables and factorization.
  have h_inner :
      ∀ t : ℝ,
        (∫ x : ℝ, f t * g (x - t) * Complex.exp ((s - 0.5) * x)) =
          f t * Complex.exp ((s - 0.5) * t) * weilTransform g s := by
    intro t
    -- Pull out the constant `f t` from the `x`-integral.
    have h_pull :
        (∫ x : ℝ, f t * g (x - t) * Complex.exp ((s - 0.5) * x)) =
          f t * ∫ x : ℝ, g (x - t) * Complex.exp ((s - 0.5) * x) := by
      -- Reassociate to expose a left-multiplication by `f t`.
      have :
          (fun x : ℝ => f t * g (x - t) * Complex.exp ((s - 0.5) * x)) =
            fun x : ℝ => (f t) * (g (x - t) * Complex.exp ((s - 0.5) * x)) := by
        funext x
        ring_nf
      simp [this, integral_mul_left]
    rw [h_pull]

    -- Change variables `x ↦ x - t` using translation invariance.
    have h_sub :
        (∫ x : ℝ, g (x - t) * Complex.exp ((s - 0.5) * x)) =
          ∫ x : ℝ, g x * Complex.exp ((s - 0.5) * (x + t)) := by
      -- Let `H x := g x * exp((s-1/2) * (x+t))`. Then `H (x - t) = g (x - t) * exp((s-1/2) * x)`.
      have h_eq :
          (fun x : ℝ => g (x - t) * Complex.exp ((s - 0.5) * x)) =
            fun x : ℝ => (fun u : ℝ => g u * Complex.exp ((s - 0.5) * (u + t))) (x - t) := by
        funext x
        -- simplify `(x - t) + t = x`
        simp [sub_add_cancel]
      -- Apply `integral_sub_right_eq_self` to `H`.
      simpa [h_eq] using
        (MeasureTheory.integral_sub_right_eq_self
          (μ := (volume : Measure ℝ))
          (f := fun u : ℝ => g u * Complex.exp ((s - 0.5) * (u + t))) t)

    -- Factor the exponential `exp((s-1/2)*(x+t)) = exp((s-1/2)*x) * exp((s-1/2)*t)`.
    have h_factor :
        (fun x : ℝ => g x * Complex.exp ((s - 0.5) * (x + t))) =
          fun x : ℝ => (g x * Complex.exp ((s - 0.5) * x)) * Complex.exp ((s - 0.5) * t) := by
      funext x
      -- Rewrite `(x + t : ℂ) = (x : ℂ) + (t : ℂ)` and expand.
      have hlin : (s - 0.5) * (x + t : ℂ) = (s - 0.5) * (x : ℂ) + (s - 0.5) * (t : ℂ) := by
        simpa [mul_add] using (mul_add (s - 0.5) (x : ℂ) (t : ℂ))
      -- Expand the exponential and reassociate.
      -- `Complex.exp (a + b) = Complex.exp a * Complex.exp b`.
      calc
        g x * Complex.exp ((s - 0.5) * (x + t : ℂ))
            = g x * (Complex.exp ((s - 0.5) * (x : ℂ)) * Complex.exp ((s - 0.5) * (t : ℂ))) := by
                simp [hlin, Complex.exp_add]
        _ = (g x * Complex.exp ((s - 0.5) * (x : ℂ))) * Complex.exp ((s - 0.5) * (t : ℂ)) := by
                ring_nf
    -- Use `integral_mul_right` to pull out the constant `exp((s-1/2)*t)`.
    have h_pull2 :
        (∫ x : ℝ, g x * Complex.exp ((s - 0.5) * (x + t))) =
          (∫ x : ℝ, g x * Complex.exp ((s - 0.5) * x)) * Complex.exp ((s - 0.5) * t) := by
      -- Rewrite integrand then pull out the constant.
      simp [h_factor, integral_mul_right]
    -- Finish the inner computation.
    -- Use `h_pull2`, then identify the remaining integral with `weilTransform g s`.
    -- (We keep the rearrangements explicit to avoid simp-normal forms of `cexp` exponents.)
    calc
      f t * ∫ x : ℝ, g (x - t) * Complex.exp ((s - 0.5) * x)
          = f t * ∫ x : ℝ, g x * Complex.exp ((s - 0.5) * (x + t)) := by
              simp [h_sub]
      _ = f t * ((∫ x : ℝ, g x * Complex.exp ((s - 0.5) * x)) * Complex.exp ((s - 0.5) * t)) := by
              simp [h_pull2]
      _ = f t * Complex.exp ((s - 0.5) * t) * weilTransform g s := by
              -- `weilTransform g s` is the remaining integral; commute factors.
              simp [weilTransform, mul_assoc, mul_left_comm, mul_comm]

  -- Substitute the inner computation, then pull out the constant `weilTransform g s`.
  simp_rw [h_inner]
  -- `weilTransform g s` is constant in `t`, so pull it out.
  -- Then identify the remaining integral as `weilTransform f s`.
  have : (∫ t : ℝ, f t * Complex.exp ((s - 0.5) * t) * weilTransform g s) =
      (∫ t : ℝ, f t * Complex.exp ((s - 0.5) * t)) * weilTransform g s := by
    simpa [mul_assoc] using
      (integral_mul_right (μ := (volume : Measure ℝ))
        (f := fun t : ℝ => f t * Complex.exp ((s - 0.5) * t)) (r := weilTransform g s))
  -- Reassociate and conclude.
  simpa [weilTransform, mul_assoc, mul_left_comm, mul_comm] using this

end ExplicitFormula
end RiemannRecognitionGeometry
