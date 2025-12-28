/-!
# Route 3: a concrete `TestSpace` instance from Schwartz/Fourier (log-coordinates)

This file implements the “log‑Schwartz/Fourier” idea in a Lean-friendly way:

- the test space is `SchwartzMap ℝ ℂ` (Schwartz functions on additive time),
- the “Mellin transform on the critical line” is modeled by the **Fourier transform**,
  evaluated at the imaginary part `t = s.im`,
- convolution is defined by transporting pointwise multiplication through the Fourier transform
  (`𝓕⁻¹(𝓕 f · 𝓕 g)`), so `mellin_conv` is immediate,
- the involution `tilde` is reflection `f(-·)`, giving `s ↦ 1 - s`,
- the conjugation `star` is pointwise complex conjugation, giving `s ↦ conj s`.

This is not yet “ζ-specific”: it only gives a concrete `TestSpace` where the algebraic Route‑3
manipulations are provably valid using Mathlib’s Fourier/Schwartz infrastructure.
-/

import RiemannRecognitionGeometry.ExplicitFormula.WeilTestFunctionProofs
import RiemannRecognitionGeometry.ExplicitFormula.Defs

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open Complex Real MeasureTheory SchwartzMap
open scoped BigOperators

namespace SchwartzTestSpace

/-- The Route‑3 “Mellin on the critical line” modeled by Fourier: `M[f](σ+it) := 𝓕 f(t)`. -/
def Mellin (f : SchwartzMap ℝ ℂ) (s : ℂ) : ℂ :=
  SchwartzMap.fourierTransformCLM (𝕜 := ℂ) f s.im

/-- Convolution transported through Fourier: `𝓕⁻¹(𝓕 f · 𝓕 g)`. -/
noncomputable def conv (f g : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  schwartzConv f g

/-- Involution corresponding to `s ↦ 1 - s`: reflection `f(-·)`. -/
def tilde (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  reflectSchwartz f

/-- Conjugation corresponding to `s ↦ conj s`: pointwise complex conjugation. -/
def star (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  conjSchwartz f

instance : TestSpace (SchwartzMap ℝ ℂ) where
  Mellin := Mellin
  conv := conv
  tilde := tilde
  star := star
  mellin_conv := by
    intro f g s
    -- `𝓕(f ⋆ g) = 𝓕 f · 𝓕 g`, evaluated at `t = s.im`.
    simp [Mellin, conv, schwartzMul_apply]
  mellin_tilde := by
    intro f s
    -- `𝓕(f(-·))(t) = 𝓕(f)(-t)` and `(1 - s).im = - s.im`.
    simp [Mellin, tilde, fourierTransform_reflect]
  mellin_star := by
    intro f s
    -- `𝓕(conj ∘ f)(t) = conj(𝓕 f (-t))` and `(conj s).im = - s.im`.
    simp [Mellin, star, fourierTransform_conj]

end SchwartzTestSpace

end ExplicitFormula
end RiemannRecognitionGeometry
