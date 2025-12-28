/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# BMO Definitions and Poisson Kernel Infrastructure

This module provides the foundational definitions for BMO (Bounded Mean Oscillation)
and the Poisson kernel that are shared between FeffermanStein.lean and JohnNirenberg.lean.

## Main Definitions

- `poissonKernel`: The Poisson kernel P(x,y) = (1/π) * y / (x² + y²)
- `intervalAverage`: The average of f over an interval
- `meanOscillation`: The mean oscillation of f over an interval
- `InBMO`: Predicate for f being in BMO (bounded mean oscillation)

## Purpose

This file exists to break the circular dependency between FeffermanStein.lean and
JohnNirenberg.lean, allowing FeffermanStein to import JohnNirenberg after both
import this shared file.
-/

import RiemannRecognitionGeometry.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section
open Real MeasureTheory Set

namespace RiemannRecognitionGeometry

/-! ## Poisson Kernel -/

/-- The Poisson kernel for the upper half-plane.
    P(x, y) = (1/π) · y / (x² + y²) for y > 0. -/
def poissonKernel (x y : ℝ) : ℝ :=
  if y > 0 then (1 / Real.pi) * y / (x^2 + y^2) else 0

/-- The Poisson kernel is positive for y > 0. -/
lemma poissonKernel_pos (x : ℝ) {y : ℝ} (hy : 0 < y) :
    0 < poissonKernel x y := by
  unfold poissonKernel
  simp only [if_pos hy]
  apply div_pos
  · apply mul_pos
    · exact one_div_pos.mpr Real.pi_pos
    · exact hy
  · have hx2 : 0 ≤ x^2 := sq_nonneg x
    have hy2 : 0 < y^2 := sq_pos_of_pos hy
    linarith

/-- The denominator x² + y² is positive for y > 0. -/
lemma poissonKernel_denom_pos (x : ℝ) {y : ℝ} (hy : 0 < y) :
    0 < x^2 + y^2 := by
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  have hy2 : 0 < y^2 := sq_pos_of_pos hy
  linarith

/-- The Poisson kernel is symmetric in x. -/
lemma poissonKernel_neg (x y : ℝ) :
    poissonKernel (-x) y = poissonKernel x y := by
  unfold poissonKernel
  simp only [neg_sq]

/-- The partial derivative ∂P/∂x. -/
def poissonKernel_dx (x y : ℝ) : ℝ :=
  if y > 0 then -(2 / Real.pi) * x * y / (x^2 + y^2)^2 else 0

/-- The partial derivative ∂P/∂y. -/
def poissonKernel_dy (x y : ℝ) : ℝ :=
  if y > 0 then (1 / Real.pi) * (x^2 - y^2) / (x^2 + y^2)^2 else 0

/-- poissonKernel_dx is an odd function in x. -/
lemma poissonKernel_dx_neg (x y : ℝ) :
    poissonKernel_dx (-x) y = -poissonKernel_dx x y := by
  unfold poissonKernel_dx
  split_ifs with hy
  · simp only [neg_sq, neg_mul, neg_neg]
    ring
  · simp

/-! ## BMO Definitions -/

/-- The average of a function over an interval. -/
def intervalAverage (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a < b then (1 / (b - a)) * ∫ t in Icc a b, f t else 0

/-- The mean oscillation of f over [a,b]. -/
def meanOscillation (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a < b then
    (1 / (b - a)) * ∫ t in Icc a b, |f t - intervalAverage f a b|
  else 0

/-- A function is in BMO if its mean oscillation is uniformly bounded. -/
def InBMO (f : ℝ → ℝ) : Prop :=
  ∃ M : ℝ, M > 0 ∧ ∀ a b : ℝ, a < b → meanOscillation f a b ≤ M

/-- Mean oscillation is nonnegative. -/
lemma meanOscillation_nonneg (f : ℝ → ℝ) (a b : ℝ) : meanOscillation f a b ≥ 0 := by
  unfold meanOscillation
  split_ifs with hab
  · apply mul_nonneg
    · exact one_div_nonneg.mpr (le_of_lt (sub_pos.mpr hab))
    · apply MeasureTheory.setIntegral_nonneg measurableSet_Icc
      intro x _; exact abs_nonneg _
  · rfl

end RiemannRecognitionGeometry
