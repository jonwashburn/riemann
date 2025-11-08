import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner

noncomputable section

namespace RH
namespace RS

open MeasureTheory
open scoped MeasureTheory

@[simp] def boundaryMap (t : ℝ) : ℂ := (1/2 : ℂ) + Complex.I * (t : ℂ)

@[simp] def boundaryRe (F : ℂ → ℂ) (t : ℝ) : ℝ := (F (boundaryMap t)).re

@[simp] def poissonKernel (b x : ℝ) : ℝ := b / (Real.pi * (b^2 + x^2))

@[simp] def poissonSmooth (F : ℂ → ℂ) (b x : ℝ) : ℝ :=
  ∫ t, poissonKernel b (x - t) * boundaryRe F t ∂(volume)

end RS
end RH
