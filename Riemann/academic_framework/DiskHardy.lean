import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Complex.UnitDisc.Basic

/-!
# Disk-level Poisson/Smirnov interface for the Cayley route

This file establishes the framework for Poisson representations on the unit disk.

## Main definitions

* `Complex.poissonKernel`: The Poisson kernel for the unit disk, normalized by `1/(2π)`.
* `Complex.HasDiskPoissonRepresentation`: A structure packaging the Poisson integral formula
  for the real part of an analytic function on the unit disk.

## Implementation notes

* We use `Complex.UnitDisc` (denoted `𝔻`) from mathlib rather than a custom set definition.
* The boundary parametrization uses `Circle.exp` directly, which automatically coerces to `ℂ`.
* The Poisson kernel takes a point `z : 𝔻` to ensure `‖z‖ < 1`.
* All integrals explicitly specify the Lebesgue measure (`volume`).

## References

* [Walter Rudin, *Real and Complex Analysis*][rudin1987]

-/

noncomputable section

open MeasureTheory Complex
open scoped UnitDisc MeasureTheory

namespace Complex

/-- The Poisson kernel for the unit disk, normalized by `1/(2π)`.

For a point `z` in the unit disk `𝔻` and a boundary point `e^{iθ}`, this gives:
P(z, e^{iθ}) = (1 - ‖z‖²) / (2π · ‖e^{iθ} - z‖²)

The normalization ensures that `∫ θ in [0, 2π], P(z, e^{iθ}) dθ = 1` for all `z ∈ 𝔻`.

This kernel appears in the Poisson integral formula for harmonic functions on the disk. -/

--def poissonKernel' (z : 𝔻) (θ : ℝ) : ℝ :=
--  (1 - ‖(z : ℂ)‖ ^ 2) / ((2 * Real.pi) * ‖Complex.exp (θ * Complex.I) - z‖ ^ 2)

def poissonKernel (z : 𝔻) (θ : ℝ) : ℝ :=
  (1 - ‖(z : ℂ)‖ ^ 2) / ((2 * Real.pi) * ‖Complex.exp (θ * Complex.I) - (z : ℂ)‖ ^ 2)

@[simp]
theorem poissonKernel_zero (θ : ℝ) : poissonKernel 0 θ = 1 / (2 * Real.pi) := by
  simp [poissonKernel, UnitDisc.coe_zero]

theorem poissonKernel_nonneg (z : 𝔻) (θ : ℝ) : 0 ≤ poissonKernel z θ := by
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
    IntegrableOn (fun θ : ℝ => (F (Circle.exp θ)).re * poissonKernel z θ)
                 (Set.Icc 0 (2 * Real.pi))
                 volume
  /-- The real part satisfies the Poisson integral formula -/
  re_eq (z : 𝔻) :
    (F z).re =
      ∫ θ in Set.Icc 0 (2 * Real.pi),
        (F (Circle.exp θ)).re * poissonKernel z θ ∂volume

/-- Constructor for `HasDiskPoissonRepresentation` from explicit data.

This is a convenience lemma that constructs the structure directly from its three components.
It can be useful when the components are already available as hypotheses. -/
lemma hasDiskPoissonRepresentation_of_data
    {F : ℂ → ℂ}
    (hA : AnalyticOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hI : ∀ z : 𝔻,
            IntegrableOn (fun θ : ℝ => (F (Circle.exp θ)).re * poissonKernel z θ)
                         (Set.Icc 0 (2 * Real.pi))
                         volume)
    (hEq : ∀ z : 𝔻,
            (F z).re =
              ∫ θ in Set.Icc 0 (2 * Real.pi),
                (F (Circle.exp θ)).re * poissonKernel z θ ∂volume) :
    HasDiskPoissonRepresentation F :=
  ⟨hA, hI, hEq⟩

end Complex
