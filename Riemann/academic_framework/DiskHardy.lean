import Riemann.Mathlib.Analysis.Complex.HardySpace.PoissonKernel

/-!
# Disk-level Poisson/Smirnov interface for the Cayley route

This file establishes the framework for Poisson representations on the unit disk.

## Main definitions

* `Complex.poissonKernel` : The classical angle/radius Poisson kernel
  `P_r(θ, φ) = (1 - r^2) / (1 - 2 r cos(θ - φ) + r^2)` (unnormalized: its integral over `φ ∈ [0,2π]` is `2π`).
* `Complex.poissonKernel'` : The disk-point Poisson kernel `P(z, e^{iθ})`, normalized by `1/(2π)`.
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

def poissonKernel' (z : 𝔻) (θ : ℝ) : ℝ :=
  (1 - ‖(z : ℂ)‖ ^ 2) / ((2 * Real.pi) * ‖Complex.exp (θ * Complex.I) - (z : ℂ)‖ ^ 2)

@[simp]
theorem poissonKernel_zero' (θ : ℝ) : poissonKernel' 0 θ = 1 / (2 * Real.pi) := by
  simp [poissonKernel', UnitDisc.coe_zero]

theorem poissonKernel_nonneg' (z : 𝔻) (θ : ℝ) : 0 ≤ poissonKernel' z θ := by
  apply div_nonneg
  · have h : ‖(z : ℂ)‖ < 1 := z.norm_lt_one
    have : ‖(z : ℂ)‖ ^ 2 < 1 := by aesop
    linarith
  · positivity

/-- `poissonKernel'` is the normalized version of the angle/radius kernel `poissonKernel`.

Writing `z = ‖z‖ · exp(i · arg z)`, one has
`poissonKernel' z θ = (2π)⁻¹ * poissonKernel ‖z‖ θ (arg z)`. -/
theorem poissonKernel'_eq_inv_two_pi_mul_poissonKernel (z : 𝔻) (θ : ℝ) :
    poissonKernel' z θ =
      (2 * Real.pi)⁻¹ * poissonKernel ‖(z : ℂ)‖ θ (Complex.arg (z : ℂ)) := by
  set w : ℂ := (z : ℂ)
  set r : ℝ := ‖w‖
  set φ : ℝ := Complex.arg w
  -- Polar decomposition: w = ‖w‖ * exp(i * arg w)
  have hw : (w : ℂ) = r * Complex.exp (φ * Complex.I) := by
    -- `‖w‖ * exp(arg w * I) = w`
    simp [w, r, φ]
  -- Rotate by `exp(-φ i)` to reduce to the real-axis case.
  have hnorm :
      ‖Complex.exp (θ * Complex.I) - w‖ ^ 2 =
        ‖Complex.exp ((θ - φ) * Complex.I) - (r : ℂ)‖ ^ 2 := by
    -- Multiply by the unit complex number `exp(-φ i)`; norms are preserved.
    have hunit : ‖Complex.exp (-(φ * Complex.I))‖ = 1 := by
      -- `‖exp((-φ) i)‖ = 1`, rewritten as `‖exp(-(φ i))‖ = 1`.
      simpa [neg_mul] using Complex.norm_exp_ofReal_mul_I (-φ)
    have hmul :
        Complex.exp ((-φ) * Complex.I) * (Complex.exp (θ * Complex.I) - w) =
          Complex.exp ((θ - φ) * Complex.I) - (r : ℂ) := by
      -- First term: `exp(-φ i) * exp(θ i) = exp((θ-φ) i)`
      have h1 :
          Complex.exp ((-φ) * Complex.I) * Complex.exp (θ * Complex.I) =
            Complex.exp ((θ - φ) * Complex.I) := by
        have hsum : (-(φ * Complex.I)) + (θ * Complex.I) = (θ - φ) * Complex.I := by ring
        calc
          Complex.exp ((-φ) * Complex.I) * Complex.exp (θ * Complex.I)
              = Complex.exp (((-φ) * Complex.I) + (θ * Complex.I)) := by
                  simp [Complex.exp_add]
          _ = Complex.exp (-(φ * Complex.I) + (θ * Complex.I)) := by
                simp [neg_mul]
          _ = Complex.exp ((θ - φ) * Complex.I) := by simp [hsum]
      -- Second term: `exp(-φ i) * w = r` via the polar decomposition of `w`.
      have h2 : Complex.exp ((-φ) * Complex.I) * w = (r : ℂ) := by
        rw [hw]
        have hsum : (-(φ * Complex.I)) + (φ * Complex.I) = 0 := by ring
        have hexp :
            Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) = (1 : ℂ) := by
          calc
            Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I)
                = Complex.exp (-(φ * Complex.I) + (φ * Complex.I)) := by
                    simpa [Complex.exp_add] using
                      (Complex.exp_add (-(φ * Complex.I)) (φ * Complex.I)).symm
            _ = Complex.exp 0 := by simp [hsum]
            _ = (1 : ℂ) := by simp
        -- Pull out the scalar `r` and cancel exponentials.
        calc
          Complex.exp ((-φ) * Complex.I) * (r * Complex.exp (φ * Complex.I))
              = (r : ℂ) * (Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I)) := by
                  -- Normalize `exp((-φ) * I)` to `exp(-(φ*I))` and reassociate.
                  simp [mul_assoc, mul_left_comm, mul_comm]
          _ = (r : ℂ) := by simp [hexp]
      -- Combine using distributivity.
      calc
        Complex.exp ((-φ) * Complex.I) * (Complex.exp (θ * Complex.I) - w)
            = Complex.exp ((-φ) * Complex.I) * Complex.exp (θ * Complex.I)
                - Complex.exp ((-φ) * Complex.I) * w := by
                  simp [mul_sub]
        _ = Complex.exp ((θ - φ) * Complex.I) - (r : ℂ) := by
              -- Rewrite the two terms using `h1`/`h2` (and normalize `-(φ*I)` if it appears).
              have hneg : -(φ * Complex.I) = (-φ) * Complex.I := by ring
              -- Turn `exp (-(φ*I))` into `exp ((-φ)*I)` so `h1`/`h2` match.
              rw [hneg] at *
              aesop
    -- Now use `‖a*b‖ = ‖a‖ * ‖b‖` and `‖exp(-φ i)‖ = 1`.
    have hnorm_eq :
        ‖Complex.exp ((-φ) * Complex.I) * (Complex.exp (θ * Complex.I) - w)‖
          = ‖Complex.exp (θ * Complex.I) - w‖ := by
      -- `‖a*b‖ = ‖a‖*‖b‖` and `‖a‖ = 1`.
      have : ‖Complex.exp ((-φ) * Complex.I)‖ = 1 := by
        simpa [neg_mul] using hunit
      -- `simp` can now close `‖a‖ * ‖b‖ = ‖b‖`.
      simp
      aesop
    have hsq_eq :
        ‖Complex.exp ((-φ) * Complex.I) * (Complex.exp (θ * Complex.I) - w)‖ ^ 2 =
          ‖Complex.exp (θ * Complex.I) - w‖ ^ 2 := by
      aesop
    -- Finally replace the left-hand side using `hmul`.
    aesop
  -- Expand both kernels and use the squared-norm identity on the real axis.
  have hden :
      ‖Complex.exp ((θ - φ) * Complex.I) - (r : ℂ)‖ ^ 2 =
        1 - 2 * r * Real.cos (θ - φ) + r ^ 2 := by
    simpa using (Complex.norm_exp_ofReal_mul_I_sub_ofReal_sq r (θ - φ))
  -- Finish.
  subst w r φ
  simp [poissonKernel', poissonKernel, mul_assoc, mul_comm]
  grind

/-- A function `F : ℂ → ℂ` has a Poisson representation on the unit disk if:
1. It is analytic on the open unit disk,
2. The Poisson integral is integrable for each point in the disk, and
3. The real part of `F` equals its Poisson integral representation.

This structure bundles the data needed for harmonic extension and Hardy space theory. -/
structure HasDiskPoissonRepresentation (F : ℂ → ℂ) : Prop where
  /-- `F` is analytic on the open unit disk -/
  analytic : AnalyticOn ℂ F {z : ℂ | ‖z‖ < 1}
  /-- The Poisson integrand is integrable for each point in the disk -/
  integrable (z : 𝔻) :
    IntegrableOn (fun θ : ℝ => (F (Circle.exp θ)).re * poissonKernel' z θ)
                 (Set.Icc 0 (2 * Real.pi))
                 volume
  /-- The real part satisfies the Poisson integral formula -/
  re_eq (z : 𝔻) :
    (F z).re =
      ∫ θ in Set.Icc 0 (2 * Real.pi),
        (F (Circle.exp θ)).re * poissonKernel' z θ ∂volume

/-- Constructor for `HasDiskPoissonRepresentation` from explicit data.

This is a convenience lemma that constructs the structure directly from its three components.
It can be useful when the components are already available as hypotheses. -/
lemma hasDiskPoissonRepresentation_of_data
    {F : ℂ → ℂ}
    (hA : AnalyticOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hI : ∀ z : 𝔻,
            IntegrableOn (fun θ : ℝ => (F (Circle.exp θ)).re * poissonKernel' z θ)
                         (Set.Icc 0 (2 * Real.pi))
                         volume)
    (hEq : ∀ z : 𝔻,
            (F z).re =
              ∫ θ in Set.Icc 0 (2 * Real.pi),
                (F (Circle.exp θ)).re * poissonKernel' z θ ∂volume) :
    HasDiskPoissonRepresentation F :=
  ⟨hA, hI, hEq⟩

end Complex
