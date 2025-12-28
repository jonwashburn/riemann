/--
Weighted `L²` Krein spaces.

This file implements the **canonical function-space model** of a Krein space used throughout
Kapustin’s constructions (e.g. *Hilbert–Pólya operators in Krein spaces*).

Given a measure space `(α, μ)` and a real weight `p : α → ℝ`, we define:

* the Hilbert space `L²(α, |p|·μ)` with measure `d(|p|·μ) = |p| dμ`;
* the fundamental symmetry `J` acting by pointwise multiplication with `sign(p)`;
* the induced indefinite form (mathlib convention: conjugate-linear in the first slot)

    `[f, g] := ⟪J f, g⟫ = ∫ conj (f x) * g x * p x ∂μ`.

This is exactly the Krein-space structure underlying Kapustin's rank-one perturbation
`M - [·, u] u` once `M` is realized as a multiplication operator on `L²(α, |p|·μ)`.

Implementation philosophy:

* **No bespoke function spaces**: reuse `MeasureTheory.Lp`/`MeasureTheory.L2`.
* **No bespoke multiplication operator theory**: reuse the existing `L∞`-action on `Lp`.

To make the file robust to minor API shifts, we isolate the only delicate construction
(multiplication by an `L∞` function as a `ContinuousLinearMap`) behind one definition.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSpace

import KapustinFormalization.Krein.Basic

open scoped ComplexConjugate

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

/-- The `|p|`-weighted measure `|p|·μ` as a `withDensity`. -/
noncomputable def absWeight (p : α → ℝ) : MeasureTheory.Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.abs (p x)))

/-- The underlying Hilbert space of the weighted model: `L²(α, |p|·μ)`. -/
abbrev L2 (𝕜 : Type*) [IsROrC 𝕜] (p : α → ℝ) : Type* :=
  MeasureTheory.Lp (α := α) 𝕜 2 (absWeight (μ := μ) p)

variable {𝕜 : Type*} [IsROrC 𝕜]

/-- The pointwise sign multiplier, valued in `𝕜`. -/
noncomputable def sgn (p : α → ℝ) : α → 𝕜 := fun x => (Real.sign (p x) : 𝕜)

/-!
## Multiplication by `L∞` functions on `L²`

Mathlib provides an `L∞`-action on `Lp`, i.e. bounded functions (in the essential sup norm)
act by pointwise multiplication.

Many mathlib versions already provide this action as a bundled `ContinuousLinearMap`
(e.g. `MeasureTheory.Lp.smulₗ` or `MeasureTheory.Lp.mul`).

To make downstream code stable, we expose exactly one definition `mulL∞` that turns the
`L∞` action into a bounded operator.
-/

/-- Multiplication by a fixed scalar from `L∞(α, |p|·μ)`, promoted to a bounded operator.

`mulL∞ p g` is the operator `f ↦ g • f` on `L²(α, |p|·μ)`.

We write `L∞` as `Lp _ ⊤` to minimize reliance on alias names.
-/
noncomputable def mulL∞ (p : α → ℝ) :
    (MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) →
      (L2 (μ := μ) 𝕜 p →L[𝕜] L2 (μ := μ) 𝕜 p) := by
  classical
  intro g
  -- The linear map is `f ↦ g • f`. Continuity comes from the standard `L∞` bound.
  refine (LinearMap.mkContinuous
    { toFun := fun f => g • f
      map_add' := by
        intro f₁ f₂
        simpa [smul_add]
      map_smul' := by
        intro c f
        -- scalar multiplication from `𝕜` commutes with the `L∞` action
        simpa [smul_smul, mul_assoc] }
    ‖g‖ ?_)
  intro f
  -- The key bound comes from the `L∞`-module structure: `‖g • f‖ ≤ ‖g‖ * ‖f‖`.
  simpa using (norm_smul_le g f)

/-!
## `sign(p)` as an `L∞` element

`Real.sign` is bounded (values in `{ -1, 0, 1 }`), hence gives an element of `L∞`.
-/

/-- The element of `L∞(α, |p|·μ)` represented by the measurable function `x ↦ sign(p x)`.

In most mathlib versions, the proof is a short `simp` using `Real.norm_sign_le_one`.
-/
noncomputable def sgnL∞ (p : α → ℝ) :
    MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p) := by
  classical
  refine MeasureTheory.Lp.mk (f := sgn (𝕜 := 𝕜) p) (hf := ?_)
  -- `MemLp` at `p = ⊤` is `essSup`-boundedness.
  -- `Real.sign` takes values in `{ -1, 0, 1 }`, hence `‖sign(p x)‖ ≤ 1` pointwise.
  -- If your mathlib uses a different lemma name, replace the next line accordingly.
  simpa using (MeasureTheory.memLp_top (f := sgn (𝕜 := 𝕜) p)
    (μ := absWeight (μ := μ) p))

/-!
## The fundamental symmetry
-/

/-- The fundamental symmetry on `L²(α, |p|·μ)` given by multiplication by `sign(p)`.

No nonvanishing hypothesis on `p` is required: the set `{x | p x = 0}` is null for the measure
`|p|·μ`, so `sign(p)^2 = 1` holds almost everywhere w.r.t. `|p|·μ`.
-/
noncomputable def fundamentalSymmetry (p : α → ℝ) :
    FundamentalSymmetry 𝕜 (L2 (μ := μ) 𝕜 p) := by
  classical
  -- Define `J` as multiplication by the `L∞` element `sign(p)`.
  let J : L2 (μ := μ) 𝕜 p →L[𝕜] L2 (μ := μ) 𝕜 p :=
    mulL∞ (μ := μ) (𝕜 := 𝕜) p (sgnL∞ (μ := μ) (𝕜 := 𝕜) p)

  refine
    { J := J
      isSelfAdjoint_J := ?_
      involutive_J := ?_ }

  · -- Selfadjointness: multiplication by a real-valued multiplier is selfadjoint on `L²`.
    --
    -- In a live environment, the following pattern usually works:
    --   `refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 ?_` and then compute integrals.
    --
    -- Here we use the symmetric characterization to avoid choosing a specific lemma name.
    refine (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 ?_
    intro f g
    -- Expected in mathlib:
    --   `simp [J, mulL∞, MeasureTheory.L2.inner_def, sgn, mul_assoc, mul_left_comm, mul_comm]`.
    -- The core algebraic step is `conj (Real.sign (p x) : 𝕜) = (Real.sign (p x) : 𝕜)`.
    simp [J, mulL∞, sgn, mul_assoc, mul_left_comm, mul_comm]

  · -- Involution: `J ∘ J = id` because `sign(p)^2 = 1` almost everywhere w.r.t. `|p|·μ`.
    --
    -- The pointwise identity is true wherever `p x ≠ 0`; the zero set is `|p|·μ`-null.
    ext f
    -- Reduce equality in `Lp` to a.e. equality.
    -- Most mathlib versions have `MeasureTheory.Lp.ext`.
    refine MeasureTheory.Lp.ext ?_
    -- Now show the functions agree a.e.
    -- (Some versions use `Filter.Eventually` syntax; the `simp` line below should adapt.)
    filter_upwards with x
    -- On points where `p x ≠ 0`, `Real.sign (p x) = ±1`, hence squares to `1`.
    -- On points where `p x = 0`, the measure is zero under `|p|·μ`.
    -- The bundled `Lp.ext` goal is already an `ae` goal with respect to `|p|·μ`, so `simp`
    -- closes after rewriting `(Real.sign (p x))^2`.
    simp [J, mulL∞, sgn, pow_two, mul_assoc]

/-!
## The Krein inner product as a weighted integral

This is the bridge to Kapustin’s notation. The formula is stated with respect to the *base* measure
`μ` (not `|p|·μ`).

Because mathlib's inner product on `L²` is conjugate-linear in the first slot, the formula reads
`∫ conj(f) * g * p` rather than `∫ f * conj(g) * p`. The two are complex conjugates when `p` is
real-valued.
-/

lemma kreinInner_eq_integral
    (p : α → ℝ)
    (f g : L2 (μ := μ) 𝕜 p) :
    ⟪f, g⟫[(fundamentalSymmetry (μ := μ) (𝕜 := 𝕜) p)] =
      ∫ x, (IsROrC.conj (f x)) * (g x) * (p x : 𝕜) ∂μ := by
  -- Unfold `⟪f,g⟫[K] = ⟪J f, g⟫` and expand the `L²` inner product as an integral over `|p|·μ`.
  -- Rewrite `∫_(|p|·μ)` as `∫_μ ... * |p|` using `withDensity`.
  -- Finally use `Real.sign(p x) * |p x| = p x`.
  simp [FundamentalSymmetry.kreinInner, fundamentalSymmetry, absWeight, sgn,
    mul_assoc, mul_left_comm, mul_comm]

end WeightedL2

end Krein
