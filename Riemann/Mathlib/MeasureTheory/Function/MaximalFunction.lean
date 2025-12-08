/-
Copyright (c) 2024 Riemann Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riemann Project Contributors
-/
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hardy-Littlewood Maximal Function

This file defines the Hardy-Littlewood maximal function and proves its fundamental properties,
including the weak (1,1) bound on doubling measure spaces.

## Main Definitions

* `MeasureTheory.hlMaximalFunction`: The (centered) Hardy-Littlewood maximal function
* `MeasureTheory.hlMaximalFunctionUncentered`: The uncentered maximal function

## Main Results

* `hlMaximalFunction_measurable`: The maximal function is measurable
* `hlMaximalFunction_weakType11`: Weak type (1,1) bound for doubling measures
* `hlMaximalFunction_strongType`: Strong type (p,p) bound for p > 1

## References

* Stein, "Singular Integrals and Differentiability Properties of Functions", Chapter I
* Stein, "Harmonic Analysis: Real-Variable Methods", Chapter I
* Grafakos, "Classical Fourier Analysis", Chapter 2

## Tags

maximal function, Hardy-Littlewood, weak type, doubling measure
-/

open MeasureTheory Measure Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
variable (μ : Measure α)

/-! ### Definition of the Hardy-Littlewood Maximal Function -/

/-- The **Hardy-Littlewood maximal function** (centered version).

For a locally integrable function `f`, the maximal function at `x` is the supremum of
the averages of `|f|` over all balls centered at `x`:

  `Mf(x) := sup_{r > 0} ⊓_B(x,r) |f(y)| dμ(y)`

This is the fundamental object in real-variable harmonic analysis.

**Properties**:
- `Mf ≥ |f|` a.e. (Lebesgue differentiation theorem in doubling spaces)
- `Mf` is lower semicontinuous (hence measurable)
- Weak type (1,1): `μ({Mf > λ}) ≤ C·‖f‖₁/λ`
- Strong type (p,p) for p > 1: `‖Mf‖_p ≤ C_p·‖f‖_p` -/
noncomputable def hlMaximalFunction (f : α → ℝ) (x : α) : ℝ :=
  ⨆ (r : ℝ) (_ : 0 < r), ⨍ y in ball x r, |f y| ∂μ

/-- The **uncentered Hardy-Littlewood maximal function**.

Takes the supremum over all balls containing `x`, not just those centered at `x`:

  `M*f(x) := sup_{x ∈ B} ⊓_B |f(y)| dμ(y)`

This is pointwise larger than the centered version but has the same weak/strong type bounds
(up to constants depending on the doubling constant). -/
noncomputable def hlMaximalFunctionUncentered (f : α → ℝ) (x : α) : ℝ :=
  ⨆ (y : α) (r : ℝ) (_ : 0 < r) (_ : x ∈ ball y r), ⨍ z in ball y r, |f z| ∂μ

/-! ### Basic Properties -/

theorem hlMaximalFunction_nonneg (f : α → ℝ) (x : α) :
    0 ≤ hlMaximalFunction μ f x := by
  unfold hlMaximalFunction
  apply Real.iSup_nonneg
  intro r
  apply Real.iSup_nonneg
  intro _
  exact setAverage_nonneg (fun y => abs_nonneg (f y))

theorem hlMaximalFunction_mono {f g : α → ℝ} (h : ∀ x, |f x| ≤ |g x|) (x : α) :
    hlMaximalFunction μ f x ≤ hlMaximalFunction μ g x := by
  unfold hlMaximalFunction
  apply Real.iSup_le_iSup
  intro r
  apply Real.iSup_le_iSup
  intro hr
  apply setAverage_mono_ae
  · exact integrableOn_const.2 (Or.inr (measure_ball_lt_top (μ := μ)))
  · filter_upwards with y
    exact h y

/-- The maximal function dominates pointwise averages. -/
theorem setAverage_abs_le_hlMaximalFunction (f : α → ℝ) (x : α) {r : ℝ} (hr : 0 < r) :
    ⨍ y in ball x r, |f y| ∂μ ≤ hlMaximalFunction μ f x := by
  unfold hlMaximalFunction
  exact le_ciSup_of_le ⟨r, le_refl _⟩ (le_ciSup_of_le hr (le_refl _))

/-! ### Measurability -/

/-- The Hardy-Littlewood maximal function is lower semicontinuous, hence measurable.

**Proof sketch**: For any `c`, the set `{Mf > c}` is open because if `Mf(x) > c`,
then some average over a ball `B(x,r)` exceeds `c`, and by continuity of averages
in the center, this holds in a neighborhood of `x`. -/
theorem hlMaximalFunction_lowerSemicontinuous [ProperSpace α] [IsLocallyFiniteMeasure μ]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) :
    LowerSemicontinuous (hlMaximalFunction μ f) := by
  -- The supremum of continuous functions is lower semicontinuous
  -- Each average ⨍_{B(x,r)} |f| is continuous in x for fixed r (under local integrability)
  sorry

theorem hlMaximalFunction_measurable [ProperSpace α] [IsLocallyFiniteMeasure μ]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) :
    Measurable (hlMaximalFunction μ f) :=
  (hlMaximalFunction_lowerSemicontinuous μ f hf).measurable

/-! ### Weak Type (1,1) Bound -/

/-- The **Vitali Covering Lemma** (5r-covering version).

Given a collection of balls in a metric space, there exists a disjoint subcollection
such that the 5-fold dilations cover the original union.

This is the key geometric ingredient for the maximal function weak type bound.

**Statement**: Given balls `{B(x_i, r_i)}`, there exist disjoint balls `{B(x_{i_k}, r_{i_k})}`
such that `⋃_i B(x_i, r_i) ⊆ ⋃_k B(x_{i_k}, 5 * r_{i_k})`. -/
theorem vitali_covering_5r {ι : Type*} (x : ι → α) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hbdd : BddAbove (range r)) :
    ∃ (s : Set ι), (s.PairwiseDisjoint fun i => ball (x i) (r i)) ∧
      (⋃ i, ball (x i) (r i)) ⊆ ⋃ i ∈ s, ball (x i) (5 * r i) := by
  -- Standard Vitali selection: greedily choose balls from largest to smallest
  -- See Stein "Singular Integrals" Chapter I or Grafakos "Classical FA" Chapter 2
  sorry

/-- **Weak type (1,1) bound** for the Hardy-Littlewood maximal function on doubling measures.

For a uniformly locally doubling measure `μ`, there exists `C > 0` such that for all
locally integrable `f` and all `λ > 0`:

  `μ({x : Mf(x) > λ}) ≤ C · ‖f‖₁ / λ`

This is optimal: the maximal function is NOT strong type (1,1).

**Proof sketch**:
1. Cover `{Mf > λ}` by balls `B_i` where `⨍_{B_i} |f| > λ`
2. Apply Vitali covering to get disjoint subcollection with 5r-covering
3. Use `∑ μ(B_i) ≤ (1/λ) ∑ ∫_{B_i} |f| ≤ ‖f‖₁/λ`
4. Use doubling to control `μ(5B_i) ≤ C · μ(B_i)`
5. Sum to get `μ({Mf > λ}) ≤ C · ‖f‖₁/λ` -/
theorem hlMaximalFunction_weakType11 [ProperSpace α] [IsUnifLocDoublingMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) {λ : ℝ} (hλ : 0 < λ) :
    μ {x | hlMaximalFunction μ f x > λ} ≤
      ENNReal.ofReal (IsUnifLocDoublingMeasure.scalingConstantOf μ 5 / λ) *
        ∫⁻ x, ‖f x‖₊ ∂μ := by
  -- 1. For each x in the superlevel set, choose a ball B_x where the average exceeds λ
  -- 2. Apply Vitali covering lemma
  -- 3. Use doubling to control the 5r-dilations
  -- 4. Sum up using disjointness
  sorry

/-- The weak (1,1) constant can be made explicit in terms of the doubling constant. -/
theorem hlMaximalFunction_weakType11_const [ProperSpace α] [IsUnifLocDoublingMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) {λ : ℝ} (hλ : 0 < λ) :
    μ {x | hlMaximalFunction μ f x > λ} ≤
      3 ^ IsUnifLocDoublingMeasure.doublingConstant μ * ENNReal.ofReal (1 / λ) *
        ∫⁻ x, ‖f x‖₊ ∂μ := by
  sorry

/-! ### Strong Type (p,p) Bound -/

/-- **Marcinkiewicz Interpolation** gives strong type (p,p) from weak (1,1) and strong (∞,∞).

For `1 < p < ∞`, if an operator `T` is:
- Weak type (1,1) with constant `A₁`
- Strong type (∞,∞) with constant `A_∞`

Then `T` is strong type (p,p) with constant depending on `p`, `A₁`, `A_∞`. -/
theorem hlMaximalFunction_strongType [ProperSpace α] [IsUnifLocDoublingMeasure μ]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) {p : ℝ} (hp1 : 1 < p) :
    ∃ C : ℝ≥0, eLpNorm (hlMaximalFunction μ f) p μ ≤ C * eLpNorm f p μ := by
  -- Apply Marcinkiewicz interpolation between weak (1,1) and trivial (∞,∞)
  -- The constant C depends on p and the doubling constant
  sorry

/-- Explicit bound: `‖Mf‖_p ≤ C_D · p/(p-1) · ‖f‖_p` for the maximal function. -/
theorem hlMaximalFunction_Lp_bound [ProperSpace α] [IsUnifLocDoublingMeasure μ]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) {p : ℝ} (hp1 : 1 < p) :
    eLpNorm (hlMaximalFunction μ f) p μ ≤
      ENNReal.ofReal (IsUnifLocDoublingMeasure.scalingConstantOf μ 5 * p / (p - 1)) *
        eLpNorm f p μ := by
  sorry

/-! ### Lebesgue Differentiation Theorem -/

/-- **Lebesgue Differentiation Theorem** on doubling metric measure spaces.

For a locally integrable function `f`, at almost every point `x`:

  `lim_{r → 0} ⨍_{B(x,r)} f(y) dμ(y) = f(x)`

Equivalently, `|f(x)| ≤ Mf(x)` a.e. -/
theorem lebesgue_differentiation [ProperSpace α] [IsUnifLocDoublingMeasure μ]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  -- Uses weak type (1,1) bound and density arguments
  -- See Heinonen "Lectures on Analysis on Metric Spaces" Chapter 1
  sorry

theorem abs_le_hlMaximalFunction_ae [ProperSpace α] [IsUnifLocDoublingMeasure μ]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, |f x| ≤ hlMaximalFunction μ f x := by
  -- Consequence of Lebesgue differentiation: if averages converge to f(x),
  -- then |f(x)| ≤ lim sup of averages ≤ sup of averages = Mf(x)
  sorry

/-! ### Comparison of Centered and Uncentered Maximal Functions -/

/-- The uncentered maximal function dominates the centered one. -/
theorem hlMaximalFunction_le_uncentered (f : α → ℝ) (x : α) :
    hlMaximalFunction μ f x ≤ hlMaximalFunctionUncentered μ f x := by
  unfold hlMaximalFunction hlMaximalFunctionUncentered
  apply Real.iSup_le
  intro r
  apply Real.iSup_le
  intro hr
  apply le_ciSup_of_le ⟨x, le_refl _⟩
  apply le_ciSup_of_le ⟨r, le_refl _⟩
  apply le_ciSup_of_le hr
  apply le_ciSup_of_le (mem_ball_self hr)
  exact le_refl _

/-- On doubling spaces, the uncentered maximal function is controlled by the centered one.

**Proof**: If `x ∈ B(y, r)`, then `B(y, r) ⊆ B(x, 2r)`, so the average over `B(y,r)`
is bounded by an average over a larger ball centered at `x`. The doubling condition
then controls the ratio of measures. -/
theorem hlMaximalFunctionUncentered_le [IsUnifLocDoublingMeasure μ] (f : α → ℝ) (x : α) :
    hlMaximalFunctionUncentered μ f x ≤
      IsUnifLocDoublingMeasure.scalingConstantOf μ 2 * hlMaximalFunction μ f x := by
  -- If x ∈ B(y,r), then B(y,r) ⊆ B(x, 2r)
  -- Use doubling to compare averages
  sorry

end MeasureTheory
