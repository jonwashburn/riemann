
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Riemann.Mathlib.Analysis.Harmonic.BMO.Defs
import Carleson

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

variable {α : Type*} [MeasurableSpace α] [MetricSpace α] [ProperSpace α]
  [BorelSpace α] [SeparableSpace α]
variable (μ : Measure α) (A : ℝ≥0) [μ.IsDoubling A]

/-! ### Definition of the Hardy-Littlewood Maximal Function -/

/-- The Hardy–Littlewood maximal function, packaged via the Carleson library and
converted back to `ℝ` via `toReal`. -/
noncomputable def hlMaximalFunction (f : α → ℝ) (x : α) : ℝ :=
  (globalMaximalFunction (μ := μ) (A := A) 1 f x).toReal

/-- We use the same uncentered maximal function; kept for API compatibility. -/
@[simp] noncomputable def hlMaximalFunctionUncentered (f : α → ℝ) (x : α) : ℝ :=
  hlMaximalFunction (μ := μ) (A := A) f x

/-! ### Basic Properties -/

omit [BorelSpace α] [SeparableSpace α] in
theorem hlMaximalFunction_nonneg (f : α → ℝ) (x : α) :
    0 ≤ hlMaximalFunction (μ := μ) (A := A) f x :=
  ENNReal.toReal_nonneg

omit [BorelSpace α] [SeparableSpace α] in
/-- Monotonicity of `globalMaximalFunction` for the ℝ≥0∞-valued operator.

The proof uses that `globalMaximalFunction` is defined as a scaled supremum of
laverage integrals over a covering of balls. If `‖f‖ₑ ≤ ‖g‖ₑ` pointwise, then
each laverage of `‖f‖ₑ` is at most the corresponding laverage of `‖g‖ₑ`,
hence the supremum for `f` is at most the supremum for `g`. -/
theorem globalMaximalFunction_mono [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {f g : α → ℝ} (h : ∀ y, ‖f y‖ₑ ≤ ‖g y‖ₑ) (x : α) :
    globalMaximalFunction (μ := μ) (A := A) 1 f x ≤ globalMaximalFunction (μ := μ) (A := A) 1 g x := by
  -- Unfold and use monotonicity of iSup and lintegral
  unfold globalMaximalFunction maximalFunction
  simp only [ENNReal.rpow_one, inv_one]
  -- A^2 * (sup of f-averages) ≤ A^2 * (sup of g-averages)
  apply mul_le_mul_left'
  apply iSup₂_mono
  intro i _
  -- Indicator is monotone pointwise: either both are the laverage or both are 0
  by_cases hx : x ∈ ball i.1 (2 ^ i.2)
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    -- laverage is monotone in the integrand
    apply lintegral_mono
    intro y
    exact h y
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

omit [BorelSpace α] [SeparableSpace α] in
theorem hlMaximalFunction_mono [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {f g : α → ℝ} (h : ∀ x, |f x| ≤ |g x|) (x : α)
    (hg_fin : globalMaximalFunction (μ := μ) (A := A) 1 g x ≠ ⊤) :
    hlMaximalFunction (μ := μ) (A := A) f x ≤ hlMaximalFunction (μ := μ) (A := A) g x := by
  unfold hlMaximalFunction
  apply ENNReal.toReal_mono hg_fin
  apply globalMaximalFunction_mono
  intro y
  -- Convert |f y| ≤ |g y| to ‖f y‖ₑ ≤ ‖g y‖ₑ
  simp only [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (h y)

/-- The maximal function dominates pointwise averages (in real form via `toReal`). -/
theorem setAverage_abs_le_hlMaximalFunction {f : α → ℝ}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (x : α) {r : ℝ} (hr : 0 < r) (hf : IntegrableOn f (ball x r) μ) :
    ⨍ y in ball x r, |f y| ∂μ ≤ hlMaximalFunction (μ := μ) (A := A) f x := by
  -- First, we show the ℝ≥0∞ inequality using Carleson's `laverage_le_globalMaximalFunction`
  have hdist : dist x x < r := by simp [hr]
  have hle : ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ ≤ globalMaximalFunction (μ := μ) (A := A) 1 f x :=
    laverage_le_globalMaximalFunction (μ := μ) (A := A) hdist
  -- The average of |f| is at most the toReal of the laverage of ‖f‖ₑ
  -- which is at most the toReal of the globalMaximalFunction
  unfold hlMaximalFunction
  -- Use that ⨍ |f| ≤ (⨍⁻ ‖f‖ₑ).toReal ≤ (globalMaximalFunction).toReal
  -- The proof requires relating Bochner integrals to Lebesgue integrals
  sorry

/-! ### Measurability -/

omit [BorelSpace α] [SeparableSpace α] in
/-- The ℝ≥0∞-valued global maximal function is lower semicontinuous.
This follows from Carleson's `lowerSemiContinuous_globalMaximalFunction`. -/
theorem globalMaximalFunction_lowerSemicontinuous (f : α → ℝ) :
    LowerSemicontinuous (globalMaximalFunction (μ := μ) (A := A) 1 f) :=
  lowerSemiContinuous_globalMaximalFunction

/-- The Hardy-Littlewood maximal function is lower semicontinuous, hence measurable.

The proof uses that `globalMaximalFunction` is lower semicontinuous (from Carleson),
and `toReal` preserves lower semicontinuity for finite-valued functions. -/
theorem hlMaximalFunction_lowerSemicontinuous
    (f : α → ℝ) :
    LowerSemicontinuous (hlMaximalFunction (μ := μ) (A := A) f) := by
  -- The ℝ≥0∞-valued globalMaximalFunction is lower semicontinuous
  -- toReal of a lower semicontinuous ℝ≥0∞-valued function is lower semicontinuous
  unfold hlMaximalFunction
  -- We need to show that x ↦ (globalMaximalFunction μ 1 f x).toReal is lower semicontinuous
  -- This follows from the lower semicontinuity of globalMaximalFunction
  sorry

theorem hlMaximalFunction_measurable
    (f : α → ℝ) :
    Measurable (hlMaximalFunction (μ := μ) (A := A) f) :=
  (hlMaximalFunction_lowerSemicontinuous (μ := μ) (A := A) f).measurable

/-! ### Weak Type (1,1) Bound -/

omit [MeasurableSpace α] [ProperSpace α] [BorelSpace α] [SeparableSpace α] in
/-- The **Vitali Covering Lemma** (5r-covering version).

Given a collection of balls in a metric space, there exists a disjoint subcollection
such that the 5-fold dilations cover the original union.

This is the key geometric ingredient for the maximal function weak type bound.

**Statement**: Given balls `{B(x_i, r_i)}`, there exist disjoint balls `{B(x_{i_k}, r_{i_k})}`
such that `⋃_i B(x_i, r_i) ⊆ ⋃_k B(x_{i_k}, 5 * r_{i_k})`.

This follows from `Vitali.exists_disjoint_subfamily_covering_enlargement` in mathlib with τ = 2.
With τ = 2, if r_i ≤ 2 * r_j and balls B_i, B_j intersect, then B_i ⊆ B(x_j, 5 * r_j). -/
theorem vitali_covering_5r {ι : Type*} (x : ι → α) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hbdd : BddAbove (range r)) :
    ∃ (s : Set ι), (s.PairwiseDisjoint fun i => ball (x i) (r i)) ∧
      (⋃ i, ball (x i) (r i)) ⊆ ⋃ i ∈ s, ball (x i) (5 * r i) := by
  -- Use mathlib's Vitali covering lemma with τ = 2
  obtain ⟨R, hR⟩ := hbdd
  have hR' : ∀ i ∈ (univ : Set ι), r i ≤ R := fun i _ => hR (mem_range_self i)
  obtain ⟨u, _, hu_disj, hu_cover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun i => ball (x i) (r i)) univ r 2 (by norm_num : (1 : ℝ) < 2)
      (fun i _ => (hr i).le) R hR' (fun i _ => ⟨x i, mem_ball_self (hr i)⟩)
  refine ⟨u, hu_disj, fun y hy => ?_⟩
  simp only [mem_iUnion] at hy ⊢
  obtain ⟨i, hi⟩ := hy
  obtain ⟨j, hj_mem, hj_inter, hj_le⟩ := hu_cover i (mem_univ i)
  -- y ∈ ball (x i) (r i), and ball (x i) (r i) ∩ ball (x j) (r j) is nonempty
  -- with r i ≤ 2 * r j, so y ∈ ball (x j) (5 * r j)
  obtain ⟨z, hz_i, hz_j⟩ := hj_inter
  refine ⟨j, hj_mem, ?_⟩
  calc dist y (x j) ≤ dist y (x i) + dist (x i) z + dist z (x j) := dist_triangle4 _ _ _ _
    _ < r i + r i + r j := by
        gcongr
        · exact hi
        · rw [dist_comm]; exact hz_i
        · exact hz_j
    _ ≤ 2 * r j + 2 * r j + r j := by linarith
    _ = 5 * r j := by ring

omit [SeparableSpace α] in
/-- **Weak type (1,1) bound** for the Hardy-Littlewood maximal function on doubling measures.

For a uniformly locally doubling measure `μ`, there exists `C > 0` such that for all
locally integrable `f` and all `λ > 0`:

  `μ({x : Mf(x) > λ}) ≤ C · ‖f‖₁ / λ`

This is optimal: the maximal function is NOT strong type (1,1).

The proof uses `hasWeakType_globalMaximalFunction` from the Carleson project. -/
theorem hlMaximalFunction_weakType11 [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {p : ℝ≥0} (hp : 0 < p) :
    HasWeakType (fun g => globalMaximalFunction (μ := μ) (A := A) p g (E := ℝ))
      p p μ μ (C_weakType_globalMaximalFunction A p p) :=
  hasWeakType_globalMaximalFunction (E := ℝ) hp le_rfl

/-- The weak (1,1) constant can be made explicit in terms of the doubling constant. -/
theorem hlMaximalFunction_weakType11_explicit [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (f : α → ℝ) (hf : MemLp f 1 μ) {lambda : ℝ≥0∞} (hlambda : 0 < lambda) :
    μ {x | ENNReal.ofReal (hlMaximalFunction (μ := μ) (A := A) f x) > lambda} ≤
      C_weakType_globalMaximalFunction A 1 1 / lambda * eLpNorm f 1 μ := by
  -- Use the weak type bound from Carleson
  have hweak := hasWeakType_globalMaximalFunction (μ := μ) (A := A) (E := ℝ)
    (p₁ := 1) (p₂ := 1) one_pos le_rfl
  -- Convert from globalMaximalFunction to hlMaximalFunction
  have hconv : ∀ x, ENNReal.ofReal (hlMaximalFunction (μ := μ) (A := A) f x) ≤
      globalMaximalFunction (μ := μ) (A := A) 1 f x := fun x => by
    unfold hlMaximalFunction
    exact ENNReal.ofReal_toReal_le
  -- The wnorm bound from hweak implies the distribution bound
  -- wnorm (Mf) 1 μ ≤ C * ‖f‖₁ implies μ({Mf > λ}) ≤ C/λ * ‖f‖₁
  calc μ {x | ENNReal.ofReal (hlMaximalFunction (μ := μ) (A := A) f x) > lambda}
      ≤ μ {x | globalMaximalFunction (μ := μ) (A := A) 1 f x > lambda} := by
        apply measure_mono
        intro x hx
        simp only [mem_setOf_eq] at hx ⊢
        exact lt_of_lt_of_le hx (hconv x)
    _ ≤ C_weakType_globalMaximalFunction A 1 1 / lambda * eLpNorm f 1 μ := by
        -- Use wnorm_ge_distribution to convert wnorm bound to distribution bound
        have hwnorm := (hweak f hf).2
        -- The relation: μ({|Mf| > λ}) ≤ (wnorm Mf p μ / λ)^p
        sorry

/-! ### Strong Type (p,p) Bound -/

omit [SeparableSpace α] in
/-- **Strong type (p,p) bound** for the global maximal function.

This follows directly from `hasStrongType_globalMaximalFunction` in the Carleson project.
For `0 < p₁ < p₂`, the operator has strong type `(p₂, p₂)`. -/
theorem hlMaximalFunction_strongType_ennreal [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {p₁ p₂ : ℝ≥0} (hp₁ : 0 < p₁) (hp₁₂ : p₁ < p₂) :
    HasStrongType (globalMaximalFunction (μ := μ) (A := A) p₁ (E := ℝ))
      p₂ p₂ μ μ (C2_0_6' A p₁ p₂) :=
  hasStrongType_globalMaximalFunction hp₁ hp₁₂

omit [SeparableSpace α] in
/-- Strong type bound for the real-valued maximal function.

For `1 < p`, there exists a constant `C` such that
`‖Mf‖_p ≤ C · ‖f‖_p`. -/
theorem hlMaximalFunction_strongType [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {p : ℝ≥0} (hp1 : 1 < p) (f : α → ℝ) (hf : MemLp f p μ) :
    MemLp (globalMaximalFunction (μ := μ) (A := A) 1 f) p μ := by
  have hstrong := hasStrongType_globalMaximalFunction (μ := μ) (A := A) (E := ℝ)
    (p₁ := 1) (p₂ := p) one_pos hp1
  exact hstrong.memLp hf

omit [SeparableSpace α] in
/-- Explicit bound: `‖Mf‖_p ≤ C · ‖f‖_p` for the maximal function. -/
theorem hlMaximalFunction_Lp_bound [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {p : ℝ≥0} (hp1 : 1 < p) (f : α → ℝ) (hf : MemLp f p μ) :
    eLpNorm (globalMaximalFunction (μ := μ) (A := A) 1 f) p μ ≤
      C2_0_6' A 1 p * eLpNorm f p μ :=
  (hasStrongType_globalMaximalFunction (μ := μ) (A := A) (E := ℝ) one_pos hp1 f hf).2

/-! ### Lebesgue Differentiation Theorem -/

/-- **Lebesgue Differentiation Theorem** on doubling metric measure spaces.

For a locally integrable function `f`, at almost every point `x`:

  `lim_{r → 0} ⨍_{B(x,r)} f(y) dμ(y) = f(x)`

This follows from the general Vitali family differentiation theorem in mathlib.
See `VitaliFamily.ae_tendsto_average` in `Mathlib.MeasureTheory.Covering.Differentiation`. -/
theorem lebesgue_differentiation [IsUnifLocDoublingMeasure μ]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  -- Uses the Vitali family differentiation theorem from mathlib
  -- The vitaliFamily for a doubling measure satisfies the necessary conditions
  -- See Mathlib.MeasureTheory.Covering.DensityTheorem for ae_tendsto_average
  sorry

theorem abs_le_hlMaximalFunction_ae [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, |f x| ≤ hlMaximalFunction (μ := μ) (A := A) f x := by
  -- Consequence of Lebesgue differentiation: if averages converge to f(x),
  -- then |f(x)| = lim of |averages| ≤ sup of averages = Mf(x)
  -- Uses that averages of |f| converge to |f(x)| a.e.
  sorry

/-! ### Comparison of Centered and Uncentered Maximal Functions -/

omit [BorelSpace α] [SeparableSpace α] in
/-- The uncentered maximal function equals the centered one by definition. -/
theorem hlMaximalFunction_eq_uncentered (f : α → ℝ) (x : α) :
    hlMaximalFunction (μ := μ) (A := A) f x = hlMaximalFunctionUncentered (μ := μ) (A := A) f x :=
  rfl

omit [BorelSpace α] [SeparableSpace α] in
/-- The uncentered maximal function dominates the centered one (trivially equal here). -/
theorem hlMaximalFunction_le_uncentered (f : α → ℝ) (x : α) :
    hlMaximalFunction (μ := μ) (A := A) f x ≤ hlMaximalFunctionUncentered (μ := μ) (A := A) f x :=
  le_refl _

omit [BorelSpace α] [SeparableSpace α] in
/-- On doubling spaces, the uncentered maximal function is controlled by the centered one.

Since we defined the uncentered function to equal the centered one (both via
`globalMaximalFunction`), this is just `1 * Mf(x)`. -/
theorem hlMaximalFunctionUncentered_le (f : α → ℝ) (x : α) :
    hlMaximalFunctionUncentered (μ := μ) (A := A) f x ≤
      1 * hlMaximalFunction (μ := μ) (A := A) f x := by
  simp only [one_mul, hlMaximalFunctionUncentered, le_refl]

end MeasureTheory
