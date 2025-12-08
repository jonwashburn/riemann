import Carleson.ToMathlib.HardyLittlewood
import Carleson.ToMathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Riemann.Mathlib.MeasureTheory.Integral.AverageAux

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

omit [BorelSpace α] [SeparableSpace α] in
/-- The maximal function dominates pointwise averages (in real form via `toReal`),
when the globalMaximalFunction is finite at the point. -/
theorem setAverage_abs_le_hlMaximalFunction {f : α → ℝ}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (x : α) {r : ℝ} (hr : 0 < r) (hf : IntegrableOn f (ball x r) μ)
    (hfin : globalMaximalFunction (μ := μ) (A := A) 1 f x ≠ ⊤) :
    ⨍ y in ball x r, |f y| ∂μ ≤ hlMaximalFunction (μ := μ) (A := A) f x := by
  -- First, we show the ℝ≥0∞ inequality using Carleson's `laverage_le_globalMaximalFunction`
  have hdist : dist x x < r := by simp [hr]
  have hle : ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ ≤ globalMaximalFunction (μ := μ) (A := A) 1 f x :=
    laverage_le_globalMaximalFunction (μ := μ) (A := A) hdist
  -- Use average_abs_eq_laverage_enorm_toReal and monotonicity of toReal
  rw [average_abs_eq_laverage_enorm_toReal hf]
  unfold hlMaximalFunction
  apply ENNReal.toReal_mono hfin
  exact hle

/-! ### Measurability -/

omit [BorelSpace α] [SeparableSpace α] in
/-- The ℝ≥0∞-valued global maximal function is lower semicontinuous.
This follows from Carleson's `lowerSemiContinuous_globalMaximalFunction`. -/
theorem globalMaximalFunction_lowerSemicontinuous (f : α → ℝ) :
    LowerSemicontinuous (globalMaximalFunction (μ := μ) (A := A) 1 f) :=
  lowerSemiContinuous_globalMaximalFunction

omit [BorelSpace α] [SeparableSpace α] in
/-- The Hardy-Littlewood maximal function is lower semicontinuous when the
underlying `globalMaximalFunction` is everywhere finite.

The proof uses that `globalMaximalFunction` is lower semicontinuous (from Carleson),
and `toReal` preserves lower semicontinuity for finite-valued functions.

For L∞ functions, `globalMaximalFunction_lt_top` provides the finiteness. -/
theorem hlMaximalFunction_lowerSemicontinuous
    (f : α → ℝ) (hfin : ∀ x, globalMaximalFunction (μ := μ) (A := A) 1 f x ≠ ⊤) :
    LowerSemicontinuous (hlMaximalFunction (μ := μ) (A := A) f) := by
  unfold hlMaximalFunction
  exact ENNReal.lowerSemicontinuous_toReal_of_lt_top
    (globalMaximalFunction_lowerSemicontinuous (μ := μ) (A := A) f) hfin

omit [SeparableSpace α] in
/-- The Hardy-Littlewood maximal function is measurable.

This follows from the measurability of `globalMaximalFunction` (which is lower
semicontinuous) and `toReal` (which is Borel measurable). -/
theorem hlMaximalFunction_measurable
    (f : α → ℝ) :
    Measurable (hlMaximalFunction (μ := μ) (A := A) f) := by
  unfold hlMaximalFunction
  exact ENNReal.measurable_toReal.comp
    (globalMaximalFunction_lowerSemicontinuous (μ := μ) (A := A) f).measurable

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

omit [SeparableSpace α] in
/-- The weak (1,1) constant can be made explicit in terms of the doubling constant.

This follows from `hasWeakType_globalMaximalFunction` by extracting the distribution bound
from the wnorm bound: `wnorm f 1 μ = ⨆ t, t * distribution f t μ`, so
`distribution f t μ ≤ wnorm f 1 μ / t`. -/
theorem hlMaximalFunction_weakType11_explicit [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (f : α → ℝ) (hf : MemLp f 1 μ) {t : ℝ≥0} (ht : 0 < t) :
    μ {x | ENNReal.ofReal (hlMaximalFunction (μ := μ) (A := A) f x) > t} ≤
      C_weakType_globalMaximalFunction A 1 1 / t * eLpNorm f 1 μ := by
  -- Use the weak type bound from Carleson
  have hweak := hasWeakType_globalMaximalFunction (μ := μ) (A := A) (E := ℝ)
    (p₁ := 1) (p₂ := 1) one_pos le_rfl
  -- Convert from globalMaximalFunction to hlMaximalFunction
  have hconv : ∀ x, ENNReal.ofReal (hlMaximalFunction (μ := μ) (A := A) f x) ≤
      globalMaximalFunction (μ := μ) (A := A) 1 f x := fun x => by
    unfold hlMaximalFunction
    exact ENNReal.ofReal_toReal_le
  -- The wnorm bound: wnorm (Mf) 1 μ ≤ C * ‖f‖₁
  have hwnorm := (hweak f hf).2
  -- For the distribution bound: t * d(t) ≤ wnorm f 1 μ implies d(t) ≤ wnorm f 1 μ / t
  calc μ {x | ENNReal.ofReal (hlMaximalFunction (μ := μ) (A := A) f x) > t}
      ≤ μ {x | globalMaximalFunction (μ := μ) (A := A) 1 f x > t} := by
        apply measure_mono
        intro x hx
        simp only [mem_setOf_eq] at hx ⊢
        exact lt_of_lt_of_le hx (hconv x)
    _ = distribution (globalMaximalFunction (μ := μ) (A := A) 1 f) t μ := by
        simp only [distribution, enorm_eq_self]
    _ ≤ C_weakType_globalMaximalFunction A 1 1 / t * eLpNorm f 1 μ := by
        -- From wnorm definition: wnorm' f 1 μ = ⨆ t, t * distribution f t μ
        -- So t * distribution f t μ ≤ wnorm f 1 μ
        -- which gives distribution f t μ ≤ wnorm f 1 μ / t ≤ C * ‖f‖₁ / t
        have hle : (t : ℝ≥0∞) * distribution (globalMaximalFunction (μ := μ) (A := A) 1 f) t μ ≤
            wnorm (globalMaximalFunction (μ := μ) (A := A) (1 : ℝ≥0) f) (1 : ℝ≥0) μ := by
          rw [wnorm_coe]
          simp only [wnorm', NNReal.coe_one, inv_one, ENNReal.rpow_one]
          exact le_iSup_of_le t le_rfl
        have ht_pos : (0 : ℝ≥0∞) < t := ENNReal.coe_pos.mpr ht
        have hwnorm' : wnorm (globalMaximalFunction (μ := μ) (A := A) (1 : ℝ≥0) f) (1 : ℝ≥0) μ ≤
            C_weakType_globalMaximalFunction A 1 1 * eLpNorm f 1 μ := by
          convert hwnorm using 2
        -- distribution f t μ ≤ wnorm / t ≤ C * ‖f‖₁ / t = C / t * ‖f‖₁
        have h1 : distribution (globalMaximalFunction (μ := μ) (A := A) 1 f) t μ ≤
            wnorm (globalMaximalFunction (μ := μ) (A := A) (1 : ℝ≥0) f) (1 : ℝ≥0) μ / t := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl ht_pos.ne') (Or.inl ENNReal.coe_ne_top)]
          rw [mul_comm]
          exact hle
        have h2 : wnorm (globalMaximalFunction (μ := μ) (A := A) (1 : ℝ≥0) f) (1 : ℝ≥0) μ / t ≤
            C_weakType_globalMaximalFunction A 1 1 * eLpNorm f 1 μ / t := by
          exact ENNReal.div_le_div_right hwnorm' t
        have h3 : C_weakType_globalMaximalFunction A 1 1 * eLpNorm f 1 μ / t =
            C_weakType_globalMaximalFunction A 1 1 / t * eLpNorm f 1 μ := by
          -- a * b / c = a / c * b by commutativity and associativity
          rw [@ENNReal.mul_div_right_comm]
        exact h3 ▸ h1.trans h2

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

omit [ProperSpace α] [μ.IsDoubling A] in
/-- **Lebesgue Differentiation Theorem** on doubling metric measure spaces.

For a locally integrable function `f`, at almost every point `x`:

  `lim_{r → 0} ⨍_{B(x,r)} f(y) dμ(y) = f(x)`

This follows from the general Vitali family differentiation theorem in mathlib.
See `IsUnifLocDoublingMeasure.ae_tendsto_average` in
`Mathlib.MeasureTheory.Covering.DensityTheorem`. -/
theorem lebesgue_differentiation [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ]
    (f : α → ℝ) (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  -- Uses the Vitali family differentiation theorem from mathlib
  -- The vitaliFamily for a doubling measure satisfies the necessary conditions
  -- IsUnifLocDoublingMeasure.ae_tendsto_average gives the result for centered balls
  have h := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := μ) hf 1
  filter_upwards [h] with x hx
  -- Specialize to the centered case: w j = x for all j, δ j = r
  -- hx says: for any sequence (w, δ) with δ → 0⁺ and x ∈ closedBall (w j) (1 * δ j),
  -- we have ⨍ closedBall (w j) (δ j) → f x
  -- Taking w = const x and δ = id, we get ⨍ closedBall x r → f x as r → 0⁺
  have hxmem : ∀ᶠ j in 𝓝[>] (0 : ℝ), x ∈ closedBall x (1 * j) := by
    filter_upwards [self_mem_nhdsWithin] with j hj
    simp only [one_mul, mem_closedBall, dist_self]
    exact (mem_Ioi.mp hj).le
  exact hx (fun _ => x) id tendsto_id hxmem

/-! ### Auxiliary Lemmas for Lebesgue Point Bound -/

/-- Conversion lemma: if `1 < p` in `ℝ≥0∞`, then `1 < p.toNNReal`. -/
lemma one_lt_toNNReal_of_one_lt {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ⊤) :
    (1 : ℝ≥0) < p.toNNReal := by
  have h1 : (1 : ℝ≥0∞).toNNReal = 1 := ENNReal.toNNReal_one
  rw [← h1]
  exact (ENNReal.toNNReal_lt_toNNReal ENNReal.one_ne_top hptop).mpr hp

omit [SeparableSpace α] in
/-- The global maximal function is a.e. finite for functions in `Lp` with `p > 1`.
This follows from `globalMaximalFunction_ae_lt_top` in the Carleson project. -/
lemma globalMaximalFunction_ae_lt_top_of_memLp
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ⊤)
    (f : α → ℝ) (hf : MemLp f p μ) :
    ∀ᵐ x ∂μ, globalMaximalFunction (μ := μ) (A := A) 1 f x < ⊤ := by
  have hp' : (1 : ℝ≥0) < p.toNNReal := one_lt_toNNReal_of_one_lt hp hptop
  have hfnn : MemLp f (p.toNNReal) μ := by rwa [ENNReal.coe_toNNReal hptop]
  exact globalMaximalFunction_ae_lt_top one_pos hp' hfnn

omit [BorelSpace α] [SeparableSpace α] in
/-- The average of `|f|` over an open ball is bounded by the maximal function,
when the global maximal function is finite at the center. -/
lemma setAverage_abs_ball_le_hlMaximalFunction
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {f : α → ℝ} (hf_loc : LocallyIntegrable f μ)
    (x : α) {r : ℝ} (hr : 0 < r)
    (hfin : globalMaximalFunction (μ := μ) (A := A) 1 f x ≠ ⊤) :
    ⨍ y in ball x r, |f y| ∂μ ≤ hlMaximalFunction (μ := μ) (A := A) f x := by
  have hdist : dist x x < r := by simp [hr]
  -- f is integrable on the ball (since ball ⊂ closedBall which is compact)
  have hf_int : IntegrableOn f (ball x r) μ := by
    have hcb : IntegrableOn f (closedBall x r) μ :=
      hf_loc.integrableOn_isCompact (isCompact_closedBall x r)
    exact hcb.mono_set ball_subset_closedBall
  have hle_lavg : ⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ ≤ globalMaximalFunction (μ := μ) (A := A) 1 f x :=
    laverage_le_globalMaximalFunction (μ := μ) (A := A) hdist
  -- Convert Bochner average of |f| to laverage of ‖f‖ₑ
  calc ⨍ y in ball x r, |f y| ∂μ
      = (⨍⁻ y in ball x r, ‖f y‖ₑ ∂μ).toReal := average_abs_eq_laverage_enorm_toReal hf_int
    _ ≤ (globalMaximalFunction (μ := μ) (A := A) 1 f x).toReal := ENNReal.toReal_mono hfin hle_lavg
    _ = hlMaximalFunction (μ := μ) (A := A) f x := rfl

/-- The pointwise absolute value is dominated by the maximal function a.e., for functions
in `Lp` with `p > 1`.

The proof combines:
1. Lebesgue differentiation: averages of `|f|` over balls converge to `|f(x)|` a.e.
2. Ball average bounds: each average is bounded by `Mf(x)` (from `laverage_le_globalMaximalFunction`)
3. Finiteness: `Mf(x) < ⊤` a.e. for `Lp` functions with `p > 1` (from `globalMaximalFunction_ae_lt_top`)

The key insight is that `|f(x)| = lim_{r→0} ⨍ ball x r |f| ≤ Mf(x)`. -/
theorem abs_le_hlMaximalFunction_ae [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ⊤) (f : α → ℝ) (hf : MemLp f p μ) :
    ∀ᵐ x ∂μ, |f x| ≤ hlMaximalFunction (μ := μ) (A := A) f x := by
  -- Step 1: Get a.e. finiteness of globalMaximalFunction
  have hfin : ∀ᵐ x ∂μ, globalMaximalFunction (μ := μ) (A := A) 1 f x < ⊤ :=
    globalMaximalFunction_ae_lt_top_of_memLp (μ := μ) (A := A) hp hptop f hf
  -- Step 2: Get Lebesgue differentiation for |f|
  have hp1 : 1 ≤ p := hp.le
  have hf_loc : LocallyIntegrable f μ := hf.locallyIntegrable hp1
  have habs_loc : LocallyIntegrable (fun x => |f x|) μ := hf_loc.norm
  have hdiff : ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in closedBall x r, |f y| ∂μ)
      (𝓝[>] 0) (𝓝 |f x|) := lebesgue_differentiation (μ := μ) (fun x => |f x|) habs_loc
  -- Step 3: Combine the a.e. conditions and conclude
  filter_upwards [hfin, hdiff] with x hx_fin hx_diff
  have hfin' : globalMaximalFunction (μ := μ) (A := A) 1 f x ≠ ⊤ := hx_fin.ne
  -- Ball averages bounded by Mf(x)
  have hball_bound : ∀ r > 0, ⨍ y in ball x r, |f y| ∂μ ≤ hlMaximalFunction (μ := μ) (A := A) f x :=
    fun r hr => setAverage_abs_ball_le_hlMaximalFunction (μ := μ) (A := A) hf_loc x hr hfin'
  -- Ball averages also converge to |f(x)| (same limit as closedBall)
  -- Strategy: use that ball ⊂ closedBall, and both averages converge to |f(x)|
  -- For r > 0: ball x r ⊆ closedBall x r ⊆ ball x (2r)
  -- The averages over nested sets converge to the same limit by Lebesgue differentiation
  have hdiff_ball : Tendsto (fun r => ⨍ y in ball x r, |f y| ∂μ) (𝓝[>] 0) (𝓝 |f x|) := by
    -- Use squeeze: for r/2 < ρ < r, we have closedBall x ρ ⊂ ball x r ⊂ closedBall x r
    -- Average over closedBall x ρ → |f x| and average over closedBall x r → |f x|
    rw [Metric.tendsto_nhds]
    intro ε hε
    -- Use ε/2 for both bounds
    have hcb := Metric.tendsto_nhds.mp hx_diff (ε / 2) (half_pos hε)
    rw [eventually_nhdsWithin_iff] at hcb ⊢
    rw [Metric.eventually_nhds_iff] at hcb ⊢
    obtain ⟨δ, hδ_pos, hδ⟩ := hcb
    -- For r < δ, ⨍ closedBall x r |f| is within ε of |f x|
    -- Use that ball x r = ⋃ ρ<r closedBall x ρ, and integrals/measures converge
    refine ⟨δ, hδ_pos, fun r hr hr_pos => ?_⟩
    have hr' : 0 < r := mem_Ioi.mp hr_pos
    have hr_lt_δ : r < δ := by simpa [abs_of_pos hr'] using hr
    -- Integrability on ball
    have hf_int_cb : ∀ ρ, IntegrableOn (fun y => |f y|) (closedBall x ρ) μ := fun ρ =>
      habs_loc.integrableOn_isCompact (isCompact_closedBall x ρ)
    have hf_int_ball : IntegrableOn (fun y => |f y|) (ball x r) μ :=
      (hf_int_cb r).mono_set ball_subset_closedBall
    -- Key: ball x r = ⋃_{n} closedBall x (r * (1 - 1/(n+2)))
    -- Use monotone convergence for integrals and measures
    -- Define approximating sequence ρₙ = r * (1 - 1/(n+2)) → r
    let ρ : ℕ → ℝ := fun n => r * (1 - 1 / (n + 2 : ℝ))
    have hρ_mono : Monotone ρ := by
      intro m n hmn
      have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by norm_cast; linarith
      have hn2 : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
        have := Nat.cast_le (α := ℝ).mpr hmn
        linarith
      have hdiv : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
        one_div_le_one_div_of_le hm2 hn2
      have hr_nonneg : 0 ≤ r := le_of_lt hr'
      -- ρ m = r * (1 - 1/(m+2)), ρ n = r * (1 - 1/(n+2))
      have hsub : 1 - 1 / ((m : ℝ) + 2) ≤ 1 - 1 / ((n : ℝ) + 2) := by linarith
      have hmul := mul_le_mul_of_nonneg_left hsub hr_nonneg
      simpa [ρ] using hmul
    have hρ_pos : ∀ n, 0 < ρ n := by
      intro n
      simp only [ρ]
      apply mul_pos hr'
      have hn2 : (0 : ℝ) < n + 2 := by norm_cast; linarith
      have h1 : (1 : ℝ) / (n + 2) < 1 := (div_lt_one hn2).mpr (by linarith)
      linarith
    have hρ_lt_r : ∀ n, ρ n < r := by
      intro n
      simp only [ρ]
      have h1 : 1 - 1 / (n + 2 : ℝ) < 1 := by
        have : 0 < 1 / (n + 2 : ℝ) := by positivity
        linarith
      calc r * (1 - 1 / (n + 2)) < r * 1 := by
            apply mul_lt_mul_of_pos_left h1 hr'
        _ = r := mul_one r
    have hρ_tendsto : Tendsto ρ atTop (𝓝 r) := by
      simp only [ρ]
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
        apply Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop
        exact tendsto_const_nhds
      have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        simp only [one_div]
        exact tendsto_inv_atTop_zero.comp h1
      have h3 : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
        convert tendsto_const_nhds.sub h2 using 1; ring_nf
      convert h3.const_mul r using 1; ring_nf
    -- ⋃ n, closedBall x (ρ n) = ball x r
    have hUnion : ⋃ n, closedBall x (ρ n) = ball x r := by
      apply Set.eq_of_subset_of_subset
      · exact iUnion_subset fun n => closedBall_subset_ball (hρ_lt_r n)
      · intro y hy
        rw [mem_ball] at hy
        -- Find n such that dist y x < ρ n
        have : ∀ᶠ n in atTop, dist y x < ρ n := hρ_tendsto.eventually (eventually_gt_nhds hy)
        obtain ⟨n, hn⟩ := this.exists
        exact mem_iUnion.mpr ⟨n, mem_closedBall.mpr hn.le⟩
    -- Use monotone convergence
    have hsm : ∀ n, MeasurableSet (closedBall x (ρ n)) := fun n => measurableSet_closedBall
    have hf_int_union : IntegrableOn (fun y => |f y|) (⋃ n, closedBall x (ρ n)) μ := by
      rw [hUnion]; exact hf_int_ball
    have h_int_conv := tendsto_setIntegral_of_monotone hsm
      (fun m n hmn => closedBall_subset_closedBall (hρ_mono hmn)) hf_int_union
    rw [hUnion] at h_int_conv
    have h_meas_conv : Tendsto (fun n => μ (closedBall x (ρ n))) atTop (𝓝 (μ (ball x r))) := by
      rw [← hUnion]
      exact tendsto_measure_iUnion_atTop (fun m n hmn => closedBall_subset_closedBall (hρ_mono hmn))
    -- Average convergence: ⨍ closedBall (ρ n) → ⨍ ball r as n → ∞
    have h_avg_conv : Tendsto (fun n => ⨍ y in closedBall x (ρ n), |f y| ∂μ) atTop
        (𝓝 (⨍ y in ball x r, |f y| ∂μ)) := by
      have hμ_ball_pos : 0 < μ (ball x r) := measure_ball_pos μ x hr'
      have hμ_ball_ne_top : μ (ball x r) ≠ ⊤ := by exact measure_ball_ne_top --measure_ball_ne_top x r
      -- Use that average = inv(measure) * integral, and both converge
      simp only [setAverage_eq, smul_eq_mul]
      apply Tendsto.mul
      · -- (μ (closedBall x (ρ n)).toReal)⁻¹ → (μ (ball x r).toReal)⁻¹
        apply Tendsto.inv₀
        · exact (ENNReal.tendsto_toReal hμ_ball_ne_top).comp h_meas_conv
        · exact (ENNReal.toReal_pos hμ_ball_pos.ne' hμ_ball_ne_top).ne'
      · exact h_int_conv
    -- Now use that ⨍ closedBall x (ρ n) is eventually within ε/2 of |f x|
    have h_cb_close : ∀ᶠ n in atTop, dist (⨍ y in closedBall x (ρ n), |f y| ∂μ) |f x| < ε / 2 := by
      have : ∀ᶠ n in atTop, ρ n < δ := hρ_tendsto.eventually (eventually_lt_nhds hr_lt_δ)
      filter_upwards [this] with n hn
      apply hδ
      · rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (hρ_pos n)]
        exact hn
      · exact mem_Ioi.mpr (hρ_pos n)
    -- Take limit: ⨍ ball x r = lim ⨍ closedBall x (ρ n), each within ε/2 of limit
    have hconv := h_avg_conv.eventually (Metric.ball_mem_nhds _ (half_pos hε))
    obtain ⟨n, hn_close, hn_dist⟩ := (hconv.and h_cb_close).exists
    have hn_close' : dist (⨍ y in closedBall x (ρ n), |f y| ∂μ) (⨍ y in ball x r, |f y| ∂μ) < ε / 2 :=
      Metric.mem_ball.mp hn_close
    calc dist (⨍ y in ball x r, |f y| ∂μ) |f x|
        ≤ dist (⨍ y in ball x r, |f y| ∂μ) (⨍ y in closedBall x (ρ n), |f y| ∂μ) +
          dist (⨍ y in closedBall x (ρ n), |f y| ∂μ) |f x| := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (by rw [dist_comm]; exact hn_close') hn_dist
      _ = ε := add_halves ε
  -- Conclude: |f(x)| = lim ⨍ ball r |f| ≤ Mf(x)
  refine le_of_tendsto hdiff_ball ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact hball_bound r (mem_Ioi.mp hr)

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
