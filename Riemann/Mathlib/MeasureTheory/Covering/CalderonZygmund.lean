import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Topology.MetricSpace.ProperSpace
import Carleson.ToMathlib.HardyLittlewood
import Carleson.TwoSidedCarleson.WeakCalderonZygmund
import Riemann.Mathlib.MeasureTheory.Function.MaximalFunction
import Riemann.Mathlib.MeasureTheory.Integral.AverageAux
import Riemann.Mathlib.Analysis.Harmonic.BMO.Defs

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


/-!
# Auxiliary lemmas for CZ/BMO on doubling metric measure spaces

This file is intentionally **not** a second formalization of the Calderón–Zygmund decomposition.
The full construction lives in the Carleson library:
`Carleson.TwoSidedCarleson.WeakCalderonZygmund`.

Instead, we collect reusable lemmas that downstream BMO/John–Nirenberg proofs need:

- identities and inequalities for set averages (`⨍`), including a Jensen-style bound;
- a disjoint-support `tsum` integrability lemma (for “bad part” sums);
- measure-ratio comparisons derived from `IsUnifLocDoublingMeasure`;
- the recursive partition `czPartitionAux` and its basic properties;
- a BMO “telescoping” estimate comparing averages on nested balls;
- a small wrapper lemma around the Carleson pointwise decomposition (`czApproximation_add_tsum_czRemainder'`).
-/

open MeasureTheory Measure Set Filter Metric TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open BigOperators

namespace MeasureTheory

section Avg

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
variable (μ : Measure α) [ProperSpace α] [IsUnifLocDoublingMeasure μ]
variable [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-! ### Auxiliary Lemmas for Average-Measure Relationships -/

/-- The set average as a real number equals the integral divided by the measure.
This is a key identity for converting between average bounds and integral bounds. -/
lemma setAverage_abs_eq_integral_div {s : Set α} (hμ : μ s ≠ ⊤) {f : α → ℝ}
    (_ : IntegrableOn f s μ) :
    ⨍ x in s, |f x| ∂μ = (∫ x in s, |f x| ∂μ) / (μ s).toReal := by
  rw [setAverage_eq, smul_eq_mul, measureReal_def]
  ring

/-- Jensen's inequality for averages: |⨍ f| ≤ ⨍ |f|.
This follows from the triangle inequality for integrals: ‖∫ f‖ ≤ ∫ ‖f‖. -/
lemma abs_setAverage_le_setAverage_abs {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ} (hf : IntegrableOn f s μ) (hμ : μ s ≠ 0) (hμ' : μ s ≠ ⊤) :
    |⨍ x in s, f x ∂μ| ≤ ⨍ x in s, |f x| ∂μ := by
  have hpos : 0 < (μ s).toReal := ENNReal.toReal_pos hμ hμ'
  simp only [setAverage_eq, smul_eq_mul, measureReal_def]
  rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  gcongr
  calc |∫ x in s, f x ∂μ|
      = ‖∫ x in s, f x ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x in s, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x in s, |f x| ∂μ := by simp only [Real.norm_eq_abs]

/-- Linearity of average: ⨍(f - c) = ⨍f - c for constant c.
Uses linearity of integral and the set average definition. -/
lemma setAverage_sub_const {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ} (hf : IntegrableOn f s μ) (c : ℝ) (hμ : μ s ≠ 0) (hμ' : μ s ≠ ⊤) :
    ⨍ x in s, (f x - c) ∂μ = (⨍ x in s, f x ∂μ) - c := by
  have hconst : IntegrableOn (fun _ => c) s μ :=
    integrableOn_const (μ := μ) (s := s) (C := c) (hs := hμ') (hC := by simp)
  have hne : (μ s).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hμ, hμ'⟩
  simp only [setAverage_eq, smul_eq_mul, measureReal_def,
             integral_sub hf hconst, setIntegral_const, smul_eq_mul]
  field_simp [hne]

/-- From an average lower bound, derive an integral lower bound.
If `level < ⨍_s |f|`, then `level * μ(s) < ∫_s |f|`. -/
lemma integral_gt_of_setAverage_gt {s : Set α}
    {f : α → ℝ} (hf : IntegrableOn f s μ) {level : ℝ}
    (havg : level < ⨍ x in s, |f x| ∂μ) (hμ : μ s ≠ 0) (hμ' : μ s ≠ ⊤) :
    level * (μ s).toReal < ∫ x in s, |f x| ∂μ := by
  have hpos : 0 < (μ s).toReal := ENNReal.toReal_pos hμ hμ'
  rw [setAverage_abs_eq_integral_div μ hμ' hf] at havg
  exact (lt_div_iff₀ hpos).mp havg

/-- If the average exceeds a threshold, then the measure is bounded by the integral.

This is the key estimate used in the CZ decomposition: from `level < ⨍ |f|` we derive
that `μ(B) ≤ (1/level) · ∫ |f|`.

**Proof outline**:
1. From `level < ⨍_s |f| = (∫_s |f|) / μ(s)` we get `level · μ(s) < ∫_s |f|`
2. Dividing by `level` gives `μ(s) < (1/level) · ∫_s |f|`
3. Convert to `ℝ≥0∞` and relate Bochner integral to Lebesgue integral -/
lemma measure_le_of_average_gt {s : Set α} (hs : MeasurableSet s)
    {f : α → ℝ} (hf : IntegrableOn f s μ) {level : ℝ} (hlevel : 0 < level)
    (havg : level < ⨍ x in s, |f x| ∂μ) (hμ : μ s ≠ 0) (hμ' : μ s ≠ ⊤) :
    μ s ≤ ENNReal.ofReal (1 / level) * ∫⁻ x in s, ‖f x‖₊ ∂μ := by
  -- Step 1: From level < ⨍ |f| we get level * μ(s) < ∫ |f|
  have hpos : 0 < (μ s).toReal := ENNReal.toReal_pos hμ hμ'
  have h1 : level * (μ s).toReal < ∫ x in s, |f x| ∂μ :=
    integral_gt_of_setAverage_gt μ hf havg hμ hμ'
  -- Step 2: Hence μ(s) < (1/level) * ∫ |f|
  have h1' : (μ s).toReal * level < ∫ x in s, |f x| ∂μ := by linarith
  have h2 : (μ s).toReal < level⁻¹ * ∫ x in s, |f x| ∂μ := by
    have h3 : (μ s).toReal < (∫ x in s, |f x| ∂μ) / level := by
      rw [lt_div_iff₀ hlevel]; exact h1'
    calc (μ s).toReal < (∫ x in s, |f x| ∂μ) / level := h3
      _ = (∫ x in s, |f x| ∂μ) * level⁻¹ := by rw [div_eq_mul_inv]
      _ = level⁻¹ * ∫ x in s, |f x| ∂μ := by ring
  -- Step 3: The integral of |f| is nonnegative
  have hint : 0 ≤ ∫ x in s, |f x| ∂μ := setIntegral_nonneg hs (fun _ _ => abs_nonneg _)
  -- Step 4: Convert to ENNReal
  have h3 : (μ s).toReal ≤ level⁻¹ * ∫ x in s, |f x| ∂μ := h2.le
  -- Step 5: ENNReal conversion
  calc μ s = ENNReal.ofReal (μ s).toReal := (ENNReal.ofReal_toReal hμ').symm
    _ ≤ ENNReal.ofReal (level⁻¹ * ∫ x in s, |f x| ∂μ) := ENNReal.ofReal_le_ofReal h3
    _ = ENNReal.ofReal level⁻¹ * ENNReal.ofReal (∫ x in s, |f x| ∂μ) := by
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hlevel.le)]
    _ = ENNReal.ofReal (1 / level) * ENNReal.ofReal (∫ x in s, |f x| ∂μ) := by
        rw [one_div]
    _ ≤ ENNReal.ofReal (1 / level) * ∫⁻ x in s, ‖f x‖₊ ∂μ := by
        gcongr
        -- Convert Bochner integral of |f| to Lebesgue integral of ‖f‖₊
        -- Key: ∫ |f| ≤ ∫⁻ ‖f‖₊ via ofReal_integral_eq_lintegral_ofReal
        rw [ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ (fun _ => abs_nonneg _))]
        apply lintegral_mono
        intro x
        -- For real f: ENNReal.ofReal |f x| = ‖f x‖ₑ = ‖f x‖₊
        -- |f x| = ‖f x‖ for real values, and ofReal ‖·‖ = enorm = nnnorm
        simp only [← Real.norm_eq_abs]
        simp

/-! ### Helper Lemmas for Partitions and Averages -/

section PartitionHelpers

variable {ι : Type*}

/-- The tsum of an indicator function applied to an element in a pairwise disjoint family equals
the function value at that element. Uses `tsum_eq_single` and disjointness. -/
lemma tsum_indicator_eq_single_of_disjoint {s : ℕ → Set α} {f : α → ℝ}
    (hs : ∀ m n, m ≠ n → Disjoint (s m) (s n)) {x : α} {j : ℕ} (hj : x ∈ s j) :
    ∑' n, (s n).indicator f x = f x := by
  rw [tsum_eq_single j]
  · exact indicator_of_mem hj f
  · intro k hkj
    have hdisj := hs k j hkj
    rw [Set.disjoint_iff_inter_eq_empty] at hdisj
    have hxk : x ∉ s k := by
      intro hk
      have hmem : x ∈ s k ∩ s j := ⟨hk, hj⟩
      rw [hdisj] at hmem
      exact hmem
    exact indicator_of_notMem hxk f

/-- If x is not in any piece, the tsum of indicators is zero. -/
lemma tsum_indicator_eq_zero_of_not_mem {s : ℕ → Set α} {f : α → ℝ} {x : α}
    (hx : ∀ n, x ∉ s n) :
    ∑' n, (s n).indicator f x = 0 := by
  have heq : ∀ n, (s n).indicator f x = 0 := fun n => indicator_of_notMem (hx n) f
  simp only [heq, tsum_zero]

/-- Integral of a function over a union equals the sum of integrals over each piece
when the pieces are pairwise disjoint and measurable. -/
lemma integral_iUnion_of_disjoint' {s : ι → Set α} [Countable ι]
    (hs : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (hmeas : ∀ i, MeasurableSet (s i)) {f : α → ℝ} (hf : Integrable f μ) :
    ∫ x in ⋃ i, s i, f x ∂μ = ∑' i, ∫ x in s i, f x ∂μ := by
  have hpw : Pairwise fun i j => Disjoint (s i) (s j) := fun i j hij => hs i j hij
  exact integral_iUnion hmeas hpw hf.integrableOn

/-- The integral of (f - average) over a set with finite positive measure is zero.
This is a fundamental property: `∫_s (f - ⨍_s f) dμ = 0`.

**Proof sketch**: By linearity of integral:
`∫_s (f - ⨍_s f) = ∫_s f - (⨍_s f) · μ(s) = ∫_s f - (∫_s f / μ(s)) · μ(s) = 0`

This lemma is the key property that ensures each bad part in the CZ decomposition has zero mean.

**API used**: `integral_sub`, `setIntegral_const`, `setAverage_eq`, `measureReal_def` -/
lemma integral_sub_setAverage_eq_zero' {s : Set α}
    {f : α → ℝ} (hf : IntegrableOn f s μ) (hμ : μ s ≠ 0) (hμ' : μ s ≠ ⊤) :
    ∫ x in s, (f x - ⨍ y in s, f y ∂μ) ∂μ = 0 := by
  -- Uses: integral_sub, setIntegral_const, setAverage_eq, measureReal_def
  -- After applying these, the expression becomes ∫_s f - ∫_s f = 0
  have hconst : IntegrableOn (fun _ => ⨍ y in s, f y ∂μ) s μ := integrableOn_const hμ'
  rw [integral_sub hf hconst, setIntegral_const, setAverage_eq]
  simp only [smul_eq_mul, measureReal_def]
  -- Now: ∫ f - (μ s).toReal⁻¹ * ∫ f * (μ s).toReal = 0
  have hpos : 0 < (μ s).toReal := ENNReal.toReal_pos hμ hμ'
  have : (μ s).toReal⁻¹ * (∫ x in s, f x ∂μ) * (μ s).toReal = ∫ x in s, f x ∂μ := by
    field_simp
  linarith

end PartitionHelpers

/-! ### Missing API Lemmas for CZ Decomposition

These lemmas provide the key estimates needed for the Calderón-Zygmund decomposition.
They bridge Mathlib's `IsUnifLocDoublingMeasure` with the specific needs of the CZ construction. -/

section MissingAPI

/-! #### Measure Comparison Lemmas -/

/-- For open balls in a metric space with doubling measure, the measure of a ball is
comparable to the measure of the closed ball. This follows from the doubling property
and the fact that the boundary has measure zero for continuous measures. -/
lemma measure_ball_le_measure_closedBall' (x : α) (r : ℝ) :
    μ (ball x r) ≤ μ (closedBall x r) := measure_mono ball_subset_closedBall

/-- The doubling constant controls measure ratios for nested balls.
This is the key estimate for bmo_telescoping.

For doubling measures, if B ⊆ B₀ with comparable radii, then μ(B₀)/μ(B) is bounded
by the scaling constant from `IsUnifLocDoublingMeasure`.

Note: The Mathlib `IsUnifLocDoublingMeasure` is uniformly *locally* doubling, meaning
the doubling property only holds for radii below `scalingScaleOf μ K`. For globally
doubling measures (as in the Carleson project), this constraint is not needed.

**Key API**: `IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul` -/
lemma measure_ball_ratio_le {x₀ x : α} {r r₀ : ℝ} {K : ℝ}
    (hr : 0 < r) (hr₀ : 0 < r₀) (hcontained : ball x r ⊆ ball x₀ r₀)
    (hK : r₀ / r ≤ K) (hK_pos : 0 < K)
    (hr_scale : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (2 * K)) :
    (μ (ball x₀ r₀)).toReal / (μ (closedBall x r)).toReal ≤
        IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K) := by
  have hB_ne : μ (ball x r) ≠ 0 := (measure_ball_pos _ x hr).ne'
  have hB_top : μ (ball x r) ≠ ⊤ := measure_ball_ne_top
  have hB₀_top : μ (ball x₀ r₀) ≠ ⊤ := measure_ball_ne_top
  have hB_pos : 0 < (μ (ball x r)).toReal := ENNReal.toReal_pos hB_ne hB_top
  have hκ := IsUnifLocDoublingMeasure.one_le_scalingConstantOf μ (2 * K)
  -- From x ∈ ball x₀ r₀ (implied by containment) and triangle inequality:
  have hx_in : x ∈ ball x₀ r₀ := hcontained (mem_ball_self hr)
  have hdist : dist x x₀ < r₀ := mem_ball.mp hx_in
  -- ball x₀ r₀ ⊆ closedBall x (2 * r₀)
  have hB₀_sub : ball x₀ r₀ ⊆ closedBall x (2 * r₀) := by
    intro y hy
    rw [mem_ball] at hy
    rw [mem_closedBall, dist_comm]
    calc dist x y ≤ dist x x₀ + dist x₀ y := dist_triangle x x₀ y
      _ ≤ r₀ + r₀ := by
        have hy' : dist x₀ y ≤ r₀ := by simpa [dist_comm] using hy.le
        exact add_le_add hdist.le hy'
      _ = 2 * r₀ := by ring
  have hr₀_le : r₀ ≤ K * r := by rw [div_le_iff₀ hr] at hK; exact hK
  have h2r₀_le : 2 * r₀ ≤ 2 * K * r := by linarith
  -- Apply the doubling property using measure_mul_le_scalingConstantOf_mul
  have h2K_pos : 0 < 2 * K := by linarith
  have h2K_mem : 2 * K ∈ Set.Ioc 0 (2 * K) := ⟨h2K_pos, le_refl _⟩
  -- switch to closed balls for both numerator and denominator to use the doubling inequality
  have hcb_pos : 0 < (μ (closedBall x r)).toReal :=
    ENNReal.toReal_pos ((measure_ball_pos _ _ hr).trans_le (measure_mono ball_subset_closedBall) |>.ne')
      measure_closedBall_lt_top.ne
  calc (μ (ball x₀ r₀)).toReal / (μ (closedBall x r)).toReal
      ≤ (μ (closedBall x (2 * r₀))).toReal / (μ (closedBall x r)).toReal := by
        apply div_le_div_of_nonneg_right _ hcb_pos.le
        exact ENNReal.toReal_mono (measure_closedBall_lt_top.ne) (measure_mono hB₀_sub)
    _ ≤ (μ (closedBall x (2 * K * r))).toReal / (μ (closedBall x r)).toReal := by
        apply div_le_div_of_nonneg_right _ hcb_pos.le
        apply ENNReal.toReal_mono (measure_closedBall_lt_top.ne)
        exact measure_mono (closedBall_subset_closedBall h2r₀_le)
    _ ≤ (IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K) * μ (closedBall x r)).toReal /
          (μ (closedBall x r)).toReal := by
        apply div_le_div_of_nonneg_right _ hcb_pos.le
        have hscaling :=
          IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul
            (μ := μ) (x := x) h2K_mem hr_scale
        have hfinite :
            IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K) * μ (closedBall x r) ≠ ∞ := by
          have hconst : (↑(IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K)) : ℝ≥0∞) ≠ ∞ := by
            simp
          exact ENNReal.mul_ne_top hconst measure_closedBall_lt_top.ne
        exact ENNReal.toReal_mono hfinite hscaling
    _ = IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K) := by
        have hconst : (↑(IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K)) : ℝ≥0∞) ≠ ∞ := by
          simp
        have hmu : μ (closedBall x r) ≠ ∞ := measure_closedBall_lt_top.ne
        have htoReal :
            (IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K) * μ (closedBall x r)).toReal =
              (μ (closedBall x r)).toReal *
                IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K) := by
          simp [mul_comm]
        calc
          (IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K) * μ (closedBall x r)).toReal /
                (μ (closedBall x r)).toReal
              = ((μ (closedBall x r)).toReal *
                  IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K)) /
                  (μ (closedBall x r)).toReal := by simp [htoReal]
          _ = IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * K) := by
            have hpos : (μ (closedBall x r)).toReal ≠ 0 := hcb_pos.ne'
            field_simp [hpos]

/-- For a uniformly locally doubling measure, the ratio `μ(closedBall x r) / μ(ball x r)`
is bounded by the doubling constant.

This follows from: `closedBall x r ⊆ closedBall x (2 * r/2)`, and by the doubling property
`μ(closedBall x r) ≤ scalingConstantOf μ 2 * μ(closedBall x (r/2)) ≤ scalingConstantOf μ 2 * μ(ball x r)`
(using `ball x (r/2) ⊆ closedBall x (r/2)` and monotonicity).

**Key insight**: For doubling measures, open and closed balls have comparable measures. -/
lemma measure_closedBall_le_mul_measure_ball (x : α) {r : ℝ} (hr : 0 < r)
    (hr_scale : r / 2 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 2) :
    μ (closedBall x r) ≤ IsUnifLocDoublingMeasure.scalingConstantOf μ 2 * μ (ball x r) := by
  -- Use that closedBall x r = closedBall x (2 * (r/2))
  have h2_mem : (2 : ℝ) ∈ Set.Ioc 0 2 := ⟨zero_lt_two, le_refl 2⟩
  have hdoubling := @IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul
    α _ _ μ _ 2 x 2 (r / 2) h2_mem hr_scale
  have heq : closedBall x r = closedBall x (2 * (r / 2)) := by
    congr 1; ring
  rw [heq]
  calc μ (closedBall x (2 * (r / 2)))
      ≤ IsUnifLocDoublingMeasure.scalingConstantOf μ 2 * μ (closedBall x (r / 2)) := hdoubling
    _ ≤ IsUnifLocDoublingMeasure.scalingConstantOf μ 2 * μ (ball x r) := by
        apply mul_le_mul_left'
        apply measure_mono
        apply closedBall_subset_ball
        linarith

/-- The ratio `μ(closedBall x r) / μ(ball x r)` is bounded for doubling measures.
This is essential for transferring between ball and closedBall averages. -/
lemma measure_closedBall_div_measure_ball_le (x : α) {r : ℝ} (hr : 0 < r)
    (hr_scale : r / 2 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 2) :
    (μ (closedBall x r)).toReal / (μ (ball x r)).toReal ≤
        IsUnifLocDoublingMeasure.scalingConstantOf μ 2 := by
  have hball_pos : 0 < μ (ball x r) := measure_ball_pos μ x hr
  have hball_ne_zero : μ (ball x r) ≠ 0 := hball_pos.ne'
  have hball_ne_top : μ (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  have hcball_ne_top : μ (closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hball_toReal_pos : 0 < (μ (ball x r)).toReal := ENNReal.toReal_pos hball_ne_zero hball_ne_top
  have hκ := IsUnifLocDoublingMeasure.one_le_scalingConstantOf μ 2
  have hκ_ne_top : (IsUnifLocDoublingMeasure.scalingConstantOf μ 2 : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hprod_ne_top : IsUnifLocDoublingMeasure.scalingConstantOf μ 2 * μ (ball x r) ≠ ⊤ :=
    ENNReal.mul_ne_top hκ_ne_top hball_ne_top
  have hbound := measure_closedBall_le_mul_measure_ball μ x hr hr_scale
  rw [div_le_iff₀ hball_toReal_pos]
  calc (μ (closedBall x r)).toReal
      ≤ (IsUnifLocDoublingMeasure.scalingConstantOf μ 2 * μ (ball x r)).toReal :=
        ENNReal.toReal_mono hprod_ne_top hbound
    _ = IsUnifLocDoublingMeasure.scalingConstantOf μ 2 * (μ (ball x r)).toReal := by
        rw [ENNReal.toReal_mul]
        rfl

/-! #### Vitali Covering Theorem API

The Mathlib Vitali covering theorem provides the key tool for constructing
disjoint subfamilies with controlled enlargement.

**Main API from Mathlib** (`Mathlib.MeasureTheory.Covering.Vitali`):

* `Vitali.exists_disjoint_subfamily_covering_enlargement`: Given any family of sets
  with a "size" function δ, extracts a disjoint subfamily such that every original
  set intersects some subfamily member with comparable size.

* `Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall`: Specialized
  version for closed balls - extracts disjoint balls whose τ-dilations cover all
  original balls.

**Usage pattern**:
```
rcases Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    t x r R hr 5 (by linarith : 3 < 5) with ⟨u, ut, u_disj, u_cover⟩
-- u ⊆ t: subfamily
-- u_disj: pairwise disjoint
-- u_cover: ∀ a ∈ t, ∃ b ∈ u, closedBall (x a) (r a) ⊆ closedBall (x b) (5 * r b)
```

This is the foundation for CZ covering constructions. -/

/-! #### Whitney/Ball Covering API

The Carleson project provides `ball_covering` for Whitney-type decompositions
of open sets. This is adapted from the depth-based approach.

**Main API from Carleson** (`Carleson.TwoSidedCarleson.WeakCalderonZygmund`):

* `ball_covering`: For any open proper subset O of a doubling metric space,
  produces a countable family of balls such that:
  - The small balls are pairwise disjoint
  - The 3× dilations cover O exactly
  - The 7× dilations touch the boundary
  - Bounded overlap (at most 2^(6a) balls cover any point)

```
theorem ball_covering (hO : IsOpen O ∧ O ≠ univ) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ),
      (univ.PairwiseDisjoint fun i ↦ ball (c i) (r i)) ∧
      ⋃ i, ball (c i) (3 * r i) = O ∧
      (∀ i, 0 < r i → ¬Disjoint (ball (c i) (7 * r i)) Oᶜ) ∧
      ∀ x ∈ O, {i | x ∈ ball (c i) (3 * r i)}.encard ≤ (2 ^ (6 * a) : ℕ)
```

The depth function `depth O x = sup{r : ball x r ⊆ O}` measures how deep
a point is inside O. The radii are chosen proportional to depth, ensuring
the boundary-touching property.

**For CZ decomposition**: Apply to O = {x : Mf x > λ} to get the covering balls. -/

/-! #### Average Monotonicity Lemmas -/

/-- Average over a subset is bounded by average over the superset times a constant,
when the measure ratio is controlled. -/
lemma setAverage_subset_le_mul {s t : Set α} (hst : s ⊆ t)
    (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (hμs : μ s ≠ 0) (hμs' : μ s ≠ ⊤) (hμt' : μ t ≠ ⊤)
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (hf_int : IntegrableOn f t μ)
    {C : ℝ} (hC : (μ t).toReal / (μ s).toReal ≤ C) :
    ⨍ x in s, f x ∂μ ≤ C * ⨍ x in t, f x ∂μ := by
  have hμt : μ t ≠ 0 := fun h => hμs (measure_mono_null hst h)
  have hs_pos : 0 < (μ s).toReal := ENNReal.toReal_pos hμs hμs'
  have ht_pos : 0 < (μ t).toReal := ENNReal.toReal_pos hμt hμt'
  simp only [setAverage_eq, smul_eq_mul, measureReal_def]
  -- ∫_s f / μ(s) ≤ C * ∫_t f / μ(t)
  -- Since s ⊆ t, ∫_s f ≤ ∫_t f
  have hf_ae : 0 ≤ᶠ[ae (μ.restrict t)] f := ae_of_all _ hf
  have hint : ∫ x in s, f x ∂μ ≤ ∫ x in t, f x ∂μ :=
    setIntegral_mono_set hf_int hf_ae hst.eventuallyLE
  have hint_nonneg : 0 ≤ ∫ x in t, f x ∂μ := setIntegral_nonneg ht_meas (fun x _ => hf x)
  -- Need: ∫_s f / μ(s) ≤ C * ∫_t f / μ(t)
  -- Since ∫_s f ≤ ∫_t f and μ(t)/μ(s) ≤ C:
  -- ∫_s f / μ(s) ≤ ∫_t f / μ(s) = (μ(t)/μ(s)) * (∫_t f / μ(t)) ≤ C * ∫_t f / μ(t)
  calc (μ s).toReal⁻¹ * ∫ x in s, f x ∂μ
      ≤ (μ s).toReal⁻¹ * ∫ x in t, f x ∂μ := by
        apply mul_le_mul_of_nonneg_left hint (inv_pos.mpr hs_pos).le
    _ = ((μ t).toReal / (μ s).toReal) * ((μ t).toReal⁻¹ * ∫ x in t, f x ∂μ) := by
        field_simp [hs_pos.ne', ht_pos.ne']
    _ ≤ C * ((μ t).toReal⁻¹ * ∫ x in t, f x ∂μ) := by
        apply mul_le_mul_of_nonneg_right hC
        exact mul_nonneg (inv_pos.mpr ht_pos).le hint_nonneg

/-! #### Lebesgue Differentiation Consequences -/

/-- If the average of |f| over all balls centered at x is bounded by M for all x,
then |f x| ≤ M for a.e. x. This is a consequence of the Lebesgue differentiation theorem
for doubling measures.

For doubling measures, the VitaliFamily gives the differentiation theorem:
`VitaliFamily.ae_tendsto_average` shows that ⨍_{B(x,r)} f → f(x) as r → 0 a.e.
Hence if ⨍_{B(x,r)} |f| ≤ M for all r > 0, we get |f(x)| ≤ M a.e. -/
lemma ae_le_of_setAverage_le {f : α → ℝ} (hf : LocallyIntegrable f μ) {M : ℝ} (hM : 0 ≤ M)
    (hbound_ball : ∀ x r, 0 < r → ⨍ y in ball x r, |f y| ∂μ ≤ M)
    (hbound_closed : ∀ x r, 0 < r → ⨍ y in closedBall x r, |f y| ∂μ ≤ M) :
    ∀ᵐ x ∂μ, |f x| ≤ M := by
  -- By Lebesgue differentiation: |f x| = lim_{r→0} ⨍_{B(x,r)} |f y| dy a.e.
  -- Since ⨍_{B(x,r)} |f y| dy ≤ M for all r, the limit is ≤ M
  have habs_loc : LocallyIntegrable (fun x => |f x|) μ := hf.norm
  -- Lebesgue differentiation gives: for a.e. x, averages of |f| over balls centered at x converge to |f x|
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := μ) habs_loc 1
  filter_upwards [hdiff] with x hx
  -- hx says: for any sequence (w, δ) with δ → 0⁺ and x ∈ closedBall (w j) (1 * δ j),
  -- we have ⨍ closedBall (w j) (δ j) |f| → |f x|
  -- Apply this with the constant sequence w_j = x and δ_j = 1/n
  let δ : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hδ_pos : ∀ n, 0 < δ n := fun n => by simp [δ]; positivity
  have hδ_tendsto : Tendsto δ atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · -- δ → 0
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [δ, one_div] using this
    · -- δ > 0
      filter_upwards with n
      exact hδ_pos n
  have hx_in : ∀ᶠ j in atTop, x ∈ closedBall x (1 * δ j) := by
    filter_upwards with j
    simp [mem_closedBall, dist_self, one_mul, (hδ_pos j).le]
  have htendsto := hx (fun _ => x) δ hδ_tendsto hx_in
  -- htendsto: ⨍ closedBall x (δ j) |f| → |f x|
  -- Since each average is ≤ M, the limit is ≤ M
  refine le_of_tendsto htendsto ?_
  filter_upwards with n
  -- Need: ⨍ closedBall x (δ n) |f| ≤ M
  -- Use that ball x (δ n) ⊆ closedBall x (δ n) and bound from hbound
  have hδn := hδ_pos n
  -- The average over closedBall is controlled by the average over ball
  -- For x ∈ closedBall, we have ball x (δ n) ⊆ closedBall x (δ n)
  calc ⨍ y in closedBall x (δ n), |f y| ∂μ
      ≤ ⨍ y in closedBall x (δ n), |f y| ∂μ := le_refl _
    _ ≤ M := hbound_closed x (δ n) hδn

/-! #### Integrability Lemmas -/

/-- A function that equals a constant on a finite measure set and equals an integrable function
elsewhere is integrable.

**API**: Uses `Integrable.piecewise` and `integrableOn_const` -/
lemma integrable_piecewise_const_of_integrable' {f : α → ℝ} (hf : Integrable f μ)
    {s : Set α} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (c : ℝ) :
    Integrable (s.piecewise (fun _ => c) f) μ :=
  Integrable.piecewise hs (integrableOn_const hμs) hf.integrableOn

/-- An indicator of (f - c) on a finite measure set with f integrable is integrable.

**API**: The key insight is that s.indicator g is supported on s, so integrability
on the whole space follows from integrability on s. -/
lemma integrable_indicator_sub_const' {s : Set α} {f : α → ℝ} (hf : IntegrableOn f s μ)
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (c : ℝ) :
    Integrable (s.indicator (f - fun _ => c)) μ := by
  -- s.indicator (f - c) has support in s, so use integrability on s
  -- The function (f - c) restricted to s is integrable since f is integrable on s
  have hconst : IntegrableOn (fun _ => c) s μ := integrableOn_const hμs
  have hsub : IntegrableOn (f - fun _ => c) s μ := hf.sub hconst
  -- The indicator of an integrable function on a measurable set is integrable
  exact hsub.integrable_indicator hs

/-- A function that is piecewise constant on disjoint sets covering the support,
with each constant bounded, is integrable if the sum of integrals is finite.

**Proof idea**: By disjointness, at each point at most one indicator is nonzero,
so the sum equals a single term. The total integral is bounded by the sum of
integrals over each piece.

**Note**: This lemma requires an explicit hypothesis that the sum of integrals is finite.
For the CZ decomposition, this follows from the overlap bound. -/
lemma integrable_tsum_indicator_of_finite_measure' {ι : Type*} [Countable ι]
    {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j))
    {f : ι → α → ℝ} (hf : ∀ i, IntegrableOn (f i) (s i) μ)
    (hsum : ∑' i, ∫⁻ x in s i, ‖f i x‖₊ ∂μ ≠ ⊤) :
    Integrable (fun x => ∑' i, (s i).indicator (f i) x) μ := by
  /- **Proof structure**:
  1. Each indicator (s i).indicator (f i) is integrable
  2. By disjointness, at each point at most one term of the tsum is nonzero
  3. Hence ‖tsum‖ = tsum ‖·‖ pointwise, and lintegral commutes with tsum
  4. The sum of lintegrals is finite by hypothesis

  **AEStronglyMeasurable**: The tsum equals at most one indicator at each point
  (by disjointness), so measurability follows from the indicator measurability.

  **HasFiniteIntegral**: By disjointness and Tonelli's theorem:
  ∫ ‖tsum‖ = ∑' i ∫ ‖indicator_i‖ < ∞ by hypothesis. -/

  -- Each indicator function is integrable
  have hind_int : ∀ i, Integrable ((s i).indicator (f i)) μ := fun i =>
    (hf i).integrable_indicator (hs i)
  -- By disjointness, at each point x, at most one indicator is nonzero
  have hdisjoint_support : ∀ x, ∀ i j, i ≠ j → x ∈ s i → x ∉ s j := by
    intro x i j hij hxi
    exact Set.disjoint_left.mp (hdisj hij) hxi
  -- Key property: at each point, at most one term is nonzero
  have htsum_single : ∀ x, (∃ i, x ∈ s i) →
      ∃ i₀, x ∈ s i₀ ∧ ∀ j ≠ i₀, (s j).indicator (f j) x = 0 := by
    intro x ⟨i, hi⟩
    use i, hi
    intro j hj
    exact Set.indicator_of_notMem (hdisjoint_support x i j hj.symm hi) (f j)
  have htsum_zero : ∀ x, (∀ i, x ∉ s i) → ∑' i, (s i).indicator (f i) x = 0 := by
    intro x hx
    simp only [Set.indicator_of_notMem (hx _), tsum_zero]
  -- The sum of lintegral norms is finite
  have hsum' : ∑' i, ∫⁻ x, ↑‖(s i).indicator (f i) x‖₊ ∂μ < ⊤ := by
    have heq : ∀ i, ∫⁻ x, ↑‖(s i).indicator (f i) x‖₊ ∂μ = ∫⁻ x in s i, ↑‖f i x‖₊ ∂μ := by
      intro i
      trans ∫⁻ x, (s i).indicator (fun y => (‖f i y‖₊ : ℝ≥0∞)) x ∂μ
      · apply lintegral_congr
        intro x
        by_cases hx : x ∈ s i
        · simp only [Set.indicator_of_mem hx]
        · simp only [Set.indicator_of_notMem hx, nnnorm_zero, ENNReal.coe_zero]
      · exact lintegral_indicator (hs i) (fun y => (‖f i y‖₊ : ℝ≥0∞))
    simp_rw [heq]
    exact hsum.lt_top
  -- Pointwise: ‖∑' i, indicator_i x‖ = ∑' i, ‖indicator_i x‖ (by disjointness, at most one nonzero)
  have hnorm_tsum : ∀ x, ‖∑' i, (s i).indicator (f i) x‖₊ = ∑' i, ‖(s i).indicator (f i) x‖₊ := by
    intro x
    by_cases hex : ∃ i, x ∈ s i
    · obtain ⟨i₀, hi₀, hzero⟩ := htsum_single x hex
      classical
      have heq1 : ∑' j, (s j).indicator (f j) x = (s i₀).indicator (f i₀) x := by
        have hterm : ∀ j, (s j).indicator (f j) x = if j = i₀ then (s i₀).indicator (f i₀) x else 0 := by
          intro j; by_cases hj : j = i₀
          · rw [hj, if_pos rfl]
          · rw [if_neg hj, hzero j hj]
        rw [show (fun j => (s j).indicator (f j) x) = (fun j => if j = i₀ then (s i₀).indicator (f i₀) x else 0) from funext hterm]
        exact tsum_ite_eq i₀ _
      have heq2 : ∑' j, ‖(s j).indicator (f j) x‖₊ = ‖(s i₀).indicator (f i₀) x‖₊ := by
        have hterm : ∀ j, ‖(s j).indicator (f j) x‖₊ = if j = i₀ then ‖(s i₀).indicator (f i₀) x‖₊ else 0 := by
          intro j; by_cases hj : j = i₀
          · rw [hj, if_pos rfl]
          · rw [if_neg hj, hzero j hj, nnnorm_zero]
        rw [show (fun j => ‖(s j).indicator (f j) x‖₊) = (fun j => if j = i₀ then ‖(s i₀).indicator (f i₀) x‖₊ else 0) from funext hterm]
        exact tsum_ite_eq i₀ _
      rw [heq1, heq2]
    · push_neg at hex
      have h1 : ∑' j, (s j).indicator (f j) x = 0 := htsum_zero x hex
      have h2 : ∑' j, ‖(s j).indicator (f j) x‖₊ = 0 := by
        have hterm : ∀ j, ‖(s j).indicator (f j) x‖₊ = 0 := fun j => by simp [Set.indicator_of_notMem (hex j)]
        simp [hterm]
      simp [h1, h2]
  -- AEStronglyMeasurable via partial sum convergence
  have haesm : AEStronglyMeasurable (fun x => ∑' i, (s i).indicator (f i) x) μ := by
    classical
    rcases Countable.exists_injective_nat ι with ⟨e, he⟩
    -- Extend the family along `e : ι → ℕ`, using `0` outside `Set.range e`.
    let g : ℕ → α → ℝ := fun n x =>
      Function.extend e (fun i : ι => (s i).indicator (f i) x) (fun _ : ℕ => 0) n
    have hg : ∀ n, AEStronglyMeasurable (g n) μ := by
      intro n
      by_cases hn : ∃ i : ι, e i = n
      · rcases hn with ⟨i, rfl⟩
        -- On the range of `e`, `Function.extend` agrees with the original function.
        have hgi : g (e i) = (s i).indicator (f i) := by
          funext x
          simp [g, he]
        simpa [hgi] using (hind_int i).aestronglyMeasurable
      · have hn' : ¬ ∃ i : ι, e i = n := hn
        have : g n = fun _ : α => 0 := by
          funext x
          simp [g, Function.extend_apply', hn']
        simpa [this] using (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : α => (0 : ℝ)) μ)
    -- Measurability follows from convergence of the finite partial sums on `ℕ`.
    have haesm_nat : AEStronglyMeasurable (fun x => ∑' n, g n x) μ := by
      apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
        (f := fun n x => ∑ i ∈ Finset.range n, g i x)
      · intro n
        simp only [← Finset.sum_apply]
        exact Finset.aestronglyMeasurable_sum (Finset.range n) (fun i _ => hg i)
      · refine ae_of_all _ (fun x => ?_)
        -- Pointwise, the series has at most one nonzero term, hence is summable.
        by_cases hex : ∃ i : ι, x ∈ s i
        · obtain ⟨i₀, hi₀, hzero⟩ := htsum_single x hex
          have hsupport : (Function.support fun n => g n x) ⊆ {e i₀} := by
            intro n hn
            by_contra hne
            have : g n x = 0 := by
              by_cases hn' : ∃ i : ι, e i = n
              · rcases hn' with ⟨i, rfl⟩
                have hi : i ≠ i₀ := by
                  intro h
                  exact hne (by simp [h] )
                have : (s i).indicator (f i) x = 0 := hzero i hi
                simp [g, he, this]
              · have hn'' : ¬ ∃ i : ι, e i = n := hn'
                simp [g, Function.extend_apply', hn'']
            exact (hn (by simpa [Function.support] using this)).elim
          have hfin : (Function.support fun n => g n x).Finite :=
            (Set.finite_singleton (e i₀)).subset hsupport
          have hsumm : Summable (fun n => g n x) := summable_of_finite_support hfin
          exact (hsumm.hasSum.tendsto_sum_nat)
        · push_neg at hex
          have : ∀ n, g n x = 0 := by
            intro n
            by_cases hn : ∃ i : ι, e i = n
            · rcases hn with ⟨i, rfl⟩
              have : (s i).indicator (f i) x = 0 :=
                Set.indicator_of_notMem (hex i) (f i)
              simp [g, he, this]
            · have hn' : ¬ ∃ i : ι, e i = n := hn
              simp [g, Function.extend_apply', hn']
          have hsumm : Summable (fun n => g n x) := by
            simpa [this] using (summable_zero : Summable (fun n : ℕ => (0 : ℝ)))
          simp [this] -- using (hsumm.hasSum.tendsto_sum_nat)
    -- Finally, identify the limit with the original `tsum` over `ι` using `tsum_extend_zero`.
    have htsum : (fun x => ∑' n, g n x) = fun x => ∑' i : ι, (s i).indicator (f i) x := by
      funext x
      -- `g · x` is the extension of `i ↦ (s i).indicator (f i) x` along `e`.
      simpa [g] using (tsum_extend_zero he (fun i : ι => (s i).indicator (f i) x))
    simpa [htsum] using haesm_nat
  -- HasFiniteIntegral: ∫ ‖tsum‖ = ∫ tsum ‖·‖ = ∑' ∫ ‖indicator_i‖ < ∞
  have hfi : HasFiniteIntegral (fun x => ∑' i, (s i).indicator (f i) x) μ := by
    rw [hasFiniteIntegral_def]
    calc ∫⁻ x, ‖∑' i, (s i).indicator (f i) x‖₊ ∂μ
        = ∫⁻ x, ∑' i, ‖(s i).indicator (f i) x‖₊ ∂μ := by
          refine lintegral_congr ?_
          intro x
          -- `hnorm_tsum` is an equality in `ℝ≥0`; coerce to `ℝ≥0∞` and rewrite the RHS.
          classical
          have hsumm : Summable (fun i : ι => ‖(s i).indicator (f i) x‖₊) := by
            by_cases hex : ∃ i : ι, x ∈ s i
            · obtain ⟨i₀, hi₀, hzero⟩ := htsum_single x hex
              have hsupport :
                  Function.support (fun i : ι => ‖(s i).indicator (f i) x‖₊) ⊆ ({i₀} : Set ι) := by
                intro i hi
                by_contra hmem
                have hne : i ≠ i₀ := by simpa [Set.mem_singleton_iff] using hmem
                have h0 : (s i).indicator (f i) x = 0 := hzero i hne
                have hnorm0 : ‖(s i).indicator (f i) x‖₊ = 0 := by simp [h0]
                exact hi hnorm0
              have hfin :
                  (Function.support (fun i : ι => ‖(s i).indicator (f i) x‖₊)).Finite :=
                (Set.finite_singleton i₀).subset hsupport
              exact summable_of_finite_support hfin
            · push_neg at hex
              have hz : (fun i : ι => ‖(s i).indicator (f i) x‖₊) = fun _ => 0 := by
                funext i
                simp [Set.indicator_of_notMem (hex i)]
              simpa [hz] using (summable_zero : Summable (fun _ : ι => (0 : ℝ≥0)))
          have hcoe :
              (↑(∑' i : ι, ‖(s i).indicator (f i) x‖₊) : ℝ≥0∞) =
                ∑' i : ι, (↑‖(s i).indicator (f i) x‖₊ : ℝ≥0∞) := by
            simpa using (ENNReal.coe_tsum hsumm)
          -- Now finish by coercing `hnorm_tsum`.
          calc
            (↑‖∑' i : ι, (s i).indicator (f i) x‖₊ : ℝ≥0∞)
                = (↑(∑' i : ι, ‖(s i).indicator (f i) x‖₊) : ℝ≥0∞) := by
                    exact congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (hnorm_tsum x)
            _ = ∑' i : ι, (↑‖(s i).indicator (f i) x‖₊ : ℝ≥0∞) := hcoe
      _ = ∑' i, ∫⁻ x, ‖(s i).indicator (f i) x‖₊ ∂μ := by
          apply lintegral_tsum; intro i; exact (hind_int i).aestronglyMeasurable.enorm
      _ < ⊤ := hsum'
  exact ⟨haesm, hfi⟩

end MissingAPI

end Avg

/-! #### Recursive Partition Lemmas -/
section Partition

variable {β : Type*} [MeasurableSpace β] [PseudoMetricSpace β] [BorelSpace β]

/-- Define the recursive partition explicitly to simplify proofs. -/
def czPartitionAux (Bⱼ : ℕ → Set β) : ℕ → Set β
  | 0 => Bⱼ 0 \ ⋃ j > 0, Bⱼ j
  | n + 1 => Bⱼ (n + 1) \ ((⋃ j < n + 1, czPartitionAux Bⱼ j) ∪ ⋃ j > n + 1, Bⱼ j)

/-- A recursive partition defined by removing previous elements and smaller balls
is pairwise disjoint. This captures the key property of the czPartition construction. -/
lemma czPartitionAux_pairwise_disjoint
    (Bⱼ : ℕ → Set β) :
    Pairwise (fun i j => Disjoint (czPartitionAux Bⱼ i) (czPartitionAux Bⱼ j)) := by
  intro i j hij
  rcases Nat.lt_trichotomy i j with h | rfl | h
  · -- Case i < j
    rw [Set.disjoint_left]
    intro x hxi hxj
    cases j with
    | zero => exact (Nat.not_lt_zero i h).elim
    | succ m =>
      unfold czPartitionAux at hxj
      simp only [Set.mem_diff, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxj
      exact hxj.2.1 i h hxi
  · exact (hij rfl).elim
  · -- Case j < i: symmetric to i < j
    rw [disjoint_comm, Set.disjoint_left]
    intro x hxj hxi
    cases i with
    | zero => exact (Nat.not_lt_zero j h).elim
    | succ m =>
      unfold czPartitionAux at hxi
      simp only [Set.mem_diff, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxi
      exact hxi.2.1 j h hxj

/-- The recursive partition element is contained in Bⱼ n. -/
lemma czPartitionAux_subset (Bⱼ : ℕ → Set β) (n : ℕ) :
    czPartitionAux Bⱼ n ⊆ Bⱼ n := by
  cases n with
  | zero =>
    unfold czPartitionAux
    exact Set.diff_subset
  | succ m =>
    unfold czPartitionAux
    exact Set.diff_subset

/-- The recursive partition element is contained in the 3× ball. -/
lemma czPartition_subset_ball3'
    {centers : ℕ → β} {radii : ℕ → ℝ} (hradii : ∀ n, 0 < radii n) (n : ℕ)
    (Bⱼ : ℕ → Set β) (hBⱼ : ∀ j, Bⱼ j = ball (centers j) (3 * radii j)) :
    czPartitionAux Bⱼ n ⊆ ball (centers n) (3 * radii n) := by
  rw [← hBⱼ n]
  exact czPartitionAux_subset Bⱼ n

/-- The recursive partition element is measurable.
Each czPartition n is a difference of measurable sets (balls and countable unions). -/
lemma czPartitionAux_measurableSet
    (Bⱼ : ℕ → Set β) (hBmeas : ∀ j, MeasurableSet (Bⱼ j)) (n : ℕ) :
    MeasurableSet (czPartitionAux Bⱼ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      unfold czPartitionAux
      apply MeasurableSet.diff (hBmeas 0)
      exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => hBmeas j))
    | succ m =>
      unfold czPartitionAux
      apply MeasurableSet.diff (hBmeas (m + 1))
      apply MeasurableSet.union
      · -- ⋃ j < m+1, czPartitionAux Bⱼ j is measurable
        apply MeasurableSet.iUnion
        intro j
        apply MeasurableSet.iUnion
        intro hj
        exact ih j hj
      · exact MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun _ => hBmeas j))

lemma czPartition_measurableSet'
    {centers : ℕ → β} {radii : ℕ → ℝ} (hradii : ∀ n, 0 < radii n) (n : ℕ)
    (Bⱼ : ℕ → Set β) (hBⱼ : ∀ j, Bⱼ j = ball (centers j) (3 * radii j)) :
    MeasurableSet (czPartitionAux Bⱼ n) := by
  apply czPartitionAux_measurableSet
  intro j
  rw [hBⱼ j]
  exact isOpen_ball.measurableSet

end Partition

/-!
## BMO helper lemma

The John–Nirenberg iteration uses a “telescoping” estimate comparing averages over nested balls.
The only nontrivial input is a measure-ratio bound, obtained from:

- `measure_ball_le_scalingConstantOf_mul_closedBall` (in `Riemann/Mathlib/MeasureTheory/Integral/AverageAux.lean`)
- `measure_closedBall_div_measure_ball_le` (proved above in this file)
- the monotonicity lemma `setAverage_subset_le_mul` (proved above)
- Jensen’s inequality in the form `abs_setAverage_le_setAverage_abs` (proved above)
-/
section BMO

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
variable (μ : Measure α) [ProperSpace α] [IsUnifLocDoublingMeasure μ]
variable [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- **BMO telescoping**: if `ball x r ⊆ ball x₀ r₀`, then the difference of averages is controlled
by the BMO bound, with an explicit constant depending on local doubling data. -/
theorem bmo_telescoping {f : α → ℝ} (hf_int : LocallyIntegrable f μ) {M : ℝ} (hM : 0 < M)
    (hbmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in ball x r, |f y - ⨍ z in ball x r, f z ∂μ| ∂μ ≤ M)
    {x₀ : α} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {x : α} {r : ℝ} (hr : 0 < r)
    (h_contained : ball x r ⊆ ball x₀ r₀)
    (hr_scale : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (2 * r₀ / r))
    (hr_scale2 : r / 2 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 2) :
    |⨍ y in ball x r, f y ∂μ - ⨍ y in ball x₀ r₀, f y ∂μ| ≤
      ((IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * r₀ / r) *
          IsUnifLocDoublingMeasure.scalingConstantOf μ 2 : ℝ≥0) : ℝ) * M := by
  classical
  -- Notation
  set B := ball x r with hB
  set B₀ := ball x₀ r₀ with hB₀
  set f_B := ⨍ y in B, f y ∂μ
  set f_B₀ := ⨍ y in B₀, f y ∂μ
  set κ := IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * r₀ / r)
  set δ := IsUnifLocDoublingMeasure.scalingConstantOf μ 2
  have hB_pos : 0 < μ B := measure_ball_pos μ x hr
  have hB₀_pos : 0 < μ B₀ := measure_ball_pos μ x₀ hr₀
  have hB_ne_zero : μ B ≠ 0 := hB_pos.ne'
  have hB_ne_top : μ B ≠ ⊤ := measure_ball_lt_top.ne
  have hB₀_ne_top : μ B₀ ≠ ⊤ := measure_ball_lt_top.ne
  -- Step 1: Jensen on `B` relative to the constant `f_B₀`.
  have hJensen : |f_B - f_B₀| ≤ ⨍ y in B, |f y - f_B₀| ∂μ := by
    have hf_B : IntegrableOn f B μ :=
      hf_int.integrableOn_isCompact (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall
    rw [← setAverage_sub_const μ measurableSet_ball hf_B f_B₀ hB_ne_zero hB_ne_top]
    have hf_sub : IntegrableOn (fun y => f y - f_B₀) B μ := by
      -- `IntegrableOn` is just integrability for `μ.restrict B`.
      simpa [IntegrableOn] using
        (hf_B.integrable.sub
          (integrableOn_const (μ := μ) (s := B) (C := f_B₀) (hs := hB_ne_top) (hC := by simp)).integrable)
    exact abs_setAverage_le_setAverage_abs μ measurableSet_ball hf_sub hB_ne_zero hB_ne_top
  -- Step 2: ratio bound `μ(B₀)/μ(B) ≤ κ * δ`.
  have hratio : (μ B₀).toReal / (μ B).toReal ≤ ((κ * δ : ℝ≥0) : ℝ) := by
    have hcb_ne_top : μ (closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hprod_ne_top : (κ : ℝ≥0∞) * μ (closedBall x r) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top hcb_ne_top
    have henn : μ B₀ ≤ (κ : ℝ≥0∞) * μ (closedBall x r) :=
      measure_ball_le_scalingConstantOf_mul_closedBall (μ := μ) hr hr₀ h_contained hr_scale
    have henn_toReal : (μ B₀).toReal ≤ ((κ : ℝ≥0∞) * μ (closedBall x r)).toReal :=
      ENNReal.toReal_mono hprod_ne_top henn
    have hB_toReal_pos : 0 < (μ B).toReal := ENNReal.toReal_pos hB_ne_zero hB_ne_top
    have hcb_ball : (μ (closedBall x r)).toReal / (μ B).toReal ≤ (δ : ℝ≥0) := by
      simpa [B, δ] using (measure_closedBall_div_measure_ball_le (μ := μ) x hr hr_scale2)
    calc
      (μ B₀).toReal / (μ B).toReal
          ≤ (((κ : ℝ≥0∞) * μ (closedBall x r)).toReal) / (μ B).toReal := by
              exact div_le_div_of_nonneg_right henn_toReal hB_toReal_pos.le
      _ = (κ : ℝ) * ((μ (closedBall x r)).toReal / (μ B).toReal) := by
            rw [ENNReal.toReal_mul]
            simp [mul_div_assoc]
      _ ≤ (κ : ℝ) * (δ : ℝ) := by
            have hκ_nonneg : 0 ≤ (κ : ℝ) := κ.coe_nonneg
            exact mul_le_mul_of_nonneg_left (by simpa using hcb_ball) hκ_nonneg
      _ = ((κ * δ : ℝ≥0) : ℝ) := by
            simp
  have hSubset :
      ⨍ y in B, |f y - f_B₀| ∂μ ≤ ((κ * δ : ℝ≥0) : ℝ) * ⨍ y in B₀, |f y - f_B₀| ∂μ := by
    -- Integrability of `y ↦ |f y - f_B₀|` on `B₀`.
    have hf_B₀ : IntegrableOn f B₀ μ :=
      hf_int.integrableOn_isCompact (isCompact_closedBall x₀ r₀) |>.mono_set ball_subset_closedBall
    have hsub : IntegrableOn (fun y => f y - f_B₀) B₀ μ := by
      simpa [IntegrableOn] using
        (hf_B₀.integrable.sub
          (integrableOn_const (μ := μ) (s := B₀) (C := f_B₀) (hs := hB₀_ne_top) (hC := by simp)).integrable)
    have hg_int : IntegrableOn (fun y => |f y - f_B₀|) B₀ μ := by
      simpa [← Real.norm_eq_abs] using hsub.norm

    simpa [B, B₀] using
      (setAverage_subset_le_mul (μ := μ) (s := B) (t := B₀) (f := fun y => |f y - f_B₀|)
        h_contained measurableSet_ball measurableSet_ball hB_ne_zero hB_ne_top hB₀_ne_top
        (fun y => abs_nonneg _) hg_int (C := ((κ * δ : ℝ≥0) : ℝ)) hratio)
  -- Step 3: BMO on `B₀`.
  have hbmo_B₀ : ⨍ y in B₀, |f y - f_B₀| ∂μ ≤ M := hbmo x₀ r₀ hr₀
  -- Combine.
  calc
    |f_B - f_B₀|
        ≤ ⨍ y in B, |f y - f_B₀| ∂μ := hJensen
    _ ≤ ((κ * δ : ℝ≥0) : ℝ) * ⨍ y in B₀, |f y - f_B₀| ∂μ := hSubset
    _ ≤ ((κ * δ : ℝ≥0) : ℝ) * M := by
          gcongr

/-- A “one-ball” John–Nirenberg step: on a subball `ball x r ⊆ ball x₀ r₀`,
large deviation from the *big* average forces a large deviation from the *small* average,
up to the telescoping constant; hence a Chebyshev bound on the subball.

This lemma is a reusable building block for John–Nirenberg / good-λ arguments. -/
theorem measure_subball_abs_sub_setAverage_gt_add_le {f : α → ℝ} (hf_int : LocallyIntegrable f μ)
    {M : ℝ} (hM : 0 < M)
    (hbmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in ball x r, |f y - ⨍ z in ball x r, f z ∂μ| ∂μ ≤ M)
    {x₀ : α} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {x : α} {r : ℝ} (hr : 0 < r)
    (h_contained : ball x r ⊆ ball x₀ r₀)
    (hr_scale : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (2 * r₀ / r))
    (hr_scale2 : r / 2 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 2)
    {t : ℝ} (ht : 0 < t) :
    μ {y ∈ ball x r |
        |f y - ⨍ z in ball x₀ r₀, f z ∂μ| >
          t + ((IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * r₀ / r) *
            IsUnifLocDoublingMeasure.scalingConstantOf μ 2 : ℝ≥0) : ℝ) * M}
      ≤ ENNReal.ofReal (M / t) * μ (ball x r) := by
  classical
  set B : Set α := ball x r
  set B₀ : Set α := ball x₀ r₀
  set fB : ℝ := ⨍ y in B, f y ∂μ
  set fB₀ : ℝ := ⨍ y in B₀, f y ∂μ
  set C : ℝ :=
    ((IsUnifLocDoublingMeasure.scalingConstantOf μ (2 * r₀ / r) *
        IsUnifLocDoublingMeasure.scalingConstantOf μ 2 : ℝ≥0) : ℝ)

  have hμB_ne_top : μ B ≠ ⊤ := (measure_ball_lt_top (μ := μ) (x := x) (r := r)).ne
  have hμB_ne_zero : μ B ≠ 0 := (measure_ball_pos (μ := μ) (x := x) (r := r) hr).ne'

  -- Telescoping control of the difference of averages.
  have htel :
      |fB - fB₀| ≤ C * M := by
    simpa [B, B₀, fB, fB₀, C] using
      (bmo_telescoping (μ := μ) (f := f) hf_int hM hbmo hr₀ hr h_contained hr_scale hr_scale2)

  -- If we are far above the big average, we are above the small average by at least `t`.
  have hsubset :
      {y ∈ B | |f y - fB₀| > t + C * M} ⊆ {y ∈ B | |f y - fB| > t} := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have htri : |f y - fB₀| ≤ |f y - fB| + |fB - fB₀| := by
      -- triangle inequality for subtraction
      -- |(f y - fB) + (fB - fB₀)| ≤ |f y - fB| + |fB - fB₀|
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (abs_add_le (f y - fB) (fB - fB₀))
    have hle : |f y - fB₀| ≤ |f y - fB| + C * M := by
      exact htri.trans (add_le_add_left htel _)
    have : t + C * M < |f y - fB| + C * M := lt_of_lt_of_le hy.2 hle
    -- cancel `C*M`
    have : t < |f y - fB| := by linarith
    simpa [gt_iff_lt] using this

  -- Chebyshev on the subball with respect to its own average.
  have hcheb :
      μ {y ∈ B | |f y - fB| > t} ≤ ENNReal.ofReal (M / t) * μ B := by
    -- Convert the BMO bound on the average to an integral bound.
    have hfB_int : IntegrableOn f B μ :=
      hf_int.integrableOn_isCompact (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall
    have hconst : IntegrableOn (fun _ : α => fB) B μ :=
      integrableOn_const (μ := μ) (s := B) (C := fB) (hs := hμB_ne_top) (hC := by simp)
    have hsub : IntegrableOn (fun y => f y - fB) B μ := hfB_int.sub hconst
    have habs : IntegrableOn (fun y => |f y - fB|) B μ := by
      simpa [← Real.norm_eq_abs] using hsub.norm
    have havg_le : (⨍ y in B, |f y - fB| ∂μ) ≤ M := by
      simpa [B, fB] using hbmo x r hr
    have hint_le : ∫ y in B, |f y - fB| ∂μ ≤ μ.real B * M := by
      have hsmul :
          μ.real B • (⨍ y in B, |f y - fB| ∂μ) = ∫ y in B, |f y - fB| ∂μ :=
        measure_smul_setAverage (μ := μ) (f := fun y => |f y - fB|) (s := B) hμB_ne_top
      have hmul : μ.real B * (⨍ y in B, |f y - fB| ∂μ) ≤ μ.real B * M :=
        mul_le_mul_of_nonneg_left havg_le ENNReal.toReal_nonneg
      have hsmul' : μ.real B * (⨍ y in B, |f y - fB| ∂μ) = ∫ y in B, |f y - fB| ∂μ := by
        simpa [smul_eq_mul] using hsmul
      simpa [hsmul'] using hmul

    -- Markov inequality on `μ.restrict B`.
    have habs' : Integrable (fun y => |f y - fB|) (μ.restrict B) := by
      simpa [IntegrableOn] using habs
    have hnonneg : 0 ≤ᵐ[μ.restrict B] fun y => |f y - fB| :=
      Eventually.of_forall (fun _ => abs_nonneg _)
    have hmarkov :
        t * ((μ.restrict B) {y | t ≤ |f y - fB|}).toReal ≤ ∫ y, |f y - fB| ∂(μ.restrict B) :=
      mul_meas_ge_le_integral_of_nonneg (μ := μ.restrict B) hnonneg habs' t
    have hmarkov' :
        t * (μ {y ∈ B | t ≤ |f y - fB|}).toReal ≤ ∫ y in B, |f y - fB| ∂μ := by
      -- rewrite the set and integral from the restricted measure form
      have hset :
          (μ.restrict B) {y | t ≤ |f y - fB|} = μ {y ∈ B | t ≤ |f y - fB|} := by
        have hnull : NullMeasurableSet {y | t ≤ |f y - fB|} (μ.restrict B) := by
          have haemeas : AEMeasurable (fun y => |f y - fB|) (μ.restrict B) := habs'.aemeasurable
          simpa [Set.preimage, Set.mem_setOf_eq] using
            (haemeas.nullMeasurableSet_preimage
              (isClosed_Ici.measurableSet : MeasurableSet (Set.Ici t)))
        have hrestrict :
            (μ.restrict B) {y | t ≤ |f y - fB|} = μ ({y | t ≤ |f y - fB|} ∩ B) :=
          Measure.restrict_apply₀ (μ := μ) (s := B) (t := {y | t ≤ |f y - fB|}) hnull
        simpa [Set.inter_comm, Set.setOf_and, and_left_comm, and_assoc, and_comm] using hrestrict
      have hint :
          (∫ y, |f y - fB| ∂(μ.restrict B)) = ∫ y in B, |f y - fB| ∂μ := by
        simp
      simpa [hset, hint] using hmarkov

    have htoReal :
        (μ {y ∈ B | t ≤ |f y - fB|}).toReal ≤ (μ.real B * M) / t := by
      have ht' : 0 < t := ht
      have : (μ {y ∈ B | t ≤ |f y - fB|}).toReal ≤ (∫ y in B, |f y - fB| ∂μ) / t := by
        exact (le_div_iff₀ ht').2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov')
      have : (μ {y ∈ B | t ≤ |f y - fB|}).toReal ≤ (μ.real B * M) / t := by
        exact this.trans (div_le_div_of_nonneg_right hint_le (by linarith))
      exact this

    have hμS_ne_top : μ {y ∈ B | t ≤ |f y - fB|} ≠ ⊤ :=
      measure_ne_top_of_subset (fun _ hy => hy.1) hμB_ne_top
    have hμrhs_ne_top : ENNReal.ofReal ((μ.real B * M) / t) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hle :
        μ {y ∈ B | t ≤ |f y - fB|} ≤ ENNReal.ofReal ((μ.real B * M) / t) :=
      (ENNReal.toReal_le_toReal hμS_ne_top hμrhs_ne_top).1 (by
        have hnonneg : 0 ≤ (μ.real B * M) / t := by
          have : 0 ≤ μ.real B * M := mul_nonneg ENNReal.toReal_nonneg (le_of_lt hM)
          exact div_nonneg this (le_of_lt ht)
        simpa [ENNReal.toReal_ofReal, hnonneg] using htoReal)

    have hμreal : ENNReal.ofReal (μ.real B) = μ B := by
      simp [Measure.real, hμB_ne_top]
    have hfac_nonneg : 0 ≤ M / t := by
      exact div_nonneg (le_of_lt hM) (le_of_lt ht)
    have hrhs :
        ENNReal.ofReal ((μ.real B * M) / t) = ENNReal.ofReal (M / t) * μ B := by
      have : (μ.real B * M) / t = μ.real B * (M / t) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      -- move factors into ENNReal and use `μ.real` = `toReal`
      calc
        ENNReal.ofReal ((μ.real B * M) / t)
            = ENNReal.ofReal (μ.real B * (M / t)) := by simp [this]
        _ = ENNReal.ofReal (μ.real B) * ENNReal.ofReal (M / t) := by
              have hμreal_nonneg : 0 ≤ μ.real B := ENNReal.toReal_nonneg
              simpa [mul_comm, mul_left_comm, mul_assoc] using (ENNReal.ofReal_mul (p := μ.real B) (q := M / t) hμreal_nonneg)
        _ = ENNReal.ofReal (M / t) * μ B := by
              simp [mul_comm, hμreal]

    -- Pass from `t ≤ ...` to `... > t`, and rewrite the RHS into the desired form.
    have hmono : μ {y ∈ B | |f y - fB| > t} ≤ μ {y ∈ B | t ≤ |f y - fB|} := by
      refine measure_mono (fun y hy => ?_)
      exact ⟨hy.1, hy.2.le⟩
    exact (hmono.trans (hle.trans_eq hrhs))

  -- Put everything together.
  have hset_eq :
      {y ∈ B | |f y - fB₀| >
          t + C * M} ⊆ {y ∈ B | |f y - fB| > t} :=
    hsubset
  -- Ensure we use the same shape as the statement (with `C*M`).
  have : μ {y ∈ B | |f y - fB₀| > t + C * M} ≤ ENNReal.ofReal (M / t) * μ B :=
    (measure_mono hset_eq) |>.trans hcheb
  simpa [B, B₀, fB, fB₀, C, C, gt_iff_lt] using this

/-!
### Global-doubling variant (no `scalingScaleOf` side conditions)

If the measure is globally doubling in the sense of `MeasureTheory.Measure.IsDoubling` (from the
Carleson library), then we can bound the needed measure ratios at *all* radii, hence we can
package the same “one-ball” step without any `scalingScaleOf` assumptions.
-/

theorem measure_subball_abs_sub_setAverage_gt_add_le_isDoubling
    {A : ℝ≥0} [μ.IsDoubling A] [NeZero μ]
    {f : α → ℝ} (hf_int : LocallyIntegrable f μ)
    {M : ℝ} (hM : 0 < M)
    (hbmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in ball x r, |f y - ⨍ z in ball x r, f z ∂μ| ∂μ ≤ M)
    {x₀ : α} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {x : α} {r : ℝ} (hr : 0 < r)
    (h_contained : ball x r ⊆ ball x₀ r₀)
    {t : ℝ} (ht : 0 < t) :
    μ {y ∈ ball x r |
        |f y - ⨍ z in ball x₀ r₀, f z ∂μ| >
          t + ((As A (2 * r₀ / r) : ℝ≥0) : ℝ) * M}
      ≤ ENNReal.ofReal (M / t) * μ (ball x r) := by
  classical
  -- We will reuse the local-doubling proof pattern, but with a global measure-ratio bound
  -- coming from `μ.IsDoubling A`.
  haveI : μ.IsOpenPosMeasure := MeasureTheory.isOpenPosMeasure_of_isDoubling (μ := μ)

  set B : Set α := ball x r
  set B₀ : Set α := ball x₀ r₀
  set fB : ℝ := ⨍ y in B, f y ∂μ
  set fB₀ : ℝ := ⨍ y in B₀, f y ∂μ
  set C : ℝ := ((As A (2 * r₀ / r) : ℝ≥0) : ℝ)

  have hμB_ne_top : μ B ≠ ⊤ := (measure_ball_lt_top (μ := μ) (x := x) (r := r)).ne
  have hμB_ne_zero : μ B ≠ 0 := (measure_ball_pos (μ := μ) (x := x) (r := r) hr).ne'
  have hμB₀_ne_top : μ B₀ ≠ ⊤ := (measure_ball_lt_top (μ := μ) (x := x₀) (r := r₀)).ne

  -- A global ratio bound: `μ(B₀) / μ(B) ≤ As A (2*r₀/r)`.
  have hratio : (μ B₀).toReal / (μ B).toReal ≤ C := by
    have hB_toReal_pos : 0 < (μ B).toReal := ENNReal.toReal_pos hμB_ne_zero hμB_ne_top
    -- `B₀ ⊆ ball x (2*r₀)` from containment, then use global doubling at scale `2*r₀/r`.
    have hx_in : x ∈ ball x₀ r₀ := h_contained (mem_ball_self hr)
    have hdist : dist x x₀ < r₀ := mem_ball.mp hx_in
    have hcontain : B₀ ⊆ ball x (2 * r₀) := by
      intro y hy
      have hy' : dist y x₀ < r₀ := by simpa [B₀, mem_ball] using hy
      have : dist y x ≤ dist y x₀ + dist x₀ x := dist_triangle y x₀ x
      have hx0 : dist x₀ x < r₀ := by simpa [dist_comm] using hdist
      have : dist y x < r₀ + r₀ := by linarith
      have : dist y x < 2 * r₀ := by linarith
      simpa [B, mem_ball] using this
    have hμB_pos : μ B ≠ 0 := hμB_ne_zero
    have hμB₀_le : μ B₀ ≤ μ (ball x (2 * r₀)) := by
      exact measure_mono hcontain
    have hμball_le :
        μ (ball x (2 * r₀)) ≤ (As A (2 * r₀ / r) : ℝ≥0∞) * μ B := by
      -- apply `measure_ball_le_same` with `s = (2*r₀)/r`
      have hs : 0 < (2 * r₀ / r) := by positivity
      -- `2*r₀ ≤ (2*r₀/r) * r`
      have : (2 * r₀ : ℝ) ≤ (2 * r₀ / r) * r := by
        have : (2 * r₀ / r) * r = 2 * r₀ := by field_simp [hr.ne']
        simp [this]
      -- `measure_ball_le_same` expects `r' ≤ s*r`
      simpa [B] using (MeasureTheory.measure_ball_le_same (μ := μ) (A := A) (x := x) (r := r)
        (r' := 2 * r₀) hs this)
    have hμball_ne_top : μ (ball x (2 * r₀)) ≠ ⊤ :=
      (hμball_le.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (hμB_ne_top.lt_top))).ne

    have htoReal_le : (μ B₀).toReal ≤ ((As A (2 * r₀ / r) : ℝ≥0∞) * μ B).toReal := by
      refine (ENNReal.toReal_mono ?_ (hμB₀_le.trans hμball_le))
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top hμB_ne_top
    have htoReal_mul :
        ((As A (2 * r₀ / r) : ℝ≥0∞) * μ B).toReal
          = (As A (2 * r₀ / r) : ℝ) * (μ B).toReal := by
      simp [ENNReal.toReal_mul]
    -- finish
    have htoReal_le' : (μ B₀).toReal ≤ (As A (2 * r₀ / r) : ℝ) * (μ B).toReal := by
      simpa [htoReal_mul] using htoReal_le
    -- divide by μ(B).toReal
    have : (μ B₀).toReal / (μ B).toReal ≤ (As A (2 * r₀ / r) : ℝ) := by
      exact (div_le_iff₀ hB_toReal_pos).2 (by simpa [mul_assoc, mul_comm, mul_left_comm] using htoReal_le')
    simpa [C] using this

  -- Telescoping control of the difference of averages, using `setAverage_subset_le_mul`.
  have htel :
      |fB - fB₀| ≤ C * M := by
    -- Jensen on `B` relative to constant `fB₀`, then compare averages by the measure ratio bound,
    -- then apply BMO on `B₀`.
    have hB_pos : 0 < μ B := measure_ball_pos μ x hr
    have hB₀_ne_zero : μ B₀ ≠ 0 := (measure_ball_pos (μ := μ) (x := x₀) (r := r₀) hr₀).ne'
    have hB_ne_zero : μ B ≠ 0 := hB_pos.ne'

    have hf_B : IntegrableOn f B μ :=
      hf_int.integrableOn_isCompact (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall
    have hJensen : |fB - fB₀| ≤ ⨍ y in B, |f y - fB₀| ∂μ := by
      rw [← setAverage_sub_const (μ := μ) (s := B) measurableSet_ball hf_B fB₀ hB_ne_zero hμB_ne_top]
      have hf_sub : IntegrableOn (fun y => f y - fB₀) B μ := by
        have hconst : IntegrableOn (fun _ : α => fB₀) B μ :=
          integrableOn_const (μ := μ) (s := B) (C := fB₀) (hs := hμB_ne_top) (hC := by simp)
        exact hf_B.sub hconst
      exact abs_setAverage_le_setAverage_abs (μ := μ) (s := B) measurableSet_ball hf_sub hB_ne_zero hμB_ne_top

    have hf_B₀ : IntegrableOn f B₀ μ :=
      hf_int.integrableOn_isCompact (isCompact_closedBall x₀ r₀) |>.mono_set ball_subset_closedBall
    have hsub : IntegrableOn (fun y => f y - fB₀) B₀ μ := by
      have hconst : IntegrableOn (fun _ : α => fB₀) B₀ μ :=
        integrableOn_const (μ := μ) (s := B₀) (C := fB₀) (hs := hμB₀_ne_top) (hC := by simp)
      exact hf_B₀.sub hconst
    have hg_int : IntegrableOn (fun y => |f y - fB₀|) B₀ μ := by
      simpa [← Real.norm_eq_abs] using hsub.norm

    have havg_subset :
        ⨍ y in B, |f y - fB₀| ∂μ ≤ C * ⨍ y in B₀, |f y - fB₀| ∂μ := by
      simpa [B, B₀] using
        (setAverage_subset_le_mul (μ := μ) (s := B) (t := B₀) (f := fun y => |f y - fB₀|)
          h_contained measurableSet_ball measurableSet_ball hB_ne_zero hμB_ne_top hμB₀_ne_top
          (fun y => abs_nonneg _) hg_int (C := C) hratio)

    have hbmo_B₀ : ⨍ y in B₀, |f y - fB₀| ∂μ ≤ M := by
      simpa [B₀, fB₀] using hbmo x₀ r₀ hr₀

    calc
      |fB - fB₀| ≤ ⨍ y in B, |f y - fB₀| ∂μ := hJensen
      _ ≤ C * ⨍ y in B₀, |f y - fB₀| ∂μ := havg_subset
      _ ≤ C * M := by gcongr

  -- If we are far above the big average, we are above the small average by at least `t`.
  have hsubset :
      {y ∈ B | |f y - fB₀| > t + C * M} ⊆ {y ∈ B | |f y - fB| > t} := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    have htri : |f y - fB₀| ≤ |f y - fB| + |fB - fB₀| := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (abs_add_le (f y - fB) (fB - fB₀))
    have hle : |f y - fB₀| ≤ |f y - fB| + C * M := by
      exact htri.trans (add_le_add_left htel _)
    have : t + C * M < |f y - fB| + C * M := lt_of_lt_of_le hy.2 hle
    have : t < |f y - fB| := by linarith
    simpa [gt_iff_lt] using this

  -- Chebyshev on the subball with respect to its own average.
  have hcheb :
      μ {y ∈ B | |f y - fB| > t} ≤ ENNReal.ofReal (M / t) * μ B := by
    -- Same Markov/Chebyshev argument as in `johnNirenberg_iteration`.
    have hfB_int : IntegrableOn f B μ :=
      hf_int.integrableOn_isCompact (isCompact_closedBall x r) |>.mono_set ball_subset_closedBall
    have hconst : IntegrableOn (fun _ : α => fB) B μ :=
      integrableOn_const (μ := μ) (s := B) (C := fB) (hs := hμB_ne_top) (hC := by simp)
    have hsub : IntegrableOn (fun y => f y - fB) B μ := hfB_int.sub hconst
    have habs : IntegrableOn (fun y => |f y - fB|) B μ := by
      simpa [← Real.norm_eq_abs] using hsub.norm
    have havg_le : (⨍ y in B, |f y - fB| ∂μ) ≤ M := by
      simpa [B, fB] using hbmo x r hr
    -- Markov inequality (real-valued)
    have hμB_ne_top' : μ B ≠ ⊤ := hμB_ne_top
    have hIntegral_le : ∫ y in B, |f y - fB| ∂μ ≤ μ.real B * M := by
      have hsmul :
          μ.real B • (⨍ y in B, |f y - fB| ∂μ) = ∫ y in B, |f y - fB| ∂μ :=
        measure_smul_setAverage (μ := μ) (f := fun y => |f y - fB|) (s := B) hμB_ne_top'
      have hmul : μ.real B * (⨍ y in B, |f y - fB| ∂μ) ≤ μ.real B * M :=
        mul_le_mul_of_nonneg_left havg_le ENNReal.toReal_nonneg
      have hsmul' : μ.real B * (⨍ y in B, |f y - fB| ∂μ) = ∫ y in B, |f y - fB| ∂μ := by
        simpa [smul_eq_mul] using hsmul
      simpa [hsmul'] using hmul

    have habs' : Integrable (fun y => |f y - fB|) (μ.restrict B) := by
      simpa [IntegrableOn] using habs
    have hnonneg : 0 ≤ᵐ[μ.restrict B] fun y => |f y - fB| :=
      Eventually.of_forall (fun _ => abs_nonneg _)
    have hmarkov :
        t * (μ {y ∈ B | t ≤ |f y - fB|}).toReal ≤ ∫ y in B, |f y - fB| ∂μ := by
      -- Use the Markov lemma on `μ.restrict B` and rewrite.
      have hmarkov0 :
          t * ((μ.restrict B) {y | t ≤ |f y - fB|}).toReal ≤ ∫ y, |f y - fB| ∂(μ.restrict B) :=
        mul_meas_ge_le_integral_of_nonneg (μ := μ.restrict B) hnonneg habs' t
      have hset :
          (μ.restrict B) {y | t ≤ |f y - fB|} = μ {y ∈ B | t ≤ |f y - fB|} := by
        have hnull : NullMeasurableSet {y | t ≤ |f y - fB|} (μ.restrict B) := by
          have haemeas : AEMeasurable (fun y => |f y - fB|) (μ.restrict B) := habs'.aemeasurable
          simpa [Set.preimage, Set.mem_setOf_eq] using
            (haemeas.nullMeasurableSet_preimage
              (isClosed_Ici.measurableSet : MeasurableSet (Set.Ici t)))
        have hrestrict :
            (μ.restrict B) {y | t ≤ |f y - fB|} = μ ({y | t ≤ |f y - fB|} ∩ B) :=
          Measure.restrict_apply₀ (μ := μ) (s := B) (t := {y | t ≤ |f y - fB|}) hnull
        simpa [Set.inter_comm, Set.setOf_and, and_left_comm, and_assoc, and_comm] using hrestrict
      have hint :
          (∫ y, |f y - fB| ∂(μ.restrict B)) = ∫ y in B, |f y - fB| ∂μ := by simp
      simpa [hset, hint] using hmarkov0

    have htoReal :
        (μ {y ∈ B | t ≤ |f y - fB|}).toReal ≤ (μ.real B * M) / t := by
      have : (μ {y ∈ B | t ≤ |f y - fB|}).toReal ≤ (∫ y in B, |f y - fB| ∂μ) / t := by
        exact (le_div_iff₀ ht).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov)
      exact this.trans (div_le_div_of_nonneg_right hIntegral_le (by linarith [hM, ht]))

    have hμS_ne_top : μ {y ∈ B | t ≤ |f y - fB|} ≠ ⊤ :=
      measure_ne_top_of_subset (fun _ hy => hy.1) hμB_ne_top
    have hμrhs_ne_top : ENNReal.ofReal ((μ.real B * M) / t) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hle :
        μ {y ∈ B | t ≤ |f y - fB|} ≤ ENNReal.ofReal ((μ.real B * M) / t) :=
      (ENNReal.toReal_le_toReal hμS_ne_top hμrhs_ne_top).1 (by
        have hnonneg : 0 ≤ (μ.real B * M) / t := by
          have : 0 ≤ μ.real B * M := mul_nonneg ENNReal.toReal_nonneg (le_of_lt hM)
          exact div_nonneg this ht.le
        simpa [ENNReal.toReal_ofReal, hnonneg] using htoReal)

    have hμreal : ENNReal.ofReal (μ.real B) = μ B := by
      simp [Measure.real, hμB_ne_top]
    have hrhs :
        ENNReal.ofReal ((μ.real B * M) / t) = ENNReal.ofReal (M / t) * μ B := by
      have : (μ.real B * M) / t = μ.real B * (M / t) := by
        simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      calc
        ENNReal.ofReal ((μ.real B * M) / t)
            = ENNReal.ofReal (μ.real B * (M / t)) := by simp [this]
        _ = ENNReal.ofReal (μ.real B) * ENNReal.ofReal (M / t) := by
              have hμreal_nonneg : 0 ≤ μ.real B := ENNReal.toReal_nonneg
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                (ENNReal.ofReal_mul (p := μ.real B) (q := M / t) hμreal_nonneg)
        _ = ENNReal.ofReal (M / t) * μ B := by simp [mul_comm, hμreal]

    have hmono : μ {y ∈ B | |f y - fB| > t} ≤ μ {y ∈ B | t ≤ |f y - fB|} := by
      refine measure_mono (fun y hy => ?_)
      exact ⟨hy.1, hy.2.le⟩
    exact (hmono.trans (hle.trans_eq hrhs))

  have : μ {y ∈ B | |f y - fB₀| > t + C * M} ≤ ENNReal.ofReal (M / t) * μ B :=
    (measure_mono hsubset) |>.trans hcheb
  simpa [B, B₀, fB, fB₀, C, gt_iff_lt] using this

end BMO

section CarlesonCZ

/-!
### CZ decomposition (Carleson)

We record one convenience lemma packaging the pointwise decomposition in the **general case**
(`GeneralCase f α`) from the Carleson development.
-/

variable {X : Type*} {a : ℕ} [MetricSpace X] [DoublingMeasure X (defaultA a : ℕ)]
variable {f : X → ℂ} {α : ℝ≥0∞}

theorem czApproximation_add_tsum_czRemainder' (hX : GeneralCase f α) (x : X) :
    czApproximation f α x + (∑' i, czRemainder' hX i x) = f x := by
  calc
    czApproximation f α x + (∑' i, czRemainder' hX i x)
        = czApproximation f α x + czRemainder f α x := by
            congr 1
            simpa using (tsum_czRemainder' (f := f) (α := α) hX x)
    _ = f x := czApproximation_add_czRemainder (f := f) (α := α) (x := x)

end CarlesonCZ

end MeasureTheory
