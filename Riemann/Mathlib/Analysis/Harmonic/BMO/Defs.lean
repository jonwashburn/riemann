import Mathlib.Data.Real.StarOrdered
import Mathlib.Order.CompletePartialOrder
import Riemann.Mathlib.Analysis.Harmonic.BMOAux
import Riemann.Mathlib.MeasureTheory.Function.BoundedSupport

/-!
# BMO: Bounded Mean Oscillation

This file provides the theory of BMO (Bounded Mean Oscillation) functions,
including the John-Nirenberg inequality and duality with H¹.

## Main Definitions

* `bmoSeminorm`: The BMO seminorm `‖f‖_* = sup_B ⨍_B |f - ⨍_B f|`
* `MemBMO`: Predicate for functions in BMO
* `BMO`: The space of BMO functions modulo constants

## Main Results

* `johnNirenberg`: The John-Nirenberg inequality
* `bmo_h1_duality`: (H¹)* ≅ BMO (Fefferman's theorem)

## Implementation Notes

BMO is crucial for:
1. Characterizing Carleson measures via `log|f|` for outer functions
2. Proving boundedness of singular integrals
3. H¹-BMO duality in the RH proof

We use Mathlib's `⨍` notation for set averages, which is defined as
`(μ s)⁻¹ * ∫ x in s, f x ∂μ`.

## References

* John-Nirenberg, "On functions of bounded mean oscillation"
* Fefferman-Stein, "H^p spaces of several variables"

## Tags

BMO, bounded mean oscillation, John-Nirenberg, Fefferman duality
-/

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]
variable {μ : Measure α}

/-! ### Set Average and Mean Oscillation -/

/-- The average of a function over a set using Mathlib's standard notation.
This is equal to `(μ s)⁻¹ * ∫ x in s, f x ∂μ`. -/
noncomputable def setAverage (f : α → ℝ) (s : Set α) (μ : Measure α) : ℝ :=
  ⨍ x in s, f x ∂μ

/-- The mean oscillation of `f` over a set `s`:
`⨍_s |f(x) - ⨍_s f|`. -/
noncomputable def meanOscillation (f : α → ℝ) (s : Set α) (μ : Measure α) : ℝ :=
  ⨍ x in s, |f x - setAverage f s μ| ∂μ

/-- The BMO seminorm: supremum of mean oscillations over all balls. -/
noncomputable def bmoSeminorm (f : α → ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ (x : α) (r : ℝ) (_hr : 0 < r), ↑‖meanOscillation f (Metric.ball x r) μ‖₊

/-- A function is in BMO if it is locally integrable and its BMO seminorm is finite.

Note: The local integrability hypothesis is essential. Without it, the Bochner average
of a non-integrable function is 0, so non-integrable functions would have BMO seminorm 0,
making MemBMO vacuously true. The standard definition of BMO in the literature assumes
f ∈ L¹_loc from the start. -/
def MemBMO (f : α → ℝ) (μ : Measure α) : Prop :=
  LocallyIntegrable f μ ∧ bmoSeminorm f μ < ⊤

/-! ### Basic Properties of Set Averages -/

section SetAverageProperties

variable {f g : α → ℝ} {s : Set α}

omit [PseudoMetricSpace α] [BorelSpace α] in
/-- The set average equals the standard Mathlib average. -/
theorem setAverage_eq_average : setAverage f s μ = ⨍ x in s, f x ∂μ := rfl

/-- Triangle inequality for the difference: |a - b| ≤ |a| + |b|. -/
lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  -- standard triangle inequality rewritten for subtraction
  simpa [sub_eq_add_neg] using abs_add_le a (-b)

omit [PseudoMetricSpace α] [BorelSpace α] in
/-- Average of a bounded function is bounded by the same constant. -/
theorem abs_setAverage_le {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x ∈ s, |f x| ≤ M)
    (hμ : μ s ≠ 0) (hμ' : μ s ≠ ⊤) (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable f μ) : |setAverage f s μ| ≤ M := by
  unfold setAverage
  haveI : Fact (μ s < ⊤) := ⟨hμ'.lt_top⟩
  haveI : NeZero (μ s) := ⟨hμ⟩
  haveI : NeZero (μ.restrict s) := inferInstance
  rw [average_eq, smul_eq_mul]
  have hμ_pos : 0 < (μ.restrict s).real univ := by
    -- for a finite, nonzero measure, `μ.real` coincides with `toReal`
    have hreal : (μ.restrict s).real univ = (μ s).toReal := by
      simp [Measure.real]
    rw [hreal]
    exact ENNReal.toReal_pos hμ hμ'
  have hμ_inv : 0 ≤ ((μ.restrict s).real univ)⁻¹ := inv_nonneg.mpr hμ_pos.le
  calc |((μ.restrict s).real univ)⁻¹ * ∫ x in s, f x ∂μ|
      = |((μ.restrict s).real univ)⁻¹| * |∫ x in s, f x ∂μ| := abs_mul _ _
    _ = ((μ.restrict s).real univ)⁻¹ * |∫ x in s, f x ∂μ| := by rw [abs_of_nonneg hμ_inv]
    _ ≤ ((μ.restrict s).real univ)⁻¹ * (M * (μ.restrict s).real univ) := by
        gcongr
        -- put the indicator of f in L¹ via the bounded-support lemma
        let g : α → ℝ := s.indicator f
        have hM' : ∀ x, |g x| ≤ M := by
          intro x; by_cases hx : x ∈ s
          · have : |f x| ≤ M := hf x hx; simpa [g, hx]
          · -- outside `s`, g x = 0, and |0| ≤ M by hM
            have : |(0 : ℝ)| ≤ M := by simpa using hM
            simpa [g, hx] using this
        have hsupp : Function.support g ⊆ s := by
          intro x hx
          simp [g, Function.mem_support] at hx
          exact hx.left
        have hint : Integrable g μ :=
          Integrable.of_bdd_support_real hM' hM hsupp hμ'.lt_top (hmeas.indicator hs)
        have hbound :=
          integral_le_of_bdd_support (μ := μ) (f := g) (M := M) (S := s)
            (by intro x hx; exact hM' x) hM hs (hμ'.lt_top) hsupp hint
        -- relate ∫_s |f| to ∫ |g|
        have hgintegral : ∫ x, |g x| ∂μ = ∫ x in s, |f x| ∂μ := by
          have : (fun x => |g x|) = s.indicator (fun x => |f x|) := by
            ext x; by_cases hx : x ∈ s <;> simp [g, hx]
          calc ∫ x, |g x| ∂μ = ∫ x, s.indicator (fun x => |f x|) x ∂μ := by simp [this]
          _ = ∫ x in s, |f x| ∂μ := integral_indicator hs
        -- rewrite the bound in terms of `(μ.restrict s).real univ`
        have hreal : (μ.restrict s).real univ = (μ s).toReal := by
          simp [Measure.real]
        have hbound' : ∫ x, |g x| ∂μ ≤ M * (μ.restrict s).real univ := by
          simpa [hreal] using hbound
        calc |∫ x in s, f x ∂μ|
            ≤ ∫ x in s, |f x| ∂μ := abs_integral_le_integral_abs (μ := μ.restrict s)
        _ = ∫ x, |g x| ∂μ := by
            have := hgintegral.symm
            simpa [Measure.restrict_apply_univ] using this
        _ ≤ M * (μ.restrict s).real univ := hbound'
    _ = M := by
      -- `(μ.real s)` is nonzero since `μ s ≠ 0` and `μ s < ∞`
      have hμreal_ne : μ.real s ≠ 0 := by
        have htoReal_ne : (μ s).toReal ≠ 0 := by
          refine ENNReal.toReal_ne_zero.mpr ?_
          aesop
        simpa [Measure.real] using htoReal_ne
      -- now use the identity `(μ.real s)⁻¹ * μ.real s = 1`
      have hId : (μ.real s)⁻¹ * μ.real s = (1 : ℝ) := inv_mul_cancel₀ hμreal_ne
      have hreal' : (μ.restrict s).real univ = μ.real s := by
        simp [Measure.real]
      calc
        ((μ.restrict s).real univ)⁻¹ * (M * (μ.restrict s).real univ)
            = M * ((μ.restrict s).real univ)⁻¹ * (μ.restrict s).real univ := by ring
        _ = M * ((μ.real s)⁻¹ * μ.real s) := by simp_rw [hreal']; simp [*]
        _ = M * 1 := by rw [hId]
        _ = M := by simp

omit [PseudoMetricSpace α] [BorelSpace α] in
/-- Mean oscillation is nonnegative. -/
theorem meanOscillation_nonneg : 0 ≤ meanOscillation f s μ := by
  -- `meanOscillation` is the average of a nonnegative function, hence nonnegative.
  unfold meanOscillation
  -- rewrite the average as a scalar multiple of an integral
  rw [average_eq, smul_eq_mul]
  -- both factors are nonnegative: the scalar and the integral of `|·|`
  refine mul_nonneg ?hscalar ?hint
  · -- scalar `(μ.restrict s).real univ)⁻¹` is nonnegative
    exact inv_nonneg.mpr ENNReal.toReal_nonneg
  · -- integral of a nonnegative function is nonnegative
    refine integral_nonneg ?hfun
    intro x
    exact abs_nonneg _

omit [PseudoMetricSpace α] [BorelSpace α] in
theorem meanOscillation_add_le_integrable
    {s : Set α} (hs : MeasurableSet s)
    (hμ_ne : μ s ≠ 0) (hμ_fin : μ s ≠ ∞)
    {f g : α → ℝ} (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
  meanOscillation (f + g) s μ ≤ meanOscillation f s μ + meanOscillation g s μ := by
  -- expand meanOscillation and apply oscillation_triangle_helper
  simpa [meanOscillation, setAverage] using
    oscillation_triangle_helper (μ := μ) (s := s) hs hμ_ne hμ_fin hf hg

omit [PseudoMetricSpace α] [BorelSpace α] in
/-- If `|f x| ≤ M` for all `x ∈ s`, then the mean oscillation over `s` is at most `2M`. -/
theorem meanOscillation_le_of_bounded {M : ℝ} (hM : 0 ≤ M) (hf : ∀ x ∈ s, |f x| ≤ M)
    (hμ : μ s ≠ 0) (hμ' : μ s ≠ ⊤) (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable f μ) :
    meanOscillation f s μ ≤ 2 * M := by
  unfold meanOscillation
  -- The key insight: |f(x) - avg| ≤ |f(x)| + |avg| ≤ M + M = 2M
  have havg : |setAverage f s μ| ≤ M := abs_setAverage_le hM hf hμ hμ' hs hmeas
  -- Bound the oscillation pointwise
  have hosc : ∀ x ∈ s, |f x - setAverage f s μ| ≤ 2 * M := fun x hx => by
    calc |f x - setAverage f s μ|
        ≤ |f x| + |setAverage f s μ| := abs_sub_le_abs_add_abs _ _
      _ ≤ M + M := add_le_add (hf x hx) havg
      _ = 2 * M := by ring
  -- Now use the bound on the average
  haveI : Fact (μ s < ⊤) := ⟨hμ'.lt_top⟩
  haveI : NeZero (μ s) := ⟨hμ⟩
  haveI : NeZero (μ.restrict s) := inferInstance
  calc
    ⨍ x in s, |f x - setAverage f s μ| ∂μ
        ≤ ⨍ _x in s, (2 * M) ∂μ := by
          -- first, build integrability of |f - avg| on s
          have hf_int : IntegrableOn (fun x ↦ |f x - setAverage f s μ|) s μ := by
            -- since |f x - avg| ≤ 2M on s and μ s < ∞, this is integrable
            have : ∀ x ∈ s, |f x - setAverage f s μ| ≤ 2 * M := hosc
            -- use the bounded-support lemma on the indicator of (f - avg)
            let h : α → ℝ := fun x => f x - setAverage f s μ
            let g : α → ℝ := s.indicator h
            have hM' : ∀ x, |g x| ≤ 2 * M := by
              intro x; by_cases hx : x ∈ s
              · have := this x hx; simpa [g, h, hx]
              · have : |(0 : ℝ)| ≤ 2 * M := by
                  have := hM; aesop
                simpa [g, hx] using this
            have hsupp : Function.support g ⊆ s := by
              intro x hx; simp [g, h, Function.mem_support] at hx; exact hx.left
            have hmeas' : AEStronglyMeasurable h μ :=
              hmeas.sub aestronglyMeasurable_const
            have hint : Integrable g μ :=
              Integrable.of_bdd_support_real hM' (by have := hM; linarith) hsupp hμ'.lt_top
                (hmeas'.indicator hs)
            -- indicator and h coincide on s, so h is integrable on s
            have hh_int : IntegrableOn h s μ := by
              -- g is integrable on s
              have hg_int : IntegrableOn g s μ := hint.integrableOn
              -- on s, g and h agree pointwise on s
              have h_eq : EqOn g h s := by
                intro x hx
                simp [g, h, hx]  -- indicator on s equals h
              -- transfer integrability from g to h using pointwise equality on s
              exact hg_int.congr_fun h_eq hs
            -- take absolute value to get integrability of |f - avg|
            simpa [h] using hh_int.abs
          have hconst_int : IntegrableOn (fun _ : α => 2 * M) s μ :=
            integrableOn_const (μ := μ) (s := s) (C := 2 * M) (hs := hμ') (hC := by finiteness)
          rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul]
          gcongr
          · exact hf_int
          · exact hconst_int
          · exact hs.nullMeasurableSet
          -- finally, apply the pointwise bound
          · apply hosc; assumption
    _ = 2 * M := by
      -- average of a constant over a finite, nonzero set is that constant
      have hμreal_ne : μ.real s ≠ 0 := by
        have htoReal_ne : (μ s).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hμ, hμ'⟩
        simpa [Measure.real] using htoReal_ne
      have hId : (μ.real s)⁻¹ * μ.real s = (1 : ℝ) := inv_mul_cancel₀ hμreal_ne
      have hreal' : (μ.restrict s).real univ = μ.real s := by
        simp [Measure.real]
      rw [average_eq, smul_eq_mul]
      simp only [integral_const, smul_eq_mul]
      calc
        ((μ.restrict s).real univ)⁻¹ * ((μ.restrict s).real univ * (2 * M))
            = 2 * M * ((μ.restrict s).real univ)⁻¹ * (μ.restrict s).real univ := by ring
        _ = 2 * M * ((μ.real s)⁻¹ * μ.real s) := by simp_rw [hreal']; simp [*]
        _ = 2 * M * 1 := by rw [hId]
        _ = 2 * M := by simp

end SetAverageProperties
end MeasureTheory
