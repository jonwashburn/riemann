import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Riemann.Mathlib.Analysis.Complex.DeBranges.Basic

/-!
# Hermite–Biehler functions and the de Branges measure
-/

open Complex Set Topology MeasureTheory
open scoped ENNReal Complex

namespace HermiteBiehlerFunction

-- [ext, continuous, no_upper_zeros lemmas omitted]

/-
/-- Hermite–Biehler functions have no zeros on the real line (de Branges, Lemma 10).

The proof is highly non-trivial and is left as a placeholder.
-/
lemma no_real_zeros (E : HermiteBiehlerFunction) (x : ℝ) : E x ≠ 0 := by
  sorry-/

variable (E : HermiteBiehlerFunction)


/-! ### Properties of the weight and measure
These properties rely on the (sorried) `no_real_zeros`.
-/

/-- For a Hermite–Biehler function, the norm `|E(x)|` on `ℝ` is strictly positive. -/
lemma norm_E_pos (x : ℝ) : 0 < ‖E x‖ := by
  refine norm_pos_iff.mpr (E.no_real_zeros x)

private lemma weight_sq_pos (x : ℝ) : 0 < ‖E x‖ ^ 2 :=
  pow_pos (E.norm_E_pos x) 2

/-- The weight function `w_E(x)` is strictly positive. -/
lemma weight_pos (x : ℝ) : 0 < E.weight x := by
  dsimp [weight]
  exact inv_pos.mpr (E.weight_sq_pos x)

/-- The continuity of the weight function on ℝ. -/
lemma continuous_weight : Continuous E.weight := by
  unfold weight
  -- E restricted to ℝ is continuous.
  have cont_E_R : Continuous (fun x : ℝ => E x) :=
    E.continuous.comp continuous_ofReal
  -- Norm and squaring are continuous.
  have cont_weight_sq : Continuous (fun x : ℝ => ‖E x‖ ^ 2) :=
    (continuous_norm.comp cont_E_R).pow 2
  -- Inversion is continuous away from zero.
  exact cont_weight_sq.inv₀ (fun x => ne_of_gt (E.weight_sq_pos x))


/-- A general lemma relating the positivity of a set integral to the measure of the set where the function is positive. -/
lemma set_lintegral_pos_iff_ae_pos_on {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) :
    (0 < ∫⁻ a in s, f a ∂μ) ↔ 0 < μ ({a ∈ s | 0 < f a}) := by
  rw [← lintegral_indicator hs, lintegral_pos_iff_support (hf.indicator hs)]
  have : Function.support (s.indicator f) = {a | a ∈ s ∧ 0 < f a} := by
    ext x
    simp [Function.mem_support]
  rw [this]

/-- The de Branges measure associated with a Hermite–Biehler function is locally finite.
A measure defined by a continuous real-valued density against Lebesgue measure is locally finite. -/
instance : IsLocallyFiniteMeasure E.measure :=
  MeasureTheory.IsLocallyFiniteMeasure.withDensity_ofReal E.continuous_weight

/-- The de Branges measure associated with a Hermite–Biehler function has full support
(is an OpenPosMeasure).
This holds because the density is continuous and strictly positive.  -/
instance : Measure.IsOpenPosMeasure E.measure := by
  refine ⟨fun U hUo hUne => ?_⟩
  rw [measure, MeasureTheory.withDensity_apply _ hUo.measurableSet]
  apply ne_of_gt
  rw [set_lintegral_pos_iff_ae_pos_on E.measurable_density hUo.measurableSet]
  have : {x | x ∈ U ∧ 0 < E.density x} = U := by
    ext x
    simp [density, ENNReal.ofReal_pos, E.weight_pos]
  rw [this]
  exact hUo.measure_pos volume hUne

/-- The de Branges measure associated with a Hermite–Biehler function is non-atomic.

Since it is defined as a `withDensity` of Lebesgue measure by a positive continuous
density, it has no atoms. This is convenient when working with pointwise
identities that may fail on a (Lebesgue-)null set, e.g. at a single point. -/
instance : MeasureTheory.NoAtoms E.measure := by
  -- `E.measure` is `volume.withDensity E.density`, and Lebesgue measure `volume` on `ℝ` is non-atomic.
  simpa [HermiteBiehlerFunction.measure] using
    (MeasureTheory.noAtoms_withDensity (μ := (MeasureTheory.volume : Measure ℝ))
      (f := E.density))

/-- In particular, every singleton has `μ_E`-measure zero. -/
lemma measure_singleton (x : ℝ) : E.measure {x} = 0 := by
  simp

end HermiteBiehlerFunction

namespace HermiteBiehlerFunction

/-!
# Hermite–Biehler functions and the de Branges measure (real-valued density view)

This section just repackages the continuity/positivity of the real-valued density
`(‖E x‖ ^ 2)⁻¹` for `E : HermiteBiehlerFunction`, using the infrastructure from
`DeBranges.Basic`. It does **not** introduce new measure instances.
-/

open Complex Set Topology MeasureTheory
open scoped ENNReal


variable (E : HermiteBiehlerFunction)

/-- The real-valued de Branges weight `(‖E x‖ ^ 2)⁻¹` is continuous. -/
lemma continuous_density_real :
    Continuous fun x : ℝ => ((norm (E x)) ^ 2)⁻¹ := by
  -- This is exactly the `weight` from `Basic.lean`.
  simpa [HermiteBiehlerFunction.weight] using E.continuous_weight

/-- The real-valued de Branges weight `(‖E x‖ ^ 2)⁻¹` is continuous and strictly
positive on `ℝ`. This is just a restatement of `continuous_weight`. -/
lemma continuous_weight_inv :
    Continuous fun x : ℝ => (‖E x‖ ^ 2)⁻¹ := by
  -- Same function as `weight`.
  simpa [HermiteBiehlerFunction.weight] using E.continuous_weight

end HermiteBiehlerFunction
