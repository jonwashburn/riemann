import VD.MathlibSubmitted.Nevanlinna_add_proximity
import VD.MathlibSubmitted.Nevanlinna_add_proximity

import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
-- Import needed for integrability of proximity function (log_plus_norm)
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib
import PrimeNumberTheoremAnd
import StrongPNT

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

open Complex Real Set Metric
open MeasureTheory
open scoped Real Topology MeasureTheory ProbabilityTheory Metric

/-!
# Cartan's Formula for Meromorphic Functions

This file proves Cartan's formula, a fundamental result in value distribution theory
relating the characteristic function of a meromorphic function to circle averages
of its counting function.

## Main results

* `cartan` : Cartan's formula for meromorphic functions with a zero at the origin
* `cartan_swap_averages` : Fubini-type swap of circle averages
* `cartan_integrability` : Product integrability of the Cartan kernel

## Implementation notes

The proof is structured around several general lemmas that may be useful elsewhere:
* Interval integral / measure restriction conversions
* Circle integrability for bounded measurable functions
* Product measure integrability for log-norm kernels
-/

/-!
## Measurability of Meromorphic Functions

Meromorphic functions on ℂ are Borel measurable. The key observation is that
the set of poles is discrete (hence countable), and the function is analytic
(hence continuous) on the complement of the poles.
-/

section MeromorphicMeasurability

/-- A function meromorphic on all of ℂ is Borel measurable.

The proof uses that:
1. The set of poles is discrete, hence countable
2. Countable sets have measure zero in ℂ
3. The function is analytic (continuous) off the poles
4. A function continuous off a measure-zero set is measurable

For the formal proof, we use that ℂ is a Polish space where continuous
functions are measurable, and the poles form a closed discrete set. -/
lemma MeromorphicOn.measurable_of_univ {f : ℂ → ℂ} (hf : MeromorphicOn f ⊤) : Measurable f := by
  -- The set of poles is discrete, hence the function is continuous on a dense open set.
  -- In a Polish space, any function that is continuous on the complement of a countable
  -- closed set is Borel measurable.
  --
  -- Strategy: Use that f is continuous off poles, poles are discrete (countable),
  -- and apply measurable_of_continuousOn_compl_countable or similar.
  --
  -- For now, we use that meromorphic functions on ℂ are limits of rational functions,
  -- which are measurable. This requires developing the theory further.
  sorry

/-- Composition of a meromorphic function with a continuous function is measurable. -/
lemma MeromorphicOn.measurable_comp_of_continuous {f : ℂ → ℂ} {g : ℝ → ℂ}
    (hf : MeromorphicOn f ⊤) (hg : Continuous g) : Measurable (f ∘ g) := by
  exact hf.measurable_of_univ.comp hg.measurable

/-- Composition of a meromorphic function with circleMap is measurable. -/
lemma MeromorphicOn.measurable_comp_circleMap {f : ℂ → ℂ} (hf : MeromorphicOn f ⊤)
    (c : ℂ) (R : ℝ) : Measurable (fun θ => f (circleMap c R θ)) :=
  hf.measurable_comp_of_continuous (continuous_circleMap c R)

end MeromorphicMeasurability

/-!
## General Integration Lemmas

These lemmas handle conversions between different representations of integrals
and provide general criteria for integrability.
-/

section IntegrationLemmas

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integral with respect to a restricted measure equals the set integral. -/
lemma integral_restrict_eq_setIntegral' {μ : Measure α} {s : Set α} (f : α → E) :
    ∫ x, f x ∂μ.restrict s = ∫ x in s, f x ∂μ := rfl

/-- Set integral equals integral with respect to restricted measure. -/
lemma setIntegral_eq_integral_restrict' {μ : Measure α} {s : Set α} (f : α → E) :
    (∫ x in s, f x ∂μ) = ∫ x, f x ∂μ.restrict s := rfl

/-- For `0 ≤ a`, the set `uIoc 0 a` equals `Ioc 0 a`. -/
lemma uIoc_zero_eq_Ioc {a : ℝ} (ha : 0 ≤ a) : Set.uIoc 0 a = Set.Ioc 0 a := by
  simp [Set.uIoc_of_le ha]

/-- Integral over `uIoc 0 a` equals integral over `Ioc 0 a` for `0 ≤ a`. -/
lemma setIntegral_uIoc_eq_Ioc {f : ℝ → E} {a : ℝ} (ha : 0 ≤ a) :
    ∫ x in Set.uIoc 0 a, f x = ∫ x in Set.Ioc 0 a, f x := by
  simp [uIoc_zero_eq_Ioc ha]

/-- Convert integral w.r.t. restricted measure to interval integral for nonnegative bounds. -/
lemma integral_restrict_Ioc_eq_intervalIntegral {f : ℝ → E} {a : ℝ} (ha : 0 ≤ a) :
    ∫ x, f x ∂volume.restrict (Set.Ioc 0 a) = ∫ x in 0..a, f x := by
  rw [integral_restrict_eq_setIntegral']
  exact (intervalIntegral.integral_of_le ha).symm

end IntegrationLemmas

/-!
## Circle Integrability Lemmas

These lemmas provide criteria for circle integrability, particularly for
bounded measurable functions.
-/

section CircleIntegrabilityLemmas

/-- A bounded, ae strongly measurable function is circle integrable.
    This is a key tool for proving circle integrability of parametric functions. -/
lemma CircleIntegrable.of_bdd_ae_measurable {f : ℂ → ℝ} {c : ℂ} {R : ℝ} {M : ℝ}
    (h_meas : AEStronglyMeasurable (fun θ => f (circleMap c R θ))
        (volume.restrict (Set.uIoc 0 (2 * Real.pi))))
    (h_bdd : ∀ᵐ θ ∂volume.restrict (Set.uIoc 0 (2 * Real.pi)), ‖f (circleMap c R θ)‖ ≤ M) :
    CircleIntegrable f c R := by
  unfold CircleIntegrable
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound ?_ h_meas M ?_
  · -- The measure of `uIoc 0 (2π)` is finite
    simp only [Set.uIoc_of_le Real.two_pi_pos.le, Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_lt_top
  · exact h_bdd

/-- Circle integrability from pointwise bound and measurability (simplified version). -/
lemma CircleIntegrable.of_norm_le_const {f : ℂ → ℝ} {c : ℂ} {R : ℝ} {M : ℝ}
    (h_meas : AEStronglyMeasurable (fun θ => f (circleMap c R θ))
        (volume.restrict (Set.uIoc 0 (2 * Real.pi))))
    (h_bdd : ∀ θ, ‖f (circleMap c R θ)‖ ≤ M) :
    CircleIntegrable f c R := by
  apply CircleIntegrable.of_bdd_ae_measurable h_meas
  filter_upwards with θ
  exact h_bdd θ

/-- A continuous function on the plane is circle integrable on every circle. -/
lemma CircleIntegrable.of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Continuous f) (c : ℂ) (R : ℝ) :
    CircleIntegrable f c R := by
  unfold CircleIntegrable
  simpa using
    (hf.comp (continuous_circleMap c R)).intervalIntegrable (a := 0) (b := 2 * Real.pi)

/-- A function that is constant on the sphere is circle integrable. -/
lemma circleIntegrable_of_const_on_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {c : ℂ} {R : ℝ} {C : E}
    (h_eq : ∀ a ∈ Metric.sphere c |R|, f a = C) :
    CircleIntegrable f c R := by
  have h_param_eq : ∀ θ, f (circleMap c R θ) = C := by
    intro θ
    apply h_eq
    -- Need to show circleMap c R θ is on the sphere.
    simp [mem_sphere_iff_norm, circleMap_sub_center]
  unfold CircleIntegrable
  simp [h_param_eq, intervalIntegrable_const]

end CircleIntegrabilityLemmas

/-!
## Product Measure Integrability

These lemmas provide criteria for integrability on product measures,
particularly for functions with logarithmic singularities.
-/

section ProductIntegrability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- If a function is integrable on each slice and the slices are uniformly bounded,
    then it is integrable on the product measure (for finite measures). -/
lemma Integrable.of_slices_bdd {μ : Measure α} {ν : Measure β} {f : α × β → ℝ}
    [IsFiniteMeasure μ] [SFinite ν]
    (h_meas : AEStronglyMeasurable f (μ.prod ν))
    (h_slice : ∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν)
    (h_bdd : ∃ M : ℝ, ∀ᵐ x ∂μ, ∫ y, |f (x, y)| ∂ν ≤ M) :
    Integrable f (μ.prod ν) := by
  classical
  rcases h_bdd with ⟨M, hM⟩
  -- Consider the function `x ↦ ∫ ‖f (x, y)‖ dy`.
  set g : α → ℝ := fun x => ∫ y, ‖f (x, y)‖ ∂ν
  have hg_meas :
      AEStronglyMeasurable g μ :=
    h_meas.norm.integral_prod_right'
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    have : 0 ≤ ∫ y, ‖f (x, y)‖ ∂ν :=
      integral_nonneg fun _ => norm_nonneg _
    simpa [g] using this
  have hg_bound :
      ∀ᵐ x ∂μ, ‖g x‖ ≤ max M 0 := by
    filter_upwards [hM] with x hx
    have hx' : g x ≤ M := by simpa [g] using hx
    have hx'' : g x ≤ max M 0 := le_trans hx' (le_max_left _ _)
    have hx_nonneg : 0 ≤ g x := hg_nonneg x
    have hnorm : ‖g x‖ = g x := by
      simp [Real.norm_eq_abs, abs_of_nonneg hx_nonneg]
    dsimp [hnorm.symm]; exact le_of_eq_of_le hnorm hx''
  have hg_int : Integrable g μ :=
    Integrable.of_bound hg_meas (max M 0) hg_bound
  -- Apply the product integrability criterion.
  have := (MeasureTheory.integrable_prod_iff h_meas).2 ⟨h_slice, hg_int⟩
  simpa [g] using this

/-- Integrability on a product of restricted Lebesgue measures from slice integrability. -/
lemma integrable_prod_of_intervalIntegrable {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (_ : a ≤ b) (hcd : c ≤ d)
    (h_meas :
      AEStronglyMeasurable f
        ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))))
    (_ : ∀ y ∈ Set.Icc c d, IntervalIntegrable (fun x => f (x, y)) volume a b)
    (h_y : ∀ x ∈ Set.Icc a b, IntervalIntegrable (fun y => f (x, y)) volume c d)
    (h_bdd : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc c d, |f (x, y)| ≤ M) :
    Integrable f ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc c d))) := by
  classical
  set μ := volume.restrict (Set.Ioc a b)
  set ν := volume.restrict (Set.Ioc c d)
  obtain ⟨M, hM⟩ := h_bdd
  have h_slice_all :
      ∀ x ∈ Set.Ioc a b, Integrable (fun y => f (x, y)) ν := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hx
    have hy := h_y x hxIcc
    have hy' :
        IntegrableOn (fun y => f (x, y)) (Set.Ioc c d) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).1 hy
    simpa [IntegrableOn, ν] using hy'
  have h_slice :
      ∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν := by
    have h_all :
        ∀ᵐ x ∂volume, x ∈ Set.Ioc a b → Integrable (fun y => f (x, y)) ν := by
      refine ae_of_all _ fun x hx => h_slice_all x hx
    have hs : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
    simpa [μ] using
      ((MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioc a b)
          (p := fun x => Integrable (fun y => f (x, y)) ν) hs).2 h_all)
  have h_bound_Ioc :
      ∀ x ∈ Set.Ioc a b, ∀ y ∈ Set.Ioc c d, |f (x, y)| ≤ max M 0 := by
    intro x hx y hy
    have hxIcc : x ∈ Set.Icc a b := Set.Ioc_subset_Icc_self hx
    have hyIcc : y ∈ Set.Icc c d := Set.Ioc_subset_Icc_self hy
    exact (hM x hxIcc y hyIcc).trans (le_max_left _ _)
  have h_ae_bound :
      ∀ x ∈ Set.Ioc a b, ∀ᵐ y ∂ν, |f (x, y)| ≤ max M 0 := by
    intro x hx
    have h_all :
        ∀ᵐ y ∂volume, y ∈ Set.Ioc c d → |f (x, y)| ≤ max M 0 := by
      refine ae_of_all _ fun y hy => h_bound_Ioc x hx y hy
    have hs : MeasurableSet (Set.Ioc c d) := measurableSet_Ioc
    simpa [ν] using
      ((MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioc c d)
          (p := fun y => |f (x, y)| ≤ max M 0) hs).2 h_all)
  have h_bound_point :
      ∀ x ∈ Set.Ioc a b,
        ∫ y, |f (x, y)| ∂ν ≤ max M 0 * ν.real univ := by
    intro x hx
    have h_nonneg : 0 ≤ᵐ[ν] fun y => |f (x, y)| :=
      ae_of_all (μ := ν) fun _ => abs_nonneg _
    have h_const : Integrable (fun _ : ℝ => max M 0) ν :=
      integrable_const (μ := ν) _
    have h_le_const := h_ae_bound x hx
    have h_int :=
      MeasureTheory.integral_mono_of_nonneg h_nonneg h_const h_le_const
    simpa [ν, integral_const (μ := ν), smul_eq_mul, mul_comm] using h_int
  have h_bound :
      ∀ᵐ x ∂μ, ∫ y, |f (x, y)| ∂ν ≤ max M 0 * ν.real univ := by
    have h_all :
        ∀ᵐ x ∂volume, x ∈ Set.Ioc a b →
            ∫ y, |f (x, y)| ∂ν ≤ max M 0 * ν.real univ := by
      refine ae_of_all _ fun x hx => h_bound_point x hx
    have hs : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
    simpa [μ] using
      ((MeasureTheory.ae_restrict_iff' (μ := volume) (s := Set.Ioc a b)
          (p := fun x =>
            ∫ y, |f (x, y)| ∂ν ≤ max M 0 * ν.real univ) hs).2 h_all)
  have :=
    Integrable.of_slices_bdd
      (μ := μ) (ν := ν) (f := f)
      (h_meas := by simpa [μ, ν] using h_meas)
      h_slice
      ⟨max M 0 * ν.real univ, h_bound⟩
  simpa [μ, ν] using this

end ProductIntegrability

/-!
## Interval Integral Swap Lemmas

These lemmas handle swapping the order of integration for interval integrals.
-/

section IntervalIntegralSwap

/-- Swap order of integration for two interval integrals.
    This is a convenient wrapper around Fubini's theorem. -/
lemma intervalIntegral_swap {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (h_int : Integrable (Function.uncurry f)
        ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (Set.uIoc c d)))) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  classical
  have hμ : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  have hν : Set.uIoc c d = Set.Ioc c d := Set.uIoc_of_le hcd
  set μ := volume.restrict (Set.Ioc a b)
  set ν := volume.restrict (Set.Ioc c d)
  have h_int' : Integrable (Function.uncurry f) (μ.prod ν) := by
    simpa [μ, ν, hμ, hν] using h_int
  have h_left :
      ∫ x in a..b, ∫ y in c..d, f x y =
        ∫ x, ∫ y, f x y ∂ν ∂μ := by
    simp [μ, ν, intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_of_le hcd]
  have h_right :
      ∫ y in c..d, ∫ x in a..b, f x y =
        ∫ y, ∫ x, f x y ∂μ ∂ν := by
    simp [μ, ν, intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_of_le hcd]
  have h_swap :=
    MeasureTheory.integral_integral_swap (μ := μ) (ν := ν) (f := f) h_int'
  calc
    ∫ x in a..b, ∫ y in c..d, f x y
        = ∫ x, ∫ y, f x y ∂ν ∂μ := h_left
    _ = ∫ y, ∫ x, f x y ∂μ ∂ν := h_swap
    _ = ∫ y in c..d, ∫ x in a..b, f x y := h_right.symm

/-- For integrable kernels, swapping interval integrals preserves equality. -/
lemma intervalIntegral_comm {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (h_int : Integrable (Function.uncurry f)
        ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (Set.uIoc a b)))) :
    ∫ x in a..b, ∫ y in a..b, f x y = ∫ y in a..b, ∫ x in a..b, f x y :=
  intervalIntegral_swap hab hab h_int

end IntervalIntegralSwap

/-!
## Log-Norm Circle Integrability

Specialized lemmas for circle integrability of log-norm functions,
which appear frequently in value distribution theory.
-/

section LogNormCircleIntegrability

/-- The function `log ‖z - a‖` is circle integrable for any `a` and any circle.
    This is a fundamental result for value distribution theory. -/
lemma circleIntegrable_log_norm_sub (z : ℂ) (c : ℂ) (R : ℝ) :
    CircleIntegrable (fun a => Real.log ‖z - a‖) c R := by
  have h := circleIntegrable_log_norm_sub_const (a := z) (c := c) (r := R)
  convert h using 1
  funext a
  rw [norm_sub_rev]

/-- Circle average of `log ‖z - ·‖` over the unit circle equals `log⁺ ‖z‖`.
    This is a key identity for Cartan's formula. -/
lemma circleAverage_log_norm_sub_eq_posLog (z : ℂ) :
    circleAverage (fun a => Real.log ‖z - a‖) 0 1 = log⁺ ‖z‖ := by
  have : (fun a => Real.log ‖z - a‖) = (fun a => Real.log ‖a - z‖) := by
    funext a; rw [norm_sub_rev]
  simp [this]

end LogNormCircleIntegrability

namespace ValueDistribution

variable {f : ℂ → ℂ}

open scoped Topology

/--
If `f` is meromorphic and continuous at `x`, and has positive meromorphic order at `x`,
then `f` is analytic at `x`.

This is a simple corollary of `MeromorphicAt.analyticAt`.
-/
lemma analyticAt_of_meromorphicOrderAt_pos
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {x : 𝕜}
    (hmero : MeromorphicAt f x) (hcont : ContinuousAt f x)
    (_ : 0 < meromorphicOrderAt f x) :
    AnalyticAt 𝕜 f x :=
  MeromorphicAt.analyticAt hmero hcont

/--
For an analytic function, `0 < meromorphicOrderAt f x` iff `f x = 0`.

This is the meromorphic-order version of `AnalyticAt.analyticOrderAt_ne_zero`.
-/
lemma meromorphicOrderAt_pos_iff_zero
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    0 < meromorphicOrderAt f x ↔ f x = 0 := by
  classical
  -- Express meromorphic order via analytic order.
  have h_eq := hf.meromorphicOrderAt_eq (f := f) (x := x)
  have h1 :
      0 < meromorphicOrderAt f x ↔
        0 < (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) := by
    simp [h_eq]
  -- For the mapped order, positivity is the same as being nonzero (since it is nonnegative).
  have h2 :
      0 < (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) ↔
        (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) ≠ 0 := by
    constructor
    · intro h; exact ne_of_gt h
    · intro hne
      have h_nonneg :
          (0 : WithTop ℤ) ≤ (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) := by
        -- `map_natCast_nonneg : 0 ≤ n.map Nat.cast`
        simp
      exact lt_of_le_of_ne h_nonneg hne.symm
  -- Unwrap the `map Nat.cast`: being nonzero after mapping is the same as being nonzero before.
  have h3 :
      (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) ≠ 0 ↔
        analyticOrderAt f x ≠ 0 := by
    -- `map_natCast_eq_zero : n.map Nat.cast = 0 ↔ n = 0`
    simp
  -- For analytic functions, analytic order ≠ 0 iff `f x = 0`.
  have h4 :
      analyticOrderAt f x ≠ 0 ↔ f x = 0 := hf.analyticOrderAt_ne_zero
  exact (h1.trans h2).trans (h3.trans h4)

/--
Jensen-type identity relating zeros and poles: for a meromorphic `f` on the plane,
the difference of counting functions at `0` and at `⊤` equals a circle average
minus the trailing coefficient term.
-/
lemma logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
    {f : ℂ → ℂ} (hf : MeromorphicOn f ⊤) {R : ℝ} (hR : R ≠ 0) :
    logCounting f 0 R - logCounting f ⊤ R
      = circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
          - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  -- Start from the functional identity of the First Main Theorem.
  have h_fun :=
    ValueDistribution.characteristic_sub_characteristic_inv (f := f) (h := hf)
  -- Evaluate at `R`.
  have h_eval :
      characteristic f ⊤ R - characteristic f⁻¹ ⊤ R =
        circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
          - (divisor f Set.univ).logCounting R := by
    have := congrArg (fun F ↦ F R) h_fun
    simpa [Pi.sub_apply] using this
  -- Quantitative version at radius `R`.
  have h_quant :=
    ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero
      (f := f) (hf := hf) (hR := hR)
  -- Combine: both right-hand sides equal the same difference.
  have h_eq :
      circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
        - (divisor f Set.univ).logCounting R
        = Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    have := h_eval
    aesop
  -- Rewrite the divisor counting term via `logCounting`.
  have h_div :
      (divisor f Set.univ).logCounting R =
        logCounting f 0 R - logCounting f ⊤ R := by
    have := ValueDistribution.log_counting_zero_sub_logCounting_top (f := f)
    exact congrArg (fun F ↦ F R) this
  -- Substitute and solve for `logCounting f 0 R - logCounting f ⊤ R`.
  have h4 :
      circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
        - (logCounting f 0 R - logCounting f ⊤ R)
        = Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    simpa [h_div] using h_eq
  have h5 :
      logCounting f 0 R - logCounting f ⊤ R
        = circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
            - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    have h' :
        circleAverage (fun z ↦ Real.log ‖f z‖) 0 R =
          Real.log ‖meromorphicTrailingCoeffAt f 0‖
            + (logCounting f 0 R - logCounting f ⊤ R) := by
      simpa [sub_eq_iff_eq_add] using h4
    have := congrArg (fun t ↦ t - Real.log ‖meromorphicTrailingCoeffAt f 0‖) h'
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
  exact h5

lemma cartan_f1 {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ} (hR : R ≠ 0) (a : ℂ) :
    logCounting f a R + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖
      = circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R + logCounting f ⊤ R := by
  -- Apply the Jensen-type lemma to `g := f - a` at `0`.
  have hg : MeromorphicOn (fun z ↦ f z - a) ⊤ := h.sub (MeromorphicOn.const a)
  have hJ :
      logCounting (fun z ↦ f z - a) 0 R - logCounting (fun z ↦ f z - a) ⊤ R
        = circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
            - Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ :=
    logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const (f := fun z ↦ f z - a)
      (hf := hg) (R := R) hR
  -- Rewrite `logCounting (f - a) 0` and `logCounting (f - a) ⊤` via the API.
  have h_zero :
      logCounting (fun z ↦ f z - a) 0 = logCounting f (↑a : WithTop ℂ) := by
    simpa using
      (ValueDistribution.logCounting_coe_eq_logCounting_sub_const_zero
        (f := f) (a₀ := a)).symm
  have h_top :
      logCounting (fun z ↦ f z - a) ⊤ = logCounting f ⊤ :=
    ValueDistribution.logCounting_sub_const (f := f) (a₀ := a)
      (hf := h)   -- `hf` here is `MeromorphicOn f univ`, which we have as `h`.
  -- Expand `hJ` and rearrange to the desired equality.
  -- Substitute the two identities into `hJ`.
  have hJ' :
      logCounting f a R - logCounting f ⊤ R
        = circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
            - Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ := by
    simpa [h_zero, h_top] using hJ
  -- Move terms: `A - B = C - D` ⇒ `A + D = C + B`.
  have :
      logCounting f a R + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖
        = circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R + logCounting f ⊤ R := by
    have := congrArg (fun t ↦ t + logCounting f ⊤ R
                           + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) hJ'
    -- A bit of algebra:
    -- left:  (A - B) + B + D = A + D
    -- right: (C - D) + B + D = C + B
    simp [sub_eq_add_neg, add_comm, add_left_comm,] at this
    simpa [add_comm, add_left_comm, add_assoc] using this
  exact this

lemma trailingCoeff_sub_const_eq_neg {f : ℂ → ℂ}
    (h : MeromorphicOn f ⊤) (h₂ : 0 < meromorphicOrderAt f 0)
    {a : ℂ} (ha : a ≠ 0) :
    meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0 = -a := by
  classical
  -- Work with g := f - a.
  let g : ℂ → ℂ := fun z ↦ f z - a
  have hmero_f : MeromorphicAt f 0 := h 0 (by trivial)
  have hmero_g : MeromorphicAt g 0 := by
    have hg_on : MeromorphicOn g ⊤ := h.sub (MeromorphicOn.const a)
    exact hg_on 0 (by trivial)
  -- `f` tends to 0 on the punctured neighborhood of 0.
  have h_tendsto0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := 0) h₂
  -- Hence `g = f - a` tends to `-a` on the punctured neighborhood.
  have h_tendsto_g :
      Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (-a)) := by
    -- use `Filter.tendsto_sub_const_iff` with `b := a`, `c := 0`
    have := (Filter.tendsto_sub_const_iff (G := ℂ) (b := a) (c := (0 : ℂ))
      (f := f) (l := 𝓝[≠] (0 : ℂ))).2 h_tendsto0
    -- left side is `Tendsto (fun z ↦ f z - a) _ (𝓝 (0 - a))`
    simpa [g, sub_eq_add_neg] using this
  -- Nonzero finite limit implies meromorphic order 0 for `g` at 0.
  have h_ord :
      meromorphicOrderAt g 0 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf := hmero_g)).mp
      ⟨-a, by simp [ha], h_tendsto_g⟩
  -- Trailing coefficient is the limit of `z ^ (-ord) • g z` on the punctured neighborhood.
  have h_trail_lim :=
    MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt (h := hmero_g)
  -- With order 0, the weight `(z-0)^(-ord)` is identically 1, so this is just `g`.
  have h_trail :
      Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (meromorphicTrailingCoeffAt g 0)) := by
    have : (fun z : ℂ =>
              (z - 0) ^ (-(meromorphicOrderAt g 0).untop₀) • g z)
          = g := by
      simp [g, h_ord]
    aesop
  -- Uniqueness of limits in a Hausdorff space.
  have h_eq :
      meromorphicTrailingCoeffAt g 0 = -a :=
    tendsto_nhds_unique'
      (X := ℂ) (Y := ℂ) (l := 𝓝[≠] (0 : ℂ))
      (a := meromorphicTrailingCoeffAt g 0) (b := -a)
      (by infer_instance) h_trail h_tendsto_g
  -- Rewrite in terms of the original function `f`.
  simpa [g] using h_eq

lemma cartan_sigma2 {f : ℂ → ℂ} (h : MeromorphicOn f ⊤)
    (h₂ : 0 < meromorphicOrderAt f 0) :
    circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 = 0 := by
  classical
  -- On the unit circle, the trailing coefficient is `-a`, so its norm is 1 and `log 1 = 0`.
  have h_on_circle :
      ∀ a ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|,
        Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ = (0 : ℝ) := by
    intro a ha
    -- On `|a| = 1` we have `a ≠ 0`.
    have hnorm : ‖a‖ = 1 := by
      -- `sphere 0 |1|` is `{a | ‖a‖ = 1}`
      aesop
    have ha_ne : a ≠ 0 := by
      intro h0; subst h0; simp at hnorm
    -- Compute trailing coefficient via the previous lemma.
    have h_tc :
        meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0 = -a :=
      trailingCoeff_sub_const_eq_neg h h₂ ha_ne
    -- Its norm is 1, hence `log 1 = 0`.
    have : Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖
        = Real.log (1 : ℝ) := by
      simp [h_tc, hnorm]  -- uses `‖-a‖ = ‖a‖`
    aesop
  -- Apply `circleAverage_const_on_circle` with constant `0`.
  have :=
    Real.circleAverage_const_on_circle
      (f := fun a : ℂ =>
        Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖)
      (c := (0 : ℂ)) (R := (1 : ℝ)) (a := (0 : ℝ)) h_on_circle
  -- The circle average equals the constant `0`.
  simpa using this

-- Kernel used in Cartan's swap-of-averages formula.
noncomputable def cartanKernel (f : ℂ → ℂ) (R : ℝ) (α β : ℝ) : ℝ :=
  Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖

/-!
### Slice Integrability of Cartan Kernel

These lemmas establish that the Cartan kernel is integrable when one variable is fixed.
-/

/-- For fixed β, the Cartan kernel is interval integrable in α.
    This follows from the circle integrability of `log ‖z - ·‖`. -/
lemma cartanKernel_integrable_in_alpha (f : ℂ → ℂ) (R : ℝ) (β : ℝ) :
    IntervalIntegrable (fun α => cartanKernel f R α β) volume 0 (2 * Real.pi) := by
  simp only [cartanKernel]
  have h_eq : (fun α => Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖)
      = (fun α => Real.log ‖circleMap 0 1 α - f (circleMap 0 R β)‖) := by
    funext α; rw [norm_sub_rev]
  rw [h_eq]
  have := circleIntegrable_log_norm_sub_const (a := f (circleMap 0 R β)) (c := 0) (r := 1)
  simpa [CircleIntegrable] using this

/-- For fixed α, the Cartan kernel is interval integrable in β
    when f is meromorphic on the circle of radius R. -/
lemma cartanKernel_integrable_in_beta {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) (R : ℝ) (α : ℝ) :
    IntervalIntegrable (fun β => cartanKernel f R α β) volume 0 (2 * Real.pi) := by
  simp only [cartanKernel]
  have hg : MeromorphicOn (fun z => f z - circleMap 0 1 α) (sphere 0 |R|) := by
    apply MeromorphicOn.sub (fun z hz => h z trivial) (fun _ _ => analyticAt_const.meromorphicAt)
  have := circleIntegrable_log_norm_meromorphicOn hg
  simpa [CircleIntegrable] using this

/-!
### Fubini-Type Lemmas for Cartan Kernel

These lemmas handle the swap of integration order needed for Cartan's formula.
-/

/-- The double interval integral equals the integral over the product measure. -/
lemma double_intervalIntegral_eq_prod_integral {f : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h_int : Integrable (Function.uncurry f)
        ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (Set.uIoc a b)))) :
    ∫ x in a..b, ∫ y in a..b, f x y =
      ∫ p : ℝ × ℝ, f p.1 p.2 ∂(volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc a b)) := by
  classical
  have hμ : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  set μ := volume.restrict (Set.Ioc a b)
  have h_int' :
      Integrable (Function.uncurry f) (μ.prod μ) := by
    simpa [μ, hμ] using h_int
  have h_iter :
      ∫ x in a..b, ∫ y in a..b, f x y =
        ∫ x, ∫ y, f x y ∂μ ∂μ := by
    simp [μ, intervalIntegral.integral_of_le hab]
  have h_prod :=
    MeasureTheory.integral_integral (μ := μ) (ν := μ) (f := f) h_int'
  simpa [μ] using h_iter.trans h_prod

/-- Convert product measure integral back to double interval integral. -/
lemma prod_integral_eq_double_intervalIntegral {f : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h_int : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
        ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (Set.uIoc a b)))) :
    ∫ p : ℝ × ℝ, f p.1 p.2 ∂(volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc a b)) =
      ∫ x in a..b, ∫ y in a..b, f x y := by
  classical
  have hμ : Set.uIoc a b = Set.Ioc a b := Set.uIoc_of_le hab
  set μ := volume.restrict (Set.Ioc a b)
  have h_int' :
      Integrable (Function.uncurry f) (μ.prod μ) := by
    simpa [Function.uncurry, μ, hμ] using h_int
  have h_prod :=
    (MeasureTheory.integral_integral (μ := μ) (ν := μ) (f := f) h_int').symm
  have h_iter :
      ∫ x, ∫ y, f x y ∂μ ∂μ =
        ∫ x in a..b, ∫ y in a..b, f x y := by
    simp [μ, intervalIntegral.integral_of_le hab]
  simpa [μ] using h_prod.trans h_iter

/-- The Cartan kernel is integrable on the product measure `[0,2π] × [0,2π]`.

This is the key integrability result needed for Cartan's formula.
The proof uses Tonelli's theorem by analyzing the iterated integral of the absolute value
of the kernel, leveraging Jensen's formula and properties of the proximity function.
-/
lemma cartan_integrability {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ} (_hR : R ≠ 0) :
    Integrable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
       (volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
  -- Proof using Tonelli's theorem strategy.
  have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have hIoc : Set.uIoc 0 (2 * Real.pi) = Set.Ioc 0 (2 * Real.pi) := Set.uIoc_of_le h0_le
  simp only [hIoc]
  set μ := volume.restrict (Set.Ioc 0 (2 * Real.pi)) with hμ_def

  -- 1. Measurability of the kernel.
  have h_meas_K : Measurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) := by
    -- Meromorphic functions on ℂ are measurable.
    have h_meas_f : Measurable f := h.measurable_of_univ
    have h_meas_G1 : Measurable (fun p : ℝ × ℝ => f (circleMap 0 R p.2)) :=
      h_meas_f.comp ((continuous_circleMap 0 R).measurable.comp measurable_snd)
    have h_meas_G2 : Measurable (fun p : ℝ × ℝ => circleMap 0 1 p.1) :=
      (continuous_circleMap 0 1).measurable.comp measurable_fst
    have h_meas_G : Measurable (fun p : ℝ × ℝ => f (circleMap 0 R p.2) - circleMap 0 1 p.1) :=
      h_meas_G1.sub h_meas_G2
    simp only [cartanKernel]
    exact Real.measurable_log.comp (continuous_norm.measurable.comp h_meas_G)

  -- 2. Integral of the absolute value of the kernel.
  let K_abs := fun p : ℝ × ℝ => ‖cartanKernel f R p.1 p.2‖
  have h_meas_K_abs : Measurable K_abs := h_meas_K.norm

  -- Inner integral: ∫_α ‖K(α, β)‖ dμ(α).
  let InnerInt := fun β => ∫ α, ‖cartanKernel f R α β‖ ∂μ

  -- Calculation of the inner integral using Jensen's formula identity: ∫|g| = 2∫g⁺ - ∫g.
  have h_inner_calc : ∀ β, InnerInt β =
      2 * (∫ α, max (cartanKernel f R α β) 0 ∂μ) -
      (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖ := by
    intro β
    let z := f (circleMap 0 R β)
    let g := fun α => cartanKernel f R α β -- g(α) = log ‖z - circleMap 0 1 α‖

    -- Integrability of g.
    have h_int_g_prop : Integrable g μ := by
      have := circleIntegrable_log_norm_sub z 0 1
      unfold CircleIntegrable at this
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le] at this
      -- Need to match the parametrization.
      have h_param_match : (fun θ => Real.log ‖z - circleMap 0 1 θ‖) = g := by
        funext θ; simp [g, cartanKernel]; rfl
      rwa [h_param_match] at this

    -- Value of ∫g (from Jensen's formula).
    have h_int_g_val : ∫ α, g (α) ∂μ = (2 * Real.pi) * log⁺ ‖z‖ := by
      have h_avg := circleAverage_log_norm_sub_eq_posLog z
      rw [Real.circleAverage_def] at h_avg
      simp only [smul_eq_mul] at h_avg
      have h_int_eq_μ : ∫ θ in (0 : ℝ)..2 * Real.pi, Real.log ‖z - circleMap 0 1 θ‖ = ∫ θ, g (θ) ∂μ := by
        rw [hμ_def, integral_restrict_Ioc_eq_intervalIntegral h0_le]
        rfl
      rw [h_int_eq_μ] at h_avg
      field_simp at h_avg
      aesop
    -- Identity |x| = 2 * max(x, 0) - x.
    have h_abs_eq : ∀ α, |g (α)| = 2 * max (g (α)) 0 - g (α) := fun α => by
      by_cases h : 0 ≤ g α
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · push_neg at h; rw [abs_of_neg h, max_eq_right (le_of_lt h)]; ring


    -- Integrability of max(g, 0).
    have h_int_g_plus : Integrable (fun α => max (g (α)) 0) μ :=
      h_int_g_prop.sup (integrable_const 0)

    -- Integrate the identity.
    have h_int_abs_g : ∫ α, |g (α)| ∂μ = 2 * ∫ α, max (g (α)) 0 ∂μ - ∫ α, g (α) ∂μ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall h_abs_eq)]
      rw [integral_sub]
      · simp only [integral_const_mul]
      · exact Integrable.const_mul h_int_g_plus 2-- h_int_g_prop
      · exact h_int_g_prop

    -- Combine everything.
    rw [h_int_g_val] at h_int_abs_g
    exact h_int_abs_g

  -- 3. Integrability of the inner integral InnerInt(β).
  -- InnerInt(β) = 2 * Term1(β) - Term2(β).

  -- Integrability of Term2(β) = (2π) * log⁺ ‖f(z_β)‖ (Proximity integrand).
  have h_int_Term2 : Integrable (fun β => (2 * Real.pi) * log⁺ ‖f (circleMap 0 R β)‖) μ := by
    -- Uses the fact that the proximity function integrand is integrable for meromorphic functions.
    have h_prox_integrand : CircleIntegrable (fun z => log⁺ ‖f z‖) 0 R :=
      circleIntegrable_posLog_norm_meromorphicOn fun x a ↦ h x trivial
    --  circleIntegrable_log_plus_norm_meromorphicOn (h.mono (Set.subset_univ _))
    unfold CircleIntegrable at h_prox_integrand
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le] at h_prox_integrand
    exact h_prox_integrand.const_mul (2 * Real.pi)

  -- Integrability of Term1(β) = ∫_α max(K(α, β), 0) dμ(α).
  -- We use the bound Term1(β) ≤ (2π) * (log⁺ ‖f(z_β)‖ + log 2).

  -- Integrability of the bound (log⁺ ‖f(z_β)‖ + log 2).
  have h_int_Bound : Integrable (fun β => log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2) μ := by
    have h_prox_int : Integrable (fun β => log⁺ ‖f (circleMap 0 R β)‖) μ := by
      have h_prox_integrand : CircleIntegrable (fun z => log⁺ ‖f z‖) 0 R :=
        circleIntegrable_posLog_norm_meromorphicOn (fun x _ ↦ h x trivial)
      unfold CircleIntegrable at h_prox_integrand
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le] at h_prox_integrand

    exact h_prox_int.add (integrable_const (Real.log 2))

  have h_int_Term1 : Integrable (fun β => ∫ α, max (cartanKernel f R α β) 0 ∂μ) μ := by
    -- Bound Term1(β).
    have h_bound_Term1 : ∀ β, (∫ α, max (cartanKernel f R α β) 0 ∂μ) ≤
        (2 * Real.pi) * (log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2) := by
      intro β
      let z := f (circleMap 0 R β)
      have h_integrand_bound : ∀ α, max (cartanKernel f R α β) 0 ≤ log⁺ ‖z‖ + Real.log 2 := by
        intro α
        let a := circleMap 0 1 α
        have ha_norm : ‖a‖ = 1 := by show ‖circleMap 0 1 α‖ = 1; simp [norm_circleMap_zero]
        -- max(log ‖z-a‖, 0) = log⁺ ‖z-a‖.
        have h_eq_logplus : max (cartanKernel f R α β) 0 = log⁺ ‖z - a‖ := by
          simp only [cartanKernel]
          rw [max_comm, Real.posLog_def]

        rw [h_eq_logplus]
        -- log⁺ ‖z-a‖ ≤ log⁺ (‖z‖ + 1) ≤ log⁺ ‖z‖ + log 2.
        have h_le_plus1 : log⁺ ‖z - a‖ ≤ log⁺ (‖z‖ + 1) := by
          apply Real.posLog_le_posLog (norm_nonneg _)
          calc ‖z - a‖ ≤ ‖z‖ + ‖a‖ := norm_sub_le z a
            _ = ‖z‖ + 1 := by rw [ha_norm]
        -- Uses the inequality log⁺(t+1) ≤ log⁺(t) + log 2.
        have h_le_log2 : log⁺ (‖z‖ + 1) ≤ log⁺ ‖z‖ + Real.log 2 := by
          calc log⁺ (‖z‖ + 1) ≤ Real.log 2 + log⁺ ‖z‖ + log⁺ 1 := Real.posLog_add
            _ = Real.log 2 + log⁺ ‖z‖ := by simp [Real.posLog_one]
            _ = log⁺ ‖z‖ + Real.log 2 := by ring

        exact le_trans h_le_plus1 h_le_log2

      -- Integrate the bound.
      have h_int_le : ∫ α, max (cartanKernel f R α β) 0 ∂μ ≤ ∫ _, log⁺ ‖z‖ + Real.log 2 ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => le_max_right _ _))
          (integrable_const _) (Filter.Eventually.of_forall h_integrand_bound)
      have h_int_const : ∫ _, log⁺ ‖z‖ + Real.log 2 ∂μ = (log⁺ ‖z‖ + Real.log 2) * (2 * Real.pi) := by
        rw [integral_const, smul_eq_mul, mul_comm, hμ_def, measureReal_restrict_apply_univ,
            Real.volume_real_Ioc_of_le h0_le, sub_zero]
      linarith [h_int_le, h_int_const.symm.le]

    -- AEStronglyMeasurable of Term1(β).
    have h_aesm_Term1 : AEStronglyMeasurable (fun β => ∫ α, max (cartanKernel f R α β) 0 ∂μ) μ := by
      -- Uses product measurability of the integrand and Fubini/Tonelli structure.
      have h_meas_integrand : Measurable (fun p : ℝ × ℝ => max (cartanKernel f R p.1 p.2) 0) :=
        h_meas_K.max measurable_const
      exact h_meas_integrand.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable

    have h_norm_bound : ∀ β, ‖∫ α, max (cartanKernel f R α β) 0 ∂μ‖ ≤
        ‖(2 * Real.pi) * (log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2)‖ := by
      intro β
      have h_int_nonneg : 0 ≤ ∫ α, max (cartanKernel f R α β) 0 ∂μ :=
        integral_nonneg (fun _ => le_max_right _ _)
      have h_bound_nonneg : 0 ≤ (2 * Real.pi) * (log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2) := by
        apply mul_nonneg (by linarith [Real.two_pi_pos])
        apply add_nonneg Real.posLog_nonneg (Real.log_nonneg (by norm_num))
      rw [Real.norm_of_nonneg h_int_nonneg, Real.norm_of_nonneg h_bound_nonneg]
      exact h_bound_Term1 β
    apply Integrable.mono (h_int_Bound.const_mul (2 * Real.pi)) h_aesm_Term1 (Filter.Eventually.of_forall h_norm_bound)

  -- InnerInt(β) is integrable.
  have h_int_InnerInt : Integrable InnerInt μ := by
    have h_diff := (h_int_Term1.const_mul 2).sub h_int_Term2
    apply Integrable.congr h_diff (Filter.Eventually.of_forall (fun β => (h_inner_calc β).symm))

  -- 4. Conclusion using Tonelli's theorem.
  -- We show that the lintegral of K_abs is finite.
  have h_tonelli_lintegral : ∫⁻ p, ENNReal.ofReal (K_abs p) ∂(μ.prod μ) =
      ∫⁻ β, ENNReal.ofReal (InnerInt β) ∂μ := by
    rw [lintegral_prod_symm _ (Measurable.ennreal_ofReal h_meas_K_abs).aemeasurable]
    apply lintegral_congr
    intro β
    simp only [InnerInt, K_abs]
    have h_nonneg : 0 ≤ᵐ[μ] fun α => ‖cartanKernel f R α β‖ :=
      Filter.Eventually.of_forall (fun _ => norm_nonneg _)
    have h_aesm : AEStronglyMeasurable (fun α => ‖cartanKernel f R α β‖) μ := by
      exact (h_meas_K.comp measurable_prodMk_right).norm.aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae h_nonneg h_aesm]
    -- The inner lintegral equals ofReal of the Bochner integral, which is finite.
    rw [ENNReal.ofReal_toReal]
    · have h_int_alpha : Integrable (fun α => cartanKernel f R α β) μ := by
        rw [hμ_def]
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le).mp (cartanKernel_integrable_in_alpha f R β)
      exact h_int_alpha.norm.lintegral_lt_top.ne

  have h_finite_prod_lintegral : ∫⁻ p, ENNReal.ofReal (K_abs p) ∂(μ.prod μ) < ⊤ := by
    rw [h_tonelli_lintegral]
    exact Integrable.lintegral_lt_top h_int_InnerInt

  -- Integrability of the kernel follows from AEStronglyMeasurable and finite integral of the norm.
  have h_aesm_K_prod : AEStronglyMeasurable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2) (μ.prod μ) :=
    h_meas_K.stronglyMeasurable.aestronglyMeasurable

  exact ⟨h_aesm_K_prod, (hasFiniteIntegral_iff_norm _).mpr h_finite_prod_lintegral⟩

lemma cartan_swap_averages
    {f : ℂ → ℂ} (_h : MeromorphicOn f ⊤) {R : ℝ}
    (h_int_kernel :
      Integrable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2)
        ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
         (volume.restrict (Set.uIoc 0 (2 * Real.pi))))) :
    circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
      = circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R := by
  classical
  -- Kernel in angular parameters α (for a) and β (for z).
  let F : ℝ → ℝ → ℝ := cartanKernel f R

  -- 1D identity: average over a of log ‖z - a‖ is log⁺ ‖z‖.
  have h_inner (z : ℂ) :
      circleAverage (fun a ↦ Real.log ‖z - a‖) 0 1 = log⁺ ‖z‖ := by
    have : (fun a ↦ Real.log ‖z - a‖) = (fun a ↦ Real.log ‖a - z‖) := by
      funext a; simp [norm_sub_rev]
    simp [this]

  -- Left-hand side as a double interval integral.
  have hL :
      circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
        =
      (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
        ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β := by
    simp [Real.circleAverage, F,
          mul_comm, mul_left_comm, mul_assoc]
    aesop
  -- Right-hand side as a single interval integral.
  have hR :
      circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R
        =
      (2 * Real.pi)⁻¹ *
        ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
    simp [Real.circleAverage,
          intervalIntegral.integral_of_le Real.two_pi_pos.le]

  -- For each β, evaluate the α-average using h_inner.
  have h_inner_on_param (β : ℝ) :
      (2 * Real.pi)⁻¹ *
          ∫ α in 0..2 * Real.pi, F α β
        =
      log⁺ ‖f (circleMap 0 R β)‖ := by
    -- First, recognize the left-hand side as a circle average in the variable `a`.
    have h_avg :
        (2 * Real.pi)⁻¹ *
            ∫ α in 0..2 * Real.pi, F α β
          =
        circleAverage (fun a : ℂ ↦ Real.log ‖f (circleMap 0 R β) - a‖) 0 1 := by
      -- This is just unfolding the definition of `Real.circleAverage` and of `F`.
      simp [Real.circleAverage, F, cartanKernel]
    -- Now apply the 1D identity `h_inner` with `z = f (circleMap 0 R β)`.
    have h_id :
        circleAverage (fun a : ℂ ↦ Real.log ‖f (circleMap 0 R β) - a‖) 0 1 =
          log⁺ ‖f (circleMap 0 R β)‖ :=
      h_inner (f (circleMap 0 R β))
    exact h_avg.trans h_id
  -- Integrability of the kernel on the product strip `[0,2π] × [0,2π]`,
  -- assumed as a hypothesis in order to apply Fubini's theorem.
  have h_int :
      Integrable (fun p : ℝ × ℝ => F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
         (volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
    simpa [F, cartanKernel] using h_int_kernel

  have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le

  -- Swap the order of integration over `[0,2π] × [0,2π]` using Fubini.
  have h_swap :
      ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β
        =
      ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β :=
    intervalIntegral_swap h0_le h0_le h_int


  -- Combine: compute the swapped integral via h_inner_on_param.
  have h_main :
      (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
          ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β
        =
      (2 * Real.pi)⁻¹ *
        ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
    have h1 :
        (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
            ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β
          =
        (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
            ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β := by
          rw [h_swap]
    have h2 :
        (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
            ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β
          =
        (2 * Real.pi)⁻¹ *
          ∫ β in 0..2 * Real.pi,
            ((2 * Real.pi)⁻¹ * ∫ α in 0..2 * Real.pi, F α β) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    have h3 :
        (2 * Real.pi)⁻¹ *
          ∫ β in 0..2 * Real.pi,
            ((2 * Real.pi)⁻¹ * ∫ α in 0..2 * Real.pi, F α β)
          =
        (2 * Real.pi)⁻¹ *
          ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro β _
      exact h_inner_on_param β

    calc
      (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β
        = (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β := by
            rw [h_swap]
      _ = (2 * Real.pi)⁻¹ * ∫ β in 0..2 * Real.pi,
              ((2 * Real.pi)⁻¹ * ∫ α in 0..2 * Real.pi, F α β) := by
            simpa using h2
      _ = (2 * Real.pi)⁻¹ * ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := h3

  -- Now match both sides with their circleAverage expressions.
  have :
      circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
        =
      (2 * Real.pi)⁻¹ *
        ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
    simpa [hL] using h_main
  -- Compare with the right-hand side.
  simpa [hR] using this

/-- The positive part of the logarithm is a continuous function. -/
@[fun_prop]
theorem continuous_posLog : Continuous fun x : ℝ => log⁺ x := by
  classical
  have h_max : Continuous fun x : ℝ => max (1 : ℝ) |x| :=
    continuous_const.max continuous_abs
  have h_ne : ∀ x : ℝ, max (1 : ℝ) |x| ≠ 0 := by
    intro x
    have hx : (0 : ℝ) < max (1 : ℝ) |x| :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact ne_of_gt hx
  have h_log : Continuous fun x : ℝ => log (max (1 : ℝ) |x|) :=
    Continuous.log h_max h_ne
  have h_eq :
      (fun x : ℝ => log⁺ x) = fun x : ℝ => log (max (1 : ℝ) |x|) := by
    funext x
    calc
      log⁺ x = log⁺ |x| := by simp [posLog_abs]
      _ = log (max (1 : ℝ) |x|) := posLog_eq_log_max_one (abs_nonneg x)
  simpa [h_eq] using h_log

/-!
### Circle Integrability for Cartan's Formula

These lemmas establish the circle integrability conditions needed for the main theorem.
-/

/-- The function `a ↦ circleAverage (log ‖f · - a‖) 0 R` is circle integrable on the unit circle.

The proof uses Fubini-Tonelli, relying on the product integrability established
in `cartan_integrability`.
-/
lemma circleIntegrable_circleAverage_log_norm_sub_unit {f : ℂ → ℂ}
    (h : MeromorphicOn f ⊤) {R : ℝ} :
    CircleIntegrable (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 := by
  by_cases hR : R = 0
  · -- When R = 0, circleAverage reduces to evaluation at 0.
    subst hR
    have h_eq : (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 0) =
        (fun a ↦ Real.log ‖f 0 - a‖) := by
      funext a
      -- Use the property that circle average at radius 0 is evaluation at the center.
      simp [circleAverage_zero]
    rw [h_eq]
    -- This relies on f(0) being defined (which holds since f : ℂ → ℂ).
    exact circleIntegrable_log_norm_sub (f 0) 0 1

  -- R ≠ 0. We use Fubini on the Cartan kernel.
  have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have h_int := cartan_integrability h hR
  -- By Fubini, the function α ↦ ∫ K(α, β) dβ is integrable.
  have h_fubini := h_int.integral_prod_left

  -- The circle average is (2π)⁻¹ times this integral.
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h0_le]

  -- Relate the parametrized integral to the circle average.
  have h_eq : ∀ α, circleAverage (fun z => Real.log ‖f z - circleMap 0 1 α‖) 0 R =
      (2 * Real.pi)⁻¹ * ∫ β in (0 : ℝ)..2 * Real.pi, cartanKernel f R α β := by
    intro α
    simp only [circleAverage, Real.circleAverage, cartanKernel, smul_eq_mul]

  -- Convert h_fubini to the required form.
  have hIoc : Set.uIoc 0 (2 * Real.pi) = Set.Ioc 0 (2 * Real.pi) := Set.uIoc_of_le h0_le
  rw [hIoc] at h_fubini
  have h_fubini' : Integrable (fun α => ∫ β in Set.Ioc 0 (2 * π), cartanKernel f R α β)
      (volume.restrict (Set.Ioc 0 (2 * π))) := by
    simp only [cartanKernel] at h_fubini ⊢
    exact h_fubini
  have h_fubini'' : Integrable (fun α => ∫ β in (0 : ℝ)..2 * π, cartanKernel f R α β)
      (volume.restrict (Set.Ioc 0 (2 * π))) := by
    simp_rw [intervalIntegral.integral_of_le h0_le]
    exact h_fubini'

  -- Scalar multiples of integrable functions are integrable.
  have h_const_mul := Integrable.const_mul h_fubini'' (2 * Real.pi)⁻¹
  apply IntegrableOn.congr_fun h_const_mul _ measurableSet_Ioc
  intro α _
  exact (h_eq α).symm

/-- The trailing coefficient function is circle integrable when f has a zero at the origin.
    On the unit circle (where |a| = 1 and a ≠ 0), the trailing coefficient of (f - a) is -a,
    so log ‖-a‖ = log 1 = 0. -/
lemma circleIntegrable_log_trailingCoeff {f : ℂ → ℂ} (h : MeromorphicOn f ⊤)
    (h₂ : 0 < meromorphicOrderAt f 0) :
    CircleIntegrable
        (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 := by
  -- The function equals zero on the entire sphere |a| = 1.
  apply circleIntegrable_of_const_on_sphere (C := 0)
  intro a ha
  -- sphere 0 |1| is the unit circle.
  have hnorm : ‖a‖ = 1 := by simp at ha; exact ha
  have ha_ne : a ≠ 0 := by intro h0; subst h0; simp at hnorm
  have h_tc := trailingCoeff_sub_const_eq_neg h h₂ ha_ne
  simp [h_tc, hnorm]

/-- Specialized lemma for circle integrability of logCounting when f(0)=0. -/
lemma circleIntegrable_logCounting_zero_case {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) (h₂ : 0 < meromorphicOrderAt f 0) {R : ℝ} :
    CircleIntegrable (fun a ↦ logCounting f a R) 0 1 := by
  by_cases hR_ne : R = 0
  · simp [hR_ne, ValueDistribution.logCounting_eval_zero]

  have hR : R ≠ 0 := hR_ne

  -- Use cartan_f1 identity: logCounting = H1 - H2.
  let H1 := fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R + logCounting f ⊤ R
  let H2 := fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖

  -- H1 is integrable.
  have hH1_int : CircleIntegrable H1 0 1 := by
    -- Uses circleIntegrable_circleAverage_log_norm_sub_unit, which relies on cartan_integrability.
    have h_avg_int := circleIntegrable_circleAverage_log_norm_sub_unit (R:=R) h
    have h_const_int := circleIntegrable_const (logCounting f ⊤ R) 0 1
    exact h_avg_int.add h_const_int

  -- H2 is integrable because f(0)=0 (uses circleIntegrable_log_trailingCoeff).
  have hH2_int : CircleIntegrable H2 0 1 := circleIntegrable_log_trailingCoeff h h₂

  -- Combine H1 and H2 using cartan_f1.
  have h_eq : (fun a : ℂ ↦ logCounting f a R) = H1 - H2 := by
    funext a
    have h_id := cartan_f1 h hR a
    simp [H1, H2] at h_id ⊢
    -- logCounting + H2 = H1 => logCounting = H1 - H2.
    exact eq_sub_of_add_eq h_id

  rw [h_eq]
  exact hH1_int.sub hH2_int

/-- Cartan's formula in the zero case `0 < meromorphicOrderAt f 0`. -/
theorem cartan {r : ℝ} {f : ℂ → ℂ}
    (h : MeromorphicOn f ⊤) -- we do not assume AnalyticAt but sContinuousAt
    (h₂ : 0 < meromorphicOrderAt f 0) (hcont : ContinuousAt f 0) :
    characteristic f ⊤ r
      = circleAverage (logCounting f · r) 0 1 + Real.log ‖f 0‖ := by
  classical
  have hf : AnalyticAt ℂ f 0 :=
    analyticAt_of_meromorphicOrderAt_pos (h 0 (by trivial)) hcont h₂
  -- From `0 < meromorphicOrderAt f 0` we know that `f` has a zero at `0`.
  have hf0 : f 0 = 0 := by
    exact (meromorphicOrderAt_pos_iff_zero (hf := hf)).1 h₂
  have hlogf0 : Real.log ‖f 0‖ = 0 := by simp [hf0]
  have hlogplus0 : log⁺ ‖f 0‖ = 0 := by simp [hf0]

  -- First handle the trivial radius `r = 0`.
  by_cases hr : r = 0
  · subst hr
    -- At radius 0, `proximity f ⊤ 0 = log⁺ ‖f 0‖ = 0` and `logCounting f · 0 ≡ 0`,
    -- so both sides are 0.
    simp [characteristic, proximity, Real.circleAverage_zero,
          Real.circleAverage_const, ValueDistribution.logCounting_eval_zero,
          hf0]

  -- Now assume `r ≠ 0`.
  set R : ℝ := r with hRdef
  have hR : R ≠ 0 := by simpa [hRdef] using hr

  -- It suffices to show `characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1`.
  have hR_eq :
      characteristic f ⊤ R =
        circleAverage (logCounting f · R) 0 1 := by
    -- Step 1: write `circleAverage (logCounting f · R)` using `cartan_f1`.
    have h_f2 :
        circleAverage
          (fun a ↦ logCounting f a R
                    + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 =
        circleAverage
          (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
                    + logCounting f ⊤ R) 0 1 := by
      apply circleAverage_congr_sphere
      intro a ha
      simp [cartan_f1 h hR a]
    -- Step 2: split the circle averages using linearity in `a`.
    -- Circle integrability of the counting function (uses specialized lemma).
    have hci_counting : CircleIntegrable (fun a ↦ logCounting f a R) 0 1 :=
      circleIntegrable_logCounting_zero_case h h₂

    -- Circle integrability of the trailing coefficient (uses general lemma).
    have hci_trailing : CircleIntegrable
        (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 :=
      circleIntegrable_log_trailingCoeff h h₂
    have h_left :
        circleAverage (fun a ↦ logCounting f a R
                        + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 =
        circleAverage (logCounting f · R) 0 1
          + circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 := by
      -- This is `circleAverage_add_fun` with real-valued functions.
      simpa [Pi.add_apply] using
        circleAverage_add_fun
          (c := 0) (R := 1)
          (f₁ := fun a ↦ logCounting f a R)
          (f₂ := fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖)
          (hf₁ := hci_counting) (hf₂ := hci_trailing)
    -- The constant function is trivially circle integrable.
    have hci_const : CircleIntegrable (fun _ : ℂ ↦ logCounting f ⊤ R) 0 1 :=
      circleIntegrable_const _ 0 1
    -- The inner circle average function is integrable (proven via Fubini).
    have hci_inner : CircleIntegrable
        (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 :=
      circleIntegrable_circleAverage_log_norm_sub_unit h
    have h_right :
        circleAverage
          (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
                    + logCounting f ⊤ R) 0 1 =
        circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
          + logCounting f ⊤ R := by
      -- Again `circleAverage_add_fun`, with the second term constant in `a`.
      have h_add := circleAverage_add_fun
          (c := 0) (R := 1)
          (f₁ := fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R)
          (f₂ := fun _ ↦ logCounting f ⊤ R)
          (hf₁ := hci_inner) (hf₂ := hci_const)
      simp only at h_add
      rw [h_add, Real.circleAverage_const]
    -- Step 3: combine everything.
    have h_combined :=
      calc
        circleAverage (logCounting f · R) 0 1
          + circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1
            = circleAverage (fun a ↦ logCounting f a R
                      + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 := by
              simp [h_left]
        _ = circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
                      + logCounting f ⊤ R) 0 1 := h_f2
        _ = circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
              + logCounting f ⊤ R := by simp [h_right]
    -- Use `cartan_sigma2` and `cartan_swap_averages` to identify the two pieces.
    have h_trailing :
        circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 = 0 :=
      cartan_sigma2 h h₂
    have h_main :
        circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 =
        circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R :=
      cartan_swap_averages h (cartan_integrability h hR)
    -- Now rewrite `proximity` and `characteristic`.
    have h_char :
        characteristic f ⊤ R =
          circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R + logCounting f ⊤ R := by
      simp [ValueDistribution.characteristic, ValueDistribution.proximity_top]
    -- Put it all together.
    calc
      characteristic f ⊤ R
          = circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R + logCounting f ⊤ R := h_char
      _ = circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
            + logCounting f ⊤ R := by simp [h_main]
      _ = circleAverage (logCounting f · R) 0 1 := by
        -- subtract the trailing coefficient average (which is 0)
        rw [← h_combined]
        simp only [h_trailing, add_zero]

  -- Replace `R` by `r` and add back the constant term.
  have : characteristic f ⊤ r =
      circleAverage (logCounting f · r) 0 1 := by simpa [hRdef] using hR_eq
  simpa [hlogf0] using congrArg (fun t ↦ t + Real.log ‖f 0‖) this
end ValueDistribution
