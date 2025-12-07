
import Mathlib
import Riemann.Mathlib.MeasureTheory.Function.LpMono

/-!
# Integrability of Bounded Functions with Finite-Measure Support

This file provides lemmas for showing that bounded functions with finite-measure
support are integrable. This is fundamental for H¹ atomic decomposition theory.

## Main Results

* `Integrable.of_bdd_support`: A bounded function supported on a finite-measure set is integrable.
* `Integrable.of_bdd_closedBall`: A bounded function supported on a closed ball is integrable.
* `integral_le_of_bdd_support`: Integral bound for bounded functions on finite measure sets.

## Implementation Notes

These lemmas are designed for upstream inclusion into Mathlib. They follow the convention
that integrability can be established from:
1. A pointwise bound `|f x| ≤ M` for all `x`
2. Support contained in a set `S` with `μ S < ⊤`
3. AEStronglyMeasurable `f`

## Tags

integrable, bounded support, finite measure, H¹ atoms
-/

open MeasureTheory Measure Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section BoundedSupport

omit [NormedSpace ℝ E] in
/-- A bounded function with finite-measure support is integrable.

This is the key lemma for showing H¹ atoms are integrable.
We reduce it to the `L^p` lemma `Memℒp.of_bdd_support` with `p = 1`. -/
theorem Integrable.of_bdd_support {f : α → E} {M : ℝ} {S : Set α}
    (hM : ∀ x, ‖f x‖ ≤ M) (hM_pos : 0 ≤ M)
    (hsupp : Function.support f ⊆ S) (hS : μ S < ⊤)
    (hmeas : AEStronglyMeasurable f μ) : Integrable f μ := by
  -- First put `f` in `ℒ^1`
  have hLp : MemLp f (1 : ℝ≥0∞) μ :=
    Memℒp.of_bdd_support (hp := by simp) (hp_top := by simp)
      hM hM_pos hsupp hS hmeas
  -- Then use the standard equivalence `MemLp f 1 μ ↔ Integrable f μ`
  exact (memLp_one_iff_integrable (μ := μ) (f := f)).mp hLp

/-- A bounded real-valued function with finite-measure support is integrable.

Special case of `Integrable.of_bdd_support` for real-valued functions using absolute value. -/
theorem Integrable.of_bdd_support_real {f : α → ℝ} {M : ℝ} {S : Set α}
    (hM : ∀ x, |f x| ≤ M) (hM_pos : 0 ≤ M)
    (hsupp : Function.support f ⊆ S) (hS : μ S < ⊤)
    (hmeas : AEStronglyMeasurable f μ) : Integrable f μ := by
  apply Integrable.of_bdd_support (M := M) hM hM_pos hsupp hS hmeas

omit [NormedSpace ℝ E] in
/-- A bounded function supported on a closed ball is integrable.

This is particularly useful for H¹ atoms which are supported on balls. -/
  theorem Integrable.of_bdd_closedBall {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    [ProperSpace X] [BorelSpace X] {μ' : Measure X} [IsFiniteMeasureOnCompacts μ']
    {f : X → E} {M : ℝ} {x₀ : X} {r : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (hM_pos : 0 ≤ M)
    (hsupp : Function.support f ⊆ Metric.closedBall x₀ r)
    (hmeas : AEStronglyMeasurable f μ') : Integrable f μ' := by
  apply Integrable.of_bdd_support hM hM_pos hsupp _ hmeas
  exact (isCompact_closedBall x₀ r).measure_lt_top

/-- Integral bound for bounded functions with finite-measure support.

If `|f x| ≤ M` for all `x ∈ S` and `support f ⊆ S`, then `∫ |f| ∂μ ≤ M * μ(S)`. -/
theorem integral_le_of_bdd_support {f : α → ℝ} {M : ℝ} {S : Set α}
    (hM : ∀ x ∈ S, |f x| ≤ M) (_ : 0 ≤ M)
    (hS_meas : MeasurableSet S) (hS : μ S < ⊤)
    (hsupp : Function.support f ⊆ S)
    (hf : Integrable f μ) :
    ∫ x, |f x| ∂μ ≤ M * (μ S).toReal := by
  have h1 : ∫ x, |f x| ∂μ = ∫ x in S, |f x| ∂μ + ∫ x in Sᶜ, |f x| ∂μ := by
    rw [← integral_add_compl hS_meas hf.abs]
  have h2 : ∫ x in Sᶜ, |f x| ∂μ = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    simp only [mem_compl_iff] at hx
    have : x ∉ Function.support f := fun h => hx (hsupp h)
    simp only [Function.mem_support, ne_eq, not_not] at this
    simp [this]
  rw [h1, h2, add_zero]
  calc ∫ x in S, |f x| ∂μ
      ≤ ∫ _x in S, M ∂μ := by
        have hconst : IntegrableOn (fun _ : α => M) S μ :=
          integrableOn_const (μ := μ) (s := S) (C := M) (hs := hS.ne) (hC := by simp)
        apply setIntegral_mono_on hf.abs.integrableOn hconst hS_meas
        intro x hx; exact hM x hx
    _ = M * (μ S).toReal := by rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl

/-- `L^∞` norm bound implies integral bound on finite measure sets, assuming the essential
supremum is finite. -/
theorem integral_le_essSup_mul_measure {f : α → ℝ} {S : Set α}
    (_ : MeasurableSet S) (hS : μ S < ⊤)
    (hf : Integrable f μ)
    (hess : essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ ≠ ⊤) :
    ∫ x in S, |f x| ∂μ ≤ (essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).toReal * (μ S).toReal := by
  have hconst : IntegrableOn (fun _ : α => (essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).toReal) S μ :=
    integrableOn_const (μ := μ) (s := S) (C := (essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).toReal)
      (hs := hS.ne) (hC := by
        -- show the constant has finite norm
        aesop)
  calc ∫ x in S, |f x| ∂μ
      ≤ ∫ _x in S, (essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).toReal ∂μ := by
        apply setIntegral_mono_ae hf.abs.integrableOn hconst
        -- use a.e. bound from essSup
        have hae :
            ∀ᵐ x ∂μ, (‖f x‖₊ : ℝ≥0∞) ≤
              essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ :=
          ae_le_essSup (μ := μ) (f := fun x => (‖f x‖₊ : ℝ≥0∞))
        filter_upwards [hae] with x hx
        have hx' : (‖f x‖₊ : ℝ) ≤ (essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).toReal :=
          ENNReal.toReal_mono hess hx
        have hx_abs : |f x| = (‖f x‖₊ : ℝ) := by
          simp [Real.norm_eq_abs]
        -- rewrite the goal using the bound in ℝ≥0∞
        calc
          |f x| = (‖f x‖₊ : ℝ) := hx_abs
          _ ≤ (essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).toReal := hx'
    _ = (essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).toReal * (μ S).toReal := by
        have hμfin : μ S ≠ ∞ := hS.ne
        have hreal : μ.real S = (μ S).toReal := by
          -- `μ.real` is the real-valued measure; finite gives `(μ S).toReal`
          simp [Measure.real]
        rw [setIntegral_const, smul_eq_mul, mul_comm, hreal]

end BoundedSupport

section ZeroIntegral

/-- A bounded function with finite-measure support and zero integral is in H¹.

This combines the support condition with the cancellation condition for atoms. -/
theorem norm_integral_le_of_bdd_support {f : α → ℝ} {M : ℝ} {S : Set α}
    (hM : ∀ x, |f x| ≤ M) (hM_pos : 0 ≤ M)
    (hsupp : Function.support f ⊆ S) (hS_meas : MeasurableSet S) (hS : μ S < ⊤)
    (hf : Integrable f μ) :
    ‖∫ x, f x ∂μ‖ ≤ M * (μ S).toReal := by
  calc ‖∫ x, f x ∂μ‖
      ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
    _ = ∫ x, |f x| ∂μ := by congr 1
    _ ≤ M * (μ S).toReal :=
        integral_le_of_bdd_support (fun x _ => hM x) hM_pos hS_meas hS hsupp hf

end ZeroIntegral

end MeasureTheory
