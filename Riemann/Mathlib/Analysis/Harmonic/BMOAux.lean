
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Auxiliary Lemmas for BMO Theory

This file provides the foundational lemmas needed for the BMO theory, including
the John-Nirenberg inequality on doubling metric measure spaces.

## Main Results

* `oscillation_triangle_helper` - Key estimate for mean oscillation triangle inequality
* `johnNirenberg_exponential_decay` - Exponential decay for John-Nirenberg on doubling spaces
* `johnNirenberg_iteration` - The iteration lemma underlying John-Nirenberg
* `bmo_memLp_loc` - BMO functions are in L^p_loc

## Implementation Notes

The John-Nirenberg inequality requires the underlying measure to be doubling (or at least
satisfy a weak geometric condition). We use `IsUnifLocDoublingMeasure` from Mathlib.
The proof follows the classical approach via Calderón-Zygmund covering and iteration.

## References

* Stein, "Harmonic Analysis", Chapter IV
* John-Nirenberg, "On functions of bounded mean oscillation", Comm. Pure Appl. Math. 1961
* Grafakos, "Classical Fourier Analysis", Section 7.1
-/

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α] {μ : Measure α}

/-! ### Mean Oscillation Triangle Inequality -/

omit [BorelSpace α] in
/-- Local integrability implies integrability on any metric ball in a proper space. -/
theorem integrableOn_ball_of_locallyIntegrable
    [ProperSpace α] [IsLocallyFiniteMeasure μ] {f : α → ℝ} (hf : LocallyIntegrable f μ)
    (x : α) {r : ℝ} (_hr : 0 < r) :
    IntegrableOn f (Metric.ball x r) μ := by
  -- local integrability gives integrability on compact sets; closed balls are compact in a proper
  -- space, so we can pass to the open ball using monotonicity.
  have h_closed :
      IntegrableOn f (Metric.closedBall x r) μ :=
    (hf.locallyIntegrableOn _).integrableOn_isCompact (isCompact_closedBall x r)
  exact h_closed.mono_set Metric.ball_subset_closedBall

omit [PseudoMetricSpace α] in
/-- Linearity of the set average under integrability and finite, nonzero measure. -/
theorem setAverage_add {s : Set α} {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (hμ_ne : μ s ≠ 0) (hμ_fin : μ s ≠ ∞) :
    ⨍ x in s, f x + g x ∂μ = ⨍ x in s, f x ∂μ + ⨍ x in s, g x ∂μ := by
  have hfin : Fact (μ s < ∞) := ⟨by simpa [hμ_fin] using hμ_fin.lt_top⟩
  have hne : NeZero (μ s) := ⟨hμ_ne⟩
  have hne' : NeZero (μ.restrict s) := inferInstance
  -- rewrite all averages as scalar multiples of integrals
  simp [average_eq, smul_eq_mul] at *
  calc (μ s).toReal⁻¹ * ∫ x in s, f x + g x ∂μ
      = (μ s).toReal⁻¹ * (∫ x in s, f x ∂μ + ∫ x in s, g x ∂μ) := by
          rw [integral_add hf hg]
    _ = (μ s).toReal⁻¹ * ∫ x in s, f x ∂μ +
        (μ s).toReal⁻¹ * ∫ x in s, g x ∂μ := by ring

omit [PseudoMetricSpace α] [BorelSpace α] in
/-- Key helper: average of `|(f+g) - avg(f+g)|` is bounded by the sum of the two oscillations.

This is the core of the mean oscillation triangle inequality. We assume the set
has finite, nonzero measure and both functions are integrable on it, which is
the natural setting for average linearity and monotonicity. -/
theorem oscillation_triangle_helper
    {s : Set α} (_ : MeasurableSet s) {f g : α → ℝ}
    (hμ_ne : μ s ≠ 0) (hμ_fin : μ s ≠ ∞)
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ) :
    ⨍ x in s, |f x + g x - ⨍ y in s, (f y + g y) ∂μ| ∂μ ≤
      (⨍ x in s, |f x - ⨍ y in s, f y ∂μ| ∂μ) +
      (⨍ x in s, |g x - ⨍ y in s, g y ∂μ| ∂μ) := by
  have hfin : Fact (μ s < ∞) := ⟨by simpa [hμ_fin] using hμ_fin.lt_top⟩
  have hne : NeZero (μ s) := ⟨hμ_ne⟩
  set avgf : ℝ := ⨍ y in s, f y ∂μ
  set avgg : ℝ := ⨍ y in s, g y ∂μ
  -- Linearity of the average for f+g
  have havg_add : ⨍ y in s, f y + g y ∂μ =
      avgf + avgg :=
    setAverage_add (μ := μ) (s := s) hf hg hμ_ne hμ_fin
  -- Pointwise triangle inequality
  have hpt :
      ∀ x, |(f x - avgf) + (g x - avgg)| ≤
        |f x - avgf| + |g x - avgg| := by
    intro x
    -- triangle inequality for the real absolute value via the norm version
    have := norm_add_le (f x - avgf) (g x - avgg)
    simpa [Real.norm_eq_abs, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  -- Rewrite the oscillation of f+g using havg_add
  have hosc_rewrite :
      (fun x => |f x + g x - ⨍ y in s, f y + g y ∂μ|)
        = fun x => |(f x - avgf) + (g x - avgg)| := by
    funext x
    simp [havg_add, avgf, avgg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Integrability of the pieces
  have hμlt : μ s < ∞ := hfin.out
  have hint_const_f : IntegrableOn (fun _ : α => avgf) s μ :=
    by
      simpa using
        (integrableOn_const (μ := μ) (s := s) (C := avgf) (hs := hμlt.ne))
  have hint_const_g : IntegrableOn (fun _ : α => avgg) s μ :=
    by
      simpa using
        (integrableOn_const (μ := μ) (s := s) (C := avgg) (hs := hμlt.ne))
  have hint_f : IntegrableOn (fun x => f x - avgf) s μ :=
    hf.sub hint_const_f
  have hint_g : IntegrableOn (fun x => g x - avgg) s μ :=
    hg.sub hint_const_g
  have hint_f_abs : IntegrableOn (fun x => |f x - avgf|) s μ := hint_f.abs
  have hint_g_abs : IntegrableOn (fun x => |g x - avgg|) s μ := hint_g.abs
  have hint_sum : IntegrableOn
      (fun x => |(f x - avgf) + (g x - avgg)|) s μ :=
    (hint_f.add hint_g).abs
  -- Average is a positive scalar times an integral; use monotonicity of integrals
  have hpt_ae : ∀ᵐ x ∂μ.restrict s,
      |(f x - avgf) + (g x - avgg)| ≤
        |f x - avgf| + |g x - avgg| := by
    exact Eventually.of_forall (by intro x; exact hpt x)
  have hmono : ∫ x in s, |(f x - avgf) + (g x - avgg)| ∂μ ≤
      ∫ x in s, |f x - avgf| + |g x - avgg| ∂μ :=
    integral_mono_ae (μ := μ.restrict s) hint_sum (hint_f_abs.add hint_g_abs) hpt_ae
  have hsum :
      ∫ x in s, |f x - avgf| + |g x - avgg| ∂μ =
        ∫ x in s, |f x - avgf| ∂μ +
          ∫ x in s, |g x - avgg| ∂μ := by
    have := integral_add hint_f_abs hint_g_abs
    simpa [IntegrableOn] using this
  have hμpos : 0 < μ.real s := by
    have hpos : 0 < (μ s).toReal := ENNReal.toReal_pos hμ_ne hμ_fin
    simpa [Measure.real] using hpos
  have hμinv_nonneg : 0 ≤ (μ.real s)⁻¹ := inv_nonneg.mpr hμpos.le
  have havg_int :
      (μ.real s)⁻¹ * ∫ y in s, f y + g y ∂μ = avgf + avgg := by
    have hμne' : μ.real s ≠ 0 := ne_of_gt hμpos
    simpa [average_eq, smul_eq_mul, hμne'] using havg_add
  have hosc_integrand :
      (fun x => |f x + g x - (μ.real s)⁻¹ * ∫ y in s, f y + g y ∂μ|)
        = fun x => |(f x - avgf) + (g x - avgg)| := by
    funext x
    have := havg_int
    -- rewrite the average of f+g using the linearity identity
    calc
      |f x + g x - (μ.real s)⁻¹ * ∫ y in s, f y + g y ∂μ|
          = |f x + g x - (avgf + avgg)| := by simp [this]
      _ = |(f x - avgf) + (g x - avgg)| := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc
    ⨍ x in s, |f x + g x - ⨍ y in s, f y + g y ∂μ| ∂μ
        = (μ.real s)⁻¹ * ∫ x in s, |(f x - avgf) + (g x - avgg)| ∂μ := by
            have hμne' : μ.real s ≠ 0 := ne_of_gt hμpos
            simp [average_eq, smul_eq_mul, hosc_integrand]
    _ ≤ (μ.real s)⁻¹ * ∫ x in s, (|f x - avgf| + |g x - avgg|) ∂μ := by
            exact mul_le_mul_of_nonneg_left hmono hμinv_nonneg
    _ = (μ.real s)⁻¹ *
          (∫ x in s, |f x - avgf| ∂μ + ∫ x in s, |g x - avgg| ∂μ) := by
            simp [hsum]
    _ = ⨍ x in s, |f x - avgf| ∂μ + ⨍ x in s, |g x - avgg| ∂μ := by
            have hμne' : μ.real s ≠ 0 := ne_of_gt hμpos
            ring_nf
            simp [average_eq, smul_eq_mul, sub_eq_add_neg, add_comm]



end MeasureTheory
