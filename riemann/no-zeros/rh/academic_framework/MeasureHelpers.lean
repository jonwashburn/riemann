import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral

/-
Shared measure helpers for interval-based integrals.

Contents:
- Finite-volume facts for real intervals
- Constant-function integrability on intervals
- Small simp rewrites for restricted measures on intervals
-/

namespace RH
namespace AcademicFramework
namespace MeasureHelpers

open Set MeasureTheory
open scoped MeasureTheory ENNReal

/-- Lebesgue measure of a closed interval is finite. -/
lemma volume_Icc_lt_top (a b : ℝ) : volume (Icc a b) < ∞ := by
  -- Reduce to the ordered interval `[min a b, max a b]`
  have hsub : Icc a b ⊆ Icc (min a b) (max a b) := by
    intro x hx
    refine And.intro ?h1 ?h2
    · exact le_trans (min_le_left _ _) hx.left
    · exact le_trans hx.right (le_max_right _ _)
  -- The ordered interval has explicit finite volume
  have hle : min a b ≤ max a b := min_le_max
  have hΔ : 0 ≤ max a b - min a b := sub_nonneg.mpr hle
  have hfin : volume (Icc (min a b) (max a b)) < ∞ := by
    simpa [Real.volume_Icc, hle, hΔ]
  exact lt_of_le_of_lt (measure_mono hsub) hfin

/-- Lebesgue measure of a half‑open bounded interval is finite. -/
lemma volume_Ioc_lt_top (a b : ℝ) : volume (Ioc a b) < ∞ := by
  -- `Ioc a b ⊆ Icc (min a b) (max a b)` so it is bounded by a finite measure
  have hsub : Ioc a b ⊆ Icc (min a b) (max a b) := by
    intro x hx
    refine And.intro ?h1 ?h2
    · exact le_trans (min_le_left _ _) (le_of_lt hx.left)
    · exact le_trans hx.right (le_max_right _ _)
  exact lt_of_le_of_lt (measure_mono hsub) (volume_Icc_lt_top (min a b) (max a b))

/-- Constant functions are integrable on `Icc a b` for Lebesgue measure. -/
lemma integrableOn_const_Icc (a b c : ℝ) :
  IntegrableOn (fun _ : ℝ => c) (Icc a b) volume :=
by
  simpa using (integrableOn_const.2 ⟨measurableSet_Icc, volume_Icc_lt_top a b⟩)

/-- Constant functions are integrable on `Ioc a b` for Lebesgue measure. -/
lemma integrableOn_const_Ioc (a b c : ℝ) :
  IntegrableOn (fun _ : ℝ => c) (Ioc a b) volume :=
by
  simpa using (integrableOn_const.2 ⟨measurableSet_Ioc, volume_Ioc_lt_top a b⟩)

/-
Project-friendly aliases

These names are used across Cert/RS modules to avoid repeating ad-hoc
finiteness and integrability proofs on bounded real intervals.
-/

/-- Alias: finite volume on a closed interval. -/
lemma volume_interval_finite (a b : ℝ) : volume (Icc a b) < ∞ :=
  volume_Icc_lt_top a b

/-- Alias: finite volume on a half‑open interval. -/
lemma volume_interval_finite_Ioc (a b : ℝ) : volume (Ioc a b) < ∞ :=
  volume_Ioc_lt_top a b

/-- Alias: constant integrable on a closed interval. -/
lemma integrableOn_const_interval (a b c : ℝ) :
  IntegrableOn (fun _ : ℝ => c) (Icc a b) volume :=
  integrableOn_const_Icc a b c

/-- Alias: constant integrable on a half‑open interval. -/
lemma integrableOn_const_interval_Ioc (a b c : ℝ) :
  IntegrableOn (fun _ : ℝ => c) (Ioc a b) volume :=
  integrableOn_const_Ioc a b c

/-- Convenience: rewrite `Measure.restrict` on intervals (definitional). -/
@[simp] lemma restrict_Icc (μ : Measure ℝ) (a b : ℝ) :
  Measure.restrict μ (Icc a b) = μ.restrict (Icc a b) := rfl

/-- Convenience: rewrite `Measure.restrict` on intervals (definitional). -/
@[simp] lemma restrict_Ioc (μ : Measure ℝ) (a b : ℝ) :
  Measure.restrict μ (Ioc a b) = μ.restrict (Ioc a b) := rfl

end MeasureHelpers
end AcademicFramework
end RH
