/-
Consistency smoke test (guardrail).

This file intentionally imports **no project axioms** (in particular, it does NOT
import `RiemannRecognitionGeometry.Axioms` or `RiemannRecognitionGeometry.Conjectures`).

It proves basic facts about Lebesgue set integrals on nontrivial intervals which
would immediately contradict any axiom of the form

  `∀ integrand, |∫ t in I, integrand t| ≤ C`

for a positive-length interval `I`.
-/

import RiemannRecognitionGeometry.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

noncomputable section

open Real Complex Set MeasureTheory
open scoped BigOperators MeasureTheory

namespace RiemannRecognitionGeometry

namespace ConsistencySmokeTest

/-- Set integral of a constant over `Icc a b` (assuming `a < b`). -/
theorem setIntegral_const_Icc (a b c : ℝ) (hab : a < b) :
    (∫ _ in Set.Icc a b, c) = c * (b - a) := by
  have h_len_pos : 0 < b - a := sub_pos.mpr hab
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, Real.volume_Icc]
  simp [ENNReal.toReal_ofReal (le_of_lt h_len_pos)]
  ring

/-- For a Whitney interval `I = [t0-len, t0+len]`, the integral of `1` is `2*len`. -/
theorem setIntegral_one_whitney (I : WhitneyInterval) :
    (∫ _ in I.interval, (1 : ℝ)) = 2 * I.len := by
  have hab : I.t0 - I.len < I.t0 + I.len := by
    linarith [I.len_pos]
  -- Reduce to the `Icc` computation.
  have h1 :
      (∫ _ in I.interval, (1 : ℝ)) = (1 : ℝ) * ((I.t0 + I.len) - (I.t0 - I.len)) := by
    simpa [WhitneyInterval.interval] using
      (setIntegral_const_Icc (a := I.t0 - I.len) (b := I.t0 + I.len) (c := (1 : ℝ)) hab)
  -- Simplify the endpoint difference.
  simpa using (by
    -- `h1` already gives the desired integral; just rewrite the RHS.
    simpa [h1] using (by
      -- Rewriting `((t0+len) - (t0-len))` to `2*len`.
      have : (1 : ℝ) * ((I.t0 + I.len) - (I.t0 - I.len)) = 2 * I.len := by ring
      simpa [this] using h1))

/-- There exist bounded integrands on `I.interval` whose integral is arbitrarily large.

This is a simple witness that rules out “uniform bound for all integrands” style axioms.
-/
theorem exists_large_whitney_integral (I : WhitneyInterval) :
    ∀ R : ℝ, ∃ c : ℝ, |∫ _ in I.interval, (c : ℝ)| ≥ R := by
  intro R
  -- Use a large positive constant function.
  have hlen_pos : 0 < I.len := I.len_pos
  have hmeas_pos : 0 < (2 * I.len) := by linarith
  -- Pick c so that c * (2*len) ≥ R.
  refine ⟨R / (2 * I.len), ?_⟩
  have hab : I.t0 - I.len < I.t0 + I.len := by
    linarith [I.len_pos]
  have hconst : (∫ _ in I.interval, (R / (2 * I.len) : ℝ)) = (R / (2 * I.len)) * (2 * I.len) := by
    -- Compute as a constant integral over `Icc`.
    have :=
      setIntegral_const_Icc (a := I.t0 - I.len) (b := I.t0 + I.len) (c := (R / (2 * I.len) : ℝ)) hab
    simpa [WhitneyInterval.interval] using this
  -- Now simplify and compare.
  have hge : |(R / (2 * I.len)) * (2 * I.len)| ≥ R := by
    have hne : (2 * I.len) ≠ 0 := ne_of_gt hmeas_pos
    -- Since `2*len > 0`, the product is exactly `R`.
    have : (R / (2 * I.len)) * (2 * I.len) = R := by
      field_simp [hne]
    simpa [this]
  simpa [hconst] using hge

end ConsistencySmokeTest

end RiemannRecognitionGeometry
