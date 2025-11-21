-- Mathlib/Analysis/Complex/DeBranges/Basic.lean
import Mathlib
import PrimeNumberTheoremAnd
import StrongPNT
import Mathlib.MeasureTheory.Measure.OpenPos


/-!
# Hermite–Biehler functions and the de Branges measure

This file defines Hermite–Biehler entire functions and the associated de Branges
measure on `ℝ`.  It is intended as infrastructure for the construction of
de Branges spaces.
-/

open Complex Set Topology MeasureTheory
open scoped UpperHalfPlane ENNReal

/-- An entire function `E : ℂ → ℂ` is a Hermite–Biehler function if it satisfies the
strict growth condition `|E (conj z)| < |E z|` for all `z` with `Im z > 0`. -/
structure HermiteBiehlerFunction where
  toFun : ℂ → ℂ
  entire : Differentiable ℂ toFun
  growth_condition : ∀ z : ℂ, 0 < z.im → norm (toFun (Complex.mk z.re (-z.im))) < norm (toFun z)

namespace HermiteBiehlerFunction

instance : CoeFun HermiteBiehlerFunction (fun _ => ℂ → ℂ) := ⟨toFun⟩

@[ext]
lemma ext {E₁ E₂ : HermiteBiehlerFunction} (h : ∀ z, E₁ z = E₂ z) : E₁ = E₂ := by
  cases E₁; cases E₂; congr; exact funext h

lemma continuous (E : HermiteBiehlerFunction) : Continuous E :=
  E.entire.continuous

/-- Hermite–Biehler functions have no zeros in the open upper half-plane. -/
lemma no_upper_zeros (E : HermiteBiehlerFunction) (z : ℂ) (hz : 0 < z.im) :
    E z ≠ 0 := by
  intro hEz
  have h := E.growth_condition z hz
  have : norm (E (Complex.mk z.re (-z.im))) < 0 := by simpa [hEz] using h
  exact (not_lt_of_ge (norm_nonneg _)) this

/-- Hermite–Biehler functions have no zeros on the real line (de Branges, Lemma 10).

The proof is non-trivial and is left as a placeholder.
-/
lemma no_real_zeros (E : HermiteBiehlerFunction) (x : ℝ) : E x ≠ 0 := by
  sorry

variable (E : HermiteBiehlerFunction)

/-! ### The de Branges measure -/

/-- The density function `|E x|⁻²` as an `ENNReal`.  This is the standard format
for use with `Measure.withDensity`. -/
noncomputable def density (x : ℝ) : ENNReal :=
  ENNReal.ofReal (((norm (E x)) ^ 2)⁻¹)

/-- A helper lemma expressing that the real-valued density is continuous.

The actual proof is non-trivial and is left as a placeholder.
-/
private lemma continuous_density_real :
    Continuous fun x : ℝ => ((norm (E x)) ^ 2)⁻¹ := by
  sorry

/-- The density function is measurable. -/
lemma measurable_density : Measurable E.density := by
  -- This follows from `continuous_density_real` together with measurability of `ofReal`.
  sorry

/-- The de Branges measure `μ_E = |E x|⁻² dx` on the real line. -/
noncomputable def measure : Measure ℝ :=
  Measure.withDensity volume E.density

/-- The measure `μ_E` is locally finite. -/
instance : IsLocallyFiniteMeasure E.measure := by
  -- This should follow from local integrability of the density.
  sorry

/-- The de Branges measure has full support on `ℝ`. -/
lemma measure_has_full_support : MeasureTheory.Measure.IsOpenPosMeasure E.measure := by
  -- This should follow from continuity of the density and `no_real_zeros`.
  sorry

end HermiteBiehlerFunction
