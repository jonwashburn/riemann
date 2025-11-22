
-- Mathlib/Analysis/Complex/DeBranges/Basic.lean
import Mathlib
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.OpenPos
import PrimeNumberTheoremAnd
import StrongPNT

/-!
# Hermite–Biehler functions and the de Branges measure

We define de Branges entire functions (satisfying the Hermite–Biehler inequality) and the stricter
class of Hermite–Biehler functions *without real zeros*, together with the associated weight and
measure on `ℝ`. This is intended as infrastructure for the construction of de Branges spaces.

We **only** state results that can be proved from the HB inequality and basic complex/real analysis.
Stronger analytic results (e.g. the equivalence between local finiteness of the measure and absence
of real zeros) are developed in separate files such as `Zeros.lean`.
-/

open Complex Set Topology MeasureTheory
open scoped ENNReal

/-- A de Branges function: entire and satisfying the Hermite–Biehler inequality
\[
  |E(\overline z)| < |E(z)|,\quad \Im z > 0.
\]
We use `star z` for `conj z`. -/
structure DeBrangesFunction where
  toFun : ℂ → ℂ
  entire : Differentiable ℂ toFun
  growth_condition :
    ∀ z : ℂ, 0 < z.im →
      ‖toFun (star z)‖ < ‖toFun z‖

namespace DeBrangesFunction

instance : CoeFun DeBrangesFunction (fun _ => ℂ → ℂ) :=
  ⟨DeBrangesFunction.toFun⟩

@[ext] lemma ext {E₁ E₂ : DeBrangesFunction}
    (h : ∀ z, E₁ z = E₂ z) : E₁ = E₂ := by
  cases E₁; cases E₂
  simp [*]; grind

/-- De Branges functions are continuous on `ℂ`. -/
lemma continuous (E : DeBrangesFunction) : Continuous E :=
  E.entire.continuous

/-- De Branges functions have no zeros in the open upper half-plane. -/
lemma no_upper_zeros (E : DeBrangesFunction) (z : ℂ) (hz : 0 < z.im) :
    E z ≠ 0 := by
  intro hEz
  have h := E.growth_condition z hz
  have : ‖E (Complex.mk z.re (-z.im))‖ < 0 := by simpa [hEz] using h
  exact (not_lt_of_ge (norm_nonneg _)) this

end DeBrangesFunction

/-- A Hermite–Biehler function in the strict de Branges sense:
a de Branges function with no real zeros. -/
structure HermiteBiehlerFunction extends DeBrangesFunction where
  /-- Hermite–Biehler functions have no real zeros by definition. -/
  no_real_zeros : ∀ x : ℝ, toFun x ≠ 0

namespace HermiteBiehlerFunction

instance : CoeFun HermiteBiehlerFunction (fun _ => ℂ → ℂ) :=
  ⟨fun E => E.toDeBrangesFunction.toFun⟩

@[ext] lemma ext {E₁ E₂ : HermiteBiehlerFunction}
    (h : ∀ z, E₁ z = E₂ z) : E₁ = E₂ := by
  cases E₁; cases E₂
  simp [*]; aesop

/-- Hermite–Biehler functions are entire on `ℂ`. -/
lemma entire' (E : HermiteBiehlerFunction) : Differentiable ℂ E :=
  E.toDeBrangesFunction.entire

/-- Hermite–Biehler functions are continuous on `ℂ`. -/
lemma continuous (E : HermiteBiehlerFunction) : Continuous E :=
  E.entire.continuous

/-- Hermite–Biehler functions have no zeros in the open upper half-plane. -/
lemma no_upper_zeros (E : HermiteBiehlerFunction) (z : ℂ) (hz : 0 < z.im) :
    E z ≠ 0 :=
  E.toDeBrangesFunction.no_upper_zeros z hz

/-- Hermite–Biehler functions have no real zeros. (By structure field.) -/
lemma no_real_zeros' (E : HermiteBiehlerFunction) (x : ℝ) : E x ≠ 0 :=
  E.no_real_zeros x

variable (E : HermiteBiehlerFunction)

/-! ### The de Branges weight and measure -/

/-- The (non-negative) *weight function* `w_E(x) = |E(x)|⁻²` on `ℝ`, viewed in `ℝ`. -/
noncomputable def weight (x : ℝ) : ℝ :=
  (‖E x‖ ^ 2)⁻¹

/-- The de Branges *density* `|E x|⁻²` as an `ENNReal`-valued function on `ℝ`,
suitable for use with `Measure.withDensity`. -/
noncomputable def density (x : ℝ) : ENNReal :=
  ENNReal.ofReal (E.weight x)

/-- The weight function is measurable (in fact continuous; see below). -/
lemma measurable_weight : Measurable E.weight := by
  -- `x ↦ E x` is continuous, hence measurable.
  have hE : Measurable fun x : ℝ => E x :=
    (E.continuous.comp continuous_ofReal).measurable
  -- `x ↦ ‖E x‖` is measurable, so are powers and inverses.
  have h_norm : Measurable fun x : ℝ => ‖E x‖ :=
    (continuous_norm.comp (E.continuous.comp continuous_ofReal)).measurable
  have h_pow : Measurable fun x : ℝ => ‖E x‖ ^ 2 :=
    h_norm.pow_const 2
  have h_inv : Measurable fun x : ℝ => (‖E x‖ ^ 2)⁻¹ :=
    h_pow.inv
  exact h_inv

/-- The de Branges density is measurable as an `ENNReal`-valued function. -/
lemma measurable_density : Measurable E.density := by
  -- `ENNReal.ofReal` is measurable, so we can compose it with `weight`.
  have h := E.measurable_weight
  exact ENNReal.measurable_ofReal.comp h

/-- The de Branges measure `μ_E = |E x|⁻² dx` on the real line.

We build it as a density with respect to Lebesgue measure. -/
noncomputable def measure : Measure ℝ :=
  Measure.withDensity volume E.density

/-
At this point we *do not* assert additional properties such as:

* `IsLocallyFiniteMeasure E.measure`
* `Measure.IsOpenPosMeasure E.measure`

These are expected to hold for Hermite–Biehler functions, but their proofs
require substantial analysis (control of zeros on `ℝ`, growth estimates
on compact sets, and continuity/positivity of the weight). They are
developed in `Measure.lean` and `Zeros.lean`.
-/

end HermiteBiehlerFunction
