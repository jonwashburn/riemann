/-
# Li coefficients and Li criterion (Route 3 skeleton)

This file records (as Lean-typed statements) the Li-criterion gate for RH and
its relationship to the explicit-formula/Weil gate.

Analytic convergence and the “sum over zeros” identity are intentionally
packaged as assumptions.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
import RiemannRecognitionGeometry.ExplicitFormula.Lagarias

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace
open ComplexConjugate

/--
A Li-criterion package (Li 1997; Lagarias 2007, Thm 6.5), layered on top of a
Lagarias explicit-formula framework.

We take Li coefficients `λ n` as real numbers (as in the criterion), and record
`RH ↔ (∀n≥1, λ n ≥ 0)`.

Further identities (sum over zeros, and the Bombieri–Lagarias realization as a
Weil functional) are represented as explicit fields, but kept abstract.
-/
structure LiFramework (F : Type) [TestSpace F] extends LagariasFramework F where
  /-- Li coefficients `λₙ` (real). -/
  lambda : ℕ → ℝ

  /-- Li criterion (Lagarias 2007, Thm 6.5): `RH ↔ ∀ n≥1, λₙ ≥ 0`. -/
  liCriterion : RiemannHypothesis ↔ (∀ n : ℕ, 1 ≤ n → 0 ≤ lambda n)

  /-- Optional: record the (symmetric) sum-over-zeros formula as a named assumption. -/
  sumOverZerosFormula : Prop

  /-- Optional: record the Bombieri–Lagarias/Lagarias realization `λₙ = W¹(φₙ * \widetilde{\bar φₙ})`.
      This typically requires extending the test-function class beyond compact support. -/
  lambdaAsWeil : Prop

/-!
## The local RH → termwise nonnegativity step (Li)

The (symmetric) sum-over-zeros formula for Li coefficients is

`λₙ = ∑_ρ (1 - (1 - 1/ρ)^n)`,

with a specific convergence convention (Lagarias §6.3). Under **RH**, each nontrivial zero `ρ`
satisfies `ρ.re = 1/2`, and then the factor `z := 1 - 1/ρ` lies on the unit circle (`abs z = 1`).
Consequently,

`Re(1 - z^n) = 1 - Re(z^n) ≥ 0`.

The lemmas below formalize exactly this *local* inequality. Upgrading it to
`RH → (∀n≥1, λₙ ≥ 0)` requires (and is essentially equivalent to) the analytic
sum-over-zeros identity plus the justification for exchanging `Re` with the symmetric sum.
-/

namespace LiAux

/-- The basic Li summand `1 - (1 - 1/ρ)^n`. -/
def liTerm (n : ℕ) (ρ : ℂ) : ℂ :=
  (1 : ℂ) - (1 - 1 / ρ) ^ n

lemma normSq_sub_one_eq_normSq_of_re_eq_half {ρ : ℂ} (hρ : ρ.re = (1 / 2 : ℝ)) :
    Complex.normSq (ρ - 1) = Complex.normSq ρ := by
  simp [Complex.normSq_apply, hρ]
  ring

lemma abs_one_sub_inv_eq_one {ρ : ℂ} (hρ : ρ.re = (1 / 2 : ℝ)) (hρ0 : ρ ≠ 0) :
    norm (1 - 1 / ρ) = 1 := by
  have hrew : (1 - ρ⁻¹) = (ρ - 1) * ρ⁻¹ := by
    simp [sub_eq_add_neg, add_mul, hρ0]
  have hns : Complex.normSq ρ ≠ 0 := by
    intro h0
    have : ρ = 0 := (Complex.normSq_eq_zero).1 h0
    exact hρ0 this
  have hn : Complex.normSq (1 - ρ⁻¹) = 1 := by
    calc
      Complex.normSq (1 - ρ⁻¹)
          = Complex.normSq ((ρ - 1) * ρ⁻¹) := by simp [hrew]
      _ = Complex.normSq (ρ - 1) * Complex.normSq (ρ⁻¹) := by
            simp
      _ = Complex.normSq (ρ - 1) * (Complex.normSq ρ)⁻¹ := by
            simp
      _ = Complex.normSq ρ * (Complex.normSq ρ)⁻¹ := by
            simp [normSq_sub_one_eq_normSq_of_re_eq_half (ρ := ρ) hρ]
      _ = 1 := by
            simp [hns]
  simp [div_eq_mul_inv, norm, hn]

lemma re_one_sub_pow_nonneg_of_abs_eq_one (z : ℂ) (n : ℕ) (hz : norm z = 1) :
    0 ≤ ((1 : ℂ) - z ^ n).re := by
  have h1 : ((1 : ℂ) - z ^ n).re = (1 : ℝ) - (z ^ n).re := by simp
  have hre : (z ^ n).re ≤ norm (z ^ n) := by exact Complex.re_le_norm (z ^ n)
  have habs : norm (z ^ n) = 1 := by
    simp [hz]
  have hre1 : (z ^ n).re ≤ (1 : ℝ) := by simpa [habs] using hre
  have : 0 ≤ (1 : ℝ) - (z ^ n).re := sub_nonneg.mpr hre1
  simpa [h1] using this

lemma liTerm_re_nonneg_of_re_eq_half {ρ : ℂ} (n : ℕ)
    (hρ : ρ.re = (1 / 2 : ℝ)) (hρ0 : ρ ≠ 0) :
    0 ≤ (liTerm n ρ).re := by
  have hz : norm (1 - 1 / ρ) = 1 := abs_one_sub_inv_eq_one (ρ := ρ) hρ hρ0
  simpa [liTerm] using (re_one_sub_pow_nonneg_of_abs_eq_one (z := (1 - 1 / ρ)) n hz)

end LiAux

namespace LiFramework

variable {F : Type} [TestSpace F] (L : LiFramework F)

/-- `LiGate`: the countable positivity hypothesis `∀ n≥1, λₙ ≥ 0`. -/
def LiGate : Prop := ∀ n : ℕ, 1 ≤ n → 0 ≤ L.lambda n

end LiFramework

end ExplicitFormula
end RiemannRecognitionGeometry
