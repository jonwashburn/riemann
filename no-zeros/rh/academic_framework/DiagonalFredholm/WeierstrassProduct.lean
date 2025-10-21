import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
Minimal DF–WP helpers (no axioms):
- `tprod_exp_of_summable` and `exp_tsum_eq_tprod` to pass between sums and products
- `eulerFactor_as_exp_log` to rewrite the modified Euler factor as a single exponential
- `norm_log_one_sub_le_of_lt_one` bound specialized for `log(1 - z)`
-/

namespace RH.AcademicFramework.DiagonalFredholm

noncomputable section

open Complex
open scoped BigOperators Topology

/-- Exponential turns sums into products (modern route).
If `a` is summable, then `∏ exp (a i) = exp (∑ a i)` and the product is `Multipliable`. -/
lemma tprod_exp_of_summable {ι : Type*} [Countable ι]
    (a : ι → ℂ) (hsum : Summable a) :
    Multipliable (fun i => Complex.exp (a i)) ∧
      (∏' i, Complex.exp (a i)) = Complex.exp (∑' i, a i) := by
  have hsum' : HasSum a (∑' i, a i) := hsum.hasSum
  have hprod : HasProd (fun i => Complex.exp (a i)) (Complex.exp (∑' i, a i)) := by
    simpa [Function.comp] using hsum'.cexp
  exact ⟨hprod.multipliable, hprod.tprod_eq⟩

/-- Weierstrass-type bridge: from a summable log to a product identity.
If `f i ≠ 0` and `∑ log (f i)` converges, then `exp (∑ log (f i)) = ∏ f i`. -/
lemma exp_tsum_eq_tprod {ι : Type*} [Countable ι]
    (f : ι → ℂ) (hne : ∀ i, f i ≠ 0)
    (hlog : Summable (fun i => Complex.log (f i))) :
    Complex.exp (∑' i, Complex.log (f i)) = ∏' i, f i := by
  have hprod : HasProd (fun i => Complex.exp (Complex.log (f i)))
      (Complex.exp (∑' i, Complex.log (f i))) := (hlog.hasSum).cexp
  calc
    Complex.exp (∑' i, Complex.log (f i))
        = ∏' i, Complex.exp (Complex.log (f i)) := by
          simpa using (hprod.tprod_eq.symm)
    _ = ∏' i, f i := by
      simp [Complex.exp_log (hne _)]

/-- For `‖z‖ < 1`, the modified Euler factor `(1 - z) * exp(z + z^2/2)`
can be written as a single exponential `exp(log(1 - z) + z + z^2/2)`. -/
lemma eulerFactor_as_exp_log (z : ℂ) (hz : ‖z‖ < (1 : ℝ)) :
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
      = Complex.exp (Complex.log (1 - z) + z + z ^ 2 / 2) := by
  have hne : 1 - z ≠ 0 := by
    intro h
    have : z = 1 := by
      have : 1 = z := sub_eq_zero.mp h
      simpa using this.symm
    have : ‖z‖ = 1 := by simpa [this]
    exact (not_lt.mpr (le_of_eq this)) hz
  calc
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
        = Complex.exp (Complex.log (1 - z)) * Complex.exp (z + z ^ 2 / 2) := by
          simpa [Complex.exp_log hne]
    _   = Complex.exp (Complex.log (1 - z) + (z + z ^ 2 / 2)) := by
          simpa [Complex.exp_add, add_comm, add_left_comm, add_assoc]

/-- Log bound for `log(1 - z)` via the modern `log(1 + z)` inequality. -/
lemma norm_log_one_sub_le_of_lt_one {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  simpa [sub_eq_add_neg, norm_neg] using
    (Complex.norm_log_one_add_le (z := -z) (by simpa [norm_neg] using hz))

end

end RH.AcademicFramework.DiagonalFredholm

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Modern DF‑WP helpers:

  - Use current mathlib: `HasSum.cexp`, `HasProd`/`Multipliable`.
  - Replace any use of non-existent `Complex.norm_log_one_sub_le` with
    `Complex.norm_log_one_add_le` specialized at `z ↦ -z`.
  - Keep the interface light; no axioms.
-/

namespace RH.AcademicFramework.DiagonalFredholm

noncomputable section

open Complex
open scoped BigOperators

/-- Power series identity for the cubic tail of `log(1 - z)`.
For `‖z‖ < 1` we have
  `∑' n, - z^(n+3) / (n+3) = Complex.log (1 - z) + z + z^2 / 2`.
This is obtained from power series for log and splitting off the first two terms. -/
lemma tsum_log_one_sub_cubic_tail {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    (∑' n : ℕ, - z ^ (n + 3) / ((n + 3 : ℕ) : ℂ))
      = Complex.log (1 - z) + z + z ^ 2 / 2 := by
  -- Placeholder: algebraic identity from power series manipulation
  -- This is a standard reindexing of the log power series
  sorry

/-- Euler factor as an exponential of the cubic tail `tsum` for `‖z‖ < 1`.
`(1 - z) * exp(z + z^2/2) = exp(∑' n, - z^(n+3)/(n+3))`. -/
lemma eulerFactor_exp_tsum_cubic_tail {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
      = Complex.exp (∑' n : ℕ, - z ^ (n + 3) / ((n + 3 : ℕ) : ℂ)) := by
  -- Placeholder: exp of log identity with cubic tail reindexing
  sorry

/-- Cubic tail bound for the log Weierstrass remainder on `‖z‖ < 1`:
`‖log(1 - z) + z + z^2/2‖ ≤ ‖z‖^3 / (1 - ‖z‖)`.

This follows from the power series for `log(1 - z)` and a comparison with the
geometric series. -/
lemma log_one_sub_plus_z_plus_sq_cubic_tail
    {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z) + z + z^2 / 2‖ ≤ ‖z‖ ^ 3 / (1 - ‖z‖) := by
  -- Placeholder: geometric series argument for the cubic tail
  -- Standard analysis using ∑_{n≥3} |z|^n/n ≤ ∑_{n≥3} |z|^n = |z|^3/(1 - |z|)
  sorry

/-- Log bound for `log(1 - z)` via the modern `log(1 + z)` inequality. -/
lemma norm_log_one_sub_le_of_lt_one {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  -- Reduce to the `log(1 + w)` bound with `w = -z`.
  simpa [sub_eq_add_neg, norm_neg] using
    (Complex.norm_log_one_add_le (z := -z) (by simpa [norm_neg] using hz))

/-- A convenient half-radius variant of the previous bound. -/
lemma norm_log_one_sub_le_half {z : ℂ} (hz : ‖z‖ < (1 : ℝ) / 2) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  have h : (1 : ℝ) / 2 < 1 := by
    simpa using (one_half_lt_one : (1 : ℝ) / 2 < 1)
  exact norm_log_one_sub_le_of_lt_one (lt_trans hz h)

/-- Uniform quadratic tail bound for the Weierstrass log remainder on ‖z‖ ≤ r < 1.
For any `r ∈ (0,1)`, there is a constant `C(r) = (1 - r)⁻¹` with
`‖log(1 - z) + z‖ ≤ C(r) ‖z‖^2` whenever ‖z‖ ≤ r. -/
lemma log_one_sub_plus_z_quadratic_tail
    {z : ℂ} {r : ℝ} (_hr0 : 0 < r) (hr1 : r < 1) (hzr : ‖z‖ ≤ r) :
    ‖Complex.log (1 - z) + z‖ ≤ (1 - r)⁻¹ * ‖z‖^2 := by
  -- Base bound from `log(1 + w) - w` with `w = -z`
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hzr hr1
  have hbase : ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
    simpa [sub_eq_add_neg, norm_neg] using
      Complex.norm_log_one_add_sub_self_le (z := -z) (by simpa [norm_neg] using hz1)
  -- Compare denominators using `‖z‖ ≤ r < 1`
  have hmono : (1 - ‖z‖)⁻¹ ≤ (1 - r)⁻¹ := by
    have hpos₁ : 0 < 1 - r := sub_pos.mpr hr1
    have hpos₂ : 0 < 1 - ‖z‖ := by linarith
    have hle : 1 - r ≤ 1 - ‖z‖ := by linarith
    exact inv_le_inv_of_le hpos₁ hle
  have hnonneg : 0 ≤ (1 - ‖z‖)⁻¹ := by
    have : 0 < 1 - ‖z‖ := sub_pos.mpr hz1
    exact inv_nonneg.mpr (le_of_lt this)
  have hhalf_le : (1 - ‖z‖)⁻¹ / 2 ≤ (1 - ‖z‖)⁻¹ := by
    simpa using (half_le_self hnonneg)
  have hconst : (1 - ‖z‖)⁻¹ / 2 ≤ (1 - r)⁻¹ := le_trans hhalf_le hmono
  have hznn : 0 ≤ ‖z‖ ^ 2 := by exact sq_nonneg _
  have hscale : ‖z‖ ^ 2 * ((1 - ‖z‖)⁻¹ / 2) ≤ ‖z‖ ^ 2 * (1 - r)⁻¹ :=
    mul_le_mul_of_nonneg_left hconst hznn
  have hbase' : ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 * ((1 - ‖z‖)⁻¹ / 2) := by
    -- regroup the division to match `hscale`'s left-hand side
    simpa [mul_div_assoc] using hbase
  have hchain : ‖Complex.log (1 - z) + z‖ ≤ ‖z‖ ^ 2 * (1 - r)⁻¹ :=
    le_trans hbase' hscale
  simpa [mul_comm] using hchain

/-- Exponential turns sums into products (modern route).
If `a` is summable, then `∏ exp (a i) = exp (∑ a i)` and the product is
`Multipliable`. -/
lemma tprod_exp_of_summable {ι : Type*} [Countable ι]
    (a : ι → ℂ) (hsum : Summable a) :
    Multipliable (fun i => Complex.exp (a i)) ∧
      (∏' i, Complex.exp (a i)) = Complex.exp (∑' i, a i) := by
  -- `HasSum.cexp` yields a `HasProd` witness, from which both facts follow.
  have hsum' : HasSum a (∑' i, a i) := hsum.hasSum
  have hprod : HasProd (fun i => Complex.exp (a i)) (Complex.exp (∑' i, a i)) := by
    simpa [Function.comp] using hsum'.cexp
  exact ⟨hprod.multipliable, hprod.tprod_eq⟩

/-- Weierstrass-type bridge: from a summable log to a product identity.
If `f i ≠ 0` and `∑ log (f i)` converges, then `exp (∑ log (f i)) = ∏ f i`.
Derived from `HasSum.cexp` and `Complex.exp_log`. -/
lemma exp_tsum_eq_tprod {ι : Type*} [Countable ι]
    (f : ι → ℂ) (hne : ∀ i, f i ≠ 0)
    (hlog : Summable (fun i => Complex.log (f i))) :
    Complex.exp (∑' i, Complex.log (f i)) = ∏' i, f i := by
  have hprod : HasProd (fun i => Complex.exp (Complex.log (f i)))
      (Complex.exp (∑' i, Complex.log (f i))) := (hlog.hasSum).cexp
  calc
    Complex.exp (∑' i, Complex.log (f i))
        = ∏' i, Complex.exp (Complex.log (f i)) := by
          simpa using (hprod.tprod_eq.symm)
    _ = ∏' i, f i := by
      simp [Complex.exp_log (hne _)]

/-! ### Minimal helper: Euler factor as an exponential -/

/-- For `‖z‖ < 1`, the modified Euler factor `(1 - z) * exp(z + z^2/2)`
can be written as a single exponential `exp(log(1 - z) + z + z^2/2)`.
This uses the principal branch of `log` on the punctured disk. -/
lemma eulerFactor_as_exp_log (z : ℂ) (hz : ‖z‖ < (1 : ℝ)) :
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
      = Complex.exp (Complex.log (1 - z) + z + z ^ 2 / 2) := by
  have hne : 1 - z ≠ 0 := by
    intro h
    have hz1 : z = 1 := by
      have : 1 = z := sub_eq_zero.mp h
      simpa using this.symm
    have : ‖z‖ = 1 := by simpa [hz1]
    exact (not_lt.mpr (le_of_eq this)) hz
  calc
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
        = Complex.exp (Complex.log (1 - z)) * Complex.exp (z + z ^ 2 / 2) := by
          simpa [Complex.exp_log hne]
    _   = Complex.exp (Complex.log (1 - z) + (z + z ^ 2 / 2)) := by
          simpa [Complex.exp_add, add_comm, add_left_comm, add_assoc]

end

end RH.AcademicFramework.DiagonalFredholm
