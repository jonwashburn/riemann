import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
Minimal DF–WP helpers (no axioms):
- `tprod_exp_of_summable` and `exp_tsum_eq_tprod` to pass between sums and products
- `eulerFactor_as_exp_log` to rewrite the modified Euler factor as a single exponential
- `norm_log_one_sub_le_of_lt_one` and the cubic-tail bound for `log(1 - z)`
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
    have hz1 : ‖z‖ = 1 := by
      have : 1 = z := sub_eq_zero.mp h
      simpa [this.symm]
    exact (ne_of_lt hz) hz1
  calc
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
        = Complex.exp (Complex.log (1 - z)) * Complex.exp (z + z ^ 2 / 2) := by
          simpa [Complex.exp_log hne]
    _   = Complex.exp (Complex.log (1 - z) + (z + z ^ 2 / 2)) := by
          simpa [Complex.exp_add] using
            (Complex.exp_add (Complex.log (1 - z)) (z + z ^ 2 / 2)).symm
    _   = Complex.exp (Complex.log (1 - z) + z + z ^ 2 / 2) := by
          simpa [add_comm, add_left_comm, add_assoc]

/-- Log bound for `log(1 - z)` via the modern `log(1 + z)` inequality. -/
lemma norm_log_one_sub_le_of_lt_one {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  have hquad : ‖Complex.log (1 - z) + z‖
      ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
    simpa [sub_eq_add_neg, norm_neg] using
      Complex.norm_log_one_add_sub_self_le (z := -z) (by simpa [norm_neg] using hz)
  have :=
    calc
      ‖Complex.log (1 - z)‖ = ‖(Complex.log (1 - z) + z) - z‖ := by ring_nf
      _ ≤ ‖Complex.log (1 - z) + z‖ + ‖z‖ := by simpa using norm_sub_le _ _
      _ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := add_le_add_right hquad _
  simpa using this

/-- Cubic tail bound for the modified Weierstrass log remainder on `‖z‖ < 1`:
`‖log(1 - z) + z + z^2/2‖ ≤ ‖z‖^3 / (1 - ‖z‖)`.
This is the `log(1 + w)` cubic remainder bound specialized to `w = -z`. -/
lemma log_one_sub_plus_z_plus_sq_cubic_tail
    {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z) + z + z ^ 2 / 2‖ ≤ ‖z‖ ^ 3 / (1 - ‖z‖) := by
  simpa [sub_eq_add_neg, norm_neg]
    using (Complex.norm_log_one_add_sub_self_sub_sq_div_two_le
      (z := -z) (by simpa [norm_neg] using hz))

end

end RH.AcademicFramework.DiagonalFredholm
