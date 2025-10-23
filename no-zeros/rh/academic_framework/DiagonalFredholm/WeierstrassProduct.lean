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
  have hsub : ‖(Complex.log (1 - z) + z) - z‖
      ≤ ‖Complex.log (1 - z) + z‖ + ‖z‖ := by
    simpa using norm_sub_le (Complex.log (1 - z) + z) z
  have hle : ‖(Complex.log (1 - z) + z) - z‖
      ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ :=
    (le_trans hsub (add_le_add_right hquad _))
  have hEq : ‖Complex.log (1 - z)‖ = ‖(Complex.log (1 - z) + z) - z‖ := by
    ring_nf
  simpa [hEq]
    using hle

/-- Cubic tail bound for the modified Weierstrass log remainder on `‖z‖ < 1`:
`‖log(1 - z) + z + z^2/2‖ ≤ ‖z‖^3 / (1 - ‖z‖)`.
This is the `log(1 + w)` cubic remainder bound specialized to `w = -z`. -/
lemma log_one_sub_plus_z_plus_sq_cubic_tail
    {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖Complex.log (1 - z) + z + z ^ 2 / 2‖ ≤ ‖z‖ ^ 3 / (1 - ‖z‖) := by
  -- Use Taylor remainder at order 2 for log(1 + w) with w = -z
  have hneg : ‖-z‖ < (1 : ℝ) := by simpa [norm_neg] using hz
  have hmain : ‖Complex.log (1 + (-z)) - Complex.logTaylor 3 (-z)‖
      ≤ ‖-z‖ ^ 3 * (1 - ‖-z‖)⁻¹ / 3 := by
    have h := (Complex.norm_log_sub_logTaylor_le (n := 2) (z := -z) hneg)
    have h23 : ((2 : ℝ) + 1) = 3 := by norm_num
    simpa [Nat.cast_add, Nat.cast_one, h23] using h
  -- Rewrite the left-hand side as the Taylor remainder and simplify
  have hLT1 : Complex.logTaylor 1 (-z) = 0 := by
    have h := congrArg (fun f : (ℂ → ℂ) => f (-z)) (Complex.logTaylor_succ 0)
    simpa [Complex.logTaylor_zero, pow_zero, one_div] using h
  have hLT2 : Complex.logTaylor 2 (-z) = -z := by
    have h := congrArg (fun f : (ℂ → ℂ) => f (-z)) (Complex.logTaylor_succ 1)
    simpa [hLT1, pow_one, one_div, inv_one] using h
  have hLT3 : Complex.logTaylor 3 (-z) = -z - z ^ 2 / 2 := by
    have h := congrArg (fun f : (ℂ → ℂ) => f (-z)) (Complex.logTaylor_succ 2)
    simpa [Complex.logTaylor_succ, hLT2, pow_two, one_div] using h
  have hEq_inside : Complex.log (1 + (-z)) - Complex.logTaylor 3 (-z)
      = Complex.log (1 - z) + z + z ^ 2 / 2 := by
    simpa [sub_eq_add_neg, hLT3, add_comm, add_left_comm, add_assoc]
  have hEq : ‖Complex.log (1 - z) + z + z ^ 2 / 2‖
      = ‖Complex.log (1 + (-z)) - Complex.logTaylor 3 (-z)‖ := by
    simpa [hEq_inside]
  have hstep : ‖Complex.log (1 - z) + z + z ^ 2 / 2‖
      ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
    simpa [hEq, norm_neg] using hmain
  -- Drop the factor 1/3: (·)/3 ≤ (·) since the quantity is nonnegative
  have hA_nonneg : 0 ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ := by
    have hz3 : 0 ≤ ‖z‖ ^ 3 := by exact pow_nonneg (norm_nonneg _) 3
    have hden : 0 ≤ (1 - ‖z‖)⁻¹ := by
      have : 0 < 1 - ‖z‖ := sub_pos.mpr hz
      exact inv_nonneg.mpr (le_of_lt this)
    exact mul_nonneg hz3 hden
  have hdrop : (‖z‖ ^ 3 * (1 - ‖z‖)⁻¹) / 3 ≤ (‖z‖ ^ 3 * (1 - ‖z‖)⁻¹) := by
    have : (1 / (3 : ℝ)) ≤ 1 := by norm_num
    have := mul_le_mul_of_nonneg_left this hA_nonneg
    simpa [div_eq_mul_inv, one_mul] using this
  exact (le_trans hstep hdrop)

end

end RH.AcademicFramework.DiagonalFredholm

-- Auxiliary cubic-tail bound for log(1+z) remainder (not in this mathlib snapshot)
namespace Complex

noncomputable section

open scoped Topology

/-- Cubic Taylor remainder bound for `log(1+z)` when `‖z‖ < 1`.
`‖log(1+z) - z - z^2/2‖ ≤ ‖z‖^3 / (1 - ‖z‖)`.
This follows from the general `norm_log_sub_logTaylor_le` with `n=2`. -/
lemma norm_log_one_add_sub_self_sub_sq_div_two_le
    {z : ℂ} (hz : ‖z‖ < (1 : ℝ)) :
    ‖log (1 + z) - z - z ^ 2 / 2‖ ≤ ‖z‖ ^ 3 / (1 - ‖z‖) := by
  -- general remainder bound with n=2
  have hrem : ‖log (1 + z) - logTaylor 3 z‖
      ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 :=
    norm_log_sub_logTaylor_le (n := 2) (z := z) hz
  -- logTaylor 3 z = z - z^2/2 (the j=0 term vanishes since inv 0 = 0 in ℂ)
  have hlt3 : logTaylor 3 z = z - z ^ 2 / 2 := by
    -- expand through three succ steps
    have h1 := congrArg (fun f : (ℂ → ℂ) => f z) (logTaylor_succ 0)
    have h2 := congrArg (fun f : (ℂ → ℂ) => f z) (logTaylor_succ 1)
    have h3 := congrArg (fun f : (ℂ → ℂ) => f z) (logTaylor_succ 2)
    -- simplify each
    have : logTaylor 1 z = 0 := by
      simpa [logTaylor_zero, logTaylor_succ, pow_zero, one_div] using h1
    have : logTaylor 2 z = z := by
      simpa [logTaylor_succ, this, pow_one, one_div, inv_one] using h2
    simpa [logTaylor_succ, this, pow_two, one_div] using h3
  have hEq : ‖log (1 + z) - z - z ^ 2 / 2‖ = ‖log (1 + z) - logTaylor 3 z‖ := by
    simpa [hlt3, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- drop the 1/3 factor on a nonnegative quantity
  have hnonneg : 0 ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ := by
    exact mul_nonneg (by exact pow_nonneg (norm_nonneg _) _)
      (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt hz)))
  have hdrop : ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ := by
    have : (1 / (3 : ℝ)) ≤ 1 := by norm_num
    simpa [div_eq_mul_inv, one_mul, mul_comm, mul_left_comm, mul_assoc]
      using mul_le_mul_of_nonneg_left this hnonneg
  have : ‖log (1 + z) - logTaylor 3 z‖ ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ :=
    le_trans hrem hdrop
  simpa [hEq, div_eq_mul_inv]

end
