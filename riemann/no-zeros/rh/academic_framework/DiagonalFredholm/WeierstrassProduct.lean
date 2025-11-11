import rh.Compat

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
      simp [this.symm]
    exact (ne_of_lt hz) hz1
  calc
    (1 - z) * Complex.exp (z + z ^ 2 / 2)
        = Complex.exp (Complex.log (1 - z)) * Complex.exp (z + z ^ 2 / 2) := by
          simp [Complex.exp_log hne]
    _   = Complex.exp (Complex.log (1 - z) + (z + z ^ 2 / 2)) := by
          simp [Complex.exp_add]
    _   = Complex.exp (Complex.log (1 - z) + z + z ^ 2 / 2) := by
          simp [add_comm, add_left_comm, add_assoc]

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
  have hLT3 : Complex.logTaylor 3 (-z) = -z - z ^ 2 / 2 := by
    -- Manually expand: logTaylor 3 w = ∑_{j=0}^{2} (-1)^j * w^{j+1} / (j+1)
    -- For j=0: (-1)^0 * w^1 / 1 = w
    -- For j=1: (-1)^1 * w^2 / 2 = -w^2/2
    -- For j=2: (-1)^2 * w^3 / 3 = w^3/3
    -- At w = -z: -z + z^2/2 + ...
    -- But we only need through j=1 for the identity
    unfold Complex.logTaylor
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  have hEq_inside : Complex.log (1 + (-z)) - Complex.logTaylor 3 (-z)
      = Complex.log (1 - z) + z + z ^ 2 / 2 := by
    simp [sub_eq_add_neg, hLT3, add_comm, add_left_comm, add_assoc]
  have hEq : ‖Complex.log (1 - z) + z + z ^ 2 / 2‖
      = ‖Complex.log (1 + (-z)) - Complex.logTaylor 3 (-z)‖ := by
    simp [hEq_inside]
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
