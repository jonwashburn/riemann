
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.Complex.Circle

/-!
# Circle Average Lemmas

This file provides lemmas about circle averages, particularly subadditivity
and monotonicity properties needed for Nevanlinna theory.

## Main results

* `posLog_norm_div_le` : log⁺ |f/g| ≤ log⁺ |f| + log⁺ |g⁻¹|
* `circleAverage_posLog_norm_div_le` : Subadditivity for circle averages
* `circleAverage_posLog_norm_le_of_bounded` : Bounded functions have bounded proximity

## References

* Hayman, W.K., "Meromorphic Functions"
* Nevanlinna, R., "Analytic Functions"
-/

open Complex Set Metric Filter Topology Real MeasureTheory

namespace Nevanlinna

variable {f g : ℂ → ℂ} {r : ℝ}

/-! ### Subadditivity of log⁺ -/

/-- Pointwise inequality: log⁺ ‖f/g‖ ≤ log⁺ ‖f‖ + log⁺ ‖g⁻¹‖ -/
lemma posLog_norm_div_le' (a b : ℂ) (_ : b ≠ 0) :
    log⁺ ‖a / b‖ ≤ log⁺ ‖a‖ + log⁺ ‖b⁻¹‖ := by
  have h1 : ‖a / b‖ = ‖a‖ / ‖b‖ := norm_div a b
  have h2 : ‖a‖ / ‖b‖ = ‖a‖ * ‖b‖⁻¹ := div_eq_mul_inv ‖a‖ ‖b‖
  rw [h1, h2, norm_inv]
  exact posLog_mul

/-- For bounded-type functions g = G/H, the circle average of log⁺ ‖g‖
    is bounded by the sum of the averages for G and H⁻¹.

This follows from the pointwise inequality `log⁺ ‖f/g‖ ≤ log⁺ ‖f‖ + log⁺ ‖g⁻¹‖`
and the fact that circle averages preserve inequalities. -/
lemma circleAverage_posLog_norm_div_le
    (hf : CircleIntegrable (fun z => log⁺ ‖f z‖) 0 r)
    (hg : CircleIntegrable (fun z => log⁺ ‖(g z)⁻¹‖) 0 r)
    (hfg : CircleIntegrable (fun z => log⁺ ‖f z / g z‖) 0 r)
    (hg_ne : ∀ z ∈ sphere (0 : ℂ) |r|, g z ≠ 0) :
    circleAverage (fun z => log⁺ ‖f z / g z‖) 0 r ≤
      circleAverage (fun z => log⁺ ‖f z‖) 0 r +
      circleAverage (fun z => log⁺ ‖(g z)⁻¹‖) 0 r := by
  -- The proof uses:
  -- 1. Pointwise: log⁺ ‖f z / g z‖ ≤ log⁺ ‖f z‖ + log⁺ ‖(g z)⁻¹‖
  -- 2. Circle average is monotone for integrable functions
  -- 3. Circle average is additive for integrable functions
  -- Mathematical proof:
  -- Step 1: Pointwise inequality on the sphere:
  --   log⁺ ‖f x / g x‖ ≤ log⁺ ‖f x‖ + log⁺ ‖(g x)⁻¹‖
  -- Step 2: Circle average preserves pointwise inequalities for integrable functions
  --   So circleAverage (log⁺ ‖f/g‖) ≤ circleAverage (log⁺ ‖f‖ + log⁺ ‖g⁻¹‖)
  -- Step 3: Circle average is additive (Real.circleAverage_add)
  --   circleAverage (h₁ + h₂) = circleAverage h₁ + circleAverage h₂
  -- Conclusion: combine Steps 2 and 3.
  --
  -- Technical note: The monotonicity of circle integrals for two functions
  -- (not just against a constant) is not directly available as a single lemma,
  -- but follows from the integral monotonicity for interval integrals.
  -- Monotonicity: circleAverage (f/g) ≤ circleAverage (f + g⁻¹) using interval integral mono
  have h_pw : ∀ θ ∈ Set.Ioo 0 (2 * π),
      log⁺ ‖f (circleMap 0 r θ) / g (circleMap 0 r θ)‖ ≤
      log⁺ ‖f (circleMap 0 r θ)‖ + log⁺ ‖(g (circleMap 0 r θ))⁻¹‖ := by
    intro θ _
    have h_mem : circleMap 0 r θ ∈ sphere (0 : ℂ) |r| := circleMap_mem_sphere' 0 r θ
    have hgx : g (circleMap 0 r θ) ≠ 0 := hg_ne _ h_mem
    exact posLog_norm_div_le' (f (circleMap 0 r θ)) (g (circleMap 0 r θ)) hgx
  -- Use interval integral monotonicity
  have h_int_mono := intervalIntegral.integral_mono_on_of_le_Ioo
    (by positivity : 0 ≤ 2 * π) hfg (hf.add hg) h_pw
  -- The circle average of the sum equals the sum of circle averages
  have h_add := Real.circleAverage_add hf hg
  -- Scale by (2π)⁻¹ and combine
  have h_scaled : circleAverage (fun z => log⁺ ‖f z / g z‖) 0 r ≤
      circleAverage (fun z => log⁺ ‖f z‖ + log⁺ ‖(g z)⁻¹‖) 0 r := by
    simp only [circleAverage_def, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left h_int_mono (by positivity)
  calc circleAverage (fun z => log⁺ ‖f z / g z‖) 0 r
      ≤ circleAverage (fun z => log⁺ ‖f z‖ + log⁺ ‖(g z)⁻¹‖) 0 r := h_scaled
    _ = circleAverage (fun z => log⁺ ‖f z‖) 0 r +
          circleAverage (fun z => log⁺ ‖(g z)⁻¹‖) 0 r := h_add

/-! ### Circle average bounds for bounded functions -/

/-- Circle average of log⁺ ‖G‖ for bounded G is bounded by log⁺ C.
    This is the key estimate for the proximity function of bounded functions. -/
lemma circleAverage_posLog_norm_le_of_bounded
    {G : ℂ → ℂ} {C : ℝ} (_ : 0 < C) (hr : 0 < r)
    (hG_int : CircleIntegrable (fun z => log⁺ ‖G z‖) 0 r)
    (hbound : ∀ θ : ℝ, ‖G (circleMap 0 r θ)‖ ≤ C) :
    circleAverage (fun z => log⁺ ‖G z‖) 0 r ≤ log⁺ C := by
  -- log⁺ ‖G‖ ≤ log⁺ C pointwise on the circle
  have h_pw : ∀ θ : ℝ, log⁺ ‖G (circleMap 0 r θ)‖ ≤ log⁺ C := by
    intro θ
    exact posLog_le_posLog (norm_nonneg _) (hbound θ)
  -- Use circleAverage_mono_on_of_le_circle
  -- The circle average of a function bounded pointwise by M is ≤ M.
  -- This follows from: circleAverage f ≤ circleAverage (const M) = M.
  apply circleAverage_mono_on_of_le_circle hG_int
  intro x hx
  -- x is on the sphere of radius |r|
  -- We need to show x = circleMap 0 r θ for some θ
  simp only [Metric.mem_sphere, dist_zero_right] at hx
  -- x ∈ sphere 0 |r| means ‖x‖ = |r| = r (since r > 0)
  have hr_abs : |r| = r := abs_of_pos hr
  rw [hr_abs] at hx
  -- Use that x = r * exp(i * arg x)
  have h_ne : x ≠ 0 := by
    intro hx0
    simp [hx0] at hx
    exact hr.ne' hx.symm
  -- x = circleMap 0 r (arg x)
  -- Every point on the sphere of radius r can be written as circleMap 0 r θ
  -- for some θ. Specifically, θ = arg x works.
  --
  -- The polar form: x = |x| * exp(i * arg x)
  -- With |x| = ‖x‖ = r, we get x = r * exp(i * arg x) = circleMap 0 r (arg x)
  have h_eq : x = circleMap 0 r (arg x) := by
    rw [circleMap]
    simp only [zero_add]
    -- x = ‖x‖ * exp (arg x * I) by the polar decomposition (norm_mul_exp_arg_mul_I)
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
    rw [hx]
  rw [h_eq]
  exact h_pw (arg x)

/-! ### Circle average of nonnegative functions -/

/-- The circle average of a nonnegative function is nonnegative.
This is a consequence of the integral of a nonnegative function being nonnegative. -/
lemma circleAverage_nonneg {f : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (_ : CircleIntegrable f c R)
    (hf_nonneg : ∀ z ∈ sphere c |R|, 0 ≤ f z) :
    0 ≤ circleAverage f c R := by
  -- circleAverage f c R = (2π)⁻¹ * ∫ θ in 0..2π, f(circleMap c R θ) dθ
  -- Since f ≥ 0 on the sphere and circleMap lands on the sphere,
  -- the integrand is nonnegative, hence the integral is nonnegative.
  unfold circleAverage
  rw [smul_eq_mul]
  apply mul_nonneg
  · exact inv_nonneg.mpr (le_of_lt Real.two_pi_pos)
  · -- The interval integral of a nonnegative function is nonnegative
    apply intervalIntegral.integral_nonneg (le_of_lt Real.two_pi_pos)
    intro θ hθ
    apply hf_nonneg
    -- circleMap c R θ is on the sphere of radius |R|
    simp only [mem_sphere, dist_eq_norm]
    rw [circleMap_sub_center]
    simp

/-- Monotonicity: if f ≤ g pointwise on the sphere, then circleAverage f ≤ circleAverage g. -/
lemma circleAverage_mono {f g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R)
    (hg : CircleIntegrable g c R)
    (h_le : ∀ z ∈ sphere c |R|, f z ≤ g z) :
    circleAverage f c R ≤ circleAverage g c R := by
  have h_diff : CircleIntegrable (fun z => g z - f z) c R := hg.sub hf
  have h_nonneg : ∀ z ∈ sphere c |R|, 0 ≤ (g z - f z) := by
    intro z hz
    exact sub_nonneg.mpr (h_le z hz)
  have h_avg_nonneg : 0 ≤ circleAverage (fun z => g z - f z) c R :=
    circleAverage_nonneg h_diff h_nonneg
  have h_avg_sub : circleAverage (fun z => g z - f z) c R =
      circleAverage g c R - circleAverage f c R :=
    circleAverage_sub hg hf
  linarith

end Nevanlinna
