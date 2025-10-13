import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Instances.Real

noncomputable section

open scoped Real
open Complex MeasureTheory

namespace sandbox_det2

private lemma exp_sub_one_smul_integral (z : ℂ) :
    z • ∫ t in (0 : ℝ)..1, Complex.exp (t • z) = Complex.exp z - 1 := by
  classical
  -- Fundamental theorem of calculus on the segment 0 → z for f = exp
  have hcont : ContinuousOn (fun t : ℝ => Complex.exp ((0 : ℂ) + t • z)) (Set.Icc (0 : ℝ) 1) := by
    have : Continuous fun t : ℝ => Complex.exp (t • z) :=
      Complex.continuous_exp.comp (continuous_id.smul continuous_const)
    simpa using this.continuousOn
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun w : ℂ => Complex.exp w) (Complex.exp ((0 : ℂ) + t • z)) ((0 : ℂ) + t • z) := by
    intro t _
    simpa using Complex.hasDerivAt_exp ((0 : ℂ) + t • z)
  have := intervalIntegral.integral_unitInterval_deriv_eq_sub (𝕜 := ℂ) (E := ℂ)
    (f := fun w : ℂ => Complex.exp w) (f' := fun w : ℂ => Complex.exp w)
    (z₀ := (0 : ℂ)) (z₁ := z) hcont hderiv
  -- z • ∫₀¹ exp(t • z) = exp z - exp 0
  simpa [zero_smul, add_comm, add_left_comm, add_assoc, Complex.exp_zero] using this

private lemma exp_sub_one_sub_id_integral_identity (z : ℂ) :
    Complex.exp z - 1 - z = ∫ t in (0 : ℝ)..1, (1 - t) * (z ^ 2) * Complex.exp (t • z) := by
  classical
  -- Consider F(t) = exp (t•z) - t•z * exp (t•z). Then F' = (1 - t) z^2 exp (t•z)
  have hderiv_exp : ∀ t, HasDerivAt (fun t : ℝ => Complex.exp (t • z)) (z * Complex.exp (t • z)) t := by
    intro t
    have hlin : HasDerivAt (fun t : ℝ => ((t : ℂ))) (1 : ℂ) t := by
      simpa using (HasDerivAt.comp_ofReal (hf := hasDerivAt_id (x := t)))
    have hsmul : HasDerivAt (fun t : ℝ => (t : ℂ) • z) (1 * z) t := by
      simpa [one_mul, smul_mul_assoc] using hlin.smul_const (f := z)
    have hsmul' : HasDerivAt (fun t : ℝ => t • z) z t := by simpa using hsmul
    simpa [mul_comm] using hsmul'.cexp
  let F : ℝ → ℂ := fun t => Complex.exp (t • z) - (t : ℂ) * z * Complex.exp (t • z)
  have hF_deriv : ∀ t, HasDerivAt F ((1 - t) * z^2 * Complex.exp (t • z)) t := by
    intro t
    have h1 := hderiv_exp t
    have h_ofReal : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t := by
      simpa using (HasDerivAt.comp_ofReal (hf := hasDerivAt_id (x := t)))
    have h_mul : HasDerivAt (fun t : ℝ => ((t : ℂ) * z)) z t := by
      have := h_ofReal.mul_const (d := z)
      simpa using this
    have h_prod : HasDerivAt (fun t : ℝ => ((t : ℂ) * z) * Complex.exp (t • z))
        (z * Complex.exp (t • z) + (t : ℂ) * z * (z * Complex.exp (t • z))) t := by
      simpa [mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using h_mul.mul (hderiv_exp t)
    have hF' : HasDerivAt F (z * Complex.exp (t • z) - (z * Complex.exp (t • z) + (t : ℂ) * z * (z * Complex.exp (t • z)))) t := by
      simpa [F, sub_eq_add_neg] using h1.sub h_prod
    -- simplify to (1 - t) * z^2 * exp (t•z)
    simpa [F, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc, pow_two, add_comm, add_left_comm,
      add_assoc, one_mul, ofReal_mul, ofReal_one] using hF'
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) * z ^ 2 * Complex.exp (t • z)) volume 0 1 := by
    -- integrable on [0,1] by continuity
    have hcont : ContinuousOn (fun t : ℝ => (1 - t) * z ^ 2 * Complex.exp (t • z)) (Set.Icc (0 : ℝ) 1) := by
      have h1 : Continuous fun t : ℝ => (1 - t : ℝ) := by continuity
      have h2 : Continuous fun t : ℝ => Complex.exp (t • z) :=
        Complex.continuous_exp.comp (continuous_id.smul continuous_const)
      simpa using (h1.ofReal.mul (continuous_const.mul h2)).continuousOn
    exact hcont.intervalIntegrable_of_Icc (by norm_num)
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := 1)
      (hab := by norm_num)
      (hcont := by
        have h1 : Continuous fun t : ℝ => Complex.exp (t • z) :=
          Complex.continuous_exp.comp (continuous_id.smul continuous_const)
        have h2 : Continuous fun t : ℝ => ((t : ℂ) * z) * Complex.exp (t • z) := by
          simpa using ((continuous_ofReal.mul continuous_const).mul h1)
        have : Continuous fun t : ℝ => F t := by
          simpa [F, sub_eq_add_neg] using h1.sub h2
        exact this.continuousOn)
      (hderiv := by intro t _; simpa using hF_deriv t)
      (hint := hint)
  have F0 : F 0 = 1 := by simp [F, Complex.exp_zero]
  have F1 : F 1 = Complex.exp z - z * Complex.exp z := by simp [F, one_smul]
  simpa [F1, F0, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using hFTC

/-- For all `z : ℂ`, `‖exp z - 1‖ ≤ ‖z‖ · exp ‖z‖`.
The proof uses the integral identity `exp z - 1 = ∫₀¹ z · exp (t z) dt` and the Bochner norm bound. -/
lemma norm_exp_sub_one_le_norm_mul_exp_norm (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  classical
  -- Represent as an integral and bound the integrand uniformly by ‖z‖·exp ‖z‖
  have hId := exp_sub_one_smul_integral z
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1, ‖z * Complex.exp (t • z)‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
    intro t ht
    have hnorm : ‖Complex.exp (t • z)‖ = Real.exp (Complex.re (t • z)) := by
      simpa [Complex.norm_eq_abs] using Complex.abs_exp (t • z)
    have hRe_le : Complex.re (t • z) ≤ ‖z‖ := by
      -- For t ∈ Ι 0 1, we have 0 ≤ t ≤ 1
      have ht' : 0 ≤ t ∧ t ≤ 1 := by
        have h01 : (0 : ℝ) ≤ 1 := by norm_num
        have huicc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le h01
        have : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [huicc] using ht
        exact And.intro this.1 this.2
      have hre_le : Complex.re z ≤ ‖z‖ := by
        simpa [Complex.norm_eq_abs] using Complex.re_le_abs z
      have : Complex.re (t • z) = t * Complex.re z := by
        simpa using Complex.smul_re z t
      have := calc
        Complex.re (t • z) = t * Complex.re z := this
        _ ≤ t * ‖z‖ := by
          have := mul_le_mul_of_nonneg_left hre_le ht'.1; simpa using this
        _ ≤ ‖z‖ := by
          have := mul_le_of_le_one_left (show 0 ≤ ‖z‖ by positivity) ht'.2; simpa using this
      exact this
    have : ‖Complex.exp (t • z)‖ ≤ Real.exp ‖z‖ := by
      have := Real.exp_le_exp.mpr hRe_le
      simpa [hnorm]
    have : ‖z * Complex.exp (t • z)‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
      simpa [norm_mul] using mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ ‖z‖)
    exact this
  -- Bound using Bochner inequality and norm-smul
  have :=
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => Complex.exp (t • z)) (C := Real.exp ‖z‖)
      (by
        intro t ht
        have hnorm : ‖Complex.exp (t • z)‖ = Real.exp (Complex.re (t • z)) := by
          simpa [Complex.norm_eq_abs] using Complex.abs_exp (t • z)
        have ht' : 0 ≤ t ∧ t ≤ 1 := by
          have hmem : t ∈ Set.Ioc (0 : ℝ) 1 := by
            have h01 : (0 : ℝ) ≤ 1 := by norm_num
            simpa [uIoc, min_eq_left h01, max_eq_right h01] using ht
          exact And.intro (le_of_lt hmem.1) hmem.2
        have hre_le : Complex.re (t • z) ≤ ‖z‖ := by
          have hz : Complex.re z ≤ ‖z‖ := by simpa [Complex.norm_eq_abs] using Complex.re_le_abs z
          have : Complex.re (t • z) = t * Complex.re z := by simpa using Complex.smul_re z t
          have := calc
            Complex.re (t • z) = t * Complex.re z := this
            _ ≤ t * ‖z‖ := by exact mul_le_mul_of_nonneg_left hz ht'.1
            _ ≤ ‖z‖ := by exact mul_le_of_le_one_left (by positivity) ht'.2
          exact this
        have := Real.exp_le_exp.mpr hre_le
        simpa [hnorm]) )
  -- Use the identity and norm_smul
  have : ‖Complex.exp z - 1‖ = ‖z • ∫ t in (0 : ℝ)..1, Complex.exp (t • z)‖ := by
    simpa [hId]
  -- rewrite and use norm_smul
  have := by
    have := this
    -- chain
    exact this
  -- final bound
  have hzpos : 0 ≤ ‖z‖ := by positivity
  have : ‖Complex.exp z - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
    have hI :=
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (f := fun t : ℝ => Complex.exp (t • z)) (C := Real.exp ‖z‖)
        (by
          intro t ht
          have hnorm : ‖Complex.exp (t • z)‖ = Real.exp (Complex.re (t • z)) := by
            simpa [Complex.norm_eq_abs] using Complex.abs_exp (t • z)
          have ht' : 0 ≤ t ∧ t ≤ 1 := by
            have h01 : (0 : ℝ) ≤ 1 := by norm_num
            have huicc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le h01
            have : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [huicc] using ht
            exact And.intro this.1 this.2
          have hre_le : Complex.re (t • z) ≤ ‖z‖ := by
            have hz : Complex.re z ≤ ‖z‖ := by simpa [Complex.norm_eq_abs] using Complex.re_le_abs z
            have : Complex.re (t • z) = t * Complex.re z := by simpa using Complex.smul_re z t
            have := calc
              Complex.re (t • z) = t * Complex.re z := this
              _ ≤ t * ‖z‖ := by exact mul_le_mul_of_nonneg_left hz ht'.1
              _ ≤ ‖z‖ := by exact mul_le_of_le_one_left (by positivity) ht'.2
            exact this
          have := Real.exp_le_exp.mpr hre_le
          simpa [hnorm]) )
    -- Now use the identity and norm_smul
    have : ‖Complex.exp z - 1‖ = ‖z‖ * ‖∫ t in (0 : ℝ)..1, Complex.exp (t • z)‖ := by
      simpa [hId, norm_smul]
    have := this ▸ (mul_le_mul_of_nonneg_left (by simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] using hI) hzpos)
    simpa using this
  exact this

/-- For all `z : ℂ`, `‖exp z - 1 - z‖ ≤ ‖z‖^2 · exp ‖z‖`.
We use the integral identity `exp z - 1 - z = ∫₀¹ (1 - t) z^2 · exp (t z) dt` and uniform bounds. -/
lemma norm_exp_sub_one_sub_id_le (z : ℂ) :
    ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  classical
  -- From the first identity and linearity: exp z - 1 - z = z • ∫₀¹ (exp (t•z) - 1)
  have hId : Complex.exp z - 1 - z = z • ∫ t in (0 : ℝ)..1, (Complex.exp (t • z) - 1) := by
    have h1 := exp_sub_one_smul_integral z
    have hconst : (∫ _t in (0 : ℝ)..1, (1 : ℂ)) = (1 : ℝ) := by
      simpa using (intervalIntegral.integral_const (a := (0 : ℝ)) (b := 1) (c := (1 : ℂ)))
    calc
      Complex.exp z - 1 - z
          = (z • ∫ t in (0 : ℝ)..1, Complex.exp (t • z)) - (z • (1 : ℝ) : ℂ) := by
            simpa [h1, hconst, one_smul, sub_eq_add_neg] using rfl
      _ = z • ∫ t in (0 : ℝ)..1, (Complex.exp (t • z) - 1) := by
            simp [intervalIntegral.integral_sub, smul_sub, sub_eq_add_neg]
  -- Bound the integrand using the first inequality at t•z, and 0 ≤ t ≤ 1
  have hbound : ∀ t ∈ Ι (0 : ℝ) 1, ‖Complex.exp (t • z) - 1‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
    intro t ht
    have ht' : 0 ≤ t ∧ t ≤ 1 := by
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      have huicc : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le h01
      have : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [huicc] using ht
      exact And.intro this.1 this.2
    have h1 : ‖Complex.exp (t • z) - 1‖ ≤ ‖t • z‖ * Real.exp ‖t • z‖ :=
      norm_exp_sub_one_le_norm_mul_exp_norm (t • z)
    have t_le_one_abs : |t| ≤ (1 : ℝ) := by
      have := ht'.2
      have t_nonneg := ht'.1
      have : |t| = t := abs_of_nonneg t_nonneg
      simpa [this]
    have h1' : ‖Complex.exp (t • z) - 1‖ ≤ |t| * ‖z‖ * Real.exp ‖z‖ := by
      have hbase := norm_exp_sub_one_le_norm_mul_exp_norm (t • z)
      have hsmul : ‖t • z‖ = |t| * ‖z‖ := by
        simpa [norm_smul] using congrArg (fun x => ‖x‖) (rfl : t • z = t • z)
      have : ‖t • z‖ * Real.exp ‖t • z‖ ≤ (|t| * ‖z‖) * Real.exp ‖z‖ := by
        have hexp_mono : Real.exp ‖t • z‖ ≤ Real.exp (|t| * ‖z‖) := by
          have : ‖t • z‖ ≤ |t| * ‖z‖ := by
            simpa [norm_smul] using le_of_eq (by rfl : ‖t • z‖ = |t| * ‖z‖)
          exact Real.exp_le_exp.mpr this
        have : (|t| * ‖z‖) ≤ ‖z‖ := by
          have hz := (mul_le_of_le_one_left (show 0 ≤ ‖z‖ by positivity) t_le_one_abs)
          simpa [one_mul, mul_comm] using hz
        have : Real.exp ‖t • z‖ ≤ Real.exp ‖z‖ := le_trans hexp_mono (Real.exp_le_exp.mpr this)
        exact mul_le_mul (le_of_eq hsmul) this (by positivity) (by positivity)
      exact hbase.trans this
    -- so, ‖exp (t•z) - 1‖ ≤ ‖z‖ * exp ‖z‖
    exact (le_trans h1' (by
      have : |t| * ‖z‖ ≤ ‖z‖ := (mul_le_of_le_one_right (by positivity) t_le_one_abs)
      have : (|t| * ‖z‖) * Real.exp ‖z‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
        exact mul_le_mul_of_nonneg_right this (by positivity)
      simpa [mul_comm, mul_left_comm, mul_assoc] using this))
  -- Bound the integral and use norm_smul
  have H :=
    (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => (Complex.exp (t • z) - 1)) (C := ‖z‖ * Real.exp ‖z‖) hbound)
  have : ‖Complex.exp z - 1 - z‖ = ‖z‖ * ‖∫ t in (0 : ℝ)..1, (Complex.exp (t • z) - 1)‖ := by
    simpa [hId, norm_smul]
  have hzpos : 0 ≤ ‖z‖ := by positivity
  have := this ▸ (mul_le_mul_of_nonneg_left (by simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)] using H) hzpos)
  -- drop the factor 1/2 for simplicity of constants
  exact this

end sandbox_det2
