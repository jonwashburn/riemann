import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-!
# Poisson Kernel Analysis Helpers

Non-asymptotic lemmas used by the KD Schur analysis. We avoid deep Fourier
machinery here, but provide general-purpose inequalities that are immediately
useful to bound restricted integrals of nonnegative kernels by their full-line
integrals, and basic properties of the Cauchy/Poisson kernel.
-/

noncomputable section
open Classical MeasureTheory

namespace RH
namespace RS
namespace PoissonKernelAnalysis

/-- Cauchy/Poisson kernel: K_σ(x) = σ / (x^2 + σ^2). -/
@[simp] def Ksigma (σ x : ℝ) : ℝ := σ / (x^2 + σ^2)

lemma Ksigma_nonneg {σ x : ℝ} (hσ : 0 ≤ σ) : 0 ≤ Ksigma σ x := by
  unfold Ksigma
  have hden : 0 ≤ x^2 + σ^2 := by
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact div_nonneg hσ hden

lemma Ksigma_sq_nonneg {σ x : ℝ} (hσ : 0 ≤ σ) : 0 ≤ (Ksigma σ x) ^ 2 := by
  exact pow_two_nonneg _

/-- Nonnegativity of Kσ·Kτ. -/
lemma Ksigma_mul_nonneg {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (t a b : ℝ) :
  0 ≤ (Ksigma σ (t - a)) * (Ksigma τ (t - b)) := by
  have h1 := Ksigma_nonneg (x := t - a) hσ
  have h2 := Ksigma_nonneg (x := t - b) hτ
  exact mul_nonneg h1 h2

/-- Pointwise bound: Kσ(x) ≤ 1/σ for σ > 0. -/
lemma Ksigma_le_inv_sigma {σ x : ℝ} (hσ : 0 < σ) : Ksigma σ x ≤ 1 / σ := by
  unfold Ksigma
  have hden : σ ^ 2 ≤ x ^ 2 + σ ^ 2 := by
    exact le_add_of_nonneg_left (sq_nonneg x)
  have hσ2pos : 0 < σ ^ 2 := by
    have hne : σ ≠ 0 := ne_of_gt hσ
    simpa using (sq_pos_of_ne_zero hne)
  have hone : 1 / (x ^ 2 + σ ^ 2) ≤ 1 / σ ^ 2 :=
    one_div_le_one_div_of_le hσ2pos hden
  have hmul := mul_le_mul_of_nonneg_left hone hσ.le
  have hEq : σ / σ ^ 2 = 1 / σ := by
    have hne : σ ≠ 0 := ne_of_gt hσ
    calc
      σ / σ ^ 2 = σ / (σ * σ) := by simp [pow_two]
      _ = (σ / σ) / σ := by simpa using (div_mul_eq_div_div σ σ σ)
      _ = 1 / σ := by simp [hne]
  exact (le_trans (by simpa [div_eq_mul_inv] using hmul) (le_of_eq hEq))

/-- Pointwise bound: for x ≠ 0, Kσ(x) ≤ σ / x^2. -/
lemma Ksigma_le_sigma_div_sq {σ x : ℝ} (hσ : 0 ≤ σ) (hx : x ≠ 0) :
  Ksigma σ x ≤ σ / x^2 := by
  unfold Ksigma
  have hden : x ^ 2 ≤ x ^ 2 + σ ^ 2 := by
    exact le_add_of_nonneg_right (sq_nonneg σ)
  have hxpos : 0 < x ^ 2 := by
    simpa using (sq_pos_of_ne_zero hx)
  have hone : 1 / (x ^ 2 + σ ^ 2) ≤ 1 / x ^ 2 :=
    one_div_le_one_div_of_le hxpos hden
  have hmul := mul_le_mul_of_nonneg_left hone hσ
  simpa [div_eq_mul_inv] using hmul

/-- Triangle-type separation: |t − b| ≥ |a − b| − |t − a|. -/
lemma sep_lower_bound (t a b : ℝ) : |t - b| ≥ |a - b| - |t - a| := by
  have : |a - b| ≤ |a - t| + |t - b| := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, abs_sub_comm]
      using abs_add (a - t) (t - b)
  simpa [sub_eq_add_neg, abs_sub_comm] using sub_le_iff_le_add'.mpr this

/-! ### Poisson kernel: finite symmetric-interval identity and whole-line limit -/

private lemma hasDerivAt_arctan_scaled {σ x : ℝ} (hσ : 0 < σ) :
  HasDerivAt (fun t : ℝ => Real.arctan (t / σ)) (Ksigma σ x) x := by
  -- d/dx arctan (x/σ) = (1 / (1 + (x/σ)^2)) * (1/σ) = σ / (x^2 + σ^2)
  have h := (Real.hasDerivAt_arctan (x / σ)).comp x ((hasDerivAt_id x).div_const σ)
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have : (1 / (1 + (x / σ) ^ 2)) * (1 / σ) = σ / (x ^ 2 + σ ^ 2) := by
    field_simp [Ksigma, pow_two, hσne]
  simpa [Ksigma, this] using h

/-- For `σ>0` and `R≥0`, the symmetric-interval integral of the Poisson kernel is
`∫_{-R..R} Kσ = 2·arctan(R/σ)`. -/
lemma integral_Ksigma_symm_interval
  {σ R : ℝ} (hσ : 0 < σ) (hR : 0 ≤ R) :
  ∫ x in (-R)..R, Ksigma σ x = 2 * Real.arctan (R / σ) := by
  -- Fundamental theorem of calculus on [-R, R]
  have hFTC :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (a := -R) (b := R)
      (fun x _ => hasDerivAt_arctan_scaled (σ := σ) (x := x) hσ)
      ((Real.continuous_arctan.comp (continuous_id.div_const σ))).continuousOn
      (by simpa using (neg_le_self_iff.mpr hR)))
  -- Use oddness of arctan to simplify the boundary values
  have hodd : Real.arctan ((-R) / σ) = - Real.arctan (R / σ) := by
    simpa using (Real.arctan_neg (R / σ))
  simpa [hodd, two_mul, sub_eq, add_comm, add_left_comm, add_assoc]
    using hFTC

/-- As `R → +∞`, the symmetric-interval integral tends to `π` (for `σ>0`). -/
lemma tendsto_integral_Ksigma_symm_atTop
  {σ : ℝ} (hσ : 0 < σ) :
  Tendsto (fun R : ℝ => ∫ x in (-R)..R, Ksigma σ x) atTop (nhds Real.pi) := by
  have hrepr : (fun R : ℝ => ∫ x in (-R)..R, Ksigma σ x)
      = fun R : ℝ => 2 * Real.arctan (|R| / σ) := by
    funext R
    simpa [abs_of_nonneg (abs_nonneg R)] using
      integral_Ksigma_symm_interval (σ := σ) (R := |R|) hσ (abs_nonneg _)
  have hlim_abs : Tendsto (fun R : ℝ => |R|) atTop atTop := tendsto_abs_atTop_atTop
  have hdiv : Tendsto (fun R : ℝ => |R| / σ) atTop atTop :=
    (tendsto_const_nhds.mul_atTop_of_pos_right hlim_abs (by exact one_div_pos.mpr hσ))
  have htan : Tendsto (fun R : ℝ => Real.arctan (|R| / σ)) atTop (nhds (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.comp hdiv
  have hcont : Continuous fun y : ℝ => 2 * y := by continuity
  have hmap := hcont.tendsto (Real.pi / 2)
  have hlim := hmap.comp htan
  simpa [hrepr, two_mul] using hlim

/-- Whole-line identity: `∫_ℝ Kσ = π` (σ>0). -/
lemma integral_Ksigma_real_line {σ : ℝ} (hσ : 0 < σ) :
  ∫ x : ℝ, Ksigma σ x = Real.pi := by
  -- using nonnegativity to identify whole-line integral with the symmetric-limit
  have hnonneg : ∀ x, 0 ≤ Ksigma σ x := by intro x; exact Ksigma_nonneg (x := x) hσ.le
  have hmono := intervalIntegral.tendsto_integral_Icc_atTop_of_nonneg
      (μ := volume) (f := fun x => Ksigma σ x)
      (by intro x hx; exact hnonneg x)
  exact hmono.unique (tendsto_integral_Ksigma_symm_atTop hσ)

open scoped Interval

/-- Symmetric-interval identity: `∫_{-R..R} Kσ = 2·arctan(R/σ)` (σ>0; R≥0). -/
lemma integral_Ksigma_symm_interval
  {σ R : ℝ} (hσ : 0 < σ) (hR : 0 ≤ R) :
  ∫ x in (-R)..R, Ksigma σ x = 2 * Real.arctan (R / σ) := by
  -- F(x) = arctan(x/σ) is an antiderivative of Kσ
  have h_deriv : ∀ x : ℝ,
      HasDerivAt (fun x => Real.arctan (x / σ)) (Ksigma σ x) x := by
    intro x
    have hA := Real.hasDerivAt_arctan (x / σ)
    have hlin : HasDerivAt (fun x => (1 / σ) * x) (1 / σ) x :=
      (hasDerivAt_id x).const_mul (1 / σ)
    -- chain rule
    have hcomp := hA.comp x hlin
    -- simplify derivative: (1/(1+(x/σ)^2)) * (1/σ) = σ/(x^2+σ^2)
    have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt hσ
    have hsim : (1 / (1 + (x / σ) ^ 2)) * (1 / σ) = σ / (x ^ 2 + σ ^ 2) := by
      field_simp [hσ_ne, pow_two, div_eq_mul_inv]
    simpa [Ksigma, hsim] using hcomp
  -- apply FTC on [-R, R]
  have hF_cont : Continuous fun x : ℝ => Real.arctan (x / σ) := by
    have : Continuous fun x : ℝ => (1 / σ) * x := by continuity
    exact Real.continuous_arctan.comp this
  have h_main := intervalIntegral.integral_deriv_eq_sub
      (fun x => Real.arctan (x / σ)) (fun x => Ksigma σ x)
      (by intro x hx; simpa using h_deriv x) (by simpa using hF_cont)
      (neg_le.mpr hR) hR
  -- Evaluate boundary values using oddness of arctan
  have harc_odd : ∀ y, Real.arctan (-y) = - Real.arctan y := by
    intro y; simpa using Real.arctan_neg y
  simpa [Ksigma, sub_eq_add_neg, harc_odd (R/σ), two_mul] using h_main

/-- Uniform symmetric bound: `∫_{-R..R} Kσ ≤ π` (σ>0; R≥0). -/
lemma integral_Ksigma_symm_interval_le_pi {σ R : ℝ} (hσ : 0 < σ) (hR : 0 ≤ R) :
  ∫ x in (-R)..R, Ksigma σ x ≤ Real.pi := by
  have h := integral_Ksigma_symm_interval (σ := σ) (R := R) hσ hR
  have harc : Real.arctan (R / σ) ≤ Real.pi / 2 := Real.arctan_le_pi_div_two (R / σ)
  have : 2 * Real.arctan (R / σ) ≤ 2 * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left harc (by norm_num : 0 ≤ (2 : ℝ))
  simpa [two_mul] using this

/-- Whole-line identity: `∫_ℝ Kσ = π` (σ>0). -/
lemma integral_Ksigma_real_line {σ : ℝ} (hσ : 0 < σ) :
  ∫ x : ℝ, Ksigma σ x = Real.pi := by
  -- use symmetric-interval formula and take limits
  have hlim : Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, Ksigma σ x)
      Filter.atTop (nhds Real.pi) := by
    have hrepr : (fun R : ℝ => ∫ x in (-R)..R, Ksigma σ x)
        = (fun R : ℝ => 2 * Real.arctan (R / σ)) := by
      funext R
      have hR := integral_Ksigma_symm_interval (σ := σ) (R := |R|) hσ (abs_nonneg _)
      simpa [two_mul] using hR
    have hA : Filter.Tendsto (fun R : ℝ => Real.arctan (R / σ)) Filter.atTop (nhds (Real.pi / 2)) := by
      have : Filter.Tendsto (fun R : ℝ => R / σ) Filter.atTop atTop := by
        -- scale by positive constant preserves atTop
        have hpos : 0 < (1 / σ) := inv_pos.mpr hσ
        exact Filter.tendsto_atTop_mul_const_right (α := ℝ) (c := (1 / σ)) hpos
      exact Real.tendsto_arctan_atTop_nhds_pi_div_two.comp this
    have hcont : Continuous fun y : ℝ => 2 * y := by continuity
    have hA2 := hcont.tendsto (Real.pi / 2) |>.comp hA
    simpa [hrepr, two_mul] using hA2
  -- nonnegativity gives whole-line integral equals the limit
  have hnonneg : ∀ x, 0 ≤ Ksigma σ x := by intro x; exact Ksigma_nonneg (x := x) hσ.le
  exact (intervalIntegral.tendsto_integral_Icc_atTop_of_nonneg (μ := volume)
    (f := fun x => Ksigma σ x) (by intro x hx; exact hnonneg x)).unique hlim

/-- Symmetric-interval identity for the squared kernel:
`∫_{-R..R} (Kσ)^2 = R/(R^2+σ^2) + (1/σ)·arctan(R/σ)` (σ>0; R≥0). -/
lemma integral_Ksigma_sq_symm_interval
  {σ R : ℝ} (hσ : 0 < σ) (hR : 0 ≤ R) :
  ∫ x in (-R)..R, (Ksigma σ x) ^ 2
    = R / (R ^ 2 + σ ^ 2) + (1 / σ) * Real.arctan (R / σ) := by
  -- Antiderivative: x/(2(x^2+σ^2)) + (1/(2σ))·arctan(x/σ)
  have h_deriv : ∀ x : ℝ,
      HasDerivAt (fun x => x / (2 * (x ^ 2 + σ ^ 2))
        + (1 / (2 * σ)) * Real.arctan (x / σ)) ((Ksigma σ x) ^ 2) x := by
    intro x
    -- first term: (1/2)·x * (x^2+σ^2)^{-1}
    have hx : HasDerivAt (fun x : ℝ => x) (1 : ℝ) x := hasDerivAt_id _
    have hden : HasDerivAt (fun x : ℝ => (x ^ 2 + σ ^ 2)⁻¹)
        (-(2 * x) * (x ^ 2 + σ ^ 2)⁻²) x := by
      have : HasDerivAt (fun x : ℝ => x ^ 2 + σ ^ 2) (2 * x) x := by
        simpa [two_mul] using (hasDerivAt_pow 2 x)
      simpa [one_div, inv_eq_one_div, pow_two] using this.inv
    have hx2 : HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * x) (1 / 2 : ℝ) x := hx.const_mul _
    have hprod := hx2.mul hden
    have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt hσ
    have h1 : HasDerivAt (fun x => x / (2 * (x ^ 2 + σ ^ 2)))
        ((σ ^ 2 - x ^ 2) / (x ^ 2 + σ ^ 2) ^ 2) x := by
      -- simplify the product derivative to the rational form
      have :
        ((1 : ℝ) / 2) * (x ^ 2 + σ ^ 2)⁻¹
          + ((1 : ℝ) / 2) * x * (-(2 * x) * (x ^ 2 + σ ^ 2)⁻²)
          = ((σ ^ 2 - x ^ 2) / (x ^ 2 + σ ^ 2) ^ 2) := by
        field_simp [one_div, inv_eq_one_div, pow_two]
      simpa [div_eq_mul_inv] using hprod.congr (fun _ => rfl) this
    -- second term: (1/(2σ))·arctan(x/σ)
    have hA := Real.hasDerivAt_arctan (x / σ)
    have hlin : HasDerivAt (fun x : ℝ => (1 / σ) * x) (1 / σ) x :=
      (hasDerivAt_id x).const_mul _
    have h2 : HasDerivAt (fun x => (1 / (2 * σ)) * Real.arctan (x / σ))
        ((1 / (2 * σ)) * (σ / (x ^ 2 + σ ^ 2))) x := by
      simpa [mul_comm, mul_left_comm, div_eq_mul_inv] using (hA.comp x hlin).const_mul (1 / (2 * σ))
    -- sum gives σ^2/(x^2+σ^2)^2
    simpa [Ksigma, pow_two] using h1.add (by
      simpa [Ksigma, div_eq_mul_inv, one_div, inv_eq_one_div] using h2)
  have hcont : Continuous fun x : ℝ => x / (2 * (x ^ 2 + σ ^ 2)) + (1 / (2 * σ)) * Real.arctan (x / σ) := by
    have : Continuous fun x : ℝ => x / (2 * (x ^ 2 + σ ^ 2)) := by
      have : Continuous fun x : ℝ => (x ^ 2 + σ ^ 2) := by continuity
      have : Continuous fun x : ℝ => (x ^ 2 + σ ^ 2)⁻¹ := by continuity
      have : Continuous fun x : ℝ => (1 / 2 : ℝ) * x := by continuity
      simpa [div_eq_mul_inv] using this.mul this_1
    have : Continuous fun x : ℝ => (1 / (2 * σ)) * Real.arctan (x / σ) := by continuity
    exact this.add this_1
  -- FTC on [-R, R]
  have hFTC := intervalIntegral.integral_deriv_eq_sub
      (fun x => x / (2 * (x ^ 2 + σ ^ 2)) + (1 / (2 * σ)) * Real.arctan (x / σ))
      (fun x => (Ksigma σ x) ^ 2)
      (by intro x hx; simpa using h_deriv x) (by simpa using hcont)
      (neg_le.mpr hR) hR
  -- boundary evaluation reduces via even/odd relations
  have hsq : (-R) ^ 2 = R ^ 2 := by simpa [pow_two] using sq_neg R
  have harc : Real.arctan ((-R) / σ) = - Real.arctan (R / σ) := by
    simpa [neg_div] using Real.arctan_neg (R / σ)
  have hboundary :
      (R / (2 * (R ^ 2 + σ ^ 2)) + (1 / (2 * σ)) * Real.arctan (R / σ))
        - ((-R) / (2 * ((-R) ^ 2 + σ ^ 2)) + (1 / (2 * σ)) * Real.arctan ((-R) / σ))
      = R / (R ^ 2 + σ ^ 2) + (1 / σ) * Real.arctan (R / σ) := by
    have h1 : R / (2 * (R ^ 2 + σ ^ 2)) - (-R) / (2 * ((-R) ^ 2 + σ ^ 2))
        = R / (R ^ 2 + σ ^ 2) := by
      simpa [hsq, sub_eq_add_neg] using by ring
    have h2 : (1 / (2 * σ)) * Real.arctan (R / σ)
        - (1 / (2 * σ)) * Real.arctan ((-R) / σ)
        = (1 / σ) * Real.arctan (R / σ) := by
      simpa [harc, sub_eq_add_neg] using by ring
    simpa [h1, h2]
  simpa [hboundary] using hFTC

/-- Whole-line L² identity for the Poisson kernel: `∫ (Kσ)^2 = π/(2σ)` (σ>0). -/
lemma l2_Ksigma {σ : ℝ} (hσ : 0 < σ) :
  ∫ x : ℝ, (Ksigma σ x) ^ 2 = Real.pi / (2 * σ) := by
  -- take the limit of the symmetric-interval identity
  have hnonneg : ∀ x, 0 ≤ (Ksigma σ x) ^ 2 := by intro x; exact pow_two_nonneg _
  have hlim : Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..R, (Ksigma σ x) ^ 2)
      Filter.atTop (nhds (Real.pi / (2 * σ))) := by
    -- limits: R/(R^2+σ^2) → 0 and arctan(R/σ) → π/2
    have h1 : Filter.Tendsto (fun R : ℝ => R / (R ^ 2 + σ ^ 2)) Filter.atTop (nhds 0) := by
      -- |R|/(R^2+σ^2) ≤ 1/|R|
      have : Filter.Tendsto (fun R : ℝ => (1 : ℝ) / R) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
      -- compare R/(R^2+σ^2) ≤ 1/R eventually
      refine this.congr' (Filter.eventually_atTop.2 ⟨(1 : ℝ), ?_⟩)
      intro R hR
      have hpos : 0 < R := lt_of_le_of_lt hR (by norm_num)
      have hden : 0 < R ^ 2 + σ ^ 2 := by
        have : 0 ≤ R ^ 2 := sq_nonneg _
        have : 0 < σ ^ 2 := by exact sq_pos_of_ne_zero _ (ne_of_gt hσ)
        exact lt_of_le_of_lt (le_add_of_nonneg_left this) this
      have : R / (R ^ 2 + σ ^ 2) ≤ 1 / R := by
        have : R / (R ^ 2 + σ ^ 2) ≤ R / (R ^ 2) := by
          have : 0 < R ^ 2 := by exact pow_two_pos_of_ne_zero _ (ne_of_gt hpos)
          exact div_le_div_of_nonneg_left (le_of_lt hpos) (by exact le_of_lt hden) (le_of_lt this)
        simpa [div_eq_mul_inv, pow_two] using this
      simpa using this
    have h2 : Filter.Tendsto (fun R : ℝ => Real.arctan (R / σ)) Filter.atTop (nhds (Real.pi / 2)) := by
      have : Filter.Tendsto (fun R : ℝ => R / σ) Filter.atTop atTop := by
        have hpos : 0 < (1 / σ) := inv_pos.mpr hσ
        exact Filter.tendsto_atTop_mul_const_right (α := ℝ) (c := (1 / σ)) hpos
      exact Real.tendsto_arctan_atTop_nhds_pi_div_two.comp this
    have hsum := h1.add (Filter.Tendsto.const_mul _ h2)
    refine hsum.congr' (Filter.eventually_of_forall (fun R => by
      simpa [two_mul] using integral_Ksigma_sq_symm_interval (σ := σ) (R := R) hσ (le_of_lt (lt_of_le_of_lt (by exact le_of_eq rfl) (by norm_num)))))
      (by simp [two_mul, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv])
  exact (intervalIntegral.tendsto_integral_Icc_atTop_of_nonneg (μ := volume)
    (f := fun x => (Ksigma σ x) ^ 2) (by intro x hx; exact hnonneg x)).unique hlim

/-!
Future targets (to be proven):
- Convolution identity on ℝ:
  ∫_ℝ Kσ(t−a)·Kτ(t−b) dt = Real.pi · K(σ+τ)(a−b)

These will allow sharp Schur bounds on dyadic annuli.
-/

/-- ## Step 2: explicit antiderivative and FTC setup -/

section Antiderivative
variable {σ τ c : ℝ}

/-- Convenience shorthands. -/
private def D1 (σ : ℝ) (x : ℝ) : ℝ := x ^ 2 + σ ^ 2
private def D2 (τ c : ℝ) (x : ℝ) : ℝ := (x - c) ^ 2 + τ ^ 2

/-- Positive denominators we will use in algebraic manipulations. -/
private lemma D1_pos (x : ℝ) (hσ : 0 < σ) : 0 < D1 σ x := by
  have hx : 0 ≤ x ^ 2 := sq_nonneg _
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_ne_zero _ (ne_of_gt hσ)
  exact lt_of_le_of_lt (add_nonneg_of_nonneg_of_nonneg hx hσ.le) hσ2

private lemma D2_pos (x : ℝ) (hτ : 0 < τ) : 0 < D2 τ c x := by
  have hx : 0 ≤ (x - c) ^ 2 := sq_nonneg _
  have hτ2 : 0 < τ ^ 2 := sq_pos_of_ne_zero _ (ne_of_gt hτ)
  exact lt_of_le_of_lt (add_nonneg_of_nonneg_of_nonneg hx hτ.le) hτ2

/-- Plus/minus structural constants. -/
private def Splus (σ τ c : ℝ) : ℝ := c ^ 2 + (σ + τ) ^ 2
private def Sminus (σ τ c : ℝ) : ℝ := c ^ 2 + (σ - τ) ^ 2

private lemma Splus_pos (hσ : 0 < σ) (hτ : 0 < τ) : 0 < Splus σ τ c := by
  have : 0 < (σ + τ) ^ 2 := sq_pos_of_ne_zero _ (by exact add_ne_zero_of_ne_of_ne (ne_of_gt hσ) (ne_of_gt hτ))
  have : 0 ≤ c ^ 2 + (σ + τ) ^ 2 := by exact add_nonneg (sq_nonneg _) (le_of_lt this)
  have : 0 < c ^ 2 + (σ + τ) ^ 2 :=
    lt_of_le_of_lt this (by simpa using (lt_add_of_pos_right (c ^ 2) (sq_pos_of_ne_zero _ (by exact add_ne_zero_of_ne_of_ne (ne_of_gt hσ) (ne_of_gt hτ)))))
  simpa [Splus]

private lemma Sminus_pos : 0 < Sminus σ τ c := by
  have : 0 ≤ c ^ 2 := sq_nonneg _
  have : 0 < c ^ 2 + (σ - τ) ^ 2 :=
    lt_of_le_of_lt (add_nonneg this (sq_nonneg _)) (lt_of_le_of_ne (le_of_eq rfl) (by intro h; cases h))
  simpa [Sminus]

/-- Coefficients for the linear-combination antiderivative. -/
private def A1 (σ τ c : ℝ) : ℝ :=
  (σ + τ) / (2 * Splus σ τ c) + (σ - τ) / (2 * Sminus σ τ c)
private def A2 (σ τ c : ℝ) : ℝ :=
  (σ + τ) / (2 * Splus σ τ c) - (σ - τ) / (2 * Sminus σ τ c)
private def B1 (σ τ c : ℝ) : ℝ :=
  c / (2 * Splus σ τ c) + c / (2 * Sminus σ τ c)
private def B2 (σ τ c : ℝ) : ℝ :=
  c / (2 * Sminus σ τ c) - c / (2 * Splus σ τ c)

/-- Explicit antiderivative candidate `F_{σ,τ,c}`. -/
@[simp] def Fantideriv (σ τ c : ℝ) (x : ℝ) : ℝ :=
  (A1 σ τ c) * Real.arctan (x / σ)
  + (A2 σ τ c) * Real.arctan ((x - c) / τ)
  + (B1 σ τ c) * ((1/2 : ℝ) * Real.log ((x - c) ^ 2 + τ ^ 2))
  + (B2 σ τ c) * ((1/2 : ℝ) * Real.log (x ^ 2 + σ ^ 2))

/-- Derivative of `F_{σ,τ,c}` equals a linear combination of kernel parts. -/
lemma hasDerivAt_Fantideriv_lincombo
  (hσ : 0 < σ) (hτ : 0 < τ) (x : ℝ) :
  HasDerivAt (Fantideriv σ τ c)
    ( (A1 σ τ c) * (σ / D1 σ x)
    + (A2 σ τ c) * (τ / D2 τ c x)
    + (B1 σ τ c) * ((x - c) / D2 τ c x)
    + (B2 σ τ c) * (x / D1 σ x) ) x := by
  -- arctan(x/σ)
  have h1 := (Real.hasDerivAt_arctan (x / σ)).comp x ((hasDerivAt_id x).div_const σ)
  have h1' : HasDerivAt (fun y => Real.arctan (y / σ)) (σ / D1 σ x) x := by
    have : (1 : ℝ) / (σ * (1 + (x / σ) ^ 2)) = σ / D1 σ x := by
      have hσne : σ ≠ 0 := ne_of_gt hσ
      field_simp [D1, pow_two, hσne]
    simpa [div_eq_mul_inv, this] using h1
  have h1'' := h1'.const_mul (A1 σ τ c)
  -- arctan((x-c)/τ)
  have h2 := (Real.hasDerivAt_arctan ((x - c) / τ)).comp x ((hasDerivAt_id x).sub_const c |>.div_const τ)
  have h2' : HasDerivAt (fun y => Real.arctan ((y - c) / τ)) (τ / D2 τ c x) x := by
    have : (1 : ℝ) / (τ * (1 + ((x - c) / τ) ^ 2)) = τ / D2 τ c x := by
      have hτne : τ ≠ 0 := ne_of_gt hτ
      field_simp [D2, pow_two, sub_eq_add_neg, hτne]
    simpa [div_eq_mul_inv, this, sub_eq_add_neg] using h2
  have h2'' := h2'.const_mul (A2 σ τ c)
  -- (1/2) log((x-c)^2+τ^2)
  have h3den : HasDerivAt (fun y : ℝ => (y - c) ^ 2 + τ ^ 2) (2 * (x - c)) x := by
    simpa [two_mul, sub_eq_add_neg] using ((hasDerivAt_id x).sub_const c).pow 2 |>.add_const (τ ^ 2)
  have h3log : HasDerivAt (fun y : ℝ => Real.log ((y - c) ^ 2 + τ ^ 2)) (2 * (x - c) / D2 τ c x) x := by
    have hpos := D2_pos (σ := σ) (τ := τ) (c := c) (x := x) hτ
    simpa [Real.deriv_log, one_div, div_eq_mul_inv] using h3den.log (by exact_mod_cast (ne_of_gt hpos))
  have h3' : HasDerivAt (fun y => (1/2 : ℝ) * Real.log ((y - c) ^ 2 + τ ^ 2)) ((x - c) / D2 τ c x) x := by
    simpa [two_mul, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h3log.const_mul (1/2 : ℝ)
  have h3'' := h3'.const_mul (B1 σ τ c)
  -- (1/2) log(x^2+σ^2)
  have h4den : HasDerivAt (fun y : ℝ => y ^ 2 + σ ^ 2) (2 * x) x := by
    simpa [two_mul] using (hasDerivAt_id x).pow 2 |>.add_const (σ ^ 2)
  have h4log : HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + σ ^ 2)) (2 * x / D1 σ x) x := by
    have hpos := D1_pos (σ := σ) (x := x) hσ
    simpa [Real.deriv_log, one_div, div_eq_mul_inv] using h4den.log (by exact_mod_cast (ne_of_gt hpos))
  have h4' : HasDerivAt (fun y => (1/2 : ℝ) * Real.log (y ^ 2 + σ ^ 2)) (x / D1 σ x) x := by
    simpa [two_mul, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h4log.const_mul (1/2 : ℝ)
  have h4'' := h4'.const_mul (B2 σ τ c)
  -- sum of pieces
  simpa [Fantideriv, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using h1''.add (h2''.add (h3''.add h4''))

/-- Define the linear-combination integrand associated to `F_{σ,τ,c}`. -/
@[simp] def lincombo (σ τ c : ℝ) (x : ℝ) : ℝ :=
    (A1 σ τ c) * (σ / D1 σ x)
  + (A2 σ τ c) * (τ / D2 τ c x)
  + (B1 σ τ c) * ((x - c) / D2 τ c x)
  + (B2 σ τ c) * (x / D1 σ x)

/-- FTC on symmetric intervals for the linear-combination integrand. -/
lemma integral_lincombo_symm_eq_Fdiff
  (hσ : 0 < σ) (hτ : 0 < τ) (R : ℝ) :
  ∫ x in (-R)..R, lincombo σ τ c x = Fantideriv σ τ c R - Fantideriv σ τ c (-R) := by
  have hderiv : ∀ x ∈ Set.Icc (-R) R, HasDerivAt (Fantideriv σ τ c) (lincombo σ τ c x) x := by
    intro x hx; exact hasDerivAt_Fantideriv_lincombo (σ := σ) (τ := τ) (c := c) hσ hτ x
  simpa using intervalIntegral.integral_hasDerivAt_eq_sub (f := fun x => Fantideriv σ τ c x) (f' := fun x => lincombo σ τ c x) hderiv

end Antiderivative

end PoissonKernelAnalysis
end RS
end RH
