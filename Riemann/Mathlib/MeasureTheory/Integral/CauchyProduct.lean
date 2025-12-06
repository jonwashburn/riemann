import Mathlib
import Riemann.Mathlib.MeasureTheory.Integral.RationalIntegrals

/-!
# Cauchy Product Integrals

This file contains the computation of the Cauchy-Cauchy product integral:
∫ℝ 1/((u²+1)((u-c)²+1)) = π·(2/(c²+4))

## Main results

* `MeasureTheory.integrable_one_div_one_plus_sq` - Integrability of 1/(1+x²)
* `MeasureTheory.integral_one_div_one_plus_sq` - ∫ 1/(1+x²) = π
* `MeasureTheory.cauchy_partial_fraction` - Partial fraction decomposition
* `MeasureTheory.integrable_cauchy_prod_shift` - Integrability of the product
* `MeasureTheory.integral_cauchy_prod_shift` - The main integral formula

## Implementation notes

For c ≠ 0, the proof constructs an explicit antiderivative using partial fractions,
then analyzes the limits at ±∞. The key insight is that A + C = 0 causes the
logarithmic terms to cancel in the limit.

-/

open MeasureTheory Real Filter Topology

namespace MeasureTheory

-- Integrability and full-line integral for 1/(1+x^2)
lemma integrable_one_div_one_plus_sq :
    Integrable (fun x : ℝ => 1 / (1 + x^2)) := by
  -- compare with (1 + ‖x‖^2)^(-1), which is integrable (r = 2)
  have h :
      Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(2 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := 2) (by norm_num)
  have h' : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) := by
    convert h using 2; norm_num
  refine (integrable_congr ?_).1 h'
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- (1+|x|^2)^(-1) = (1 + x^2)^(-1) = 1/(1+x^2)
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Real.rpow_neg_one]
  rw [← one_div]

theorem integral_one_div_one_plus_sq :
    ∫ x : ℝ, 1 / (1 + x^2) = Real.pi := by
  simp

/-- Dominated integrability (real-valued): if `f` is a.e. strongly measurable,
`g` is integrable, `g ≥ 0` a.e., and `‖f‖ ≤ g` a.e., then `f` is integrable. -/
lemma integrable_of_dominated_of_integrable
  {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {f g : α → ℝ}
  (hf_meas : AEStronglyMeasurable f μ)
  (hg_int : Integrable g μ)
  (h_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
  Integrable f μ := by
  -- package measurability + finiteness
  exact Integrable.mono' hg_int hf_meas h_bound

/-- If `0 ≤ f ≤ g` a.e., `f` is a.e. strongly measurable, and `g` is integrable,
then `f` is integrable. Real-valued convenience wrapper. -/
lemma integrable_of_le_of_nonneg_of_le
  {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {f g : α → ℝ}
  (hf_meas : AEStronglyMeasurable f μ)
  (hg_int : Integrable g μ)
  (hf_nonneg : ∀ᵐ x ∂μ, 0 ≤ f x)
  (h_le : ∀ᵐ x ∂μ, f x ≤ g x) :
  Integrable f μ := by
  -- from 0 ≤ f and f ≤ g we get ‖f‖ ≤ g and g ≥ 0
  have h_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x :=
    (hf_nonneg.and h_le).mono (fun x hx => by
      simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  exact integrable_of_dominated_of_integrable hf_meas hg_int h_bound

/-- Partial fraction decomposition for 1/((u^2+1)((u-c)^2+1)) when c ≠ 0. -/
lemma cauchy_partial_fraction (c : ℝ) (hc : c ≠ 0) :
  ∀ u : ℝ,
    1 / ((u^2 + 1) * ((u - c)^2 + 1))
      =
    (((2 / (c * (c^2 + 4))) * u) + (1 / (c^2 + 4))) / (u^2 + 1)
    + ((-(2 / (c * (c^2 + 4))) * (u - c)) + (1 / (c^2 + 4))) / ((u - c)^2 + 1) := by
  intro u
  have h1 : (u^2 + 1) ≠ 0 := by positivity
  have h2 : ((u - c)^2 + 1) ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

-- Integrability of the Cauchy–Cauchy product for any shift c
lemma integrable_cauchy_prod_shift (c : ℝ) :
  Integrable (fun u : ℝ => 1 / ((u^2 + 1) * ((u - c)^2 + 1))) := by
  -- pointwise domination by 1 / (1 + u^2)
  have hdom :
    ∀ u, 0 ≤ 1 / ((u^2 + 1) * ((u - c)^2 + 1)) ∧
         1 / ((u^2 + 1) * ((u - c)^2 + 1)) ≤ 1 / (u^2 + 1) := by
    intro u
    constructor
    · positivity
    · have hpos : 0 < u^2 + 1 := by positivity
      have hden₂ : 1 ≤ ((u - c)^2 + 1) := by
        have : 0 ≤ (u - c)^2 := sq_nonneg _
        linarith [this]
      have hle_den : (u^2 + 1) ≤ (u^2 + 1) * ((u - c)^2 + 1) := by
        calc (u^2 + 1)
            = (u^2 + 1) * 1 := by ring
          _ ≤ (u^2 + 1) * ((u - c)^2 + 1) :=
              mul_le_mul_of_nonneg_left hden₂ (le_of_lt hpos)
      exact
        (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hpos hle_den)
  have hg : Integrable (fun u : ℝ => 1 / (u^2 + 1)) :=
    by simpa [add_comm] using integrable_one_div_one_plus_sq
  -- measurability
  have h_meas_f :
      AEStronglyMeasurable (fun u : ℝ => 1 / ((u^2 + 1) * ((u - c)^2 + 1))) := by
    -- inverse is continuous away from 0; denominators are never 0
    have h1c : Continuous (fun u : ℝ => (u^2 + 1)⁻¹) :=
      ((continuous_id.pow 2).add continuous_const).inv₀ (by intro u; positivity)
    have h2c : Continuous (fun u : ℝ => ((u - c)^2 + 1)⁻¹) :=
      (((continuous_id.sub continuous_const).pow 2).add continuous_const).inv₀ (by intro u; positivity)
    have h1m : AEStronglyMeasurable (fun u : ℝ => (u^2 + 1)⁻¹) := h1c.aestronglyMeasurable
    have h2m : AEStronglyMeasurable (fun u : ℝ => ((u - c)^2 + 1)⁻¹) := h2c.aestronglyMeasurable
    have hprod :
        AEStronglyMeasurable (fun u : ℝ => (u^2 + 1)⁻¹ * ((u - c)^2 + 1)⁻¹) :=
      h1m.mul h2m
    have hEq :
        (fun u : ℝ => (u^2 + 1)⁻¹ * ((u - c)^2 + 1)⁻¹)
          = (fun u : ℝ => 1 / ((u^2 + 1) * ((u - c)^2 + 1))) := by
      funext u
      simp_rw [one_div]; field_simp
    aesop
  -- dominated convergence-type integrability criterion
  exact integrable_of_le_of_nonneg_of_le
    (hf_meas := h_meas_f)
    (hg_int := hg)
    (hf_nonneg := Filter.Eventually.of_forall (fun u => (hdom u).1))
    (h_le := Filter.Eventually.of_forall (fun u => (hdom u).2))

-- Base integral for c = 0
lemma integral_cauchy_prod_shift_zero :
  ∫ u : ℝ, 1 / ((u^2 + 1) * ((u - 0)^2 + 1)) = Real.pi / 2 := by
  have hform :
      (fun u : ℝ => 1 / ((u^2 + 1) * ((u - 0)^2 + 1)))
        = (fun u : ℝ => (1 / (u^2 + 1))^2) := by
    funext u
    simp [sub_zero, sq]
  simp_rw [hform, integral_one_div_one_plus_sq_sq]

-- Antiderivative (for c ≠ 0) via the PF decomposition
lemma cauchy_pf_antideriv (c : ℝ) (hc : c ≠ 0) :
  ∃ F : ℝ → ℝ,
    (∀ u, HasDerivAt F (1 / ((u^2 + 1) * ((u - c)^2 + 1))) u)
    ∧ ∃ A B C D : ℝ,
        A = 2 / (c * (c^2 + 4)) ∧
        B = 1 / (c^2 + 4) ∧
        C = -A ∧
        D = 1 / (c^2 + 4) := by
  classical
  -- decomposition constants
  let A : ℝ := 2 / (c * (c^2 + 4))
  let B : ℝ := 1 / (c^2 + 4)
  let C : ℝ := -A
  let D : ℝ := 1 / (c^2 + 4)
  -- antiderivative
  let F : ℝ → ℝ := fun u =>
      (A / 2) * Real.log (1 + u^2)
    + (C / 2) * Real.log (1 + (u - c)^2)
    + B * Real.arctan u
    + D * Real.arctan (u - c)
  have h_pf := cauchy_partial_fraction c hc
  have hderiv : ∀ u,
      HasDerivAt F (1 / ((u^2 + 1) * ((u - c)^2 + 1))) u := by
    intro u
    -- pieces
    have hA : HasDerivAt (fun u => (A / 2) * Real.log (1 + u^2))
               (A * u / (1 + u^2)) u := by
      have : HasDerivAt (fun u : ℝ => Real.log (1 + u^2)) (2 * u / (1 + u^2)) u := by
        have hden : HasDerivAt (fun u : ℝ => 1 + u^2) (2 * u) u := by
          -- derivative of u^2 is 2*u; adding a constant 1 does not change it
          have hsq : HasDerivAt (fun u : ℝ => u^2) (2 * u) u := by
            simpa using (hasDerivAt_id' u).pow 2
          -- now derivative of u^2 + 1 is still 2*u
          simpa [add_comm] using hsq.add_const 1
        have hlog : HasDerivAt (fun u => Real.log (1 + u^2)) ((1 + u^2)⁻¹ * (2 * u)) u := by
          exact (hasDerivAt_log (by positivity)).comp u hden
        convert hlog using 1
        field_simp
      convert (this.const_mul (A / 2)) using 1
      field_simp
    have hC : HasDerivAt (fun u => (C / 2) * Real.log (1 + (u - c)^2))
                (C * (u - c) / (1 + (u - c)^2)) u := by
      have hden : HasDerivAt (fun u => 1 + (u - c)^2) (2 * (u - c)) u := by
        have h1 : HasDerivAt (fun u => (u - c)^2) (2 * (u - c)) u := by
          simpa using ((hasDerivAt_id' u).sub (hasDerivAt_const u c)).pow 2
        -- derivative of (u - c)^2 + 1 is still 2*(u - c)
        have h' : HasDerivAt (fun u => (u - c)^2 + 1) (2 * (u - c)) u := by
          simpa using h1.add_const 1
        -- rewrite (u - c)^2 + 1 as 1 + (u - c)^2
        simpa [add_comm] using h'
      have hlog : HasDerivAt (fun u => Real.log (1 + (u - c)^2))
                ((1 + (u - c)^2)⁻¹ * (2 * (u - c))) u := by
        exact (hasDerivAt_log (by positivity)).comp u hden
      have : HasDerivAt (fun u : ℝ => Real.log (1 + (u - c)^2))
                (2 * (u - c) / (1 + (u - c)^2)) u := by
        convert hlog using 1
        field_simp
      convert (this.const_mul (C / 2)) using 1
      field_simp
    have hB : HasDerivAt (fun u => B * Real.arctan u) (B / (1 + u^2)) u := by
      convert (hasDerivAt_arctan u).const_mul B using 1
      field_simp
    have hD : HasDerivAt (fun u => D * Real.arctan (u - c))
               (D / (1 + (u - c)^2)) u := by
      convert ((hasDerivAt_arctan (u - c)).comp u
        ((hasDerivAt_id' u).sub (hasDerivAt_const u c))).const_mul D using 1
      field_simp; simp
    -- sum and PF algebra
    have hsum := (hA.add hC).add (hB.add hD)
    have hpf' :
      ((A * u) / (1 + u ^ 2)) + (C * (u - c) / (1 + (u - c) ^ 2))
      + (B / (1 + u ^ 2)) + (D / (1 + (u - c) ^ 2))
        = 1 / ((u ^ 2 + 1) * ((u - c) ^ 2 + 1)) := by
      -- start from the PF identity and split numerators using `add_div`
      have h0 := (h_pf u).symm
      -- expand constants and normalize sums/denominators without `inv_eq_one_div`
      simpa [A, B, C, D, add_div, add_comm, add_left_comm, add_assoc,
              mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
        using h0
    -- combine with the derivative sum
    have hsum' :
      HasDerivAt F (((u - c) ^ 2 + 1)⁻¹ * (u ^ 2 + 1)⁻¹) u := by
      -- first turn the sum into 1 / ((u^2+1)((u-c)^2+1)) via PF, aligning the function to F
      have hfun_eq :
          (fun x =>
            (A / 2) * Real.log (1 + x^2)
            + (C / 2) * Real.log (1 + (x - c)^2)
            + (B * Real.arctan x + D * Real.arctan (x - c)))
          =ᶠ[𝓝 u] F :=
        Filter.Eventually.of_forall (by
          intro x
          simp [F, add_comm, add_left_comm, add_assoc])
      have hFsum :
          HasDerivAt F
            (A * u / (1 + u^2)
             + C * (u - c) / (1 + (u - c)^2)
             + (B / (1 + u^2) + D / (1 + (u - c)^2))) u :=
        HasDerivAt.congr_of_eventuallyEq hsum (EventuallyEq.symm hfun_eq)
      have : HasDerivAt F (1 / ((u ^ 2 + 1) * ((u - c) ^ 2 + 1))) u := by
        convert hFsum using 1
        rw [← hpf']
        ring
      -- then rewrite 1/(a*b) as b⁻¹ * a⁻¹
      convert this using 1
      field_simp
    convert hsum' using 1
    rw [one_div, mul_inv, mul_comm]
  refine ⟨F, hderiv, A, B, C, D, rfl, rfl, rfl, rfl⟩

open Filter Real Topology

set_option maxHeartbeats 800000 in
-- Limits of the antiderivative (for c ≠ 0)
lemma cauchy_pf_limits (c : ℝ) (_ : c ≠ 0) :
  ∃ F : ℝ → ℝ, ∃ A B C D : ℝ,
    A = 2 / (c * (c^2 + 4)) ∧ B = 1 / (c^2 + 4) ∧ C = -A ∧ D = 1 / (c^2 + 4) ∧
    (∀ x, F x =
      (A / 2) * Real.log (1 + x^2)
      + (C / 2) * Real.log (1 + (x - c)^2)
      + B * Real.arctan x
      + D * Real.arctan (x - c)) ∧
    Tendsto F atTop (𝓝 ((B + D) * (Real.pi / 2))) ∧
    Tendsto F atBot (𝓝 (-(B + D) * (Real.pi / 2))) := by
  classical
  -- Choose explicit constants and antiderivative candidate
  let A : ℝ := 2 / (c * (c^2 + 4))
  let B : ℝ := 1 / (c^2 + 4)
  let C : ℝ := -A
  let D : ℝ := 1 / (c^2 + 4)
  let F : ℝ → ℝ := fun u =>
      (A / 2) * Real.log (1 + u^2)
    + (C / 2) * Real.log (1 + (u - c)^2)
    + B * Real.arctan u
    + D * Real.arctan (u - c)
  have AplusC : A + C = 0 := by simp [C]
  -- arctan terms → ±π/2, log-ratio term → 0 (A + C = 0 cancels logs)
  have hF_top :
      Tendsto F atTop (𝓝 ((B + D) * (Real.pi / 2))) := by
    have hatan :
        Tendsto (fun u => B * Real.arctan u + D * Real.arctan (u - c)) atTop
                (𝓝 ((B + D) * (Real.pi / 2))) := by
      have h1 : Tendsto (fun u => B * Real.arctan u) atTop (𝓝 (B * (Real.pi / 2))) :=
        (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul B
      have h2 : Tendsto (fun u => D * Real.arctan (u - c)) atTop
                    (𝓝 (D * (Real.pi / 2))) := by
        have : Tendsto (fun u => u - c) atTop atTop :=
          IntegralOneOverOnePlusSqSq.tendsto_atTop_add_const_right (-c)
        exact ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp this).const_mul D
      convert h1.add h2 using 1
      ring_nf
    have hratio :
        Tendsto (fun u : ℝ => (1 + u^2) / (1 + (u - c)^2)) atTop (𝓝 (1 : ℝ)) := by
      have hlin :
          Tendsto (fun u : ℝ => (-2 * c) * (u / (1 + u^2))) atTop (𝓝 (0 : ℝ)) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (Real.tendsto_div_one_add_sq_atTop.const_mul (-2 * c))
      have hpow : Tendsto (fun u : ℝ => u ^ (2 : ℕ)) atTop atTop :=
        tendsto_pow_atTop (α := ℝ) (n := 2) (by decide)
      have hplus : Tendsto (fun u : ℝ => 1 + u^2) atTop atTop := by
        have h := Filter.tendsto_atTop_add_const_right
          (l := atTop) (f := fun u : ℝ => u^2) (C := (1 : ℝ)) hpow
        simpa [add_comm] using h
      have hconst :
          Tendsto (fun u : ℝ => (c^2 : ℝ) / (1 + u^2)) atTop (𝓝 (0 : ℝ)) := by
        have h := (Real.tendsto_one_div_atTop_zero.comp hplus).const_mul (c^2)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
      have hnum :
          Tendsto (fun u : ℝ => (-2 * c * u + c^2) / (1 + u^2)) atTop (𝓝 (0 : ℝ)) := by
        have := hlin.add hconst
        simpa [add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc,
          div_eq_mul_inv, add_div, sub_eq_add_neg, mul_add, add_mul] using this
      have hsum :
          Tendsto (fun u : ℝ => 1 + ((-2 * c * u + c^2) / (1 + u^2))) atTop (𝓝 (1 : ℝ)) := by
        simpa [add_zero] using (tendsto_const_nhds.add hnum)
      have hrewrite :
          (fun u =>
              (A / 2) * Real.log (1 + u^2) +
              (C / 2) * Real.log (1 + (u - c)^2))
            =
          fun u => (A / 2) * Real.log ((1 + u^2) / (1 + (u - c)^2)) := by
        funext u
        have hpos1 : 0 < 1 + u^2 := by positivity
        have hpos2 : 0 < 1 + (u - c)^2 := by positivity
        have hCneg : C = -A := by
          have := congrArg (fun x : ℝ => x - A) AplusC
          aesop
        calc
          A / 2 * Real.log (1 + u^2) + C / 2 * Real.log (1 + (u - c)^2)
              = A / 2 * Real.log (1 + u^2) + (-A) / 2 * Real.log (1 + (u - c)^2) := by
                simp [hCneg]
          _   = (A / 2) * (Real.log (1 + u^2) - Real.log (1 + (u - c)^2)) := by
                ring
          _   = (A / 2) * Real.log ((1 + u^2) / (1 + (u - c)^2)) := by
                have h := (Real.log_div hpos1.ne' hpos2.ne')
                have h' :
                    (A / 2) * (Real.log (1 + u^2) - Real.log (1 + (u - c)^2))
                      = (A / 2) * Real.log ((1 + u^2) / (1 + (u - c)^2)) := by
                  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
                    congrArg (fun t => (A / 2) * t) h.symm
                simpa [sub_eq_add_neg] using h'
      have hdeninv :
          Tendsto (fun u : ℝ => (1 + ((-2 * c * u + c^2) / (1 + u^2)))⁻¹)
            atTop (𝓝 (1 : ℝ)) := by
        have h := (continuousAt_inv₀ (by simp)).tendsto.comp hsum
        simpa [Function.comp, inv_one] using h
      have hratio :
          Tendsto (fun u : ℝ => (1 + u^2) / (1 + (u - c)^2)) atTop (𝓝 (1 : ℝ)) := by
        have hrewrite_ratio : (fun u : ℝ => (1 + u^2) / (1 + (u - c)^2)) =
            (fun u : ℝ => (1 + ((-2 * c * u + c^2) / (1 + u^2)))⁻¹) := by
          funext u
          have hden : (1 + u^2) ≠ 0 := by positivity
          have hcalc : 1 + (u - c)^2 = (1 + u^2) + (- 2 * c * u + c^2) := by ring
          calc
            (1 + u^2) / (1 + (u - c)^2)
                = (1 + u^2) / ((1 + u^2) + (- 2 * c * u + c^2)) := by simp [hcalc]
            _   = 1 / (1 + ((- 2 * c * u + c^2) / (1 + u^2))) := by
                  field_simp [hden]
            _   = (1 + ((- 2 * c * u + c^2) / (1 + u^2)))⁻¹ := by
                  simp [one_div]
        simpa [hrewrite_ratio] using hdeninv
      simpa [hrewrite] using hratio
    have hlog :
        Tendsto (fun u =>
            (A / 2) * Real.log (1 + u^2) +
            (C / 2) * Real.log (1 + (u - c)^2)) atTop (𝓝 0) := by
      have hlogRatio :
          Tendsto (fun u : ℝ => Real.log ((1 + u^2) / (1 + (u - c)^2))) atTop (𝓝 0) := by
        have h := (continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
        simpa [Function.comp, Real.log_one] using h
      have hmul := hlogRatio.const_mul (A / 2)
      have hrewrite :
          (fun u =>
              (A / 2) * Real.log (1 + u^2) +
              (C / 2) * Real.log (1 + (u - c)^2))
            =
          fun u => (A / 2) * Real.log ((1 + u^2) / (1 + (u - c)^2)) := by
        funext u
        have hpos1 : 0 < 1 + u^2 := by positivity
        have hpos2 : 0 < 1 + (u - c)^2 := by positivity
        have hCneg : C = -A := by
          have := congrArg (fun x : ℝ => x - A) AplusC
          aesop
        calc
          A / 2 * Real.log (1 + u^2) + C / 2 * Real.log (1 + (u - c)^2)
              = A / 2 * Real.log (1 + u^2) + (-A) / 2 * Real.log (1 + (u - c)^2) := by
                simp [hCneg]
          _   = (A / 2) * (Real.log (1 + u^2) - Real.log (1 + (u - c)^2)) := by
                ring
          _   = (A / 2) * Real.log ((1 + u^2) / (1 + (u - c)^2)) := by
                have h := Real.log_div hpos1.ne' hpos2.ne'
                simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
                  using congrArg (fun t => (A / 2) * t) h.symm
      simpa [hrewrite] using hmul
    have hsumF :
        Tendsto (fun u =>
          (A / 2) * Real.log (1 + u^2) +
          (C / 2) * Real.log (1 + (u - c)^2) +
          B * Real.arctan u +
          D * Real.arctan (u - c)) atTop
          (𝓝 ((B + D) * (Real.pi / 2))) := by
      simpa [add_comm, add_left_comm, add_assoc] using hlog.add hatan
    simpa [F, add_comm, add_left_comm, add_assoc] using hsumF
  have hF_bot :
      Tendsto F atBot (𝓝 (-(B + D) * (Real.pi / 2))) := by
    have hatan :
        Tendsto (fun u => B * Real.arctan u + D * Real.arctan (u - c)) atBot
                (𝓝 (-(B + D) * (Real.pi / 2))) := by
      have h1 : Tendsto (fun u => B * Real.arctan u) atBot (𝓝 (B * -(Real.pi / 2))) :=
        (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).const_mul B
      have h2 : Tendsto (fun u => D * Real.arctan (u - c)) atBot
                    (𝓝 (D * -(Real.pi / 2))) := by
        have : Tendsto (fun u => u - c) atBot atBot := by
          -- use the dedicated lemma for translations atBot
          simpa [sub_eq_add_neg] using
            IntegralOneOverOnePlusSqSq.tendsto_atBot_add_const_right (-c)
        exact ((tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp this).const_mul D
      convert h1.add h2 using 1
      ring_nf
    have hlog :
        Tendsto (fun u =>
            (A / 2) * Real.log (1 + u^2) +
            (C / 2) * Real.log (1 + (u - c)^2)) atBot (𝓝 0) := by
      have hlogRatio :
          Tendsto (fun u : ℝ => Real.log ((1 + u^2) / (1 + (u - c)^2))) atBot (𝓝 0) := by
        -- establish the ratio tends to 1 atBot
        have hlin :
            Tendsto (fun u : ℝ => (-2 * c) * (u / (1 + u^2))) atBot (𝓝 (0 : ℝ)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (IntegralOneOverOnePlusSqSq.tendsto_div_one_add_sq_atBot.const_mul (-2 * c))
        -- u^2 → +∞ as u → -∞
        have h_abs : Tendsto (fun u : ℝ => |u|) atBot atTop :=
          Filter.tendsto_abs_atBot_atTop
        have h_pow : Tendsto (fun v : ℝ => v ^ (2 : ℕ)) atTop atTop :=
          tendsto_pow_atTop (α := ℝ) (n := 2) (by decide)
        have h_u2 : Tendsto (fun u : ℝ => u ^ (2 : ℕ)) atBot atTop := by
          -- (|u|)^2 = u^2
          have h_comp :
              ((fun v : ℝ => v ^ (2 : ℕ)) ∘ fun u : ℝ => |u|)
                = (fun u : ℝ => u ^ (2 : ℕ)) := by
            funext u
            simp [Function.comp, sq_abs]
          simpa [h_comp] using (h_pow.comp h_abs)
        -- hence 1 + u^2 → +∞
        have hplus :
            Tendsto (fun u : ℝ => (u ^ (2 : ℕ)) + 1) atBot atTop :=
          Filter.tendsto_atTop_add_const_right (l := atBot)
            (f := fun u : ℝ => u ^ (2 : ℕ)) (C := (1 : ℝ)) h_u2
        -- c^2/(1+u^2) → 0
        have hconst :
            Tendsto (fun u : ℝ => (c ^ 2 : ℝ) / (1 + u ^ (2 : ℕ))) atBot (𝓝 (0 : ℝ)) := by
          have h_one_div := Real.tendsto_one_div_atTop_zero.comp hplus
          have h_mul := h_one_div.const_mul (c ^ 2 : ℝ)
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, add_comm] using h_mul
        -- (-2cu + c^2)/(1+u^2) → 0
        have hnum :
            Tendsto (fun u : ℝ => (-2 * c * u + c ^ 2) / (1 + u ^ (2 : ℕ))) atBot (𝓝 (0 : ℝ)) := by
          have := hlin.add hconst
          simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
            div_eq_mul_inv, add_div, sub_eq_add_neg, mul_add, add_mul] using this
        -- 1 + ... → 1, then take inverse
        have hsum :
            Tendsto (fun u : ℝ => 1 + ((-2 * c * u + c ^ 2) / (1 + u ^ (2 : ℕ)))) atBot (𝓝 (1 : ℝ)) := by
          simpa [add_zero] using (tendsto_const_nhds.add hnum)
        have hdeninv :
            Tendsto (fun u : ℝ => (1 + ((-2 * c * u + c ^ 2) / (1 + u ^ (2 : ℕ))))⁻¹)
              atBot (𝓝 (1 : ℝ)) := by
          have h := (continuousAt_inv₀ (by simp)).tendsto.comp hsum
          simpa [Function.comp, inv_one] using h
        -- algebra: rewrite the ratio as that inverse
        have hratio :
            Tendsto (fun u : ℝ => (1 + u ^ (2 : ℕ)) / (1 + (u - c) ^ 2)) atBot (𝓝 (1 : ℝ)) := by
          have hrewrite_ratio :
              (fun u : ℝ => (1 + u ^ (2 : ℕ)) / (1 + (u - c) ^ 2)) =
                (fun u : ℝ => (1 + ((-2 * c * u + c ^ 2) / (1 + u ^ (2 : ℕ))))⁻¹) := by
            funext u
            have hden : (1 + u ^ (2 : ℕ)) ≠ 0 := by positivity
            have hcalc : 1 + (u - c) ^ 2 = (1 + u ^ 2) + (-2 * c * u + c ^ 2) := by ring
            calc
              (1 + u ^ (2 : ℕ)) / (1 + (u - c) ^ 2)
                  = (1 + u ^ (2 : ℕ)) / ((1 + u ^ 2) + (-2 * c * u + c ^ 2)) := by simp [hcalc]
              _ = 1 / (1 + ((-2 * c * u + c ^ 2) / (1 + u ^ (2 : ℕ)))) := by
                    field_simp [hden]
              _ = (1 + ((-2 * c * u + c ^ 2) / (1 + u ^ (2 : ℕ))))⁻¹ := by
                    simp [one_div]
          simpa [hrewrite_ratio] using hdeninv
        -- conclude for log ∘ ratio
        have h := (continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
        simpa [Function.comp, Real.log_one] using h
      -- scale by A/2 and rewrite back to the original sum of logs
      have hmul := hlogRatio.const_mul (A / 2)
      have hrewrite :
          (fun u =>
              (A / 2) * Real.log (1 + u^2) +
              (C / 2) * Real.log (1 + (u - c)^2))
            =
          fun u => (A / 2) * Real.log ((1 + u^2) / (1 + (u - c)^2)) := by
        funext u
        have hpos1 : 0 < 1 + u^2 := by positivity
        have hpos2 : 0 < 1 + (u - c)^2 := by positivity
        have hCneg : C = -A := by
          have := congrArg (fun x : ℝ => x - A) AplusC
          simp [add_comm, add_left_comm, sub_eq_add_neg] at this
          aesop
        calc
          A / 2 * Real.log (1 + u^2) + C / 2 * Real.log (1 + (u - c)^2)
              = A / 2 * Real.log (1 + u^2) + (-A) / 2 * Real.log (1 + (u - c)^2) := by
                simp [hCneg]
          _   = (A / 2) * (Real.log (1 + u^2) - Real.log (1 + (u - c)^2)) := by
                ring
          _   = (A / 2) * Real.log ((1 + u^2) / (1 + (u - c)^2)) := by
                have h := Real.log_div hpos1.ne' hpos2.ne'
                simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
                  using congrArg (fun t => (A / 2) * t) h.symm
      simpa [hrewrite] using hmul
    have hsum := hlog.add hatan
    simpa [F, add_comm, add_left_comm, add_assoc] using hsum
  exact ⟨F, A, B, C, D, rfl, rfl, rfl, rfl,
    (by intro x; simp [F, add_comm, add_left_comm]),
    hF_top, hF_bot⟩

-- c ≠ 0 case of the full line integral
lemma integral_cauchy_prod_shift_ne_zero (c : ℝ) (hc : c ≠ 0) :
  ∫ u : ℝ, 1 / ((u^2 + 1) * ((u - c)^2 + 1)) = Real.pi * (2 / (c^2 + 4)) := by
  classical
  -- take F and limits (±∞) built from the explicit formula, together with its pointwise def
  rcases cauchy_pf_limits c hc with
    ⟨F, A, B, C, D, hA, hB, hC, hD, hFdef, htop, hbot⟩
  -- explicit expression, used to compute derivative
  let G : ℝ → ℝ :=
    fun u =>
      (A / 2) * Real.log (1 + u^2)
    + (C / 2) * Real.log (1 + (u - c)^2)
    + B * Real.arctan u
    + D * Real.arctan (u - c)
  -- A-term
  have hA' :
      ∀ x, HasDerivAt (fun t => (A / 2) * Real.log (1 + t^2))
            (A * x / (1 + x^2)) x := by
    intro x
    have hden : HasDerivAt (fun t : ℝ => 1 + t^2) (2 * x) x := by
      -- d/dt (t^2) = 2 * t, specialized at t = x
      have hsq : HasDerivAt (fun t : ℝ => t^2) (2 * x) x := by
        simpa using (hasDerivAt_id' x).pow 2
      -- d/dt (t^2 + 1) = 2 * t, specialized at t = x
      have h' : HasDerivAt (fun t : ℝ => t^2 + 1) (2 * x) x := by
        simpa using hsq.add_const 1
      -- rewrite t^2 + 1 as 1 + t^2
      simpa [add_comm] using h'
    have hlog : HasDerivAt (fun t => Real.log (1 + t^2))
      ((1 + x^2)⁻¹ * (2 * x)) x := by
      exact (hasDerivAt_log (by positivity)).comp x hden
    have hlog' : HasDerivAt (fun t => Real.log (1 + t^2))
              (2 * x / (1 + x^2)) x := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog
    have hA'' := (hlog'.const_mul (A / 2))
    have hconst : (A / 2) * (2 * x) = A * x := by ring
    simpa [div_eq_mul_inv, hconst, mul_comm, mul_left_comm, mul_assoc] using hA''
  -- C-term
  have hC' :
      ∀ x, HasDerivAt (fun t => (C / 2) * Real.log (1 + (t - c)^2))
            (C * (x - c) / (1 + (x - c)^2)) x := by
    intro x
    have hden : HasDerivAt (fun t => 1 + (t - c)^2) (2 * (x - c)) x := by
      have h1 : HasDerivAt (fun t => (t - c)^2) (2 * (x - c)) x := by
        simpa using ((hasDerivAt_id' x).sub (hasDerivAt_const x c)).pow 2
      -- derivative of (t - c)^2 + 1 is still 2 * (x - c)
      have h' : HasDerivAt (fun t => (t - c)^2 + 1) (2 * (x - c)) x := by
        simpa using h1.add_const 1
      -- rewrite (t - c)^2 + 1 as 1 + (t - c)^2
      simpa [add_comm] using h'
    have hlog : HasDerivAt (fun t => Real.log (1 + (t - c)^2))
              ((1 + (x - c)^2)⁻¹ * (2 * (x - c))) x :=
      (hasDerivAt_log (by positivity)).comp x hden
    have hlog' : HasDerivAt (fun t => Real.log (1 + (t - c)^2))
              (2 * (x - c) / (1 + (x - c)^2)) x := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog
    have hC'' := (hlog'.const_mul (C / 2))
    have hconstC : (C / 2) * (2 * (x - c)) = C * (x - c) := by ring
    simpa [div_eq_mul_inv, hconstC, mul_comm, mul_left_comm, mul_assoc] using hC''
  -- B-term
  have hB' :
      ∀ x, HasDerivAt (fun t => B * Real.arctan t)
            (B / (1 + x^2)) x := by
    intro x
    convert (hasDerivAt_arctan x).const_mul B using 1
    field_simp
  -- D-term
  have hD' :
      ∀ x, HasDerivAt (fun t => D * Real.arctan (t - c))
            (D / (1 + (x - c)^2)) x := by
    intro x
    convert ((hasDerivAt_arctan (x - c)).comp x
      ((hasDerivAt_id' x).sub (hasDerivAt_const x c))).const_mul D using 1
    field_simp; simp
  -- partial fraction identity → integrand
  have hpf :
    ∀ u, (A * u / (1 + u^2)
          + C * (u - c) / (1 + (u - c)^2)
          + (B / (1 + u^2) + D / (1 + (u - c)^2)))
        = 1 / ((u ^ 2 + 1) * ((u - c) ^ 2 + 1)) := by
    intro u
    have h0 := (cauchy_partial_fraction c hc u).symm
    simpa [hA, hB, hC, hD, add_div, add_comm, add_left_comm, add_assoc,
           mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using h0
  have hG : ∀ u,
      HasDerivAt G
        (A * u / (1 + u^2)
        + C * (u - c) / (1 + (u - c)^2)
        + (B / (1 + u^2) + D / (1 + (u - c)^2))) u := by
    intro u
    simpa [G, add_comm, add_left_comm, add_assoc]
      using (hA' u).add (hC' u) |>.add ((hB' u).add (hD' u))
  -- derivative of F via congruence along the neighborhood (use pointwise def)
  have hderiv : ∀ u, HasDerivAt F (1 / ((u ^ 2 + 1) * ((u - c) ^ 2 + 1))) u := by
    intro u
    have hfun_eq : (fun x => G x) =ᶠ[𝓝 u] F :=
      Filter.Eventually.of_forall (by intro x; simp [G, hFdef x])
    have hF' :
      HasDerivAt F
        (A * u / (1 + u^2)
         + C * (u - c) / (1 + (u - c)^2)
         + (B / (1 + u^2) + D / (1 + (u - c)^2))) u :=
      HasDerivAt.congr_of_eventuallyEq (hG u) (EventuallyEq.symm hfun_eq)
    -- rewrite the derivative into the integrand, and then as product of inverses
    have hF'' : HasDerivAt F (1 / ((u ^ 2 + 1) * ((u - c) ^ 2 + 1))) u := by
      simpa [hpf u] using hF'
    -- done
    exact hF''
  -- integrability and FTC
  have hint := integrable_cauchy_prod_shift c
  have hFTC :=
    integral_of_hasDerivAt_of_tendsto
      (hderiv := hderiv) (hf' := hint) (hbot := hbot) (htop := htop)
  -- evaluate RHS jump
  have hBD : B + D = 2 / (c^2 + 4) := by simp [hB, hD]; ring
  calc
    ∫ u : ℝ, 1 / ((u^2 + 1) * ((u - c)^2 + 1))
        = (B + D) * (Real.pi / 2) - (-(B + D) * (Real.pi / 2)) := hFTC
    _   = Real.pi * (B + D) := by ring
    _   = Real.pi * (2 / (c^2 + 4)) := by simp [hBD]

/-- The "base" Cauchy–Cauchy product integral:
    ∫ℝ 1/((u^2+1)((u-c)^2+1)) = π·(2)/(c^2+4). -/
theorem integral_cauchy_prod_shift (c : ℝ) :
    ∫ u : ℝ, 1 / ((u^2 + 1) * ((u - c)^2 + 1))
      = Real.pi * (2 / (c^2 + 4)) := by
  classical
  by_cases hc : c = 0
  · -- c = 0: known square integral
    subst hc
    -- ((u^2+1)^2)⁻¹ = (u^2+1)⁻¹*(u^2+1)⁻¹ and π*2/4 = π/2
    have hsq : ∫ u : ℝ, ((u ^ 2 + 1) ^ 2)⁻¹ = Real.pi / 2 :=
      integral_one_div_one_plus_sq_sq'
    have hprod :
        ∫ u : ℝ, (u ^ 2 + 1)⁻¹ * (u ^ 2 + 1)⁻¹ = Real.pi / 2 := by
      simpa [pow_two, one_div, mul_comm, mul_left_comm, mul_assoc] using hsq
    have hbase :
        ∫ u : ℝ, 1 / ((u ^ 2 + 1) * ((u - 0) ^ 2 + 1)) = Real.pi / 2 := by
      simpa [sub_zero, one_div, mul_comm, mul_left_comm, mul_assoc] using hprod
    have hπrewrite : Real.pi / 2 = Real.pi * (2 * (4 : ℝ)⁻¹) := by
      have : (1 / 2 : ℝ) = 2 / 4 := by norm_num
      calc
        Real.pi / 2 = Real.pi * (1 / 2) := by simp [div_eq_mul_inv]
        _ = Real.pi * (2 / 4) := by simp [this]
        _ = Real.pi * (2 * (4 : ℝ)⁻¹) := by simp [div_eq_mul_inv]
    simpa [hπrewrite] using hbase
  exact integral_cauchy_prod_shift_ne_zero c hc

end MeasureTheory
