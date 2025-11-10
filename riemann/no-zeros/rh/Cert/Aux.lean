import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib

namespace MeasureTheory

lemma integral_comp_smul_sub_pos
    {f : ℝ → ℝ} {σ a : ℝ} (hσ : 0 < σ) :
    ∫ t : ℝ, f ((t - a) / σ) = σ * ∫ u : ℝ, f u := by
  let Φ : ℝ → ℝ := fun u => σ * u + a
  have h_deriv : ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt Φ σ x := by
    intro x _; simpa [Φ] using ((hasDerivAt_id x).const_mul σ).add_const a
  have h_inj : Set.InjOn Φ (Set.univ : Set ℝ) := by
    intro x _ y _ hxy
    have hx : σ * x = σ * y := by
      have := congrArg (fun z => z - a) hxy
      simpa [Φ, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
             mul_comm, mul_left_comm, mul_assoc] using this
    exact mul_left_cancel₀ (ne_of_gt hσ) hx
  have h :=
    integral_image_eq_integral_abs_deriv_smul
      (s := (Set.univ : Set ℝ)) (f := Φ) (f' := fun _ => σ)
      (hs := MeasurableSet.univ)
      (hf' := fun x hx => (h_deriv x hx).hasDerivWithinAt)
      (hf := h_inj)
      (g := fun t => f ((t - a) / σ))
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hrange₀ : Set.range (fun u : ℝ => a + σ * u) = Set.univ := by
    ext y; constructor
    · intro _; simp
    · intro _; refine ⟨(y - a) / σ, ?_⟩
      field_simp [hσne]
  have hrange : Set.range Φ = Set.univ := by
    simpa [Φ, add_comm, mul_comm] using hrange₀
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hcomp2 : (fun x : ℝ => σ * f (σ * x / σ)) = (fun x => σ * f x) := by
    funext x
    have : σ * x / σ = x := by field_simp [hσne]
    simp [this]
  simpa [hrange, Φ, hcomp2, abs_of_pos hσ, setIntegral_univ, integral_mul_left]
    using h

variable {E : Type*} [NormedAddCommGroup E] --[NormedSpace ℝ E]
variable {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]

/-- If `f` is continuous on `uIcc a b`, then `f` is interval integrable on `a..b`. -/
lemma intervalIntegrable_of_continuousOn
    {f : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Set.uIcc a b)) :
    IntervalIntegrable f μ a b :=
  ContinuousOn.intervalIntegrable hf

/-- Convenience variant for continuous functions. -/
lemma intervalIntegrable_of_continuous
    {f : ℝ → E} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable f μ a b :=
  hf.intervalIntegrable a b

end MeasureTheory

namespace Real

@[simp] lemma rpow_neg_natCast_of_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ (-(n : ℝ)) = (x ^ n)⁻¹ := by
  -- rpow_neg holds for nonnegative bases; then rewrite the RHS with rpow_natCast
  simpa [Real.rpow_natCast] using (Real.rpow_neg (x := x) (y := (n : ℝ)) hx)

lemma rpow_neg_natCast_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ (-(n : ℝ)) = (x ^ n)⁻¹ :=
  rpow_neg_natCast_of_nonneg hx.le n

end Real

namespace Metric

open Real MeasureTheory Filter Topology

variable {α : Type*} [PseudoMetricSpace α]

@[simp]
theorem tendsto_atBot_atBot {α : Type*} {β : Type*} [Nonempty α]
    [Preorder α] [IsDirected α (· ≥ ·)] [Preorder β] {f : α → β} :
    Tendsto f atBot atBot ↔ ∀ b : β, ∃ i : α, ∀ a : α, a ≤ i → f a ≤ b := Filter.tendsto_atBot_atBot

omit [PseudoMetricSpace α] in
-- This is the ε-δ characterization for atBot
theorem tendsto_atBot {f : ℝ → α} [PseudoMetricSpace α] {a : α} :
    Tendsto f atBot (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ x ≤ N, dist (f x) a < ε := by
  classical
  constructor
  · intro hf ε hε
    -- switch to atTop via g t = f (-t)
    have hf' : Tendsto (fun t => f (-t)) atTop (𝓝 a) := hf.comp tendsto_neg_atTop_atBot
    rcases (Metric.tendsto_atTop.mp hf') ε hε with ⟨N, hN⟩
    refine ⟨-N, ?_⟩
    intro x hx
    have hx' : -x ≥ N := by simpa using (neg_le_neg hx)
    have h' := hN (-x) hx'
    simpa [neg_neg] using h'
  · intro h
    -- build the atTop statement for g t = f (-t), then switch back
    have h' : ∀ ε > 0, ∃ N, ∀ t ≥ N, dist (f (-t)) a < ε := by
      intro ε hε
      rcases h ε hε with ⟨N, hN⟩
      exact ⟨-N, by intro t ht; exact hN (-t) (by simpa using (neg_le_neg ht))⟩
    have hf' := (Metric.tendsto_atTop.mpr h').comp tendsto_neg_atBot_atTop
    have hcomp : ((fun n => f (-n)) ∘ Neg.neg) = f := by
      funext x; simp [Function.comp, neg_neg]
    simpa [hcomp] using hf'

end Metric

/-!
# Missing API for Improper Integrals

This file contains sketches and guidance for implementing the missing lemmas
needed to complete the proof of `integral_eq_tendsto_of_tendsto_atTop_atBot`.

## Overview

The main theorem states that if F is an antiderivative of f with limits at ±∞,
then the integral of f over ℝ equals the difference of those limits.

To prove this, we need to establish:
1. f is integrable (integrability from antiderivative limits)
2. The limit of interval integrals equals the full integral (exhaustion lemma)

-/

namespace MeasureTheory

open Real Filter Topology intervalIntegral

lemma abs_add_three (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  calc |a + b + c|
    _ = |(a + b) + c| := by ring_nf
    _ ≤ |a + b| + |c| := abs_add _ _
    _ ≤ |a| + |b| + |c| := by linarith [abs_add a b]

/-! ### Lemma 1: Integrability from Antiderivative Limits -/

/-- If f has an antiderivative F that converges at ±∞, then f is integrable. -/
lemma tendsto_intervalIntegral_of_hasDerivAt_of_tendsto
    {f F : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt F (f x) x)
    (hint_loc : ∀ a b : ℝ, IntegrableOn f (Set.uIcc a b))
    {L_top L_bot : ℝ}
    (hFtop : Tendsto F atTop (𝓝 L_top))
    (hFbot : Tendsto F atBot (𝓝 L_bot)) :
    Tendsto (fun R : ℝ => ∫ x in (-R)..R, f x) atTop (𝓝 (L_top - L_bot)) := by
  have hFTC (R : ℝ) :
      ∫ x in (-R)..R, f x = F R - F (-R) := by
    -- Oriented FTC works without assuming -R ≤ R
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      exact hderiv x
    · exact (hint_loc (-R) R).intervalIntegrable
  have hlim : Tendsto (fun R => F R - F (-R)) atTop (𝓝 (L_top - L_bot)) := by
    have h1 := hFtop
    have h2 : Tendsto (fun R => F (-R)) atTop (𝓝 L_bot) :=
      hFbot.comp tendsto_neg_atTop_atBot
    simpa using h1.sub h2
  have h_eq : (fun R : ℝ => ∫ x in (-R)..R, f x) = (fun R => F R - F (-R)) := by
    funext R; exact hFTC R
  simpa [h_eq]
    using hlim


/-! ### Lemma 2: Exhaustion by Symmetric Intervals -/

/-- The limit of integrals over symmetric expanding intervals equals
    the integral over the whole space. -/
lemma integral_eq_of_tendsto_intervalIntegral
    {f : ℝ → ℝ}
    (hf : Integrable f)
    (h_limit : ∃ L, Tendsto (fun R => ∫ x in (-R)..R, f x) atTop (𝓝 L)) :
    ∫ x : ℝ, f x = Classical.choose h_limit := by
  have key :
      Tendsto (fun R : ℝ => ∫ x in (-R)..R, f x) atTop (𝓝 (∫ x, f x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral
      (μ := volume) (f := f) (hfi := hf)
      (ha := tendsto_neg_atTop_atBot) (hb := tendsto_id)
  have h_tendsto_choose :
      Tendsto (fun R : ℝ => ∫ x in (-R)..R, f x) atTop (𝓝 (Classical.choose h_limit)) :=
    Classical.choose_spec h_limit

  exact tendsto_nhds_unique key h_tendsto_choose

/-! ### Lemma 3: Alternative Approach Using Ioi/Iic -/


/-! ### Main Theorem Using the Above Lemmas -/

/-- Complete proof using the helper lemmas. -/
theorem integral_eq_tendsto_of_tendsto_atTop_atBot
    {f F : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt F (f x) x)
    (hf : Integrable f)
    {L_top L_bot : ℝ}
    (hFtop : Tendsto F atTop (𝓝 L_top))
    (hFbot : Tendsto F atBot (𝓝 L_bot)) :
    ∫ x : ℝ, f x = L_top - L_bot := by
  exact integral_of_hasDerivAt_of_tendsto hderiv hf hFbot hFtop

end MeasureTheory

namespace Real
open Filter Topology Real

lemma tendsto_one_div_atTop_zero : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
  simpa only [one_div] using tendsto_inv_atTop_zero

/-- The limit of x/(1+x²) as x → +∞ is 0. -/
lemma tendsto_div_one_add_sq_atTop :
    Tendsto (fun x => x / (1 + x^2)) atTop (𝓝 (0 : ℝ)) := by
  refine (tendsto_zero_iff_norm_tendsto_zero).mpr ?_
  have h_eq : (fun x : ℝ => ‖x / (1 + x^2)‖) =ᶠ[atTop]
              (fun x : ℝ => x / (1 + x^2)) := by
     filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
     rw [Real.norm_eq_abs, abs_of_nonneg]
     exact div_nonneg (le_of_lt hx) (by positivity)
  have key : ∀ᶠ (x : ℝ) in (atTop : Filter ℝ), x / (1 + x^2) ≤ 1 / x := by
    refine (eventually_gt_atTop (0 : ℝ)).mono ?_
    intro x hx
    have hden1 : 0 < 1 + x^2 := by positivity
    have hden2 : 0 < x := hx
    have hmul : x * x ≤ 1 * (1 + x^2) := by nlinarith [sq_nonneg x]
    simpa using ((div_le_div_iff hden1 hden2).2 hmul)

  have lower : ∀ᶠ (x : ℝ) in (atTop : Filter ℝ), 0 ≤ x / (1 + x^2) := by
    refine (eventually_gt_atTop (0 : ℝ)).mono ?_
    intro x hx
    exact div_nonneg (le_of_lt hx) (by positivity)

  have h_tend :
      Tendsto (fun x : ℝ => x / (1 + x^2)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      tendsto_one_div_atTop_zero
      lower
      key
  exact Tendsto.congr' (EventuallyEq.symm h_eq) h_tend

/-- Scaling lemma for the limit. -/
lemma tendsto_div_const_mul_one_add_sq_atTop (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun x => x / (c * (1 + x^2))) atTop (𝓝 0) := by
  have : (fun x => x / (c * (1 + x^2))) =
         (fun x => (1/c) * (x / (1 + x^2))) := by
    ext x; field_simp [hc]
  rw [this]
  exact by simpa [mul_zero] using (tendsto_div_one_add_sq_atTop.const_mul (1 / c))


/-- arctan tends to π/2 at +∞. -/
lemma tendsto_arctan_div_two_atTop :
    Tendsto (fun x => arctan x / 2) atTop (𝓝 (π / 4)) := by
  have : (π / 4 : ℝ) = (π / 2) / 2 := by ring
  rw [this]
  have h := tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  exact h.div_const 2

/-- arctan tends to -π/2 at -∞. -/
lemma tendsto_arctan_div_two_atBot :
    Tendsto (fun x => arctan x / 2) atBot (𝓝 (-π / 4)) := by
  rw [show (-π / 4 : ℝ) = (-(π / 2)) / 2 by ring]
  exact (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).div_const 2

end Real



/-!
# Proof of : ∫ 1/(1+x²)² = π/2

-/

namespace IntegralOneOverOnePlusSqSq
open Real

-- Define the antiderivative
noncomputable def F (x : ℝ) : ℝ := x / (2 * (1 + x^2)) + arctan x / 2

-- Key algebraic lemma for simplification
lemma algebra_simp (x : ℝ) (_ : 1 + x^2 ≠ 0) :
    (2 * (1 + x^2) - 4 * x^2) / (4 * (1 + x^2)^2) + 1 / (2 * (1 + x^2)) =
    ((1 + x^2)^2)⁻¹ := by
  field_simp
  ring

-- The derivative of F is our integrand
theorem hasDerivAt_F (x : ℝ) :
    HasDerivAt F ((1 + x^2)^2)⁻¹ x := by
  unfold F
  -- Derivative of x / (2 * (1 + x^2))
  have h_frac : HasDerivAt (fun x => x / (2 * (1 + x^2)))
      ((2 * (1 + x^2) * 1 - x * (2 * 2 * x)) / (2 * (1 + x^2))^2) x := by
    have h_num : HasDerivAt (fun x => x) 1 x := hasDerivAt_id' x
    have h_den : HasDerivAt (fun x => 2 * (1 + x^2)) (2 * 2 * x) x := by
      have : HasDerivAt (fun x => 1 + x^2) (2 * x) x := by
        convert (hasDerivAt_id' x).pow 2 |>.add (hasDerivAt_const x 1) using 1
        · ext; ring
        · ring
      convert this.const_mul 2 using 1
      ring
    have h_ne : 2 * (1 + x^2) ≠ 0 := by positivity
    convert h_num.div h_den h_ne using 1
    ring
  -- Derivative of arctan x / 2
  have h_arctan : HasDerivAt (fun x => arctan x / 2)
      (((1 + x^2)⁻¹) / 2) x := by
    convert (hasDerivAt_arctan x).div_const 2 using 1
    ring
  convert h_frac.add h_arctan using 1
  have : (2 * (1 + x^2) * 1 - x * (2 * 2 * x)) / (2 * (1 + x^2))^2 + ((1 + x^2)⁻¹) / 2 =
         ((1 + x^2)^2)⁻¹ := by
    have h0 : 1 + x^2 ≠ 0 := by positivity
    calc (2 * (1 + x^2) * 1 - x * (2 * 2 * x)) / (2 * (1 + x^2))^2 + ((1 + x^2)⁻¹) / 2
        = (2 * (1 + x^2) - 4 * x^2) / (2 * (1 + x^2))^2 + ((1 + x^2)⁻¹) / 2 := by ring
      _ = (2 * (1 + x^2) - 4 * x^2) / (4 * (1 + x^2)^2) + 1 / (2 * (1 + x^2)) := by
          rw [pow_two (2 * (1 + x^2))]
          rw [inv_eq_one_div]
          field_simp
          ring
      _ = ((1 + x^2)^2)⁻¹ := algebra_simp x h0
  exact id (Eq.symm this)

-- F is differentiable everywhere
theorem differentiable_F : Differentiable ℝ F := by
  intro x
  exact (hasDerivAt_F x).differentiableAt

-- Integral on a finite interval
theorem integral_on_interval (a b : ℝ) :
    ∫ x in a..b, ((1 + x^2)^2)⁻¹ = F b - F a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · -- Has derivative
    intro x _
    exact hasDerivAt_F x
  · -- Integrability of the derivative (i.e., the integrand)
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · continuity
    · intro x
      positivity

open Filter Real Topology

-- Limit at +∞
theorem F_limit_atTop : Tendsto F atTop (𝓝 (π / 4)) := by
  unfold F
  have h1 : Tendsto (fun (x : ℝ) => x / (2 * (1 + x^2))) atTop (𝓝 0) := by
    have : (fun (x : ℝ) => x / (2 * (1 + x^2))) = (fun (x : ℝ) => (1 / 2) * (x / (1 + x^2))) := by
      ext x; field_simp
    rw [this]
    convert Real.tendsto_div_one_add_sq_atTop.const_mul (1 / 2) using 1
    norm_num
  have h2 : Tendsto (fun (x : ℝ) => arctan x / 2) atTop (𝓝 (π / 4)) :=
    Real.tendsto_arctan_div_two_atTop
  have hsum :
      Tendsto (fun x : ℝ => x / (2 * (1 + x^2)) + arctan x / 2) atTop (𝓝 (0 + π / 4)) :=
    h1.add h2
  simpa [F, add_comm, add_left_comm, add_assoc, add_zero] using hsum

lemma tendsto_div_one_add_sq_atBot :
    Tendsto (fun x : ℝ => x / (1 + x^2)) atBot (𝓝 0) := by
  -- use oddness and `tendsto_neg_atBot_atTop`
  have h := (Real.tendsto_div_one_add_sq_atTop.neg).comp tendsto_neg_atBot_atTop
  have hfun :
      ((fun x : ℝ => -(x / (1 + x * x))) ∘ Neg.neg)
        = fun x : ℝ => x / (1 + x * x) := by
    funext x
    simp [Function.comp, neg_div, neg_neg]
  simpa [pow_two, hfun] using h

lemma tendsto_div_2mul_one_add_sq_atBot :
    Tendsto (fun x : ℝ => x / (2 * (1 + x^2))) atBot (𝓝 0) := by
  -- equal to `(1/2) * (x / (1 + x^2))`
  have := (tendsto_div_one_add_sq_atBot.const_mul (1 / 2))
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

theorem F_limit_atBot : Tendsto F atBot (𝓝 (-π / 4)) := by
  unfold F
  have h1 := tendsto_div_2mul_one_add_sq_atBot
  have h2 : Tendsto (fun (x : ℝ) => arctan x / 2) atBot (𝓝 (-π / 4)) :=
    Real.tendsto_arctan_div_two_atBot
  have hsum :
      Tendsto (fun x : ℝ => x / (2 * (1 + x^2)) + arctan x / 2) atBot (𝓝 (0 + (-π / 4))) :=
    h1.add h2
  simpa [F, add_comm, add_left_comm, add_assoc, add_zero] using hsum

open MeasureTheory
-- Integrability by comparison (decay as x^{-4})
lemma integrable_inv_one_add_sq_sq :
    Integrable (fun x : ℝ => ((1 + x^2)^2)⁻¹) := by
  -- use the Japanese bracket lemma with r = 4
  have h :
      Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := 4) (by norm_num)
  -- simplify the exponent
  have h' : Integrable (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-2 : ℝ)) := by
    convert h using 2; norm_num
  -- rewrite to our concrete integrand
  refine (integrable_congr ?_).1 h'
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- (1+|x|^2)^(-2) = ((1+|x|^2)^2)⁻¹ = ((1+x^2)^2)⁻¹
  simp only [Real.norm_eq_abs, sq_abs]
  norm_cast

theorem integral_one_div_one_plus_sq_sq :
    ∫ u : ℝ, ((u^2 + 1)^2)⁻¹ = π / 2 := by
  have h_comm : (fun u : ℝ => ((u^2 + 1)^2)⁻¹) = fun u => ((1 + u^2)^2)⁻¹ := by
    ext u; ring_nf
  rw [h_comm]
  -- integrability by comparison (proved separately)
  -- integrability by comparison (proved separately)
  have hf : Integrable (fun x : ℝ => ((1 + x^2)^2)⁻¹) :=
    integrable_inv_one_add_sq_sq
  have h :=
    (MeasureTheory.integral_of_hasDerivAt_of_tendsto
      (f := F) (f' := fun x => ((1 + x^2)^2)⁻¹)
      (hderiv := hasDerivAt_F) (hf' := hf)
      (hbot := F_limit_atBot) (htop := F_limit_atTop))
  -- RHS simplifies: π/4 - (-π/4) = π/2
  convert h using 1
  ring

end IntegralOneOverOnePlusSqSq

-- Export the main result
theorem integral_one_div_one_plus_sq_sq' :
    ∫ u : ℝ, ((u^2 + 1)^2)⁻¹ = Real.pi / 2 :=
  IntegralOneOverOnePlusSqSq.integral_one_div_one_plus_sq_sq

open Real MeasureTheory

/-- Interval version of change of variables. -/
lemma integral_comp_div_sub_pos_Ioo
    (f : ℝ → ℝ) (σ a b c : ℝ) (hσ : 0 < σ)
    (_ : ContinuousOn f Set.univ) :
    ∫ t in a..b, f ((t - c) / σ) =
    σ * ∫ u in (a - c)/σ..(b - c)/σ, f u := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have h :=
    (intervalIntegral.integral_comp_div_add
      (f := f) (a := a) (b := b) (c := σ) (d := -c / σ) hσne)
  simpa [sub_eq_add_neg, add_div, smul_eq_mul] using h


lemma integral_comp_smul_sub_pos_interval
    (f : ℝ → ℝ) (σ a b c : ℝ) (hσ : 0 < σ) :
    ∫ t in a..b, f ((t - c) / σ) =
    σ * ∫ u in (a - c)/σ..(b - c)/σ, f u := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have h :=
    (intervalIntegral.integral_comp_div_add
      (f := f) (a := a) (b := b) (c := σ) (d := -c / σ) hσne)
  simpa [sub_eq_add_neg, add_div, smul_eq_mul] using h

lemma integral_forms_equiv :
    (fun u : ℝ => (1 / (u^2 + 1))^2) = fun u => ((u^2 + 1)^2)⁻¹ := by
  ext u
  field_simp

theorem integral_one_div_one_plus_sq_sq_inv :
    ∫ u : ℝ, ((u^2 + 1)^2)⁻¹ ∂volume = π / 2 :=
  integral_one_div_one_plus_sq_sq'

theorem integral_one_div_one_plus_sq_sq :
    ∫ u : ℝ, (1 / (u^2 + 1))^2 ∂volume = π / 2 := by
  rw [integral_forms_equiv]
  exact integral_one_div_one_plus_sq_sq_inv

theorem integral_one_div_one_plus_sq_sq_direct :
    ∫ u : ℝ, (1 / (u^2 + 1))^2 = π / 2 := by
  rw [integral_forms_equiv]
  exact integral_one_div_one_plus_sq_sq'

-- Restatement with clear equivalence
example :
    (∫ u : ℝ, (1 / (u^2 + 1))^2 ∂volume = π / 2) ↔
    (∫ u : ℝ, ((u^2 + 1)^2)⁻¹ ∂volume = π / 2) := by
  constructor <;> intro h
  · rw [integral_forms_equiv] at h; exact h
  · rw [integral_forms_equiv]; exact h

open MeasureTheory Real

open Real MeasureTheory Filter Topology


namespace ParameterIntegral

open MeasureTheory TopologicalSpace

/-- Continuity of parameter-dependent integrals (dominated convergence). -/
theorem continuousOn_integral_of_dominated
    {α β E : Type*} [MeasurableSpace α] [TopologicalSpace β] [FirstCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E]
    (f : α → β → E) (μ : Measure α) (S : Set β)
    (h_meas : ∀ b ∈ S, AEStronglyMeasurable (fun a => f a b) μ)
    (h_cont : ∀ a, ContinuousOn (f a) S)
    (g : α → ℝ) (hg : Integrable g μ)
    (h_bound : ∀ b ∈ S, ∀ᵐ a ∂μ, ‖f a b‖ ≤ g a) :
    ContinuousOn (fun b => ∫ a, f a b ∂μ) S := by
  apply continuousOn_of_dominated
  · intro b hb; exact h_meas b hb
  · intro b hb; exact h_bound b hb
  · exact hg
  ·
    have h_cont_ae : ∀ᵐ a ∂μ, ContinuousOn (fun b => f a b) S :=
      Filter.Eventually.of_forall h_cont
    simpa using h_cont_ae
