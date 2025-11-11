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

/-!
# Parameter measurability and continuity for Poisson kernel integrals

Fix a finite set of shifts `Zk : Finset ℝ` and a measurable set `I ⊆ ℝ`.
For `σ > 0`, consider the Poisson kernel
`P σ y := σ / (y^2 + σ^2)` and the finite sum
`V σ t := ∑ γ ∈ Zk, P σ (t - γ)`. We prove:

* For any `0 < ε ≤ σ_max`, the map
  `σ ↦ ∫ t in I, (V σ t)^2` is `ContinuousOn` on `[ε, σ_max]`
  provided `I` is measurable and bounded.

* As a corollary, this map is a.e. strongly measurable on `(0, σ_max)`
  with respect to the restricted Lebesgue measure.

We rely on mathlib’s `continuousOn_of_dominated` lemma for parametric
integrals: continuity in the parameter follows from a uniform L¹ dominator
on the parameter set together with a.e. continuity in the parameter and
measurability in the space variable.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Set

namespace PoissonParam

/-- Poisson kernel `σ/(y^2+σ^2)` (with the usual normalization for the real line). -/
@[simp] def P (σ y : ℝ) : ℝ := σ / (y^2 + σ^2)

/-- Finite Poisson sum `V σ t = ∑_{γ∈Zk} P σ (t - γ)`. -/
@[simp] def V (Zk : Finset ℝ) (σ t : ℝ) : ℝ :=
  ∑ γ ∈ Zk, P σ (t - γ)

/-- Square of the finite Poisson sum (the integrand we care about). -/
@[simp] def Φ (Zk : Finset ℝ) (σ t : ℝ) : ℝ := (V Zk σ t)^2

/-- Basic continuity in `t` for fixed `σ`: `t ↦ Φ Zk σ t` is continuous. -/
lemma continuous_in_t (Zk : Finset ℝ) (σ : ℝ) (hσ : σ ≠ 0) :
    Continuous (fun t : ℝ => Φ Zk σ t) := by
  -- each summand `t ↦ P σ (t - γ)` is continuous (denominator never vanishes)
  have h_each : ∀ γ ∈ Zk, Continuous (fun t : ℝ => P σ (t - γ)) := by
    intro γ _; dsimp [P]
    have hden : Continuous fun t : ℝ => (t - γ)^2 + σ^2 := by continuity
    -- denominator is ≥ σ^2 > 0, so never zero
    have hden_ne : ∀ t, (t - γ)^2 + σ^2 ≠ 0 := by
      intro t
      have hσ2pos : 0 < σ^2 := by simpa using (sq_pos_iff.mpr hσ)
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hσ2pos)
    simpa using (continuous_const.div hden hden_ne)
  -- sum of continuous functions is continuous; then square
  have hsum : Continuous (fun t : ℝ => V Zk σ t) := continuous_finset_sum Zk h_each
  simp only [Φ]
  exact hsum.pow 2

/-- Continuity in `σ` on a compact range `[ε, σ_max]` for fixed `t`. -/
lemma continuousOn_in_sigma_on_Icc
    (Zk : Finset ℝ) {ε σmax : ℝ} (hε : 0 < ε) (_ : ε ≤ σmax) (t : ℝ) :
    ContinuousOn (fun σ : ℝ => Φ Zk σ t) (Icc ε σmax) := by
  -- Each summand `σ ↦ P σ (t - γ)` is continuous on `Icc ε σmax`
  have h_each : ∀ γ ∈ Zk, ContinuousOn (fun σ : ℝ => P σ (t - γ)) (Icc ε σmax) := by
    intro γ _; dsimp [P]
    -- continuity of numerator and denominator
    have hnum : ContinuousOn (fun σ : ℝ => σ) (Icc ε σmax) :=
      (continuous_id.continuousOn)
    have hden : ContinuousOn (fun σ : ℝ => (t - γ)^2 + σ^2) (Icc ε σmax) := by
      have : Continuous fun σ : ℝ => (t - γ)^2 + σ^2 := by continuity
      exact this.continuousOn
    -- denominator never vanishes on `[ε, σmax]` since `σ ≥ ε > 0`
    have hpos : ∀ σ ∈ Icc ε σmax, (t - γ)^2 + σ^2 ≠ 0 := by
      intro σ hσ
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (lt_of_lt_of_le hε hσ.1)))
    simpa using hnum.div hden hpos
  -- Sum of `ContinuousOn` functions is `ContinuousOn`; then square
  have hsum : ContinuousOn (fun σ : ℝ => V Zk σ t) (Icc ε σmax) :=
    continuousOn_finset_sum Zk h_each
  -- squaring preserves `ContinuousOn`
  have : ContinuousOn (fun σ : ℝ => (V Zk σ t)^2) (Icc ε σmax) :=
    hsum.pow 2
  simpa only [Φ] using this

/-- **Uniform L¹ domination on `[ε, σ_max]`** over a bounded measurable set `I`.

For `σ ∈ [ε, σ_max]`, all summands are ≤ `1/ε`, hence the square of the sum
is bounded by `((Zk.card : ℝ) / ε)^2`. This constant is integrable on
`volume.restrict I` because `I` is bounded and measurable. -/
lemma L1_dominator_const
    (Zk : Finset ℝ) {ε σmax : ℝ} (hε : 0 < ε) (_ : ε ≤ σmax)
    (I : Set ℝ) (hI : MeasurableSet I) (hI_bdd : Bornology.IsBounded I) :
    ∃ C > 0,
      Integrable (fun _ : ℝ => (C : ℝ)) (volume.restrict I)
      ∧ ∀ σ ∈ Icc ε σmax, ∀ᵐ t ∂(volume.restrict I),
           ‖Φ Zk σ t‖ ≤ C := by
  classical
  -- Finite measure of `I` from boundedness
  obtain ⟨R, hR⟩ : ∃ R ≥ (0 : ℝ), I ⊆ Metric.closedBall (0 : ℝ) R := by
    rcases hI_bdd.subset_closedBall (0 : ℝ) with ⟨R, hsub⟩
    exact ⟨max R 0, le_max_right _ _, by
      intro x hx
      have hx' := hsub hx
      -- `closedBall 0 R ⊆ closedBall 0 (max R 0)`
      exact (Metric.closedBall_subset_closedBall (le_max_left _ _)) hx'⟩
  have hμI_lt_top : (volume I) < ⊤ := by
    -- `closedBall 0 R` has finite measure in `ℝ`; use monotonicity
    have hsubset : I ⊆ Set.Icc (-R) R := by
      intro x hx
      have hx' : x ∈ Metric.closedBall (0 : ℝ) R := hR.2 hx
      -- closedBall in ℝ is `Icc (-R) R`
      have : Metric.closedBall (0 : ℝ) R = Set.Icc (-R) R := by
        ext x; simp [Metric.mem_closedBall, Real.norm_eq_abs, abs_le]
      simpa [this] using hx'
    have hvol : volume (Set.Icc (-R) R) < ⊤ := by
      -- Explicit finite volume for intervals on `ℝ`
      simp [Real.volume_Icc]
    exact (lt_of_le_of_lt (measure_mono hsubset) hvol)
  -- constant dominator
  let C : ℝ := max 1 (((Zk.card : ℝ) / ε)^2)
  have hCpos : 0 < C := by
    simp only [C]
    exact lt_max_iff.mpr (Or.inl one_pos)
  have hint_const : Integrable (fun _ : ℝ => (C : ℝ)) (volume.restrict I) := by
    -- integrability of a positive constant on a finite-measure set
    have : (volume.restrict I) Set.univ = volume I := by
      simp [Measure.restrict_apply, hI]
    -- Use `integrable_const` with finiteness of measure
    have h_fin : (volume.restrict I) Set.univ < ⊤ := by simpa [this] using hμI_lt_top
    simpa [C] using (integrable_const_iff.2 (Or.inr h_fin))
  refine ⟨C, hCpos, hint_const, ?_⟩
  intro σ hσ
  -- pointwise bound: `P σ (t-γ) ≤ 1/σ ≤ 1/ε`, hence the sum ≤ `card * (1/ε)`, then square
  have hσpos : 0 < σ := lt_of_lt_of_le hε (show ε ≤ σ from hσ.1)
  have h_le_one_div_eps :
      ∀ t γ, P σ (t - γ) ≤ 1 / ε := by
    intro t γ
    have h1 : P σ (t - γ) ≤ 1 / σ := by
      -- multiply inequality by positive `((t - γ)^2 + σ^2) * σ`
      -- equivalently show `σ^2 ≤ (t - γ)^2 + σ^2`
      have : σ^2 ≤ (t - γ)^2 + σ^2 := by
        have : 0 ≤ (t - γ)^2 := sq_nonneg _
        linarith
      -- `σ / A ≤ 1/σ` iff `σ^2 ≤ A`
      have : σ / ((t - γ)^2 + σ^2) ≤ σ / (σ^2) :=
        div_le_div_of_nonneg_left (le_of_lt hσpos) (sq_pos_of_pos hσpos) (by linarith)
      calc P σ (t - γ)
        _ = σ / ((t - γ)^2 + σ^2) := rfl
        _ ≤ σ / (σ^2) := this
        _ = 1 / σ := by field_simp; ring
    have : (1 / σ) ≤ (1 / ε) :=
      (one_div_le_one_div_of_le hε (show ε ≤ σ from hσ.1))
    exact le_trans h1 this
  -- bound a.e. (actually for all t)
  refine ((ae_restrict_iff' hI).2 ?_ : ∀ᵐ t ∂(volume.restrict I), ‖Φ Zk σ t‖ ≤ C)
  refine Filter.Eventually.of_forall ?_
  intro t
  have hsum_le : V Zk σ t ≤ (Zk.card : ℝ) * (1/ε) := by
    classical
    have : ∀ γ ∈ Zk, P σ (t - γ) ≤ 1 / ε := by
      intro γ _; exact h_le_one_div_eps t γ
    have hs := Finset.sum_le_sum this
    simpa [V, Finset.sum_const, nsmul_eq_mul] using hs
  have hsum_nonneg : 0 ≤ V Zk σ t := by
    -- all summands are ≥ 0
    have : ∀ γ ∈ Zk, 0 ≤ P σ (t - γ) := by
      intro γ _
      dsimp [P]
      apply div_nonneg
      · exact hσpos.le
      · positivity
    simpa [V] using (Finset.sum_nonneg this)
  have : (V Zk σ t)^2 ≤ ((Zk.card : ℝ) * (1/ε))^2 :=
    pow_le_pow_left hsum_nonneg hsum_le 2
  intro _
  -- turn into a norm inequality and rewrite `C`
  calc ‖Φ Zk σ t‖
    _ = |(V Zk σ t)^2| := by simp [Φ, Real.norm_eq_abs]
    _ = (V Zk σ t)^2 := abs_of_nonneg (sq_nonneg _)
    _ ≤ ((Zk.card : ℝ) * (1/ε))^2 := this
    _ ≤ C := by simp [C, one_div]; aesop

/-- **Continuity on compact σ‑ranges** away from 0.

If `I` is measurable and bounded, then for every `0 < ε ≤ σ_max` the function
`σ ↦ ∫ t in I, (∑ γ∈Zk, σ / ((t - γ)^2 + σ^2))^2` is continuous on `Icc ε σ_max`. -/
theorem continuousOn_integral_sq_poisson_Icc
    (Zk : Finset ℝ) (I : Set ℝ) (hI : MeasurableSet I) (hI_bdd : Bornology.IsBounded I)
    {ε σmax : ℝ} (hε : 0 < ε) (hεσ : ε ≤ σmax) :
    ContinuousOn
      (fun σ => ∫ t in I, (Φ Zk σ t)) (Icc ε σmax) := by
  -- Apply `continuousOn_of_dominated`
  set μ := (volume.restrict I)
  -- (1) measurability in `t` for each `σ`:
  have h_meas : ∀ σ ∈ Icc ε σmax, AEStronglyMeasurable (fun t => Φ Zk σ t) μ := by
    intro σ hσ
    have hσne : σ ≠ 0 := (lt_of_lt_of_le hε hσ.1).ne'
    exact (continuous_in_t Zk σ hσne).aestronglyMeasurable
  -- (2) a.e. continuity in `σ` on the parameter set:
  have h_cont_ae : ∀ᵐ t ∂μ, ContinuousOn (fun σ => Φ Zk σ t) (Icc ε σmax) := by
    -- We in fact have pointwise continuity, hence certainly a.e.
    apply Filter.Eventually.of_forall
    intro t
    exact continuousOn_in_sigma_on_Icc Zk hε hεσ t
  -- (3) existence of a uniform L¹ dominator on the parameter set:
  rcases L1_dominator_const Zk hε hεσ I hI hI_bdd with ⟨C, _, hintC, hbound⟩
  -- Conclude by the parametric dominated-continuity lemma
  apply continuousOn_of_dominated (F := fun σ t => Φ Zk σ t) (bound := fun _ => C)
  · -- measurability in `t` for each `σ ∈ S`
    exact h_meas
  · -- domination `‖f t σ‖ ≤ g t` a.e. in `t` for each `σ ∈ S`
    exact hbound
  · -- integrability of the dominator
    exact hintC
  · -- a.e. continuity in σ
    exact h_cont_ae

/-- **A.e. strong measurability on `(0, σ_max)` under restriction.**

From the previous continuity on compacts away from `0`,
we deduce a.e. strong measurability for the restricted measure on `Ioc 0 σ_max`. -/
theorem aestronglyMeasurable_integral_sq_poisson_Ioc
    (Zk : Finset ℝ) (I : Set ℝ) (hI : MeasurableSet I) (hI_bdd : Bornology.IsBounded I)
    {σmax : ℝ} (_ : 0 < σmax) :
    AEStronglyMeasurable
      (fun σ => ∫ t in I, (Φ Zk σ t))
      (volume.restrict (Ioc (0 : ℝ) σmax)) := by
  classical
  -- cover `(0, σmax)` by the increasing union of compacts `[1/(n+1), σmax]`
  have hcov :
      (Ioc (0 : ℝ) σmax) = ⋃ n : ℕ, Icc ((1 : ℝ) / (n + 1)) σmax := by
    ext σ; constructor
    · intro hσ
      rcases hσ with ⟨h0, hle⟩
      -- choose `n` with `1/(n+1) < σ`
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 : ℝ) / (n + 1) < σ := by
        -- standard archimedean argument
        have : 0 < σ := h0
        rcases exists_nat_one_div_lt this with ⟨n, hn⟩
        exact ⟨n, hn.trans_le le_rfl⟩
      refine mem_iUnion.2 ⟨n, ?_⟩
      exact ⟨le_of_lt hn, hle⟩
    · intro hσ
      rcases mem_iUnion.1 hσ with ⟨n, hn⟩
      have pos : 0 < (1 : ℝ) / (n + 1) := one_div_pos.mpr (Nat.cast_add_one_pos n)
      exact ⟨pos.trans_le hn.1, hn.2⟩
  -- on each compact `[1/(n+1), σmax]` the map is continuous hence strongly measurable
  have h_on : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun σ => ∫ t in I, (Φ Zk σ t))
        (volume.restrict (Icc ((1 : ℝ) / (n + 1)) σmax)) := by
    intro n
    -- continuity ⇒ measurability ⇒ a.e. strong measurability on the restricted measure
    by_cases h : (1 : ℝ) / (n + 1) ≤ σmax
    · have hcont := continuousOn_integral_sq_poisson_Icc Zk I hI hI_bdd
        (one_div_pos.mpr (Nat.cast_add_one_pos n)) h
      exact hcont.aestronglyMeasurable measurableSet_Icc
    · -- interval is empty when 1/(n+1) > σmax
      rw [Icc_eq_empty h]
      simp only [Measure.restrict_empty]
      exact aestronglyMeasurable_zero_measure (fun σ => ∫ t in I, (Φ Zk σ t))
  -- glue along the union
  --simp [hcov, BoxIntegral.Prepartition.iUnion_restrict]
  -- glue along the union
  rw [hcov]
  exact aestronglyMeasurable_iUnion_iff.mpr h_on

end PoissonParam
open PoissonParam
/-- Measurability of σ ↦ ∫ Vk²(σ,t) dt for Poisson sums. -/
theorem aestronglyMeasurable_integral_sq_poisson
    {Zk : Finset ℝ} (I : Set ℝ) (hI : MeasurableSet I)
    (hI_bounded : Bornology.IsBounded I) (σ_max : ℝ) (hσ_max : 0 < σ_max) :
    AEStronglyMeasurable
      (fun σ => ∫ t in I, (∑ γ in Zk, σ / ((t - γ)^2 + σ^2))^2)
      (Measure.restrict volume (Set.Ioc 0 σ_max)) := by
  exact aestronglyMeasurable_integral_sq_poisson_Ioc Zk I hI hI_bounded hσ_max


--#min_imports
