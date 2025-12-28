import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Measure Theory Integral Auxiliary Lemmas

This file contains auxiliary lemmas for measure theory integrals, including:
- Power inequalities
- Change of variables for integrals
- Set integral monotonicity
- Interval integrability from continuity
- Real power lemmas
- Filter/tendsto lemmas for metric spaces

## Main results

* `RH.pow_le_pow_of_le_left` - Power monotonicity for semirings
* `MeasureTheory.integral_comp_smul_sub_pos` - Change of variables ∫ f((t-a)/σ) = σ * ∫ f
* `MeasureTheory.set_integral_mono_on_nonneg` - Set integral monotonicity
* `MeasureTheory.intervalIntegrable_of_continuousOn` - Interval integrability from continuity
* `Real.rpow_neg_natCast_of_nonneg` - Real power with negative exponent
* `Metric.tendsto_atBot` - ε-δ characterization for tendsto at atBot

-/

namespace RH

lemma pow_le_pow_of_le_left {α : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α} (h₁ : a ≤ b) (h₂ : 0 ≤ a) :
  ∀ n : ℕ, a ^ n ≤ b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : 0 ≤ b := le_trans h₂ h₁
    have hbn : 0 ≤ b ^ n := pow_nonneg hb _
    have : a ^ n * a ≤ b ^ n * b := mul_le_mul ih h₁ h₂ hbn
    simpa [pow_succ] using this

end RH

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
      field_simp [hσne]; simp
  have hrange : Set.range Φ = Set.univ := by
    simpa [Φ, add_comm, mul_comm] using hrange₀
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hcomp2 : (fun x : ℝ => σ * f (σ * x / σ)) = (fun x => σ * f x) := by
    funext x
    have : σ * x / σ = x := by field_simp [hσne]
    simp [this]
  simpa [hrange, Φ, hcomp2, abs_of_pos hσ, setIntegral_univ, MeasureTheory.integral_const_mul]
    using h

/-- Monotonicity of set integrals: if `f ≤ g` almost everywhere on `s`,
and both are integrable on `s`, then `∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ`. -/
lemma set_integral_mono_on_nonneg {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {s : Set α} (hs : MeasurableSet s) {f g : α → ℝ}
    (hf : MeasureTheory.IntegrableOn f s μ) (hg : MeasureTheory.IntegrableOn g s μ)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ := by
  apply MeasureTheory.integral_mono_ae hf hg
  exact (MeasureTheory.ae_restrict_iff' hs).mpr h

variable {E : Type*} [NormedAddCommGroup E]
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

@[simp] lemma rpow_neg_natCast_of_nonneg {x : ℝ} (_ : 0 ≤ x) (n : ℕ) :
    x ^ (-(n : ℝ)) = (x ^ n)⁻¹ := by
  -- rpow_neg holds for nonnegative bases; then rewrite the RHS with rpow_natCast
  simp

lemma rpow_neg_natCast_of_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ (-(n : ℝ)) = (x ^ n)⁻¹ :=
  rpow_neg_natCast_of_nonneg hx.le n

end Real

namespace Metric

open Real MeasureTheory Filter Topology

variable {α : Type*} [PseudoMetricSpace α]

@[simp]
theorem tendsto_atBot_atBot' {α : Type*} {β : Type*} [Nonempty α]
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

namespace MeasureTheory

open Real Filter Topology intervalIntegral

lemma abs_add_three (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  calc |a + b + c|
    _ = |(a + b) + c| := by ring_nf
    _ ≤ |a + b| + |c| := abs_add_le _ _
    _ ≤ |a| + |b| + |c| := by linarith [abs_add_le a b]

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

/-- If f has an antiderivative F that converges at ±∞, then the integral of f over ℝ
equals the difference of those limits of the antiderivative. -/
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
    simpa using ((div_le_div_iff₀ hden1 hden2).2 hmul)
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
