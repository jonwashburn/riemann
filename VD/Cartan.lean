import VD.MathlibSubmitted.Nevanlinna_add_proximity
import VD.MathlibSubmitted.Nevanlinna_add_proximity

import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib
import PrimeNumberTheoremAnd
import StrongPNT

open Filter Function MeromorphicOn Metric Real Set Classical Topology ValueDistribution

open Complex Real Set Metric
open MeasureTheory
open scoped Real

namespace ValueDistribution

variable {f : ℂ → ℂ}


open scoped Topology

/--
If `f` is meromorphic and continuous at `x`, and has positive meromorphic order at `x`,
then `f` is analytic at `x`.

This is a simple corollary of `MeromorphicAt.analyticAt`.
-/
lemma analyticAt_of_meromorphicOrderAt_pos
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {x : 𝕜}
    (hmero : MeromorphicAt f x) (hcont : ContinuousAt f x)
    (hpos : 0 < meromorphicOrderAt f x) :
    AnalyticAt 𝕜 f x :=
  MeromorphicAt.analyticAt hmero hcont

/--
For an analytic function, `0 < meromorphicOrderAt f x` iff `f x = 0`.

This is the meromorphic-order version of `AnalyticAt.analyticOrderAt_ne_zero`.
-/
lemma meromorphicOrderAt_pos_iff_zero
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    0 < meromorphicOrderAt f x ↔ f x = 0 := by
  classical
  -- Express meromorphic order via analytic order.
  have h_eq := hf.meromorphicOrderAt_eq (f := f) (x := x)
  have h1 :
      0 < meromorphicOrderAt f x ↔
        0 < (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) := by
    simp [h_eq]
  -- For the mapped order, positivity is the same as being nonzero (since it is nonnegative).
  have h2 :
      0 < (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) ↔
        (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) ≠ 0 := by
    constructor
    · intro h; exact ne_of_gt h
    · intro hne
      have h_nonneg :
          (0 : WithTop ℤ) ≤ (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) := by
        -- `map_natCast_nonneg : 0 ≤ n.map Nat.cast`
        simp
      exact lt_of_le_of_ne h_nonneg hne.symm
  -- Unwrap the `map Nat.cast`: being nonzero after mapping is the same as being nonzero before.
  have h3 :
      (analyticOrderAt f x).map (Nat.cast : ℕ → ℤ) ≠ 0 ↔
        analyticOrderAt f x ≠ 0 := by
    -- `map_natCast_eq_zero : n.map Nat.cast = 0 ↔ n = 0`
    simp
  -- For analytic functions, analytic order ≠ 0 iff `f x = 0`.
  have h4 :
      analyticOrderAt f x ≠ 0 ↔ f x = 0 := hf.analyticOrderAt_ne_zero
  exact (h1.trans h2).trans (h3.trans h4)

/--
Jensen-type identity relating zeros and poles: for a meromorphic `f` on the plane,
the difference of counting functions at `0` and at `⊤` equals a circle average
minus the trailing coefficient term.
-/
lemma logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const
    {f : ℂ → ℂ} (hf : MeromorphicOn f ⊤) {R : ℝ} (hR : R ≠ 0) :
    logCounting f 0 R - logCounting f ⊤ R
      = circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
          - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
  -- Start from the functional identity of the First Main Theorem.
  have h_fun :=
    ValueDistribution.characteristic_sub_characteristic_inv (f := f) (h := hf)
  -- Evaluate at `R`.
  have h_eval :
      characteristic f ⊤ R - characteristic f⁻¹ ⊤ R =
        circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
          - (divisor f Set.univ).logCounting R := by
    have := congrArg (fun F ↦ F R) h_fun
    simpa [Pi.sub_apply] using this
  -- Quantitative version at radius `R`.
  have h_quant :=
    ValueDistribution.characteristic_sub_characteristic_inv_of_ne_zero
      (f := f) (hf := hf) (hR := hR)
  -- Combine: both right-hand sides equal the same difference.
  have h_eq :
      circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
        - (divisor f Set.univ).logCounting R
        = Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    have := h_eval
    aesop
  -- Rewrite the divisor counting term via `logCounting`.
  have h_div :
      (divisor f Set.univ).logCounting R =
        logCounting f 0 R - logCounting f ⊤ R := by
    have := ValueDistribution.log_counting_zero_sub_logCounting_top (f := f)
    exact congrArg (fun F ↦ F R) this
  -- Substitute and solve for `logCounting f 0 R - logCounting f ⊤ R`.
  have h4 :
      circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
        - (logCounting f 0 R - logCounting f ⊤ R)
        = Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    simpa [h_div] using h_eq
  have h5 :
      logCounting f 0 R - logCounting f ⊤ R
        = circleAverage (fun z ↦ Real.log ‖f z‖) 0 R
            - Real.log ‖meromorphicTrailingCoeffAt f 0‖ := by
    have h' :
        circleAverage (fun z ↦ Real.log ‖f z‖) 0 R =
          Real.log ‖meromorphicTrailingCoeffAt f 0‖
            + (logCounting f 0 R - logCounting f ⊤ R) := by
      simpa [sub_eq_iff_eq_add] using h4
    have := congrArg (fun t ↦ t - Real.log ‖meromorphicTrailingCoeffAt f 0‖) h'
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this.symm
  exact h5

lemma cartan_f1 {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ} (hR : R ≠ 0) (a : ℂ) :
    logCounting f a R + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖
      = circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R + logCounting f ⊤ R := by
  -- Apply the Jensen-type lemma to `g := f - a` at `0`.
  have hg : MeromorphicOn (fun z ↦ f z - a) ⊤ := h.sub (MeromorphicOn.const a)
  have hJ :
      logCounting (fun z ↦ f z - a) 0 R - logCounting (fun z ↦ f z - a) ⊤ R
        = circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
            - Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ :=
    logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const (f := fun z ↦ f z - a)
      (hf := hg) (R := R) hR
  -- Rewrite `logCounting (f - a) 0` and `logCounting (f - a) ⊤` via the API.
  have h_zero :
      logCounting (fun z ↦ f z - a) 0 = logCounting f (↑a : WithTop ℂ) := by
    simpa using
      (ValueDistribution.logCounting_coe_eq_logCounting_sub_const_zero
        (f := f) (a₀ := a)).symm
  have h_top :
      logCounting (fun z ↦ f z - a) ⊤ = logCounting f ⊤ :=
    ValueDistribution.logCounting_sub_const (f := f) (a₀ := a)
      (hf := h)   -- `hf` here is `MeromorphicOn f univ`, which we have as `h`.
  -- Expand `hJ` and rearrange to the desired equality.
  -- Substitute the two identities into `hJ`.
  have hJ' :
      logCounting f a R - logCounting f ⊤ R
        = circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
            - Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ := by
    simpa [h_zero, h_top] using hJ
  -- Move terms: `A - B = C - D` ⇒ `A + D = C + B`.
  have :
      logCounting f a R + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖
        = circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R + logCounting f ⊤ R := by
    have := congrArg (fun t ↦ t + logCounting f ⊤ R
                           + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) hJ'
    -- A bit of algebra:
    -- left:  (A - B) + B + D = A + D
    -- right: (C - D) + B + D = C + B
    simp [sub_eq_add_neg, add_comm, add_left_comm,] at this
    simpa [add_comm, add_left_comm, add_assoc] using this
  exact this

lemma trailingCoeff_sub_const_eq_neg {f : ℂ → ℂ}
    (h : MeromorphicOn f ⊤) (h₂ : 0 < meromorphicOrderAt f 0)
    {a : ℂ} (ha : a ≠ 0) :
    meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0 = -a := by
  classical
  -- Work with g := f - a.
  let g : ℂ → ℂ := fun z ↦ f z - a
  have hmero_f : MeromorphicAt f 0 := h 0 (by trivial)
  have hmero_g : MeromorphicAt g 0 := by
    have hg_on : MeromorphicOn g ⊤ := h.sub (MeromorphicOn.const a)
    exact hg_on 0 (by trivial)
  -- `f` tends to 0 on the punctured neighborhood of 0.
  have h_tendsto0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := 0) h₂
  -- Hence `g = f - a` tends to `-a` on the punctured neighborhood.
  have h_tendsto_g :
      Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (-a)) := by
    -- use `Filter.tendsto_sub_const_iff` with `b := a`, `c := 0`
    have := (Filter.tendsto_sub_const_iff (G := ℂ) (b := a) (c := (0 : ℂ))
      (f := f) (l := 𝓝[≠] (0 : ℂ))).2 h_tendsto0
    -- left side is `Tendsto (fun z ↦ f z - a) _ (𝓝 (0 - a))`
    simpa [g, sub_eq_add_neg] using this
  -- Nonzero finite limit implies meromorphic order 0 for `g` at 0.
  have h_ord :
      meromorphicOrderAt g 0 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf := hmero_g)).mp
      ⟨-a, by simp [ha], h_tendsto_g⟩
  -- Trailing coefficient is the limit of `z ^ (-ord) • g z` on the punctured neighborhood.
  have h_trail_lim :=
    MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt (h := hmero_g)
  -- With order 0, the weight `(z-0)^(-ord)` is identically 1, so this is just `g`.
  have h_trail :
      Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (meromorphicTrailingCoeffAt g 0)) := by
    have : (fun z : ℂ =>
              (z - 0) ^ (-(meromorphicOrderAt g 0).untop₀) • g z)
          = g := by
      simp [g, h_ord]
    aesop
  -- Uniqueness of limits in a Hausdorff space.
  have h_eq :
      meromorphicTrailingCoeffAt g 0 = -a :=
    tendsto_nhds_unique'
      (X := ℂ) (Y := ℂ) (l := 𝓝[≠] (0 : ℂ))
      (a := meromorphicTrailingCoeffAt g 0) (b := -a)
      (by infer_instance) h_trail h_tendsto_g
  -- Rewrite in terms of the original function `f`.
  simpa [g] using h_eq

lemma cartan_sigma2 {f : ℂ → ℂ} (h : MeromorphicOn f ⊤)
    (h₂ : 0 < meromorphicOrderAt f 0) :
    circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 = 0 := by
  classical
  -- On the unit circle, the trailing coefficient is `-a`, so its norm is 1 and `log 1 = 0`.
  have h_on_circle :
      ∀ a ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|,
        Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖ = (0 : ℝ) := by
    intro a ha
    -- On `|a| = 1` we have `a ≠ 0`.
    have hnorm : ‖a‖ = 1 := by
      -- `sphere 0 |1|` is `{a | ‖a‖ = 1}`
      aesop
    have ha_ne : a ≠ 0 := by
      intro h0; subst h0; simp at hnorm
    -- Compute trailing coefficient via the previous lemma.
    have h_tc :
        meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0 = -a :=
      trailingCoeff_sub_const_eq_neg h h₂ ha_ne
    -- Its norm is 1, hence `log 1 = 0`.
    have : Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖
        = Real.log (1 : ℝ) := by
      simp [h_tc, hnorm]  -- uses `‖-a‖ = ‖a‖`
    aesop
  -- Apply `circleAverage_const_on_circle` with constant `0`.
  have :=
    Real.circleAverage_const_on_circle
      (f := fun a : ℂ =>
        Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖)
      (c := (0 : ℂ)) (R := (1 : ℝ)) (a := (0 : ℝ)) h_on_circle
  -- The circle average equals the constant `0`.
  simpa using this

lemma integral_restrict_eq_setIntegral
  {α E} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {s : Set α} (f : α → E) :
  ∫ x, f x ∂μ.restrict s = ∫ x in s, f x ∂μ :=
rfl

lemma setIntegral_eq_integral_restrict
  {α E} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure α} {s : Set α} (f : α → E) :
  (∫ x in s, f x ∂μ) = ∫ x, f x ∂μ.restrict s :=
rfl

-- Kernel used in Cartan's swap-of-averages formula.
noncomputable def cartanKernel (f : ℂ → ℂ) (R : ℝ) (α β : ℝ) : ℝ :=
  Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖

lemma cartan_swap_averages
    {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ}
    (h_int_kernel :
      Integrable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2)
        ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
         (volume.restrict (Set.uIoc 0 (2 * Real.pi))))) :
    circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
      = circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R := by
  classical
  -- Kernel in angular parameters α (for a) and β (for z).
  let F : ℝ → ℝ → ℝ := cartanKernel f R

  -- 1D identity: average over a of log ‖z - a‖ is log⁺ ‖z‖.
  have h_inner (z : ℂ) :
      circleAverage (fun a ↦ Real.log ‖z - a‖) 0 1 = log⁺ ‖z‖ := by
    have : (fun a ↦ Real.log ‖z - a‖) = (fun a ↦ Real.log ‖a - z‖) := by
      funext a; simp [norm_sub_rev]
    simp [this]

  -- Left-hand side as a double interval integral.
  have hL :
      circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
        =
      (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
        ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β := by
    simp [Real.circleAverage, F,
          mul_comm, mul_left_comm, mul_assoc,
          intervalIntegral.integral_of_le Real.two_pi_pos.le]
    aesop
  -- Right-hand side as a single interval integral.
  have hR :
      circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R
        =
      (2 * Real.pi)⁻¹ *
        ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
    simp [Real.circleAverage,
          intervalIntegral.integral_of_le Real.two_pi_pos.le]

  -- For each β, evaluate the α-average using h_inner.
  have h_inner_on_param (β : ℝ) :
      (2 * Real.pi)⁻¹ *
          ∫ α in 0..2 * Real.pi, F α β
        =
      log⁺ ‖f (circleMap 0 R β)‖ := by
    -- First, recognize the left-hand side as a circle average in the variable `a`.
    have h_avg :
        (2 * Real.pi)⁻¹ *
            ∫ α in 0..2 * Real.pi, F α β
          =
        circleAverage (fun a : ℂ ↦ Real.log ‖f (circleMap 0 R β) - a‖) 0 1 := by
      -- This is just unfolding the definition of `Real.circleAverage` and of `F`.
      simpa [Real.circleAverage, F, cartanKernel,
             intervalIntegral.integral_of_le Real.two_pi_pos.le]
    -- Now apply the 1D identity `h_inner` with `z = f (circleMap 0 R β)`.
    have h_id :
        circleAverage (fun a : ℂ ↦ Real.log ‖f (circleMap 0 R β) - a‖) 0 1 =
          log⁺ ‖f (circleMap 0 R β)‖ :=
      h_inner (f (circleMap 0 R β))
    exact h_avg.trans h_id
  -- Integrability of the kernel on the product strip `[0,2π] × [0,2π]`,
  -- assumed as a hypothesis in order to apply Fubini's theorem.
  have h_int :
      Integrable (fun p : ℝ × ℝ => F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
         (volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
    simpa [F, cartanKernel] using h_int_kernel

  -- Swap the order of integration over `[0,2π] × [0,2π]` using Fubini.
  have h_swap :
      ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β
        =
      ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β := by
    -- Work with the measure restricted to the unordered interval `uIoc 0 (2π)` in the
    -- second variable, and apply `intervalIntegral_integral_swap`.
    let μR : Measure ℝ := volume.restrict (Set.uIoc 0 (2 * Real.pi))
    -- `intervalIntegral_integral_swap` expects integrability of `Function.uncurry F`
    -- w.r.t. `(volume.restrict (Set.uIoc 0 (2π))).prod μR`, which is exactly `h_int`.
    have h_int' :
        Integrable (Function.uncurry F)
          ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod μR) := by
      simpa [μR, Function.uncurry] using h_int
    have h_swap' :=
      (MeasureTheory.intervalIntegral_integral_swap
        (a := 0) (b := 2 * Real.pi)
        (μ := μR)
        (f := F)
        (h_int := h_int'))

    -- Identify the inner integral on the left as an interval integral in `β`.
    have h_left :
        ∫ α in 0..2 * Real.pi, ∫ β, F α β ∂μR
          =
        ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β := by
      -- For each `α`, `∫ β, F α β ∂μR` is the same as `∫ β in 0..2π, F α β`.
      have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
      have h_eq_inner :
          EqOn (fun α : ℝ => ∫ β, F α β ∂μR)
               (fun α : ℝ => ∫ β in 0..2 * Real.pi, F α β)
               (Set.uIcc 0 (2 * Real.pi)) := by
        intro α _
        -- Rewrite the integral w.r.t. `μR` as a set integral on `uIoc 0 (2π)`,
        -- then identify this with the interval integral on `0..2π`.
        calc
          ∫ β, F α β ∂μR
              = ∫ β in Set.uIoc 0 (2 * Real.pi), F α β := by
                  simp [μR]-- MeasureTheory.set_integral_neg_eq_set_integral_nonpos]
          _ = ∫ β in Set.Ioc 0 (2 * Real.pi), F α β := by
                simp [Set.uIoc, h0_le, min_eq_left h0_le, max_eq_right h0_le]
          _ = ∫ β in 0..2 * Real.pi, F α β := by
                simp [intervalIntegral.integral_of_le h0_le]
      -- Now use `intervalIntegral.integral_congr` in the `α`-variable.
      exact intervalIntegral.integral_congr (μ := volume) h_eq_inner

    -- Identify the outer integral on the right as an interval integral in `β`.
    -- Identify the outer integral on the right as an interval integral in `β`.
    have h_right :
        ∫ β, ∫ α in 0..2 * Real.pi, F α β ∂μR
          =
        ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β := by
      -- For each `β`, integrating with respect to `μR` is the same as integrating over `β ∈ (0, 2π]`.
      have h0_le : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
      have hμ :
          μR = volume.restrict (Set.Ioc 0 (2 * Real.pi)) := by
        dsimp [μR]
        simp [Set.uIoc_of_le h0_le]
      let g : ℝ → ℝ := fun β ↦ ∫ α in 0..2 * Real.pi, F α β
      have h_goal :
          ∫ β, g β ∂volume.restrict (Set.Ioc 0 (2 * Real.pi))
            =
          ∫ β in 0..2 * Real.pi, g β := by
        have h_set :
            ∫ β, g β ∂volume.restrict (Set.Ioc 0 (2 * Real.pi))
              =
            ∫ β in Set.Ioc 0 (2 * Real.pi), g β := by
          simp [g, integral_restrict_eq_setIntegral]
        have h_interval :
            ∫ β in Set.Ioc 0 (2 * Real.pi), g β
              =
            ∫ β in 0..2 * Real.pi, g β := by
          simp [g, intervalIntegral.integral_of_le h0_le]
        exact h_set.trans h_interval
      simpa [hμ, g] using h_goal

    -- Put everything together.
    calc
      ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β
          = ∫ α in 0..2 * Real.pi, ∫ β, F α β ∂μR := by
              simpa using h_left.symm
      _ = ∫ β, ∫ α in 0..2 * Real.pi, F α β ∂μR := by
              rw [h_swap']
      _ = ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β := h_right

  -- Combine: compute the swapped integral via h_inner_on_param.
  have h_main :
      (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
          ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β
        =
      (2 * Real.pi)⁻¹ *
        ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
    have h1 :
        (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
            ∫ α in 0..2 * Real.pi, ∫ β in 0..2 * Real.pi, F α β
          =
        (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
            ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β := by
          simp [h_swap]
    have h2 :
        (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ *
            ∫ β in 0..2 * Real.pi, ∫ α in 0..2 * Real.pi, F α β
          =
        (2 * Real.pi)⁻¹ *
          ∫ β in 0..2 * Real.pi,
            ((2 * Real.pi)⁻¹ * ∫ α in 0..2 * Real.pi, F α β) := by
      simp [mul_comm, mul_left_comm, mul_assoc, integral_mul_left]
    have h3 :
        (2 * Real.pi)⁻¹ *
          ∫ β in 0..2 * Real.pi,
            ((2 * Real.pi)⁻¹ * ∫ α in 0..2 * Real.pi, F α β)
          =
        (2 * Real.pi)⁻¹ *
          ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
      simp [h_inner_on_param]
      aesop

    aesop

  -- Now match both sides with their circleAverage expressions.
  have :
      circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
        =
      (2 * Real.pi)⁻¹ *
        ∫ β in 0..2 * Real.pi, log⁺ ‖f (circleMap 0 R β)‖ := by
    simpa [hL] using h_main
  -- Compare with the right-hand side.
  simpa [hR] using this

lemma cartan_integrability {f : ℂ → ℂ} (h : MeromorphicOn f ⊤) {R : ℝ} (hR : R ≠ 0) :
    Integrable (fun p : ℝ × ℝ => cartanKernel f R p.1 p.2)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod
       (volume.restrict (Set.uIoc 0 (2 * Real.pi)))) := by
  -- This requires detailed analysis of singularities
  sorry

/-- Cartan's formula in the zero case `0 < meromorphicOrderAt f 0`. -/
theorem cartan {r : ℝ} {f : ℂ → ℂ}
    (h : MeromorphicOn f ⊤) -- we do not assume AnalyticAt but sContinuousAt
    (h₂ : 0 < meromorphicOrderAt f 0) (hcont : ContinuousAt f 0) :
    characteristic f ⊤ r
      = circleAverage (logCounting f · r) 0 1 + Real.log ‖f 0‖ := by
  classical
  have hf : AnalyticAt ℂ f 0 :=
  analyticAt_of_meromorphicOrderAt_pos
    (hmero := h 0 (by trivial))  -- from `MeromorphicOn f ⊤`
    (hcont := hcont)
    (hpos := h₂)
  -- From `0 < meromorphicOrderAt f 0` we know that `f` has a zero at `0`.
  have hf0 : f 0 = 0 := by
    exact (meromorphicOrderAt_pos_iff_zero (hf := hf)).1 h₂
  have hlogf0 : Real.log ‖f 0‖ = 0 := by simp [hf0]
  have hlogplus0 : log⁺ ‖f 0‖ = 0 := by simp [hf0]

  -- First handle the trivial radius `r = 0`.
  by_cases hr : r = 0
  · subst hr
    -- At radius 0, `proximity f ⊤ 0 = log⁺ ‖f 0‖ = 0` and `logCounting f · 0 ≡ 0`,
    -- so both sides are 0.
    simp [characteristic, proximity, Real.circleAverage_zero,
          Real.circleAverage_const, ValueDistribution.logCounting_eval_zero,
          hf0]

  -- Now assume `r ≠ 0`.
  set R : ℝ := r with hRdef
  have hR : R ≠ 0 := by simpa [hRdef] using hr

  -- It suffices to show `characteristic f ⊤ R = circleAverage (logCounting f · R) 0 1`.
  have hR_eq :
      characteristic f ⊤ R =
        circleAverage (logCounting f · R) 0 1 := by
    -- Step 1: write `circleAverage (logCounting f · R)` using `cartan_f1`.
    have h_f2 :
        circleAverage
          (fun a ↦ logCounting f a R
                    + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 =
        circleAverage
          (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
                    + logCounting f ⊤ R) 0 1 := by
      apply circleAverage_congr_sphere
      intro a ha
      simp [cartan_f1 h hR a]
    -- Step 2: split the circle averages using linearity in `a`.
    have h_left :
        circleAverage (fun a ↦ logCounting f a R
                        + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 =
        circleAverage (logCounting f · R) 0 1
          + circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 := by
      -- This is `circleAverage_add_fun` with real-valued functions.
      simpa [Pi.add_apply] using
        circleAverage_add_fun
          (c := 0) (R := 1)
          (f₁ := fun a ↦ logCounting f a R)
          (f₂ := fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖)
          (hf₁ := by sorry) (hf₂ := by sorry)
    have h_right :
        circleAverage
          (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
                    + logCounting f ⊤ R) 0 1 =
        circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
          + logCounting f ⊤ R := by
      -- Again `circleAverage_add_fun`, with the second term constant in `a`.
      simpa [Pi.add_apply] using
        circleAverage_add_fun
          (c := 0) (R := 1)
          (f₁ := fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R)
          (f₂ := fun _ ↦ logCounting f ⊤ R)
          (hf₁ := by sorry) (hf₂ := by sorry)
    -- Step 3: combine everything.
    have :=
      calc
        circleAverage (logCounting f · R) 0 1
          + circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1
            = circleAverage (fun a ↦ logCounting f a R
                      + Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 := by
              simpa [h_left]
        _ = circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R
                      + logCounting f ⊤ R) 0 1 := h_f2
        _ = circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
              + logCounting f ⊤ R := by simpa [h_right]
    -- Use `cartan_sigma2` and `cartan_swap_averages` to identify the two pieces.
    have h_trailing :
        circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (fun z ↦ f z - a) 0‖) 0 1 = 0 :=
      cartan_sigma2 h h₂
    have h_main :
        circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 =
        circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R :=
      cartan_swap_averages h (cartan_integrability h hR)
    -- Now rewrite `proximity` and `characteristic`.
    have h_char :
        characteristic f ⊤ R =
          circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R + logCounting f ⊤ R := by
      simp [ValueDistribution.characteristic, ValueDistribution.proximity_top]
    -- Put it all together.
    calc
      characteristic f ⊤ R
          = circleAverage (fun z ↦ log⁺ ‖f z‖) 0 R + logCounting f ⊤ R := h_char
      _ = circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
            + logCounting f ⊤ R := by simpa [h_main]
      _ = circleAverage (logCounting f · R) 0 1 := by
        -- subtract the trailing coefficient average (which is 0)
        have := this
        simp [h_trailing, add_comm, add_left_comm, add_assoc] at this
        simpa using this.symm

  -- Replace `R` by `r` and add back the constant term.
  have : characteristic f ⊤ r =
      circleAverage (logCounting f · r) 0 1 := by simpa [hRdef] using hR_eq
  simpa [hlogf0] using congrArg (fun t ↦ t + Real.log ‖f 0‖) this
end ValueDistribution
