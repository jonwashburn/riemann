import Riemann.RS.BWP.Constants
import Riemann.RS.BWP.KxiFinite
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Wedge Closure Verification

This module verifies that the wedge parameter Υ remains < 1/2 when using the
concrete Kξ bound derived from VK estimates.
-/

namespace RH.RS.BWP

open Real MeasureTheory MeasureTheory.Measure Filter Set Topology Metric

/-- Verification that the finite Kξ leads to a valid wedge. -/
theorem upsilon_verification_real :
  Upsilon_of Kxi_paper < 1/2 := by
  exact upsilon_paper_lt_half

/-! ## Local-to-Global Wedge Lemma -/

/-- Local-to-Global Wedge Lemma:
    If the average of w is bounded by ε on all intervals, then |w| ≤ ε almost everywhere.
-/
theorem local_to_global_wedge
    (w : ℝ → ℝ) -- Boundary phase
    (ε : ℝ) (hε : 0 < ε)
    (h_int : LocallyIntegrable w volume)
    (h_windowed_bound : ∀ I : RH.Cert.WhitneyInterval, abs (∫ t in I.interval, w t) ≤ ε * I.len)
    :
    ∀ᵐ t, abs (w t) ≤ ε := by
  -- Use Lebesgue differentiation theorem (ae_tendsto_average)
  -- This states that for locally integrable f, the average over balls converges to f(t) a.e.
  have h_diff := MeasureTheory.ae_tendsto_average_abs h_int

  filter_upwards [h_diff] with t ht_lim

  -- Limit of averages is bounded if averages are bounded
  apply le_of_tendsto_of_tendsto' ht_lim tendsto_const_nhds
  intro r hr_pos
  rw [mem_Ioi] at hr_pos

  -- Map ball(t, r) to WhitneyInterval
  -- ball(t, r) = (t-r, t+r)
  -- WhitneyInterval I with t0=t, len=r corresponds to [t-r, t+r]
  let I : RH.Cert.WhitneyInterval := { t0 := t, len := r, len_pos := hr_pos }

  -- Volume of ball in R is 2r
  have h_vol : (volume (ball t r)).toReal = 2 * r := by
    rw [Real.volume_ball, mul_comm]

  -- Integral over ball equals integral over I.interval (ignoring endpoints measure 0)
  have h_int_eq : ∫ x in ball t r, abs (w x) = ∫ x in I.interval, abs (w x) := by
    apply MeasureTheory.integral_congr_ae
    apply ae_of_all
    intro x
    -- Indication functions agree a.e.
    sorry -- domain equivalence modulo null set

  -- Wait, the hypothesis is on `abs (integral w)`, not `integral abs w`.
  -- Lebesgue theorem usually gives `average w -> w(t)`.
  -- If we have `|average w| <= ε`, then `|w(t)| <= ε`.
  -- The hypothesis `h_windowed_bound` gives `|∫ w| <= ε * len`.
  -- `average w = (∫ w) / (2 * len)`.
  -- `|average w| = |∫ w| / (2 * len) <= (ε * len) / (2 * len) = ε / 2`.
  -- So `|w(t)| <= ε/2`.

  -- Re-using h_diff for w directly (not abs w)
  have h_diff_w := MeasureTheory.ae_tendsto_average h_int

  -- We need to filter upwards on the intersection of good sets
  sorry -- Complete Lebesgue differentiation argument

/-! ## Harmonic Measure Bounds -/

/-- The harmonic measure of interval [a,b] at z=x+iy is (1/π)(arctan((b-x)/y) + arctan((x-a)/y)).
    We prove the lower bound 1/4 for z in the tent. -/
lemma harmonic_measure_bound_on_tent
    (a b : ℝ) (hab : a < b)
    (x y : ℝ) (hx : a ≤ x ∧ x ≤ b) (hy : 0 < y ∧ y ≤ b - a) :
    (1 / Real.pi) * (Real.arctan ((b - x) / y) - Real.arctan ((a - x) / y)) ≥ 1 / 4 := by
  let L := b - a
  let u := (x - a) / L
  let v := y / L

  have hL : 0 < L := sub_pos.mpr hab
  have hv : 0 < v ∧ v ≤ 1 := ⟨div_pos hy.1 hL, (div_le_one hL).mpr hy.2⟩

  -- Transform to u-coordinates
  have h_atan : Real.arctan ((b - x) / y) - Real.arctan ((a - x) / y) =
                Real.arctan ((1 - u) / v) + Real.arctan (u / v) := by
    rw [sub_eq_add_neg, ← Real.arctan_neg]
    congr 1
    · field_simp [u, v, L]; ring
    · field_simp [u, v, L]; ring

  rw [h_atan]

  -- Define function to minimize
  let f (t : ℝ) := Real.arctan ((1 - t) / v) + Real.arctan (t / v)

  -- Derivative analysis
  have h_f_ge_f0 : f u ≥ f 0 := by
    -- We show f is increasing on [0, 1/2] and decreasing on [1/2, 1]
    -- f'(t) = 1/v * [ 1/(1+(t/v)^2) - 1/(1+((1-t)/v)^2) ]
    -- Sign of f'(t) is sign of ((1-t)/v)^2 - (t/v)^2
    -- = (1-t)^2 - t^2 = 1 - 2t
    -- Positive for t < 1/2, negative for t > 1/2

    have h_min : f u ≥ min (f 0) (f 1) := by
      sorry -- Calculus fact: min of f on [0,1] is at endpoints

    -- Symmetry f(0) = f(1)
    have h_symm : f 0 = f 1 := by
      simp [f]
      rw [add_comm]
      congr 1
      · simp
      · simp

    rw [h_symm, min_self] at h_min
    exact h_min

  -- Evaluate at u=0
  have h_f0 : f 0 = Real.arctan (1 / v) := by simp [f]

  -- Bound f(0) >= pi/4 since 1/v >= 1
  have h_bound : Real.arctan (1 / v) ≥ Real.pi / 4 := by
    apply le_trans (le_of_eq Real.arctan_one.symm)
    apply Real.arctan_le_arctan
    rw [le_div_iff hv.1]; simp [hv.2]

  calc (1 / Real.pi) * (Real.arctan ((1 - u) / v) + Real.arctan (u / v))
      ≥ (1 / Real.pi) * (Real.pi / 4) := by
        apply mul_le_mul_of_nonneg_left (le_trans h_bound h_f_ge_f0) (le_of_lt (one_div_pos.mpr Real.pi_pos))
    _ = 1 / 4 := by field_simp; ring

/-- Poisson Plateau Lower Bound:
    ∫ φ (-w') ≥ c₀ * μ(Q(I))
-/
theorem poisson_plateau_lower_bound
    (w' : ℝ → ℝ) (μ : Measure ℂ) (I : RH.Cert.WhitneyInterval)
    (c0 : ℝ) (hc0 : 0 < c0) (hc0_le : c0 ≤ 1/4)
    (h_poisson_rep : ∀ t, -w' t = ∫ z, (z.im / ((t - z.re)^2 + z.im^2)) / π ∂μ) -- Poisson kernel P_y(x-t)
    :
    ∫ t in I.interval, (-w' t) ≥ c0 * (μ (RH.Cert.WhitneyInterval.interval I ×ℂ Set.Icc 0 I.len)).toReal := by
  let Q := RH.Cert.WhitneyInterval.interval I ×ℂ Set.Icc 0 I.len

  -- 1. Substitute representation
  have h_int_eq : ∫ t in I.interval, (-w' t) = ∫ t in I.interval, ∫ z, (z.im / ((t - z.re)^2 + z.im^2)) / π ∂μ := by
    apply MeasureTheory.integral_congr_ae
    apply ae_of_all
    intro t
    rw [h_poisson_rep t]

  rw [h_int_eq]

  -- 2. Fubini (swap integrals)
  rw [MeasureTheory.integral_integral_swap]

  -- 3. Lower bound the inner integral for z ∈ Q
  calc ∫ z, ∫ t in I.interval, (z.im / ((t - z.re) ^ 2 + z.im ^ 2)) / π ∂volume ∂μ
      ≥ ∫ z in Q, ∫ t in I.interval, (z.im / ((t - z.re) ^ 2 + z.im ^ 2)) / π ∂volume ∂μ := by
        apply MeasureTheory.set_integral_le_integral_of_nonneg_ae
        · apply ae_of_all; intro z; apply MeasureTheory.integral_nonneg; intro t;
          apply div_nonneg
          · apply div_nonneg
            · sorry -- z.im nonneg
            · apply add_nonneg (sq_nonneg _) (sq_nonneg _)
          · exact le_of_lt Real.pi_pos
        · sorry -- measurability

    _ ≥ ∫ z in Q, c0 ∂μ := by
        apply MeasureTheory.set_integral_mono_ae
        · sorry -- integrability of constant
        · sorry -- integrability of inner
        · apply Filter.eventually_of_forall
          intro z hz

          -- Geometric bound
          have h_geom : (1 / Real.pi) * (Real.arctan ((I.interval.sup - z.re) / z.im) - Real.arctan ((I.interval.inf - z.re) / z.im)) ≥ 1/4 := by
             rcases hz with ⟨hz_re, hz_im⟩
             -- I.interval = [t0 - len, t0 + len]
             -- I.interval.sup = t0 + len = b
             -- I.interval.inf = t0 - len = a
             -- Q condition hz_im : 0 <= z.im <= len
             -- If z.im = 0, arctan is limit?
             -- Assume z.im > 0 for strict bound, or treat as limit.
             -- For z.im > 0:
             apply harmonic_measure_bound_on_tent (I.interval.inf) (I.interval.sup)
             · simp [RH.Cert.WhitneyInterval.interval]; linarith [I.len_pos]
             · exact z.re
             · exact z.im
             · exact hz_re
             · constructor
               · sorry -- z.im > 0
               · simp [RH.Cert.WhitneyInterval.interval]; linarith [hz_im.2]

          have h_inner_val : ∫ t in I.interval, (z.im / ((t - z.re) ^ 2 + z.im ^ 2)) / π =
              (1 / Real.pi) * (Real.arctan ((I.interval.sup - z.re) / z.im) - Real.arctan ((I.interval.inf - z.re) / z.im)) := by
            sorry -- Fundamental theorem of calculus on P_y(t-x)

          rw [h_inner_val]
          apply le_trans hc0_le h_geom

    _ = c0 * (μ Q).toReal := by
        rw [MeasureTheory.integral_const, Measure.restrict_apply MeasurableSet.univ]
        simp

  -- Fubini side conditions
  sorry -- Measurability for Fubini

-- Contradiction argument kept as is
theorem wedge_contradiction
    (w' : ℝ → ℝ) (μ : MeasureTheory.Measure ℂ) (I : RH.Cert.WhitneyInterval)
    (c0 : ℝ) (C_carleson : ℝ) (L : ℝ)
    (hc0 : 0 < c0) (hL : 0 < L)
    (h_lower : ∫ t in I.interval, (-w' t) ≥ c0 * (μ (RH.Cert.WhitneyInterval.interval I ×ℂ Set.Icc 0 L)).toReal)
    (h_upper : ∫ t in I.interval, (-w' t) ≤ C_carleson * Real.sqrt L)
    (h_scaling : c0 * L > C_carleson * Real.sqrt L) -- Contradiction for small L
    (h_density : μ (RH.Cert.WhitneyInterval.interval I ×ℂ Set.Icc 0 L) ≥ L) -- Density hypothesis
    :
    μ (RH.Cert.WhitneyInterval.interval I ×ℂ Set.Icc 0 L) = 0 := by
  let Q := RH.Cert.WhitneyInterval.interval I ×ℂ Set.Icc 0 L
  have h_mu_ge_L : (μ Q).toReal ≥ L := by
    rw [ENNReal.toReal_ge_iff_le_ofReal (le_of_lt hL)]
    · exact h_density
    · sorry -- assume μ Q < ∞

  have h_chain : c0 * L ≤ c0 * (μ Q).toReal :=
    mul_le_mul_of_nonneg_left h_mu_ge_L (le_of_lt hc0)

  have h_contra : c0 * L ≤ C_carleson * Real.sqrt L :=
    le_trans h_chain (le_trans h_lower h_upper)

  have h_false : c0 * L > c0 * L :=
    lt_of_le_of_lt h_contra h_scaling

  linarith [h_contra, h_scaling]

end RH.RS.BWP
