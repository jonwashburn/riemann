/-
  rh/RS/PoissonPlateau.lean


  Poisson plateau for the normalized half-plane kernel
    P_b(y) = (1/π) * b / (y^2 + b^2).


  We fix the even window ψ := (1/4)·1_{[-2,2]} and prove a uniform plateau:
    (P_b * ψ)(x) ≥ c0  for all 0 < b ≤ 1 and |x| ≤ 1,
  with the explicit constant  c0 = 1/(4π).

  Mechanical measure-theory cleanup only; no new ideas.
-/


import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Algebra.Group.Indicator
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Topology.Support


noncomputable section


namespace RH
namespace RS


open Set MeasureTheory
open scoped MeasureTheory


/-! ## Normalized Poisson kernel -/


/-- Normalized half-plane Poisson kernel on ℝ:
  `poissonKernel b y = (1/π) * b / (y^2 + b^2)`. -/
@[simp] def poissonKernel (b y : ℝ) : ℝ := (1 / Real.pi) * b / (y^2 + b^2)


lemma poissonKernel_nonneg (b : ℝ) (hb : 0 < b) (y : ℝ) : 0 ≤ poissonKernel b y := by
  have hpos : 0 ≤ (1 / Real.pi) := one_div_nonneg.mpr (le_of_lt Real.pi_pos)
  have hden : 0 < y * y + b * b :=
    add_pos_of_nonneg_of_pos (mul_self_nonneg y) (mul_self_pos.mpr (ne_of_gt hb))
  have hfrac : 0 ≤ b / (y * y + b * b) := div_nonneg (le_of_lt hb) (le_of_lt hden)
  have hmul : 0 ≤ (1 / Real.pi) * (b / (y * y + b * b)) := mul_nonneg hpos hfrac
  have : 0 ≤ ((1 / Real.pi) * b) / (y * y + b * b) := by
    simpa [mul_div_assoc] using hmul
  simpa [poissonKernel, pow_two, mul_comm, mul_left_comm, mul_assoc] using this


/-- Nonnegativity of the normalized half‑plane Poisson kernel. -/
lemma halfplane_poisson_kernel_nonneg {b x : ℝ} (hb : 0 < b) :
  0 ≤ poissonKernel b x :=
  poissonKernel_nonneg b hb x


/-! ## The fixed window ψ := (1/4)·1_{[-2,2]} -/


/-- Simple even, nonnegative bump with unit mass and compact support:
    `ψ(t) = (1/4) · 1_{[-2,2]}(t)`. -/
@[simp] def psi (t : ℝ) : ℝ :=
  (1 / (4 : ℝ)) * Set.indicator (Icc (-2 : ℝ) 2) (fun _ => (1 : ℝ)) t


lemma psi_even : Function.Even psi := by
  classical
  intro t
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · have hneg : -t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨hL, hR⟩
      exact ⟨by simpa using (neg_le_neg hR), by simpa using (neg_le_neg hL)⟩
    simp [psi, Set.indicator_of_mem, ht, hneg, mul_comm, mul_left_comm, mul_assoc]
  · have hneg : -t ∉ Icc (-2 : ℝ) 2 := by
      by_contra hmem
      rcases hmem with ⟨hL, hR⟩
      have : t ∈ Icc (-2 : ℝ) 2 := ⟨by simpa using (neg_le_neg hR), by simpa using (neg_le_neg hL)⟩
      exact ht this
    simp [psi, Set.indicator_of_not_mem, ht, hneg]


lemma psi_nonneg : ∀ x, 0 ≤ psi x := by
  intro x
  classical
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · simp [psi, Set.indicator_of_mem, hx, mul_comm, mul_left_comm, mul_assoc]
  · simp [psi, Set.indicator_of_not_mem, hx]


/-- Compute the (measure-theoretic) support `{x | ψ x ≠ 0}` of `ψ`: it is exactly `[-2,2]`. -/
lemma psi_support_eq : Function.support psi = Icc (-2 : ℝ) 2 := by
  classical
  ext x; constructor
  · intro hxSupp
    by_cases hx : x ∈ Icc (-2 : ℝ) 2
    · exact hx
    · have : psi x = 0 := by simp [psi, Set.indicator_of_not_mem hx]
      exact (hxSupp this).elim
  · intro hx
    have hxval : psi x = (1 / (4 : ℝ)) := by simp [psi, Set.indicator_of_mem hx]
    simpa [hxval]


/-- Compact support of `ψ` without deprecated constructors: identify `tsupport ψ`
    with `Icc (-2,2)` using `isClosed_Icc.closure_eq`. -/
lemma psi_hasCompactSupport : HasCompactSupport psi := by
  classical
  change IsCompact (tsupport psi)
  have hts : tsupport psi = Icc (-2 : ℝ) 2 := by
    simpa [tsupport, psi_support_eq, isClosed_Icc.closure_eq]
  simpa [hts] using (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2))


/-- Unit mass of `ψ` using `volume` and the interval-measure formula. -/
lemma psi_integral_one : ∫ x, psi x ∂(volume) = (1 : ℝ) := by
  classical
  have hmeas : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
  -- Rewrite the integrand as an indicator of a constant
  have hψ_id : (fun x => psi x)
      = Set.indicator (Icc (-2 : ℝ) 2) (fun _ => (1 / (4 : ℝ))) := by
    funext x
    by_cases hx : x ∈ Icc (-2 : ℝ) 2
    · simp [psi, Set.indicator_of_mem hx, mul_comm, mul_left_comm, mul_assoc]
    · simp [psi, Set.indicator_of_not_mem hx]
  calc
    ∫ x, psi x ∂(volume)
        = ∫ x, Set.indicator (Icc (-2 : ℝ) 2) (fun _ => (1/4 : ℝ)) x ∂(volume) := by
              rw [hψ_id]
    _   = ∫ x in Icc (-2 : ℝ) 2, (1/4 : ℝ) ∂(volume) := by
              simp [integral_indicator, hmeas]
    _   = (volume (Icc (-2 : ℝ) 2)).toReal * (1/4 : ℝ) := by
              simp [integral_const]
    _   = ((2 : ℝ) - (-2)) * (1/4 : ℝ) := by
              simp [Real.volume_Icc, sub_eq_add_neg]
    _   = (1 : ℝ) := by norm_num

/-! ## Plateau: uniform lower bound for the Poisson average with ψ -/


/-- **Poisson plateau** with the fixed even window `ψ := (1/4)·1_{[-2,2]}`.
    We produce the explicit constant `c0 = 1/(4π)` valid for all `0 < b ≤ 1` and `|x| ≤ 1`. -/
lemma poisson_plateau_c0 :
  ∃ ψ : ℝ → ℝ, Function.Even ψ ∧ (∀ x, 0 ≤ ψ x) ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x ∂(volume) = (1 : ℝ)) ∧
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {b x}, 0 < b → b ≤ 1 → |x| ≤ 1 →
      (∫ t, RH.RS.poissonKernel b (x - t) * ψ t ∂(volume)) ≥ c0 := by
  classical
  -- Fix ψ
  refine ⟨psi, psi_even, psi_nonneg, psi_hasCompactSupport, psi_integral_one, ?_⟩
  -- Choose explicit c0
  refine ⟨(1 / (4 * Real.pi)), ?_, ?_⟩
  · have hπ : 0 < Real.pi := Real.pi_pos
    have h4 : (0 : ℝ) < 4 := by norm_num
    have : 0 < 4 * Real.pi := mul_pos h4 hπ
    simpa [one_div] using (one_div_pos.mpr this)
  · intro b x hb hb_le hx
    have hπ : 0 < Real.pi := Real.pi_pos
    have hb0 : 0 ≤ b := le_of_lt hb

    -- Rewrite the convolution using the indicator of [-2,2].
    have hmeas2 : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
    -- Rewrite the convolution against ψ as a set integral and pull out (1/4)
    have conv_eq :
        (∫ t, poissonKernel b (x - t) * psi t ∂(volume))
          = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
      classical
      -- pointwise rewrite to an indicator on [-2,2]
      have hpt : (fun t => poissonKernel b (x - t) * psi t)
          = Set.indicator (Icc (-2 : ℝ) 2)
              (fun t => (1/4 : ℝ) * poissonKernel b (x - t)) := by
        funext t
        by_cases ht : t ∈ Icc (-2 : ℝ) 2
        · simp [psi, Set.indicator_of_mem ht, mul_comm, mul_left_comm, mul_assoc]
        · simp [psi, Set.indicator_of_not_mem ht]
      -- convert to a set integral and use linearity to pull out the constant
      have kcont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
        have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
          Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
        have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
          intro t; have : 0 < (x - t) ^ 2 + b ^ 2 := by
            have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb)
            exact add_pos_of_nonneg_of_pos (by exact sq_nonneg _) this
          exact ne_of_gt this
        have hrecip : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) := by
          exact (continuous_const.div hden (by intro t; exact hpos t))
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using (continuous_const.mul (continuous_const.mul hrecip))
      have hint_on : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (-2 : ℝ) 2) volume :=
        (kcont.integrableOn_Icc)
      calc
        ∫ t, poissonKernel b (x - t) * psi t ∂(volume)
            = ∫ t, Set.indicator (Icc (-2 : ℝ) 2) (fun t => (1/4 : ℝ) * poissonKernel b (x - t)) t ∂(volume) := by
                  rw [hpt]
        _   = ∫ t in Icc (-2 : ℝ) 2, (1/4 : ℝ) * poissonKernel b (x - t) ∂(volume) := by
                  simp [integral_indicator, hmeas2]
        _   = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
                  -- Use scalar linearity for set integrals
                  exact integral_mul_left _ _

    -- A single subinterval J := [x-b, x+b] sits inside [-2,2] if |x| ≤ 1 and b ≤ 1.
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := by
      rcases abs_le.mp hx with ⟨hL, hR⟩
      exact ⟨by linarith, by linarith⟩
    have J_subset : Icc (x - b) (x + b) ⊆ Icc (-2 : ℝ) 2 := by
      intro t ht
      have hL : -2 ≤ x - b := by linarith [hxIcc.1, hb_le]
      have hR : x + b ≤ 2 := by linarith [hxIcc.2, hb_le]
      exact ⟨le_trans hL ht.1, le_trans ht.2 hR⟩

    -- Pointwise lower bound on J: |x-t| ≤ b ⇒ P_b(x - t) ≥ 1/(2π b).
    have kernel_lb_on_J :
        ∀ {t}, t ∈ Icc (x - b) (x + b) →
          poissonKernel b (x - t) ≥ (1 / (2 * Real.pi * b)) := by
      intro t ht
      -- |x - t| ≤ b on J
      have hdist : |x - t| ≤ b := by
        have h01 : -b ≤ t - x := by linarith [ht.1]
        have h02 : t - x ≤ b := by linarith [ht.2]
        have : |t - x| ≤ b := abs_le.mpr ⟨by linarith, by linarith⟩
        simpa [abs_sub_comm] using this
      -- Denominator comparison: (x - t)^2 + b^2 ≤ 2 * b^2
      have hbne : b ≠ 0 := ne_of_gt hb
      have hb0 : 0 ≤ b := le_of_lt hb
      have sq_le : (x - t) ^ 2 ≤ b ^ 2 := by
        -- from |x - t| ≤ |b|
        have : |x - t| ≤ |b| := by simpa [abs_of_nonneg hb0] using hdist
        -- use sq_le_sq: a^2 ≤ b^2 ↔ |a| ≤ |b|
        simpa [pow_two, sq_abs, abs_of_nonneg hb0] using (sq_le_sq.mpr this)
      have den_le : (x - t) ^ 2 + b ^ 2 ≤ 2 * b ^ 2 := by
        have := add_le_add_right sq_le (b ^ 2)
        simpa [two_mul] using this
      have den_pos : 0 < (x - t) ^ 2 + b ^ 2 := by
        have : 0 < b ^ 2 := sq_pos_iff.mpr hbne
        exact add_pos_of_nonneg_of_pos (by exact sq_nonneg _) this
      -- 1/(2*b^2) ≤ 1/((x - t)^2 + b^2)
      have inv_le : (1 : ℝ) / (2 * b ^ 2) ≤ (1 : ℝ) / ((x - t) ^ 2 + b ^ 2) :=
        one_div_le_one_div_of_le den_pos den_le
      -- multiply by ((1/π) * b) ≥ 0 to preserve inequality direction (switch to ≥ form)
      have const_nonneg : 0 ≤ (1 / Real.pi) * b :=
        mul_nonneg (one_div_nonneg.mpr (le_of_lt Real.pi_pos)) hb0
      have hmul : (1 / Real.pi) * b * ((1 : ℝ) / ((x - t) ^ 2 + b ^ 2))
                   ≥ (1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2)) := by
        have := mul_le_mul_of_nonneg_left inv_le const_nonneg
        -- flip sides to get ≥
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      -- rewrite left to the Poisson kernel and keep the right as a simple constant in b
      have : poissonKernel b (x - t) ≥ (1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2)) := by
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using hmul
      -- conclude the claimed bound (we use a slightly different but equivalent constant form)
      -- This is acceptable as a pointwise constant lower bound on J
      -- returning the statement in the required direction
      -- `(1/π) * b * (1/(2 b^2)) = 1/(2 π b)`; we do not need exact rewrite here
      -- but it's fine to keep this weaker form
      -- Finally, match goal direction
      have hb' : (1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2)) = (1 / (2 * Real.pi * b)) := by
        have hbne : b ≠ 0 := ne_of_gt hb
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        -- Direct simplification using field_simp
        field_simp [hbne, hpi, pow_two]
        ring
      rw [← hb']
      exact this

    -- (1) Integral over [-2,2] ≥ integral over J by monotonicity & nonnegativity.
    have nonneg_pb : ∀ t, 0 ≤ poissonKernel b (x - t) := by
      intro t; simpa using halfplane_poisson_kernel_nonneg (x := x - t) hb
    have int_mono :
        ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume)
        ≥ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume) := by
      -- Integrable on the larger set via continuity on a compact interval
      have kcont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
        -- polynomial/positive-denominator composition is continuous
        have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
          Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
        have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
          intro t; have : 0 < (x - t) ^ 2 + b ^ 2 := by
            have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb)
            exact add_pos_of_nonneg_of_pos (by exact sq_nonneg _) this
          exact ne_of_gt this
        have hrecip : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) := by
          exact (continuous_const.div hden (by intro t; exact hpos t))
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using (continuous_const.mul (continuous_const.mul hrecip))
      have int_on : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (-2 : ℝ) 2) volume :=
        (kcont.integrableOn_Icc)
      have hnonneg : 0 ≤ᵐ[Measure.restrict volume (Icc (-2 : ℝ) 2)]
          (fun t : ℝ => poissonKernel b (x - t)) :=
        Filter.Eventually.of_forall (fun t => by
          have := halfplane_poisson_kernel_nonneg (x := x - t) hb
          simpa)
      have hst : (Icc (x - b) (x + b) : Set ℝ) ≤ᵐ[volume] (Icc (-2 : ℝ) 2) :=
        Filter.Eventually.of_forall (fun t => by
          intro ht; exact J_subset ht)
      have hmono : ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume)
                     ≤ ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) :=
        setIntegral_mono_set int_on hnonneg hst
      exact hmono

    -- (2) Lower bound the integral over J by a constant on J.
    have const_lb :
        ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume)
          ≥ ((1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2))) * (volume (Icc (x - b) (x + b))).toReal := by
      -- Pointwise lower bound on J and integrability imply a constant lower bound
      have hsJ : MeasurableSet (Icc (x - b) (x + b)) := isClosed_Icc.measurableSet
      have hμJ : volume (Icc (x - b) (x + b)) < ⊤ := by
        simp only [Real.volume_Icc]
        exact ENNReal.coe_lt_top
      have kcont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
        have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
          Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
        have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
          intro t; have : 0 < (x - t) ^ 2 + b ^ 2 := by
            have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb)
            exact add_pos_of_nonneg_of_pos (by exact sq_nonneg _) this
          exact ne_of_gt this
        have hrecip : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) := by
          exact (continuous_const.div hden (by intro t; exact hpos t))
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using (continuous_const.mul (continuous_const.mul hrecip))
      have hintJ : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (x - b) (x + b)) volume :=
        (kcont.integrableOn_Icc)
      have hpt : ∀ t ∈ Icc (x - b) (x + b),
          ((1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2))) ≤ poissonKernel b (x - t) := by
        intro t ht
        have := kernel_lb_on_J ht
        rw [ge_iff_le] at this
        -- kernel_lb_on_J gives: poissonKernel b (x - t) ≥ 1 / (2 * Real.pi * b)
        -- We need to show it's also ≥ (1 / Real.pi) * b * (1 / (2 * b ^ 2))
        -- These are equal as shown in the hb' proof
        have hb' : (1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2)) = (1 / (2 * Real.pi * b)) := by
          have hbne : b ≠ 0 := ne_of_gt hb
          have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
          field_simp [hbne, hpi, pow_two]
          ring
        rw [hb']
        exact this
      have : ((1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2))) * (volume (Icc (x - b) (x + b))).toReal
            ≤ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume) := by
        -- use setIntegral_ge_of_const_le
        simpa [mul_comm] using
          (setIntegral_ge_of_const_le (μ := volume) (s := Icc (x - b) (x + b))
            (f := fun t : ℝ => poissonKernel b (x - t))
            (c := ((1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2)))) hsJ hμJ.ne hpt hintJ)
      exact this

    -- (3) Measure of J is 2b, so RHS is (1/(2πb)) * (2b) = 1/π.
    have meas_J : (volume (Icc (x - b) (x + b))).toReal = (2 : ℝ) * b := by
      have hle : x - b ≤ x + b := by linarith [hb0]
      have : volume (Icc (x - b) (x + b)) = ENNReal.ofReal ((x + b) - (x - b)) := by
        simpa [sub_eq_add_neg] using
          (Real.volume_Icc : volume (Icc (x - b) (x + b)) = ENNReal.ofReal ((x + b) - (x - b)))
      have hnn : 0 ≤ ((x + b) - (x - b)) := by
        have heq : (2 : ℝ) * b = (x + b) - (x - b) := by
          ring
        have hpos : 0 ≤ (2 : ℝ) * b := by exact mul_nonneg (by norm_num) hb0
        rw [← heq]
        exact hpos
      simpa [this, ENNReal.toReal_ofReal, sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc]
    have J_lb :
        ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) ∂(volume) ≥ (1 / Real.pi) := by
      -- convert the constant lower bound using the measure identity
      have : ((1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2))) * (volume (Icc (x - b) (x + b))).toReal
               = ((1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2))) * ((2 : ℝ) * b) := by
        rw [meas_J]
      -- Now `((1/π) * b * (1/(2 b^2))) * (2 b) = 1/π` by cancellation
      have hbne : b ≠ 0 := ne_of_gt hb
      have hcalc : ((1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2))) * ((2 : ℝ) * b) = (1 / Real.pi) := by
        -- regroup the b terms
        have : b * ((1 : ℝ) / (2 * b ^ 2)) * ((2 : ℝ) * b)
              = 1 := by
          -- b * (1/(2 b^2)) * (2 b) = (b * (2 b)) / (2 b^2) = 1
          have hden : (2 : ℝ) * b ^ 2 ≠ 0 := by
            exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hbne)
          have : (b * ((2 : ℝ) * b)) / ((2 : ℝ) * b ^ 2) = (1 : ℝ) := by
            have hnumden : b * ((2 : ℝ) * b) = (2 : ℝ) * b ^ 2 := by ring
            have : ((2 : ℝ) * b ^ 2) / ((2 : ℝ) * b ^ 2) = (1 : ℝ) := by
              simp [hden]
            simpa [hnumden]
          -- rewrite lhs into the above fraction
          simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
            using this
        -- multiply by (1/π)
        simpa [mul_comm, mul_left_comm, mul_assoc] using congrArg (fun y => (1 / Real.pi) * y) this
      have volume_eq : ((1 / Real.pi) * b * ((1 : ℝ) / (2 * b ^ 2))) * (volume (Icc (x - b) (x + b))).toReal
               = (1 / Real.pi) := by
        rw [this]
        exact hcalc
      -- conclude the lower bound
      exact volume_eq ▸ const_lb

    -- (4) Put it all together with the ψ factor (1/4).
    -- ∫_{[-2,2]} ≥ ∫_J ≥ 1/π  ⇒  (1/4)*∫_{[-2,2]} ≥ (1/4)*(1/π) = 1/(4π).
    have base_lb :
        (1 / Real.pi) ≤ ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) :=
      le_trans J_lb int_mono
    -- Multiply by (1/4) ≥ 0
    have : (1/4 : ℝ) * (∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume))
              ≥ (1/4 : ℝ) * (1 / Real.pi) := by
      have : 0 ≤ (1 / (4 : ℝ)) := by norm_num
      exact (mul_le_mul_of_nonneg_left base_lb this)
    -- Conclude
    calc
      ∫ t, poissonKernel b (x - t) * psi t ∂(volume)
          = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := conv_eq
      _   ≥ (1/4 : ℝ) * (1 / Real.pi) := this
      _   = 1 / (4 * Real.pi) := by ring


end RS
end RH
