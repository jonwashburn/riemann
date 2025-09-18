/-
  rh/RS/PoissonPlateau.lean

  Poisson plateau: a concrete even window ψ with a uniform positive lower bound
  for its Poisson smoothing on the unit Carleson box (|x| ≤ 1, 0 < b ≤ 1).

  We use the simple top-hat window ψ = (1/4)·1_{[-2,2]} and show that
    (P_b * ψ)(x) ≥ 1/(4π) for all 0 < b ≤ 1 and |x| ≤ 1.

  Mathlib-only; no axioms.
-/

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.Topology.Support

noncomputable section

namespace RH
namespace RS

open Set MeasureTheory
open scoped MeasureTheory

/-- Normalized half-plane Poisson kernel on ℝ. -/
@[simp] def poissonKernel (b u : ℝ) : ℝ := (1 / Real.pi) * (b / (u ^ 2 + b ^ 2))

lemma poissonKernel_nonneg {b u : ℝ} (hb : 0 ≤ b) : 0 ≤ poissonKernel b u := by
  have hπ : 0 ≤ (1 / Real.pi) := by
    have : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    simpa [one_div] using (inv_nonneg.mpr this)
  have hden : 0 ≤ u ^ 2 + b ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfrac : 0 ≤ b / (u ^ 2 + b ^ 2) := div_nonneg hb hden
  simpa [poissonKernel] using mul_nonneg hπ hfrac

/-- Fixed even, nonnegative, compactly supported window ψ = (1/4)·1_{[-2,2]}. -/
@[simp] def psi (t : ℝ) : ℝ := (1 / (4 : ℝ)) * (Icc (-2 : ℝ) 2).indicator (fun _ => (1 : ℝ)) t

lemma psi_nonneg : ∀ t, 0 ≤ psi t := by
  intro t; by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · simp [psi, Set.indicator_of_mem ht]
  · simp [psi, Set.indicator_of_not_mem ht]

-- (Optional) ψ is even (not used below, but recorded for completeness)
lemma psi_even_pointwise : ∀ t, psi (-t) = psi t := by
  intro t
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · have hneg : -t ∈ Icc (-2 : ℝ) 2 := by
      rcases ht with ⟨hL, hR⟩; exact ⟨by simpa using (neg_le_neg hR), by simpa using (neg_le_neg hL)⟩
    simp [psi, Set.indicator_of_mem ht, Set.indicator_of_mem hneg]
  · have hneg : -t ∉ Icc (-2 : ℝ) 2 := by
      by_contra hmem; rcases hmem with ⟨hL, hR⟩
      exact ht ⟨by simpa using (neg_le_neg hR), by simpa using (neg_le_neg hL)⟩
    simp [psi, Set.indicator_of_not_mem ht, Set.indicator_of_not_mem hneg]

lemma psi_even : Even psi := by
  intro t; exact psi_even_pointwise t

lemma psi_hasCompactSupport : HasCompactSupport psi := by
  -- Topological support equals the closed interval [-2,2]
  change IsCompact (tsupport psi)
  have hts : tsupport psi = Icc (-2 : ℝ) 2 := by
    -- tsupport = closure of pointwise support; here support is exactly Icc (-2,2)
    have : Function.support psi = Icc (-2 : ℝ) 2 := by
      ext t; constructor
      · intro ht
        by_contra hnot
        have : psi t = 0 := by simp [psi, Set.indicator_of_not_mem hnot]
        exact ht this
      · intro ht
        have : psi t = (1 / (4 : ℝ)) := by simp [psi, Set.indicator_of_mem ht]
        exact by simpa [this]
    simpa [tsupport, this, isClosed_Icc.closure_eq]
  simpa [hts] using (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2))

lemma psi_integral_one : ∫ t, psi t ∂(volume) = 1 := by
  have hmeas : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
  have hpt : (fun t => psi t) = (Icc (-2 : ℝ) 2).indicator (fun _ => (1 / (4 : ℝ))) := by
    funext t; by_cases ht : t ∈ Icc (-2 : ℝ) 2 <;> simp [psi, ht]
  calc
    ∫ t, psi t ∂(volume)
        = ∫ t, (Icc (-2 : ℝ) 2).indicator (fun _ => (1 / (4 : ℝ))) t ∂(volume) := by
              simpa [hpt]
    _   = ∫ t in Icc (-2 : ℝ) 2, (1 / (4 : ℝ)) ∂(volume) := by
              simp [integral_indicator, hmeas]
    _   = (volume (Icc (-2 : ℝ) 2)).toReal * (1 / (4 : ℝ)) := by
              simp [integral_const]
    _   = ((2 : ℝ) - (-2)) * (1 / (4 : ℝ)) := by
              simp [Real.volume_Icc, sub_eq_add_neg]
    _   = 1 := by norm_num

/-- The Poisson smoothing of ψ at height b and horizontal coordinate x. -/
@[simp] def poissonSmooth (b x : ℝ) : ℝ := ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t)

@[simp] def c0_plateau : ℝ := 1 / (4 * Real.pi)

lemma c0_plateau_pos : 0 < c0_plateau := by
  have : 0 < 4 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  simpa [c0_plateau, one_div] using inv_pos.mpr this

/-- Uniform plateau lower bound: (P_b * ψ)(x) ≥ 1/(4π) for 0 < b ≤ 1, |x| ≤ 1. -/
theorem poisson_plateau_lower_bound
  {b x : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hx : |x| ≤ 1) :
  c0_plateau ≤ poissonSmooth b x := by
  classical
  -- The big interval S and a length-2b subinterval J around x
  set S : Set ℝ := Icc (-2 : ℝ) 2
  have hS_meas : MeasurableSet S := isClosed_Icc.measurableSet
<<<<<<< HEAD
  have hb0 : 0 ≤ b := le_of_lt hb
=======
    have hb0 : 0 ≤ b := le_of_lt hb
>>>>>>> origin/main
  have hxI : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
  -- J := [x - b, x + b] ⊆ [-2,2]
  have hJsubset : Icc (x - b) (x + b) ⊆ S := by
    intro t ht; exact ⟨by linarith [hxI.1, hb1], by linarith [hxI.2, hb1]⟩
  -- Nonnegativity of the kernel
  have hnonneg : ∀ t, 0 ≤ poissonKernel b (x - t) :=
    fun t => poissonKernel_nonneg (b := b) (u := x - t) hb0
  -- Monotonicity of integrals on sets (nonnegative integrand)
  have int_mono : ∫ t in S, poissonKernel b (x - t)
                    ≥ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) := by
    -- reduce to indicators and compare pointwise
    have hpt : (S.indicator fun t => poissonKernel b (x - t))
                ≥ (Icc (x - b) (x + b)).indicator (fun t => poissonKernel b (x - t)) := by
      intro t; by_cases htJ : t ∈ Icc (x - b) (x + b)
      · have htS : t ∈ S := hJsubset htJ; simp [Set.indicator_of_mem htS, Set.indicator_of_mem htJ, le_rfl]
      · by_cases htS : t ∈ S
        · simp [Set.indicator_of_mem htS, Set.indicator_of_not_mem htJ, hnonneg t]
        · simp [Set.indicator_of_not_mem htS, Set.indicator_of_not_mem htJ]
    have hintS : Integrable (S.indicator fun t => poissonKernel b (x - t)) := by
      -- continuity on compact interval ⇒ integrable
      have cont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
        have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
          Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
        have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
          intro t; have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb); exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
        have hrec : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) :=
          continuous_const.div hden (by intro t; exact hpos t)
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using continuous_const.mul (continuous_const.mul hrec)
      -- use continuity on compact interval [-2,2]
      have : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (-2 : ℝ) 2) :=
      (cont.continuousAt.intervalIntegrable).integrableOn_Icc
      simpa [integrable_indicator_iff, hS_meas] using this
    have hintJ : Integrable ((Icc (x - b) (x + b)).indicator fun t => poissonKernel b (x - t)) := by
      have cont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
        have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
          Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
        have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
          intro t; have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb); exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
        have hrec : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) :=
          continuous_const.div hden (by intro t; exact hpos t)
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using continuous_const.mul (continuous_const.mul hrec)
      have : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (x - b) (x + b)) :=
        (cont.continuousAt.intervalIntegrable).integrableOn_Icc
      have hmeasJ : MeasurableSet (Icc (x - b) (x + b)) := isClosed_Icc.measurableSet
      simpa [integrable_indicator_iff, hmeasJ] using this
    have := integral_mono_ae (μ := volume) hintJ hintS (ae_of_all _ hpt)
    simpa [integral_indicator, hS_meas, isClosed_Icc.measurableSet] using this
  -- Pointwise lower bound on J: for t ∈ J, |x - t| ≤ b ⇒ denominator ≤ 2 b^2
  have kernel_lb : ∀ t ∈ Icc (x - b) (x + b), (1 / (2 * Real.pi * b)) ≤ poissonKernel b (x - t) := by
    intro t ht
    have hdist : |x - t| ≤ b := by
      have h1 : -b ≤ t - x := by linarith [ht.1]
      have h2 : t - x ≤ b := by linarith [ht.2]
      have : |t - x| ≤ b := abs_le.mpr ⟨h1, h2⟩
      simpa [abs_sub_comm] using this
    have hbpos : 0 < b := hb
    have hb2pos : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hbpos)
    have sq_le : (x - t) ^ 2 ≤ b ^ 2 := by
      have : |x - t| ≤ b := by simpa [abs_sub_comm] using hdist
      simpa [pow_two] using (sq_le_sq.mpr this)
    have den_le : (x - t) ^ 2 + b ^ 2 ≤ 2 * b ^ 2 := by
      have := add_le_add_right sq_le (b ^ 2); simpa [two_mul] using this
    have den_pos : 0 < (x - t) ^ 2 + b ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) hb2pos
    have inv_le : (1 : ℝ) / (2 * b ^ 2) ≤ (1 : ℝ) / ((x - t) ^ 2 + b ^ 2) :=
      one_div_le_one_div_of_le den_pos den_le
    have cnonneg : 0 ≤ (1 / Real.pi) * b :=
      mul_nonneg (le_of_lt (inv_pos.mpr Real.pi_pos)) hb0
    have := mul_le_mul_of_nonneg_left inv_le cnonneg
    -- rewrite to kernel form
    have hleft : (1 / Real.pi) * b * (1 / (2 * b ^ 2)) = (1 / (2 * Real.pi * b)) := by
      field_simp [one_div] at *
    have hright : (1 / Real.pi) * b * (1 / ((x - t) ^ 2 + b ^ 2)) = poissonKernel b (x - t) := by
      simp [poissonKernel, one_div, div_eq_mul_inv]
    simpa [hleft, hright]
  -- Lower bound the integral over J by a constant times its length 2b
  have measJ_toReal : (volume (Icc (x - b) (x + b))).toReal = 2 * b := by
    have : volume (Icc (x - b) (x + b)) = ENNReal.ofReal ((x + b) - (x - b)) := by
      simpa [sub_eq_add_neg] using (Real.volume_Icc : _)
    have hnn : 0 ≤ (2 : ℝ) * b := mul_nonneg (by norm_num) hb0
    have : (volume (Icc (x - b) (x + b))).toReal = (2 : ℝ) * b := by
      simpa [this, ENNReal.toReal_ofReal, hnn] using rfl
    simpa using this
  have constJ : (∫ t in Icc (x - b) (x + b), poissonKernel b (x - t))
                  ≥ (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) (x + b))).toReal := by
    have hmeasJ : MeasurableSet (Icc (x - b) (x + b)) := isClosed_Icc.measurableSet
    have hμJ : (volume (Icc (x - b) (x + b))) < ⊤ := by
      simp [Real.volume_Icc]
    have hcont : Continuous fun t : ℝ => poissonKernel b (x - t) := by
        have hden : Continuous fun t : ℝ => (x - t) ^ 2 + b ^ 2 :=
          Continuous.add ((continuous_const.sub continuous_id).pow 2) continuous_const
        have hpos : ∀ t, (x - t) ^ 2 + b ^ 2 ≠ 0 := by
        intro t; have : 0 < b ^ 2 := sq_pos_iff.mpr (ne_of_gt hb); exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) this)
      have hrec : Continuous fun t : ℝ => 1 / ((x - t) ^ 2 + b ^ 2) :=
        continuous_const.div hden (by intro t; exact hpos t)
        simpa [poissonKernel, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
        using continuous_const.mul (continuous_const.mul hrec)
    have hint : IntegrableOn (fun t : ℝ => poissonKernel b (x - t)) (Icc (x - b) (x + b)) :=
      (hcont.continuousAt.intervalIntegrable).integrableOn_Icc
    -- AE pointwise bound of a constant on J
    have hpt : (fun _ => (1 / (2 * Real.pi * b))) ≤ᵐ[Measure.restrict volume (Icc (x - b) (x + b))]
                (fun t => poissonKernel b (x - t)) := by
      refine (ae_restrict_iff.mpr hmeasJ).2 ?_;
      exact eventually_of_forall (fun t ht => kernel_lb t ht)
    -- Integrability of the constant on J
    have hint_c : IntegrableOn (fun _ => (1 / (2 * Real.pi * b))) (Icc (x - b) (x + b)) := by
      -- constant on a finite-measure set is integrable
      simpa using (integrableOn_const.mpr hμJ)
    -- Compare integrals on J
    have hineq := integral_mono_ae (μ := volume.restrict (Icc (x - b) (x + b))) hint_c hint hpt
    -- Evaluate the constant integral
    have hconst : ∫ t in Icc (x - b) (x + b), (1 / (2 * Real.pi * b))
                    = (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) (x + b))).toReal := by
      simpa [integral_const, hmeasJ]
    -- Rearrange
    have : (1 / (2 * Real.pi * b)) * (volume (Icc (x - b) (x + b))).toReal
              ≤ ∫ t in Icc (x - b) (x + b), poissonKernel b (x - t) := by
      simpa [hconst] using hineq
    -- flip sides to match goal
    simpa [mul_comm] using this
  -- Integral over S ≥ integral over J
  have base : ∫ t in S, poissonKernel b (x - t) ≥ (1 / (2 * Real.pi * b)) * (2 * b) := by
    have := ge_trans int_mono constJ
    simpa [measJ_toReal] using this
  -- Multiply by (1/4) via ψ definition to finish
  have : (1 / (4 : ℝ)) * (∫ t in S, poissonKernel b (x - t)) ≥ (1 / (4 : ℝ)) * (1 / Real.pi) := by
    have : (1 / (4 : ℝ)) * (∫ t in S, poissonKernel b (x - t))
            ≥ (1 / (4 : ℝ)) * ((1 / (2 * Real.pi * b)) * (2 * b)) :=
      mul_le_mul_of_nonneg_left base (by norm_num)
    simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using this
  -- Rewrite to poissonSmooth and c0
  have conv_eq : poissonSmooth b x = ∫ t in S, poissonKernel b (x - t) := rfl
  have c0_eq : c0_plateau = (1 / (4 : ℝ)) * (1 / Real.pi) := by simp [c0_plateau, one_div]
  -- Compare with ψ convolution: (P_b * ψ)(x) = (1/4) * ∫_{-2}^2 P_b(x - t) dt
  -- We present the bound directly in terms of `poissonSmooth` and `c0_plateau`.
  simpa [conv_eq, c0_eq, one_div] using this

/-!
Existence form consumed by the wedge assembly: pick ψ, prove the basic
properties, and supply c0 = 1/(4π) with the uniform lower bound.
-/
lemma poisson_plateau_c0 :
  ∃ ψ : ℝ → ℝ, Function.Even ψ ∧ (∀ t, 0 ≤ ψ t) ∧ HasCompactSupport ψ ∧
    (∫ t, psi t ∂(volume) = 1) ∧
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ {b x : ℝ}, 0 < b → b ≤ 1 → |x| ≤ 1 →
      (∫ t, poissonKernel b (x - t) * psi t ∂(volume)) ≥ c0 := by
  refine ⟨psi, psi_even, psi_nonneg, psi_hasCompactSupport, ?mass, ⟨c0_plateau, c0_plateau_pos, ?bound⟩⟩
  · simpa using psi_integral_one
  · intro b x hb hb1 hx
    -- rewrite convolution against ψ as a set integral on [-2,2]
    have hmeas : MeasurableSet (Icc (-2 : ℝ) 2) := isClosed_Icc.measurableSet
    have hpt : (fun t => poissonKernel b (x - t) * psi t)
                = (Icc (-2 : ℝ) 2).indicator (fun t => (1/4 : ℝ) * poissonKernel b (x - t)) := by
      funext t
      by_cases ht : t ∈ Icc (-2 : ℝ) 2
      · simp [psi, Set.indicator_of_mem ht, mul_comm, mul_left_comm, mul_assoc]
      · simp [psi, Set.indicator_of_not_mem ht]
    have conv_eq : (∫ t, poissonKernel b (x - t) * psi t ∂(volume))
                    = (1/4 : ℝ) * ∫ t in Icc (-2 : ℝ) 2, poissonKernel b (x - t) ∂(volume) := by
      simp [hpt, integral_indicator, hmeas, integral_const, mul_comm, mul_left_comm, mul_assoc]
    -- apply the set bound proved above
    have base := poisson_plateau_lower_bound (b := b) (x := x) hb hb1 hx
    simpa [c0_plateau, conv_eq, one_div, mul_comm, mul_left_comm, mul_assoc] using base

end RS
end RH
