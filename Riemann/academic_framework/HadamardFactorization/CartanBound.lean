import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Riemann.academic_framework.HadamardFactorization.Lindelof
import Riemann.academic_framework.HadamardFactorization.Lemmas

noncomputable section

namespace ComplexAnalysis
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric MeasureTheory intervalIntegral
open scoped BigOperators Topology ENNReal

/-!
## Cartan / minimum-modulus bounds for Hadamard factorization (Tao's Theorem 22)

This file contains the "probabilistic radius" / averaging lemmas needed to upgrade the Hadamard
quotient growth bound from order `m+1` to any exponent `τ` with `ρ < τ < m+1`.

The key inputs are:
- `lindelof_zero_data`: summability of `‖z_n‖^{-σ}` for all `σ > ρ`;
- `posLog_log_one_div_abs_one_sub_le_sqrt`: a soft bound controlling the logarithmic singularity.
-/

/-! ### A radial majorant for the logarithmic singularity on a circle -/

lemma posLog_log_one_div_norm_one_sub_le_posLog_log_one_div_abs_one_sub
    {t : ℝ} (ht : t ≠ 1) (w : ℂ) (hw : ‖w‖ = t) :
    max 0 (Real.log (1 / ‖(1 : ℂ) - w‖))
      ≤ max 0 (Real.log (1 / |1 - t|)) := by
  -- Reverse triangle: `|1 - t| = |‖1‖ - ‖w‖| ≤ ‖1 - w‖`.
  have hrev : |(‖(1 : ℂ)‖ : ℝ) - ‖w‖| ≤ ‖(1 : ℂ) - w‖ :=
    abs_norm_sub_norm_le (1 : ℂ) w
  have hrev' : |1 - t| ≤ ‖(1 : ℂ) - w‖ := by
    simpa [hw] using hrev
  have ht0 : |1 - t| ≠ 0 := by
    -- `|1 - t| = 0 ↔ t = 1`
    have : (1 : ℝ) - t ≠ 0 := by
      intro h
      have : (t : ℝ) = 1 := (sub_eq_zero.mp h).symm
      exact ht this
    simpa [abs_eq_zero] using this
  have htpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm ht0)
  by_cases hw0 : ‖(1 : ℂ) - w‖ = 0
  · -- Then `w = 1`, hence `t = 1`, contradicting `ht`.
    have hw1 : w = (1 : ℂ) := by
      have : (1 : ℂ) - w = 0 := by simpa [norm_eq_zero] using hw0
      simpa [eq_comm] using (sub_eq_zero.mp this)
    have : t = 1 := by
      have : ‖w‖ = (1 : ℝ) := by simp [hw1]
      simpa [hw] using this
    exact (ht this).elim
  have hwpos : 0 < ‖(1 : ℂ) - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  have hdiv :
      (1 / ‖(1 : ℂ) - w‖ : ℝ) ≤ (1 / |1 - t| : ℝ) :=
    one_div_le_one_div_of_le htpos hrev'
  have hlog :
      Real.log (1 / ‖(1 : ℂ) - w‖) ≤ Real.log (1 / |1 - t|) := by
    have hposL : 0 < (1 / ‖(1 : ℂ) - w‖ : ℝ) := by positivity
    exact Real.log_le_log hposL hdiv
  exact max_le_max le_rfl hlog

/-! ### A coarse dyadic-interval bound for the singularity average -/

namespace LogSingularity

def φ (t : ℝ) : ℝ :=
  max 0 (Real.log (1 / |1 - t|))

lemma φ_nonneg (t : ℝ) : 0 ≤ φ t := by simp [φ]

lemma φ_le_sqrt (t : ℝ) : φ t ≤ Real.sqrt (2 / |1 - t|) := by
  simpa [φ] using (posLog_log_one_div_abs_one_sub_le_sqrt (t := t))

/-!
We fix a single universal constant for the dyadic averaging estimate:

`K := ∫_{1/4}^{4} sqrt(2/|1-t|) dt`.

All bounds below are then stated with a constant `Cφ` built from `K` (and `log 2`), which is
independent of the scale `A`.
-/

noncomputable def K : ℝ :=
  ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), Real.sqrt (2 / |1 - t|) ∂volume

lemma K_nonneg : 0 ≤ K := by
  -- Pointwise nonnegativity on the interval.
  have hle : (1 / 4 : ℝ) ≤ (4 : ℝ) := by norm_num
  have hnn : ∀ t ∈ Set.Icc (1 / 4 : ℝ) (4 : ℝ), 0 ≤ Real.sqrt (2 / |1 - t|) := by
    intro t ht
    exact Real.sqrt_nonneg _
  simpa [K] using (intervalIntegral.integral_nonneg (μ := (volume : MeasureTheory.Measure ℝ)) hle hnn)

noncomputable def Cφ : ℝ :=
  Real.log 2 + 4 * K + 1

lemma Cφ_pos : 0 < Cφ := by
  have hlog : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hK : 0 ≤ K := K_nonneg
  have : 0 < Real.log 2 + 4 * K := by nlinarith
  have : 0 < Real.log 2 + 4 * K + 1 := by linarith
  simpa [Cφ] using this

lemma intervalIntegrable_sqrt_two_div_abs_one_sub_Icc :
    IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (4 : ℝ) := by
  -- Reduce to integrability of `u ↦ sqrt(2/|u|)` on `[0,3]`, then compose with `t ↦ 1 - t` and `t ↦ t - 1`.
  let f : ℝ → ℝ := fun u => Real.sqrt (2 / |u|)

  have hf0 : IntervalIntegrable f volume (0 : ℝ) (3 : ℝ) := by
    -- Compare to `sqrt 2 * u^(-1/2)` on `(0,3]`.
    have hpow : IntervalIntegrable (fun u : ℝ => u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) := by
      simpa using
        (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (3 : ℝ))
          (r := (- (2⁻¹ : ℝ))) (by linarith : (-1 : ℝ) < - (2⁻¹ : ℝ)))
    have hpow2 :
        IntervalIntegrable (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) volume (0 : ℝ) (3 : ℝ) :=
      hpow.const_mul (Real.sqrt 2)
    have hEq :
        Set.EqOn f (fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (Set.uIoc (0 : ℝ) (3 : ℝ)) := by
      intro u hu
      have hu' : u ∈ Set.Ioc (0 : ℝ) (3 : ℝ) := by
        simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 3 by norm_num)] using hu
      have hu0 : 0 < u := hu'.1
      have hu0' : 0 ≤ u := le_of_lt hu0
      have habs : |u| = u := abs_of_nonneg hu0'
      have : f u = Real.sqrt (2 / u) := by simp [f, habs]
      calc
        f u = Real.sqrt (2 / u) := this
        _ = Real.sqrt 2 / Real.sqrt u := by
              simp
        _ = Real.sqrt 2 * (Real.sqrt u)⁻¹ := by simp [div_eq_mul_inv]
        _ = Real.sqrt 2 * (u ^ (2⁻¹ : ℝ))⁻¹ := by simp [Real.sqrt_eq_rpow]
        _ = Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ)) := by
              have h : (u ^ (2⁻¹ : ℝ))⁻¹ = u ^ (- (2⁻¹ : ℝ)) := by
                simpa using (Real.rpow_neg hu0' (2⁻¹ : ℝ)).symm
              simp [h]
    exact (IntervalIntegrable.congr (a := (0 : ℝ)) (b := (3 : ℝ)) (μ := (volume : MeasureTheory.Measure ℝ))
      (f := fun u : ℝ => Real.sqrt 2 * u ^ (- (2⁻¹ : ℝ))) (g := f) hEq.symm) hpow2

  have hf0' : IntervalIntegrable f volume (0 : ℝ) (3 / 4 : ℝ) :=
    hf0.mono_set (by
      intro u hu
      -- `uIcc 0 (3/4) ⊆ uIcc 0 3`.
      have hsub : Set.uIcc (0 : ℝ) (3 / 4 : ℝ) ⊆ Set.uIcc (0 : ℝ) (3 : ℝ) := by
        refine Set.uIcc_subset_uIcc ?_ ?_
        · simp
        · -- `3/4 ∈ uIcc 0 3`
          have h0 : (0 : ℝ) ≤ (3 / 4 : ℝ) := by nlinarith
          have h1 : (3 / 4 : ℝ) ≤ (3 : ℝ) := by nlinarith
          exact (Set.mem_uIcc).2 (Or.inl ⟨h0, h1⟩)
      exact hsub hu)

  -- Left part: `t ∈ [1/4,1]` corresponds to `u = 1 - t ∈ [0,3/4]`.
  have hleft : IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (1 : ℝ) := by
    have htmp : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 : ℝ) ((1 : ℝ) - (3 / 4 : ℝ)) := by
      simpa using (hf0'.comp_sub_left (c := (1 : ℝ)))
    have htmp' : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume ((1 : ℝ) - (3 / 4 : ℝ)) (1 : ℝ) := htmp.symm
    have hsub : ((1 : ℝ) - (3 / 4 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    -- rewrite endpoints
    have htmp'' : IntervalIntegrable (fun t : ℝ => f (1 - t)) volume (1 / 4 : ℝ) (1 : ℝ) := by
      simpa [hsub] using htmp'
    simpa [f] using htmp''

  -- Right part: `t ∈ [1,4]` corresponds to `u = t - 1 ∈ [0,3]`.
  have hright : IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 : ℝ) (4 : ℝ) := by
    have htmp : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) ((3 : ℝ) + (1 : ℝ)) := by
      simpa using (hf0.comp_sub_right (c := (1 : ℝ)))
    have hsub : ((3 : ℝ) + (1 : ℝ)) = (4 : ℝ) := by norm_num
    have htmp' : IntervalIntegrable (fun t : ℝ => f (t - 1)) volume (1 : ℝ) (4 : ℝ) := by
      simpa [hsub] using htmp
    have hcongr :
        Set.EqOn (fun t : ℝ => f (t - 1)) (fun t : ℝ => Real.sqrt (2 / |1 - t|)) (Set.uIoc (1 : ℝ) (4 : ℝ)) := by
      intro t ht
      simp [f, abs_sub_comm]
    exact (IntervalIntegrable.congr (a := (1 : ℝ)) (b := (4 : ℝ)) (μ := (volume : MeasureTheory.Measure ℝ))
      (f := fun t : ℝ => f (t - 1)) (g := fun t : ℝ => Real.sqrt (2 / |1 - t|)) hcongr) htmp'

  exact hleft.trans hright

end LogSingularity

/-! ### Counting zeros in balls from Lindelöf summability -/

namespace ZeroData

open scoped BigOperators

variable {f : ℂ → ℂ} (hz : ZeroData f)

lemma card_nonzero_zeros_le_tsum_mul_rpow {τ : ℝ}
    (hτ_pos : 0 < τ)
    (hsum : Summable (fun n : ℕ => ‖hz.zeros n‖⁻¹ ^ τ)) :
    ∀ {R : ℝ}, 0 < R →
      ((hz.finite_in_ball R).toFinset.card : ℝ)
        ≤ (∑' n : ℕ, ‖hz.zeros n‖⁻¹ ^ τ) * R ^ τ := by
  classical
  intro R hRpos
  set s : Finset ℕ := (hz.finite_in_ball R).toFinset
  have hR0 : R ≠ 0 := ne_of_gt hRpos
  have hτ0 : 0 ≤ τ := le_of_lt hτ_pos
  -- Lower bound each term in the finset by `(1/R)^τ`.
  have hterm :
      ∀ n ∈ s, (R⁻¹ ^ τ : ℝ) ≤ ‖hz.zeros n‖⁻¹ ^ τ := by
    intro n hn
    have hn' : hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ R := by
      simpa [s] using (Finset.mem_coe.1 hn)
    have hn0 : 0 < ‖hz.zeros n‖ := norm_pos_iff.2 hn'.1
    have h_le : (1 / R : ℝ) ≤ (1 / ‖hz.zeros n‖ : ℝ) :=
      one_div_le_one_div_of_le hn0 (by simpa [one_div] using hn'.2)
    -- Raise both sides to the power `τ`.
    have : (1 / R : ℝ) ^ τ ≤ (1 / ‖hz.zeros n‖ : ℝ) ^ τ :=
      Real.rpow_le_rpow (by positivity) h_le hτ0
    simpa [one_div, inv_rpow, hn0.ne'] using this
  have hsum_fin :
      (s.card : ℝ) * (R⁻¹ ^ τ : ℝ) ≤ ∑ n ∈ s, ‖hz.zeros n‖⁻¹ ^ τ := by
    -- Sum the pointwise bound.
    have := (Finset.sum_le_sum fun n hn => hterm n hn)
    -- Rewrite LHS sum of a constant.
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hle_tsum :
      (∑ n ∈ s, ‖hz.zeros n‖⁻¹ ^ τ) ≤ (∑' n : ℕ, ‖hz.zeros n‖⁻¹ ^ τ) := by
    -- Finite sum ≤ tsum (all terms are nonnegative).
    exact Summable.sum_le_tsum (s := s) (hs := fun _ _ => by positivity) hsum
  have hmain : (s.card : ℝ) * (R⁻¹ ^ τ : ℝ) ≤ (∑' n : ℕ, ‖hz.zeros n‖⁻¹ ^ τ) :=
    hsum_fin.trans hle_tsum
  -- Multiply by `R^τ` and simplify `(R⁻¹)^τ * R^τ = 1`.
  have hRpow0 : (R ^ τ : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hRpos τ)
  have hmul :
      (s.card : ℝ) * (R⁻¹ ^ τ : ℝ) * (R ^ τ) ≤ (∑' n : ℕ, ‖hz.zeros n‖⁻¹ ^ τ) * (R ^ τ) := by
    exact mul_le_mul_of_nonneg_right hmain (by positivity)
  -- Finish.
  have : (s.card : ℝ) ≤ (∑' n : ℕ, ‖hz.zeros n‖⁻¹ ^ τ) * R ^ τ := by
    -- Rearrange the left factor.
    have h1 : (R⁻¹ ^ τ : ℝ) * (R ^ τ) = 1 := by
      calc
        (R⁻¹ ^ τ : ℝ) * (R ^ τ) = (R ^ τ)⁻¹ * (R ^ τ) := by
          simp [Real.inv_rpow (le_of_lt hRpos)]
        _ = 1 := by simp [hRpow0]
    -- Use `hmul` and `h1`.
    simpa [mul_assoc, h1, mul_one, s] using hmul
  simpa [s, mul_assoc] using this

end ZeroData

end Hadamard
end ComplexAnalysis
