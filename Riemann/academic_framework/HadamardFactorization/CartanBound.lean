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

lemma log_ge_neg_max0_log_inv {x : ℝ} (_hx : 0 ≤ x) :
    Real.log x ≥ - max 0 (Real.log (1 / x)) := by
  -- Rewrite `log(1/x)` and split on the sign of `log x`.
  have : max 0 (Real.log (1 / x)) = max 0 (-Real.log x) := by
    simp [Real.log_inv]
  rw [this]
  by_cases hlog : 0 ≤ Real.log x
  · have hmax : max 0 (-Real.log x) = 0 := max_eq_left (by linarith)
    simpa [hmax] using hlog
  · have hlog' : Real.log x ≤ 0 := le_of_not_ge hlog
    have hmax : max 0 (-Real.log x) = -Real.log x := max_eq_right (by linarith)
    simp [hmax]

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

lemma intervalIntegrable_phi_dyadic {A : ℝ} (hA : 0 ≤ A) :
    IntervalIntegrable φ volume A (2 * A) := by
  classical
  by_cases hA0 : A = 0
  · subst hA0
    -- degenerate interval
    simpa using (intervalIntegral.intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (0 : ℝ) (0 : ℝ))
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hA_le : A ≤ 2 * A := by nlinarith

  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      -- On `[A,2A]` we have `t ≤ 1/2`, hence `φ t ≤ log 2`.
      have hφ_le : ∀ t ∈ Set.Icc A (2 * A), φ t ≤ Real.log 2 := by
        intro t ht
        have ht_le : t ≤ (1 / 2 : ℝ) := by
          have : t ≤ 2 * A := ht.2
          exact this.trans (by nlinarith [hsmall])
        have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
          have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
          have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
          simpa [abs_of_nonneg hnonneg] using this
        have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
          have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
          have := one_div_le_one_div_of_le hhalfpos hden
          simpa [one_div, div_eq_mul_inv] using this
        have hxpos : 0 < (1 / |1 - t| : ℝ) := by positivity
        have hlog : Real.log (1 / |1 - t|) ≤ Real.log 2 := Real.log_le_log hxpos hfrac
        have hlog2_nonneg : 0 ≤ Real.log 2 := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact Real.log_nonneg this
        have : max 0 (Real.log (1 / |1 - t|)) ≤ Real.log 2 := by
          simpa [max_le_iff] using And.intro hlog2_nonneg hlog
        simpa [φ] using this

      have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
        intervalIntegral.intervalIntegrable_const
      have hmeas : AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) := by
        have : Measurable φ := by
          unfold φ
          fun_prop
        exact this.aestronglyMeasurable
      have hdom :
          (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))] fun _ => ‖(Real.log 2 : ℝ)‖ := by
        refine MeasureTheory.ae_restrict_of_forall_mem
          (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.uIoc A (2 * A))
          (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A (2 * A)))) ?_
        intro t ht
        have htIoc : t ∈ Set.Ioc A (2 * A) := by
          simpa [Set.uIoc_of_le hA_le] using ht
        have ht' : t ∈ Set.Icc A (2 * A) := ⟨le_of_lt htIoc.1, htIoc.2⟩
        have hφt : φ t ≤ Real.log 2 := hφ_le t ht'
        have hφt0 : 0 ≤ φ t := φ_nonneg t
        have hlog2_nn : 0 ≤ (Real.log 2 : ℝ) := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact Real.log_nonneg this
        simpa [Real.norm_eq_abs, abs_of_nonneg hφt0, abs_of_nonneg hlog2_nn] using hφt
      exact IntervalIntegrable.mono_fun hconst hmeas hdom
  | inr hge_quarter =>
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          -- For `t ≥ 2`, we have `φ t = 0` (hence integrable).
          have hEq : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIoc A (2 * A)) := by
            intro t ht
            have htIoc : t ∈ Set.Ioc A (2 * A) := by
              simpa [Set.uIoc_of_le hA_le] using ht
            have ht2 : (2 : ℝ) ≤ t := le_trans hbig (le_of_lt htIoc.1)
            have hden : (1 : ℝ) ≤ |1 - t| := by
              have : (1 : ℝ) ≤ t - 1 := by linarith
              have : (1 : ℝ) ≤ |t - 1| := by
                simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
              simpa [abs_sub_comm] using this
            have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := by
              have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) hden
              exact (div_le_one hpos).2 hden
            have hpos : 0 < (1 / |1 - t| : ℝ) := by positivity
            have hlog : Real.log (1 / |1 - t|) ≤ 0 :=
              le_trans (Real.log_le_log hpos hfrac) (by simp)
            have : max 0 (Real.log (1 / |1 - t|)) = 0 := max_eq_left hlog
            simpa [φ] using this
          have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume A (2 * A) :=
            intervalIntegral.intervalIntegrable_const
          exact (IntervalIntegrable.congr (a := A) (b := (2 * A)) (μ := (volume : MeasureTheory.Measure ℝ))
            (f := fun _ => (0 : ℝ)) (g := fun t => φ t) (by
              intro t ht
              simpa using (hEq (x := t) ht).symm)) hz
      | inr hA_le_two =>
          -- Middle scale: `A ∈ [1/4,2]`; dominate by the integrable `sqrt` bound.
          have hsqrt_big :
              IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume (1 / 4 : ℝ) (4 : ℝ) :=
            intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
          have hsqrt :
              IntervalIntegrable (fun t : ℝ => Real.sqrt (2 / |1 - t|)) volume A (2 * A) := by
            refine hsqrt_big.mono_set ?_
            refine Set.uIcc_subset_uIcc ?_ ?_
            · exact (Set.mem_uIcc).2 (Or.inl ⟨hge_quarter, by nlinarith [hA_le_two]⟩)
            · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hge_quarter], by nlinarith [hA_le_two]⟩)
          have hmeas : AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) := by
            have : Measurable φ := by
              unfold φ
              fun_prop
            exact this.aestronglyMeasurable
          have hdom :
              (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))]
                fun t => ‖Real.sqrt (2 / |1 - t|)‖ := by
            refine MeasureTheory.ae_restrict_of_forall_mem
              (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.uIoc A (2 * A))
              (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A (2 * A)))) ?_
            intro t ht
            have htIoc : t ∈ Set.Ioc A (2 * A) := by
              simpa [Set.uIoc_of_le hA_le] using ht
            have ht' : t ∈ Set.Icc A (2 * A) := ⟨le_of_lt htIoc.1, htIoc.2⟩
            have hle : φ t ≤ Real.sqrt (2 / |1 - t|) := φ_le_sqrt t
            have hφ0 : 0 ≤ φ t := φ_nonneg t
            have hs0 : 0 ≤ Real.sqrt (2 / |1 - t|) := Real.sqrt_nonneg _
            -- avoid `simp` rewriting `sqrt(2/|1-t|)` into a quotient
            calc
              ‖φ t‖ = φ t := by rw [Real.norm_of_nonneg hφ0]
              _ ≤ Real.sqrt (2 / |1 - t|) := hle
              _ = ‖Real.sqrt (2 / |1 - t|)‖ := by
                    symm
                    rw [Real.norm_of_nonneg hs0]
          exact IntervalIntegrable.mono_fun hsqrt hmeas hdom

lemma intervalIntegrable_phi_div {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    IntervalIntegrable (fun r : ℝ => φ (r / a)) volume R (2 * R) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hRa_nonneg : 0 ≤ R / a := by
    exact div_nonneg hR (le_of_lt ha)
  have hφ : IntervalIntegrable φ volume (R / a) (2 * (R / a)) :=
    intervalIntegrable_phi_dyadic (A := (R / a)) hRa_nonneg
  -- scale by `a⁻¹`
  have := (hφ.comp_mul_right (c := (a⁻¹ : ℝ)))
  -- simplify endpoints and integrand
  have hupper : a * (R * (a⁻¹ * 2)) = (2 * R) := by
    field_simp [ha0]
  -- `comp_mul_right` produces the endpoint `a * (R * (a⁻¹ * 2))`; rewrite it to `2*R`.
  simpa [div_eq_mul_inv, ha0, hupper, mul_assoc, mul_left_comm, mul_comm] using this

lemma integral_phi_le_Cφ_mul {A : ℝ} (hA : 0 ≤ A) :
    (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
  classical
  by_cases hA0 : A = 0
  · subst hA0
    simp [Cφ, φ, K]
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
  have hA_le : A ≤ 2 * A := by nlinarith
  have hCφ_nn : 0 ≤ Cφ := le_of_lt Cφ_pos

  -- Small scale: `A ≤ 1/4`, hence `t ≤ 1/2` on `[A,2A]` and `φ t ≤ log 2`.
  cases le_total A (1 / 4 : ℝ) with
  | inl hsmall =>
      have hφ_le : ∀ t ∈ Set.Icc A (2 * A), φ t ≤ Real.log 2 := by
        intro t ht
        have ht0 : 0 ≤ t := le_trans hA ht.1
        have ht_le : t ≤ (1 / 2 : ℝ) := by
          have : t ≤ 2 * A := ht.2
          have : t ≤ (1 / 2 : ℝ) := this.trans (by nlinarith [hsmall])
          exact this
        -- Bound `log(1/|1-t|)` by `log 2`.
        have hlog2_nonneg : 0 ≤ Real.log 2 := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact Real.log_nonneg this
        have hden : (1 / 2 : ℝ) ≤ |1 - t| := by
          have hnonneg : 0 ≤ (1 - t : ℝ) := by linarith
          have : (1 / 2 : ℝ) ≤ (1 - t : ℝ) := by linarith
          simpa [abs_of_nonneg hnonneg] using this
        have hfrac : (1 / |1 - t| : ℝ) ≤ 2 := by
          have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
          -- `1/|1-t| ≤ 1/(1/2) = 2`
          have := one_div_le_one_div_of_le hhalfpos hden
          simpa [one_div, div_eq_mul_inv] using this
        have hxpos : 0 < (1 / |1 - t| : ℝ) := by positivity
        have hlog : Real.log (1 / |1 - t|) ≤ Real.log 2 := Real.log_le_log hxpos hfrac
        -- Convert to `max 0 _`.
        have : max 0 (Real.log (1 / |1 - t|)) ≤ Real.log 2 := by
          simpa [max_le_iff] using And.intro hlog2_nonneg hlog
        simpa [φ] using this

      -- Integrability: bounded by the constant `log 2` on a finite interval.
      have hconst : IntervalIntegrable (fun _ : ℝ => (Real.log 2 : ℝ)) volume A (2 * A) :=
        intervalIntegral.intervalIntegrable_const
      have hmeas : AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) := by
        -- `φ` is measurable, hence a.e. strongly measurable for any measure.
        have : Measurable φ := by
          unfold φ
          fun_prop
        exact this.aestronglyMeasurable
      have hdom : (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))] fun _ => ‖(Real.log 2 : ℝ)‖ := by
        -- Prove the bound pointwise on the interval, then restrict.
        refine MeasureTheory.ae_restrict_of_forall_mem
          (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.uIoc A (2 * A))
          (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A (2 * A)))) ?_
        intro t ht
        have htIoc : t ∈ Set.Ioc A (2 * A) := by
          simpa [Set.uIoc_of_le hA_le] using ht
        have ht' : t ∈ Set.Icc A (2 * A) := ⟨le_of_lt htIoc.1, htIoc.2⟩
        have hφt : φ t ≤ Real.log 2 := hφ_le t ht'
        have hφt0 : 0 ≤ φ t := φ_nonneg t
        have hlog2_nn : 0 ≤ (Real.log 2 : ℝ) := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          exact Real.log_nonneg this
        -- norms are absolute values on ℝ
        simpa [Real.norm_eq_abs, abs_of_nonneg hφt0, abs_of_nonneg hlog2_nn] using hφt
      have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
        IntervalIntegrable.mono_fun hconst hmeas hdom

      have hle_int :
          (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ ∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume := by
        refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ)) hA_le hφ_int hconst ?_
        intro t ht
        exact hφ_le t ht

      -- Compute the RHS and finish.
      have hRHS : (∫ (t : ℝ) in A..(2 * A), (Real.log 2 : ℝ) ∂volume) = A * Real.log 2 := by
        -- `∫ c = (b-a)*c`
        simp [intervalIntegral.integral_const, sub_eq_add_neg, add_assoc, two_mul]
      -- `A*log2 ≤ Cφ*A`
      have hcoef : A * Real.log 2 ≤ Cφ * A := by
        have hlog_le : Real.log 2 ≤ Cφ := by
          -- `log 2 ≤ log 2 + 4*K + 1`
          dsimp [Cφ]
          have hK : 0 ≤ K := K_nonneg
          linarith [hK]
        have := mul_le_mul_of_nonneg_left hlog_le hA
        -- rewrite `A * Cφ` as `Cφ * A`
        simpa [mul_assoc, mul_left_comm, mul_comm] using this
      -- Chain inequalities.
      calc
        (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
            ≤ A * Real.log 2 := by simpa [hRHS] using hle_int
        _ ≤ Cφ * A := hcoef

  | inr hge_quarter =>
      -- Large scale: if `2 ≤ A`, then `φ` vanishes on `[A,2A]`.
      cases le_total (2 : ℝ) A with
      | inl hbig =>
          have hφ0 : Set.EqOn (fun t : ℝ => φ t) (fun _ => (0 : ℝ)) (Set.uIcc A (2 * A)) := by
            intro t ht
            have ht' : t ∈ Set.Icc A (2 * A) := by
              simpa [Set.uIcc_of_le hA_le] using ht
            have htA : A ≤ t := ht'.1
            have ht2 : 2 ≤ t := le_trans hbig htA
            have hden : 1 ≤ |1 - t| := by
              -- for `t ≥ 2`, `|1-t| = t-1 ≥ 1`
              have : (1 : ℝ) ≤ t - 1 := by linarith
              have : (1 : ℝ) ≤ |t - 1| := by simpa [abs_of_nonneg (by linarith : 0 ≤ t - 1)] using this
              simpa [abs_sub_comm] using this
            have hfrac : (1 / |1 - t| : ℝ) ≤ 1 := by
              have hpos : 0 < |1 - t| := lt_of_lt_of_le (by norm_num) hden
              exact (div_le_one hpos).2 hden
            have hlog : Real.log (1 / |1 - t|) ≤ 0 := by
              have hpos : 0 < (1 / |1 - t| : ℝ) := by positivity
              exact le_trans (Real.log_le_log hpos hfrac) (by simp)
            -- so `max 0` is zero
            have hmax : max 0 (Real.log (1 / |1 - t|)) = 0 := max_eq_left hlog
            simpa [φ] using hmax
          have : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) = 0 := by
            simpa using intervalIntegral.integral_congr (μ := (volume : MeasureTheory.Measure ℝ)) hφ0
          -- RHS is nonnegative, so done.
          have hnonneg : (0 : ℝ) ≤ Cφ * A := mul_nonneg hCφ_nn hA
          simpa [this] using hnonneg
      | inr hA_le_two =>
          -- Middle scale: `A ∈ [1/4,2]`. Compare to the sqrt bound and then to `K`.
          have hA_lower : (1 / 4 : ℝ) ≤ A := hge_quarter
          have hA_upper : (2 * A : ℝ) ≤ 4 := by nlinarith [hA_le_two]

          -- Sqrt integrable on `[A,2A]` by restriction.
          let s (t : ℝ) : ℝ := Real.sqrt (2 / |1 - t|)
          have hsqrt_big :
              IntervalIntegrable s volume (1 / 4 : ℝ) (4 : ℝ) :=
            intervalIntegrable_sqrt_two_div_abs_one_sub_Icc
          have hsqrt :
              IntervalIntegrable s volume A (2 * A) := by
            refine hsqrt_big.mono_set ?_
            -- `uIcc A (2A) ⊆ uIcc (1/4) 4`
            refine Set.uIcc_subset_uIcc ?_ ?_
            · exact (Set.mem_uIcc).2 (Or.inl ⟨hA_lower, by nlinarith [hA_le_two]⟩)
            · exact (Set.mem_uIcc).2 (Or.inl ⟨by nlinarith [hA_lower], hA_upper⟩)
          have hmeasφ : AEStronglyMeasurable (fun t : ℝ => φ t) (volume.restrict (Set.uIoc A (2 * A))) := by
            have : Measurable φ := by
              unfold φ
              fun_prop
            exact this.aestronglyMeasurable
          have hdomφ : (fun t : ℝ => ‖φ t‖) ≤ᶠ[ae (volume.restrict (Set.uIoc A (2 * A)))] fun t => ‖s t‖ := by
            refine MeasureTheory.ae_restrict_of_forall_mem
              (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.uIoc A (2 * A))
              (by simpa using (measurableSet_uIoc : MeasurableSet (Set.uIoc A (2 * A)))) ?_
            intro t ht
            have htIoc : t ∈ Set.Ioc A (2 * A) := by
              simpa [Set.uIoc_of_le hA_le] using ht
            have ht' : t ∈ Set.Icc A (2 * A) := ⟨le_of_lt htIoc.1, htIoc.2⟩
            have hle : φ t ≤ s t := φ_le_sqrt t
            have hφ0 : 0 ≤ φ t := φ_nonneg t
            have hs0 : 0 ≤ s t := Real.sqrt_nonneg _
            simpa [Real.norm_eq_abs, abs_of_nonneg hφ0, abs_of_nonneg hs0] using hle
          have hφ_int : IntervalIntegrable φ volume A (2 * A) :=
            IntervalIntegrable.mono_fun hsqrt hmeasφ hdomφ

          have hle_int :
              (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
                ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := by
            refine intervalIntegral.integral_mono_on (μ := (volume : MeasureTheory.Measure ℝ)) hA_le hφ_int hsqrt ?_
            intro t ht
            exact φ_le_sqrt t
          have hle_K :
              (∫ (t : ℝ) in A..(2 * A), s t ∂volume)
                ≤ ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume := by
            refine intervalIntegral.integral_mono_interval (μ := (volume : MeasureTheory.Measure ℝ))
              (c := (1 / 4 : ℝ)) (d := (4 : ℝ)) (a := A) (b := (2 * A))
              hA_lower hA_le hA_upper ?_ hsqrt_big
            -- a.e. nonnegativity on the big interval
            exact Filter.Eventually.of_forall (fun _t => Real.sqrt_nonneg _)
          have hKdef : (∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume) = K := by
            rfl
          have hKbound : K ≤ (4 * K) * A := by
            have hK0 : 0 ≤ K := K_nonneg
            have hA' : (1 : ℝ) ≤ 4 * A := by nlinarith [hA_lower]
            calc
              K = K * 1 := by simp
              _ ≤ K * (4 * A) := mul_le_mul_of_nonneg_left hA' hK0
              _ = (4 * K) * A := by ring
          have hfinal :
              (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ Cφ * A := by
            have : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ K := by
              calc
                (∫ (t : ℝ) in A..(2 * A), φ t ∂volume)
                    ≤ ∫ (t : ℝ) in A..(2 * A), s t ∂volume := hle_int
                _ ≤ ∫ (t : ℝ) in (1 / 4 : ℝ)..(4 : ℝ), s t ∂volume := hle_K
                _ = K := by simp [K, s]
            have h1 : (∫ (t : ℝ) in A..(2 * A), φ t ∂volume) ≤ (4 * K) * A :=
              this.trans hKbound
            -- `(4*K)*A ≤ Cφ*A`
            have hcoef : (4 * K : ℝ) ≤ Cφ := by
              have hlog2 : 0 ≤ Real.log 2 := by
                have : (1 : ℝ) ≤ 2 := by norm_num
                exact Real.log_nonneg this
              have hK : 0 ≤ K := K_nonneg
              dsimp [Cφ]
              linarith [hlog2, hK]
            have h2 : (4 * K) * A ≤ Cφ * A := mul_le_mul_of_nonneg_right hcoef hA
            exact h1.trans h2
          exact hfinal

lemma integral_phi_div_le_Cφ_mul {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume) ≤ Cφ * R := by
  by_cases hR0 : R = 0
  · subst hR0
    simp
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hc : (a⁻¹ : ℝ) ≠ 0 := inv_ne_zero ha0
  -- Scale-change: `r = t * a`.
  have hsub :=
    (intervalIntegral.integral_comp_mul_right
      (f := fun t : ℝ => φ t) (a := R) (b := (2 * R)) (c := (a⁻¹ : ℝ)) hc)
  -- Rewrite the LHS integrand.
  have hsub' :
      (∫ (r : ℝ) in R..(2 * R), φ (r / a) ∂volume)
        = a * (∫ (t : ℝ) in (R / a)..((2 * R) / a), φ t ∂volume) := by
    -- `c⁻¹ •` is multiplication by `c⁻¹` in ℝ, and `(a⁻¹)⁻¹ = a`.
    -- Also `r * a⁻¹ = r / a`.
    have : (a⁻¹ : ℝ)⁻¹ = a := by simp
    -- massage endpoints
    simpa [div_eq_mul_inv, this, mul_assoc, mul_left_comm, mul_comm] using hsub

  -- Apply the dyadic-interval bound at scale `R/a`.
  have hRa_nonneg : 0 ≤ R / a := by
    have : 0 ≤ (a : ℝ) := le_of_lt ha
    exact div_nonneg hR this
  have hmain :
      (∫ (t : ℝ) in (R / a)..((2 * R) / a), φ t ∂volume) ≤ Cφ * (R / a) := by
    -- `((2*R)/a) = 2*(R/a)`
    have : (2 * R) / a = 2 * (R / a) := by ring
    simpa [this] using (integral_phi_le_Cφ_mul (A := (R / a)) hRa_nonneg)
  -- Multiply by `a` (positive) and simplify.
  have ha_nn : 0 ≤ (a : ℝ) := le_of_lt ha
  have := mul_le_mul_of_nonneg_left hmain ha_nn
  -- `a * (Cφ * (R/a)) = Cφ * R`.
  have hsim : a * (Cφ * (R / a)) = Cφ * R := by
    field_simp [ha0]
  -- Finish.
  simpa [hsub', hsim, mul_assoc] using this

end LogSingularity

/-! ### Counting zeros in balls from Lindelöf summability -/

namespace ZeroData

open scoped BigOperators

/-!
## Bridging lemma: from the 1D singularity `φ` to a complex lower bound

This is the inequality used in Tao's probabilistic-radius argument: on a circle `‖u‖ = r`,
the quantity `log ‖1 - u/a‖` is bounded below in terms of `φ(r/‖a‖)`.
-/

lemma log_norm_one_sub_div_ge_neg_phi {u a : ℂ} {r : ℝ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖) :
    Real.log ‖(1 : ℂ) - u / a‖ ≥ -LogSingularity.φ (r / ‖a‖) := by
  -- Compare norms using the reverse triangle inequality.
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnorm_eq : ‖(1 : ℂ) - u / a‖ = ‖a - u‖ / ‖a‖ := by
    -- `(1 - u/a) = (a - u)/a`
    have : (1 : ℂ) - u / a = (a - u) / a := by
      field_simp [ha]
    exact (calc
      ‖(1 : ℂ) - u / a‖ = ‖(a - u) / a‖ := by simpa [this]
      _ = ‖a - u‖ / ‖a‖ := by simp [norm_div])
  have hrev : |‖a‖ - ‖u‖| ≤ ‖a - u‖ := by
    simpa using (abs_norm_sub_norm_le a u)
  have hdiv : |‖a‖ - ‖u‖| / ‖a‖ ≤ ‖a - u‖ / ‖a‖ :=
    div_le_div_of_nonneg_right hrev (le_of_lt ha_norm)
  have habs : |1 - (r / ‖a‖)| = |‖a‖ - ‖u‖| / ‖a‖ := by
    -- rewrite using `‖u‖ = r`
    have hu : ‖u‖ = r := hur
    have ha0 : (‖a‖ : ℝ) ≠ 0 := ha_norm.ne'
    have h1 : (1 : ℝ) - (r / ‖a‖) = (‖a‖ - r) / ‖a‖ := by
      field_simp [ha0]
    exact (calc
      |1 - (r / ‖a‖)| = |(‖a‖ - r) / ‖a‖| := by simpa [h1]
      _ = |‖a‖ - r| / ‖a‖ := by simp [abs_div, abs_of_pos ha_norm]
      _ = |‖a‖ - ‖u‖| / ‖a‖ := by simpa [hu])
  have hnorm_ge : |1 - (r / ‖a‖)| ≤ ‖(1 : ℂ) - u / a‖ := by
    have : |1 - (r / ‖a‖)| ≤ ‖a - u‖ / ‖a‖ := by
      simpa [habs] using hdiv
    simpa [hnorm_eq] using this

  -- Positivity of the scalar distance from the forbidden radius.
  have hx0 : 0 < |1 - (r / ‖a‖)| := by
    have : (1 - (r / ‖a‖) : ℝ) ≠ 0 := by
      intro h0
      have : r = ‖a‖ := by
        have : r / ‖a‖ = (1 : ℝ) := by linarith
        simpa using (div_eq_iff ha_norm.ne').1 this
      exact hr this
    have : |1 - (r / ‖a‖)| ≠ 0 := by
      simpa [abs_eq_zero] using this
    exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm this)

  -- Use `log_ge_neg_max0_log_inv` at `x = |1 - r/‖a‖|` and monotonicity of `log`.
  have hlogx :
      Real.log |1 - (r / ‖a‖)|
        ≥ -max 0 (Real.log (1 / |1 - (r / ‖a‖)|)) :=
    LogSingularity.log_ge_neg_max0_log_inv (x := |1 - (r / ‖a‖)|) (le_of_lt hx0)
  have hlog_mono :
      Real.log |1 - (r / ‖a‖)| ≤ Real.log ‖(1 : ℂ) - u / a‖ :=
    Real.log_le_log (by positivity) hnorm_ge
  have hphi :
      -max 0 (Real.log (1 / |1 - (r / ‖a‖)|)) = -LogSingularity.φ (r / ‖a‖) := by
    simp [LogSingularity.φ, abs_sub_comm]
  linarith [hlog_mono, hlogx, hphi]

variable {f : ℂ → ℂ} (hz : ZeroData f)

lemma exists_radius_Ioc_sum_phi_div_le_Cφ_mul_card :
    ∀ {R : ℝ}, 0 < R →
      ∃ r ∈ Set.Ioc R (2 * R),
        (∑ n ∈ (hz.finite_in_ball (4 * R)).toFinset, LogSingularity.φ (r / ‖hz.zeros n‖))
          ≤ LogSingularity.Cφ * ((hz.finite_in_ball (4 * R)).toFinset.card : ℝ) := by
  classical
  intro R hRpos
  have hR : 0 ≤ R := le_of_lt hRpos
  have hab : R ≤ 2 * R := by nlinarith
  -- Indices of nonzero zeros in the ball of radius `4R` (finite by `ZeroData`).
  let s : Finset ℕ := (hz.finite_in_ball (4 * R)).toFinset
  -- The summed function of interest.
  let g : ℝ → ℝ := ∑ n ∈ s, fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖)

  have hterm_int :
      ∀ n ∈ s, IntervalIntegrable (fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖))
        (volume : MeasureTheory.Measure ℝ) R (2 * R) := by
    intro n hn
    have hn' : hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 4 * R := by
      simpa [s] using (Finset.mem_coe.1 hn)
    have ha : 0 < ‖hz.zeros n‖ := norm_pos_iff.2 hn'.1
    -- Use the interval-integrability lemma for `φ(r/a)`.
    simpa [LogSingularity.φ, LogSingularity.intervalIntegrable_phi_div] using
      (LogSingularity.intervalIntegrable_phi_div (a := ‖hz.zeros n‖) (R := R) ha hR)

  have hg_int : IntervalIntegrable g (volume : MeasureTheory.Measure ℝ) R (2 * R) := by
    -- Finite sum of interval-integrable functions.
    have : ∀ n ∈ s, IntervalIntegrable (fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖))
        (volume : MeasureTheory.Measure ℝ) R (2 * R) := hterm_int
    -- `IntervalIntegrable.sum` works on the function-sum `∑ n∈s, f n`.
    simpa [g] using (IntervalIntegrable.sum (μ := (volume : MeasureTheory.Measure ℝ)) (a := R) (b := (2 * R))
      s (f := fun n : ℕ => fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖)) this)

  have hg_on : IntegrableOn g (Set.Ioc R (2 * R)) (volume : MeasureTheory.Measure ℝ) := by
    -- Interval integrable ↔ integrable on `Ioc` when `R ≤ 2R`.
    have hiff :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := (volume : MeasureTheory.Measure ℝ))
        (f := g) (a := R) (b := (2 * R)) hab)
    exact hiff.1 hg_int

  -- Measure of the interval is finite and nonzero.
  have hμ_ne0 : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) ≠ 0 := by
    -- `volume (Ioc R 2R) = ofReal (2R - R) = ofReal R`
    have : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) = ENNReal.ofReal R := by
      simp [Real.volume_Ioc, sub_eq_add_neg, two_mul]
    intro h0
    have : R ≤ 0 := (ENNReal.ofReal_eq_zero).1 (this.symm.trans h0)
    linarith
  have hμ_neTop : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) ≠ ⊤ := by
    have : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) = ENNReal.ofReal R := by
      simp [Real.volume_Ioc, sub_eq_add_neg, two_mul]
    simpa [this] using (ENNReal.ofReal_ne_top : ENNReal.ofReal R ≠ ⊤)

  -- Pick `r` where `g r` is ≤ its average.
  rcases MeasureTheory.exists_le_setAverage (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.Ioc R (2 * R))
      (f := g) hμ_ne0 hμ_neTop hg_on with ⟨r, hr_mem, hr_le_avg⟩

  -- Bound the average using the integral bound for each term.
  have havg_le :
      (⨍ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
        ≤ LogSingularity.Cφ * (s.card : ℝ) := by
    -- Rewrite average as `(μ.real s)⁻¹ * ∫`.
    have hreal : (volume.real (Set.Ioc R (2 * R)) : ℝ) = R := by
      -- `volume (Ioc R 2R) = ofReal R`, and `toReal (ofReal R) = R` for `R ≥ 0`.
      have : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) = ENNReal.ofReal R := by
        simp [Real.volume_Ioc, sub_eq_add_neg, two_mul]
      simp [Measure.real, this, hR]
    -- Integral bound.
    have hintegral :
        (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
          ≤ LogSingularity.Cφ * R * (s.card : ℝ) := by
      -- Switch to interval integral and integrate the finite sum termwise.
      have hInt_eq :
          (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
            = ∫ x in R..(2 * R), g x ∂(volume : MeasureTheory.Measure ℝ) := by
        simpa using (intervalIntegral.integral_of_le (μ := (volume : MeasureTheory.Measure ℝ)) (f := g) hab).symm
      -- Expand the integral of the sum.
      have hsum_int :
          (∫ x in R..(2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
            = ∑ n ∈ s, ∫ x in R..(2 * R), (fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖)) x
                ∂(volume : MeasureTheory.Measure ℝ) := by
        -- use `integral_finset_sum`
        simpa [g] using
          (intervalIntegral.integral_finset_sum (μ := (volume : MeasureTheory.Measure ℝ))
            (a := R) (b := (2 * R)) (s := s)
            (f := fun n : ℕ => fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖)) hterm_int)
      -- Bound each integral by `Cφ * R`.
      have hle_each :
          ∀ n ∈ s, (∫ x in R..(2 * R), LogSingularity.φ (x / ‖hz.zeros n‖)
              ∂(volume : MeasureTheory.Measure ℝ))
            ≤ LogSingularity.Cφ * R := by
        intro n hn
        have hn' : hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 4 * R := by
          simpa [s] using (Finset.mem_coe.1 hn)
        have ha : 0 < ‖hz.zeros n‖ := norm_pos_iff.2 hn'.1
        -- Apply the scaling bound lemma.
        simpa using (LogSingularity.integral_phi_div_le_Cφ_mul (a := ‖hz.zeros n‖) (R := R) ha hR)
      have hsum_le :
          (∑ n ∈ s, ∫ x in R..(2 * R), LogSingularity.φ (x / ‖hz.zeros n‖) ∂(volume : MeasureTheory.Measure ℝ))
            ≤ ∑ n ∈ s, (LogSingularity.Cφ * R) := by
        refine Finset.sum_le_sum ?_
        intro n hn
        exact hle_each n hn
      -- Finish: `∑ (Cφ*R) = card*s * (Cφ*R)`
      have hsum_const : (∑ n ∈ s, (LogSingularity.Cφ * R)) = (s.card : ℝ) * (LogSingularity.Cφ * R) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      -- assemble
      have : (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
              ≤ (s.card : ℝ) * (LogSingularity.Cφ * R) := by
        -- rewrite `∫` and apply the bounds
        calc
          (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
              = ∫ x in R..(2 * R), g x ∂(volume : MeasureTheory.Measure ℝ) := hInt_eq
          _ = ∑ n ∈ s, ∫ x in R..(2 * R), LogSingularity.φ (x / ‖hz.zeros n‖) ∂(volume : MeasureTheory.Measure ℝ) := by
                simpa [hsum_int]
          _ ≤ ∑ n ∈ s, (LogSingularity.Cφ * R) := hsum_le
          _ = (s.card : ℝ) * (LogSingularity.Cφ * R) := by simpa [hsum_const]
      -- reorder factors
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    -- Now divide by `R` for the average.
    have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
    -- `setAverage_eq`
    have havg_eq :
        (⨍ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
          = (R : ℝ)⁻¹ * (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ)) := by
      -- scalar multiplication on ℝ is multiplication
      simp [MeasureTheory.setAverage_eq, hreal, smul_eq_mul]
    -- apply bound
    calc
      (⨍ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
          = R⁻¹ * (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ)) := havg_eq
      _ ≤ R⁻¹ * (LogSingularity.Cφ * R * (s.card : ℝ)) := by
            gcongr
      _ = LogSingularity.Cφ * (s.card : ℝ) := by
            field_simp [hRne]

  refine ⟨r, hr_mem, ?_⟩
  -- `g r` is bounded by the average, and the average by `Cφ * card`.
  have : g r ≤ LogSingularity.Cφ * (s.card : ℝ) := hr_le_avg.trans havg_le
  -- Unfold `g` to a finset sum at the point.
  simpa [g] using this

lemma exists_radius_Ioc_sum_phi_div_le_Cφ_mul_card_avoid :
    ∀ {R : ℝ}, 0 < R →
      ∃ r ∈ Set.Ioc R (2 * R),
        r ∉ ((hz.finite_in_ball (4 * R)).toFinset.image (fun n : ℕ => ‖hz.zeros n‖) : Finset ℝ) ∧
        (∑ n ∈ (hz.finite_in_ball (4 * R)).toFinset, LogSingularity.φ (r / ‖hz.zeros n‖))
          ≤ LogSingularity.Cφ * ((hz.finite_in_ball (4 * R)).toFinset.card : ℝ) := by
  classical
  intro R hRpos
  -- Use the positive-measure version of the first moment method to get many good radii, then avoid
  -- finitely many forbidden radii.
  let s : Finset ℕ := (hz.finite_in_ball (4 * R)).toFinset
  let bad : Finset ℝ := s.image (fun n : ℕ => ‖hz.zeros n‖)
  let g : ℝ → ℝ := ∑ n ∈ s, fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖)
  have hR : 0 ≤ R := le_of_lt hRpos
  have hab : R ≤ 2 * R := by nlinarith

  -- Integrability of `g` on the interval.
  have hterm_int :
      ∀ n ∈ s, IntervalIntegrable (fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖))
        (volume : MeasureTheory.Measure ℝ) R (2 * R) := by
    intro n hn
    have hn' : hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 4 * R := by
      simpa [s] using (Finset.mem_coe.1 hn)
    have ha : 0 < ‖hz.zeros n‖ := norm_pos_iff.2 hn'.1
    simpa using (LogSingularity.intervalIntegrable_phi_div (a := ‖hz.zeros n‖) (R := R) ha hR)
  have hg_int : IntervalIntegrable g (volume : MeasureTheory.Measure ℝ) R (2 * R) := by
    simpa [g] using
      (IntervalIntegrable.sum (μ := (volume : MeasureTheory.Measure ℝ)) (a := R) (b := (2 * R))
        s (f := fun n : ℕ => fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖)) hterm_int)
  have hg_on : IntegrableOn g (Set.Ioc R (2 * R)) (volume : MeasureTheory.Measure ℝ) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (μ := (volume : MeasureTheory.Measure ℝ))
      (f := g) (a := R) (b := (2 * R)) hab).1 hg_int

  have hμ_ne0 : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) ≠ 0 := by
    have : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) = ENNReal.ofReal R := by
      simp [Real.volume_Ioc, sub_eq_add_neg, two_mul]
    intro h0
    have : R ≤ 0 := (ENNReal.ofReal_eq_zero).1 (this.symm.trans h0)
    linarith
  have hμ_neTop : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) ≠ ⊤ := by
    have : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) = ENNReal.ofReal R := by
      simp [Real.volume_Ioc, sub_eq_add_neg, two_mul]
    simpa [this] using (ENNReal.ofReal_ne_top : ENNReal.ofReal R ≠ ⊤)

  -- Positive measure set of good radii.
  have hpos :
      0 < (volume {x : ℝ | x ∈ Set.Ioc R (2 * R) ∧ g x ≤ ⨍ a in Set.Ioc R (2 * R), g a ∂(volume : MeasureTheory.Measure ℝ)}
        : ℝ≥0∞) := by
    simpa using
      (MeasureTheory.measure_le_setAverage_pos (μ := (volume : MeasureTheory.Measure ℝ)) (s := Set.Ioc R (2 * R))
        (f := g) hμ_ne0 hμ_neTop hg_on)

  -- Avoid finitely many bad radii (measure zero).
  have : ∃ r ∈ {x : ℝ | x ∈ Set.Ioc R (2 * R) ∧ g x ≤ ⨍ a in Set.Ioc R (2 * R), g a ∂(volume : MeasureTheory.Measure ℝ)},
      r ∉ (bad : Set ℝ) := by
    by_contra h
    push_neg at h
    have hsub :
        ({x : ℝ | x ∈ Set.Ioc R (2 * R) ∧ g x ≤ ⨍ a in Set.Ioc R (2 * R), g a ∂(volume : MeasureTheory.Measure ℝ)}
          : Set ℝ) ⊆ (bad : Set ℝ) := by
      intro x hx
      exact h x hx
    have hbad0 : (volume (bad : Set ℝ) : ℝ≥0∞) = 0 := by
      simpa using (Set.Finite.measure_zero (μ := (volume : MeasureTheory.Measure ℝ)) bad.finite_toSet)
    have : (volume
        ({x : ℝ | x ∈ Set.Ioc R (2 * R) ∧ g x ≤ ⨍ a in Set.Ioc R (2 * R), g a ∂(volume : MeasureTheory.Measure ℝ)}
          : Set ℝ) : ℝ≥0∞) = 0 :=
      MeasureTheory.measure_mono_null hsub hbad0
    exact (ne_of_gt hpos) this

  rcases this with ⟨r, hr_good, hr_not_bad⟩
  have hr_mem : r ∈ Set.Ioc R (2 * R) := (hr_good.1)
  have hr_le_avg : g r ≤ ⨍ a in Set.Ioc R (2 * R), g a ∂(volume : MeasureTheory.Measure ℝ) := (hr_good.2)

  -- Now use the already-proved average bound at one good radius (same as in the previous lemma).
  rcases exists_radius_Ioc_sum_phi_div_le_Cφ_mul_card (hz := hz) (R := R) hRpos with ⟨r0, hr0_mem, hr0_bound⟩
  -- We need a bound at `r`, not `r0`. We use `g r ≤ average ≤ Cφ*card` (as in the previous lemma),
  -- which is exactly what the previous lemma established for *some* point; re-prove the final
  -- average bound locally by reusing the `avg ≤ Cφ*card` proof from that lemma.
  -- Rather than re-proving it again, we directly unfold `g` and use the inequality chain:
  -- `g r ≤ average ≤ Cφ*card(s)` with the same `avg` bound as in `exists_radius_Ioc_sum...`.
  --
  -- We recover `avg ≤ Cφ * card(s)` by repeating the last step of the proof in that lemma.
  have havg_le :
      (⨍ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
        ≤ LogSingularity.Cφ * (s.card : ℝ) := by
    -- Apply the existing lemma with the same `R`, which provides *some* witness `r1`;
    -- the average bound itself is independent of the witness, so we can extract it by rerunning
    -- the proof (it is the `havg_le` subgoal there).
    -- We reuse the proof by calling the lemma and then recomputing via `setAverage_eq` and
    -- the integral comparison (as in `exists_radius_Ioc_sum...`).
    -- Concretely: we can just repeat the final `avg ≤ Cφ*card` proof by `exact`-ing the
    -- corresponding `havg_le` from that lemma's internal proof is not possible here, so we
    -- re-run the argument using the already proved bound `integral_phi_div_le_Cφ_mul`.
    --
    -- (This keeps the lemma self-contained and avoids fragile proof term extraction.)
    have hreal : (volume.real (Set.Ioc R (2 * R)) : ℝ) = R := by
      have : (volume (Set.Ioc R (2 * R)) : ℝ≥0∞) = ENNReal.ofReal R := by
        simp [Real.volume_Ioc, sub_eq_add_neg, two_mul]
      simp [Measure.real, this, hR]
    have hintegral :
        (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
          ≤ LogSingularity.Cφ * R * (s.card : ℝ) := by
      have hInt_eq :
          (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
            = ∫ x in R..(2 * R), g x ∂(volume : MeasureTheory.Measure ℝ) := by
        simpa using (intervalIntegral.integral_of_le (μ := (volume : MeasureTheory.Measure ℝ)) (f := g) hab).symm
      have hsum_int :
          (∫ x in R..(2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
            = ∑ n ∈ s, ∫ x in R..(2 * R), LogSingularity.φ (x / ‖hz.zeros n‖)
                ∂(volume : MeasureTheory.Measure ℝ) := by
        simpa [g] using
          (intervalIntegral.integral_finset_sum (μ := (volume : MeasureTheory.Measure ℝ))
            (a := R) (b := (2 * R)) (s := s)
            (f := fun n : ℕ => fun r : ℝ => LogSingularity.φ (r / ‖hz.zeros n‖)) hterm_int)
      have hle_each :
          ∀ n ∈ s, (∫ x in R..(2 * R), LogSingularity.φ (x / ‖hz.zeros n‖)
              ∂(volume : MeasureTheory.Measure ℝ))
            ≤ LogSingularity.Cφ * R := by
        intro n hn
        have hn' : hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 4 * R := by
          simpa [s] using (Finset.mem_coe.1 hn)
        have ha : 0 < ‖hz.zeros n‖ := norm_pos_iff.2 hn'.1
        simpa using (LogSingularity.integral_phi_div_le_Cφ_mul (a := ‖hz.zeros n‖) (R := R) ha hR)
      have hsum_le :
          (∑ n ∈ s, ∫ x in R..(2 * R), LogSingularity.φ (x / ‖hz.zeros n‖) ∂(volume : MeasureTheory.Measure ℝ))
            ≤ ∑ n ∈ s, (LogSingularity.Cφ * R) := by
        refine Finset.sum_le_sum ?_
        intro n hn
        exact hle_each n hn
      have hsum_const : (∑ n ∈ s, (LogSingularity.Cφ * R)) = (s.card : ℝ) * (LogSingularity.Cφ * R) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      have : (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
              ≤ (s.card : ℝ) * (LogSingularity.Cφ * R) := by
        calc
          (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
              = ∫ x in R..(2 * R), g x ∂(volume : MeasureTheory.Measure ℝ) := hInt_eq
          _ = ∑ n ∈ s, ∫ x in R..(2 * R), LogSingularity.φ (x / ‖hz.zeros n‖) ∂(volume : MeasureTheory.Measure ℝ) := by
                simpa [hsum_int]
          _ ≤ ∑ n ∈ s, (LogSingularity.Cφ * R) := hsum_le
          _ = (s.card : ℝ) * (LogSingularity.Cφ * R) := by simpa [hsum_const]
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
    have havg_eq :
        (⨍ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
          = (R : ℝ)⁻¹ * (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ)) := by
      simp [MeasureTheory.setAverage_eq, hreal, smul_eq_mul]
    calc
      (⨍ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ))
          = R⁻¹ * (∫ x in Set.Ioc R (2 * R), g x ∂(volume : MeasureTheory.Measure ℝ)) := havg_eq
      _ ≤ R⁻¹ * (LogSingularity.Cφ * R * (s.card : ℝ)) := by gcongr
      _ = LogSingularity.Cφ * (s.card : ℝ) := by
            field_simp [hRne]

  refine ⟨r, hr_mem, ?_, ?_⟩
  · -- `r ∉ bad`
    intro hn
    exact hr_not_bad hn
  · -- bound on the finite sum, using `g r ≤ avg ≤ Cφ*card`
    have : g r ≤ LogSingularity.Cφ * (s.card : ℝ) := hr_le_avg.trans havg_le
    simpa [g] using this

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
