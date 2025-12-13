import Riemann.Mathlib.Analysis.Harmonic.BMO.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Doubling
import Riemann.Mathlib.Analysis.Harmonic.BMOAux

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α] {μ : Measure α}

variable [ProperSpace α]
variable [IsFiniteMeasureOnCompacts μ]

/-!
### Weak-type bounds from the BMO `L¹`-control

These lemmas are **not** the John–Nirenberg inequality (they only give polynomial / weak-
`L¹` decay), but they are useful auxiliary estimates and sanity checks.
-/

omit [BorelSpace α] in
/-- A basic Chebyshev/Markov estimate: if the mean oscillation on `B(x₀,r)` is bounded by `M`,
then the set where `|f - f_B| > 2·λ` has relative measure at most `1/2` (assuming `M ≤ λ`).

This is the standard weak-type consequence of the BMO `L¹` bound, and **does not** imply
John–Nirenberg exponential decay by itself. -/
theorem bmo_chebyshev_decay {f : α → ℝ} (hf_loc : LocallyIntegrable f μ) {M : ℝ} (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    {x₀ : α} {r : ℝ} (hr : 0 < r) {lambda : ℝ} (hlambda : M ≤ lambda) :
    μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > 2 * lambda} ≤
      (1 / 2) * μ (Metric.ball x₀ r) := by
  classical
  set B : Set α := Metric.ball x₀ r
  set fB : ℝ := ⨍ y in B, f y ∂μ
  set g : α → ℝ := fun x => |f x - fB|
  have hlambda_pos : 0 < lambda := lt_of_lt_of_le hM hlambda
  have hεpos : 0 < (2 * lambda) := by linarith [hlambda_pos]
  have hμB_ne_top : μ B ≠ ⊤ := (measure_ball_lt_top (μ := μ) (x := x₀) (r := r)).ne
  -- Integrability on the ball.
  have hfB_int : IntegrableOn f B μ := by
    have hcb : IntegrableOn f (Metric.closedBall x₀ r) μ :=
      hf_loc.integrableOn_isCompact (isCompact_closedBall x₀ r)
    exact hcb.mono_set Metric.ball_subset_closedBall
  have hg_int : IntegrableOn g B μ := by
    have hconst : IntegrableOn (fun _ : α => fB) B μ :=
      integrableOn_const (μ := μ) (s := B) (C := fB) (hs := hμB_ne_top) (hC := by simp)
    have hsub : IntegrableOn (fun x => f x - fB) B μ := hfB_int.sub hconst
    simpa [g, ← Real.norm_eq_abs] using hsub.norm
  -- Convert the BMO bound on the average to an integral bound.
  have hIntegral_le : ∫ x in B, g x ∂μ ≤ μ.real B * M := by
    have hsmul : μ.real B • (⨍ x in B, g x ∂μ) = ∫ x in B, g x ∂μ :=
      measure_smul_setAverage (μ := μ) (f := g) (s := B) hμB_ne_top
    have havg_le : (⨍ x in B, g x ∂μ) ≤ M := by
      simpa [B, fB, g] using (hmo x₀ r hr)
    have hmul :
        μ.real B * (⨍ x in B, g x ∂μ) ≤ μ.real B * M := by
      exact mul_le_mul_of_nonneg_left havg_le ENNReal.toReal_nonneg
    have hsmul' : μ.real B * (⨍ x in B, g x ∂μ) = ∫ x in B, g x ∂μ := by
      simpa [smul_eq_mul] using hsmul
    simpa [hsmul', mul_assoc, mul_left_comm, mul_comm] using hmul
  -- Markov inequality on `μ.restrict B`.
  have hg_int' : Integrable g (μ.restrict B) := by
    simpa [IntegrableOn] using hg_int
  have hg_nonneg : 0 ≤ᵐ[μ.restrict B] g :=
    Eventually.of_forall (fun _ => abs_nonneg _)
  have hmarkov_raw :
      (2 * lambda) * ((μ.restrict B) {x | (2 * lambda) ≤ g x}).toReal ≤ ∫ x in B, g x ∂μ := by
    have h' :
        (2 * lambda) * (μ.restrict B).real {x | (2 * lambda) ≤ g x} ≤ ∫ x, g x ∂(μ.restrict B) :=
      mul_meas_ge_le_integral_of_nonneg (μ := μ.restrict B) hg_nonneg hg_int' (2 * lambda)
    simpa [Measure.real, measureReal_def, B, g] using h'
  have hmarkov :
      (2 * lambda) * (μ {x ∈ B | (2 * lambda) ≤ g x}).toReal ≤ ∫ x in B, g x ∂μ := by
    have hmeas :
        (μ.restrict B) {x | (2 * lambda) ≤ g x} = μ {x ∈ B | (2 * lambda) ≤ g x} := by
      -- Use `Measure.restrict_apply₀` (works for `NullMeasurableSet`).
      have ht : NullMeasurableSet {x | (2 * lambda) ≤ g x} (μ.restrict B) := by
        have hga : AEMeasurable g (μ.restrict B) := hg_int'.aemeasurable
        -- `{x | 2*lambda ≤ g x}` is the preimage of `Ici (2*lambda)`.
        simpa [Set.preimage, Set.mem_setOf_eq] using
          (hga.nullMeasurableSet_preimage
            (isClosed_Ici.measurableSet : MeasurableSet (Set.Ici (2 * lambda))))
      -- Now unfold the restricted measure application.
      have hrestrict :
          (μ.restrict B) {x | (2 * lambda) ≤ g x} = μ ({x | (2 * lambda) ≤ g x} ∩ B) :=
        Measure.restrict_apply₀ (μ := μ) (s := B) (t := {x | (2 * lambda) ≤ g x}) ht
      -- And rewrite the intersection as a set-builder.
      simpa [Set.inter_comm, Set.setOf_and, and_left_comm, and_assoc, and_comm] using hrestrict
    simpa [hmeas] using hmarkov_raw
  have htoReal_ge :
      (μ {x ∈ B | (2 * lambda) ≤ g x}).toReal ≤ (μ.real B * M) / (2 * lambda) := by
    have hdiv :
        (μ {x ∈ B | (2 * lambda) ≤ g x}).toReal ≤ (∫ x in B, g x ∂μ) / (2 * lambda) :=
      (le_div_iff₀ hεpos).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov)
    have hdiv2 :
        (∫ x in B, g x ∂μ) / (2 * lambda) ≤ (μ.real B * M) / (2 * lambda) := by
      exact div_le_div_of_nonneg_right hIntegral_le (by linarith [hlambda_pos])
    exact hdiv.trans hdiv2
  have hmono :
      μ {x ∈ B | g x > 2 * lambda} ≤ μ {x ∈ B | (2 * lambda) ≤ g x} := by
    refine measure_mono (fun x hx => ?_)
    exact ⟨hx.1, hx.2.le⟩
  have hμge_ne_top : μ {x ∈ B | (2 * lambda) ≤ g x} ≠ ⊤ :=
    measure_ne_top_of_subset (fun _ hx => hx.1) hμB_ne_top
  have htoReal_bad :
      (μ {x ∈ B | g x > 2 * lambda}).toReal ≤ (μ.real B * M) / (2 * lambda) := by
    exact (ENNReal.toReal_mono hμge_ne_top hmono).trans htoReal_ge
  have hcoeff : (μ.real B * M) / (2 * lambda) ≤ (1 / 2 : ℝ) * (μ B).toReal := by
    have h2lambda_pos : 0 < 2 * lambda := by linarith [hlambda_pos]
    apply (div_le_iff₀ h2lambda_pos).2
    have hμreal_eq : μ.real B = (μ B).toReal := by simp [Measure.real]
    have : (μ B).toReal * M ≤ (μ B).toReal * lambda :=
      mul_le_mul_of_nonneg_left hlambda ENNReal.toReal_nonneg
    simpa [hμreal_eq, mul_assoc, mul_left_comm, mul_comm] using this
  have htoReal_final :
      (μ {x ∈ B | g x > 2 * lambda}).toReal ≤ ((1 / 2 : ℝ≥0∞) * μ B).toReal := by
    calc
      (μ {x ∈ B | g x > 2 * lambda}).toReal
          ≤ (μ.real B * M) / (2 * lambda) := htoReal_bad
      _ ≤ (1 / 2 : ℝ) * (μ B).toReal := hcoeff
      _ = ((1 / 2 : ℝ≥0∞) * μ B).toReal := by
            simp [ENNReal.toReal_mul]
  have hμbad_ne_top : μ {x ∈ B | g x > 2 * lambda} ≠ ⊤ :=
    measure_ne_top_of_subset (fun _ hx => hx.1) hμB_ne_top
  have hμrhs_ne_top : ((1 / 2 : ℝ≥0∞) * μ B) ≠ ⊤ := by finiteness
  have hmain :
      μ {x ∈ B | g x > 2 * lambda} ≤ (1 / 2 : ℝ≥0∞) * μ B :=
    (ENNReal.toReal_le_toReal hμbad_ne_top hμrhs_ne_top).1 htoReal_final
  simpa [B, g, fB] using hmain

omit [BorelSpace α] in
/-- A weak geometric decay statement obtained by applying Chebyshev at dyadic thresholds.

This is still only a **weak-type** estimate: the threshold is `2^k·M`, so this translates to
polynomial decay in the parameter `t`. -/
theorem bmo_geometric_decay_pow_two {f : α → ℝ} (hf_loc : LocallyIntegrable f μ) {M : ℝ}
    (hM : 0 < M)
    (hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    {x₀ : α} {r : ℝ} (hr : 0 < r) (k : ℕ) :
    μ {x ∈ Metric.ball x₀ r |
        |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > (2 : ℝ) ^ k * M} ≤
      (1 / 2) ^ k * μ (Metric.ball x₀ r) := by
  classical
  set B : Set α := Metric.ball x₀ r
  set fB : ℝ := ⨍ y in B, f y ∂μ
  set g : α → ℝ := fun x => |f x - fB|
  have hμB_ne_top : μ B ≠ ⊤ := (measure_ball_lt_top (μ := μ) (x := x₀) (r := r)).ne
  -- Integrability on the ball.
  have hfB_int : IntegrableOn f B μ := by
    have hcb : IntegrableOn f (Metric.closedBall x₀ r) μ :=
      hf_loc.integrableOn_isCompact (isCompact_closedBall x₀ r)
    exact hcb.mono_set Metric.ball_subset_closedBall
  have hg_int : IntegrableOn g B μ := by
    have hconst : IntegrableOn (fun _ : α => fB) B μ :=
      integrableOn_const (μ := μ) (s := B) (C := fB) (hs := hμB_ne_top) (hC := by simp)
    have hsub : IntegrableOn (fun x => f x - fB) B μ := hfB_int.sub hconst
    simpa [g, ← Real.norm_eq_abs] using hsub.norm
  have hg_int' : Integrable g (μ.restrict B) := by
    simpa [IntegrableOn] using hg_int
  have hg_nonneg : 0 ≤ᵐ[μ.restrict B] g :=
    Eventually.of_forall (fun _ => abs_nonneg _)
  have hg_ae : AEMeasurable g (μ.restrict B) := hg_int'.aemeasurable
  -- Convert the BMO bound on the average to an integral bound.
  have hIntegral_le : ∫ x in B, g x ∂μ ≤ μ.real B * M := by
    have hsmul : μ.real B • (⨍ x in B, g x ∂μ) = ∫ x in B, g x ∂μ :=
      measure_smul_setAverage (μ := μ) (f := g) (s := B) hμB_ne_top
    have havg_le : (⨍ x in B, g x ∂μ) ≤ M := by
      simpa [B, fB, g] using (hmo x₀ r hr)
    have hmul : μ.real B * (⨍ x in B, g x ∂μ) ≤ μ.real B * M :=
      mul_le_mul_of_nonneg_left havg_le ENNReal.toReal_nonneg
    have hsmul' : μ.real B * (⨍ x in B, g x ∂μ) = ∫ x in B, g x ∂μ := by
      simpa [smul_eq_mul] using hsmul
    simpa [hsmul'] using hmul
  -- Work with the restricted measure.
  set t : ℝ := (2 : ℝ) ^ k * M
  have ht_pos : 0 < t := by
    have hpow : 0 < (2 : ℝ) ^ k := by positivity
    exact mul_pos hpow hM
  -- Markov inequality for the ENNReal-valued function `ENNReal.ofReal ∘ g` on `μ.restrict B`.
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (g x)) (μ.restrict B) :=
    hg_ae.ennreal_ofReal
  have hε0 : (ENNReal.ofReal t) ≠ 0 := by
    have : ¬t ≤ 0 := not_le_of_gt ht_pos
    simpa [ENNReal.ofReal_eq_zero] using this
  have hεtop : (ENNReal.ofReal t) ≠ ∞ := ENNReal.ofReal_ne_top
  have hlintegral_le :
      ∫⁻ x, ENNReal.ofReal (g x) ∂(μ.restrict B) ≤ ENNReal.ofReal (μ.real B * M) := by
    have h' : ∫ x, g x ∂(μ.restrict B) ≤ μ.real B * M := by
      simpa [IntegrableOn] using hIntegral_le
    have h_ofReal' : ENNReal.ofReal (∫ x, g x ∂(μ.restrict B)) ≤ ENNReal.ofReal (μ.real B * M) :=
      ENNReal.ofReal_le_ofReal h'
    -- Rewrite the LHS using `ofReal_integral_eq_lintegral_ofReal`.
    have h_eq :
        ENNReal.ofReal (∫ x, g x ∂(μ.restrict B)) =
          ∫⁻ x, ENNReal.ofReal (g x) ∂(μ.restrict B) := by
      simpa using (ofReal_integral_eq_lintegral_ofReal (μ := μ.restrict B) (f := g) hg_int'
        hg_nonneg)
    simpa [h_eq] using h_ofReal'
  have hmarkov_le :
      (μ.restrict B) {x | t ≤ g x} ≤
        (ENNReal.ofReal (μ.real B * M)) / (ENNReal.ofReal t) := by
    have hmarkov0 :
        (μ.restrict B) {x | ENNReal.ofReal t ≤ ENNReal.ofReal (g x)} ≤
          (∫⁻ x, ENNReal.ofReal (g x) ∂(μ.restrict B)) / (ENNReal.ofReal t) :=
      meas_ge_le_lintegral_div (μ := μ.restrict B) hmeas hε0 hεtop
    have hset :
        {x | ENNReal.ofReal t ≤ ENNReal.ofReal (g x)} = {x | t ≤ g x} := by
      ext x
      have hgx : 0 ≤ g x := abs_nonneg _
      simpa [Set.mem_setOf_eq] using (ENNReal.ofReal_le_ofReal_iff hgx : _)
    have hmarkov1 :
        (μ.restrict B) {x | t ≤ g x} ≤
          (∫⁻ x, ENNReal.ofReal (g x) ∂(μ.restrict B)) / (ENNReal.ofReal t) := by
      simpa [hset] using hmarkov0
    exact hmarkov1.trans (ENNReal.div_le_div_right hlintegral_le _)
  -- Convert the restricted-measure statement to the desired set in `μ`.
  have hnull_gt : NullMeasurableSet {x | t < g x} (μ.restrict B) := by
    have : NullMeasurableSet (g ⁻¹' Set.Ioi t) (μ.restrict B) :=
      hg_ae.nullMeasurableSet_preimage (isOpen_Ioi.measurableSet : MeasurableSet (Set.Ioi t))
    simpa [Set.preimage, Set.mem_setOf_eq] using this
  have hrestrict_gt :
      (μ.restrict B) {x | t < g x} = μ {x ∈ B | t < g x} := by
    have h' :
        (μ.restrict B) {x | t < g x} = μ ({x | t < g x} ∩ B) :=
      Measure.restrict_apply₀ (μ := μ) (s := B) (t := {x | t < g x}) hnull_gt
    simpa [Set.inter_comm, Set.setOf_and, and_left_comm, and_assoc, and_comm] using h'
  have hle_restrict :
      (μ.restrict B) {x | t < g x} ≤ (μ.restrict B) {x | t ≤ g x} :=
    measure_mono (by
      intro x hx
      have hx' : t < g x := by simpa [Set.mem_setOf_eq] using hx
      exact hx'.le)
  have hbound :
      μ {x ∈ B | t < g x} ≤ (ENNReal.ofReal (μ.real B * M)) / (ENNReal.ofReal t) := by
    simpa [hrestrict_gt] using (hle_restrict.trans hmarkov_le)
  -- Simplify the RHS at the dyadic threshold `t = 2^k * M`.
  have hM0 : (ENNReal.ofReal M) ≠ 0 := by
    have : ¬M ≤ 0 := not_le_of_gt hM
    simpa [ENNReal.ofReal_eq_zero] using this
  have hMtop : (ENNReal.ofReal M) ≠ ∞ := ENNReal.ofReal_ne_top
  have hμreal : ENNReal.ofReal (μ.real B) = μ B := by
    -- `μ.real B = (μ B).toReal` and `μ B < ⊤`
    simp [Measure.real, hμB_ne_top]
  have h2pow : ENNReal.ofReal ((2 : ℝ) ^ k) = (2 : ℝ≥0∞) ^ k := by
    simp
  have hsimp :
      (ENNReal.ofReal (μ.real B * M)) / (ENNReal.ofReal t) = (1 / 2 : ℝ≥0∞) ^ k * μ B := by
    -- rewrite `t` and cancel `ofReal M`
    have ht' : ENNReal.ofReal t = ENNReal.ofReal ((2 : ℝ) ^ k) * ENNReal.ofReal M := by
      simp [t]
    calc
      (ENNReal.ofReal (μ.real B * M)) / (ENNReal.ofReal t)
          = (ENNReal.ofReal (μ.real B) * ENNReal.ofReal M) /
              (ENNReal.ofReal ((2 : ℝ) ^ k) * ENNReal.ofReal M) := by
              simp [t, ht']
      _ = (ENNReal.ofReal (μ.real B)) / (ENNReal.ofReal ((2 : ℝ) ^ k)) := by
            -- cancel the common factor `ENNReal.ofReal M`
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (ENNReal.mul_div_mul_right (ENNReal.ofReal (μ.real B)) (ENNReal.ofReal ((2 : ℝ) ^ k))
                hM0 hMtop)
      _ = (μ B) / ((2 : ℝ≥0∞) ^ k) := by simp [hμreal, h2pow]
      _ = (1 / 2 : ℝ≥0∞) ^ k * μ B := by
            -- `a / b = b⁻¹ * a` and `((2^k)⁻¹) = (1/2)^k`
            simp [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
  -- Conclude, unfolding definitions.
  have hbound' : μ {x ∈ B | t < g x} ≤ (1 / 2 : ℝ≥0∞) ^ k * μ B := by
    calc
      μ {x ∈ B | t < g x}
          ≤ (ENNReal.ofReal (μ.real B * M)) / (ENNReal.ofReal t) := hbound
      _ = (1 / 2 : ℝ≥0∞) ^ k * μ B := hsimp
  have : μ {x ∈ B | |f x - fB| > t} ≤ (1 / 2 : ℝ≥0∞) ^ k * μ B := by
    simpa [g] using hbound'
  simpa [B, fB, t] using this

end MeasureTheory
