import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.CircleAverageLemmas
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.PosLogLemmas
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.CanonicalRepresentation
import Riemann.Mathlib.Analysis.Complex.HardySpace.PoissonKernel
/-!
# Harnack-type Bounds for Harmonic Functions

This file provides Harnack-type oscillation bounds for harmonic functions on the disc,
which are essential for establishing bounds on `log|f|` for analytic functions.

## Main results

* `HarmonicOnNhd.norm_le_sup_sphere` : Maximum principle for harmonic functions
* `HarmonicOnNhd.oscillation_on_ball` : Oscillation bound for harmonic functions
* `AnalyticOnNhd.log_norm_harmonicOnNhd` : log|f| is harmonic for analytic nonvanishing f
* `AnalyticOnNhd.circleAverage_abs_log_norm_le_sup` : Circle average bound for |log|f||
*

## References

* Conway, J.B., "Functions of One Complex Variable I", Chapter IV
* Rudin, W., "Real and Complex Analysis", Chapter 11
-/

open Complex Set Metric Filter Topology Real MeasureTheory InnerProductSpace
open scoped Real ComplexConjugate

namespace Nevanlinna

variable {f : ℂ → ℂ} {u : ℂ → ℝ} {c : ℂ} {R r : ℝ}

/-! ### Maximum principle for harmonic functions -/

/-- For a harmonic function u on closedBall(0, R), the maximum principle gives:
|u(z)| ≤ sup_{|w|=R} |u(w)| for all z in the closed ball.

This uses the fact that u = Re(F) for some holomorphic F, and applies the
maximum modulus principle to exp(F) and exp(-F). -/
lemma HarmonicOnNhd.norm_le_sup_sphere (hR : 0 < R)
    (hu : HarmonicOnNhd u (closedBall (0 : ℂ) R))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    |u z| ≤ ⨆ w ∈ sphere (0 : ℂ) R, |u w| := by
  classical
  have h_sphere_ne : (sphere (0 : ℂ) R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR.le
  have h_sphere_compact : IsCompact (sphere (0 : ℂ) R) :=
    isCompact_sphere (0 : ℂ) R
  have hu_cont : ContinuousOn u (closedBall (0 : ℂ) R) := by
    intro x hx
    exact (hu x hx).1.continuousAt.continuousWithinAt
  have h_abs_cont :
      ContinuousOn (fun w : ℂ => |u w|) (sphere (0 : ℂ) R) :=
    continuous_abs.comp_continuousOn (hu_cont.mono sphere_subset_closedBall)
  have h_bdd :
      BddAbove ((fun w : ℂ => |u w|) '' sphere (0 : ℂ) R) :=
    h_sphere_compact.bddAbove_image h_abs_cont
  have h_goal :
      |u z| ≤ ⨆ w : sphere (0 : ℂ) R, |u w| := by
    have h_interior :
        z ∉ sphere (0 : ℂ) R →
        |u z| ≤ ⨆ w : sphere (0 : ℂ) R, |u w| := by
      intro hz_sphere
      -- Get the extension to an open set containing the closed ball
      have hR_abs : |R| = R := abs_of_pos hR
      obtain ⟨ε, hε_pos, hε_subset⟩ := (isCompact_closedBall (0 : ℂ) R).exists_thickening_subset_open
        (isOpen_setOf_harmonicAt u) hu
      rw [← hR_abs, thickening_closedBall hε_pos (abs_nonneg R), hR_abs] at hε_subset
      have hu_ball : HarmonicOnNhd u (ball (0 : ℂ) (ε + R)) := fun x hx => hε_subset hx
      -- By harmonic_is_realOfHolomorphic, get F holomorphic with Re F = u
      obtain ⟨F, hF_an, hF_eq⟩ := harmonic_is_realOfHolomorphic hu_ball
      have h_cb_subset : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) (ε + R) := by
        intro w hw
        simp only [mem_closedBall, dist_zero_right] at hw
        simp only [mem_ball, dist_zero_right]
        linarith
      have hF_an_cb : AnalyticOnNhd ℂ F (closedBall (0 : ℂ) R) := fun w hw => hF_an w (h_cb_subset hw)
      have hF_re : ∀ w ∈ closedBall (0 : ℂ) R, (F w).re = u w := fun w hw => hF_eq (h_cb_subset hw)
      -- z is in the interior ball
      have hz_ball : z ∈ ball (0 : ℂ) R := by
        simp only [mem_closedBall, dist_zero_right] at hz
        simp only [mem_sphere, dist_zero_right] at hz_sphere
        simp only [mem_ball, dist_zero_right]
        exact lt_of_le_of_ne hz hz_sphere
      -- The frontier of the ball is the sphere
      have h_frontier : frontier (ball (0 : ℂ) R) = sphere (0 : ℂ) R :=
        frontier_ball (0 : ℂ) (ne_of_gt hR)
      -- exp ∘ F is differentiable on the closed ball (DiffContOnCl)
      have hExpF_diff : DiffContOnCl ℂ (Complex.exp ∘ F) (ball (0 : ℂ) R) := by
        refine ⟨?_, ?_⟩
        · exact Complex.differentiable_exp.comp_differentiableOn
            (hF_an_cb.differentiableOn.mono ball_subset_closedBall)
        · rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
          exact Complex.continuous_exp.comp_continuousOn hF_an_cb.continuousOn
      -- exp(-F) is also differentiable
      have hExpNegF_diff : DiffContOnCl ℂ (fun w => Complex.exp (-F w)) (ball (0 : ℂ) R) := by
        refine ⟨?_, ?_⟩
        · exact Complex.differentiable_exp.comp_differentiableOn
            ((hF_an_cb.neg).differentiableOn.mono ball_subset_closedBall)
        · rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
          exact Complex.continuous_exp.comp_continuousOn (hF_an_cb.neg).continuousOn
      -- The norm |exp(F w)| = exp(Re F w) = exp(u w)
      have hExpF_norm : ∀ w ∈ closedBall (0 : ℂ) R, ‖Complex.exp (F w)‖ = Real.exp (u w) := by
        intro w hw
        rw [Complex.norm_exp, hF_re w hw]
      have hExpNegF_norm : ∀ w ∈ closedBall (0 : ℂ) R, ‖Complex.exp (-F w)‖ = Real.exp (-u w) := by
        intro w hw
        rw [Complex.norm_exp, neg_re, hF_re w hw]
      -- BddAbove for exp(u) on sphere
      have h_bdd_exp : BddAbove ((fun v => ‖Complex.exp (F v)‖) '' sphere (0 : ℂ) R) :=
        (h_sphere_compact.image_of_continuousOn
          (continuous_norm.comp_continuousOn
            (Complex.continuous_exp.comp_continuousOn
              (hF_an_cb.continuousOn.mono sphere_subset_closedBall)))).bddAbove
      have h_bdd_neg_exp : BddAbove ((fun v => ‖Complex.exp (-F v)‖) '' sphere (0 : ℂ) R) :=
        (h_sphere_compact.image_of_continuousOn
          (continuous_norm.comp_continuousOn
            (Complex.continuous_exp.comp_continuousOn
              ((hF_an_cb.neg).continuousOn.mono sphere_subset_closedBall)))).bddAbove
      -- Apply maximum modulus to exp(F)
      have h_exp_le :
          ‖Complex.exp (F z)‖ ≤ sSup ((fun v => ‖Complex.exp (F v)‖) '' sphere (0 : ℂ) R) := by
        apply Complex.norm_le_of_forall_mem_frontier_norm_le
          (f := fun w => Complex.exp (F w))
          (U := ball (0 : ℂ) R) isBounded_ball
        · simpa using hExpF_diff
        · intro w hw
          rw [h_frontier] at hw
          exact le_csSup h_bdd_exp ⟨w, hw, rfl⟩
        · exact subset_closure hz_ball
      -- Apply maximum modulus to exp(-F)
      have h_neg_exp_le :
          ‖Complex.exp (-F z)‖ ≤ sSup ((fun v => ‖Complex.exp (-F v)‖) '' sphere (0 : ℂ) R) := by
        apply Complex.norm_le_of_forall_mem_frontier_norm_le
          (f := fun w => Complex.exp (-F w))
          (U := ball (0 : ℂ) R) isBounded_ball
        · simpa using hExpNegF_diff
        · intro w hw
          rw [h_frontier] at hw
          exact le_csSup h_bdd_neg_exp ⟨w, hw, rfl⟩
        · exact subset_closure hz_ball
      -- Convert to bounds on u
      rw [hExpF_norm z hz] at h_exp_le
      rw [hExpNegF_norm z hz] at h_neg_exp_le
      -- exp(u z) ≤ sup_{sphere} exp(u) and exp(-u z) ≤ sup_{sphere} exp(-u)
      -- Taking logs: u z ≤ sup u and -u z ≤ sup (-u)
      -- Therefore: |u z| ≤ max(sup u, sup(-u)) ≤ sup |u|
      have h_exp_eq : sSup ((fun v => ‖Complex.exp (F v)‖) '' sphere (0 : ℂ) R) =
          sSup ((fun v => Real.exp (u v)) '' sphere (0 : ℂ) R) := by
        congr 1
        ext x
        simp only [mem_image]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨v, hv, (hExpF_norm v (sphere_subset_closedBall hv)).symm⟩
        · rintro ⟨v, hv, rfl⟩
          exact ⟨v, hv, hExpF_norm v (sphere_subset_closedBall hv)⟩
      have h_neg_exp_eq : sSup ((fun v => ‖Complex.exp (-F v)‖) '' sphere (0 : ℂ) R) =
          sSup ((fun v => Real.exp (-u v)) '' sphere (0 : ℂ) R) := by
        congr 1
        ext x
        simp only [mem_image]
        constructor
        · rintro ⟨v, hv, rfl⟩
          exact ⟨v, hv, (hExpNegF_norm v (sphere_subset_closedBall hv)).symm⟩
        · rintro ⟨v, hv, rfl⟩
          exact ⟨v, hv, hExpNegF_norm v (sphere_subset_closedBall hv)⟩
      rw [h_exp_eq] at h_exp_le
      rw [h_neg_exp_eq] at h_neg_exp_le
      -- BddAbove for u and -u on sphere
      have hu_cont_sphere : ContinuousOn u (sphere (0 : ℂ) R) :=
        hu_cont.mono sphere_subset_closedBall
      have h_bdd_u : BddAbove ((fun w => u w) '' sphere (0 : ℂ) R) :=
        (h_sphere_compact.image_of_continuousOn hu_cont_sphere).bddAbove
      have h_bdd_neg_u : BddAbove ((fun w => -u w) '' sphere (0 : ℂ) R) :=
        (h_sphere_compact.image_of_continuousOn (continuous_neg.comp_continuousOn
          hu_cont_sphere)).bddAbove
      have h_bdd_exp_u : BddAbove ((fun w => Real.exp (u w)) '' sphere (0 : ℂ) R) :=
        (h_sphere_compact.image_of_continuousOn (Real.continuous_exp.comp_continuousOn
          hu_cont_sphere)).bddAbove
      have h_bdd_exp_neg_u : BddAbove ((fun w => Real.exp (-u w)) '' sphere (0 : ℂ) R) :=
        (h_sphere_compact.image_of_continuousOn (Real.continuous_exp.comp_continuousOn
          (continuous_neg.comp_continuousOn hu_cont_sphere))).bddAbove
      -- The supremum of exp(u) is achieved at some point
      obtain ⟨w_max, hw_max_mem, hw_max_eq⟩ := h_sphere_compact.exists_isMaxOn h_sphere_ne
        (Real.continuous_exp.comp_continuousOn (hu_cont.mono sphere_subset_closedBall))
      have h_sSup_exp : sSup ((fun w => Real.exp (u w)) '' sphere (0 : ℂ) R) = Real.exp (u w_max) := by
        apply le_antisymm
        · apply csSup_le (h_sphere_ne.image _)
          intro x hx
          obtain ⟨w, hw, rfl⟩ := hx
          exact hw_max_eq hw
        · exact le_csSup h_bdd_exp_u ⟨w_max, hw_max_mem, rfl⟩
      -- Similarly for -u
      obtain ⟨w_min, hw_min_mem, hw_min_eq⟩ := h_sphere_compact.exists_isMaxOn h_sphere_ne
        (Real.continuous_exp.comp_continuousOn (continuous_neg.comp_continuousOn
          (hu_cont.mono sphere_subset_closedBall)))
      have h_sSup_exp_neg :
          sSup ((fun w => Real.exp (-u w)) '' sphere (0 : ℂ) R) = Real.exp (-u w_min) := by
        apply le_antisymm
        · apply csSup_le (h_sphere_ne.image _)
          intro x hx
          obtain ⟨w, hw, rfl⟩ := hx
          exact hw_min_eq hw
        · exact le_csSup h_bdd_exp_neg_u ⟨w_min, hw_min_mem, rfl⟩
      -- From h_exp_le: exp(u z) ≤ exp(u w_max), so u z ≤ u w_max
      rw [h_sSup_exp] at h_exp_le
      have h_u_le : u z ≤ u w_max := Real.exp_le_exp.mp h_exp_le
      -- From h_neg_exp_le: exp(-u z) ≤ exp(-u w_min), so -u z ≤ -u w_min, i.e., u w_min ≤ u z
      rw [h_sSup_exp_neg] at h_neg_exp_le
      have h_neg_u_le : -u z ≤ -u w_min := Real.exp_le_exp.mp h_neg_exp_le
      -- Now: |u z| = max(u z, -u z) ≤ max(u w_max, -u w_min) ≤ sup |u|
      have h_w_max_le : |u w_max| ≤ ⨆ w : sphere (0 : ℂ) R, |u w| := by
        have h_mem : |u w_max| ∈ (fun w => |u w|) '' sphere (0 : ℂ) R := ⟨w_max, hw_max_mem, rfl⟩
        calc |u w_max| ≤ sSup ((fun w => |u w|) '' sphere (0 : ℂ) R) := le_csSup h_bdd h_mem
          _ = ⨆ w : sphere (0 : ℂ) R, |u w| :=
            sSup_image' (s := sphere (0 : ℂ) R) (f := fun w : ℂ => |u w|)
      have h_w_min_le : |u w_min| ≤ ⨆ w : sphere (0 : ℂ) R, |u w| := by
        have h_mem : |u w_min| ∈ (fun w => |u w|) '' sphere (0 : ℂ) R := ⟨w_min, hw_min_mem, rfl⟩
        calc |u w_min| ≤ sSup ((fun w => |u w|) '' sphere (0 : ℂ) R) := le_csSup h_bdd h_mem
          _ = ⨆ w : sphere (0 : ℂ) R, |u w| :=
            sSup_image' (s := sphere (0 : ℂ) R) (f := fun w : ℂ => |u w|)
      calc |u z| = max (u z) (-u z) := rfl --abs_eq_max_neg (u z)
        _ ≤ max (u w_max) (-u w_min) := max_le_max h_u_le h_neg_u_le
        _ ≤ max |u w_max| |u w_min| := by
          apply max_le_max
          · exact le_abs_self _
          · exact neg_le_abs _
        _ ≤ max (⨆ w : sphere (0 : ℂ) R, |u w|) (⨆ w : sphere (0 : ℂ) R, |u w|) :=
            max_le_max h_w_max_le h_w_min_le
        _ = ⨆ w : sphere (0 : ℂ) R, |u w| := max_self _
    -- For z on the sphere, we have |u z| ≤ supremum
    by_cases hz_sphere : z ∈ sphere (0 : ℂ) R
    · have h_mem : |u z| ∈ (fun w => |u w|) '' sphere (0 : ℂ) R := ⟨z, hz_sphere, rfl⟩
      have h_sup_eq :
          sSup ((fun w => |u w|) '' sphere (0 : ℂ) R) =
            ⨆ w : sphere (0 : ℂ) R, |u w| :=
        sSup_image' (s := sphere (0 : ℂ) R) (f := fun w : ℂ => |u w|)
      calc |u z| ≤ sSup ((fun w => |u w|) '' sphere (0 : ℂ) R) := le_csSup h_bdd h_mem
        _ = ⨆ w : sphere (0 : ℂ) R, |u w| := h_sup_eq
    · exact h_interior hz_sphere
  have h_sup_le :
      (⨆ w : sphere (0 : ℂ) R, |u w|) ≤ ⨆ w ∈ sphere (0 : ℂ) R, |u w| := by
    -- The indexing subtype `sphere 0 R` is non-empty.
    haveI : Nonempty (sphere (0 : ℂ) R) := h_sphere_ne.to_subtype
    -- We bound each term of the left supremum by the two-indexed supremum.
    refine ciSup_le ?_
    intro w
    -- every term |u w| is below the two-indexed supremum
    have : |u w| ≤ ⨆ (_ : (w : ℂ) ∈ sphere (0 : ℂ) R), |u w| := by
      simp
    have h_bdd' : BddAbove (range fun w : ℂ => ⨆ (_ : w ∈ sphere (0 : ℂ) R), |u w|) := by
      refine ⟨sSup ((fun w => |u w|) '' sphere (0 : ℂ) R) + 1, ?_⟩
      rintro _ ⟨w, rfl⟩
      by_cases hw : w ∈ sphere (0 : ℂ) R
      · simp only [ciSup_pos hw]
        exact (le_csSup h_bdd ⟨w, hw, rfl⟩).trans (le_add_of_nonneg_right zero_le_one)
      · simp only [ciSup_neg hw, Real.sSup_empty]
        apply add_nonneg
        · obtain ⟨w₀, hw₀⟩ := h_sphere_ne
          exact Real.sSup_nonneg' ⟨|u w₀|, ⟨w₀, hw₀, rfl⟩, abs_nonneg _⟩
        · exact zero_le_one
    exact le_ciSup_of_le h_bdd' (w : ℂ) this
  exact h_goal.trans h_sup_le

/-- The oscillation of a harmonic function on a ball is controlled by the boundary. -/
lemma HarmonicOnNhd.oscillation_on_ball (hR : 0 < R)
    (hu : HarmonicOnNhd u (closedBall (0 : ℂ) R)) :
    ∀ z ∈ closedBall (0 : ℂ) R, ∀ w ∈ closedBall (0 : ℂ) R,
      |u z - u w| ≤ 2 * ⨆ v ∈ sphere (0 : ℂ) R, |u v| := by
  intro z hz w hw
  have h1 : |u z| ≤ ⨆ v ∈ sphere (0 : ℂ) R, |u v| := norm_le_sup_sphere hR hu hz
  have h2 : |u w| ≤ ⨆ v ∈ sphere (0 : ℂ) R, |u v| := norm_le_sup_sphere hR hu hw
  calc |u z - u w| ≤ |u z| + |u w| := by simpa [sub_eq_add_neg, abs_neg] using abs_add_le (u z) (-(u w))
    _ ≤ (⨆ v ∈ sphere (0 : ℂ) R, |u v|) + (⨆ v ∈ sphere (0 : ℂ) R, |u v|) := add_le_add h1 h2
    _ = 2 * ⨆ v ∈ sphere (0 : ℂ) R, |u v| := (two_mul _).symm

/-- For analytic nonvanishing f, the function log|f| is harmonic.
This uses the Mathlib lemma `AnalyticAt.harmonicAt_log_norm`. -/
lemma AnalyticOnNhd.log_norm_harmonicOnNhd (_ : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hf_ne : ∀ z ∈ closedBall (0 : ℂ) R, f z ≠ 0) :
    HarmonicOnNhd (fun z => Real.log ‖f z‖) (closedBall (0 : ℂ) R) := by
  intro z hz
  exact AnalyticAt.harmonicAt_log_norm (hf z hz) (hf_ne z hz)

/-- Circle average bound for |log|f|| when f is analytic and nonvanishing.
Uses the mean value property for harmonic functions and the maximum principle. -/
lemma AnalyticOnNhd.circleAverage_abs_log_norm_le_sup (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hf_ne : ∀ z ∈ closedBall (0 : ℂ) R, f z ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    circleAverage (fun z => |Real.log ‖f z‖|) 0 r ≤
        ⨆ w ∈ sphere (0 : ℂ) R, |Real.log ‖f w‖| := by
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) r ⊆ closedBall (0 : ℂ) R :=
    closedBall_subset_closedBall (le_of_lt hrR)
  -- log|f| is harmonic
  have h_harm : HarmonicOnNhd (fun z => Real.log ‖f z‖) (closedBall (0 : ℂ) R) :=
    log_norm_harmonicOnNhd hR hf hf_ne
  -- |log|f|| is continuous on the closed ball
  have h_cont : ContinuousOn (fun z => |Real.log ‖f z‖|) (closedBall (0 : ℂ) r) := by
    have hf_cont := hf.continuousOn.mono h_subset
    have hf_ne' : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
    have h_log_cont : ContinuousOn (fun z => Real.log ‖f z‖) (closedBall (0 : ℂ) r) :=
      ContinuousOn.log (continuous_norm.comp_continuousOn hf_cont)
        (fun z hz => (norm_pos_iff.mpr (hf_ne' z hz)).ne')
    exact continuous_abs.comp_continuousOn h_log_cont
  -- Circle integrability of |log|f||
  have h_int : CircleIntegrable (fun z => |Real.log ‖f z‖|) 0 r := by
    have h_abs : |r| = r := abs_of_pos hr0
    have h_sphere_eq : sphere (0 : ℂ) |r| = sphere 0 r := by rw [h_abs]
    have h_cont_sphere := h_cont.mono sphere_subset_closedBall
    rw [← h_sphere_eq] at h_cont_sphere
    have h_ci := h_cont_sphere.circleIntegrable
    rw [h_abs] at h_ci
    exact h_ci hr0.le
  -- BddAbove for outer sphere
  have h_bdd_R : BddAbove ((fun w => |Real.log ‖f w‖|) '' sphere (0 : ℂ) R) := by
    have hf_cont_R := hf.continuousOn.mono sphere_subset_closedBall
    have hf_ne_R : ∀ z ∈ sphere (0 : ℂ) R, f z ≠ 0 := fun z hz =>
      hf_ne z (sphere_subset_closedBall hz)
    have h_log_cont_R : ContinuousOn (fun z => Real.log ‖f z‖) (sphere (0 : ℂ) R) :=
      ContinuousOn.log (continuous_norm.comp_continuousOn hf_cont_R)
        (fun z hz => (norm_pos_iff.mpr (hf_ne_R z hz)).ne')
    exact ((isCompact_sphere (0 : ℂ) R).image_of_continuousOn
      (continuous_abs.comp_continuousOn h_log_cont_R)).bddAbove
  -- Maximum principle: |log|f(z)|| ≤ sup on sphere R
  have h_max_principle : ∀ z ∈ closedBall (0 : ℂ) R,
      |Real.log ‖f z‖| ≤ ⨆ w ∈ sphere (0 : ℂ) R, |Real.log ‖f w‖| := by
    intro z hz
    exact HarmonicOnNhd.norm_le_sup_sphere hR h_harm hz
  -- Circle average ≤ supremum on inner circle ≤ sup on outer sphere
  calc circleAverage (fun z => |Real.log ‖f z‖|) 0 r
      ≤ ⨆ w ∈ sphere (0 : ℂ) |r|, |Real.log ‖f w‖| := by
        rw [hr_abs]
        apply Real.circleAverage_mono_on_of_le_circle h_int
        intro x hx
        rw [hr_abs] at hx
        -- x ∈ sphere 0 r, so |...(x)| ≤ sup over sphere 0 r
        have h_bdd_r : BddAbove ((fun w => |Real.log ‖f w‖|) '' sphere (0 : ℂ) r) :=
          ((isCompact_sphere (0 : ℂ) r).image_of_continuousOn
            (h_cont.mono sphere_subset_closedBall)).bddAbove
        have h_mem : |Real.log ‖f x‖| ∈ (fun w => |Real.log ‖f w‖|) '' sphere (0 : ℂ) r :=
          ⟨x, hx, rfl⟩
        have h1 : |Real.log ‖f x‖| ≤ sSup ((fun w => |Real.log ‖f w‖|) '' sphere (0 : ℂ) r) :=
          le_csSup h_bdd_r h_mem
        have h2 : sSup ((fun w => |Real.log ‖f w‖|) '' sphere (0 : ℂ) r) ≤
            ⨆ w ∈ sphere (0 : ℂ) r, |Real.log ‖f w‖| := by
          rw [sSup_image']
          haveI : Nonempty (sphere (0 : ℂ) r) := (NormedSpace.sphere_nonempty.mpr hr0.le).to_subtype
          have h_bdd' : BddAbove (range fun w : ℂ => ⨆ (_ : w ∈ sphere (0 : ℂ) r), |Real.log ‖f w‖|) := by
            refine ⟨sSup ((fun w => |Real.log ‖f w‖|) '' sphere (0 : ℂ) r) + 1, ?_⟩
            rintro _ ⟨w, rfl⟩
            by_cases hw : w ∈ sphere (0 : ℂ) r
            · simp only [ciSup_pos hw]
              exact (le_csSup h_bdd_r ⟨w, hw, rfl⟩).trans (le_add_of_nonneg_right zero_le_one)
            · simp only [ciSup_neg hw, Real.sSup_empty]
              apply add_nonneg
              · have h_sphere_ne : (sphere (0 : ℂ) r).Nonempty := NormedSpace.sphere_nonempty.mpr hr0.le
                obtain ⟨v₀, hv₀⟩ := h_sphere_ne
                exact Real.sSup_nonneg' ⟨|Real.log ‖f v₀‖|, ⟨v₀, hv₀, rfl⟩, abs_nonneg _⟩
              · exact zero_le_one
          refine ciSup_le (fun ⟨w, hw⟩ => ?_)
          have : |Real.log ‖f w‖| ≤ ⨆ (_ : w ∈ sphere (0 : ℂ) r), |Real.log ‖f w‖| := by simp_all
          exact le_ciSup_of_le h_bdd' w this
        exact h1.trans h2
    _ ≤ ⨆ w ∈ sphere (0 : ℂ) R, |Real.log ‖f w‖| := by
      apply ciSup_le
      intro w
      by_cases hw : w ∈ sphere (0 : ℂ) |r|
      · rw [hr_abs] at hw
        have hw_cb : w ∈ closedBall (0 : ℂ) R := h_subset (sphere_subset_closedBall hw)
        calc ⨆ (_ : w ∈ sphere 0 |r|), |Real.log ‖f w‖|
            = |Real.log ‖f w‖| := ciSup_pos (by rwa [hr_abs])
          _ ≤ ⨆ v ∈ sphere (0 : ℂ) R, |Real.log ‖f v‖| := h_max_principle w hw_cb
      · rw [ciSup_neg hw, Real.sSup_empty]
        have h_sphere_ne : (sphere (0 : ℂ) R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
        obtain ⟨w₀, hw₀⟩ := h_sphere_ne
        exact le_trans (abs_nonneg (Real.log ‖f w₀‖)) (h_max_principle w₀ (sphere_subset_closedBall hw₀))

/-- For analytic nonvanishing f, circleAverage(log⁺|f⁻¹|) ≤ sup on sphere R of |log|f||.
This chains the pointwise bound log⁺|f⁻¹| ≤ |log|f|| with circle average monotonicity. -/
lemma AnalyticOnNhd.circleAverage_posLog_inv_le_sup (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hf_ne : ∀ z ∈ closedBall (0 : ℂ) R, f z ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    circleAverage (fun z => log⁺ ‖(f z)⁻¹‖) 0 r ≤
        ⨆ w ∈ sphere (0 : ℂ) R, |Real.log ‖f w‖| := by
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) r ⊆ closedBall (0 : ℂ) R :=
    closedBall_subset_closedBall (le_of_lt hrR)
  -- Pointwise bound:
  have h_pointwise :
      ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖(f z)⁻¹‖ ≤ |Real.log ‖f z‖| := by
    intro z hz
    rw [hr_abs] at hz
    have hz_cb : z ∈ closedBall (0 : ℂ) R := h_subset (sphere_subset_closedBall hz)
    have hfz_ne : f z ≠ 0 := hf_ne z hz_cb
    rw [norm_inv]
    -- log⁺(x⁻¹) = max(0, -log x) ≤ |log x|
    -- Use: Real.posLog x⁻¹ = max 0 (log x⁻¹) = max 0 (-log x) for x > 0
    simp only [posLog, Real.log_inv]
    exact max_le (abs_nonneg _) (neg_le_abs _)
  -- Circle integrability of log⁺|f⁻¹|
  have h_int1 : CircleIntegrable (fun z => log⁺ ‖(f z)⁻¹‖) 0 r := by
    have hf_cont := hf.continuousOn.mono h_subset
    have hf_ne' : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
    have h_inv_cont : ContinuousOn (fun z => (f z)⁻¹) (closedBall (0 : ℂ) r) :=
      ContinuousOn.inv₀ hf_cont hf_ne'
    have h_g_cont :
        ContinuousOn (fun z => log⁺ ‖(f z)⁻¹‖) (closedBall (0 : ℂ) r) :=
      (continuous_posLog'.comp continuous_norm).comp_continuousOn h_inv_cont
    -- Use the same pattern as before for circleIntegrable
    have h_sphere_eq : sphere (0 : ℂ) |r| = sphere 0 r := by rw [hr_abs]
    have h_cont_sphere := h_g_cont.mono sphere_subset_closedBall
    rw [← h_sphere_eq] at h_cont_sphere
    have h_ci := h_cont_sphere.circleIntegrable
    rw [hr_abs] at h_ci
    exact h_ci hr0.le
  -- Chain the bounds

  -- Integrability of |log|f||
  have h_int2 : CircleIntegrable (fun z => |Real.log ‖f z‖|) 0 r := by
    have hf_cont := hf.continuousOn.mono h_subset
    have hf_ne' : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
    have h_log_cont : ContinuousOn (fun z => Real.log ‖f z‖) (closedBall (0 : ℂ) r) :=
      ContinuousOn.log (continuous_norm.comp_continuousOn hf_cont)
        (fun z hz => (norm_pos_iff.mpr (hf_ne' z hz)).ne')
    have h_abs_cont : ContinuousOn (fun z => |Real.log ‖f z‖|) (closedBall (0 : ℂ) r) :=
      continuous_abs.comp_continuousOn h_log_cont
    have h_sphere_eq : sphere (0 : ℂ) |r| = sphere 0 r := by rw [hr_abs]
    have h_cont_sphere := h_abs_cont.mono sphere_subset_closedBall
    rw [← h_sphere_eq] at h_cont_sphere
    have h_ci := h_cont_sphere.circleIntegrable
    rw [hr_abs] at h_ci
    exact h_ci hr0.le
  -- Final chain
  calc
    circleAverage (fun z => log⁺ ‖(f z)⁻¹‖) 0 r
      ≤ circleAverage (fun z => |Real.log ‖f z‖|) 0 r := by
        apply circleAverage_mono h_int1 h_int2
        intro z hz
        exact h_pointwise z hz
    _ ≤ ⨆ w ∈ sphere (0 : ℂ) R, |Real.log ‖f w‖| :=
        circleAverage_abs_log_norm_le_sup hR hf hf_ne hr0 hrR

/-- **Growth estimate for analytic nonvanishing functions**.

For H analytic and nonvanishing on `closedBall 0 R`, the circle average of `log⁺ ‖H⁻¹‖`
on the inner circle of radius r is bounded by the supremum of `|log ‖H‖|` on the outer
sphere of radius R. This follows from the maximum principle for harmonic functions. -/
lemma circleAverage_posLog_inv_analytic_growth_bound
    {H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hH_an : AnalyticOnNhd ℂ H (Metric.closedBall 0 R))
    (hH_ne : ∀ z ∈ Metric.closedBall 0 R, H z ≠ 0)
    {r : ℝ} (hr0 : 0 < r) (hrR : r < R) :
    circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤
        ⨆ w ∈ Metric.sphere (0 : ℂ) R, |Real.log ‖H w‖| := by
  -- For analytic nonvanishing H, Jensen's formula gives:
  -- circleAverage (log ‖H‖) 0 r = log ‖H 0‖
  have hr_ne : r ≠ 0 := ne_of_gt hr0
  have hr_abs : |r| = r := abs_of_pos hr0

  have hH_an_r : AnalyticOnNhd ℂ H (Metric.closedBall 0 r) :=
    hH_an.mono (Metric.closedBall_subset_closedBall (le_of_lt hrR))
  have hH_ne_r : ∀ z ∈ Metric.closedBall 0 r, H z ≠ 0 :=
    fun z hz => hH_ne z (Metric.closedBall_subset_closedBall (le_of_lt hrR) hz)

  -- Mean value property
  have h_avg : circleAverage (Real.log ‖H ·‖) 0 r = Real.log ‖H 0‖ := by
    apply AnalyticOnNhd.circleAverage_log_norm_of_ne_zero
    · rw [hr_abs]; exact hH_an_r
    · intro u hu; rw [hr_abs] at hu; exact hH_ne_r u hu

  -- Key: log⁺(1/x) ≤ |log x| for x > 0
  have h_poslog_le_abs : ∀ z ∈ Metric.sphere (0 : ℂ) r,
      log⁺ ‖(H z)⁻¹‖ ≤ |Real.log ‖H z‖| := by
    intro z hz
    simp only [Metric.mem_sphere, dist_zero_right] at hz
    have hz_ball : z ∈ Metric.closedBall 0 R :=
      Metric.closedBall_subset_closedBall (le_of_lt hrR) (by simp [hz])
    have hHz_ne : H z ≠ 0 := hH_ne z hz_ball
    have hHz_pos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz_ne
    rw [norm_inv]
    simp only [posLog_def, Real.log_inv]
    exact sup_le (abs_nonneg _) (neg_le_abs _)

  -- The proof strategy:
  -- 1. log⁺ ‖H⁻¹(z)‖ ≤ |log ‖H(z)‖| pointwise (from h_poslog_le_abs)
  -- 2. circleAverage of smaller function ≤ circleAverage of larger function
  -- 3. circleAverage(|log ‖H‖|, r) ≤ sup on sphere R (from HarmonicBounds)

  -- Circle integrability of log⁺ ‖H⁻¹‖
  have h_int_poslog : CircleIntegrable (fun z => log⁺ ‖(H z)⁻¹‖) 0 r := by
    apply circleIntegrable_continuous_on_closedBall hr0
    have h_cont := hH_an_r.continuousOn
    have h_inv_cont : ContinuousOn (fun z => (H z)⁻¹) (Metric.closedBall 0 r) :=
      ContinuousOn.inv₀ h_cont hH_ne_r
    exact ValueDistribution.continuous_posLog.comp_continuousOn
      (continuous_norm.comp_continuousOn h_inv_cont)

  -- Circle integrability of |log ‖H‖|
  have h_int_abs_log : CircleIntegrable (fun z => |Real.log ‖H z‖|) 0 r := by
    apply circleIntegrable_continuous_on_closedBall hr0
    have h_cont := hH_an_r.continuousOn
    have h_norm_pos : ∀ z ∈ Metric.closedBall 0 r, ‖H z‖ ≠ 0 :=
      fun z hz => (norm_pos_iff.mpr (hH_ne_r z hz)).ne'
    have h_log_cont : ContinuousOn (fun z => Real.log ‖H z‖) (Metric.closedBall 0 r) :=
      ContinuousOn.log (continuous_norm.comp_continuousOn h_cont) h_norm_pos
    exact continuous_abs.comp_continuousOn h_log_cont

  -- Step 1: circleAverage(log⁺ ‖H⁻¹‖) ≤ circleAverage(|log ‖H‖|)
  have h_avg_le : circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r ≤
      circleAverage (fun z => |Real.log ‖H z‖|) 0 r := by
    have h_mono : ∀ z ∈ Metric.sphere (0 : ℂ) |r|,
        log⁺ ‖(H z)⁻¹‖ ≤ |Real.log ‖H z‖| := by
      intro z hz
      rw [hr_abs] at hz
      exact h_poslog_le_abs z hz
    apply circleAverage_mono h_int_poslog h_int_abs_log h_mono

  -- Step 2: circleAverage(|log ‖H‖|) ≤ sup on sphere R
  have h_sup_bound : circleAverage (fun z => |Real.log ‖H z‖|) 0 r ≤
      ⨆ w ∈ Metric.sphere (0 : ℂ) R, |Real.log ‖H w‖| :=
    Nevanlinna.AnalyticOnNhd.circleAverage_abs_log_norm_le_sup hR hH_an hH_ne hr0 hrR

  -- Combine the bounds
  calc circleAverage (fun z => log⁺ ‖(H z)⁻¹‖) 0 r
      ≤ circleAverage (fun z => |Real.log ‖H z‖|) 0 r := h_avg_le
    _ ≤ ⨆ w ∈ Metric.sphere (0 : ℂ) R, |Real.log ‖H w‖| := h_sup_bound

end Nevanlinna


namespace InnerProductSpace

open Complex Real MeasureTheory
open scoped Real

/-! ### Schwarz/Poisson representation lemma (disc, center 0)

The proof of `HarmonicOnNhd.poisson_upper_bound` needs the standard identity

`Re(F z) = (2π)⁻¹ ∫₀^{2π} Re(S(z/R, θ)) · Re(F(circleMap 0 R θ)) dθ`

for an analytic `F` on a neighborhood of the closed disc. We package this as a helper lemma so the
rest of the inequality argument is purely order/algebra/integrability bookkeeping.
-/
set_option maxHeartbeats 400000 in
/-- **Schwarz/Poisson representation for the real part** (disc, center `0`).

If `F` is analytic on a neighborhood of `closedBall 0 R`, then for every `z` with `‖z‖ < R`,
`(F z).re` is the `schwarzKernel`-average of the boundary real part `(F (circleMap 0 R θ)).re`.

This is the classical Schwarz integral formula specialized to the real part, and it is the bridge
between Cauchy’s formula for `F` and Poisson kernel estimates for a harmonic function `Re F`. -/
lemma re_eq_schwarzKernel_integral
    {F : ℂ → ℂ} {R : ℝ} (hRpos : 0 < R)
    (hF_an : AnalyticOnNhd ℂ F (ball (0 : ℂ) R))
    (hF_cont : ContinuousOn F (closedBall (0 : ℂ) R))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) :
    (F z).re =
      (2 * π)⁻¹ *
        ∫ θ in (0 : ℝ)..2 * π,
          (Complex.schwarzKernel (z / R) θ).re * (F (circleMap (0 : ℂ) R θ)).re := by
  classical
  -- Reduce to the unit disc by scaling.
  have hz_norm : ‖z‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hRabs : |R| = R := abs_of_pos hRpos
  have hz1 : ‖z / R‖ < 1 := by
    -- `‖z / R‖ = ‖z‖ / |R| < 1`
    -- Use `‖z‖ < R` and `|R| = R`.
    have : ‖z‖ / |R| < 1 := by
      -- `‖z‖ < |R|` since `|R| = R`
      have : ‖z‖ < |R| := by simpa [hRabs] using hz_norm
      exact (div_lt_one (abs_pos.2 hRpos.ne')).2 this
    -- now rewrite `‖z / R‖`
    simpa [norm_div, Complex.norm_real, Real.norm_eq_abs] using this
  set z1 : ℂ := z / R
  have hz1_mem : z1 ∈ ball (0 : ℂ) (1 : ℝ) := by
    simpa [z1, Metric.mem_ball, dist_zero_right] using hz1

  -- Scale the analytic function.
  let F1 : ℂ → ℂ := fun w => F (R * w)
  have hF1_an : AnalyticOnNhd ℂ F1 (ball (0 : ℂ) (1 : ℝ)) := by
    intro w hw
    have hw' : R * w ∈ ball (0 : ℂ) R := by
      -- `‖R*w‖ < R` since `‖w‖ < 1`
      have : ‖w‖ < 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hw
      have : ‖(R : ℂ) * w‖ < R := by
        -- `‖(R:ℂ)*w‖ = |R|*‖w‖ < |R| = R`
        have hRabs_pos : 0 < |R| := abs_pos.2 hRpos.ne'
        have hmul : |R| * ‖w‖ < |R| * (1 : ℝ) :=
          mul_lt_mul_of_pos_left this hRabs_pos
        have : |R| * ‖w‖ < R := by simpa [hRabs, mul_one] using hmul
        simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc] using this
      simpa [Metric.mem_ball, dist_zero_right] using this
    -- compose analyticity with the linear map `w ↦ R*w`
    have h_mul : AnalyticAt ℂ (fun w : ℂ => (R : ℂ) * w) w :=
      (analyticAt_const.mul analyticAt_id)
    simpa [F1] using (hF_an (R * w) hw').comp h_mul

  have hF1_cont : ContinuousOn F1 (closedBall (0 : ℂ) (1 : ℝ)) := by
    -- Use `ContinuousOn.comp` with the linear map `w ↦ R*w`.
    have hmul_cont : ContinuousOn (fun w : ℂ => (R : ℂ) * w) (closedBall (0 : ℂ) (1 : ℝ)) :=
      (continuous_const.mul continuous_id).continuousOn
    have hmul_maps :
        MapsTo (fun w : ℂ => (R : ℂ) * w)
          (closedBall (0 : ℂ) (1 : ℝ)) (closedBall (0 : ℂ) R) := by
      intro w hw
      have hw_le : ‖w‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hw
      have : ‖(R : ℂ) * w‖ ≤ R := by
        -- `‖(R:ℂ)*w‖ = |R|*‖w‖ ≤ |R| = R`
        have : |R| * ‖w‖ ≤ |R| * (1 : ℝ) :=
          mul_le_mul_of_nonneg_left hw_le (abs_nonneg R)
        have : |R| * ‖w‖ ≤ R := by simpa [hRabs, mul_one] using this
        simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using this
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    -- Now compose.
    exact hF_cont.comp hmul_cont hmul_maps

  -- Now prove the unit-disc version for `F1` and `z1`, then translate back.
  have h_unit :
      (F1 z1).re =
        (2 * π)⁻¹ *
          ∫ θ in (0 : ℝ)..2 * π,
            (Complex.schwarzKernel z1 θ).re * (F1 (circleMap (0 : ℂ) (1 : ℝ) θ)).re := by
    -- Core unit-disc proof: reduce to a power-series/Fourier-mode computation on the unit circle.
    --
    -- Notation for the boundary parametrization.
    let ζ : ℝ → ℂ := circleMap (0 : ℂ) (1 : ℝ)
    have hζ_exp : ∀ θ : ℝ, ζ θ = Complex.exp (θ * Complex.I) := by
      intro θ; simp [ζ, circleMap, one_mul]
    have hζ_norm : ∀ θ : ℝ, ‖ζ θ‖ = 1 := by
      intro θ
      simp [ζ, circleMap, Complex.norm_exp_ofReal_mul_I]
    have hζ_ne : ∀ θ : ℝ, ζ θ ≠ 0 := by
      intro θ
      have : ζ θ ∈ sphere (0 : ℂ) (1 : ℝ) := by
        simp [ζ]
      exact ne_of_mem_sphere this (by norm_num)

    -- Boundary real part as a continuous function.
    let u : ℝ → ℝ := fun θ => (F1 (ζ θ)).re
    have hu_cont : Continuous u := by
      have hF1circ : Continuous (fun θ : ℝ => F1 (ζ θ)) := by
        -- `ζ` lands in `closedBall 0 1`, so we can compose `ContinuousOn`.
        have hζ_mem : ∀ θ : ℝ, ζ θ ∈ closedBall (0 : ℂ) (1 : ℝ) := by
          intro θ
          simp [ζ]
        exact hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem
      simpa [u] using (continuous_re.comp hF1circ)
    have hu_int : IntervalIntegrable u volume (0 : ℝ) (2 * π) :=
      hu_cont.intervalIntegrable 0 (2 * π)

    -- Cauchy/mean-value orthogonality: positive Fourier modes integrate to zero.
    have h_pos_mode :
        ∀ n : ℕ, 0 < n →
          ∫ θ in (0 : ℝ)..2 * π, (ζ θ) ^ n * (F1 (ζ θ)) = 0 := by
      intro n hn
      -- Apply the mean value property to `g(w) = w^n * F1 w` at the center `0`.
      let g : ℂ → ℂ := fun w => w ^ n * F1 w
      have hg_cont : ContinuousOn g (closedBall (0 : ℂ) (1 : ℝ)) := by
        have hpow : ContinuousOn (fun w : ℂ => w ^ n) (closedBall (0 : ℂ) (1 : ℝ)) :=
          (continuous_id.pow n).continuousOn
        exact (hpow.mul hF1_cont)
      have hg_diff : ∀ w ∈ ball (0 : ℂ) (1 : ℝ) \ (∅ : Set ℂ), DifferentiableAt ℂ g w := by
        intro w hw
        have hw' : w ∈ ball (0 : ℂ) (1 : ℝ) := hw.1
        have hF1w : DifferentiableAt ℂ F1 w := (hF1_an w hw').differentiableAt
        have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ n) w :=
          (differentiableAt_id.pow n)
        simpa [g] using (hpow.mul hF1w)
      have h_avg : circleAverage g (0 : ℂ) (1 : ℝ) = g 0 := by
        -- mean value for complex-differentiable functions
        simpa using
          (circleAverage_of_differentiable_on_off_countable (f := g) (c := (0 : ℂ)) (R := (1 : ℝ))
            (s := (∅ : Set ℂ)) Set.countable_empty
            (by simpa [abs_one] using hg_cont)
            (by simpa [abs_one] using hg_diff))
      -- Unfold circleAverage and simplify `g(circleMap 0 1 θ)`.
      have hg0 : g 0 = 0 := by
        -- `0^n = 0` for `n>0`
        simp [g, hn.ne']
      -- Convert the circleAverage identity into the desired integral identity.
      -- `circleAverage g 0 1 = (2π)⁻¹ • ∫ θ, g(ζ θ)`
      have h_avg0 : circleAverage g (0 : ℂ) (1 : ℝ) = 0 := by
        simpa [hg0] using h_avg
      have hmul := congrArg (fun x : ℂ => (2 * π : ℝ) • x) h_avg0
      have hne : (2 * π : ℝ) ≠ 0 := (ne_of_gt Real.two_pi_pos)
      -- unfold `circleAverage` and cancel the `(2π)⁻¹`
      -- to obtain the vanishing of the integral.
      have :
          (∫ θ in (0 : ℝ)..2 * π, g (circleMap (0 : ℂ) (1 : ℝ) θ)) = 0 := by
        simpa [Real.circleAverage, smul_smul, inv_mul_cancel₀ hne] using hmul
      -- rewrite `g` and `ζ`
      simpa [g, ζ, circleMap, mul_assoc, mul_left_comm, mul_comm] using this

    -- Expand the Schwarz kernel and interchange sum/integral (dominated convergence).
    -- We will work with the complex Schwarz integral and take real parts at the end.
    have h_schwarz_series :
        ∀ θ : ℝ,
          Complex.schwarzKernel z1 θ
            = 1 + 2 * ∑' n : ℕ, (z1 / (ζ θ)) ^ (n + 1) := by
      intro θ
      -- Use the project lemma with `ζ = exp(θ i)` and rewrite it as `ζ θ`.
      -- `ζ θ = exp(θ i)` since radius is 1.
      simpa [hζ_exp θ, ζ, div_eq_mul_inv, circleMap, one_mul] using
        (Complex.schwarzKernel_series (z := z1) hz1 θ)

    -- Define the complex Schwarz integral with boundary data `u`.
    let G : ℂ := (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ) • Complex.schwarzKernel z1 θ
    have hG_re :
        G.re =
          (2 * π)⁻¹ *
            ∫ θ in (0 : ℝ)..2 * π, (Complex.schwarzKernel z1 θ).re * u θ := by
      -- Move `re` inside; `u θ` is real so it scales real parts.
      have hInt :
          IntervalIntegrable (fun θ : ℝ => (u θ : ℂ) • Complex.schwarzKernel z1 θ) volume
            (0 : ℝ) (2 * π) := by
        -- continuity of the integrand on a compact interval
        have hcontK : Continuous fun θ : ℝ => Complex.schwarzKernel z1 θ := by
          classical
          -- rewrite through `ζ θ = circleMap 0 1 θ` to avoid coercion hassles
          have hζ_cont : Continuous ζ := continuous_circleMap (0 : ℂ) (1 : ℝ)
          have hne : ∀ θ : ℝ, ζ θ - z1 ≠ 0 := by
            intro θ h0
            have hz1' : ‖z1‖ < 1 := hz1
            have h_eq : ζ θ = z1 := sub_eq_zero.mp h0
            have : (1 : ℝ) = ‖z1‖ := by
              -- `‖ζ θ‖ = 1` since `ζ θ` is on the unit circle
              simpa [h_eq] using (hζ_norm θ).symm
            exact (lt_irrefl (1 : ℝ) (this ▸ hz1'))
          -- continuity of `(ζ+z1)/(ζ-z1)`
          have hcont' : Continuous fun θ : ℝ => (ζ θ + z1) / (ζ θ - z1) :=
            (hζ_cont.add continuous_const).div (hζ_cont.sub continuous_const) (by intro θ; exact hne θ)
          -- and this equals `schwarzKernel`
          simpa [Complex.schwarzKernel, hζ_exp] using hcont'
        have hcont : Continuous fun θ : ℝ => (u θ : ℂ) • Complex.schwarzKernel z1 θ :=
          (Complex.continuous_ofReal.comp hu_cont).smul hcontK
        exact hcont.intervalIntegrable 0 (2 * π)
      -- Use the continuous linear map `reCLM` to commute `re` with the interval integral.
      have h_re_int :
          ∫ θ in (0 : ℝ)..2 * π, ((u θ : ℂ) • Complex.schwarzKernel z1 θ).re =
            (∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ) • Complex.schwarzKernel z1 θ).re := by
        -- `reCLM` commutes with interval integrals
        simpa using
          (Complex.reCLM.intervalIntegral_comp_comm
            (f := fun θ : ℝ => (u θ : ℂ) • Complex.schwarzKernel z1 θ) (a := (0 : ℝ)) (b := 2 * π)
            (μ := volume) hInt)
      -- Pointwise simplification.
      have h_point :
          (fun θ : ℝ => ((u θ : ℂ) • Complex.schwarzKernel z1 θ).re) =
            fun θ : ℝ => (Complex.schwarzKernel z1 θ).re * u θ := by
        funext θ
        -- `((uθ:ℂ)•Kθ).re = uθ * Kθ.re = Kθ.re * uθ`
        calc
          ((u θ : ℂ) • Complex.schwarzKernel z1 θ).re = u θ * (Complex.schwarzKernel z1 θ).re := by
            simp [smul_eq_mul]
          _ = (Complex.schwarzKernel z1 θ).re * u θ := by
            simp [mul_comm]
      have h_main :
          (∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ) • Complex.schwarzKernel z1 θ).re =
            ∫ θ in (0 : ℝ)..2 * π, (Complex.schwarzKernel z1 θ).re * u θ := by
        -- Start from `h_re_int` and rewrite the left integrand using `h_point`.
        -- (`simp` prefers `u θ * K.re`, so we finish with `mul_comm`.)
        have h' :
            (∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ) • Complex.schwarzKernel z1 θ).re =
              ∫ θ in (0 : ℝ)..2 * π, u θ * (Complex.schwarzKernel z1 θ).re := by
          simpa [h_point, mul_comm, mul_left_comm, mul_assoc] using h_re_int.symm
        -- commute the real multiplication in the integrand
        refine h'.trans ?_
        refine intervalIntegral.integral_congr ?_
        intro θ hθ
        simp [mul_comm]
      -- account for the outer scalar `(2π)⁻¹`
      -- `re ((a:ℝ) • z) = a * re z` and `a • z = a * z` for `ℂ`.
      calc
        G.re
            = ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
                (u θ : ℂ) • Complex.schwarzKernel z1 θ).re := rfl
        _ = (2 * π : ℝ)⁻¹ * (∫ θ in (0 : ℝ)..2 * π,
                (u θ : ℂ) • Complex.schwarzKernel z1 θ).re := by
              simp [Complex.real_smul, smul_eq_mul, mul_assoc]
        _ = (2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
                (Complex.schwarzKernel z1 θ).re * u θ := by
              simpa [h_main]

    -- Show `G.re = (F1 z1).re` via the Schwarz integral formula:
    -- `G = F1 z1 - I * Im(F1 0)`.
    have hG :
        G = F1 z1 - Complex.I * (F1 0).im := by
      classical
      -- notation
      have hζ_mem : ∀ θ : ℝ, ζ θ ∈ closedBall (0 : ℂ) (1 : ℝ) := by
        intro θ
        simp [ζ]
      have hζ_ne' : ∀ θ : ℝ, ζ θ ≠ 0 := by
        intro θ
        have : ζ θ ∈ sphere (0 : ℂ) (1 : ℝ) := by
          simp [ζ]
        exact ne_of_mem_sphere this (by norm_num)

      -- circle average of `F1` at the center
      have hF1_avg : (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ) = F1 0 := by
        have hF_avg : circleAverage (fun w : ℂ => F1 w) (0 : ℂ) (1 : ℝ) = F1 0 := by
          have hF1_diff : ∀ w ∈ ball (0 : ℂ) (1 : ℝ) \ (∅ : Set ℂ), DifferentiableAt ℂ F1 w := by
            intro w hw
            exact (hF1_an w hw.1).differentiableAt
          have hF1_cont' : ContinuousOn F1 (closedBall (0 : ℂ) |(1 : ℝ)|) := by
            simpa [abs_one] using hF1_cont
          simpa using
            (circleAverage_of_differentiable_on_off_countable (f := F1) (c := (0 : ℂ)) (R := (1 : ℝ))
              (s := (∅ : Set ℂ)) Set.countable_empty hF1_cont' (by
                simpa [abs_one] using hF1_diff))
        simpa [Real.circleAverage, ζ] using hF_avg

      -- Cauchy formula in `θ`-integral form
      have hF1_cauchy :
          (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
              (ζ θ) • ((ζ θ - z1)⁻¹ • F1 (ζ θ)) = F1 z1 := by
        have hz1_ball : z1 ∈ ball (0 : ℂ) (1 : ℝ) := by
          simpa [Metric.mem_ball, dist_zero_right] using hz1
        have hF1_diff : ∀ x ∈ ball (0 : ℂ) (1 : ℝ) \ (∅ : Set ℂ), DifferentiableAt ℂ F1 x := by
          intro x hx
          exact (hF1_an x hx.1).differentiableAt
        have h_cauchy :
            ((2 * π * I : ℂ)⁻¹ • ∮ w in C(0, (1 : ℝ)), (w - z1)⁻¹ • F1 w) = F1 z1 := by
          simpa using
            (Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
              (E := ℂ) (R := (1 : ℝ)) (c := (0 : ℂ)) (w := z1) (f := F1) (s := (∅ : Set ℂ))
              (hs := Set.countable_empty) (hw := hz1_ball)
              (hc := hF1_cont)
              (hd := by simpa using hF1_diff))
        -- Convert the circle integral to a `θ`-integral and cancel the `I` factors.
        have h' :
            -(I *
                (I *
                  ((↑π)⁻¹ *
                    (2⁻¹ *
                      ∫ x : ℝ in 0..π * 2,
                        circleMap (0 : ℂ) (1 : ℝ) x *
                          (F1 (circleMap (0 : ℂ) (1 : ℝ) x) *
                            (circleMap (0 : ℂ) (1 : ℝ) x + -z1)⁻¹))))) =
              F1 z1 := by
          simpa [circleIntegral, ζ, deriv_circleMap, smul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm, sub_eq_add_neg] using h_cauchy
        have h'' :
            (↑π)⁻¹ *
                (2⁻¹ *
                  ∫ x : ℝ in 0..π * 2,
                    circleMap (0 : ℂ) (1 : ℝ) x *
                      (F1 (circleMap (0 : ℂ) (1 : ℝ) x) *
                        (circleMap (0 : ℂ) (1 : ℝ) x + -z1)⁻¹)) =
              F1 z1 := by
          -- cancel the `I` factors: `-(I * (I * A)) = A`
          set A : ℂ :=
              (↑π)⁻¹ *
                (2⁻¹ *
                  ∫ x : ℝ in 0..π * 2,
                    circleMap (0 : ℂ) (1 : ℝ) x *
                      (F1 (circleMap (0 : ℂ) (1 : ℝ) x) *
                        (circleMap (0 : ℂ) (1 : ℝ) x + -z1)⁻¹)) with hA
          have h'_A : -(I * (I * A)) = F1 z1 := by
            simpa [A] using h'
          have hI : -(I * (I * A)) = A := by
            calc
              -(I * (I * A)) = -((I * I) * A) := by
                -- reassociate to expose `I * I`
                simpa using congrArg Neg.neg (mul_assoc I I A).symm
              _ = -((-1 : ℂ) * A) := by simp [Complex.I_mul_I]
              _ = A := by simp
          -- rewrite the LHS using `hI`
          simpa [hA] using (hI.symm.trans h'_A)
        -- Rewrite `circleMap 0 1` as `ζ`, reorder factors, and rewrite `(2*π)⁻¹` as `π⁻¹*2⁻¹`.
        -- Also switch `π*2` to `2*π`.
        simpa [ζ, smul_eq_mul, Complex.real_smul, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg] using h''

      -- Vanishing of the conjugate term by geometric series + `h_pos_mode`.
      have h_conj_int :
          ∫ θ in (0 : ℝ)..2 * π, (star (F1 (ζ θ))) / (ζ θ - z1) = 0 := by
        -- Write the integrand as a uniformly summable series
        let K : TopologicalSpace.Compacts ℝ := ⟨uIcc (0 : ℝ) (2 * π), isCompact_uIcc⟩
        let term : ℕ → C(ℝ, ℂ) := fun n =>
          ⟨fun θ : ℝ => (z1 ^ n) * star ((ζ θ) ^ (n + 1) * F1 (ζ θ)),
            (continuous_const.pow n).mul <|
              continuous_star.comp <|
                ((continuous_circleMap (0 : ℂ) (1 : ℝ)).pow (n + 1)).mul
                  (hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem)⟩
        have hsum :
            Summable fun n : ℕ => ‖(term n).restrict (K : Set ℝ)‖ := by
          -- bound by `‖F1∘ζ‖∞ * ‖z1‖^n`
          have hgeom : Summable fun n : ℕ => ‖z1‖ ^ n :=
            summable_geometric_of_lt_one (norm_nonneg z1) hz1
          refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
            (Summable.mul_left ‖(⟨fun θ : ℝ => F1 (ζ θ),
              (hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem)⟩ : C(ℝ, ℂ)).restrict (K : Set ℝ)‖ hgeom)
          have hn0 :
              (0 : ℝ) ≤
                ‖(⟨fun θ : ℝ => F1 (ζ θ),
                  (hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem)⟩ : C(ℝ, ℂ)).restrict (K : Set ℝ)‖ *
                  ‖z1‖ ^ n :=
            mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
          refine (ContinuousMap.norm_le _ hn0).2 ?_
          intro x
          have hζx : ‖ζ x‖ = 1 := hζ_norm x
          have hF_bd :
              ‖(⟨fun θ : ℝ => F1 (ζ θ),
                (hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem)⟩ : C(ℝ, ℂ)).restrict (K : Set ℝ) x‖
                ≤ ‖(⟨fun θ : ℝ => F1 (ζ θ),
                  (hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem)⟩ : C(ℝ, ℂ)).restrict (K : Set ℝ)‖ :=
            ContinuousMap.norm_coe_le_norm _ x
          calc
            ‖(term n).restrict (K : Set ℝ) x‖
                = ‖z1 ^ n * star ((ζ x) ^ (n + 1) * F1 (ζ x))‖ := by
                    simp [term, K, ContinuousMap.restrict_apply]
            _ ≤ ‖z1 ^ n‖ * ‖star ((ζ x) ^ (n + 1) * F1 (ζ x))‖ := norm_mul_le _ _
            _ = ‖z1‖ ^ n * ‖(ζ x) ^ (n + 1) * F1 (ζ x)‖ := by simp [norm_pow]
            _ ≤ ‖z1‖ ^ n * (‖(ζ x) ^ (n + 1)‖ * ‖F1 (ζ x)‖) := by
                  gcongr
                  exact norm_mul_le _ _
            _ = ‖z1‖ ^ n * ‖F1 (ζ x)‖ := by simp [norm_pow, hζx]
            _ ≤ ‖(⟨fun θ : ℝ => F1 (ζ θ),
                  (hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem)⟩ : C(ℝ, ℂ)).restrict (K : Set ℝ)‖ *
                  ‖z1‖ ^ n := by
                  -- use the sup bound `hF_bd` and commute the product
                  simpa [mul_comm, mul_left_comm, mul_assoc] using
                    (mul_le_mul_of_nonneg_left hF_bd (pow_nonneg (norm_nonneg _) _))
        have hswap :
            ∑' n : ℕ, ∫ θ in (0 : ℝ)..2 * π, term n θ =
              ∫ θ in (0 : ℝ)..2 * π, ∑' n : ℕ, term n θ := by
          simpa using
            (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
              (a := (0 : ℝ)) (b := 2 * π) (f := term) hsum)
        -- pointwise sum equals the original integrand by the geometric series for `1/(ζ - z1)`
        have hpoint :
            (fun θ : ℝ => (star (F1 (ζ θ))) / (ζ θ - z1)) =
              fun θ : ℝ => ∑' n : ℕ, term n θ := by
          funext θ
          -- Abbreviations
          set ζθ : ℂ := ζ θ
          have hζθ_ne : ζθ ≠ 0 := by
            simpa [ζθ] using hζ_ne' θ
          -- On the unit circle: `star ζθ = ζθ⁻¹`
          have hζθ_star : star ζθ = ζθ⁻¹ := by
            -- `ζθ * star ζθ = 1` since `‖ζθ‖ = 1`
            have h_normSq : Complex.normSq ζθ = 1 := by
              have hζθ_norm : ‖ζθ‖ = 1 := by simpa [ζθ] using hζ_norm θ
              calc
                Complex.normSq ζθ = ‖ζθ‖ ^ 2 := Complex.normSq_eq_norm_sq ζθ
                _ = 1 := by simp [hζθ_norm]
            have hmul : ζθ * star ζθ = 1 := by
              simpa [h_normSq] using (Complex.mul_conj ζθ)
            -- multiply on the left by `ζθ⁻¹`
            have := congrArg (fun t : ℂ => ζθ⁻¹ * t) hmul
            simpa [mul_assoc, hζθ_ne] using this
          -- Geometric series for `z1 * star ζθ`
          have hz_mul : ‖z1 * star ζθ‖ < 1 := by
            have hζθ_norm : ‖ζθ‖ = 1 := by
              simpa [ζθ] using hζ_norm θ
            have hz' : ‖z1‖ * ‖ζθ‖ < 1 := by
              simpa [hζθ_norm, mul_one] using hz1
            -- `‖star ζθ‖ = ‖ζθ‖`, so this is exactly `hz'` after rewriting `norm_mul`.
            simpa [norm_mul] using hz'
          have hgeom : (∑' n : ℕ, (z1 * star ζθ) ^ n) = (1 - (z1 * star ζθ))⁻¹ :=
            tsum_geometric_of_norm_lt_one hz_mul
          -- Rewrite the RHS series to match the geometric sum.
          have hterm :
              (fun n : ℕ => term n θ) =
                fun n : ℕ => (star (F1 ζθ)) * (star ζθ) * (z1 * star ζθ) ^ n := by
            funext n
            -- unfold `term` and use `star_mul`, `star_pow`, and commutativity
            -- `star (ζθ^(n+1) * F1 ζθ) = star(F1 ζθ) * (star ζθ)^(n+1)`
            -- and `(z1 * star ζθ)^n = z1^n * (star ζθ)^n`
            simp [term, ζθ, mul_assoc, mul_left_comm, mul_comm, pow_succ, star_mul, star_pow, mul_pow]
          -- Assemble everything
          -- LHS = `star(F1 ζθ) * (ζθ - z1)⁻¹`
          -- RHS = `star(F1 ζθ) * star ζθ * (1 - z1 * star ζθ)⁻¹`
          -- and `ζθ - z1 = ζθ * (1 - z1 * star ζθ)` using `star ζθ = ζθ⁻¹`.
          have hfac : ζθ - z1 = ζθ * (1 - z1 * star ζθ) := by
            -- expand and use `ζθ * star ζθ = 1`
            have hzstar : ζθ * star ζθ = 1 := by
              -- from `hζθ_star`
              simp [hζθ_star, hζθ_ne]
            -- now expand
            -- prove the reversed direction and then symmetrize
            have : ζθ * (1 - z1 * star ζθ) = ζθ - z1 := by
              calc
                ζθ * (1 - z1 * star ζθ) = ζθ - ζθ * (z1 * star ζθ) := by
                  simp [mul_sub]
                _ = ζθ - z1 := by
                  -- `ζθ * (z1 * star ζθ) = z1`
                  have hzmul : ζθ * (z1 * star ζθ) = z1 := by
                    calc
                      ζθ * (z1 * star ζθ) = z1 * (ζθ * star ζθ) := by
                        simp [mul_left_comm]
                      _ = z1 := by
                        calc
                          z1 * (ζθ * star ζθ) = z1 * 1 := by
                            exact congrArg (fun t : ℂ => z1 * t) hzstar
                          _ = z1 := by simp
                  simpa [hzmul]
            simpa using this.symm
          -- finalize using the geometric-series identity `hgeom`
          have hgeom' : (∑' n : ℕ, (z1 * star ζθ) ^ n) = (1 - z1 * star ζθ)⁻¹ := hgeom
          -- rewrite the RHS sum
          have hR :
              (∑' n : ℕ, term n θ) =
                (star (F1 ζθ) * star ζθ) * (1 - z1 * star ζθ)⁻¹ := by
            calc
              (∑' n : ℕ, term n θ) =
                  ∑' n : ℕ, (star (F1 ζθ) * star ζθ) * (z1 * star ζθ) ^ n := by
                    -- use `hterm`
                    refine tsum_congr ?_
                    intro n
                    have hterm_n :
                        term n θ = (star (F1 ζθ)) * (star ζθ) * (z1 * star ζθ) ^ n := by
                      simpa using congrArg (fun f => f n) hterm
                    -- reassociate to match the target form
                    simp [hterm_n, mul_assoc]
              _ = (star (F1 ζθ) * star ζθ) * ∑' n : ℕ, (z1 * star ζθ) ^ n := by
                    -- pull out the constant factor
                    simpa [mul_assoc] using
                      (tsum_mul_left (a := star (F1 ζθ) * star ζθ)
                        (f := fun n : ℕ => (z1 * star ζθ) ^ n))
              _ = (star (F1 ζθ) * star ζθ) * (1 - z1 * star ζθ)⁻¹ := by
                    simpa using
                      congrArg (fun t : ℂ => (star (F1 ζθ) * star ζθ) * t) hgeom'
          -- rewrite the LHS using `hfac` and `hζθ_star`
          have hL :
              (star (F1 ζθ)) / (ζθ - z1) =
                (star (F1 ζθ) * star ζθ) * (1 - z1 * star ζθ)⁻¹ := by
            calc
              (star (F1 ζθ)) / (ζθ - z1)
                  = (star (F1 ζθ)) * (ζθ - z1)⁻¹ := by simp [div_eq_mul_inv]
              _ = (star (F1 ζθ)) * (ζθ * (1 - z1 * star ζθ))⁻¹ := by
                    simp [hfac]
              _ = (star (F1 ζθ)) * ((1 - z1 * star ζθ)⁻¹ * ζθ⁻¹) := by
                    simp [mul_inv_rev, mul_left_comm, mul_comm]
              _ = (star (F1 ζθ) * star ζθ) * (1 - z1 * star ζθ)⁻¹ := by
                    -- replace `ζθ⁻¹` by `star ζθ` and rearrange
                    simp [hζθ_star, mul_assoc, mul_left_comm, mul_comm]
          -- combine
          simpa [ζθ, hL, hR] using (Eq.trans hL hR.symm)
        have h_each : ∀ n : ℕ, ∫ θ in (0 : ℝ)..2 * π, term n θ = 0 := by
          intro n
          have hnpos : 0 < n + 1 := Nat.succ_pos _
          have h0 := h_pos_mode (n + 1) hnpos
          -- Let `g θ = ζ θ^(n+1) * F1 (ζ θ)`.
          let g : ℝ → ℂ := fun θ : ℝ => (ζ θ) ^ (n + 1) * F1 (ζ θ)
          have hg_cont : Continuous g :=
            ((continuous_circleMap (0 : ℂ) (1 : ℝ)).pow (n + 1)).mul
              (hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem)
          have hg_int : IntervalIntegrable g volume (0 : ℝ) (2 * π) :=
            hg_cont.intervalIntegrable 0 (2 * π)
          -- Conjugation (star) commutes with interval integrals.
          have hstar_int :
              ∫ θ in (0 : ℝ)..2 * π, star (g θ) =
                star (∫ θ in (0 : ℝ)..2 * π, g θ) := by
            -- use conjugation as a continuous ℝ-linear map
            simpa using
              (((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap).intervalIntegral_comp_comm
                (μ := volume) (a := (0 : ℝ)) (b := 2 * π) (f := fun θ : ℝ => g θ) hg_int)
          have hstar0 : ∫ θ in (0 : ℝ)..2 * π, star (g θ) = 0 := by
            -- use `h0 : ∫ g = 0`
            have h0' : (∫ θ in (0 : ℝ)..2 * π, g θ) = 0 := by
              simpa [g] using h0
            calc
              ∫ θ in (0 : ℝ)..2 * π, star (g θ)
                  = star (∫ θ in (0 : ℝ)..2 * π, g θ) := hstar_int
              _ = 0 := by simp [h0']
          -- Now finish using linearity of the interval integral.
          calc
            ∫ θ in (0 : ℝ)..2 * π, term n θ
                = ∫ θ in (0 : ℝ)..2 * π, (z1 ^ n) * star (g θ) := by
                    simp [term, g]
            _ = (z1 ^ n) * ∫ θ in (0 : ℝ)..2 * π, star (g θ) := by
                    simp
            _ = 0 := by
                  -- avoid `simp` rewriting `mul_eq_zero` into a disjunction
                  rw [hstar0]
                  simp
        have : ∫ θ in (0 : ℝ)..2 * π, ∑' n : ℕ, term n θ = 0 := by
          rw [← hswap]
          simp [h_each]
        -- `hpoint` is stated with `star`, but goals may display `starRingEnd`; normalize first.
        have hpoint' :
            (fun θ : ℝ => (starRingEnd ℂ) (F1 (ζ θ)) / (ζ θ - z1)) =
              fun θ : ℝ => ∑' n : ℕ, term n θ := by
          funext θ
          have hθ := congrArg (fun f => f θ) hpoint
          -- rewrite `starRingEnd` to `star` explicitly to avoid `simp` recursion
          rw [starRingEnd_apply (R := ℂ) (x := F1 (ζ θ))]
          exact hθ
        simpa [hpoint'] using this

      -- Now compute `G` by expanding `schwarzKernel` and using `hF1_avg`, `hF1_cauchy`, and `h_conj_int`.
      -- This is the classical Schwarz integral formula.
      -- (Details are straightforward algebra; Lean can handle with `simp`/`ring_nf`.)
      -- NOTE: keep it explicit to avoid performance issues.
      -- We unfold `G`, rewrite `u` using `re_eq_add_conj`, and simplify.
      unfold G u
      -- We use `((F1 (ζ θ)).re : ℂ) = (F1 (ζ θ) + star (F1 (ζ θ))) / 2`,
      -- and `schwarzKernel z1 θ = 1 + 2 * z1 / (ζ θ - z1)`.
      have hζ_denom : ∀ θ : ℝ, ζ θ - z1 ≠ 0 := by
        intro θ h0
        have h_eq : ζ θ = z1 := sub_eq_zero.mp h0
        have : (1 : ℝ) = ‖z1‖ := by
          simpa [h_eq] using (hζ_norm θ).symm
        exact (lt_irrefl (1 : ℝ) (this ▸ hz1))

      have hK : ∀ θ : ℝ, Complex.schwarzKernel z1 θ = 1 + 2 * z1 / (ζ θ - z1) := by
        intro θ
        -- unfold the kernel and rewrite `exp(θ i)` as `ζ θ`
        have hK' : Complex.schwarzKernel z1 θ = (ζ θ + z1) / (ζ θ - z1) := by
          -- `schwarzKernel z θ = (exp(θ i) + z)/(exp(θ i) - z)`
          simp [Complex.schwarzKernel, (hζ_exp θ).symm]
        -- rewrite `(ζ+z)/(ζ-z)` as `1 + 2*z/(ζ-z)`
        have hden : ζ θ - z1 ≠ 0 := hζ_denom θ
        -- clear the denominator
        -- (this is a small algebraic identity)
        have : (ζ θ + z1) / (ζ θ - z1) = 1 + 2 * z1 / (ζ θ - z1) := by
          -- multiply both sides by `ζ θ - z1`
          field_simp [hden]
          ring
        simp [hK', this]

      have hu' : ∀ θ : ℝ, (u θ : ℂ) = (F1 (ζ θ) + star (F1 (ζ θ))) / 2 := by
        intro θ
        -- Use `Complex.re_eq_add_conj`, and let simp convert `star` to `conj` (`Complex.star_def`).
        simpa [u] using (Complex.re_eq_add_conj (F1 (ζ θ)))

      -- First, rewrite the integrand using `hu'` and `hK`.
      -- Then expand and use `hF1_avg`, `hF1_cauchy`, and `h_conj_int`.
      --
      -- We proceed by computing the scalar-multiplied integral directly.
      have hIntF1 :
          (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
              z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) = F1 z1 - F1 0 := by
        -- Start from Cauchy, then subtract the average term.
        -- `ζ/(ζ-z1) = 1 + z1/(ζ-z1)`.
        have hsplit :
            (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
                (ζ θ) • ((ζ θ - z1)⁻¹ • F1 (ζ θ))
              =
            (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
                (F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ))) := by
          -- pointwise: `ζ • ((ζ - z1)⁻¹ • F1) = F1 + z1 * ((ζ - z1)⁻¹ • F1)`
          have hpoint :
              EqOn
                (fun θ : ℝ => (ζ θ) • ((ζ θ - z1)⁻¹ • F1 (ζ θ)))
                (fun θ : ℝ => (F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ))))
                (Set.uIcc (0 : ℝ) (2 * π)) := by
            intro θ hθ
            have hden : ζ θ - z1 ≠ 0 := hζ_denom θ
            have hfirst :
                (ζ θ - z1) * ((ζ θ - z1)⁻¹ * F1 (ζ θ)) = F1 (ζ θ) := by
              calc
                (ζ θ - z1) * ((ζ θ - z1)⁻¹ * F1 (ζ θ))
                    = ((ζ θ - z1) * (ζ θ - z1)⁻¹) * F1 (ζ θ) := by
                        simp [mul_assoc]
                _ = F1 (ζ θ) := by simp [hden]
            calc
              (ζ θ) • ((ζ θ - z1)⁻¹ • F1 (ζ θ))
                  = ζ θ * ((ζ θ - z1)⁻¹ * F1 (ζ θ)) := by
                      simp [smul_eq_mul]
              _ = ((ζ θ - z1) + z1) * ((ζ θ - z1)⁻¹ * F1 (ζ θ)) := by ring
              _ = (ζ θ - z1) * ((ζ θ - z1)⁻¹ * F1 (ζ θ)) +
                    z1 * ((ζ θ - z1)⁻¹ * F1 (ζ θ)) := by
                      -- expand before simp rewrites `(ζ - z1) + z1` to `ζ`
                      rw [add_mul]
              _ = F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ * F1 (ζ θ)) := by
                      simp [hfirst]
              _ = F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) := by
                      simp [smul_eq_mul]
          have hcongr :
              ∫ θ in (0 : ℝ)..2 * π, (ζ θ) • ((ζ θ - z1)⁻¹ • F1 (ζ θ)) =
                ∫ θ in (0 : ℝ)..2 * π, (F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ))) := by
            simpa using
              (intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := 2 * π) (by
                simpa [Set.uIcc] using hpoint))
          -- apply congruence to the scalar-multiplied integrals
          simpa [hcongr]
        -- Use `hsplit` to rewrite `hF1_cauchy`
        have hC := hF1_cauchy
        -- rewrite `ζ • ((ζ - z1)⁻¹ • F1)` as a sum
        have hC' :
            (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
                (F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ))) = F1 z1 := by
          exact hsplit.symm.trans hC
        -- split the integral of a sum
        have hsum_int :
            (2 * π : ℝ)⁻¹ •
                ∫ θ in (0 : ℝ)..2 * π, (F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)))
              =
            ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) +
            (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) := by
          -- linearity of the interval integral
          -- provide the integrability hypotheses via continuity on a compact interval
          have hF1circ : Continuous fun θ : ℝ => F1 (ζ θ) :=
            hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem
          have hIntF :
              IntervalIntegrable (fun θ : ℝ => F1 (ζ θ)) volume (0 : ℝ) (2 * π) :=
            hF1circ.intervalIntegrable 0 (2 * π)
          have hIntG :
              IntervalIntegrable (fun θ : ℝ => z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ))) volume (0 : ℝ) (2 * π) := by
            -- continuity of `θ ↦ (ζ θ - z1)⁻¹` and multiplication by `F1 (ζ θ)`
            have hcont_inv : Continuous fun θ : ℝ => (ζ θ - z1)⁻¹ := by
              have hcont_sub : Continuous fun θ : ℝ => ζ θ - z1 :=
                (continuous_circleMap (0 : ℂ) (1 : ℝ)).sub continuous_const
              exact hcont_sub.inv₀ (by intro θ; exact hζ_denom θ)
            have hcont_prod : Continuous fun θ : ℝ => (ζ θ - z1)⁻¹ * F1 (ζ θ) :=
              hcont_inv.mul hF1circ
            have hcont : Continuous fun θ : ℝ => z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) := by
              simpa [smul_eq_mul, mul_assoc] using (continuous_const.mul hcont_prod)
            exact hcont.intervalIntegrable 0 (2 * π)
          -- Now apply additivity and distribute scalar multiplication.
          -- Note: we keep everything in `•` form to avoid normalization issues.
          -- Do the additivity step explicitly to avoid `simp` normalizing scalars to `π⁻¹ * 2⁻¹`.
          have hadd :
              ∫ θ in (0 : ℝ)..2 * π,
                  (F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)))
                =
                (∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) +
                  ∫ θ in (0 : ℝ)..2 * π, z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) := by
            simpa using (intervalIntegral.integral_add (μ := volume) (a := (0 : ℝ)) (b := 2 * π) hIntF hIntG)
          -- now distribute the scalar multiplication
          -- `(c • (A + B)) = c • A + c • B`
          -- and rewrite using `hadd`.
          -- avoid `simp` rewriting `(2*π)⁻¹` into `π⁻¹ * 2⁻¹`
          calc
            (2 * π : ℝ)⁻¹ •
                ∫ θ in (0 : ℝ)..2 * π, (F1 (ζ θ) + z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)))
                =
                (2 * π : ℝ)⁻¹ •
                  ((∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) +
                    ∫ θ in (0 : ℝ)..2 * π, z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ))) := by
                  -- don't let `simp` unfold the real scalar action on `ℂ` here
                  rw [hadd]
            _ =
                ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) +
                  (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) := by
                  -- don't let `simp` rewrite the real scalar action on `ℂ`
                  -- `smul_add` gives the RHS with explicit parentheses; `simp` can match them safely.
                  simp
        -- combine with `hF1_avg`
        -- From `hC'` plus `hsum_int`, isolate the `z1/(ζ-z1)` term.
        have hCsum :
            ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) +
              (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) =
                F1 z1 := by
          -- rewrite the left side of `hC'` using `hsum_int`
          -- avoid `simp` normalizations (it likes to rewrite `(2*π)⁻¹` to `π⁻¹*2⁻¹`)
          have h := hC'
          -- rewrite the LHS of `hC'` using `hsum_int`
          -- (`hsum_int` has exactly the same LHS, so this is a pure rewrite)
          rw [hsum_int] at h
          exact h
        have hCsum' :
            ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ))) +
              (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ) =
                F1 z1 := by
          simpa [add_assoc, add_left_comm, add_comm] using hCsum
        have hz_term :
            (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) =
              F1 z1 - (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ) :=
          eq_sub_of_add_eq hCsum'
        -- finalize using `hF1_avg : (2π)⁻¹•∫ F1(ζθ) = F1 0`
        -- avoid simp rewriting scalars into `π⁻¹ * 2⁻¹`; rewrite the average term directly
        have hz_term' :
            (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, z1 * ((ζ θ - z1)⁻¹ • F1 (ζ θ)) =
              F1 z1 - F1 0 := by
          -- rewrite `(2π)⁻¹ • ∫ F1` using `hF1_avg` without any further simp normalization
          have hz := hz_term
          rw [hF1_avg] at hz
          exact hz
        exact hz_term'

      -- The conjugate term vanishes (use `h_conj_int`).
      have hIntConj :
          (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
              z1 * (star (F1 (ζ θ)) / (ζ θ - z1)) = 0 := by
        -- `h_conj_int : ∫ star(F1(ζθ))/(ζθ - z1) = 0`
        have : ∫ θ in (0 : ℝ)..2 * π, z1 * (star (F1 (ζ θ)) / (ζ θ - z1)) =
            z1 * ∫ θ in (0 : ℝ)..2 * π, (star (F1 (ζ θ)) / (ζ θ - z1)) := by
          -- pull out constant `z1`
          simp [intervalIntegral.integral_const_mul]
        -- now apply `h_conj_int` without triggering `mul_eq_zero` disjunctions
        rw [this]
        rw [h_conj_int]
        simp

      -- Also, the average of the conjugate is the conjugate of the average.
      have hConj_avg :
          (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, star (F1 (ζ θ)) = star (F1 0) := by
        -- commute `star` with the interval integral
        have hF1circ : Continuous fun θ : ℝ => F1 (ζ θ) :=
          hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem
        have hInt : IntervalIntegrable (fun θ : ℝ => F1 (ζ θ)) volume (0 : ℝ) (2 * π) :=
          hF1circ.intervalIntegrable 0 (2 * π)
        have hstar_int :
            ∫ θ in (0 : ℝ)..2 * π, star (F1 (ζ θ)) =
              star (∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) := by
          -- `intervalIntegral_comp_comm` is phrased using `conjCLE`; rewrite it to `conj`,
          -- then use `Complex.star_def : star = conj`.
          have hconj :
              ∫ θ in (0 : ℝ)..2 * π, conj (F1 (ζ θ)) =
                conj (∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) := by
            simpa [RCLike.conjCLE_apply] using
              (((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap).intervalIntegral_comp_comm
                (μ := volume) (a := (0 : ℝ)) (b := 2 * π) (f := fun θ : ℝ => F1 (ζ θ)) hInt)
          -- rewrite `star` to `conj`
          simpa [Complex.star_def] using hconj
        -- scale by `(2π)⁻¹`
        calc
          (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, star (F1 (ζ θ))
              = (2 * π : ℝ)⁻¹ • star (∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) := by
                  -- apply `hstar_int` and then scale
                  simpa using congrArg (fun t : ℂ => (2 * π : ℝ)⁻¹ • t) hstar_int
          _ = star ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)) := by
                  -- `star` commutes with real scalar multiplication
                  simp
          _ = star (F1 0) := by
                  -- push `hF1_avg` through `star`
                  simpa using congrArg star hF1_avg

      -- Now finish the computation of `G`.
      -- Expand `u` and `schwarzKernel`, split integrals, and apply the lemmas above.
      have : (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ) • Complex.schwarzKernel z1 θ =
          F1 z1 - Complex.I * (F1 0).im := by
        -- rewrite the integrand pointwise
        have hpoint :
            (fun θ : ℝ => (u θ : ℂ) • Complex.schwarzKernel z1 θ) =
              fun θ : ℝ =>
                ((F1 (ζ θ) + star (F1 (ζ θ))) / 2) *
                  (1 + 2 * z1 / (ζ θ - z1)) := by
          funext θ
          simp [hu' θ, hK θ, smul_eq_mul, div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm,
            mul_comm]
        -- substitute and expand
        -- `((A+B)/2) * (1 + 2*C) = (A+B)/2 + (A+B)*C`
        -- where `C = z1/(ζ-z1)`.
        -- We keep it structured to avoid simp recursion.
        rw [hpoint]
        -- split as: average term + Cauchy term + conjugate term
        -- use `re_eq_add_conj` at 0 to simplify constants.
        have h_avg_term :
            (2 * π : ℝ)⁻¹ •
                ∫ θ in (0 : ℝ)..2 * π, ((F1 (ζ θ) + star (F1 (ζ θ))) / 2)
              =
            (F1 0).re := by
          -- Rewrite the integrand using `hu'`, then use the real-part mean value formula `hF1_avg`.
          -- Everything is kept in `•` form to avoid normal form issues (`(2*π)⁻¹` vs `π⁻¹*2⁻¹`).
          have hcongr :
              (∫ θ in (0 : ℝ)..2 * π, ((F1 (ζ θ) + star (F1 (ζ θ))) / 2)) =
                ∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ) := by
            refine intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := 2 * π) ?_
            intro θ hθ
            simpa using (hu' θ).symm
          have h_ofReal_int :
              (∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ)) =
                ((∫ θ in (0 : ℝ)..2 * π, u θ) : ℂ) := by
            -- commute `Complex.ofReal` with the interval integral
            simp
          -- Take real parts of the complex mean value formula.
          have hF1circ : Continuous fun θ : ℝ => F1 (ζ θ) :=
            hF1_cont.comp_continuous (continuous_circleMap (0 : ℂ) (1 : ℝ)) hζ_mem
          have hIntF1 : IntervalIntegrable (fun θ : ℝ => F1 (ζ θ)) volume (0 : ℝ) (2 * π) :=
            hF1circ.intervalIntegrable 0 (2 * π)
          have h_re_int :
              (∫ θ in (0 : ℝ)..2 * π, u θ) =
                (∫ θ in (0 : ℝ)..2 * π, F1 (ζ θ)).re := by
            -- commute `re` with the interval integral and unfold `u`
            have h :=
              (Complex.reCLM.intervalIntegral_comp_comm
                (f := fun θ : ℝ => F1 (ζ θ)) (a := (0 : ℝ)) (b := 2 * π) (μ := volume) hIntF1)
            -- `h : ∫ θ, (F1 (ζ θ)).re = (∫ θ, F1 (ζ θ)).re`
            simpa [u] using h
          have hF1_avg_r :
              (2 * π : ℝ)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, u θ) = (F1 0).re := by
            have h := congrArg Complex.re hF1_avg
            -- `re (r • z) = r * re z`
            -- and rewrite `re(∫ F1) = ∫ u` using `h_re_int`
            simpa [Complex.real_smul, smul_eq_mul, h_re_int, mul_assoc] using h
          -- Convert the scalar identity to an equality in `ℂ`, but keep the integral as `∫ ↑u`
          -- (avoids the fragile `↑(∫ u)` vs `∫ ↑u` coercion battle).
          have hcast :
              ((↑((2 * π : ℝ)⁻¹) : ℂ) * ((∫ θ in (0 : ℝ)..2 * π, u θ) : ℂ)) = ((F1 0).re : ℂ) := by
            -- cast `hF1_avg_r : (2π)⁻¹ * ∫ u = (F1 0).re`
            have h := congrArg (fun t : ℝ => (t : ℂ)) hF1_avg_r
            -- turn `↑(r*s)` into `↑r * ↑s` without letting simp rewrite the integral
            -- (we rewrite `((∫ u):ℂ)` into `∫ ↑u` later, explicitly).
            have h' :
                (((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, u θ : ℝ) : ℂ) = ((F1 0).re : ℂ) := by
              simpa using h
            -- Rewrite the LHS *backwards* using `ofReal_mul`.
            -- This avoids simp discovering a lemma rewriting `↑(∫ u)` into `∫ ↑u` too early.
            calc
              (↑((2 * π : ℝ)⁻¹) : ℂ) * ((∫ θ in (0 : ℝ)..2 * π, u θ) : ℂ)
                  = (↑((2 * π : ℝ)⁻¹) : ℂ) * ∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ) := by
                        -- rewrite `↑(∫ u)` into `∫ (u:ℂ)` using the interval-integral lemma
                        simp
              _ = (((2 * π : ℝ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, u θ : ℝ) : ℂ) := by
                        -- rewrite `∫ (u:ℂ)` back to `↑(∫ u)`, then use `Complex.ofReal_mul`
                        have hu_cast :
                            (∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ)) =
                              (↑(∫ θ in (0 : ℝ)..2 * π, u θ) : ℂ) := by
                          simpa using
                            (intervalIntegral.integral_ofReal (a := (0 : ℝ)) (b := 2 * π)
                              (μ := volume) (f := u))
                        -- now it's the plain coercion lemma `↑(r*s) = ↑r * ↑s`
                        -- after rewriting the integral
                        simp [hu_cast]
              _ = ((F1 0).re : ℂ) := h'
          have hcast' :
              ((↑(2 * π : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, (u θ : ℂ)) = ((F1 0).re : ℂ) := by
            -- turn `↑((2π)⁻¹)` into `((↑(2π))⁻¹)` and rewrite `((∫ u):ℂ)` as `∫ (u:ℂ)`
            have h1 := hcast
            -- `↑((2π)⁻¹) = (↑(2π))⁻¹`
            rw [Complex.ofReal_inv] at h1
            -- `((∫ u):ℂ) = ∫ (u:ℂ)`
            -- from `h_ofReal_int : ∫ (u:ℂ) = ((∫ u):ℂ)`
            -- so rewrite the RHS factor
            simpa [mul_assoc] using (congrArg (fun t => (↑(2 * π : ℝ) : ℂ)⁻¹ * t) h_ofReal_int.symm |>.trans h1)
          -- now plug back the actual integrand and take real parts
          have : (2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, ((F1 (ζ θ) + star (F1 (ζ θ))) / 2)
                = ((F1 0).re : ℂ) := by
            rw [hcongr]
            -- rewrite scalar action as multiplication and use `hcast'`
            simpa [smul_eq_mul, mul_assoc] using hcast'
          -- Take real parts: need to handle the coercion carefully
          have hre : ((2 * π : ℝ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, ((F1 (ζ θ) + star (F1 (ζ θ))) / 2)).re = (F1 0).re := by
            rw [this]
            simp only [Complex.ofReal_re]
          exact this

        -- Cauchy / conjugate contributions:
        have h_cauchy_term :
            (2 * π : ℝ)⁻¹ •
                ∫ θ in (0 : ℝ)..2 * π, (F1 (ζ θ) * (z1 / (ζ θ - z1))) =
              F1 z1 - F1 0 := by
          -- `F1 * (z1/(ζ-z1)) = z1 * ((ζ-z1)⁻¹ • F1)` up to commutativity
          -- so this is exactly `hIntF1`.
          simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hIntF1

        have h_conj_term :
            (2 * π : ℝ)⁻¹ •
                ∫ θ in (0 : ℝ)..2 * π, (star (F1 (ζ θ)) * (z1 / (ζ θ - z1))) = 0 := by
          -- reduce to `hIntConj`
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hIntConj

        -- Assemble: average + cauchy + conj
        -- (This is purely algebra now.)
        -- Rewrite the integral of the full expanded expression.
        -- We do it by `simp` with explicit rewrite lemmas to avoid recursion.
        -- NOTE: `simp` will take care of scalar/`•` vs `*` conversions.
        -- TODO: keep this explicit if simp is slow.
        -- This block may need minor massaging depending on simp normal forms.
        have : (2 * π : ℝ)⁻¹ •
                ∫ θ in (0 : ℝ)..2 * π,
                  ((F1 (ζ θ) + star (F1 (ζ θ))) / 2) *
                    (1 + 2 * z1 / (ζ θ - z1))
              =
              (F1 0).re + (F1 z1 - F1 0) := by
          -- Pointwise expansion: ((A+B)/2) * (1 + 2*C) = (A+B)/2 + A*C + B*C
          have hpw : ∀ θ, ((F1 (ζ θ) + star (F1 (ζ θ))) / 2) * (1 + 2 * z1 / (ζ θ - z1))
              = (F1 (ζ θ) + star (F1 (ζ θ))) / 2
                + F1 (ζ θ) * (z1 / (ζ θ - z1))
                + star (F1 (ζ θ)) * (z1 / (ζ θ - z1)) := fun θ => by ring
          -- Rewrite the integrand using hpw
          have hint_eq : ∫ θ in (0 : ℝ)..2 * π, ((F1 (ζ θ) + star (F1 (ζ θ))) / 2) * (1 + 2 * z1 / (ζ θ - z1))
              = ∫ θ in (0 : ℝ)..2 * π, ((F1 (ζ θ) + star (F1 (ζ θ))) / 2
                + F1 (ζ θ) * (z1 / (ζ θ - z1))
                + star (F1 (ζ θ)) * (z1 / (ζ θ - z1))) :=
            intervalIntegral.integral_congr (fun θ _ => hpw θ)
          rw [hint_eq]
          -- Continuity (hence integrability)
          have hF1ζ : Continuous (fun θ => F1 (ζ θ)) :=
            hF1_cont.comp_continuous (continuous_circleMap 0 1) hζ_mem
          have hζz1inv : Continuous (fun θ => (ζ θ - z1)⁻¹) :=
            (continuous_circleMap 0 1).sub continuous_const |>.inv₀ hζ_denom
          have hi1 : IntervalIntegrable (fun θ => (F1 (ζ θ) + star (F1 (ζ θ))) / 2) volume 0 (2 * π) :=
            (hF1ζ.add hF1ζ.star).div_const 2 |>.intervalIntegrable 0 (2 * π)
          have hi2 : IntervalIntegrable (fun θ => F1 (ζ θ) * (z1 / (ζ θ - z1))) volume 0 (2 * π) :=
            (hF1ζ.mul (continuous_const.mul hζz1inv)).intervalIntegrable 0 (2 * π)
          have hi3 : IntervalIntegrable (fun θ => star (F1 (ζ θ)) * (z1 / (ζ θ - z1))) volume 0 (2 * π) :=
            (hF1ζ.star.mul (continuous_const.mul hζz1inv)).intervalIntegrable 0 (2 * π)
          -- Split integrals and distribute smul
          rw [show (fun θ => (F1 (ζ θ) + star (F1 (ζ θ))) / 2
                + F1 (ζ θ) * (z1 / (ζ θ - z1))
                + star (F1 (ζ θ)) * (z1 / (ζ θ - z1)))
              = (fun θ => (F1 (ζ θ) + star (F1 (ζ θ))) / 2
                + (F1 (ζ θ) * (z1 / (ζ θ - z1)) + star (F1 (ζ θ)) * (z1 / (ζ θ - z1)))) by funext; ring]
          rw [intervalIntegral.integral_add hi1 (hi2.add hi3)]
          rw [intervalIntegral.integral_add hi2 hi3]
          rw [smul_add, smul_add]
          -- Apply the three lemmas
          rw [h_avg_term, h_cauchy_term, h_conj_term]
          ring

        -- finish: `re + (F1 z1 - F1 0) = F1 z1 - I * (F1 0).im`
        -- since `F1 0 = re + I*im`.
        have hsplit0 : F1 0 = (F1 0).re + Complex.I * (F1 0).im := by
          have h := Complex.re_add_im (F1 0)
          -- h : (F1 0).re + (F1 0).im * I = F1 0
          -- Need: F1 0 = (F1 0).re + I * (F1 0).im
          rw [mul_comm] at h
          exact h.symm
        -- now conclude
        calc
          (2 * π : ℝ)⁻¹ •
              ∫ θ in (0 : ℝ)..2 * π,
                ((F1 (ζ θ) + star (F1 (ζ θ))) / 2) *
                  (1 + 2 * z1 / (ζ θ - z1))
              = (F1 0).re + (F1 z1 - F1 0) := this
          _ = F1 z1 - (F1 0 - (F1 0).re) := by ring
          _ = F1 z1 - Complex.I * (F1 0).im := by
                have : F1 0 - (F1 0).re = Complex.I * (F1 0).im := by
                  apply Complex.ext
                  · simp [Complex.mul_re, Complex.I_re, Complex.I_im,
                      Complex.ofReal_re, Complex.ofReal_im]
                  · simp [Complex.mul_im, Complex.I_re, Complex.I_im,
                      Complex.ofReal_re, Complex.ofReal_im]
                rw [this]

      -- discharge the original goal (it matches the computed equality)
      simpa [this]

    have : (F1 z1).re = G.re := by
      have := congrArg Complex.re hG
      -- `re (I * r) = 0` for real `r`
      simpa using this.symm
    -- Conclude.
    -- Rewrite RHS to match the statement.
    -- Note `u θ = (F1 (ζ θ)).re` and `ζ = circleMap 0 1`.
    simpa [hG_re, u, ζ] using this

  -- Finish by rewriting `F1` and `z1` back in terms of `F`, `R`, and `z`.
  -- `F1 z1 = F z`
  have hF1z : F1 z1 = F z := by
    simp [F1, z1, mul_div_cancel₀, hRpos.ne']
  -- `circleMap 0 R θ = R * circleMap 0 1 θ`
  have h_circleMap : ∀ θ : ℝ, circleMap (0 : ℂ) R θ = R * circleMap (0 : ℂ) (1 : ℝ) θ := by
    intro θ
    simp [circleMap]
  -- Rewrite the unit identity into the desired one.
  -- (All rewriting is definitional/algebraic.)
  simpa [hF1z, F1, z1, h_circleMap] using h_unit

/--
**Poisson upper bound (disc, center 0).**

If `f : ℂ → ℝ` is harmonic on `closedBall 0 R` and `‖z‖ < R`, then

`f z ≤ ((R + ‖z‖) / (R - ‖z‖)) * circleAverage (fun w ↦ max (f w) 0) 0 R`.

This is the standard Poisson kernel bound, obtained by:
- representing `f` as the real part of a holomorphic function `F` on a slightly larger ball;
- applying Cauchy’s integral formula to `F` and rewriting the boundary integral using the Schwarz
  kernel `S(z/R, θ) = (e^{iθ} + z/R)/(e^{iθ} - z/R)`;
- using `Re S = (2π) · poissonKernel'` and `poissonKernel_max`.
-/
theorem HarmonicOnNhd.poisson_upper_bound
    {f : ℂ → ℝ} {R : ℝ} {z : ℂ}
    (_hz0 : 0 ≤ ‖z‖) (hzR : ‖z‖ < R)
    (hf : HarmonicOnNhd f (closedBall (0 : ℂ) R)) :
    f z ≤ (R + ‖z‖) / (R - ‖z‖) * circleAverage (fun w ↦ max (f w) 0) 0 R := by
  classical
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg z) hzR

  -- Thicken the closed ball so we can write `f` as `Re(F)` for holomorphic `F` on a ball.
  obtain ⟨ε, hε_pos, hε_subset⟩ :=
    (isCompact_closedBall (0 : ℂ) R).exists_thickening_subset_open
      (isOpen_setOf_harmonicAt f) hf
  -- On the thickened set we get a harmonic neighborhood on a slightly larger ball.
  have hf_ball : HarmonicOnNhd f (ball (0 : ℂ) (ε + R)) := by
    -- rewrite the thickening description into a ball inclusion
    have hR_abs : |R| = R := abs_of_pos hRpos
    -- `thickening ε (closedBall 0 R) = ball 0 (ε + R)`
    -- (after rewriting `R` as `|R|`)
    have : thickening ε (closedBall (0 : ℂ) R) = ball (0 : ℂ) (ε + R) := by
      simpa [hR_abs, add_comm, add_left_comm, add_assoc] using
        (thickening_closedBall (x := (0 : ℂ)) (δ := R) hε_pos hRpos.le)
    -- use `hε_subset : thickening ε (closedBall 0 R) ⊆ {x | HarmonicAt f x}`
    intro x hx
    have hx' : x ∈ thickening ε (closedBall (0 : ℂ) R) := by simpa [this] using hx
    exact hε_subset hx'

  -- Represent harmonic function as real part of holomorphic function on the bigger ball.
  obtain ⟨F, hF_an, hF_re⟩ := harmonic_is_realOfHolomorphic (z := (0 : ℂ)) (R := ε + R) hf_ball

  -- We'll apply Cauchy integral formula at `w = z` for the analytic function `F`.
  have hz_ball : z ∈ ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_zero_right] using hzR
  have hz_big : z ∈ ball (0 : ℂ) (ε + R) := by
    -- `‖z‖ < R < ε + R`
    simpa [Metric.mem_ball, dist_zero_right] using (lt_of_lt_of_le hzR (by linarith))

  -- Restrict `F` to the closed ball of radius `R` (needed for circle integral theorems).
  have hF_cont : ContinuousOn F (closedBall (0 : ℂ) R) := by
    intro x hx
    have hx' : x ∈ ball (0 : ℂ) (ε + R) := by
      -- `closedBall 0 R ⊆ ball 0 (ε+R)`
      have hxR : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hx
      have hxlt : ‖x‖ < ε + R := lt_of_le_of_lt hxR (by linarith)
      simpa [Metric.mem_ball, dist_zero_right] using hxlt
    exact (hF_an x hx').continuousAt.continuousWithinAt

  have hF_diff : ∀ x ∈ ball (0 : ℂ) R \ (∅ : Set ℂ), DifferentiableAt ℂ F x := by
    intro x hx
    -- `x ∈ ball 0 R ⊆ ball 0 (ε+R)`
    have hx' : x ∈ ball (0 : ℂ) (ε + R) := by
      have : ‖x‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hx.1
      have : ‖x‖ < ε + R := lt_of_lt_of_le this (by linarith)
      simpa [Metric.mem_ball, dist_zero_right] using this
    exact (hF_an x hx').differentiableAt

  -- Cauchy integral formula in circleAverage form:
  have h_cauchy :
      ((2 * π * I : ℂ)⁻¹ • ∮ w in C(0, R), (w - z)⁻¹ • F w) = F z := by
    -- Use the general Cauchy integral formula lemma (countable exceptional set = ∅).
    simpa using
      (Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        (E := ℂ) (R := R) (c := (0 : ℂ)) (w := z) (f := F) (s := (∅ : Set ℂ))
        (hs := Set.countable_empty) (hw := by
          -- `z ∈ ball 0 R`
          simpa using hz_ball)
        (hc := hF_cont)
        (hd := by
          simpa using hF_diff))

  -- Rewrite `F z` as a circleAverage over the boundary using `Real.circleAverage_eq_circleIntegral`.
  -- We will use the parametrization `w = circleMap 0 R θ = R * exp(iθ)`.
  have h_circleAvg :
      (2 * π : ℝ)⁻¹ • ∫ θ in 0..2 * π,
        (circleMap (0 : ℂ) R θ) • ((circleMap (0 : ℂ) R θ - z)⁻¹ • F (circleMap (0 : ℂ) R θ)) =
        F z := by
    -- Start from Cauchy integral formula and unfold `circleIntegral`.
    -- `circleIntegral` is integral over θ of `deriv_circleMap * (w - z)⁻¹ • F w`.
    -- For `circleMap 0 R θ = R*exp(iθ)`, we have `deriv_circleMap = I * (circleMap 0 R θ - 0) = I * w`,
    -- so after canceling the `I` from `(2πI)⁻¹` we get the Cauchy kernel `w/(w - z)`.
    --
    -- This file already has `Real.circleAverage_eq_circleIntegral`, so we can rely on that
    -- plus straightforward algebra / simp.
    --
    -- Convert `h_cauchy` by rewriting the circle integral into an interval integral in θ.
    -- (We keep the proof explicit but let `simp` handle the standard circleIntegral unfolding.)
    --
    -- NOTE: This is a purely algebraic rewrite, no further analysis.
    have hR_ne : R ≠ 0 := (ne_of_gt hRpos)
    -- Expand circleIntegral in terms of interval integral:
    -- We'll use the definition of `circleIntegral` as in Mathlib.
    -- `simp [circleIntegral, circleMap, deriv_circleMap]` should reduce it.
    -- Then `field_simp` clears denominators and matches `schwarzKernel`.
    -- We do the conversion by rewriting `h_cauchy` directly.
    -- (We keep the result as a statement for later use; proof by `simpa` after unfolding.)
    -- Unfortunately, `simp`/`ring` needs some help with casts and `R`-scaling.
    --
    -- A robust route is to rewrite the circle integral using `Real.circleAverage_eq_circleIntegral`.
    -- Apply it to the ℂ-valued function `fun w => (w - z)⁻¹ • F w`, then solve for the integral.
    --
    -- From `Real.circleAverage_eq_circleIntegral hR_ne`:
    --   circleAverage g 0 R = (2πI)⁻¹ • ∮ (w-0)⁻¹ • g w
    -- We choose `g w := (w - z)⁻¹ • F w * w` so that `(w-0)⁻¹ * g w = (w-z)⁻¹ • F w`.
    let g : ℂ → ℂ := fun w => w • ((w - z)⁻¹ • F w)
    have hg_avg :
        Real.circleAverage g 0 R =
          (2 * π * I : ℂ)⁻¹ • ∮ w in C(0, R), (w - 0)⁻¹ • g w := by
      simp [Real.circleAverage_eq_circleIntegral (f := g) (c := (0 : ℂ)) (R := R) hR_ne]
    -- On the circle (`w ∈ sphere 0 R`) we have `(w - 0)⁻¹ • g w = (w - z)⁻¹ • F w`.
    have hg_simpl :
        EqOn (fun w => (w - 0)⁻¹ • g w) (fun w => (w - z)⁻¹ • F w) (sphere (0 : ℂ) R) := by
      intro w hw
      have hw0 : w ≠ 0 := by
        have hw_norm : ‖w‖ = R := by
          simpa [Metric.mem_sphere, dist_zero_right] using hw
        intro hw0
        subst hw0
        have : (0 : ℝ) = R := by simpa using hw_norm
        exact hR_ne this.symm
      -- now it's just `w⁻¹ • (w • x) = x`
      simp [g, sub_zero, hw0]
    have hcongr :
        (∮ w in C(0, R), (w - 0)⁻¹ • g w) = ∮ w in C(0, R), (w - z)⁻¹ • F w := by
      exact circleIntegral.integral_congr (c := (0 : ℂ)) (R := R) (hR := hRpos.le) hg_simpl
    have : (2 * π * I : ℂ)⁻¹ • ∮ w in C(0, R), (w - 0)⁻¹ • g w = F z := by
      -- rewrite the circle integral using `hcongr` and then apply `h_cauchy`
      rw [hcongr]
      exact h_cauchy
    -- Therefore `circleAverage g 0 R = F z`.
    have h_avg_eq : Real.circleAverage g 0 R = F z := by
      -- combine `hg_avg` with `this`
      simpa [hg_avg] using this
    -- Unfold circleAverage to an interval integral in θ.
    -- Here `g (circleMap 0 R θ) = (circleMap 0 R θ) • ((circleMap 0 R θ - z)⁻¹ • F (circleMap 0 R θ))`.
    -- We do it by `simp`/`field_simp`/`ring`.
    -- Finally, convert the scalar normalization: `(2π)⁻¹` on ℝ matches `(2π)⁻¹` on ℂ via `ofReal`.
    --
    -- Since the result is purely algebraic, `simp` should close with `h_avg_eq`.
    -- We keep it as `by` block to allow local rewrites.
    -- NOTE: `Real.circleAverage` is polymorphic; here it returns ℂ.
    -- So `Real.circleAverage` uses real scalar `(2π)⁻¹`; Lean coerces to ℂ.
    -- We'll simply unfold and use `simp` with `circleMap` algebra.
    --
    -- Use the definition:
    -- `Real.circleAverage g 0 R = (2π)⁻¹ • ∫ θ, g(circleMap 0 R θ)`
    -- and substitute `g`.
    simpa [Real.circleAverage, g] using h_avg_eq

  -- Take real parts.
  have h_re :
      f z =
        (2 * π)⁻¹ *
          (∫ θ in (0 : ℝ)..2 * π,
              (circleMap (0 : ℂ) R θ) *
                ((circleMap (0 : ℂ) R θ - z)⁻¹ * F (circleMap (0 : ℂ) R θ))).re := by
    have hFz_re : (F z).re = f z := hF_re hz_big
    have : (F z).re =
        (2 * π)⁻¹ *
          (∫ θ in (0 : ℝ)..2 * π,
              (circleMap (0 : ℂ) R θ) *
                ((circleMap (0 : ℂ) R θ - z)⁻¹ * F (circleMap (0 : ℂ) R θ))).re := by
      -- Take `re` of `h_circleAvg` and simplify.
      simpa [Complex.smul_re, intervalIntegral.integral_smul, smul_eq_mul, mul_assoc,
        mul_left_comm, mul_comm, sub_eq_add_neg] using (congrArg Complex.re h_circleAvg).symm
    simpa [hFz_re] using this

  -- Now bound the integrand by using `max (f (circleMap ..)) 0` and the Poisson kernel maximum bound.
  -- Convert `(schwarzKernel (z/R) θ).re` into `(2π) * poissonKernel'`.
  have hzR' : ‖z / R‖ < 1 := by
    -- `‖z / R‖ = ‖z‖ / |R|` and `‖z‖ < R`
    have hRabs : |R| = R := abs_of_pos hRpos
    simpa [norm_div, hRabs] using (by exact (div_lt_one₀ hRpos).mpr hzR)
  -- Pack `z/R` as a unit disc point.
  let zD : Complex.UnitDisc := ⟨z / R, by simpa using hzR'⟩
  have h_re_kernel : ∀ θ : ℝ, (Complex.schwarzKernel (z / R) θ).re = (2 * Real.pi) * Complex.poissonKernel' zD θ := by
    intro θ
    -- This is exactly `schwarzKernel_re_eq_poissonKernel`.
    simpa [zD] using Complex.schwarzKernel_re_eq_poissonKernel zD θ

  -- Use positivity and `poissonKernel_max` for the unit disc Poisson kernel `poissonKernel'`.
  have h_poisson_le :
      ∀ θ : ℝ,
        0 ≤ (Complex.schwarzKernel (z / R) θ).re ∧
        (Complex.schwarzKernel (z / R) θ).re ≤ (1 + ‖z / R‖) / (1 - ‖z / R‖) := by
    intro θ
    -- Use `poissonKernel'_eq_inv_two_pi_mul_poissonKernel` + `poissonKernel_max`.
    have hpk' :
        Complex.poissonKernel' zD θ =
          (2 * Real.pi)⁻¹ * Complex.poissonKernel ‖(zD : ℂ)‖ θ (Complex.arg (zD : ℂ)) := by
      exact Complex.poissonKernel'_eq_inv_two_pi_mul_poissonKernel zD θ
    have hpk_max :
        Complex.poissonKernel ‖(zD : ℂ)‖ θ (Complex.arg (zD : ℂ))
          ≤ (1 + ‖(zD : ℂ)‖) / (1 - ‖(zD : ℂ)‖) := by
      have hr0 : 0 ≤ ‖(zD : ℂ)‖ := norm_nonneg _
      have hr1 : ‖(zD : ℂ)‖ < 1 := zD.norm_lt_one
      simpa using
        (Complex.poissonKernel_max (r := ‖(zD : ℂ)‖) hr0 hr1 θ (Complex.arg (zD : ℂ)))
    have hpk_nonneg :
        0 ≤ Complex.poissonKernel ‖(zD : ℂ)‖ θ (Complex.arg (zD : ℂ)) := by
      have hr0 : 0 ≤ ‖(zD : ℂ)‖ := norm_nonneg _
      have hr1 : ‖(zD : ℂ)‖ < 1 := zD.norm_lt_one
      exact Complex.poissonKernel_nonneg hr0 hr1 θ (Complex.arg (zD : ℂ))
    -- Rewrite `schwarzKernel.re` as the (unnormalized) Poisson kernel.
    have h_schwarz_eq :
        (Complex.schwarzKernel (z / R) θ).re =
          Complex.poissonKernel ‖(zD : ℂ)‖ θ (Complex.arg (zD : ℂ)) := by
      have hpi_pos : 0 < (2 * Real.pi) := by positivity
      calc
        (Complex.schwarzKernel (z / R) θ).re
            = (2 * Real.pi) * Complex.poissonKernel' zD θ := by simp [h_re_kernel θ]
          _ = (2 * Real.pi) *
                ((2 * Real.pi)⁻¹ * Complex.poissonKernel ‖(zD : ℂ)‖ θ (Complex.arg (zD : ℂ))) := by
              simp [hpk']
          _ = Complex.poissonKernel ‖(zD : ℂ)‖ θ (Complex.arg (zD : ℂ)) := by
              field_simp
    have hzD_norm : ‖(zD : ℂ)‖ = ‖z / R‖ := rfl
    constructor
    · simpa [h_schwarz_eq, hzD_norm] using hpk_nonneg
    · simpa [h_schwarz_eq, hzD_norm] using hpk_max

  -- Use the inequality: `x ≤ x⁺ = max x 0` pointwise, and positivity of the kernel.
  -- From `h_re`, rewrite `f z` as an integral and bound by `poissonKernel_max * circleAverage (max f 0)`.
  have h_le_avg :
      f z ≤ ((1 + ‖z / R‖) / (1 - ‖z / R‖)) *
        circleAverage (fun w ↦ max (f w) 0) 0 R := by
    -- We start from the integral representation `h_re`, then:
    -- 1) replace `(F (circleMap 0 R θ)).re` by `f (circleMap 0 R θ)` using `hF_re`
    -- 2) bound `f (...) ≤ max (f (...)) 0`
    -- 3) bound kernel by its max, factor it out, and identify the remaining integral as circleAverage.
    --
    -- Step 1: rewrite boundary real part.
    have h_boundary_re :
        ∀ θ : ℝ, (F (circleMap (0 : ℂ) R θ)).re = f (circleMap (0 : ℂ) R θ) := by
      intro θ
      have hθ_mem : circleMap (0 : ℂ) R θ ∈ ball (0 : ℂ) (ε + R) := by
        -- On the circle of radius R, norm = |R| = R < ε + R.
        have : ‖circleMap (0 : ℂ) R θ‖ = |R| := by
          simp [circleMap]
        have : ‖circleMap (0 : ℂ) R θ‖ ≤ R := by
          simp [this, abs_of_pos hRpos]
        have : ‖circleMap (0 : ℂ) R θ‖ < ε + R := lt_of_le_of_lt this (by linarith)
        simpa [Metric.mem_ball, dist_zero_right] using this
      -- Apply `hF_re` on the bigger ball.
      simpa using hF_re hθ_mem

    -- Establish continuity of f on the closed ball (from harmonicity)
    have hf_contOn : ContinuousOn f (closedBall (0 : ℂ) R) := by
      intro x hx
      have hx_big : x ∈ ball (0 : ℂ) (ε + R) := by
        have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
        have : ‖x‖ < ε + R := lt_of_le_of_lt hxR (by linarith)
        simpa [Metric.mem_ball, dist_zero_right] using this
      -- HarmonicAt gives ContDiffAt, which gives ContinuousAt
      exact (hf_ball x hx_big).1.continuousAt.continuousWithinAt

    -- Continuity of f ∘ circleMap
    have hf_circ : Continuous (fun θ => f (circleMap (0 : ℂ) R θ)) := by
      have hcirc_mem : ∀ θ, circleMap (0 : ℂ) R θ ∈ closedBall (0 : ℂ) R := fun θ => by
        simp only [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos hRpos, le_refl]
      exact hf_contOn.comp_continuous (continuous_circleMap 0 R) hcirc_mem

    -- Continuity of Schwarz kernel real part
    have hK_cont : Continuous (fun θ => (Complex.schwarzKernel (z / R) θ).re) := by
      -- schwarzKernel is continuous for z in ball 0 1
      have hzR_mem : ‖z / R‖ < 1 := hzR'
      exact Complex.continuous_re.comp (Complex.continuous_schwarzKernel_theta hzR_mem)

    -- Use the Schwarz/Poisson representation for the real part.
    -- schwarzKernel_re_avg_eq_re gives: (F z).re = (2π)⁻¹ * ∫ schwarzKernel.re * (F ∘ circleMap).re
    -- Since f = F.re on ball 0 R (via hF_re), we get the result.
    have h_re' :
        f z =
          (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
            (Complex.schwarzKernel (z / R) θ).re * f (circleMap (0 : ℂ) R θ) := by
      -- Use the Schwarz kernel representation theorem for analytic functions.
      -- Need analyticity on ball 0 R and continuity on closedBall 0 R.
      have hF_an_R : AnalyticOnNhd ℂ F (ball (0 : ℂ) R) :=
        hF_an.mono (ball_subset_ball (by linarith : R ≤ ε + R))
      -- Apply the Schwarz representation theorem
      have h_schwarz := re_eq_schwarzKernel_integral hRpos hF_an_R hF_cont hz_ball
      -- h_schwarz: (F z).re = (2π)⁻¹ * ∫ schwarzKernel.re * (F ∘ circleMap).re
      -- We have f = F.re on ball 0 (ε + R), and z ∈ ball 0 R ⊆ ball 0 (ε + R)
      -- so f z = (F z).re
      have hz_big' : z ∈ ball (0 : ℂ) (ε + R) :=
        ball_subset_ball (by linarith : R ≤ ε + R) hz_ball
      have hfz_eq : f z = (F z).re := (hF_re hz_big').symm
      rw [hfz_eq, h_schwarz]
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _hθ
      simp only
      rw [h_boundary_re θ]

    -- Now bound the integrand by replacing `f` with `max f 0` and kernel with its max bound.
    have h_int_le :
        (∫ θ in (0 : ℝ)..2 * π,
            (Complex.schwarzKernel (z / R) θ).re * f (circleMap (0 : ℂ) R θ))
          ≤ (∫ θ in (0 : ℝ)..2 * π,
            ((1 + ‖z / R‖) / (1 - ‖z / R‖)) * (max (f (circleMap (0 : ℂ) R θ)) 0)) := by
      -- Integrability of left side
      have hi_left : IntervalIntegrable
          (fun θ => (Complex.schwarzKernel (z / R) θ).re * f (circleMap (0 : ℂ) R θ))
          volume 0 (2 * π) :=
        (hK_cont.mul hf_circ).intervalIntegrable 0 (2 * π)
      -- Integrability of right side
      have hi_right : IntervalIntegrable
          (fun θ => ((1 + ‖z / R‖) / (1 - ‖z / R‖)) * max (f (circleMap (0 : ℂ) R θ)) 0)
          volume 0 (2 * π) :=
        (continuous_const.mul (hf_circ.max continuous_const)).intervalIntegrable 0 (2 * π)
      -- Apply monotonicity
      apply intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * π) hi_left hi_right
      intro θ _hθ
      have hk_nonneg := (h_poisson_le θ).1
      have hk_le := (h_poisson_le θ).2
      have hf_le : f (circleMap (0 : ℂ) R θ) ≤ max (f (circleMap (0 : ℂ) R θ)) 0 := le_max_left _ _
      calc
        (Complex.schwarzKernel (z / R) θ).re * f (circleMap (0 : ℂ) R θ)
            ≤ (Complex.schwarzKernel (z / R) θ).re * max (f (circleMap (0 : ℂ) R θ)) 0 := by
              exact mul_le_mul_of_nonneg_left hf_le hk_nonneg
          _ ≤ ((1 + ‖z / R‖) / (1 - ‖z / R‖)) * max (f (circleMap (0 : ℂ) R θ)) 0 := by
              have hb_nonneg : 0 ≤ max (f (circleMap (0 : ℂ) R θ)) 0 := le_max_right _ _
              exact mul_le_mul_of_nonneg_right hk_le hb_nonneg

    -- Apply scaling by `(2π)⁻¹` and simplify.
    have h_scale :
        (2 * π)⁻¹ *
            (∫ θ in (0 : ℝ)..2 * π,
              (Complex.schwarzKernel (z / R) θ).re * f (circleMap (0 : ℂ) R θ))
          ≤ (2 * π)⁻¹ *
            (∫ θ in (0 : ℝ)..2 * π,
              ((1 + ‖z / R‖) / (1 - ‖z / R‖)) * max (f (circleMap (0 : ℂ) R θ)) 0) := by
      exact mul_le_mul_of_nonneg_left h_int_le (by positivity : 0 ≤ (2 * π)⁻¹)

    -- Rewrite RHS: factor constants and identify circleAverage.
    -- `circleAverage g 0 R = (2π)⁻¹ • ∫ θ, g(circleMap 0 R θ)`.
    have h_rhs :
        (2 * π)⁻¹ *
            (∫ θ in (0 : ℝ)..2 * π,
              ((1 + ‖z / R‖) / (1 - ‖z / R‖)) * max (f (circleMap (0 : ℂ) R θ)) 0)
          = ((1 + ‖z / R‖) / (1 - ‖z / R‖)) *
              circleAverage (fun w ↦ max (f w) 0) 0 R := by
      -- Use the definition: circleAverage f c R = (2π)⁻¹ • ∫ θ, f(circleMap c R θ)
      simp only [Real.circleAverage_def, smul_eq_mul]
      -- Factor out the constant from the integral
      rw [intervalIntegral.integral_const_mul]
      ring
    -- Put together using h_re', h_scale, h_rhs
    calc f z = (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
                (Complex.schwarzKernel (z / R) θ).re * f (circleMap (0 : ℂ) R θ) := h_re'
      _ ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
            ((1 + ‖z / R‖) / (1 - ‖z / R‖)) * max (f (circleMap (0 : ℂ) R θ)) 0 := h_scale
      _ = ((1 + ‖z / R‖) / (1 - ‖z / R‖)) * circleAverage (fun w ↦ max (f w) 0) 0 R := h_rhs
  -- Convert the coefficient `((1 + ‖z/R‖)/(1 - ‖z/R‖))` into `((R+‖z‖)/(R-‖z‖))`.
  have h_coeff :
      (1 + ‖z / R‖) / (1 - ‖z / R‖) = (R + ‖z‖) / (R - ‖z‖) := by
    have hRabs : |R| = R := abs_of_pos hRpos
    have hRne : R ≠ 0 := hRpos.ne'
    have h1 : ‖z / R‖ = ‖z‖ / R := by simp [hRabs]
    rw [h1]
    have hden_pos : 0 < R - ‖z‖ := sub_pos.mpr hzR
    field_simp [hRne, hden_pos.ne']

  rw [← h_coeff]
  exact h_le_avg

end InnerProductSpace
