import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.CircleAverageLemmas
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.PosLogLemmas

/-!
# Harnack-type Bounds for Harmonic Functions

This file provides Harnack-type oscillation bounds for harmonic functions on the disc,
which are essential for establishing bounds on `log|f|` for analytic functions.

## Main results

* `HarmonicOnNhd.norm_le_sup_sphere` : Maximum principle for harmonic functions
* `HarmonicOnNhd.oscillation_on_ball` : Oscillation bound for harmonic functions
* `AnalyticOnNhd.log_norm_harmonicOnNhd` : log|f| is harmonic for analytic nonvanishing f
* `AnalyticOnNhd.circleAverage_abs_log_norm_le_sup` : Circle average bound for |log|f||

## References

* Conway, J.B., "Functions of One Complex Variable I", Chapter IV
* Rudin, W., "Real and Complex Analysis", Chapter 11
-/

open Complex Set Metric Filter Topology Real MeasureTheory InnerProductSpace
open scoped Real

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

end Nevanlinna
