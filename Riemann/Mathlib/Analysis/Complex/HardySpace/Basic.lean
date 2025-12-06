
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.ContinuousOn

/-!
# Hardy Spaces: Basic Definitions

This file provides the foundational definitions for Hardy spaces H^p on the unit disc.

## Main definitions

* `Complex.unitDisc` : The open unit disc as a subset of ℂ (= ball 0 1)
* `Complex.IsInHInfty` : The class of bounded analytic functions on the disc (H^∞)
* `Complex.IsInHardySpace` : The class of H^p functions for finite p
* `Complex.circleNorm` : The L^p norm on circles
* `Complex.hardyNorm` : The Hardy space norm

## Implementation notes

We use `Complex.UnitDisc` (𝔻) from Mathlib as the primary type for points in the disc.
We also define `Complex.unitDisc` as the set `{z : ℂ | ‖z‖ < 1}` = `Metric.ball 0 1`
for convenience in statements about analytic functions on open sets.

## References

* Duren, P.L., "Theory of H^p Spaces"
* Garnett, J.B., "Bounded Analytic Functions"
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### The unit disc: connecting Mathlib's UnitDisc to set-based formulations -/

/-- The open unit disc as a subset of ℂ. This equals `Metric.ball 0 1` and
is the underlying set of `Complex.UnitDisc`. -/
def unitDisc : Set ℂ := {z : ℂ | ‖z‖ < 1}

@[simp]
lemma mem_unitDisc {z : ℂ} : z ∈ unitDisc ↔ ‖z‖ < 1 := Iff.rfl

lemma unitDisc_eq_ball : unitDisc = Metric.ball (0 : ℂ) 1 := by
  ext z; simp [unitDisc, Metric.mem_ball, dist_zero_right]

lemma isOpen_unitDisc : IsOpen unitDisc := by
  rw [unitDisc_eq_ball]; exact Metric.isOpen_ball

lemma zero_mem_unitDisc : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]

/-- The coercion from `𝔻` lands in `unitDisc`. -/
lemma UnitDisc.coe_mem (z : 𝔻) : (z : ℂ) ∈ unitDisc := z.norm_lt_one

/-- `unitDisc` is precisely the range of the coercion from `𝔻`. -/
lemma unitDisc_eq_range_coe : unitDisc = Set.range (UnitDisc.coe : 𝔻 → ℂ) := by
  ext z
  simp only [mem_unitDisc, Set.mem_range]
  constructor
  · intro hz
    exact ⟨UnitDisc.mk z hz, rfl⟩
  · rintro ⟨w, rfl⟩
    exact w.norm_lt_one

/-- The closed disc of radius r. -/
def closedDisc (r : ℝ) : Set ℂ := Metric.closedBall (0 : ℂ) r

@[simp]
lemma mem_closedDisc {z : ℂ} {r : ℝ} : z ∈ closedDisc r ↔ ‖z‖ ≤ r := by
  simp [closedDisc, Metric.mem_closedBall, dist_zero_right]

lemma closedDisc_subset_unitDisc {r : ℝ} (hr : r < 1) : closedDisc r ⊆ unitDisc := by
  intro z hz
  rw [mem_closedDisc] at hz
  simp only [mem_unitDisc]
  exact lt_of_le_of_lt hz hr

/-! ### L^p norms on circles -/

/-- The L^p norm of f on the circle of radius r, for p ∈ (0, ∞). -/
def circleNorm (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..2 * Real.pi, ‖f (circleMap 0 r θ)‖ ^ p) ^ (1 / p)

/-- The L^∞ norm of f on the circle of radius r. -/
def circleSupNorm (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ θ : ℝ, ‖f (circleMap 0 r θ)‖

/-- The Hardy norm for finite p. -/
def hardyNorm (p : ℝ) (f : ℂ → ℂ) : ℝ :=
  ⨆ r : {r : ℝ // 0 < r ∧ r < 1}, circleNorm p f r.val

/-- The H^∞ norm (supremum on the disc). -/
def hardySupNorm (f : ℂ → ℂ) : ℝ :=
  ⨆ z : 𝔻, ‖f z‖

/-! ### Hardy space definitions -/

/-- H^∞: bounded analytic functions on the disc. -/
structure IsInHInfty (f : ℂ → ℂ) : Prop where
  /-- The function is analytic on the unit disc. -/
  analyticOn : AnalyticOn ℂ f unitDisc
  /-- The function is bounded on the unit disc. -/
  bounded : ∃ M : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ M

/-- A function belongs to the Hardy space H^p (for finite p > 0) if it is analytic on the disc
and has bounded Hardy norm. -/
structure IsInHardySpace (p : ℝ) (f : ℂ → ℂ) : Prop where
  /-- The function is analytic on the unit disc. -/
  analyticOn : AnalyticOn ℂ f unitDisc
  /-- The Hardy norm is finite. -/
  hardyNorm_finite : BddAbove (Set.range fun r : {r : ℝ // 0 < r ∧ r < 1} => circleNorm p f r.val)

/-- Characterization of H^∞. -/
lemma isInHInfty_iff {f : ℂ → ℂ} :
    IsInHInfty f ↔ AnalyticOn ℂ f unitDisc ∧ ∃ M : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ M := by
  constructor
  · intro hf; exact ⟨hf.analyticOn, hf.bounded⟩
  · intro ⟨ha, hb⟩; exact ⟨ha, hb⟩

/-! ### Basic properties of Hardy space functions -/

/-- H^p functions are analytic on the disc. -/
lemma IsInHardySpace.analyticOnDisc {p : ℝ} {f : ℂ → ℂ} (hf : IsInHardySpace p f) :
    AnalyticOn ℂ f unitDisc := hf.analyticOn

/-- H^∞ functions are analytic on the disc. -/
lemma IsInHInfty.analyticOnDisc {f : ℂ → ℂ} (hf : IsInHInfty f) :
    AnalyticOn ℂ f unitDisc := hf.analyticOn

/-- H^∞ functions are bounded on the disc. -/
lemma IsInHInfty.isBounded {f : ℂ → ℂ} (hf : IsInHInfty f) :
    ∃ M : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ M := hf.bounded

/-- H^∞ functions are continuous on the disc. -/
lemma IsInHInfty.continuousOn {f : ℂ → ℂ} (hf : IsInHInfty f) :
    ContinuousOn f unitDisc := by
  apply hf.analyticOn.continuousOn

/-- For analytic functions on the unit disc, analyticity at interior points.
On open sets, `AnalyticOn` coincides with `AnalyticOnNhd`, giving pointwise `AnalyticAt`. -/
lemma analyticAt_of_analyticOn_unitDisc {f : ℂ → ℂ} (hf : AnalyticOn ℂ f unitDisc) {z : ℂ}
    (hz : z ∈ unitDisc) : AnalyticAt ℂ f z :=
  (isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf) z hz

/-! ### Helper inequalities -/

/-- log(1/x) ≥ 1-x for 0 < x ≤ 1. Key for relating Blaschke sums to Jensen sums.

This follows from the standard inequality log x ≤ x - 1 for x > 0. -/
lemma Real.one_sub_le_log_inv {x : ℝ} (hx0 : 0 < x) (_ : x ≤ 1) :
    1 - x ≤ Real.log (1 / x) := by
  rw [one_div, Real.log_inv]
  -- Need to show 1 - x ≤ -log x, i.e., log x ≤ x - 1
  -- This follows from the fact that exp y ≥ 1 + y, applied with y = log x
  have h := Real.add_one_le_exp (Real.log x)
  rw [Real.exp_log hx0] at h
  linarith

/-- For 0 < |a| < 1, we have 1 - |a| ≤ log(1/|a|). -/
lemma one_sub_norm_le_log_inv_norm {a : ℂ} (ha0 : a ≠ 0) (ha1 : ‖a‖ < 1) :
    1 - ‖a‖ ≤ Real.log (1 / ‖a‖) := by
  apply Real.one_sub_le_log_inv (norm_pos_iff.mpr ha0)
  exact le_of_lt ha1

end Complex
