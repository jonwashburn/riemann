/-
Copyright (c) 2025. All rights reserved.
Released under MIT license.

# Whitney Geometry and Dyadic Covering

This module provides the infrastructure for proving the interior coverage axiom:
every point in the critical strip lies in the interior of some recognizer band.

Adapted from jonwashburn/riemann repository.
-/

import RiemannRecognitionGeometry.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Set.Countable

noncomputable section
open Classical MeasureTheory
open scoped BigOperators MeasureTheory

namespace RiemannRecognitionGeometry

/-! ## Dyadic Intervals -/

/-- A dyadic interval at scale k with index m: center at (m + 1/2) · 2^(-k), length 2^(-k). -/
def dyadicInterval (k : ℤ) (m : ℤ) : WhitneyInterval where
  t0 := (m : ℝ) * (2 : ℝ)^(-k) + (2 : ℝ)^(-k) / 2
  len := (2 : ℝ)^(-k) / 2
  len_pos := by
    have h : (0 : ℝ) < (2 : ℝ)^(-k) := zpow_pos (by norm_num : (0 : ℝ) < 2) (-k)
    linarith

/-- The length of dyadic interval at scale k is 2^(-k). -/
lemma dyadicInterval_full_length (k : ℤ) (m : ℤ) :
    2 * (dyadicInterval k m).len = (2 : ℝ)^(-k) := by
  simp [dyadicInterval]
  ring

/-! ## Scale Selection for Coverage

Given σ > 1/2, we need to find a scale k such that the recognizer band at that
scale contains points with real part σ.
-/

/-- For σ ∈ (1/2, 1], find the appropriate dyadic scale. -/
def findScale (σ : ℝ) (hσ_lower : 1/2 < σ) (hσ_upper : σ ≤ 1) : ℤ :=
  -- We need L such that λ_rec · L ≤ σ - 1/2 ≤ Λ_rec · L
  -- With λ_rec = 1/3 and Λ_rec = 3/2, we need L ≈ (σ - 1/2)
  -- Use k = ⌈-log₂(3(σ - 1/2))⌉
  Int.ceil (-Real.logb 2 (3 * (σ - 1/2)))

/-- For t ∈ ℝ and scale k, find the dyadic interval index. -/
def findIndex (t : ℝ) (k : ℤ) : ℤ :=
  Int.floor (t / (2 : ℝ)^(-k))

/-! ## Main Coverage Lemma

We prove that every point in {1/2 < Re(s) ≤ 1} lies in the interior of some
recognizer band constructed from dyadic intervals.
-/

/-- Construct a recognizer band for a given point in the critical strip.
    This uses the default parameters λ_rec = 1/3, Λ_rec = 3/2. -/
def coveringBand (s : ℂ) (hs_lower : 1/2 < s.re) (hs_upper : s.re ≤ 1) : RecognizerBand :=
  let σ := s.re
  let t := s.im
  -- Choose scale based on σ
  let k := findScale σ hs_lower hs_upper
  -- Choose index based on t
  let m := findIndex t k
  -- Construct the band
  { base := dyadicInterval k m
    params := defaultRecognizerParams }

/-- Auxiliary: 3 * (σ - 1/2) > 0 for σ > 1/2. -/
private lemma three_sigma_pos (σ : ℝ) (hσ : 1/2 < σ) : 0 < 3 * (σ - 1/2) := by linarith

/-- Auxiliary: 3 * (σ - 1/2) ≤ 3/2 for σ ≤ 1. -/
private lemma three_sigma_le (σ : ℝ) (hσ : σ ≤ 1) : 3 * (σ - 1/2) ≤ 3/2 := by linarith

/-- The key scale lemma: if k = ⌈-log₂(3(σ - 1/2))⌉ and L = 2^(-k),
    then L/3 ≤ σ - 1/2 < 2L/3, which places σ in the interior of the band. -/
private lemma scale_basic_bounds (σ : ℝ) (hσ_lower : 1/2 < σ) (hσ_upper : σ ≤ 1) :
    let k := findScale σ hσ_lower hσ_upper
    let L := (2 : ℝ)^(-k)
    L / 3 ≤ σ - 1/2 ∧ σ - 1/2 < 2 * L / 3 := by
  intro k L

  -- Set x = 3 * (σ - 1/2), so x > 0 and x ≤ 3/2
  set x := 3 * (σ - 1/2) with hx_def
  have hx_pos : 0 < x := three_sigma_pos σ hσ_lower

  -- k = ⌈-log₂(x)⌉, so we have:
  -- (1) -log₂(x) ≤ k    (ceiling property: t ≤ ⌈t⌉)
  -- (2) k < -log₂(x) + 1 (ceiling property: ⌈t⌉ < t + 1)
  have h_ceil_lower : -Real.logb 2 x ≤ k := Int.le_ceil (-Real.logb 2 x)
  have h_ceil_upper : (k : ℝ) < -Real.logb 2 x + 1 := Int.ceil_lt_add_one (-Real.logb 2 x)

  have hL_pos : 0 < L := zpow_pos (by norm_num : (0 : ℝ) < 2) (-k)
  have two_pos : (0 : ℝ) < 2 := by norm_num
  have two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  have one_lt_two : (1 : ℝ) < 2 := by norm_num

  -- From (1): -log₂(x) ≤ k means log₂(x) ≥ -k
  -- This gives: x ≥ 2^(-k) = L
  have h_x_lower : L ≤ x := by
    have h1 : Real.logb 2 x ≥ -(k : ℝ) := by linarith
    -- logb 2 x ≥ -k ↔ x ≥ 2^(-k) when 1 < 2 and x > 0
    have h2 := @Real.le_logb_iff_rpow_le 2 (-(k : ℝ)) x one_lt_two hx_pos
    -- h2 : -(k : ℝ) ≤ logb 2 x ↔ 2^(-(k:ℝ)) ≤ x
    rw [ge_iff_le, h2] at h1
    -- Now h1 : 2^(-(k : ℝ)) ≤ x
    -- We need L = 2^(-k : ℤ) ≤ x
    -- The key is that 2^(-(k : ℝ)) = 2^(-k : ℤ)
    -- Note: -(k : ℝ) is the same as ((-k) : ℤ) : ℝ when cast properly
    have h3 : (2 : ℝ) ^ (-(k : ℝ)) = (2 : ℝ) ^ (-k : ℤ) := by
      have : (-(k : ℝ)) = ((-k : ℤ) : ℝ) := by simp [Int.cast_neg]
      rw [this, Real.rpow_intCast]
    rw [h3] at h1
    exact h1

  -- From (2): k < -log₂(x) + 1 means log₂(x) < 1 - k
  -- This gives: x < 2^(1-k) = 2 · 2^(-k) = 2L
  have h_x_upper : x < 2 * L := by
    have h1 : Real.logb 2 x < 1 - (k : ℝ) := by linarith
    -- logb 2 x < 1-k ↔ x < 2^(1-k) when 1 < 2 and x > 0
    have h2 := @Real.logb_lt_iff_lt_rpow 2 x (1 - (k : ℝ)) one_lt_two hx_pos
    rw [h2] at h1
    -- h1 : x < 2^(1 - (k : ℝ))
    -- 2^(1-k) = 2^1 * 2^(-k) = 2 * 2^(-k) = 2 * L
    have h3 : (2 : ℝ) ^ (1 - (k : ℝ)) = 2 * (2 : ℝ) ^ (-k : ℤ) := by
      have h4 : (2 : ℝ) ^ (1 - (k : ℝ)) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(k : ℝ)) := by
        rw [← Real.rpow_add two_pos]
        ring_nf
      have h5 : (-(k : ℝ)) = ((-k : ℤ) : ℝ) := by simp [Int.cast_neg]
      rw [h4, Real.rpow_one, h5, Real.rpow_intCast]
    rw [h3] at h1
    exact h1

  -- Translate to σ - 1/2 bounds using x = 3(σ - 1/2)
  constructor
  · -- From L ≤ 3(σ - 1/2): L/3 ≤ σ - 1/2
    linarith
  · -- From 3(σ - 1/2) < 2L: σ - 1/2 < 2L/3
    linarith

/-- Key lemma: the σ-coordinate lies in the band's range with margin.
    This is the core of the interior coverage proof.

    The band has:
    - len = L/2 where L = 2^(-k)
    - σ_lower = 1/2 + (1/3) * (L/2) = 1/2 + L/6
    - σ_upper = 1/2 + (3/2) * (L/2) = 1/2 + 3L/4
    - thickness = (3/2 - 1/3) * (L/2) = 7L/12
    - margin = thickness/8 = 7L/96

    From scale selection: L/3 ≤ σ - 1/2 < 2L/3

    We verify:
    - Lower: L/6 + 7L/96 = 23L/96 ≤ L/3 = 32L/96 ✓
    - Upper: 2L/3 = 64L/96 < 3L/4 - 7L/96 = 65L/96 ✓ -/
lemma σ_in_band_range (s : ℂ) (hs_lower : 1/2 < s.re) (hs_upper : s.re ≤ 1) :
    let B := coveringBand s hs_lower hs_upper
    B.σ_lower + B.thickness / 8 ≤ s.re ∧ s.re ≤ B.σ_upper - B.thickness / 8 := by
  -- Get the basic bounds from scale selection
  have ⟨h_basic_lower, h_basic_upper⟩ := scale_basic_bounds s.re hs_lower hs_upper

  -- Unfold definitions
  simp only [coveringBand, RecognizerBand.σ_lower, RecognizerBand.σ_upper,
             RecognizerBand.thickness, defaultRecognizerParams, dyadicInterval]

  set k := findScale s.re hs_lower hs_upper
  set L := (2 : ℝ)^(-k)

  have hL_pos : 0 < L := zpow_pos (by norm_num : (0 : ℝ) < 2) (-k)

  -- The half-length is L/2
  -- σ_lower = 1/2 + (1/3) * (L/2) = 1/2 + L/6
  -- σ_upper = 1/2 + (3/2) * (L/2) = 1/2 + 3L/4
  -- thickness = (3/2 - 1/3) * (L/2) = 7L/12
  -- margin = 7L/96

  -- Need to show:
  -- (1) 1/2 + L/6 + 7L/96 ≤ s.re, i.e., 1/2 + 23L/96 ≤ s.re
  -- (2) s.re ≤ 1/2 + 3L/4 - 7L/96, i.e., s.re ≤ 1/2 + 65L/96

  -- From h_basic_lower: L/3 ≤ s.re - 1/2, so s.re ≥ 1/2 + L/3 = 1/2 + 32L/96
  -- Since 32L/96 > 23L/96, we have s.re ≥ 1/2 + 23L/96 ✓

  -- From h_basic_upper: s.re - 1/2 < 2L/3, so s.re < 1/2 + 64L/96
  -- Since 64L/96 < 65L/96, we have s.re ≤ 1/2 + 65L/96 ✓

  constructor
  · -- Lower bound: 1/2 + L/6 + 7L/96 ≤ s.re
    -- Simplify: 1/2 + L/6 + 7L/96 = 1/2 + 16L/96 + 7L/96 = 1/2 + 23L/96
    -- We have s.re - 1/2 ≥ L/3 = 32L/96 > 23L/96
    have h1 : 1 / 3 * (L / 2) + (3 / 2 - 1 / 3) * (L / 2) / 8 = 23 * L / 96 := by ring
    have h2 : L / 3 = 32 * L / 96 := by ring
    have h3 : (23 : ℝ) * L / 96 < 32 * L / 96 := by nlinarith
    linarith
  · -- Upper bound: s.re ≤ 1/2 + 3L/4 - 7L/96
    -- Simplify: 1/2 + 3L/4 - 7L/96 = 1/2 + 72L/96 - 7L/96 = 1/2 + 65L/96
    -- We have s.re - 1/2 < 2L/3 = 64L/96 < 65L/96
    have h1 : 3 / 2 * (L / 2) - (3 / 2 - 1 / 3) * (L / 2) / 8 = 65 * L / 96 := by ring
    have h2 : 2 * L / 3 = 64 * L / 96 := by ring
    have h3 : (64 : ℝ) * L / 96 < 65 * L / 96 := by nlinarith
    linarith

/-- Key lemma: the t-coordinate lies in the band's interval.
    This follows from the floor function properties. -/
lemma t_in_band_interval (s : ℂ) (hs_lower : 1/2 < s.re) (hs_upper : s.re ≤ 1) :
    let B := coveringBand s hs_lower hs_upper
    s.im ∈ B.base.interval := by
  -- Unfold all definitions
  simp only [coveringBand, WhitneyInterval.interval, dyadicInterval, Set.mem_Icc]
  -- The interval is [m * 2^(-k) + 2^(-k)/2 - 2^(-k)/2, m * 2^(-k) + 2^(-k)/2 + 2^(-k)/2]
  -- which simplifies to [m * 2^(-k), (m+1) * 2^(-k)]
  set k := findScale s.re hs_lower hs_upper
  set L := (2 : ℝ)^(-k)
  set m := findIndex s.im k

  -- L = 2^(-k) > 0
  have hL_pos : 0 < L := zpow_pos (by norm_num : (0 : ℝ) < 2) (-k)

  -- By definition of findIndex, m = ⌊t / L⌋
  -- So m ≤ t / L < m + 1
  -- Thus m * L ≤ t < (m + 1) * L
  have h_floor_le : ↑m ≤ s.im / L := Int.floor_le (s.im / L)
  have h_lt_floor_succ : s.im / L < ↑m + 1 := Int.lt_floor_add_one (s.im / L)

  -- Multiply by L (positive) to get: m * L ≤ t ∧ t < (m+1) * L
  have h_lower : (m : ℝ) * L ≤ s.im := by
    have := mul_le_mul_of_nonneg_right h_floor_le (le_of_lt hL_pos)
    rwa [div_mul_cancel₀] at this
    exact ne_of_gt hL_pos
  have h_upper : s.im < ((m : ℝ) + 1) * L := by
    have := mul_lt_mul_of_pos_right h_lt_floor_succ hL_pos
    rwa [div_mul_cancel₀] at this
    exact ne_of_gt hL_pos

  constructor
  · -- Lower bound: m * L + L/2 - L/2 = m * L ≤ t
    linarith
  · -- Upper bound: t < (m+1) * L = m * L + L = m * L + L/2 + L/2
    linarith

/-- **THEOREM**: Interior Coverage (eliminates axiom)

Every point with 1/2 < Re(s) ≤ 1 lies in the interior of some recognizer band.

This replaces `interior_coverage_exists_axiom`. -/
theorem interior_coverage_exists (s : ℂ) (hs_lower : 1/2 < s.re) (hs_upper : s.re ≤ 1) :
    ∃ (I : WhitneyInterval) (B : RecognizerBand), B.base = I ∧ s ∈ B.interior := by
  let B := coveringBand s hs_lower hs_upper
  refine ⟨B.base, B, rfl, ?_⟩
  -- s ∈ B.interior means:
  -- B.σ_lower + B.thickness / 8 ≤ s.re ∧
  -- s.re ≤ B.σ_upper - B.thickness / 8 ∧
  -- s.im ∈ B.base.interval
  simp only [RecognizerBand.interior, Set.mem_setOf_eq]
  obtain ⟨hσ_lower, hσ_upper⟩ := σ_in_band_range s hs_lower hs_upper
  have ht := t_in_band_interval s hs_lower hs_upper
  exact ⟨hσ_lower, hσ_upper, ht⟩

/-! ## Countable Whitney Family -/

/-- The set of all dyadic Whitney intervals forms a countable family. -/
def dyadicWhitneyFamily : Set WhitneyInterval :=
  { I | ∃ (k : ℤ) (m : ℤ), I = dyadicInterval k m }

/-- The dyadic Whitney family is countable. -/
theorem dyadicWhitneyFamily_countable : Set.Countable dyadicWhitneyFamily := by
  -- ℤ × ℤ is countable, and we have a surjection onto dyadicWhitneyFamily
  have h : dyadicWhitneyFamily = Set.range (fun p : ℤ × ℤ => dyadicInterval p.1 p.2) := by
    ext I
    simp only [dyadicWhitneyFamily, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · intro ⟨k, m, hI⟩; exact ⟨(k, m), hI.symm⟩
    · intro ⟨⟨k, m⟩, hI⟩; exact ⟨k, m, hI.symm⟩
  rw [h]
  exact Set.countable_range _

/-! ## Dyadic Interval Selection for Phase Bounds

The key insight: for any γ ∈ ℝ \ {0}, we can choose a dyadic interval I
containing γ such that 2 * I.len is comparable to |γ|.

This is crucial for the phase bound argument and replaces the flawed
`whitney_interval_width` approach that attempted to derive this from
band coverage (which doesn't work for large zeros).
-/

/-- For any nonzero γ, find the scale j such that 2^(-j) ∈ [|γ|, 2|γ|). -/
def scaleForGamma (γ : ℝ) (hγ : γ ≠ 0) : ℤ :=
  -Int.ceil (Real.logb 2 |γ|)

/-- For any nonzero γ and scale j, find the index m such that γ ∈ [m·2^(-j), (m+1)·2^(-j)). -/
def indexForGamma (γ : ℝ) (j : ℤ) : ℤ :=
  Int.floor (γ / (2 : ℝ)^(-j))

/-- Construct a dyadic interval containing γ with appropriate width. -/
def dyadicIntervalForGamma (γ : ℝ) (hγ : γ ≠ 0) : WhitneyInterval :=
  let j := scaleForGamma γ hγ
  let m := indexForGamma γ j
  dyadicInterval j m

/-- **KEY LEMMA**: For any nonzero γ, there exists a dyadic interval I
    containing γ with width comparable to |γ|.

    Specifically: |γ|/2 ≤ 2 * I.len ≤ 2|γ|.

    This is weaker than what phase_bound_from_arctan needs (which requires
    2 * I.len ≥ |γ|), but we can achieve that by choosing a coarser scale. -/
lemma dyadic_interval_contains_gamma (γ : ℝ) (hγ : γ ≠ 0) :
    let I := dyadicIntervalForGamma γ hγ
    γ ∈ I.interval := by
  intro I
  -- Direct proof using floor properties
  simp only [dyadicIntervalForGamma, scaleForGamma, indexForGamma, dyadicInterval,
             WhitneyInterval.interval, Set.mem_Icc] at I ⊢
  set j := -Int.ceil (Real.logb 2 |γ|) with hj_def
  set L := (2 : ℝ)^(-j) with hL_def
  have hL_pos : 0 < L := zpow_pos (by norm_num : (0 : ℝ) < 2) (-j)
  set m := Int.floor (γ / L) with hm_def
  have h_floor_le : (m : ℝ) ≤ γ / L := Int.floor_le (γ / L)
  have h_lt_floor_succ : γ / L < (m : ℝ) + 1 := Int.lt_floor_add_one (γ / L)
  have h_lower : (m : ℝ) * L ≤ γ := by
    have := mul_le_mul_of_nonneg_right h_floor_le (le_of_lt hL_pos)
    rwa [div_mul_cancel₀] at this; exact ne_of_gt hL_pos
  have h_upper : γ < ((m : ℝ) + 1) * L := by
    have := mul_lt_mul_of_pos_right h_lt_floor_succ hL_pos
    rwa [div_mul_cancel₀] at this; exact ne_of_gt hL_pos
  constructor
  · -- m*L + L/2 - L/2 = m*L ≤ γ
    have h1 : (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 - (2 : ℝ)^(-j) / 2 = (m : ℝ) * (2 : ℝ)^(-j) := by ring
    calc (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 - (2 : ℝ)^(-j) / 2
        = (m : ℝ) * (2 : ℝ)^(-j) := h1
      _ = (m : ℝ) * L := by rw [hL_def]
      _ ≤ γ := h_lower
  · -- γ ≤ t0 + len = (m+1)*L = m*L + L/2 + L/2
    have h1 : ((m : ℝ) + 1) * (2 : ℝ)^(-j) = (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 + (2 : ℝ)^(-j) / 2 := by ring
    have h2 : γ < (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 + (2 : ℝ)^(-j) / 2 := by
      calc γ < ((m : ℝ) + 1) * L := h_upper
        _ = ((m : ℝ) + 1) * (2 : ℝ)^(-j) := by rw [hL_def]
        _ = (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 + (2 : ℝ)^(-j) / 2 := h1
    exact le_of_lt h2

/-- **THEOREM**: For any nonzero γ, we can construct a dyadic interval I such that
    γ ∈ I.interval, 2 * I.len ≥ |γ|, and 2 * I.len ≤ 4|γ|.

    This provides the geometric constraint needed for phase bounds without
    relying on the band coverage structure. -/
theorem dyadic_interval_with_width (γ : ℝ) (hγ : γ ≠ 0) :
    ∃ I : WhitneyInterval, γ ∈ I.interval ∧
      2 * I.len ≥ |γ| ∧ 2 * I.len ≤ 4 * |γ| := by
  -- Strategy: Choose j = -⌈log₂|γ|⌉ so that 2^(-j) = 2^⌈log₂|γ|⌉ ≥ |γ|
  -- From ceiling: ⌈log₂|γ|⌉ ≥ log₂|γ|, so 2^⌈log₂|γ|⌉ ≥ 2^(log₂|γ|) = |γ|
  -- Also ⌈log₂|γ|⌉ < log₂|γ| + 1, so 2^⌈log₂|γ|⌉ < 2^(log₂|γ|+1) = 2|γ|

  have h_abs_pos : 0 < |γ| := abs_pos.mpr hγ
  have two_pos : (0 : ℝ) < 2 := by norm_num
  have one_lt_two : (1 : ℝ) < 2 := by norm_num
  have one_le_two : (1 : ℝ) ≤ 2 := by norm_num

  -- Define the scale: j = -⌈log₂|γ|⌉, so -j = ⌈log₂|γ|⌉
  set j := -Int.ceil (Real.logb 2 |γ|) with hj_def
  -- L = 2^(-j) = 2^⌈log₂|γ|⌉
  set L := (2 : ℝ)^(-j) with hL_def

  have hL_pos : 0 < L := zpow_pos two_pos (-j)

  -- The key: -j = ⌈log₂|γ|⌉, and L = 2^(⌈log₂|γ|⌉)
  have h_neg_j : (-j : ℤ) = Int.ceil (Real.logb 2 |γ|) := by simp [hj_def]

  -- Lower bound: L ≥ |γ|
  -- From ⌈log₂|γ|⌉ ≥ log₂|γ| and monotonicity of 2^x
  have h_L_lower : L ≥ |γ| := by
    have h_ceil : Real.logb 2 |γ| ≤ Int.ceil (Real.logb 2 |γ|) := Int.le_ceil _
    -- 2^⌈log₂|γ|⌉ ≥ 2^(log₂|γ|) = |γ|
    have h1 : (2 : ℝ) ^ (Int.ceil (Real.logb 2 |γ|) : ℝ) ≥ (2 : ℝ) ^ (Real.logb 2 |γ|) := by
      exact Real.rpow_le_rpow_of_exponent_le one_le_two h_ceil
    have h2 : (2 : ℝ) ^ (Real.logb 2 |γ|) = |γ| := by
      exact Real.rpow_logb two_pos (ne_of_gt one_lt_two) h_abs_pos
    rw [h2] at h1
    -- Connect to L
    have h3 : L = (2 : ℝ) ^ (Int.ceil (Real.logb 2 |γ|) : ℝ) := by
      rw [hL_def, h_neg_j, Real.rpow_intCast]
    rw [h3]
    exact h1

  -- Upper bound: L < 2|γ|
  -- From ⌈log₂|γ|⌉ < log₂|γ| + 1 and strict monotonicity
  have h_L_upper : L < 2 * |γ| := by
    have h_ceil_lt : (Int.ceil (Real.logb 2 |γ|) : ℝ) < Real.logb 2 |γ| + 1 := Int.ceil_lt_add_one _
    -- 2^⌈log₂|γ|⌉ < 2^(log₂|γ|+1) = 2·|γ|
    have h1 : (2 : ℝ) ^ (Int.ceil (Real.logb 2 |γ|) : ℝ) < (2 : ℝ) ^ (Real.logb 2 |γ| + 1) := by
      exact Real.rpow_lt_rpow_of_exponent_lt one_lt_two h_ceil_lt
    have h2 : (2 : ℝ) ^ (Real.logb 2 |γ| + 1) = 2 * |γ| := by
      rw [Real.rpow_add two_pos, Real.rpow_one, Real.rpow_logb two_pos (ne_of_gt one_lt_two) h_abs_pos]
      ring
    rw [h2] at h1
    have h3 : L = (2 : ℝ) ^ (Int.ceil (Real.logb 2 |γ|) : ℝ) := by
      rw [hL_def, h_neg_j, Real.rpow_intCast]
    rw [h3]
    exact h1

  -- Choose index m and construct interval
  set m := Int.floor (γ / L) with hm_def
  let I : WhitneyInterval := dyadicInterval j m

  use I

  constructor
  · -- γ ∈ I.interval
    simp only [dyadicInterval, WhitneyInterval.interval, Set.mem_Icc]
    have h_floor_le : (m : ℝ) ≤ γ / L := Int.floor_le (γ / L)
    have h_lt_floor_succ : γ / L < (m : ℝ) + 1 := Int.lt_floor_add_one (γ / L)
    have h_lower : (m : ℝ) * L ≤ γ := by
      have := mul_le_mul_of_nonneg_right h_floor_le (le_of_lt hL_pos)
      rwa [div_mul_cancel₀] at this; exact ne_of_gt hL_pos
    have h_upper : γ < ((m : ℝ) + 1) * L := by
      have := mul_lt_mul_of_pos_right h_lt_floor_succ hL_pos
      rwa [div_mul_cancel₀] at this; exact ne_of_gt hL_pos
    constructor
    · -- Lower bound
      have h1 : (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 - (2 : ℝ)^(-j) / 2 = (m : ℝ) * (2 : ℝ)^(-j) := by ring
      calc (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 - (2 : ℝ)^(-j) / 2
          = (m : ℝ) * (2 : ℝ)^(-j) := h1
        _ = (m : ℝ) * L := by rw [hL_def]
        _ ≤ γ := h_lower
    · -- Upper bound: γ ≤ I.t0 + I.len
      have h1 : ((m : ℝ) + 1) * (2 : ℝ)^(-j) = (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 + (2 : ℝ)^(-j) / 2 := by ring
      have h2 : (m : ℝ) * (2 : ℝ)^(-j) + (2 : ℝ)^(-j) / 2 + (2 : ℝ)^(-j) / 2 = I.t0 + I.len := by
        simp only [I, dyadicInterval]
      rw [← h2, ← h1, ← hL_def]
      exact le_of_lt h_upper

  constructor
  · -- 2 * I.len ≥ |γ|
    have h1 : 2 * I.len = (2 : ℝ)^(-j) := by simp only [I, dyadicInterval]; ring
    rw [h1, ← hL_def]
    exact h_L_lower
  · -- 2 * I.len ≤ 4 * |γ|
    have h1 : 2 * I.len = (2 : ℝ)^(-j) := by simp only [I, dyadicInterval]; ring
    rw [h1, ← hL_def]
    have h2 : L < 2 * |γ| := h_L_upper
    linarith [h_abs_pos]

end RiemannRecognitionGeometry
