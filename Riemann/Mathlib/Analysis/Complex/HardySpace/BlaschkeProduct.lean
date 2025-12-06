
import Riemann.Mathlib.Analysis.Complex.HardySpace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Blaschke Products

This file develops the theory of Blaschke factors and Blaschke products,
which are the building blocks for factorizing bounded analytic functions.

## Main definitions

* `Complex.blaschkeFactor` : The Blaschke factor B_a(z) for a point a in the disc

## Main results

* `Complex.blaschkeFactor_analyticOn` : Blaschke factors are analytic on the disc
* `Complex.blaschkeFactor_norm_eq_one_on_circle` : |B_a(z)| = 1 for |z| = 1
* `Complex.blaschkeFactor_norm_lt_one_in_disc` : |B_a(z)| < 1 for |z| < 1

## References

* Duren, P.L., "Theory of H^p Spaces", Chapter 2
* Garnett, J.B., "Bounded Analytic Functions", Chapter II
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Blaschke factor -/

/-- The Blaschke factor for a point a in the unit disc.
This is the automorphism of the unit disc that maps a to 0 and has |B_a(z)| = |z| on the circle.
For a = 0, we define B_0(z) = z. -/
def blaschkeFactor (a : ℂ) (z : ℂ) : ℂ :=
  if a = 0 then z else (‖a‖ / a) * (a - z) / (1 - starRingEnd ℂ a * z)

/-- The Blaschke factor is analytic on the unit disc. -/
lemma blaschkeFactor_analyticOn {a : ℂ} (ha : ‖a‖ < 1) :
    AnalyticOn ℂ (blaschkeFactor a) unitDisc := by
  intro z hz
  unfold blaschkeFactor
  by_cases ha0 : a = 0
  · simp only [ha0, ↓reduceIte]
    exact analyticWithinAt_id
  · simp only [ha0, ↓reduceIte]
    have h_denom_ne : 1 - starRingEnd ℂ a * z ≠ 0 := by
      intro heq
      have h1 : starRingEnd ℂ a * z = 1 := (sub_eq_zero.mp heq).symm
      have h2 : ‖starRingEnd ℂ a * z‖ = 1 := by rw [h1]; simp
      rw [norm_mul, Complex.norm_conj] at h2
      have hz_lt : ‖z‖ < 1 := hz
      have h_prod_lt : ‖a‖ * ‖z‖ < 1 := by
        calc ‖a‖ * ‖z‖ ≤ ‖a‖ := by nlinarith [norm_nonneg z]
          _ < 1 := ha
      linarith
    have h_num : AnalyticAt ℂ (fun w => a - w) z := analyticAt_const.sub analyticAt_id
    have h_denom : AnalyticAt ℂ (fun w => 1 - starRingEnd ℂ a * w) z :=
      analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
    have h_full : AnalyticAt ℂ (fun w => (↑‖a‖ / a) * (a - w) / (1 - starRingEnd ℂ a * w)) z := by
      have h1 : AnalyticAt ℂ (fun w => (↑‖a‖ / a) * (a - w)) z :=
        analyticAt_const.mul h_num
      exact h1.div h_denom h_denom_ne
    exact h_full.analyticWithinAt

/-- The Blaschke factor has modulus 1 on the unit circle. -/
lemma blaschkeFactor_norm_eq_one_on_circle {a : ℂ} (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖blaschkeFactor a z‖ = 1 := by
  unfold blaschkeFactor
  split_ifs with ha0
  · simp [hz]
  · -- Standard computation: |a-z|² = |1 - āz|² when |z| = 1
    have h_denom_ne : 1 - starRingEnd ℂ a * z ≠ 0 := by
      intro heq
      have h1 : starRingEnd ℂ a * z = 1 := (sub_eq_zero.mp heq).symm
      have h2 : ‖starRingEnd ℂ a * z‖ = 1 := by rw [h1]; simp
      rw [norm_mul, Complex.norm_conj] at h2
      have h3 : ‖a‖ * ‖z‖ = 1 := h2
      rw [hz, mul_one] at h3
      linarith
    have hz_normSq : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz, one_pow]
    have h_normSq_eq : Complex.normSq (a - z) = Complex.normSq (1 - starRingEnd ℂ a * z) := by
      have h_re_eq : (a * starRingEnd ℂ z).re = (starRingEnd ℂ a * z).re := by
        rw [← Complex.conj_re (a * starRingEnd ℂ z)]
        simp only [map_mul, Complex.conj_conj]
      simp only [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_mul, Complex.normSq_conj,
        hz_normSq, mul_one]
      simp only [one_mul, map_mul, Complex.conj_conj]
      linarith [h_re_eq]
    have h_norms_eq : ‖a - z‖ = ‖1 - starRingEnd ℂ a * z‖ := by
      have h1 : ‖a - z‖ ^ 2 = ‖1 - starRingEnd ℂ a * z‖ ^ 2 := by
        simp only [← Complex.normSq_eq_norm_sq]
        exact h_normSq_eq
      have h2 := norm_nonneg (a - z)
      have h3 := norm_nonneg (1 - starRingEnd ℂ a * z)
      nlinarith [sq_nonneg (‖a - z‖ - ‖1 - starRingEnd ℂ a * z‖),
        sq_nonneg (‖a - z‖ + ‖1 - starRingEnd ℂ a * z‖)]
    have ha_ne : ‖a‖ ≠ 0 := by simp [ha0]
    have h_num_ne : ‖a - z‖ ≠ 0 := by
      intro heq
      rw [norm_eq_zero, sub_eq_zero] at heq
      rw [heq, hz] at ha
      linarith
    simp only [norm_div, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
    rw [h_norms_eq]
    field_simp [ha_ne, h_num_ne, h_denom_ne]

/-- The Blaschke factor has modulus < 1 inside the disc. -/
lemma blaschkeFactor_norm_lt_one_in_disc {a : ℂ} (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖blaschkeFactor a z‖ < 1 := by
  unfold blaschkeFactor
  split_ifs with ha0
  · simp [hz]
  · have h_denom_ne : 1 - starRingEnd ℂ a * z ≠ 0 := by
      intro heq
      have h1 : starRingEnd ℂ a * z = 1 := (sub_eq_zero.mp heq).symm
      have h2 : ‖starRingEnd ℂ a * z‖ = 1 := by rw [h1]; simp
      rw [norm_mul, Complex.norm_conj] at h2
      have h3 : ‖a‖ * ‖z‖ = 1 := h2
      have h4 : ‖a‖ * ‖z‖ < 1 := by
        calc ‖a‖ * ‖z‖ < 1 * ‖z‖ := by nlinarith [norm_nonneg z]
          _ = ‖z‖ := one_mul _
          _ < 1 := hz
      linarith
    have h_normSq_diff : Complex.normSq (a - z) - Complex.normSq (1 - starRingEnd ℂ a * z) =
        (Complex.normSq a - 1) * (1 - Complex.normSq z) := by
      have h_re_eq : (a * starRingEnd ℂ z).re = (starRingEnd ℂ a * z).re := by
        rw [← Complex.conj_re (a * starRingEnd ℂ z)]
        simp only [map_mul, Complex.conj_conj]
      simp only [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_conj, one_mul, map_mul, Complex.conj_conj]
      ring
    have ha_normSq : Complex.normSq a < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have h1 : ‖a‖ ^ 2 < 1 ^ 2 := sq_lt_sq' (by linarith [norm_nonneg a]) ha
      linarith
    have hz_normSq : Complex.normSq z < 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have h1 : ‖z‖ ^ 2 < 1 ^ 2 := sq_lt_sq' (by linarith [norm_nonneg z]) hz
      linarith
    have h_diff_neg : Complex.normSq (a - z) - Complex.normSq (1 - starRingEnd ℂ a * z) < 0 := by
      rw [h_normSq_diff]
      apply mul_neg_of_neg_of_pos <;> linarith
    have h_normSq_lt : Complex.normSq (a - z) < Complex.normSq (1 - starRingEnd ℂ a * z) := by
      linarith
    have h_norm_lt : ‖a - z‖ < ‖1 - starRingEnd ℂ a * z‖ := by
      have h1 : ‖a - z‖ ^ 2 < ‖1 - starRingEnd ℂ a * z‖ ^ 2 := by
        simp only [← Complex.normSq_eq_norm_sq]
        exact h_normSq_lt
      have h2 := norm_nonneg (a - z)
      have h3 := norm_nonneg (1 - starRingEnd ℂ a * z)
      nlinarith [sq_nonneg (‖a - z‖ - ‖1 - starRingEnd ℂ a * z‖),
        sq_nonneg (‖a - z‖ + ‖1 - starRingEnd ℂ a * z‖)]
    have ha_ne : ‖a‖ ≠ 0 := fun h => ha0 (norm_eq_zero.mp h)
    simp only [norm_div, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
    have h1 : ‖a‖ / ‖a‖ = 1 := div_self ha_ne
    calc ‖a‖ / ‖a‖ * ‖a - z‖ / ‖1 - starRingEnd ℂ a * z‖
        = 1 * ‖a - z‖ / ‖1 - starRingEnd ℂ a * z‖ := by rw [h1]
      _ = ‖a - z‖ / ‖1 - starRingEnd ℂ a * z‖ := by ring
      _ < 1 := by rw [div_lt_one (norm_pos_iff.mpr h_denom_ne)]; exact h_norm_lt

/-- The Blaschke factor maps the disc to the disc. -/
lemma blaschkeFactor_mapsTo {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (blaschkeFactor a) unitDisc unitDisc := by
  intro z hz
  simp only [mem_unitDisc]
  exact blaschkeFactor_norm_lt_one_in_disc ha hz

/-- The Blaschke factor vanishes exactly at a. -/
lemma blaschkeFactor_zero_iff {a : ℂ} (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    blaschkeFactor a z = 0 ↔ z = a := by
  unfold blaschkeFactor
  split_ifs with ha0
  · simp [ha0]
  · have h_denom_ne : 1 - starRingEnd ℂ a * z ≠ 0 := by
      intro heq
      have h1 : starRingEnd ℂ a * z = 1 := (sub_eq_zero.mp heq).symm
      have h2 : ‖starRingEnd ℂ a * z‖ = 1 := by rw [h1]; simp
      rw [norm_mul, Complex.norm_conj] at h2
      have h3 : ‖a‖ * ‖z‖ = 1 := h2
      have h4 : ‖a‖ * ‖z‖ < 1 := by
        calc ‖a‖ * ‖z‖ < 1 * ‖z‖ := by nlinarith [norm_nonneg z]
          _ = ‖z‖ := one_mul _
          _ < 1 := hz
      linarith
    constructor
    · intro h
      rw [div_eq_zero_iff] at h
      rcases h with (h1 | h2)
      · rw [mul_eq_zero] at h1
        rcases h1 with (h3 | h4)
        · rw [div_eq_zero_iff] at h3
          rcases h3 with (h5 | h6)
          · simp only [Complex.ofReal_eq_zero, norm_eq_zero] at h5
            exact absurd h5 ha0
          · exact absurd h6 ha0
        · exact (sub_eq_zero.mp h4).symm
      · exact absurd h2 h_denom_ne
    · intro h
      rw [div_eq_zero_iff]
      left
      rw [mul_eq_zero]
      right
      rw [h, sub_self]

/-- The Blaschke factor is nonzero when z ≠ a. -/
lemma blaschkeFactor_ne_zero_of_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) (hne : z ≠ a) :
    blaschkeFactor a z ≠ 0 := by
  intro h
  have := (blaschkeFactor_zero_iff ha hz).mp h
  exact hne this

/-- For Blaschke factors with power: B_a(z)^n ≠ 0 when z ≠ a or n = 0. -/
lemma blaschkeFactor_pow_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) {n : ℕ}
    (h : z ≠ a ∨ n = 0) :
    (blaschkeFactor a z) ^ n ≠ 0 := by
  rcases h with hne | hn0
  · exact pow_ne_zero n (blaschkeFactor_ne_zero_of_ne ha hz hne)
  · simp [hn0]

/-- A tprod containing a zero term equals zero. -/
lemma tprod_eq_zero_of_eq_zero {α : Type*} [CommMonoidWithZero α] [TopologicalSpace α]
    [T2Space α] {f : ℕ → α} (n : ℕ) (hfn : f n = 0) :
    ∏' k, f k = 0 := by
  have h : ∃ k, f k = 0 := ⟨n, hfn⟩
  exact tprod_of_exists_eq_zero h

end Complex
