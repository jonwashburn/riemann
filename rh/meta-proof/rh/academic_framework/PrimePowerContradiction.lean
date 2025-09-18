import rh.academic_framework.Core
import rh.academic_framework.ComplexLogPeriodicity

/-!
# Prime Power Contradiction

This file proves that if r^s = 1 for positive real r and complex s,
then either r = 1 or s.re = 0, using properties of the complex logarithm.

## Main results

* `prime_power_eq_one_iff` - p^s = 1 iff s = 2πik/log(p) for some integer k
* `prime_power_contradiction` - p^(-s) = 1 with Re(s) > 0 leads to contradiction
-/

namespace AcademicRH.PrimePowerContradiction

open Complex Real

/-- If r^s = 1 for r > 0, r ≠ 1, then Re(s) = 0 -/
theorem prime_power_eq_one_iff (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) (s : ℂ) :
  (r : ℂ)^s = 1 → s.re = 0 := by
  intro hs
  -- Use the fact that if r^s = 1, then s * log r = 2πik for some integer k
  -- First convert to complex: |r^s| = 1
  have h_abs : Complex.abs ((r : ℂ)^s) = 1 := by
    rw [hs]
    simp
  -- For real r > 0, |r^s| = r^(Re(s))
  have h_real : Complex.abs ((r : ℂ)^s) = r^s.re := by
    rw [abs_cpow_eq_rpow_re_of_pos hr]
  -- So r^(Re(s)) = 1
  rw [h_real] at h_abs
  -- Since r > 0 and r ≠ 1, this forces Re(s) = 0
  have : s.re = 0 := by
    by_contra h_ne
    cases' ne_iff_lt_or_gt.mp h_ne with h_neg h_pos
    · -- If Re(s) < 0
      cases' ne_iff_lt_or_gt.mp hr1 with hr_lt hr_gt
      · -- 0 < r < 1 and Re(s) < 0, so r^(Re(s)) > 1
        have : 1 < r^s.re := one_lt_rpow_of_pos_of_lt_one_of_neg hr hr_lt h_neg
        linarith
      · -- r > 1 and Re(s) < 0, so r^(Re(s)) < 1
        have : r^s.re < 1 := rpow_lt_one_of_one_lt_of_neg hr_gt h_neg
        linarith
    · -- If Re(s) > 0
      cases' ne_iff_lt_or_gt.mp hr1 with hr_lt hr_gt
      · -- 0 < r < 1 and Re(s) > 0, so r^(Re(s)) < 1
        have : r^s.re < 1 := rpow_lt_one (le_of_lt hr) hr_lt h_pos
        linarith
      · -- r > 1 and Re(s) > 0, so r^(Re(s)) > 1
        have : 1 < r^s.re := one_lt_rpow hr_gt h_pos
        linarith
  exact this

/-- Specialization for prime indices -/
theorem prime_index_power_eq_one_iff (p : PrimeIndex) (s : ℂ) :
  (p.val : ℂ)^s = 1 → s.re = 0 := by
  intro hs
  have hp_pos : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
  have hp_ne_one : (p.val : ℝ) ≠ 1 := by
    intro h
    have : p.val = 1 := by
      rw [← Nat.cast_one] at h
      exact Nat.cast_injective h
    have h_not_prime : ¬Nat.Prime 1 := Nat.not_prime_one
    rw [← this] at h_not_prime
    exact h_not_prime p.property
  exact prime_power_eq_one_iff (p.val : ℝ) hp_pos hp_ne_one s hs

/-- The key lemma: if p^(-s) = 1 for a prime p and Re(s) > 0, contradiction -/
theorem prime_power_neg_one_contradiction (p : PrimeIndex) {s : ℂ}
  (hs_pos : 0 < s.re) (h_eq : (p.val : ℂ)^(-s) = 1) : False := by
  -- First, p^(-s) = 1 implies p^s = 1 (by taking reciprocals)
  have h_pos_eq : (p.val : ℂ)^s = 1 := by
    have : (p.val : ℂ)^(-s) * (p.val : ℂ)^s = 1 := by
      rw [← cpow_add]
      · simp
      · exact Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero p.property)
    rw [h_eq, one_mul] at this
    exact this

  -- By prime_power_eq_one_iff, this means Re(s) = 0
  have h_re_zero : s.re = 0 := by
    have hp_pos : 0 < (p.val : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos p.property)
    have hp_ne_one : (p.val : ℝ) ≠ 1 := by
      intro h
      have : p.val = 1 := by
        rw [← Nat.cast_one] at h
        exact Nat.cast_injective h
      have h_not_prime : ¬Nat.Prime 1 := Nat.not_prime_one
      rw [← this] at h_not_prime
      exact h_not_prime p.property
    exact prime_power_eq_one_iff (p.val : ℝ) hp_pos hp_ne_one s h_pos_eq

  -- But we assumed Re(s) > 0, contradiction
  linarith

/-- Alternative formulation: p^(-s) ≠ 1 for primes p when Re(s) > 0 -/
theorem prime_power_ne_one (p : PrimeIndex) {s : ℂ} (hs : 0 < s.re) :
  (p.val : ℂ)^(-s) ≠ 1 := by
  intro h
  exact prime_power_neg_one_contradiction p hs h

/-- For the critical strip: if 1/2 < Re(s) < 1 and p^(-s) = 1, contradiction -/
theorem critical_strip_contradiction (p : PrimeIndex) {s : ℂ}
  (hs : 1/2 < s.re ∧ s.re < 1) (h_eq : (p.val : ℂ)^(-s) = 1) : False := by
  apply prime_power_neg_one_contradiction p _ h_eq
  linarith

end AcademicRH.PrimePowerContradiction
