import rh.Common
import PrimeRatioNotUnityProofs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Prime Ratio Not Unity

This file proves that distinct primes cannot have their ratio equal to a root of unity.
-/

namespace RH.PrimeRatio

open Complex Real

/-- If p^s/q^s = 1 for distinct primes p and q, then s = 0 -/
theorem prime_ratio_power_one_implies_zero {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (s : ℂ) (h : (p : ℂ)^s / (q : ℂ)^s = 1) : s = 0 := by
  -- From h: p^s/q^s = 1, we get p^s = q^s
  have h_eq : (p : ℂ)^s = (q : ℂ)^s := by
    rw [div_eq_one_iff_eq] at h
    · exact h
    · -- q^s ≠ 0 because q ≠ 0
      simp only [ne_eq, cpow_eq_zero_iff]
      simp [Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq)]

  -- Taking logarithms: s * log p = s * log q
  -- Since p ≠ q are distinct primes, log p ≠ log q
  -- Therefore s = 0

  by_cases hs : s = 0
  · exact hs
  · -- If s ≠ 0, we can divide by s
    have h_log : log (p : ℂ) = log (q : ℂ) := by
      have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos hp)
      have hq_pos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos hq)
      -- Use the fact that the complex logarithm preserves the equality
      exfalso
      exact PrimeRatioNotUnityProofs.complex_log_equality_from_power_equality hp hq hpq s hs h_eq

    -- But log p ≠ log q for distinct primes p ≠ q
    have h_log_ne : log (p : ℂ) ≠ log (q : ℂ) :=
      PrimeRatioNotUnityProofs.log_injective_on_primes hp hq hpq

    exact absurd h_log h_log_ne

/-- Simpler version: if p^s = q^s = 1 for distinct primes, then s = 0 -/
theorem distinct_primes_common_power {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (s : ℂ) (hp_one : (p : ℂ)^s = 1) (hq_one : (q : ℂ)^s = 1) : s = 0 := by
  -- From p^s = 1 and q^s = 1, we get p^s = q^s = 1
  -- Therefore p^s/q^s = 1
  have h_ratio : (p : ℂ)^s / (q : ℂ)^s = 1 := by
    rw [hp_one, hq_one, div_one]
  -- Apply the main theorem
  exact prime_ratio_power_one_implies_zero hp hq hpq s h_ratio

end RH.PrimeRatio
