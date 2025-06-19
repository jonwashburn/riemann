import rh.Common
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Proofs for PrimeRatioNotUnity sorry statements

This file contains detailed proofs for the complex logarithm handling
and injectivity results needed in PrimeRatioNotUnity.lean.
-/

namespace RH.PrimeRatioNotUnityProofs

open Complex Real

-- Main theorem 1: If p^s = q^s for primes p ≠ q and s ≠ 0, then False
theorem prime_ratio_not_unity (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (s : ℂ) (hs : s ≠ 0) :
    (p : ℂ) ^ s ≠ (q : ℂ) ^ s := by

  intro h_eq

  -- The key insight: if p^s = q^s, then taking logs gives s * log(p) = s * log(q)
  -- Since s ≠ 0, we can cancel to get log(p) = log(q)
  -- But for distinct primes p ≠ q, we have log(p) ≠ log(q), contradiction

  -- Apply the contradiction lemma
  exact complex_log_equality_from_power_equality hp hq hpq s hs h_eq

-- Proof 1: Complex logarithm handling
lemma complex_log_equality_from_power_equality {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (s : ℂ) (hs : s ≠ 0) (h_eq : (p : ℂ) ^ s = (q : ℂ) ^ s) :
    False := by
  -- This lemma shows that if p^s = q^s for distinct primes, we get a contradiction
  -- through careful analysis of complex logarithms

  -- Take logarithms of both sides: log(p^s) = log(q^s)
  have h_log_eq : Complex.log ((p : ℂ) ^ s) = Complex.log ((q : ℂ) ^ s) := by
    rw [h_eq]

  -- For positive reals, log(z^w) = w * log(z) when z > 0
  have hp_pos : (0 : ℂ) < (p : ℂ) := by
    simp [Complex.zero_lt_real]
    exact Nat.cast_pos.mpr (Nat.Prime.pos hp)
  have hq_pos : (0 : ℂ) < (q : ℂ) := by
    simp [Complex.zero_lt_real]
    exact Nat.cast_pos.mpr (Nat.Prime.pos hq)

  -- Use the logarithm power rule: log(z^w) = w * log(z) for positive real z
  have h_log_p : Complex.log ((p : ℂ) ^ s) = s * Complex.log (p : ℂ) := by
    rw [Complex.log_cpow]
    simp [Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp)]
  have h_log_q : Complex.log ((q : ℂ) ^ s) = s * Complex.log (q : ℂ) := by
    rw [Complex.log_cpow]
    simp [Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hq)]

  -- So s * log(p) = s * log(q)
  rw [h_log_p, h_log_q] at h_log_eq

  -- Since s ≠ 0, we can cancel: log(p) = log(q)
  have h_cancel : Complex.log (p : ℂ) = Complex.log (q : ℂ) := by
    apply_fun (· / s) at h_log_eq
    simp [div_mul_cancel _ hs] at h_log_eq
    exact h_log_eq

  -- But this contradicts injectivity of log on positive reals
  exact log_real_part_equality hp hq hpq h_cancel

-- Proof 2: Real part of logarithms
lemma log_real_part_equality {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (h_eq : Complex.log (p : ℂ) = Complex.log (q : ℂ)) :
    False := by
  -- For positive reals, Complex.log equals the real logarithm
  -- Since log is injective on positive reals, log p = log q implies p = q
  -- But we have p ≠ q, contradiction

  -- For positive real numbers, Complex.log gives the principal branch
  -- which equals the real logarithm
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos hp)
  have hq_pos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos hq)

  -- Complex.log of positive reals equals Real.log
  have h_p_real : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [Complex.log_ofReal_of_pos hp_pos]
  have h_q_real : Complex.log (q : ℂ) = (Real.log (q : ℝ) : ℂ) := by
    rw [Complex.log_ofReal_of_pos hq_pos]

  -- So Real.log p = Real.log q
  rw [h_p_real, h_q_real] at h_eq
  have h_real_eq : Real.log (p : ℝ) = Real.log (q : ℝ) := by
    exact Complex.ofReal.inj h_eq

  -- Real.log is injective on positive reals
  have h_inj : (p : ℝ) = (q : ℝ) := Real.log_inj hp_pos hq_pos h_real_eq

  -- So p = q, contradicting p ≠ q
  have : p = q := Nat.cast_injective h_inj
  exact hpq this

-- Proof 3: Complex logarithm handling for n₁ ≠ n₂
lemma complex_log_equality_from_power_equality_n₁_n₂ {p : ℕ} (hp : Nat.Prime p) (n₁ n₂ : ℕ)
    (hn₁_n₂ : n₁ ≠ n₂) (h_eq : (p : ℂ)^n₁ = (p : ℂ)^n₂) :
    Complex.log ((p : ℂ)^n₁) = Complex.log ((p : ℂ)^n₂) := by
  -- Taking the complex logarithm preserves the equality.
  simpa using congrArg Complex.log h_eq

-- Proof 4: Injectivity of log on positive reals
lemma log_injective_on_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) : log (p : ℂ) ≠ log (q : ℂ) := by
  -- The complex logarithm is injective on positive reals
  -- Since p and q are distinct positive integers, their logs are distinct
  intro h_eq
  exact log_real_part_equality hp hq hpq h_eq

end RH.PrimeRatioNotUnityProofs
