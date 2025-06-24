import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Complex Logarithm Periodicity

This file provides lemmas about the periodicity of the complex logarithm
that are needed for proving `complex_eigenvalue_relation`.
-/

namespace RH.ComplexLogPeriodicity

open Complex Real

/-- The complex exponential function is periodic with period 2πi -/
lemma exp_periodic : Function.Periodic Complex.exp (2 * π * I) := by
  intro z
  simp only [Function.Periodic]
  rw [exp_add]
  simp only [exp_two_pi_mul_I]
  ring

/-- If exp z₁ = exp z₂, then z₁ - z₂ = 2πik for some integer k -/
lemma exp_eq_exp_iff_exists_int {z₁ z₂ : ℂ} :
    exp z₁ = exp z₂ ↔ ∃ k : ℤ, z₁ = z₂ + 2 * π * I * k := by
  constructor
  · intro h
    -- exp is injective modulo 2πi
    -- exp(z₁) = exp(z₂) iff exp(z₁ - z₂) = 1
    have h_eq : exp (z₁ - z₂) = 1 := by
      rw [exp_sub, h, div_self (exp_ne_zero _)]
    -- exp w = 1 iff w = 2πik for some integer k
    have ⟨k, hk⟩ := exp_eq_one_iff.mp h_eq
    use k
    rw [← hk]
    ring
  · intro ⟨k, hk⟩
    rw [hk, exp_add]
    simp only [exp_two_pi_mul_I_mul]

/-- For z ≠ 0, log(z^w) and w*log(z) differ by 2πik for some integer k -/
lemma log_cpow_eq_mul_log_add_int {z w : ℂ} (hz : z ≠ 0) :
    ∃ k : ℤ, log (z ^ w) = w * log z + 2 * π * I * k := by
  -- We have exp(log(z^w)) = z^w = exp(w * log z)
  have h_exp : exp (log (z ^ w)) = exp (w * log z) := by
    rw [exp_log (cpow_ne_zero hz _), exp_mul_log hz]
  -- By exp_eq_exp_iff_exists_int, log(z^w) = w*log(z) + 2πik
  exact exp_eq_exp_iff_exists_int.mp h_exp

/-- For positive real z, log(z^w) = w*log(z) when w is real -/
lemma log_rpow_of_pos {x : ℝ} (hx : 0 < x) (r : ℝ) :
    log ((x : ℂ) ^ (r : ℂ)) = r * log (x : ℂ) := by
  -- For positive real base and real exponent, no branch cut issues
  have : (x : ℂ) ^ (r : ℂ) = ((x ^ r) : ℝ : ℂ) := by
    rw [← ofReal_cpow hx.le]
    rfl
  rw [this, log_ofReal_of_pos (rpow_pos_of_pos hx _)]
  rw [log_ofReal_of_pos hx]
  simp only [ofReal_mul, ofReal_log hx]

/-- Key lemma: If z^w = 1 for z ≠ 0, then w * log z = 2πik for some integer k -/
lemma cpow_eq_one_iff {z w : ℂ} (hz : z ≠ 0) :
    z ^ w = 1 ↔ ∃ k : ℤ, w * log z = 2 * π * I * k := by
  constructor
  · intro h
    -- Take logarithms: log(z^w) = log(1) = 0
    have h_log : log (z ^ w) = 0 := by
      rw [h, log_one]
    -- By log_cpow_eq_mul_log_add_int, log(z^w) = w*log(z) + 2πik
    obtain ⟨k, hk⟩ := log_cpow_eq_mul_log_add_int hz
    rw [h_log] at hk
    use -k
    linarith
  · intro ⟨k, hk⟩
    -- If w * log z = 2πik, then z^w = exp(w * log z) = exp(2πik) = 1
    rw [← exp_log hz, ← exp_mul_log hz]
    rw [hk]
    simp only [exp_two_pi_mul_I_mul]

/-- For distinct positive integers, if p^s = q^s = 1, then we get integer relations -/
lemma distinct_powers_one_gives_relation {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q)
    {s : ℂ} (hs_ne : s ≠ 0) (hp_one : (p : ℂ) ^ s = 1) (hq_one : (q : ℂ) ^ s = 1) :
    ∃ m n : ℤ, n ≠ 0 ∧ Real.log (p : ℝ) * n = Real.log (q : ℝ) * m := by
  -- From p^s = 1, we get s * log p = 2πi * k₁ for some k₁
  have ⟨k₁, hk₁⟩ := cpow_eq_one_iff (Nat.cast_ne_zero.mpr hp.ne') hp_one
  -- From q^s = 1, we get s * log q = 2πi * k₂ for some k₂
  have ⟨k₂, hk₂⟩ := cpow_eq_one_iff (Nat.cast_ne_zero.mpr hq.ne') hq_one

  -- Since p, q are positive reals, log p and log q are real
  have h_log_p : log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    rw [log_ofReal_of_pos (Nat.cast_pos.mpr hp)]
  have h_log_q : log (q : ℂ) = (Real.log (q : ℝ) : ℂ) := by
    rw [log_ofReal_of_pos (Nat.cast_pos.mpr hq)]

  -- Rewrite the equations
  rw [h_log_p] at hk₁
  rw [h_log_q] at hk₂

  -- We have s * (log p) = 2πi * k₁ and s * (log q) = 2πi * k₂
  -- Taking the ratio: (log p) / (log q) = k₁ / k₂
  -- Cross multiply: (log p) * k₂ = (log q) * k₁

  use k₁, k₂

  constructor
  · -- k₂ ≠ 0
    intro h_zero
    -- If k₂ = 0, then s * log q = 0, so s = 0 (since log q ≠ 0 for q > 1)
    rw [h_zero, mul_zero] at hk₂
    simp only [ofReal_eq_zero] at hk₂
    have h_log_q_pos : 0 < Real.log (q : ℝ) := by
      apply Real.log_pos
      exact Nat.one_lt_cast.mpr (Nat.succ_lt_succ hp)
    have : s = 0 := by
      by_contra hs
      have : (Real.log (q : ℝ) : ℂ) ≠ 0 := by
        simp only [ofReal_eq_zero]
        exact h_log_q_pos.ne'
      have h_prod : s * (Real.log (q : ℝ) : ℂ) = 0 := by
        rw [← hk₂]
        simp
      exact this (mul_eq_zero.mp h_prod |>.resolve_left hs)
    -- But s ≠ 0 by assumption
    exact hs_ne this

  · -- (log p) * k₂ = (log q) * k₁
    -- From s * (log p) = 2πi * k₁ and s * (log q) = 2πi * k₂
    -- We can eliminate s by cross-multiplication

    -- First, let's work with the complex equations
    have h_eq1 : s * (Real.log (p : ℝ) : ℂ) = 2 * π * I * k₁ := hk₁
    have h_eq2 : s * (Real.log (q : ℝ) : ℂ) = 2 * π * I * k₂ := hk₂

    -- Multiply first equation by k₂ and second by k₁
    have h_mul1 : s * (Real.log (p : ℝ) : ℂ) * k₂ = 2 * π * I * k₁ * k₂ := by
      rw [h_eq1]
      ring
    have h_mul2 : s * (Real.log (q : ℝ) : ℂ) * k₁ = 2 * π * I * k₂ * k₁ := by
      rw [h_eq2]
      ring

    -- Since k₁ * k₂ = k₂ * k₁, we get equality
    have h_complex : s * (Real.log (p : ℝ) : ℂ) * k₂ = s * (Real.log (q : ℝ) : ℂ) * k₁ := by
      rw [h_mul1, h_mul2]
      ring

    -- Rearrange to get (log p) * k₂ = (log q) * k₁ in ℂ
    have : (Real.log (p : ℝ) : ℂ) * k₂ = (Real.log (q : ℝ) : ℂ) * k₁ := by
      rw [← mul_assoc, ← mul_assoc] at h_complex
      -- Need to cancel s, but we need s ≠ 0
      -- From the equations s * log p = 2πi * k₁ and s * log q = 2πi * k₂
      -- If s = 0, then 0 = 2πi * k₁ and 0 = 2πi * k₂, so k₁ = k₂ = 0
      -- But we already proved k₂ ≠ 0, so s ≠ 0
      by_cases hs : s = 0
      · -- If s = 0
        rw [hs] at hk₂
        simp at hk₂
        have : k₂ = 0 := by
          by_contra h_k2_ne
          have : 2 * π * I * k₂ ≠ 0 := by
            simp only [mul_ne_zero, two_ne_zero, π_ne_zero, I_ne_zero]
            exact ⟨⟨by norm_num, π_ne_zero⟩, I_ne_zero⟩ |>.2 (Int.cast_ne_zero.mpr h_k2_ne)
          rw [← hk₂] at this
          exact this (by simp)
        -- But we proved k₂ ≠ 0 in the first part, contradiction
        exact absurd this (by assumption)
      · -- If s ≠ 0, we can cancel it
        rw [mul_comm s _, mul_comm s _] at h_complex
        exact mul_left_cancel₀ hs h_complex

    -- Since both sides are real, we can extract the real equation
    have h_real : Real.log (p : ℝ) * k₂ = Real.log (q : ℝ) * k₁ := by
      have h_left : ((Real.log (p : ℝ) * k₂) : ℂ) = (Real.log (p : ℝ) : ℂ) * k₂ := by
        simp only [ofReal_mul, ofReal_intCast]
      have h_right : ((Real.log (q : ℝ) * k₁) : ℂ) = (Real.log (q : ℝ) : ℂ) * k₁ := by
        simp only [ofReal_mul, ofReal_intCast]
      rw [← h_left, ← h_right]
      exact ofReal_injective this

    exact h_real

end RH.ComplexLogPeriodicity
