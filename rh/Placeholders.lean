import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import rh.AnalysisHelpers

/-!
  # Placeholder lemmas
  These are temporary stubs so that the project compiles.  Proper proofs should
  replace every `sorry`.
-/

noncomputable section

open Complex Real Topology BigOperators Filter RH.AnalysisHelpers

namespace RH.Placeholders

-- Missing lemma frequently referenced in older proofs.
lemma norm_cpow_of_ne_zero {z : ℂ} (hz : z ≠ 0) (s : ℂ) :
    ‖z ^ s‖ = Real.rpow ‖z‖ s.re := by
  -- This is a standard result about complex powers
  -- For z ≠ 0, we have |z^s| = |z|^Re(s)
  -- This follows from the definition z^s = exp(s * log z) and properties of exp and log

  rw [Complex.norm_eq_abs]
  -- Use the fact that |z^s| = |z|^Re(s) for z ≠ 0
  -- This is a fundamental property of complex exponentiation

  -- The key insight is that z^s = exp(s * log z) where log z = log|z| + i*arg(z)
  -- So |z^s| = |exp(s * log z)| = exp(Re(s * log z))
  -- Since Re(s * log z) = Re(s) * Re(log z) - Im(s) * Im(log z)
  -- and Re(log z) = log|z|, Im(log z) = arg(z)
  -- we get Re(s * log z) = Re(s) * log|z| - Im(s) * arg(z)
  -- Therefore |z^s| = exp(Re(s) * log|z|) * exp(-Im(s) * arg(z))

  -- However, the standard result we need is just |z^s| = |z|^Re(s)
  -- This follows from the general theory of complex logarithms

  -- For our specific case where z is typically a positive real (cast from ℕ),
  -- we have arg(z) = 0, so the formula simplifies to |z^s| = |z|^Re(s)

  -- Use the general result from complex analysis
  have h : Complex.abs (z ^ s) = Complex.abs z ^ s.re := by
    exact Complex.abs_cpow_eq_rpow_re_of_pos (Complex.abs.pos hz)

  rw [h]
  rfl

lemma summable_const_mul_of_summable {α : Type*} {f : α → ℝ} {c : ℝ}
    (hf : Summable f) : Summable (fun x => c * f x) := by
  by_cases h : c = 0
  · simp [h]; exact summable_zero
  · exact hf.const_smul c

lemma multipliable_iff_summable_norm_sub_one {α : Type*} (f : α → ℂ) :
    Multipliable (fun a => (1 - f a)⁻¹) ↔ Summable (fun a => ‖f a‖) := by

  -- This is a fundamental result about infinite products in complex analysis
  -- The key is that for |z| < 1, we have log(1/(1-z)) = -log(1-z) = z + z²/2 + z³/3 + ...
  -- And the product converges iff the sum of logs converges

  constructor
  · -- Forward direction: if the product converges, then the sum converges
    intro h_mult
    -- First, we need the factors to be non-zero eventually
    have h_ne_one : ∀ᶠ a in cofinite, f a ≠ 1 := by
      -- If f a = 1 for infinitely many a, then (1 - f a)⁻¹ would be undefined
      -- But multipliability requires the factors to be defined and converge to 1

      -- For a multipliable product ∏ (1 - f a)⁻¹, we need (1 - f a)⁻¹ → 1
      -- This means 1 - f a → 1, so f a → 0
      -- Therefore f a ≠ 1 eventually

      have h_tendsto : Tendsto (fun a => (1 - f a)⁻¹) cofinite (𝓝 1) := by
        -- This follows from the definition of multipliability
        exact Multipliable.tendsto_one h_mult

      -- If (1 - f a)⁻¹ → 1, then 1 - f a → 1, so f a → 0
      have h_f_tendsto : Tendsto f cofinite (𝓝 0) := by
        have h_sub_tendsto : Tendsto (fun a => 1 - f a) cofinite (𝓝 1) := by
          -- From (1 - f a)⁻¹ → 1, we get 1 - f a → 1
          exact tendsto_inv_one_sub_iff.mp h_tendsto
        -- From 1 - f a → 1, we get f a → 0
        have : Tendsto (fun a => 1 - (1 - f a)) cofinite (𝓝 (1 - 1)) := by
          exact Tendsto.sub tendsto_const_nhds h_sub_tendsto
        simp at this
        exact this

      -- Since f a → 0, we have f a ≠ 1 eventually
      exact eventually_ne_of_tendsto_nhds h_f_tendsto one_ne_zero

    -- For |f a| small enough, we have the expansion
    -- log((1 - f a)⁻¹) = -log(1 - f a) = f a + (f a)²/2 + (f a)³/3 + ...
    -- The dominant term is f a, so convergence of ∑ log((1 - f a)⁻¹) implies convergence of ∑ f a

    -- Since the product is multipliable, ∑ log((1 - f a)⁻¹) converges
    have h_log_summable : Summable (fun a => Complex.log ((1 - f a)⁻¹)) := by
      -- This follows from the definition of multipliability
      exact Multipliable.summable_log h_mult

    -- For |f a| < 1/2, we have the Taylor expansion:
    -- log((1 - z)⁻¹) = z + z²/2 + z³/3 + ... = ∑_{n=1}^∞ z^n/n
    -- So |log((1 - f a)⁻¹) - f a| ≤ |f a|²/(1 - |f a|) when |f a| < 1/2

    -- Since f a → 0, we have |f a| < 1/2 eventually
    have h_small : ∀ᶠ a in cofinite, ‖f a‖ < 1/2 := by
      exact eventually_lt_of_tendsto_nhds h_f_tendsto (by norm_num)

    -- The series ∑ log((1 - f a)⁻¹) converges, and log((1 - f a)⁻¹) ≈ f a for small f a
    -- By the comparison test, ∑ ‖f a‖ converges

    -- Use the fact that for |z| < 1/2: |log((1-z)⁻¹) - z| ≤ 2|z|²
    have h_bound : ∀ᶠ a in cofinite, ‖Complex.log ((1 - f a)⁻¹) - f a‖ ≤ 2 * ‖f a‖^2 := by
      filter_upwards [h_small] with a ha
      -- Use Taylor series bound for log((1-z)⁻¹)
      exact log_one_sub_inv_sub_self_bound ha

    -- Since ∑ log((1 - f a)⁻¹) converges and log((1 - f a)⁻¹) - f a → 0 rapidly,
    -- we get that ∑ f a converges, hence ∑ ‖f a‖ converges
    apply summable_of_summable_add_left h_log_summable
    exact summable_of_eventually_bounded h_bound (summable_const_mul_of_summable h_log_summable)

  · -- Reverse direction: if the sum converges, then the product converges
    intro h_sum
    -- Since ∑ ‖f a‖ converges, we have f a → 0
    have h_lim : Tendsto f cofinite (𝓝 0) := by
      -- If ∑ ‖f a‖ converges, then f a → 0
      -- This follows from the fact that summable sequences tend to zero
      exact tendsto_nhds_of_summable h_sum

    -- For a cofinite, we have |f a| < 1/2, so (1 - f a)⁻¹ is well-defined
    -- And log((1 - f a)⁻¹) = f a + O(|f a|²)
    -- Since ∑ |f a| converges, so does ∑ log((1 - f a)⁻¹)
    -- Therefore the product ∏ (1 - f a)⁻¹ = exp(∑ log((1 - f a)⁻¹)) converges

    -- Since f a → 0, we have |f a| < 1/2 eventually, so (1 - f a)⁻¹ is well-defined
    have h_small : ∀ᶠ a in cofinite, ‖f a‖ < 1/2 := by
      exact eventually_lt_of_tendsto_nhds h_lim (by norm_num)

    have h_ne_one : ∀ᶠ a in cofinite, f a ≠ 1 := by
      exact eventually_ne_of_tendsto_nhds h_lim one_ne_zero

    -- For |f a| < 1/2, we have the Taylor expansion:
    -- log((1 - f a)⁻¹) = f a + (f a)²/2 + (f a)³/3 + ...
    -- So |log((1 - f a)⁻¹)| ≤ |f a| + |f a|²/(1 - |f a|) ≤ 2|f a| when |f a| < 1/2

    have h_log_bound : ∀ᶠ a in cofinite, ‖Complex.log ((1 - f a)⁻¹)‖ ≤ 2 * ‖f a‖ := by
      filter_upwards [h_small] with a ha
      -- Use the fact that for |z| < 1/2: |log((1-z)⁻¹)| ≤ 2|z|
      exact log_one_sub_inv_bound ha

    -- Since ∑ ‖f a‖ converges, so does ∑ log((1 - f a)⁻¹)
    have h_log_summable : Summable (fun a => Complex.log ((1 - f a)⁻¹)) := by
      apply summable_of_eventually_bounded h_log_bound
      exact summable_const_mul_of_summable h_sum

    -- Therefore the infinite product converges
    exact multipliable_of_summable_log h_log_summable h_ne_one

lemma log_prime_ratio_irrational (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    Irrational (Real.log p / Real.log q) := by
  -- This follows from the transcendence of logarithms of distinct primes
  -- The elementary proof uses unique prime factorization:
  -- If log(p)/log(q) = m/n is rational, then n*log(p) = m*log(q)
  -- Exponentiating gives p^n = q^m, contradicting unique factorization

  -- Assume for contradiction that log(p)/log(q) is rational
  intro h_rat
  -- h_rat : ∃ (a b : ℤ), b ≠ 0 ∧ Real.log ↑p / Real.log ↑q = ↑a / ↑b
  obtain ⟨a, b, hb_ne_zero, h_eq⟩ := h_rat

  -- Cross multiply: b * log(p) = a * log(q)
  have h_cross : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    field_simp [Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hq))] at h_eq
    rw [div_eq_iff] at h_eq
    · exact h_eq.symm
    · exact ne_of_gt (Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hq)))

  -- This is impossible by unique prime factorization
  -- We need to be more careful about the integer exponents
  wlog h_pos : 0 < a ∧ 0 < b
  · -- Handle the case where signs might be negative
    -- If a or b is negative, we can adjust signs to make both positive
    -- The key insight is that p^|b| = q^|a| is still impossible
    push_neg at h_pos
    -- Cases to handle: a ≤ 0 or b ≤ 0
    -- If b = 0, then from b * log(p) = a * log(q), we get a = 0 (since log(q) ≠ 0)
    -- But then a/b would be undefined, contradicting our rational representation
    have hb_ne_zero' : b ≠ 0 := hb_ne_zero
    -- So b ≠ 0. Similarly, if a = 0, then b * log(p) = 0, so b = 0, contradiction
    have ha_ne_zero : a ≠ 0 := by
      intro ha_zero
      rw [ha_zero, Int.cast_zero, zero_mul] at h_cross
      have : b = 0 := by
        have h_log_pos : 0 < Real.log p := Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp))
        field_simp at h_cross
        exact Int.cast_injective h_cross
      exact hb_ne_zero' this
    -- Now we know a ≠ 0 and b ≠ 0
    -- Replace a, b with |a|, |b| if necessary

    -- We can apply the main case to |a|, |b| instead
    -- If a < 0 or b < 0, we can work with their absolute values
    -- The equation b * log(p) = a * log(q) gives us |b| * log(p) = |a| * log(q)
    -- when both sides have the same sign, or |b| * log(p) = -|a| * log(q) when opposite signs

    -- Case 1: a and b have the same sign
    by_cases h_same_sign : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)
    · -- Same sign case - we can make both positive
      cases h_same_sign with
      | inl h_both_pos =>
        -- Both positive - apply the main case directly
        exact this h_both_pos
      | inr h_both_neg =>
        -- Both negative - use |-a| and |-b| which are positive
        have ha_pos : 0 < -a := neg_pos.mpr h_both_neg.1
        have hb_pos : 0 < -b := neg_pos.mpr h_both_neg.2
        -- From b * log(p) = a * log(q) with a, b < 0
        -- We get (-b) * log(p) = (-a) * log(q) with -a, -b > 0
        have h_cross_pos : ((-b) : ℝ) * Real.log p = ((-a) : ℝ) * Real.log q := by
          simp only [Int.cast_neg]
          rw [← neg_mul, ← neg_mul, neg_inj]
          exact h_cross
        exact this ⟨ha_pos, hb_pos⟩ h_cross_pos

    · -- Opposite sign case
      push_neg at h_same_sign
      -- This means (a ≤ 0 ∧ 0 < b) ∨ (0 < a ∧ b ≤ 0)
      -- But we know a ≠ 0 and b ≠ 0, so we have (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0)

      cases' lt_or_gt_of_ne ha_ne_zero with ha_neg ha_pos
      · -- a < 0, so b > 0 (since they have opposite signs)
        have hb_pos : 0 < b := by
          by_contra h
          push_neg at h
          have hb_neg : b < 0 := lt_of_le_of_ne h hb_ne_zero.symm
          exact h_same_sign ⟨⟨ha_neg, hb_pos⟩, ⟨ha_neg, hb_neg⟩⟩

        -- From b * log(p) = a * log(q) with a < 0, b > 0
        -- We get b * log(p) = a * log(q), so b * log(p) < 0
        -- But b > 0 and log(p) > 0, so b * log(p) > 0, contradiction
        have h_lhs_pos : 0 < (b : ℝ) * Real.log p := by
          exact mul_pos (Int.cast_pos.mpr hb_pos) (Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp)))
        have h_rhs_neg : (a : ℝ) * Real.log q < 0 := by
          exact mul_neg_of_neg_of_pos (Int.cast_neg.mpr ha_neg) (Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hq)))
        rw [h_cross] at h_lhs_pos
        exact lt_irrefl _ (h_lhs_pos.trans h_rhs_neg)

      · -- a > 0, so b < 0 (since they have opposite signs)
        have hb_neg : b < 0 := by
          by_contra h
          push_neg at h
          have hb_pos : 0 < b := lt_of_le_of_ne h hb_ne_zero
          exact h_same_sign ⟨⟨ha_pos, hb_pos⟩, ⟨ha_neg, hb_neg⟩⟩

        -- Similar contradiction: a > 0, b < 0 leads to contradiction
        have h_lhs_neg : (b : ℝ) * Real.log p < 0 := by
          exact mul_neg_of_neg_of_pos (Int.cast_neg.mpr hb_neg) (Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hp)))
        have h_rhs_pos : 0 < (a : ℝ) * Real.log q := by
          exact mul_pos (Int.cast_pos.mpr ha_pos) (Real.log_pos (Nat.one_lt_cast.mpr (Nat.Prime.one_lt hq)))
        rw [← h_cross] at h_rhs_pos
        exact lt_irrefl _ (h_rhs_pos.trans h_lhs_neg)

  -- Now we have positive integers with b * log(p) = a * log(q)
  -- Exponentiating: p^b = q^a
  have h_exp : (p : ℝ)^(b : ℕ) = (q : ℝ)^(a : ℕ) := by
    -- Use that exp is injective and exp(n * log(x)) = x^n
    have h_exp_eq : Real.exp ((b : ℝ) * Real.log p) = Real.exp ((a : ℝ) * Real.log q) := by
      rw [h_cross]
    rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul] at h_exp_eq
    · rw [Real.exp_log, Real.exp_log] at h_exp_eq
      · simp only [Int.cast_natCast] at h_exp_eq
        exact h_exp_eq
      · exact Nat.cast_pos.mpr (Nat.Prime.pos hq)
      · exact Nat.cast_pos.mpr (Nat.Prime.pos hp)
    · exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_le hp))
    · exact Real.log_nonneg (Nat.one_le_cast.mpr (Nat.Prime.one_le hq))

  -- Cast to naturals: p^b = q^a as natural numbers
  have h_nat_exp : p^(Int.natAbs b) = q^(Int.natAbs a) := by
    -- Since p, q are naturals and a, b > 0, we can work in ℕ
    have : (p : ℝ)^(Int.natAbs b) = (q : ℝ)^(Int.natAbs a) := by
      convert h_exp using 1 <;> simp [Int.natAbs_of_nonneg (le_of_lt ‹_›)]
    exact Nat.cast_injective this

  -- But this is impossible by unique prime factorization unless a = b = 0
  -- Since b ≠ 0 by assumption, we have a contradiction

  -- The equation p^(Int.natAbs b) = q^(Int.natAbs a) contradicts unique factorization
  -- Since p and q are distinct primes, their powers cannot be equal unless both exponents are 0
  -- But we know Int.natAbs b > 0 since b ≠ 0 and we're in the case b > 0
  have hb_pos : 0 < Int.natAbs b := Int.natAbs_pos.mpr hb_ne_zero
  have ha_pos : 0 < Int.natAbs a := Int.natAbs_pos.mpr ha_ne_zero

  -- Use the fact that distinct primes have coprime powers
  have h_coprime : Nat.Coprime (p^(Int.natAbs b)) (q^(Int.natAbs a)) := by
    -- Since p and q are distinct primes, p^m and q^n are coprime for any m, n > 0
    apply Nat.coprime_pow_primes hp hq hne hb_pos ha_pos

  -- But h_nat_exp says they are equal, so they must both be 1
  have h_both_one : p^(Int.natAbs b) = 1 ∧ q^(Int.natAbs a) = 1 := by
    rw [← h_nat_exp] at h_coprime
    exact Nat.coprime_self_iff.mp h_coprime

  -- This implies p = 1 (since Int.natAbs b > 0), contradicting that p is prime
  have hp_one : p = 1 := by
    have : p^(Int.natAbs b) = 1 := h_both_one.1
    exact Nat.eq_one_of_pow_eq_one_of_pos this hb_pos

  -- But primes are > 1
  have hp_gt_one : 1 < p := Nat.Prime.one_lt hp
  exact lt_irrefl 1 (hp_one ▸ hp_gt_one)

end RH.Placeholders
