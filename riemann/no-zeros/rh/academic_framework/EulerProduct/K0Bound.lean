import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import rh.academic_framework.EulerProduct.PrimeSeries

/-!
# Arithmetic prime-power tail K0 bound

We record a formal definition of the prime-power tail constant

  K0 := (1/4) * ∑_{p} ∑_{k≥2} p^{-k} / k^2

valid at the level of nonnegative series (interpreted via `tsum` on
`ℝ≥0∞` upper bounds or via absolute convergence on `ℝ`). We also give
a general inequality that reduces bounding `K0` to bounding the prime
Dirichlet series blocks `P(k) := ∑_{p} p^{-k}` for integers `k ≥ 2`.

This file purposefully stops short of a hard numeric evaluation such as
`K0 ≤ 0.03486808`. That final enclosure can be added later using either
interval arithmetic or a numerics file; here we isolate the algebraic
reduction and clean inequalities needed by higher layers.
-/

namespace RH.AcademicFramework.EulerProduct.K0

open scoped BigOperators


/-- Prime-power block for integer exponent `k≥2`: `P(k) = ∑_{p} p^{-k}` as a real series. -/
noncomputable def P (k : ℕ) : ℝ :=
  (∑' p : Nat.Primes, (p : ℝ) ^ (-(k : ℝ)))

/-- The arithmetic tail constant as a real number: `(1/4) * ∑_{k≥2} P(k)/k^2`.
Named `K0Const` to avoid clashing with the surrounding namespace name. -/
noncomputable def K0Const : ℝ :=
  (1/4 : ℝ) * (∑' k : {n // 2 ≤ n}, P k / (((k : ℕ) : ℝ) ^ 2))

/-! ### Coarse upper bound shape (for numerics) -/

/-- A convenient coarse upper-bound value for `K0` used in diagnostics:
`K0UpperSimple = (1/4) * P(2) * ∑_{k≥2} 1/k^2`.

This captures the elementary monotonicity heuristic `P(k) ≤ P(2)` for `k≥2` and
factors out the zeta(2)-tail. A formal inequality `K0 ≤ K0UpperSimple` will be
added once the supporting monotonicity and subtype–tsum comparison lemmas are
landed. -/
noncomputable def K0UpperSimple : ℝ :=
  (1/4 : ℝ) * P 2 * (∑' k : {n // 2 ≤ n}, (1 : ℝ) / (((k : ℕ) : ℝ) ^ 2))

/-! ### Basic summability -/

/-- For integer `k ≥ 2`, the prime series `∑_p p^{-k}` converges (absolute). -/
lemma summable_P_of_two_le (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(k : ℝ))) := by
  -- Reduce to the real-exponent lemma `r > 1`
  have hr : (1 : ℝ) < (k : ℝ) := by
    have hk1 : (1 : ℕ) < k := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hk
    exact_mod_cast hk1
  -- Use the prime-series convergence for real exponents > 1
  simpa using AcademicRH.EulerProduct.real_prime_rpow_summable hr

/-- Convenience: rewrite `P k` with the `tsum` over primes and invoke summability. -/
lemma summable_P (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(k : ℝ))) :=
  summable_P_of_two_le k hk

/-! ### Helper: subtype tsum ≤ total (nonnegative) -/

section Helpers

variable {f : ℕ → ℝ}

/-- If `f ≥ 0` termwise and `f` is summable, then the sum over a subset is
less than or equal to the total sum (via indicator). -/
lemma tsum_subtype_le_total
    (s : Set ℕ) (h0 : ∀ n : ℕ, 0 ≤ f n)
    (hf : Summable f) :
    (∑' n : {n // n ∈ s}, f n) ≤ (∑' n : ℕ, f n) := by
  classical
  have hsub : (∑' n : {n // n ∈ s}, f n)
      = ∑' n : ℕ, s.indicator f n := by
    simpa using (tsum_subtype (s := s) (f := f))
  have hind_le : ∀ n : ℕ, s.indicator f n ≤ f n := by
    intro n; by_cases hn : n ∈ s
    · simp [Set.indicator_of_mem hn]
    · have : s.indicator f n = 0 := by simpa [Set.indicator_of_not_mem hn]
      simpa [this] using h0 n
  have hsum_ind : Summable (s.indicator f) := hf.indicator _
  have := tsum_le_tsum hind_le hsum_ind hf
  simpa [hsub]

end Helpers

/-! ### Skeleton inequalities (pointwise-to-series and numeric plan) -/

notation "K0" => K0Const

/-- Pointwise-to-series majorization skeleton: assuming pointwise
`P k ≤ B k` and summability of both weighted series over `k≥2`, we have
`K0 ≤ (1/4) * ∑ B(k)/k^2`. -/
theorem K0_le_series_of_pointwise
    (B : {n // 2 ≤ n} → ℝ)
    (hpt : ∀ k : {n // 2 ≤ n}, P k ≤ B k)
    (hPL : Summable (fun k : {n // 2 ≤ n} => P k / (((k : ℕ) : ℝ) ^ 2)))
    (hBL : Summable (fun k : {n // 2 ≤ n} => B k / (((k : ℕ) : ℝ) ^ 2))) :
    K0 ≤ (1/4 : ℝ) * (∑' k : {n // 2 ≤ n}, B k / (((k : ℕ) : ℝ) ^ 2)) := by
  classical
  have hpt' : ∀ k : {n // 2 ≤ n},
      P k / (((k : ℕ) : ℝ) ^ 2) ≤ B k / (((k : ℕ) : ℝ) ^ 2) := by
    intro k
    have hk : 0 ≤ (((k : ℕ) : ℝ) ^ 2) := by simpa using sq_nonneg (((k : ℕ) : ℝ))
    exact (div_le_div_of_nonneg_right (hpt k) hk)
  have hsum : (∑' k : {n // 2 ≤ n}, P k / (((k : ℕ) : ℝ) ^ 2))
            ≤ (∑' k : {n // 2 ≤ n}, B k / (((k : ℕ) : ℝ) ^ 2)) :=
    tsum_le_tsum hpt' hPL hBL
  have hmul := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1/4)
  simpa [K0Const, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Numeric plan skeleton (finite block + tail decomposition): if for each `k≥2`
`integerTail k ≤ F k + T k` and both weighted series converge, then
`K0 ≤ (1/4) * (∑ F/k^2 + ∑ T/k^2)`. -/
theorem K0_le_finitePlusTail
    (integerTail : {n // 2 ≤ n} → ℝ)
    (F T : {n // 2 ≤ n} → ℝ)
    (hdecomp : ∀ k : {n // 2 ≤ n}, integerTail k ≤ F k + T k)
    (hF : Summable (fun k : {n // 2 ≤ n} => F k / (((k : ℕ) : ℝ) ^ 2)))
    (hT : Summable (fun k : {n // 2 ≤ n} => T k / (((k : ℕ) : ℝ) ^ 2)))
    (hPsum : Summable (fun k : {n // 2 ≤ n} => P k / (((k : ℕ) : ℝ) ^ 2)))
    (hIsum : Summable (fun k : {n // 2 ≤ n} => integerTail k / (((k : ℕ) : ℝ) ^ 2)))
    (hP_le_int : ∀ k : {n // 2 ≤ n}, P k ≤ integerTail k) :
    K0 ≤ (1/4 : ℝ) * ((∑' k, F k / (((k : ℕ) : ℝ) ^ 2)) + (∑' k, T k / (((k : ℕ) : ℝ) ^ 2))) := by
  classical
  have hlin : (∑' k : {n // 2 ≤ n}, (F k + T k) / (((k : ℕ) : ℝ) ^ 2))
      = (∑' k, F k / (((k : ℕ) : ℝ) ^ 2)) + (∑' k, T k / (((k : ℕ) : ℝ) ^ 2)) := by
    have := (tsum_add hF hT)
    simpa [add_div] using this
  -- apply the pointwise-to-series lemma twice: P ≤ integerTail ≤ F+T
  have h1 : K0 ≤ (1/4 : ℝ) * (∑' k : {n // 2 ≤ n}, integerTail k / (((k : ℕ) : ℝ) ^ 2)) := by
    refine K0_le_series_of_pointwise (B := integerTail) (hpt := ?_) (hPL := hPsum) (hBL := hIsum)
    intro k; exact hP_le_int k
  have h2 : (∑' k : {n // 2 ≤ n}, integerTail k / (((k : ℕ) : ℝ) ^ 2))
      ≤ (∑' k : {n // 2 ≤ n}, (F k + T k) / (((k : ℕ) : ℝ) ^ 2)) := by
    -- pointwise and summable comparison
    have hpt' : ∀ k : {n // 2 ≤ n},
        integerTail k / (((k : ℕ) : ℝ) ^ 2)
        ≤ (F k + T k) / (((k : ℕ) : ℝ) ^ 2) := by
      intro k
      have hk : 0 ≤ (((k : ℕ) : ℝ) ^ 2) := by simpa using sq_nonneg (((k : ℕ) : ℝ))
      exact (div_le_div_of_nonneg_right (hdecomp k) hk)
    have hsumL := hIsum
    have hsumR : Summable (fun k : {n // 2 ≤ n} => (F k + T k) / (((k : ℕ) : ℝ) ^ 2)) := by
      simpa [add_div] using (hF.add hT)
    exact tsum_le_tsum hpt' hsumL hsumR
  have : K0 ≤ (1/4 : ℝ) * (∑' k : {n // 2 ≤ n}, (F k + T k) / (((k : ℕ) : ℝ) ^ 2)) := by
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 1/4)
    exact le_trans h1 this
  simpa [hlin, mul_add] using this

/-! ### Interface predicate for certificate consumers -/

/-- Interface-level statement: the arithmetic tail constant `K0` is
nonnegative on the half-plane strip. This is packaged as a predicate to
avoid committing to an analytic construction in this track. Certificate
consumers can require this fact without depending on concrete `U` data. -/
def K0_bound_on_strip : Prop := 0 ≤ K0

/-- Proof of nonnegativity: `K0 = (1/4) * ∑_{k≥2} P(k)/k^2 ≥ 0` since each term is
nonnegative and the prefactor `1/4` is nonnegative. -/
theorem K0_bound_on_strip_proved : K0_bound_on_strip := by
  classical
  dsimp [K0_bound_on_strip, K0Const]
  have hterm_nonneg : ∀ k : {n // 2 ≤ n}, 0 ≤ P k / (((k : ℕ) : ℝ) ^ 2) := by
    intro k
    -- `P k = ∑' p primes (p : ℝ) ^ (-(k : ℝ))` with nonnegative terms
    have hPk_nonneg : 0 ≤ P k := by
      have hprime_nonneg : ∀ p : Nat.Primes, 0 ≤ (p : ℝ) ^ (-(k : ℝ)) := by
        intro p
        -- Real rpow is nonnegative for nonnegative base
        exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (p : ℕ))) _
      simpa [P] using (tsum_nonneg hprime_nonneg)
    have hk2_nonneg : 0 ≤ (((k : ℕ) : ℝ) ^ 2) := by
      simpa using sq_nonneg (((k : ℕ) : ℝ))
    exact div_nonneg hPk_nonneg hk2_nonneg
  have hsum_nonneg : 0 ≤ (∑' k : {n // 2 ≤ n}, P k / (((k : ℕ) : ℝ) ^ 2)) :=
    tsum_nonneg hterm_nonneg
  have hcoef : 0 ≤ (1/4 : ℝ) := by norm_num
  exact mul_nonneg hcoef hsum_nonneg

end RH.AcademicFramework.EulerProduct.K0
