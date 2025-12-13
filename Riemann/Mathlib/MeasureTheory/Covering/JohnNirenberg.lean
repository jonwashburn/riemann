import Riemann.Mathlib.MeasureTheory.Covering.CalderonZygmund

/-!
# John–Nirenberg covering/iteration toolkit

This file is the **covering/iteration API layer** for the John–Nirenberg inequality.

It is intentionally independent of any particular BMO definition file: it packages the
reusable covering lemmas and the (linear-threshold) geometric decay iteration that feed into
`Analysis/Harmonic/BMO/JohnNirenberg.lean`.

The goal is Stein-level modularity:
- geometric covering lemma(s),
- one-step decay lemma(s),
- iteration lemma(s).

No placeholders are allowed in this file.
-/

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α] {μ : Measure α}

section Basics

variable [ProperSpace α] [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- Elementary real-analysis inequality: for `x ≥ 0`,
\((1/2)^{\lfloor x \rfloor} \le 2\, e^{-(\log 2) x}\).

This is the bridge from linear-threshold geometric decay to the usual exponential tail. -/
lemma pow_half_floor_le_two_mul_exp_neg_log_two_mul (x : ℝ) (hx : 0 ≤ x) :
    (1 / 2 : ℝ) ^ (Int.floor x).toNat ≤ 2 * Real.exp (-(Real.log 2) * x) := by
  -- Proof: `n := ⌊x⌋` gives `n ≤ x < n+1`.
  -- Hence `2^{-n} = exp(-(log 2) n) ≤ exp(-(log 2) (x-1)) = 2 * exp(-(log 2) x)`.
  have hx_lt : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hx_lt' : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
  -- Convert `Int.floor x` to nat for the exponent.
  have hn0 : 0 ≤ Int.floor x := by
    -- since `x ≥ 0`, `floor x ≥ 0`
    exact Int.floor_nonneg.mpr hx
  set n : ℕ := (Int.floor x).toNat
  have hn_eq : (n : ℤ) = Int.floor x := by
    -- `toNat_of_nonneg`
    simpa [n] using (Int.toNat_of_nonneg hn0)
  have hn_le_x : (n : ℝ) ≤ x := by
    -- from floor_le
    -- Convert Int.floor x to n using hn_eq
    calc (n : ℝ) = (Int.floor x : ℝ) :=
      Eq.symm (ext_cauchy (congrArg cauchy (congrArg Int.cast (id (Eq.symm hn_eq)))))
      _ ≤ x := hx_lt
  have hx_lt_succ : x < (n : ℝ) + 1 := by
    calc x < (Int.floor x : ℝ) + 1 := hx_lt'
      _ = (n : ℝ) + 1 :=
        congrFun (congrArg HAdd.hAdd (congrArg Int.cast (id (Eq.symm hn_eq)))) 1
  -- Now do the exponential comparison.
  have hlog2_pos : 0 < Real.log 2 := by
    simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h2pos : (0 : ℝ) < 2 := by norm_num
  -- Rewrite `(1/2)^n` as `2^{-n}`.
  have hpow : (1 / 2 : ℝ) ^ n = Real.exp (-(Real.log 2) * (n : ℝ)) := by
    -- `a^b = exp(b*log a)` for positive `a`.
    have hhalf_pos : (0 : ℝ) < (1 / 2) := by norm_num
    -- use `Real.rpow_natCast` via `rpow_def`
    -- `x^n` is `Real.rpow` for nat?
    -- simplest: `x^n = exp(n * log x)` for `x>0`.
    -- use lemma `Real.rpow_natCast` with `x=1/2`.
    calc
      (1 / 2 : ℝ) ^ n = Real.exp (Real.log (1 / 2) * (n : ℝ)) := by
        -- `Real.exp_log` trick
        have : (1 / 2 : ℝ) ^ n = Real.exp (Real.log ((1 / 2 : ℝ) ^ n)) := by
          rw [Real.exp_log (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n)]
        -- rewrite `log (a^n) = n*log a`
        -- Use `Real.log_pow` for natural number exponents
        rw [this, Real.log_pow]
        ring_nf
      _ = Real.exp (-(Real.log 2) * (n : ℝ)) := by
        -- `log(1/2) = -log 2`
        have : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
          -- `log (1/2) = log 1 - log 2 = -log 2`
          simp [div_eq_mul_inv, Real.log_inv]
        simp [mul_comm]
  -- Use monotonicity of `exp` with `n ≤ x < n+1`.
  have h_exp_le :
      Real.exp (-(Real.log 2) * (n : ℝ)) ≤ 2 * Real.exp (-(Real.log 2) * x) := by
    -- from `x < n+1` -> `-(log2)*n ≤ -(log2)*(x-1)`
    have : x - 1 < (n : ℝ) := by linarith
    have hmul : (-(Real.log 2)) * (n : ℝ) ≤ (-(Real.log 2)) * (x - 1) := by
      -- multiply inequality by negative number reverses
      have hneg : (-(Real.log 2)) < 0 := by linarith [hlog2_pos]
      exact (mul_le_mul_of_nonpos_left (le_of_lt this) (le_of_lt hneg))
    -- exponentiate
    have : Real.exp (-(Real.log 2) * (n : ℝ)) ≤ Real.exp (-(Real.log 2) * (x - 1)) :=
      by
        exact Real.exp_le_exp.mpr (by
          -- rewrite
          simpa [mul_assoc] using hmul)
    -- `exp(-(log2)*(x-1)) = exp(log2) * exp(-(log2)*x) = 2 * exp(-(log2)*x)`
    have hexp_shift : Real.exp (-(Real.log 2) * (x - 1)) = 2 * Real.exp (-(Real.log 2) * x) := by
      -- expand `x-1` and use `exp_add`
      have : (-(Real.log 2) * (x - 1)) = (-(Real.log 2) * x) + Real.log 2 := by ring
      -- then exp_add
      simp_rw [this, Real.exp_add]
      -- now we need to show: exp(-(log 2) * x) * exp(log 2) = 2 * exp(-(log 2) * x)
      rw [Real.exp_log h2pos]
      ring
    calc
      Real.exp (-(Real.log 2) * (n : ℝ))
          ≤ Real.exp (-(Real.log 2) * (x - 1)) := this
      _ = 2 * Real.exp (-(Real.log 2) * x) := hexp_shift
  -- finish
  calc
    (1 / 2 : ℝ) ^ n
        = Real.exp (-(Real.log 2) * (n : ℝ)) := hpow
    _ ≤ 2 * Real.exp (-(Real.log 2) * x) := h_exp_le

end Basics

/-!
### Abstract iteration → exponential tail

This section is purely measure-theoretic/real-analytic: it packages the standard argument turning
an iterative **geometric decay** estimate into an exponential distribution bound using the
bridge lemma `pow_half_floor_le_two_mul_exp_neg_log_two_mul`.
-/
section Iteration
omit [MetricSpace α] [BorelSpace α] in
lemma measure_geometric_decay_of_step {E : ℕ → Set α}
    (hstep : ∀ n, μ (E (n + 1)) ≤ (1 / 2 : ℝ≥0∞) * μ (E n)) (n : ℕ) :
    μ (E n) ≤ (1 / 2 : ℝ≥0∞) ^ n * μ (E 0) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- one step + induction
      calc
        μ (E (n + 1)) ≤ (1 / 2 : ℝ≥0∞) * μ (E n) := hstep n
        _ ≤ (1 / 2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) ^ n * μ (E 0)) := by gcongr
        _ = (1 / 2 : ℝ≥0∞) ^ (n + 1) * μ (E 0) := by
              simp [pow_succ, mul_assoc, mul_comm]

omit [MetricSpace α] [BorelSpace α] in
/-- Turn a geometric decay estimate at integer steps into an exponential tail bound. -/
lemma measure_exponential_decay_of_geometric {E : ℕ → Set α}
    (hstep : ∀ n, μ (E (n + 1)) ≤ (1 / 2 : ℝ≥0∞) * μ (E n))
    {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    μ (E (Int.floor (t / c)).toNat) ≤
      2 * μ (E 0) * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / c))) := by
  -- First use geometric decay at `n = ⌊t/c⌋`.
  have hgeom := measure_geometric_decay_of_step (μ := μ) hstep (Int.floor (t / c)).toNat
  -- Bound `(1/2)^(⌊t/c⌋)` by `2*exp(-(log2)*(t/c))` (in ℝ), then convert.
  have hx : 0 ≤ t / c := by
    exact div_nonneg ht hc.le
  have hpow_real :
      (1 / 2 : ℝ) ^ (Int.floor (t / c)).toNat ≤
        2 * Real.exp (-(Real.log 2) * (t / c)) :=
    pow_half_floor_le_two_mul_exp_neg_log_two_mul (x := t / c) hx
  have hpow_ennreal :
      (1 / 2 : ℝ≥0∞) ^ (Int.floor (t / c)).toNat ≤
        ENNReal.ofReal (2 * Real.exp (-(Real.log 2) * (t / c))) := by
    have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
    -- Push the real inequality into `ℝ≥0∞` via `ENNReal.ofReal`.
    simpa [ENNReal.ofReal_pow hhalf, ENNReal.inv_pow, div_eq_mul_inv] using
      (ENNReal.ofReal_le_ofReal hpow_real)
  -- finish, multiplying by `μ (E 0)`
  calc
    μ (E (Int.floor (t / c)).toNat)
        ≤ (1 / 2 : ℝ≥0∞) ^ (Int.floor (t / c)).toNat * μ (E 0) := hgeom
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(Real.log 2) * (t / c))) * μ (E 0) := by
          gcongr
    _ = 2 * μ (E 0) * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / c))) := by
          -- rearrange and split `ofReal` product
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          have hexp : 0 ≤ Real.exp (-(Real.log 2) * (t / c)) := by positivity
          simp [ENNReal.ofReal_mul h2, mul_assoc, mul_left_comm, mul_comm]

end Iteration

/-!
### Covering lemmas (Besicovitch/Vitali layer)

At Stein-level generality, the John–Nirenberg iteration requires a stopping-time covering lemma.
In Euclidean spaces, this is obtained from the measurable Besicovitch covering theorem.

We expose a *reusable* wrapper around `Besicovitch.exists_disjoint_closedBall_covering_ae` that will
be used to build the CZ-style covering inside the JN proof.
-/
section Covering

variable [SecondCountableTopology α] [HasBesicovitchCovering α]
variable (μ)

open Metric

/-- A wrapper around the measurable Besicovitch covering theorem, phrased in the form convenient
for CZ/JN constructions: given admissible radii `f x` accumulating at `0` for each `x ∈ s`, extract
a countable disjoint family of closed balls covering almost all of `s`. -/
theorem exists_disjoint_closedBall_covering_ae
    [SFinite μ] (f : α → Set ℝ) (s : Set α)
    (hf : ∀ x ∈ s, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty) (R : α → ℝ)
    (hR : ∀ x ∈ s, 0 < R x) :
    ∃ (t : Set α) (r : α → ℝ),
      t.Countable ∧ t ⊆ s ∧
        (∀ x ∈ t, r x ∈ f x ∩ Ioo 0 (R x)) ∧
        μ (s \ ⋃ x ∈ t, Metric.closedBall x (r x)) = 0 ∧
        t.PairwiseDisjoint (fun x => Metric.closedBall x (r x)) := by
  simpa using
    (Besicovitch.exists_disjoint_closedBall_covering_ae (μ := μ) f s hf R hR)

end Covering

end MeasureTheory
