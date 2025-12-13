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
          simpa [mul_assoc] using hmul)
    -- `exp(-(log2)*(x-1)) = exp(log2) * exp(-(log2)*x) = 2 * exp(-(log2)*x)`
    have hexp_shift : Real.exp (-(Real.log 2) * (x - 1)) = 2 * Real.exp (-(Real.log 2) * x) := by
      have : (-(Real.log 2) * (x - 1)) = (-(Real.log 2) * x) + Real.log 2 := by ring
      simp_rw [this, Real.exp_add]
      rw [Real.exp_log h2pos]
      ring
    calc
      Real.exp (-(Real.log 2) * (n : ℝ))
          ≤ Real.exp (-(Real.log 2) * (x - 1)) := this
      _ = 2 * Real.exp (-(Real.log 2) * x) := hexp_shift
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
### One-step estimates on a ball vs its 7×-dilation

The abstract iteration in `section Iteration` needs a **one-step** estimate of the form
`μ(E_{n+1}) ≤ (1/2) μ(E_n)`.  In practice this comes from a Chebyshev estimate on a ball `B`,
after comparing the relevant averages on `B` and on a slightly larger ball.

We isolate here the convenient specialization of
`MeasureTheory.measure_subball_abs_sub_setAverage_gt_add_le` (from `Covering/CalderonZygmund.lean`)
to the case where the “big ball” is the **7× dilation** of the small one (same center).
This pins down the telescoping constant to a fixed local-doubling scale (`14` and `2`).
-/
section BMOStep

variable [ProperSpace α] [IsUnifLocDoublingMeasure μ]
variable [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-- Special case of `measure_subball_abs_sub_setAverage_gt_add_le` where the big ball is `ball x (7*r)`.

The telescoping constant becomes
`scalingConstantOf μ 14 * scalingConstantOf μ 2` and the scaling assumptions reduce to
`r ≤ scalingScaleOf μ 14` and `r/2 ≤ scalingScaleOf μ 2`. -/
theorem measure_ball_abs_sub_setAverage_gt_add_le_seven_mul {f : α → ℝ}
    (hf_int : LocallyIntegrable f μ) {M : ℝ} (hM : 0 < M)
    (hbmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    {x : α} {r : ℝ} (hr : 0 < r)
    (hr_scale : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 14)
    (hr_scale2 : r / 2 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 2)
    {t : ℝ} (ht : 0 < t) :
    μ {y ∈ Metric.ball x r |
        |f y - ⨍ z in Metric.ball x (7 * r), f z ∂μ| >
          t + ((IsUnifLocDoublingMeasure.scalingConstantOf μ 14 *
              IsUnifLocDoublingMeasure.scalingConstantOf μ 2 : ℝ≥0) : ℝ) * M}
      ≤ ENNReal.ofReal (M / t) * μ (Metric.ball x r) := by
  have hr₀ : 0 < (7 * r) := by nlinarith
  have h_contained : Metric.ball x r ⊆ Metric.ball x (7 * r) := by
    -- `r ≤ 7*r` since `r > 0`
    simpa [Metric.ball] using (Metric.ball_subset_ball (by nlinarith [hr.le] : r ≤ 7 * r))
  -- Match the scale parameter `2 * r₀ / r` to `14`.
  have h14 : (2 * (7 * r) / r) = (14 : ℝ) := by
    have hr0 : (r : ℝ) ≠ 0 := hr.ne'
    -- `2 * (7*r) / r = 14`
    calc
      2 * (7 * r) / r = (14 * r) / r := by ring
      _ = (14 : ℝ) := by simp [hr0]
  -- The same identity in the “normalized” form that `simp` tends to produce.
  have h14' : (r * (2 * 7) / r) = (14 : ℝ) := by
    have hr0 : (r : ℝ) ≠ 0 := hr.ne'
    calc
      r * (2 * 7) / r = (14 * r) / r := by ring
      _ = (14 : ℝ) := by simp [hr0]
  -- Apply the general subball lemma with `x₀ = x`, `r₀ = 7*r`.
  -- `simp` needs the scale parameter in the exact form `2 * r₀ / r`.
  have hr_scale' : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (2 * (7 * r) / r) := by
    simpa [h14] using hr_scale
  simpa [h14, h14', mul_assoc, mul_left_comm, mul_comm] using
    (MeasureTheory.measure_subball_abs_sub_setAverage_gt_add_le (μ := μ) (f := f) hf_int hM hbmo
      (x₀ := x) (r₀ := 7 * r) hr₀ (x := x) (r := r) hr h_contained
      hr_scale' hr_scale2 ht)

end BMOStep

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

/-!
#### A Whitney-style a.e. covering of an open set by disjoint balls

This is the geometric input typically used to run stopping-time arguments (CZ / John–Nirenberg):
we cover an open set `O` by a countable disjoint family of balls whose *fixed dilation* stays
inside `O`.
-/

/-- In a space with the Besicovitch covering property, any open set `O` can be covered a.e. by a
countable family of **disjoint** closed balls whose `7`-dilations stay inside `O`.

This is a convenient “Whitney a.e. covering” lemma tailored to later CZ/JN arguments. -/
theorem exists_disjoint_closedBall_covering_ae_of_isOpen
    [SFinite μ] {O : Set α} (hO : IsOpen O) :
    ∃ (t : Set α) (r : α → ℝ),
      t.Countable ∧ t ⊆ O ∧
        (∀ x ∈ t, 0 < r x ∧ Metric.closedBall x (7 * r x) ⊆ O) ∧
        μ (O \ ⋃ x ∈ t, Metric.closedBall x (r x)) = 0 ∧
        t.PairwiseDisjoint (fun x => Metric.closedBall x (r x)) := by
  classical
  -- Admissible radii at `x`: those whose `7`-closed-ball stays inside `O`.
  let f : α → Set ℝ := fun x => {r | 0 < r ∧ Metric.closedBall x (7 * r) ⊆ O}
  have hf : ∀ x ∈ O, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ hδ
    -- choose a small neighborhood inside `O`
    rcases Metric.isOpen_iff.mp hO x hx with ⟨ε, hε, hεO⟩
    -- take `r = min (ε/8) (δ/2)` so that `7r < ε` and `r < δ`
    refine ⟨min (ε / 8) (δ / 2), ?_⟩
    have hr_pos : 0 < min (ε / 8) (δ / 2) := by
      have hε8 : 0 < ε / 8 := by positivity
      have hδ2 : 0 < δ / 2 := by positivity
      exact lt_min hε8 hδ2
    have hr_lt_δ : min (ε / 8) (δ / 2) < δ := by
      have : δ / 2 < δ := by linarith
      exact (min_le_right _ _).trans_lt this
    refine ⟨?_, ?_⟩
    · -- membership in `f x`
      refine ⟨hr_pos, ?_⟩
      -- show `closedBall x (7*r) ⊆ O` via containment in `ball x ε`
      have h7r_lt : (7 : ℝ) * min (ε / 8) (δ / 2) < ε := by
        have hle : (7 : ℝ) * min (ε / 8) (δ / 2) ≤ 7 * (ε / 8) := by gcongr; exact min_le_left _ _
        have hlt : (7 : ℝ) * (ε / 8) < ε := by nlinarith
        exact lt_of_le_of_lt hle hlt
      intro y hy
      have : dist y x < ε := by
        -- `dist y x ≤ 7*r` and `7*r < ε`
        have hy' : dist y x ≤ (7 : ℝ) * min (ε / 8) (δ / 2) := by
          simpa [Metric.mem_closedBall, mul_assoc] using hy
        exact lt_of_le_of_lt hy' h7r_lt
      exact hεO (by simpa [Metric.mem_ball] using this)
    · -- membership in `Ioo 0 δ`
      exact ⟨hr_pos, hr_lt_δ⟩
  -- Apply Besicovitch covering theorem with `R = 1` (any positive bound works).
  obtain ⟨t, r, t_count, tO, hrt, hcover, hdisj⟩ :=
    exists_disjoint_closedBall_covering_ae (μ := μ) f O hf (fun _ => (1 : ℝ)) (fun _ _ => one_pos)
  refine ⟨t, r, t_count, tO, ?_, hcover, hdisj⟩
  intro x hx
  have hx' := hrt x hx
  refine ⟨?_, ?_⟩
  · exact hx'.1.1
  · -- the `7`-dilation stays in `O`
    simpa [f] using hx'.1.2

/-- **Local-to-global half-measure** via a Whitney a.e. covering.

If an open set `O` is covered a.e. by a countable disjoint family of (closed) balls `Bᵢ`,
and on each `Bᵢ` a subset `E ⊆ O` has measure at most half the measure of `Bᵢ`,
then `μ E ≤ (1/2) μ O`. -/
theorem measure_le_half_of_isOpen_of_forall_ball
    [SFinite μ] {O E : Set α} (hO : IsOpen O) (hE : E ⊆ O)
    (hball : ∀ (x : α) (r : ℝ), Metric.closedBall x (7 * r) ⊆ O →
      μ (E ∩ Metric.closedBall x r) ≤ (1 / 2 : ℝ≥0∞) * μ (Metric.closedBall x r)) :
    μ E ≤ (1 / 2 : ℝ≥0∞) * μ O := by
  classical
  obtain ⟨t, r, ht_count, htO, _h7, hcover, hdisj⟩ :=
    exists_disjoint_closedBall_covering_ae_of_isOpen (μ := μ) (O := O) hO
  -- Let `U` be the union of the Whitney balls.
  let U : Set α := ⋃ x ∈ t, Metric.closedBall x (r x)
  have hE_diff : μ (E \ U) = 0 := by
    have hsub : E \ U ⊆ O \ U := by
      intro y hy; exact ⟨hE hy.1, hy.2⟩
    exact measure_mono_null hsub hcover
  -- Reduce to `E ∩ U`.
  have hE_le : μ E ≤ μ (E ∩ U) := by
    have hsplit : μ E ≤ μ (E ∩ U) + μ (E \ U) :=
      MeasureTheory.measure_le_inter_add_diff (μ := μ) E U
    simpa [hE_diff] using hsplit
  -- Subadditivity on the (bi)union.
  have hE_interU_le :
      μ (E ∩ U) ≤ ∑' p : t, μ (E ∩ Metric.closedBall (p : α) (r p)) := by
    have hrewrite : E ∩ U = ⋃ x ∈ t, E ∩ Metric.closedBall x (r x) := by
      ext y; constructor
      · intro hy
        rcases hy with ⟨hyE, hyU⟩
        rcases mem_iUnion₂.mp hyU with ⟨x, hx, hyx⟩
        exact mem_iUnion₂.mpr ⟨x, hx, ⟨hyE, hyx⟩⟩
      · intro hy
        rcases mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
        exact ⟨hyx.1, mem_iUnion₂.mpr ⟨x, hx, hyx.2⟩⟩
    -- apply outer-measure subadditivity
    simpa [hrewrite] using
      (MeasureTheory.measure_biUnion_le (μ := μ) ht_count (fun x => E ∩ Metric.closedBall x (r x)))
  -- Termwise half-measure bound.
  have hsum_le :
      (∑' p : t, μ (E ∩ Metric.closedBall (p : α) (r p)))
        ≤ (1 / 2 : ℝ≥0∞) * (∑' p : t, μ (Metric.closedBall (p : α) (r p))) := by
    have hterm : ∀ p : t,
        μ (E ∩ Metric.closedBall (p : α) (r p))
          ≤ (1 / 2 : ℝ≥0∞) * μ (Metric.closedBall (p : α) (r p)) := by
      intro p
      have hp7 : Metric.closedBall (p : α) (7 * r p) ⊆ O := (_h7 (p : α) p.property).2
      simpa using hball (p : α) (r p) hp7
    have := ENNReal.tsum_le_tsum hterm
    simpa [ENNReal.tsum_mul_left] using this
  -- Compute `μ O` via the disjoint cover.
  have hU_eq : μ U = μ O := by
    have hU_sub : U ⊆ O := by
      intro y hy
      rcases mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
      have hx7 : 0 < r x ∧ Metric.closedBall x (7 * r x) ⊆ O := _h7 x hx
      have hsub : Metric.closedBall x (r x) ⊆ Metric.closedBall x (7 * r x) := by
        refine Metric.closedBall_subset_closedBall ?_
        nlinarith [hx7.1.le]
      exact hx7.2 (hsub hyx)
    have : μ O ≤ μ U := by
      calc
        μ O ≤ μ (U ∪ (O \ U)) := by
              refine measure_mono ?_
              intro y hy
              by_cases hyU : y ∈ U <;> simp [hyU, hy]
        _ ≤ μ U + μ (O \ U) := measure_union_le _ _
        _ = μ U := by simp [U, hcover]
    exact le_antisymm (measure_mono hU_sub) this
  have hO_tsum : μ O = ∑' p : t, μ (Metric.closedBall (p : α) (r p)) := by
    have hmeas : ∀ x ∈ t, MeasurableSet (Metric.closedBall x (r x)) := by
      intro _ _; exact measurableSet_closedBall
    -- `μ U` as a tsum (countable + disjoint)
    have : μ U = ∑' p : t, μ (Metric.closedBall (p : α) (r p)) := by
      simpa [U] using (MeasureTheory.measure_biUnion (μ := μ) (s := t)
        (f := fun x => Metric.closedBall x (r x)) ht_count hdisj hmeas)
    simpa [hU_eq] using this
  -- Finish.
  calc
    μ E ≤ μ (E ∩ U) := hE_le
    _ ≤ ∑' p : t, μ (E ∩ Metric.closedBall (p : α) (r p)) := hE_interU_le
    _ ≤ (1 / 2 : ℝ≥0∞) * ∑' p : t, μ (Metric.closedBall (p : α) (r p)) := hsum_le
    _ = (1 / 2 : ℝ≥0∞) * μ O := by simp [hO_tsum]

end Covering

end MeasureTheory
