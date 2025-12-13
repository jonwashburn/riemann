import Riemann.Mathlib.MeasureTheory.Covering.CalderonZygmund
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Order.Zorn

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

omit [MeasurableSpace α] [BorelSpace α] [HasBesicovitchCovering α] in
/-!
#### A purely topological Whitney ball covering (Zorn/depth argument)

For some CZ/good-λ style arguments it is convenient to have a *geometric* ball covering of an open
proper set `O` by disjoint balls whose fixed dilations cover `O` and touch the boundary.

This lemma is independent of measures and Besicovitch/Vitali families; it is proved by a Zorn
maximality argument using the "depth" function `x ↦ infDist x Oᶜ`.
-/

--omit μ [HasBesicovitchCovering α] [SFinite μ] in
theorem exists_countable_disjoint_ball_covering_three_of_isOpen
    [ProperSpace α] {O : Set α} (hO : IsOpen O) (hO' : O ≠ univ) :
    ∃ (U : Set α) (r : α → ℝ),
      U.Countable ∧ U ⊆ O ∧
        U.PairwiseDisjoint (fun c => Metric.ball c (r c)) ∧
        (∀ c ∈ U, 0 < r c) ∧
        (⋃ c ∈ U, Metric.ball c (3 * r c)) = O ∧
        (∀ c ∈ U, ¬Disjoint (Metric.ball c (7 * r c)) Oᶜ) := by
  classical
  -- Use the depth `d x = infDist x Oᶜ` and radii `r x = d x / 6`.
  let d : α → ℝ := fun x => Metric.infDist x Oᶜ
  let r : α → ℝ := fun x => d x / 6

  -- The family of candidate centre sets: disjoint balls of radius `r`.
  let W : Set (Set α) :=
    {U | U ⊆ O ∧ U.PairwiseDisjoint (fun c => Metric.ball c (r c))}
  obtain ⟨U, hUmax⟩ : ∃ U, Maximal (· ∈ W) U := by
    refine zorn_subset _ ?_
    intro C hCW hchain
    refine ⟨⋃₀ C, ?_, ?_⟩
    · -- `⋃₀ C` is still in `W`
      constructor
      · -- subset of `O`
        intro x hx
        rcases mem_sUnion.mp hx with ⟨s, hsC, hxs⟩
        exact (hCW hsC).1 hxs
      · -- pairwise disjointness of the balls
        -- The chain condition gives directedness, so we can use `pairwiseDisjoint_sUnion`.
        have hdir : DirectedOn (· ⊆ ·) C := hchain.directedOn
        -- `pairwiseDisjoint_sUnion` expects pairwise disjointness on each set in the family.
        -- We use the disjointness provided by membership in `W`.
        have : (⋃₀ C).PairwiseDisjoint (fun c => Metric.ball c (r c)) := by
          -- Convert from `PairwiseDisjoint` to `Pairwise` on `Disjoint` for `pairwiseDisjoint_sUnion`.
          refine (pairwiseDisjoint_sUnion hdir).2 ?_
          intro s hsC
          exact (hCW hsC).2
        simpa [W] using this
    · -- each `s ∈ C` is a subset of `⋃₀ C`
      intro s hsC
      exact subset_sUnion_of_mem hsC

  have hU : U ∈ W := hUmax.1
  have hU_sub : U ⊆ O := hU.1
  have hU_disj : U.PairwiseDisjoint (fun c => Metric.ball c (r c)) := hU.2

  -- Positivity of radii on centres in `U`.
  have hO_compl_ne : Oᶜ.Nonempty := by
    rcases (ne_univ_iff_exists_notMem _).1 hO' with ⟨x, hx⟩
    exact ⟨x, hx⟩
  have hO_closed : IsClosed Oᶜ := isClosed_compl_iff.2 hO
  have hr_pos : ∀ c ∈ U, 0 < r c := by
    intro c hcU
    have hcO : c ∈ O := hU_sub hcU
    have hd_pos : 0 < d c := by
      -- `d c > 0` since `c ∉ Oᶜ` and `Oᶜ` is closed nonempty
      have : c ∉ Oᶜ := by simpa using hcO
      have hiff := (hO_closed.notMem_iff_infDist_pos (x := c) hO_compl_ne)
      exact (hiff.mp this)
    have : 0 < d c / 6 := by nlinarith
    simpa [r] using this

  -- A key geometric estimate: if the radius-balls around `x` and `y` intersect, then
  -- `x ∈ ball y (3 * r y)`.
  have depth_bound_1 :
      ∀ {x y : α},
        ¬Disjoint (Metric.ball x (r x)) (Metric.ball y (r y)) →
          x ∈ Metric.ball y (3 * r y) := by
    intro x y hnd
    rcases Set.not_disjoint_iff.mp hnd with ⟨z, hz₁, hz₂⟩
    have hxz : dist z x < r x := by simpa [Metric.mem_ball] using hz₁
    have hyz : dist z y < r y := by simpa [Metric.mem_ball] using hz₂
    have hxy : dist x y < r x + r y := by
      have : dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      have hxz' : dist x z < r x := by simpa [dist_comm] using hxz
      have hyz' : dist z y < r y := hyz
      exact lt_of_le_of_lt this (by linarith)
    -- Compare depths using `infDist`'s Lipschitz property.
    have hd_le : d x ≤ d y + dist x y := Metric.infDist_le_infDist_add_dist (s := Oᶜ) (x := x) (y := y)
    have hdx_lt : d x < (7 / 5) * d y := by
      -- Use `dist x y < (d x + d y) / 6` to solve for `d x` in terms of `d y`.
      have hdist_le : dist x y < (d x + d y) / 6 := by
        -- rewrite `r x + r y`
        have : r x + r y = (d x + d y) / 6 := by
          simp [r, add_div]
        simpa [this] using hxy
      have : d x < d y + (d x + d y) / 6 := lt_of_le_of_lt hd_le (by linarith)
      linarith
    have hrx_le : r x < (7 / 5) * r y := by
      -- divide by 6
      simpa [r, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_lt_mul_of_pos_right hdx_lt (by positivity : (0 : ℝ) < (1 / 6 : ℝ)))
    -- Now `dist x y < r x + r y < 3 * r y`
    have : dist x y < 3 * r y := by
      have hrx_le' : r x ≤ (7 / 5) * r y := le_of_lt hrx_le
      have hxy2 : dist x y < (7 / 5) * r y + r y := by
        refine lt_of_lt_of_le hxy ?_
        exact add_le_add_right hrx_le' (r y)
      have hry_nonneg : 0 ≤ r y := by
        have hd : 0 ≤ d y := Metric.infDist_nonneg (x := y) (s := Oᶜ)
        have : 0 ≤ d y / 6 := div_nonneg hd (by norm_num)
        simpa [r] using this
      have hle : (7 / 5) * r y + r y ≤ 3 * r y := by
        calc
          (7 / 5 : ℝ) * r y + r y = (12 / 5 : ℝ) * r y := by ring
          _ ≤ (3 : ℝ) * r y := by
              have hcoeff : (12 / 5 : ℝ) ≤ 3 := by norm_num
              exact mul_le_mul_of_nonneg_right hcoeff hry_nonneg
          _ = 3 * r y := by ring
      exact lt_of_lt_of_le hxy2 hle
    simpa [Metric.mem_ball] using this

  -- Show the `3`-dilations cover all of `O`.
  have hcover : (⋃ c ∈ U, Metric.ball c (3 * r c)) = O := by
    refine subset_antisymm ?_ ?_
    · -- LHS ⊆ O since each ball is centred in O and has radius < infDist to Oᶜ
      refine iUnion₂_subset fun c hcU => ?_
      have hcO : c ∈ O := hU_sub hcU
      have hsub : Metric.ball c (3 * r c) ⊆ O := by
        -- `3 * r c < d c`, hence `ball c (3*r c) ⊆ ball c (d c) ⊆ O`
        have hlt : 3 * r c < d c := by
          have hdpos : 0 < d c := by
            have : c ∉ Oᶜ := by simpa using hcO
            have hiff := (hO_closed.notMem_iff_infDist_pos (x := c) hO_compl_ne)
            exact (hiff.mp this)
          have hhalf : d c / 2 < d c := by nlinarith [hdpos]
          have h3 : 3 * r c = d c / 2 := by
            simp [r, div_eq_mul_inv]
            ring
          simpa [h3] using hhalf
        have : Metric.ball c (3 * r c) ⊆ Metric.ball c (d c) :=
          Metric.ball_subset_ball hlt.le
        exact this.trans (by simpa [d] using (Metric.ball_infDist_subset_compl (s := Oᶜ) (x := c)))
      exact hsub
    · intro x hxO
      -- If `x` is not covered, we can add it to `U`, contradicting maximality.
      by_contra hx
      have hx_not : ∀ c ∈ U, Disjoint (Metric.ball x (r x)) (Metric.ball c (r c)) := by
        intro c hcU
        by_contra hnd
        have : x ∈ Metric.ball c (3 * r c) := depth_bound_1 hnd
        exact hx (mem_iUnion₂.mpr ⟨c, hcU, this⟩)
      -- `insert x U` is still in `W` and strictly larger.
      have hW_insert : insert x U ∈ W := by
        refine ⟨?_, ?_⟩
        · intro y hy
          rcases mem_insert_iff.mp hy with rfl | hyU
          · exact hxO
          · exact hU_sub hyU
        · -- disjointness: old ones + new one
          intro a ha b hb hab
          rcases mem_insert_iff.mp ha with rfl | haU
          · rcases mem_insert_iff.mp hb with rfl | hbU
            · exact (hab rfl).elim
            · exact hx_not b hbU
          · rcases mem_insert_iff.mp hb with rfl | hbU
            · exact (hx_not a haU).symm
            · exact hU_disj haU hbU hab
      have hxU_not : x ∉ U := by
        intro hxU
        -- if `x ∈ U` then `x` is covered by its own ball
        exact hx (mem_iUnion₂.mpr ⟨x, hxU, mem_ball_self (by
          have : 0 < r x := hr_pos x hxU
          nlinarith [this])⟩)
      have hss : U ⊂ insert x U := ssubset_insert hxU_not
      have hins : insert x U ⊆ U := hUmax.2 hW_insert hss.le
      have hxU : x ∈ U := hins (by simp)
      exact hxU_not hxU

  -- Boundary touching: each `7`-dilation meets `Oᶜ`.
  have htouch : ∀ c ∈ U, ¬Disjoint (Metric.ball c (7 * r c)) Oᶜ := by
    intro c hcU
    have hcO : c ∈ O := hU_sub hcU
    have hne : Oᶜ.Nonempty := hO_compl_ne
    obtain ⟨y, hyO, hyd⟩ :=
      (hO_closed.exists_infDist_eq_dist hne c)
    -- `y ∈ Oᶜ` and `dist c y = d c < 7 * r c`
    have hyball : y ∈ Metric.ball c (7 * r c) := by
      have : dist y c < 7 * r c := by
        -- `dist y c = d c` and `7 * (d c / 6) > d c`
        have hdist : dist y c = d c := by simpa [d, dist_comm] using hyd.symm
        have hdpos : 0 < d c := by
          have : c ∉ Oᶜ := by simpa using hcO
          have hiff := (hO_closed.notMem_iff_infDist_pos (x := c) hne)
          exact (hiff.mp this)
        have hcoeff : (1 : ℝ) < (7 / 6 : ℝ) := by norm_num
        have hd_lt : d c < (7 / 6 : ℝ) * d c := by
          simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using
            (mul_lt_mul_of_pos_left hcoeff hdpos)
        have : d c < 7 * (d c / 6) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hd_lt
        -- conclude
        exact (hdist.symm ▸ this)
      simpa [Metric.mem_ball] using this
    exact Set.not_disjoint_iff.mpr ⟨y, hyball, hyO⟩

  refine ⟨U, r, ?_, hU_sub, hU_disj, hr_pos, hcover, htouch⟩
  -- Countability of `U` from disjointness of open balls.
  have : U.Countable := by
    -- `PairwiseDisjoint` + open + nonempty in a separable space
    have hne_ball : ∀ c ∈ U, (Metric.ball c (r c)).Nonempty := by
      intro c hcU
      exact Metric.nonempty_ball.2 (hr_pos c hcU)
    have hopen : ∀ c ∈ U, IsOpen (Metric.ball c (r c)) := by
      intro c _; exact isOpen_ball
    have hsep : TopologicalSpace.SeparableSpace α := by infer_instance
    exact hU_disj.countable_of_isOpen hopen hne_ball
  exact this

/-!
#### Picking radii with null spheres

To pass from closed balls to open balls in covering arguments, it is convenient to pick radii `r`
such that the boundary sphere `sphere x r` has measure `0`. The set of exceptional radii is
countable (as it sits inside the discontinuity set of the monotone function
`r ↦ μ (closedBall x r)`), hence we can always pick such an `r` inside any nontrivial interval.
-/

omit [SecondCountableTopology α] [HasBesicovitchCovering α] in
lemma countable_setOf_measure_sphere_ne_zero [SFinite μ] (x : α) :
    Set.Countable {r : ℝ | μ (Metric.sphere x r) ≠ 0} := by
  classical
  -- In an s-finite space, only countably many level sets of a measurable function can have
  -- positive measure. Apply this to `y ↦ dist y x`.
  let g : α → ℝ := fun y => dist y x
  have hg : Measurable g := (continuous_id.dist continuous_const).measurable
  have hcount : Set.Countable {r : ℝ | 0 < μ {y : α | g y = r} } :=
    Measure.countable_meas_level_set_pos (μ := μ) (g := g) hg
  simpa [g, Metric.sphere, pos_iff_ne_zero] using hcount

/-- A Whitney-style a.e. covering of an open set by disjoint **open** balls.

This is a strengthening of `exists_disjoint_closedBall_covering_ae_of_isOpen` where the chosen radii
have null spheres, hence we can replace closed balls by open balls without changing the covered set
up to a null set. -/
theorem exists_disjoint_ball_covering_ae_of_isOpen
    [SFinite μ] {O : Set α} (hO : IsOpen O) :
    ∃ (t : Set α) (r : α → ℝ),
      t.Countable ∧ t ⊆ O ∧
        (∀ x ∈ t, 0 < r x ∧ Metric.closedBall x (7 * r x) ⊆ O ∧ μ (Metric.sphere x (r x)) = 0) ∧
        μ (O \ ⋃ x ∈ t, Metric.ball x (r x)) = 0 ∧
        t.PairwiseDisjoint (fun x => Metric.ball x (r x)) := by
  classical
  -- Admissible radii at `x`: those whose `7`-closed-ball stays inside `O` and whose sphere is null.
  let f : α → Set ℝ := fun x =>
    {r | 0 < r ∧ Metric.closedBall x (7 * r) ⊆ O ∧ μ (Metric.sphere x r) = 0}
  have hf : ∀ x ∈ O, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ hδ
    rcases Metric.isOpen_iff.mp hO x hx with ⟨ε, hε, hεO⟩
    -- first choose a small radius `r₀` so that `closedBall x (7*r₀) ⊆ O` and `r₀ < δ`
    let r₀ : ℝ := min (ε / 8) (δ / 2)
    have hr₀_pos : 0 < r₀ := by
      have hε8 : 0 < ε / 8 := by positivity
      have hδ2 : 0 < δ / 2 := by positivity
      exact lt_min hε8 hδ2
    have hr₀_lt_δ : r₀ < δ := by
      have : δ / 2 < δ := by linarith
      exact (min_le_right _ _).trans_lt this
    have h7r₀_sub : Metric.closedBall x (7 * r₀) ⊆ O := by
      -- `closedBall x (7*r₀) ⊆ ball x ε ⊆ O`
      have h7r₀_lt : (7 : ℝ) * r₀ < ε := by
        have hle : (7 : ℝ) * r₀ ≤ 7 * (ε / 8) := by gcongr; exact min_le_left _ _
        have hlt : (7 : ℝ) * (ε / 8) < ε := by nlinarith
        exact lt_of_le_of_lt hle hlt
      intro y hy
      have : dist y x < ε := by
        have : dist y x ≤ 7 * r₀ := by simpa [Metric.mem_closedBall, dist_comm, mul_assoc] using hy
        exact lt_of_le_of_lt this h7r₀_lt
      exact hεO (by simpa [Metric.mem_ball, dist_comm] using this)
    -- now pick `r ∈ (0, r₀)` outside the countable exceptional set `{r | μ (sphere x r) ≠ 0}`.
    have hcount : Set.Countable {r : ℝ | μ (Metric.sphere x r) ≠ 0} :=
      countable_setOf_measure_sphere_ne_zero (μ := μ) x
    have hdense : Dense ({r : ℝ | μ (Metric.sphere x r) ≠ 0}ᶜ) :=
      Set.Countable.dense_compl (𝕜 := ℝ) (E := ℝ) hcount
    have hopen : IsOpen (Ioo (0 : ℝ) r₀) := isOpen_Ioo
    have hne : (Ioo (0 : ℝ) r₀).Nonempty := by
      refine ⟨r₀ / 2, ?_⟩
      have hr2_pos : 0 < r₀ / 2 := by positivity
      have hr2_lt : r₀ / 2 < r₀ := by linarith
      exact ⟨hr2_pos, hr2_lt⟩
    rcases hdense.exists_mem_open hopen hne with ⟨r, hr_mem, hrIoo⟩
    have hr_sphere : μ (Metric.sphere x r) = 0 := by
      have : ¬ μ (Metric.sphere x r) ≠ 0 := by
        simpa [Set.mem_compl_iff, Set.mem_setOf_eq] using hr_mem
      exact by simpa using this
    -- conclude
    refine ⟨r, ?_⟩
    have hr_pos : 0 < r := hrIoo.1
    have hr_lt_r₀ : r < r₀ := hrIoo.2
    have hr_lt_δ : r < δ := by
      have hr_lt_δ2 : r < δ / 2 := by
        exact lt_of_lt_of_le hr_lt_r₀ (min_le_right _ _)
      have hδ2_lt_δ : δ / 2 < δ := by linarith
      exact hr_lt_δ2.trans hδ2_lt_δ
    have h7r_sub : Metric.closedBall x (7 * r) ⊆ O := by
      refine (Metric.closedBall_subset_closedBall ?_).trans h7r₀_sub
      nlinarith [hr_lt_r₀.le]
    refine ⟨?_, ?_⟩
    · exact ⟨hr_pos, h7r_sub, hr_sphere⟩
    · exact ⟨hr_pos, hr_lt_δ⟩
  -- Apply Besicovitch covering theorem with any positive radius bound, say `R = 1`.
  obtain ⟨t, r, ht_count, htO, hrt, hcover, hdisj⟩ :=
    exists_disjoint_closedBall_covering_ae (μ := μ) f O hf (fun _ => (1 : ℝ)) (fun _ _ => one_pos)
  -- Translate the conclusions from closed balls to open balls (the boundary has measure `0`).
  refine ⟨t, r, ht_count, htO, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := hrt x hx
    refine ⟨hx'.1.1, hx'.1.2.1, hx'.1.2.2⟩
  · -- `O` is covered a.e. by the open balls as well
    have hsphere0 : ∀ x ∈ t, μ (Metric.sphere x (r x)) = 0 := by
      intro x hx
      exact (hrt x hx).1.2.2
    have hnull_sphere :
        μ (⋃ x ∈ t, Metric.sphere x (r x)) = 0 := by
      simpa using (MeasureTheory.measure_biUnion_null_iff (μ := μ) ht_count (s := fun x => Metric.sphere x (r x))).2
        hsphere0
    have hsub :
        O \ ⋃ x ∈ t, Metric.ball x (r x) ⊆
          (O \ ⋃ x ∈ t, Metric.closedBall x (r x)) ∪ ⋃ x ∈ t, Metric.sphere x (r x) := by
      intro y hy
      by_cases hyc : y ∈ ⋃ x ∈ t, Metric.closedBall x (r x)
      · -- then `y` lies on some sphere, since it is not in the corresponding open ball
        right
        rcases mem_iUnion₂.mp hyc with ⟨x, hx, hyx⟩
        have hyb : y ∉ Metric.ball x (r x) := by
          intro hyb
          exact hy.2 (mem_iUnion₂.mpr ⟨x, hx, hyb⟩)
        refine mem_iUnion₂.mpr ⟨x, hx, ?_⟩
        -- `y ∈ closedBall` and `y ∉ ball` means `y ∈ sphere`
        have hy_le : dist y x ≤ r x := by
          simpa [Metric.mem_closedBall] using hyx
        have hy_ge : r x ≤ dist y x := by
          have : ¬ dist y x < r x := by
            simpa [Metric.mem_ball] using hyb
          exact not_lt.mp this
        have hy_eq : dist y x = r x := le_antisymm hy_le hy_ge
        simpa [Metric.mem_sphere] using hy_eq
      · left
        exact ⟨hy.1, hyc⟩
    have : μ (O \ ⋃ x ∈ t, Metric.ball x (r x)) ≤
        μ (O \ ⋃ x ∈ t, Metric.closedBall x (r x)) + μ (⋃ x ∈ t, Metric.sphere x (r x)) :=
      (measure_mono hsub) |>.trans (measure_union_le _ _)
    -- both terms are zero
    have : μ (O \ ⋃ x ∈ t, Metric.ball x (r x)) = 0 := by
      have h0 : μ (O \ ⋃ x ∈ t, Metric.closedBall x (r x)) = 0 := hcover
      simpa [h0, hnull_sphere] using le_antisymm (this.trans (by simp [h0, hnull_sphere])) bot_le
    exact this
  · -- pairwise disjointness passes from closed balls to balls
    exact hdisj.mono fun _ => Metric.ball_subset_closedBall

/-- Ball-version of `measure_le_half_of_isOpen_of_forall_ball`.

The proof uses `exists_disjoint_ball_covering_ae_of_isOpen` so that we can sum over disjoint open
balls and apply local bounds stated on open balls. -/
theorem measure_le_half_of_isOpen_of_forall_ball'
    [SFinite μ] {O E : Set α} (hO : IsOpen O) (hE : E ⊆ O)
    (hball : ∀ (x : α) (r : ℝ), Metric.closedBall x (7 * r) ⊆ O →
      μ (E ∩ Metric.ball x r) ≤ (1 / 2 : ℝ≥0∞) * μ (Metric.ball x r)) :
    μ E ≤ (1 / 2 : ℝ≥0∞) * μ O := by
  classical
  obtain ⟨t, r, ht_count, htO, hrt, hcover, hdisj⟩ :=
    exists_disjoint_ball_covering_ae_of_isOpen (μ := μ) (O := O) hO
  let U : Set α := ⋃ x ∈ t, Metric.ball x (r x)
  have hU_sub : U ⊆ O := by
    intro y hy
    rcases mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
    have hx7 : Metric.closedBall x (7 * r x) ⊆ O := (hrt x hx).2.1
    have hsub : Metric.ball x (r x) ⊆ Metric.closedBall x (7 * r x) := by
      refine Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall ?_)
      nlinarith [(hrt x hx).1.le]
    exact hx7 (hsub hyx)
  have hE_diff : μ (E \ U) = 0 := by
    have hsub : E \ U ⊆ O \ U := by
      intro y hy; exact ⟨hE hy.1, hy.2⟩
    exact measure_mono_null hsub hcover
  have hE_le : μ E ≤ μ (E ∩ U) := by
    have hsplit : μ E ≤ μ (E ∩ U) + μ (E \ U) :=
      MeasureTheory.measure_le_inter_add_diff (μ := μ) E U
    simpa [hE_diff] using hsplit
  have hEU_le :
      μ (E ∩ U) ≤ ∑' p : t, μ (E ∩ Metric.ball (p : α) (r p)) := by
    have hrewrite : E ∩ U = ⋃ x ∈ t, E ∩ Metric.ball x (r x) := by
      ext y; constructor
      · intro hy
        rcases hy with ⟨hyE, hyU⟩
        rcases mem_iUnion₂.mp hyU with ⟨x, hx, hyx⟩
        exact mem_iUnion₂.mpr ⟨x, hx, ⟨hyE, hyx⟩⟩
      · intro hy
        rcases mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
        exact ⟨hyx.1, mem_iUnion₂.mpr ⟨x, hx, hyx.2⟩⟩
    simpa [hrewrite] using
      (MeasureTheory.measure_biUnion_le (μ := μ) ht_count (fun x => E ∩ Metric.ball x (r x)))
  have hsum_le :
      (∑' p : t, μ (E ∩ Metric.ball (p : α) (r p)))
        ≤ (1 / 2 : ℝ≥0∞) * (∑' p : t, μ (Metric.ball (p : α) (r p))) := by
    have hterm : ∀ p : t,
        μ (E ∩ Metric.ball (p : α) (r p))
          ≤ (1 / 2 : ℝ≥0∞) * μ (Metric.ball (p : α) (r p)) := by
      intro p
      have hp7 : Metric.closedBall (p : α) (7 * r p) ⊆ O := (hrt (p : α) p.property).2.1
      simpa using hball (p : α) (r p) hp7
    have := ENNReal.tsum_le_tsum hterm
    simpa [ENNReal.tsum_mul_left] using this
  have hO_tsum : μ O = ∑' p : t, μ (Metric.ball (p : α) (r p)) := by
    have hU_eq : μ U = μ O := by
      have : μ O ≤ μ U := by
        calc
          μ O ≤ μ (U ∪ (O \ U)) := by
                refine measure_mono ?_
                intro y hy
                by_cases hyU : y ∈ U <;> simp [hyU, hy]
          _ ≤ μ U + μ (O \ U) := measure_union_le _ _
          _ = μ U := by simp [U, hcover]
      exact le_antisymm (measure_mono hU_sub) this
    have hmeas : ∀ x ∈ t, MeasurableSet (Metric.ball x (r x)) := by
      intro _ _; exact isOpen_ball.measurableSet
    have hU_tsum : μ U = ∑' p : t, μ (Metric.ball (p : α) (r p)) := by
      simpa [U] using (MeasureTheory.measure_biUnion (μ := μ) (s := t)
        (f := fun x => Metric.ball x (r x)) ht_count (hdisj) hmeas)
    simpa [hU_eq] using hU_tsum
  -- Finish.
  calc
    μ E ≤ μ (E ∩ U) := hE_le
    _ ≤ ∑' p : t, μ (E ∩ Metric.ball (p : α) (r p)) := hEU_le
    _ ≤ (1 / 2 : ℝ≥0∞) * ∑' p : t, μ (Metric.ball (p : α) (r p)) := hsum_le
    _ = (1 / 2 : ℝ≥0∞) * μ O := by simp [hO_tsum]

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
