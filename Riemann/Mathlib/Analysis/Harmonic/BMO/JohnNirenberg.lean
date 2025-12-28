import Riemann.Mathlib.Analysis.Harmonic.BMO.Defs
import Riemann.Mathlib.MeasureTheory.Covering.CalderonZygmund
import Riemann.Mathlib.MeasureTheory.Covering.JohnNirenberg
import Riemann.Mathlib.Analysis.Harmonic.BMOAux

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

 variable {α : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α] {μ : Measure α}

/-!
### John–Nirenberg inequality

This file is intended to contain the *nontrivial* John–Nirenberg exponential decay for BMO.

We keep the assumptions split so that later we can provide both:
- a **local-doubling** version (using `IsUnifLocDoublingMeasure`), and
- a **global-doubling** version (using `MeasureTheory.Measure.IsDoubling` from the Carleson library).
-/

variable [ProperSpace α] [IsUnifLocDoublingMeasure μ]
variable [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]

/-!
### Global-doubling John–Nirenberg

TODO: add a globally doubling version (Carleson API) that derives the geometric step internally.
-/

omit [BorelSpace α] [ProperSpace α] [IsUnifLocDoublingMeasure μ]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] in
/-- Exponential tail from a `1/2` geometric step at linear thresholds.

For a function `f` with bounded mean oscillation ≤ `M` on all balls, the superlevel sets
of `|f - f_B|` decay exponentially.

The constant is expressed in the canonical form with `Real.log 2` in the exponent.

(Implementation note: we factor the *abstract iteration → exponential tail* part in
`MeasureTheory.measure_exponential_decay_of_geometric`. The remaining hard part is the
geometric-decay step `hstep`, proved by a CZ/stopping-time covering argument.) -/
theorem johnNirenberg_exponential_decay_of_hstep {f : α → ℝ} {x₀ : α} {r : ℝ} (_hr : 0 < r)
    (_hf_loc : LocallyIntegrable f μ) {M : ℝ} (_hM : 0 < M)
    (_hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    {c : ℝ} (hc : 0 < c)
    (hstep : ∀ n : ℕ,
      μ {x ∈ Metric.ball x₀ r |
          |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > (n + 1 : ℝ) * c} ≤
        (1 / 2 : ℝ≥0∞) *
          μ {x ∈ Metric.ball x₀ r |
            |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > (n : ℝ) * c})
    {t : ℝ} (ht : 0 < t) :
    μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > t} ≤
      2 * μ (Metric.ball x₀ r) *
        ENNReal.ofReal (Real.exp (-(Real.log 2) * t / c)) := by
  classical
  -- Notation for the base ball and its average.
  let B : Set α := Metric.ball x₀ r
  let fB : ℝ := ⨍ y in B, f y ∂μ
  -- The integer-step superlevel sets at scale `2*M`.
  let E : ℕ → Set α := fun n =>
    {x ∈ B | |f x - fB| > (n : ℝ) * c}
  -- Step inequality in the form expected by `measure_exponential_decay_of_geometric`.
  have hstep' : ∀ n, μ (E (n + 1)) ≤ (1 / 2 : ℝ≥0∞) * μ (E n) := by
    intro n
    simpa [E, B, fB, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc, add_left_comm,
      add_comm, gt_iff_lt] using hstep n
  -- Monotonicity in the threshold: `t ≥ n*(2M)` gives `{>t} ⊆ E n`.
  have hmono_threshold (n : ℕ) (hn : (n : ℝ) * c ≤ t) :
      {x ∈ B | |f x - fB| > t} ⊆ E n := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    exact lt_of_le_of_lt hn hx.2
  -- Apply the abstract geometric→exponential tail lemma at `n = ⌊t/c⌋`.
  have hgeom_exp :
      μ (E (Int.floor (t / c)).toNat) ≤
        2 * μ (E 0) * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / c))) := by
    have ht' : 0 ≤ t := ht.le
    have hc' : 0 < c := hc
    simpa [B, fB] using
      (MeasureTheory.measure_exponential_decay_of_geometric (μ := μ) (E := E) hstep' ht' hc')
  -- `E 0 ⊆ B`, hence `μ (E 0) ≤ μ B`.
  have hE0_le : μ (E 0) ≤ μ B := by
    refine measure_mono ?_
    intro x hx
    exact hx.1
  -- `{>t} ⊆ E ⌊t/(2M)⌋`.
  have hsubset_floor : {x ∈ B | |f x - fB| > t} ⊆ E (Int.floor (t / c)).toNat := by
    have hfloor_le : (Int.floor (t / c) : ℝ) ≤ t / c := Int.floor_le _
    have hc' : 0 < c := hc
    have hn_le : ((Int.floor (t / c)).toNat : ℝ) ≤ t / c := by
      -- `toNat` of `floor` is ≤ the real value.
      have hn0 : 0 ≤ Int.floor (t / c) := by
        exact Int.floor_nonneg.2 (div_nonneg ht.le (le_of_lt hc'))
      -- cast `toNat` back to ℤ then to ℝ
      have hcast : ((Int.floor (t / c)).toNat : ℤ) = Int.floor (t / c) := by
        simpa using (Int.toNat_of_nonneg hn0)
      -- now compare in ℝ
      have : ((Int.floor (t / c)).toNat : ℝ) = (Int.floor (t / c) : ℝ) := by
        -- `simp` can handle the casts once we have the ℤ equality.
        exact_mod_cast hcast
      calc
        ((Int.floor (t / c)).toNat : ℝ)
            = (Int.floor (t / c) : ℝ) := this
        _ ≤ t / c := by exact_mod_cast hfloor_le
    have hn_mul : ((Int.floor (t / c)).toNat : ℝ) * c ≤ t := by
      -- multiply `hn_le` by the positive constant `c`
      have : ((Int.floor (t / c)).toNat : ℝ) * c ≤ (t / c) * c := by
        gcongr
      -- simplify RHS to `t`
      simpa [div_mul_eq_mul_div, hc'.ne', mul_assoc] using this
    exact hmono_threshold _ hn_mul
  -- Conclude, upgrading `μ (E 0)` to `μ B` and rewriting `B`, `fB`.
  have :
      μ {x ∈ B | |f x - fB| > t} ≤
        2 * μ B * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / c))) := by
    calc
      μ {x ∈ B | |f x - fB| > t}
          ≤ μ (E (Int.floor (t / c)).toNat) := by
              exact measure_mono hsubset_floor
      _ ≤ 2 * μ (E 0) * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / c))) := hgeom_exp
      _ ≤ 2 * μ B * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / c))) := by
              gcongr
  simpa [B, fB, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

omit [BorelSpace α] [ProperSpace α] [IsUnifLocDoublingMeasure μ]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] in
/-- Convenience wrapper of `johnNirenberg_exponential_decay_of_hstep` with the step size `c = 2*M`. -/
theorem johnNirenberg_exponential_decay {f : α → ℝ} {x₀ : α} {r : ℝ} (_hr : 0 < r)
    (_hf_loc : LocallyIntegrable f μ) {M : ℝ} (hM : 0 < M)
    (_hmo : ∀ (x : α) (r : ℝ) (_ : 0 < r),
      ⨍ y in Metric.ball x r, |f y - ⨍ z in Metric.ball x r, f z ∂μ| ∂μ ≤ M)
    (hstep : ∀ n : ℕ,
      μ {x ∈ Metric.ball x₀ r |
          |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > (n + 1 : ℝ) * (2 * M)} ≤
        (1 / 2 : ℝ≥0∞) *
          μ {x ∈ Metric.ball x₀ r |
            |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > (n : ℝ) * (2 * M)})
    {t : ℝ} (ht : 0 < t) :
    μ {x ∈ Metric.ball x₀ r | |f x - ⨍ y in Metric.ball x₀ r, f y ∂μ| > t} ≤
      2 * μ (Metric.ball x₀ r) *
        ENNReal.ofReal (Real.exp (-(Real.log 2) * t / (2 * M))) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (johnNirenberg_exponential_decay_of_hstep (μ := μ) (f := f) (x₀ := x₀) (r := r)
      _hr _hf_loc hM _hmo (c := 2 * M) (by nlinarith [hM]) hstep ht)

end MeasureTheory
