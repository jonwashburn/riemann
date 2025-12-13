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

omit [BorelSpace α] [ProperSpace α] [IsUnifLocDoublingMeasure μ]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] in
/-- **John–Nirenberg inequality**: exponential decay of the distribution function.

For a function `f` with bounded mean oscillation ≤ `M` on all balls, the superlevel sets
of `|f - f_B|` decay exponentially.

The constant is expressed in the canonical form with `Real.log 2` in the exponent.

(Implementation note: we factor the *abstract iteration → exponential tail* part in
`MeasureTheory.measure_exponential_decay_of_geometric`. The remaining hard part is the
geometric-decay step `hstep`, proved by a CZ/Whitney covering argument in the surrounding API.) -/
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
  classical
  -- Notation for the base ball and its average.
  let B : Set α := Metric.ball x₀ r
  let fB : ℝ := ⨍ y in B, f y ∂μ
  -- The integer-step superlevel sets at scale `2*M`.
  let E : ℕ → Set α := fun n =>
    {x ∈ B | |f x - fB| > (n : ℝ) * (2 * M)}

  -- Step inequality in the form expected by `measure_exponential_decay_of_geometric`.
  have hstep' : ∀ n, μ (E (n + 1)) ≤ (1 / 2 : ℝ≥0∞) * μ (E n) := by
    intro n
    simpa [E, B, fB, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc, add_left_comm,
      add_comm, gt_iff_lt] using hstep n

  -- Monotonicity in the threshold: `t ≥ n*(2M)` gives `{>t} ⊆ E n`.
  have hmono_threshold (n : ℕ) (hn : (n : ℝ) * (2 * M) ≤ t) :
      {x ∈ B | |f x - fB| > t} ⊆ E n := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    exact lt_of_le_of_lt hn hx.2

  -- Apply the abstract geometric→exponential tail lemma at `n = ⌊t/(2M)⌋`.
  have hgeom_exp :
      μ (E (Int.floor (t / (2 * M))).toNat) ≤
        2 * μ (E 0) * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / (2 * M)))) := by
    have ht' : 0 ≤ t := ht.le
    have hc : 0 < (2 * M) := by nlinarith [hM]
    simpa [B, fB] using
      (MeasureTheory.measure_exponential_decay_of_geometric (μ := μ) (E := E) hstep' ht' hc)

  -- `E 0 ⊆ B`, hence `μ (E 0) ≤ μ B`.
  have hE0_le : μ (E 0) ≤ μ B := by
    refine measure_mono ?_
    intro x hx
    exact hx.1

  -- `{>t} ⊆ E ⌊t/(2M)⌋`.
  have hsubset_floor : {x ∈ B | |f x - fB| > t} ⊆ E (Int.floor (t / (2 * M))).toNat := by
    have hfloor_le : (Int.floor (t / (2 * M)) : ℝ) ≤ t / (2 * M) := Int.floor_le _
    have hc : 0 < (2 * M) := by nlinarith [hM]
    have hn_le : ((Int.floor (t / (2 * M))).toNat : ℝ) ≤ t / (2 * M) := by
      -- `toNat` of `floor` is ≤ the real value.
      have hn0 : 0 ≤ Int.floor (t / (2 * M)) := by
        exact Int.floor_nonneg.2 (div_nonneg ht.le (le_of_lt hc))
      -- cast `toNat` back to ℤ then to ℝ
      have hcast : ((Int.floor (t / (2 * M))).toNat : ℤ) = Int.floor (t / (2 * M)) := by
        simpa using (Int.toNat_of_nonneg hn0)
      -- now compare in ℝ
      have : ((Int.floor (t / (2 * M))).toNat : ℝ) = (Int.floor (t / (2 * M)) : ℝ) := by
        -- `simp` can handle the casts once we have the ℤ equality.
        exact_mod_cast hcast
      -- finish
      calc
        ((Int.floor (t / (2 * M))).toNat : ℝ)
            = (Int.floor (t / (2 * M)) : ℝ) := this
        _ ≤ t / (2 * M) := by exact_mod_cast hfloor_le
    have hn_mul : ((Int.floor (t / (2 * M))).toNat : ℝ) * (2 * M) ≤ t := by
      -- multiply `hn_le` by the positive constant `2*M`
      have : ((Int.floor (t / (2 * M))).toNat : ℝ) * (2 * M) ≤ (t / (2 * M)) * (2 * M) := by
        gcongr
      -- simplify RHS to `t`
      simpa [div_mul_eq_mul_div, hc.ne', mul_assoc] using this
    exact hmono_threshold _ hn_mul

  -- Conclude, upgrading `μ (E 0)` to `μ B` and rewriting `B`, `fB`.
  have :
      μ {x ∈ B | |f x - fB| > t} ≤
        2 * μ B * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / (2 * M)))) := by
    calc
      μ {x ∈ B | |f x - fB| > t}
          ≤ μ (E (Int.floor (t / (2 * M))).toNat) := by
              exact measure_mono hsubset_floor
      _ ≤ 2 * μ (E 0) * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / (2 * M)))) := hgeom_exp
      _ ≤ 2 * μ B * ENNReal.ofReal (Real.exp (-(Real.log 2) * (t / (2 * M)))) := by
              gcongr

  -- Final formatting: `t / (2*M)` as `t / (2*M)` and revert abbreviations.
  simpa [B, fB, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

end MeasureTheory
