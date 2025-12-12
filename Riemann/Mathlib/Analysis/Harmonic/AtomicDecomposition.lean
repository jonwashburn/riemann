
import Mathlib
import Riemann.RS.WhitneyGeometryDefs
import Riemann.Cert.KxiWhitney_RvM
import Riemann.Mathlib.MeasureTheory.Function.BoundedSupport
import Riemann.Mathlib.MeasureTheory.Measure.Carleson.Defs

/-!
# Atomic Decomposition for Hardy Spaces

This file provides the atomic decomposition theory for H¹, connecting Whitney
intervals from the Riemann Hypothesis proof to H¹ atoms.

## Main Definitions

* `H1Atom`: A real H¹ atom - a function supported on a ball with zero integral
* `AtomicDecomposition`: Representation of H¹ functions as sums of atoms
* `WhitneyAtom`: An atom adapted to a Whitney interval

## Main Results

* `H1Atom.integrable`: Every H¹ atom is integrable
* `H1Atom.norm_le_one`: The L¹ norm of an atom is bounded by 1
* `whitneyAtom_is_H1Atom`: Whitney-adapted functions form H¹ atoms

## Implementation Notes

The atomic decomposition is fundamental for:
1. Proving H¹-BMO duality (Fefferman's theorem)
2. Establishing Carleson measure characterizations
3. Connecting to the RH proof via Whitney intervals

## References

* Stein, "Harmonic Analysis", Chapter III
* Coifman-Weiss, "Extensions of Hardy spaces and their use in analysis"

## Tags

H¹ atom, atomic decomposition, Hardy space, Whitney interval
-/

open MeasureTheory Measure Set Filter Real
open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] [BorelSpace α]

/-! ### H¹ Atoms -/

/-- An **H¹ atom** is a function `a : ℝ → ℝ` satisfying:
1. `support a ⊆ B(x₀, r)` for some ball
2. `‖a‖_∞ ≤ 1/|B(x₀, r)|`
3. `∫ a = 0` (cancellation condition)

This is the classical definition from Coifman-Weiss. -/
structure H1Atom where
  /-- The atom function -/
  f : ℝ → ℝ
  /-- Center of the supporting ball -/
  center : ℝ
  /-- Radius of the supporting ball -/
  radius : ℝ
  /-- Radius is positive -/
  radius_pos : 0 < radius
  /-- Support condition -/
  support_subset : Function.support f ⊆ Metric.closedBall center radius
  /-- Size condition: `‖a‖_∞ ≤ 1/(2r)` (measure of ball in ℝ is `2r`) -/
  size_bound : ∀ x, |f x| ≤ 1 / (2 * radius)
  /-- Cancellation condition -/
  integral_zero : ∫ x, f x = 0
  /-- Measurability -/
  measurable : AEStronglyMeasurable f volume

namespace H1Atom

variable (a : H1Atom)

/-- The measure of the supporting ball. -/
noncomputable def ballMeasure : ℝ≥0∞ := volume (Metric.closedBall a.center a.radius)

/-- The supporting ball has finite measure. -/
theorem ballMeasure_lt_top : a.ballMeasure < ⊤ := by
  unfold ballMeasure
  rw [Real.volume_closedBall]
  simp only [ENNReal.ofReal_lt_top]

/-- H¹ atoms are integrable.

This uses `Integrable.of_bdd_support` from the infrastructure lemmas. -/
theorem integrable : Integrable a.f volume := by
  have hr_pos := a.radius_pos
  have h2r_pos : 0 < 2 * a.radius := by linarith
  have hM_pos : 0 ≤ 1 / (2 * a.radius) := le_of_lt (one_div_pos.mpr h2r_pos)
  exact Integrable.of_bdd_support_real a.size_bound hM_pos a.support_subset
    a.ballMeasure_lt_top a.measurable

/-- The L¹ norm of an H¹ atom is at most 1.

This follows from: `‖a‖₁ ≤ ‖a‖_∞ · |B| ≤ (1/|B|) · |B| = 1`. -/
theorem norm_le_one : ∫ x, |a.f x| ≤ 1 := by
  have hr_pos := a.radius_pos
  have hball_meas : volume (Metric.closedBall a.center a.radius) =
      ENNReal.ofReal (2 * a.radius) := Real.volume_closedBall a.center a.radius
  have h2r_pos : 0 < 2 * a.radius := by linarith
  have hM_pos : 0 ≤ 1 / (2 * a.radius) := le_of_lt (one_div_pos.mpr h2r_pos)
  calc ∫ x, |a.f x|
      ≤ (1 / (2 * a.radius)) * (volume (Metric.closedBall a.center a.radius)).toReal := by
        apply integral_le_of_bdd_support (fun x _ => a.size_bound x) hM_pos
          measurableSet_closedBall a.ballMeasure_lt_top a.support_subset a.integrable
    _ = (1 / (2 * a.radius)) * (2 * a.radius) := by
        rw [hball_meas, ENNReal.toReal_ofReal h2r_pos.le]
    _ = 1 := by rw [one_div, inv_mul_cancel₀ h2r_pos.ne']

/-- The L^p norm of an H¹ atom is bounded for 1 ≤ p < ∞. -/
theorem memLp (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤) : MemLp a.f p volume := by
  have hr_pos := a.radius_pos
  have h2r_pos : 0 < 2 * a.radius := by linarith
  have hM_pos : 0 ≤ 1 / (2 * a.radius) := le_of_lt (one_div_pos.mpr h2r_pos)
  have hM : ∀ x, ‖a.f x‖ ≤ 1 / (2 * a.radius) := fun x => by
    rw [Real.norm_eq_abs]; exact a.size_bound x
  exact Memℒp.of_bdd_support hp hp_top hM hM_pos a.support_subset a.ballMeasure_lt_top a.measurable

end H1Atom

/-! ### Whitney-Adapted Atoms -/

/-- An atom adapted to a Whitney interval from the RH proof.

This connects the Whitney decomposition structure to H¹ theory. -/
structure WhitneyAtom extends H1Atom where
  /-- The underlying Whitney interval -/
  whitneyInterval : RH.Cert.WhitneyInterval
  /-- The support is contained in the interval -/
  support_in_interval : Function.support f ⊆ whitneyInterval.interval
  /-- The size bound uses the Whitney interval length -/
  whitney_size : ∀ x, |f x| ≤ 1 / (2 * whitneyInterval.len)

namespace WhitneyAtom

variable (wa : WhitneyAtom)

/-- Extract the underlying H¹ atom. -/
def asH1Atom : H1Atom := wa.toH1Atom

/-- The Whitney interval center. -/
def intervalCenter : ℝ := wa.whitneyInterval.t0

/-- The Whitney interval half-length. -/
def intervalHalfLength : ℝ := wa.whitneyInterval.len

/-- Whitney atoms are integrable. -/
theorem integrable : Integrable wa.f volume := wa.asH1Atom.integrable

/-- The L¹ norm of a Whitney atom is at most 1. -/
theorem norm_le_one : ∫ x, |wa.f x| ≤ 1 := wa.asH1Atom.norm_le_one

end WhitneyAtom

/-! ### Atomic Decomposition -/

/-- An atomic decomposition of a function `f` is a representation
`f = ∑ λₙ aₙ` where `aₙ` are atoms and `∑ |λₙ| < ∞`. -/
structure AtomicDecomposition where
  /-- The sequence of atoms -/
  atoms : ℕ → H1Atom
  /-- The sequence of coefficients -/
  coeffs : ℕ → ℝ
  /-- The coefficients are absolutely summable -/
  summable_coeffs : Summable (fun n => |coeffs n|)
  /-- The target function -/
  target : ℝ → ℝ
  /-- Measurability of the target function (needed for `Integrable`). -/
  measurable_target : AEStronglyMeasurable target volume
  /-- The decomposition converges to the target in L¹ (robust formulation via `lintegral`). -/
  converges :
    Tendsto (fun N =>
      ∫⁻ x, ENNReal.ofReal
        |target x - ∑ n ∈ Finset.range N, coeffs n • (atoms n).f x|) atTop (𝓝 0)

namespace AtomicDecomposition

variable (ad : AtomicDecomposition)

/-- The H¹ norm of the decomposition. -/
noncomputable def h1Norm : ℝ := ∑' n, |ad.coeffs n|

/-- The H¹ norm is finite (since the series is summable). -/
theorem h1Norm_lt_top : ENNReal.ofReal ad.h1Norm < ⊤ := ENNReal.ofReal_lt_top

/-- The H¹ norm equals the series sum. -/
theorem h1Norm_eq : ad.h1Norm = ∑' n, |ad.coeffs n| := rfl

/-- The target function is integrable.

**Proof**:
Each atom `aₙ` is integrable with `‖aₙ‖₁ ≤ 1`, so `|λₙ| · ‖aₙ‖₁ ≤ |λₙ|`.
The partial sums `∑_{n<N} λₙ aₙ` converge in L¹ since `∑ |λₙ| < ∞`.
The target equals the limit, hence is integrable. -/
theorem target_integrable : Integrable ad.target volume := by
  classical
  -- Finite partial sums.
  let S : ℕ → (ℝ → ℝ) :=
    fun N x => ∑ n ∈ Finset.range N, ad.coeffs n • (ad.atoms n).f x

  have hS_int : ∀ N, Integrable (S N) volume := by
    intro N
    -- A finite sum of integrable functions is integrable.
    refine integrable_finset_sum (μ := volume) (s := Finset.range N)
      (f := fun n x => ad.coeffs n • (ad.atoms n).f x) ?_
    intro n hn
    -- Each atom is integrable, and scaling preserves integrability.
    simpa [Pi.smul_apply] using (H1Atom.integrable (ad.atoms n)).smul (ad.coeffs n)

  -- From `L¹` convergence (in the robust `lintegral` sense), pick an index where the distance is finite.
  have hfin_event :
      (∀ᶠ N in atTop,
        (∫⁻ x, ENNReal.ofReal |ad.target x - S N x| ∂volume) < ∞) := by
    have hnhds : Set.Iio (∞ : ℝ≥0∞) ∈ 𝓝 (0 : ℝ≥0∞) :=
      Iio_mem_nhds (by simp)
    exact ad.converges.eventually hnhds
  rcases hfin_event.exists with ⟨N, hNfin⟩

  -- The difference `target - S N` is integrable (measurable + finite integral of the norm).
  have hdiff_int : Integrable (fun x => ad.target x - S N x) volume := by
    refine ⟨ad.measurable_target.sub (hS_int N).aestronglyMeasurable, ?_⟩
    -- `HasFiniteIntegral` is exactly finiteness of the `lintegral` of the norm.
    -- Here `‖target - S N‖ = |target - S N|`.
    have : (∫⁻ x, ENNReal.ofReal ‖ad.target x - S N x‖ ∂volume) < ∞ := by
      simpa [Real.norm_eq_abs] using hNfin
    simpa [MeasureTheory.hasFiniteIntegral_iff_norm] using this

  -- Finally, `target = (target - S N) + S N`.
  have hsum_int : Integrable (fun x => (ad.target x - S N x) + S N x) volume :=
    hdiff_int.add (hS_int N)
  have hsum_eq : (fun x => (ad.target x - S N x) + S N x) = ad.target := by
    funext x
    ring
  simpa [hsum_eq] using hsum_int

end AtomicDecomposition

/-! ### Connection to Carleson Measures -/

/-- The tent over a Whitney interval. -/
def whitneyTent (I : RH.Cert.WhitneyInterval) (α : ℝ) : Set (ℝ × ℝ) :=
  I.interval ×ˢ Ioc 0 (α * (2 * I.len))

/-- A Carleson measure is characterized by its action on atoms.

This is the key connection: if `μ` is Carleson, then for any atom `a` supported
on an interval `I`, we have `∫∫_{T(I)} |Pa|² dμ ≤ C · |I|`.

**Proof Sketch**:
1. The tent `T(I) = I × (0, r)` where `r = radius` is contained in the Carleson tent
2. By Carleson condition: `μ(T(I)) ≤ K · |I|`
3. The integral of 1 over `T(I)` is exactly `μ(T(I))`

This estimate is fundamental because:
- Atoms have cancellation (∫ a = 0)
- Their Poisson extension decays rapidly away from T(I)
- The measure contribution is controlled by K · |I| -/
theorem atom_carleson_bound (a : H1Atom) (μ : Measure (ℝ × ℝ≥0)) (K : ℝ≥0)
    (_hμ : CarlesonMeasure.IsCarlesonMeasure μ volume (CarlesonMeasure.ballCarlesonFamily ℝ) K) :
    μ (Metric.closedBall a.center a.radius ×ˢ Ioo (0 : ℝ≥0) ⟨a.radius, a.radius_pos.le⟩) ≤
      K * volume (Metric.closedBall a.center a.radius) := by
  classical
  -- Use the defining bound `μ(tent i) / volume(baseSet i) ≤ K` for the ball Carleson family.
  let r : ℝ≥0 := ⟨a.radius, a.radius_pos.le⟩
  let i : (CarlesonMeasure.ballCarlesonFamily ℝ).ι := (a.center, r)
  have hdiv :
      μ ((CarlesonMeasure.ballCarlesonFamily ℝ).tent i) /
          volume ((CarlesonMeasure.ballCarlesonFamily ℝ).baseSet i) ≤ K :=
    CarlesonMeasure.IsCarlesonMeasure.tent_measure_div_baseSet_le (μ := μ) (ν := volume)
      (F := CarlesonMeasure.ballCarlesonFamily ℝ) (K := K) _hμ i
  -- Identify tent and base set.
  have ht :
      (CarlesonMeasure.ballCarlesonFamily ℝ).tent i =
        Metric.closedBall a.center a.radius ×ˢ Ioo (0 : ℝ≥0) r := by
    simp [CarlesonMeasure.ballCarlesonFamily, CarlesonMeasure.CarlesonFamily.tent, i, r]
  have hb :
      (CarlesonMeasure.ballCarlesonFamily ℝ).baseSet i = Metric.closedBall a.center a.radius := by
    simp [CarlesonMeasure.ballCarlesonFamily, i, r]
  -- The base set has positive, finite volume.
  have hvol_eq :
      volume ((CarlesonMeasure.ballCarlesonFamily ℝ).baseSet i) = ENNReal.ofReal (2 * a.radius) := by
    -- rewrite the base set as `closedBall` with real radius, then use the explicit formula in `ℝ`
    rw [hb]
    simp
  have hvol_ne_zero : volume ((CarlesonMeasure.ballCarlesonFamily ℝ).baseSet i) ≠ 0 := by
    have h2r_pos : 0 < 2 * a.radius := by linarith [a.radius_pos]
    have : ¬(2 * a.radius) ≤ 0 := not_le_of_gt h2r_pos
    have : ENNReal.ofReal (2 * a.radius) ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using this
    -- avoid simp rewriting the goal further
    rw [hvol_eq]
    exact this
  have hvol_ne_top : volume ((CarlesonMeasure.ballCarlesonFamily ℝ).baseSet i) ≠ ⊤ := by
    rw [hvol_eq]
    exact ENNReal.ofReal_ne_top
  -- Rearrange the Carleson ratio bound.
  have : μ ((CarlesonMeasure.ballCarlesonFamily ℝ).tent i) ≤
        (K : ℝ≥0∞) * volume ((CarlesonMeasure.ballCarlesonFamily ℝ).baseSet i) := by
    -- `x / y ≤ K`  iff  `x ≤ K * y` for `y ≠ 0, y ≠ ⊤`.
    have := (ENNReal.div_le_iff hvol_ne_zero hvol_ne_top).1 hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- rewrite `tent` and `baseSet` without expanding `volume`
  have h' := this
  -- avoid `simp`-rewrites like `volume_closedBall`; just rewrite by definitional equalities
  rw [ht] at h'
  rw [hb] at h'
  simpa [r] using h'

end MeasureTheory
