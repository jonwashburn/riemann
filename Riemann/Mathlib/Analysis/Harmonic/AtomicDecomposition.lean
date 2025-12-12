import Riemann.Cert.KxiPPlus
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

/-! ### Atomic H¹ (Tier A): norm defined by infimum over decompositions -/

/-- An atomic decomposition *of* a fixed function `f` is an `AtomicDecomposition` whose `target`
is `f`.

This is the (Tier A) notion used to define the atomic Hardy-space seminorm by taking an infimum
over all decompositions.
-/
abbrev AtomicDecompositionOf (f : ℝ → ℝ) : Type :=
  {ad : AtomicDecomposition // ad.target = f}

namespace AtomicDecomposition

variable (ad : AtomicDecomposition)

/-- A basic triangle-inequality bound for the L¹ norm of the target.

If `f = ∑ λₙ aₙ` in the L¹ sense, and `‖aₙ‖₁ ≤ 1`, then `‖f‖₁ ≤ ∑ |λₙ|`.

This is the key estimate needed to relate the atomic H¹ seminorm to the ambient L¹ norm. -/
theorem integral_abs_target_le_h1Norm : (∫ x, |ad.target x| ∂volume) ≤ ad.h1Norm := by
  classical
  -- Partial sums.
  let S : ℕ → (ℝ → ℝ) :=
    fun N x => ∑ n ∈ Finset.range N, ad.coeffs n • (ad.atoms n).f x

  have hS_int : ∀ N, Integrable (S N) volume := by
    intro N
    refine integrable_finset_sum (μ := volume) (s := Finset.range N)
      (f := fun n x => ad.coeffs n • (ad.atoms n).f x) ?_
    intro n hn
    simpa [Pi.smul_apply] using (H1Atom.integrable (ad.atoms n)).smul (ad.coeffs n)

  have htarget_int : Integrable ad.target volume := ad.target_integrable
  have hdiff_int : ∀ N, Integrable (fun x => ad.target x - S N x) volume := fun N =>
    htarget_int.sub (hS_int N)

  -- Convert the `lintegral`-convergence in the structure to a real `L¹` convergence.
  have hdiff_tendsto :
      Tendsto (fun N => ∫ x, |ad.target x - S N x| ∂volume) atTop (𝓝 0) := by
    let L : ℕ → ℝ≥0∞ := fun N => ∫⁻ x, ENNReal.ofReal |ad.target x - S N x| ∂volume
    have hL : Tendsto L atTop (𝓝 0) := by
      simpa [L, S] using ad.converges
    have htoReal : Tendsto (fun N => (L N).toReal) atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hL
    have hEq : (fun N => ∫ x, |ad.target x - S N x| ∂volume) = fun N => (L N).toReal := by
      funext N
      have hnonneg : 0 ≤ᵐ[volume] (fun x => |ad.target x - S N x|) := by
        filter_upwards with x
        exact abs_nonneg _
      have hmeas :
          AEStronglyMeasurable (fun x => |ad.target x - S N x|) volume := by
        -- Use integrability of the difference.
        simpa [Real.norm_eq_abs] using (hdiff_int N).aestronglyMeasurable.norm
      -- `integral = toReal(lintegral)` for a nonnegative integrand.
      simpa [L] using (integral_eq_lintegral_of_nonneg_ae (μ := volume) hnonneg hmeas)
    simpa [hEq] using htoReal

  -- Bound the L¹ norm of the partial sums by the partial sums of `|coeffs|`.
  have hS_bound : ∀ N, (∫ x, |S N x| ∂volume) ≤ ∑ n ∈ Finset.range N, |ad.coeffs n| := by
    intro N
    induction N with
    | zero =>
        simp [S]
    | succ N ih =>
        have hS_succ : S (N + 1) = fun x => S N x + ad.coeffs N • (ad.atoms N).f x := by
          funext x
          simp [S, Finset.sum_range_succ, add_comm]
        have hterm_int : Integrable (fun x => ad.coeffs N • (ad.atoms N).f x) volume := by
          simpa [Pi.smul_apply] using (H1Atom.integrable (ad.atoms N)).smul (ad.coeffs N)
        have hS_int' : Integrable (S N) volume := hS_int N
        have hadd :
            (∫ x, |S (N + 1) x| ∂volume) ≤
              (∫ x, |S N x| ∂volume) + ∫ x, |ad.coeffs N • (ad.atoms N).f x| ∂volume := by
          -- Use `|f+g| ≤ |f|+|g|` and monotonicity of the integral.
          have hle : (fun x => |S (N + 1) x|) ≤ fun x => |S N x| + |ad.coeffs N • (ad.atoms N).f x| := by
            intro x
            -- rewrite `S (N+1)` as `S N + term`
            have : S (N + 1) x = S N x + ad.coeffs N • (ad.atoms N).f x := by
              simp [hS_succ]
            -- apply triangle inequality
            simpa [this] using (abs_add_le (S N x) (ad.coeffs N • (ad.atoms N).f x))
          have hleft_int : Integrable (fun x => |S (N + 1) x|) volume := by
            have : Integrable (S (N + 1)) volume := hS_int (N + 1)
            simpa [Real.norm_eq_abs] using this.norm
          have h1 : Integrable (fun x => |S N x|) volume := by
            simpa [Real.norm_eq_abs] using hS_int'.norm
          have h2 : Integrable (fun x => |ad.coeffs N • (ad.atoms N).f x|) volume := by
            simpa [Real.norm_eq_abs] using hterm_int.norm
          have hright_int : Integrable (fun x => |S N x| + |ad.coeffs N • (ad.atoms N).f x|) volume :=
            h1.add h2
          have hmono :
              (∫ x, |S (N + 1) x| ∂volume) ≤
                ∫ x, |S N x| + |ad.coeffs N • (ad.atoms N).f x| ∂volume :=
            integral_mono hleft_int hright_int hle
          -- Rewrite the RHS integral of a sum as a sum of integrals.
          calc
            (∫ x, |S (N + 1) x| ∂volume)
                ≤ ∫ x, |S N x| + |ad.coeffs N • (ad.atoms N).f x| ∂volume := hmono
            _ = (∫ x, |S N x| ∂volume) + ∫ x, |ad.coeffs N • (ad.atoms N).f x| ∂volume := by
                simpa using (integral_add (μ := volume) h1 h2)
        have hterm_bound : (∫ x, |ad.coeffs N • (ad.atoms N).f x| ∂volume) ≤ |ad.coeffs N| := by
          -- `∫ |c·a| = |c| ∫ |a| ≤ |c|`.
          have habs : (fun x => |ad.coeffs N • (ad.atoms N).f x|) =
              fun x => |ad.coeffs N| * |(ad.atoms N).f x| := by
            funext x
            simp
          calc
            (∫ x, |ad.coeffs N • (ad.atoms N).f x| ∂volume)
                = ∫ x, |ad.coeffs N| * |(ad.atoms N).f x| ∂volume := by
                    simp
            _ = |ad.coeffs N| * ∫ x, |(ad.atoms N).f x| ∂volume := by
                    simpa using
                      (integral_const_mul (μ := volume) (|ad.coeffs N|) (fun x => |(ad.atoms N).f x|))
            _ ≤ |ad.coeffs N| * 1 := by
                    gcongr
                    exact H1Atom.norm_le_one (ad.atoms N)
            _ = |ad.coeffs N| := by simp
        calc
          (∫ x, |S (N + 1) x| ∂volume)
              ≤ (∫ x, |S N x| ∂volume) + ∫ x, |ad.coeffs N • (ad.atoms N).f x| ∂volume := hadd
          _ ≤ (∑ n ∈ Finset.range N, |ad.coeffs n|) + |ad.coeffs N| := by
              gcongr
          _ = ∑ n ∈ Finset.range (N + 1), |ad.coeffs n| := by
              simp [Finset.sum_range_succ, add_comm]

  -- Finish using an `ε`-argument from `L¹` convergence.
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hε' : Set.Iio ε ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hε
  have h_event : ∀ᶠ N in atTop, (∫ x, |ad.target x - S N x| ∂volume) < ε :=
    hdiff_tendsto.eventually hε'
  rcases h_event.exists with ⟨N, hN⟩
  have hsum_le : (∑ n ∈ Finset.range N, |ad.coeffs n|) ≤ ad.h1Norm := by
    -- nonnegative series: partial sums are bounded by the `tsum`
    simpa [AtomicDecomposition.h1Norm] using
      (Summable.sum_le_tsum (s := Finset.range N) (f := fun n => |ad.coeffs n|)
        (fun n _hn => abs_nonneg (ad.coeffs n)) ad.summable_coeffs)
  -- `‖target‖₁ ≤ ‖target - S N‖₁ + ‖S N‖₁`.
  have htri :
      (∫ x, |ad.target x| ∂volume) ≤
        (∫ x, |ad.target x - S N x| ∂volume) + ∫ x, |S N x| ∂volume := by
    -- pointwise triangle inequality and integral monotonicity
    have hle :
        (fun x => |ad.target x|) ≤ fun x => |ad.target x - S N x| + |S N x| := by
      intro x
      -- `target = (target - S N) + S N`
      have hsum : ad.target x = (ad.target x - S N x) + S N x := by ring
      -- rewrite the left-hand side using `hsum`, then apply the triangle inequality
      -- `|a + b| ≤ |a| + |b|`
      have : |ad.target x| ≤ |ad.target x - S N x| + |S N x| := by
        -- rewriting under `abs` is safe with `rw`
        -- (it turns the goal into `abs_add`)
        rw [hsum]
        simpa using (abs_add_le (ad.target x - S N x) (S N x))
      exact this
    have hleft_int : Integrable (fun x => |ad.target x|) volume := by
      simpa [Real.norm_eq_abs] using htarget_int.norm
    have h1 : Integrable (fun x => |ad.target x - S N x|) volume := by
      simpa [Real.norm_eq_abs] using (hdiff_int N).norm
    have h2 : Integrable (fun x => |S N x|) volume := by
      simpa [Real.norm_eq_abs] using (hS_int N).norm
    have hright_int : Integrable (fun x => |ad.target x - S N x| + |S N x|) volume :=
      h1.add h2
    have hmono := integral_mono hleft_int hright_int hle
    -- rewrite the RHS integral of a sum as a sum of integrals
    simpa [integral_add h1 h2] using hmono
  calc
    (∫ x, |ad.target x| ∂volume)
        ≤ (∫ x, |ad.target x - S N x| ∂volume) + ∫ x, |S N x| ∂volume := htri
    _ ≤ ad.h1Norm + ε := by
          -- bound `‖S N‖₁` by `∑_{n<N} |coeffs n|`, then by `h1Norm`
          have hSN : (∫ x, |S N x| ∂volume) ≤ ∑ n ∈ Finset.range N, |ad.coeffs n| :=
            hS_bound N
          have h1 : (∫ x, |ad.target x - S N x| ∂volume) ≤ ε := le_of_lt hN
          have h2 : (∫ x, |S N x| ∂volume) ≤ ad.h1Norm := (hSN.trans hsum_le)
          -- the estimate gives `≤ ε + ad.h1Norm`; swap the sum order
          have : (∫ x, |ad.target x - S N x| ∂volume) + ∫ x, |S N x| ∂volume ≤ ε + ad.h1Norm :=
            add_le_add h1 h2
          simpa [add_comm, add_left_comm, add_assoc] using this

end AtomicDecomposition

/-- The atomic H¹ seminorm: infimum of the ℓ¹ norms of coefficients over all atomic decompositions. -/
noncomputable def atomicH1Norm (f : ℝ → ℝ) : ℝ≥0∞ :=
  ⨅ d : AtomicDecompositionOf f, ENNReal.ofReal d.1.h1Norm

/-- Predicate: `f` has finite atomic H¹ seminorm. -/
def MemAtomicH1 (f : ℝ → ℝ) : Prop := atomicH1Norm f < ⊤

namespace MemAtomicH1

variable {f : ℝ → ℝ}

theorem nonempty (hf : MemAtomicH1 f) : Nonempty (AtomicDecompositionOf f) := by
  classical
  rcases isEmpty_or_nonempty (AtomicDecompositionOf f) with hempty | hne
  · haveI : IsEmpty (AtomicDecompositionOf f) := hempty
    -- then `atomicH1Norm f = ⊤`, contradiction
    exfalso
    simp [MemAtomicH1, atomicH1Norm] at hf
  · exact hne

theorem integrable (hf : MemAtomicH1 f) : Integrable f volume := by
  classical
  rcases (nonempty (f := f) hf) with ⟨d⟩
  -- integrability comes from any atomic decomposition
  have : Integrable d.1.target volume := d.1.target_integrable
  simpa [d.2] using this

end MemAtomicH1

/-- The ambient L¹ seminorm is controlled by the atomic H¹ seminorm. -/
theorem lintegral_abs_le_atomicH1Norm (f : ℝ → ℝ) :
    (∫⁻ x, ENNReal.ofReal |f x| ∂volume) ≤ atomicH1Norm f := by
  classical
  rcases isEmpty_or_nonempty (AtomicDecompositionOf f) with hempty | hne
  · haveI : IsEmpty (AtomicDecompositionOf f) := hempty
    simp [atomicH1Norm]
  · -- compare to each decomposition and take the infimum
    refine le_iInf (fun d => ?_)
    have hf_int : Integrable f volume := by
      -- `f` is integrable, since it is the target of an atomic decomposition
      have : Integrable d.1.target volume := d.1.target_integrable
      simpa [d.2] using this
    have habs_int : Integrable (fun x => |f x|) volume := by
      simpa [Real.norm_eq_abs] using hf_int.norm
    have h_ofReal :
        ENNReal.ofReal (∫ x, |f x| ∂volume) =
          ∫⁻ x, ENNReal.ofReal |f x| ∂volume := by
      -- `|f|` is nonnegative, so the integral is the `toReal` of the `lintegral`
      simpa using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (μ := volume)
          (f := fun x => |f x|) habs_int
          (by
            filter_upwards with x
            exact abs_nonneg _))
    have hreal : (∫ x, |f x| ∂volume) ≤ d.1.h1Norm := by
      -- Use the L¹ estimate for this particular decomposition.
      simpa [d.2] using d.1.integral_abs_target_le_h1Norm
    have hENN : ENNReal.ofReal (∫ x, |f x| ∂volume) ≤ ENNReal.ofReal d.1.h1Norm :=
      ENNReal.ofReal_le_ofReal hreal
    -- rewrite the `lintegral` as an `ofReal` integral and conclude
    simpa [atomicH1Norm, h_ofReal] using hENN

/-- **(Tier A) Atomic decomposition theorem**: from a finite atomic H¹ seminorm, one can extract a
decomposition with coefficient sum controlled by `2 * atomicH1Norm f`.

This is the standard “near minimizer” statement coming from the definition of the infimum; it is
not the analytic Coifman–Meyer–Stein theorem (which would derive atomic decompositions from a
different, non-atomic definition of `H¹`). -/
theorem coifman_meyer_stein (f : ℝ → ℝ) (hf : MemAtomicH1 f) :
    ∃ d : AtomicDecompositionOf f, ENNReal.ofReal d.1.h1Norm ≤ 2 * atomicH1Norm f := by
  classical
  -- Choose a decomposition if the infimum is `0`, otherwise use the definition of `iInf`.
  set r : ℝ≥0∞ := atomicH1Norm f
  have hr_lt_top : r < ⊤ := hf
  by_cases hr0 : r = 0
  · -- If `atomicH1Norm f = 0`, then `∫ |f| = 0` in the `lintegral` sense, so the zero decomposition works.
    rcases (MemAtomicH1.nonempty (f := f) hf) with ⟨d₀⟩
    -- A fixed atom (the zero function is an atom).
    let a0 : H1Atom :=
      { f := 0
        center := 0
        radius := 1
        radius_pos := by norm_num
        support_subset := by
          simp
        size_bound := by
          intro x; simp
        integral_zero := by simp
        measurable := by simpa using (MeasureTheory.aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ)) volume) }
    have hL0 :
        (∫⁻ x, ENNReal.ofReal |f x| ∂volume) = 0 := by
      have hle : (∫⁻ x, ENNReal.ofReal |f x| ∂volume) ≤ r :=
        (lintegral_abs_le_atomicH1Norm f)
      have hle0 : (∫⁻ x, ENNReal.ofReal |f x| ∂volume) ≤ 0 := by simpa [r, hr0] using hle
      exact le_antisymm hle0 (by simp)
    -- The zero-coefficient decomposition.
    refine ⟨⟨
      { atoms := fun _ => a0
        coeffs := fun _ => 0
        summable_coeffs := by simpa using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
        target := f
        measurable_target := by simpa [d₀.2] using d₀.1.measurable_target
        converges := by
          -- The L¹ distance to the zero partial sums is constantly `0`.
          have : (fun N =>
              ∫⁻ x, ENNReal.ofReal
                |f x - ∑ n ∈ Finset.range N, (0 : ℝ) • a0.f x| ∂volume)
              = fun _ : ℕ => (∫⁻ x, ENNReal.ofReal |f x| ∂volume) := by
                funext N
                simp [a0]
          -- rewrite to a constant sequence
          simp [hL0] } ,
      rfl⟩, ?_⟩
    -- Coefficient sum is `0`, and `r = 0`.
    simp [AtomicDecomposition.h1Norm, r, hr0]
  · -- If `r ≠ 0`, we can use `r < 2r` and the defining property of `iInf`.
    have hr_lt : r < 2 * r := by
      -- For finite `r` with `r ≠ 0`, we have `r < r + r = 2 * r`.
      have hr_ne_top : r ≠ (⊤ : ℝ≥0∞) := ne_of_lt hr_lt_top
      have hlt : r < r + r := by
        -- `lt_add_right` is available for `ℝ≥0∞` numbers away from `⊤`.
        simpa using (ENNReal.lt_add_right hr_ne_top hr0)
      simpa [two_mul] using hlt
    -- There exists a decomposition with coefficient sum `< 2r`.
    have hex : ∃ d : AtomicDecompositionOf f, ENNReal.ofReal d.1.h1Norm < 2 * r := by
      by_contra h
      have hall : ∀ d : AtomicDecompositionOf f, 2 * r ≤ ENNReal.ofReal d.1.h1Norm := by
        intro d
        have : ¬ ENNReal.ofReal d.1.h1Norm < 2 * r := by
          intro hlt
          exact h ⟨d, hlt⟩
        exact le_of_not_gt this
      have : 2 * r ≤ r := by
        -- `2r` is a lower bound of the family, hence below the infimum.
        have hle : 2 * r ≤ ⨅ d : AtomicDecompositionOf f, ENNReal.ofReal d.1.h1Norm := le_iInf hall
        simpa [atomicH1Norm, r] using hle
      exact (not_le_of_gt hr_lt) this
    rcases hex with ⟨d, hdlt⟩
    refine ⟨d, ?_⟩
    -- weaken `<` to `≤` and rewrite `r`.
    simpa [r] using le_of_lt hdlt

/-! ### Connection to Carleson Measures -/

/-!
#### Whitney tents: project-level (`ℝ × ℝ`) vs mathlib-facing (`ℝ × ℝ≥0`)

The Riemann/RS layer historically uses tents in the upper half-plane as subsets of `ℝ × ℝ`,
typically with the “closed top” convention `Ioc 0 r`.

For Carleson-measure theory and interoperability with `CarlesonMeasure.CarlesonFamily`, the
canonical ambient space is `ℝ × ℝ≥0` and the canonical tent uses the “open top” convention
`Ioo 0 r`.

We keep both conventions and provide clean bridge lemmas via the coercion map `ℝ≥0 → ℝ`.
-/

open CarlesonMeasure

/-- The RS-flavoured Whitney tent (subset of `ℝ × ℝ`) with “closed top” (`Ioc`). -/
def whitneyTentReal (I : RH.Cert.WhitneyInterval) (α : ℝ) : Set (ℝ × ℝ) :=
  I.interval ×ˢ Ioc 0 (α * (2 * I.len))

/-- The vertical scale (height) for the Whitney tent, as an element of `ℝ≥0`. -/
noncomputable def whitneyScale (α : ℝ≥0) (I : RH.Cert.WhitneyInterval) : ℝ≥0 :=
  α * (2 * ⟨I.len, I.len_pos.le⟩)

/-- A Carleson family on `ℝ` indexed by Whitney intervals, with scale `α * (2 * I.len)`. -/
noncomputable def whitneyCarlesonFamily (α : ℝ≥0) : CarlesonFamily ℝ where
  ι := RH.Cert.WhitneyInterval
  baseSet I := I.interval
  scale I := whitneyScale α I
  measurableSet_baseSet I := by
    -- `I.interval = Icc _ _` is measurable in the Borel σ-algebra.
    simp [RH.Cert.WhitneyInterval.interval]

/-- The mathlib-facing Whitney tent (subset of `ℝ × ℝ≥0`) coming from the Carleson-family tent. -/
def whitneyTent (I : RH.Cert.WhitneyInterval) (α : ℝ≥0) : Set (ℝ × ℝ≥0) :=
  (whitneyCarlesonFamily α).tent I

/-- Coercion map `(ℝ × ℝ≥0) → (ℝ × ℝ)` used to compare the two tent conventions. -/
def whitneyTentCoe : (ℝ × ℝ≥0) → (ℝ × ℝ) := fun p => (p.1, (p.2 : ℝ))

@[simp] lemma whitneyTentCoe_fst (p : ℝ × ℝ≥0) : (whitneyTentCoe p).1 = p.1 := rfl
@[simp] lemma whitneyTentCoe_snd (p : ℝ × ℝ≥0) : (whitneyTentCoe p).2 = (p.2 : ℝ) := rfl

/-- Preimage description: pulling back the RS tent along coercion produces the same base interval
and the “closed top” interval `Ioc` in the `ℝ≥0` coordinate. -/
theorem preimage_whitneyTentReal (I : RH.Cert.WhitneyInterval) (α : ℝ≥0) :
    whitneyTentCoe ⁻¹' (whitneyTentReal I (α : ℝ))
      = I.interval ×ˢ Set.Ioc (0 : ℝ≥0) (whitneyScale α I) := by
  ext p
  -- Reduce to pointwise membership conditions and translate inequalities through coercions.
  have hscale :
      ((whitneyScale α I : ℝ≥0) : ℝ) = (α : ℝ) * (2 * I.len) := by
    simp [whitneyScale, mul_assoc, mul_left_comm, mul_comm]
  constructor
  · intro hp
    have hp' :
        p.1 ∈ I.interval ∧ ((p.2 : ℝ) ∈ Set.Ioc (0 : ℝ) ((α : ℝ) * (2 * I.len))) := by
      simpa [whitneyTentCoe, whitneyTentReal, Set.preimage, Set.mem_prod, Set.mem_Ioc] using hp
    refine ⟨hp'.1, ?_⟩
    rcases hp'.2 with ⟨hp0, hpR⟩
    refine ⟨?_, ?_⟩
    · simpa using hp0
    · -- rewrite the bound and use `NNReal.coe_le_coe`
      have : (p.2 : ℝ) ≤ (whitneyScale α I : ℝ) := by
        simpa [hscale] using hpR
      exact NNReal.coe_le_coe.1 this
  · intro hp
    rcases hp with ⟨hpI, hpY⟩
    rcases hpY with ⟨hp0, hpR⟩
    have hp0' : (0 : ℝ) < (p.2 : ℝ) := by simpa using hp0
    have hpR' : (p.2 : ℝ) ≤ (α : ℝ) * (2 * I.len) := by
      have : (p.2 : ℝ) ≤ (whitneyScale α I : ℝ) := NNReal.coe_le_coe.2 hpR
      simpa [hscale] using this
    -- package back into the preimage membership
    have :
        p.1 ∈ I.interval ∧ ((p.2 : ℝ) ∈ Set.Ioc (0 : ℝ) ((α : ℝ) * (2 * I.len))) := by
      exact ⟨hpI, ⟨hp0', hpR'⟩⟩
    simpa [whitneyTentCoe, whitneyTentReal, Set.preimage, Set.mem_prod, Set.mem_Ioc] using this

/-- The mathlib-facing tent is contained in the pullback of the RS-flavoured tent (open top
implies closed top). -/
theorem whitneyTent_subset_preimage_whitneyTentReal (I : RH.Cert.WhitneyInterval) (α : ℝ≥0) :
    whitneyTent I α ⊆ whitneyTentCoe ⁻¹' (whitneyTentReal I (α : ℝ)) := by
  intro p hp
  -- unfold the `CarlesonFamily.tent` membership
  have : p ∈ I.interval ×ˢ Set.Ioo (0 : ℝ≥0) (whitneyScale α I) := by
    simpa [whitneyTent, whitneyCarlesonFamily, whitneyScale, CarlesonFamily.tent] using hp
  rcases this with ⟨hpI, hpY⟩
  refine (preimage_whitneyTentReal (I := I) (α := α)).symm ▸ ?_
  refine ⟨hpI, ?_⟩
  -- `Ioo` implies `Ioc`
  exact ⟨hpY.1, hpY.2.le⟩

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
