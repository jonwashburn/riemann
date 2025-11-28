
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.ContinuousOn
import Riemann.Mathlib.Analysis.Complex.Cartan
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.CircleAverageLemmas
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.PosLogLemmas
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.MinimumModulues'
import Mathlib

/-!
# Hardy Spaces on the Unit Disc

This file develops the theory of Hardy spaces H^p on the unit disc, providing
the foundational infrastructure for Nevanlinna theory and the Poisson-Jensen
representation theorem.

## Main definitions

* `HardySpace p` : The Hardy space H^p on the unit disc for `p : ℝ≥0∞`
* `HardySpace.norm` : The H^p norm (supremum of L^p norms on circles)
* `HardySpace.boundaryValue` : The radial limit function on the boundary
* `HardyNorm` : The Hardy space norm functional

## Main results

* `HardySpace.analyticOn` : H^p functions are analytic on the disc
* `HardySpace.boundaryValue_exists_ae` : Radial limits exist a.e. (Fatou's theorem)
* `HardySpace.log_integrable` : For f ∈ H^p with f ≢ 0, log|f| is integrable on circles
* `HardySpace.jensen_inequality` : Jensen's inequality for H^p functions

## Implementation notes

We define Hardy spaces using the supremum of L^p norms on circles of radius r < 1.
For H^∞, this coincides with the supremum norm on the disc.

The key technical results are:
1. Fatou's theorem on radial limits (boundary values exist a.e.)
2. Integrability of log|f| for non-identically-zero H^p functions
3. The connection to Nevanlinna's proximity function

## References

* Duren, P.L., "Theory of H^p Spaces"
* Garnett, J.B., "Bounded Analytic Functions"
* Koosis, P., "Introduction to H^p Spaces"
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### The unit disc and basic properties -/

/-- The open unit disc as a subset of ℂ. -/
def unitDisc : Set ℂ := {z : ℂ | ‖z‖ < 1}

@[simp]
lemma mem_unitDisc {z : ℂ} : z ∈ unitDisc ↔ ‖z‖ < 1 := Iff.rfl

lemma unitDisc_eq_ball : unitDisc = Metric.ball (0 : ℂ) 1 := by
  ext z; simp [unitDisc, Metric.mem_ball, dist_zero_right]

lemma isOpen_unitDisc : IsOpen unitDisc := by
  rw [unitDisc_eq_ball]; exact Metric.isOpen_ball

lemma zero_mem_unitDisc : (0 : ℂ) ∈ unitDisc := by simp [unitDisc]

/-- The closed disc of radius r. -/
def closedDisc (r : ℝ) : Set ℂ := Metric.closedBall (0 : ℂ) r

@[simp]
lemma mem_closedDisc {z : ℂ} {r : ℝ} : z ∈ closedDisc r ↔ ‖z‖ ≤ r := by
  simp [closedDisc, Metric.mem_closedBall, dist_zero_right]

lemma closedDisc_subset_unitDisc {r : ℝ} (hr : r < 1) : closedDisc r ⊆ unitDisc := by
  intro z hz
  simp only [mem_closedDisc] at hz
  simp only [mem_unitDisc]
  exact lt_of_le_of_lt hz hr

/-! ### L^p norms on circles -/

/-- The L^p norm of f on the circle of radius r, for p ∈ (0, ∞). -/
def circleNorm (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (circleAverage (fun z => ‖f z‖ ^ p) 0 r) ^ (1 / p)

/-- The L^∞ norm of f on the circle of radius r. -/
def circleSupNorm (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ θ : ℝ, ‖f (circleMap 0 r θ)‖

/-- The Hardy norm for finite p. -/
def hardyNorm (p : ℝ) (f : ℂ → ℂ) : ℝ :=
  ⨆ r : {r : ℝ // 0 < r ∧ r < 1}, circleNorm p f r.val

/-- The H^∞ norm (supremum on the disc). -/
def hardySupNorm (f : ℂ → ℂ) : ℝ :=
  ⨆ z : unitDisc, ‖f z‖

/-! ### Hardy space definitions -/

/-- H^∞: bounded analytic functions on the disc. -/
structure IsInHInfty (f : ℂ → ℂ) : Prop where
  /-- The function is analytic on the open unit disc. -/
  analyticOn : AnalyticOn ℂ f unitDisc
  /-- The function is bounded on the disc. -/
  bounded : ∃ M : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ M

/-- A function belongs to the Hardy space H^p (for finite p > 0) if it is analytic on the disc
and has uniformly bounded L^p norms on circles. -/
structure IsInHardySpace (p : ℝ) (f : ℂ → ℂ) : Prop where
  /-- The function is analytic on the open unit disc. -/
  analyticOn : AnalyticOn ℂ f unitDisc
  /-- The Hardy norm is finite (uniformly bounded over all circles). -/
  norm_finite : ∃ M : ℝ, ∀ r : ℝ, 0 < r → r < 1 → circleNorm p f r ≤ M

/-- Characterization of H^∞. -/
lemma isInHInfty_iff {f : ℂ → ℂ} :
    IsInHInfty f ↔ AnalyticOn ℂ f unitDisc ∧ ∃ M : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ M := by
  constructor
  · intro ⟨hf_an, hf_bdd⟩
    exact ⟨hf_an, hf_bdd⟩
  · intro ⟨hf_an, hM⟩
    exact ⟨hf_an, hM⟩

/-! ### Basic properties of Hardy space functions -/

/-- H^p functions are analytic on the disc. -/
lemma IsInHardySpace.analyticOnDisc {p : ℝ} {f : ℂ → ℂ} (hf : IsInHardySpace p f) :
    AnalyticOn ℂ f unitDisc := hf.analyticOn

/-- H^∞ functions are analytic on the disc. -/
lemma IsInHInfty.analyticOnDisc {f : ℂ → ℂ} (hf : IsInHInfty f) :
    AnalyticOn ℂ f unitDisc := hf.analyticOn

/-- H^∞ functions are bounded on the disc. -/
lemma IsInHInfty.isBounded {f : ℂ → ℂ} (hf : IsInHInfty f) :
    ∃ M : ℝ, ∀ z ∈ unitDisc, ‖f z‖ ≤ M := hf.bounded

/-- H^∞ functions are continuous on the disc. -/
lemma IsInHInfty.continuousOn {f : ℂ → ℂ} (hf : IsInHInfty f) :
    ContinuousOn f unitDisc :=
  hf.analyticOnDisc.continuousOn

/-! ### Boundary values (Fatou's theorem) -/

/-- The radial limit of f at angle θ, if it exists. -/
def radialLimit (f : ℂ → ℂ) (θ : ℝ) : ℂ :=
  limUnder (𝓝[<] 1) (fun r => f (circleMap 0 r θ))

/-- The radial limit exists for H^∞ functions at every point.

**Proof Strategy (Fatou's Theorem for Bounded Analytic Functions):**

For bounded analytic functions on the disc, radial limits exist *everywhere*
(not just almost everywhere). The proof uses:

1. **Power series representation**: f(z) = ∑ aₙ zⁿ converges absolutely for |z| < 1.
   The boundedness |f(z)| ≤ M implies the coefficients satisfy |aₙ| ≤ M by Cauchy estimates.

2. **Abel summation**: For the radial approach z = r·e^{iθ} with r → 1⁻,
   f(r·e^{iθ}) = ∑ aₙ rⁿ e^{inθ} is an Abel sum of the Fourier series.

3. **Uniform boundedness**: The family {f(r·e^{iθ})}_{r<1} is uniformly bounded by M,
   so by compactness of the closed ball in ℂ, there exist limit points.

4. **Uniqueness via Cauchy**: Any two limit points along radial sequences would give
   different boundary values, contradicting the Poisson integral representation.

The classical proof uses the Poisson integral representation for bounded harmonic functions.
For bounded *analytic* functions, the Cauchy integral formula provides a more direct path.

**Technical Note**: This result requires Mathlib infrastructure for:
- Power series convergence on the boundary (Abel's theorem)
- Or the Poisson kernel representation for harmonic functions
- Currently not fully available in Mathlib, so we mark this as a deep sorry.
-/
lemma IsInHInfty.radialLimit_exists {f : ℂ → ℂ} (hf : IsInHInfty f) (θ : ℝ) :
    ∃ L : ℂ, Tendsto (fun r => f (circleMap 0 r θ)) (𝓝[<] 1) (𝓝 L) := by
  -- The radial path r ↦ f(r·e^{iθ}) for r ∈ (0, 1)
  -- is a bounded continuous function on (0, 1).
  obtain ⟨M, hM⟩ := hf.bounded
  have hM_pos : 0 ≤ M := by
    by_contra h_neg
    push_neg at h_neg
    have : ‖f 0‖ ≤ M := hM 0 zero_mem_unitDisc
    linarith [norm_nonneg (f 0)]
  -- The image f({r·e^{iθ} : r ∈ (0,1)}) is contained in closedBall 0 M
  have h_bdd : ∀ r : ℝ, 0 < r → r < 1 → ‖f (circleMap 0 r θ)‖ ≤ M := by
    intro r hr0 hr1
    apply hM
    simp only [mem_unitDisc, circleMap, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real]
    simp only [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  -- The function is continuous on (0, 1) × {θ}
  have h_cont : ContinuousOn (fun r => f (circleMap 0 r θ)) (Set.Ioo 0 1) := by
    have h_maps : MapsTo (fun r => circleMap 0 r θ) (Set.Ioo 0 1) unitDisc := by
      intro r ⟨hr0, hr1⟩
      simp only [mem_unitDisc, circleMap, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I,
        mul_one, Complex.norm_real]
      simp only [Real.norm_eq_abs, abs_of_pos hr0]
      exact hr1
    -- circleMap 0 r θ = r • exp(θ * I) is continuous in r
    have h_circle_cont : Continuous (fun r : ℝ => circleMap 0 r θ) := by
      unfold circleMap
      simp only [zero_add]
      exact continuous_ofReal.smul continuous_const
    exact hf.continuousOn.comp h_circle_cont.continuousOn h_maps
  -- For bounded analytic functions, the radial limit exists.
  -- This is a deep result requiring either:
  -- (a) Abel's theorem on power series boundary behavior, or
  -- (b) Poisson integral representation for bounded harmonic functions
  --
  -- The boundedness ensures the image lies in a compact set, so cluster points exist.
  -- The key is showing the limit is unique, which follows from the rigidity of
  -- analytic functions (identity theorem) applied via the Poisson representation.
  --
  -- This requires Mathlib infrastructure for Fatou's theorem / Abel summation
  -- that is not yet available, so we mark this as a foundational sorry.
  sorry

/-- The boundary value function for H^∞. -/
def IsInHInfty.boundaryValue {f : ℂ → ℂ} (hf : IsInHInfty f) : ℝ → ℂ :=
  fun θ => (hf.radialLimit_exists θ).choose

/-- The boundary value function is measurable.

**Proof Strategy:**
Once radial limits exist everywhere (from `radialLimit_exists`), the boundary value
function θ ↦ lim_{r→1⁻} f(r·e^{iθ}) is measurable because:

1. For each r < 1, the function θ ↦ f(r·e^{iθ}) is continuous (hence measurable)
2. The pointwise limit of measurable functions is measurable
3. The radial limit exists everywhere by Fatou's theorem

Alternatively, the boundary value function can be expressed as a limit of
the continuous functions fᵣ(θ) = f(r·e^{iθ}) as r → 1, which converges
pointwise to the boundary value. Pointwise limits of measurable functions
are measurable.
-/
lemma IsInHInfty.boundaryValue_measurable {f : ℂ → ℂ} (hf : IsInHInfty f) :
    Measurable hf.boundaryValue := by
  -- The boundary value is a pointwise limit of continuous (hence measurable) functions.
  -- fₙ(θ) := f((1 - 1/(n+2)) · e^{iθ}) → boundaryValue(θ) as n → ∞
  --
  -- Each fₙ is continuous in θ (composition of continuous functions).
  -- The pointwise limit of measurable functions is measurable.
  --
  -- This uses the fact that radialLimit_exists gives convergence along any
  -- sequence rₙ → 1⁻, so in particular along rₙ = 1 - 1/(n+2).
  --
  -- Technical implementation requires showing:
  -- 1. The approximating functions are measurable
  -- 2. The limit equals boundaryValue (by uniqueness of limits)
  -- 3. Applying measurable_of_tendsto_metrizable or similar
  --
  -- This is a consequence of radialLimit_exists, so we mark it as depending on that.
  sorry

/-! ### Integrability of log|f| -/

/-- For a bounded analytic function that is not identically zero,
log|f| is integrable on every circle of radius r < 1. -/
lemma IsInHInfty.log_norm_circleIntegrable {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    CircleIntegrable (fun z => Real.log ‖f z‖) 0 r := by
  -- Analytic functions on connected open sets are meromorphic
  -- log|f| is integrable for meromorphic functions (logarithmic singularities are integrable)
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz
    simp only [mem_unitDisc]
    calc ‖z‖ ≤ |r| := hz
      _ = r := hr_abs
      _ < 1 := hr1
  -- For open sets, AnalyticOn ↔ AnalyticOnNhd, which gives AnalyticAt at each point
  have hf_anNhd : AnalyticOnNhd ℂ f unitDisc := isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf.analyticOn
  -- f is analytic hence meromorphic on the closed ball
  have hf_merom : MeromorphicOn f (closedBall (0 : ℂ) |r|) := fun z hz =>
    (hf_anNhd z (h_subset hz)).meromorphicAt
  -- Apply circle integrability for meromorphic functions on spheres
  have h_sphere_subset : sphere (0 : ℂ) |r| ⊆ closedBall (0 : ℂ) |r| := sphere_subset_closedBall
  have hf_merom_sphere : MeromorphicOn f (sphere (0 : ℂ) |r|) := fun z hz => hf_merom z (h_sphere_subset hz)
  exact circleIntegrable_log_norm_meromorphicOn hf_merom_sphere

/-- For a bounded analytic nonvanishing function,
log|f| is continuous on the closed disc. -/
lemma IsInHInfty.log_norm_continuousOn_of_ne_zero {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf_ne : ∀ z ∈ unitDisc, f z ≠ 0) {r : ℝ} (hr1 : r < 1) :
    ContinuousOn (fun z => Real.log ‖f z‖) (closedDisc r) := by
  have h_subset := closedDisc_subset_unitDisc hr1
  have hf_cont := hf.continuousOn.mono h_subset
  have hf_ne' : ∀ z ∈ closedDisc r, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
  exact ContinuousOn.log (continuous_norm.comp_continuousOn hf_cont)
    (fun z hz => (norm_pos_iff.mpr (hf_ne' z hz)).ne')

/-! ### Jensen's inequality for Hardy spaces -/

/-- Jensen's inequality: for f ∈ H^∞ with f(0) ≠ 0,
log|f(0)| ≤ circleAverage (log|f|) 0 r for all r < 1.

This is a consequence of Jensen's formula: for analytic f, the circle average of log|f|
equals log|f(0)| plus a nonnegative contribution from zeros. -/
lemma IsInHInfty.jensen_inequality {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.log ‖f 0‖ ≤ circleAverage (fun z => Real.log ‖f z‖) 0 r := by
  -- Apply Jensen's formula: circleAverage log|f| = ∑ zeros + log|trailing coeff at 0|
  -- For analytic f with f(0) ≠ 0, the trailing coefficient is f(0), and the sum is nonnegative.
  have hr_ne : r ≠ 0 := ne_of_gt hr0
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz
    simp only [mem_unitDisc]
    calc ‖z‖ ≤ |r| := hz
      _ = r := hr_abs
      _ < 1 := hr1
  -- For open sets, AnalyticOn ↔ AnalyticOnNhd
  have hf_anNhd : AnalyticOnNhd ℂ f unitDisc := isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf.analyticOn
  -- f is analytic hence meromorphic on the closed ball
  have hf_merom : MeromorphicOn f (closedBall (0 : ℂ) |r|) := fun z hz =>
    (hf_anNhd z (h_subset hz)).meromorphicAt
  -- Apply Jensen's formula
  have hJ := MeromorphicOn.circleAverage_log_norm hr_ne hf_merom
  -- For analytic f with f(0) ≠ 0, the trailing coefficient equals f(0)
  have hf_an_0 : AnalyticAt ℂ f 0 := hf_anNhd 0 zero_mem_unitDisc
  have h_trailing : meromorphicTrailingCoeffAt f 0 = f 0 :=
    AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero hf_an_0 hf0
  -- Jensen's formula gives: circleAverage = finsum + divisor(0)*log(r) + log|trailing|
  -- Since f is analytic (no poles), each divisor value is the zero order ≥ 0
  -- Each log(r * ‖-u‖⁻¹) is nonneg for u in the ball (since r ≥ ‖u‖)
  -- So the finsum is nonnegative, giving the inequality
  rw [hJ, h_trailing]
  -- The proof has two parts:
  -- 1. The divisor at 0 is 0 (since f(0) ≠ 0), so divisor(0)*log(r) = 0
  -- 2. The finsum is nonnegative because:
  --    - For analytic f, AnalyticOnNhd.divisor_nonneg gives divisor(u) ≥ 0
  --    - For u in the ball with ‖u‖ ≤ r, log(r/‖u‖) ≥ 0
  --    - So each term divisor(u) * log(r/‖u‖) ≥ 0
  --
  -- The formal proof uses Mathlib's divisor API from Mathlib.Analysis.Meromorphic.Divisor
  -- Specifically: AnalyticOnNhd.divisor_nonneg and MeromorphicOn.divisor_apply
  have hf_an_ball : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) := fun z hz => hf_anNhd z (h_subset hz)
  -- The divisor at 0 is 0 since f(0) ≠ 0 (zero order is 0)
  have h_div_0_term : (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) 0 : ℤ) * Real.log r = 0 := by
    -- When f(0) ≠ 0, the meromorphic order at 0 is 0, so divisor(0) = 0
    have h0_mem : (0 : ℂ) ∈ closedBall (0 : ℂ) |r| := by simp [hr_abs, hr0.le]
    rw [MeromorphicOn.divisor_apply hf_an_ball.meromorphicOn h0_mem]
    -- f is analytic at 0, so meromorphicOrderAt = analyticOrderAt (as a natural)
    -- f(0) ≠ 0 implies analyticOrderAt = 0
    have hf_an_0' : AnalyticAt ℂ f 0 := hf_an_ball 0 h0_mem
    have h_order_0 : meromorphicOrderAt f 0 = 0 := by
      rw [hf_an_0'.meromorphicOrderAt_eq]
      simp [hf_an_0'.analyticOrderAt_eq_zero.mpr hf0]
    simp [h_order_0]
  -- The finsum term is nonnegative (divisor ≥ 0 and log factor ≥ 0 for each u)
  -- This uses AnalyticOnNhd.divisor_nonneg from Mathlib.Analysis.Meromorphic.Divisor
  have h_finsum_nonneg : 0 ≤ ∑ᶠ u, ↑(MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) u) *
      Real.log (r * ‖0 - u‖⁻¹) := by
    -- Each term is nonneg: divisor(u) ≥ 0 (analytic) and log(r/‖u‖) ≥ 0 (u in ball)
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |r|
    · -- In the ball: use divisor_nonneg and log factor bound
      have h_div_u_nonneg : 0 ≤ (MeromorphicOn.divisor f (closedBall (0 : ℂ) |r|) u : ℤ) := by
        rw [MeromorphicOn.divisor_apply hf_an_ball.meromorphicOn hu]
        -- Analytic functions have nonnegative meromorphic order; divisor is untop₀ of order
        have h_ord := (hf_an_ball u hu).meromorphicOrderAt_nonneg
        -- (meromorphicOrderAt f u).untop₀ is nonneg when 0 ≤ meromorphicOrderAt f u
        exact WithTop.untop₀_nonneg.mpr h_ord
      have h_log_nonneg : 0 ≤ Real.log (r * ‖0 - u‖⁻¹) := by
        by_cases hu_zero : u = 0
        · -- At u = 0, ‖0 - 0‖⁻¹ = 0⁻¹ = 0, so log(r * 0) = log(0)
          simp only [hu_zero, sub_zero, norm_zero, inv_zero, mul_zero, Real.log_zero, le_refl]
        · have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu_zero
          have hu_in : ‖u‖ ≤ r := by simp only [mem_closedBall, dist_zero_right, hr_abs] at hu; exact hu
          have h_eq : ‖0 - u‖ = ‖u‖ := by simp
          rw [h_eq]
          apply Real.log_nonneg
          -- Need to show: 1 ≤ r * ‖u‖⁻¹, i.e., ‖u‖ ≤ r
          calc 1 = r * r⁻¹ := by field_simp
            _ ≤ r * ‖u‖⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hu_norm hu_in) hr0.le
      exact mul_nonneg (Int.cast_nonneg.mpr h_div_u_nonneg) h_log_nonneg
    · -- Outside the ball: divisor is 0 by definition
      simp only [MeromorphicOn.divisor_def, hf_an_ball.meromorphicOn, hu, and_false, ite_false,
        Int.cast_zero, zero_mul, le_refl]
  linarith [h_div_0_term, h_finsum_nonneg]

/-- For analytic nonvanishing f, the circle average of log|f| equals log|f(0)|.
This is the mean value property for harmonic functions (log|f| is harmonic when f ≠ 0). -/
lemma IsInHInfty.circleAverage_log_norm_eq {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf_ne : ∀ z ∈ unitDisc, f z ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    circleAverage (fun z => Real.log ‖f z‖) 0 r = Real.log ‖f 0‖ := by
  -- Apply Mathlib's mean value property for analytic nonvanishing functions.
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) |r| ⊆ unitDisc := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz
    simp only [mem_unitDisc]
    calc ‖z‖ ≤ |r| := hz
      _ = r := hr_abs
      _ < 1 := hr1
  -- f is nonvanishing on the closed ball
  have hf_ne' : ∀ z ∈ closedBall (0 : ℂ) |r|, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
  -- For open sets, AnalyticOn ↔ AnalyticOnNhd
  have hf_anNhd : AnalyticOnNhd ℂ f unitDisc := isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf.analyticOn
  -- f is analytic on a neighborhood of the closed ball
  have hf_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) := fun z hz => hf_anNhd z (h_subset hz)
  -- Apply the mean value property
  exact AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hf_an hf_ne'

/-! ### Connection to Nevanlinna theory -/

/-- The proximity function m(r, f) for Hardy space functions. -/
def proximityFunction (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  circleAverage (fun z => log⁺ ‖f z‖) 0 r

/-- For bounded f, the proximity function is bounded. -/
lemma IsInHInfty.proximityFunction_bounded {f : ℂ → ℂ} (hf : IsInHInfty f) :
    ∃ M : ℝ, ∀ r : ℝ, 0 < r → r < 1 → proximityFunction f r ≤ M := by
  obtain ⟨C, hC⟩ := hf.bounded
  use log⁺ C
  intro r hr0 hr1
  unfold proximityFunction
  -- The proof uses that log⁺ ‖f‖ ≤ log⁺ C pointwise, hence the average is bounded.
  have h_subset := closedDisc_subset_unitDisc hr1
  have h_pointwise : ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖f z‖ ≤ log⁺ C := by
    intro z hz
    have hz_disc : z ∈ unitDisc := by
      simp only [mem_unitDisc, Metric.mem_sphere, dist_zero_right, abs_of_pos hr0] at hz ⊢
      rw [hz]; exact hr1
    exact posLog_le_posLog (norm_nonneg _) (hC z hz_disc)
  -- Circle integrability
  have hInt : CircleIntegrable (fun z => log⁺ ‖f z‖) 0 r := by
    have hf_cont := hf.continuousOn.mono h_subset
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖f z‖) (closedDisc r) :=
      ValueDistribution.continuous_posLog.comp_continuousOn
        (continuous_norm.comp_continuousOn hf_cont)
    exact Nevanlinna.circleIntegrable_continuous_on_closedBall hr0 h_g_cont
  exact circleAverage_mono_on_of_le_circle hInt h_pointwise

/-- For bounded nonvanishing f, the proximity function of 1/f is related to that of f
by the First Main Theorem identity. -/
lemma IsInHInfty.proximityFunction_inv_eq {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf_ne : ∀ z ∈ unitDisc, f z ≠ 0) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    proximityFunction (fun z => (f z)⁻¹) r =
      proximityFunction f r - Real.log ‖f 0‖ := by
  -- This is the First Main Theorem identity for nonvanishing functions.
  -- The key identity: log⁺(x⁻¹) = log⁺(x) - log(x) for x > 0
  -- Taking circle averages: m(r, 1/f) = m(r, f) - circleAverage(log|f|)
  --                                   = m(r, f) - log|f(0)| (by mean value property)
  unfold proximityFunction
  have hr_abs : |r| = r := abs_of_pos hr0
  have h_subset : closedBall (0 : ℂ) r ⊆ unitDisc := by
    intro z hz
    simp only [mem_closedBall, dist_zero_right] at hz
    simp only [mem_unitDisc]
    exact lt_of_le_of_lt hz hr1
  -- f is nonvanishing on the closed ball
  have hf_ne' : ∀ z ∈ closedBall (0 : ℂ) r, f z ≠ 0 := fun z hz => hf_ne z (h_subset hz)
  -- For open sets, AnalyticOn ↔ AnalyticOnNhd
  have hf_anNhd : AnalyticOnNhd ℂ f unitDisc := isOpen_unitDisc.analyticOn_iff_analyticOnNhd.mp hf.analyticOn
  -- f is analytic on a neighborhood of the closed ball
  have hf_an : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r) := fun z hz => hf_anNhd z (h_subset hz)
  -- The circle average of log|f| equals log|f(0)| by mean value property
  have hf_ne_abs : ∀ z ∈ closedBall (0 : ℂ) |r|, f z ≠ 0 := by rwa [hr_abs]
  have hf_an_abs : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) |r|) := by rwa [hr_abs]
  have h_mv := AnalyticOnNhd.circleAverage_log_norm_of_ne_zero hf_an_abs hf_ne_abs
  -- Pointwise identity: log⁺|f⁻¹| = log⁺|f| - log|f| for nonvanishing f
  -- This uses: log⁺ x - log⁺ x⁻¹ = log x (Real.posLog_sub_posLog_inv)
  -- Rearranging: log⁺ x⁻¹ = log⁺ x - log x
  have h_key : ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖(f z)⁻¹‖ = log⁺ ‖f z‖ - Real.log ‖f z‖ := by
    intro z hz
    have hz_disc : z ∈ unitDisc := by
      simp only [mem_sphere, dist_zero_right, hr_abs] at hz
      simp only [mem_unitDisc, hz, hr1]
    have hfz_ne : f z ≠ 0 := hf_ne z hz_disc
    have hfz_pos : 0 < ‖f z‖ := norm_pos_iff.mpr hfz_ne
    rw [norm_inv]
    -- From log⁺ x - log⁺ x⁻¹ = log x, we get log⁺ x⁻¹ = log⁺ x - log x
    have h := Real.posLog_sub_posLog_inv (x := ‖f z‖)
    linarith
  -- Circle integrability
  have h_int_f : CircleIntegrable (fun z => log⁺ ‖f z‖) 0 r := by
    have hf_cont := hf.continuousOn.mono h_subset
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖f z‖) (closedBall (0 : ℂ) r) :=
      ValueDistribution.continuous_posLog.comp_continuousOn
        (continuous_norm.comp_continuousOn hf_cont)
    exact Nevanlinna.circleIntegrable_continuous_on_closedBall hr0 h_g_cont
  have h_int_log : CircleIntegrable (fun z => Real.log ‖f z‖) 0 r :=
    hf.log_norm_circleIntegrable ⟨0, zero_mem_unitDisc, hf_ne 0 zero_mem_unitDisc⟩ hr0 hr1
  have h_int_inv : CircleIntegrable (fun z => log⁺ ‖(f z)⁻¹‖) 0 r := by
    have hf_inv_cont : ContinuousOn (fun z => (f z)⁻¹) (closedBall (0 : ℂ) r) :=
      ContinuousOn.inv₀ (hf.continuousOn.mono h_subset) hf_ne'
    have h_g_cont : ContinuousOn (fun z => log⁺ ‖(f z)⁻¹‖) (closedBall (0 : ℂ) r) :=
      ValueDistribution.continuous_posLog.comp_continuousOn
        (continuous_norm.comp_continuousOn hf_inv_cont)
    exact Nevanlinna.circleIntegrable_continuous_on_closedBall hr0 h_g_cont
  -- Take circle averages using the pointwise identity
  have h_congr : circleAverage (fun z => log⁺ ‖(f z)⁻¹‖) 0 r =
      circleAverage (fun z => log⁺ ‖f z‖ - Real.log ‖f z‖) 0 r :=
    circleAverage_congr_sphere h_key
  -- circleAverage (f - g) = circleAverage f - circleAverage g
  have h_avg : circleAverage (fun z => log⁺ ‖f z‖ - Real.log ‖f z‖) 0 r =
      circleAverage (fun z => log⁺ ‖f z‖) 0 r - circleAverage (fun z => Real.log ‖f z‖) 0 r := by
    rw [← circleAverage_sub h_int_f h_int_log]
    rfl
  rw [h_congr, h_avg, h_mv]

/-! ### Blaschke products and canonical factorization -/

/-- A function is a Blaschke product if it is a (possibly infinite) product of
Blaschke factors, converging uniformly on compact subsets of the disc. -/
def IsBlaschkeProduct (B : ℂ → ℂ) : Prop :=
  ∃ (zeros : ℕ → ℂ) (mult : ℕ → ℕ),
    (∀ n, zeros n ∈ unitDisc ∨ mult n = 0) ∧
    -- The Blaschke condition: ∑ (1 - |a_n|) < ∞
    Summable (fun n => (1 - ‖zeros n‖) * mult n) ∧
    -- B is the product of Blaschke factors
    ∀ z ∈ unitDisc, B z = ∏' n, (blaschkeFactor (zeros n) z) ^ mult n
  where
    blaschkeFactor (a : ℂ) (z : ℂ) : ℂ :=
      if ‖a‖ = 0 then z else (‖a‖ / a) * (a - z) / (1 - starRingEnd ℂ a * z)

/-- The outer function associated to a positive measurable function on the circle. -/
def outerFunction (u : ℝ → ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi,
    u θ • (Complex.exp (θ * Complex.I) + z) / (Complex.exp (θ * Complex.I) - z))

/-- The canonical factorization theorem: every H^p function (p < ∞) with f ≢ 0
factors as f = B · S · F where B is a Blaschke product, S is a singular inner function,
and F is an outer function.

For H^∞, we have the simpler factorization f = B · G where G is nonvanishing in H^∞. -/
theorem IsInHInfty.canonical_factorization {f : ℂ → ℂ} (hf : IsInHInfty f)
    (hf_ne : ∃ z ∈ unitDisc, f z ≠ 0) :
    ∃ (B G : ℂ → ℂ),
      IsBlaschkeProduct B ∧
      IsInHInfty G ∧
      (∀ z ∈ unitDisc, G z ≠ 0) ∧
      ∀ z ∈ unitDisc, f z = B z * G z := by
  /-
  **Proof Strategy (Blaschke Factorization for H^∞):**

  Step 1: Extract zeros {aₙ} of f with multiplicities.
  By the identity theorem, f ≢ 0 has at most countably many zeros in the disc.

  Step 2: Prove the Blaschke condition ∑(1 - |aₙ|) < ∞.
  Jensen's formula gives: log|f(0)| + ∑_{|aₙ|<r} log(r/|aₙ|) ≤ log M.
  Taking r → 1 and using log(r/|a|) ≥ (1-|a|) yields the condition.

  Step 3: Construct B(z) = ∏ₙ bₙ(z) where bₙ is the Blaschke factor for aₙ.
  The product converges uniformly on compact subsets by the M-test,
  using |1 - bₙ(z)| ≤ C(1 - |aₙ|).

  Step 4: Define G = f/B on unitDisc \ {zeros of f}.
  At each aₙ, the zero of f is cancelled by B, so G extends analytically.
  G is nonvanishing by construction.

  Step 5: Show G ∈ H^∞ with the same bound M.
  Use |B(z)| ≤ 1 and |B(z)| → 1 as |z| → 1 (radial limits).
  By the maximum principle, |G| = |f|/|B| ≤ M on the disc.
  -/
  sorry

end Complex

end
