
import Riemann.Mathlib.Analysis.Complex.HardySpace.PoissonKernel
import Mathlib.MeasureTheory.Function.AEMeasurableSequence
import Mathlib.Topology.MetricSpace.Dilation
import Riemann.Mathlib.Analysis.Complex.HardySpace.Basic

/-!
# Fatou's Theorem for Hardy Spaces

This file develops Fatou's theorem on the existence of radial (non-tangential)
limits for bounded analytic functions on the unit disc.
See: https://en.wikipedia.org/wiki/Fatou%27s_theorem

## Main definitions

* `Complex.radialPath` : The radial path r ↦ f(r·e^{iθ})
* `Complex.radialLimit` : The radial limit at angle θ
* `Complex.HasRadialLimit` : Predicate for existence of radial limit
* `Complex.IsInHInfty.boundaryValue` : The boundary value function (defined a.e.)

## Main results

* `Complex.IsInHInfty.radialLimit_exists_ae` : Fatou's theorem for H^∞
* `Complex.IsInHInfty.clusterPt_exists` : Cluster points always exist

## References

* Stein, E.M., Shakarchi, R., "Complex Analysis", Chapter 5
* Garnett, J.B., "Bounded Analytic Functions", Chapter II
-/

noncomputable section

open Complex Set Metric Filter Topology Real MeasureTheory
open scoped UnitDisc ENNReal NNReal

namespace Complex

/-! ### Radial path infrastructure -/

/-- The radial path parametrization for a function on the disc. -/
@[simp]
def radialPath (f : ℂ → ℂ) (θ : ℝ) : ℝ → ℂ := fun r => f (circleMap 0 r θ)

/-- The radial limit of f at angle θ, if it exists. -/
def radialLimit (f : ℂ → ℂ) (θ : ℝ) : ℂ :=
  limUnder (𝓝[<] 1) (radialPath f θ)

/-- The radial path maps (0, 1) into the unit disc. -/
lemma radialPath_mapsTo_unitDisc (θ : ℝ) :
    MapsTo (fun r => circleMap 0 r θ) (Ioo 0 1) unitDisc := by
  intro r ⟨hr0, hr1⟩
  simp only [mem_unitDisc, circleMap, zero_add, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr0, hr1]

/-- The circleMap is continuous in the radius parameter. -/
lemma continuous_circleMap_radius (θ : ℝ) : Continuous (fun r : ℝ => circleMap 0 r θ) := by
  simp only [circleMap, zero_add]
  exact continuous_ofReal.smul continuous_const

/-- A point θ has a radial limit if the radial path converges. -/
def HasRadialLimit (f : ℂ → ℂ) (θ : ℝ) : Prop :=
  ∃ L : ℂ, Tendsto (radialPath f θ) (𝓝[<] 1) (𝓝 L)

/-- If a radial limit exists, it equals any cluster point. -/
lemma radialLimit_unique_of_exists {f : ℂ → ℂ} {θ : ℝ} {L₁ L₂ : ℂ}
    (h₁ : Tendsto (radialPath f θ) (𝓝[<] 1) (𝓝 L₁))
    (h₂ : MapClusterPt L₂ (𝓝[<] 1) (radialPath f θ)) : L₁ = L₂ := by
  -- In a metric space, if x is a limit and y is a cluster point, then x = y
  by_contra h_ne
  have h_dist : 0 < dist L₁ L₂ := dist_pos.mpr h_ne
  have : ∀ᶠ r in 𝓝[<] 1, dist (radialPath f θ r) L₁ < dist L₁ L₂ / 2 :=
    h₁ (Metric.ball_mem_nhds L₁ (by linarith))
  have h₂_freq : ∃ᶠ r in 𝓝[<] 1, dist (radialPath f θ r) L₂ < dist L₁ L₂ / 2 := by
    rw [MapClusterPt] at h₂
    exact h₂.frequently (Metric.ball_mem_nhds L₂ (by linarith))
  have h_both : ∃ᶠ r in 𝓝[<] 1, dist (radialPath f θ r) L₂ < dist L₁ L₂ / 2 ∧
                                  dist (radialPath f θ r) L₁ < dist L₁ L₂ / 2 :=
    h₂_freq.and_eventually this
  obtain ⟨r, hr₂, hr₁⟩ := h_both.exists
  have h_tri : dist L₁ L₂ ≤ dist L₁ (radialPath f θ r) + dist (radialPath f θ r) L₂ :=
    dist_triangle L₁ (radialPath f θ r) L₂
  have hr₁' : dist L₁ (radialPath f θ r) < dist L₁ L₂ / 2 := by
    rw [dist_comm]; exact hr₁
  linarith

/-- For bounded functions, the radial path eventually lies in a compact set. -/
lemma radialPath_eventually_in_closedBall {f : ℂ → ℂ} {M : ℝ}
    (hM : ∀ z ∈ unitDisc, ‖f z‖ ≤ M) (θ : ℝ) :
    ∀ᶠ r in 𝓝[<] 1, radialPath f θ r ∈ Metric.closedBall (0 : ℂ) M := by
  have h_in : ∀ r ∈ Ioo (1/2 : ℝ) 1, radialPath f θ r ∈ Metric.closedBall (0 : ℂ) M := by
    intro r ⟨hr_lo, hr_hi⟩
    simp only [radialPath, Metric.mem_closedBall, dist_zero_right]
    apply hM
    simp only [mem_unitDisc, circleMap, zero_add, norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r), hr_hi]
  have h_mem : Ioo (1/2 : ℝ) 1 ∈ 𝓝[<] 1 := by
    rw [mem_nhdsWithin]
    refine ⟨Ioo (1/2 : ℝ) 2, isOpen_Ioo, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro x hx
    simp only [mem_inter_iff, mem_Ioo, mem_Iio] at hx ⊢
    exact ⟨hx.1.1, hx.2⟩
  exact eventually_of_mem h_mem h_in

/-- Existence of a cluster point for bounded radial paths via compactness. -/
lemma radialPath_exists_clusterPt {f : ℂ → ℂ} {M : ℝ} (_ : 0 ≤ M)
    (hM : ∀ z ∈ unitDisc, ‖f z‖ ≤ M) (θ : ℝ) :
    ∃ L ∈ Metric.closedBall (0 : ℂ) M, MapClusterPt L (𝓝[<] 1) (radialPath f θ) := by
  have h_compact : IsCompact (Metric.closedBall (0 : ℂ) M) := isCompact_closedBall 0 M
  have h_eventually := radialPath_eventually_in_closedBall hM θ
  apply h_compact.exists_mapClusterPt_of_frequently
  exact Eventually.frequently h_eventually

/-- For H^∞ functions, the radial path is continuous on (0, 1). -/
lemma IsInHInfty.radialPath_continuousOn {f : ℂ → ℂ} (hf : IsInHInfty f) (θ : ℝ) :
    ContinuousOn (radialPath f θ) (Ioo 0 1) := by
  unfold radialPath
  have h_circle_cont := continuous_circleMap_radius θ
  have h_maps := radialPath_mapsTo_unitDisc θ
  exact hf.continuousOn.comp h_circle_cont.continuousOn h_maps

/-- Set of points where radial limit exists. -/
def radialLimitSet (f : ℂ → ℂ) : Set ℝ :=
  {θ | HasRadialLimit f θ}

/-- Cluster points always exist (this is TRUE for all θ, by compactness). -/
theorem IsInHInfty.clusterPt_exists {f : ℂ → ℂ} (hf : IsInHInfty f) (θ : ℝ) :
    ∃ L : ℂ, MapClusterPt L (𝓝[<] 1) (radialPath f θ) := by
  obtain ⟨M, hM⟩ := hf.bounded
  have hM_nonneg : 0 ≤ M := by
    by_contra h_neg; push_neg at h_neg
    have : ‖f 0‖ ≤ M := hM 0 zero_mem_unitDisc
    linarith [norm_nonneg (f 0)]
  obtain ⟨L, _, hL⟩ := radialPath_exists_clusterPt hM_nonneg hM θ
  exact ⟨L, hL⟩

/-- The boundary value function for H^∞, defined a.e.
At points where the radial limit exists, this equals that limit.
At other points, we pick an arbitrary cluster point (which always exists). -/
def IsInHInfty.boundaryValue {f : ℂ → ℂ} (hf : IsInHInfty f) : ℝ → ℂ :=
  fun θ => (hf.clusterPt_exists θ).choose

/-- At points where the radial limit exists, boundaryValue equals the limit. -/
lemma IsInHInfty.boundaryValue_eq_limit {f : ℂ → ℂ} (hf : IsInHInfty f) {θ : ℝ}
    (hθ : HasRadialLimit f θ) : ∃ L : ℂ,
    Tendsto (radialPath f θ) (𝓝[<] 1) (𝓝 L) ∧ hf.boundaryValue θ = L := by
  obtain ⟨L, hL⟩ := hθ
  refine ⟨L, hL, ?_⟩
  have h_cluster : MapClusterPt (hf.boundaryValue θ) (𝓝[<] 1) (radialPath f θ) :=
    (hf.clusterPt_exists θ).choose_spec
  exact (radialLimit_unique_of_exists hL h_cluster).symm

/-- **Fatou's Theorem (Almost Everywhere Version)**

For f ∈ H^∞, the radial limit exists for almost every θ ∈ [0, 2π).
This is the fundamental theorem on boundary values of bounded analytic functions.

**Key ingredients:**
1. Poisson representation of bounded harmonic functions
2. Lebesgue differentiation theorem
3. The fact that the Poisson kernel is an approximate identity
-/
theorem IsInHInfty.radialLimit_exists_ae {f : ℂ → ℂ} (hf : IsInHInfty f) :
    ∀ᵐ θ ∂volume, HasRadialLimit f θ := by
  -- The proof uses Poisson representation and Lebesgue differentiation
  -- This requires the full infrastructure from measure theory
  sorry

/-- For H^∞ functions, the radial limit set has full measure. -/
theorem IsInHInfty.radialLimitSet_ae_eq_univ {f : ℂ → ℂ} (hf : IsInHInfty f) :
    radialLimitSet f =ᵐ[volume] Set.univ := by
  simp only [eventuallyEq_set, mem_univ, iff_true]
  exact hf.radialLimit_exists_ae

/-- The boundary value function is AE measurable.

**Proof Strategy:**
The boundary value function θ ↦ lim_{r→1⁻} f(r·e^{iθ}) is AE measurable because:

1. For each n, the function fₙ(θ) = f((1-1/(n+2))·e^{iθ}) is continuous (hence measurable)
2. fₙ → boundaryValue pointwise a.e. by Fatou's theorem
3. A.e. pointwise limits of measurable functions are AE measurable
-/
lemma IsInHInfty.boundaryValue_aemeasurable {f : ℂ → ℂ} (hf : IsInHInfty f) :
    AEMeasurable hf.boundaryValue volume := by
  -- Define the approximating sequence: fₙ(θ) = f((1 - 1/(n+2))·e^{iθ})
  let rₙ : ℕ → ℝ := fun n => 1 - 1 / (n + 2)

  -- Each rₙ is in (0, 1)
  have hrₙ_pos : ∀ n, 0 < rₙ n := by
    intro n
    simp only [rₙ]
    have h1 : (n : ℝ) + 2 > 0 := by positivity
    have h2 : 1 / ((n : ℝ) + 2) > 0 := one_div_pos.mpr h1
    have h3 : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one h1]
      linarith
    linarith

  have hrₙ_lt : ∀ n, rₙ n < 1 := by
    intro n
    simp only [rₙ]
    have h1 : (n : ℝ) + 2 > 0 := by positivity
    have h2 : 1 / ((n : ℝ) + 2) > 0 := one_div_pos.mpr h1
    linarith

  -- The sequence rₙ → 1
  have hrₙ_tendsto : Tendsto rₙ atTop (𝓝 1) := by
    simp only [rₙ]
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 : Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h2
    simp only [sub_zero] at h3
    convert h3 using 1
    ext n; simp [one_div]

  -- Step 1: Each approximant θ ↦ f((1-1/(n+2))·e^{iθ}) is continuous, hence measurable
  have h_approx_measurable : ∀ n, Measurable (fun θ : ℝ => f (circleMap 0 (rₙ n) θ)) := by
    intro n
    have h_circle_cont : Continuous (fun θ : ℝ => circleMap 0 (rₙ n) θ) := continuous_circleMap 0 (rₙ n)
    have h_maps : ∀ θ : ℝ, circleMap 0 (rₙ n) θ ∈ unitDisc := by
      intro θ
      simp only [mem_unitDisc, circleMap, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I,
        mul_one, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_pos (hrₙ_pos n)]
      exact hrₙ_lt n
    have h_cont : Continuous (fun θ : ℝ => f (circleMap 0 (rₙ n) θ)) :=
      hf.continuousOn.comp_continuous h_circle_cont h_maps
    exact h_cont.measurable

  -- Step 2: For a.e. θ, the approximants converge to the boundary value
  have h_tendsto_ae : ∀ᵐ θ ∂volume, Tendsto (fun n => f (circleMap 0 (rₙ n) θ)) atTop (𝓝 (hf.boundaryValue θ)) := by
    filter_upwards [hf.radialLimit_exists_ae] with θ hθ
    obtain ⟨L, hL, hL_eq⟩ := hf.boundaryValue_eq_limit hθ
    rw [hL_eq]
    apply hL.comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hrₙ_tendsto, ?_⟩
    filter_upwards with n
    exact hrₙ_lt n

  -- Step 3: Apply aemeasurable_of_tendsto_metrizable_ae
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (h_approx_measurable n).aemeasurable) h_tendsto_ae

end Complex
