import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Riemann.Mathlib.Analysis.Complex.DeBranges.Basic

/-!
# Infrastructure for Zeros of Analytic Functions and Local Integrability

This file provides tools to analyze the order of zeros of entire functions and
establishes the correspondence between the absence of real zeros and the
local finiteness of the de Branges measure.
-/

open Complex Topology Filter MeasureTheory Asymptotics
open scoped Topology

namespace Complex

/-! ### 1. Order of Zeros (Multiplicity) -/

/--
If `f` is entire and not identically zero, then for any `z₀`, there is a unique
order `N` (the multiplicity) and an analytic `g` near `z₀` with `g z₀ ≠ 0` such that
locally around `z₀` we have
\[
  f z = (z - z₀)^N \cdot g z.
\]

This is a local factorization statement, phrased using `∀ᶠ z in 𝓝 z₀, …`, and is a wrapper
around `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` together with the identity
principle for entire functions.
-/
lemma exists_order_and_factorization {f : ℂ → ℂ} (hf_entire : Differentiable ℂ f)
    (hf_not_id_zero : f ≠ 0) (z₀ : ℂ) :
    ∃! (N : ℕ), ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
      g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ N • g z := by
  classical
  -- Upgrade differentiability to analyticity on `ℂ`.
  have hf_analyticOn : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (Complex.analyticOnNhd_univ_iff_differentiable (f := f)).2 hf_entire
  have hf_analyticAt : AnalyticAt ℂ f z₀ :=
    hf_analyticOn z₀ (by simp)

  -- `f` is not locally zero around `z₀`, otherwise the identity principle would force `f = 0`.
  have hf_not_locally_zero : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
    intro hLoc
    -- `EqOn f 0 univ` by the identity principle.
    have hEqOn :
        Set.EqOn f (fun _ : ℂ => (0 : ℂ)) (Set.univ : Set ℂ) := by
      have hfz₀ : f =ᶠ[𝓝 z₀] (fun _ : ℂ => (0 : ℂ)) := by
        -- `EventuallyEq` is just eventual equality of the values.
        simpa [Filter.EventuallyEq, Pi.zero_apply] using hLoc
      -- Apply the identity principle on the connected set `univ`.
      have h :=
        (hf_analyticOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (U := (Set.univ : Set ℂ)) (z₀ := z₀)
          isPreconnected_univ (by simp) hfz₀)
      simpa [Pi.zero_apply] using h
    -- Hence `f = 0`, contradicting `hf_not_id_zero`.
    have h_zero : f = 0 := by
      funext z
      have hz := hEqOn (by simp : z ∈ (Set.univ : Set ℂ))
      simpa [Pi.zero_apply] using hz
    exact hf_not_id_zero h_zero

  -- Existence of some order `N` and analytic `g` with the desired local factorization.
  obtain ⟨N, g, hg_an, hg_ne, hg_eq⟩ :=
    (hf_analyticAt.exists_eventuallyEq_pow_smul_nonzero_iff).2 hf_not_locally_zero

  refine ⟨N, ?_, ?_⟩
  · exact ⟨g, hg_an, hg_ne, hg_eq⟩
  · -- Uniqueness of the order: use `AnalyticAt.unique_eventuallyEq_pow_smul_nonzero`.
    intro N' hN'
    rcases hN' with ⟨g', hg'_an, hg'_ne, hg'_eq⟩
    have h :=
      AnalyticAt.unique_eventuallyEq_pow_smul_nonzero
        (𝕜 := ℂ) (E := ℂ) (f := f) (z₀ := z₀)
        (m := N) (n := N')
        ⟨g, hg_an, hg_ne, hg_eq⟩
        ⟨g', hg'_an, hg'_ne, hg'_eq⟩
    exact h.symm

open Asymptotics

/--
Asymptotic behavior near a zero. If `f(z₀)=0`, then `f(z) = Θ((z-z₀)^N)` for `N ≥ 1`.
-/
lemma isTheta_at_zero_order {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (z₀ : ℂ) :
    ∃ (N : ℕ), (f z₀ = 0 → N ≥ 1) ∧
    f =Θ[𝓝 z₀] (fun z => (z - z₀) ^ N) := by
  classical
  -- 1. Factorization f = (z - z₀)^N • g with g analytic and nonvanishing at z₀.
  obtain ⟨N, hN_exists, -⟩ :=
    exists_order_and_factorization (f := f)
      (hf_entire := hf) (hf_not_id_zero := hf_ne) z₀
  rcases hN_exists with ⟨g, hg_an, hg_ne, hg_eq⟩
  -- 2. Show N ≥ 1 if f z₀ = 0.
  have hNpos : f z₀ = 0 → 1 ≤ N := by
    intro hf0
    -- If N = 0 then f =ᶠ g near z₀, hence by continuity f z₀ = g z₀, contradiction.
    by_contra hN
    have hN0 : N = 0 := by
      -- from ¬ (1 ≤ N) we get N ≤ 0
      have hle : N ≤ 0 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hN)
      -- in ℕ, N ≤ 0 implies N = 0
      exact le_antisymm hle (Nat.zero_le _)
    subst hN0
    have h_ev : f =ᶠ[𝓝 z₀] fun z => (z - z₀) ^ (0 : ℕ) * g z := by
      -- turn the eventual equality with `•` into one with `*`
      have := hg_eq
      -- `smul_eq_mul` on ℂ
      refine this.mono ?_
      intro z hz; simpa [pow_zero, one_mul, smul_eq_mul] using hz
    -- Take the equality at the point z₀ from the eventual equality.
    have h_val : f z₀ = (z₀ - z₀) ^ (0 : ℕ) * g z₀ :=
      Filter.EventuallyEq.eq_of_nhds h_ev
    -- Using f z₀ = 0, this forces g z₀ = 0, contradicting hg_ne.
    have hg0' : 0 = g z₀ := by
      simpa [hf0, pow_zero, one_mul] using h_val
    have hg0 : g z₀ = 0 := hg0'.symm
    exact hg_ne hg0
  -- 3. Θ-asymptotics.
  -- First, pass from eventual equality to Θ for the factored form.
  have h_ev_mul : f =ᶠ[𝓝 z₀] fun z => (z - z₀) ^ N * g z := by
    refine hg_eq.mono ?_
    intro z hz; simpa [smul_eq_mul] using hz
  have hTheta_mul : f =Θ[𝓝 z₀] (fun z => (z - z₀) ^ N * g z) :=
    h_ev_mul.isTheta
  -- Next, show g is Θ to the constant g z₀, using continuity and g z₀ ≠ 0.
  have h_cont_g : ContinuousAt g z₀ := hg_an.continuousAt
  have hTheta_g_const :
      (fun z => g z) =Θ[𝓝 z₀] fun _ => g z₀ := by
    -- Consider h(z) = g z - g z₀, which tends to 0 at z₀.
    let h : ℂ → ℂ := fun z => g z - g z₀
    have h_tendsto : Tendsto h (𝓝 z₀) (𝓝 0) := by
      have h_cont : ContinuousAt h z₀ := h_cont_g.sub continuousAt_const
      simpa [h] using h_cont.tendsto
    -- Hence h =o[𝓝 z₀] (const g z₀) by `isLittleO_const_iff`.
    have h_littleO_const :
        h =o[𝓝 z₀] (fun _ : ℂ => g z₀) :=
      (Asymptotics.isLittleO_const_iff (l := 𝓝 z₀) (f'' := h)
        (c := g z₀) hg_ne).2 h_tendsto
    -- Then const =Θ (h + const) =Θ g.
    have hTheta_const_g :
        (fun _ : ℂ => g z₀) =Θ[𝓝 z₀] (fun z => h z + g z₀) :=
      Asymptotics.IsLittleO.right_isTheta_add h_littleO_const
    have h_eq : (fun z => h z + g z₀) =ᶠ[𝓝 z₀] g := by
      refine Filter.Eventually.of_forall ?_
      intro z
      simp [h]
    exact (hTheta_const_g.trans_eventuallyEq h_eq).symm
  -- Combine Θ for g with Θ for the factor (z - z₀)^N.
  have hTheta_prod :
      (fun z => (z - z₀) ^ N * g z) =Θ[𝓝 z₀]
      (fun z => (z - z₀) ^ N * g z₀) :=
    (Asymptotics.isTheta_refl _ _).mul hTheta_g_const
  -- Drop the nonzero constant factor `g z₀`.
  have hTheta_drop :
      (fun z => g z₀ * (z - z₀) ^ N) =Θ[𝓝 z₀] (fun z => (z - z₀) ^ N) := by
    -- First get Θ for the base function and its constant multiple
    have hTheta_base_scaled :
        (fun z => (z - z₀) ^ N) =Θ[𝓝 z₀] fun z => g z₀ * (z - z₀) ^ N :=
      (Asymptotics.isTheta_const_mul_right
        (l := 𝓝 z₀)
        (f := fun z => (z - z₀) ^ N)
        (g := fun z => (z - z₀) ^ N)
        (c := g z₀) hg_ne).2
        (Asymptotics.isTheta_rfl
          (f := fun z => (z - z₀) ^ N)
          (l := 𝓝 z₀))
    -- Then just flip the Θ-equivalence.
    exact hTheta_base_scaled.symm

  -- Adjust the middle factor of `hTheta_prod` so it matches `hTheta_drop`.
  have h_middle_eq :
      (fun z => (z - z₀) ^ N * g z₀) =ᶠ[𝓝 z₀] fun z => g z₀ * (z - z₀) ^ N := by
    filter_upwards with z
    ring
  have hTheta_prod' :
      (fun z => (z - z₀) ^ N * g z) =Θ[𝓝 z₀] fun z => g z₀ * (z - z₀) ^ N :=
    hTheta_prod.trans_eventuallyEq h_middle_eq

  -- Final chaining: f Θ (z - z₀)^N * g z Θ g z₀ * (z - z₀)^N Θ (z - z₀)^N.
  refine ⟨N, hNpos, ?_⟩
  exact hTheta_mul.trans (hTheta_prod'.trans hTheta_drop)

end Complex
namespace MeasureTheory

open Real Set
/-!
### 2. Local integrability of a power singularity at a point

We first characterize integrability of `|x|^(-p)` on a one-sided interval `(0, t)`,
then use symmetry to handle a punctured symmetric interval around `0`. This is the
core analytic input for the de Branges measure singularity analysis.
-/

/-- One-sided integrability of a power at `0`: `∫_{0 < x < t} |x|^{-p} dx` is finite
iff `p < 1`. This is a direct reformulation of `integrableOn_Ioo_rpow_iff`. -/
lemma integrableOn_Ioo_abs_rpow_neg_iff {p t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => |x| ^ (-p)) (Ioo (0 : ℝ) t) volume ↔ p < 1 := by
  -- On `(0, t)`, we have `|x| = x`, so `|x|^(-p) = x^(-p)` pointwise on that set.
  have h_abs :
      ∀ ⦃x : ℝ⦄, x ∈ Ioo (0 : ℝ) t → |x| ^ (-p) = x ^ (-p) := by
    intro x hx
    have hx_pos : 0 < x := hx.1
    simp [abs_of_pos hx_pos]
  -- Use this to replace the integrand on `Ioo (0,t)`.
  have h_congr :
      IntegrableOn (fun x : ℝ => |x| ^ (-p)) (Ioo (0 : ℝ) t) volume
        ↔ IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioo (0 : ℝ) t) volume := by
    -- Pointwise equality on the integration domain `(0,t)`.
    have hEq :
        EqOn (fun x : ℝ => |x| ^ (-p)) (fun x : ℝ => x ^ (-p)) (Ioo (0 : ℝ) t) := by
      intro x hx
      simp [h_abs hx]
    -- Now use the standard congruence lemma for `IntegrableOn`.
    exact integrableOn_congr_fun hEq isOpen_Ioo.measurableSet
  -- Now use the library lemma for `x ↦ x ^ s` with `s = -p`.
  have h_core :
      IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioo (0 : ℝ) t) volume ↔ -1 < -p :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -p) ht)
  -- Translate `-1 < -p` to `p < 1`.
  constructor
  · intro h
    have h' : IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioo (0 : ℝ) t) volume :=
      h_congr.mp h
    have h_exp : -1 < -p := h_core.mp h'
    have : p < 1 := by linarith
    exact this
  · intro hp_lt
    have h_exp : -1 < -p := by linarith
    have h' : IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioo (0 : ℝ) t) volume :=
      h_core.mpr h_exp
    exact h_congr.mpr h'

/-! ### 2. Local Integrability of Power Singularities -/

/-- Local integrability at a single point: `nhds x₀` version of the p-test. -/
lemma integrableAtFilter_abs_sub_rpow_neg (x₀ : ℝ) (p : ℝ) :
  IntegrableAtFilter (fun x : ℝ => |x - x₀| ^ (-p)) (𝓝 x₀) volume ↔ p < 1 := by
  constructor
  · rintro ⟨s, hs_nhds, h_int⟩
    rcases Metric.mem_nhds_iff.mp hs_nhds with ⟨ε, hε, h_sub⟩
    have h_subset : Ioo x₀ (x₀ + ε) ⊆ s := by
      rw [Real.ball_eq_Ioo] at h_sub
      exact Subset.trans (Ioo_subset_Ioo (by linarith) (by linarith)) h_sub
    have h_int_right : IntegrableOn (fun x => |x - x₀| ^ (-p)) (Ioo x₀ (x₀ + ε)) volume :=
      h_int.mono_set h_subset
    -- Translate x -> x - x₀
    let e := Homeomorph.addLeft x₀
    rw [← map_add_left_eq_self volume x₀] at h_int_right
    change IntegrableOn _ _ (Measure.map e volume) at h_int_right
    erw [MeasurableEmbedding.integrableOn_map_iff e.measurableEmbedding] at h_int_right
    have h_preimage : e ⁻¹' (Ioo x₀ (x₀ + ε)) = Ioo 0 ε := by
      ext y
      simp [e, Homeomorph.addLeft, Ioo]
    rw [h_preimage] at h_int_right
    dsimp [e] at h_int_right
    simp only [Function.comp_def, add_sub_cancel_left] at h_int_right
    rw [integrableOn_Ioo_abs_rpow_neg_iff hε] at h_int_right
    exact h_int_right
  · intro hp_lt
    use Ioo (x₀ - 1) (x₀ + 1)
    refine ⟨Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
    rw [← union_diff_cancel (singleton_subset_iff.2 ⟨by linarith, by linarith⟩ : {x₀} ⊆ Ioo (x₀ - 1) (x₀ + 1))]
    rw [integrableOn_union, integrableOn_singleton_iff]
    refine ⟨?_, ?_⟩
    · simp
    · have : Ioo (x₀ - 1) (x₀ + 1) \ {x₀} = Ioo (x₀ - 1) x₀ ∪ Ioo x₀ (x₀ + 1) := by
        ext x
        simp [mem_Ioo, mem_singleton_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, hne⟩
          rcases lt_trichotomy x x₀ with hlt | heq | hgt
          · exact Or.inl ⟨h1, hlt⟩
          · contradiction
          · exact Or.inr ⟨hgt, h2⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨⟨h1, by linarith⟩, by linarith⟩
          · exact ⟨⟨by linarith, h2⟩, by linarith⟩
      rw [this]
      rw [integrableOn_union]
      constructor
      · -- Left side: Ioo (x₀ - 1) x₀
        let e := Homeomorph.addLeft x₀
        rw [← map_add_left_eq_self volume x₀]
        change IntegrableOn _ _ (Measure.map e volume)
        rw [MeasurableEmbedding.integrableOn_map_iff e.measurableEmbedding]
        have h_preimage : e ⁻¹' (Ioo (x₀ - 1) x₀) = Ioo (-1) 0 := by
          ext y
          simp [e, Homeomorph.addLeft, Ioo]
          grind
        rw [h_preimage]
        dsimp [e]
        simp only [Function.comp_def, add_sub_cancel_left]
        -- Reflect y -> -y
        let neg := Homeomorph.neg ℝ
        -- Lebesgue measure on ℝ is invariant under x ↦ -x
        rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
        change IntegrableOn _ _ (Measure.map neg volume)
        rw [MeasurableEmbedding.integrableOn_map_iff neg.measurableEmbedding]
        have h_preimage_neg : neg ⁻¹' (Ioo (-1) 0) = Ioo 0 1 := by
          ext; simp [neg, Ioo]; constructor <;> intros <;> aesop
        rw [h_preimage_neg]
        dsimp [neg]
        simp only [Function.comp_def, abs_neg]
        rwa [integrableOn_Ioo_abs_rpow_neg_iff zero_lt_one]
      · -- Right side: Ioo x₀ (x₀ + 1)
        let e := Homeomorph.addLeft x₀
        rw [← map_add_left_eq_self volume x₀]
        change IntegrableOn _ _ (Measure.map e volume)
        rw [MeasurableEmbedding.integrableOn_map_iff e.measurableEmbedding]
        have h_preimage : e ⁻¹' (Ioo x₀ (x₀ + 1)) = Ioo 0 1 := by
          ext; simp [e, Ioo]
        rw [h_preimage]
        dsimp [e]
        simp only [Function.comp_def, add_sub_cancel_left]
        rwa [integrableOn_Ioo_abs_rpow_neg_iff zero_lt_one]

lemma locallyIntegrable_abs_sub_rpow_neg (x₀ : ℝ) (p : ℝ) :
    LocallyIntegrable (fun x : ℝ => |x - x₀| ^ (-p)) volume ↔ p < 1 := by
  -- Using LocallyIntegrable definition directly:
  constructor
  · intro h
    -- specialize at `x := x₀`
    have hx := h x₀
    -- apply the local p-test
    exact (integrableAtFilter_abs_sub_rpow_neg x₀ p).1 hx
  · intro hp x
    -- need `IntegrableAtFilter` for every `x`
    by_cases hx : x = x₀
    · subst hx
      -- Now `x = x₀`, so we can reuse the `x₀`-case of the local p-test.
      simpa using (integrableAtFilter_abs_sub_rpow_neg x p).2 hp
    · -- `x ≠ x₀`: function is continuous at x
      have h_cont : ContinuousOn (fun y => |y - x₀| ^ (-p)) {y | y ≠ x₀} := by
        -- base: y ↦ |y - x₀| is continuous on `{y | y ≠ x₀}`
        have h_base : ContinuousOn (fun y : ℝ => |y - x₀|) {y | y ≠ x₀} := by
          refine (Continuous.continuousOn ?_).abs
          exact (continuous_id.sub continuous_const)
        -- exponent: constant function y ↦ -p is continuous
        have h_exp : ContinuousOn (fun _ : ℝ => -p) {y | y ≠ x₀} :=
          continuous_const.continuousOn
        -- apply the real power continuity lemma
        refine ContinuousOn.rpow h_base h_exp ?_
        intro y hy
        -- on `{y | y ≠ x₀}`, the base is nonzero
        left
        have hy' : y - x₀ ≠ 0 := sub_ne_zero.mpr hy
        exact abs_ne_zero.mpr hy'
      have h_open : IsOpen {y : ℝ | y ≠ x₀} := isOpen_ne
      have h_mem : x ∈ {y : ℝ | y ≠ x₀} := hx
      rw [← nhdsWithin_eq_nhds.mpr (IsOpen.mem_nhds h_open h_mem)]
      exact h_cont.integrableAt_nhdsWithin h_open.measurableSet h_mem

/-- Local integrability of `|x - x₀|^{-p}` near `x₀` is controlled by the same
exponent condition `p < 1`. This is the core analytic input; the full
`LocallyIntegrable` statement will add the (easy) translation and compactness
arguments on top of this lemma. -/
lemma locallyIntegrable_abs_sub_rpow_neg' (x₀ : ℝ) (p : ℝ) :
    LocallyIntegrable (fun x : ℝ => |x - x₀| ^ (-p)) volume ↔ p < 1 := by
  -- This is exactly `locallyIntegrable_abs_sub_rpow_neg`.
  simpa using (locallyIntegrable_abs_sub_rpow_neg x₀ p)

end MeasureTheory

namespace DeBrangesFunction

variable (E : DeBrangesFunction)

/-! ### 3. Application to de Branges functions -/

/-- The de Branges weight `w_E(x) = ‖E x‖⁻²` on `ℝ` for a (possibly) real-zero function. -/
noncomputable def weight (x : ℝ) : ℝ :=
  (‖E x‖ ^ 2)⁻¹

/-- The weight function is measurable (in fact continuous; see below). -/
lemma measurable_weight : Measurable E.weight := by
  -- `x ↦ E x` is continuous, hence measurable.
  have hE : Measurable fun x : ℝ => E x :=
    (E.continuous.comp continuous_ofReal).measurable
  -- `x ↦ ‖E x‖` is measurable, so are powers and inverses.
  have h_norm : Measurable fun x : ℝ => ‖E x‖ :=
    (continuous_norm.comp (E.continuous.comp continuous_ofReal)).measurable
  have h_pow : Measurable fun x : ℝ => ‖E x‖ ^ 2 :=
    h_norm.pow_const 2
  have h_inv : Measurable fun x : ℝ => (‖E x‖ ^ 2)⁻¹ :=
    h_pow.inv
  exact h_inv

/-- The corresponding `ENNReal`-valued density. -/
noncomputable def density (x : ℝ) : ENNReal :=
  ENNReal.ofReal (E.weight x)

/-- The de Branges density is measurable as an `ENNReal`-valued function. -/
lemma measurable_density : Measurable E.density := by
  -- `ENNReal.ofReal` is measurable, so we can compose it with `weight`.
  have h := E.measurable_weight
  exact ENNReal.measurable_ofReal.comp h

/-- The de Branges measure `μ_E = |E(x)|⁻² dx` on `ℝ`. -/
noncomputable def measure : Measure ℝ :=
  Measure.withDensity volume E.density

/--
If `E(x₀) = 0`, the weight `|E(x)|^{-2}` behaves asymptotically like `|x - x₀|^{-2N}`
with `N ≥ 1`.
-/
lemma weight_asymptotics_near_real_point {x₀ : ℝ} (hE_not_zero : E.toFun ≠ 0) :
    ∃ (N : ℕ), (E x₀ = 0 → N ≥ 1) ∧ ∃ (C : ℝ), C > 0 ∧
    (fun x : ℝ => E.weight x) =Θ[𝓝 x₀]
      (fun x : ℝ => C * |x - x₀| ^ (-2 * (N : ℝ))) := by
  classical
  -- Consider `E` as a function `ℂ → ℂ`
  let f : ℂ → ℂ := fun z => E z
  have hf_diff : Differentiable ℂ f := E.entire
  -- Apply the complex Θ-order lemma at the real point `x₀ : ℂ`
  obtain ⟨N, hNpos, hTheta_f⟩ :=
    Complex.isTheta_at_zero_order (f := f) hf_diff hE_not_zero (x₀ : ℂ)
  -- From `f =Θ (z-x₀)^N` we get an asymptotic equivalence of norms on ℂ
  have hTheta_norm :
      (fun z : ℂ => ‖f z‖) =Θ[𝓝 (x₀ : ℂ)]
        (fun z : ℂ => ‖z - (x₀ : ℂ)‖ ^ (N : ℕ)) := by
    -- first: `f =Θ (z-x₀)^N` ⇒ norms are Θ‑equivalent
    have h₁ : (fun z : ℂ => ‖f z‖) =Θ[𝓝 (x₀ : ℂ)]
        (fun z : ℂ => ‖(z - (x₀ : ℂ)) ^ N‖) := by
      rw [Asymptotics.isTheta_norm_left, Asymptotics.isTheta_norm_right]
      exact hTheta_f
    -- but `‖(z - x₀)^N‖ = ‖z - x₀‖^N`
    have h₂ :
        (fun z : ℂ => ‖(z - (x₀ : ℂ)) ^ N‖) =ᶠ[𝓝 (x₀ : ℂ)]
          fun z => ‖z - (x₀ : ℂ)‖ ^ (N : ℕ) := by
      refine Filter.Eventually.of_forall ?_
      intro z
      simp [norm_pow]
    exact h₁.trans_eventuallyEq h₂
  -- Square the norms: `‖f z‖^2 =Θ ‖z-x₀‖^(2N)`
  have hTheta_norm_sq :
      (fun z : ℂ => ‖f z‖ ^ 2) =Θ[𝓝 (x₀ : ℂ)]
        (fun z : ℂ => ‖z - (x₀ : ℂ)‖ ^ (2 * N)) := by
    -- use Θ‑pow with exponent 2
    have h := (Asymptotics.IsTheta.pow (f := fun z => ‖f z‖)
        (g := fun z => ‖z - (x₀ : ℂ)‖ ^ (N : ℕ)) hTheta_norm 2)
    -- simplify the right-hand side exponent
    have h_exp :
        (fun z : ℂ => (‖z - (x₀ : ℂ)‖ ^ (N : ℕ)) ^ (2 : ℕ)) =ᶠ[𝓝 (x₀ : ℂ)]
          fun z => ‖z - (x₀ : ℂ)‖ ^ (2 * N) := by
      refine Filter.Eventually.of_forall ?_
      intro z
      -- (a^N)^2 = a^(2*N)
      simp [pow_mul]
      ring_nf
    -- rewrite both sides
    have hL : (fun z : ℂ => ‖f z‖ ^ 2) =Θ[𝓝 (x₀ : ℂ)]
        (fun z : ℂ => (‖z - (x₀ : ℂ)‖ ^ (N : ℕ)) ^ (2 : ℕ)) := h
    exact hL.trans_eventuallyEq h_exp
  -- Invert: `(‖f z‖^2)⁻¹ =Θ ‖z-x₀‖^(-2N)` along `𝓝 (x₀ : ℂ)`
  have hTheta_inv :
      (fun z : ℂ => (‖f z‖ ^ 2)⁻¹) =Θ[𝓝 (x₀ : ℂ)]
        (fun z : ℂ => ‖z - (x₀ : ℂ)‖ ^ (- (2 * N : ℤ))) := by
    -- view powers as integer powers for inversion
    -- First, express both sides with zpow and then apply `IsTheta.inv`
    have h_zpow :
        (fun z : ℂ => ‖f z‖ ^ (2 : ℕ)) =Θ[𝓝 (x₀ : ℂ)]
          (fun z : ℂ => ‖z - (x₀ : ℂ)‖ ^ (2 * N)) := hTheta_norm_sq
    have h_zpow' :
        (fun z : ℂ => ‖f z‖ ^ (2 : ℕ)) =Θ[𝓝 (x₀ : ℂ)]
          (fun z : ℂ => ‖z - (x₀ : ℂ)‖ ^ (2 * N)) :=
      h_zpow
    -- apply Θ‑inversion
    have h_inv :
        (fun z : ℂ => (‖f z‖ ^ 2)⁻¹) =Θ[𝓝 (x₀ : ℂ)]
          (fun z : ℂ => (‖z - (x₀ : ℂ)‖ ^ (2 * N))⁻¹) :=
      Asymptotics.IsTheta.inv
        (l := 𝓝 (x₀ : ℂ))
        (f := fun z => ‖f z‖ ^ 2)
        (g := fun z => ‖z - (x₀ : ℂ)‖ ^ (2 * N))
        h_zpow'
    -- rewrite RHS as a negative integer power
    have h_rewrite :
        (fun z : ℂ => (‖z - (x₀ : ℂ)‖ ^ (2 * N))⁻¹) =ᶠ[𝓝 (x₀ : ℂ)]
          fun z => ‖z - (x₀ : ℂ)‖ ^ (- (2 * N : ℤ)) := by
      refine Filter.Eventually.of_forall ?_
      intro z
      -- (‖z - x₀‖^(2*N))⁻¹ = ‖z - x₀‖^(-(2*N))
      simp [zpow_neg]; rfl
    -- clean up both sides
    have hL :
        (fun z : ℂ => (‖f z‖ ^ (2 : ℕ))⁻¹) =Θ[𝓝 (x₀ : ℂ)]
          (fun z : ℂ => (‖z - (x₀ : ℂ)‖ ^ (2 * N))⁻¹) := h_inv
    have hL' :
        (fun z : ℂ => (‖f z‖ ^ 2)⁻¹) =Θ[𝓝 (x₀ : ℂ)]
          (fun z : ℂ => (‖z - (x₀ : ℂ)‖ ^ (2 * N))⁻¹) := by
      simpa using hL
    exact hL'.trans_eventuallyEq h_rewrite
  -- Now restrict to the real line: `x : ℝ ↦ z := (x : ℂ)`.
  -- On reals, `‖(x:ℂ) - (x₀:ℂ)‖ = |x - x₀|`.
  have hTheta_real :
      (fun x : ℝ => (‖E x‖ ^ 2)⁻¹) =Θ[𝓝 x₀]
        (fun x : ℝ => |x - x₀| ^ (- (2 * N : ℤ))) := by
    -- First, pull back `hTheta_inv` along the inclusion `ℝ → ℂ`.
    have hO₁ :
        (fun x : ℝ => (‖f (x : ℂ)‖ ^ 2)⁻¹) =O[𝓝 x₀]
          (fun x : ℝ => ‖(x : ℂ) - (x₀ : ℂ)‖ ^ (- (2 * N : ℤ))) :=
      (hTheta_inv.isBigO).comp_tendsto (continuous_ofReal.tendsto x₀)
    have hO₂ :
        (fun x : ℝ => ‖(x : ℂ) - (x₀ : ℂ)‖ ^ (- (2 * N : ℤ))) =O[𝓝 x₀]
          (fun x : ℝ => (‖f (x : ℂ)‖ ^ 2)⁻¹) :=
      (hTheta_inv.isBigO_symm).comp_tendsto (continuous_ofReal.tendsto x₀)
    -- Rewrite using `f = E`.
    have hO₁' :
        (fun x : ℝ => (‖E x‖ ^ 2)⁻¹) =O[𝓝 x₀]
          (fun x : ℝ => ‖(x : ℂ) - (x₀ : ℂ)‖ ^ (- (2 * N : ℤ))) := by
      simpa [f] using hO₁
    have hO₂' :
        (fun x : ℝ => ‖(x : ℂ) - (x₀ : ℂ)‖ ^ (- (2 * N : ℤ))) =O[𝓝 x₀]
          (fun x : ℝ => (‖E x‖ ^ 2)⁻¹) := by
      simpa [f] using hO₂
    -- This gives Θ-asymptotics with the complex norm on the right-hand side.
    have hTheta_real' :
        (fun x : ℝ => (‖E x‖ ^ 2)⁻¹) =Θ[𝓝 x₀]
          (fun x : ℝ => ‖(x : ℂ) - (x₀ : ℂ)‖ ^ (- (2 * N : ℤ))) :=
      ⟨hO₁', hO₂'⟩
    -- Replace `‖(x:ℂ) - (x₀:ℂ)‖` with `|x - x₀|`.
    have h_eq_abs :
        (fun x : ℝ => ‖(x : ℂ) - (x₀ : ℂ)‖ ^ (- (2 * N : ℤ)))
          =ᶠ[𝓝 x₀] fun x : ℝ => |x - x₀| ^ (- (2 * N : ℤ)) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      have hbase : ‖(x : ℂ) - (x₀ : ℂ)‖ = ‖x - x₀‖ := by
        simpa [Complex.ofReal_sub] using (Complex.norm_real (x - x₀))
      simp [hbase, Real.norm_eq_abs]
    exact hTheta_real'.trans_eventuallyEq h_eq_abs

  -- Finally, rewrite the RHS in the requested Real form with exponent `-2 * (N : ℝ)`
  -- and take C = 1 > 0.
  refine ⟨N, ?_, 1, by norm_num, ?_⟩
  · -- the order condition comes directly from `isTheta_at_zero_order`
    intro hx0
    exact hNpos (by
      -- `f x₀ = 0` is the same as `E x₀ = 0`
      simpa using congrArg id hx0)
  · -- clean up the exponent and constant on reals
    -- `|x - x₀| ^ (- (2 * N : ℤ))` is (up to rewriting) exactly
    -- `1 * |x - x₀| ^ (-2 * (N : ℝ))`.
    -- Thus, by `IsTheta.isTheta_congr_right`, we get the desired form.
    have h_exp :
        (fun x : ℝ => |x - x₀| ^ (- (2 * N : ℤ))) =ᶠ[𝓝 x₀]
          fun x : ℝ => |x - x₀| ^ (-2 * (N : ℝ)) := by
      -- On `ℝ`, integer and real powers agree when the exponent is an integer.
      refine Filter.Eventually.of_forall ?_
      intro x
      have h_exponent :
          ((- (2 * N : ℤ)) : ℝ) = (-2 : ℝ) * (N : ℝ) := by
        -- Simplify the cast of `-(2 * N)` from `ℤ` to `ℝ`.
        -- The result is `-2 * (N : ℝ)`.
        simp [mul_comm]
      calc
        |x - x₀| ^ (- (2 * N : ℤ))
            = |x - x₀| ^ ((- (2 * N : ℤ)) : ℝ) := by
                simpa [Real.rpow_intCast] using
                  (Real.rpow_intCast (|x - x₀|) (- (2 * N : ℤ))).symm
        _ = |x - x₀| ^ (-2 * (N : ℝ)) := by
                simp
    -- combine
    -- first, rewrite the left-hand side of `hTheta_real` using `weight`
    have hTheta_real' :
        (fun x : ℝ => E.weight x) =Θ[𝓝 x₀]
          fun x : ℝ => |x - x₀| ^ (- (2 * N : ℤ)) := by
      simpa [DeBrangesFunction.weight] using hTheta_real
    -- then transport along the eventual equality on the right-hand side
    have hTheta_real'' :
        (fun x : ℝ => E.weight x) =Θ[𝓝 x₀]
          fun x : ℝ => |x - x₀| ^ (-2 * (N : ℝ)) :=
      hTheta_real'.trans_eventuallyEq h_exp
    -- finally, insert the trivial constant factor `1`
    simpa [DeBrangesFunction.weight, one_mul] using hTheta_real''

open Set

/--
**Theorem:** The de Branges measure `μ_E` is locally finite if and only if `E` has no real zeros,
assuming `E` is not identically zero.
-/
lemma locallyFiniteMeasure_iff_no_real_zeros (hE_not_zero : E.toFun ≠ 0) :
    IsLocallyFiniteMeasure E.measure ↔ ∀ x : ℝ, E x ≠ 0 := by
  constructor
  · -- (⇒) Locally finite ⇒ no real zeros.
    intro hLocFin
    -- Use the instance coming from the hypothesis.
    have _ : IsLocallyFiniteMeasure E.measure := hLocFin
    by_contra h_exists_zero
    push_neg at h_exists_zero
    rcases h_exists_zero with ⟨x₀, hx₀⟩
    -- Asymptotics of the weight near the real zero `x₀`.
    obtain ⟨N, hNpos, C, hCpos, hTheta_weight⟩ :=
      E.weight_asymptotics_near_real_point (x₀ := x₀) hE_not_zero
    have hN_ge1 : 1 ≤ N := hNpos hx₀

    -- From local finiteness of `E.measure`, pick an open neighbourhood `U` of `x₀`
    -- with finite measure.
    rcases (E.measure.exists_isOpen_measure_lt_top x₀) with
      ⟨U, hxU, hUopen, hμU_lt⟩
    have hU_mem : U ∈ 𝓝 x₀ := hUopen.mem_nhds hxU
    have hU_meas : MeasurableSet U := hUopen.measurableSet

    -- Express `E.measure U` as a lower Lebesgue integral of the density.
    have hμU_ne :
        (∫⁻ x in U, E.density x ∂(volume)) ≠ ⊤ := by
      have hμU_ne' : E.measure U ≠ ⊤ := hμU_lt.ne
      -- `withDensity_apply` identifies the measure of `U` with the integral of the density.
      simpa [DeBrangesFunction.measure, hU_meas] using hμU_ne'

    -- View this as an integral with respect to `volume.restrict U`.
    have hμU_ne_restrict :
        (∫⁻ x, E.density x ∂(volume.restrict U)) ≠ ⊤ := by
      -- By definition, `∫⁻ x in U, _ ∂volume` is the same as
      -- `∫⁻ x, _ ∂(volume.restrict U)`.
      simpa using hμU_ne

    -- Finite integral of the (non-negative) density gives finite integral
    -- of its `toReal`, i.e. of the real-valued weight.
    have hfi_density :
        HasFiniteIntegral (fun x => (E.density x).toReal) (volume.restrict U) :=
      hasFiniteIntegral_toReal_of_lintegral_ne_top hμU_ne_restrict

    -- The density is `ofReal (E.weight x)`, and `E.weight x ≥ 0` for all `x`.
    have hweight_nonneg (x : ℝ) : 0 ≤ E.weight x := by
      dsimp [DeBrangesFunction.weight]
      have : 0 ≤ ‖E x‖ ^ 2 := by
        have hnorm_nonneg : (0 : ℝ) ≤ ‖E x‖ := norm_nonneg _
        exact pow_two_nonneg _
      exact inv_nonneg.mpr this

    have hfi_weight :
        HasFiniteIntegral E.weight (volume.restrict U) := by
      -- Pointwise identification of `(E.density x).toReal` with `E.weight x`.
      have h_eq :
          (fun x => (E.density x).toReal) = E.weight := by
        funext x
        have hx : 0 ≤ E.weight x := hweight_nonneg x
        -- `density x = ofReal (weight x)`.
        simp [DeBrangesFunction.density, DeBrangesFunction.weight]
      simpa [h_eq] using hfi_density

    -- Hence the weight is integrable on `U` with respect to Lebesgue measure.
    have hInt_weight_U : IntegrableOn E.weight U volume := by
      -- `IntegrableOn` is just integrability with respect to `volume.restrict U`.
      have :
          Integrable E.weight (volume.restrict U) :=
        ⟨E.measurable_weight.aestronglyMeasurable, hfi_weight⟩
      simpa [IntegrableOn] using this

    -- So `E.weight` is integrable at the filter `𝓝 x₀`.
    have hIntAt_weight :
        IntegrableAtFilter E.weight (𝓝 x₀) volume :=
      ⟨U, hU_mem, hInt_weight_U⟩

    -- Let `g` be the model singularity `C * |x - x₀|^{-2N}`.
    let g : ℝ → ℝ := fun x =>
      C * |x - x₀| ^ (-2 * (N : ℝ))

    -- From `IsTheta`, we know `g =O[𝓝 x₀] E.weight`.
    have hBigO_g_weight :
        g =O[𝓝 x₀] (fun x : ℝ => E.weight x) :=
      (hTheta_weight.symm).isBigO

    -- Extract a neighbourhood on which we have the pointwise domination
    -- `‖g x‖ ≤ c * ‖E.weight x‖`.
    obtain ⟨c, hc_pos, hc_bound⟩ :=
        (Asymptotics.isBigO_iff' (f := g)
          (g := fun x : ℝ => E.weight x) (l := 𝓝 x₀)).1 hBigO_g_weight
    -- First get some `T₀ ∈ 𝓝 x₀` where the bound holds.
    obtain ⟨T₀, hT₀_mem, hT₀_forall⟩ :
        ∃ T ∈ 𝓝 x₀, ∀ x ∈ T, ‖g x‖ ≤ c * ‖E.weight x‖ :=
      Filter.Eventually.exists_mem hc_bound
    -- Shrink to an open neighbourhood `T ⊆ T₀` for measurability.
    rcases mem_nhds_iff.1 hT₀_mem with ⟨T, hT_subset, hT_open, hT_x₀⟩
    have hT_mem : T ∈ 𝓝 x₀ := hT_open.mem_nhds hT_x₀
    have hT_forall : ∀ x ∈ T, ‖g x‖ ≤ c * ‖E.weight x‖ := by
      intro x hxT
      exact hT₀_forall x (hT_subset hxT)

    -- Work on the intersection `S = U ∩ T`, which is still a neighbourhood of `x₀`.
    set S : Set ℝ := U ∩ T
    have hS_mem : S ∈ 𝓝 x₀ := inter_mem hU_mem hT_mem
    have hS_subset_U : S ⊆ U := inter_subset_left
    have hT_meas : MeasurableSet T := hT_open.measurableSet
    have hS_meas : MeasurableSet S := hU_meas.inter hT_meas

    -- `E.weight` is integrable on `S`.
    have hInt_weight_S : IntegrableOn E.weight S volume :=
      hInt_weight_U.mono_set hS_subset_U

    -- On `S`, we have the domination `‖g x‖ ≤ c * ‖E.weight x‖`.
    have hDom_S :
        ∀ᵐ x ∂(volume.restrict S),
          ‖g x‖ ≤ c * ‖E.weight x‖ := by
      -- Pointwise bound on `S`.
      have h_forall :
          ∀ x, x ∈ S → ‖g x‖ ≤ c * ‖E.weight x‖ := by
        intro x hxS
        exact hT_forall x hxS.2
      -- First, restrict the global statement with the implication `x ∈ S → …`.
      have hAE :
          ∀ᵐ x ∂(volume.restrict S),
            x ∈ S → ‖g x‖ ≤ c * ‖E.weight x‖ :=
        ae_restrict_of_ae (μ := volume) (Filter.Eventually.of_forall h_forall)
      -- Under `volume.restrict S`, we have `x ∈ S` almost everywhere.
      have hAE_mem :
          ∀ᵐ x ∂(volume.restrict S), x ∈ S :=
        ae_restrict_mem (μ := volume) (s := S) hS_meas
      -- Combine to drop the hypothesis `x ∈ S`.
      refine (hAE.and hAE_mem).mono ?_
      intro x hx
      exact hx.1 hx.2

    -- Integrability of the majorant `x ↦ c * E.weight x` on `S`.
    have hInt_major :
        Integrable (fun x => c * E.weight x) (volume.restrict S) := by
      have hInt_weight :
          Integrable E.weight (volume.restrict S) := by
        -- `IntegrableOn` over `S` is the same as integrability w.r.t. `volume.restrict S`.
        simpa [IntegrableOn] using hInt_weight_S
      -- Constant multiple of an integrable function is integrable.
      simpa using hInt_weight.const_mul c

    -- Hence `g` is integrable on `S` by comparison.
    have hInt_g_S :
        Integrable g (volume.restrict S) :=
      Integrable.mono'
        (hg := hInt_major)
        (hf := by
          -- `g` is measurable, hence a.e.-strongly measurable with respect to `volume.restrict S`.
          -- We obtain `AEStronglyMeasurable` via the equivalence with `AEMeasurable` on `ℝ`.
          have hg_meas : Measurable g := by
            -- `g x = C * |x - x₀| ^ (-2 * (N : ℝ))`
            fun_prop
          have hg_aemeas : AEMeasurable g (volume.restrict S) :=
            Measurable.aemeasurable hg_meas
          -- In a second countable Borel space like `ℝ`, `AEMeasurable` and `AEStronglyMeasurable`
          -- are equivalent.
          exact
            (aestronglyMeasurable_iff_aemeasurable
              (μ := volume.restrict S) (f := g)).2 hg_aemeas)
        (h := by
          -- Turn the domination on `S` into an a.e. inequality with a real-valued majorant.
          -- On `S`, we have `‖g x‖ ≤ c * ‖E.weight x‖` almost everywhere, and `E.weight x ≥ 0`,
          -- so `‖E.weight x‖ = E.weight x`.
          refine hDom_S.mono ?_
          intro x hx
          have hx0 : 0 ≤ E.weight x := hweight_nonneg x
          -- simplify the norm on `ℝ`
          simpa [Real.norm_eq_abs, abs_of_nonneg hx0] using hx)

    have hInt_g_S' : IntegrableOn g S volume := by
      simpa [IntegrableOn] using hInt_g_S

    -- Thus `g` is integrable at the filter `𝓝 x₀`.
    have hIntAt_g :
        IntegrableAtFilter g (𝓝 x₀) volume :=
      ⟨S, hS_mem, hInt_g_S'⟩

    -- Remove the harmless positive constant `C` from `g`.
    have hIntAt_model :
        IntegrableAtFilter
          (fun x : ℝ => |x - x₀| ^ (-2 * (N : ℝ)))
          (𝓝 x₀) volume := by
      -- On `S`, `g` is integrable, hence so is its constant multiple `C⁻¹ • g`.
      refine ⟨S, hS_mem, ?_⟩
      have hInt_Cinv_g :
          IntegrableOn (fun x : ℝ => C⁻¹ * g x) S volume := by
        -- View `IntegrableOn` over `S` as integrability w.r.t. `volume.restrict S`.
        have hgS : Integrable g (volume.restrict S) := by
          simpa [IntegrableOn] using hInt_g_S'
        have hCinv : Integrable (fun x : ℝ => C⁻¹ * g x) (volume.restrict S) :=
          hgS.const_mul C⁻¹
        simpa [IntegrableOn] using hCinv
      -- Rewrite `C⁻¹ * g` as the model function on `S`.
      have hC_ne : (C : ℝ) ≠ 0 := ne_of_gt hCpos
      have hEqOn :
          EqOn (fun x : ℝ => C⁻¹ * g x)
               (fun x : ℝ => |x - x₀| ^ (-2 * (N : ℝ))) S := by
        intro x hx
        dsimp [g]
        -- `C⁻¹ * (C * a) = a`
        have : C⁻¹ * (C * |x - x₀| ^ (-2 * (N : ℝ))) = |x - x₀| ^ (-2 * (N : ℝ)) := by
          have := inv_mul_cancel_left₀ hC_ne (|x - x₀| ^ (-2 * (N : ℝ)))
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        simpa [this]
      exact hInt_Cinv_g.congr_fun hEqOn hS_meas

    -- Apply the p-test: local integrability of `|x - x₀|^{-p}` forces `p < 1`.
    have h_exp_lt :
        2 * (N : ℝ) < 1 := by
      -- `integrableAtFilter_abs_sub_rpow_neg` is stated for exponent `-p`,
      -- so take `p := 2 * (N : ℝ)`.
      have h_lemm :=
        (integrableAtFilter_abs_sub_rpow_neg (x₀ := x₀) (p := 2 * (N : ℝ))).1
      -- Rewrite the model function into the required form.
      have h_exponent : (-2 : ℝ) * (N : ℝ) = -(2 * (N : ℝ)) := by ring
      have hIntAt_model' :
          IntegrableAtFilter
            (fun x : ℝ => |x - x₀| ^ (-(2 * (N : ℝ)))) (𝓝 x₀) volume := by
        simpa [h_exponent] using hIntAt_model
      -- Now apply the lemma.
      exact h_lemm hIntAt_model'

    -- But `N ≥ 1` contradicts `2 * (N : ℝ) < 1`.
    have h_ge : (2 : ℝ) ≤ 2 * (N : ℝ) := by
      have hN_ge1_real : (1 : ℝ) ≤ N := by
        exact_mod_cast hN_ge1
      have h2_pos : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
      -- Multiply the inequality `1 ≤ N` by `2`.
      have := mul_le_mul_of_nonneg_left hN_ge1_real h2_pos
      simpa [two_mul, one_mul] using this
    -- From `2 ≤ 2N < 1` we get `2 < 1`, impossible.
    have : (2 : ℝ) < 1 := lt_of_le_of_lt h_ge h_exp_lt
    linarith
  · -- (⇐) No real zeros ⇒ locally finite.
    intro hNoZeros
    -- If no real zeros, `(‖E x‖^2)⁻¹` is continuous on `ℝ` and hence defines a locally finite
    -- with-density measure.
    have continuous_weight : Continuous E.weight := by
      dsimp [weight]
      have cont_E_R : Continuous (fun x : ℝ => E x) :=
        E.continuous.comp continuous_ofReal
      have cont_sq : Continuous (fun x : ℝ => ‖E x‖ ^ 2) :=
        (continuous_norm.comp cont_E_R).pow 2
      exact cont_sq.inv₀ (by
        intro x
        have hx : E x ≠ 0 := hNoZeros x
        have hpos : 0 < ‖E x‖ := norm_pos_iff.mpr hx
        exact ne_of_gt (pow_pos hpos 2))
    exact MeasureTheory.IsLocallyFiniteMeasure.withDensity_ofReal continuous_weight


/-- Convenience version of `locallyFiniteMeasure_iff_no_real_zeros` that does not
require an explicit `E ≠ 0` hypothesis, since a de Branges function is never
identically zero. -/
lemma locallyFiniteMeasure_iff_no_real_zeros'
    (E : DeBrangesFunction) :
    IsLocallyFiniteMeasure E.measure ↔ ∀ x : ℝ, E x ≠ 0 :=
  locallyFiniteMeasure_iff_no_real_zeros
    (E := E) (hE_not_zero := DeBrangesFunction.not_identically_zero E)

end DeBrangesFunction

/-! ### 4. Bridge lemmas for `HermiteBiehlerFunction` -/

namespace HermiteBiehlerFunction

variable (E : HermiteBiehlerFunction)

/-- On the real line, the de Branges weight attached to a Hermite–Biehler
function agrees with the de Branges weight of its underlying
`DeBrangesFunction`. -/
lemma weight_eq_deBranges_weight (x : ℝ) :
    E.weight x = DeBrangesFunction.weight E.toDeBrangesFunction x := by
  -- Both sides are definitionally `(‖E x‖ ^ 2)⁻¹`.
  rfl

/-- On the real line, the `ENNReal`-valued de Branges density attached to a
Hermite–Biehler function agrees with the density of its underlying
`DeBrangesFunction`. -/
lemma density_eq_deBranges_density (x : ℝ) :
    E.density x = DeBrangesFunction.density E.toDeBrangesFunction x := by
  -- Both sides are `ENNReal.ofReal` of the corresponding weights.
  rfl

/-- The de Branges measure attached to a Hermite–Biehler function agrees with
the de Branges measure of its underlying `DeBrangesFunction`. -/
lemma measure_eq_deBranges_measure :
    E.measure = DeBrangesFunction.measure E.toDeBrangesFunction := by
  -- The two measures are `withDensity` of equal densities.
  -- We prove equality by extensionality on measurable sets.
  ext s hs
  simp [HermiteBiehlerFunction.measure, DeBrangesFunction.measure]
  aesop

/-- Specialization of `DeBrangesFunction.locallyFiniteMeasure_iff_no_real_zeros`
to Hermite–Biehler functions, using the bridge lemmas above. -/
lemma locallyFiniteMeasure_iff_no_real_zeros_hermite :
    IsLocallyFiniteMeasure E.measure ↔ ∀ x : ℝ, E x ≠ 0 := by
  -- Work with the underlying de Branges function.
  have h :=
    DeBrangesFunction.locallyFiniteMeasure_iff_no_real_zeros'
      (E := E.toDeBrangesFunction)
  -- Rewrite the left-hand side using the measure bridge lemma.
  have h_left :
      IsLocallyFiniteMeasure E.measure ↔
        IsLocallyFiniteMeasure (DeBrangesFunction.measure E.toDeBrangesFunction) := by
    constructor <;> intro hμ
    · simpa [measure_eq_deBranges_measure E] using hμ
    · simpa [measure_eq_deBranges_measure E] using hμ
  -- Rewrite the right-hand side using the definitional equality `E x = _`.
  have h_right :
      (∀ x : ℝ, E.toDeBrangesFunction x ≠ 0) ↔ ∀ x : ℝ, E x ≠ 0 := by
    constructor
    · intro h x; simpa using h x
    · intro h x; simpa using h x
  -- Combine the equivalence with the two rewrites.
  exact (h_left.trans h).trans h_right

end HermiteBiehlerFunction

/-
I'll address both parts of your question about mathlib4's treatment of these topics.

## Order of Zeros and Factorization for Analytic Functions

Mathlib4 defines the **order of vanishing** (order of zeros) in `Mathlib/Analysis/Analytic/Order.lean` through the function `analyticOrderAt`, which returns the unique `n : ℕ⊤` such that an analytic function can be factored as `f(z) = (z - z₀)^n • g(z)` where `g` is analytic and non-vanishing at `z₀`. [1](#3-0)

The key characterization theorem states that `analyticOrderAt f z₀ = n` if and only if there exists an analytic function `g` with `g(z₀) ≠ 0` such that `f z = (z - z₀) ^ n • g z` holds eventually near `z₀`: [2](#3-1)

The existence and uniqueness of this factorization is established through the principle of isolated zeros. The foundational theorem shows that for analytic functions, either the function vanishes identically in a neighborhood or the factorization exists with a unique order: [3](#3-2)

The uniqueness of the order in the factorization is proven in: [4](#3-3)

## Asymptotic Behavior with Theta Notation

While mathlib4 defines the `IsTheta` relation (written `f =Θ[l] g`) in `Mathlib/Analysis/Asymptotics/Theta.lean`: [5](#3-4)

**However**, I did not find an explicit theorem in mathlib4 that directly connects `analyticOrderAt f z₀ = N` to the asymptotic statement `f =Θ[𝓝 z₀] (fun z => (z - z₀) ^ N)`. The factorization theorem provides the multiplicative structure `f z = (z - z₀) ^ n • g z` with `g z₀ ≠ 0`, which conceptually implies the asymptotic equivalence, but this specific connection appears not to be formally stated in the current codebase.

## Local Integrability of Power Singularities

For the integrability condition of `|x - x₀|^(-p)`, mathlib4 does not have a theorem exactly in the form you stated. However, it contains the fundamental building block:

The key theorem `integrableOn_Ioo_rpow_iff` shows that `x^s` is integrable on `(0, t)` if and only if `-1 < s`: [6](#3-5)

For a function of the form `|x - x₀|^(-p)`, after a change of variables `y = x - x₀`, the integrability near `x₀` reduces to checking integrability of `|y|^(-p)` near `0`. With exponent `s = -p`, the condition `-1 < s` becomes `-1 < -p`, which is equivalent to `p < 1`.

The corresponding result for interval integrability is: [7](#3-6)

## Notes

- The factorization theory for analytic functions is fully developed with complete proofs of existence, uniqueness, and characterizations.
- The asymptotic Theta notation exists but the explicit connection to analytic order may need to be established if required for specific applications.
- For local integrability of power singularities, the fundamental integrability criterion exists, though the specific equivalence statement for `LocallyIntegrable` on all of `ℝ` with the exact form you mentioned may not be explicitly stated. The integrability near the singularity is what determines local integrability, and this is controlled by the condition `p < 1`.

### Citations

**File:** Mathlib/Analysis/Analytic/Order.lean (L32-44)
```text
/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ⊤`.

The order is defined to be `⊤` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `AnalyticAt.analyticOrderAt_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

If `f` isn't analytic at `z₀`, then `analyticOrderAt f z₀` returns a junk value of `0`. -/
noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ⊤ :=
  if hf : AnalyticAt 𝕜 f z₀ then
    if h : ∀ᶠ z in 𝓝 z₀, f z = 0 then ⊤
    else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
  else 0
```

**File:** Mathlib/Analysis/Analytic/Order.lean (L78-90)
```text
lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = n ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  split_ifs with h
  · simp only [ENat.top_ne_coe, false_iff]
    contrapose! h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn ↦ (WithTop.coe_inj.mp hn : h.choose = n) ▸ h.choose_spec, fun h' ↦ ?_⟩
    rw [AnalyticAt.unique_eventuallyEq_pow_smul_nonzero h.choose_spec h']

```

**File:** Mathlib/Analysis/Analytic/IsolatedZeros.lean (L174-181)
```text
lemma unique_eventuallyEq_pow_smul_nonzero {m n : ℕ}
    (hm : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m • g z)
    (hn : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z) :
    m = n := by
  simp_rw [← zpow_natCast] at hm hn
  exact Int.ofNat_inj.mp <| unique_eventuallyEq_zpow_smul_nonzero
    (let ⟨g, h₁, h₂, h₃⟩ := hm; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)
    (let ⟨g, h₁, h₂, h₃⟩ := hn; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)
```

**File:** Mathlib/Analysis/Analytic/IsolatedZeros.lean (L186-203)
```text
theorem exists_eventuallyEq_pow_smul_nonzero_iff (hf : AnalyticAt 𝕜 f z₀) :
    (∃ (n : ℕ), ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z) ↔ (¬∀ᶠ z in 𝓝 z₀, f z = 0) := by
  constructor
  · rintro ⟨n, g, hg_an, hg_ne, hg_eq⟩
    contrapose! hg_ne
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq, ← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    refine (eventually_nhdsWithin_iff.mpr ?_).frequently
    filter_upwards [hg_eq, hg_ne] with z hf_eq hf0 hz
    rwa [hf0, eq_comm, smul_eq_zero_iff_right] at hf_eq
    exact pow_ne_zero _ (sub_ne_zero.mpr hz)
  · intro hf_ne
    rcases hf with ⟨p, hp⟩
    exact ⟨p.order, _, ⟨_, hp.has_fpower_series_iterate_dslope_fslope p.order⟩,
      hp.iterate_dslope_fslope_ne_zero (hf_ne.imp hp.locally_zero_iff.mpr),
      hp.eq_pow_order_mul_iterate_dslope⟩

```

**File:** Mathlib/Analysis/Asymptotics/Theta.lean (L39-45)
```text
/-- We say that `f` is `Θ(g)` along a filter `l` (notation: `f =Θ[l] g`) if `f =O[l] g` and
`g =O[l] f`. -/
def IsTheta (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  IsBigO l f g ∧ IsBigO l g f

@[inherit_doc]
notation:100 f " =Θ[" l "] " g:100 => IsTheta l f g
```

**File:** Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean (L40-62)
```text
theorem intervalIntegrable_rpow' {r : ℝ} (h : -1 < r) :
    IntervalIntegrable (fun x => x ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff, uIoc_of_le hc]
    have hderiv : ∀ x ∈ Ioo 0 c, HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
      intro x hx
      convert (Real.hasDerivAt_rpow_const (p := r + 1) (Or.inl hx.1.ne')).div_const (r + 1) using 1
      simp [(by linarith : r + 1 ≠ 0)]
    apply integrableOn_deriv_of_nonneg _ hderiv
    · intro x hx; apply rpow_nonneg hx.1.le
    · refine (continuousOn_id.rpow_const ?_).div_const _; intro x _; right; linarith
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).smul (cos (r * π))
    rw [intervalIntegrable_iff] at m ⊢
    refine m.congr_fun ?_ measurableSet_Ioc; intro x hx
    rw [uIoc_of_le (by linarith : 0 ≤ -c)] at hx
    simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, log_neg_eq_log, mul_comm,
      rpow_def_of_pos hx.1, rpow_def_of_neg (by linarith [hx.1] : -x < 0)]
```

**File:** Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean (L64-84)
```text
/-- The power function `x ↦ x^s` is integrable on `(0, t)` iff `-1 < s`. -/
lemma integrableOn_Ioo_rpow_iff {s t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ x ^ s) (Ioo (0 : ℝ) t) ↔ -1 < s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  swap
  · rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]
    apply intervalIntegrable_rpow' h (a := 0) (b := t)
  contrapose! h
  intro H
  have I : 0 < min 1 t := lt_min zero_lt_one ht
  have H' : IntegrableOn (fun x ↦ x ^ s) (Ioo 0 (min 1 t)) :=
    H.mono (Set.Ioo_subset_Ioo le_rfl (min_le_right _ _)) le_rfl
  have : IntegrableOn (fun x ↦ x⁻¹) (Ioo 0 (min 1 t)) := by
    apply H'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hx.1)]
    rwa [← Real.rpow_neg_one x, Real.rpow_le_rpow_left_iff_of_base_lt_one hx.1]
    exact lt_of_lt_of_le hx.2 (min_le_left _ _)
  have : IntervalIntegrable (fun x ↦ x⁻¹) volume 0 (min 1 t) := by
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le I.le]
  simp [intervalIntegrable_inv_iff, I.ne] at this
```

-/
