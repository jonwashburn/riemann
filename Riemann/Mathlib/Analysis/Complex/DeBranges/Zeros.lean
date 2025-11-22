import Riemann.Mathlib.Analysis.Complex.DeBranges.Basic
import Mathlib
import PrimeNumberTheoremAnd
import StrongPNT

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
    hf_analyticOn z₀ (by simpa)

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

/--
Asymptotic behavior near a zero. If `f(z₀)=0`, then `f(z) = Θ((z-z₀)^N)` for `N ≥ 1`.
-/
lemma isTheta_at_zero_order {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf_ne : f ≠ 0) (z₀ : ℂ) :
    ∃ (N : ℕ), (f z₀ = 0 → N ≥ 1) ∧
    f =Θ[𝓝 z₀] (fun z => (z - z₀) ^ N) := by
  sorry

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
  -- implement the interval splitting + translation as above
  sorry

lemma locallyIntegrable_abs_sub_rpow_neg (x₀ : ℝ) (p : ℝ) :
    LocallyIntegrable (fun x : ℝ => |x - x₀| ^ (-p)) volume ↔ p < 1 := by
  -- Using LocallyIntegrable definition directly:
  constructor
  · intro h
    -- specialize at `x := x₀`
    have hx := h x₀
    -- apply the local p-test
    exact (integrableAtFilter_abs_sub_rpow_neg x₀ p).1 hx
  · intro hp
    -- need `IntegrableAtFilter` for every `x`
    intro x
    by_cases hx : x = x₀
    · subst hx
      -- Now `x = x₀`, so we can reuse the `x₀`-case of the local p-test.
      simpa using (integrableAtFilter_abs_sub_rpow_neg x p).2 hp
    · -- `x ≠ x₀`: choose a small ball away from `x₀` and bound the function
      -- to show integrable there (standard bounded-on-compact argument)
      sorry

/-- Local integrability of `|x - x₀|^{-p}` near `x₀` is controlled by the same
exponent condition `p < 1`. This is the core analytic input; the full
`LocallyIntegrable` statement will add the (easy) translation and compactness
arguments on top of this lemma. -/
lemma locallyIntegrable_abs_sub_rpow_neg' (x₀ : ℝ) (p : ℝ) :
    LocallyIntegrable (fun x : ℝ => |x - x₀| ^ (-p)) volume ↔ p < 1 := by
  -- Sketch of the full proof (to be filled in subsequent iterations):
  -- 1. By translation invariance of Lebesgue measure, reduce the problem to `x₀ = 0`,
  --    i.e. to `LocallyIntegrable (fun x => |x| ^ (-p)) volume`.
  -- 2. Using the definition of `LocallyIntegrable` and sigma-compactness of `ℝ`,
  --    show that for this specific function, local integrability is equivalent
  --    to integrability on some (equivalently, every) small symmetric interval
  --    around `0`, e.g. `IntegrableOn (fun x => |x| ^ (-p)) (Ioo (0 : ℝ) 1)`.
  -- 3. Apply `integrableOn_Ioo_abs_rpow_neg_iff` to identify this with `p < 1`.
  --
  -- We leave the topological/measure-theoretic glue (steps 1–2) to a later pass.
  sorry

end MeasureTheory

namespace DeBrangesFunction

variable (E : DeBrangesFunction)

/-! ### 3. Application to de Branges functions -/

/-- The de Branges weight `w_E(x) = ‖E x‖⁻²` on `ℝ` for a (possibly) real-zero function. -/
noncomputable def weight (x : ℝ) : ℝ :=
  (‖E x‖ ^ 2)⁻¹

/-- The corresponding `ENNReal`-valued density. -/
noncomputable def density (x : ℝ) : ENNReal :=
  ENNReal.ofReal (E.weight x)

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
  -- Uses factorization of an entire function at a zero and Theta-asymptotics.
  -- To be filled using `AnalyticAt.analyticOrderAt_eq_natCast` and `IsTheta` API.
  sorry

/--
**Theorem:** The de Branges measure `μ_E` is locally finite if and only if `E` has no real zeros,
assuming `E` is not identically zero.
-/
lemma locallyFiniteMeasure_iff_no_real_zeros (hE_not_zero : E.toFun ≠ 0) :
    IsLocallyFiniteMeasure E.measure ↔ ∀ x : ℝ, E x ≠ 0 := by
  constructor
  · -- (⇒) Locally finite ⇒ no real zeros.
    intro hLocFin
    by_contra h_exists_zero
    push_neg at h_exists_zero
    rcases h_exists_zero with ⟨x₀, hx₀⟩
    -- From `weight_asymptotics_near_real_point`, near `x₀` the weight looks like
    -- `C * |x - x₀|^{-2N}` with `N ≥ 1`, which is not locally integrable by the p-test.
    -- This contradicts local finiteness of `E.measure`.
    sorry
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

/-
I'll address both parts of your question about mathlib4's treatment of these topics.

## Order of Zeros and Factorization for Analytic Functions

Mathlib4 defines the **order of vanishing** (order of zeros) in `Mathlib/Analysis/Analytic/Order.lean` through the function `analyticOrderAt`, which returns the unique `n : ℕ∞` such that an analytic function can be factored as `f(z) = (z - z₀)^n • g(z)` where `g` is analytic and non-vanishing at `z₀`. [1](#3-0)

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
/-- The order of vanishing of `f` at `z₀`, as an element of `ℕ∞`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `AnalyticAt.analyticOrderAt_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

If `f` isn't analytic at `z₀`, then `analyticOrderAt f z₀` returns a junk value of `0`. -/
noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ∞ :=
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
end DeBrangesFunction
