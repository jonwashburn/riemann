import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Parameter-Dependent Poisson Kernel Integrals

This file establishes continuity and measurability results for parameter-dependent
integrals involving Poisson kernels.

## Main definitions

* `PoissonParam.P` - The Poisson kernel σ/(y² + σ²)
* `PoissonParam.V` - Finite Poisson sum V(σ,t) = Σ P(σ, t-γ)
* `PoissonParam.Φ` - Square of the Poisson sum (V(σ,t))²

## Main results

* `continuousOn_integral_sq_poisson_Icc` - Continuity of σ ↦ ∫ (V σ t)² dt on [ε, σmax]
* `aestronglyMeasurable_integral_sq_poisson_Ioc` - Measurability on (0, σmax]

## Implementation notes

We use dominated convergence to establish continuity in the parameter σ.
The dominating function is the constant ((#Zk)/ε)² which is integrable on
bounded measurable sets.

-/

open MeasureTheory Real

open Real MeasureTheory Filter Topology


namespace ParameterIntegral

open MeasureTheory TopologicalSpace

/-- Continuity of parameter-dependent integrals (dominated convergence). -/
theorem continuousOn_integral_of_dominated
    {α β E : Type*} [MeasurableSpace α] [TopologicalSpace β] [FirstCountableTopology β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E]
    (f : α → β → E) (μ : Measure α) (S : Set β)
    (h_meas : ∀ b ∈ S, AEStronglyMeasurable (fun a => f a b) μ)
    (h_cont : ∀ a, ContinuousOn (f a) S)
    (g : α → ℝ) (hg : Integrable g μ)
    (h_bound : ∀ b ∈ S, ∀ᵐ a ∂μ, ‖f a b‖ ≤ g a) :
    ContinuousOn (fun b => ∫ a, f a b ∂μ) S := by
  apply continuousOn_of_dominated
  · intro b hb; exact h_meas b hb
  · intro b hb; exact h_bound b hb
  · exact hg
  ·
    have h_cont_ae : ∀ᵐ a ∂μ, ContinuousOn (fun b => f a b) S :=
      Filter.Eventually.of_forall h_cont
    simpa using h_cont_ae

/-!
# Parameter measurability and continuity for Poisson kernel integrals

Fix a finite set of shifts `Zk : Finset ℝ` and a measurable set `I ⊆ ℝ`.
For `σ > 0`, consider the Poisson kernel
`P σ y := σ / (y^2 + σ^2)` and the finite sum
`V σ t := ∑ γ ∈ Zk, P σ (t - γ)`. We prove:

* For any `0 < ε ≤ σ_max`, the map
  `σ ↦ ∫ t in I, (V σ t)^2` is `ContinuousOn` on `[ε, σ_max]`
  provided `I` is measurable and bounded.

* As a corollary, this map is a.e. strongly measurable on `(0, σ_max)`
  with respect to the restricted Lebesgue measure.

We rely on mathlib's `continuousOn_of_dominated` lemma for parametric
integrals: continuity in the parameter follows from a uniform L¹ dominator
on the parameter set together with a.e. continuity in the parameter and
measurability in the space variable.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Set

namespace PoissonParam

/-- Poisson kernel `σ/(y^2+σ^2)` (with the usual normalization for the real line). -/
@[simp] def P (σ y : ℝ) : ℝ := σ / (y^2 + σ^2)

/-- Finite Poisson sum `V σ t = ∑_{γ∈Zk} P σ (t - γ)`. -/
@[simp] def V (Zk : Finset ℝ) (σ t : ℝ) : ℝ :=
  ∑ γ ∈ Zk, P σ (t - γ)

/-- Square of the finite Poisson sum (the integrand we care about). -/
@[simp] def Φ (Zk : Finset ℝ) (σ t : ℝ) : ℝ := (V Zk σ t)^2

/-- Basic continuity in `t` for fixed `σ`: `t ↦ Φ Zk σ t` is continuous. -/
lemma continuous_in_t (Zk : Finset ℝ) (σ : ℝ) (hσ : σ ≠ 0) :
    Continuous (fun t : ℝ => Φ Zk σ t) := by
  -- each summand `t ↦ P σ (t - γ)` is continuous (denominator never vanishes)
  have h_each : ∀ γ ∈ Zk, Continuous (fun t : ℝ => P σ (t - γ)) := by
    intro γ _; dsimp [P]
    have hden : Continuous fun t : ℝ => (t - γ)^2 + σ^2 := by continuity
    -- denominator is ≥ σ^2 > 0, so never zero
    have hden_ne : ∀ t, (t - γ)^2 + σ^2 ≠ 0 := by
      intro t
      have hσ2pos : 0 < σ^2 := by simpa using (sq_pos_iff.mpr hσ)
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hσ2pos)
    simpa using (continuous_const.div hden hden_ne)
  -- sum of continuous functions is continuous; then square
  have hsum : Continuous (fun t : ℝ => V Zk σ t) := continuous_finset_sum Zk h_each
  simp only [Φ]
  exact hsum.pow 2

/-- Continuity in `σ` on a compact range `[ε, σ_max]` for fixed `t`. -/
lemma continuousOn_in_sigma_on_Icc
    (Zk : Finset ℝ) {ε σmax : ℝ} (hε : 0 < ε) (_ : ε ≤ σmax) (t : ℝ) :
    ContinuousOn (fun σ : ℝ => Φ Zk σ t) (Icc ε σmax) := by
  -- Each summand `σ ↦ P σ (t - γ)` is continuous on `Icc ε σmax`
  have h_each : ∀ γ ∈ Zk, ContinuousOn (fun σ : ℝ => P σ (t - γ)) (Icc ε σmax) := by
    intro γ _; dsimp [P]
    -- continuity of numerator and denominator
    have hnum : ContinuousOn (fun σ : ℝ => σ) (Icc ε σmax) :=
      (continuous_id.continuousOn)
    have hden : ContinuousOn (fun σ : ℝ => (t - γ)^2 + σ^2) (Icc ε σmax) := by
      have : Continuous fun σ : ℝ => (t - γ)^2 + σ^2 := by continuity
      exact this.continuousOn
    -- denominator never vanishes on `[ε, σmax]` since `σ ≥ ε > 0`
    have hpos : ∀ σ ∈ Icc ε σmax, (t - γ)^2 + σ^2 ≠ 0 := by
      intro σ hσ
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (lt_of_lt_of_le hε hσ.1)))
    simpa using hnum.div hden hpos
  -- Sum of `ContinuousOn` functions is `ContinuousOn`; then square
  have hsum : ContinuousOn (fun σ : ℝ => V Zk σ t) (Icc ε σmax) :=
    continuousOn_finset_sum Zk h_each
  -- squaring preserves `ContinuousOn`
  have : ContinuousOn (fun σ : ℝ => (V Zk σ t)^2) (Icc ε σmax) :=
    hsum.pow 2
  simpa only [Φ] using this


/-- **Uniform L¹ domination on `[ε, σ_max]`** over a bounded measurable set `I`.

For `σ ∈ [ε, σ_max]`, all summands are ≤ `1/ε`, hence the square of the sum
is bounded by `((Zk.card : ℝ) / ε)^2`. This constant is integrable on
`volume.restrict I` because `I` is bounded and measurable. -/
lemma L1_dominator_const
    (Zk : Finset ℝ) {ε σmax : ℝ} (hε : 0 < ε) (_ : ε ≤ σmax)
    (I : Set ℝ) (hI : MeasurableSet I) (hI_bdd : Bornology.IsBounded I) :
    ∃ C > 0,
      Integrable (fun _ : ℝ => (C : ℝ)) (volume.restrict I)
      ∧ ∀ σ ∈ Icc ε σmax, ∀ᵐ t ∂(volume.restrict I),
           ‖Φ Zk σ t‖ ≤ C := by
  classical
  -- Finite measure of `I` from boundedness
  obtain ⟨R, hR⟩ : ∃ R ≥ (0 : ℝ), I ⊆ Metric.closedBall (0 : ℝ) R := by
    rcases hI_bdd.subset_closedBall (0 : ℝ) with ⟨R, hsub⟩
    exact ⟨max R 0, le_max_right _ _, by
      intro x hx
      have hx' := hsub hx
      -- `closedBall 0 R ⊆ closedBall 0 (max R 0)`
      exact (Metric.closedBall_subset_closedBall (le_max_left _ _)) hx'⟩
  have hμI_lt_top : (volume I) < ⊤ := by
    -- `closedBall 0 R` has finite measure in `ℝ`; use monotonicity
    have hsubset : I ⊆ Set.Icc (-R) R := by
      intro x hx
      have hx' : x ∈ Metric.closedBall (0 : ℝ) R := hR.2 hx
      -- closedBall in ℝ is `Icc (-R) R`
      have : Metric.closedBall (0 : ℝ) R = Set.Icc (-R) R := by
        ext x; simp [Metric.mem_closedBall, Real.norm_eq_abs, abs_le]
      simpa [this] using hx'
    have hvol : volume (Set.Icc (-R) R) < ⊤ := by
      -- Explicit finite volume for intervals on `ℝ`
      simp [Real.volume_Icc]
    exact (lt_of_le_of_lt (measure_mono hsubset) hvol)
  -- constant dominator
  let C : ℝ := max 1 (((Zk.card : ℝ) / ε)^2)
  have hCpos : 0 < C := by
    simp only [C]
    exact lt_max_iff.mpr (Or.inl one_pos)
  have hint_const : Integrable (fun _ : ℝ => (C : ℝ)) (volume.restrict I) := by
    -- integrability of a positive constant on a finite-measure set
    have : (volume.restrict I) Set.univ = volume I := by
      simp [Measure.restrict_apply]
    -- Use `integrable_const` with finiteness of measure
    have h_fin : (volume.restrict I) Set.univ < ⊤ := by simpa [this] using hμI_lt_top
    have : IsFiniteMeasure (volume.restrict I) := by
      constructor
      simpa [Measure.restrict_apply, hI] using hμI_lt_top
    simp [C]
  refine ⟨C, hCpos, hint_const, ?_⟩
  intro σ hσ
  -- pointwise bound: `P σ (t-γ) ≤ 1/σ ≤ 1/ε`, hence the sum ≤ `card * (1/ε)`, then square
  have hσpos : 0 < σ := lt_of_lt_of_le hε (show ε ≤ σ from hσ.1)
  have h_le_one_div_eps :
      ∀ t γ, P σ (t - γ) ≤ 1 / ε := by
    intro t γ
    have h1 : P σ (t - γ) ≤ 1 / σ := by
      -- multiply inequality by positive `((t - γ)^2 + σ^2) * σ`
      -- equivalently show `σ^2 ≤ (t - γ)^2 + σ^2`
      have : σ^2 ≤ (t - γ)^2 + σ^2 := by
        have : 0 ≤ (t - γ)^2 := sq_nonneg _
        linarith
      -- `σ / A ≤ 1/σ` iff `σ^2 ≤ A`
      have : σ / ((t - γ)^2 + σ^2) ≤ σ / (σ^2) :=
        div_le_div_of_nonneg_left (le_of_lt hσpos) (sq_pos_of_pos hσpos) (by linarith)
      calc P σ (t - γ)
        _ = σ / ((t - γ)^2 + σ^2) := rfl
        _ ≤ σ / (σ^2) := this
        _ = 1 / σ := by field_simp
    have : (1 / σ) ≤ (1 / ε) :=
      (one_div_le_one_div_of_le hε (show ε ≤ σ from hσ.1))
    exact le_trans h1 this
  -- bound a.e. (actually for all t)
  refine ((ae_restrict_iff' hI).2 ?_ : ∀ᵐ t ∂(volume.restrict I), ‖Φ Zk σ t‖ ≤ C)
  refine Filter.Eventually.of_forall ?_
  intro t
  have hsum_le : V Zk σ t ≤ (Zk.card : ℝ) * (1/ε) := by
    classical
    have : ∀ γ ∈ Zk, P σ (t - γ) ≤ 1 / ε := by
      intro γ _; exact h_le_one_div_eps t γ
    have hs := Finset.sum_le_sum this
    simpa [V, Finset.sum_const, nsmul_eq_mul] using hs
  have hsum_nonneg : 0 ≤ V Zk σ t := by
    -- all summands are ≥ 0
    have : ∀ γ ∈ Zk, 0 ≤ P σ (t - γ) := by
      intro γ _
      dsimp [P]
      apply div_nonneg
      · exact hσpos.le
      · positivity
    simpa [V] using (Finset.sum_nonneg this)
  have : (V Zk σ t)^2 ≤ ((Zk.card : ℝ) * (1/ε))^2 :=
    pow_le_pow_left₀ hsum_nonneg hsum_le 2
  intro _
  -- turn into a norm inequality and rewrite `C`
  calc ‖Φ Zk σ t‖
    _ = |(V Zk σ t)^2| := by simp [Φ, Real.norm_eq_abs]
    _ = (V Zk σ t)^2 := abs_of_nonneg (sq_nonneg _)
    _ ≤ ((Zk.card : ℝ) * (1/ε))^2 := this
    _ ≤ C := by simp [C, one_div]; aesop

/-- **Continuity on compact σ‑ranges** away from 0.

If `I` is measurable and bounded, then for every `0 < ε ≤ σ_max` the function
`σ ↦ ∫ t in I, (∑ γ∈Zk, σ / ((t - γ)^2 + σ^2))^2` is continuous on `Icc ε σ_max`. -/
theorem continuousOn_integral_sq_poisson_Icc
    (Zk : Finset ℝ) (I : Set ℝ) (hI : MeasurableSet I) (hI_bdd : Bornology.IsBounded I)
    {ε σmax : ℝ} (hε : 0 < ε) (hεσ : ε ≤ σmax) :
    ContinuousOn
      (fun σ => ∫ t in I, (Φ Zk σ t)) (Icc ε σmax) := by
  -- Apply `continuousOn_of_dominated`
  set μ := (volume.restrict I)
  -- (1) measurability in `t` for each `σ`:
  have h_meas : ∀ σ ∈ Icc ε σmax, AEStronglyMeasurable (fun t => Φ Zk σ t) μ := by
    intro σ hσ
    have hσne : σ ≠ 0 := (lt_of_lt_of_le hε hσ.1).ne'
    exact (continuous_in_t Zk σ hσne).aestronglyMeasurable
  -- (2) a.e. continuity in `σ` on the parameter set:
  have h_cont_ae : ∀ᵐ t ∂μ, ContinuousOn (fun σ => Φ Zk σ t) (Icc ε σmax) := by
    -- We in fact have pointwise continuity, hence certainly a.e.
    apply Filter.Eventually.of_forall
    intro t
    exact continuousOn_in_sigma_on_Icc Zk hε hεσ t
  -- (3) existence of a uniform L¹ dominator on the parameter set:
  rcases L1_dominator_const Zk hε hεσ I hI hI_bdd with ⟨C, _, hintC, hbound⟩
  -- Conclude by the parametric dominated-continuity lemma
  apply continuousOn_of_dominated (F := fun σ t => Φ Zk σ t) (bound := fun _ => C)
  · -- measurability in `t` for each `σ ∈ S`
    exact h_meas
  · -- domination `‖f t σ‖ ≤ g t` a.e. in `t` for each `σ ∈ S`
    exact hbound
  · -- integrability of the dominator
    exact hintC
  · -- a.e. continuity in σ
    exact h_cont_ae

/-- **A.e. strong measurability on `(0, σ_max)` under restriction.**

From the previous continuity on compacts away from `0`,
we deduce a.e. strong measurability for the restricted measure on `Ioc 0 σ_max`. -/
theorem aestronglyMeasurable_integral_sq_poisson_Ioc
    (Zk : Finset ℝ) (I : Set ℝ) (hI : MeasurableSet I) (hI_bdd : Bornology.IsBounded I)
    {σmax : ℝ} (_ : 0 < σmax) :
    AEStronglyMeasurable
      (fun σ => ∫ t in I, (Φ Zk σ t))
      (volume.restrict (Ioc (0 : ℝ) σmax)) := by
  classical
  -- cover `(0, σmax)` by the increasing union of compacts `[1/(n+1), σmax]`
  have hcov :
      (Ioc (0 : ℝ) σmax) = ⋃ n : ℕ, Icc ((1 : ℝ) / (n + 1)) σmax := by
    ext σ; constructor
    · intro hσ
      rcases hσ with ⟨h0, hle⟩
      -- choose `n` with `1/(n+1) < σ`
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 : ℝ) / (n + 1) < σ := by
        -- standard archimedean argument
        have : 0 < σ := h0
        rcases exists_nat_one_div_lt this with ⟨n, hn⟩
        exact ⟨n, hn.trans_le le_rfl⟩
      refine mem_iUnion.2 ⟨n, ?_⟩
      exact ⟨le_of_lt hn, hle⟩
    · intro hσ
      rcases mem_iUnion.1 hσ with ⟨n, hn⟩
      have pos : 0 < (1 : ℝ) / (n + 1) := one_div_pos.mpr (Nat.cast_add_one_pos n)
      exact ⟨pos.trans_le hn.1, hn.2⟩
  -- on each compact `[1/(n+1), σmax]` the map is continuous hence strongly measurable
  have h_on : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun σ => ∫ t in I, (Φ Zk σ t))
        (volume.restrict (Icc ((1 : ℝ) / (n + 1)) σmax)) := by
    intro n
    -- continuity ⇒ measurability ⇒ a.e. strong measurability on the restricted measure
    by_cases h : (1 : ℝ) / (n + 1) ≤ σmax
    · have hcont := continuousOn_integral_sq_poisson_Icc Zk I hI hI_bdd
        (one_div_pos.mpr (Nat.cast_add_one_pos n)) h
      exact hcont.aestronglyMeasurable measurableSet_Icc
    · -- interval is empty when 1/(n+1) > σmax
      rw [Icc_eq_empty h]
      simp only [Measure.restrict_empty]
      exact aestronglyMeasurable_zero_measure (fun σ => ∫ t in I, (Φ Zk σ t))
  -- glue along the union
  --simp [hcov, BoxIntegral.Prepartition.iUnion_restrict]
  rw [hcov]
  exact aestronglyMeasurable_iUnion_iff.mpr h_on

end PoissonParam

end

end ParameterIntegral

namespace MeasureTheory

open ParameterIntegral.PoissonParam

/-- Measurability of σ ↦ ∫ Vk²(σ,t) dt for Poisson sums. -/
theorem aestronglyMeasurable_integral_sq_poisson
    {Zk : Finset ℝ} (I : Set ℝ) (hI : MeasurableSet I)
    (hI_bounded : Bornology.IsBounded I) (σ_max : ℝ) (hσ_max : 0 < σ_max) :
    AEStronglyMeasurable
      (fun σ => ∫ t in I, (∑ γ ∈ Zk, σ / ((t - γ)^2 + σ^2))^2)
      (Measure.restrict volume (Set.Ioc 0 σ_max)) := by
  exact aestronglyMeasurable_integral_sq_poisson_Ioc Zk I hI hI_bounded hσ_max

end MeasureTheory
