import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

open MeromorphicOn Metric Real Set Classical

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/--
Monotonicity of the logarithmic counting function in the divisor argument:
if `D₁ ≤ D₂` pointwise and `1 ≤ r`, then `logCounting D₁ r ≤ logCounting D₂ r`.
-/
lemma logCounting_le
    {D₁ D₂ : locallyFinsuppWithin (Set.univ : Set E) ℤ}
    (hD : D₁ ≤ D₂) {r : ℝ} (hr : 1 ≤ r) :
    logCounting D₁ r ≤ logCounting D₂ r := by
  classical
  have hr_nonneg : 0 ≤ r := le_trans (by norm_num) hr
  -- Expand the definition of `logCounting` at radius `r`.
  change
    (∑ᶠ z, D₁.toClosedBall r z * log (r * ‖z‖⁻¹) + (D₁ 0) * log r)
      ≤
    (∑ᶠ z, D₂.toClosedBall r z * log (r * ‖z‖⁻¹) + (D₂ 0) * log r)
  -- It suffices to bound the finsum part and the `D 0 * log r` term separately.
  refine add_le_add ?h_sum ?h_zero
  · -- Finsum part: use a common finite support and compare termwise.
    have h₁s :
        ((D₁.toClosedBall r).support ∪ (D₂.toClosedBall r).support).Finite := by
      apply Set.finite_union.2
      constructor
      · exact Function.locallyFinsuppWithin.finiteSupport _ (isCompact_closedBall (0 : E) |r|)
      · exact Function.locallyFinsuppWithin.finiteSupport _ (isCompact_closedBall (0 : E) |r|)
    -- Rewrite both finsums as sums over this common finite support.
    have h₁ :
        ∑ᶠ z, D₁.toClosedBall r z * log (r * ‖z‖⁻¹) =
          ∑ z ∈ h₁s.toFinset,
            D₁.toClosedBall r z * log (r * ‖z‖⁻¹) := by
      refine
        finsum_eq_finset_sum_of_support_subset
          (fun i ↦ (D₁.toClosedBall r i : ℝ) * log (r * ‖i‖⁻¹)) ?_
      intro z hz
      aesop
    have h₂ :
        ∑ᶠ z, D₂.toClosedBall r z * log (r * ‖z‖⁻¹) =
          ∑ z ∈ h₁s.toFinset,
            D₂.toClosedBall r z * log (r * ‖z‖⁻¹) := by
      refine
        finsum_eq_finset_sum_of_support_subset
          (fun i ↦ (D₂.toClosedBall r i : ℝ) * log (r * ‖i‖⁻¹)) ?_
      intro z hz
      aesop
    -- Reduce finsum inequality to a finite sum inequality.
    simp [h₁, h₂]
    -- Show each summand is monotone in `D` because the logarithmic weight is ≥ 0 for `r ≥ 1`.
    refine Finset.sum_le_sum ?_
    intro z hz
    -- From `hz : z ∈ h₁s.toFinset` we get that `z` lies in the closed ball.
    have hz' :
        z ∈ (D₁.toClosedBall r).support ∪ (D₂.toClosedBall r).support :=
      (Set.Finite.mem_toFinset h₁s).1 hz
    have hz_mem : z ∈ closedBall (0 : E) |r| := by
      rcases hz' with hz₁ | hz₂
      · exact (D₁.toClosedBall r).supportWithinDomain hz₁
      · exact (D₂.toClosedBall r).supportWithinDomain hz₂
    have hz_norm_le_abs : ‖z‖ ≤ |r| := by
      -- membership in `closedBall 0 |r|` is equivalent to `‖z‖ ≤ |r|`
      simpa [Metric.closedBall, dist_eq_norm] using hz_mem
    have hz_norm_le : ‖z‖ ≤ r := by
      simpa [abs_of_nonneg hr_nonneg] using hz_norm_le_abs
    -- Nonnegativity of the logarithmic weight.
    have hlog_nonneg :
        0 ≤ log (r * ‖z‖⁻¹) := by
      by_cases hz0 : z = 0
      · subst hz0
        simp
      · have hz_pos : 0 < ‖z‖ := by
          simp [hz0]
        have hz_nonneg : 0 ≤ ‖z‖ := le_of_lt hz_pos
        -- Divide `‖z‖ ≤ r` by `‖z‖ > 0` to get `1 ≤ r / ‖z‖`.
        have hdiv :
            1 ≤ r / ‖z‖ := by
          have h := div_le_div_of_nonneg_right hz_norm_le hz_nonneg
          have hz_ne : ‖z‖ ≠ 0 := ne_of_gt hz_pos
          simpa [div_self hz_ne] using h
        have hge1 : 1 ≤ r * ‖z‖⁻¹ := by
          simpa [div_eq_mul_inv] using hdiv
        exact Real.log_nonneg hge1
    -- Monotonicity in the coefficient: restrict the pointwise inequality `hD`.
    have hcoeff :
        (D₁.toClosedBall r z : ℤ) ≤ D₂.toClosedBall r z := by
      -- On the closed ball, `toClosedBall` just evaluates the original functions.
      have h₁' :
          (D₁.toClosedBall r z : ℤ) = D₁ z := by
        simp [toClosedBall, restrictMonoidHom, restrict_apply, hz_mem]
      have h₂' :
          (D₂.toClosedBall r z : ℤ) = D₂ z := by
        simp [toClosedBall, restrictMonoidHom, restrict_apply, hz_mem]
      have hDz : D₁ z ≤ D₂ z := hD z
      simpa [h₁', h₂'] using hDz
    have hcoeff_real :
        (D₁.toClosedBall r z : ℝ) ≤ D₂.toClosedBall r z := Int.cast_le.mpr hcoeff
    have := mul_le_mul_of_nonneg_right hcoeff_real hlog_nonneg
    simpa using this
  · -- The `D 0 * log r` term: again monotone because `log r ≥ 0` when `1 ≤ r`.
    have hlogr_nonneg : 0 ≤ log r := Real.log_nonneg hr
    have hcoeff0 : (D₁ 0 : ℤ) ≤ D₂ 0 := hD 0
    have hcoeff0_real : (D₁ 0 : ℝ) ≤ D₂ 0 := Int.cast_le.mpr hcoeff0
    have := mul_le_mul_of_nonneg_right hcoeff0_real hlogr_nonneg
    simpa using this

end Function.locallyFinsuppWithin

open MeromorphicOn Metric Real Set Classical

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜} {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

/--
Adding a locally vanishing function does not change the order.
-/
theorem meromorphicOrderAt_add_top
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₁ : meromorphicOrderAt f₁ x = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x = meromorphicOrderAt f₂ x := by
  rw [meromorphicOrderAt_congr]
  filter_upwards [meromorphicOrderAt_eq_top_iff.1 hf₁] with z hz
  simp_all

namespace ValueDistribution

/--
The counting function of a constant function is zero.
-/
@[simp] theorem logCounting_const
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {c : E} {e : WithTop E} :
    logCounting (fun _ ↦ c : 𝕜 → E) e = 0 := by
  simp [logCounting]

/--
The counting function of the constant function zero is zero.
-/
@[simp] theorem logCounting_const_zero [ProperSpace 𝕜] {e : WithTop E} :
    logCounting (0 : 𝕜 → E) e = 0 := logCounting_const

/--
The divisor of `f₁ + f₂` is larger than or equal to the minimum of the divisors
of `f₁` and `f₂`, respectively.
-/
theorem min_divisor_le_divisor_add {f₁ f₂ : 𝕜 → E} {z : 𝕜} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) (h₁z : z ∈ U) (h₃ : meromorphicOrderAt (f₁ + f₂) z ≠ ⊤) :
    min (divisor f₁ U z) (divisor f₂ U z) ≤ divisor (f₁ + f₂) U z := by
  by_cases hz : z ∉ U
  · simp_all
  simp only [Decidable.not_not] at hz
  rw [divisor_apply hf₁ hz, divisor_apply hf₂ hz, divisor_apply (hf₁.add hf₂) hz]
  by_cases h₁ : meromorphicOrderAt f₁ z = ⊤
  · rw [inf_le_iff]
    right
    rwa [meromorphicOrderAt_add_top]
  by_cases h₂ : meromorphicOrderAt f₂ z = ⊤
  · rw [inf_le_iff]
    left
    rwa [add_comm, meromorphicOrderAt_add_top]
  rw [← WithTop.untop₀_min h₁ h₂]
  apply WithTop.untop₀_le_untop₀ h₃
  exact meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz)

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the maximum of the
pole divisors of `f₁` and `f₂`, respectively.
-/
theorem negPart_divisor_add_le_max {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ := by
  intro z
  by_cases hz : z ∉ U
  · simp [hz]
  rw [Decidable.not_not] at hz
  simp only [Function.locallyFinsuppWithin.negPart_apply, Function.locallyFinsuppWithin.max_apply]
  by_cases hf₁₂ : meromorphicOrderAt (f₁ + f₂) z = ⊤
  · simp [divisor_apply (hf₁.add hf₂) hz, hf₁₂, negPart_nonneg]
  rw [← negPart_min]
  apply ((le_iff_posPart_negPart _ _).1 (min_divisor_le_divisor_add hf₁ hf₂ hz hf₁₂)).2

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the sum of the pole
divisors of `f₁` and `f₂`, respectively.
-/
theorem negPart_divisor_add_le_add {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    (divisor (f₁ + f₂) U)⁻ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
  calc (divisor (f₁ + f₂) U)⁻
  _ ≤ max (divisor f₁ U)⁻ (divisor f₂ U)⁻ :=
    negPart_divisor_add_le_max hf₁ hf₂
  _ ≤ (divisor f₁ U)⁻ + (divisor f₂ U)⁻ := by
    by_cases h : (divisor f₁ U)⁻ ≤ (divisor f₂ U)⁻
    <;> simp_all [negPart_nonneg]

/--
For `1 ≤ r`, the counting function of `f + g` at `⊤` is less than or equal to
the sum of the counting functions of `f` and `g`, respectively.
-/
theorem counting_top_add_le [ProperSpace 𝕜] {f₁ f₂ : 𝕜 → E} {r : ℝ}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₁f₂ : MeromorphicOn f₂ Set.univ) (hr : 1 ≤ r) :
    logCounting (f₁ + f₂) ⊤ r ≤ ((logCounting f₁ ⊤) + (logCounting f₂ ⊤)) r := by
  simp only [logCounting, ↓reduceDIte]
  rw [← Function.locallyFinsuppWithin.logCounting.map_add]
  exact Function.locallyFinsuppWithin.logCounting_le (negPart_divisor_add_le_add h₁f₁ h₁f₂) hr

/--
Asymptotically, the counting function of `f + g` at `⊤` is less than or equal to
the sum of the counting functions of `f` and `g`, respectively.
-/
theorem counting_top_add_eventually_le [ProperSpace 𝕜] {f₁ f₂ : 𝕜 → E}
    (h₁f₁ : MeromorphicOn f₁ Set.univ) (h₁f₂ : MeromorphicOn f₂ Set.univ) :
    logCounting (f₁ + f₂) ⊤ ≤ᶠ[Filter.atTop] (logCounting f₁ ⊤) + (logCounting f₂ ⊤) := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ counting_top_add_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the counting function of a sum `∑ a, f a` at `⊤` is less than or
equal to the sum of the counting functions of `f ·`.
-/
theorem counting_top_sum_le [ProperSpace 𝕜] {α : Type*} (s : Finset α) (f : α → 𝕜 → E)
    {r : ℝ} (h₁f : ∀ a, MeromorphicOn (f a) Set.univ) (hr : 1 ≤ r) :
    logCounting (∑ a ∈ s, f a) ⊤ r ≤ (∑ a ∈ s, (logCounting (f a) ⊤)) r := by
  induction s using Finset.induction with
  | empty =>
    simp
  | insert a s ha hs =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc logCounting (f a + ∑ x ∈ s, f x) ⊤ r
    _ ≤ (logCounting (f a) ⊤ + logCounting (∑ x ∈ s, f x) ⊤) r :=
      counting_top_add_le (h₁f a) (MeromorphicOn.sum h₁f) hr
    _ ≤ (logCounting (f a) ⊤ + ∑ x ∈ s, logCounting (f x) ⊤) r :=
      add_le_add (by trivial) hs

/--
Asymptotically, the counting function of a sum `∑ a, f a` at `⊤` is less than or
equal to the sum of the counting functions of `f ·`.
-/
theorem counting_top_sum_eventually_le [ProperSpace 𝕜] {α : Type*} (s : Finset α) (f : α → 𝕜 → E)
    (h₁f : ∀ a, MeromorphicOn (f a) Set.univ) :
    logCounting (∑ a ∈ s, f a) ⊤ ≤ᶠ[Filter.atTop] ∑ a ∈ s, (logCounting (f a) ⊤) := by
  filter_upwards [Filter.eventually_ge_atTop 1]
  exact fun _ hr ↦ counting_top_sum_le s f h₁f hr

end ValueDistribution
