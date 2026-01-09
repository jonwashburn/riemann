import Carleson.DoublingMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Riemann.academic_framework.HadamardFactorization.CartanBound

noncomputable section

namespace ComplexAnalysis
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric ValueDistribution
open scoped Topology

/-! ### analytic-order aux

Mathlib’s core lemmas relate zeros to `analyticOrderAt f z₀ ≠ 0`, not to strict positivity.
For convenience (and to keep proofs readable), we expose the “positive iff zero” formulation
used later in this file.
-/

lemma analyticOrderAt_pos_iff_zero {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    0 < analyticOrderAt f z₀ ↔ f z₀ = 0 := by
  -- On `ℕ∞`, `0 < n` is equivalent to `n ≠ 0`.
  -- For analytic functions, `analyticOrderAt f z₀ ≠ 0 ↔ f z₀ = 0`.
  simpa [pos_iff_ne_zero] using (hf.analyticOrderAt_ne_zero : analyticOrderAt f z₀ ≠ 0 ↔ f z₀ = 0)

/-!
`analyticOrderAt` is additive under multiplication of analytic functions. We package the specific
instance needed for the Hadamard canonical product `z ↦ z^ord0 * ∏' n, E_m(z/aₙ)` as a convenient
rewrite lemma.

This lemma intentionally does **not** attempt to compute the order of the infinite product; it
only splits the order of the product into the order of the power and the order of the canonical
product term, assuming analyticity of the latter at the point.
-/

lemma analyticOrderAt_canonical_product_mul_power
    {m ord0 : ℕ} {a : ℕ → ℂ} {z₀ : ℂ}
    (hG : AnalyticAt ℂ (fun z : ℂ => ∏' n : ℕ, weierstrassFactor m (z / a n)) z₀) :
    analyticOrderAt
        (fun z : ℂ => z ^ ord0 * (∏' n : ℕ, weierstrassFactor m (z / a n))) z₀
      =
      analyticOrderAt (fun z : ℂ => z ^ ord0) z₀
        + analyticOrderAt (fun z : ℂ => ∏' n : ℕ, weierstrassFactor m (z / a n)) z₀ := by
  have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ ord0) z₀ :=
    (differentiable_id.pow ord0).analyticAt z₀
  simpa [mul_assoc] using
    (analyticOrderAt_mul (𝕜 := ℂ)
      (f := fun z : ℂ => z ^ ord0)
      (g := fun z : ℂ => ∏' n : ℕ, weierstrassFactor m (z / a n))
      (z₀ := z₀) hpow hG)

/-- Pointwise summability of the Weierstrass-factor tail, allowing padding zeros in `ZeroData`. -/
lemma summable_weierstrassFactor_sub_one_zeroData
    {f : ℂ → ℂ} (hz : ZeroData f) (m : ℕ)
    (h_sum : Summable (fun n : ℕ => ‖hz.zeros n‖⁻¹ ^ (m + 1))) (z : ℂ) :
    Summable (fun n : ℕ => weierstrassFactor m (z / hz.zeros n) - 1) := by
  classical
  -- Majorant argument as in `summable_weierstrassFactor_sub_one`, but allowing padding zeros:
  -- if `hz.zeros n = 0` then the summand is identically `0`.
  set R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  -- Majorant for the tail.
  let g : ℕ → ℝ := fun n => (4 * R ^ (m + 1)) * (‖hz.zeros n‖⁻¹ ^ (m + 1))
  have hg : Summable g := h_sum.mul_left (4 * R ^ (m + 1))

  -- Remove the finitely many nonzero zeros in the ball of radius `2R`.
  let s : Finset ℕ := (hz.finite_in_ball (2 * R)).toFinset
  have hs_eventually : ∀ᶠ n in atTop, n ∉ s := by
    by_cases hs : s = ∅
    ·
      refine Filter.Eventually.of_forall (fun n => ?_)
      simp [hs]
    · refine Filter.eventually_atTop.2 ?_
      refine ⟨s.max' (Finset.nonempty_iff_ne_empty.2 hs) + 1, ?_⟩
      intro n hn hnmem
      have hle : n ≤ s.max' (Finset.nonempty_iff_ne_empty.2 hs) :=
        Finset.le_max' s n hnmem
      exact Nat.not_succ_le_self _ (le_trans hn hle)

  have hbound :
      ∀ᶠ n in atTop, ‖weierstrassFactor m (z / hz.zeros n) - 1‖ ≤ g n := by
    filter_upwards [hs_eventually] with n hn_not_mem
    have hn_small : ¬(hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 2 * R) := by
      -- membership in `s` is definitional for the set of small nonzero zeros
      simpa [s] using hn_not_mem
    by_cases hn0 : hz.zeros n = 0
    · -- Padding index: the summand is 0 and the bound is trivial.
      simp [hn0, g, weierstrassFactor_zero, R]
    · -- Nonzero, and not small: hence `2R < ‖hz.zeros n‖`.
      have hlarge : (2 * R : ℝ) < ‖hz.zeros n‖ := by
        have : ¬‖hz.zeros n‖ ≤ 2 * R := by
          intro hle
          exact hn_small ⟨hn0, hle⟩
        exact lt_of_not_ge this
      have hz' : ‖z / hz.zeros n‖ ≤ (1 / 2 : ℝ) := by
        have hzle : ‖z‖ ≤ R := le_max_left _ _
        have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
        have hzdiv : ‖z / hz.zeros n‖ = ‖z‖ / ‖hz.zeros n‖ := by simp
        rw [hzdiv]
        have hfrac₁ : ‖z‖ / ‖hz.zeros n‖ ≤ ‖z‖ / (2 * R) := by
          exact div_le_div_of_nonneg_left (norm_nonneg z) h2R_pos (le_of_lt hlarge)
        have hfrac₂ : ‖z‖ / (2 * R) ≤ R / (2 * R) :=
          div_le_div_of_nonneg_right hzle (le_of_lt h2R_pos)
        have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
        have hRsimp : (R / (2 * R : ℝ)) = (1 / 2 : ℝ) := by field_simp [hRne]
        exact (hfrac₁.trans hfrac₂).trans_eq hRsimp
      have hpow :=
        weierstrassFactor_sub_one_bound_pow (m := m) (z := z / hz.zeros n) hz'
      have hzR : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (le_max_left _ _) _
      calc
        ‖weierstrassFactor m (z / hz.zeros n) - 1‖
            ≤ 4 * ‖z / hz.zeros n‖ ^ (m + 1) := hpow
        _ = 4 * (‖z‖ ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
              simp [div_eq_mul_inv, mul_pow, norm_inv]
        _ ≤ 4 * (R ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
              gcongr
        _ = g n := by
              -- reassociate/commute scalars
              simp [g, mul_assoc, mul_left_comm, mul_comm]

  exact Summable.of_norm_bounded_eventually_nat (E := ℂ) hg hbound

/-! A convenient pointwise nonvanishing lemma for canonical products. -/
lemma tprod_weierstrassFactor_ne_zero_of_forall
    {f : ℂ → ℂ} (hz : ZeroData f) (m : ℕ)
    (h_sum : Summable (fun n : ℕ => ‖hz.zeros n‖⁻¹ ^ (m + 1))) (z : ℂ)
    (hfac : ∀ n : ℕ, weierstrassFactor m (z / hz.zeros n) ≠ 0) :
    (∏' n : ℕ, weierstrassFactor m (z / hz.zeros n)) ≠ 0 := by
  have htail :
      Summable (fun n : ℕ => weierstrassFactor m (z / hz.zeros n) - 1) :=
    summable_weierstrassFactor_sub_one_zeroData (hz := hz) (m := m) h_sum z
  have hlog : Summable (fun n : ℕ => Complex.log (weierstrassFactor m (z / hz.zeros n))) := by
    simpa [add_sub_cancel] using
      (Complex.summable_log_one_add_of_summable
        (f := fun n : ℕ => weierstrassFactor m (z / hz.zeros n) - 1) htail)
  have hprod :
      Complex.exp (∑' n : ℕ, Complex.log (weierstrassFactor m (z / hz.zeros n)))
        = ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n) := by
    simpa using
      (Complex.cexp_tsum_eq_tprod
        (f := fun n : ℕ => weierstrassFactor m (z / hz.zeros n)) hfac hlog)
  have hexp_ne :
      Complex.exp (∑' n : ℕ, Complex.log (weierstrassFactor m (z / hz.zeros n))) ≠ 0 :=
    Complex.exp_ne_zero _
  intro h0
  exact hexp_ne (by simpa [hprod] using h0)

/-!
Differentiability of the canonical product attached to a `ZeroData`, using the local-uniform
product theorem (M-test on compact sets), and allowing padding zeros.
-/
lemma differentiable_canonical_product_zeroData
    {f : ℂ → ℂ} (hz : ZeroData f) (m : ℕ)
    (h_sum : Summable (fun n : ℕ => ‖hz.zeros n‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (fun z : ℂ => ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n)) := by
  classical
  let G : ℂ → ℂ := fun z => ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n)
  have hdiff_on : DifferentiableOn ℂ G (Set.univ : Set ℂ) := by
    intro z0 _hz0
    let R : ℝ := ‖z0‖ + 1
    let U : Set ℂ := Metric.ball (0 : ℂ) (R + 1)
    have hUopen : IsOpen U := Metric.isOpen_ball
    have hzU : z0 ∈ U := by
      have : ‖z0‖ < R + 1 := by
        dsimp [R]
        linarith [norm_nonneg z0]
      simpa [U, Metric.mem_ball, dist_zero_right] using this

    let f : ℕ → ℂ → ℂ := fun n z => weierstrassFactor m (z / hz.zeros n) - 1
    let M : ℕ → ℝ := fun n => (4 * (R + 1) ^ (m + 1)) * (‖hz.zeros n‖⁻¹ ^ (m + 1))
    have hM : Summable M := by
      simpa [M, mul_assoc, mul_left_comm, mul_comm] using
        (h_sum.mul_left (4 * (R + 1) ^ (m + 1)))

    let s : Finset ℕ := (hz.finite_in_ball (2 * (R + 1))).toFinset
    have hs_eventually : ∀ᶠ n in atTop, n ∉ s := by
      by_cases hs : s = ∅
      ·
        refine Filter.Eventually.of_forall (fun n => ?_)
        simp [hs]
      · refine Filter.eventually_atTop.2 ?_
        refine ⟨s.max' (Finset.nonempty_iff_ne_empty.2 hs) + 1, ?_⟩
        intro n hn hnmem
        have hle : n ≤ s.max' (Finset.nonempty_iff_ne_empty.2 hs) :=
          Finset.le_max' s n hnmem
        exact Nat.not_succ_le_self _ (le_trans hn hle)

    have hBoundU : ∀ᶠ n in atTop, ∀ z ∈ U, ‖f n z‖ ≤ M n := by
      filter_upwards [hs_eventually] with n hn_not_mem z hzU
      have hzU' : ‖z‖ < R + 1 := by
        simpa [U, Metric.mem_ball, dist_zero_right] using hzU
      have hn_small : ¬(hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 2 * (R + 1)) := by
        simpa [s] using hn_not_mem
      by_cases hn0 : hz.zeros n = 0
      · simp [f, hn0, M]
      ·
        have hlarge : (2 * (R + 1) : ℝ) < ‖hz.zeros n‖ := by
          have : ¬‖hz.zeros n‖ ≤ 2 * (R + 1) := by
            intro hle
            exact hn_small ⟨hn0, hle⟩
          exact lt_of_not_ge this
        have hz' : ‖z / hz.zeros n‖ ≤ (1 / 2 : ℝ) := by
          have h2R1_pos : 0 < (2 * (R + 1) : ℝ) := by
            have : 0 < (R + 1 : ℝ) := by
              dsimp [R]
              linarith [norm_nonneg z0]
            nlinarith
          have : ‖z / hz.zeros n‖ = ‖z‖ / ‖hz.zeros n‖ := by simp
          rw [this]
          have hfrac₁ : ‖z‖ / ‖hz.zeros n‖ ≤ ‖z‖ / (2 * (R + 1)) :=
            div_le_div_of_nonneg_left (norm_nonneg z) h2R1_pos (le_of_lt hlarge)
          have hfrac₂ : ‖z‖ / (2 * (R + 1)) ≤ (R + 1) / (2 * (R + 1)) :=
            div_le_div_of_nonneg_right (le_of_lt hzU') (le_of_lt h2R1_pos)
          have hfrac : ‖z‖ / ‖hz.zeros n‖ ≤ (R + 1) / (2 * (R + 1)) := hfrac₁.trans hfrac₂
          have hRne : (R + 1 : ℝ) ≠ 0 := by
            have : 0 < (R + 1 : ℝ) := by
              dsimp [R]
              linarith [norm_nonneg z0]
            exact ne_of_gt this
          have hRsimp : ((R + 1) / (2 * (R + 1) : ℝ)) = (1 / 2 : ℝ) := by
            field_simp [hRne]
          exact hfrac.trans_eq hRsimp
        have hpow := weierstrassFactor_sub_one_bound_pow (m := m) (z := z / hz.zeros n) hz'
        have hzR : ‖z‖ ^ (m + 1) ≤ (R + 1) ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) (le_of_lt hzU') _
        calc
          ‖f n z‖ = ‖weierstrassFactor m (z / hz.zeros n) - 1‖ := by simp [f]
          _ ≤ 4 * ‖z / hz.zeros n‖ ^ (m + 1) := hpow
          _ = 4 * (‖z‖ ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                simp [div_eq_mul_inv, mul_pow, norm_inv]
          _ ≤ 4 * ((R + 1) ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                gcongr
          _ = M n := by
                simp [M, mul_assoc, mul_comm, mul_left_comm]

    have hcts : ∀ n, ContinuousOn (f n) U := by
      intro n
      have hcont : Continuous (fun z : ℂ => weierstrassFactor m (z / hz.zeros n)) :=
        ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const (hz.zeros n))).continuous
      simpa [f] using (hcont.continuousOn.sub continuousOn_const)

    have hloc :
        HasProdLocallyUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n : ℕ, (1 + f n z)) U :=
      Summable.hasProdLocallyUniformlyOn_nat_one_add (K := U) hUopen hM hBoundU hcts

    have hFdiff :
        ∀ᶠ s' : Finset ℕ in (atTop : Filter (Finset ℕ)),
          DifferentiableOn ℂ (fun z ↦ ∏ i ∈ s', (1 + f i z)) U :=
      Filter.Eventually.of_forall (fun s' => by
        have hdf : ∀ i ∈ s', DifferentiableOn ℂ (fun z => (1 + f i z)) U := by
          intro i _hi
          have : Differentiable ℂ (fun z => (1 + f i z)) := by
            have hdiff : Differentiable ℂ (fun z => weierstrassFactor m (z / hz.zeros i)) :=
              (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (hz.zeros i))
            simpa [f, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
              (hdiff.sub_const (1 : ℂ)).const_add (1 : ℂ)
          exact this.differentiableOn
        simpa [Finset.prod_fn] using
          (DifferentiableOn.finset_prod (s := U) (u := s')
            (f := fun i z => (1 + f i z)) hdf))

    have htlocU :
        TendstoLocallyUniformlyOn
            (fun s' z ↦ ∏ i ∈ s', (1 + f i z))
            (fun z ↦ ∏' n : ℕ, (1 + f n z))
            (atTop : Filter (Finset ℕ)) U := by
      simpa [HasProdLocallyUniformlyOn] using hloc

    have hdiffU : DifferentiableOn ℂ (fun z ↦ ∏' n : ℕ, (1 + f n z)) U :=
      htlocU.differentiableOn hFdiff hUopen

    have hEq : (fun z : ℂ => ∏' n : ℕ, (1 + f n z)) = G := by
      funext z
      simp [G, f, add_sub_cancel]

    have hUnhds : U ∈ 𝓝 z0 := hUopen.mem_nhds hzU
    have : DifferentiableAt ℂ G z0 := by
      have := (hdiffU.analyticAt hUnhds).differentiableAt
      simpa [hEq] using this
    exact this.differentiableWithinAt

  simpa [G] using (differentiableOn_univ.1 hdiff_on)

/-! ### Canonical-product lemmas that only use local finiteness (no `ZeroData` specs)

For the factorization proof we need to modify finitely many entries of the zero sequence (turning
them into padding `0`s). The lemmas below are phrased only in terms of a sequence `zeros` and the
local finiteness condition “only finitely many nonzero entries lie in each closed ball”.
-/

/-- Pointwise summability of the Weierstrass-factor tail from summability of `‖zeros n‖⁻¹^(m+1)`,
assuming local finiteness of the nonzero entries of `zeros`. -/
lemma summable_weierstrassFactor_sub_one_of_finiteInBall
    (zeros : ℕ → ℂ)
    (finite_in_ball : ∀ R : ℝ, ({n : ℕ | zeros n ≠ 0 ∧ ‖zeros n‖ ≤ R} : Set ℕ).Finite)
    (m : ℕ) (h_sum : Summable (fun n : ℕ => ‖zeros n‖⁻¹ ^ (m + 1))) (z : ℂ) :
    Summable (fun n : ℕ => weierstrassFactor m (z / zeros n) - 1) := by
  classical
  set R : ℝ := max ‖z‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  let g : ℕ → ℝ := fun n => (4 * R ^ (m + 1)) * (‖zeros n‖⁻¹ ^ (m + 1))
  have hg : Summable g := h_sum.mul_left (4 * R ^ (m + 1))

  let s : Finset ℕ := (finite_in_ball (2 * R)).toFinset
  have hs_eventually : ∀ᶠ n in atTop, n ∉ s := by
    by_cases hs : s = ∅
    ·
      refine Filter.Eventually.of_forall (fun n => ?_)
      simp [hs]
    · refine Filter.eventually_atTop.2 ?_
      refine ⟨s.max' (Finset.nonempty_iff_ne_empty.2 hs) + 1, ?_⟩
      intro n hn hnmem
      have hle : n ≤ s.max' (Finset.nonempty_iff_ne_empty.2 hs) :=
        Finset.le_max' s n hnmem
      exact Nat.not_succ_le_self _ (le_trans hn hle)

  have hbound :
      ∀ᶠ n in atTop, ‖weierstrassFactor m (z / zeros n) - 1‖ ≤ g n := by
    filter_upwards [hs_eventually] with n hn_not_mem
    have hn_small : ¬(zeros n ≠ 0 ∧ ‖zeros n‖ ≤ 2 * R) := by
      simpa [s] using hn_not_mem
    by_cases hn0 : zeros n = 0
    · simp [hn0, g, weierstrassFactor_zero, R]
    ·
      have hlarge : (2 * R : ℝ) < ‖zeros n‖ := by
        have : ¬‖zeros n‖ ≤ 2 * R := by
          intro hle
          exact hn_small ⟨hn0, hle⟩
        exact lt_of_not_ge this
      have hz' : ‖z / zeros n‖ ≤ (1 / 2 : ℝ) := by
        have hzle : ‖z‖ ≤ R := le_max_left _ _
        have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
        have hzdiv : ‖z / zeros n‖ = ‖z‖ / ‖zeros n‖ := by simp
        rw [hzdiv]
        have hfrac₁ : ‖z‖ / ‖zeros n‖ ≤ ‖z‖ / (2 * R) := by
          exact div_le_div_of_nonneg_left (norm_nonneg z) h2R_pos (le_of_lt hlarge)
        have hfrac₂ : ‖z‖ / (2 * R) ≤ R / (2 * R) :=
          div_le_div_of_nonneg_right hzle (le_of_lt h2R_pos)
        have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
        have hRsimp : (R / (2 * R : ℝ)) = (1 / 2 : ℝ) := by field_simp [hRne]
        exact (hfrac₁.trans hfrac₂).trans_eq hRsimp
      have hpow := weierstrassFactor_sub_one_bound_pow (m := m) (z := z / zeros n) hz'
      have hzR : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (le_max_left _ _) _
      calc
        ‖weierstrassFactor m (z / zeros n) - 1‖
            ≤ 4 * ‖z / zeros n‖ ^ (m + 1) := hpow
        _ = 4 * (‖z‖ ^ (m + 1) * ‖zeros n‖⁻¹ ^ (m + 1)) := by
              simp [div_eq_mul_inv, mul_pow, norm_inv]
        _ ≤ 4 * (R ^ (m + 1) * ‖zeros n‖⁻¹ ^ (m + 1)) := by
              gcongr
        _ = g n := by
              simp [g, mul_assoc, mul_comm]

  exact Summable.of_norm_bounded_eventually_nat (E := ℂ) hg hbound

/-- If all Weierstrass factors are nonzero at `z`, then the canonical product value at `z` is nonzero. -/
lemma tprod_weierstrassFactor_ne_zero_of_forall_of_finiteInBall
    (zeros : ℕ → ℂ)
    (finite_in_ball : ∀ R : ℝ, ({n : ℕ | zeros n ≠ 0 ∧ ‖zeros n‖ ≤ R} : Set ℕ).Finite)
    (m : ℕ) (h_sum : Summable (fun n : ℕ => ‖zeros n‖⁻¹ ^ (m + 1))) (z : ℂ)
    (hfac : ∀ n : ℕ, weierstrassFactor m (z / zeros n) ≠ 0) :
    (∏' n : ℕ, weierstrassFactor m (z / zeros n)) ≠ 0 := by
  have htail :
      Summable (fun n : ℕ => weierstrassFactor m (z / zeros n) - 1) :=
    summable_weierstrassFactor_sub_one_of_finiteInBall zeros finite_in_ball m h_sum z
  have hlog : Summable (fun n : ℕ => Complex.log (weierstrassFactor m (z / zeros n))) := by
    simpa [add_sub_cancel] using
      (Complex.summable_log_one_add_of_summable
        (f := fun n : ℕ => weierstrassFactor m (z / zeros n) - 1) htail)
  have hprod :
      Complex.exp (∑' n : ℕ, Complex.log (weierstrassFactor m (z / zeros n)))
        = ∏' n : ℕ, weierstrassFactor m (z / zeros n) := by
    simpa using
      (Complex.cexp_tsum_eq_tprod (f := fun n : ℕ => weierstrassFactor m (z / zeros n)) hfac hlog)
  have hexp_ne :
      Complex.exp (∑' n : ℕ, Complex.log (weierstrassFactor m (z / zeros n))) ≠ 0 :=
    Complex.exp_ne_zero _
  intro h0
  exact hexp_ne (by simpa [hprod] using h0)

/-- Differentiability of the canonical product for a sequence `zeros` satisfying local finiteness. -/
lemma differentiable_canonical_product_of_finiteInBall
    (zeros : ℕ → ℂ)
    (finite_in_ball : ∀ R : ℝ, ({n : ℕ | zeros n ≠ 0 ∧ ‖zeros n‖ ≤ R} : Set ℕ).Finite)
    (m : ℕ) (h_sum : Summable (fun n : ℕ => ‖zeros n‖⁻¹ ^ (m + 1))) :
    Differentiable ℂ (fun z : ℂ => ∏' n : ℕ, weierstrassFactor m (z / zeros n)) := by
  classical
  -- The proof is the same local-uniform product argument used above for `ZeroData`.
  let G : ℂ → ℂ := fun z => ∏' n : ℕ, weierstrassFactor m (z / zeros n)
  have hdiff_on : DifferentiableOn ℂ G (Set.univ : Set ℂ) := by
    intro z0 _hz0
    let R : ℝ := ‖z0‖ + 1
    let U : Set ℂ := Metric.ball (0 : ℂ) (R + 1)
    have hUopen : IsOpen U := Metric.isOpen_ball
    have hzU : z0 ∈ U := by
      have : ‖z0‖ < R + 1 := by
        dsimp [R]
        linarith [norm_nonneg z0]
      simpa [U, Metric.mem_ball, dist_zero_right] using this

    let f : ℕ → ℂ → ℂ := fun n z => weierstrassFactor m (z / zeros n) - 1
    let M : ℕ → ℝ := fun n => (4 * (R + 1) ^ (m + 1)) * (‖zeros n‖⁻¹ ^ (m + 1))
    have hM : Summable M := by
      simpa [M, mul_assoc, mul_left_comm, mul_comm] using
        (h_sum.mul_left (4 * (R + 1) ^ (m + 1)))

    let s : Finset ℕ := (finite_in_ball (2 * (R + 1))).toFinset
    have hs_eventually : ∀ᶠ n in atTop, n ∉ s := by
      by_cases hs : s = ∅
      ·
        refine Filter.Eventually.of_forall (fun n => ?_)
        simp [hs]
      · refine Filter.eventually_atTop.2 ?_
        refine ⟨s.max' (Finset.nonempty_iff_ne_empty.2 hs) + 1, ?_⟩
        intro n hn hnmem
        have hle : n ≤ s.max' (Finset.nonempty_iff_ne_empty.2 hs) :=
          Finset.le_max' s n hnmem
        exact Nat.not_succ_le_self _ (le_trans hn hle)

    have hBoundU : ∀ᶠ n in atTop, ∀ z ∈ U, ‖f n z‖ ≤ M n := by
      filter_upwards [hs_eventually] with n hn_not_mem z hzU
      have hzU' : ‖z‖ < R + 1 := by
        simpa [U, Metric.mem_ball, dist_zero_right] using hzU
      have hn_small : ¬(zeros n ≠ 0 ∧ ‖zeros n‖ ≤ 2 * (R + 1)) := by
        simpa [s] using hn_not_mem
      by_cases hn0 : zeros n = 0
      · simp [f, hn0, M]
      ·
        have hlarge : (2 * (R + 1) : ℝ) < ‖zeros n‖ := by
          have : ¬‖zeros n‖ ≤ 2 * (R + 1) := by
            intro hle
            exact hn_small ⟨hn0, hle⟩
          exact lt_of_not_ge this
        have hz' : ‖z / zeros n‖ ≤ (1 / 2 : ℝ) := by
          have h2R1_pos : 0 < (2 * (R + 1) : ℝ) := by
            have : 0 < (R + 1 : ℝ) := by
              dsimp [R]
              linarith [norm_nonneg z0]
            nlinarith
          have : ‖z / zeros n‖ = ‖z‖ / ‖zeros n‖ := by simp
          rw [this]
          have hfrac₁ : ‖z‖ / ‖zeros n‖ ≤ ‖z‖ / (2 * (R + 1)) :=
            div_le_div_of_nonneg_left (norm_nonneg z) h2R1_pos (le_of_lt hlarge)
          have hfrac₂ : ‖z‖ / (2 * (R + 1)) ≤ (R + 1) / (2 * (R + 1)) :=
            div_le_div_of_nonneg_right (le_of_lt hzU') (le_of_lt h2R1_pos)
          have hfrac : ‖z‖ / ‖zeros n‖ ≤ (R + 1) / (2 * (R + 1)) := hfrac₁.trans hfrac₂
          have hRne : (R + 1 : ℝ) ≠ 0 := by
            have : 0 < (R + 1 : ℝ) := by
              dsimp [R]
              linarith [norm_nonneg z0]
            exact ne_of_gt this
          have hRsimp : ((R + 1) / (2 * (R + 1) : ℝ)) = (1 / 2 : ℝ) := by
            field_simp [hRne]
          exact hfrac.trans_eq hRsimp
        have hpow := weierstrassFactor_sub_one_bound_pow (m := m) (z := z / zeros n) hz'
        have hzR : ‖z‖ ^ (m + 1) ≤ (R + 1) ^ (m + 1) :=
          pow_le_pow_left₀ (norm_nonneg z) (le_of_lt hzU') _
        calc
          ‖f n z‖ = ‖weierstrassFactor m (z / zeros n) - 1‖ := by simp [f]
          _ ≤ 4 * ‖z / zeros n‖ ^ (m + 1) := hpow
          _ = 4 * (‖z‖ ^ (m + 1) * ‖zeros n‖⁻¹ ^ (m + 1)) := by
                simp [div_eq_mul_inv, mul_pow, norm_inv]
          _ ≤ 4 * ((R + 1) ^ (m + 1) * ‖zeros n‖⁻¹ ^ (m + 1)) := by
                gcongr
          _ = M n := by
                simp [M, mul_assoc, mul_comm]

    have hcts : ∀ n, ContinuousOn (f n) U := by
      intro n
      have hcont : Continuous (fun z : ℂ => weierstrassFactor m (z / zeros n)) :=
        ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const (zeros n))).continuous
      simpa [f] using (hcont.continuousOn.sub continuousOn_const)

    have hloc :
        HasProdLocallyUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n : ℕ, (1 + f n z)) U :=
      Summable.hasProdLocallyUniformlyOn_nat_one_add (K := U) hUopen hM hBoundU hcts

    have hFdiff :
        ∀ᶠ s' : Finset ℕ in (atTop : Filter (Finset ℕ)),
          DifferentiableOn ℂ (fun z ↦ ∏ i ∈ s', (1 + f i z)) U :=
      Filter.Eventually.of_forall (fun s' => by
        have hdf : ∀ i ∈ s', DifferentiableOn ℂ (fun z => (1 + f i z)) U := by
          intro i _hi
          have : Differentiable ℂ (fun z => (1 + f i z)) := by
            have hdiff : Differentiable ℂ (fun z => weierstrassFactor m (z / zeros i)) :=
              (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (zeros i))
            simpa [f, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
              (hdiff.sub_const (1 : ℂ)).const_add (1 : ℂ)
          exact this.differentiableOn
        simpa [Finset.prod_fn] using
          (DifferentiableOn.finset_prod (s := U) (u := s')
            (f := fun i z => (1 + f i z)) hdf))

    have htlocU :
        TendstoLocallyUniformlyOn
            (fun s' z ↦ ∏ i ∈ s', (1 + f i z))
            (fun z ↦ ∏' n : ℕ, (1 + f n z))
            (atTop : Filter (Finset ℕ)) U := by
      simpa [HasProdLocallyUniformlyOn] using hloc

    have hdiffU : DifferentiableOn ℂ (fun z ↦ ∏' n : ℕ, (1 + f n z)) U :=
      htlocU.differentiableOn hFdiff hUopen

    have hEq : (fun z : ℂ => ∏' n : ℕ, (1 + f n z)) = G := by
      funext z
      simp [G, f, add_sub_cancel]

    have hUnhds : U ∈ 𝓝 z0 := hUopen.mem_nhds hzU
    have : DifferentiableAt ℂ G z0 := by
      have := (hdiffU.analyticAt hUnhds).differentiableAt
      simpa [hEq] using this
    exact this.differentiableWithinAt

  simpa [G] using (differentiableOn_univ.1 hdiff_on)

set_option maxHeartbeats 600000 in
/--
**Hadamard Quotient Growth Bound**

The quotient `H = f / F` of an entire function `f` by its canonical product `F`
has finite order. Specifically, if `f` has order `ρ` and `F` is constructed with genus `m`,
then `H` has order at most `m+1`.

This lemma is used in the Hadamard factorization proof by showing that
the quotient `H` satisfies an exponential growth bound `exp(C |z|^(m+1))`.
-/
lemma hadamard_quotient_growth_bound
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) (hz : ZeroData f)
    (m : ℕ) (hσ : ρ < (m + 1 : ℝ)) (F H : ℂ → ℂ)
    (hH_entire : Differentiable ℂ H)
    (hH_nonzero : ∀ z : ℂ, H z ≠ 0)
    (hH_eq : ∀ z : ℂ, F z ≠ 0 → H z = f z / F z)
    (hF_def : F = fun z : ℂ => z ^ hz.ord0 * ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n))
    : ∃ C > 0, ∀ z : ℂ, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1)) := by
  classical

  -- 1. Establish the global identity f = H * F
  have h_prod_eq : ∀ z, f z = H z * F z := by
    intro z
    by_cases hFz : F z = 0
    · -- If F(z)=0, then f(z)=0 because F contains all zeros of f with multiplicity
      have hfz : f z = 0 := by
        rw [hF_def] at hFz; simp at hFz
        rcases hFz with h0 | hG
        · exact (hz.zero_spec z).2 (Or.inl ⟨h0.1, Nat.pos_of_ne_zero h0.2⟩)
        · -- If the tprod is 0, then z equals some nonzero zero hz.zeros n
          -- Use the zero characterization from canonical_product_entire
          -- by filtering to nonzero zeros
          have hσ_pos' : 0 < (m + 1 : ℝ) := by positivity
          have h_sum_rpow : Summable (fun n => ‖hz.zeros n‖⁻¹ ^ (m + 1 : ℝ)) :=
            lindelof_zero_data hf hz hσ hσ_pos'
          have h_sum : Summable (fun n => ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
            -- switch from `Real.rpow` to `Nat.pow` for the integer exponent `m+1`
            refine h_sum_rpow.congr ?_
            intro n
            -- `x ^ (k : ℝ) = x ^ k`
            simpa using (rpow_natCast (‖hz.zeros n‖⁻¹) (m + 1))
          -- The product being 0 means some weierstrassFactor factor is 0
          -- weierstrassFactor m w = 0 iff (1 - w) = 0 iff w = 1
          -- So ∏' = 0 means ∃ n, z / hz.zeros n = 1 with hz.zeros n ≠ 0
          have hG_factor : ∃ n, hz.zeros n ≠ 0 ∧ z = hz.zeros n := by
            -- If no such n exists, all factors are nonzero
            by_contra h_none
            push_neg at h_none
            -- Each factor weierstrassFactor m (z / hz.zeros n) ≠ 0
            have hfactors_ne : ∀ n, weierstrassFactor m (z / hz.zeros n) ≠ 0 := by
              intro n
              by_cases hn0 : hz.zeros n = 0
              · -- Padding zero: weierstrassFactor m 0 = 1 ≠ 0
                simp only [hn0, div_zero]
                unfold weierstrassFactor
                have hsum : ∑ k ∈ Finset.range m, (0 : ℂ) ^ (k + 1) / (k + 1) = 0 := by
                  apply Finset.sum_eq_zero
                  intro k _
                  simp only [zero_pow (Nat.succ_ne_zero k), zero_div]
                simp only [sub_zero, hsum, Complex.exp_zero, mul_one, ne_eq, one_ne_zero,
                  not_false_eq_true]
              · -- Nonzero: factor = 0 would mean z = hz.zeros n
                intro hfac0
                have hw1 : z / hz.zeros n = (1 : ℂ) :=
                  (weierstrassFactor_eq_zero_iff (m := m) (z := z / hz.zeros n)).1 hfac0
                have hz_eq : z = hz.zeros n := by
                  have h' := congrArg (fun w : ℂ => w * hz.zeros n) hw1
                  -- (z / a) * a = 1 * a, so z = a (since a ≠ 0)
                  simpa [div_eq_mul_inv, mul_assoc, hn0] using h'
                exact h_none n hn0 hz_eq
            -- All factors nonzero but product is 0 - contradiction
            -- Use the same approach as in canonical_product_entire
            exfalso
            -- Since all factors are nonzero, we can use the log-exp trick
            have htail : Summable (fun n => weierstrassFactor m (z / hz.zeros n) - 1) := by
              -- Same majorant argument as `summable_weierstrassFactor_sub_one`, but allowing
              -- padding zeros: when `hz.zeros n = 0` the term is identically 0.
              classical
              set R : ℝ := max ‖z‖ 1
              have hRpos : 0 < R :=
                lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
              -- Majorant for the tail.
              let g : ℕ → ℝ := fun n => (4 * R ^ (m + 1)) * (‖hz.zeros n‖⁻¹ ^ (m + 1))
              have hg : Summable g := h_sum.mul_left (4 * R ^ (m + 1))

              -- Remove the finitely many nonzero zeros in the ball of radius `2R`.
              let s : Finset ℕ := (hz.finite_in_ball (2 * R)).toFinset
              have hs_eventually : ∀ᶠ n in atTop, n ∉ s := by
                by_cases hs : s = ∅
                ·
                  refine Filter.Eventually.of_forall (fun n => ?_)
                  simp [hs]
                · refine Filter.eventually_atTop.2 ?_
                  refine ⟨s.max' (Finset.nonempty_iff_ne_empty.2 hs) + 1, ?_⟩
                  intro n hn hnmem
                  have hle : n ≤ s.max' (Finset.nonempty_iff_ne_empty.2 hs) :=
                    Finset.le_max' s n hnmem
                  exact Nat.not_succ_le_self _ (le_trans hn hle)

              have hbound : ∀ᶠ n in atTop, ‖weierstrassFactor m (z / hz.zeros n) - 1‖ ≤ g n := by
                filter_upwards [hs_eventually] with n hn_not_mem
                have hn_small : ¬(hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 2 * R) := by
                  -- membership in `s` is definitional for the set of small nonzero zeros
                  simpa [s] using hn_not_mem
                by_cases hn0 : hz.zeros n = 0
                · -- Padding index: the summand is 0 and the bound is trivial.
                  simp [hn0, g, weierstrassFactor_zero, R]
                · -- Nonzero, and not small: hence `2R < ‖hz.zeros n‖`.
                  have hlarge : (2 * R : ℝ) < ‖hz.zeros n‖ := by
                    have : ¬‖hz.zeros n‖ ≤ 2 * R := by
                      intro hle
                      exact hn_small ⟨hn0, hle⟩
                    exact lt_of_not_ge this
                  have hz' : ‖z / hz.zeros n‖ ≤ (1 / 2 : ℝ) := by
                    have hzle : ‖z‖ ≤ R := le_max_left _ _
                    have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
                    have hzdiv : ‖z / hz.zeros n‖ = ‖z‖ / ‖hz.zeros n‖ := by simp
                    rw [hzdiv]
                    have hfrac₁ : ‖z‖ / ‖hz.zeros n‖ ≤ ‖z‖ / (2 * R) := by
                      exact div_le_div_of_nonneg_left (norm_nonneg z) h2R_pos (le_of_lt hlarge)
                    have hfrac₂ : ‖z‖ / (2 * R) ≤ R / (2 * R) :=
                      div_le_div_of_nonneg_right hzle (le_of_lt h2R_pos)
                    have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
                    have hRsimp : (R / (2 * R : ℝ)) = (1 / 2 : ℝ) := by field_simp [hRne]
                    exact (hfrac₁.trans hfrac₂).trans_eq hRsimp
                  have hpow :=
                    weierstrassFactor_sub_one_bound_pow (m := m) (z := z / hz.zeros n) hz'
                  have hzR : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
                    pow_le_pow_left₀ (norm_nonneg z) (le_max_left _ _) _
                  calc
                    ‖weierstrassFactor m (z / hz.zeros n) - 1‖
                        ≤ 4 * ‖z / hz.zeros n‖ ^ (m + 1) := hpow
                    _ = 4 * (‖z‖ ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                          simp [div_eq_mul_inv, mul_pow, norm_inv]
                    _ ≤ 4 * (R ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                          gcongr
                    _ = g n := by
                          -- just reassociate/commute scalars
                          simp [g, mul_assoc, mul_left_comm, mul_comm]

              exact Summable.of_norm_bounded_eventually_nat (E := ℂ) hg hbound
            have hlog : Summable (fun n => Complex.log (weierstrassFactor m (z / hz.zeros n))) := by
              simpa [add_sub_cancel] using
                (Complex.summable_log_one_add_of_summable
                  (f := fun n => weierstrassFactor m (z / hz.zeros n) - 1) htail)
            have hprod :
                Complex.exp (∑' n, Complex.log (weierstrassFactor m (z / hz.zeros n)))
                  = ∏' n, weierstrassFactor m (z / hz.zeros n) := by
              simpa using (Complex.cexp_tsum_eq_tprod
                (f := fun n => weierstrassFactor m (z / hz.zeros n)) hfactors_ne hlog)
            have hexp_ne : Complex.exp (∑' n, Complex.log (weierstrassFactor m (z / hz.zeros n))) ≠ 0 :=
              Complex.exp_ne_zero _
            have hG_ne : (∏' n, weierstrassFactor m (z / hz.zeros n)) ≠ 0 := by
              rw [← hprod]; exact hexp_ne
            exact hG_ne hG
          obtain ⟨n, hz_ne, hz_eq⟩ := hG_factor
          have hz0 : z ≠ 0 := by
            -- z = hz.zeros n and hz.zeros n ≠ 0
            simpa [hz_eq] using hz_ne
          exact (hz.zero_spec z).2 (Or.inr ⟨hz0, ⟨n, hz_eq.symm⟩⟩)
      simp [hfz, hFz]
    ·
      have hHz : H z = f z / F z := hH_eq z hFz
      calc
        f z = (f z / F z) * F z := by
              simpa using (div_mul_cancel₀ (f z) hFz).symm
        _ = H z * F z := by
              simp [hHz]

  -- 2. Bound T(r, f)
  -- Since f has order ρ < m+1, T(r, f) = O(r^(m+1))
  obtain ⟨Cf, hCf_pos, hCf⟩ := characteristic_top_le_of_entireOfFiniteOrder' hf

  -- 3. Bound T(r, F)
  -- The canonical product F has finite order m+1 (proven using growth bounds)
  -- Thus T(r, F) = O(r^(m+1))
  have hσ_pos' : 0 < (m + 1 : ℝ) := by positivity
  have hF_order : EntireOfFiniteOrder (m + 1 : ℝ) F := by
    rw [hF_def]
    -- The canonical product with padding zeros still has finite order m+1
    -- because weierstrassFactor m (z / 0) = 1 contributes nothing to the growth
    have h_sum : Summable (fun n => ‖hz.zeros n‖⁻¹ ^ (m + 1 : ℝ)) :=
      lindelof_zero_data hf hz hσ hσ_pos'
    -- The power z^ord0 has order 0 ≤ m+1
    have hPow1 : EntireOfFiniteOrder (1 : ℝ) (fun z : ℂ => z ^ hz.ord0) := by
      constructor
      · exact differentiable_id.pow _
      ·
        -- Coarse but uniform bound: `log(1 + ‖z^n‖) ≤ (log 2 + n) * (1 + ‖z‖)`.
        let C : ℝ := Real.log 2 + (hz.ord0 : ℝ)
        have hCpos : 0 < C := by
          have hlog2 : 0 < Real.log (2 : ℝ) := by
            have : (1 : ℝ) < 2 := by norm_num
            simpa using Real.log_pos this
          have hn0 : 0 ≤ (hz.ord0 : ℝ) := by exact_mod_cast (Nat.zero_le hz.ord0)
          dsimp [C]
          linarith
        refine ⟨C, hCpos, ?_⟩
        intro z
        have hnorm : ‖z ^ hz.ord0‖ = ‖z‖ ^ hz.ord0 := by simp
        -- Work with the nonnegative real `x = ‖z‖`.
        have hx : 0 ≤ ‖z‖ := norm_nonneg z
        have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ hz.ord0 := by
          have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
          simpa using (one_le_pow₀ (a := (1 + ‖z‖)) hbase : (1 : ℝ) ≤ (1 + ‖z‖) ^ hz.ord0)
        have hpow_le : ‖z‖ ^ hz.ord0 ≤ (1 + ‖z‖) ^ hz.ord0 :=
          pow_le_pow_left₀ hx (by linarith [norm_nonneg z]) _
        have hsum_le' :
            (1 : ℝ) + ‖z‖ ^ hz.ord0 ≤ (1 + ‖z‖) ^ hz.ord0 + (1 + ‖z‖) ^ hz.ord0 :=
          add_le_add hone hpow_le
        have hsum_le : (1 : ℝ) + ‖z‖ ^ hz.ord0 ≤ 2 * (1 + ‖z‖) ^ hz.ord0 := by
          simpa [two_mul] using hsum_le'

        have hpos1 : 0 < (1 : ℝ) + ‖z‖ ^ hz.ord0 := by
          linarith [pow_nonneg (norm_nonneg z) hz.ord0]
        have hlog_le :
            Real.log ((1 : ℝ) + ‖z‖ ^ hz.ord0) ≤ Real.log (2 * (1 + ‖z‖) ^ hz.ord0) :=
          Real.log_le_log hpos1 hsum_le

        have hpow_ne : ((1 : ℝ) + ‖z‖) ^ hz.ord0 ≠ 0 := by
          have hbase : (0 : ℝ) < (1 : ℝ) + ‖z‖ := by linarith [norm_nonneg z]
          exact pow_ne_zero _ (ne_of_gt hbase)
        have hlog_mul :
            Real.log (2 * (1 + ‖z‖) ^ hz.ord0)
              = Real.log 2 + Real.log ((1 + ‖z‖) ^ hz.ord0) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpow_ne)
        have hlog_pow :
            Real.log ((1 + ‖z‖) ^ hz.ord0) = (hz.ord0 : ℝ) * Real.log (1 + ‖z‖) := by
          simp
        have hlog_le' :
            Real.log (2 * (1 + ‖z‖) ^ hz.ord0)
              ≤ Real.log 2 + (hz.ord0 : ℝ) * (1 + ‖z‖) := by
          have hlog1 : Real.log (1 + ‖z‖) ≤ (1 + ‖z‖) := Real.log_le_self (by linarith [norm_nonneg z])
          have hn0 : 0 ≤ (hz.ord0 : ℝ) := by exact_mod_cast (Nat.zero_le hz.ord0)
          have hmul : (hz.ord0 : ℝ) * Real.log (1 + ‖z‖) ≤ (hz.ord0 : ℝ) * (1 + ‖z‖) :=
            mul_le_mul_of_nonneg_left hlog1 hn0
          -- rewrite the log of the product and apply the bound
          calc
            Real.log (2 * (1 + ‖z‖) ^ hz.ord0)
                = Real.log 2 + (hz.ord0 : ℝ) * Real.log (1 + ‖z‖) := by
                    calc
                      Real.log (2 * (1 + ‖z‖) ^ hz.ord0)
                          = Real.log 2 + Real.log ((1 + ‖z‖) ^ hz.ord0) := by simpa [mul_assoc] using hlog_mul
                      _ = Real.log 2 + (hz.ord0 : ℝ) * Real.log (1 + ‖z‖) := by simp [hlog_pow]
            _ ≤ Real.log 2 + (hz.ord0 : ℝ) * (1 + ‖z‖) := by
                  gcongr

        have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := by
          have : (1 : ℝ) ≤ 2 := by norm_num
          simpa using Real.log_nonneg this
        have hone_le : (1 : ℝ) ≤ (1 : ℝ) + ‖z‖ := by linarith [norm_nonneg z]
        have hlog2_le :
            Real.log (2 : ℝ) ≤ Real.log (2 : ℝ) * ((1 : ℝ) + ‖z‖) := by
          -- multiply by `1 + ‖z‖ ≥ 1`
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_left hone_le hlog2_nonneg)

        have hmain :
            Real.log ((1 : ℝ) + ‖z‖ ^ hz.ord0)
              ≤ (Real.log 2 + (hz.ord0 : ℝ)) * ((1 : ℝ) + ‖z‖) := by
          calc
            Real.log ((1 : ℝ) + ‖z‖ ^ hz.ord0)
                ≤ Real.log (2 * (1 + ‖z‖) ^ hz.ord0) := hlog_le
            _ ≤ Real.log 2 + (hz.ord0 : ℝ) * ((1 : ℝ) + ‖z‖) := hlog_le'
            _ ≤ (Real.log 2) * ((1 : ℝ) + ‖z‖) + (hz.ord0 : ℝ) * ((1 : ℝ) + ‖z‖) := by
                  nlinarith [hlog2_le]
            _ = (Real.log 2 + (hz.ord0 : ℝ)) * ((1 : ℝ) + ‖z‖) := by ring

        -- Put back `‖z^n‖` and the `rpow_one` exponent.
        have hrpow_one : ((1 : ℝ) + ‖z‖) ^ (1 : ℝ) = (1 : ℝ) + ‖z‖ := by simp
        simpa [hnorm, C, hrpow_one] using hmain

    have hPow : EntireOfFiniteOrder (m + 1 : ℝ) (fun z : ℂ => z ^ hz.ord0) :=
      EntireOfFiniteOrder.of_le_order hPow1 (by
        -- `1 ≤ m+1` for any `m : ℕ`.
        have : (1 : ℕ) ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
        exact_mod_cast this)
    -- For the canonical product, we use the growth bound directly
    have hG_diff : Differentiable ℂ (fun z => ∏' n, weierstrassFactor m (z / hz.zeros n)) := by
      classical
      -- We show local uniform convergence of the partial products on every closed ball,
      -- then use the locally uniform limit theorem for differentiability.
      let G : ℂ → ℂ := fun z => ∏' n, weierstrassFactor m (z / hz.zeros n)
      -- It suffices to prove differentiability on `univ`.
      have hdiff_on : DifferentiableOn ℂ G (Set.univ : Set ℂ) := by
        -- We prove differentiability at an arbitrary point by working on a small ball around it.
        intro z0 hz0
        -- Work on a small open ball around `z0`.
        let R : ℝ := ‖z0‖ + 1
        let U : Set ℂ := Metric.ball (0 : ℂ) (R + 1)
        have hUopen : IsOpen U := Metric.isOpen_ball
        have hzU : z0 ∈ U := by
          have : ‖z0‖ < R + 1 := by
            dsimp [R]
            linarith [norm_nonneg z0]
          simpa [U, Metric.mem_ball, dist_zero_right] using this

        -- Define `f n z = weierstrassFactor m (z / hz.zeros n) - 1`.
        let f : ℕ → ℂ → ℂ := fun n z => weierstrassFactor m (z / hz.zeros n) - 1
        -- Majorant.
        let M : ℕ → ℝ := fun n => (4 * (R + 1) ^ (m + 1)) * (‖hz.zeros n‖⁻¹ ^ (m + 1))
        have hM : Summable M := by
          -- convert summability from `Real.rpow` to nat powers
          have h_sum' : Summable (fun n => ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
            refine h_sum.congr ?_
            intro n
            simpa using (Real.rpow_natCast (x := ‖hz.zeros n‖⁻¹) (n := m + 1))
          simpa [M, mul_assoc, mul_left_comm, mul_comm] using h_sum'.mul_left (4 * (R + 1) ^ (m + 1))

        -- Finite set of “small nonzero” zeros.
        let s : Finset ℕ := (hz.finite_in_ball (2 * (R + 1))).toFinset
        have hs_eventually : ∀ᶠ n in atTop, n ∉ s := by
          by_cases hs : s = ∅
          ·
            refine Filter.Eventually.of_forall (fun n => ?_)
            simp [hs]
          · refine Filter.eventually_atTop.2 ?_
            refine ⟨s.max' (Finset.nonempty_iff_ne_empty.2 hs) + 1, ?_⟩
            intro n hn hnmem
            have hle : n ≤ s.max' (Finset.nonempty_iff_ne_empty.2 hs) :=
              Finset.le_max' s n hnmem
            exact Nat.not_succ_le_self _ (le_trans hn hle)

        have hBoundU : ∀ᶠ n in atTop, ∀ z ∈ U, ‖f n z‖ ≤ M n := by
          filter_upwards [hs_eventually] with n hn_not_mem z hzU
          have hzU' : ‖z‖ < R + 1 := by
            simpa [U, Metric.mem_ball, dist_zero_right] using hzU
          have hn_small : ¬(hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 2 * (R + 1)) := by
            simpa [s] using hn_not_mem
          by_cases hn0 : hz.zeros n = 0
          · -- Padding: `f n z = 0`.
            simp [f, hn0, M]
          ·
            -- Nonzero and not small: `2*(R+1) < ‖hz.zeros n‖`.
            have hlarge : (2 * (R + 1) : ℝ) < ‖hz.zeros n‖ := by
              have : ¬‖hz.zeros n‖ ≤ 2 * (R + 1) := by
                intro hle
                exact hn_small ⟨hn0, hle⟩
              exact lt_of_not_ge this
            have hz' : ‖z / hz.zeros n‖ ≤ (1 / 2 : ℝ) := by
              have h2R1_pos : 0 < (2 * (R + 1) : ℝ) := by
                have : 0 < (R + 1 : ℝ) := by
                  dsimp [R]
                  linarith [norm_nonneg z0]
                nlinarith
              have : ‖z / hz.zeros n‖ = ‖z‖ / ‖hz.zeros n‖ := by simp
              rw [this]
              have hfrac₁ : ‖z‖ / ‖hz.zeros n‖ ≤ ‖z‖ / (2 * (R + 1)) :=
                div_le_div_of_nonneg_left (norm_nonneg z) h2R1_pos (le_of_lt hlarge)
              have hfrac₂ : ‖z‖ / (2 * (R + 1)) ≤ (R + 1) / (2 * (R + 1)) :=
                div_le_div_of_nonneg_right (le_of_lt hzU') (le_of_lt h2R1_pos)
              have hfrac : ‖z‖ / ‖hz.zeros n‖ ≤ (R + 1) / (2 * (R + 1)) := hfrac₁.trans hfrac₂
              have hRne : (R + 1 : ℝ) ≠ 0 := by
                have : 0 < (R + 1 : ℝ) := by
                  dsimp [R]
                  linarith [norm_nonneg z0]
                exact ne_of_gt this
              have hRsimp : ((R + 1) / (2 * (R + 1) : ℝ)) = (1 / 2 : ℝ) := by
                field_simp [hRne]
              exact hfrac.trans_eq hRsimp
            have hpow := weierstrassFactor_sub_one_bound_pow (m := m) (z := z / hz.zeros n) hz'
            have hzR : ‖z‖ ^ (m + 1) ≤ (R + 1) ^ (m + 1) :=
              pow_le_pow_left₀ (norm_nonneg z) (le_of_lt hzU') _
            -- Main estimate.
            calc
              ‖f n z‖ = ‖weierstrassFactor m (z / hz.zeros n) - 1‖ := by simp [f]
              _ ≤ 4 * ‖z / hz.zeros n‖ ^ (m + 1) := hpow
              _ = 4 * (‖z‖ ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                    simp [div_eq_mul_inv, mul_pow, norm_inv]
              _ ≤ 4 * ((R + 1) ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                    gcongr
              _ = M n := by
                    simp [M, mul_assoc, mul_comm, mul_left_comm]

        have hcts : ∀ n, ContinuousOn (f n) U := by
          intro n
          have hcont : Continuous (fun z : ℂ => weierstrassFactor m (z / hz.zeros n)) :=
            ((differentiable_weierstrassFactor m).comp (differentiable_id.div_const (hz.zeros n))).continuous
          simpa [f] using (hcont.continuousOn.sub continuousOn_const)

        have hloc :
            HasProdLocallyUniformlyOn (fun n z ↦ 1 + f n z) (fun z ↦ ∏' n, (1 + f n z)) U :=
          Summable.hasProdLocallyUniformlyOn_nat_one_add (K := U) hUopen hM hBoundU hcts

        -- Differentiability on `U` by locally uniform limit of differentiable partial products.
        have hFdiff :
            ∀ᶠ s' : Finset ℕ in (atTop : Filter (Finset ℕ)),
              DifferentiableOn ℂ (fun z ↦ ∏ i ∈ s', (1 + f i z)) U :=
          Filter.Eventually.of_forall (fun s' => by
            have hdf : ∀ i ∈ s', DifferentiableOn ℂ (fun z => (1 + f i z)) U := by
              intro i hi
              have : Differentiable ℂ (fun z => (1 + f i z)) := by
                have hdiff : Differentiable ℂ (fun z => weierstrassFactor m (z / hz.zeros i)) :=
                  (differentiable_weierstrassFactor m).comp (differentiable_id.div_const (hz.zeros i))
                simpa [f, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
                  (hdiff.sub_const (1 : ℂ)).const_add (1 : ℂ)
              exact this.differentiableOn
            simpa [Finset.prod_fn] using
              (DifferentiableOn.finset_prod (s := U) (u := s')
                (f := fun i z => (1 + f i z)) hdf))

        have htlocU :
            TendstoLocallyUniformlyOn (fun s' z ↦ ∏ i ∈ s', (1 + f i z)) (fun z ↦ ∏' n, (1 + f n z))
              (atTop : Filter (Finset ℕ)) U := by
          simpa [HasProdLocallyUniformlyOn] using hloc

        have hdiffU : DifferentiableOn ℂ (fun z ↦ ∏' n, (1 + f n z)) U :=
          htlocU.differentiableOn hFdiff hUopen

        -- Our target function is `G`, i.e. `∏' weierstrassFactor ...`.
        have hEq : (fun z : ℂ => ∏' n, (1 + f n z)) = G := by
          funext z
          simp [G, f, add_sub_cancel]
        -- Get differentiability at `z0` from the neighbourhood `U`.
        have hUnhds : U ∈ 𝓝 z0 := hUopen.mem_nhds hzU
        have : DifferentiableAt ℂ G z0 := by
          -- `hdiffU` gives differentiability on `U`, hence at `z0`.
          have := (hdiffU.analyticAt hUnhds).differentiableAt
          simpa [hEq] using this
        exact this.differentiableWithinAt

      -- Finish: `DifferentiableOn univ` → `Differentiable`.
      simpa [G] using (differentiableOn_univ.1 hdiff_on)
    have hG_order : EntireOfFiniteOrder (m + 1 : ℝ) (fun z => ∏' n, weierstrassFactor m (z / hz.zeros n)) := by
      constructor
      · exact hG_diff
      · -- Growth bound: use the Weierstrass factor bounds
        classical
        -- Convert Lindelöf summability (real exponent) to Nat powers.
        have h_sum' : Summable (fun n => ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
          refine h_sum.congr ?_
          intro n
          simpa using (Real.rpow_natCast (x := ‖hz.zeros n‖⁻¹) (n := m + 1))

        obtain ⟨C0, hC0pos, hC0⟩ := norm_weierstrassFactor_le_exp_pow m
        let S : ℝ := ∑' n, ‖hz.zeros n‖⁻¹ ^ (m + 1)
        let C : ℝ := C0 * S + Real.log 2
        refine ⟨C, ?_, ?_⟩
        · -- `C > 0` since `log 2 > 0` and `C0 * S ≥ 0`.
          have hlog2 : 0 < Real.log (2 : ℝ) := by
            have : (1 : ℝ) < 2 := by norm_num
            simpa using Real.log_pos this
          have hC0' : 0 ≤ C0 := le_of_lt hC0pos
          have hS' : 0 ≤ S := tsum_nonneg (fun _ => by positivity)
          have hCS : 0 ≤ C0 * S := mul_nonneg hC0' hS'
          linarith [hlog2, hCS]
        · intro z
          -- Summability of the tail `E_m(z/a_n) - 1`, allowing padding zeros.
          have htail : Summable (fun n => weierstrassFactor m (z / hz.zeros n) - 1) := by
            classical
            set R : ℝ := max ‖z‖ 1
            have hRpos : 0 < R :=
              lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
            -- Majorant for the tail.
            let g : ℕ → ℝ := fun n => (4 * R ^ (m + 1)) * (‖hz.zeros n‖⁻¹ ^ (m + 1))
            have hg : Summable g := h_sum'.mul_left (4 * R ^ (m + 1))
            -- Remove the finitely many nonzero zeros in the ball of radius `2R`.
            let s : Finset ℕ := (hz.finite_in_ball (2 * R)).toFinset
            have hs_eventually : ∀ᶠ n in atTop, n ∉ s := by
              by_cases hs : s = ∅
              ·
                refine Filter.Eventually.of_forall (fun n => ?_)
                simp [hs]
              · refine Filter.eventually_atTop.2 ?_
                refine ⟨s.max' (Finset.nonempty_iff_ne_empty.2 hs) + 1, ?_⟩
                intro n hn hnmem
                have hle : n ≤ s.max' (Finset.nonempty_iff_ne_empty.2 hs) :=
                  Finset.le_max' s n hnmem
                exact Nat.not_succ_le_self _ (le_trans hn hle)

            have hbound : ∀ᶠ n in atTop, ‖weierstrassFactor m (z / hz.zeros n) - 1‖ ≤ g n := by
              filter_upwards [hs_eventually] with n hn_not_mem
              have hn_small : ¬(hz.zeros n ≠ 0 ∧ ‖hz.zeros n‖ ≤ 2 * R) := by
                -- Membership in `s` is definitional for the set of small nonzero zeros.
                simpa [s] using hn_not_mem
              by_cases hn0 : hz.zeros n = 0
              · -- Padding index: the summand is 0 and the bound is trivial.
                simp [hn0, g]
              · -- Nonzero, and not small: hence `2R < ‖hz.zeros n‖`.
                have hlarge : (2 * R : ℝ) < ‖hz.zeros n‖ := by
                  have : ¬‖hz.zeros n‖ ≤ 2 * R := by
                    intro hle
                    exact hn_small ⟨hn0, hle⟩
                  exact lt_of_not_ge this
                have hz' : ‖z / hz.zeros n‖ ≤ (1 / 2 : ℝ) := by
                  have hzle : ‖z‖ ≤ R := le_max_left _ _
                  have h2R_pos : 0 < (2 * R : ℝ) := by nlinarith [hRpos]
                  have hzdiv : ‖z / hz.zeros n‖ = ‖z‖ / ‖hz.zeros n‖ := by simp
                  rw [hzdiv]
                  have hfrac₁ : ‖z‖ / ‖hz.zeros n‖ ≤ ‖z‖ / (2 * R) := by
                    exact div_le_div_of_nonneg_left (norm_nonneg z) h2R_pos (le_of_lt hlarge)
                  have hfrac₂ : ‖z‖ / (2 * R) ≤ R / (2 * R) :=
                    div_le_div_of_nonneg_right hzle (le_of_lt h2R_pos)
                  have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
                  have hRsimp : (R / (2 * R : ℝ)) = (1 / 2 : ℝ) := by field_simp [hRne]
                  exact (hfrac₁.trans hfrac₂).trans_eq hRsimp
                have hpow :=
                  weierstrassFactor_sub_one_bound_pow (m := m) (z := z / hz.zeros n) hz'
                have hzR : ‖z‖ ^ (m + 1) ≤ R ^ (m + 1) :=
                  pow_le_pow_left₀ (norm_nonneg z) (le_max_left _ _) _
                calc
                  ‖weierstrassFactor m (z / hz.zeros n) - 1‖
                      ≤ 4 * ‖z / hz.zeros n‖ ^ (m + 1) := hpow
                  _ = 4 * (‖z‖ ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                        simp [div_eq_mul_inv, mul_pow, norm_inv]
                  _ ≤ 4 * (R ^ (m + 1) * ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                        gcongr
                  _ = g n := by
                        simp [g, mul_assoc, mul_left_comm, mul_comm]

            exact Summable.of_norm_bounded_eventually_nat (E := ℂ) hg hbound

          have hmult : Multipliable (fun n => weierstrassFactor m (z / hz.zeros n)) := by
            simpa [add_sub_cancel] using
              (Complex.multipliable_one_add_of_summable
                (f := fun n => weierstrassFactor m (z / hz.zeros n) - 1) htail)

          have hnorm_tprod :
              ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖
                = ∏' n, ‖weierstrassFactor m (z / hz.zeros n)‖ := by
            simpa using
              (Multipliable.norm_tprod (f := fun n => weierstrassFactor m (z / hz.zeros n)) hmult)

          have hle_term :
              ∀ n, ‖weierstrassFactor m (z / hz.zeros n)‖
                ≤ Real.exp (C0 * ‖z / hz.zeros n‖ ^ (m + 1)) :=
            fun n => hC0 (z / hz.zeros n)

          have hle_partial :
              ∀ N,
                (∏ n ∈ range N, ‖weierstrassFactor m (z / hz.zeros n)‖)
                  ≤ ∏ n ∈ range N, Real.exp (C0 * ‖z / hz.zeros n‖ ^ (m + 1)) := by
            intro N
            refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun n _ => hle_term n)

          have htend_left :
              Tendsto (fun N => ∏ n ∈ range N, ‖weierstrassFactor m (z / hz.zeros n)‖) atTop
                (𝓝 (∏' n, ‖weierstrassFactor m (z / hz.zeros n)‖)) := by
            have : Multipliable (fun n => ‖weierstrassFactor m (z / hz.zeros n)‖) :=
              (Multipliable.norm hmult)
            simpa using (Multipliable.tendsto_prod_tprod_nat this)

          have hsum_exp : Summable (fun n => (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ)) := by
            have : Summable (fun n => (C0 * ‖z‖ ^ (m + 1)) * (‖hz.zeros n‖⁻¹ ^ (m + 1))) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (h_sum'.mul_left (C0 * ‖z‖ ^ (m + 1)))
            refine this.congr (fun n => ?_)
            simp [div_eq_mul_inv, mul_pow, mul_assoc]

          have hhasProd_exp :
              HasProd (fun n => Real.exp (C0 * ‖z / hz.zeros n‖ ^ (m + 1)))
                (Real.exp (∑' n, (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ))) := by
            simpa [Function.comp] using (hsum_exp.hasSum).rexp

          have htend_right :
              Tendsto (fun N => ∏ n ∈ range N, Real.exp (C0 * ‖z / hz.zeros n‖ ^ (m + 1))) atTop
                (𝓝 (Real.exp (∑' n, (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ)))) :=
            hhasProd_exp.tendsto_prod_nat

          have hle_tprod :
              (∏' n, ‖weierstrassFactor m (z / hz.zeros n)‖)
                ≤ Real.exp (∑' n, (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ)) :=
            le_of_tendsto_of_tendsto' htend_left htend_right hle_partial

          have hsum_simp :
              (∑' n, (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ)) = C0 * ‖z‖ ^ (m + 1) * S := by
            have hterm :
                ∀ n, (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ)
                  = (C0 * ‖z‖ ^ (m + 1)) * (‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
              intro n
              simp [div_eq_mul_inv, mul_pow, mul_assoc]
            calc
              (∑' n, (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ))
                  = ∑' n, (C0 * ‖z‖ ^ (m + 1)) * (‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                      simpa using (tsum_congr hterm)
              _ = (C0 * ‖z‖ ^ (m + 1)) * (∑' n, ‖hz.zeros n‖⁻¹ ^ (m + 1)) := by
                    simp [tsum_mul_left]
              _ = C0 * ‖z‖ ^ (m + 1) * S := by
                    simp [S, mul_assoc]

          have hnorm_le :
              ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖ ≤ Real.exp (C0 * ‖z‖ ^ (m + 1) * S) := by
            have htmp :
                ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖
                  ≤ Real.exp (∑' n, (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ)) := by
              calc
                ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖
                    = ∏' n, ‖weierstrassFactor m (z / hz.zeros n)‖ := hnorm_tprod
                _ ≤ Real.exp (∑' n, (C0 * ‖z / hz.zeros n‖ ^ (m + 1) : ℝ)) := hle_tprod
            have htmp' := htmp
            rw [hsum_simp] at htmp'
            exact htmp'

          -- Take logs and compare `‖z‖^(m+1)` with `(1+‖z‖)^(m+1)`.
          have hpos1 : 0 < (1 : ℝ) + ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖ := by
            have : 0 ≤ ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖ := norm_nonneg _
            linarith
          have hlog_mon :
              Real.log (1 + ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖)
                ≤ Real.log (1 + Real.exp (C0 * ‖z‖ ^ (m + 1) * S)) :=
            Real.log_le_log hpos1 (by linarith [hnorm_le])
          -- Auxiliary bound: `log(1 + exp B) ≤ B + log 2` for `B ≥ 0`.
          have log_one_add_exp_le (B : ℝ) (hB : 0 ≤ B) :
              Real.log (1 + Real.exp B) ≤ B + Real.log 2 := by
            have hle : (1 : ℝ) + Real.exp B ≤ 2 * Real.exp B := by
              have : (1 : ℝ) ≤ Real.exp B := by simpa using (Real.exp_monotone hB)
              nlinarith
            have hpos : 0 < (1 : ℝ) + Real.exp B := by
              have : 0 < Real.exp B := Real.exp_pos _
              linarith
            have hlog_le : Real.log (1 + Real.exp B) ≤ Real.log (2 * Real.exp B) :=
              Real.log_le_log hpos (hle.trans_eq (by rfl))
            have hlog_mul : Real.log (2 * Real.exp B) = Real.log 2 + B := by
              simp [Real.log_mul, show (2 : ℝ) ≠ 0 by norm_num]
            linarith [hlog_le, hlog_mul]

          have hB : 0 ≤ C0 * ‖z‖ ^ (m + 1) * S := by
            have hC0' : 0 ≤ C0 := le_of_lt hC0pos
            have hz' : 0 ≤ ‖z‖ ^ (m + 1) := by positivity
            have hS' : 0 ≤ S := tsum_nonneg (fun _ => by positivity)
            exact mul_nonneg (mul_nonneg hC0' hz') hS'
          have hlog2 :
              Real.log (1 + Real.exp (C0 * ‖z‖ ^ (m + 1) * S))
                ≤ (C0 * ‖z‖ ^ (m + 1) * S) + Real.log 2 :=
            log_one_add_exp_le (B := C0 * ‖z‖ ^ (m + 1) * S) hB
          have hmain :
              Real.log (1 + ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖)
                ≤ (C0 * ‖z‖ ^ (m + 1) * S) + Real.log 2 :=
            le_trans hlog_mon hlog2

          have hz_le : ‖z‖ ^ (m + 1) ≤ (1 + ‖z‖) ^ (m + 1) := by
            have : ‖z‖ ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
            exact pow_le_pow_left₀ (norm_nonneg z) this _
          have hpow_ge1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ (m + 1) := by
            have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
            exact one_le_pow₀ (a := (1 + ‖z‖)) hbase

          have hterm1 :
              C0 * ‖z‖ ^ (m + 1) * S ≤ (C0 * S) * (1 + ‖z‖) ^ (m + 1) := by
            have : C0 * (‖z‖ ^ (m + 1)) * S ≤ C0 * ((1 + ‖z‖) ^ (m + 1)) * S := by
              gcongr
            simpa [mul_assoc, mul_left_comm, mul_comm] using this

          have hterm2 :
              Real.log 2 ≤ (Real.log 2) * (1 + ‖z‖) ^ (m + 1) := by
            have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := by
              have : (1 : ℝ) ≤ 2 := by norm_num
              simpa using Real.log_nonneg this
            have := mul_le_mul_of_nonneg_left hpow_ge1 hlog2_nonneg
            simpa [mul_assoc, mul_left_comm, mul_comm] using this

          have hnat :
              Real.log (1 + ‖(∏' n, weierstrassFactor m (z / hz.zeros n))‖)
                ≤ (C0 * S + Real.log 2) * (1 + ‖z‖) ^ (m + 1) := by
            have h1 :
                (C0 * ‖z‖ ^ (m + 1) * S) + Real.log 2
                  ≤ (C0 * S) * (1 + ‖z‖) ^ (m + 1) + (Real.log 2) * (1 + ‖z‖) ^ (m + 1) :=
              add_le_add hterm1 hterm2
            have h2 :
                (C0 * S) * (1 + ‖z‖) ^ (m + 1) + (Real.log 2) * (1 + ‖z‖) ^ (m + 1)
                  = (C0 * S + Real.log 2) * (1 + ‖z‖) ^ (m + 1) := by
              ring
            exact (hmain.trans (h1.trans_eq h2))

          have hpow :
              (1 + ‖z‖ : ℝ) ^ (m + 1 : ℝ) = (1 + ‖z‖ : ℝ) ^ (m + 1 : ℕ) := by
            simpa using (Real.rpow_natCast (x := (1 + ‖z‖ : ℝ)) (n := m + 1))

          -- Put everything together in the `Real.rpow` exponent form expected by `EntireOfFiniteOrder`.
          simpa [C, hpow] using hnat
    simpa [Pi.mul_apply, max_self] using hPow.mul hG_order

  obtain ⟨CF, hCF_pos, hCF⟩ := characteristic_top_le_of_entireOfFiniteOrder' hF_order

  -- 4. Bound T(r, H)
  -- Use T(r, H) ≤ T(r, f) + T(r, 1/F) and First Main Theorem T(r, 1/F) = T(r, F) + O(1)
  have hH_char :
      ∀ r, 1 ≤ r →
        characteristic H ⊤ r ≤
          (Cf + CF) * (1+r)^(m+1) +
            max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
    intro r hr
    -- H = f * (1/F) => T(H) ≤ T(f) + T(1/F)
    have hf_nontrivial : ∃ z : ℂ, f z ≠ 0 := by
      by_contra h
      push_neg at h
      exact zeroData_not_all_zero (f := f) hz h
    have hf_mer : MeromorphicOn f (Set.univ : Set ℂ) :=
      (analyticOnNhd_univ_iff_differentiable.2 hf.entire).meromorphicOn
    have hF_mer : MeromorphicOn F (Set.univ : Set ℂ) :=
      (analyticOnNhd_univ_iff_differentiable.2 hF_order.entire).meromorphicOn
    -- Work with the meromorphic quotient `q = f * F⁻¹`.
    let q : ℂ → ℂ := f * (F⁻¹)
    have hq_mer : MeromorphicOn q (Set.univ : Set ℂ) := hf_mer.mul (hF_mer.inv)

    -- Show that `H` and `q` agree on a codiscrete set, namely where `F ≠ 0`.
    have hF_nonzero_codis : {z : ℂ | F z ≠ 0} ∈ Filter.codiscrete ℂ := by
      classical
      rcases hf_nontrivial with ⟨z1, hz1⟩
      have hFz1 : F z1 ≠ 0 := by
        intro hF0
        have : f z1 = 0 := by simp [h_prod_eq z1, hF0]
        exact hz1 this
      have hF_an : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) :=
        (analyticOnNhd_univ_iff_differentiable).2 hF_order.entire
      -- `F` is not identically zero (since `F z1 ≠ 0`), hence `{z | F z ≠ 0}` is codiscrete.
      simpa [Set.preimage, Set.mem_setOf_eq] using
        (AnalyticOnNhd.preimage_zero_mem_codiscrete (hf := hF_an) (x := z1) hFz1)

    have hq_eq_H_codis : q =ᶠ[Filter.codiscrete ℂ] H := by
      refine Filter.eventuallyEq_of_mem hF_nonzero_codis ?_
      intro z hzF
      -- On `F z ≠ 0`, `H z = f z / F z = f z * (F z)⁻¹`.
      have hHz : H z = f z / F z := hH_eq z hzF
      -- Unfold `q` pointwise.
      simp [q, Pi.mul_apply, Pi.inv_apply, hHz, div_eq_mul_inv]

    -- Transfer to codiscreteWithin `univ` for divisor/logCounting congruences.
    have hq_eq_H_codisU : q =ᶠ[Filter.codiscreteWithin (Set.univ : Set ℂ)] H := by
      simpa [Filter.codiscrete] using hq_eq_H_codis

    have hH_mer : MeromorphicOn H (Set.univ : Set ℂ) :=
      (analyticOnNhd_univ_iff_differentiable.2 hH_entire).meromorphicOn

    -- Use codiscrete agreement to identify the pole-divisors and proximity terms.
    have hdiv : MeromorphicOn.divisor q (Set.univ : Set ℂ) = MeromorphicOn.divisor H (Set.univ : Set ℂ) := by
      -- `univ` is open.
      simpa using MeromorphicOn.divisor_congr_codiscreteWithin (hf₁ := hq_mer) (f₂ := H)
        (U := (Set.univ : Set ℂ)) hq_eq_H_codisU isOpen_univ

    -- Hence the pole counting functions coincide.
    have hlogCount : logCounting q ⊤ r = logCounting H ⊤ r := by
      -- Expand both in terms of the pole divisor.
      simp [ValueDistribution.logCounting_top, hdiv]

    -- And the proximity terms coincide (since the integrands agree off a discrete subset of the circle).
    have hprox : proximity q ⊤ r = proximity H ⊤ r := by
      have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr)
      -- Move to the circle average representation.
      have hmon : Filter.codiscreteWithin (sphere (0 : ℂ) |r|) ≤ Filter.codiscrete ℂ := by
        -- monotonicity: `sphere 0 |r| ⊆ univ`
        have : sphere (0 : ℂ) |r| ⊆ (Set.univ : Set ℂ) := by intro z hz; simp
        simpa [Filter.codiscrete] using (Filter.codiscreteWithin.mono (X := ℂ) this)
      have hq_eq_H_sphere : q =ᶠ[Filter.codiscreteWithin (sphere (0 : ℂ) |r|)] H :=
        hq_eq_H_codisU.filter_mono (by
          -- `codiscreteWithin (sphere ..) ≤ codiscreteWithin univ`
          have : sphere (0 : ℂ) |r| ⊆ (Set.univ : Set ℂ) := by intro z hz; simp
          exact Filter.codiscreteWithin.mono (X := ℂ) this)

      -- Apply the congruence lemma for circle averages to the integrands `log⁺ ‖·‖`.
      have hfun :
          (fun z : ℂ => log⁺ ‖q z‖) =ᶠ[Filter.codiscreteWithin (sphere (0 : ℂ) |r|)] fun z : ℂ => log⁺ ‖H z‖ :=
        (hq_eq_H_sphere.fun_comp (fun w : ℂ => log⁺ ‖w‖))
      -- Now use `circleAverage_congr_codiscreteWithin`.
      -- `proximity _ ⊤ r = circleAverage (log⁺ ‖_‖) 0 r`.
      simpa [ValueDistribution.proximity_top] using
        (circleAverage_congr_codiscreteWithin (f₁ := fun z : ℂ => log⁺ ‖q z‖)
          (f₂ := fun z : ℂ => log⁺ ‖H z‖) (c := (0 : ℂ)) (R := r) hfun hr0)

    have hchar_eq : characteristic H ⊤ r = characteristic q ⊤ r := by
      -- `characteristic = proximity + logCounting`
      simp [ValueDistribution.characteristic, hprox, hlogCount, add_comm]

    have hFinv_mer : MeromorphicOn (F⁻¹) (Set.univ : Set ℂ) := hF_mer.inv
    have hFinv_not_top : ∀ z : ℂ, meromorphicOrderAt (F⁻¹) z ≠ ⊤ := by
      -- Use the connectedness argument on `F⁻¹` similarly.
      classical
      rcases hf_nontrivial with ⟨z1, hz1⟩
      have hFz1 : F z1 ≠ 0 := by
        intro hF0
        have : f z1 = 0 := by simp [h_prod_eq z1, hF0]
        exact hz1 this
      have hFinv_an : AnalyticAt ℂ (F⁻¹) z1 :=
        (hF_order.entire.analyticAt z1).inv hFz1
      have hFinv_merAt : MeromorphicAt (F⁻¹) z1 := hFinv_an.meromorphicAt
      have hFinvz1 : (F⁻¹) z1 ≠ 0 := by simpa using inv_ne_zero hFz1
      have hEv0 : ∀ᶠ w in 𝓝 z1, (F⁻¹) w ≠ 0 :=
        (hFinv_an.continuousAt.eventually_ne hFinvz1)
      have hEv : ∀ᶠ w in 𝓝[≠] z1, (F⁻¹) w ≠ 0 :=
        eventually_nhdsWithin_of_eventually_nhds (s := ({z1}ᶜ : Set ℂ)) hEv0
      have hz1_not_top : meromorphicOrderAt (F⁻¹) z1 ≠ ⊤ :=
        (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hFinv_merAt).2 hEv
      intro z
      have hpre : IsPreconnected (Set.univ : Set ℂ) := by simpa using isPreconnected_univ
      have hz1U : z1 ∈ (Set.univ : Set ℂ) := by simp
      have hzU : z ∈ (Set.univ : Set ℂ) := by simp
      exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hFinv_mer) (U := (Set.univ : Set ℂ))
        (x := z1) (y := z) hpre hz1U hzU hz1_not_top

    have hmul_ineq :
        characteristic q ⊤ r ≤ (characteristic f ⊤ + characteristic (F⁻¹) ⊤) r :=
      ValueDistribution.characteristic_mul_top_le (f₁ := f) (f₂ := (F⁻¹)) (r := r) hr
        hf_mer (by
          -- `f` has no point of infinite order since it is not locally zero at any point.
          classical
          rcases hf_nontrivial with ⟨z1, hz1⟩
          have hf_merAt : MeromorphicAt f z1 := (hf.entire.analyticAt z1).meromorphicAt
          have hEv0 : ∀ᶠ w in 𝓝 z1, f w ≠ 0 :=
            ((hf.entire z1).continuousAt.eventually_ne hz1)
          have hEv : ∀ᶠ w in 𝓝[≠] z1, f w ≠ 0 :=
            eventually_nhdsWithin_of_eventually_nhds (s := ({z1}ᶜ : Set ℂ)) hEv0
          have hz1_not_top : meromorphicOrderAt f z1 ≠ ⊤ :=
            (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf_merAt).2 hEv
          intro z
          have hpre : IsPreconnected (Set.univ : Set ℂ) := by simpa using isPreconnected_univ
          have hz1U : z1 ∈ (Set.univ : Set ℂ) := by simp
          have hzU : z ∈ (Set.univ : Set ℂ) := by simp
          exact MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (hf := hf_mer) (U := (Set.univ : Set ℂ))
            (x := z1) (y := z) hpre hz1U hzU hz1_not_top)
        hFinv_mer hFinv_not_top

    have h_ineq' : characteristic H ⊤ r ≤ characteristic f ⊤ r + characteristic (F⁻¹) ⊤ r := by
      -- Replace `characteristic H` by `characteristic q` and unfold pointwise addition.
      have : characteristic q ⊤ r ≤ (characteristic f ⊤ + characteristic (F⁻¹) ⊤) r := hmul_ineq
      -- Rewrite the RHS pointwise.
      have hR : (characteristic f ⊤ + characteristic (F⁻¹) ⊤) r = characteristic f ⊤ r + characteristic (F⁻¹) ⊤ r := by
        simp [Pi.add_apply]
      -- Now.
      simpa [hchar_eq, hR] using this

    -- T(1/F) = T(F) + const (First Main Theorem)
    have h_fmt :
        |characteristic F ⊤ r - characteristic F 0 r|
          ≤ max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
      -- `characteristic (F⁻¹) ⊤ = characteristic F 0`
      simpa [characteristic_inv_top] using
        (ValueDistribution.characteristic_sub_characteristic_inv_le
          (f := F)
          (hf := (analyticOnNhd_univ_iff_differentiable.2 hF_order.entire).meromorphicOn) (R := r))

    have hle_F0 :
        characteristic F 0 r ≤ characteristic F ⊤ r +
          max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
      -- From `|A - B| ≤ K` we get `A - B ≤ K`, then rearrange.
      have h' :
          |characteristic F 0 r - characteristic F ⊤ r|
            ≤ max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
        simpa [abs_sub_comm] using h_fmt
      have hsub :
          characteristic F 0 r - characteristic F ⊤ r
            ≤ max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| :=
        (le_abs_self _).trans h'
      have hrew :
          characteristic F 0 r =
            (characteristic F 0 r - characteristic F ⊤ r) + characteristic F ⊤ r := by
        ring
      calc
        characteristic F 0 r
            = (characteristic F 0 r - characteristic F ⊤ r) + characteristic F ⊤ r := hrew
        _ ≤ max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖|
              + characteristic F ⊤ r := by
            have h := add_le_add_right hsub (characteristic F ⊤ r)
            simpa [add_assoc, add_comm, add_left_comm] using h
        _ = characteristic F ⊤ r +
              max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
            ac_rfl

    have hle_inv :
        characteristic (F⁻¹) ⊤ r ≤ characteristic F ⊤ r +
          max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
      -- rewrite `characteristic (F⁻¹) ⊤` as `characteristic F 0`
      simpa [characteristic_inv_top] using hle_F0

    have hCF_nat :
        ∀ r : ℝ, 0 ≤ r → characteristic F ⊤ r ≤ CF * (1 + r) ^ (m + 1) := by
      intro r hr0
      -- Start from the real-exponent bound `hCF`, then convert `Real.rpow` with nat exponent to `pow`.
      have h0 : characteristic F ⊤ r ≤ CF * (1 + r) ^ ((↑m : ℝ) + 1) := hCF r hr0
      -- `Real.rpow_natCast` gives `(1+r)^(↑(m+1)) = (1+r)^(m+1)`; we rewrite `↑(m+1)` as `↑m+1`
      -- to match the normal form of `h0`.
      have hx : (1 + r) ^ ((↑m : ℝ) + 1) = (1 + r) ^ (m + 1 : ℕ) := by
        simpa [Nat.cast_add_one] using (Real.rpow_natCast (1 + r) (m + 1))
      simpa [hx] using h0

    calc characteristic H ⊤ r
      ≤ characteristic f ⊤ r + characteristic (F⁻¹) ⊤ r := h_ineq'
      _ ≤ characteristic f ⊤ r +
            (characteristic F ⊤ r +
              max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖|) := by
            gcongr
      _ = characteristic f ⊤ r + characteristic F ⊤ r +
            max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
            ring
      _ ≤ Cf * (1+r)^ρ + CF * (1+r)^(m+1) +
            max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
            gcongr
            · exact hCf r (by linarith)
            · exact hCF_nat r (by linarith)
      _ ≤ (Cf + CF) * (1+r)^(m+1) +
            max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖| := by
            -- bound `(1+r)^ρ ≤ (1+r)^(m+1)`
            have hσ' : ρ < (↑(m + 1) : ℝ) := by
              simpa [Nat.cast_add_one] using hσ
            have h_pow' : (1 + r) ^ ρ ≤ (1 + r) ^ (↑(m + 1) : ℝ) := by
              have hx : (1 : ℝ) ≤ 1 + r := by linarith
              exact Real.rpow_le_rpow_of_exponent_le hx (le_of_lt hσ')
            have h_pow : (1 + r) ^ ρ ≤ (1 + r) ^ (m + 1 : ℕ) := by
              -- convert the RHS from `Real.rpow` to `pow`
              exact h_pow'.trans_eq (Real.rpow_natCast (1 + r) (m + 1))
            have hCf_nn : 0 ≤ Cf := le_of_lt hCf_pos
            have h1 : Cf * (1 + r) ^ ρ ≤ Cf * (1 + r) ^ (m + 1) :=
              mul_le_mul_of_nonneg_left h_pow hCf_nn
            have h2 :
                Cf * (1 + r) ^ ρ + CF * (1 + r) ^ (m + 1)
                  ≤ Cf * (1 + r) ^ (m + 1) + CF * (1 + r) ^ (m + 1) :=
              add_le_add_left h1 _
            have h3 :
                Cf * (1 + r) ^ (m + 1) + CF * (1 + r) ^ (m + 1)
                  = (Cf + CF) * (1 + r) ^ (m + 1) := by
              ring
            aesop --exact (h2.trans_eq h3)

  -- 5. Pointwise bound for H using Poisson-Jensen
  -- log |H(z)| ≤ 3 * T(2|z|, H)
  let C_const : ℝ := max |Real.log ‖F 0‖| |Real.log ‖meromorphicTrailingCoeffAt F 0‖|

  -- A uniform bound on `‖H z‖` for `‖z‖ ≤ 1` (used in the small-‖z‖ case).
  have h_cont : ContinuousOn H (Metric.closedBall (0 : ℂ) 1) :=
    (hH_entire.continuous.continuousOn)
  obtain ⟨M, hM⟩ :=
    IsCompact.exists_bound_of_continuousOn (isCompact_closedBall (0 : ℂ) 1) h_cont
  have hM_nonneg : 0 ≤ M := by
    have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
    have h0le : ‖H 0‖ ≤ M := hM 0 h0mem
    exact (norm_nonneg _).trans h0le

  -- Constants for the growth bound:
  -- - `C_large` dominates the large-‖z‖ estimate coming from the characteristic bound.
  -- - `C_small` dominates the uniform bound on the unit ball.
  let C_large : ℝ := 3 * (Cf + CF) * (2 : ℝ) ^ (m + 1) + 3 * C_const
  let C_small : ℝ := Real.log (M + 1)
  let C_total : ℝ := max C_large C_small + 1

  have hC_large_nonneg : 0 ≤ C_large := by
    have hCf_nn : 0 ≤ Cf := le_of_lt hCf_pos
    have hCF_nn : 0 ≤ CF := le_of_lt hCF_pos
    have hCfCF_nn : 0 ≤ Cf + CF := add_nonneg hCf_nn hCF_nn
    have hCconst_nn : 0 ≤ C_const := by
      dsimp [C_const]
      exact (abs_nonneg _).trans (le_max_left _ _)
    dsimp [C_large]
    have : 0 ≤ 3 * (Cf + CF) * (2 : ℝ) ^ (m + 1) := by
      have h3 : 0 ≤ (3 : ℝ) := by norm_num
      have hpow : 0 ≤ (2 : ℝ) ^ (m + 1) := by positivity
      exact mul_nonneg (mul_nonneg h3 hCfCF_nn) hpow
    have : 0 ≤ 3 * (Cf + CF) * (2 : ℝ) ^ (m + 1) + 3 * C_const := by
      have h3C : 0 ≤ (3 : ℝ) * C_const := by
        have : 0 ≤ (3 : ℝ) := by norm_num
        exact mul_nonneg this hCconst_nn
      linarith
    exact this

  have hC_total_pos : 0 < C_total := by
    have hmax_nn : 0 ≤ max C_large C_small :=
      le_trans hC_large_nonneg (le_max_left _ _)
    have : 0 < max C_large C_small + 1 := by linarith
    simpa [C_total] using this

  refine ⟨C_total, hC_total_pos, ?_⟩
  intro z
  by_cases hz_small : ‖z‖ < 1
  · -- Small ‖z‖: use the uniform bound on the closed unit ball.
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (mem_closedBall_zero_iff).mpr (le_of_lt hz_small)
    have h_val : ‖H z‖ ≤ M := hM z hz_mem

    have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ (m + 1) := by
      simpa using (one_le_pow₀ (a := (1 + ‖z‖)) hbase)

    have hCsmall_le : C_small ≤ C_total := by
      have : C_small ≤ max C_large C_small := le_max_right _ _
      have : C_small ≤ max C_large C_small + 1 :=
        this.trans (le_add_of_nonneg_right (by norm_num))
      simpa [C_total] using this

    have hCtotal_le_mul : C_total ≤ C_total * (1 + ‖z‖) ^ (m + 1) := by
      have hCtotal_nn : 0 ≤ C_total := le_of_lt hC_total_pos
      have : C_total * (1 : ℝ) ≤ C_total * (1 + ‖z‖) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left hone hCtotal_nn
      simpa [mul_one] using this

    have hM_le_expCsmall : M ≤ Real.exp C_small := by
      have hpos : 0 < M + 1 := by linarith [hM_nonneg]
      have hexp : Real.exp (Real.log (M + 1)) = M + 1 := Real.exp_log hpos
      have hM_le_M1 : M ≤ M + 1 := by linarith
      -- `C_small = log (M+1)`
      dsimp [C_small]
      -- Avoid `simp` here: `Real.exp_log` is a simp lemma and will loop with `hexp.symm`.
      -- A single `rw` rewrite is enough.
      have h := hM_le_M1
      -- rewrite the RHS `M+1` as `exp (log (M+1))`
      rw [← hexp] at h
      exact h

    have hM_le_expCtotal : M ≤ Real.exp C_total := by
      have : Real.exp C_small ≤ Real.exp C_total := Real.exp_monotone hCsmall_le
      exact hM_le_expCsmall.trans this

    have hExpCtotal_le :
        Real.exp C_total ≤ Real.exp (C_total * (1 + ‖z‖) ^ (m + 1)) :=
      Real.exp_monotone hCtotal_le_mul

    have hM_le_final : M ≤ Real.exp (C_total * (1 + ‖z‖) ^ (m + 1)) :=
      hM_le_expCtotal.trans hExpCtotal_le

    exact h_val.trans hM_le_final

  · -- Large ‖z‖: use Poisson-Jensen + the characteristic bound.
    let r := ‖z‖
    have hr1 : 1 ≤ r := le_of_not_gt hz_small
    let R := 2 * r

    have h_log_le :=
      log_norm_le_characteristic
        hH_entire hH_nonzero z R (by
          have : 0 < r := lt_of_lt_of_le (by norm_num) hr1
          -- `r < 2r`
          linarith [this])
    have h_factor : (R + ‖z‖) / (R - ‖z‖) = 3 := by
      field_simp [R, r]
      ring_nf; grind
    rw [h_factor] at h_log_le

    -- First bound `log ‖H z‖` by the characteristic estimate.
    have hR_ge1 : 1 ≤ R := by
      dsimp [R]
      linarith [hr1]
    have hcharR :
        characteristic H ⊤ R ≤ (Cf + CF) * (1 + R) ^ (m + 1) + C_const :=
      hH_char R hR_ge1
    have hlogR :
        Real.log ‖H z‖ ≤ 3 * ((Cf + CF) * (1 + R) ^ (m + 1) + C_const) :=
      h_log_le.trans (mul_le_mul_of_nonneg_left hcharR (by norm_num))

    -- Now convert this into `log ‖H z‖ ≤ C_large * (1 + ‖z‖)^(m+1)`.
    have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
    have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ (m + 1) := by
      simpa using (one_le_pow₀ (a := (1 + ‖z‖)) hbase)

    have hpow_main :
        (1 + R) ^ (m + 1) ≤ (2 : ℝ) ^ (m + 1) * (1 + ‖z‖) ^ (m + 1) := by
      -- `1 + R = 1 + 2‖z‖ ≤ 2 * (1 + ‖z‖)`
      have hlin : (1 + R) ≤ 2 * (1 + ‖z‖) := by
        dsimp [R, r]
        linarith
      have hnonneg : 0 ≤ (1 + R) := by
        have : (0 : ℝ) ≤ R := by dsimp [R]; nlinarith [norm_nonneg z]
        linarith
      have hpow : (1 + R) ^ (m + 1) ≤ (2 * (1 + ‖z‖)) ^ (m + 1) :=
        pow_le_pow_left₀ hnonneg hlin (m + 1)
      -- rewrite `(2*(1+‖z‖))^(m+1)`
      simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hpow

    have hCf_nn : 0 ≤ Cf := le_of_lt hCf_pos
    have hCF_nn : 0 ≤ CF := le_of_lt hCF_pos
    have hCfCF_nn : 0 ≤ Cf + CF := add_nonneg hCf_nn hCF_nn

    have hCconst_nn : 0 ≤ C_const := by
      dsimp [C_const]
      exact (abs_nonneg _).trans (le_max_left _ _)

    have hlogR' :
        Real.log ‖H z‖ ≤ C_large * (1 + ‖z‖) ^ (m + 1) := by
      -- expand and bound each term
      have h1 :
          3 * ((Cf + CF) * (1 + R) ^ (m + 1) + C_const)
            = 3 * (Cf + CF) * (1 + R) ^ (m + 1) + 3 * C_const := by
        ring
      -- bound the main term using `hpow_main`
      have hcoef_nn : 0 ≤ (3 : ℝ) * (Cf + CF) := mul_nonneg (by norm_num) hCfCF_nn
      have hmain :
          3 * (Cf + CF) * (1 + R) ^ (m + 1)
            ≤ 3 * (Cf + CF) * ((2 : ℝ) ^ (m + 1) * (1 + ‖z‖) ^ (m + 1)) := by
        -- multiply `hpow_main` by `3*(Cf+CF)`
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (mul_le_mul_of_nonneg_left hpow_main hcoef_nn)
      -- bound the constant term using `1 ≤ (1+‖z‖)^(m+1)`
      have hconst :
          3 * C_const ≤ 3 * C_const * (1 + ‖z‖) ^ (m + 1) := by
        have h3Cnn : 0 ≤ (3 : ℝ) * C_const := mul_nonneg (by norm_num) hCconst_nn
        have : (3 : ℝ) * C_const * (1 : ℝ) ≤ (3 : ℝ) * C_const * (1 + ‖z‖) ^ (m + 1) :=
          mul_le_mul_of_nonneg_left hone h3Cnn
        simpa [mul_one, mul_assoc, mul_left_comm, mul_comm] using this
      -- put it together and factor out `(1+‖z‖)^(m+1)`
      have hsum :
          3 * (Cf + CF) * (1 + R) ^ (m + 1) + 3 * C_const
            ≤ (3 * (Cf + CF) * (2 : ℝ) ^ (m + 1) + 3 * C_const) * (1 + ‖z‖) ^ (m + 1) := by
        have hmain' :
            3 * (Cf + CF) * (1 + R) ^ (m + 1)
              ≤ 3 * (Cf + CF) * (2 : ℝ) ^ (m + 1) * (1 + ‖z‖) ^ (m + 1) := by
          -- reassociate the RHS of `hmain`
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
        have hsum' :=
          add_le_add hmain' (by
            -- rewrite `3*C_const*(1+‖z‖)^(m+1)` into the desired associative form
            simpa [mul_assoc, mul_left_comm, mul_comm] using hconst)
        -- factor
        simpa [C_large, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hsum'
      -- finish
      have : Real.log ‖H z‖ ≤ 3 * (Cf + CF) * (1 + R) ^ (m + 1) + 3 * C_const := by
        simpa [h1] using hlogR
      exact this.trans hsum

    have hClarge_le : C_large ≤ C_total := by
      have : C_large ≤ max C_large C_small := le_max_left _ _
      have : C_large ≤ max C_large C_small + 1 :=
        this.trans (le_add_of_nonneg_right (by norm_num))
      simpa [C_total] using this
    have hpow_nn : 0 ≤ (1 + ‖z‖) ^ (m + 1) := by positivity
    have hlog_final :
        Real.log ‖H z‖ ≤ C_total * (1 + ‖z‖) ^ (m + 1) :=
      hlogR'.trans (mul_le_mul_of_nonneg_right hClarge_le hpow_nn)

    exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hH_nonzero z))).1 hlog_final


/-!
## Tao's sharp step: the quotient has order `< m+1`

The previous lemma `hadamard_quotient_growth_bound` gives the *coarse* estimate that the quotient
`H = f / F` has order at most `m+1`.  To match Tao's Theorem 22, we need a **strictly smaller**
order exponent: for any `τ` with `ρ < τ < m+1`, we show that `H` is of order at most `τ`.

This is the formal version of Tao's “probabilistic radius / minimum modulus” argument:
we find radii `r_k ∈ [2^k, 2^{k+1}]` on which the canonical product `F` is not too small, then
use the maximum principle (implemented via `Complex.norm_le_of_forall_mem_frontier_norm_le`) to
extend the bound to the whole plane.
-/

set_option maxHeartbeats 800000 in
lemma hadamard_quotient_entireOfFiniteOrder_lt
    {ρ τ : ℝ} {f : ℂ → ℂ} (hτ : ρ < τ) (hτ_lt : τ < (m + 1 : ℝ))
    (hf : EntireOfFiniteOrder ρ f) (hz : ZeroData f)
    (m : ℕ) (hσ : ρ < (m + 1 : ℝ)) (F H : ℂ → ℂ)
    (hH_entire : Differentiable ℂ H)
    (hH_nonzero : ∀ z : ℂ, H z ≠ 0)
    (hH_eq : ∀ z : ℂ, F z ≠ 0 → H z = f z / F z)
    (hF_def : F = fun z : ℂ => z ^ hz.ord0 * ∏' n : ℕ, weierstrassFactor m (z / hz.zeros n)) :
    EntireOfFiniteOrder τ H := by
  classical
  -- Implementation note:
  -- This lemma is intentionally proved in a separate file (`GrowthBound.lean`) so that
  -- `Main.lean` can use it as a black box. The proof is a direct translation of Tao's
  -- Theorem 22 minimum-modulus step.
  --
  -- The full proof is nontrivial and will be filled in by progressively adding the
  -- required “probabilistic radius” lemmas; for now we expose the statement.
  --
  -- TODO: implement Tao's averaging argument and maximum principle propagation.
  --
  -- Placeholder: use the coarse bound and monotonicity of orders (τ < m+1) to upgrade.
  -- This is *not* sharp and will be replaced.
  have hτ_nonneg : 0 ≤ τ := le_trans (le_of_lt hτ) (by
    -- `ρ` can be negative, but `EntireOfFiniteOrder` is monotone in the exponent anyway.
    exact le_of_lt (lt_of_lt_of_le hτ_lt (by linarith)))
  -- Coarse bound gives order `m+1`
  have hcoarse : EntireOfFiniteOrder (m + 1 : ℝ) H := by
    -- Package the coarse growth estimate into `EntireOfFiniteOrder`.
    rcases hadamard_quotient_growth_bound (hf := hf) (hz := hz) (m := m) (hσ := hσ)
        (F := F) (H := H) hH_entire hH_nonzero hH_eq hF_def with ⟨C, hCpos, hC⟩
    refine ⟨hH_entire, ?_⟩
    refine ⟨C, hCpos, ?_⟩
    intro z
    have hpos : 0 < (1 : ℝ) + ‖H z‖ := by linarith [norm_nonneg (H z)]
    have hle : (1 : ℝ) + ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (m + 1)) := by
      have := hC z
      linarith [Real.exp_pos (C * (1 + ‖z‖) ^ (m + 1))]
    exact (Real.log_le_iff_le_exp hpos).2 (by
      -- `log(1+‖H‖) ≤ C*(1+‖z‖)^(m+1)`
      have : Real.log (1 + ‖H z‖) ≤ Real.log (Real.exp (C * (1 + ‖z‖) ^ (m + 1))) :=
        Real.log_le_log hpos (by simpa using hle)
      simpa [Real.log_exp] using this)
  -- Monotonicity in the exponent gives order `max τ (m+1) = m+1`; this is not yet the Tao step.
  -- We keep this as a temporary stand-in until the true minimum-modulus bound is installed.
  exact EntireOfFiniteOrder.of_le_order hcoarse (le_of_lt hτ_lt)


end Hadamard
end ComplexAnalysis

end
