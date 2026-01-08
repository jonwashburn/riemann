import Carleson.ToMathlib.ENorm
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.BourbakiWitt
import PrimeNumberTheoremAnd.DerivativeBound
import Riemann.Mathlib.Analysis.Complex.DeBranges.Nevanlinna.HarmonicBounds
import Riemann.academic_framework.HadamardFactorization.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section

namespace ComplexAnalysis
namespace Hadamard

open Complex Real BigOperators Finset Set Filter Topology Metric
open scoped Topology

/-- Borel-Carathéodory bound for entire functions.

If f is analytic on |z| ≤ R with f(0) = 0 and Re(f(z)) ≤ M for all |z| ≤ R,
then |f(z)| ≤ 2Mr/(R-r) for |z| ≤ r < R.

This connects to `borelCaratheodory_closedBall` from StrongPNT. -/
theorem borel_caratheodory_bound {f : ℂ → ℂ} {r R M : ℝ}
    (hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hr : 0 < r) (hR : r < R) (hM : 0 < M)
    (hf0 : f 0 = 0)
    (hf_re : ∀ z, ‖z‖ ≤ R → (f z).re ≤ M) :
    ∀ z, ‖z‖ ≤ r → ‖f z‖ ≤ 2 * M * r / (R - r) := by
  intro z hz
  have hRpos : 0 < R := lt_trans hr hR
  have hAnal : AnalyticOn ℂ f (Metric.closedBall 0 R) := by
    intro w hw
    exact (hf_anal w hw).analyticWithinAt
  have hRe : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M := by
    intro w hw
    have : ‖w‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact hf_re w this
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (borelCaratheodory_closedBall (M := M) (R := R) (r := r) (z := z)
      hRpos hAnal hf0 hM hRe hR hz')

/-- Derivative bound from Borel-Carathéodory.

If f is analytic on |z| ≤ R with f(0) = 0 and Re(f(z)) ≤ M for all |z| ≤ R,
then |f'(z)| ≤ 16MR²/(R-r)³ for |z| ≤ r < R.

This connects to `BorelCaratheodoryDeriv` from StrongPNT. -/
theorem borel_caratheodory_deriv_bound {f : ℂ → ℂ} {r R M : ℝ}
    (hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R))
    (hr : 0 < r) (hR : r < R) (hM : 0 < M)
    (hf0 : f 0 = 0)
    (hf_re : ∀ z, ‖z‖ ≤ R → (f z).re ≤ M) :
    ∀ z, ‖z‖ ≤ r → ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  intro z hz
  have hAnal : AnalyticOn ℂ f (Metric.closedBall 0 R) := by
    intro w hw
    exact (hf_anal w hw).analyticWithinAt
  have hRe : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M := by
    intro w hw
    have : ‖w‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact hf_re w this
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  -- Choose the midpoint radius `r' = (R+r)/2` to get a clean constant.
  set r' : ℝ := (R + r) / 2
  have hr_lt_r' : r < r' := by
    have : r < (R + r) / 2 := by linarith [hR]
    simpa [r'] using this
  have hr'_lt_R : r' < R := by
    have : (R + r) / 2 < R := by linarith [hR]
    simpa [r'] using this
  have hderiv :
      ‖deriv f z‖ ≤ 2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) := by
    simpa using
      (derivativeBound
        (R := R) (M := M) (r := r) (r' := r') (z := z) (f := f)
        hAnal hf0 hM hRe hr hz' hr_lt_r' hr'_lt_R)
  -- Simplify the constant for this choice of `r'`.
  have hconst :
      2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) = 16 * M * r' ^ 2 / (R - r) ^ 3 := by
    have hRr0 : (R - r) ≠ 0 := sub_ne_zero.mpr (ne_of_gt hR)
    have hden1 : R - r' ≠ 0 := ne_of_gt (sub_pos.mpr hr'_lt_R)
    have hden2 : r' - r ≠ 0 := ne_of_gt (sub_pos.mpr hr_lt_r')
    have hRr' : R - r' = (R - r) / 2 := by simp [r']; ring
    have hr'r : r' - r = (R - r) / 2 := by simp [r']; ring
    field_simp [div_eq_mul_inv, hRr0, hden1, hden2]
    simp [hRr', hr'r]
    ring
  have hr'_le_R : r' ≤ R := by
    have : (R + r) / 2 ≤ R := by linarith [le_of_lt hR]
    simpa [r'] using this
  have hr'_sq_le : r' ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (lt_trans hr hr_lt_r')) hr'_le_R 2
  have hden_nn : 0 ≤ (R - r) ^ 3 := pow_nonneg (sub_nonneg.mpr (le_of_lt hR)) 3
  have hMnn : 0 ≤ M := le_of_lt hM
  have hnum : 16 * M * r' ^ 2 ≤ 16 * M * R ^ 2 := by
    have h16M : 0 ≤ 16 * M := by nlinarith [hMnn]
    have := mul_le_mul_of_nonneg_left hr'_sq_le h16M
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hfinal :
      16 * M * r' ^ 2 / (R - r) ^ 3 ≤ 16 * M * R ^ 2 / (R - r) ^ 3 :=
    div_le_div_of_nonneg_right hnum hden_nn
  have : ‖deriv f z‖ ≤ 16 * M * r' ^ 2 / (R - r) ^ 3 := by
    simpa [hconst] using hderiv
  exact le_trans this hfinal

/-- Lindelöf's theorem: finite order implies summability of zero exponents.

If f is entire of order ρ, then for any σ > ρ, the series ∑|aₙ|^{-σ}
converges, where aₙ are the nonzero zeros of f. -/
theorem lindelof_zero_exponent {f : ℂ → ℂ} {ρ σ : ℝ}
    (hf : EntireOfFiniteOrder ρ f)
    (hσ : ρ < σ)
    (hf0 : f 0 ≠ 0)
    (zeros : ℕ → ℂ)
    (h_inj : Function.Injective zeros)
    (h_zeros : ∀ n, f (zeros n) = 0 ∧ zeros n ≠ 0) :
    Summable (fun n => ‖zeros n‖⁻¹ ^ σ) := by
  -- We give a clean Jensen + dyadic-shell proof.
  classical

  -- Step 0: reduce to a nonnegative order.
  have hρ_nonneg : 0 ≤ ρ := by
    by_contra hρ
    have hρneg : ρ < 0 := lt_of_not_ge hρ
    rcases hf.growth with ⟨C, hCpos, hC⟩
    have hbounded : ∃ M, ∀ z : ℂ, ‖f z‖ ≤ M := by
      refine ⟨Real.exp C, ?_⟩
      intro z
      have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
      have hpow : (1 + ‖z‖) ^ ρ ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hbase (le_of_lt hρneg)
      have hlog_le : Real.log (1 + ‖f z‖) ≤ C := by
        have h1 : Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ := hC z
        have h2 : C * (1 + ‖z‖) ^ ρ ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
        have h3 : C * (1 + ‖z‖) ^ ρ ≤ C := by simpa using h2
        exact h1.trans h3
      have hpos : 0 < (1 : ℝ) + ‖f z‖ := by linarith [norm_nonneg (f z)]
      have hle : (1 : ℝ) + ‖f z‖ ≤ Real.exp C := (Real.log_le_iff_le_exp hpos).1 hlog_le
      have hle' : ‖f z‖ ≤ (1 : ℝ) + ‖f z‖ := le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      exact hle'.trans hle
    have hb_range : Bornology.IsBounded (Set.range f) := by
      rcases hbounded with ⟨M, hM⟩
      refine (isBounded_iff_forall_norm_le).2 ?_
      refine ⟨M, ?_⟩
      intro y hy
      rcases hy with ⟨z, rfl⟩
      simpa using hM z
    rcases (Differentiable.exists_eq_const_of_bounded hf.entire hb_range) with ⟨c, hc⟩
    have hz0 : f (zeros 0) = 0 := (h_zeros 0).1
    -- `f` is constant, so `f 0 = f (zeros 0) = 0`, contradicting `f 0 ≠ 0`.
    have : f 0 = f (zeros 0) := by simp [hc]
    exact hf0 (this.trans hz0)

  have hσ_pos : 0 < σ := lt_of_le_of_lt hρ_nonneg hσ

  -- Choose an intermediate exponent `τ` with `ρ ≤ τ < σ`.
  let τ : ℝ := (ρ + σ) / 2
  have hρτ : ρ ≤ τ := by dsimp [τ]; linarith
  have hτσ : τ < σ := by dsimp [τ]; linarith
  have hτ_nonneg : 0 ≤ τ := le_trans hρ_nonneg hρτ

  -- Upgrade to order `τ`, and extract a simple norm bound.
  have hfτ : EntireOfFiniteOrder τ f := EntireOfFiniteOrder.of_le_order hf hρτ
  rcases hfτ.norm_bound with ⟨C, hCpos, hC⟩

  -- Normalize so that `g 0 = 1`.
  let f0 : ℂ := f 0
  let g : ℂ → ℂ := fun z => f z / f0
  have hg_entire : Differentiable ℂ g := by
    simpa [g, f0] using (hfτ.entire.div_const (f 0))
  have hg0 : g 0 = 1 := by
    simp [g, f0, hf0]

  -- A zero-free ball around `0`, hence `r0 ≤ ‖zeros n‖` for all `n`.
  obtain ⟨r0, hr0pos, hr0⟩ :
      ∃ r0 > 0, ∀ z : ℂ, ‖z‖ < r0 → f z ≠ 0 := by
    have hcont : ContinuousAt f 0 := (hfτ.entire 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont.eventually_ne hf0
    rcases Metric.mem_nhds_iff.mp hne with ⟨r, hrpos, hr⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    have : z ∈ Metric.ball (0 : ℂ) r := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hr this

  have hr0_le_norm : ∀ n, r0 ≤ ‖zeros n‖ := by
    intro n
    have hz0 : f (zeros n) = 0 := (h_zeros n).1
    have hnot : ¬ ‖zeros n‖ < r0 := by
      intro hlt
      exact (hr0 (zeros n) hlt) hz0
    exact le_of_not_gt hnot

  -- Dyadic shell index: `k(n) = ⌊logb 2 (‖zeros n‖/r0)⌋₊`.
  let kfun : ℕ → ℕ := fun n => ⌊Real.logb 2 (‖zeros n‖ / r0)⌋₊

  -- Dyadic bounds for `x ≥ 1`.
  have hdyadic_lower :
      ∀ {x : ℝ}, 1 ≤ x → (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
    have hlog_nonneg : 0 ≤ Real.logb 2 x :=
      Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
    have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
      simpa using (Nat.floor_le hlog_nonneg)
    exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
      (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le
  have hdyadic_upper :
      ∀ {x : ℝ}, 1 ≤ x → x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
    have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
    exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
      (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1) (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

  -- For each **nonzero** entry, we have `r0*2^{k(n)} ≤ ‖zeros n‖ < r0*2^{k(n)+1}`.
  have hk_lower : ∀ n, zeros n ≠ 0 → r0 * (2 : ℝ) ^ (kfun n : ℝ) ≤ ‖zeros n‖ := by
    intro n hn0
    have hx1 : (1 : ℝ) ≤ ‖zeros n‖ / r0 := by
      have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
      have : r0 / r0 ≤ ‖zeros n‖ / r0 :=
        div_le_div_of_nonneg_right (hr0_le_norm n) (le_of_lt hr0pos)
      simpa [hr0ne] using this
    have hle : (2 : ℝ) ^ (kfun n : ℝ) ≤ ‖zeros n‖ / r0 := by
      simpa [kfun] using (hdyadic_lower (x := ‖zeros n‖ / r0) hx1)
    have := mul_le_mul_of_nonneg_left hle (le_of_lt hr0pos)
    have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
    have hxEq : r0 * (‖zeros n‖ / r0) = ‖zeros n‖ := by
      field_simp [hr0ne]
    simpa [mul_assoc, hxEq] using this
  have hk_upper : ∀ n, zeros n ≠ 0 → ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := by
    intro n hn0
    have hx1 : (1 : ℝ) ≤ ‖zeros n‖ / r0 := by
      have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
      have : r0 / r0 ≤ ‖zeros n‖ / r0 :=
        div_le_div_of_nonneg_right (hr0_le_norm n) (le_of_lt hr0pos)
      simpa [hr0ne] using this
    have hlt : ‖zeros n‖ / r0 < (2 : ℝ) ^ ((kfun n : ℝ) + 1) := by
      simpa [kfun] using (hdyadic_upper (x := ‖zeros n‖ / r0) hx1)
    have := mul_lt_mul_of_pos_left hlt hr0pos
    have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
    have hxEq : r0 * (‖zeros n‖ / r0) = ‖zeros n‖ := by
      field_simp [hr0ne]
    simpa [mul_assoc, hxEq] using this

  -- Define shells for the partition: `S 0` collects the padding indices with `zeros n = 0`, and
  -- `S (k+1)` collects the nonzero entries whose dyadic index is `k`.
  let S : ℕ → Set ℕ :=
    fun k =>
      match k with
      | 0 => {n : ℕ | zeros n = 0}
      | k + 1 => {n : ℕ | zeros n ≠ 0 ∧ kfun n = k}
  have hS : ∀ n : ℕ, ∃! k : ℕ, n ∈ S k := by
    intro n
    by_cases hn0 : zeros n = 0
    · -- Case: zeros n = 0, so n ∈ S 0
      refine ⟨0, by simp [S, hn0], ?_⟩
      intro k hk
      cases k with
      | zero => rfl
      | succ k =>
          have hk' : zeros n ≠ 0 ∧ kfun n = k := by
            simpa [S] using hk
          exact False.elim (hk'.1 hn0)
    · -- Case: zeros n ≠ 0, so n ∈ S (kfun n + 1)
      refine ⟨kfun n + 1, by simp [S, hn0], ?_⟩
      intro k hk
      cases k with
      | zero =>
          have : zeros n = 0 := by simpa [S] using hk
          exact False.elim (hn0 this)
      | succ k =>
          have hk' : zeros n ≠ 0 ∧ kfun n = k := by
            simpa [S] using hk
          have : k = kfun n := hk'.2.symm
          simp [this]

  -- Nonnegativity of the summand.
  have hnonneg : 0 ≤ fun n : ℕ => ‖zeros n‖⁻¹ ^ σ := by
    intro n
    exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (zeros n))) σ

  -- We apply the partition lemma: it suffices to prove summability of the shell `tsum`s.
  have hshell :
      (∀ k : ℕ, Summable fun n : S k => ‖zeros n.1‖⁻¹ ^ σ) ∧
        Summable fun k : ℕ => ∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ := by
    constructor
    · intro k
      cases k with
      | zero =>
        -- S 0 = {n | zeros n = 0}, so all summands are 0^σ = 0 for σ > 0
        have hsum_zero : ∀ n : S 0, (‖zeros n.1‖⁻¹ : ℝ) ^ σ = 0 := by
          intro n
          have hz : zeros n.1 = 0 := n.2
          simp only [hz, norm_zero, inv_zero]
          exact Real.zero_rpow (ne_of_gt hσ_pos)
        simp_rw [hsum_zero]
        exact summable_zero
      | succ k =>
      -- Each shell S (k+1) is finite: it injects into the set of zeros of `f` in a fixed closed ball.
      classical
      -- We pick radii so that the whole shell `S k` lies inside `‖z‖ ≤ r`.
      -- (For `n ∈ S k` we have `‖zeros n‖ < r0 * 2^(k+1)` by definition of the dyadic shell.)
      let r : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
      let R : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 2)
      have hr : 0 < r := by
        have h2 : 0 < (2 : ℝ) ^ ((k : ℝ) + 1) :=
          Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
        exact mul_pos hr0pos h2
      have hRpos : 0 < R := by
        have h2 : 0 < (2 : ℝ) ^ ((k : ℝ) + 2) :=
          Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
        exact mul_pos hr0pos h2
      have hrR : r < R := by
        -- `R = 2*r`.
        have h2 : (1 : ℝ) < 2 := by norm_num
        have : r < (2 : ℝ) * r := lt_mul_of_one_lt_left hr h2
        -- show `2*r = R`
        have h2pos : 0 < (2 : ℝ) := by norm_num
        have hpow : (2 : ℝ) ^ ((k : ℝ) + 2) = (2 : ℝ) ^ ((k : ℝ) + 1) * (2 : ℝ) := by
          have : (k : ℝ) + 2 = ((k : ℝ) + 1) + 1 := by ring
          calc
            (2 : ℝ) ^ ((k : ℝ) + 2)
                = (2 : ℝ) ^ (((k : ℝ) + 1) + 1) := by simp [this]
            _ = (2 : ℝ) ^ ((k : ℝ) + 1) * (2 : ℝ) ^ (1 : ℝ) := by
                  simpa using (Real.rpow_add h2pos ((k : ℝ) + 1) (1 : ℝ))
            _ = (2 : ℝ) ^ ((k : ℝ) + 1) * (2 : ℝ) := by simp
        have hR_eq : R = (2 : ℝ) * r := by
          dsimp [R, r]
          calc
            r0 * (2 : ℝ) ^ ((k : ℝ) + 2)
                = r0 * ((2 : ℝ) ^ ((k : ℝ) + 1) * (2 : ℝ)) := by
                    simp [hpow]
            _ = (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) := by ring
        simpa [hR_eq] using this
      -- Jensen bound gives a finite set of zeros in `‖z‖ ≤ r`.
      have hg_anal : AnalyticOnNhd ℂ g (Metric.closedBall 0 R) := by
        intro z hz
        exact hg_entire.analyticAt z
      let M0 : ℝ := max 2 (‖f0‖)⁻¹
      have hM0pos : 0 < M0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
      let B : ℝ := Real.exp (C * (1 + R) ^ τ) * M0
      have hB : 1 < B := by
        have hexp : 1 ≤ Real.exp (C * (1 + R) ^ τ) :=
          (Real.one_le_exp_iff).2 (by
            have : 0 ≤ (1 + R : ℝ) ^ τ := by
              exact Real.rpow_nonneg (by linarith [hRpos.le]) τ
            nlinarith [le_of_lt hCpos, this])
        have hM0 : (1 : ℝ) < M0 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
        -- `1 < exp(...) * M0` since `1 ≤ exp(...)` and `1 < M0`.
        have : 1 < (Real.exp (C * (1 + R) ^ τ)) * M0 := by
          -- use `one_lt_mul` with `1 ≤ exp` and `1 < M0`
          exact one_lt_mul (show 1 ≤ Real.exp (C * (1 + R) ^ τ) from hexp) hM0
        simpa [B] using this
      have hg_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B := by
        intro z hzR
        have hfz : ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := hC z
        have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow_le : (1 + ‖z‖ : ℝ) ^ τ ≤ (1 + R) ^ τ :=
          Real.rpow_le_rpow (by positivity) hbase hτ_nonneg
        have hmul_le : C * (1 + ‖z‖) ^ τ ≤ C * (1 + R) ^ τ :=
          mul_le_mul_of_nonneg_left hpow_le (le_of_lt hCpos)
        have hexp_le : Real.exp (C * (1 + ‖z‖) ^ τ) ≤ Real.exp (C * (1 + R) ^ τ) :=
          (Real.exp_le_exp.2 hmul_le)
        have hfz' : ‖f z‖ ≤ Real.exp (C * (1 + R) ^ τ) := hfz.trans hexp_le
        have hf0pos : 0 < ‖f0‖ := norm_pos_iff.mpr hf0
        have hdiv_le :
            ‖g z‖ ≤ Real.exp (C * (1 + R) ^ τ) * (‖f0‖)⁻¹ := by
          have : ‖g z‖ = ‖f z‖ / ‖f0‖ := by simp [g, f0]
          have hdiv :
              ‖f z‖ / ‖f0‖ ≤ Real.exp (C * (1 + R) ^ τ) / ‖f0‖ :=
            div_le_div_of_nonneg_right hfz' (le_of_lt hf0pos)
          simpa [this, div_eq_mul_inv, mul_assoc] using hdiv
        have hM0 : (‖f0‖)⁻¹ ≤ M0 := le_max_right _ _
        have hB' : Real.exp (C * (1 + R) ^ τ) * (‖f0‖)⁻¹ ≤ Real.exp (C * (1 + R) ^ τ) * M0 :=
          mul_le_mul_of_nonneg_left hM0 (le_of_lt (Real.exp_pos _))
        exact le_trans hdiv_le (by simpa [B] using hB')
      rcases jensen_zeros_bound (f := g) (r := r) (R := R) (B := B) hg_anal hr hrR hg0 hB hg_bound
        with ⟨Z, hZ, -⟩
      -- Inject `S (k+1)` into `Z` via `n ↦ zeros n`, using the shell upper bound.
      -- For n ∈ S (k+1), we have zeros n ≠ 0 ∧ kfun n = k, so ‖zeros n‖ < r0*2^(k+1) = r.
      -- We use `Finite.of_injective` into `Z` by mapping every `n ∈ S (k+1)` to zeros n.
      have hmemZ : ∀ n : S (k+1), zeros n.1 ∈ Z := by
        intro n
        -- For n ∈ S (k+1), we have zeros n ≠ 0 ∧ kfun n = k
        have hn_ne : zeros n.1 ≠ 0 := n.2.1
        have hkfun_eq : kfun n.1 = k := n.2.2
        have hn_lower : r0 * (2 : ℝ) ^ (kfun n.1 : ℝ) ≤ ‖zeros n.1‖ := hk_lower n.1 hn_ne
        have hn_upper : ‖zeros n.1‖ < r0 * (2 : ℝ) ^ ((kfun n.1 : ℝ) + 1) := hk_upper n.1 hn_ne
        have hk_eq : (kfun n.1 : ℝ) = (k : ℝ) := by exact_mod_cast hkfun_eq
        have hn_lower' : r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖zeros n.1‖ := by simpa [hk_eq] using hn_lower
        have hn_upper' : ‖zeros n.1‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
          simpa [hk_eq] using hn_upper
        have hle_r : ‖zeros n.1‖ ≤ r := by
          -- With our choice `r = r0 * 2^(k+1)`, this is exactly the dyadic upper bound.
          exact le_of_lt (by simpa [r] using hn_upper')
        have hfz : f (zeros n.1) = 0 := (h_zeros n.1).1
        have hg_z : g (zeros n.1) = 0 := by
          have hf0ne : f0 ≠ 0 := hf0
          simp [g, f0, hfz]
        exact (hZ (zeros n.1)).2 ⟨hle_r, hg_z⟩
      let φ : S (k+1) → Z := fun n => ⟨zeros n.1, hmemZ n⟩
      have hφ_inj : Function.Injective φ := by
        intro a b hab
        have : zeros a.1 = zeros b.1 := congrArg Subtype.val hab
        have : a.1 = b.1 := h_inj this
        ext
        exact this
      have : Finite Z := by infer_instance
      haveI : Finite (S (k+1)) := Finite.of_injective φ hφ_inj
      exact Summable.of_finite
    ·
      -- Shell `tsum` summability: Jensen gives `card(S k) = O((2^k)^τ)`, and dyadic bounds give
      -- `‖zeros n‖^{-σ} = O((2^{-σ})^k)` on shell `k`. Hence the shell sums are dominated by a
      -- geometric series with ratio `2^(τ-σ) < 1`.
      classical
      let log2 : ℝ := Real.log (2 : ℝ)
      have hlog2_pos : 0 < log2 := by
        dsimp [log2]
        exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlog2_ne : log2 ≠ 0 := ne_of_gt hlog2_pos

      let M0 : ℝ := max 2 (‖f0‖)⁻¹
      have hM0_pos : 0 < M0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)

      let q : ℝ := (2 : ℝ) ^ (τ - σ)
      have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hq_lt_one : q < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
          (sub_neg.2 hτσ)
      have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
        summable_geometric_of_lt_one hq_nonneg hq_lt_one

      let qσ : ℝ := (2 : ℝ) ^ (-σ)
      have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hqσ_lt_one : qσ < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
          (by linarith [hσ_pos])
      have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
        summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one

      -- Explicit constants for a geometric majorant.
      let A : ℝ := (C / log2) * (1 + 4 * r0) ^ τ * (r0 ^ (-σ))
      let B : ℝ := ((Real.log M0) / log2 + 1) * (r0 ^ (-σ))
      have hmajor : Summable (fun k : ℕ => A * q ^ k + B * qσ ^ k) :=
        (hgeom_q.mul_left A).add (hgeom_qσ.mul_left B)

      -- We bound the *tail* shell sums `k ↦ ∑' n : S (k+1), ...` by a geometric series, then use
      -- `summable_nat_add_iff` to transfer summability back to `k ↦ ∑' n : S k, ...`.
      refine (summable_nat_add_iff (f := fun k : ℕ => ∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ) 1).1 ?_
      refine Summable.of_nonneg_of_le
        (g := fun k : ℕ => ∑' n : S (k + 1), ‖zeros n.1‖⁻¹ ^ σ)
        (f := fun k : ℕ => A * q ^ k + B * qσ ^ k)
        (fun k => by
          have hnn : ∀ n : S (k + 1), 0 ≤ ‖zeros n.1‖⁻¹ ^ σ := by
            intro n
            exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (zeros n.1))) σ
          exact tsum_nonneg hnn)
        (fun k => by
          -- Fix a shell index `k`.
          -- Jensen bound at radii `r = r0 * 2^(k+1)` and `R = 2*r`.
          let r : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
          let R : ℝ := (2 : ℝ) * r
          have hr : 0 < r := by
            have h2 : 0 < (2 : ℝ) ^ ((k : ℝ) + 1) :=
              Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
            exact mul_pos hr0pos h2
          have hRpos : 0 < R := mul_pos (by norm_num : (0 : ℝ) < 2) hr
          have hrR : r < R := by
            have h2 : (1 : ℝ) < 2 := by norm_num
            simpa [R, mul_assoc] using (lt_mul_of_one_lt_left hr h2)

          have hg_anal : AnalyticOnNhd ℂ g (Metric.closedBall 0 R) := by
            intro z hz
            exact hg_entire.analyticAt z
          let Bk : ℝ := Real.exp (C * (1 + R) ^ τ) * M0
          have hBk : 1 < Bk := by
            have hexp : 1 ≤ Real.exp (C * (1 + R) ^ τ) :=
              (Real.one_le_exp_iff).2 (by
                have : 0 ≤ (1 + R : ℝ) ^ τ := Real.rpow_nonneg (by linarith [hRpos.le]) τ
                nlinarith [le_of_lt hCpos, this])
            have hM0 : (1 : ℝ) < M0 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
            have : 1 < Real.exp (C * (1 + R) ^ τ) * M0 := one_lt_mul hexp hM0
            simpa [Bk] using this
          have hg_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ Bk := by
            intro z hzR
            have hfz : ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ τ) := hC z
            have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
            have hpow_le : (1 + ‖z‖ : ℝ) ^ τ ≤ (1 + R) ^ τ :=
              Real.rpow_le_rpow (by positivity) hbase hτ_nonneg
            have hmul_le : C * (1 + ‖z‖) ^ τ ≤ C * (1 + R) ^ τ :=
              mul_le_mul_of_nonneg_left hpow_le (le_of_lt hCpos)
            have hexp_le : Real.exp (C * (1 + ‖z‖) ^ τ) ≤ Real.exp (C * (1 + R) ^ τ) :=
              (Real.exp_le_exp.2 hmul_le)
            have hfz' : ‖f z‖ ≤ Real.exp (C * (1 + R) ^ τ) := hfz.trans hexp_le
            have hf0pos : 0 < ‖f0‖ := norm_pos_iff.mpr hf0
            have hdiv_le :
                ‖g z‖ ≤ Real.exp (C * (1 + R) ^ τ) * (‖f0‖)⁻¹ := by
              have : ‖g z‖ = ‖f z‖ / ‖f0‖ := by simp [g, f0]
              have hdiv :
                  ‖f z‖ / ‖f0‖ ≤ Real.exp (C * (1 + R) ^ τ) / ‖f0‖ :=
                div_le_div_of_nonneg_right hfz' (le_of_lt hf0pos)
              simpa [this, div_eq_mul_inv, mul_assoc] using hdiv
            have hM0' : (‖f0‖)⁻¹ ≤ M0 := le_max_right _ _
            have hBk' :
                Real.exp (C * (1 + R) ^ τ) * (‖f0‖)⁻¹ ≤ Real.exp (C * (1 + R) ^ τ) * M0 :=
              mul_le_mul_of_nonneg_left hM0' (le_of_lt (Real.exp_pos _))
            exact le_trans hdiv_le (by simpa [Bk] using hBk')

          rcases jensen_zeros_bound (f := g) (r := r) (R := R) (B := Bk) hg_anal hr hrR hg0 hBk hg_bound
            with ⟨Z, hZ, hZcard⟩

          -- Inject `S (k+1)` into `↥Z`.
          let φ : S (k+1) → Z := fun n => by
            refine ⟨zeros n.1, ?_⟩
            -- For n ∈ S (k+1), we have zeros n ≠ 0 ∧ kfun n = k
            have hn_ne : zeros n.1 ≠ 0 := n.2.1
            have hkfun_eq : kfun n.1 = k := n.2.2
            have hn_upper : ‖zeros n.1‖ < r0 * (2 : ℝ) ^ ((kfun n.1 : ℝ) + 1) := hk_upper n.1 hn_ne
            have hk_eq : (kfun n.1 : ℝ) = (k : ℝ) := by exact_mod_cast hkfun_eq
            have hn_upper' : ‖zeros n.1‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
              simpa [hk_eq] using hn_upper
            have hle_r : ‖zeros n.1‖ ≤ r := by
              exact le_of_lt (by simpa [r] using hn_upper')
            have hfz : f (zeros n.1) = 0 := (h_zeros n.1).1
            have hg_z : g (zeros n.1) = 0 := by
              have hf0ne : f0 ≠ 0 := hf0
              simp [g, f0, hfz]
            exact (hZ (zeros n.1)).2 ⟨hle_r, hg_z⟩
          have hφ_inj : Function.Injective φ := by
            intro a b hab
            have : zeros a.1 = zeros b.1 := congrArg Subtype.val hab
            have : a.1 = b.1 := h_inj this
            ext
            exact this
          classical
          -- `S (k+1)` is finite since it injects into the finite type `Z`.
          haveI : Finite (S (k+1)) := Finite.of_injective φ hφ_inj
          letI : Fintype (S (k+1)) := Fintype.ofFinite (S (k+1))

          have hcard_nat : Fintype.card (S (k+1)) ≤ Z.card := by
            -- `Fintype.card_le_of_injective` gives the inequality with the codomain cardinality as a
            -- `Fintype.card`; rewrite it to `Finset.card` using `Fintype.card_coe`.
            simpa [Fintype.card_coe] using (Fintype.card_le_of_injective φ hφ_inj)
          have hcard_Z : (Z.card : ℝ) ≤ Real.log Bk / log2 + 1 := by
            have hx_nonneg : 0 ≤ Real.log Bk / log2 := by
              have : 0 ≤ Real.log Bk := le_of_lt (Real.log_pos hBk)
              exact div_nonneg this (le_of_lt hlog2_pos)
            have hceil_le :
                (Nat.ceil (Real.log Bk / Real.log (R / r)) : ℝ)
                  ≤ Real.log Bk / log2 + 1 := by
              -- `R/r = 2`
              have hrat : R / r = (2 : ℝ) := by
                have hrne : r ≠ 0 := ne_of_gt hr
                simp [R, hrne, div_eq_mul_inv]
              have hx_nonneg' : 0 ≤ Real.log Bk / Real.log (R / r) := by
                have hlogBk_nonneg : 0 ≤ Real.log Bk := le_of_lt (Real.log_pos hBk)
                have hlogRr_pos : 0 < Real.log (R / r) := by simpa [hrat, log2] using hlog2_pos
                exact div_nonneg hlogBk_nonneg (le_of_lt hlogRr_pos)
              have hlt := Nat.ceil_lt_add_one (R := ℝ) (a := Real.log Bk / Real.log (R / r)) hx_nonneg'
              have hle : (Nat.ceil (Real.log Bk / Real.log (R / r)) : ℝ)
                  ≤ Real.log Bk / Real.log (R / r) + 1 := le_of_lt hlt
              -- replace denominator with `log2`
              simpa [hrat, log2] using hle
            have hZcard' : (Z.card : ℝ) ≤ (Nat.ceil (Real.log Bk / Real.log (R / r)) : ℝ) := by
              exact_mod_cast hZcard
            exact hZcard'.trans hceil_le

          have hcard_S : (Fintype.card (S (k+1)) : ℝ) ≤ Real.log Bk / log2 + 1 := by
            have : (Fintype.card (S (k+1)) : ℝ) ≤ (Z.card : ℝ) := by exact_mod_cast hcard_nat
            exact this.trans hcard_Z

          -- Dyadic lower bound: on shell `k+1`, all zeros satisfy `r0 * 2^k ≤ ‖zero‖`.
          -- (For n ∈ S (k+1), kfun n = k, so the lower bound is r0 * 2^k)
          let t : ℝ := r0 * (2 : ℝ) ^ (k : ℕ)
          have ht_pos : 0 < t := by
            have h2 : 0 < (2 : ℝ) ^ (k : ℕ) := by positivity
            exact mul_pos hr0pos h2
          have hterm_le : ∀ n : S (k+1), ‖zeros n.1‖⁻¹ ^ σ ≤ t⁻¹ ^ σ := by
            intro n
            -- For n ∈ S (k+1), we have zeros n ≠ 0 ∧ kfun n = k
            have hn_ne : zeros n.1 ≠ 0 := n.2.1
            have hkfun_eq : kfun n.1 = k := n.2.2
            have hn_lower : r0 * (2 : ℝ) ^ (kfun n.1 : ℝ) ≤ ‖zeros n.1‖ := hk_lower n.1 hn_ne
            have hk_eq : (kfun n.1 : ℝ) = (k : ℝ) := by exact_mod_cast hkfun_eq
            have hn_lower' : r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖zeros n.1‖ := by simpa [hk_eq] using hn_lower
            have hkpow : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ (k : ℕ) := by
              simp
            have hn_lower'' : t ≤ ‖zeros n.1‖ := by simpa [t, hkpow] using hn_lower'
            have hb : 0 < ‖zeros n.1‖ := norm_pos_iff.2 hn_ne
            have hinv : ‖zeros n.1‖⁻¹ ≤ t⁻¹ :=
              (inv_le_inv₀ (a := ‖zeros n.1‖) (b := t) hb ht_pos).2 hn_lower''
            have h0 : 0 ≤ ‖zeros n.1‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
            exact Real.rpow_le_rpow h0 hinv (le_of_lt hσ_pos)

          -- Turn the `tsum` into a finite sum and bound by `card * bound`.
          have hshell_sum :
              (∑' n : S (k+1), ‖zeros n.1‖⁻¹ ^ σ) ≤ (Fintype.card (S (k+1)) : ℝ) * (t⁻¹ ^ σ) := by
            classical
            simp [tsum_fintype]
            have h' : ∀ n ∈ (Finset.univ : Finset (S (k+1))), ‖zeros n.1‖⁻¹ ^ σ ≤ t⁻¹ ^ σ := by
              intro n hn
              exact hterm_le n
            have := Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (S (k+1))))
              (f := fun n : S (k+1) => ‖zeros n.1‖⁻¹ ^ σ) (n := t⁻¹ ^ σ) h'
            simpa [nsmul_eq_mul] using this

          -- Rewrite `t⁻¹ ^ σ` as `r0^(-σ) * (2^(-σ))^k`.
          have ht_scale : t⁻¹ ^ σ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
            -- (r0*2^k)^{-σ} identity
            have hr0_le : 0 ≤ r0 := le_of_lt hr0pos
            have h2pow : 0 ≤ (2 : ℝ) ^ (k : ℕ) := by positivity
            have hxnonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℕ) := mul_nonneg hr0_le h2pow
            -- unfold t
            dsimp [t]
            calc
              (r0 * (2 : ℝ) ^ (k : ℕ))⁻¹ ^ σ
                  = ((r0 * (2 : ℝ) ^ (k : ℕ)) ^ σ)⁻¹ := Real.inv_rpow hxnonneg σ
              _ = (r0 * (2 : ℝ) ^ (k : ℕ)) ^ (-σ) := by
                    simpa using (Real.rpow_neg hxnonneg σ).symm
              _ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (k : ℕ)) ^ (-σ) := by
                    simp [Real.mul_rpow hr0_le h2pow]
              _ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
                    -- `((2^k)^(-σ)) = (2^(-σ))^k`
                    have h2 : 0 ≤ (2 : ℝ) := by norm_num
                    have hk'' : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k := by
                      simp
                    have hpow' : ((2 : ℝ) ^ k) ^ (-σ) = ((2 : ℝ) ^ (-σ)) ^ k := by
                      calc
                        ((2 : ℝ) ^ k) ^ (-σ) = ((2 : ℝ) ^ (k : ℝ)) ^ (-σ) := by simp [hk'']
                        _ = (2 : ℝ) ^ ((k : ℝ) * (-σ)) := by
                              have := Real.rpow_mul h2 (k : ℝ) (-σ)
                              simpa [mul_comm] using this.symm
                        _ = (2 : ℝ) ^ ((-σ) * (k : ℝ)) := by ring_nf
                        _ = ((2 : ℝ) ^ (-σ)) ^ (k : ℝ) := by
                              simpa [Real.rpow_mul h2] using (Real.rpow_mul h2 (-σ) (k : ℝ))
                        _ = ((2 : ℝ) ^ (-σ)) ^ k := by
                              simp
                    simp [hpow']

          -- Bound the RHS by the geometric majorant.
          have : (Fintype.card (S (k+1)) : ℝ) * (t⁻¹ ^ σ)
              ≤ A * q ^ k + B * qσ ^ k := by
            -- Use `card ≤ log Bk/log2 + 1` and bound `log Bk` by growth.
            have hlogBk : Real.log Bk = C * (1 + R) ^ τ + Real.log M0 := by
              have hexp_pos : 0 < Real.exp (C * (1 + R) ^ τ) := Real.exp_pos _
              have hlog_mul : Real.log (Real.exp (C * (1 + R) ^ τ) * M0)
                    = Real.log (Real.exp (C * (1 + R) ^ τ)) + Real.log M0 := by
                exact Real.log_mul (ne_of_gt hexp_pos) (ne_of_gt hM0_pos)
              simp [Bk, hlog_mul]
            have hcard_le' :
                (Fintype.card (S (k+1)) : ℝ)
                  ≤ (C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1 := by
              -- rewrite `log Bk / log2`
              have : Real.log Bk / log2 = (C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 := by
                calc
                  Real.log Bk / log2 = (C * (1 + R) ^ τ + Real.log M0) / log2 := by simp [hlogBk]
                  _ = (C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 := by
                        field_simp [hlog2_ne]
              -- use `hcard_S` above
              have hcard_S' : (Fintype.card (S (k+1)) : ℝ) ≤ Real.log Bk / log2 + 1 := hcard_S
              -- substitute
              simpa [this, add_assoc, add_left_comm, add_comm] using hcard_S'

            -- Bound `(1+R)^τ` by `((1+4*r0)^τ) * ((2^k)^τ)`.
            have hR_le : (1 : ℝ) + R ≤ (1 + 4 * r0) * (2 : ℝ) ^ k := by
              -- `R = 2*r = 4*r0*2^k` and `1 ≤ 2^k`.
              have hk1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
              have h2pow2 : (2 : ℝ) ^ ((k : ℝ) + 1) = (2 : ℝ) * (2 : ℝ) ^ k := by
                have h2 : (0 : ℝ) < 2 := by norm_num
                calc
                  (2 : ℝ) ^ ((k : ℝ) + 1)
                      = (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
                          simpa using (Real.rpow_add h2 (k : ℝ) (1 : ℝ))
                  _ = (2 : ℝ) ^ k * (2 : ℝ) := by
                        have hk' : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k := by
                          simp
                        simp [hk']
                  _ = (2 : ℝ) * (2 : ℝ) ^ k := by ring
              have hR_eq : R = (4 * r0) * (2 : ℝ) ^ k := by
                -- unfold `R` and `r`, and use `2^(k+1) = 2*2^k`.
                dsimp [R, r]
                -- `R = 2 * r0 * 2^(k+1) = 4*r0*2^k`
                calc
                  (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
                      = (2 : ℝ) * (r0 * ((2 : ℝ) * (2 : ℝ) ^ k)) := by simp [h2pow2]
                  _ = (4 * r0) * (2 : ℝ) ^ k := by ring
              calc
                (1 : ℝ) + R = 1 + (4 * r0) * (2 : ℝ) ^ k := by simp [hR_eq]
                _ ≤ (2 : ℝ) ^ k + (4 * r0) * (2 : ℝ) ^ k := by gcongr
                _ = (1 + 4 * r0) * (2 : ℝ) ^ k := by ring

            have hpow_le : ((1 : ℝ) + R) ^ τ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ τ :=
              Real.rpow_le_rpow (by positivity) hR_le hτ_nonneg
            have hsplit :
                ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ τ
                  = (1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ := by
              have hbase1 : 0 ≤ (1 + 4 * r0 : ℝ) := by linarith [le_of_lt hr0pos]
              have hbase2 : 0 ≤ (2 : ℝ) ^ k := by positivity
              simp [Real.mul_rpow hbase1 hbase2]
            have hpow_le' : ((1 : ℝ) + R) ^ τ ≤ (1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ :=
              le_trans hpow_le (by simp [hsplit])

            -- Convert `((2^k)^τ)` to `((2^τ)^k)` and combine with `qσ^k`.
            have h2powτ : ((2 : ℝ) ^ k) ^ τ = ((2 : ℝ) ^ τ) ^ k := by
              have h2 : 0 ≤ (2 : ℝ) := by norm_num
              have hk' : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ k := by
                simp
              calc
                ((2 : ℝ) ^ k) ^ τ = ((2 : ℝ) ^ (k : ℝ)) ^ τ := by simp [hk']
                _ = (2 : ℝ) ^ ((k : ℝ) * τ) := by
                      have := Real.rpow_mul h2 (k : ℝ) τ
                      simpa [mul_comm] using this.symm
                _ = (2 : ℝ) ^ (τ * (k : ℝ)) := by ring_nf
                _ = ((2 : ℝ) ^ τ) ^ k := by
                      have hr' : (2 : ℝ) ^ (τ * (k : ℝ)) = ((2 : ℝ) ^ τ) ^ (k : ℝ) := by
                        simp [Real.rpow_mul h2]
                      have hn : ((2 : ℝ) ^ τ) ^ (k : ℝ) = ((2 : ℝ) ^ τ) ^ k := by
                        simp
                      exact hr'.trans hn
            have hq : q = (2 : ℝ) ^ τ * (2 : ℝ) ^ (-σ) := by
              have h2pos : (0 : ℝ) < 2 := by norm_num
              have : (τ - σ) = τ + (-σ) := by ring
              calc
                q = (2 : ℝ) ^ (τ + (-σ)) := by simp [q, this]
                _ = (2 : ℝ) ^ τ * (2 : ℝ) ^ (-σ) := by
                      simpa using (Real.rpow_add h2pos τ (-σ))
            have hq_pow : q ^ k = ((2 : ℝ) ^ τ) ^ k * ((2 : ℝ) ^ (-σ)) ^ k := by
              simp [hq, mul_pow]

            -- rewrite `t⁻¹ ^ σ` into `r0^(-σ) * qσ^k`
            have ht_scale' : t⁻¹ ^ σ = (r0 ^ (-σ)) * qσ ^ k := by simp [qσ, ht_scale]

            -- Now a direct domination by the majorant (algebraic bookkeeping).
            -- First expand the left-hand side using the card bound.
            have hL :
                (Fintype.card (S (k+1)) : ℝ) * (t⁻¹ ^ σ)
                  ≤ ((C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (t⁻¹ ^ σ) := by
              exact mul_le_mul_of_nonneg_right hcard_le' (by
                have : 0 ≤ t⁻¹ ^ σ := Real.rpow_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hr0pos) (by positivity))) σ
                exact this)
            -- rewrite scale
            rw [ht_scale'] at hL ⊢
            -- and bound the growth term `(1+R)^τ`
            -- `((C*(1+R)^τ)/log2) * r0^{-σ} * qσ^k ≤ A * q^k`
            have hstep1 :
                ((C * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k) ≤ A * q ^ k := by
              have hdiv_nonneg : 0 ≤ C / log2 := div_nonneg (le_of_lt hCpos) (le_of_lt hlog2_pos)
              have hnonneg_r0 : 0 ≤ r0 ^ (-σ) := Real.rpow_nonneg (le_of_lt hr0pos) _
              have hnonneg_qσk : 0 ≤ qσ ^ k := pow_nonneg hqσ_nonneg k
              -- `((1+R)^τ) * qσ^k ≤ (1+4*r0)^τ * q^k`
              have hgrow : (1 + R) ^ τ * (qσ ^ k) ≤ (1 + 4 * r0) ^ τ * (q ^ k) := by
                -- use `hpow_le'` and the identities for powers
                have hqk' : q ^ k = ((2 : ℝ) ^ τ) ^ k * (qσ ^ k) := by
                  simp [q, qσ, hq, mul_pow, mul_comm]
                calc
                  (1 + R) ^ τ * (qσ ^ k)
                      ≤ ((1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ) * (qσ ^ k) := by
                          gcongr
                  _ = (1 + 4 * r0) ^ τ * (((2 : ℝ) ^ k) ^ τ * (qσ ^ k)) := by ring
                  _ = (1 + 4 * r0) ^ τ * (((2 : ℝ) ^ τ) ^ k * (qσ ^ k)) := by
                        simp [h2powτ]
                  _ = (1 + 4 * r0) ^ τ * (q ^ k) := by simp [hqk']
              -- now multiply by nonneg constants
              calc
                ((C * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k)
                    = (C / log2) * ((1 + R) ^ τ * (qσ ^ k)) * (r0 ^ (-σ)) := by
                        field_simp [hlog2_ne]
                _ ≤ (C / log2) * ((1 + 4 * r0) ^ τ * (q ^ k)) * (r0 ^ (-σ)) := by
                      gcongr
                _ = A * q ^ k := by
                      simp [A, mul_assoc, mul_left_comm, mul_comm]
            have hstep2 :
                ((Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k) ≤ B * qσ ^ k := by
              simp [B, mul_assoc, mul_left_comm, mul_comm]
            -- put it together
            have hsum :
                ((C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k)
                  ≤ A * q ^ k + B * qσ ^ k := by
              -- split the scalar sum into two and use the step bounds
              calc
                ((C * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k)
                    = ((C * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k)
                        + ((Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k) := by ring
                _ ≤ A * q ^ k + B * qσ ^ k := by
                      gcongr
            exact le_trans hL hsum

          -- chain everything
          exact le_trans hshell_sum this
        ) hmajor

  -- Conclude from `summable_partition`.
  have := (summable_partition (f := fun n : ℕ => ‖zeros n‖⁻¹ ^ σ) hnonneg (s := S) hS)
  exact (this.2 hshell)

/-- The quotient of entire functions f/G is entire when G has the same zeros.

If f and G are entire with the same zeros (counting multiplicity), and G(z) ≠ 0
for z not a zero of f, then f/G extends to an entire function. -/
theorem quotient_entire {f G : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hG : Differentiable ℂ G)
    (hG_nontrivial : ∃ z, G z ≠ 0)
    (h_ord : ∀ z : ℂ, analyticOrderAt G z ≤ analyticOrderAt f z) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ ∀ z, G z ≠ 0 → H z = f z / G z := by
  classical
  -- Define the quotient on the punctured neighbourhoods.
  let q : ℂ → ℂ := fun z ↦ f z / G z
  -- Fill in the removable singularities by taking the `limUnder` at each potential pole.
  let H : ℂ → ℂ := fun z ↦ if hz : G z = 0 then limUnder (𝓝[≠] z) q else q z
  refine ⟨H, ?_, ?_⟩
  · -- `H` is entire: check differentiability at each point.
    intro z0
    by_cases hz0 : G z0 = 0
    · -- Removable singularity at `z0`.
      have hf_an : AnalyticAt ℂ f z0 := (hf.analyticAt z0)
      have hG_an : AnalyticAt ℂ G z0 := (hG.analyticAt z0)
      -- `G` is not locally zero anywhere, otherwise it would be identically zero.
      have hG_not_eventually_zero : ¬ (∀ᶠ z in 𝓝 z0, G z = 0) := by
        intro hloc
        have hG_univ : AnalyticOnNhd ℂ G (Set.univ : Set ℂ) :=
          (analyticOnNhd_univ_iff_differentiable).2 hG
        have hfreq : ∃ᶠ z in 𝓝[≠] z0, G z = 0 :=
          (hloc.filter_mono nhdsWithin_le_nhds).frequently
        have hEq : Set.EqOn G 0 (Set.univ : Set ℂ) :=
          AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
            (f := G) (U := (Set.univ : Set ℂ)) hG_univ (by simpa using isPreconnected_univ)
            (by simp) hfreq
        rcases hG_nontrivial with ⟨w, hw⟩
        exact hw (by simpa using hEq (by simp : w ∈ (Set.univ : Set ℂ)))
      -- Hence `G` is eventually nonzero on a punctured neighbourhood of `z0`.
      have hG_ne : ∀ᶠ z in 𝓝[≠] z0, G z ≠ 0 :=
        (hG_an.eventually_eq_zero_or_eventually_ne_zero).resolve_left hG_not_eventually_zero

      -- On a punctured neighbourhood of `z0`, `H = q`.
      have hH_eq_q : ∀ᶠ z in 𝓝[≠] z0, H z = q z := by
        filter_upwards [hG_ne] with z hz
        simp [H, q, hz]

      -- `q` is meromorphic at `z0`, and has nonnegative order thanks to `h_ord`.
      have hq_mer : MeromorphicAt q z0 :=
        (hf_an.meromorphicAt).div (hG_an.meromorphicAt)
      have h_cast_mono : Monotone (fun n : ℕ => (n : ℤ)) := by
        intro a b hab
        exact Int.ofNat_le.2 hab
      have hmap_mono : Monotone (fun t : ℕ∞ => t.map (fun n : ℕ => (n : ℤ))) :=
        (ENat.monotone_map_iff (f := fun n : ℕ => (n : ℤ))).2 h_cast_mono
      have hG_le_f : meromorphicOrderAt G z0 ≤ meromorphicOrderAt f z0 := by
        -- Transport the analytic order inequality to a meromorphic order inequality.
        have : (analyticOrderAt G z0).map (fun n : ℕ => (n : ℤ))
              ≤ (analyticOrderAt f z0).map (fun n : ℕ => (n : ℤ)) :=
          hmap_mono (h_ord z0)
        simpa [hG_an.meromorphicOrderAt_eq, hf_an.meromorphicOrderAt_eq] using this
      have hq_nonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt q z0 := by
        have hq_order :
            meromorphicOrderAt q z0 = meromorphicOrderAt f z0 + -meromorphicOrderAt G z0 := by
          -- `order(q) = order(f) + order(1/G)`.
          have hmul :
              meromorphicOrderAt (fun z => f z * (G z)⁻¹) z0
                = meromorphicOrderAt f z0 + meromorphicOrderAt (fun z => (G z)⁻¹) z0 := by
            simpa using
              (meromorphicOrderAt_mul (x := z0) (f := f) (g := fun z => (G z)⁻¹)
                (hf := hf_an.meromorphicAt) (hg := (hG_an.meromorphicAt.inv)))
          have hinv : meromorphicOrderAt (fun z => (G z)⁻¹) z0 = -meromorphicOrderAt G z0 := by
            simpa using (meromorphicOrderAt_inv (f := G) (x := z0))
          calc
            meromorphicOrderAt q z0
                = meromorphicOrderAt (fun z => f z * (G z)⁻¹) z0 := by
                    simp [q, div_eq_mul_inv]
            _ = meromorphicOrderAt f z0 + meromorphicOrderAt (fun z => (G z)⁻¹) z0 := hmul
            _ = meromorphicOrderAt f z0 + -meromorphicOrderAt G z0 := by simp [hinv]
        -- Nonnegativity follows from `order(G) ≤ order(f)` and the fact that `G` is not locally zero.
        have hG_ne_top : meromorphicOrderAt G z0 ≠ ⊤ :=
          (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hG_an.meromorphicAt)).2 hG_ne
        have hcancel : meromorphicOrderAt G z0 + -meromorphicOrderAt G z0 = 0 :=
          LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top (x := meromorphicOrderAt G z0) hG_ne_top
        have h0 : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z0 + -meromorphicOrderAt G z0 := by
          have h := add_le_add_left hG_le_f (-meromorphicOrderAt G z0)
          simpa [hcancel, add_assoc] using h
        simpa [hq_order] using h0

      -- `q` has a limit along `𝓝[≠] z0`, hence tends to `limUnder ... q`.
      have hq_hasLimit : ∃ c, Tendsto q (𝓝[≠] z0) (𝓝 c) :=
        tendsto_nhds_of_meromorphicOrderAt_nonneg hq_mer hq_nonneg
      have hq_tendsto_lim : Tendsto q (𝓝[≠] z0) (𝓝 (limUnder (𝓝[≠] z0) q)) :=
        tendsto_nhds_limUnder hq_hasLimit

      -- Choose a neighbourhood on which `G` is nonzero except at the center; there `H` is an update
      -- of `q` by the computed limit.
      have hmem : {z : ℂ | G z ≠ 0} ∈ 𝓝[≠] z0 := hG_ne
      rcases (mem_nhdsWithin.1 hmem) with ⟨U, hU_open, hz0U, hU⟩
      have hU_nhds : U ∈ 𝓝 z0 := hU_open.mem_nhds hz0U
      have hU' : ∀ z, z ∈ U \ {z0} → G z ≠ 0 := by
        intro z hz
        have : z ∈ U ∩ ({z0}ᶜ : Set ℂ) := by
          refine ⟨hz.1, ?_⟩
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz.2
        exact hU this
      -- Continuity of the updated quotient at `z0`.
      have hcont_update :
          ContinuousAt (Function.update q z0 (limUnder (𝓝[≠] z0) q)) z0 := by
        -- `q → limUnder ... q` on the punctured neighbourhood.
        exact (continuousAt_update_same).2 hq_tendsto_lim
      -- The update is meromorphic at `z0` (it agrees with `q` on a punctured neighbourhood).
      have hmer_update : MeromorphicAt (Function.update q z0 (limUnder (𝓝[≠] z0) q)) z0 := by
        refine hq_mer.congr ?_
        -- `update q z0 _` equals `q` on `𝓝[≠] z0`.
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hz_ne : z ≠ z0 := by
          simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
        simp [Function.update, hz_ne]  -- `z ≠ z0`
      -- Hence the update is analytic at `z0`, and therefore differentiable at `z0`.
      have han_update :
          AnalyticAt ℂ (Function.update q z0 (limUnder (𝓝[≠] z0) q)) z0 :=
        MeromorphicAt.analyticAt hmer_update hcont_update

      -- Finally, `H` agrees with this update on a neighbourhood of `z0`, hence is analytic at `z0`.
      have hEq_on : (fun z => H z) =ᶠ[𝓝 z0] (Function.update q z0 (limUnder (𝓝[≠] z0) q)) := by
        -- On `U`, there are no other zeros of `G`, so `H` matches `q` off `z0` and matches the
        -- update at `z0` by definition.
        refine (eventually_of_mem hU_nhds ?_)
        intro z hzU
        by_cases hz : z = z0
        · subst hz
          simp [H, hz0, q]
        · have : z ∈ (U \ {z0}) := ⟨hzU, by simpa [Set.mem_singleton_iff] using hz⟩
          have hGz : G z ≠ 0 := hU' z this
          simp [H, q, hGz, Function.update, hz]

      have hanH : AnalyticAt ℂ H z0 := han_update.congr hEq_on.symm
      exact hanH.differentiableAt
    · -- Regular point: `G z0 ≠ 0`, so `H = f/G` near `z0`.
      have hG0 : G z0 ≠ 0 := hz0
      -- On this branch, `H z0 = f z0 / G z0`.
      have hHz0 : H z0 = f z0 / G z0 := by simp [H, q, hG0]
      -- Differentiability of the quotient at a point with nonzero denominator.
      have hdiff : DifferentiableAt ℂ (fun z => f z / G z) z0 :=
        (hf z0).div (hG z0) hG0
      -- `H` agrees with the quotient in a neighbourhood of `z0` (by continuity of `G`).
      have hG_near : ∀ᶠ z in 𝓝 z0, G z ≠ 0 :=
        (hG z0).continuousAt.eventually_ne hG0
      have hEq : (fun z => H z) =ᶠ[𝓝 z0] (fun z => f z / G z) := by
        filter_upwards [hG_near] with z hz
        simp [H, q, hz]
      -- Conclude.
      exact hdiff.congr_of_eventuallyEq hEq
  · intro z hz
    simp [H, q, hz]


set_option maxHeartbeats 800000 in
/-- Lindelöf's theorem, `ZeroData` version (zeros counted with multiplicity).

If `f` is entire of finite order `ρ` and `hz : ZeroData f` enumerates the nonzero zeros with
multiplicity, then for any `σ > ρ` the series `∑ ‖hz.zeros n‖^{-σ}` converges. -/
theorem lindelof_zero_data {f : ℂ → ℂ} {ρ σ : ℝ}
    (hf : EntireOfFiniteOrder ρ f)
    (hz : ZeroData f)
    (hσ : ρ < σ)
    (hσ_pos : 0 < σ) :
    Summable (fun n : ℕ => ‖hz.zeros n‖⁻¹ ^ σ) := by
  classical

  -- `ZeroData f` rules out the identically-zero function (countability obstruction).
  have hnot_all_zero : ¬ (∀ z : ℂ, f z = 0) := by
    intro hzero
    have hsubset : ({0}ᶜ : Set ℂ) ⊆ Set.range hz.zeros := by
      intro z hz0
      have hz' : f z = 0 := hzero z
      have hzspec := (hz.zero_spec z).1 hz'
      rcases hzspec with h0 | hnon0
      · exact False.elim (hz0 h0.1)
      · exact hnon0.2
    have hcount_range : (Set.range hz.zeros).Countable := Set.countable_range hz.zeros
    have hcount_compl : ({0}ᶜ : Set ℂ).Countable := hcount_range.mono hsubset
    have hcount_univ : (Set.univ : Set ℂ).Countable := by
      have h0c : ({0} : Set ℂ).Countable := Set.countable_singleton 0
      have : ({0} ∪ ({0}ᶜ) : Set ℂ).Countable := h0c.union hcount_compl
      simpa [Set.union_compl_self] using this
    exact not_countable_complex hcount_univ

  -- Choose an intermediate exponent `τ` with `ρ ≤ τ < σ` and `0 ≤ τ`.
  -- We take `τ := (max ρ 0 + σ) / 2`, which is always nonnegative and lies strictly below `σ`
  -- because `σ > max ρ 0` (from `hσ` and `hσ_pos`).
  let τ : ℝ := (max ρ 0 + σ) / 2
  have hσ_gt_max : max ρ 0 < σ := by
    cases le_total ρ 0 with
    | inl hρ0 =>
        have : max ρ 0 = 0 := max_eq_right hρ0
        simpa [this] using hσ_pos
    | inr h0ρ =>
        have : max ρ 0 = ρ := max_eq_left h0ρ
        simpa [this] using hσ
  have hρτ : ρ ≤ τ := by
    have hmax_le : max ρ 0 ≤ τ := by
      dsimp [τ]
      have : max ρ 0 ≤ σ := le_of_lt hσ_gt_max
      linarith
    exact (le_trans (le_max_left ρ 0) hmax_le)
  have hτσ : τ < σ := by
    dsimp [τ]
    linarith [hσ_gt_max]
  have hτ_nonneg : 0 ≤ τ := by
    dsimp [τ]
    have : (0 : ℝ) ≤ max ρ 0 := le_max_right ρ 0
    linarith [this, le_of_lt hσ_pos]

  -- Upgrade to order `τ`, and extract a simple norm bound.
  have hfτ : EntireOfFiniteOrder τ f := EntireOfFiniteOrder.of_le_order hf hρτ
  rcases hfτ.norm_bound with ⟨Cf, hCf_pos, hCf⟩

  -- Rule out `analyticOrderAt f 0 = ⊤` using the same obstruction.
  have hf_univ : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf.entire
  have hf_not_top0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ := by
    intro htop
    have hloc : ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0 := (analyticOrderAt_eq_top.mp htop)
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 :=
      (hloc.filter_mono nhdsWithin_le_nhds).frequently
    have hEq : Set.EqOn f 0 (Set.univ : Set ℂ) :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (f := f) (U := (Set.univ : Set ℂ)) hf_univ (by simpa using isPreconnected_univ)
        (by simp) hfreq
    have hzero : ∀ z : ℂ, f z = 0 := by
      intro z
      simpa using hEq (by simp : z ∈ (Set.univ : Set ℂ))
    exact hnot_all_zero hzero

  have horder_f0 : analyticOrderAt f (0 : ℂ) = (hz.ord0 : ℕ∞) := by
    have hcast :
        (analyticOrderNatAt f (0 : ℂ) : ℕ∞) = analyticOrderAt f (0 : ℂ) :=
      Nat.cast_analyticOrderNatAt (f := f) (z₀ := (0 : ℂ)) hf_not_top0
    simpa [hz.ord0_spec] using hcast.symm

  -- Divide out the zero at 0: `G0(z) = z^{ord0}`.
  let G0 : ℂ → ℂ := fun z => z ^ hz.ord0
  have hG0_entire : Differentiable ℂ G0 := by
    simp [G0]
  have hG0_nontrivial : ∃ z, G0 z ≠ 0 := by
    refine ⟨1, ?_⟩
    simp [G0]
  have horder_G0_0 : analyticOrderAt G0 (0 : ℂ) = (hz.ord0 : ℕ∞) := by
    simpa [G0, sub_zero] using
      (analyticOrderAt_centeredMonomial (z₀ := (0 : ℂ)) (n := hz.ord0))
  have h_ord0 : ∀ z : ℂ, analyticOrderAt G0 z ≤ analyticOrderAt f z := by
    intro z
    by_cases hz0 : z = 0
    · subst hz0
      simp [horder_G0_0, horder_f0]
    ·
      have hG0z_ne : G0 z ≠ 0 := by
        simpa [G0] using pow_ne_zero hz.ord0 hz0
      have hG0_order0 : analyticOrderAt G0 z = 0 := by
        have hAn : AnalyticAt ℂ G0 z := hG0_entire.analyticAt z
        exact (hAn.analyticOrderAt_eq_zero).2 hG0z_ne
      simp [hG0_order0]

  -- Entire quotient `f / z^{ord0}`.
  rcases quotient_entire (f := f) (G := G0) hf.entire hG0_entire hG0_nontrivial h_ord0 with
    ⟨f₁, hf₁_entire, hf₁_eq⟩

  -- `f₁(0) ≠ 0` from the local factorization of `f` at 0.
  have hf₁0 : f₁ 0 ≠ 0 := by
    have hf0_an : AnalyticAt ℂ f (0 : ℂ) := (hf.entire.analyticAt 0)
    rcases (hf0_an.analyticOrderAt_eq_natCast.mp horder_f0) with ⟨g0, hg0_an, hg0_ne, hfg0⟩
    let q : ℂ → ℂ := fun z => f z / G0 z
    have hq_eq : q =ᶠ[𝓝[≠] (0 : ℂ)] g0 := by
      have hfg0' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z = (z - 0) ^ hz.ord0 • g0 z :=
        hfg0.filter_mono nhdsWithin_le_nhds
      filter_upwards [hfg0', self_mem_nhdsWithin] with z hzfg hzneq
      have hz0 : z ≠ (0 : ℂ) := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hzneq
      have hG0z : G0 z ≠ 0 := by simpa [G0] using pow_ne_zero hz.ord0 hz0
      have hzfg' : f z = z ^ hz.ord0 * g0 z := by
        simpa [smul_eq_mul, sub_zero] using hzfg
      have : q z = g0 z := by
        -- cancel `z^ord0`
        calc
          q z = (z ^ hz.ord0 * g0 z) / (z ^ hz.ord0) := by simp [q, G0, hzfg']
          _ = g0 z := by
                field_simp [hG0z]
      simp [this]
    have htend_g0 : Tendsto g0 (𝓝[≠] (0 : ℂ)) (𝓝 (g0 0)) :=
      (hg0_an.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have htend_q : Tendsto q (𝓝[≠] (0 : ℂ)) (𝓝 (g0 0)) :=
      Filter.Tendsto.congr' hq_eq.symm htend_g0
    have hq_eq_f₁ : q =ᶠ[𝓝[≠] (0 : ℂ)] f₁ := by
      filter_upwards [self_mem_nhdsWithin] with z hzneq
      have hz0 : z ≠ (0 : ℂ) := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hzneq
      have hG0z : G0 z ≠ 0 := by simpa [G0] using pow_ne_zero hz.ord0 hz0
      simp [q, hf₁_eq z hG0z]
    have htend_f₁ : Tendsto f₁ (𝓝[≠] (0 : ℂ)) (𝓝 (g0 0)) :=
      Filter.Tendsto.congr' hq_eq_f₁ htend_q
    have htend_f₁0 : Tendsto f₁ (𝓝[≠] (0 : ℂ)) (𝓝 (f₁ 0)) :=
      ((hf₁_entire 0).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hlim : f₁ 0 = g0 0 := tendsto_nhds_unique htend_f₁0 htend_f₁
    simpa [hlim] using hg0_ne

  -- Normalize so that `g 0 = 1`.
  let g : ℂ → ℂ := fun z => f₁ z / f₁ 0
  have hg_entire : Differentiable ℂ g := by
    simpa [g] using (hf₁_entire.div_const (f₁ 0))
  have hg0 : g 0 = 1 := by
    simp [g, hf₁0]

  -- Zeros: for every **nonzero** entry in `hz.zeros`, `g` vanishes there.
  have hg_zeros : ∀ n, hz.zeros n ≠ 0 → g (hz.zeros n) = 0 := by
    intro n
    intro hn0
    have hG0z : G0 (hz.zeros n) ≠ 0 := by
      simpa [G0] using pow_ne_zero hz.ord0 hn0
    have hfz : f (hz.zeros n) = 0 := by
      have : (hz.zeros n = 0 ∧ 0 < hz.ord0) ∨ (hz.zeros n ≠ 0 ∧ ∃ k, hz.zeros k = hz.zeros n) :=
        Or.inr ⟨hn0, ⟨n, rfl⟩⟩
      exact (hz.zero_spec (hz.zeros n)).2 this
    have hf₁z : f₁ (hz.zeros n) = 0 := by
      simp [hf₁_eq _ hG0z, hfz]
    simp [g, hf₁z]

  -- A zero-free ball around `0`, hence `r0 ≤ ‖hz.zeros n‖` for all **nonzero** entries.
  obtain ⟨r0, hr0pos, hr0⟩ :
      ∃ r0 > 0, ∀ z : ℂ, ‖z‖ < r0 → g z ≠ 0 := by
    have hcont : ContinuousAt g 0 := (hg_entire 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), g z ≠ 0 := hcont.eventually_ne (by simp [hg0])
    rcases (Metric.mem_nhds_iff.mp hne) with ⟨r, hrpos, hr⟩
    refine ⟨r, hrpos, ?_⟩
    intro z hz
    have : z ∈ Metric.ball (0 : ℂ) r := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hr this

  have hr0_le_norm : ∀ n, hz.zeros n ≠ 0 → r0 ≤ ‖hz.zeros n‖ := by
    intro n
    intro hn0
    have hz0 : g (hz.zeros n) = 0 := hg_zeros n hn0
    have hnot : ¬ ‖hz.zeros n‖ < r0 := by
      intro hlt
      exact (hr0 (hz.zeros n) hlt) hz0
    exact le_of_not_gt hnot

  -- Dyadic shell index: `k(n) = ⌊logb 2 (‖zeros n‖/r0)⌋₊`.
  let zeros : ℕ → ℂ := hz.zeros
  let kfun : ℕ → ℕ := fun n => ⌊Real.logb 2 (‖zeros n‖ / r0)⌋₊

  -- Dyadic bounds for `x ≥ 1`.
  have hdyadic_lower :
      ∀ {x : ℝ}, 1 ≤ x → (2 : ℝ) ^ (⌊Real.logb 2 x⌋₊ : ℝ) ≤ x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
    have hlog_nonneg : 0 ≤ Real.logb 2 x :=
      Real.logb_nonneg (b := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2) hx
    have hfloor_le : (⌊Real.logb 2 x⌋₊ : ℝ) ≤ Real.logb 2 x := by
      simpa using (Nat.floor_le hlog_nonneg)
    exact (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (x := (⌊Real.logb 2 x⌋₊ : ℝ)) (y := x)
      (by norm_num : (1 : ℝ) < 2) hx0).1 hfloor_le
  have hdyadic_upper :
      ∀ {x : ℝ}, 1 ≤ x → x < (2 : ℝ) ^ ((⌊Real.logb 2 x⌋₊ : ℝ) + 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
    have hlt : Real.logb 2 x < (⌊Real.logb 2 x⌋₊ : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one (Real.logb 2 x))
    exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (x := x)
      (y := (⌊Real.logb 2 x⌋₊ : ℝ) + 1) (by norm_num : (1 : ℝ) < 2) hx0).1 hlt

  -- For each nonzero `n`, we have `r0*2^{k(n)} ≤ ‖zeros n‖ < r0*2^{k(n)+1}`.
  have hk_lower : ∀ n, zeros n ≠ 0 → r0 * (2 : ℝ) ^ (kfun n : ℝ) ≤ ‖zeros n‖ := by
    intro n hn0
    have hx1 : (1 : ℝ) ≤ ‖zeros n‖ / r0 := by
      have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
      have : r0 / r0 ≤ ‖zeros n‖ / r0 :=
        div_le_div_of_nonneg_right (hr0_le_norm n hn0) (le_of_lt hr0pos)
      simpa [hr0ne] using this
    have hle : (2 : ℝ) ^ (kfun n : ℝ) ≤ ‖zeros n‖ / r0 := by
      simpa [kfun] using (hdyadic_lower (x := ‖zeros n‖ / r0) hx1)
    have := mul_le_mul_of_nonneg_left hle (le_of_lt hr0pos)
    have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
    have hxEq : r0 * (‖zeros n‖ / r0) = ‖zeros n‖ := by
      field_simp [hr0ne]
    simpa [mul_assoc, hxEq] using this
  have hk_upper : ∀ n, zeros n ≠ 0 → ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := by
    intro n hn0
    have hx1 : (1 : ℝ) ≤ ‖zeros n‖ / r0 := by
      have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
      have : r0 / r0 ≤ ‖zeros n‖ / r0 :=
        div_le_div_of_nonneg_right (hr0_le_norm n hn0) (le_of_lt hr0pos)
      simpa [hr0ne] using this
    have hlt : ‖zeros n‖ / r0 < (2 : ℝ) ^ ((kfun n : ℝ) + 1) := by
      simpa [kfun] using (hdyadic_upper (x := ‖zeros n‖ / r0) hx1)
    have := mul_lt_mul_of_pos_left hlt hr0pos
    have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
    have hxEq : r0 * (‖zeros n‖ / r0) = ‖zeros n‖ := by
      field_simp [hr0ne]
    simpa [mul_assoc, hxEq] using this

  -- Define shells: `S 0` collects the padding indices with `zeros n = 0`, and
  -- `S (k+1)` collects the nonzero entries whose dyadic index is `k`.
  let S : ℕ → Set ℕ :=
    fun k =>
      match k with
      | 0 => {n : ℕ | zeros n = 0}
      | k + 1 => {n : ℕ | zeros n ≠ 0 ∧ kfun n = k}
  have hS : ∀ n : ℕ, ∃! k : ℕ, n ∈ S k := by
    intro n
    by_cases hn0 : zeros n = 0
    · -- Case: zeros n = 0, so n ∈ S 0
      refine ⟨0, by simp [S, hn0], ?_⟩
      intro k hk
      cases k with
      | zero => rfl
      | succ k =>
          have hk' : zeros n ≠ 0 ∧ kfun n = k := by
            simpa [S] using hk
          exact False.elim (hk'.1 hn0)
    · -- Case: zeros n ≠ 0, so n ∈ S (kfun n + 1)
      refine ⟨kfun n + 1, by simp [S, hn0], ?_⟩
      intro k hk
      cases k with
      | zero =>
          have : zeros n = 0 := by simpa [S] using hk
          exact False.elim (hn0 this)
      | succ k =>
          have hk' : zeros n ≠ 0 ∧ kfun n = k := by
            simpa [S] using hk
          have : k = kfun n := hk'.2.symm
          simp [this]

  -- Nonnegativity of the summand.
  have hnonneg : 0 ≤ fun n : ℕ => ‖zeros n‖⁻¹ ^ σ := by
    intro n
    exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (zeros n))) σ

  -- We apply the partition lemma: it suffices to prove summability of the shell `tsum`s.
  have hshell :
      (∀ k : ℕ, Summable fun n : S k => ‖zeros n.1‖⁻¹ ^ σ) ∧
        Summable fun k : ℕ => ∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ := by
    constructor
    · intro k
      cases k with
      | zero =>
          -- On the padding shell `S 0 = {n | zeros n = 0}`, the summand is identically `0`
          -- because `σ > 0` (and `0 ^ σ = 0` for `Real.rpow`).
          have hsum_zero : ∀ n : S 0, ‖zeros n.1‖⁻¹ ^ σ = 0 := by
            intro n
            have hz : zeros n.1 = 0 := n.2
            simp only [hz, norm_zero, inv_zero]
            exact Real.zero_rpow (ne_of_gt hσ_pos)
          simp_rw [hsum_zero]
          exact summable_zero
      | succ k =>
          -- For `S (k+1)`, the shell only contains indices with `zeros n ≠ 0`, and is finite by
          -- local finiteness of the nonzero zero set.
          have hSk_finite : (S (k + 1)).Finite := by
            refine (hz.finite_in_ball (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))).subset ?_
            intro n hn
            have hn' : zeros n ≠ 0 ∧ kfun n = k := by simpa [S] using hn
            have hn_upper : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) :=
              hk_upper n hn'.1
            have hk' : (kfun n : ℝ) = (k : ℝ) := by exact_mod_cast hn'.2
            have hn_upper' : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
              simpa [hk'] using hn_upper
            exact ⟨hn'.1, le_of_lt hn_upper'⟩
          haveI : Finite (S (k + 1)) := hSk_finite.to_subtype
          exact Summable.of_finite
    ·
      -- Shell `tsum` summability: Jensen gives `card(S k) = O((2^k)^τ)` (counting multiplicity),
      -- and dyadic bounds give `‖zeros n‖^{-σ} = O((2^{-σ})^k)` on shell `k`.
      classical
      let log2 : ℝ := Real.log (2 : ℝ)
      have hlog2_pos : 0 < log2 := by
        dsimp [log2]
        exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hlog2_ne : log2 ≠ 0 := ne_of_gt hlog2_pos

      -- A global exponential bound for `f₁` of the same order `τ`.
      have h_compact : IsCompact (Metric.closedBall (0 : ℂ) (1 : ℝ)) :=
        isCompact_closedBall (0 : ℂ) (1 : ℝ)
      have h_cont : ContinuousOn f₁ (Metric.closedBall (0 : ℂ) (1 : ℝ)) :=
        (hf₁_entire.continuous).continuousOn
      obtain ⟨M1, hM1⟩ := h_compact.exists_bound_of_continuousOn h_cont
      have hM1_nonneg : 0 ≤ M1 := by
        have h0 := hM1 0 (by simp [Metric.mem_closedBall])
        exact le_trans (norm_nonneg _) h0

      let C1 : ℝ := max Cf (Real.log (1 + M1) + 1)
      have hC1pos : 0 < C1 := lt_of_lt_of_le hCf_pos (le_max_left _ _)

      have hC1 : ∀ z : ℂ, ‖f₁ z‖ ≤ Real.exp (C1 * (1 + ‖z‖) ^ τ) := by
        intro z
        by_cases hz1 : ‖z‖ < 1
        · have hz_cb : z ∈ Metric.closedBall (0 : ℂ) (1 : ℝ) := by
            have : ‖z‖ ≤ (1 : ℝ) := le_of_lt hz1
            simpa [Metric.mem_closedBall, dist_zero_right] using this
          have hzM : ‖f₁ z‖ ≤ M1 := hM1 z hz_cb
          have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ τ := by
            have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
            exact Real.one_le_rpow hbase hτ_nonneg
          have hlog_le : Real.log (1 + ‖f₁ z‖) ≤ Real.log (1 + M1) := by
            have hpos : 0 < (1 : ℝ) + ‖f₁ z‖ := by linarith [norm_nonneg (f₁ z)]
            exact Real.log_le_log hpos (by linarith [hzM])
          have hlogM1_le : Real.log (1 + M1) ≤ C1 * (1 + ‖z‖) ^ τ := by
            have hC1_ge : Real.log (1 + M1) ≤ C1 := by
              have h1 : Real.log (1 + M1) ≤ Real.log (1 + M1) + 1 :=
                le_add_of_nonneg_right zero_le_one
              have h2 : Real.log (1 + M1) + 1 ≤ C1 := by
                simp [C1]
              exact h1.trans h2
            have hC1_le : (C1 : ℝ) ≤ C1 * (1 + ‖z‖) ^ τ := by
              simpa [mul_one] using (mul_le_mul_of_nonneg_left hone (le_of_lt hC1pos))
            exact hC1_ge.trans hC1_le
          have hlog_main : Real.log (1 + ‖f₁ z‖) ≤ C1 * (1 + ‖z‖) ^ τ :=
            hlog_le.trans hlogM1_le
          have hpos : 0 < (1 : ℝ) + ‖f₁ z‖ := by linarith [norm_nonneg (f₁ z)]
          have h1 : (1 : ℝ) + ‖f₁ z‖ ≤ Real.exp (C1 * (1 + ‖z‖) ^ τ) :=
            (Real.log_le_iff_le_exp hpos).1 hlog_main
          linarith [Real.exp_pos (C1 * (1 + ‖z‖) ^ τ)]
        · have hz1' : (1 : ℝ) ≤ ‖z‖ := le_of_not_gt hz1
          have hz0 : z ≠ (0 : ℂ) := by
            have : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hz1'
            exact (norm_pos_iff.mp this)
          have hG0z : G0 z ≠ 0 := by simpa [G0] using pow_ne_zero hz.ord0 hz0
          have hf₁z : f₁ z = f z / G0 z := hf₁_eq z hG0z
          have hnorm_le : ‖f₁ z‖ ≤ ‖f z‖ := by
            have hzpow : (1 : ℝ) ≤ ‖G0 z‖ := by
              have : (1 : ℝ) ≤ ‖z‖ ^ hz.ord0 := one_le_pow₀ hz1'
              simpa [G0, norm_pow] using this
            calc
              ‖f₁ z‖ = ‖f z / G0 z‖ := by simp [hf₁z]
              _ = ‖f z‖ / ‖G0 z‖ := by simp
              _ ≤ ‖f z‖ := div_le_self (norm_nonneg _) hzpow
          have hfz : ‖f z‖ ≤ Real.exp (Cf * (1 + ‖z‖) ^ τ) := hCf z
          have hCf_le : Cf ≤ C1 := le_max_left _ _
          have hexp_le : Real.exp (Cf * (1 + ‖z‖) ^ τ) ≤ Real.exp (C1 * (1 + ‖z‖) ^ τ) := by
            have hmul_le : Cf * (1 + ‖z‖) ^ τ ≤ C1 * (1 + ‖z‖) ^ τ :=
              mul_le_mul_of_nonneg_right hCf_le (Real.rpow_nonneg (by linarith [norm_nonneg z]) τ)
            exact Real.exp_le_exp.2 hmul_le
          exact hnorm_le.trans (hfz.trans hexp_le)

      let M0 : ℝ := max 2 (‖f₁ 0‖)⁻¹
      have hM0_pos : 0 < M0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)

      let q : ℝ := (2 : ℝ) ^ (τ - σ)
      have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hq_lt_one : q < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
          (sub_neg.2 hτσ)
      have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
        summable_geometric_of_lt_one hq_nonneg hq_lt_one

      let qσ : ℝ := (2 : ℝ) ^ (-σ)
      have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
      have hqσ_lt_one : qσ < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
          (by linarith [hσ_pos])
      have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
        summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one

      let A : ℝ := (C1 / log2) * (1 + 4 * r0) ^ τ * (r0 ^ (-σ))
      let B : ℝ := ((Real.log M0) / log2 + 1) * (r0 ^ (-σ))
      have hmajor : Summable (fun k : ℕ => A * q ^ k + B * qσ ^ k) :=
        (hgeom_q.mul_left A).add (hgeom_qσ.mul_left B)

      -- We bound the *tail* shell sums `k ↦ ∑' n : S (k+1), ...` by a geometric series, then use
      -- `summable_nat_add_iff` to transfer summability back to `k ↦ ∑' n : S k, ...`.
      refine (summable_nat_add_iff (f := fun k : ℕ => ∑' n : S k, ‖zeros n.1‖⁻¹ ^ σ) 1).1 ?_
      refine Summable.of_nonneg_of_le
        (g := fun k : ℕ => ∑' n : S (k + 1), ‖zeros n.1‖⁻¹ ^ σ)
        (f := fun k : ℕ => A * q ^ k + B * qσ ^ k)
        (fun k => by
          have hnn : ∀ n : S (k + 1), 0 ≤ ‖zeros n.1‖⁻¹ ^ σ := by
            intro n
            exact Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg (zeros n.1))) σ
          exact tsum_nonneg hnn)
        (fun k => by
          -- Fix a shell index `k`, apply Jensen at radii `r = r0*2^(k+1)` and `R = 2r`.
          let r : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
          let R : ℝ := (2 : ℝ) * r
          have hr : 0 < r := by
            have h2 : 0 < (2 : ℝ) ^ ((k : ℝ) + 1) :=
              Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
            exact mul_pos hr0pos h2
          have hRpos : 0 < R := mul_pos (by norm_num : (0 : ℝ) < 2) hr
          have hrR : r < R := by
            have h2 : (1 : ℝ) < 2 := by norm_num
            simpa [R, mul_assoc] using (lt_mul_of_one_lt_left hr h2)

          have hg_anal : AnalyticOnNhd ℂ g (Metric.closedBall 0 R) := by
            intro z hz
            exact hg_entire.analyticAt z

          let Bk : ℝ := Real.exp (C1 * (1 + R) ^ τ) * M0
          have hBk : 1 < Bk := by
            have hexp : 1 ≤ Real.exp (C1 * (1 + R) ^ τ) :=
              (Real.one_le_exp_iff).2 (by
                have : 0 ≤ (1 + R : ℝ) ^ τ := Real.rpow_nonneg (by linarith [hRpos.le]) τ
                nlinarith [le_of_lt hC1pos, this])
            have hM0 : (1 : ℝ) < M0 := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _)
            have : 1 < Real.exp (C1 * (1 + R) ^ τ) * M0 := one_lt_mul hexp hM0
            simpa [Bk] using this

          have hg_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ Bk := by
            intro z hzR
            have hf₁z : ‖f₁ z‖ ≤ Real.exp (C1 * (1 + ‖z‖) ^ τ) := hC1 z
            have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
            have hpow_le : (1 + ‖z‖ : ℝ) ^ τ ≤ (1 + R) ^ τ :=
              Real.rpow_le_rpow (by positivity) hbase hτ_nonneg
            have hmul_le : C1 * (1 + ‖z‖) ^ τ ≤ C1 * (1 + R) ^ τ :=
              mul_le_mul_of_nonneg_left hpow_le (le_of_lt hC1pos)
            have hexp_le : Real.exp (C1 * (1 + ‖z‖) ^ τ) ≤ Real.exp (C1 * (1 + R) ^ τ) :=
              (Real.exp_le_exp.2 hmul_le)
            have hf₁z' : ‖f₁ z‖ ≤ Real.exp (C1 * (1 + R) ^ τ) := hf₁z.trans hexp_le
            have hf₁0pos : 0 < ‖f₁ 0‖ := norm_pos_iff.mpr hf₁0
            have hdiv_le :
                ‖g z‖ ≤ Real.exp (C1 * (1 + R) ^ τ) * (‖f₁ 0‖)⁻¹ := by
              have : ‖g z‖ = ‖f₁ z‖ / ‖f₁ 0‖ := by simp [g]
              have hdiv :
                  ‖f₁ z‖ / ‖f₁ 0‖ ≤ Real.exp (C1 * (1 + R) ^ τ) / ‖f₁ 0‖ :=
                div_le_div_of_nonneg_right hf₁z' (le_of_lt hf₁0pos)
              simpa [this, div_eq_mul_inv, mul_assoc] using hdiv
            have hM0' : (‖f₁ 0‖)⁻¹ ≤ M0 := le_max_right _ _
            have hBk' :
                Real.exp (C1 * (1 + R) ^ τ) * (‖f₁ 0‖)⁻¹ ≤ Real.exp (C1 * (1 + R) ^ τ) * M0 :=
              mul_le_mul_of_nonneg_left hM0' (le_of_lt (Real.exp_pos _))
            exact le_trans hdiv_le (by simpa [Bk] using hBk')

          rcases jensen_zeros_multiplicity_bound (f := g) (r := r) (R := R) (B := Bk)
            hg_anal hr hrR hg0 hBk hg_bound with ⟨Z, hZ, hZmult⟩

          -- Fix a `Fintype` structure on the shell `S (k+1)` (we will use `tsum_fintype` below).
          have hSk_finite : (S (k + 1)).Finite := by
            refine (hz.finite_in_ball (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))).subset ?_
            intro n hn
            have hk : kfun n = k := (by
              have hn' : zeros n ≠ 0 ∧ kfun n = k := by simpa [S] using hn
              exact hn'.2)
            have hn_upper : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := hk_upper n (by
              have hn' : zeros n ≠ 0 ∧ kfun n = k := by simpa [S] using hn
              exact hn'.1)
            have hk' : (kfun n : ℝ) = (k : ℝ) := by exact_mod_cast hk
            have hn_upper' : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by simpa [hk'] using hn_upper
            exact ⟨(by
              have hn' : zeros n ≠ 0 ∧ kfun n = k := by simpa [S] using hn
              exact hn'.1), le_of_lt hn_upper'⟩
          letI : Fintype (S (k + 1)) := hSk_finite.fintype

          -- Bounding `card(S k)` by the multiplicity (divisor) sum in `‖z‖ ≤ r`.
          have hcard_S : (Fintype.card (S (k + 1)) : ℝ) ≤ Real.log Bk / log2 + 1 := by
            classical
            -- Inject `S (k+1)` into `T := {n | zeros n ≠ 0 ∧ ‖zeros n‖ ≤ r}`.
            let T : Set ℕ := {n : ℕ | zeros n ≠ 0 ∧ ‖zeros n‖ ≤ r}
            have hT_finite : T.Finite := hz.finite_in_ball r
            letI : Fintype T := hT_finite.fintype
            have hST : S (k + 1) ⊆ T := by
              intro n hn
              have hn' : zeros n ≠ 0 ∧ kfun n = k := by simpa [S] using hn
              have hk : kfun n = k := hn'.2
              have hn_upper : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((kfun n : ℝ) + 1) := hk_upper n hn'.1
              have hk' : (kfun n : ℝ) = (k : ℝ) := by exact_mod_cast hk
              have hn_upper' : ‖zeros n‖ < r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by simpa [hk'] using hn_upper
              have : ‖zeros n‖ ≤ r := by simpa [r] using (le_of_lt hn_upper')
              exact ⟨hn'.1, this⟩
            let incl : S (k + 1) → T := fun n => ⟨n.1, hST n.2⟩
            have hincl : Function.Injective incl := by
              intro a b hab
              ext
              exact congrArg (fun t : T => t.1) hab
            have hcard_le : Fintype.card (S (k + 1)) ≤ Fintype.card T :=
              Fintype.card_le_of_injective incl hincl
            have hcard_le' : (Fintype.card (S (k + 1)) : ℝ) ≤ (Fintype.card T : ℝ) := by
              exact_mod_cast hcard_le

            -- Each `n ∈ T` maps to a zero of `g` in `Z`.
            have hmemZ : ∀ n : T, zeros n.1 ∈ Z := by
              intro n
              have hn_ne : zeros n.1 ≠ 0 := n.2.1
              have hnR : ‖zeros n.1‖ ≤ r := n.2.2
              have hgz : g (zeros n.1) = 0 := hg_zeros n.1 hn_ne
              exact (hZ (zeros n.1)).2 ⟨hnR, hgz⟩

            -- Compare `card T` with the divisor sum via fibers.
            let fiber : Z → Type := fun z => {n : ℕ // zeros n = z.1}
            have hfinite_fiber : ∀ z : Z, Finite (fiber z) := by
              intro z
              have hz_ne0 : z.1 ≠ (0 : ℂ) := by
                intro hz0
                have : g z.1 = 0 := (hZ z.1).1 z.2 |>.2
                simp [hz0, hg0] at this
              have : ({n : ℕ | zeros n = z.1} : Set ℕ).Finite :=
                hz.finite_fiber (z := z.1) (by simpa using hz_ne0)
              simpa [fiber] using this.to_subtype
            classical
            letI : ∀ z : Z, Fintype (fiber z) := fun z => Fintype.ofFinite (fiber z)

            -- Injection `T → Σ z, fiber z`.
            let ψ : T → Sigma fiber := fun n => ⟨⟨zeros n.1, hmemZ n⟩, ⟨n.1, rfl⟩⟩
            have hψ_inj : Function.Injective ψ := by
              intro a b hab
              exact Subtype.ext (congrArg (fun p => p.2.1) hab)
            have hcardT_le_sigma : Fintype.card T ≤ Fintype.card (Sigma fiber) :=
              Fintype.card_le_of_injective ψ hψ_inj
            have hcardT_le_sum :
                (Fintype.card T : ℝ) ≤ ∑ z : Z, (Fintype.card (fiber z) : ℝ) := by
              have hnat : (Fintype.card T : ℝ) ≤ (Fintype.card (Sigma fiber) : ℝ) := by
                exact_mod_cast hcardT_le_sigma
              have hcard_sigma_nat : Fintype.card (Sigma fiber) = ∑ z : Z, Fintype.card (fiber z) :=
                Fintype.card_sigma (ι := Z) (α := fiber)
              -- cast the nat identity using `Nat.cast_sum` over `Finset.univ`
              have hcard_sigma :
                  (Fintype.card (Sigma fiber) : ℝ) = ∑ z : Z, (Fintype.card (fiber z) : ℝ) := by
                classical
                -- `∑ z : Z, ...` is a `Finset.univ` sum
                simp [hcard_sigma_nat]
              exact hnat.trans_eq hcard_sigma

            -- Pointwise: fiber cardinality equals divisor value.
            have hfiber_eq_div :
                ∀ z : Z, (Fintype.card (fiber z) : ℝ)
                  = (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z.1 : ℝ) := by
              intro z
              have hz_ne0 : z.1 ≠ (0 : ℂ) := by
                intro hz0
                have : g z.1 = 0 := (hZ z.1).1 z.2 |>.2
                simp [hz0, hg0] at this
              -- divisor = analytic order for analytic functions
              have hg_mer : MeromorphicOn g (Metric.closedBall (0 : ℂ) |R|) :=
                by
                  -- `|R| = R` since `R > 0`.
                  simpa [abs_of_pos hRpos] using (hg_anal.meromorphicOn)
              have hzU : z.1 ∈ Metric.closedBall (0 : ℂ) |R| := by
                have : ‖z.1‖ ≤ r := (hZ z.1).1 z.2 |>.1
                have : ‖z.1‖ ≤ R := le_trans this (le_of_lt hrR)
                simpa [Metric.mem_closedBall, dist_zero_right, abs_of_pos hRpos] using this
              have hdiv_int :
                  MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z.1
                    = (analyticOrderNatAt g z.1 : ℤ) := by
                -- local lemma by cases on `analyticOrderAt`
                have hg_an : AnalyticAt ℂ g z.1 := hg_entire.analyticAt z.1
                -- reuse the standalone lemma pattern
                simp [MeromorphicOn.divisor_apply hg_mer hzU, hg_an.meromorphicOrderAt_eq]
                cases h : analyticOrderAt g z.1 <;> simp [analyticOrderNatAt, h]
              have hdiv_real :
                  (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z.1 : ℝ)
                    = (analyticOrderNatAt g z.1 : ℝ) := by
                simp [hdiv_int, Int.cast_natCast]
              -- analytic order at `z ≠ 0` is preserved under dividing out `z^{ord0}` and scaling.
              have horder_eq : analyticOrderNatAt g z.1 = analyticOrderNatAt f z.1 := by
                have hG0z : G0 z.1 ≠ 0 := by simpa [G0] using pow_ne_zero hz.ord0 hz_ne0
                -- `f₁` agrees with `f/G0` near `z`.
                have hG0_near : ∀ᶠ w in 𝓝 z.1, G0 w ≠ 0 :=
                  (hG0_entire z.1).continuousAt.eventually_ne hG0z
                have hf₁_congr :
                    analyticOrderAt f₁ z.1 = analyticOrderAt (fun w => f w / G0 w) z.1 := by
                  apply analyticOrderAt_congr
                  filter_upwards [hG0_near] with w hw
                  simp [hf₁_eq w hw]
                have hf_an : AnalyticAt ℂ f z.1 := (hf.entire.analyticAt z.1)
                have hG_an : AnalyticAt ℂ G0 z.1 := (hG0_entire.analyticAt z.1)
                have hGinv_an : AnalyticAt ℂ (fun w => (G0 w)⁻¹) z.1 := hG_an.inv hG0z
                have hGinv0 : (fun w => (G0 w)⁻¹) z.1 ≠ 0 := by simp [hG0z]
                have hGinv_order : analyticOrderAt (fun w => (G0 w)⁻¹) z.1 = 0 :=
                  (hGinv_an.analyticOrderAt_eq_zero).2 hGinv0
                have hmul :
                    analyticOrderAt (fun w => f w * (G0 w)⁻¹) z.1 = analyticOrderAt f z.1 := by
                  calc
                    analyticOrderAt (fun w => f w * (G0 w)⁻¹) z.1
                        = analyticOrderAt f z.1 + analyticOrderAt (fun w => (G0 w)⁻¹) z.1 := by
                            simpa using (analyticOrderAt_mul (𝕜 := ℂ) (f := f) (g := fun w => (G0 w)⁻¹)
                              (z₀ := z.1) hf_an hGinv_an)
                    _ = analyticOrderAt f z.1 + 0 := by simp [hGinv_order]
                    _ = analyticOrderAt f z.1 := by simp
                have hdiv :
                    analyticOrderAt (fun w => f w / G0 w) z.1 = analyticOrderAt f z.1 := by
                  simp [div_eq_mul_inv, hmul]
                have hf₁_order : analyticOrderAt f₁ z.1 = analyticOrderAt f z.1 := by
                  simpa [hf₁_congr] using hdiv
                have hconst_an : AnalyticAt ℂ (fun _ : ℂ => (f₁ 0)⁻¹) z.1 := analyticAt_const
                have hconst_ne : (fun _ : ℂ => (f₁ 0)⁻¹) z.1 ≠ 0 := by simp [hf₁0]
                have hconst_order : analyticOrderAt (fun _ : ℂ => (f₁ 0)⁻¹) z.1 = 0 :=
                  (hconst_an.analyticOrderAt_eq_zero).2 hconst_ne
                have hg_order :
                    analyticOrderAt g z.1 = analyticOrderAt f₁ z.1 := by
                  have := analyticOrderAt_mul (𝕜 := ℂ) (f := f₁) (g := fun _ : ℂ => (f₁ 0)⁻¹)
                    (z₀ := z.1) (hf₁_entire.analyticAt z.1) hconst_an
                  -- `g = f₁ * const` as a function
                  simpa [g, div_eq_mul_inv, hconst_order, add_zero, mul_assoc] using this
                -- convert to nat order
                simp [analyticOrderNatAt, hg_order, hf₁_order]
              -- multiplicity spec: analytic order = fiber cardinal
              have hmult : analyticOrderNatAt f z.1 = Nat.card (fiber z) := by
                simpa [fiber] using (hz.zeros_mult_spec z.1 hz_ne0)
              -- convert `Nat.card` to `Fintype.card`
              have hcard : (Fintype.card (fiber z) : ℝ) = (Nat.card (fiber z) : ℝ) := by
                classical
                simp
              have : (Fintype.card (fiber z) : ℝ) = (analyticOrderNatAt g z.1 : ℝ) := by
                have := congrArg (fun n : ℕ => (n : ℝ)) (hmult.symm)
                -- `Nat.card` and `Fintype.card` coincide
                -- and replace `analyticOrderNatAt f` by `analyticOrderNatAt g`
                simpa [hcard, horder_eq] using this
              -- finish via `hdiv_real`
              simpa [hdiv_real] using this

            have hcardT_le_div :
                (Fintype.card T : ℝ)
                  ≤ ∑ z ∈ Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ) := by
              -- `card T ≤ Σ card fiber = Σ divisor`
              have hsum_eq :
                  (∑ z : Z, (Fintype.card (fiber z) : ℝ))
                    = ∑ z ∈ Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ) := by
                classical
                calc
                  (∑ z : Z, (Fintype.card (fiber z) : ℝ))
                      = ∑ z : Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z.1 : ℝ) := by
                          refine Finset.sum_congr rfl ?_
                          intro z hzuniv
                          simpa using hfiber_eq_div z
                  _ = ∑ z ∈ Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ) := by
                        simpa using (Finset.sum_coe_sort Z (fun z => (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ)))
              have : (Fintype.card T : ℝ)
                    ≤ ∑ z : Z, (Fintype.card (fiber z) : ℝ) := hcardT_le_sum
              exact this.trans_eq hsum_eq

            have hrat : R / r = (2 : ℝ) := by
              have hrne : r ≠ 0 := ne_of_gt hr
              simp [R, hrne, div_eq_mul_inv]
            have hZmult' :
                (∑ z ∈ Z, (MeromorphicOn.divisor g (Metric.closedBall (0 : ℂ) |R|) z : ℝ))
                  ≤ Real.log Bk / log2 := by
              simpa [hrat, log2] using hZmult
            have hcardT : (Fintype.card T : ℝ) ≤ Real.log Bk / log2 :=
              hcardT_le_div.trans hZmult'
            -- finish
            exact hcard_le'.trans (hcardT.trans (by linarith))

          -- Dyadic lower bound on shell `k`: all zeros satisfy `r0 * 2^k ≤ ‖zero‖`.
          let t : ℝ := r0 * (2 : ℝ) ^ (k : ℕ)
          have ht_pos : 0 < t := by
            have h2 : 0 < (2 : ℝ) ^ (k : ℕ) := by positivity
            exact mul_pos hr0pos h2
          have hterm_le : ∀ n : S (k + 1), ‖zeros n.1‖⁻¹ ^ σ ≤ t⁻¹ ^ σ := by
            intro n
            -- For n ∈ S (k+1), we have zeros n ≠ 0 ∧ kfun n = k
            have hn' : zeros n.1 ≠ 0 ∧ kfun n.1 = k := n.2
            have hn_lower : r0 * (2 : ℝ) ^ (kfun n.1 : ℝ) ≤ ‖zeros n.1‖ := hk_lower n.1 hn'.1
            have hk_eq : (kfun n.1 : ℝ) = (k : ℝ) := by exact_mod_cast hn'.2
            have hn_lower' : r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖zeros n.1‖ := by
              simpa [hk_eq] using hn_lower
            have hkpow : (2 : ℝ) ^ (k : ℝ) = (2 : ℝ) ^ (k : ℕ) := by simp
            have hn_lower'' : t ≤ ‖zeros n.1‖ := by simpa [t, hkpow] using hn_lower'
            have hb : 0 < ‖zeros n.1‖ := by
              exact norm_pos_iff.2 hn'.1
            have hinv : ‖zeros n.1‖⁻¹ ≤ t⁻¹ :=
              (inv_le_inv₀ (a := ‖zeros n.1‖) (b := t) hb ht_pos).2 hn_lower''
            have h0 : 0 ≤ ‖zeros n.1‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
            exact Real.rpow_le_rpow h0 hinv (le_of_lt hσ_pos)

          have hshell_sum :
              (∑' n : S (k + 1), ‖zeros n.1‖⁻¹ ^ σ) ≤ (Fintype.card (S (k + 1)) : ℝ) * (t⁻¹ ^ σ) := by
            classical
            simp [tsum_fintype]
            have h' : ∀ n ∈ (Finset.univ : Finset (S (k + 1))), ‖zeros n.1‖⁻¹ ^ σ ≤ t⁻¹ ^ σ := by
              intro n hn
              exact hterm_le n
            have := Finset.sum_le_card_nsmul (s := (Finset.univ : Finset (S (k + 1))))
              (f := fun n : S (k + 1) => ‖zeros n.1‖⁻¹ ^ σ) (n := t⁻¹ ^ σ) h'
            simpa [nsmul_eq_mul] using this

          have ht_scale : t⁻¹ ^ σ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
            have hr0_le : 0 ≤ r0 := le_of_lt hr0pos
            have h2pow : 0 ≤ (2 : ℝ) ^ (k : ℕ) := by positivity
            have hxnonneg : 0 ≤ r0 * (2 : ℝ) ^ (k : ℕ) := mul_nonneg hr0_le h2pow
            dsimp [t]
            calc
              (r0 * (2 : ℝ) ^ (k : ℕ))⁻¹ ^ σ
                  = ((r0 * (2 : ℝ) ^ (k : ℕ)) ^ σ)⁻¹ := Real.inv_rpow hxnonneg σ
              _ = (r0 * (2 : ℝ) ^ (k : ℕ)) ^ (-σ) := by
                    simpa using (Real.rpow_neg hxnonneg σ).symm
              _ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (k : ℕ)) ^ (-σ) := by
                    simp [Real.mul_rpow hr0_le h2pow]
              _ = (r0 ^ (-σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
                    have h2 : 0 ≤ (2 : ℝ) := by norm_num
                    have hpow' : ((2 : ℝ) ^ k) ^ (-σ) = ((2 : ℝ) ^ (-σ)) ^ k := by
                      calc
                        ((2 : ℝ) ^ k) ^ (-σ) = (2 : ℝ) ^ ((k : ℝ) * (-σ)) := by
                              have := Real.rpow_mul h2 (k : ℝ) (-σ)
                              simpa using this.symm
                        _ = (2 : ℝ) ^ ((-σ) * (k : ℝ)) := by ring_nf
                        _ = ((2 : ℝ) ^ (-σ)) ^ (k : ℝ) := by
                              simpa [Real.rpow_mul h2] using (Real.rpow_mul h2 (-σ) (k : ℝ))
                        _ = ((2 : ℝ) ^ (-σ)) ^ k := by simp
                    simp [hpow']

          have : (Fintype.card (S (k + 1)) : ℝ) * (t⁻¹ ^ σ)
              ≤ A * q ^ k + B * qσ ^ k := by
            -- (verbatim from the end of `lindelof_zero_exponent`)
            have hlogBk : Real.log Bk = C1 * (1 + R) ^ τ + Real.log M0 := by
              have hexp_pos : 0 < Real.exp (C1 * (1 + R) ^ τ) := Real.exp_pos _
              have hlog_mul : Real.log (Real.exp (C1 * (1 + R) ^ τ) * M0)
                    = Real.log (Real.exp (C1 * (1 + R) ^ τ)) + Real.log M0 := by
                exact Real.log_mul (ne_of_gt hexp_pos) (ne_of_gt hM0_pos)
              simp [Bk, hlog_mul]
            have hcard_le' :
                (Fintype.card (S (k+1)) : ℝ)
                  ≤ (C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1 := by
              have : Real.log Bk / log2 = (C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 := by
                calc
                  Real.log Bk / log2 = (C1 * (1 + R) ^ τ + Real.log M0) / log2 := by simp [hlogBk]
                  _ = (C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 := by
                        field_simp [hlog2_ne]
              have hcard_S' : (Fintype.card (S (k + 1)) : ℝ) ≤ Real.log Bk / log2 + 1 := hcard_S
              simpa [this, add_assoc, add_left_comm, add_comm] using hcard_S'

            have ht_scale' : t⁻¹ ^ σ = (r0 ^ (-σ)) * qσ ^ k := by simp [qσ, ht_scale]

            have hL :
                (Fintype.card (S (k+1)) : ℝ) * (t⁻¹ ^ σ)
                  ≤ ((C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (t⁻¹ ^ σ) := by
              exact mul_le_mul_of_nonneg_right hcard_le' (by
                have : 0 ≤ t⁻¹ ^ σ := Real.rpow_nonneg (inv_nonneg.mpr (mul_nonneg (le_of_lt hr0pos) (by positivity))) σ
                exact this)
            rw [ht_scale'] at hL ⊢

            have hstep1 :
                ((C1 * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k) ≤ A * q ^ k := by
              have hpow_le' : (1 + R) ^ τ ≤ (1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ := by
                have hk1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
                have hR_le : (1 : ℝ) + R ≤ (1 + 4 * r0) * (2 : ℝ) ^ k := by
                  have h2pow2 : (2 : ℝ) ^ ((k : ℝ) + 1) = (2 : ℝ) * (2 : ℝ) ^ k := by
                    have h2 : (0 : ℝ) < 2 := by norm_num
                    calc
                      (2 : ℝ) ^ ((k : ℝ) + 1)
                          = (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ (1 : ℝ) := by
                              simpa using (Real.rpow_add h2 (k : ℝ) (1 : ℝ))
                      _ = (2 : ℝ) ^ k * (2 : ℝ) := by simp
                      _ = (2 : ℝ) * (2 : ℝ) ^ k := by ring
                  have hR_eq : R = (4 * r0) * (2 : ℝ) ^ k := by
                    dsimp [R, r]
                    calc
                      (2 : ℝ) * (r0 * (2 : ℝ) ^ ((k : ℝ) + 1))
                          = (2 : ℝ) * (r0 * ((2 : ℝ) * (2 : ℝ) ^ k)) := by simp [h2pow2]
                      _ = (4 * r0) * (2 : ℝ) ^ k := by ring
                  calc
                    (1 : ℝ) + R = 1 + (4 * r0) * (2 : ℝ) ^ k := by simp [hR_eq]
                    _ ≤ (2 : ℝ) ^ k + (4 * r0) * (2 : ℝ) ^ k := by gcongr
                    _ = (1 + 4 * r0) * (2 : ℝ) ^ k := by ring
                have hbaseR : 0 ≤ (1 + 4 * r0 : ℝ) := by linarith [le_of_lt hr0pos]
                have hbase2 : 0 ≤ (2 : ℝ) ^ k := by positivity
                have hpow : ((1 : ℝ) + R) ^ τ ≤ ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ τ :=
                  Real.rpow_le_rpow (by positivity) hR_le hτ_nonneg
                have hsplit : ((1 + 4 * r0) * (2 : ℝ) ^ k) ^ τ
                    = (1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ := by
                  simp [Real.mul_rpow hbaseR hbase2]
                exact le_trans hpow (by simp [hsplit])
              have hq : q = (2 : ℝ) ^ τ * (2 : ℝ) ^ (-σ) := by
                have h2pos : (0 : ℝ) < 2 := by norm_num
                have : (τ - σ) = τ + (-σ) := by ring
                calc
                  q = (2 : ℝ) ^ (τ + (-σ)) := by simp [q, this]
                  _ = (2 : ℝ) ^ τ * (2 : ℝ) ^ (-σ) := by simpa using (Real.rpow_add h2pos τ (-σ))
              have h2powτ : ((2 : ℝ) ^ k) ^ τ = ((2 : ℝ) ^ τ) ^ k := by
                have h2 : 0 ≤ (2 : ℝ) := by norm_num
                calc
                  ((2 : ℝ) ^ k) ^ τ = (2 : ℝ) ^ ((k : ℝ) * τ) := by
                        have := Real.rpow_mul h2 (k : ℝ) τ
                        simpa using this.symm
                  _ = (2 : ℝ) ^ (τ * (k : ℝ)) := by ring_nf
                  _ = ((2 : ℝ) ^ τ) ^ k := by simp [Real.rpow_mul h2]
              have hqk' : q ^ k = ((2 : ℝ) ^ τ) ^ k * (qσ ^ k) := by
                simp [q, qσ, hq, mul_pow, mul_comm]
              have hgrow : (1 + R) ^ τ * (qσ ^ k) ≤ (1 + 4 * r0) ^ τ * (q ^ k) := by
                calc
                  (1 + R) ^ τ * (qσ ^ k)
                      ≤ ((1 + 4 * r0) ^ τ * ((2 : ℝ) ^ k) ^ τ) * (qσ ^ k) := by gcongr
                  _ = (1 + 4 * r0) ^ τ * (((2 : ℝ) ^ k) ^ τ * (qσ ^ k)) := by ring
                  _ = (1 + 4 * r0) ^ τ * (((2 : ℝ) ^ τ) ^ k * (qσ ^ k)) := by simp [h2powτ]
                  _ = (1 + 4 * r0) ^ τ * (q ^ k) := by simp [hqk']
              calc
                ((C1 * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k)
                    = (C1 / log2) * ((1 + R) ^ τ * (qσ ^ k)) * (r0 ^ (-σ)) := by
                        field_simp [hlog2_ne]
                _ ≤ (C1 / log2) * ((1 + 4 * r0) ^ τ * (q ^ k)) * (r0 ^ (-σ)) := by
                      gcongr
                _ = A * q ^ k := by
                      simp [A, mul_assoc, mul_left_comm, mul_comm]
            have hstep2 :
                ((Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k) ≤ B * qσ ^ k := by
              simp [B, mul_assoc, mul_left_comm, mul_comm]
            have hsum :
                ((C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k)
                  ≤ A * q ^ k + B * qσ ^ k := by
              calc
                ((C1 * (1 + R) ^ τ) / log2 + (Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k)
                    = ((C1 * (1 + R) ^ τ) / log2) * (r0 ^ (-σ) * qσ ^ k)
                        + ((Real.log M0) / log2 + 1) * (r0 ^ (-σ) * qσ ^ k) := by ring
                _ ≤ A * q ^ k + B * qσ ^ k := by gcongr
            exact le_trans hL hsum

          exact le_trans hshell_sum this
        ) hmajor

  -- Conclude from `summable_partition`.
  have := (summable_partition (f := fun n : ℕ => ‖zeros n‖⁻¹ ^ σ) hnonneg (s := S) hS)
  exact (this.2 hshell)

/-- A zero-free entire function with polynomial growth is exp of a polynomial.

If H is entire, zero-free, and `|H(z)| ≤ exp(C * (1 + |z|)^n)` for some `C` and `n`,
then H = exp(P) for some polynomial P of degree at most n. -/
theorem zero_free_polynomial_growth_is_exp_poly {H : ℂ → ℂ} {n : ℕ}
    (hH : Differentiable ℂ H)
    (h_nonzero : ∀ z, H z ≠ 0)
    (h_bound : ∃ C > 0, ∀ z, ‖H z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ n)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n ∧ ∀ z, H z = exp (Polynomial.eval z P) := by
  classical
  rcases h_bound with ⟨C, hCpos, hC⟩

  -- Step 1: build a global holomorphic logarithm by integrating the logarithmic derivative.
  let L : ℂ → ℂ := fun z => deriv H z / H z
  have hderivH : Differentiable ℂ (deriv H) := by
    intro z
    exact ((hH.analyticAt z).deriv).differentiableAt
  have hL : Differentiable ℂ L := by
    simpa [L] using (hderivH.div hH h_nonzero)

  -- A global primitive of `L`, defined by wedge integrals from `0`.
  let h : ℂ → ℂ := fun z => Complex.wedgeIntegral (0 : ℂ) z L
  have hh_deriv : ∀ z, HasDerivAt h (L z) z := by
    intro z
    -- Apply Morera's theorem on the ball `ball 0 (‖z‖ + 1)`.
    let r : ℝ := ‖z‖ + 1
    have hrpos : 0 < r := by
      dsimp [r]
      linarith [norm_nonneg z]
    have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
      have : dist z (0 : ℂ) < r := by
        simp [r, dist_zero_right]
      simpa [Metric.mem_ball] using this
    have hconserv : Complex.IsConservativeOn L (Metric.ball (0 : ℂ) r) :=
      (hL.differentiableOn).isConservativeOn
    have hcont : ContinuousOn L (Metric.ball (0 : ℂ) r) :=
      hL.continuous.continuousOn
    simpa [h, r] using hconserv.hasDerivAt_wedgeIntegral (f_cont := hcont) (hz := hz_ball)
  have hh : Differentiable ℂ h := fun z => (hh_deriv z).differentiableAt
  have hderiv_h : ∀ z, deriv h z = L z := fun z => (hh_deriv z).deriv

  -- Step 2: show `H = exp(k)` for an entire `k`.
  let k : ℂ → ℂ := fun z => h z + Complex.log (H 0)
  have hk : Differentiable ℂ k := hh.add_const (Complex.log (H 0))

  have hk_exp : ∀ z, H z = Complex.exp (k z) := by
    -- Consider `F = exp(k) / H`. Its derivative is zero, hence it's constant.
    let F : ℂ → ℂ := fun z => Complex.exp (k z) / H z
    have hF_deriv : ∀ z, deriv F z = 0 := by
      intro z
      have hH_has : HasDerivAt H (deriv H z) z := (hH z).hasDerivAt
      have hk_has : HasDerivAt k (L z) z := by
        -- `k' = h'` since the constant term has derivative 0
        have hh_has : HasDerivAt h (L z) z := hh_deriv z
        simpa [k, L] using hh_has.add_const (Complex.log (H 0))
      have hExp : HasDerivAt (fun w => Complex.exp (k w)) (Complex.exp (k z) * L z) z :=
        (HasDerivAt.cexp hk_has)
      have hDiv := (HasDerivAt.div hExp hH_has (h_nonzero z))
      -- simplify the quotient-rule formula using `L z = H'(z)/H(z)`
      have :
          deriv F z =
            ((Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z) / (H z) ^ 2 := by
        simpa [F] using hDiv.deriv
      rw [this]
      -- `((exp(k) * (H'/H)) * H - exp(k) * H') / H^2 = 0`
      have hnum :
          (Complex.exp (k z) * L z) * H z - Complex.exp (k z) * deriv H z = 0 := by
        -- cancel `H z` inside `L z = H'/H`
        dsimp [L]
        field_simp [h_nonzero z]
        ring
      simp [hnum]
    have hF_diff : Differentiable ℂ F := by
      -- `F = exp(k) / H`
      exact (hk.cexp).div hH h_nonzero
    have hF_const : ∀ z, F z = F 0 := by
      intro z
      exact is_const_of_deriv_eq_zero hF_diff hF_deriv z 0
    have hF0 : F 0 = 1 := by
      -- `h 0 = 0`, so `k 0 = log(H 0)` and `exp(k 0) / H 0 = 1`.
      have hh0 : h 0 = 0 := by simp [h, Complex.wedgeIntegral]
      have hk0 : k 0 = Complex.log (H 0) := by simp [k, hh0]
      have hH0 : H 0 ≠ 0 := h_nonzero 0
      simp [F, hk0, Complex.exp_log hH0, hH0]
    intro z
    have : F z = 1 := by simpa [hF0] using (hF_const z)
    -- rearrange `F z = exp(k z)/H z = 1`
    have hHz : H z ≠ 0 := h_nonzero z
    have : Complex.exp (k z) / H z = 1 := by simpa [F] using this
    -- multiply through by `H z`
    have : Complex.exp (k z) = H z := by
      -- `a / b = 1` implies `a = b`
      field_simp [hHz] at this
      simpa using this
    exact this.symm

  -- Step 3: show all derivatives of `k` above order `n` vanish, hence `k` is a polynomial.
  have hk_re_bound : ∀ z, (k z).re ≤ C * (1 + ‖z‖) ^ n := by
    intro z
    -- From `H z = exp(k z)` and the growth bound on `H`.
    have hHz : H z ≠ 0 := h_nonzero z
    have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr hHz
    have hlog_le : Real.log ‖H z‖ ≤ C * (1 + ‖z‖) ^ n := by
      have := Real.log_le_log hpos (hC z)
      simpa [Real.log_exp] using this
    have hlog_eq : Real.log ‖H z‖ = (k z).re := by
      have : ‖H z‖ = Real.exp (k z).re := by
        simpa [hk_exp z] using (Complex.norm_exp (k z))
      calc
        Real.log ‖H z‖ = Real.log (Real.exp (k z).re) := by simp [this]
        _ = (k z).re := by simp
    -- conclude
    simpa [hlog_eq] using hlog_le

  have hk_iteratedDeriv_eq_zero : ∀ m : ℕ, n < m → iteratedDeriv m k 0 = 0 := by
    intro m hm
    -- Use Cauchy estimate on `k - k 0` with radii `R` and `r = R/2`, then send `R → ∞`.
    have hm' : 0 < (m - n : ℕ) := Nat.sub_pos_of_lt hm
    have hmne : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 hm')
    -- Work with `f = k - k 0`, which vanishes at `0`.
    let f : ℂ → ℂ := fun z => k z - k 0
    have hf : Differentiable ℂ f := hk.sub_const (k 0)
    have hf0 : f 0 = 0 := by simp [f]
    -- First bound: `Re(f z) ≤ C * (1+R)^n + ‖k 0‖` on `‖z‖ ≤ R`.
    have hf_re_bound : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R → (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
      intro R hRpos z hzR
      have hkz : (k z).re ≤ C * (1 + ‖z‖) ^ n := hk_re_bound z
      have hkz' : (k z).re ≤ C * (1 + R) ^ n := by
        have h1 : (1 + ‖z‖ : ℝ) ≤ 1 + R := by linarith
        have hpow : (1 + ‖z‖ : ℝ) ^ n ≤ (1 + R) ^ n :=
          pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 n
        exact hkz.trans (mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos))
      -- `Re(f z) = Re(k z) - Re(k 0) ≤ C (1+R)^n + ‖k 0‖`.
      have hRe0 : -(k 0).re ≤ ‖k 0‖ := by
        have habs : |(k 0).re| ≤ ‖k 0‖ := Complex.abs_re_le_norm (k 0)
        have hneg : -(k 0).re ≤ |(k 0).re| := by
          simpa using (neg_le_abs (k 0).re)
        exact hneg.trans habs
      -- assemble
      have : (f z).re ≤ C * (1 + R) ^ n + ‖k 0‖ := by
        -- `Re(f z) = Re(k z) - Re(k 0)`
        have : (f z).re = (k z).re - (k 0).re := by simp [f, sub_eq_add_neg]
        -- use `hkz'` and `hRe0`
        nlinarith [this, hkz', hRe0]
      exact this

    -- Apply Borel–Carathéodory to get a norm bound for `f` on `‖z‖ ≤ R/2`.
    have hf_bound_on_ball : ∀ R : ℝ, 0 < R →
        ∀ z, ‖z‖ ≤ R / 2 → ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
      intro R hRpos z hz
      have hR2pos : 0 < R / 2 := by nlinarith
      have hlt : R / 2 < R := by nlinarith
      have hMpos : 0 < (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        have : 0 ≤ C * (1 + R) ^ n := by
          refine mul_nonneg (le_of_lt hCpos) ?_
          exact pow_nonneg (by linarith) _
        nlinarith [this, norm_nonneg (k 0)]
      have hf_anal : AnalyticOnNhd ℂ f (Metric.closedBall 0 R) := by
        intro w hw
        exact (hf.analyticAt w)
      have hf_re : ∀ w, ‖w‖ ≤ R → (f w).re ≤ (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro w hw
        have := hf_re_bound R hRpos w hw
        linarith
      have hf_bc :=
        borel_caratheodory_bound (f := f) (r := R / 2) (R := R)
          (M := (C * (1 + R) ^ n + ‖k 0‖ + 1))
          hf_anal hR2pos hlt hMpos hf0 hf_re z hz
      -- simplify the constant `2*M*r/(R-r)` at `r=R/2`
      have hconst :
          2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) * (R / 2) / (R - R / 2)
            = 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        field_simp [hRpos.ne'] ; ring
      -- finish
      simpa [hconst] using hf_bc

    -- Use Cauchy estimate for iterated derivatives of `f` on the circle of radius `R/2`.
    have hCauchy : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv m f 0‖ ≤
          (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m := by
      intro R hRpos
      have hR2pos : 0 < R / 2 := by nlinarith
      have hf_diffCont : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) (R / 2)) := hf.diffContOnCl
      have hbound_sphere :
          ∀ z ∈ Metric.sphere (0 : ℂ) (R / 2),
            ‖f z‖ ≤ 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1) := by
        intro z hz
        have hz' : ‖z‖ ≤ R / 2 := by
          simpa [Metric.mem_sphere, dist_zero_right] using (le_of_eq hz)
        exact hf_bound_on_ball R hRpos z hz'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := m) (c := (0 : ℂ))
          (R := R / 2) (C := 2 * (C * (1 + R) ^ n + ‖k 0‖ + 1))
          (hR := hR2pos) hf_diffCont hbound_sphere)

    -- Let `R → ∞`: the Cauchy bound tends to `0` for `m > n`, forcing `iteratedDeriv m f 0 = 0`.
    have hf_iter_eq : iteratedDeriv m f 0 = 0 := by
      by_contra hne
      have ha : 0 < ‖iteratedDeriv m f 0‖ := norm_pos_iff.2 hne

      let RHS : ℝ → ℝ := fun R =>
        (m.factorial : ℝ) * (2 * (C * (1 + R) ^ n + ‖k 0‖ + 1)) / (R / 2) ^ m
      have hle_RHS : ∀ R : ℝ, 0 < R → ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        intro R hRpos
        simpa [RHS] using hCauchy R hRpos

      -- Show `RHS R → 0` as `R → ∞`.
      have hRHS_tendsto : Tendsto RHS atTop (𝓝 0) := by
        -- First show `(C * (1+R)^n + K) / (R/2)^m → 0` for `K = ‖k 0‖ + 1`.
        let K : ℝ := ‖k 0‖ + 1
        have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
        have hm0 : m ≠ 0 := ne_of_gt hmpos

        have hratio : Tendsto (fun R : ℝ => R ^ n / (R / 2) ^ m) atTop (𝓝 0) := by
          -- Rewrite `R^n/(R/2)^m = 2^m * (R^n / R^m)` and use `m > n`.
          have hident :
              (fun R : ℝ => R ^ n / (R / 2) ^ m) = fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m) := by
            funext R
            simp [div_eq_mul_inv, mul_pow, mul_assoc, mul_comm]
          have hmain : Tendsto (fun R : ℝ => R ^ n / R ^ m) atTop (𝓝 0) := by
            have hp : m - n ≠ 0 := (Nat.pos_iff_ne_zero.1 (Nat.sub_pos_of_lt hm))
            have hmain' : Tendsto (fun R : ℝ => (R ^ (m - n))⁻¹) atTop (𝓝 0) := by
              simpa using (tendsto_pow_neg_atTop (𝕜 := ℝ) (n := m - n) hp)
            have hEq : (fun R : ℝ => (R ^ (m - n))⁻¹) =ᶠ[atTop] fun R : ℝ => R ^ n / R ^ m := by
              have hEq' : (fun R : ℝ => R ^ n / R ^ m) =ᶠ[atTop] fun R : ℝ => (R ^ (m - n))⁻¹ := by
                filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
                have hle : n ≤ m := le_of_lt hm
                have hm_eq : n + (m - n) = m := Nat.add_sub_of_le hle
                have hn0 : R ^ n ≠ 0 := pow_ne_zero n hR
                calc
                  R ^ n / R ^ m = R ^ n / R ^ (n + (m - n)) := by simp [hm_eq]
                  _ = R ^ n * ((R ^ (m - n))⁻¹ * (R ^ n)⁻¹) := by
                        simp [pow_add, div_eq_mul_inv, mul_comm]
                  _ = (R ^ (m - n))⁻¹ := by
                        ring_nf
                        simp [hn0]
              exact hEq'.symm
            exact Filter.Tendsto.congr' hEq hmain'
          have : Tendsto (fun R : ℝ => (2 : ℝ) ^ m * (R ^ n / R ^ m)) atTop (𝓝 ((2 : ℝ) ^ m * 0)) :=
            tendsto_const_nhds.mul hmain
          simpa [hident] using this

        have hinv : Tendsto (fun R : ℝ => ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          have hdiv : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
            (tendsto_id.atTop_div_const (r := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2))
          have hpow : Tendsto (fun R : ℝ => (R / 2) ^ m) atTop atTop :=
            (Filter.tendsto_pow_atTop (α := ℝ) (n := m) hm0).comp hdiv
          simpa using hpow.inv_tendsto_atTop

        -- Upgrade `R^n/(R/2)^m → 0` to `(1+R)^n/(R/2)^m → 0` using the factor `((1+R)/R)^n → 1`.
        have hdiv : Tendsto (fun R : ℝ => (1 + R) / R) atTop (𝓝 (1 : ℝ)) := by
          have hinv : Tendsto (fun R : ℝ => (R : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
            tendsto_inv_atTop_zero
          have hadd : Tendsto (fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹) atTop (𝓝 (1 : ℝ)) := by
            simpa using (tendsto_const_nhds.add hinv)
          have hEq : (fun R : ℝ => (1 + R) / R) =ᶠ[atTop] fun R : ℝ => (1 : ℝ) + (R : ℝ)⁻¹ := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            -- `((1+R)/R) = 1 + 1/R` for `R ≠ 0`.
            field_simp [hR]
            ring
          exact Filter.Tendsto.congr' hEq.symm hadd
        have hdiv_pow : Tendsto (fun R : ℝ => ((1 + R) / R) ^ n) atTop (𝓝 (1 : ℝ)) := by
          simpa using (hdiv.pow n)
        have hone_add_ratio :
            Tendsto (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m) atTop (𝓝 (0 : ℝ)) := by
          have hEq :
              (fun R : ℝ => (1 + R) ^ n / (R / 2) ^ m)
                =ᶠ[atTop] fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) := by
            filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
            -- algebraic identity valid for `R ≠ 0`
            have hRpow : (R ^ n : ℝ) ≠ 0 := pow_ne_zero n hR
            -- `((1+R)/R)^n * (R^n/(R/2)^m) = (1+R)^n/(R/2)^m`
            have hident :
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m) = (1 + R) ^ n / (R / 2) ^ m := by
              calc
                ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)
                    = ((1 + R) ^ n / R ^ n) * (R ^ n / (R / 2) ^ m) := by
                        simp [div_pow]
                _ = ((1 + R) ^ n * R ^ n) / (R ^ n * (R / 2) ^ m) := by
                        simp [div_mul_div_comm, mul_comm]
                _ = ((1 + R) ^ n * R ^ n) / ((R / 2) ^ m * R ^ n) := by
                        simp [mul_comm]
                _ = (1 + R) ^ n / (R / 2) ^ m := by
                        simpa [mul_assoc, mul_comm, mul_left_comm] using
                          (mul_div_mul_right (a := (1 + R) ^ n) (b := (R / 2) ^ m) hRpow)
            exact hident.symm
          have hmul :
              Tendsto (fun R : ℝ => ((1 + R) / R) ^ n * (R ^ n / (R / 2) ^ m)) atTop (𝓝 (0 : ℝ)) := by
            simpa [mul_zero] using (hdiv_pow.mul hratio)
          exact Filter.Tendsto.congr' hEq.symm hmul

        have h1 : Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hone_add_ratio)
        have h2 : Tendsto (fun R : ℝ => K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (tendsto_const_nhds.mul hinv)
        have hsum :
            Tendsto (fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹) atTop (𝓝 0) := by
          simpa using (h1.add h2)
        have hrew :
            (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m)
              = fun R : ℝ => C * ((1 + R) ^ n / (R / 2) ^ m) + K * ((R / 2) ^ m)⁻¹ := by
          funext R
          simp [div_eq_mul_inv, mul_add, mul_assoc, mul_comm]
        have hbase : Tendsto (fun R : ℝ => (C * (1 + R) ^ n + K) / (R / 2) ^ m) atTop (𝓝 0) := by
          simpa [hrew] using hsum

        -- Multiply by the constant `(m!)*2` and rewrite to `RHS`.
        have hconst :
            Tendsto (fun _ : ℝ => (m.factorial : ℝ) * (2 : ℝ)) atTop (𝓝 ((m.factorial : ℝ) * (2 : ℝ))) :=
          tendsto_const_nhds
        have hmul : Tendsto (fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m)) atTop (𝓝 0) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using (hconst.mul hbase)
        have hRHS_rw : RHS = fun R : ℝ => ((m.factorial : ℝ) * (2 : ℝ)) *
              ((C * (1 + R) ^ n + K) / (R / 2) ^ m) := by
          funext R
          dsimp [RHS, K]
          ring_nf
        simpa [hRHS_rw] using hmul

      -- `RHS R → 0`, so eventually `RHS R < ‖iteratedDeriv m f 0‖ / 2`.
      have hsmall : ∀ᶠ R in atTop, RHS R < ‖iteratedDeriv m f 0‖ / 2 :=
        (tendsto_order.1 hRHS_tendsto).2 _ (half_pos ha)
      have hle_eventually : ∀ᶠ R in atTop, ‖iteratedDeriv m f 0‖ ≤ RHS R := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hRpos
        exact hle_RHS R hRpos
      rcases (hle_eventually.and hsmall).exists with ⟨R, hle, hlt⟩
      have : ‖iteratedDeriv m f 0‖ < ‖iteratedDeriv m f 0‖ := by
        exact (lt_of_le_of_lt hle hlt).trans (half_lt_self ha)
      exact lt_irrefl _ this

    -- Transfer back from `f = k - k 0` to `k` (derivatives of constants vanish for `m > 0`).
    have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hm
    have hm0 : m ≠ 0 := ne_of_gt hmpos
    have hkcd : ContDiffAt ℂ (↑m) k (0 : ℂ) := (hk.analyticAt 0).contDiffAt
    have hccd : ContDiffAt ℂ (↑m) (fun _ : ℂ => k 0) (0 : ℂ) := contDiffAt_const
    have hsub : iteratedDeriv m f 0 = iteratedDeriv m k 0 - iteratedDeriv m (fun _ : ℂ => k 0) 0 := by
      simpa [f] using (iteratedDeriv_sub (n := m) (x := (0 : ℂ)) hkcd hccd)
    have hconst0 : iteratedDeriv m (fun _ : ℂ => k 0) 0 = 0 := by
      simp [iteratedDeriv_const, hm0]
    have hf_eq : iteratedDeriv m f 0 = iteratedDeriv m k 0 := by
      simp [hsub, hconst0]
    simpa [hf_eq] using hf_iter_eq

  -- Step 4: build the polynomial from the Taylor coefficients at 0 and finish.
  let P : Polynomial ℂ :=
    ∑ m ∈ Finset.range (n + 1), Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)
  have hPdeg : P.natDegree ≤ n := by
    -- A finset sum of monomials indexed by `range (n+1)` has `natDegree ≤ n`.
    have hnat :
        P.natDegree ≤
          Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) := by
      simpa [P, Function.comp] using
        (Polynomial.natDegree_sum_le (s := Finset.range (n + 1))
          (f := fun m : ℕ =>
            Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)))
    have hfold :
        Finset.fold max 0
            (fun m : ℕ =>
              (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
            (Finset.range (n + 1)) ≤ n := by
      -- `fold max` is bounded by `n` since each monomial has `natDegree ≤ m ≤ n` on this range.
      refine (Finset.fold_max_le (f := fun m : ℕ =>
        (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree)
        (b := 0) (s := Finset.range (n + 1)) (c := n)).2 ?_
      refine ⟨Nat.zero_le n, ?_⟩
      intro m hm
      have hmon :
          (Polynomial.monomial m ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0)).natDegree ≤ m :=
        Polynomial.natDegree_monomial_le _
      have hm_le : m ≤ n := Nat.le_of_lt_succ (Finset.mem_range.1 hm)
      exact hmon.trans hm_le
    exact hnat.trans hfold
  have hk_poly : ∀ z, k z = Polynomial.eval z P := by
    intro z
    -- Taylor series of an entire function, then truncate using vanishing of higher derivatives.
    have htaylor := Complex.taylorSeries_eq_of_entire' (c := (0 : ℂ)) (z := z) hk
    have htail : ∀ m : ℕ, m ∉ Finset.range (n + 1) →
        ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m) = 0 := by
      intro m hm'
      have hmgt : n < m := by
        have : n + 1 ≤ m := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hm')
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) this
      have hz : iteratedDeriv m k 0 = 0 := hk_iteratedDeriv_eq_zero m hmgt
      simp [hz]
    have htsum :
        (∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m)
          = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      simpa [sub_zero] using (tsum_eq_sum (s := Finset.range (n + 1)) htail)
    have hfinite :
        k z = ∑ m ∈ Finset.range (n + 1), (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * z ^ m := by
      calc
        k z = ∑' m : ℕ, (m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0 * (z - 0) ^ m := by
          simpa using htaylor.symm
        _ = _ := htsum
    -- Evaluate the polynomial `P` and match the finite sum (commuting factors as needed).
    have hEval :
        Polynomial.eval z P =
          ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      classical
      -- Work with `eval₂RingHom` to avoid simp loops around `Polynomial.eval`.
      change Polynomial.eval₂ (RingHom.id ℂ) z P = _
      let φ : Polynomial ℂ →+* ℂ := Polynomial.eval₂RingHom (RingHom.id ℂ) z
      change φ P = _
      -- `eval₂` of a monomial is `coeff * z^m`; commute to `z^m * coeff`.
      simp [P, φ, Polynomial.eval₂_monomial, mul_comm]
    have hfinite' :
        k z = ∑ m ∈ Finset.range (n + 1), z ^ m * ((m.factorial : ℂ)⁻¹ * iteratedDeriv m k 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfinite
    simpa [hEval] using hfinite'

  refine ⟨P, hPdeg, ?_⟩
  intro z
  have : H z = Complex.exp (k z) := by simp [hk_exp z]
  -- `k = P.eval` gives `H = exp(P.eval)`
  simp [this, hk_poly z]

/-! ## Part 6: The Hadamard Factorization Theorem -/

/-
`hadamard_quotient_growth_bound` is the main analytic input needed to finish Hadamard’s
factorization theorem.

It should prove a global growth estimate for the zero-free quotient

`H(z) = f(z) / (z^ord0 * ∏' n, weierstrassFactor m (z / zeros n))`
-/

/-! ## Helper inequalities: `log⁺` vs `log (1 + ·)` -/

lemma posLog_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    log⁺ x ≤ Real.log (1 + x) := by
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    -- `log⁺ x = max 0 (log x)` and `0 ≤ log (1 + x)` and `log x ≤ log (1 + x)`
    have h0 : 0 ≤ Real.log (1 + x) := by
      have : (1 : ℝ) ≤ 1 + x := by linarith
      exact Real.log_nonneg this
    have hlog : Real.log x ≤ Real.log (1 + x) := by
      have hx1 : x ≤ 1 + x := by linarith
      exact Real.log_le_log hx_pos hx1
    -- `max 0 (log x) ≤ log (1 + x)`
    simpa [Real.posLog, max_le_iff] using And.intro h0 hlog

lemma posLog_norm_le_log_one_add_norm (z : ℂ) :
    log⁺ ‖z‖ ≤ Real.log (1 + ‖z‖) :=
  posLog_le_log_one_add (x := ‖z‖) (norm_nonneg z)

/-- On any circle, the circle average of `log⁺ ‖F⁻¹‖` equals the circle average of
`log⁺ ‖F‖` minus the circle average of `log ‖F‖`.

Precisely:
`circleAverage (log⁺ ‖F⁻¹‖) c r = circleAverage (log⁺ ‖F‖) c r - circleAverage (log ‖F‖) c r`.
This is just the pointwise identity `log⁺ x - log⁺ x⁻¹ = log x` averaged over the circle. -/
lemma circleAverage_posLog_norm_inv_eq_circleAverage_posLog_norm_sub_circleAverage_log_norm
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (h_pos : CircleIntegrable (fun z ↦ log⁺ ‖F z‖) c r)
    (h_inv : CircleIntegrable (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r)
    (_h_log : CircleIntegrable (fun z ↦ Real.log ‖F z‖) c r) :
    circleAverage (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r
      = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
          - circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
  -- Pointwise identity on the circle
  have h_point :
      Set.EqOn
        (fun z : ℂ => (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖))
        (fun z : ℂ => Real.log ‖F z‖)
        (Metric.sphere c |r|) := by
    intro z _
    simpa [norm_inv] using (Real.posLog_sub_posLog_inv (x := ‖F z‖))
  -- Average of the difference equals difference of averages
  have h_sub :
      circleAverage (fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖)) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ log⁺ ‖(F z)⁻¹‖) c r := by
    simpa using (Real.circleAverage_sub (c := c) (R := r) h_pos h_inv)
  -- Replace the LHS integrand using the pointwise identity on the sphere
  have h_congr :
      circleAverage (fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖)) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    simpa using
      (circleAverage_congr_sphere (f₁ := fun z ↦ (log⁺ ‖F z‖) - (log⁺ ‖(F z)⁻¹‖))
        (f₂ := fun z ↦ Real.log ‖F z‖) (c := c) (R := r) h_point)
  -- Rearrange to solve for the average of `log⁺ ‖F⁻¹‖`.
  have h_sub' :
      circleAverage (fun z ↦ log⁺ ‖F z‖ - log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r := by
    simpa [norm_inv] using h_sub
  have h_congr' :
      circleAverage (fun z ↦ log⁺ ‖F z‖ - log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    simpa [norm_inv] using h_congr
  have hdiff :
      circleAverage (fun z ↦ log⁺ ‖F z‖) c r - circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    exact h_sub'.symm.trans h_congr'
  have hfinal :
      circleAverage (fun z ↦ log⁺ ‖F z‖⁻¹) c r
        = circleAverage (fun z ↦ log⁺ ‖F z‖) c r
            - circleAverage (fun z ↦ Real.log ‖F z‖) c r := by
    linarith [hdiff]
  simpa [norm_inv] using hfinal

/-! ## Circle-average bounds from `EntireOfFiniteOrder` -/

lemma circleIntegrable_posLog_norm_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℝ) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 r := by
  -- Use the standard meromorphic integrability lemma (entire ⇒ meromorphic).
  have hA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  have hM : MeromorphicOn f (Set.univ : Set ℂ) := hA.meromorphicOn
  -- Restrict meromorphy to the sphere.
  have hMsphere : MeromorphicOn f (sphere (0 : ℂ) |r|) := fun z hz => hM z (by simp)
  simpa using (circleIntegrable_posLog_norm_meromorphicOn (c := (0 : ℂ)) (R := r) hMsphere)

lemma circleIntegrable_posLog_norm_of_entire_center
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z‖) c r := by
  -- Entire ⇒ meromorphic on `univ`, hence on every sphere
  have hA : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  have hM : MeromorphicOn f (Set.univ : Set ℂ) := hA.meromorphicOn
  have hMsphere : MeromorphicOn f (sphere c |r|) := fun z hz => hM z (by simp)
  simpa using (circleIntegrable_posLog_norm_meromorphicOn (c := c) (R := r) hMsphere)

lemma circleAverage_posLog_norm_le_of_entireOfFiniteOrder
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      circleAverage (fun z ↦ log⁺ ‖f z‖) 0 r ≤ C * (1 + r) ^ ρ := by
  rcases hf.growth with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  have h_int : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) 0 r :=
    circleIntegrable_posLog_norm_of_entire (f := f) hf.entire r
  -- Pointwise bound on the circle: `log⁺ ‖f z‖ ≤ log (1 + ‖f z‖) ≤ C * (1 + r)^ρ`.
  have h_pw : ∀ z ∈ sphere (0 : ℂ) |r|, log⁺ ‖f z‖ ≤ C * (1 + r) ^ ρ := by
    intro z hz
    have hz_norm : ‖z‖ = r := by
      have : ‖z‖ = |r| := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      simpa [abs_of_nonneg hr0] using this
    calc
      log⁺ ‖f z‖ ≤ Real.log (1 + ‖f z‖) := posLog_le_log_one_add (x := ‖f z‖) (norm_nonneg _)
      _ ≤ C * (1 + ‖z‖) ^ ρ := hC z
      _ = C * (1 + r) ^ ρ := by simp [hz_norm]
  -- Average is ≤ the constant.
  exact Real.circleAverage_mono_on_of_le_circle (c := (0 : ℂ)) (R := r) (f := fun z ↦ log⁺ ‖f z‖)
    h_int h_pw

lemma circleAverage_posLog_norm_le_of_entireOfFiniteOrder_center
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) (hρ_nonneg : 0 ≤ ρ) :
    ∃ C > 0, ∀ (c : ℂ) (r : ℝ), 0 ≤ r →
      circleAverage (fun z ↦ log⁺ ‖f z‖) c r ≤ C * (1 + ‖c‖ + r) ^ ρ := by
  rcases hf.growth with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro c r hr0
  -- Integrable on any circle centered at c
  have h_int : CircleIntegrable (fun z ↦ log⁺ ‖f z‖) c r :=
    circleIntegrable_posLog_norm_of_entire_center hf.entire c r
  -- On the sphere: ‖z‖ ≤ ‖c‖ + r, hence a uniform pointwise bound.
  have h_pw : ∀ z ∈ sphere c |r|, log⁺ ‖f z‖ ≤ C * (1 + ‖c‖ + r) ^ ρ := by
    intro z hz
    have hz_norm_le : ‖z‖ ≤ ‖c‖ + r := by
      have hz' : ‖z - c‖ = |r| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have htri : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
        have hcz : c + (z - c) = z := by
          calc
            c + (z - c) = c + z - c := by
              simp
            _ = z := by
              simp
        simpa [hcz] using (norm_add_le c (z - c))
      simpa [hz', abs_of_nonneg hr0] using htri
    calc
      log⁺ ‖f z‖ ≤ Real.log (1 + ‖f z‖) := posLog_le_log_one_add (x := ‖f z‖) (norm_nonneg _)
      _ ≤ C * (1 + ‖z‖) ^ ρ := hC z
      _ ≤ C * (1 + (‖c‖ + r)) ^ ρ := by
            have hbase : (1 + ‖z‖ : ℝ) ≤ 1 + (‖c‖ + r) := by linarith
            have hpow : (1 + ‖z‖ : ℝ) ^ ρ ≤ (1 + (‖c‖ + r)) ^ ρ :=
              Real.rpow_le_rpow (by positivity) hbase hρ_nonneg
            exact mul_le_mul_of_nonneg_left hpow (le_of_lt hCpos)
      _ = C * (1 + ‖c‖ + r) ^ ρ := by ring_nf
  exact Real.circleAverage_mono_on_of_le_circle (c := c) (R := r) (f := fun z ↦ log⁺ ‖f z‖)
    h_int h_pw

/-! ## ValueDistribution: basic bounds we can get “for free” from `EntireOfFiniteOrder` -/

open ValueDistribution

lemma characteristic_top_le_of_entireOfFiniteOrder
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      characteristic f ⊤ r ≤ C * (1 + r) ^ ρ + (logCounting f ⊤ r) := by
  rcases circleAverage_posLog_norm_le_of_entireOfFiniteOrder (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- `characteristic = proximity + logCounting`, and `proximity_top = circleAverage log⁺`.
  have hprox : proximity f ⊤ r ≤ C * (1 + r) ^ ρ := by
    -- Rewrite `proximity` and apply the circle-average bound from `EntireOfFiniteOrder`.
    simpa [ValueDistribution.proximity_top] using hC r hr0
  -- Add `logCounting f ⊤ r` on both sides.
  have := add_le_add_right hprox (logCounting f ⊤ r)
  -- Unfold `characteristic`.
  simpa [ValueDistribution.characteristic, add_assoc, add_comm, add_left_comm] using this

/-! ## Entire functions have no poles: `logCounting f ⊤ = 0` -/

lemma logCounting_top_eq_zero_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    logCounting f ⊤ = 0 := by
  -- Entire ⇒ analytic on a neighbourhood of `univ`
  have hf_an : AnalyticOnNhd ℂ f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable).2 hf
  -- Hence the divisor is nonnegative, so the negative part (pole divisor) is zero.
  have hDnonneg : 0 ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf_an
  have hneg : (MeromorphicOn.divisor f (Set.univ : Set ℂ))⁻ = 0 := by
    ext z
    have hz : (0 : ℤ) ≤ MeromorphicOn.divisor f (Set.univ : Set ℂ) z := hDnonneg z
    -- `z ↦ divisor f univ z` is pointwise ≥ 0, hence its negative part vanishes.
    simp [negPart_eq_zero.2 hz]
  -- Rewrite `logCounting f ⊤` as the logCounting of the pole divisor.
  simp [ValueDistribution.logCounting_top, hneg]

/-! ## Characteristic bounds for entire functions of finite order -/

lemma characteristic_top_le_of_entireOfFiniteOrder'
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r → characteristic f ⊤ r ≤ C * (1 + r) ^ ρ := by
  rcases circleAverage_posLog_norm_le_of_entireOfFiniteOrder (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- For entire `f`, the pole-counting term vanishes.
  have hlog0 : logCounting f ⊤ r = 0 := by
    have hfun : logCounting f ⊤ = 0 := logCounting_top_eq_zero_of_entire (f := f) hf.entire
    simpa using congrArg (fun g : ℝ → ℝ => g r) hfun
  -- Unfold the characteristic and use the proximity bound.
  have hprox : proximity f ⊤ r ≤ C * (1 + r) ^ ρ := by
    simpa [ValueDistribution.proximity_top] using hC r hr0
  simpa [ValueDistribution.characteristic, hlog0] using (add_le_add_right hprox 0)

lemma characteristic_inv_top (f : ℂ → ℂ) :
    characteristic (f⁻¹) ⊤ = characteristic f 0 := by
  ext r
  simp [ValueDistribution.characteristic, ValueDistribution.proximity_inv, ValueDistribution.logCounting_inv]

lemma characteristic_zero_le_of_entireOfFiniteOrder'
    {ρ : ℝ} {f : ℂ → ℂ} (hf : EntireOfFiniteOrder ρ f) :
    ∃ C > 0, ∀ r : ℝ, 0 ≤ r →
      characteristic f 0 r ≤ C * (1 + r) ^ ρ +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
  -- Bound `characteristic f 0` by `characteristic f ⊤` plus an absolute constant,
  -- using the first part of the First Main Theorem.
  rcases characteristic_top_le_of_entireOfFiniteOrder' (hf := hf) with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro r hr0
  -- Meromorphy on `univ`
  have hf_mer : MeromorphicOn f (Set.univ : Set ℂ) :=
    (analyticOnNhd_univ_iff_differentiable.2 hf.entire).meromorphicOn
  -- Quantitative First Main Theorem bound:
  have hdiff :
      |characteristic f ⊤ r - characteristic (f⁻¹) ⊤ r|
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    ValueDistribution.characteristic_sub_characteristic_inv_le (f := f) (hf := hf_mer) (R := r)

  -- From `|A - B| ≤ K` we get `B ≤ A + K`.
  have hdiff' :
      |characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r|
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    simpa [abs_sub_comm] using hdiff
  have hsub :
      characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r
        ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    (le_abs_self _).trans hdiff'
  have hle_inv :
      characteristic (f⁻¹) ⊤ r ≤ characteristic f ⊤ r +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    by
      -- Rearrange `B = (B - A) + A` and use `B - A ≤ K`.
      have hrew :
          characteristic (f⁻¹) ⊤ r =
            (characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r) + characteristic f ⊤ r := by
        ring
      calc
        characteristic (f⁻¹) ⊤ r
            = (characteristic (f⁻¹) ⊤ r - characteristic f ⊤ r) + characteristic f ⊤ r := hrew
        _ ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| + characteristic f ⊤ r := by
              -- Add `characteristic f ⊤ r` on the right of `hsub`.
              have h := add_le_add_right hsub (characteristic f ⊤ r)
              simpa [add_assoc, add_comm, add_left_comm] using h
        _ = characteristic f ⊤ r + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
              ac_rfl
  have hle0 :
      characteristic f 0 r ≤ characteristic f ⊤ r +
        max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by
    -- rewrite `characteristic (f⁻¹) ⊤` as `characteristic f 0`
    simpa [characteristic_inv_top] using hle_inv

  -- Now use the growth bound for `characteristic f ⊤ r`.
  have htop : characteristic f ⊤ r ≤ C * (1 + r) ^ ρ := hC r hr0
  have htop' :
      characteristic f ⊤ r + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
        ≤ C * (1 + r) ^ ρ +
          max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
    by
      -- `A ≤ B` implies `A + K ≤ B + K`.
      simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right htop
        (max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)
  exact hle0.trans htop'

/-! ## Mean-value bounds: circle averages to pointwise bounds for harmonic functions -/

lemma harmonicOnNhd_le_circleAverage_pos
    {u : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |r|)) :
    u c ≤ circleAverage (fun z ↦ max (u z) 0) c r := by
  -- Mean value property: `circleAverage u c r = u c`.
  have hmean : circleAverage u c r = u c :=
    HarmonicOnNhd.circleAverage_eq (f := u) (c := c) (R := r) hu
  -- Pointwise: `u ≤ max u 0`, so the average is monotone.
  have hci_u : CircleIntegrable u c r := by
    -- Harmonicity implies `C²` and hence continuity on the sphere.
    have hcont_sphere : ContinuousOn u (Metric.sphere c |r|) := by
      intro z hz
      have hz_cb : z ∈ Metric.closedBall c |r| := sphere_subset_closedBall hz
      have hz_harm : InnerProductSpace.HarmonicAt u z := hu z hz_cb
      exact hz_harm.1.continuousAt.continuousWithinAt
    exact hcont_sphere.circleIntegrable'
  have hci_pos : CircleIntegrable (fun z ↦ max (u z) 0) c r := by
    have hcont_sphere_u : ContinuousOn u (Metric.sphere c |r|) := by
      intro z hz
      have hz_cb : z ∈ Metric.closedBall c |r| := sphere_subset_closedBall hz
      have hz_harm : InnerProductSpace.HarmonicAt u z := hu z hz_cb
      exact hz_harm.1.continuousAt.continuousWithinAt
    have hpair : ContinuousOn (fun z : ℂ => (u z, (0 : ℝ))) (Metric.sphere c |r|) :=
      hcont_sphere_u.prodMk (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℝ)) (Metric.sphere c |r|))
    have hmax : ContinuousOn (fun p : ℝ × ℝ => max p.1 p.2) (Set.univ : Set (ℝ × ℝ)) :=
      continuous_max.continuousOn
    have hcont_pos : ContinuousOn (fun z : ℂ => max (u z) 0) (Metric.sphere c |r|) := by
      -- compose `max` with the continuous pair map `(u,0)`.
      simpa [Function.comp, Set.MapsTo] using
        (hmax.comp hpair (by intro z hz; simp))
    exact hcont_pos.circleIntegrable'
  have hmono : circleAverage u c r ≤ circleAverage (fun z ↦ max (u z) 0) c r := by
    apply Real.circleAverage_mono hci_u hci_pos
    intro z hz
    exact le_max_left _ _
  -- Rewrite with the mean value property.
  simpa [hmean] using hmono

lemma norm_le_exp_circleAverage_posLog_of_entire_nonzero
    {H : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hH_entire : Differentiable ℂ H) (hH_nonzero : ∀ z, H z ≠ 0) :
    ‖H c‖ ≤ Real.exp (circleAverage (fun z ↦ log⁺ ‖H z‖) c r) := by
  -- Apply the previous lemma to `u(z) = log ‖H z‖`.
  let u : ℂ → ℝ := fun z => Real.log ‖H z‖
  have hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |r|) := by
    intro z hz
    have hAn : AnalyticAt ℂ H z := (hH_entire.analyticAt z)
    have hHz : H z ≠ 0 := hH_nonzero z
    -- `log ‖H‖` is harmonic at each point where `H ≠ 0`.
    exact (hAn.harmonicAt_log_norm hHz)
  have hle : u c ≤ circleAverage (fun z ↦ max (u z) 0) c r :=
    harmonicOnNhd_le_circleAverage_pos (u := u) (c := c) (r := r) hu
  -- Rewrite `max (log‖H‖) 0` as `log⁺ ‖H‖`.
  have hmax : (fun z ↦ max (u z) 0) = fun z ↦ log⁺ ‖H z‖ := by
    funext z
    simp [u, Real.posLog, max_comm]
  have hle' : Real.log ‖H c‖ ≤ circleAverage (fun z ↦ log⁺ ‖H z‖) c r := by
    simpa [u, hmax] using hle
  -- Exponentiate.
  have hpos : 0 < ‖H c‖ := norm_pos_iff.mpr (hH_nonzero c)
  exact (Real.log_le_iff_le_exp hpos).1 hle'

/-! ## ZeroData implies nontriviality (used to rule out `order = ⊤` cases) -/

lemma zeroData_not_all_zero {f : ℂ → ℂ} (hz : ZeroData f) : ¬ (∀ z : ℂ, f z = 0) := by
  intro hzero
  have hsubset : ({0}ᶜ : Set ℂ) ⊆ Set.range hz.zeros := by
    intro z hz0
    have hz' : f z = 0 := hzero z
    have hzspec := (hz.zero_spec z).1 hz'
    rcases hzspec with h0 | hnon0
    · exact False.elim (hz0 h0.1)
    · exact hnon0.2
  have hcount_range : (Set.range hz.zeros).Countable := Set.countable_range hz.zeros
  have hcount_compl : ({0}ᶜ : Set ℂ).Countable := hcount_range.mono hsubset
  have hcount_univ : (Set.univ : Set ℂ).Countable := by
    have h0c : ({0} : Set ℂ).Countable := Set.countable_singleton 0
    have : ({0} ∪ ({0}ᶜ) : Set ℂ).Countable := h0c.union hcount_compl
    simpa [Set.union_compl_self] using this
  exact not_countable_complex hcount_univ

open Complex Real BigOperators Finset Set Filter Topology Metric ValueDistribution
open scoped Topology

namespace ComplexAnalysis
namespace Hadamard

/-!
## Analytic Estimates for the Hadamard Quotient

We establish that the quotient `H = f / F` of an entire function by its canonical product
has finite order. This relies on bounding the characteristic function of `H` and using
the Poisson-Jensen formula.
-/

/-!
## Cartan / minimum-modulus style lower bounds (Tao, Theorem 22)

The “missing” step to get the sharp polynomial degree bound `≤ ⌊ρ⌋` is to control how small
the canonical product can get on a *sequence of circles* `‖z‖ = R_k`.  This matches Tao’s
probabilistic-radius argument in `academic_framework/HadamardFactorization/hadamard.md`.

We begin with pointwise lower bounds for the Weierstrass factors in the far/near regimes.
-/

open scoped BigOperators

lemma log_norm_weierstrassFactor_ge_neg_two_pow {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖weierstrassFactor m z‖ := by
  -- Use the exact representation from `WeierstrassFactorBound`: `E_m(z) = exp(-logTail)`.
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1 : ℂ) := by
    intro h
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [h] using hz
    norm_num at this
  have hEq' : weierstrassFactor' m z = Complex.exp (-logTail m z) :=
    weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
  have hEq : weierstrassFactor m z = Complex.exp (-logTail m z) := by
    -- `weierstrassFactor = weierstrassFactor'` by unfolding definitions.
    simpa [weierstrassFactor, weierstrassFactor', partialLogSum'] using hEq'
  -- Take `Real.log ‖·‖` and bound the real part.
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = (-logTail m z).re := by
    -- `‖exp w‖ = exp (Re w)` and `log (exp x) = x`.
    simp [hEq, Complex.norm_exp, Real.log_exp]
  -- `Re w ≥ -‖w‖`.
  have hre : (-logTail m z).re ≥ -‖logTail m z‖ := by
    have habs : |(-logTail m z).re| ≤ ‖-logTail m z‖ := Complex.abs_re_le_norm _
    have : (-‖-logTail m z‖) ≤ (-logTail m z).re := by
      -- From `|re| ≤ ‖·‖` deduce `-‖·‖ ≤ re`.
      have := neg_le_of_abs_le habs
      simpa using this
    simpa [norm_neg] using this
  -- Tail norm bound: `‖logTail m z‖ ≤ 2‖z‖^(m+1)` when `‖z‖ ≤ 1/2`.
  have htail :
      ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) := by
    have h1 : ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) :=
      norm_logTail_le hz_lt m
    have h2 : ‖z‖ ^ (m + 1) / (1 - ‖z‖) ≤ 2 * ‖z‖ ^ (m + 1) :=
      norm_pow_div_one_sub_le_two hz m
    exact h1.trans h2
  -- Assemble.
  have : (-logTail m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-logTail m z).re ≥ -‖logTail m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            -- rewrite `-‖tail‖ ≥ - (2 * ‖z‖^(m+1))`
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this

lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_sub
    (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m) ≤ Real.log ‖weierstrassFactor m z‖ := by
  classical
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    -- `log ‖1 - 1‖ = 0` and `weierstrassFactor m 1 = 0`, so the claim is trivial.
    simp [weierstrassFactor]
  -- Expand `weierstrassFactor` and take logs (now `‖1 - z‖ > 0`).
  set S : ℂ := ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1)
  have hS :
      weierstrassFactor m z = (1 - z) * Complex.exp S := by
    simp [weierstrassFactor, S]
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  -- `log ‖(1-z) * exp S‖ = log ‖1-z‖ + Re S`.
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = Real.log ‖1 - z‖ + S.re := by
    -- `‖uv‖ = ‖u‖*‖v‖`, and `‖exp S‖ = exp (Re S)`.
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt hnorm_pos
    calc
      Real.log ‖weierstrassFactor m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
                simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (by
              -- `‖exp S‖ ≠ 0`
              exact (ne_of_gt (by simp))))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  -- Bound `S.re` from below by `-‖S‖`, then by a crude dyadic bound.
  have hre : S.re ≥ -‖S‖ := by
    have habs : |S.re| ≤ ‖S‖ := Complex.abs_re_le_norm _
    have := neg_le_of_abs_le habs
    simpa using this
  have hnormS :
      ‖S‖ ≤ (m : ℝ) * max 1 (‖z‖ ^ m) := by
    -- `‖∑ t‖ ≤ ∑ ‖t‖` and each term is bounded by `max 1 (‖z‖^m)`.
    have hsum :
        ‖S‖ ≤ ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ := by
      simpa [S] using
        (norm_sum_le (s := Finset.range m) (f := fun k => z ^ (k + 1) / (k + 1)))
    have hterm :
        ∀ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖ ≤ max 1 (‖z‖ ^ m) := by
      intro k hk
      have hk' : k + 1 ≤ m := Nat.succ_le_of_lt (Finset.mem_range.1 hk)
      -- `‖z^(k+1)/(k+1)‖ ≤ ‖z‖^(k+1)` and `‖z‖^(k+1) ≤ max 1 (‖z‖^m)`.
      have hdiv : ‖z ^ (k + 1) / (k + 1)‖ ≤ ‖z‖ ^ (k + 1) := by
        -- denominator has norm ≥ 1
        have hden : (1 : ℝ) ≤ (k + 1 : ℝ) := by norm_cast; omega
        have hden' : (1 : ℝ) ≤ ‖((k + 1 : ℕ) : ℂ)‖ := by
          have hn : ‖((k + 1 : ℕ) : ℂ)‖ = (k + 1 : ℝ) := by
            simpa using (Complex.norm_natCast (k + 1))
          -- Avoid `simpa` here: in this toolchain `simp` turns `1 ≤ (k+1:ℝ)` into `True`.
          rw [hn]
          exact hden
        -- rewrite the norm of the quotient
        have hnorm :
            ‖z ^ (k + 1) / (k + 1)‖ = ‖z‖ ^ (k + 1) / ‖((k + 1 : ℕ) : ℂ)‖ := by
          simp [norm_pow, Nat.cast_add_one]
        -- now `a / b ≤ a` since `1 ≤ b`
        rw [hnorm]
        exact div_le_self (pow_nonneg (norm_nonneg z) _) hden'
      have hpow : ‖z‖ ^ (k + 1) ≤ max 1 (‖z‖ ^ m) := by
        by_cases hz1 : ‖z‖ ≤ 1
        · -- if `‖z‖ ≤ 1`, then `‖z‖^(k+1) ≤ 1`
          have hle1 : ‖z‖ ^ (k + 1) ≤ (1 : ℝ) := by
            exact pow_le_one₀ (norm_nonneg z) hz1
          exact le_trans hle1 (le_max_left _ _)
        · -- if `‖z‖ > 1`, monotonicity of powers gives `‖z‖^(k+1) ≤ ‖z‖^m`
          have hz1' : 1 ≤ ‖z‖ := le_of_not_ge hz1
          have hle : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ m := by
            exact pow_le_pow_right₀ hz1' hk'
          exact le_trans hle (le_max_right _ _)
      exact hdiv.trans hpow
    have hsum' :
        ∑ k ∈ Finset.range m, ‖z ^ (k + 1) / (k + 1)‖
          ≤ ∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m) := by
      exact Finset.sum_le_sum (fun k hk => hterm k hk)
    have hconst :
        (∑ _k ∈ Finset.range m, max 1 (‖z‖ ^ m))
          = (m : ℝ) * max 1 (‖z‖ ^ m) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have := le_trans hsum (le_trans hsum' (le_of_eq hconst))
    exact this
  have hSre : S.re ≥ -(m : ℝ) * max 1 (‖z‖ ^ m) := by
    calc
      S.re ≥ -‖S‖ := hre
      _ ≥ -(m : ℝ) * max 1 (‖z‖ ^ m) := by
            nlinarith [hnormS]
  -- Finish.
  -- Move `S.re` to the RHS via `hlog`.
  calc
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m)
        ≤ Real.log ‖1 - z‖ + S.re := by linarith [hSre]
    _ = Real.log ‖weierstrassFactor m z‖ := by
          simp [hlog]

/-!
### Averages of the logarithmic singularity (Tao's probabilistic radius step)

We control the *average* size of the positive part of `log (1 / |1 - t|)` near `t = 1`
by dominating it with an integrable power singularity. This is the analytic core of the
probabilistic method used in Tao's proof of Hadamard factorization.
-/

lemma neg_log_le_sqrt_two_div {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  -- Let `t := -log x ≥ 0`.
  have ht : 0 ≤ -Real.log x := by
    have hlog_le0 : Real.log x ≤ 0 := by
      -- `log x ≤ x - 1 ≤ 0` for `x ≤ 1`.
      have h := Real.log_le_sub_one_of_pos hx
      linarith
    linarith
  -- `1 + t + t^2/2 ≤ exp t`, and `exp(-log x) = 1/x`.
  have hquad := Real.quadratic_le_exp_of_nonneg ht
  have hexp : Real.exp (-Real.log x) = x⁻¹ := by
    simp [Real.exp_neg, Real.exp_log hx]
  -- Drop the nonnegative terms `1 + t` from the LHS.
  have hsq :
      (-Real.log x) ^ 2 / 2 ≤ x⁻¹ := by
    have : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) := by
      have hle : (-Real.log x) ^ 2 / 2 ≤ 1 + (-Real.log x) + (-Real.log x) ^ 2 / 2 := by
        have : 0 ≤ (1 : ℝ) + (-Real.log x) := by linarith [ht]
        linarith
      exact hle.trans hquad
    simpa [hexp] using this
  -- Take square roots.
  have hx_inv : 0 ≤ x⁻¹ := by exact inv_nonneg.2 (le_of_lt hx)
  have h2x_inv : 0 ≤ (2 / x) := by
    have : 0 ≤ (2 : ℝ) := by norm_num
    exact div_nonneg this (le_of_lt hx)
  have hsqrt :
      |(-Real.log x)| ≤ Real.sqrt (2 / x) := by
    -- From `t^2 ≤ 2/x`, we get `|t| ≤ sqrt(2/x)`.
    have hsq' : (-Real.log x) ^ 2 ≤ 2 / x := by
      -- `t^2 / 2 ≤ x⁻¹`  ->  `t^2 ≤ 2 * x⁻¹`  ->  `t^2 ≤ 2 / x`
      have hmul : 2 * ((-Real.log x) ^ 2 / 2) ≤ 2 * x⁻¹ :=
        mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 2)
      have hmul' : (-Real.log x) ^ 2 ≤ 2 * x⁻¹ := by
        calc
          (-Real.log x) ^ 2 = 2 * ((-Real.log x) ^ 2 / 2) := by ring
          _ ≤ 2 * x⁻¹ := hmul
      simpa [div_eq_mul_inv, mul_assoc] using hmul'
    -- rewrite `t^2` as `|t|^2` and take square roots
    have habs : |(-Real.log x)| ^ 2 ≤ 2 / x := by
      simpa [sq_abs] using hsq'
    have := Real.sqrt_le_sqrt habs
    -- `sqrt(|t|^2) = |t|`
    simpa [Real.sqrt_sq_eq_abs] using this
  -- Since `t ≥ 0`, `|t| = t`.
  have habs_t : |(-Real.log x)| = -Real.log x := by
    simp [abs_of_nonneg ht]
  -- Finish.
  simpa [habs_t] using hsqrt

lemma posLog_log_one_div_abs_one_sub_le_sqrt {t : ℝ} :
    max 0 (Real.log (1 / |1 - t|)) ≤ Real.sqrt (2 / |1 - t|) := by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · -- then `t = 1`, both sides are 0
      have : t = 1 := by
        have : 1 - t = 0 := by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have hpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        neg_log_le_sqrt_two_div (x := |1 - t|) hpos ht
      -- On `|1-t| ≤ 1`, the log is nonnegative: `log(1/|1-t|) = -log|1-t|`.
      have hlog : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by
        simp [Real.log_inv]
      have hnonneg : 0 ≤ Real.log (1 / |1 - t|) := by
        -- `1 / |1-t| ≥ 1` since `|1-t| ≤ 1`
        have : (1 : ℝ) ≤ 1 / |1 - t| := by
          have hpos' : 0 < |1 - t| := hpos
          -- `1 ≤ 1 / a` iff `a ≤ 1` for `a > 0`
          exact (one_le_div hpos').2 ht
        exact Real.log_nonneg this
      have hmax : max 0 (Real.log (1 / |1 - t|)) = Real.log (1 / |1 - t|) :=
        max_eq_right hnonneg
      -- Avoid `simp`: it rewrites `max ≤ _` into a conjunction via `max_le_iff`.
      calc
        max 0 (Real.log (1 / |1 - t|))
            = Real.log (1 / |1 - t|) := hmax
        _ = -Real.log |1 - t| := hlog
        _ ≤ Real.sqrt (2 / |1 - t|) := hle
  · -- If `|1-t| > 1`, then `log(1/|1-t|) ≤ 0`, so LHS is 0.
    have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have hle0 : Real.log (1 / |1 - t|) ≤ 0 := by
      have hpos : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t|) ≤ 1 := by
        -- `a / b ≤ 1 ↔ a ≤ b` for `b > 0`, with `a = 1`, `b = |1-t|`.
        exact (div_le_one hpos).2 (le_of_lt hlt)
      have h1 : 0 < (1 / |1 - t|) := by positivity
      exact le_trans (Real.log_le_log h1 this) (by simp)
    have hmax : max 0 (Real.log (1 / |1 - t|)) = 0 := max_eq_left hle0
    have hrhs : 0 ≤ Real.sqrt (2 / |1 - t|) := by
      have : 0 ≤ 2 / |1 - t| := by
        exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _)
      exact Real.sqrt_nonneg _
    -- Avoid `simp`: it rewrites `max ≤ _` into a conjunction via `max_le_iff`.
    rw [hmax]
    exact hrhs

/-!
### Algebraic and growth lemmas for `exp (Polynomial.eval z P)`

To upgrade the degree bound from `≤ ⌈ρ⌉` to `≤ ⌊ρ⌋`, we use the fact that the order of
an exponential of a nonzero polynomial is an **integer**: it equals the degree.

The key input is a lower bound: if `P.natDegree = n` and the leading coefficient is nonzero,
then along a suitable ray we have `Re (P z) ≳ ‖z‖^n`, hence `log(1+‖exp(P z)‖) ≳ ‖z‖^n`.
-/

open Polynomial

lemma exists_pow_eq_complex {n : ℕ} (hn : 0 < n) (w : ℂ) : ∃ z : ℂ, z ^ n = w := by
  classical
  by_cases hw : w = 0
  · subst hw
    refine ⟨0, ?_⟩
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simp [hn0]
  · refine ⟨Complex.exp (Complex.log w / n), ?_⟩
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    calc
      (Complex.exp (Complex.log w / n)) ^ n
          = Complex.exp ((n : ℂ) * (Complex.log w / n)) := by
              -- `(exp x)^n = exp(n*x)`
              simpa using (Complex.exp_nat_mul (Complex.log w / n) n).symm
      _ = Complex.exp (Complex.log w) := by
            -- cancel `n` against `/ n`
            simp [div_eq_mul_inv, hn0]; grind
      _ = w := by simpa using (Complex.exp_log hw)

/--
**Poisson-Jensen Upper Bound for Entire Functions**

If `H` is entire and zero-free, then `log |H(z)|` is bounded by the characteristic function
`T(R, H)` via the Poisson kernel estimate. Note that for zero-free functions, `N(r, H) = 0`,
so `T(r, H) = m(r, H)`.
-/
lemma log_norm_le_characteristic {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hH_nz : ∀ z, H z ≠ 0) (z : ℂ) (R : ℝ) (hR : ‖z‖ < R) :
    Real.log ‖H z‖ ≤ (R + ‖z‖) / (R - ‖z‖) * characteristic H ⊤ R := by
  -- u(w) = log |H(w)| is harmonic because H is entire and zero-free
  let u := fun w => Real.log ‖H w‖
  have hu_harm : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall 0 R) := by
    intro w _
    exact (hH.analyticAt w).harmonicAt_log_norm (hH_nz w)
  -- Apply the Poisson upper bound for harmonic functions:
  -- u(z) ≤ Avg(P * u⁺) (since u⁻ ≥ 0 and P ≥ 0).
  -- The max of the Poisson kernel P(z, ζ) is (R+|z|)/(R-|z|).
  have h_bound := InnerProductSpace.HarmonicOnNhd.poisson_upper_bound
    (f := u) (R := R) (z := z) (by linarith [norm_nonneg z]) hR hu_harm
  -- Relate circle average of u⁺ to the characteristic function
  -- proximity H ⊤ R = circleAverage (log⁺ |H|) = circleAverage (u⁺)
  have h_prox : proximity H ⊤ R = circleAverage (fun w => max (u w) 0) 0 R := by
    simp only [proximity, u, Real.posLog_def, max_comm]
    rfl
  -- For entire zero-free H, characteristic = proximity (since N(r, H) = 0)
  have h_char : characteristic H ⊤ R = proximity H ⊤ R := by
    rw [characteristic, logCounting_top_eq_zero_of_entire hH, add_zero]
  -- Combine estimates
  rw [h_char, h_prox]
  refine h_bound.trans ?_
  gcongr



end Hadamard
end ComplexAnalysis
