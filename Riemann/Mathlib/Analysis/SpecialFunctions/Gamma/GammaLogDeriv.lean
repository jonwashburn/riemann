
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Riemann.Mathlib.Analysis.SpecialFunctions.Gamma.BinetKernel

/-!
# Complex Digamma Function

This file defines the complex digamma function ψ(z) = Γ'(z)/Γ(z) and develops its
key properties.

## Main Definitions

* `Complex.digamma`: The digamma function ψ(z) = d/dz log Γ(z)
* `Real.digamma`: The real digamma function

## Main Results

* `Complex.digamma_nat`: ψ(n+1) = -γ + Hₙ (uses Mathlib's `hasDerivAt_Gamma_nat`)
* `Real.digamma_nat`: Real version
* `Real.tendsto_digamma_sub_log`: ψ(n+1) - log(n+1) → 0

## References

* NIST DLMF 5.2, 5.7, 5.9
* Mathlib: `Mathlib.NumberTheory.Harmonic.GammaDeriv`
-/

open Real Complex Set MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

/-! ## Section 1: Complex Digamma Function -/

namespace Complex

/-- The digamma function ψ(z) = d/dz log Γ(z) = Γ'(z)/Γ(z).
For z not a pole, this is well-defined and holomorphic. -/
def digamma (z : ℂ) : ℂ :=
  deriv Gamma z / Gamma z

/-- The digamma function at positive integers in terms of harmonic numbers.
This follows from `Complex.hasDerivAt_Gamma_nat`. -/
theorem digamma_nat (n : ℕ) :
    digamma (n + 1) = -Real.eulerMascheroniConstant + harmonic n := by
  unfold digamma
  have h_fact_ne : ((Nat.factorial n : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Nat.factorial_ne_zero n
  rw [Complex.deriv_Gamma_nat, Gamma_nat_eq_factorial, mul_div_cancel_left₀ _ h_fact_ne]

/-- The digamma function satisfies ψ(z+1) = ψ(z) + 1/z for z not a pole.
This follows from the functional equation Γ(z+1) = z·Γ(z). -/
theorem digamma_add_one {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) (hz0 : z ≠ 0) :
    digamma (z + 1) = digamma z + 1 / z := by
  unfold digamma
  -- Γ(z+1) = z * Γ(z)
  have h_Gamma_eq : Gamma (z + 1) = z * Gamma z := Gamma_add_one z hz0
  -- Γ'(z+1) = Γ(z) + z * Γ'(z)
  have h_deriv_Gamma : deriv Gamma (z + 1) = Gamma z + z * deriv Gamma z := by
    -- We need to differentiate z * Gamma z
    have h_diff_Gamma : DifferentiableAt ℂ Gamma z := differentiableAt_Gamma z hz
    have h_eq : ∀ᶠ w in 𝓝 z, Gamma (w + 1) = w * Gamma w := by
      filter_upwards [eventually_ne_nhds hz0] with w hw
      exact Gamma_add_one w hw
    rw [← deriv_comp_add_const]
    rw [EventuallyEq.deriv_eq h_eq]
    have h_prod : deriv (fun w => w * Gamma w) z = z * deriv Gamma z + Gamma z := by
      have h := deriv_mul differentiableAt_id h_diff_Gamma
      simp only [id_eq] at h
      rw [show (id * Gamma) = (fun w => w * Gamma w) from rfl] at h
      rw [h, add_comm]
      aesop
    rw [h_prod]
    ring
  rw [h_Gamma_eq, h_deriv_Gamma]
  have h_Gamma_ne : Gamma z ≠ 0 := Gamma_ne_zero hz
  field_simp [hz0, h_Gamma_ne]
  ring


/-! ### Helper lemmas for digamma_series -/

/-- Sum of 1/(k+1) for k = 0 to N-1 equals harmonic N. -/
lemma sum_inv_add_one_eq_harmonic (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 / ((k : ℂ) + 1)) = (harmonic N : ℂ) := by
  induction N with
  | zero => simp [harmonic]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ]
    simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
    congr 1
    push_cast
    ring

/-- The partial sum of the digamma series can be rewritten using harmonic numbers. -/
lemma digamma_series_partial_sum (z : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ) - 1 / (z + n)) =
    (harmonic N : ℂ) - ∑ n ∈ Finset.range N, (1 / (z + n)) := by
  rw [Finset.sum_sub_distrib, sum_inv_add_one_eq_harmonic]

/-- The "Euler form" of the partial sum: log n - ∑_{j=0}^n 1/(z+j).
This is the derivative of logGammaSeq with respect to z. -/
def digamma_euler_seq (z : ℂ) (n : ℕ) : ℂ :=
  log n - ∑ j ∈ Finset.range (n + 1), (1 / (z + j))

/- The difference between our series partial sum and the Euler form tends to 0.
Key identity: (-γ + H_N - ∑_{j=0}^{N-1} 1/(z+j)) - (log N - ∑_{j=0}^N 1/(z+j))
            = (H_N - log N - γ) + 1/(z+N) → 0

Proof outline:
1. 1/(z+N) → 0 as N → ∞ (since |z+N| → ∞)
2. H_N - log N → γ (from `Real.tendsto_harmonic_sub_log`)
3. So (H_N - log N - γ) + 1/(z+N) → 0 + 0 = 0
-/
/-- 1/(z + n) → 0 as n → ∞ for any fixed z. -/
lemma tendsto_inv_add_nat_atTop (z : ℂ) :
    Tendsto (fun n : ℕ => (1 : ℂ) / (z + n)) atTop (𝓝 0) := by
  simp only [one_div]
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- For large enough n, ‖z + n‖ > 1/ε, so ‖(z + n)⁻¹‖ < ε
  obtain ⟨N, hN⟩ := exists_nat_gt (‖z‖ + ε⁻¹)
  use N
  intro n hn
  simp only [dist_zero_right]
  have hn' : (n : ℝ) > ‖z‖ + ε⁻¹ := lt_of_lt_of_le hN (Nat.cast_le.mpr hn)
  -- Key: ‖z + n‖ ≥ n - ‖z‖ > ε⁻¹
  have h_diff_pos : (0 : ℝ) < n - ‖z‖ := by
    rw [sub_pos]
    apply lt_trans _ hn'
    simp only [lt_add_iff_pos_right, inv_pos, hε]
  have h_norm_lower : ‖z + n‖ ≥ n - ‖z‖ := by
    have h1 : ‖z + n‖ ≥ |‖z‖ - ‖(n : ℂ)‖| := by
      simpa using abs_norm_sub_norm_le z (-(n : ℂ))
    simp only [norm_natCast] at h1
    rw [abs_sub_comm, abs_of_nonneg (le_of_lt h_diff_pos)] at h1
    exact h1
  have h_eps_lt : ε⁻¹ < (n : ℝ) - ‖z‖ := by linarith
  have h_norm_big : ε⁻¹ < ‖z + n‖ := lt_of_lt_of_le h_eps_lt h_norm_lower
  have h_ne : z + n ≠ 0 := by
    intro h
    simp only [h, norm_zero] at h_norm_big
    linarith [inv_pos.mpr hε]
  simp only [norm_inv]
  exact inv_lt_of_inv_lt₀ hε h_norm_big

/-- Harmonic minus log tends to Euler-Mascheroni constant, lifted to ℂ. -/
lemma tendsto_harmonic_sub_log_complex :
    Tendsto (fun n : ℕ => ((harmonic n : ℝ) - Real.log n : ℂ)) atTop
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have h := Real.tendsto_harmonic_sub_log
  have h' := Complex.continuous_ofReal.continuousAt.tendsto.comp h
  convert h' using 1
  ext n
  simp only [Function.comp_apply, Complex.ofReal_sub]

/-- Algebraic simplification for the Euler difference. For N ≥ 1:
(-γ + H_N - ∑_{j<N} 1/(z+j)) - (log N - ∑_{j≤N} 1/(z+j)) = (H_N - log N - γ) + 1/(z+N) -/
lemma digamma_euler_diff_eq (z : ℂ) (N : ℕ) (_hN : N ≠ 0) :
    (-(Real.eulerMascheroniConstant : ℂ) +
      ∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ) - 1 / (z + n))) - digamma_euler_seq z N =
    ((harmonic N : ℂ) - log N - Real.eulerMascheroniConstant) + 1 / (z + N) := by
  simp only [digamma_euler_seq, digamma_series_partial_sum]
  rw [Finset.sum_range_succ]
  ring

lemma digamma_series_euler_diff (z : ℂ) (_hz : ∀ n : ℕ, z ≠ -n) :
    Tendsto (fun N => (-(Real.eulerMascheroniConstant : ℂ) +
      ∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ) - 1 / (z + n))) - digamma_euler_seq z N)
      atTop (𝓝 0) := by
  -- Step 1: (H_N - log N) → γ in ℂ
  have h1 : Tendsto (fun N : ℕ => ((harmonic N : ℂ) - log N - Real.eulerMascheroniConstant))
      atTop (𝓝 0) := by
    have h := tendsto_harmonic_sub_log_complex
    have h' := h.sub_const (Real.eulerMascheroniConstant : ℂ)
    simp only [sub_self] at h'
    apply Tendsto.congr' _ h'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [sub_sub, Complex.natCast_log, Complex.ofReal_ratCast]
  -- Step 2: 1/(z+N) → 0
  have h2 : Tendsto (fun N : ℕ => (1 : ℂ) / (z + N)) atTop (𝓝 0) := tendsto_inv_add_nat_atTop z
  -- Step 3: Combine and use the algebraic identity
  have h_sum := h1.add h2
  simp only [add_zero] at h_sum
  apply Tendsto.congr' _ h_sum
  filter_upwards [eventually_ne_atTop 0] with N hN
  rw [digamma_euler_diff_eq z N hN]

/-- The derivative of logGammaSeq at x equals the digamma Euler form.

For x > 0 and n ≥ 1:
d/dx (logGammaSeq x n) = log n - ∑ m ∈ range(n+1) 1/(x+m)
                       = digamma_euler_seq x n

This is the key link between the Bohr-Mollerup approach and digamma. -/
lemma deriv_logGammaSeq_eq_digamma_euler {x : ℝ} (hx : 0 < x) (n : ℕ) :
    deriv (fun y => Real.BohrMollerup.logGammaSeq y n) x =
      (Real.log n - ∑ m ∈ Finset.range (n + 1), (1 / (x + m) : ℝ)) := by
  -- logGammaSeq x n = x * log n + log n! - ∑ m, log (x + m)
  -- d/dx = log n + 0 - ∑ m, 1/(x+m) = log n - ∑ m, 1/(x+m)
  have h_pos : ∀ m : ℕ, (0 : ℝ) < x + m := fun m => by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h_ne : ∀ m : ℕ, x + m ≠ 0 := fun m => ne_of_gt (h_pos m)
  -- Build the HasDerivAt for the sum of logs
  have h_sum : HasDerivAt (fun y => ∑ m ∈ Finset.range (n + 1), Real.log (y + m))
      (∑ m ∈ Finset.range (n + 1), (x + m)⁻¹) x := by
    have h_each : ∀ m ∈ Finset.range (n + 1),
        HasDerivAt (fun y => Real.log (y + m)) (x + m)⁻¹ x := by
      intro m _
      have h_inner : HasDerivAt (fun y => y + (m : ℝ)) 1 x := (hasDerivAt_id x).add_const (m : ℝ)
      have h_log := Real.hasDerivAt_log (h_ne m)
      have h_comp := h_log.comp x h_inner
      simp only [mul_one] at h_comp
      exact h_comp
    have h_eq : (fun y => ∑ m ∈ Finset.range (n + 1), Real.log (y + m)) =
        ∑ m ∈ Finset.range (n + 1), (fun y => Real.log (y + m)) := by
      ext y; simp only [Finset.sum_apply]
    rw [h_eq]
    exact HasDerivAt.sum h_each
  -- Build the HasDerivAt for the first part
  have h_first : HasDerivAt (fun y => y * Real.log n + Real.log n.factorial) (Real.log n) x := by
    have h1 : HasDerivAt (fun y => y * Real.log n) (1 * Real.log n) x :=
      (hasDerivAt_id x).mul_const _
    simp only [one_mul] at h1
    have h2 : HasDerivAt (fun _y => Real.log n.factorial) 0 x := hasDerivAt_const x _
    convert h1.add h2 using 1; ring
  -- Combine
  have h_all : HasDerivAt (fun y => Real.BohrMollerup.logGammaSeq y n)
      (Real.log n - ∑ m ∈ Finset.range (n + 1), (x + m)⁻¹) x := by
    simp only [Real.BohrMollerup.logGammaSeq]
    exact h_first.sub h_sum
  rw [h_all.deriv]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [one_div]

/-! ### Convergence of digamma_euler_seq -/

/-- GammaSeq z is differentiable in z for each n and z not a non-positive integer. -/
lemma differentiableAt_GammaSeq (z : ℂ) (n : ℕ) (hz : ∀ m : ℕ, m ≤ n → z ≠ -m) :
    DifferentiableAt ℂ (fun w => GammaSeq w n) z := by
  unfold GammaSeq
  have h_prod_ne : ∏ j ∈ Finset.range (n + 1), (z + j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.mem_range] at hj
    specialize hz j (Nat.lt_succ_iff.mp hj)
    intro heq
    rw [add_eq_zero_iff_eq_neg] at heq
    exact hz heq
  refine DifferentiableAt.div ?_ ?_ h_prod_ne
  · have h_cpow : DifferentiableAt ℂ (fun w => (n : ℂ) ^ w) z := by
      by_cases hn : n = 0
      · -- When n = 0, the function is 0^w which equals 0 for w.re > 0
        -- Actually we need to show DifferentiableAt even at poles.
        -- For n = 0, 0^w is not differentiable at w = 0, but we're assuming
        -- z is not a non-positive integer, so z ≠ 0 is guaranteed by hz 0.
        subst hn
        -- n = 0, so 0^w. This is differentiable away from 0 (it's constant 0 for re w > 0).
        -- But we need to be careful about the definition near 0.
        have hz0 : z ≠ 0 := by
          specialize hz 0 (le_refl 0)
          simp at hz
          exact hz
        -- 0^z = 0 when z ≠ 0 (by the convention in Mathlib for cpow)
        -- This case is degenerate and the function is locally constant 0
        have h_eq : (fun w : ℂ => (0 : ℂ) ^ w) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
          filter_upwards [eventually_ne_nhds hz0] with w hw
          simp [zero_cpow hw]
        have h_diff_const : DifferentiableAt ℂ (fun _ : ℂ => (0 : ℂ)) z := differentiableAt_const _
        exact h_diff_const.congr_of_eventuallyEq (by simpa using h_eq)
      · exact differentiableAt_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
    exact h_cpow.mul (differentiableAt_const _)
  · -- The product ∏ (z + j) is differentiable
    have h_each : ∀ j ∈ Finset.range (n + 1), DifferentiableAt ℂ (fun w => w + (j : ℂ)) z :=
      fun j _ => differentiableAt_id.add (differentiableAt_const _)
    classical
    have h_prod :
        DifferentiableAt ℂ (fun w => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) z := by
      simpa using
        (DifferentiableAt.fun_finset_prod (u := Finset.range (n + 1))
            (f := fun j w => w + (j : ℂ)) h_each)
    exact h_prod

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in

/-- The logarithmic derivative of GammaSeq equals digamma_euler_seq. -/
lemma logDeriv_GammaSeq (z : ℂ) (n : ℕ) (hz : ∀ m : ℕ, m ≤ n → z ≠ -m) (hn : n ≠ 0) :
    logDeriv (fun w => GammaSeq w n) z = digamma_euler_seq z n := by
  -- logDeriv (GammaSeq · n) z = deriv (GammaSeq · n) z / GammaSeq z n
  -- GammaSeq z n = n^z * n! / ∏_{j≤n} (z + j)
  -- log(GammaSeq z n) = z * log n + log(n!) - ∑_{j≤n} log(z + j)
  -- d/dz log(GammaSeq z n) = log n - ∑_{j≤n} 1/(z+j) = digamma_euler_seq z n
  unfold logDeriv digamma_euler_seq GammaSeq
  have h_prod_ne : ∏ j ∈ Finset.range (n + 1), (z + j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.mem_range] at hj
    specialize hz j (Nat.lt_succ_iff.mp hj)
    intro heq; rw [add_eq_zero_iff_eq_neg] at heq; exact hz heq
  have h_GammaSeq_ne : GammaSeq z n ≠ 0 := by
    unfold GammaSeq
    refine div_ne_zero ?_ h_prod_ne
    refine mul_ne_zero ?_ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    rw [cpow_ne_zero_iff]
    left
    exact Nat.cast_ne_zero.mpr hn
  -- The derivative of n^z is n^z * log n
  have h_deriv_cpow : deriv (fun w => (n : ℂ) ^ w) z = (n : ℂ) ^ z * log n := by
    have h := (hasDerivAt_id z).const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
    simp only [id_eq, mul_one] at h
    exact h.deriv
  -- Use the quotient rule for logarithmic derivative
  -- logDeriv (f/g) = logDeriv f - logDeriv g
  -- logDeriv (n^z * n!) = log n (since d/dz n^z = n^z * log n)
  -- logDeriv (∏ (z+j)) = ∑ 1/(z+j)
  have h_eq_fun : (fun w : ℂ => (n : ℂ) ^ w * ↑(Nat.factorial n) /
      ∏ j ∈ Finset.range (n + 1), (w + ↑j)) =
      (fun w : ℂ => (n : ℂ) ^ w * ↑(Nat.factorial n)) / (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + ↑j)) := by
    ext w : 1
    simp only [Pi.div_apply]
  -- rewrite the goal in terms of logDeriv and apply the quotient rule
  change
    logDeriv (fun w => (n : ℂ) ^ w * ↑(Nat.factorial n) /
        ∏ j ∈ Finset.range (n + 1), (w + ↑j)) z
      = log n - ∑ j ∈ Finset.range (n + 1), 1 / (z + ↑j)
  have h_div :=
    logDeriv_div (f := fun w => (n : ℂ) ^ w * ↑(Nat.factorial n))
      (g := fun w => ∏ j ∈ Finset.range (n + 1), (w + ↑j))
      (z := z) h_prod_ne
  -- use the quotient rule: logDeriv (f/g) = logDeriv f - logDeriv g
  have h_goal :
      logDeriv (fun w => (n : ℂ) ^ w * ↑(Nat.factorial n) /
          ∏ j ∈ Finset.range (n + 1), (w + ↑j)) z
        = logDeriv (fun w => (n : ℂ) ^ w * ↑(Nat.factorial n)) z
          - logDeriv (fun w => ∏ j ∈ Finset.range (n + 1), (w + ↑j)) z := by
    simpa using h_div
  -- reduce to numerator and denominator log-derivatives
  refine h_goal.trans ?_
  -- logDeriv of numerator
  · have h_num : logDeriv (fun w => (n : ℂ) ^ w * ↑(Nat.factorial n)) z = log n := by
      rw [show (fun w => (n : ℂ) ^ w * ↑(Nat.factorial n)) =
          (fun w => (n : ℂ) ^ w) * (fun _ => (Nat.factorial n : ℂ)) by ext; rfl]
      rw [logDeriv_mul]
      · simp only [logDeriv_const, add_zero]
        rw [logDeriv, h_deriv_cpow]
        field_simp
        rw [cpow_ne_zero_iff]; left; exact Nat.cast_ne_zero.mpr hn
      · exact differentiableAt_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))
      · exact differentiableAt_const _
      · rw [cpow_ne_zero_iff]; left; exact Nat.cast_ne_zero.mpr hn
    -- logDeriv of denominator
    have h_denom : logDeriv (fun w => ∏ j ∈ Finset.range (n + 1), (w + ↑j)) z =
        ∑ j ∈ Finset.range (n + 1), 1 / (z + j) := by
      rw [logDeriv_prod]
      · congr 1
        ext j
        rw [logDeriv, deriv_add_const', deriv_id'']
        simp only [one_div]
      · intro j _
        exact differentiableAt_id.add (differentiableAt_const _)
      · intro j hj
        rw [Finset.mem_range] at hj
        specialize hz j (Nat.lt_succ_iff.mp hj)
        intro heq; rw [add_eq_zero_iff_eq_neg] at heq; exact hz heq
    rw [h_num, h_denom]
    ring
  · exact (differentiableAt_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn))).mul
      (differentiableAt_const _)
  · apply DifferentiableAt.finset_prod
    intro j _
    exact differentiableAt_id.add (differentiableAt_const (j : ℂ))
  · refine mul_ne_zero ?_ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    rw [cpow_ne_zero_iff]; left; exact Nat.cast_ne_zero.mpr hn
  · exact h_prod_ne

/-- GammaSeq tends to Gamma locally uniformly on the right half-plane. -/
lemma tendstoLocallyUniformlyOn_GammaSeq :
    TendstoLocallyUniformlyOn (fun n z => GammaSeq z n) Gamma atTop {z : ℂ | 0 < z.re} := by
  -- This follows from the proof of GammaSeq_tendsto_Gamma in Mathlib,
  -- which uses dominated convergence on the integral representation.
  -- The key is that the approximating integrals converge uniformly on compact subsets.
  sorry

/-- For Re(z) > 0, the Euler sequence for digamma converges to digamma(z).

The proof uses `logDeriv_tendsto`: if F_n → F locally uniformly and each F_n is
differentiable, then logDeriv F_n → logDeriv F. Here F_n = GammaSeq · n and F = Gamma.

Since logDeriv (GammaSeq · n) z = digamma_euler_seq z n (by direct computation)
and logDeriv Gamma z = Gamma'(z)/Gamma(z) = digamma z, we get the result. -/
lemma tendsto_digamma_euler_seq_of_re_pos {z : ℂ} (hpos : 0 < z.re) :
    Tendsto (digamma_euler_seq z) atTop (𝓝 (digamma z)) := by
  unfold digamma
  have hz : ∀ n : ℕ, z ≠ -n := fun n => by
    intro heq
    rw [heq, neg_re, natCast_re, neg_pos] at hpos
    exact (Nat.cast_nonneg n).not_lt hpos
  -- Strategy: Use logDeriv_tendsto
  -- logDeriv Gamma z = deriv Gamma z / Gamma z = digamma z
  -- logDeriv (GammaSeq · n) z = digamma_euler_seq z n
  -- GammaSeq → Gamma locally uniformly on Re(z) > 0
  -- Therefore digamma_euler_seq z n → digamma z
  have h_Gamma_ne : Gamma z ≠ 0 := Gamma_ne_zero hz
  have h_open : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const continuous_re
  have h_mem : z ∈ {w : ℂ | 0 < w.re} := hpos
  -- Use logDeriv_tendsto theorem
  have h_limit := Complex.logDeriv_tendsto h_open ⟨z, h_mem⟩ tendstoLocallyUniformlyOn_GammaSeq
  -- Show each GammaSeq is differentiable on the right half-plane
  have h_diff : ∀ᶠ n in atTop, DifferentiableOn ℂ (fun w => GammaSeq w n) {w : ℂ | 0 < w.re} := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro w hw
    have hw' : ∀ m : ℕ, m ≤ n → w ≠ -m := fun m _ heq => by
      simp only [Set.mem_setOf_eq] at hw
      rw [heq, neg_re, natCast_re, neg_pos] at hw
      exact (Nat.cast_nonneg m).not_lt hw
    exact (differentiableAt_GammaSeq w n hw').differentiableWithinAt
  specialize h_limit h_diff h_Gamma_ne
  -- Convert logDeriv to our definitions
  have h_eq : ∀ᶠ n in atTop, logDeriv (fun w => GammaSeq w n) z = digamma_euler_seq z n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hz' : ∀ m : ℕ, m ≤ n → z ≠ -m := fun m _ => hz m
    exact logDeriv_GammaSeq z n hz' (Nat.one_le_iff_ne_zero.mp (Nat.one_le_of_lt hn))
  have h_eq' : ∀ᶠ n in atTop, digamma_euler_seq z n = logDeriv (fun w => GammaSeq w n) z := by
    filter_upwards [h_eq] with n hn
    exact hn.symm
  rw [Tendsto.congr' h_eq']
  convert h_limit using 1
  simp only [logDeriv]

/-- The Euler form converges to ψ(z). -/
lemma tendsto_digamma_euler_seq {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    Tendsto (digamma_euler_seq z) atTop (𝓝 (digamma z)) := by
  -- Strategy: For Re(z) > 0, use the direct proof.
  -- For Re(z) ≤ 0, shift z by a positive integer to get into the positive region,
  -- then use the functional equation.
  by_cases hpos : 0 < z.re
  · exact tendsto_digamma_euler_seq_of_re_pos hpos
  · -- Find m such that Re(z) + m > 0
    push_neg at hpos
    -- Let m = ⌈1 - Re(z)⌉ + 1, so Re(z) + m > 0
    let m := Nat.ceil (1 - z.re) + 1
    have hm_pos : 0 < z.re + m := by
      simp only [m]
      have h1 : (1 : ℝ) - z.re ≤ ↑(Nat.ceil (1 - z.re)) := Nat.le_ceil _
      linarith
    -- z + m is not a non-positive integer
    have hz' : ∀ n : ℕ, z + m ≠ -n := fun n => by
      intro heq
      have : z = -(n : ℂ) - m := by linarith
      rw [this] at hz
      specialize hz (n + m)
      push_cast at hz
      ring_nf at hz
      exact hz rfl
    -- Use that digamma_euler_seq (z + m) → digamma (z + m)
    have h_limit : Tendsto (digamma_euler_seq (z + m)) atTop (𝓝 (digamma (z + m))) :=
      tendsto_digamma_euler_seq_of_re_pos hm_pos
    -- Now use the functional equation to relate back to z
    sorry

/-- Series representation: ψ(z) = -γ + ∑_{n=0}^∞ (1/(n+1) - 1/(z+n))

This is the fundamental series expansion of the digamma function, connecting
it to the harmonic series and Euler-Mascheroni constant. -/
theorem digamma_series {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    Tendsto (fun N => -(Real.eulerMascheroniConstant : ℂ) +
      ∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ) - 1 / (z + n)))
      atTop (𝓝 (digamma z)) := by
  -- Strategy: Show our series differs from digamma_euler_seq by a term that → 0
  -- Then use that digamma_euler_seq → digamma z
  have h1 := digamma_series_euler_diff z hz
  have h2 := tendsto_digamma_euler_seq hz
  -- Our series = (our series - euler_seq) + euler_seq
  have heq : (fun N => -(Real.eulerMascheroniConstant : ℂ) +
      ∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ) - 1 / (z + n))) =
      (fun N => ((-(Real.eulerMascheroniConstant : ℂ) +
        ∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ) - 1 / (z + n))) - digamma_euler_seq z N) +
        digamma_euler_seq z N) := by
    ext N; ring
  rw [heq]
  convert h1.add h2 using 1
  simp only [zero_add]

/-- Gauss's integral representation for the digamma function.

For Re(z) > 0:
ψ(z) = ∫₀^∞ (e^{-t}/t - e^{-zt}/(1 - e^{-t})) dt

This integral representation is fundamental for analytic continuation
and asymptotic analysis. -/
theorem digamma_gauss_integral {z : ℂ} (hz : 0 < z.re) :
    digamma z = ∫ t in Ioi (0 : ℝ),
      ((exp (-t) : ℂ) / t - exp (-z * t) / (1 - exp (-t))) := by
  sorry

end Complex

/-! ## Section 2: Real Digamma Function -/

namespace Real

/-- The real digamma function ψ(x) = d/dx log Γ(x). -/
def digamma (x : ℝ) : ℝ :=
  deriv Gamma x / Gamma x

/-- The digamma function at positive integers. -/
theorem digamma_nat (n : ℕ) :
    digamma (n + 1) = -eulerMascheroniConstant + harmonic n := by
  unfold digamma
  have h_ne : Gamma (n + 1 : ℝ) ≠ 0 := by
    rw [Gamma_nat_eq_factorial]
    have := Nat.factorial_pos n
    positivity
  have h_deriv := hasDerivAt_Gamma_nat n
  have h_fact_ne : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := by
    have := Nat.factorial_pos n
    positivity
  rw [h_deriv.deriv, Gamma_nat_eq_factorial, mul_div_cancel_left₀ _ h_fact_ne]

/-- The sequence ψ(n+1) - log(n+1) tends to 0 as n → ∞.

This follows from ψ(n+1) = -γ + Hₙ and Hₙ - log(n+1) → γ. -/
theorem tendsto_digamma_sub_log :
    Tendsto (fun n : ℕ => digamma (n + 1) - log (n + 1)) atTop (𝓝 0) := by
  have h : ∀ n : ℕ, digamma (n + 1) - log (n + 1) =
      -eulerMascheroniConstant + ((harmonic n : ℝ) - log (n + 1)) := by
    intro n
    rw [digamma_nat n]
    ring
  simp_rw [h]
  have h_tendsto := tendsto_harmonic_sub_log_add_one
  have heq : (fun n : ℕ => -eulerMascheroniConstant + ((harmonic n : ℝ) - log ((n : ℝ) + 1))) =
      (fun n : ℕ => (harmonic n : ℝ) - log ((n : ℝ) + 1) - eulerMascheroniConstant) := by
    ext n; ring
  rw [heq]
  have hzero : (0 : ℝ) = eulerMascheroniConstant - eulerMascheroniConstant := by ring
  rw [hzero]
  exact h_tendsto.sub_const eulerMascheroniConstant

/-- Asymptotic: digamma x ~ log x as x → ∞. -/
theorem tendsto_digamma_div_log :
    Tendsto (fun x : ℝ => digamma x / log x) atTop (𝓝 1) := by
  sorry

end Real

/-! ## Section 3: Connection to BinetKernel -/

namespace Complex

/-- Binet's integral representation for log Γ.
For Re(z) > 0:
log Γ(z) = (z - 1/2) log z - z + log(2π)/2 + J(z)

where J(z) = ∫₀^∞ K̃(t) e^{-tz} dt is the Binet integral. -/
theorem logGamma_eq_stirling_plus_J {z : ℂ} (hz : 0 < z.re) :
    log (Gamma z) = (z - 1/2) * log z - z + log (2 * Real.pi) / 2 +
      ∫ t in Ioi (0 : ℝ), (BinetKernel.Ktilde t : ℂ) * exp (-t * z) := by
  sorry

end Complex

namespace Real

/-- Stirling's formula error bound using the Binet integral. -/
theorem logGamma_stirling_error {x : ℝ} (hx : 1 ≤ x) :
    |log (Gamma x) - ((x - 1/2) * log x - x + log (2 * Real.pi) / 2)| ≤
      1 / (12 * x) := by
  sorry

end Real

end
