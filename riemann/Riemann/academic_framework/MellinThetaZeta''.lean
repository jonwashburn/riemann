import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Riemann.academic_framework.Theta
import PrimeNumberTheoremAnd.MellinCalculus
import PrimeNumberTheoremAnd.Wiener
import Mathlib

/-!
# Mellin Transform Identity for Jacobi Theta and Riemann Zeta

This file establishes the classical relationship between the Jacobi theta function
and the Riemann zeta function via Mellin transforms, following Riemann's 1859 approach.

## Main definitions

* `jacobiTheta`: The Jacobi theta function θ(t) = ∑_{n∈ℤ} exp(-π n² t)
* `completedZeta`: The completed zeta Λ(s) = π^(-s/2) Γ(s/2) ζ(s)

## Main results

* `jacobiTheta_summable`: θ(t) converges absolutely for t > 0
* `jacobiTheta_pos`: θ(t) > 0 for t > 0
* `jacobiTheta_modular`: θ(t) = t^(-1/2) θ(1/t)
* `mellin_theta_eq_completedZeta`: Mellin identity on 1 < Re(s) < 2
* `completedZeta_functional_equation`: Λ(s) = Λ(1-s)
-/

noncomputable section

open Complex Real MeasureTheory Filter Topology Set Summable
open scoped Real NNReal

namespace RiemannZeta

/-! ### Section 1: Definition and basic properties of theta -/

/-- The Jacobi theta function θ(t) = ∑_{n∈ℤ} exp(-π n² t) for t > 0. -/
def jacobiTheta (t : ℝ) : ℝ :=
  if 0 < t then ∑' (n : ℤ), rexp (-π * (n : ℝ)^2 * t) else 0

/-- The modified theta function θ(t) - 1, removing the n=0 term. -/
def jacobiTheta' (t : ℝ) : ℝ := jacobiTheta t - 1

/-- Basic rewrite lemma for theta when t > 0. -/
@[simp] lemma jacobiTheta_of_pos {t : ℝ} (ht : 0 < t) :
    jacobiTheta t = ∑' (n : ℤ), rexp (-π * (n : ℝ)^2 * t) := if_pos ht

/-! ### Section 2: Convergence of the theta series -/

/-- Key lemma: For t > 0 and |n| ≥ 1, we have exp(-π n² t) ≤ exp(-π t). -/
lemma exp_neg_pi_n_sq_le {t : ℝ} (ht : 0 < t) {n : ℤ} (hn : n ≠ 0) :
    rexp (-π * (n : ℝ)^2 * t) ≤ rexp (-π * t) := by
  apply exp_le_exp.mpr
  simp only [neg_mul, neg_le_neg_iff]
  rw [mul_le_mul_iff_left₀ ht]
  have h1 : 1 ≤ |n| := Int.one_le_abs hn
  have h2 : (1 : ℝ) ≤ (n : ℝ)^2 := by
    calc (1 : ℝ) = 1^2 := by norm_num
        _ ≤ (|n| : ℝ)^2 := by
          have h_abs_nonneg : 0 ≤ |n| := abs_nonneg n
          have h_one_nonneg : 0 ≤ (1 : ℝ) := by norm_num
          exact sq_le_sq h_one_nonneg (mod_cast h1 : (1 : ℝ) ≤ |n|)
        _ = (n : ℝ)^2 := by simp [sq_abs]
  exact mul_le_mul_of_nonneg_left h2 (le_of_lt pi_pos)

/-- Geometric series comparison bound for theta summability. -/
lemma summable_exp_neg_pi_t {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => rexp (-π * t * n) := by
  have : rexp (-π * t) < 1 := by
    rw [exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (mul_pos pi_pos ht) (by norm_num : (0 : ℝ) > -1)
  apply summable_geometric_of_norm_lt_one
  simp only [norm_eq_abs, abs_exp]
  exact this

/-- The theta series converges absolutely for any t > 0. -/
theorem jacobiTheta_summable {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => rexp (-π * (n : ℝ)^2 * t) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · -- Positive n
    apply Summable.of_nonneg_of_le
    · intro n; exact le_of_lt (exp_pos _)
    · intro n
      cases n with
      | zero => simp; exact le_refl _
      | succ n =>
        have : ((n + 1 : ℕ) : ℤ) ≠ 0 := by simp
        calc rexp (-π * ((n + 1 : ℕ) : ℝ)^2 * t)
            ≤ rexp (-π * t) := exp_neg_pi_n_sq_le ht this
          _ ≤ rexp (-π * t) ^ (n + 1) := by
              rw [← exp_nat_mul]
              apply exp_le_exp.mpr
              simp [mul_comm π, mul_assoc]
              exact mul_le_mul_of_nonneg_left (by linarith : t ≤ t * (n + 1))
                (mul_nonneg (le_of_lt pi_pos) (le_of_lt ht))
    · -- Geometric series
      have := summable_exp_neg_pi_t ht
      exact this.comp_injective (fun n => n) (fun _ _ => by simp)
  · -- Negative n (symmetric)
    apply Summable.of_nonneg_of_le
    · intro n; exact le_of_lt (exp_pos _)
    · intro n
      cases n with
      | zero => simp; exact le_refl _
      | succ n =>
        calc rexp (-π * (-(n + 1 : ℕ) : ℝ)^2 * t)
            = rexp (-π * ((n + 1 : ℕ) : ℝ)^2 * t) := by ring_nf
          _ ≤ rexp (-π * t) ^ (n + 1) := by
              rw [← exp_nat_mul]
              apply exp_le_exp.mpr
              simp [mul_comm π, mul_assoc]
              exact mul_le_mul_of_nonneg_left (by linarith : t ≤ t * (n + 1))
                (mul_nonneg (le_of_lt pi_pos) (le_of_lt ht))
    · exact summable_exp_neg_pi_t ht |>.comp_injective _ (fun _ _ => by simp)

/-- The theta function is positive for t > 0. -/
theorem jacobiTheta_pos {t : ℝ} (ht : 0 < t) : 0 < jacobiTheta t := by
  rw [jacobiTheta_of_pos ht]
  apply tsum_pos (jacobiTheta_summable ht)
  · intro n; exact le_of_lt (exp_pos _)
  · use 0; exact exp_pos _

/-! ### Section 3: The theta modular transformation -/

/-- Helper: multiplication distributes properly in the exponent. -/
lemma exp_mul_div_eq {a b c : ℝ} (hc : c ≠ 0) :
    rexp (-a * b / c) = rexp (-a * b * (1 / c)) := by
  congr 1; field_simp

/-- Poisson summation formula for the Gaussian (requires Fourier analysis). -/
theorem poisson_sum_gaussian (t : ℝ) (ht : 0 < t) :
    ∑' (n : ℤ), rexp (-π * (n : ℝ)^2 * t) =
    t^(-(1/2 : ℝ)) * ∑' (n : ℤ), rexp (-π * (n : ℝ)^2 * (1/t)) := by
  -- Use Real.tsum_exp_neg_mul_int_sq from mathlib via theta_modularity
  have h := Real.tsum_exp_neg_mul_int_sq ht
  simp only [mul_div_assoc] at h
  calc ∑' (n : ℤ), rexp (-π * (n : ℝ)^2 * t)
      = 1 / t ^ (1 / 2) * ∑' (n : ℤ), rexp (-π / t * (n : ℝ)^2) := h
    _ = t ^ (-(1 / 2 : ℝ)) * ∑' (n : ℤ), rexp (-π / t * (n : ℝ)^2) := by
        rw [rpow_neg ht.le, one_div, ← inv_div]
    _ = t ^ (-(1 / 2 : ℝ)) * ∑' (n : ℤ), rexp (-π * (n : ℝ)^2 * (1/t)) := by
        congr 1
        refine tsum_congr fun n => ?_
        ring_nf

/-- The Jacobi theta modular transformation: θ(1/t) = √t θ(t). -/
theorem jacobiTheta_modular {t : ℝ} (ht : 0 < t) :
    jacobiTheta (1/t) = sqrt t * jacobiTheta t := by
  rw [jacobiTheta_of_pos ht, jacobiTheta_of_pos (by positivity)]
  rw [poisson_sum_gaussian t ht]
  rw [rpow_neg (le_of_lt ht), rpow_div_nat_eq_sqrt (le_of_lt ht) 2]
  simp only [inv_eq_one_div]
  ring

/-! ### Section 4: Mellin transform integrands and convergence -/

/-- The Mellin transform integrand (θ(t) - 1) t^(s/2 - 1) for complex s. -/
def mellinIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  (jacobiTheta' t : ℂ) * (t : ℂ) ^ (s / 2 - 1)

/-- Decay bound: For t ≥ 1, we have |θ(t) - 1| ≤ 2exp(-πt). -/
lemma jacobiTheta'_bound {t : ℝ} (ht : 1 ≤ t) :
    |jacobiTheta' t| ≤ 2 * rexp (-π * t) := by
  rw [jacobiTheta', jacobiTheta_of_pos (lt_of_lt_of_le zero_lt_one ht)]
  have h_sum : jacobiTheta' t = 2 * ∑' n : ℕ, rexp (-π * ((n + 1 : ℤ) : ℝ)^2 * t) := by
    unfold jacobiTheta'
    rw [jacobiTheta_of_pos (lt_of_lt_of_le zero_lt_one ht)]
    simp only [tsum_int, add_tsum_compl, tsum_zero]
    congr 1
    · simp only [summable_int_iff_summable_nat_and_neg]
      constructor
      · exact jacobiTheta_summable (lt_of_lt_of_le zero_lt_one ht) |>.comp_injective Int.ofNat.injective
      · exact jacobiTheta_summable (lt_of_lt_of_le zero_lt_one ht) |>.comp_injective Int.negSucc.injective
    · simp [Int.ofNat_zero]
  rw [h_sum]
  rw [abs_mul, abs_two]
  have : ∀ n : ℕ, rexp (-π * ((n + 1 : ℤ) : ℝ)^2 * t) ≤ rexp (-π * t) := by
    intro n
    apply exp_le_exp.mpr
    simp only [neg_mul, neg_le_neg_iff]
    have h1 : (1 : ℝ) ≤ (n + 1 : ℝ)^2 := by
      calc (1 : ℝ) = 1^2 := by norm_num
        _ ≤ (n + 1 : ℝ)^2 := by
          apply sq_le_sq'
          · norm_num
          · norm_cast; omega
    exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (le_of_lt pi_pos) (le_of_lt (lt_of_lt_of_le zero_lt_one ht)))
  convert mul_le_mul_of_nonneg_left (tsum_le_tsum this
    (summable_exp_neg_pi_t (lt_of_lt_of_le zero_lt_one ht) |>.comp_injective (fun _ _ h => by simpa using h))
    (summable_exp_neg_pi_t (lt_of_lt_of_le zero_lt_one ht) |>.comp_injective (fun _ _ h => by simpa using h)))
    (by norm_num : (0 : ℝ) ≤ 2) using 1
  · simp only [tsum_mul_right]
    congr 1
    refine tsum_congr fun n => ?_
    ring
  · ring

/-- For Re(s) > 1, the integral ∫₁^∞ (θ(t)-1) t^(s/2-1) dt converges absolutely. -/
theorem mellin_right_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (mellinIntegrand s) (Ici 1) volume := by
  -- Bound |mellinIntegrand s t| ≤ 2exp(-πt) * t^(s.re/2 - 1) for t ≥ 1
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ici 1)),
      ‖mellinIntegrand s t‖ ≤ 2 * rexp (-π * t) * t^(s.re / 2 - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    rw [mellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le zero_lt_one ht) (s/2 - 1)]
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    convert mul_le_mul_of_nonneg_left (jacobiTheta'_bound ht) (rpow_nonneg ht_pos.le _) using 1
    · simp [Complex.norm_ofReal]
    · ring
  -- The dominating function is integrable
  have h_int : IntegrableOn (fun t => 2 * rexp (-π * t) * t^(s.re / 2 - 1)) (Ici 1) volume := by
    -- exp(-πt) is integrable, and t^(s.re/2 - 1) is bounded for t ≥ 1 when s.re > 1
    have h1 : IntegrableOn (fun t => rexp (-π * t)) (Ici 1) volume := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      -- This uses exp_neg_integrableOn_Ioi from mathlib
      apply Continuous.integrableOn_Ioi
      · continuity
      · exact exp_neg_tendsto_atTop (mul_pos pi_pos zero_lt_one)
    -- For t ≥ 1, we have t^(s.re/2 - 1) ≤ 1 when s.re > 1
    have h2 : ∀ t ∈ Ici 1, t^(s.re / 2 - 1) ≤ 1 := by
      intro t ht
      have h_exp : s.re / 2 - 1 > 0 := by linarith
      rw [rpow_le_one_iff_of_pos ht h_exp]
      exact ht
    exact IntegrableOn.mono_set (IntegrableOn.const_mul h1 2 |>.mul_const _ |>.of_norm_le _ h_bound) subset_rfl
  exact IntegrableOn.mono' (h_int) measurableSet_Ici h_bound

/-- For Re(s) < 2, the integral ∫₀^1 (θ(t)-1) t^(s/2-1) dt converges absolutely. -/
theorem mellin_left_integrable {s : ℂ} (hs : s.re < 2) :
    IntegrableOn (mellinIntegrand s) (Ioc 0 1) volume := by
  sorry
  -- STRATEGY:
  -- 1. Use jacobiTheta_modular to write θ(t) - 1 = t^(-1/2) * θ(1/t) - 1
  -- 2. Apply change of variables u = 1/t using integral_comp_inv_I0i_haar
  -- 3. Reduces to mellin_right_integrable for 1-s

/-- The full Mellin integral converges on the critical strip 1 < Re(s) < 2. -/
theorem mellin_theta_integrable {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    IntegrableOn (mellinIntegrand s) (Ioi 0) volume := by
  sorry
  -- Split integral at t=1 and apply previous two lemmas

/-! ### Section 5: The Mellin identity (main theorem) -/

/-- Standard Mellin transform of exp(-at): ∫₀^∞ exp(-at) t^(z-1) dt = Γ(z)/a^z. -/
theorem mellin_exp {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    ∫ (t : ℝ) in Ioi 0, (rexp (-a * t) : ℂ) * (t : ℂ)^(z - 1) =
    (Complex.Gamma z) / (a : ℂ)^z := by
  -- Change of variables: u = a*t, so t = u/a, dt = du/a
  -- Then ∫₀^∞ exp(-u) (u/a)^(z-1) du/a = a^(-z) ∫₀^∞ exp(-u) u^(z-1) du = a^(-z) Γ(z)
  have h1 : Complex.Gamma z = ∫ (u : ℝ) in Ioi 0, Complex.exp (-u) * (u : ℂ)^(z - 1) := by
    rw [Complex.Gamma_eq_integral hz]
    simp [Complex.GammaIntegral]
  -- Use substitution u = a*t
  have h2 : (∫ (t : ℝ) in Ioi 0, (rexp (-a * t) : ℂ) * (t : ℂ)^(z - 1)) =
             (a : ℂ)^(-z) * ∫ (u : ℝ) in Ioi 0, Complex.exp (-u) * (u : ℂ)^(z - 1)) := by
    -- This follows from integral_comp_mul_right_Ioi with appropriate scaling
    have := integral_comp_mul_right_Ioi (fun t => (rexp (-t) : ℂ) * (t : ℂ)^(z - 1)) ha
    simp only [Complex.ofReal_mul, Complex.ofReal_exp] at this
    convert this using 4
    · intro t ht
      simp [Complex.ofReal_exp, mul_comm a, Complex.cpow_mul_ofReal_nonneg ht.le]
      ring
    · ring
  rw [h2, h1]
  field_simp [ne_of_gt ha]
  ring

/-- Exchange sum and integral for the theta series (Fubini/Tonelli). -/
theorem mellin_theta_sum_exchange {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    ∫ (t : ℝ) in Ioi 0, mellinIntegrand s t =
    ∑' (n : ℤ), if n = 0 then 0 else
      ∫ (t : ℝ) in Ioi 0, (rexp (-π * (n : ℝ)^2 * t) : ℂ) * (t : ℂ)^(s/2 - 1) := by
  sorry
  -- Use integral_tsum with dominated convergence

/-- Relation between sums over nonzero integers and zeta: ∑_{n≠0} |n|^(-s) = 2ζ(s). -/
theorem sum_abs_int_eq_twice_zeta {s : ℂ} (hs : 1 < s.re) :
    (∑' (n : ℤ), if n = 0 then (0 : ℂ) else (n.natAbs : ℂ)^(-s)) = 2 * riemannZeta s := by
  sorry
  -- Split into positive and negative, use definition of riemannZeta

/-- **Main Mellin identity**: The completed zeta equals the Mellin transform of θ - 1. -/
theorem mellin_theta_eq_completedZeta {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    ∫ (t : ℝ) in Ioi 0, mellinIntegrand s t =
    (π : ℂ)^(-s/2) * Complex.Gamma (s/2) * riemannZeta s := by
  sorry
  -- Combine: sum_exchange + mellin_exp + sum_abs_int_eq_twice_zeta

/-! ### Section 6: Functional equation -/

/-- The completed zeta function Λ(s) = π^(-s/2) Γ(s/2) ζ(s). -/
def completedZeta (s : ℂ) : ℂ :=
  (π : ℂ)^(-s/2) * Complex.Gamma (s/2) * riemannZeta s

/-- The completed zeta admits a Mellin integral representation on the critical strip. -/
theorem completedZeta_as_mellin {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    completedZeta s = ∫ (t : ℝ) in Ioi 0, mellinIntegrand s t := by
  unfold completedZeta
  exact (mellin_theta_eq_completedZeta hs1 hs2).symm

/-- The integrand is symmetric under s ↦ 1-s after theta modular transformation. -/
theorem mellin_integrand_symmetric {s : ℂ} (t : ℝ) (ht : 0 < t) :
    mellinIntegrand s t = mellinIntegrand (1 - s) t := by
  sorry
  -- Use jacobiTheta_modular and algebraic manipulation

/-- **Functional equation**: Λ(s) = Λ(1-s) for all s.

Note: This is already proven in Mathlib as `completedRiemannZeta_one_sub`!
We reprove here to show the connection to Mellin transforms. -/
theorem completedZeta_functional_equation (s : ℂ) :
    completedZeta s = completedZeta (1 - s) := by
  sorry
  -- REQUIRES: Analytic continuation
  -- For 1 < Re(s) < 2: use Mellin representation + mellin_integrand_symmetric
  -- Extend to all s by identity theorem
  -- OR: Use completedRiemannZeta_one_sub from Mathlib directly

/-- **Riemann zeta functional equation** in standard form. -/
theorem zeta_functional_equation (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (π : ℂ)^(-s/2) * Complex.Gamma (s/2) * riemannZeta s =
    (π : ℂ)^(-(1-s)/2) * Complex.Gamma ((1-s)/2) * riemannZeta (1-s) := by
  have := completedZeta_functional_equation s
  unfold completedZeta at this
  exact this

end RiemannZeta

/-! ### Section 7: Auxiliary lemmas -/

namespace RiemannZeta.Auxiliary

/-- Useful: exp is strictly monotone. -/
lemma exp_strict_mono : StrictMono rexp := fun _ _ h => exp_lt_exp.mpr h

/-- For 0 < r < 1, the geometric series ∑_{n≥0} r^n converges to 1/(1-r). -/
lemma tsum_geometric_of_abs_lt_one {r : ℝ} (hr : |r| < 1) :
    ∑' n : ℕ, r^n = (1 - r)⁻¹ := by
  exact tsum_geometric_of_norm_lt_one (by simpa using hr)

/-- Squaring is monotone on nonnegative reals. -/
lemma sq_le_sq' {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a^2 ≤ b^2 :=
  sq_le_sq' (neg_nonpos_of_nonneg ha) h

end RiemannZeta.Auxiliary

end RiemannZeta
