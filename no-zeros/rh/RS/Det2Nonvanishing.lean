import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import rh.RS.Det2Outer
import rh.academic_framework.DiagonalFredholm.Determinant
open scoped Real

/-!
# det₂ Euler factors: local estimates toward nonvanishing on Ω

This module starts the analytic work needed to prove `det2_nonzero_on_RSΩ`.
We focus on the prime Euler factors and prove concrete bounds that will feed
the summability and product arguments in later steps.  Each lemma here is fully
proved (no admits) so we keep forward momentum—even if strengthening these
estimates later takes additional effort.
-/

noncomputable section

open Complex

namespace RH
namespace RS

open scoped BigOperators

/-- Right half-plane domain Ω. -/
local notation "Ω" => RH.RS.Ω

namespace Det2

open RH.AcademicFramework.DiagonalFredholm

variable {s : ℂ}

/-- For any prime `p`, the norm of the complex power `(p : ℂ) ^ (-s)` depends
only on the real part of `s`. This follows from the general `abs_cpow` identity.
-/
lemma norm_prime_cpow_neg (p : Nat.Primes) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  simpa [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hp]

/-- On Ω = {Re s > 1/2}, the Euler-factor base `λ := p^(−s)` satisfies the universal bound
`‖λ‖ ≤ 2^(−1/2)`. This uses monotonicity of real powers in the exponent and (for negative
exponents) in the base. -/
lemma lambda_norm_le_inv_sqrt_two_onOmega (p : Nat.Primes)
    (hs : (1/2 : ℝ) < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-(1/2 : ℝ)) := by
  classical
  have hnorm := norm_prime_cpow_neg (p := p) (s := s)
  -- Step 1: decrease the exponent from `-s.re` to `-(1/2)` using `Re s ≥ 1/2` and base ≥ 1
  have hs_le : (1/2 : ℝ) ≤ s.re := le_of_lt hs
  have h_exp_mono : (p : ℝ) ^ (-(s.re)) ≤ (p : ℝ) ^ (-(1/2 : ℝ)) := by
    -- For base ≥ 1, `a^x` is monotone in `x`
    have hp_ge_one : (1 : ℝ) ≤ (p : ℝ) := by
      have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
      exact (by norm_num : (1 : ℝ) ≤ 2).trans hp_two
    have hx : -(s.re) ≤ -(1/2 : ℝ) := by exact neg_le_neg hs_le
    exact Real.rpow_le_rpow_of_base_ge_one hp_ge_one hx
  -- Step 2: compare bases at fixed negative exponent r = -(1/2)
  have h_base_mono : (p : ℝ) ^ (-(1/2 : ℝ)) ≤ (2 : ℝ) ^ (-(1/2 : ℝ)) := by
    -- For r ≤ 0, `b ≥ a ≥ 0` gives `b^r ≤ a^r`
    have h_nonpos : (-(1/2 : ℝ)) ≤ 0 := by norm_num
    have h0le2 : (0 : ℝ) ≤ 2 := by norm_num
    have h2lep : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    simpa using Real.rpow_le_rpow_of_exponent_nonpos h0le2 h2lep h_nonpos
  -- Wrap up
  simpa [hnorm] using le_trans h_exp_mono h_base_mono

/-- With `λ := p^(−s)` and `w := λ + λ^2/2`, we have on Ω the quantitative bound
`‖w‖ ≤ c + c^2/2` where `c = 2^(−1/2)`. In particular, a numerically sharp estimate
(c ≤ 3/4 and hence `c + c^2/2 < 1`) yields `‖w‖ < 1`. -/
lemma w_norm_le_from_lambda_onOmega (p : Nat.Primes)
    (hs : (1/2 : ℝ) < s.re) :
    let λ : ℂ := (p : ℂ) ^ (-s)
    let w : ℂ := λ + λ^2 / 2
    in ‖w‖ ≤ (2 : ℝ) ^ (-(1/2 : ℝ)) + ((2 : ℝ) ^ (-(1/2 : ℝ)))^2 / 2 := by
  classical
  intro λ w
  -- Triangle inequality and basic norm algebra
  have h1 : ‖w‖ ≤ ‖λ‖ + ‖λ^2 / 2‖ := by
    simpa [w, sub_eq_add_neg] using Complex.norm_add_le λ (λ^2 / 2)
  have hdiv : ‖λ^2 / 2‖ = ‖λ‖^2 / 2 := by
    have : ‖λ^2‖ = ‖λ‖^2 := by simpa using Complex.norm_pow λ 2
    simpa [div_eq_mul_inv, Complex.norm_mul, Complex.norm_inv, this]
  have hc : ‖λ‖ ≤ (2 : ℝ) ^ (-(1/2 : ℝ)) :=
    lambda_norm_le_inv_sqrt_two_onOmega (p := p) (s := s) hs
  -- Monotonicity of y ↦ y + y^2/2 on y ≥ 0
  have hmono_sq : ‖λ‖^2 ≤ ((2 : ℝ) ^ (-(1/2 : ℝ)))^2 := by
    have hnonneg : 0 ≤ ‖λ‖ := Complex.norm_nonneg _
    have := mul_le_mul hc hc hnonneg (by exact Real.rpow_nonneg_of_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    simpa [pow_two] using this
  have hsum : ‖λ‖ + ‖λ‖^2 / 2 ≤ (2 : ℝ) ^ (-(1/2 : ℝ)) + ((2 : ℝ) ^ (-(1/2 : ℝ)))^2 / 2 := by
    exact add_le_add (by exact hc) (by exact (div_le_div_of_nonneg_right hmono_sq (by norm_num : (0:ℝ) ≤ 2)))
  -- Conclude
  have := le_trans h1 (by simpa [hdiv] using hsum)
  exact this

/-- A crude but unconditional bound for the det₂ Euler factor.  We only need a
polynomial-type control, so we bound the exponential piece using
`abs_exp_sub_one_le` and the algebraic part directly.
-/
lemma norm_det2EulerFactor_le (p : Nat.Primes) (s : ℂ) :
    ‖det2EulerFactor s p‖ ≤ (1 + ‖(p : ℂ) ^ (-s)‖) *
      Real.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) := by
  classical
  dsimp [det2EulerFactor]
  have h1 : ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + ‖(p : ℂ) ^ (-s)‖ := by
    simpa [sub_eq_add_neg] using Complex.norm_sub_le (1 : ℂ) ((p : ℂ) ^ (-s))
  have h2 : ‖Complex.exp ((p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2)‖
      = Real.exp (‖(p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2‖) := by
    simpa using Complex.norm_exp _
  have h3 : ‖(p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2‖
      ≤ ‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2 := by
    have := Complex.norm_add_le ((p : ℂ) ^ (-s)) ((p : ℂ) ^ (-2 * s) / 2)
    have hdiv : ‖(p : ℂ) ^ (-2 * s) / 2‖ = ‖(p : ℂ) ^ (-2 * s)‖ / 2 := by
      simp [div_eq_mul_inv, Complex.norm_mul, Complex.norm_inv]
    simpa [hdiv]
  have h4 : Real.exp (‖(p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s) / 2‖)
      ≤ Real.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) := by
    exact Real.exp_le_exp.mpr h3
  have := mul_le_mul h1 h4 (by positivity) (by positivity)
  simpa [Complex.norm_mul, h2] using this

/-- Quantitative remainder control: `det2EulerFactor s p` stays within a linear
bound of `1`, which already suffices to initiate the summability estimates.  The
target cubic decay will be approached by sharpening this lemma later.
-/
lemma norm_det2EulerFactor_sub_one_bound
    (p : Nat.Primes) (s : ℂ) :
    ‖det2EulerFactor s p - 1‖ ≤
      (1 + ‖(p : ℂ) ^ (-s)‖) *
        Real.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) + 1 := by
  classical
  have h := Complex.norm_sub_le (det2EulerFactor s p) 1
  have hbound := norm_det2EulerFactor_le (p := p) (s := s)
  have : ‖det2EulerFactor s p‖
      ≤ (1 + ‖(p : ℂ) ^ (-s)‖) *
        Real.exp (‖(p : ℂ) ^ (-s)‖ + ‖(p : ℂ) ^ (-2 * s)‖ / 2) :=
    hbound
  have h1 : ‖det2EulerFactor s p - 1‖
      ≤ ‖det2EulerFactor s p‖ + 1 := h
  exact le_trans h1 (by
    have := add_le_add this (le_of_eq rfl)
    simpa)

/-- Quadratic-exponential remainder bound for a single Euler factor.
Let `λ := p^{-s}` and `w := λ + λ^2/2`. Then
`‖(1 - λ)·exp(w) - 1‖ ≤ ((‖w‖^2 + ‖λ‖·‖w‖ + ‖λ‖^2/2) · exp ‖w‖)`.
This gives an `O(‖λ‖^2 · exp(‖w‖))` control suitable for summability on Ω.
-/
lemma eulerFactor_remainder_quadratic_exp
    (p : Nat.Primes) (s : ℂ) :
    let λ : ℂ := (p : ℂ) ^ (-s)
    let w : ℂ := λ + λ ^ 2 / 2
    in ‖det2EulerFactor s p - 1‖
       ≤ ((‖w‖ ^ 2) + ‖λ‖ * ‖w‖ + (‖λ‖ ^ 2) / 2) * Real.exp ‖w‖ := by
  classical
  intro λ w
  -- Shorthands
  let E : ℂ := Complex.exp w
  have hdet : det2EulerFactor s p = (1 - λ) * E := by
    dsimp [det2EulerFactor, w, λ]
    rfl
  -- Algebraic decomposition: E - 1 - λ E = (E-1-w) + (w-λ) - λ (E-1)
  have hdecomp : E - 1 - λ * E = (E - 1 - w) + (w - λ) - λ * (E - 1) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, w]
    ring
  -- Start from the definition
  have hstart : ‖det2EulerFactor s p - 1‖ = ‖E - 1 - λ * E‖ := by
    simp [hdet, mul_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Triangle inequality on the decomposition
  have htri1 : ‖(E - 1 - w) + (w - λ) - λ * (E - 1)‖
      ≤ ‖(E - 1 - w) + (w - λ)‖ + ‖λ * (E - 1)‖ := by
    simpa [sub_eq_add_neg] using Complex.norm_sub_le ((E - 1 - w) + (w - λ)) (λ * (E - 1))
  have htri2 : ‖(E - 1 - w) + (w - λ)‖ ≤ ‖E - 1 - w‖ + ‖w - λ‖ :=
    Complex.norm_add_le _ _
  have hmul : ‖λ * (E - 1)‖ = ‖λ‖ * ‖E - 1‖ := by
    simpa using Complex.norm_mul λ (E - 1)
  -- Collect the three pieces
  have hsum : ‖E - 1 - λ * E‖
      ≤ ‖E - 1 - w‖ + ‖w - λ‖ + ‖λ‖ * ‖E - 1‖ := by
    have := le_trans htri1 (add_le_add_right htri2 _)
    simpa [hmul, add_comm, add_left_comm, add_assoc, hdecomp]
      using this
  have h1 : ‖E - 1 - w‖ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by
    simpa [E] using RH.RS.norm_exp_sub_one_sub_id_le w
  have h2 : ‖E - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
    simpa [E] using RH.RS.norm_exp_sub_one_le_norm_mul_exp_norm w
  have hwλ : w - λ = λ ^ 2 / 2 := by
    simp [w, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have h3 : ‖w - λ‖ = ‖λ‖ ^ 2 / 2 := by
    have : ‖λ ^ 2 / (2 : ℂ)‖ = ‖λ‖ ^ 2 / 2 := by
      simp [Complex.norm_div, Complex.norm_pow, Complex.norm_ofReal]
    simpa [hwλ]
  -- Assemble
  have hpos : 1 ≤ Real.exp ‖w‖ := by
    have : (0 : ℝ) ≤ ‖w‖ := by positivity
    simpa using Real.exp_le_exp.mpr this
  have h3' : ‖w - λ‖ ≤ (‖λ‖ ^ 2 / 2) * Real.exp ‖w‖ := by
    have := mul_le_mul_of_nonneg_right (le_of_eq h3) (by positivity : 0 ≤ Real.exp ‖w‖)
    simpa [mul_comm] using this
  have hsum' := add_le_add (add_le_add h1 h3') (mul_le_mul_of_nonneg_left h2 (by positivity))
  -- Final simplification
  simpa [hstart, mul_add, add_comm, add_left_comm, add_assoc]
    using hsum'

lemma eulerFactor_remainder_quadratic_small
    (p : Nat.Primes) (s : ℂ)
    (hsmall :
      let λ : ℂ := (p : ℂ) ^ (-s)
      let w : ℂ := λ + λ ^ 2 / 2
      ‖w‖ ≤ 1)
    :
    let λ : ℂ := (p : ℂ) ^ (-s)
    let w : ℂ := λ + λ ^ 2 / 2
    in ‖det2EulerFactor s p - 1‖
       ≤ ‖w‖ ^ 2 + 2 * ‖λ‖ * ‖w‖ + (‖λ‖ ^ 2) / 2 := by
  classical
  intro λ w
  have hsmall' : ‖w‖ ≤ 1 := by
    simpa using hsmall
  -- abbreviate E := exp w
  let E : ℂ := Complex.exp w
  have hdet : det2EulerFactor s p = (1 - λ) * E := by
    dsimp [det2EulerFactor, w, λ]
    rfl
  -- decomposition
  have hdecomp : E - 1 - λ * E = (E - 1 - w) + (w - λ) - λ * (E - 1) := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, w]
    ring
  -- triangle pieces
  have htri1 : ‖(E - 1 - w) + (w - λ) - λ * (E - 1)‖
      ≤ ‖(E - 1 - w) + (w - λ)‖ + ‖λ * (E - 1)‖ := by
    simpa [sub_eq_add_neg] using
      Complex.norm_sub_le ((E - 1 - w) + (w - λ)) (λ * (E - 1))
  have htri2 : ‖(E - 1 - w) + (w - λ)‖ ≤ ‖E - 1 - w‖ + ‖w - λ‖ :=
    Complex.norm_add_le _ _
  have hmul : ‖λ * (E - 1)‖ = ‖λ‖ * ‖E - 1‖ := by
    simpa using Complex.norm_mul λ (E - 1)
  -- bound ‖E - 1 - w‖ via mathlib small-argument
  have h1 : ‖E - 1 - w‖ ≤ ‖w‖ ^ 2 := by
    -- abs variant
    have : Complex.abs (Complex.exp w - 1 - w) ≤ Complex.abs w ^ 2 :=
      Complex.abs_exp_sub_one_sub_id_le (by simpa [Complex.norm_eq_abs] using hsmall')
    simpa [E, Complex.norm_eq_abs] using this
  -- bound ‖w - λ‖ algebraically
  have hwλ : w - λ = λ ^ 2 / 2 := by
    simp [w, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have h2 : ‖w - λ‖ = ‖λ‖ ^ 2 / 2 := by
    have : ‖λ ^ 2 / (2 : ℂ)‖ = ‖λ‖ ^ 2 / 2 := by
      simp [Complex.norm_div, Complex.norm_pow, Complex.norm_ofReal]
    simpa [hwλ]
  -- bound ‖E - 1‖ via mathlib small-argument
  have h3 : ‖E - 1‖ ≤ 2 * ‖w‖ := by
    have : Complex.abs (Complex.exp w - 1) ≤ 2 * Complex.abs w :=
      Complex.abs_exp_sub_one_le (by simpa [Complex.norm_eq_abs] using hsmall')
    simpa [E, Complex.norm_eq_abs] using this
  -- assemble
  have hsum : ‖E - 1 - λ * E‖ ≤ ‖w‖ ^ 2 + (‖λ‖ ^ 2 / 2) + (‖λ‖ * (2 * ‖w‖)) := by
    have := le_trans htri1 (add_le_add_right htri2 _)
    have : ‖E - 1 - λ * E‖ ≤ (‖E - 1 - w‖ + ‖w - λ‖) + ‖λ‖ * ‖E - 1‖ := by
      simpa [hmul, add_comm, add_left_comm, add_assoc, hdecomp] using this
    refine this.trans ?_
    have := add_le_add (add_le_add h1 (by simpa [h2]))
      (mul_le_mul_of_nonneg_left h3 (by positivity))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- reorder terms
  have : ‖det2EulerFactor s p - 1‖
      = ‖E - 1 - λ * E‖ := by
    simp [hdet, mul_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have := this ▸ hsum
  -- convert ‖λ‖ * (2 * ‖w‖) to 2 * ‖λ‖ * ‖w‖ and reassociate
  have : (‖w‖ ^ 2 + (‖λ‖ ^ 2 / 2) + (‖λ‖ * (2 * ‖w‖)))
      = (‖w‖ ^ 2 + 2 * ‖λ‖ * ‖w‖ + (‖λ‖ ^ 2) / 2) := by ring
  simpa [this] using this

/-- Numeric bound: let `c := 2^(−1/2) = 1/√2`. Then `c + c^2/2 ≤ 1`. -/
lemma two_pow_neg_half_plus_square_half_le_one :
  (2 : ℝ) ^ (-(1/2 : ℝ)) + ((2 : ℝ) ^ (-(1/2 : ℝ)))^2 / 2 ≤ 1 := by
  classical
  -- Show `2^(−1/2) = 1/√2`
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hneg : (2 : ℝ) ^ (-(1/2 : ℝ)) = ((2 : ℝ) ^ (1/2 : ℝ))⁻¹ := by
    simpa [Real.rpow_neg, h2ne]
      using (Real.rpow_neg (2 : ℝ) (1/2 : ℝ))
  have hsqrt : (2 : ℝ) ^ (1/2 : ℝ) = Real.sqrt 2 := by
    have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
    simpa [hnonneg] using (Real.sqrt_eq_rpow hnonneg).symm
  have hc : (2 : ℝ) ^ (-(1/2 : ℝ)) = 1 / Real.sqrt 2 := by
    simpa [hneg, hsqrt, inv_eq_one_div]
  -- Then the bound reduces to `1/√2 + (1/2)/2 ≤ 1`, i.e. `1/√2 ≤ 3/4`.
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h43_le_sqrt2 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
    -- use `Real.le_sqrt` with squares: (4/3)^2 = 16/9 ≤ 2
    have hsq : ((4 : ℝ) / 3)^2 ≤ (2 : ℝ) := by norm_num
    have : 0 ≤ (2 : ℝ) := by norm_num
    have hnonneg43 : 0 ≤ (4 : ℝ) / 3 := by norm_num
    have := (Real.le_sqrt this).2
      ⟨by simpa [pow_two] using hsq, hnonneg43⟩
    simpa using this
  have inv_le : 1 / Real.sqrt 2 ≤ 1 / ((4 : ℝ) / 3) :=
    (one_div_le_one_div_of_le (by norm_num) h43_le_sqrt2)
  have h_one_div_43 : 1 / ((4 : ℝ) / 3) = (3 : ℝ) / 4 := by
    field_simp
  have h_main : 1 / Real.sqrt 2 ≤ (3 : ℝ) / 4 := by simpa [h_one_div_43] using inv_le
  -- Now finish
  have : (1 / Real.sqrt 2) + ((1 / Real.sqrt 2)^2) / 2 ≤ 1 := by
    have hsq : (1 / Real.sqrt 2)^2 = (1 : ℝ) / 2 := by
      -- (1/√2)^2 = 1 / (√2)^2 = 1/2
      have : (Real.sqrt 2)^2 = (2 : ℝ) := by
        simpa [pow_two] using Real.sqrt_mul_self (by norm_num : 0 ≤ (2 : ℝ))
      -- manipulate fractions
      have : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / (Real.sqrt 2)^2 := by
        field_simp [pow_two]
      simpa [this] using congrArg (fun x : ℝ => (1 : ℝ) / x) this
    have : (1 / Real.sqrt 2) + ((1 : ℝ) / 2) / 2 ≤ 1 := by
      -- reduce to 1/√2 ≤ 3/4
      have : (1 : ℝ) / 2 / 2 = (1 : ℝ) / 4 := by field_simp
      simpa [this] using add_le_add_of_le_of_le h_main (le_of_eq rfl)
    simpa [hsq] using this
  simpa [hc] using this

/-- On Ω, the `w`-parameter is small: `‖w‖ ≤ 1`. -/
lemma w_small_onOmega (p : Nat.Primes) (s : ℂ)
    (hs : (1/2 : ℝ) < s.re) :
    let λ : ℂ := (p : ℂ) ^ (-s)
    let w : ℂ := λ + λ ^ 2 / 2
    in ‖w‖ ≤ 1 := by
  classical
  intro λ w
  -- bound by `c + c^2/2` with `c = 2^(−1/2)` and then apply the numeric lemma
  have hbound := w_norm_le_from_lambda_onOmega (p := p) (s := s) hs
  have hnum := two_pow_neg_half_plus_square_half_le_one
  exact le_trans hbound hnum

/-- On Ω, the Euler-factor remainder admits a small-argument quadratic bound. -/
lemma eulerFactor_remainder_onOmega
    (p : Nat.Primes) (s : ℂ) (hs : (1/2 : ℝ) < s.re) :
    let λ : ℂ := (p : ℂ) ^ (-s)
    let w : ℂ := λ + λ ^ 2 / 2
    in ‖det2EulerFactor s p - 1‖
       ≤ ‖w‖ ^ 2 + 2 * ‖λ‖ * ‖w‖ + (‖λ‖ ^ 2) / 2 := by
  classical
  intro λ w
  -- Use the small-argument wrapper
  exact eulerFactor_remainder_quadratic_small (p := p) (s := s)
    (by simpa using w_small_onOmega (p := p) (s := s) hs)

end Det2

end RS
end RH
