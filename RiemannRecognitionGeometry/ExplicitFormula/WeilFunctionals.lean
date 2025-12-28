/-
Copyright (c) 2024 Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Washburn, Gemini
-/
import RiemannRecognitionGeometry.ExplicitFormula.WeilTestFunction
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.VonMangoldt

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula
namespace WeilFunctionals

open Complex Real MeasureTheory SchwartzMap Topology Filter Set ArithmeticFunction WeilTestFunction

variable (f : WeilTestFunction)

/--
Logarithmic derivative of the Gamma factor for Zeta, `Γℝ(s) = π^{-s/2} Γ(s/2)`.
Note: The factor π^{-s/2} adds a -1/2 log π term to the derivative.
-/
def GammaLogDeriv (s : ℂ) : ℂ :=
  (logDeriv Complex.Gamma) s

/--
Archimedean term for Zeta.
`𝒜(g) = \frac{1}{4\pi} \int_{-\infty}^\infty g(x) \Psi_{arch}(x) dx`
Derived from the Gamma factor in the functional equation.
-/
def archimedeanTerm : ℂ :=
  let h := fourierTransformCLM ℂ f.toSchwartz
  let term1 := (1 / (2 * π)) * ∫ x : ℝ, f.toSchwartz x *
    (GammaLogDeriv (1/4 + Complex.I * (x/2)) + GammaLogDeriv (1/4 - Complex.I * (x/2)))
  let term2 := - h 0 * Real.log π
  term1 + term2

/--
Prime power contribution:
`∑_{n} \frac{\Lambda(n)}{\sqrt{n}} (g(\log n) + g(-\log n))`
-/
def primeTerm : ℂ :=
  - ∑' n : ℕ, if n = 0 then 0 else
    ((vonMangoldt n : ℂ) / Real.sqrt n) *
      (f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n))

/--
Absolute convergence of the prime-power series defining `primeTerm`.

This is the analytic input needed to justify swapping prime sums with integrals in the explicit-formula
derivation (a Track 2 obligation).
-/
theorem summable_primeTerm (f : WeilTestFunction) :
    Summable (fun n : ℕ =>
      if n = 0 then (0 : ℂ) else
        ((vonMangoldt n : ℂ) / Real.sqrt n) *
          (f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n))) := by
  classical
  -- Use the exponential decay bound for `f`.
  obtain ⟨C, ε, hε, hbound⟩ := f.decay
  have hC0 : 0 ≤ C := by
    have h0 := hbound 0
    have : ‖f.toSchwartz 0‖ ≤ C := by
      simpa using h0
    exact le_trans (norm_nonneg _) this
  set δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith

  -- A summable comparison series: `n ↦ const / n^(1+δ)`.
  have hsum_r :
      Summable (fun n : ℕ => ((n : ℝ) ^ (1 + δ))⁻¹) := by
    -- `∑ 1 / n^(1+δ)` converges for `1+δ > 1`.
    have : (1 : ℝ) < 1 + δ := by linarith
    -- `Real.summable_nat_rpow_inv` is stated for `(n^p)⁻¹`.
    simpa using (Real.summable_nat_rpow_inv (p := (1 + δ))).2 this
  have hsum_const :
      Summable (fun n : ℕ => (2 * C / δ) * ((n : ℝ) ^ (1 + δ))⁻¹) := by
    simpa using (hsum_r.mul_left (2 * C / δ))

  -- Apply direct comparison test in `ℂ`.
  refine Summable.of_norm_bounded (E := ℂ)
    (f := fun n : ℕ =>
      if n = 0 then (0 : ℂ) else
        ((vonMangoldt n : ℂ) / Real.sqrt n) *
          (f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n)))
    (g := fun n : ℕ => (2 * C / δ) * ((n : ℝ) ^ (1 + δ))⁻¹) hsum_const ?_
  intro n
  by_cases hn : n = 0
  ·
    have hne : (1 + δ) ≠ 0 := by linarith
    simp [hn, Real.zero_rpow hne]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mp hnpos

  -- Basic bounds on `Λ(n)` and `log n`.
  have hΛle : (vonMangoldt n) ≤ Real.log (n : ℝ) := by
    simpa using (ArithmeticFunction.vonMangoldt_le_log (n := n))
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn1
    exact Real.log_nonneg hn1'

  -- Bound the Schwartz values using the decay hypothesis.
  have hf1 : ‖f.toSchwartz (Real.log n)‖ ≤ C * Real.exp (-(1 / 2 + ε) * |Real.log n|) :=
    hbound (Real.log n)
  have hf2 : ‖f.toSchwartz (-Real.log n)‖ ≤ C * Real.exp (-(1 / 2 + ε) * |-Real.log n|) :=
    hbound (-Real.log n)
  have habs_log : |Real.log n| = Real.log (n : ℝ) := by
    -- since `n ≥ 1`, `log n ≥ 0`
    have : 0 ≤ Real.log (n : ℝ) := hlog_nonneg
    simpa using (_root_.abs_of_nonneg this)
  have habs_neg_log : |-Real.log n| = Real.log (n : ℝ) := by
    -- `|-x| = |x|`
    simpa [abs_neg, habs_log]

  -- Combine the two decay bounds and use triangle inequality.
  have hsum_f :
      ‖f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n)‖ ≤
        (C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ))) +
          (C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ))) := by
    -- triangle + rewrite `|±log n|`
    have := norm_add_le (f.toSchwartz (Real.log n)) (f.toSchwartz (-Real.log n))
    refine this.trans ?_
    have h1 : ‖f.toSchwartz (Real.log n)‖ ≤ C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)) := by
      simpa [habs_log] using hf1
    have h2 : ‖f.toSchwartz (-Real.log n)‖ ≤ C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)) := by
      simpa [habs_neg_log] using hf2
    exact add_le_add h1 h2

  -- Convert the exponential decay to a power bound: `exp(-(1/2+ε) log n) = n^(-(1/2+ε))`.
  have hexp_pow :
      Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)) = (n : ℝ) ^ (-(1 / 2 + ε)) := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    -- `Real.rpow_def_of_pos` + commutativity
    simp [Real.rpow_def_of_pos hn0, mul_assoc, mul_comm, mul_left_comm]

  -- A crude bound `log n ≤ n^δ / δ`.
  have hlog_le_rpow : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ :=
    Real.log_natCast_le_rpow_div n hδ

  -- Put it all together.
  have hterm :
      ‖((vonMangoldt n : ℂ) / Real.sqrt n) *
          (f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n))‖
        ≤ (2 * C / δ) * ((n : ℝ) ^ (1 + δ))⁻¹ := by
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hn0' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    -- Bound the prefactor norm by `log n / sqrt n`.
    have hpref :
        ‖(vonMangoldt n : ℂ) / Real.sqrt n‖ ≤ (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) := by
      have hΛ0 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hlog0 : 0 ≤ Real.log (n : ℝ) := hlog_nonneg
      have hΛabs : ‖(vonMangoldt n : ℂ)‖ = vonMangoldt n := by
        -- `‖(Λ n : ℂ)‖ = |Λ n| = Λ n` (since `Λ n ≥ 0`)
        simp [Complex.norm_eq_abs, Complex.abs_ofReal, _root_.abs_of_nonneg hΛ0]
      have hsqrtC : ‖(Real.sqrt (n : ℝ) : ℂ)‖ = Real.sqrt (n : ℝ) := by
        simp [Complex.norm_eq_abs, Complex.abs_ofReal, _root_.abs_of_nonneg (le_of_lt hsqrt_pos)]
      -- start from `Λ n ≤ log n` and divide by `sqrt n`
      have hdiv : (vonMangoldt n) / Real.sqrt (n : ℝ) ≤ Real.log (n : ℝ) / Real.sqrt (n : ℝ) :=
        div_le_div_of_nonneg_right hΛle (le_of_lt hsqrt_pos)
      -- rewrite the left side as a norm
      simpa [div_eq_mul_inv, norm_mul, norm_inv, hΛabs, hsqrtC, Complex.norm_eq_abs,
        Complex.abs_ofReal, _root_.abs_of_nonneg hΛ0, _root_.abs_of_pos hsqrt_pos] using hdiv

    -- Bound the Schwartz sum by `2*C*exp(...)`.
    have hsum_f' :
        ‖f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n)‖ ≤
          2 * C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)) := by
      have heq : (C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ))) +
            (C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)))
          = 2 * C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)) := by ring
      exact hsum_f.trans (le_of_eq heq)

    -- Combine prefactor and Schwartz bounds.
    have hmul1 :
        ‖((vonMangoldt n : ℂ) / Real.sqrt n) *
            (f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n))‖
          ≤ (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) *
              (2 * C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ))) := by
      have hnm := norm_mul ((vonMangoldt n : ℂ) / Real.sqrt n)
        (f.toSchwartz (Real.log n) + f.toSchwartz (-Real.log n))
      refine (le_of_eq hnm).trans ?_
      exact mul_le_mul hpref hsum_f' (by positivity) (by positivity)

    -- Now absorb the `log` using `log_natCast_le_rpow_div`.
    -- Rewrite `exp(-(1/2+ε)*log n) = n^(-(1/2+ε))`.
    have hexp : Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)) = (n : ℝ) ^ (-(1 / 2 + ε)) := hexp_pow
    -- Rewrite `1 / sqrt n = n^(-(1/2))`.
    have hinv_sqrt : (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simp [Real.sqrt_eq_rpow, Real.rpow_neg hn0']
    -- Convert to a `rpow` expression and apply `hlog_le_rpow`.
    have hlog_factor :
        (Real.log (n : ℝ)) * (n : ℝ) ^ (-(1 + ε)) ≤ (1 / δ) * (n : ℝ) ^ (-(1 + δ)) := by
      -- start from `log n ≤ n^δ / δ`, multiply by `n^(-(1+ε))` and simplify exponents
      have hlog' : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ := hlog_le_rpow
      have hmul' :
          Real.log (n : ℝ) * (n : ℝ) ^ (-(1 + ε)) ≤ ((n : ℝ) ^ δ / δ) * (n : ℝ) ^ (-(1 + ε)) :=
        mul_le_mul_of_nonneg_right hlog' (by
          have : 0 ≤ (n : ℝ) ^ (-(1 + ε)) := by
            exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le n)) _
          simpa [this])
      -- simplify RHS: `(n^δ/δ) * n^{-(1+ε)} = (1/δ) * n^{-(1+δ)}` since `δ = ε/2`
      have hδdef : δ = ε / 2 := rfl
      have hsimp :
          ((n : ℝ) ^ δ / δ) * (n : ℝ) ^ (-(1 + ε)) = (1 / δ) * (n : ℝ) ^ (-(1 + δ)) := by
        -- pure `rpow` algebra
        have hnpos : 0 < (n : ℝ) := hn0
        -- `n^δ / δ * n^{-(1+ε)} = (1/δ) * n^δ * n^{-(1+ε)} = (1/δ) * n^{δ-(1+ε)}`
        have hrpow_add : (n : ℝ) ^ δ * (n : ℝ) ^ (-(1 + ε)) = (n : ℝ) ^ (δ + (-(1 + ε))) :=
          (Real.rpow_add hnpos δ (-(1 + ε))).symm
        have hexp_eq : δ + (-(1 + ε)) = -(1 + δ) := by
          simp only [hδdef]
          ring
        calc ((n : ℝ) ^ δ / δ) * (n : ℝ) ^ (-(1 + ε))
            = (1 / δ) * ((n : ℝ) ^ δ * (n : ℝ) ^ (-(1 + ε))) := by ring
          _ = (1 / δ) * (n : ℝ) ^ (δ + (-(1 + ε))) := by rw [hrpow_add]
          _ = (1 / δ) * (n : ℝ) ^ (-(1 + δ)) := by rw [hexp_eq]
      exact hmul'.trans_eq hsimp

    have hfinal :
        (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) *
            (2 * C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)))
          ≤ (2 * C / δ) * ((n : ℝ) ^ (1 + δ))⁻¹ := by
      -- rewrite into `log n * n^{-(1+ε)} ≤ (1/δ) * n^{-(1+δ)}`
      have hnpos : 0 < (n : ℝ) := hn0
      have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (n : ℝ)
      -- compute `(1/sqrt n) * exp(-(1/2+ε)*log n) = n^{-(1+ε)}`
      have hsqrt_rpow : (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)) =
          (n : ℝ) ^ (-(1 + ε)) := by
        -- `sqrt n = n^(1/2)`, so `(sqrt n)^{-1} = n^{-1/2}`
        have hinv : (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ) ^ (-(1/2 : ℝ)) := by
          rw [hsqrt, ← Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt hnpos)]
          ring_nf
        -- `exp(-(1/2+ε)*log n) = n^{-(1/2+ε)}`
        have hexp' : Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)) = (n : ℝ) ^ (-(1/2 + ε)) := hexp
        -- combine: `n^{-1/2} * n^{-(1/2+ε)} = n^{-1/2 + (-(1/2+ε))} = n^{-(1+ε)}`
        have hsum : (-(1/2 : ℝ)) + (-(1/2 + ε)) = -(1 + ε) := by ring
        calc (Real.sqrt (n : ℝ))⁻¹ * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ))
            = (n : ℝ) ^ (-(1/2 : ℝ)) * (n : ℝ) ^ (-(1/2 + ε)) := by rw [hinv, hexp']
          _ = (n : ℝ) ^ ((-(1/2 : ℝ)) + (-(1/2 + ε))) := (Real.rpow_add hnpos _ _).symm
          _ = (n : ℝ) ^ (-(1 + ε)) := by rw [hsum]
      -- simplify LHS: `log n / sqrt n * (2*C*exp(...)) = 2*C * (log n * n^{-(1+ε)})`
      have hlhs : (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) *
            (2 * C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ))) =
          (2 * C) * (Real.log (n : ℝ) * (n : ℝ) ^ (-(1 + ε))) := by
        calc (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) *
              (2 * C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)))
            = Real.log (n : ℝ) * (Real.sqrt (n : ℝ))⁻¹ *
                (2 * C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ))) := by ring
          _ = 2 * C * (Real.log (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹ *
                Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)))) := by ring
          _ = 2 * C * (Real.log (n : ℝ) * (n : ℝ) ^ (-(1 + ε))) := by rw [hsqrt_rpow]
      -- use `hlog_factor` to bound
      have hmul : (2 * C) * (Real.log (n : ℝ) * (n : ℝ) ^ (-(1 + ε))) ≤
          (2 * C) * ((1 / δ) * (n : ℝ) ^ (-(1 + δ))) :=
        mul_le_mul_of_nonneg_left hlog_factor (by positivity)
      -- finish by rewriting the RHS as `(2*C/δ) * (n^(1+δ))⁻¹`
      have hrhs : (2 * C) * ((1 / δ) * (n : ℝ) ^ (-(1 + δ))) =
          (2 * C / δ) * ((n : ℝ) ^ (1 + δ))⁻¹ := by
        have hneg_inv : (n : ℝ) ^ (-(1 + δ)) = ((n : ℝ) ^ (1 + δ))⁻¹ := by
          rw [Real.rpow_neg (le_of_lt hnpos)]
        calc (2 * C) * ((1 / δ) * (n : ℝ) ^ (-(1 + δ)))
            = (2 * C / δ) * (n : ℝ) ^ (-(1 + δ)) := by ring
          _ = (2 * C / δ) * ((n : ℝ) ^ (1 + δ))⁻¹ := by rw [hneg_inv]
      -- assemble the chain
      calc (Real.log (n : ℝ) / Real.sqrt (n : ℝ)) *
            (2 * C * Real.exp (-(1 / 2 + ε) * Real.log (n : ℝ)))
          = (2 * C) * (Real.log (n : ℝ) * (n : ℝ) ^ (-(1 + ε))) := hlhs
        _ ≤ (2 * C) * ((1 / δ) * (n : ℝ) ^ (-(1 + δ))) := hmul
        _ = (2 * C / δ) * ((n : ℝ) ^ (1 + δ))⁻¹ := hrhs

    exact hmul1.trans hfinal

  -- Finish the bound for the `if`-expression.
  simp only [hn, if_neg, not_false_eq_true]
  exact hterm

/--
Geometric side: Sum of prime term, archimedean term, and boundary terms (poles).
This corresponds to the "Arithmetic Side" in the Lagarias formulation (explicit formula).
`Warith(f) = W_primes + W_arch + W_poles`.
-/
def Warith : ℂ :=
  f.weilTransform 1 +
  f.weilTransform 0 +
  primeTerm f +
  archimedeanTerm f

/--
The Weil Positivity Gate (Concrete).
The Riemann Hypothesis is equivalent to `Warith (f.convolution f.conjugation.reflection) ≥ 0`
for all Weil test functions `f`.
-/
def WeilGate : Prop :=
  ∀ f : WeilTestFunction, 0 ≤ (Warith (f.convolution f.conjugation.reflection)).re

end WeilFunctionals
end ExplicitFormula
end RiemannRecognitionGeometry
