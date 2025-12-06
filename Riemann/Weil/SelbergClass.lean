import Mathlib
import Riemann
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
-- We import these to ensure we can eventually link to the Zero Density and Hadamard machinery
import PrimeNumberTheoremAnd.HadamardFactorization
import StrongPNT.PNT1_ComplexAnalysis

open Mathlib LSeries EulerProduct Analysis Complex
/-!
# The Selberg Class of L-functions

This file defines the Selberg class of L-functions, a class of Dirichlet series
satisfying four axioms: analyticity, Ramanujan conjecture, functional equation,
and Euler product.

## Main Definitions

* `SelbergClass`: A structure bundling the data and properties of a function in the Selberg class.

## References

* [A. Selberg, *Old and new conjectures about a class of Dirichlet series*][selberg1992]
-/

noncomputable section

open Set Complex Real Topology Filter Asymptotics ArithmeticFunction

namespace NumberTheory.Selberg

/--
The **Selberg Class** `S` consists of Dirichlet series `F(s) = ∑ a_n n⁻ˢ` satisfying:
1. **Ramanujan hypothesis**: `a_n ≪ n^ε` for any `ε > 0`.
2. **Analyticity**: `(s-1)^m F(s)` is an entire function of **finite order**.
3. **Functional equation**: `Φ(s) = ω Φ(1-s)`.
4. **Euler product**: `log F(s) = ∑ b_n n⁻ˢ`.
-/
structure SelbergClass where
  /-- The Dirichlet coefficients `a_n`. -/
  a : ℕ → ℂ
  /-- Normalization `a_1 = 1`. -/
  a_one : a 1 = 1
  /-- The L-function defined by the series. -/
  F : ℂ → ℂ
  /-- The series converges to F for Re(s) > 1. -/
  l_series_eq : ∀ s, 1 < s.re → F s = LSeries a s

  /-- **Axiom 1: Ramanujan Hypothesis** (coefficient bound). -/
  a_bound : ∀ ε > 0, IsBigO atTop a (fun n ↦ (n : ℝ) ^ ε)

  /-- **Axiom 2: Analyticity**.
      There exists an integer `m` (order of pole at s=1) such that `(s-1)^m F(s)` extends to an entire function. -/
  m : ℕ
  /-- The completed function (minus the pole) extends to an entire function. -/
  entire_continuation : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ EqOn g (fun s ↦ (s - 1) ^ m * F s) {1}ᶜ
  /-- **Finite Order**: The function `(s-1)^m F(s)` has finite order of growth.
      This is required for the Hadamard factorization. -/
  finite_order : ∃ (A : ℝ) (B : ℝ), ∀ s, s ≠ 1 → ‖(s - 1) ^ m * F s‖ ≤ A * Real.exp (Real.exp (B * ‖s‖))

  /-- **Axiom 3: Functional Equation**. -/
  Q : ℝ
  Q_pos : 0 < Q
  k : ℕ
  lambda : Fin k → ℝ
  lambda_pos : ∀ i, 0 < lambda i
  mu : Fin k → ℂ
  mu_re_nonneg : ∀ i, 0 ≤ (mu i).re
  omega : ℂ
  omega_norm : ‖omega‖ = 1

  /-- The completed function `Φ(s)`. -/
  Phi : ℂ → ℂ := fun s ↦ Q ^ s * (∏ i : Fin k, Gamma (lambda i * s + mu i)) * F s

  /-- The functional equation relates `Φ(s)` and `Φ(1-s)`. -/
  functional_equation : ∀ s, Phi s = omega * star (Phi (1 - star s))

  /-- **Axiom 4: Euler Product**.
      Expressed via the coefficients `b_n` of the Dirichlet series for `log F(s)`. -/
  b : ℕ → ℂ
  b_zero : b 0 = 0
  b_support : ∀ n, b n ≠ 0 → IsPrimePow n
  theta : ℝ
  theta_lt_half : theta < 1/2
  b_bound : ∀ n, ‖b n‖ ≤ n ^ theta
  /-- Equality of `F` with the exponential of the series involving `b`. -/
  euler_product_eq : ∀ s, 1 < s.re → F s = Complex.exp (LSeries b s)

/--
A **Motivic L-function** is expected to be in the Selberg class.
Since we lack a definition of Motives in Mathlib, we define the *analytic data*
associated with a motivic L-function.
-/
structure MotivicLFunctionData extends SelbergClass where
  /-- The weight of the motive. -/
  w : ℤ
  /-- The degree of the L-function (sum of 2 * lambda_i). -/
  d : ℕ
  /-- Consistency check: The degree matches the sum of lambda parameters. -/
  degree_eq : (∑ i, 2 * lambda i) = (d : ℝ)

namespace SelbergClass
open Finset
/-- The degree of the L-function, defined as `2 * ∑ λ_i`. -/
def degree (L : SelbergClass) : ℝ := 2 * ∑ i, L.lambda i

/--
A version of the Removable Singularity Theorem:
If `f` is continuous on `ℂ` and holomorphic on `ℂ \ {c}`, then `f` is entire.
-/
lemma differentiable_of_continuous_of_differentiableOn_compl_singleton
    {f : ℂ → ℂ} {c : ℂ} (h_cont : Continuous f)
    (h_diff : DifferentiableOn ℂ f {c}ᶜ) :
    Differentiable ℂ f := by
  -- Use the removable singularity API with `s = univ`
  have hs : (univ : Set ℂ) ∈ 𝓝 c := univ_mem
  -- `differentiableOn_compl_singleton_and_continuousAt_iff` expects `s \ {c}`
  have h_diff' : DifferentiableOn ℂ f ((univ : Set ℂ) \ {c}) := by
    -- `{c}ᶜ = univ \ {c}` as sets
    convert h_diff using 1
    ext z
    simp [mem_compl_iff, mem_diff, mem_singleton_iff, mem_univ]
  have h_pair : DifferentiableOn ℂ f ((univ : Set ℂ) \ {c}) ∧ ContinuousAt f c :=
    ⟨h_diff', h_cont.continuousAt⟩
  have h_all :
      DifferentiableOn ℂ f (univ : Set ℂ) :=
        (differentiableOn_compl_singleton_and_continuousAt_iff hs).mp h_pair
  -- `h_all` is `DifferentiableOn ℂ f univ`, hence `Differentiable ℂ f`
  simpa [differentiableOn_univ] using h_all

/-
We assume `Mathlib.NumberTheory.LSeries.RiemannZeta` gives:

* `riemannZeta` as a meromorphic function with a simple pole at `1`,
* holomorphy on `ℂ \ {1}`.

If you already have a theorem there declaring holomorphy on `ℂ \ {1}`, replace the proof below by a direct reference.
-/

/-- `riemannZeta` is holomorphic on `ℂ \ {1}`. -/
lemma differentiableOn_riemannZeta :
    DifferentiableOn ℂ riemannZeta {1}ᶜ := by
  -- `riemannZeta` is meromorphic with only pole at 1 (from Mathlib).
  -- This typically appears as a statement that `riemannZeta` is holomorphic away from `{1}`.
  -- We rephrase it as `DifferentiableOn` using the `analyticAt`/`analyticOn` API.
  -- If Mathlib has `analyticOn_riemannZeta : AnalyticOn ℂ riemannZeta {1}ᶜ`,
  -- this becomes just: `exact (analyticOn_riemannZeta.differentiableOn)`
  have h_analytic : AnalyticOn ℂ riemannZeta {1}ᶜ :=
    -- replace this `sorry` by the actual Mathlib lemma once you locate it
    -- for now we assume riemannZeta is given by an analytic continuation
    -- with only a simple pole at 1.
    -- If you don't yet have such a lemma, this is where you should build one
    -- using the representation of ζ(s) in `RiemannZeta.lean`.
    sorry
  exact h_analytic.differentiableOn

/--
`(s - 1) * ζ(s)` tends to `1` as `s → 1`.

This encodes that ζ has a simple pole at `1` with residue `1`.
-/
lemma tendsto_sub_one_mul_riemannZeta_one :
    Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝 1) (𝓝 1) := by
  -- Strategy:
  -- 1. Define the function `g(s) = (s - 1) * ζ(s)` on `s ≠ 1`.
  -- 2. Use the principal part / Laurent expansion at 1 coming from `RiemannZeta.lean`
  --    which says the principal part at 1 is `(s-1)⁻¹` with coefficient 1 and bounded rest.
  -- 3. Then `(s-1)*ζ(s)` has a removable singularity at 1 with value 1 and is continuous.
  -- You likely already have in `RiemannZeta.lean` some theorem of the form
  -- `exists_limit_mul_sub_one_riemannZeta` or a residue statement.
  -- This is the place to turn that into the `Tendsto` lemma.
  have h_res :
      ∃ (L : ℂ), Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 L) := by
    -- prove existence of the limit on the punctured neighborhood using the
    -- specific representation of ζ around 1; the limit `L` will be 1.
    sorry
  rcases h_res with ⟨L, hL⟩
  -- Show `L = 1` using the specific expansion (again, from `RiemannZeta.lean`)
  have hL1 : L = 1 := by
    -- fill this using whatever explicit form of ζ(s) near 1 you have
    sorry
  -- Glue from `𝓝[≠] 1` to `𝓝 1` using the fact the function is bounded near 1
  -- and has at most a removable singularity.
  have h_lim :
      Tendsto (fun s : ℂ ↦ (s - 1) * riemannZeta s) (𝓝 1) (𝓝 L) := by
    -- standard lemma: limit along punctured neighborhood equals limit along full neighborhood
    -- if the singularity is removable.
    -- Otherwise, you can explicitly show continuity of the updated function.
    sorry
  simpa [hL1] using h_lim

/--
The function `(s-1)ζ(s)` extends to an entire function.
-/
lemma differentiable_mul_sub_one_riemannZeta :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      EqOn g (fun s ↦ (s - 1) * riemannZeta s) {1}ᶜ := by
  let g := Function.update (fun s ↦ (s - 1) * riemannZeta s) 1 1
  refine ⟨g, ?_, ?_⟩
  · -- `g` is entire by removable singularity
    -- 1. Differentiable on {1}ᶜ
    have h_diff_on : DifferentiableOn ℂ g {1}ᶜ := by
      -- On {1}ᶜ, g matches the product, which is differentiable
      apply DifferentiableOn.congr (f := fun s ↦ (s - 1) * riemannZeta s)
      · apply DifferentiableOn.mul
        · exact DifferentiableOn.sub differentiableOn_id differentiableOn_const
        · exact differentiableOn_riemannZeta
      · intro x hx
        simp [g, Function.update, mem_compl_singleton_iff.mp hx]

    -- 2. Continuous everywhere
    have h_cont : Continuous g := by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx : x = 1
      · -- Continuity at 1: matches the limit
        subst hx
        rw [continuousAt_update_same]
        exact tendsto_sub_one_mul_riemannZeta_one
      · -- Continuity on {1}ᶜ: follows from differentiability
        rw [continuousAt_update_of_ne hx]
        exact h_diff_on.continuousOn x hx

    -- 3. Apply Removable Singularity Theorem
    exact differentiable_of_continuous_of_differentiableOn_compl_singleton h_cont h_diff_on
  · -- EqOn
    intro s hs
    simp [g, Function.update, mem_compl_singleton_iff.mp hs]

/--
**The Riemann Zeta Function is in the Selberg Class.**
This serves as the primary test case for the definition.
-/
def riemannZeta : SelbergClass where
  a := fun n ↦ 1
  a_one := rfl
  F := _root_.riemannZeta
  l_series_eq := by
    intro s hs
    rw [← LSeries_one_eq_riemannZeta]
    all_goals aesop
  a_bound := by
    intro ε hε
    apply IsBigO.of_bound 1
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp only [norm_eq_abs, one_mul]
    norm_cast
    exact Nat.one_le_pow ε n hn
  m := 1
  entire_continuation := differentiable_mul_sub_one_riemannZeta
  finite_order := by
    -- Known growth bound for Zeta
    sorry
  Q := 1 / Real.sqrt Real.pi
  Q_pos := by
    rw [one_div]
    exact inv_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos)
  k := 1
  lambda := fun _ ↦ 1/2
  lambda_pos := fun _ ↦ by norm_num
  mu := fun _ ↦ 0
  mu_re_nonneg := by simp
  omega := 1
  omega_norm := by simp
  functional_equation := by
    -- Standard functional equation ξ(s) = ξ(1-s)
    sorry
  b := fun n ↦ if IsPrimePow n then (vonMangoldt n) / Real.log n else 0
  b_zero := by simp
  b_support := by
    intro n h
    split_ifs at h with hp
    exact hp
    contradiction
  theta := 0
  theta_lt_half := by norm_num
  b_bound := by
    intro n
    dsimp
    split_ifs with h
    · obtain ⟨p, k, hp, hk, rfl⟩ := h
      rw [vonMangoldt_apply_pow hp hk, Real.log_pow, abs_div, abs_of_nonneg (Real.log_nonneg (Nat.one_le_cast.2 (Nat.Prime.one_le hp))), abs_of_pos (Nat.cast_pos.2 hk)]
      rw [div_mul_eq_div_div, div_self (Real.log_pos (Nat.one_lt_cast.2 (Nat.Prime.one_lt hp))).ne', one_div]
      simp only [Nat.cast_pow, Real.rpow_zero, norm_eq_abs]
      apply le_trans (inv_le_one (Nat.one_le_cast.2 hk))
      simp
    · simp
  euler_product_eq := by
    -- Euler product of Zeta
    sorry

end SelbergClass
end NumberTheory.Selberg
