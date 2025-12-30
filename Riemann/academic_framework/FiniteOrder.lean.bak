import Mathlib
import PrimeNumberTheoremAnd.StrongPNT
import StrongPNT

open Complex Real BigOperators Finset Classical ArithmeticFunction vonMangoldt

open scoped Topology

/-!
# Hadamard factorization for entire functions of finite order

This file sets up a general API for **Hadamard factorization** of entire functions
of finite order.  The goal is to have a reusable statement that can be applied
in analytic number theory (for example to the completed Riemann zeta function or
to L-functions in the Selberg class), while keeping the core analytic statement
independent of any arithmetic input.

Mathematically, the main ingredients are:

* A predicate `EntireOfFiniteOrder ρ f` expressing that `f : ℂ → ℂ` is entire and
	satisfies a power-type growth bound of order at most `ρ`.
* The Weierstrass elementary factors `E_m(z)` of genus `m`.
* An abstract `ZeroData f` packaging the zeros of `f` with multiplicities and a
	local finiteness condition.
* A Hadamard factorization theorem, stating that an entire function of finite
	order admits a factorization as an exponential of a polynomial times a
	canonical product built from its zeros.

At this stage we only provide the *interface* and a schematic statement of the
factorization theorem with a single `sorry` placeholder for the analytic core.
The intent is that this will be filled using the Nevanlinna / De Branges
infrastructure developed elsewhere in this project.

The API is designed with both Annals-of-Mathematics style statements and
Mathlib reuse in mind.
-/

noncomputable section

namespace ComplexAnalysis
namespace Hadamard

open Set Filter
/--
`EntireOfFiniteOrder ρ f` means: `f` is entire and of (global) order at most `ρ`.

We encode the order condition via a global bound on
`log (1 + ‖f(z)‖)` in terms of `(1 + ‖z‖)^ρ`.  This formulation is flexible
enough for Hadamard products and matches standard complex-analytic conventions.
-/
structure EntireOfFiniteOrder (ρ : ℝ) (f : ℂ → ℂ) : Prop where
/-- Entirety of `f`. -/
entire : Differentiable ℂ f
/-- Global growth bound of order at most `ρ`. -/
growth : ∃ C > 0, ∀ z : ℂ,
  Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ

namespace EntireOfFiniteOrder

variable {ρ : ℝ} {f : ℂ → ℂ}


lemma differentiable (hf : EntireOfFiniteOrder ρ f) :
  Differentiable ℂ f := hf.entire

/-- A convenient coercion lemma: from `EntireOfFiniteOrder` to an explicit norm bound. -/
lemma norm_bound (hf : EntireOfFiniteOrder ρ f) :
  ∃ C' > 0, ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C' * (1 + ‖z‖) ^ ρ) := by
  rcases hf.growth with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro z
  have hlog := hC z
  -- `log(1 + ‖f z‖) ≤ C * (1 + ‖z‖)^ρ`
  -- ⇒ `1 + ‖f z‖ ≤ exp(C * (1 + ‖z‖)^ρ)`
  have hpos : 0 < (1 : ℝ) + ‖f z‖ := by
    have : (0 : ℝ) ≤ ‖f z‖ := norm_nonneg _
    linarith
  have h1 : (1 : ℝ) + ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ ρ) := by
    rw [← Real.log_le_iff_le_exp hpos]
    exact hlog
  -- conclude `‖f z‖ ≤ exp(C * (1 + ‖z‖)^ρ)`
  have hexp_pos : 0 < Real.exp (C * (1 + ‖z‖) ^ ρ) := Real.exp_pos _
  linarith

end EntireOfFiniteOrder

/--
The Weierstrass elementary factor of genus `m`:

`E_m(z) = (1 - z) * exp(z + z^2/2 + ... + z^m/m)`.

We package it in a single definition for later use in canonical products.
-/
noncomputable
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
(1 - z) * Complex.exp
  (∑ k ∈ Finset.range m.succ, z^(k + 1) / (k + 1))

lemma weierstrassFactor_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
simp [weierstrassFactor]

/-- Helper: difference of constant and identity is differentiable. -/
lemma differentiable_one_sub_id : Differentiable ℂ (fun z : ℂ => (1 : ℂ) - z) :=
  Differentiable.sub (differentiable_const 1) differentiable_id

/-- Helper: finite sum of differentiable functions is differentiable. -/
lemma differentiable_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℂ (f i)) :
    Differentiable ℂ (fun z => ∑ i ∈ s, f i z) := Differentiable.fun_sum hf

lemma differentiable_weierstrassFactor (m : ℕ) :
  Differentiable ℂ (weierstrassFactor m) := by
  -- `z ↦ 1 - z` is differentiable
  have h₁ : Differentiable ℂ (fun z : ℂ => (1 : ℂ) - z) := differentiable_one_sub_id
  -- `z ↦ ∑ k ∈ range (m+1), z^(k+1) / (k+1)` is a finite sum of monomials,
  -- hence differentiable
  have h₂ :
      Differentiable ℂ
        (fun z : ℂ =>
          ∑ k ∈ Finset.range m.succ, z ^ (k + 1) / (k + 1)) := by
    apply differentiable_finset_sum
    intro k _
    -- coefficient `1 / (k+1)` times `z^(k+1)`
    exact (differentiable_id.pow _).div_const _
  -- compose with `Complex.exp`
  have h₃ :
      Differentiable ℂ
        (fun z : ℂ =>
          Complex.exp
            (∑ k ∈ Finset.range m.succ, z ^ (k + 1) / (k + 1))) :=
    Complex.differentiable_exp.comp h₂
  -- product of differentiable functions
  exact h₁.mul h₃
