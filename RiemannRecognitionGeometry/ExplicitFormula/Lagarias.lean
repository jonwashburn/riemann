/-
# Lagarias (2007): explicit formula and Weil positivity (Route 3 skeleton)

This file encodes the *statements* (as Lean-typed axioms/structures) of:
- Lagarias Thm 3.1 (Guinand–Weil explicit formula), and
- Lagarias Thm 3.2 (Weil positivity criterion for RH),

in the Mellin-transform normalization used in `renormalized_tail_bound.md` §8.

No Carleson/BMO/Whitney infrastructure is imported here.
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannRecognitionGeometry.ExplicitFormula.Defs

noncomputable section

open Complex

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open TestSpace

/-- Lagarias' completed zeta in the normalization
`ξ(s) = (1/2) s (s-1) π^{-s/2} Γ(s/2) ζ(s)`.

We define it using Mathlib's `completedRiemannZeta`:
`completedRiemannZeta s = π^{-s/2} Γ(s/2) ζ(s)` (up to harmless point-value conventions
at `s=0,1`). The prefactor `s(s-1)` removes the poles and yields an entire function.
-/
def xiLagarias (s : ℂ) : ℂ := (1/2 : ℂ) * s * (s - 1) * completedRiemannZeta s

lemma xiLagarias_one_sub (s : ℂ) : xiLagarias (1 - s) = xiLagarias s := by
  unfold xiLagarias
  -- First apply the functional equation to the completed zeta factor.
  rw [completedRiemannZeta_one_sub s]
  -- The remaining equality is just commutative-ring algebra in `s`.
  ring_nf

lemma deriv_xiLagarias_one_sub (s : ℂ) : deriv xiLagarias (1 - s) = - deriv xiLagarias s := by
  -- Differentiate the functional equation `xiLagarias (1 - z) = xiLagarias z`.
  have hfun : (fun z : ℂ => xiLagarias (1 - z)) = xiLagarias := by
    funext z
    simpa using xiLagarias_one_sub z
  -- Use `deriv_comp_const_sub` to compute the derivative of the left side.
  have hcomp :
      deriv (fun z : ℂ => xiLagarias (1 - z)) s = - deriv xiLagarias (1 - s) := by
    -- `1 - z` is `1 - z` (a const-sub), so this is exactly `deriv_comp_const_sub`.
    simpa [sub_eq_add_neg] using (deriv_comp_const_sub (f := xiLagarias) (a := (1 : ℂ)) (x := s))
  -- Rewrite using `hfun` and rearrange.
  have : deriv xiLagarias s = - deriv xiLagarias (1 - s) := by
    simpa [hfun] using hcomp
  -- Flip sides by negating the equality.
  have hneg : -deriv xiLagarias s = deriv xiLagarias (1 - s) := by
    simpa using congrArg (fun z : ℂ => -z) this
  simpa using hneg.symm

lemma logDeriv_xiLagarias_one_sub (s : ℂ) : logDeriv xiLagarias (1 - s) = - logDeriv xiLagarias s := by
  -- Expand `logDeriv` and rewrite using the functional equation and the derivative identity.
  -- Then it is just the algebraic identity `(-a)/b = -(a/b)`.
  simp [logDeriv, deriv_xiLagarias_one_sub, xiLagarias_one_sub, neg_div]

/-- The functional-equation log-derivative identity specialized to vertical-line points `c - it`. -/
lemma logDeriv_xiLagarias_leftEdge (c t : ℝ) :
    logDeriv xiLagarias (((1 - c : ℝ) : ℂ) + (t : ℂ) * I) =
      - logDeriv xiLagarias ((c : ℂ) + ((-t : ℝ) : ℂ) * I) := by
  -- Apply `logDeriv_xiLagarias_one_sub` to `s = c - it` and simplify `1 - (c - it)`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
    (logDeriv_xiLagarias_one_sub (s := (c : ℂ) + ((-t : ℝ) : ℂ) * I))

/-!
## Zeros: relating `xiLagarias` and `riemannZeta` (basic correspondence lemmas)

These lemmas are not the Route 3 bottleneck; they are routine “interface glue”
needed to connect Lagarias-style statements (formulated in terms of `ξ`) with
Mathlib's `RiemannHypothesis` predicate (formulated in terms of `ζ`).

We keep hypotheses explicit to avoid sweeping analytic subtleties under the rug.
-/

lemma completedRiemannZeta_eq_zero_of_riemannZeta_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hsre : 0 < s.re) (hz : riemannZeta s = 0) :
    completedRiemannZeta s = 0 := by
  have hΓ : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hdef := riemannZeta_def_of_ne_zero (s := s) hs0
  have hdiv : completedRiemannZeta s / Complex.Gammaℝ s = 0 := by
    simpa [hdef] using hz
  rcases (div_eq_zero_iff).1 hdiv with hcomp | hΓ0
  · exact hcomp
  · exact False.elim (hΓ hΓ0)

lemma xiLagarias_eq_zero_of_riemannZeta_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hsre : 0 < s.re) (hz : riemannZeta s = 0) :
    xiLagarias s = 0 := by
  have hcomp : completedRiemannZeta s = 0 :=
    completedRiemannZeta_eq_zero_of_riemannZeta_eq_zero (s := s) hs0 hsre hz
  unfold xiLagarias
  simp [hcomp]

lemma riemannZeta_eq_zero_of_xiLagarias_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsre : 0 < s.re) (hxi : xiLagarias s = 0) :
    riemannZeta s = 0 := by
  have hΓ : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hdef := riemannZeta_def_of_ne_zero (s := s) hs0
  have hpref : ((1/2 : ℂ) * s * (s - 1)) ≠ 0 := by
    have hhalf : (1/2 : ℂ) ≠ 0 := by norm_num
    have hsMinus1 : s - 1 ≠ 0 := by
      intro h
      apply hs1
      exact sub_eq_zero.mp h
    have h1 : (1/2 : ℂ) * s ≠ 0 := mul_ne_zero hhalf hs0
    have h2 : ((1/2 : ℂ) * s) * (s - 1) ≠ 0 := mul_ne_zero h1 hsMinus1
    simpa [mul_assoc] using h2
  -- Extract `completedRiemannZeta s = 0` from `xiLagarias s = 0`.
  have hcomp : completedRiemannZeta s = 0 := by
    unfold xiLagarias at hxi
    -- reassociate to isolate the `completedRiemannZeta` factor
    have hxi' : ((1/2 : ℂ) * s * (s - 1)) * completedRiemannZeta s = 0 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hxi
    rcases mul_eq_zero.mp hxi' with hpre0 | hcomp0
    · exact False.elim (hpref hpre0)
    · exact hcomp0
  -- Now use `ζ = Λ / Γ` (Mathlib's interface) and the nonvanishing of `Γ`.
  rw [hdef]
  simp [hcomp]

/--
A packaged set of explicit-formula functionals in Lagarias' Mellin normalization.

`W0(f) = M[f](0)`, `W2(f) = M[f](1)`, and `W1(f) = ∑_ρ M[f](ρ)` (symmetric summation).
We keep `W1` and `Warith` abstract, since their analytic definition/convergence
is part of the Route 3 bottleneck.
-/
structure LagariasFramework (F : Type) [TestSpace F] where
  /-- The spectral zero-sum functional `W^{(1)}(f) = ∑_ρ M[f](ρ)` (symmetric summation). -/
  W1 : F → ℂ
  /-- The arithmetic-side functional `W_arith(f) = W_∞(f) + ∑_p W_p(f)`. -/
  Warith : F → ℂ

  /-- Lagarias Thm 3.1 (Explicit Formula): `W_spec(f) = W_arith(f)` for all nice `f`. -/
  explicitFormula : ∀ f : F, M[f](1) - W1 f + M[f](0) = Warith f

  /-- Lagarias Thm 3.2 (Weil positivity): `RH ↔ (∀f, Re(W1(f*~\bar f)) ≥ 0)`. -/
  weilPositivity :
      RiemannHypothesis ↔ (∀ f : F, 0 ≤ (W1 (TestSpace.quad (F:=F) f)).re)

/-- `W^{(2)}(f) = M[f](1)` (spectral boundary term). -/
def W2 {F : Type} [TestSpace F] (f : F) : ℂ := M[f](1)

/-- `W^{(0)}(f) = M[f](0)` (spectral boundary term). -/
def W0 {F : Type} [TestSpace F] (f : F) : ℂ := M[f](0)

/-- `W_spec(f) = W2(f) - W1(f) + W0(f)` (Lagarias). -/
def Wspec {F : Type} [TestSpace F] (f : F) (L : LagariasFramework F) : ℂ :=
  W2 f - L.W1 f + W0 f

-- Convenience projection: view `Wspec` as a function once `L` is fixed.
namespace LagariasFramework

variable {F : Type} [TestSpace F] (L : LagariasFramework F)

/-- `W_spec` as a unary functional for a fixed framework. -/
def Wspec (f : F) : ℂ :=
  (W2 f) - (L.W1 f) + (W0 f)

/-- `WeilGate`: the explicit-formula positivity hypothesis (the Route 3 bottleneck). -/
def WeilGate : Prop := ∀ f : F, 0 ≤ (L.W1 (TestSpace.quad (F:=F) f)).re

end LagariasFramework

-- Provide the `Wspec` used in the structure field above.
-- (We keep it outside the structure to avoid dependent recursion issues.)
@[simp] lemma Wspec_eq (F : Type) [TestSpace F] (L : LagariasFramework F) (f : F) :
    (LagariasFramework.Wspec (F:=F) L f) = W2 f - L.W1 f + W0 f := rfl

end ExplicitFormula
end RiemannRecognitionGeometry
