/-
# Route 3: Lagarias explicit-formula functionals (concrete definitions)

This file defines the explicit-formula functionals in Lagarias' Mellin normalization
for concrete test functions `f : ℝ → ℂ` (interpreted as functions on `(0,∞)`).

- `W2(f) = M[f](1)` and `W0(f) = M[f](0)` where `M = Mathlib.Analysis.MellinTransform.mellin`.
- `W_p(f)` and `W_∞(f)` as in Lagarias §3.
- `W_arith(f) = W_∞(f) + Σ_p W_p(f)` (defined as a `tsum` over primes; convergence is an analytic issue).

We do **not** define the spectral zero-sum `W1` here (that is the genuinely hard part).
-/

import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RiemannRecognitionGeometry.ExplicitFormula.MathlibBridge

noncomputable section

namespace RiemannRecognitionGeometry
namespace ExplicitFormula

open MeasureTheory Set

/-- Concrete Mellin transform alias. -/
abbrev M (f : ℝ → ℂ) (s : ℂ) : ℂ := mellin f s

/-- `W^{(2)}(f) = M[f](1)`. -/
def W2 (f : ℝ → ℂ) : ℂ := M f 1

/-- `W^{(0)}(f) = M[f](0)`. -/
def W0 (f : ℝ → ℂ) : ℂ := M f 0

/-- The Lagarias involution `~f(x) = (1/x) f(1/x)`. -/
def tilde (f : ℝ → ℂ) : ℝ → ℂ := tildeFun f

/-- The prime-power local term `W_p(f)` (Lagarias §3), defined for any natural `p`.

For RH applications we will only use this at primes; the definition uses `Nat.Prime p` at the
`W_arith` level.

`W_p(f) = (log p) * Σ_{n≥1} ( f(p^n) + ~f(p^n) )`.
-/
def Wp (p : ℕ) (f : ℝ → ℂ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) *
    (∑' n : ℕ,
      (f ((p ^ (n + 1) : ℕ) : ℝ) + (tilde f) ((p ^ (n + 1) : ℕ) : ℝ)))

/-- The archimedean term `W_∞(f)` in Lagarias' explicit formula (Mellin normalization).

`W∞(f) = (γ + log π) f(1) + ∫_{1}^{∞} ((f(x)+~f(x) - (2/x^2) f(1)) / (x^2-1)) * x dx`.

The integral is taken over `Ioi 1` (the integrand has a removable singularity at `x=1` for nice `f`).
-/
def Winfty (f : ℝ → ℂ) : ℂ :=
  let c : ℂ := (Real.eulerMascheroniConstant + Real.log Real.pi)
  c * f 1 +
    ∫ x : ℝ in Ioi (1 : ℝ),
      (((f x + (tilde f) x - ((2 : ℝ) / (x ^ 2)) * f 1) / (x ^ 2 - 1)) * x)

/-- The full arithmetic-side functional `W_arith(f) = W_∞(f) + Σ_{p prime} W_p(f)`.

Convergence of the infinite sum is part of the analytic work; for compactly supported `f` this
reduces to a finite sum.
-/
def Warith (f : ℝ → ℂ) : ℂ :=
  Winfty f +
    ∑' p : ℕ, (if Nat.Prime p then Wp p f else 0)

end ExplicitFormula
end RiemannRecognitionGeometry
