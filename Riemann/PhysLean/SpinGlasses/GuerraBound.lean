import Riemann.PhysLean.SpinGlasses.Algebra

open MeasureTheory ProbabilityTheory Real BigOperators

namespace SpinGlass

/-!
# Guerra's bound: algebraic core (finite `N`)

The analytic part of Guerra's interpolation (differentiation under the disorder expectation,
Gaussian IBP, and endpoint evaluation) is substantial.  This file isolates the *finite‑`N`
algebraic* inequality that is the key ingredient once the derivative identity is established.

See `SpinGlasses/Defs.lean` for the underlying trace computations and for the proof that the
relevant combination is bounded by \((β^2/4)(1-q)^2\) via nonnegativity of a Gibbs average of a
square.
-/

variable {N : ℕ} {β q : ℝ}

/--
**Finite‑`N` Guerra derivative bound (algebraic part).**

This is the inequality corresponding to Talagrand's Eq. (1.65) *after* Gaussian IBP has reduced
the derivative of the interpolated expected free energy to a trace of the covariance kernels
against the Hessian.
-/
theorem guerra_derivative_bound_algebra_core (hN : 0 < N) (H : EnergySpace N) :
    let term_sk := (∑ σ, ∑ τ, sk_cov_kernel N β σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    let term_simple := (∑ σ, ∑ τ, simple_cov_kernel N β q σ τ * hessian_free_energy N H (std_basis N σ) (std_basis N τ))
    (1 / 2) * (term_sk - term_simple) ≤ (β^2 / 4) * (1 - q)^2 :=
  SpinGlass.guerra_derivative_bound_algebra (N := N) (β := β) (q := q) hN H

end SpinGlass
