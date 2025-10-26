import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Jacobi theta modularity via Poisson summation

We define the Jacobi theta function on the positive reals by
`θ(t) = ∑' (n : ℤ), Real.exp (-π * t * (n : ℝ)^2)` and prove the
modularity relation `θ(t) = t^(-1/2) * θ(1/t)` for `t > 0`.

Proof sketch: this is a direct application of the Gaussian Poisson
summation identity available in mathlib as
`Real.tsum_exp_neg_mul_int_sq (ha : 0 < a)` which states
`∑ exp(-π a n^2) = 1 / a^(1/2) * ∑ exp(-π / a n^2)` for `a > 0`.
Taking `a = t` yields the claim, using `one_div` and `Real.rpow_neg_one`.
-/

noncomputable section

namespace RH.AcademicFramework

open scoped Real BigOperators

namespace Theta

/-- Jacobi theta function `θ(t) = ∑_{n∈ℤ} e^{-π t n^2}` for `t > 0`. -/
def theta (t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2)

lemma theta_def (t : ℝ) :
    theta t = ∑' n : ℤ, Real.exp (-Real.pi * t * (n : ℝ) ^ 2) := rfl

/-- Modularity of the Jacobi theta function: `θ(t) = t^(-1/2) θ(1/t)` for `t>0`.

This is `Real.tsum_exp_neg_mul_int_sq` rewritten to match the usual form. -/
theorem theta_modularity {t : ℝ} (ht : 0 < t) :
    theta t = t ^ (-(1 : ℝ) / 2) * theta (t⁻¹) := by
  -- Direct `simpa` from the Gaussian Poisson summation identity.
  simpa [ theta
        , (by simpa [one_div] using Real.rpow_neg (show 0 ≤ t from ht.le) (1 / 2 : ℝ))
        , div_eq_mul_inv
        , mul_comm, mul_left_comm, mul_assoc
        ] using (Real.tsum_exp_neg_mul_int_sq ht)

end Theta

-- Re-export the main theorem at the `RH.AcademicFramework` namespace level.
export Theta (theta_modularity)

end RH.AcademicFramework
