import rh.academic_framework.FredholmInfrastructure
import rh.academic_framework.EulerProduct.OperatorView
import rh.academic_framework.EulerProductMathlib
import rh.academic_framework.Common
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Euler Product Connection

This file connects the Euler product representation with the Fredholm determinant.

## Main results

* `euler_product_eq_zeta` - The Euler product equals the Riemann zeta function
* `fredholm_det_eq_zeta_inv` - The Fredholm determinant equals 1/ζ(s)
-/

namespace AcademicRH.EulerProductConnection

open Complex Real BigOperators
open AcademicRH.FredholmInfrastructure AcademicRH.EulerProduct

/-- The Euler product equals the Riemann zeta function for Re(s) > 1 -/
theorem euler_product_eq_zeta {s : ℂ} (hs : 1 < s.re) :
  ∏' p : PrimeIndex, (1 - (p.val : ℂ)^(-s))⁻¹ = riemannZeta s := by
  sorry

/-- The Fredholm determinant equals 1/ζ(s) for Re(s) > 1 -/
theorem fredholm_det_eq_zeta_inv {s : ℂ} (hs : 1 < s.re) :
  fredholm_det (1 - euler_operator s hs) = (riemannZeta s)⁻¹ := by
  sorry

/-- The regularized Fredholm determinant formula -/
theorem fredholm_det2_eq_product {s : ℂ} (hs : 1 < s.re) :
  RH.fredholm_det2 s = ∏' p : {p : ℕ // Nat.Prime p}, (1 - (p.val : ℂ)^(-s)) * Complex.exp ((p.val : ℂ)^(-s)) := by
  sorry

/-- Connection between operator determinant and zeta function -/
theorem operator_det_zeta_connection {s : ℂ} (hs : 0 < s.re ∧ s.re < 1) :
  fredholm_det (1 - euler_operator_strip s hs) = (riemannZeta s)⁻¹ := by
  sorry

end AcademicRH.EulerProductConnection
