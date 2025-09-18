import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Liouville
import rh.RS.SchurGlobalization

namespace RH.AcademicFramework.EPM

/-!
Euler product and zeta wrappers (mathlib-backed).
-/

open Complex
open scoped BigOperators

/-- Euler product: for Re(s) > 1, ζ(s) equals the product over primes. -/
theorem euler_product_wrapper
    (s : ℂ) (hs : 1 < s.re) :
    riemannZeta s = ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  -- Use mathlib's `riemannZeta_eulerProduct_tprod` and flip the equality.
  simpa [eq_comm] using (riemannZeta_eulerProduct_tprod (s := s) hs)

/-- Nonvanishing: for Re(s) > 1, ζ(s) ≠ 0. -/
theorem zeta_nonzero_re_gt_one
    {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 := by
  simpa using riemannZeta_ne_zero_of_one_lt_re hs

/-- Boundary-line nonvanishing on `Re = 1`, delegated to the RS export.

Given an RS boundary bridge `B : RH.RS.ZetaSchurBoundaryBridge`, this theorem
states `riemannZeta z ≠ 0` for any complex `z` with `z.re = 1`, by invoking
`RH.RS.ZetaNoZerosOnRe1FromSchur`.

Callers are expected to provide the RS-side bridge bundling the pinch data. -/
theorem zeta_nonzero_re_eq_one
    (z : ℂ) (hz : z.re = 1) (B : RH.RS.ZetaSchurBoundaryBridge) :
    riemannZeta z ≠ 0 :=
  RH.RS.ZetaNoZerosOnRe1FromSchur B z hz

/-- Prop-level hook mirroring the intended RS export; callers can depend on this
statement-shaped wrapper until the RS proof is provided. -/
def zeta_nonzero_re_eq_one_statement
    (z : ℂ) (hz : z.re = 1) (w : RH.RS.ZetaSchurDecomposition) : Prop :=
  RH.RS.ZetaNoZerosOnRe1FromSchur_Statement z hz w

/-! Boundary-line nonvanishing via the RS boundary bridge (once the ζ→Θ/N
bridge provides local pinch data for each boundary point). -/

/-- If an RS boundary bridge is available, ζ has no zeros on `Re = 1`. -/
theorem zeta_nonzero_re_eq_one_from_bridge
    (z : ℂ) (hz : z.re = 1) (B : RH.RS.ZetaSchurBoundaryBridge) :
    riemannZeta z ≠ 0 :=
  zeta_nonzero_re_eq_one z hz B

/-- If an RS off-zeros boundary assignment is available, ζ has no zeros on `Re = 1`. -/
theorem zeta_nonzero_re_eq_one_from_offZerosAssignment
    (z : ℂ) (hz : z.re = 1) (A : RH.RS.OffZerosBoundaryAssignment) :
    riemannZeta z ≠ 0 :=
by
  have h := RH.RS.ZetaNoZerosOnRe1_from_offZerosAssignment A
  exact h z hz

/-- If the Prop-level RS bridge holds, ζ has no zeros on `Re = 1`. -/
theorem zeta_nonzero_re_eq_one_from_bridgeStatement
    (z : ℂ) (hz : z.re = 1)
    (h : RH.RS.ZetaSchurBridgeStatement) :
    riemannZeta z ≠ 0 :=
  RH.RS.ZetaNoZerosOnRe1FromSchur_from_bridgeStatement h z hz

/-- Statement-level wrapper mirroring the RS export, from a boundary bridge. -/
theorem zeta_nonzero_re_eq_one_statement_from_bridge
    (z : ℂ) (hz : z.re = 1) (B : RH.RS.ZetaSchurBoundaryBridge) :
    RH.RS.ZetaNoZerosOnRe1FromSchur_Statement z hz B.w :=
  RH.RS.ZetaNoZerosOnRe1FromSchur_Statement_from_bridge B z hz

-- Note: boundary-line nonvanishing is delegated to the RS layer when needed.
-- We intentionally do not duplicate it here to keep this module mathlib-only.

/-- If the RS off-zeros boundary hypothesis holds for Θ,N, then ζ has no zeros on Re = 1. -/
theorem zeta_nonzero_re_eq_one_from_offZerosAssignmentStatement
    {Θ N : ℂ → ℂ}
    (h : RH.RS.OffZerosBoundaryHypothesis Θ N)
    (z : ℂ) (hz : z.re = 1) :
    riemannZeta z ≠ 0 :=
  RH.RS.ZetaNoZerosOnRe1_from_offZerosAssignmentStatement h z hz

/-- Trivial zeros: ζ vanishes at negative even integers. -/
theorem zeta_trivial_zero_neg_two_mul_nat_add_one (n : ℕ) :
    riemannZeta (-2 * (n + 1)) = 0 := by
  simpa using riemannZeta_neg_two_mul_nat_add_one n

end RH.AcademicFramework.EPM
