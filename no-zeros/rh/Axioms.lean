import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.SchurGlobalization

/-!
This module intentionally declares no axioms. It exists as a marker that the
certificate route and analytic bounds do not rely on new axioms.

It also re-exports certain theorems proved elsewhere (e.g. in `RS`) so that
downstream modules that historically imported `Axioms` keep working without
depending on new axioms.
-/

namespace RH.Axioms

/-- Public re-export: Non-vanishing of ζ on the boundary line Re(s) = 1.
Proved in `RH.RS` via the Schur–Herglotz globalization and pinch argument. -/
theorem zeta_nonvanishing_on_Re_eq_one (z : ℂ) (hz : z.re = 1) :
    riemannZeta z ≠ 0 :=
  RH.RS.ZetaNoZerosOnRe1FromSchur z hz

@[simp]
theorem zeta_nonvanishing_on_Re_eq_one_rev (z : ℂ) (hz : (1 : ℝ) = z.re) :
    riemannZeta z ≠ 0 :=
  zeta_nonvanishing_on_Re_eq_one z hz.symm

end RH.Axioms
