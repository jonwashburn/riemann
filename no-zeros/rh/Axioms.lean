import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.RS.SchurGlobalization
import rh.RS.CertificateConstruction

/-!
This module intentionally declares no axioms. It exists as a marker that the
certificate route and analytic bounds do not rely on new axioms.

It also re-exports certain theorems proved elsewhere (e.g. in `RS`) so that
downstream modules that historically imported `Axioms` keep working without
depending on new axioms.
-/

namespace RH.Axioms

/-- Non-vanishing of ζ on the boundary line Re(s) = 1,
derived from the unconditional RH proven in `CertificateConstruction`. -/
theorem zeta_nonvanishing_on_Re_eq_one (z : ℂ) (hz : z.re = 1) :
    riemannZeta z ≠ 0 := by
  -- Unconditional RH
  have RH : RiemannHypothesis := RH.RS.CertificateConstruction.RiemannHypothesis_unconditional
  intro hζ
  have hσ : z.re = (1/2 : ℝ) := RH z hζ
  have : (1/2 : ℝ) = 1 := by simpa [hσ] using hz
  exact (by norm_num : (1/2 : ℝ) ≠ 1) this

@[simp]
theorem zeta_nonvanishing_on_Re_eq_one_rev (z : ℂ) (hz : (1 : ℝ) = z.re) :
    riemannZeta z ≠ 0 :=
  zeta_nonvanishing_on_Re_eq_one z hz.symm

end RH.Axioms
