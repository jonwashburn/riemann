import rh.Cert.KxiPPlus
import rh.Cert.K0PPlus
import rh.academic_framework.EulerProduct.K0Bound
import rh.Cert.FactorsWitness

noncomputable section

namespace RH.AcademicFramework.Certificate

/-! Certificate capabilities availability flags -/

/-- Availability of the Kξ track via existence of a closed-strip
functional-equation factors witness. Downstream consumers only need
existence of a witness; numeric instantiation can be refined separately. -/
def KxiAvailable : Prop := Nonempty RH.Cert.FunctionalEquationStripFactors

/-- Availability of the arithmetic tail nonnegativity `K0 ≥ 0` from the proved lemma. -/
def K0Available : Prop := RH.AcademicFramework.EulerProduct.K0.K0_bound_on_strip

/-- Proven availability: delegates to the arithmetic-tail lemma. -/
theorem K0Available_proved : K0Available :=
  RH.AcademicFramework.EulerProduct.K0.K0_bound_on_strip_proved

/-- Readiness flag for certificate chain hooks: depends on availability of
both Kξ and K0 tracks. -/
def Ready : Prop :=
  KxiAvailable ∧ K0Available

/-- From a functional-equation closed-strip factors witness, we get
`KxiAvailable` via the existential `∃ Kξ, KxiBound Kξ`. -/
theorem KxiAvailable_of_factors
    (h : Nonempty RH.Cert.FunctionalEquationStripFactors) :
    KxiAvailable := h

/-- If `K0Available` holds and a factors witness exists, the certificate
track is ready (modulo the `CertificateReady` flag exposed by `rh/Cert`). -/
theorem Ready_of_factors
    (hK0 : K0Available)
    (hfac : Nonempty RH.Cert.FunctionalEquationStripFactors) : Ready := by
  refine And.intro ?hKxi hK0
  exact KxiAvailable_of_factors hfac

/-- Unconditional readiness: combine arithmetic-tail availability with the
concrete closed-strip factors witness built from the uniform H′ bound. -/
theorem Ready_unconditional : Ready :=
  Ready_of_factors K0Available_proved RH.Cert.factors_witness_nonempty

end RH.AcademicFramework.Certificate
