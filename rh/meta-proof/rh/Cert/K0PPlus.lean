import rh.academic_framework.EulerProduct.K0Bound

noncomputable section

namespace RH.Cert

/-- Availability of the arithmetic tail nonnegativity bound `K0 ≥ 0` on closed strips. -/
def K0Available : Prop := RH.AcademicFramework.EulerProduct.K0.K0_bound_on_strip

/-- Proven availability: delegates to the arithmetic-tail lemma. -/
theorem K0Available_proved : K0Available :=
  RH.AcademicFramework.EulerProduct.K0.K0_bound_on_strip_proved

end RH.Cert
