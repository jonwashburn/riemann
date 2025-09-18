import rh.RS.TentShadow
import rh.academic_framework.HalfPlaneOuter

/-!
Thin RS-level wrappers for the boundary Poisson approximate-identity (AI)
used by the AI-based negativity selection. These wrappers let RS/CRGreenOuter
consume the AI for the concrete pinch field `F := 2 · J_pinch det2 O`
without importing AF internals directly.
-/

noncomputable section

namespace RH
namespace RS

open RH.AcademicFramework.HalfPlaneOuter

/-- RS alias: boundary Poisson AI for an arbitrary `F`. -/
abbrev BoundaryPoissonAI (F : ℂ → ℂ) : Prop :=
  RH.AcademicFramework.HalfPlaneOuter.BoundaryPoissonAI F

/-- RS alias: implication from Poisson representation to boundary AI. -/
abbrev boundaryPoissonAI_from_rep (F : ℂ → ℂ) : Prop :=
  RH.AcademicFramework.HalfPlaneOuter.boundaryPoissonAI_from_rep F

/-- Pinch field (explicit, RS-level spelling).
Note: AF also provides `F_pinch`; we keep the explicit form locally. -/
@[simp] def F_pinch (det2 O : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (2 : ℂ) * J_pinch det2 O z

/-- RS alias: boundary Poisson AI specialized to the pinch field. -/
abbrev BoundaryPoissonAI_pinch (det2 O : ℂ → ℂ) : Prop :=
  BoundaryPoissonAI (F_pinch det2 O)

/-- RS alias: AF pinch AI adapter (representation ⇒ boundary AI). -/
abbrev boundaryPoissonAI_from_rep_pinch (det2 O : ℂ → ℂ) : Prop :=
  RH.AcademicFramework.HalfPlaneOuter.boundaryPoissonAI_from_rep_Jpinch det2 O

/-- Produce the concrete AI hypothesis for the pinch field from a
half–plane Poisson representation and the AF adapter. -/
theorem AI_for_pinch_of_rep
  {det2 O : ℂ → ℂ}
  (hRep : RH.AcademicFramework.HalfPlaneOuter.HasHalfPlanePoissonRepresentation (F_pinch det2 O))
  (hImp : boundaryPoissonAI_from_rep_pinch det2 O) :
  BoundaryPoissonAI_pinch det2 O :=
by
  -- The AF adapter is an implication `HasRep → BoundaryAI`; apply it.
  exact hImp hRep

end RS
end RH
