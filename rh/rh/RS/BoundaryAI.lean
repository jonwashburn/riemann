import rh.RS.TentShadow
import rh.academic_framework.HalfPlaneOuter
import rh.RS.BoundaryWedge

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

/-- From a half–plane Poisson representation of `F`, obtain the RS transport
predicate: boundary a.e. nonnegativity `(P+)` implies interior nonnegativity
on `Ω` for the real part of `F`. -/
theorem transport_of_rep
  (F : ℂ → ℂ)
  (hRep : RH.AcademicFramework.HalfPlaneOuter.HasHalfPlanePoissonRepresentation F) :
  HasHalfPlanePoissonTransport F := by
  intro hPPlus z hzΩ
  -- Convert membership in Ω to the real-part inequality
  have hz : z.re > (1/2 : ℝ) := by simpa [Ω, Set.mem_setOf_eq] using hzΩ
  -- Use the AF representation to transport boundary nonnegativity to the interior
  exact interior_re_nonneg_of_PPlus_and_rep (F := F) hRep hPPlus z hz

/-- Pinch specialization: from a Poisson representation of the pinch field
`F := (2 : ℂ) * J_pinch det2 O`, obtain the RS transport predicate
`HasHalfPlanePoissonTransport F`. -/
theorem transport_for_pinch_of_rep
  {det2 O : ℂ → ℂ}
  (hRep : RH.AcademicFramework.HalfPlaneOuter.HasHalfPlanePoissonRepresentation (F_pinch det2 O)) :
  HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z) := by
  -- Delegate to the generic wrapper
  exact transport_of_rep (F := F_pinch det2 O) hRep

end RS
end RH
