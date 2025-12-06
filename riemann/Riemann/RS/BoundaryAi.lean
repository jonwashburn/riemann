-- TentShadow gated to reduce build surface; BoundaryWedge provides needed glue
import Riemann.RS.HalfPlaneOuterV2
--import Riemann.RS.BoundaryWedgeProof
import Riemann.RS.Cayley
--import Riemann.RS.Domain

/-!
Thin RS-level wrappers for the boundary Poisson approximate-identity (AI)
used by the AI-based negativity selection. These wrappers let RS/CRGreenOuter
consume the AI for the concrete pinch field `F := 2 · J_pinch det2 O`
without importing AF internals directly.
-/

noncomputable section

namespace RH
namespace RS

open RH.AcademicFramework.HalfPlaneOuterV2

/-- RS alias: boundary Poisson AI for an arbitrary `F`. -/
abbrev BoundaryAI (F : ℂ → ℂ) : Prop :=
  RH.AcademicFramework.HalfPlaneOuterV2.BoundaryAI F

/-- RS alias: implication from Poisson representation to boundary AI. -/
abbrev boundaryAI_from_poissonRep (F : ℂ → ℂ) : Prop :=
  RH.AcademicFramework.HalfPlaneOuterV2.boundaryAI_from_poissonRep F

/-- RS transport predicate: boundary `(P+)` implies interior nonnegativity of `Re F` on `Ω`. -/
def HasHalfPlanePoissonTransport (F : ℂ → ℂ) : Prop :=
  RH.AcademicFramework.HalfPlaneOuterV2.BoundaryPositive F →
    ∀ z ∈ RH.RS.Ω, 0 ≤ (F z).re

/-- RS alias: boundary Poisson AI specialized to the pinch field. -/
abbrev BoundaryAI_pinch (det2 O : ℂ → ℂ) : Prop :=
  BoundaryAI (RH.RS.F_pinch det2 O)

/-- RS alias: AF pinch AI adapter (representation ⇒ boundary AI). -/
abbrev boundaryAI_from_poissonRep_pinch (det2 O : ℂ → ℂ) : Prop :=
  RH.AcademicFramework.HalfPlaneOuterV2.boundaryAI_from_poissonRep
    (F := RH.RS.F_pinch det2 O)

/-- Produce the concrete AI hypothesis for the pinch field from a
half–plane Poisson representation and the AF adapter. -/
theorem AI_for_pinch_of_rep
  {det2 O : ℂ → ℂ}
  (hRep : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRep (RH.RS.F_pinch det2 O))
  (hImp : boundaryAI_from_poissonRep_pinch det2 O) :
  BoundaryAI_pinch det2 O :=
by
  -- The AF adapter is an implication `HasRep → BoundaryAI`; apply it.
  exact hImp hRep

/-- From a half–plane Poisson representation of `F`, obtain the RS transport
predicate: boundary a.e. nonnegativity `(P+)` implies interior nonnegativity
on `Ω` for the real part of `F`. -/
theorem transport_of_rep
  (F : ℂ → ℂ)
  (hRep : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRep F) :
  HasHalfPlanePoissonTransport F := by
  intro hPPlus z hzΩ_RS
  -- Convert membership in RS.Ω to AF.Ω
  have hzΩ_AF : z ∈ RH.AcademicFramework.HalfPlaneOuterV2.Ω := by
    simpa [RH.RS.Ω, RH.AcademicFramework.HalfPlaneOuterV2.Ω, Set.mem_setOf_eq]
      using hzΩ_RS
  -- Use the AF transport to obtain interior nonnegativity
  exact RH.AcademicFramework.HalfPlaneOuterV2.poissonTransport (F := F) hRep hPPlus z hzΩ_AF

/-- Pinch specialization: from a Poisson representation of the pinch field
`F := (2 : ℂ) * J_pinch det2 O`, obtain the RS transport predicate
`HasHalfPlanePoissonTransport F`. -/
theorem transport_for_pinch_of_rep
  {det2 O : ℂ → ℂ}
  (hRep : RH.AcademicFramework.HalfPlaneOuterV2.HasPoissonRep (RH.RS.F_pinch det2 O)) :
  HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z) := by
  -- Delegate to the generic wrapper
  exact transport_of_rep (F := RH.RS.F_pinch det2 O) hRep

end RS
end RH
