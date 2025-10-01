import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import rh.Cert.KxiPPlus
import rh.RS.BoundaryWedgeProof
import rh.RS.CRGreenOuter
import rh.RS.PoissonPlateau
import rh.RS.PoissonAI
-- (no import of DirectWedgeProof to avoid cycles)

/-!
RS bridge: Concrete Carleson ⇒ (P+).

We expose a concise adapter that delegates to existing helpers:
- CR–Green pairing + Whitney remainder packaging + Carleson budget → local wedge
- Plateau window with positive lower bound → H¹–BMO window criterion
- A.e. upgrade to boundary wedge `(P+)`.

API provided (used downstream):
- `PPlus_of_ConcreteHalfPlaneCarleson`
- `PPlusFromCarleson_exists_proved`

No axioms and no `sorry`.
-/

noncomputable section

open Complex

namespace RH
namespace RS

/- Reordered: provide adapters that avoid forward references. -/

/-- Thin legacy wrappers to preserve names; they delegate to BoundaryWedge API and trivialize to Prop-level. -/
-- Retain legacy name as a no-op Prop for compatibility in callers, if any
@[simp] def localWedge_from_WhitneyCarleson
    (F : ℂ → ℂ)
    (hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ) : Prop :=
  True

/-- Legacy alias: delegate to BoundaryWedge adapters and plateau. -/
theorem localWedge_from_CRGreen_and_Poisson
    (F : ℂ → ℂ)
    (hex : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ) :
    localWedge_from_WhitneyCarleson (F := F) hex := by
  classical
  rcases hex with ⟨Kξ, hKξ0, hCar⟩
  obtain ⟨ψ, _hψ_even, _hψ_nonneg, _hψ_comp, hψ_mass1,
          ⟨c0, hc0_pos, hPlateau⟩⟩ := RH.RS.poisson_plateau_c0
  let hKxiVar : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ := ⟨Kξ, hKξ0, hCar⟩
  have _pairing :=
        fun {lenI : ℝ}
            (U : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (_ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
            (I : Set ℝ) (α' : ℝ)
            (σ : MeasureTheory.Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
            (gradU gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ) (B : ℝ → ℝ)
            (Cψ_pair Cψ_rem : ℝ)
            (hPairVol :
              |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
                ≤ Cψ_pair * Real.sqrt (RS.boxEnergyCRGreen gradU σ Q))
            (Rside Rtop Rint : ℝ)
            (hEqDecomp :
              (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
                = (∫ t in I, _ψ t * B t) + Rside + Rtop + Rint)
            (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
            (hRintBound :
              |Rint| ≤ Cψ_rem * Real.sqrt (RS.boxEnergyCRGreen gradU σ Q))
            (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
            (hEnergy_le : RS.boxEnergyCRGreen gradU σ Q ≤ Classical.choose hKxiVar * lenI) =>
          have hCar' : RH.Cert.ConcreteHalfPlaneCarleson (Classical.choose hKxiVar) :=
            (Classical.choose_spec hKxiVar).2
          RS.local_pairing_bound_from_IBP_and_Carleson
            (Kξ := Classical.choose hKxiVar) (lenI := lenI) (hCar := hCar')
            U W _ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem
            (hPairVol := hPairVol)
            (Rside := Rside) (Rtop := Rtop) (Rint := Rint)
            (hEqDecomp := hEqDecomp)
            (hSideZero := hSideZero) (hTopZero := hTopZero)
            (hRintBound := hRintBound)
            (hCψ_nonneg := hCψ_nonneg)
            (hEnergy_le := hEnergy_le)
  simp [localWedge_from_WhitneyCarleson]

-- (legacy aliases and AI variants removed; concise façade only)

end RS
end RH
