import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import rh.RS.WhitneyGeometryDefs
import rh.RS.CRGreenOuter
import rh.Cert.KxiPPlus
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Boundary wedge assembly (concise adapter)

This module exposes a small, stable API used by the glue code. It avoids heavy
measure-theoretic derivations and only packages already-available bounds.
-/

noncomputable section
open Classical MeasureTheory
open scoped MeasureTheory BigOperators

namespace RH
namespace RS

/-- Alias: pass through a provided overlap-to-length bound. -/
lemma sum_shadowLen_le_of_indicator_bound
  {ι : Type*} (S : Finset ι) (Q : ι → Set (ℝ × ℝ)) (I : Set ℝ) (C : ℝ)
  (hOverlap : (∑ i in S, Whitney.shadowLen (Q i)) ≤ C * Whitney.length I) :
  (∑ i in S, Whitney.shadowLen (Q i)) ≤ C * Whitney.length I := hOverlap

/-- Aggregate local Carleson bounds using an overlap bound on `∑ℓ`.
If each `E i ≤ Kξ·ℓ i` and `∑ℓ ≤ C·|I|`, then `∑E ≤ Kξ·C·|I|`. -/
lemma sum_energy_from_carleson_and_indicator_overlap
  {ι : Type*} (S : Finset ι)
  (E : ι → ℝ) (Q : ι → Set (ℝ × ℝ)) (I : Set ℝ)
  (Kξ C : ℝ)
  (hOverlap : (∑ i in S, Whitney.shadowLen (Q i)) ≤ C * Whitney.length I)
  (hCar_local : ∀ i ∈ S, E i ≤ Kξ * Whitney.shadowLen (Q i))
  (hKξ_nonneg : 0 ≤ Kξ) (hC_nonneg : 0 ≤ C) :
  (∑ i in S, E i) ≤ Kξ * C * Whitney.length I := by
  classical
  -- Sum local Carleson
  have hE_sum : (∑ i in S, E i) ≤ (∑ i in S, Kξ * Whitney.shadowLen (Q i)) :=
    Finset.sum_le_sum (by intro i hi; simpa using hCar_local i hi)
  -- Factor constants and use overlap
  have : (∑ i in S, Kξ * Whitney.shadowLen (Q i)) =
      Kξ * (∑ i in S, Whitney.shadowLen (Q i)) := by
    simpa using (Finset.mul_sum (s := S) (f := fun i => Whitney.shadowLen (Q i)) (a := Kξ)).symm
  have hbound : Kξ * (∑ i in S, Whitney.shadowLen (Q i)) ≤ Kξ * (C * Whitney.length I) :=
    mul_le_mul_of_nonneg_left hOverlap hKξ_nonneg
  have : (∑ i in S, Kξ * Whitney.shadowLen (Q i)) ≤ Kξ * C * Whitney.length I := by
    simpa [this, mul_left_comm, mul_comm, mul_assoc]
      using hbound
  exact le_trans hE_sum this

/-- Adapter: combine CR–Green analytic pairing/remainder with a Carleson budget. -/
@[simp] theorem local_pairing_bound_from_Carleson_budget
  {Kξ lenI : ℝ}
  (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (α' : ℝ)
  (σ : MeasureTheory.Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (RH.RS.boxEnergyCRGreen gradU σ Q))
  (hRemBound :
    |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ) - (∫ t in I, ψ t * B t)|
      ≤ Cψ_rem * Real.sqrt (RH.RS.boxEnergyCRGreen gradU σ Q))
  (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
  (hEnergy_le : RH.RS.boxEnergyCRGreen gradU σ Q ≤ Kξ * lenI)
  : |∫ t in I, ψ t * B t| ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) := by
  classical
  have hCarlSqrt :
      Real.sqrt (RH.RS.boxEnergyCRGreen gradU σ Q) ≤ Real.sqrt (Kξ * lenI) :=
    Real.sqrt_le_sqrt hEnergy_le
  exact
    (le_trans
      (RH.RS.pairing_whitney_analytic_bound
        U W ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem hPairVol hRemBound)
      (mul_le_mul_of_nonneg_left hCarlSqrt hCψ_nonneg))

/-- Wiring adapter (IBP route). -/
@[simp] theorem local_pairing_bound_from_IBP_and_Carleson
  {Kξ lenI : ℝ}
  (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (α' : ℝ)
  (σ : MeasureTheory.Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (RH.RS.boxEnergyCRGreen gradU σ Q))
  (Rside Rtop Rint : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (RH.RS.boxEnergyCRGreen gradU σ Q))
  (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
  (hEnergy_le : RH.RS.boxEnergyCRGreen gradU σ Q ≤ Kξ * lenI)
  : |∫ t in I, ψ t * B t| ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) := by
  classical
  have hAnalytic := RH.RS.CRGreen_pairing_whitney_from_green_trace
    U W ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem hPairVol Rside Rtop Rint hEqDecomp hSideZero hTopZero hRintBound
  have hCarlSqrt :
      Real.sqrt (RH.RS.boxEnergyCRGreen gradU σ Q) ≤ Real.sqrt (Kξ * lenI) :=
    Real.sqrt_le_sqrt hEnergy_le
  exact (le_trans hAnalytic (mul_le_mul_of_nonneg_left hCarlSqrt hCψ_nonneg))

/-- Wiring adapter (IBP + a.e. side/top vanish). -/
@[simp] theorem local_pairing_bound_from_IBP_aeZero_and_Carleson
  {Kξ lenI : ℝ}
  (hCar : RH.Cert.ConcreteHalfPlaneCarleson Kξ)
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (α' : ℝ)
  (σ : MeasureTheory.Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (RH.RS.boxEnergyCRGreen gradU σ Q))
  (μ_side μ_top : MeasureTheory.Measure (ℝ × ℝ)) (F_side F_top : (ℝ × ℝ) → ℝ)
  (Rside Rtop Rint : ℝ)
  (hSideDef : Rside = ∫ x, (χ x) * (F_side x) ∂μ_side)
  (hTopDef  : Rtop  = ∫ x, (χ x) * (F_top x)  ∂μ_top)
  (hSideAE  : (fun x => χ x) =ᵐ[μ_side] 0)
  (hTopAE   : (fun x => χ x) =ᵐ[μ_top] 0)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (RH.RS.boxEnergyCRGreen gradU σ Q))
  (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
  (hEnergy_le : RH.RS.boxEnergyCRGreen gradU σ Q ≤ Kξ * lenI)
  : |∫ t in I, ψ t * B t| ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) := by
  classical
  -- a.e. vanish ⇒ side/top integrals vanish
  have hZero := RH.RS.side_top_zero_from_ae_zero μ_side μ_top F_side F_top (fun x => χ x) Rside Rtop hSideDef hTopDef hSideAE hTopAE
  have hSideZero : Rside = 0 := hZero.1
  have hTopZero  : Rtop  = 0 := hZero.2
  -- Use the IBP adapter with explicit zeros
  have hEqDecomp' : (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + 0 + 0 + Rint := by
    simpa [hSideZero, hTopZero, add_comm, add_left_comm, add_assoc] using hEqDecomp
  exact local_pairing_bound_from_IBP_and_Carleson hCar U W ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem
    hPairVol 0 0 Rint hEqDecomp' (by simp) (by simp) hRintBound hCψ_nonneg hEnergy_le

end RS
end RH
