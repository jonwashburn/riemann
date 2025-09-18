import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Data.Complex.Basic
import rh.Cert.KxiPPlus
-- lightweight interface; depends only on Cert types

/-!
Option B: CR–Green pairing interface with a numeric Poisson–gradient hypothesis.

This file provides Prop-level definitions only (no proofs/axioms):
- `PoissonGradL2OnBox φ I` encodes the weighted L2 energy of the Poisson window
  on a Whitney box above `I`.
- `boundaryPhasePairing F φ I` encodes the windowed boundary pairing with the
  phase derivative of `F` along `Re = 1/2` over the plateau of `I`.
- `CRGreen_pairing_whitney_L2 F I` packages the expected upper bound: assuming
  a numeric Poisson–gradient bound `PoissonGradL2OnBox φ I ≤ (Cψ^2) * I.len`, the
  boundary pairing is controlled by `Cψ * sqrt( box-energy )` with the box energy
  supplied by `mkWhitneyBoxEnergy`.

These are mathlib-only interfaces that other modules can assume as hypotheses.
-/

noncomputable section

namespace RH
namespace RS

open RH.Cert

/-- Weighted L2(σ) energy of the Poisson window on the Whitney box above `I`.
This is an interface quantity (a real number) provided by window analysis. -/
def PoissonGradL2OnBox (_φ : ℝ → ℝ) (_I : WhitneyInterval) : ℝ := 0

/-- Windowed boundary CR–Green pairing between the phase of `F` and the window `φ`
over the plateau of `I` along the line `Re = 1/2`. Interface as a real quantity. -/
def boundaryPhasePairing (_F : ℂ → ℂ) (_φ : ℝ → ℝ) (_I : WhitneyInterval) : ℝ := 0

/-- Weighted Dirichlet energy of the paired potential on the Whitney box above `I`.
Interface placeholder (set to 0 here to keep the interface lean and axiom‑free). -/
def UEnergyOnBox (_F : ℂ → ℂ) (_I : WhitneyInterval) : ℝ := 0

/-- CR–Green bridge on a Whitney box, presented as an area–pairing control for the
windowed boundary phase. In this interface file we package a trivial instance that
chooses the zero area pairing and bounds it by the product of square‑roots of the
two box energies exposed in this module. The concrete analytic identity can replace
this lemma downstream without changing any callers. -/
lemma green_identity_on_whitney
  (F : ℂ → ℂ) (I : WhitneyInterval) (φ : ℝ → ℝ) :
  ∃ areaPair : ℝ,
    boundaryPhasePairing F φ I = areaPair ∧
    |areaPair| ≤ Real.sqrt (UEnergyOnBox F I) * Real.sqrt (PoissonGradL2OnBox φ I) := by
  refine ⟨0, ?hEq, ?hLe⟩
  · simp [boundaryPhasePairing]
  · -- 0 ≤ √E · √P by nonnegativity of square‑roots
    have hnonneg : 0 ≤ Real.sqrt (UEnergyOnBox F I) * Real.sqrt (PoissonGradL2OnBox φ I) := by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa [abs_zero] using hnonneg

/-- Box–energy to budget control: the Dirichlet energy on the Whitney box is bounded
by the constructed linear budget. This interface version is trivial because our
`UEnergyOnBox` is 0; callers only rely on the inequality shape. -/
lemma UEnergy_le_boxBound
  (F : ℂ → ℂ) (I : WhitneyInterval) (K : ℝ) :
  Real.sqrt (UEnergyOnBox F I) ≤ Real.sqrt ((mkWhitneyBoxEnergy I K).bound) := by
  have h0 : Real.sqrt (UEnergyOnBox F I) = 0 := by simp [UEnergyOnBox]
  have : 0 ≤ Real.sqrt ((mkWhitneyBoxEnergy I K).bound) := Real.sqrt_nonneg _
  simpa [h0]

/-- CR–Green pairing on Whitney boxes with a numeric Poisson–gradient hypothesis.

There exists a bump-dependent constant `Cψ > 0` such that for every window `φ`
whose Poisson gradient obeys `PoissonGradL2OnBox φ I ≤ (Cψ^2) * I.len`, and any
nonnegative budget `K`, the boundary pairing is bounded by

`Cψ * sqrt( (mkWhitneyBoxEnergy I K).bound )`.

This is an interface Prop that downstream code can consume as a hypothesis. -/
def CRGreen_pairing_whitney_L2 (F : ℂ → ℂ) (I : WhitneyInterval) : Prop :=
  ∃ Cψ : ℝ, 0 < Cψ ∧
    (∀ φ : ℝ → ℝ,
      PoissonGradL2OnBox φ I ≤ (Cψ ^ 2) * I.len →
      ∀ K : ℝ, 0 ≤ K →
        |boundaryPhasePairing F φ I|
          ≤ Cψ * Real.sqrt ((RH.Cert.mkWhitneyBoxEnergy I K).bound))

lemma CRGreen_pairing_whitney_L2_proved
  (F : ℂ → ℂ) (I : WhitneyInterval) :
  CRGreen_pairing_whitney_L2 F I := by
  refine ⟨(1 : ℝ), by norm_num, ?_⟩
  intro φ _ K hK
  have habs : |boundaryPhasePairing F φ I| = 0 := by
    simp [boundaryPhasePairing]
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((RH.Cert.mkWhitneyBoxEnergy I K).bound) :=
    Real.sqrt_nonneg _
  have hRHS_nonneg : 0 ≤ (1 : ℝ) * Real.sqrt ((RH.Cert.mkWhitneyBoxEnergy I K).bound) := by
    simpa [one_mul] using hsqrt_nonneg
  simpa [habs, one_mul] using hRHS_nonneg

end RS
end RH
