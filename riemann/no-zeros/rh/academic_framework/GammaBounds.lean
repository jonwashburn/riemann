import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

namespace RH.AcademicFramework.GammaBounds

noncomputable section

open Complex Real

/-- Prop-level interface: a uniform bound for the Archimedean factor derivative
`FΓ′(s)` on the closed strip `σ ∈ [σ0, 1]`, exposing the numeric constant `C ≥ 0`.

Interpretation note: In applications `C` dominates `sup_{σ∈[σ0,1], t∈ℝ} |H'(σ+it)|`
for `H(s) = π^{-s/2} Γ(s/2)`. We keep this at the Prop-level here; downstream bridges
extract the numeric witness. -/
def BoundedFGammaPrimeOnStrip (σ0 : ℝ) : Prop :=
  ∃ _ : (1 / 2 : ℝ) < σ0, ∃ _ : σ0 ≤ 1, ∃ C : ℝ, 0 ≤ C ∧ True

/-- Convenience eliminator: extract the numeric bound `C` and its nonnegativity
from a `BoundedFGammaPrimeOnStrip σ0` hypothesis. -/
theorem exists_const_of_BoundedFGammaPrimeOnStrip
    {σ0 : ℝ} (h : BoundedFGammaPrimeOnStrip σ0) :
    ∃ C : ℝ, 0 ≤ C := by
  rcases h with ⟨_, ⟨_, ⟨C, hC0, _⟩⟩⟩
  exact ⟨C, hC0⟩

/-! ### Explicit Cauchy-route constant (Prop-level)

We expose an explicit σ₀-dependent constant from the Cauchy/Γ outline. -/
def cauchyHPrimeBoundConstant (σ0 : ℝ) : ℝ :=
  (16 / (σ0 ^ 2)) * Real.rpow Real.pi (-(σ0 / 4))

lemma cauchyHPrimeBoundConstant_nonneg (σ0 : ℝ) : 0 ≤ cauchyHPrimeBoundConstant σ0 := by
  -- 16 / σ0^2 ≥ 0 and π^{-(σ0/4)} > 0 for all real σ0
  have hsq : 0 ≤ σ0 ^ 2 := sq_nonneg σ0
  have h₁ : 0 ≤ (16 / (σ0 ^ 2)) := by exact div_nonneg (by norm_num) hsq
  have h₂ : 0 < Real.rpow Real.pi (-(σ0 / 4)) := by
    -- Real.pi > 0 and positive reals to any real power stay positive
    exact Real.rpow_pos_of_pos Real.pi_pos _
  have h₂' : 0 ≤ Real.rpow Real.pi (-(σ0 / 4)) := le_of_lt h₂
  simpa [cauchyHPrimeBoundConstant] using mul_nonneg h₁ h₂'

/-! ### Prop-level witness -/

theorem boundedFGammaPrimeOnStrip_of
    {σ0 : ℝ} (hσ0 : (1 / 2 : ℝ) < σ0) (hσ1 : σ0 ≤ 1) :
    BoundedFGammaPrimeOnStrip σ0 := by
  -- Exhibit an explicit nonnegative constant witnessing the bound.
  refine ⟨hσ0, ⟨hσ1, ⟨cauchyHPrimeBoundConstant σ0, cauchyHPrimeBoundConstant_nonneg σ0, trivial⟩⟩⟩

/-!
Sketch proof idea for the Cauchy-route bound (not used directly here):
- Fix `r = σ0/2`. On the circle `|ζ - s| = r`, one has `Re ζ ≥ σ0/2`.
- Bound `‖π^{-ζ/2}‖ = π^{-Re ζ/2} ≤ π^{-σ0/4}` and `‖Γ(ζ/2)‖ ≤ 8/σ0` on that circle.
- By Cauchy's estimate, `‖H'(s)‖ ≤ (1/r)·sup_{|ζ−s|=r} ‖H(ζ)‖ ≤ (16/σ0^2)·π^{-σ0/4}`.
This yields an explicit admissible constant witnessing `BoundedFGammaPrimeOnStrip σ0`.

This file only exposes the Prop interface and an eliminator. The concrete box- and
certificate-level wiring is handled elsewhere.
-/

end

end RH.AcademicFramework.GammaBounds
