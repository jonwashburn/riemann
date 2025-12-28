/--
Hardy/Mellin analytic model: transport of Kapustin’s **integral scalar** to an **analytic scalar**.

### Context

In the weighted `L²` multiplier model (`Krein/WeightedL2`), Kapustin’s rank‑one eigenvalue criterion
involves the scalar

`⟪J u, (A - z I)⁻¹ u⟫`

which, for multiplication resolvents, is represented by an integral with respect to the *base*
measure (`Krein/WeightedL2KapustinScalarIntegral`).

Kapustin’s analytic arguments then move this scalar to a Hardy / de Branges realization via a
unitary equivalence (typically a Mellin–Paley–Wiener type transform, possibly followed by further
unitary identifications).

This file packages the **minimal** abstraction required for that passage:

* a target Hilbert/Krein model `H` equipped with a fundamental symmetry `K'`,
* a unitary equivalence `U : L²(α, |p|·μ) ≃ₗᵢ H` that *intertwines* the fundamental symmetries,
* and the resulting identity expressing Kapustin’s `L²`-integral scalar as the corresponding
  (analytic) Hilbert scalar in `H`.

Crucially, the transport lemma is proved **directly from the integral formula** in
`WeightedL2KapustinScalarIntegral`, so that subsequent analytic work can start from an integral
expression and end in the Hardy/de Branges scalar product without redoing the `L²` bookkeeping.
-/

import KapustinFormalization.Krein.WeightedL2KapustinScalarIntegral
import KapustinFormalization.Krein.Intertwining

open scoped ComplexConjugate

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {p : α → ℝ}

universe uH

/--
A **Hardy/Mellin model** for the weighted `L²` Krein space.

This is an abstract packaging of the analytic realization used in Kapustin’s papers:

* `H` is the target Hilbert space (Hardy space, de Branges space, Sonin space, …),
* `K'` is its fundamental symmetry,
* `U` is a unitary equivalence from the weighted `L²` model,
* `intertwines` records the compatibility `K'.J ∘ U = U ∘ K.J`.

Once such a model is instantiated, the Kapustin scalar condition can be transported to `H` and
identified with the corresponding analytic scalar.
-/
structure HardyMellinModel where
  /-- The target Hilbert space (Hardy/de Branges realization). -/
  H : Type uH
  /-- Normed additive structure on `H`. -/
  instNormed : NormedAddCommGroup H
  /-- Inner product structure on `H`. -/
  instInner : InnerProductSpace 𝕜 H
  /-- Completeness of `H`. -/
  instComplete : CompleteSpace H
  /-- Fundamental symmetry on `H`. -/
  K' : FundamentalSymmetry 𝕜 H
  /-- Unitary equivalence from the weighted `L²` model. -/
  U : L2 (μ := μ) 𝕜 p ≃ₗᵢ[𝕜] H
  /-- Intertwining condition `K'.J ∘ U = U ∘ K.J`. -/
  intertwines :
    FundamentalSymmetry.Intertwines
      (K := K (μ := μ) (𝕜 := 𝕜) p)
      (K' := K')
      (U := U.toContinuousLinearEquiv.toContinuousLinearMap)

attribute [instance] HardyMellinModel.instNormed
attribute [instance] HardyMellinModel.instInner
attribute [instance] HardyMellinModel.instComplete

namespace HardyMellinModel

variable {μ}

/-- The analytic realization of Kapustin’s scalar in the target model. -/
noncomputable def analyticScalar
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    𝕜 :=
  ⟪M.K'.J (M.U u), M.U (mInv • u)⟫_𝕜

/-- The same scalar, but expressed as the **Krein bracket** in the target model. -/
noncomputable def analyticKreinScalar
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    𝕜 :=
  ⟪M.U u, M.U (mInv • u)⟫[M.K']

@[simp] lemma analyticKreinScalar_eq_analyticScalar
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    analyticKreinScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv
      = analyticScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv := by
  -- This is just definitional expansion of the Krein bracket.
  simp [analyticKreinScalar, analyticScalar, FundamentalSymmetry.kreinInner]

/--
**Transport of the integral scalar to the analytic scalar.**

Let `M` be a Hardy/Mellin model of the weighted `L²` Krein space.
Then Kapustin’s scalar computed in the `L²` model (hence given by an explicit integral) equals the
corresponding Hilbert scalar in the target analytic model.

This is the precise bridge needed to continue Kapustin’s argument in Hardy/de Branges language
starting *directly* from the `L²` integral.
-/
lemma analyticScalar_eq_integral
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    analyticScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv
      = ∫ x, (IsROrC.conj (u x)) * ((mInv x) * (u x)) * (p x : 𝕜) ∂μ := by
  -- Step 1: intertwining identifies `K'.J (U u)` with `U (K.J u)`.
  have hJU : M.K'.J (M.U u) = M.U ((K (μ := μ) (𝕜 := 𝕜) p).J u) := by
    -- `intertwines_apply` gives `K'.J (U u) = U (K.J u)`.
    simpa using
      (FundamentalSymmetry.intertwines_apply
        (K := K (μ := μ) (𝕜 := 𝕜) p)
        (K' := M.K')
        (U := M.U.toContinuousLinearEquiv.toContinuousLinearMap)
        (h := M.intertwines)
        (x := u))

  -- Step 2: use unitarity of `U` to pull the inner product back to the `L²` model.
  have hinner :
      ⟪M.K'.J (M.U u), M.U (mInv • u)⟫_𝕜
        = ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, (mInv • u)⟫_𝕜 := by
    -- Rewrite the left slot using `hJU`, then apply `inner_map_map`.
    -- `inner_map_map` states `⟪U x, U y⟫ = ⟪x, y⟫`.
    simpa [hJU] using (M.U.inner_map_map ((K (μ := μ) (𝕜 := 𝕜) p).J u) (mInv • u)).symm

  -- Step 3: rewrite the `L²`-model scalar by the integral formula.
  -- (This is exactly the lemma proved in `WeightedL2KapustinScalarIntegral`.)
  simpa [analyticScalar, hinner] using
    (inner_Ju_smul_eq_integral (μ := μ) (𝕜 := 𝕜) (p := p) (u := u) (mInv := mInv))

/-- The integral scalar equals the target **Krein bracket** version of the analytic scalar. -/
lemma analyticKreinScalar_eq_integral
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    analyticKreinScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv
      = ∫ x, (IsROrC.conj (u x)) * ((mInv x) * (u x)) * (p x : 𝕜) ∂μ := by
  -- Reduce to the Hilbert-inner-product statement.
  simpa [analyticKreinScalar_eq_analyticScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv] using
    (analyticScalar_eq_integral (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv)

/--
A convenient reformulation: Kapustin’s analytic scalar condition in the Hardy/Mellin model is
*equivalent* to the corresponding integral identity in the weighted `L²` model.
-/
lemma analyticScalar_eq_one_iff_integral_eq_one
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    (analyticScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv = 1)
      ↔ ((∫ x, (IsROrC.conj (u x)) * ((mInv x) * (u x)) * (p x : 𝕜) ∂μ) = 1) := by
  -- Immediate from `analyticScalar_eq_integral`.
  simpa [analyticScalar_eq_integral (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv]

/-- The corresponding statement for the Krein‑bracket formulation of the analytic scalar. -/
lemma analyticKreinScalar_eq_one_iff_integral_eq_one
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    (analyticKreinScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv = 1)
      ↔ ((∫ x, (IsROrC.conj (u x)) * ((mInv x) * (u x)) * (p x : 𝕜) ∂μ) = 1) := by
  -- Immediate from `analyticKreinScalar_eq_integral`.
  simpa [analyticKreinScalar_eq_integral (μ := μ) (𝕜 := 𝕜) (p := p) M u mInv]

/-!
## Convenience specializations for the non-real shift symbol

Downstream Kapustin eigenvalue arguments almost always take

`mInv = (shiftSymbol a λ)⁻¹` (for `Im λ ≠ 0`),

so we record the corresponding specializations in the analytic model.
-/

lemma analyticScalar_shiftSymbol_inv_smul_eq_integral
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (λ : 𝕜) :
    analyticScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u ((shiftSymbol (μ := μ) (p := p) a λ)⁻¹)
      = ∫ x, (IsROrC.conj (u x)) * (((a x - λ)⁻¹) * (u x)) * (p x : 𝕜) ∂μ := by
  -- Combine the general transport lemma with the pointwise simplification of the inverse shift
  -- symbol.
  simpa [shiftSymbol_apply (μ := μ) (p := p) (a := a) (λ := λ), mul_assoc] using
    (analyticScalar_eq_integral (μ := μ) (𝕜 := 𝕜) (p := p) M u
      ((shiftSymbol (μ := μ) (p := p) a λ)⁻¹))

lemma analyticKreinScalar_shiftSymbol_inv_smul_eq_integral
    (M : HardyMellinModel (μ := μ) (𝕜 := 𝕜) (p := p))
    (u : L2 (μ := μ) 𝕜 p)
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (λ : 𝕜) :
    analyticKreinScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u ((shiftSymbol (μ := μ) (p := p) a λ)⁻¹)
      = ∫ x, (IsROrC.conj (u x)) * (((a x - λ)⁻¹) * (u x)) * (p x : 𝕜) ∂μ := by
  -- Reduce to the Hilbert formulation.
  simpa [analyticKreinScalar_eq_analyticScalar (μ := μ) (𝕜 := 𝕜) (p := p) M u
      ((shiftSymbol (μ := μ) (p := p) a λ)⁻¹)] using
    (analyticScalar_shiftSymbol_inv_smul_eq_integral (μ := μ) (𝕜 := 𝕜) (p := p) M u a λ)

end HardyMellinModel

end WeightedL2

end Krein
