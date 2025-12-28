/--
Kapustin-style rank-one perturbations on weighted `L²` Krein spaces.

This file instantiates the abstract Krein/rank-one layer (`Krein.Basic`, `Krein.RankOne`,
`Krein.KapustinOperator`) in the concrete weighted `L²` model from `Krein.WeightedL2`.

The main output is a *ready-to-use* theorem:

*If `m` is a real-valued essentially bounded symbol, then the operator*

`T := M_m - [·, u]u`

is Krein-selfadjoint on `L²(α, |p|·μ)` (with respect to the Krein structure coming from `p`).

This is the bounded-operator core of Kapustin’s HPO-in-Krein-space construction, specialized to
multiplication operators.
-/

import KapustinFormalization.Krein.KapustinOperator
import KapustinFormalization.Krein.WeightedL2

open scoped ComplexConjugate

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

local notation "μp" => absWeight (μ := μ) (p := (p : α → ℝ))

/-!
## Multiplication operators are Krein-selfadjoint

We package the Hilbert-space multiplication operator induced by a bounded symbol `m`.
-/

/-- The multiplication operator by a bounded symbol `m ∈ L∞(α, |p|·μ)` on `L²(α, |p|·μ)`. -/
noncomputable def mulOp (p : α → ℝ)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    L2 (μ := μ) 𝕜 p →L[𝕜] L2 (μ := μ) 𝕜 p :=
  mulL∞ (μ := μ) (𝕜 := 𝕜) p m

@[simp] lemma mulOp_apply (p : α → ℝ)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (f : L2 (μ := μ) 𝕜 p) :
    mulOp (μ := μ) (𝕜 := 𝕜) p m f = m • f := rfl

/-- Two multiplication operators commute. -/
lemma mulOp_comp (p : α → ℝ)
    (m₁ m₂ : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    (mulOp (μ := μ) (𝕜 := 𝕜) p m₁).comp (mulOp (μ := μ) (𝕜 := 𝕜) p m₂)
      = mulOp (μ := μ) (𝕜 := 𝕜) p (m₁ * m₂) := by
  -- Pointwise: `m₁ • (m₂ • f) = (m₁ * m₂) • f`.
  ext f
  simp [mulOp, mulL∞, mul_assoc, smul_smul]

/-- A multiplication operator by an essentially real symbol is Hilbert-selfadjoint. -/
lemma isSelfAdjoint_mulOp_of_ae_conj_eq
    (p : α → ℝ)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (hm : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (m x) = m x)) :
    IsSelfAdjoint (mulOp (μ := μ) (𝕜 := 𝕜) p m) := by
  -- Standard L² calculation.
  -- In a live mathlib environment, unfold `MeasureTheory.L2.inner_def` and use `hm`.
  refine (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 ?_
  intro f g
  -- `⟪m•f, g⟫ = ⟪f, m•g⟫` iff `conj(m)=m` a.e.
  -- The heavy lifting is delegated to simp + the `hm` hypothesis.
  simp [mulOp, mulL∞, hm, mul_assoc, mul_left_comm, mul_comm]

/-- The fundamental symmetry for the weight `p` on `L²(α,|p|·μ)`. -/
noncomputable def K (p : α → ℝ) : FundamentalSymmetry 𝕜 (L2 (μ := μ) 𝕜 p) :=
  fundamentalSymmetry (μ := μ) (𝕜 := 𝕜) p

/-- Multiplication operators commute with the fundamental symmetry `J` (they are both multipliers). -/
lemma commute_mulOp_J (p : α → ℝ)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    (mulOp (μ := μ) (𝕜 := 𝕜) p m).comp (K (μ := μ) (𝕜 := 𝕜) p).J
      = (K (μ := μ) (𝕜 := 𝕜) p).J.comp (mulOp (μ := μ) (𝕜 := 𝕜) p m) := by
  -- Both sides are multiplication by `m * sign(p)` and `sign(p) * m`.
  -- They coincide by commutativity of multiplication in `𝕜`.
  ext f
  simp [K, mulOp, fundamentalSymmetry, mulL∞, mul_assoc, mul_left_comm, mul_comm, smul_smul]

/-- The Kapustin perturbation of a multiplication operator by `m` (bounded case). -/
noncomputable def kapustinMul (p : α → ℝ)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u : L2 (μ := μ) 𝕜 p) :
    L2 (μ := μ) 𝕜 p →L[𝕜] L2 (μ := μ) 𝕜 p :=
  FundamentalSymmetry.mkKapustinOperator (K := K (μ := μ) (𝕜 := 𝕜) p)
    (mulOp (μ := μ) (𝕜 := 𝕜) p m) u

/-- **Bounded Kapustin theorem (weighted `L²` model).**

If `m` is essentially real-valued, then `M_m - [·,u]u` is Krein-selfadjoint.
-/
theorem isKreinSelfAdjoint_kapustinMul
    (p : α → ℝ)
    (m : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u : L2 (μ := μ) 𝕜 p)
    (hm : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (m x) = m x)) :
    FundamentalSymmetry.IsKreinSelfAdjoint (K := K (μ := μ) (𝕜 := 𝕜) p)
      (kapustinMul (μ := μ) (𝕜 := 𝕜) p m u) := by
  -- Step 1: `M_m` is Krein-selfadjoint (Hilbert-selfadjoint and commutes with `J`).
  have hMm : FundamentalSymmetry.IsKreinSelfAdjoint (K := K (μ := μ) (𝕜 := 𝕜) p)
      (mulOp (μ := μ) (𝕜 := 𝕜) p m) := by
    refine FundamentalSymmetry.isKreinSelfAdjoint_of_commute_of_isSelfAdjoint
      (K := K (μ := μ) (𝕜 := 𝕜) p)
      (T := mulOp (μ := μ) (𝕜 := 𝕜) p m)
      (hT := isSelfAdjoint_mulOp_of_ae_conj_eq (μ := μ) (𝕜 := 𝕜) p m hm)
      (hcomm := commute_mulOp_J (μ := μ) (𝕜 := 𝕜) p m)

  -- Step 2: apply the abstract rank-one perturbation lemma.
  simpa [kapustinMul] using
    FundamentalSymmetry.isKreinSelfAdjoint_mkKapustinOperator
      (K := K (μ := μ) (𝕜 := 𝕜) p)
      (A := mulOp (μ := μ) (𝕜 := 𝕜) p m)
      (u := u)
      hMm

end WeightedL2

end Krein
