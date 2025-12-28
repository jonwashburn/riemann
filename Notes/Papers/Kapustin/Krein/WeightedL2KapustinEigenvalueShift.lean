/--
Eigenpair construction for Kapustin perturbations from a *direct* shift equation.

This file complements `Krein/WeightedL2KapustinEigenvalue.lean`.

In many analytic situations (notably when the spectral parameter lies on the Hilbert-spectrum of
the base multiplication operator), the resolvent symbol `(a-λ)⁻¹` need not be essentially bounded,
so the resolvent-based eigenvector ansatz cannot be expressed using the `L∞` action on `L²`.

Nevertheless, Kapustin’s constructions produce an `L²` vector `f` solving the inhomogeneous shift
equation

`(M_a - λI) f = u`,

and then verify the scalar normalization `⟪J u, f⟫ = 1`.

The main theorem below packages this purely algebraic mechanism in the weighted `L²` model.
-/

import KapustinFormalization.Krein.WeightedL2Kapustin
import KapustinFormalization.Krein.WeightedL2MulOpAlgebra
import KapustinFormalization.Krein.KapustinEigenvalue

namespace Krein

namespace WeightedL2

open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

/-!
## Shift equations for multiplication operators

We record a convenient rewriting lemma turning the abstract shift operator
`FundamentalSymmetry.shift` into a multiplier by the shifted `L∞` symbol.
-/

section

variable {p : α → ℝ}

lemma shift_mulOp_eq_mulOp_shiftSymbol
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (λ : 𝕜) :
    Krein.FundamentalSymmetry.shift (K := K (μ := μ) (𝕜 := 𝕜) p)
        (mulOp (μ := μ) (𝕜 := 𝕜) p a) λ
      = mulOp (μ := μ) (𝕜 := 𝕜) p
          (a - λ • (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))) := by
  -- This is exactly the `mulOp` shift identity.
  -- `shift A λ = A - λI` and `mulOp (a - λ•1) = mulOp a - λI`.
  simp [Krein.FundamentalSymmetry.shift,
    mulOp_sub_smul_one (μ := μ) (𝕜 := 𝕜) (p := p) (m := a) (c := λ)]

end

/-!
## Kapustin eigenpair from a shift solution
-/

theorem kapustinMul_eigenpair_of_shiftEq
    {p : α → ℝ}
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u : L2 (μ := μ) 𝕜 p)
    (λ : 𝕜)
    (f : L2 (μ := μ) 𝕜 p)
    (hf :
      Krein.FundamentalSymmetry.shift (K := K (μ := μ) (𝕜 := 𝕜) p)
          (mulOp (μ := μ) (𝕜 := 𝕜) p a) λ f = u)
    (hscalar : ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, f⟫_𝕜 = 1) :
    kapustinMul (μ := μ) (𝕜 := 𝕜) p a u f = λ • f := by
  -- Apply the abstract Kapustin lemma that does not assume resolvents.
  simpa [kapustinMul] using
    (Krein.FundamentalSymmetry.kapustin_apply_eq_smul_of_shift_apply_eq_u_of_inner_eq_one
      (K := K (μ := μ) (𝕜 := 𝕜) p)
      (A := mulOp (μ := μ) (𝕜 := 𝕜) p a) (z := λ) (u := u) (x := f)
      hf hscalar)

theorem kapustinMul_exists_eigenpair_of_shiftEq
    {p : α → ℝ}
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u : L2 (μ := μ) 𝕜 p)
    (λ : 𝕜)
    (f : L2 (μ := μ) 𝕜 p)
    (hu : u ≠ 0)
    (hf :
      Krein.FundamentalSymmetry.shift (K := K (μ := μ) (𝕜 := 𝕜) p)
          (mulOp (μ := μ) (𝕜 := 𝕜) p a) λ f = u)
    (hscalar : ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, f⟫_𝕜 = 1) :
    ∃ f' : L2 (μ := μ) 𝕜 p, f' ≠ 0 ∧ kapustinMul (μ := μ) (𝕜 := 𝕜) p a u f' = λ • f' := by
  refine ⟨f, ?_, kapustinMul_eigenpair_of_shiftEq (μ := μ) (p := p) (a := a) (u := u)
    (λ := λ) (f := f) hf hscalar⟩
  intro hf0
  -- If `f = 0`, the shift equation forces `u = 0`.
  have : u = 0 := by simpa [hf0] using hf
  exact hu this

end WeightedL2

end Krein
