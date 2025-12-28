/--
Eigenvectors/eigenvalues for Kapustin perturbations of multiplication operators.

This file is the bridge between:

* the abstract Krein/rank-one spectral-parameter calculus
  (`Krein/RankOneEigenvalue.lean`, `Krein/KapustinEigenvalue.lean`), and
* the concrete weighted `L²` multiplier model (`Krein/WeightedL2Kapustin.lean`,
  `Krein/WeightedL2MulEquiv.lean`).

The main lemma gives a **canonical eigenvector candidate** on the resolvent set of the
base multiplication operator.

Informally, if

* `T = M_a - [·,u]u` and
* `m = a - λ` is invertible in `L∞` with inverse `mInv`, and
* the scalar condition `⟪J u, mInv • u⟫ = 1` holds,

then `f = mInv • u` satisfies `T f = λ f`.

This is exactly the algebraic reduction used in Kapustin's HPO-in-Krein-space note;
all analytic content is pushed into verifying the scalar condition.
-/

import KapustinFormalization.Krein.KapustinEigenvalue
import KapustinFormalization.Krein.WeightedL2MulOpAlgebra

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

/-!
## Eigenvector construction on the resolvent set

We model the resolvent `(M_a - λ I)⁻¹` as multiplication by the inverse `mInv` of
`m = a - λ•1` in the `L∞` algebra.
-/

open scoped ComplexConjugate

theorem kapustinMul_eigenpair_of_invSymbol
    (p : α → ℝ)
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u : L2 (μ := μ) 𝕜 p)
    (λ : 𝕜)
    (m mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (hm : m = a - λ • (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)))
    (h₁ : m * mInv = 1)
    (h₂ : mInv * m = 1)
    (hu : u ≠ 0)
    (hscalar : ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, (mInv • u)⟫_𝕜 = 1) :
    ∃ f : L2 (μ := μ) 𝕜 p, f ≠ 0 ∧
      kapustinMul (μ := μ) (𝕜 := 𝕜) p a u f = λ • f := by
  classical
  -- Build the bounded equivalence corresponding to multiplication by `m = a - λ`.
  let Az : (L2 (μ := μ) 𝕜 p) ≃L[𝕜] (L2 (μ := μ) 𝕜 p) :=
    mulEquiv (μ := μ) (𝕜 := 𝕜) p m mInv h₁ h₂

  -- The candidate eigenvector is the resolvent applied to `u`.
  refine ⟨mInv • u, ?_, ?_⟩

  · -- Nontriviality: if `mInv • u = 0`, applying `M_m` gives `u = 0`.
    intro h0
    have : (mulOp (μ := μ) (𝕜 := 𝕜) p m) (mInv • u) = u := by
      -- `m • (mInv • u) = (m*mInv) • u = u`.
      simp [mulOp, h₁, smul_smul]
    -- Rewrite using `h0`.
    have : u = 0 := by simpa [h0] using this
    exact hu this

  · -- Eigenvalue equation.
    -- First, relate `Az.toCLM` to the shift `M_a - λI`.
    have hAz : Az.toContinuousLinearMap
        = Krein.FundamentalSymmetry.shift (K := K (μ := μ) (𝕜 := 𝕜) p)
            (mulOp (μ := μ) (𝕜 := 𝕜) p a) λ := by
      -- `Az.toCLM = mulOp m` by construction.
      -- Then `mulOp m = mulOp (a - λ•1) = mulOp a - λ•I`.
      simp [Az, hm, Krein.FundamentalSymmetry.shift,
        mulOp_sub_smul_one (μ := μ) (𝕜 := 𝕜) (p := p) (m := a) (c := λ)]

    -- Apply the abstract Kapustin eigenvector lemma.
    have heq : (Krein.FundamentalSymmetry.mkKapustinOperator
        (K := K (μ := μ) (𝕜 := 𝕜) p)
        (mulOp (μ := μ) (𝕜 := 𝕜) p a) u)
        (Az.symm u) = λ • (Az.symm u) := by
      -- The scalar condition is exactly `⟪J u, (A-λI)⁻¹ u⟫ = 1`.
      -- Note `Az.symm u = mInv • u`.
      have hscalar' : ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, Az.symm u⟫_𝕜 = 1 := by
        simpa [Az] using hscalar
      exact Krein.FundamentalSymmetry.kapustin_apply_symm_u_eq_smul
        (K := K (μ := μ) (𝕜 := 𝕜) p)
        (A := mulOp (μ := μ) (𝕜 := 𝕜) p a) (z := λ)
        (Az := Az) (hAz := hAz) (u := u) hscalar'

    -- Finally, identify `mkKapustinOperator` with `kapustinMul` and `Az.symm u` with `mInv•u`.
    -- `Az.symm u = mInv • u` is definitional for `mulEquiv`.
    simpa [kapustinMul, Az] using heq

end WeightedL2

end Krein
