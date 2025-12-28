/--
Non-real spectral parameters: Kapustin eigenvalues ⇔ scalar condition (weighted `L²` multiplier model).

This file synthesizes the two key ingredients already formalized:

* the **abstract** rank-one/Kapustin eigenvalue calculus on the resolvent set
  (`Krein/RankOneEigenvalue.lean`, `Krein/KapustinEigenvalue.lean`), and
* the **concrete** weighted-`L²` multiplier model together with the automatic invertibility of
  non-real shifts of essentially real symbols (`Krein/WeightedL2NonrealShift.lean`).

### Mathematical content

Let `a ∈ L∞(α,|p|·μ)` be essentially real and consider the Kapustin perturbation

`T := M_a - [·,u]u`

on `L²(α,|p|·μ)`. If `Im λ ≠ 0`, then the shifted symbol `a - λ` is a.e. nonzero, hence invertible in
`L∞` with inverse `(a - λ)⁻¹`. In this regime the eigenvalue problem

`T f = λ f`

is equivalent to the scalar condition

`⟪J u, (a-λ)⁻¹ • u⟫ = 1`,

and every eigenvector is colinear with the resolvent vector `(a-λ)⁻¹ • u`.

This is precisely the reduction used in Kapustin’s Krein–Hilbert–Pólya arguments for
non-real candidate eigenvalues.
-/

import KapustinFormalization.Krein.WeightedL2NonrealShift

namespace Krein

namespace WeightedL2

open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

section

variable {p : α → ℝ}

/-!
## Eigenvectors are scalar multiples of the resolvent vector

This is the specialization of the abstract Kapustin eigenvector ansatz to the multiplier model,
using the explicit `ContinuousLinearEquiv` representing the non-real shift.
-/

theorem kapustinMul_eq_smul_resolvent_u_of_nonreal_eigen
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u f : L2 (μ := μ) 𝕜 p)
    (λ : 𝕜)
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0)
    (hf : kapustinMul (μ := μ) (𝕜 := 𝕜) p a u f = λ • f) :
    f = (⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, f⟫_𝕜)
          • (((shiftSymbol (μ := μ) (p := p) a λ)⁻¹) • u) := by
  classical
  -- Instantiate the abstract lemma with the explicit equivalence for the non-real shift.
  let Az : (L2 (μ := μ) 𝕜 p) ≃L[𝕜] (L2 (μ := μ) 𝕜 p) :=
    mulEquivShift (μ := μ) (p := p) (a := a) (λ := λ) ha hλ

  have hAz : Az.toContinuousLinearMap
        = Krein.FundamentalSymmetry.shift
            (K := K (μ := μ) (𝕜 := 𝕜) p)
            (mulOp (μ := μ) (𝕜 := 𝕜) p a) λ := by
    -- `Az` is multiplication by `a - λ`, and `shift (M_a) λ = M_{a-λ}`.
    -- We keep the proof pointwise for robustness.
    ext g
    simp [Az, mulEquivShift, Krein.FundamentalSymmetry.shift,
      shiftSymbol, mulOp_sub_smul_one (μ := μ) (𝕜 := 𝕜) (p := p) (m := a) (c := λ)]

  -- Apply the abstract eigenvector ansatz and rewrite the resolvent action as multiplication
  -- by `(a-λ)⁻¹`.
  have hf' : (Krein.FundamentalSymmetry.mkKapustinOperator
        (K := K (μ := μ) (𝕜 := 𝕜) p)
        (mulOp (μ := μ) (𝕜 := 𝕜) p a) u) f = λ • f := by
    simpa [kapustinMul] using hf

  have := Krein.FundamentalSymmetry.eq_smul_symm_u_of_kapustin_apply_eq_smul
    (K := K (μ := μ) (𝕜 := 𝕜) p)
    (A := mulOp (μ := μ) (𝕜 := 𝕜) p a) (z := λ)
    (Az := Az) (hAz := hAz) (u := u) (x := f) hf'

  -- `Az.symm u = (a-λ)⁻¹ • u` by construction of `mulEquivShift`.
  simpa [Az, mulEquivShift_symm_apply (μ := μ) (p := p) (a := a) (λ := λ) ha hλ] using this

/-!
## Eigenvalue existence ⇔ scalar condition (non-real shift)

This is the canonical reduction in Kapustin’s work: for `Im λ ≠ 0`, the shift is automatically
invertible, so the eigenvalue problem reduces to a single scalar identity.
-/

theorem kapustinMul_exists_nonzero_eigenvector_iff_scalar_of_nonrealShift
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u : L2 (μ := μ) 𝕜 p)
    (λ : 𝕜)
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0) :
    (∃ f : L2 (μ := μ) 𝕜 p,
        f ≠ 0 ∧ kapustinMul (μ := μ) (𝕜 := 𝕜) p a u f = λ • f)
      ↔ ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u,
          ((shiftSymbol (μ := μ) (p := p) a λ)⁻¹ • u)⟫_𝕜 = 1 := by
  classical
  constructor
  · rintro ⟨f, hf0, hf⟩
    -- Use the abstract “eigenvector ⇒ scalar condition” lemma on the resolvent set.
    let Az : (L2 (μ := μ) 𝕜 p) ≃L[𝕜] (L2 (μ := μ) 𝕜 p) :=
      mulEquivShift (μ := μ) (p := p) (a := a) (λ := λ) ha hλ

    have hAz : Az.toContinuousLinearMap
          = Krein.FundamentalSymmetry.shift
              (K := K (μ := μ) (𝕜 := 𝕜) p)
              (mulOp (μ := μ) (𝕜 := 𝕜) p a) λ := by
      ext g
      simp [Az, mulEquivShift, Krein.FundamentalSymmetry.shift,
        shiftSymbol, mulOp_sub_smul_one (μ := μ) (𝕜 := 𝕜) (p := p) (m := a) (c := λ)]

    have hf' : (Krein.FundamentalSymmetry.mkKapustinOperator
          (K := K (μ := μ) (𝕜 := 𝕜) p)
          (mulOp (μ := μ) (𝕜 := 𝕜) p a) u) f = λ • f := by
      simpa [kapustinMul] using hf

    have hscalar := Krein.FundamentalSymmetry.inner_symm_u_eq_one_of_kapustin_apply_eq_smul
      (K := K (μ := μ) (𝕜 := 𝕜) p)
      (A := mulOp (μ := μ) (𝕜 := 𝕜) p a) (z := λ)
      (Az := Az) (hAz := hAz) (u := u) (x := f) hf' hf0

    -- Rewrite `Az.symm u` as `(a-λ)⁻¹ • u`.
    simpa [Az, mulEquivShift_symm_apply (μ := μ) (p := p) (a := a) (λ := λ) ha hλ] using hscalar

  · intro hscalar
    -- First, `hscalar` forces `u ≠ 0`.
    have hu : u ≠ 0 := by
      intro hu0
      have : (0 : 𝕜) = 1 := by
        simpa [hu0] using hscalar
      exact zero_ne_one this

    -- Then apply the existing construction of an eigenpair from the scalar condition.
    simpa using
      kapustinMul_eigenpair_of_nonrealShift (μ := μ) (𝕜 := 𝕜)
        (p := p) (a := a) (u := u) (λ := λ)
        (ha := ha) (hλ := hλ) (hu := hu) (hscalar := hscalar)

end

end WeightedL2

end Krein
