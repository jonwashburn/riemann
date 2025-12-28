/--
Integral formula for Kapustin’s scalar condition in the weighted `L²` model.

Kapustin’s rank-one eigenvalue criterion (on the resolvent set) involves the scalar

`⟪J u, (A - z I)⁻¹ u⟫`.

In the **multiplier model** `A = M_a` on the weighted Hilbert space

`L²(α, |p|·μ)`,

the resolvent vector is represented by pointwise multiplication `mInv • u`, where
`mInv ∈ L∞(α, |p|·μ)` is a symbol encoding `(a - z)⁻¹`.

This file rewrites the scalar as an integral with respect to the *base* measure `μ`:

`⟪J u, mInv • u⟫ = ∫ conj(u(x)) * (mInv(x) * u(x)) * p(x) dμ`.

This identity is the canonical bridge from the abstract functional-analytic rank-one calculus
to the analytic estimates in Kapustin’s papers (Hardy/Mellin computations, contour shifts,
explicit integral representations, etc.).
-/

import KapustinFormalization.Krein.WeightedL2Kapustin
import KapustinFormalization.Krein.WeightedL2NonrealShift

open scoped ComplexConjugate

namespace Krein

namespace WeightedL2

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

section

variable {p : α → ℝ}

/-!
## The Kapustin scalar as a base-measure integral

The lemma `kreinInner_eq_integral` in `Krein/WeightedL2.lean` already gives the formula

`⟪f,g⟫[K] = ∫ conj(f) * g * p dμ`,

where `⟪·,·⟫[K]` is the Krein bracket induced by the fundamental symmetry
`J = mul (sign p)`.

Since the Krein bracket is defined by `⟪f,g⟫[K] = ⟪J f, g⟫` in the *Hilbert* inner product,
we obtain Kapustin’s scalar `⟪J u, mInv•u⟫` by specializing `f := u` and `g := mInv•u`.
-/

lemma inner_Ju_smul_eq_integral
    (u : L2 (μ := μ) 𝕜 p)
    (mInv : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) :
    ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u, (mInv • u)⟫_𝕜 =
      ∫ x, (IsROrC.conj (u x)) * ((mInv x) * (u x)) * (p x : 𝕜) ∂μ := by
  -- Rewrite the Hilbert inner product scalar as a Krein bracket, then apply the weighted model
  -- integral formula. The remaining algebra is just reassociation of scalars.
  --
  -- `⟪u, mInv•u⟫[K]` is definitionally `⟪J u, mInv•u⟫`.
  -- The lemma `kreinInner_eq_integral` then gives the desired integral.
  -- Finally, `simp` converts `(mInv • u) x` into `mInv x * u x`.
  -- (1) Apply the weighted-model integral formula to the Krein bracket.
  have hKrein :
      ⟪u, (mInv • u)⟫[(K (μ := μ) (𝕜 := 𝕜) p)]
        = ∫ x, (IsROrC.conj (u x)) * ((mInv x) * (u x)) * (p x : 𝕜) ∂μ := by
    -- `K p` is definitionally `fundamentalSymmetry p`.
    simpa [K, mul_assoc] using
      (kreinInner_eq_integral (μ := μ) (𝕜 := 𝕜) (p := p) (f := u) (g := (mInv • u)))

  -- (2) The Krein bracket is by definition the Hilbert inner product with `J` on the left.
  -- Rewrite the goal using that definitional equality and conclude from `hKrein`.
  simpa [FundamentalSymmetry.kreinInner] using hKrein

/-!
## Specialization to the non-real shift

For `Im λ ≠ 0` and essentially real `a`, the shift symbol `m = a - λ` is invertible in `L∞` and
Kapustin’s scalar condition is expressed using the canonical inverse `m⁻¹`.

The next lemma is the exact integral expression for the scalar appearing in
`WeightedL2NonrealShift.kapustinMul_eigenpair_of_nonrealShift`.
-/

lemma inner_Ju_shiftSymbol_inv_smul_eq_integral
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u : L2 (μ := μ) 𝕜 p)
    (λ : 𝕜) :
    ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u,
        ((shiftSymbol (μ := μ) (p := p) a λ)⁻¹ • u)⟫_𝕜 =
      ∫ x, (IsROrC.conj (u x)) * (((a x - λ)⁻¹) * (u x)) * (p x : 𝕜) ∂μ := by
  -- Start from the general lemma with `mInv := (shiftSymbol a λ)⁻¹`.
  -- Then rewrite the inverse symbol pointwise using `shiftSymbol_apply`.
  simpa [shiftSymbol_apply (μ := μ) (p := p) (a := a) (λ := λ), mul_assoc] using
    (inner_Ju_smul_eq_integral (μ := μ) (p := p) (u := u)
      (mInv := (shiftSymbol (μ := μ) (p := p) a λ)⁻¹))

end

end WeightedL2

end Krein
