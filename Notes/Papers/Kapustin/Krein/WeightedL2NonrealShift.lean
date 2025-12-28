/--
Automatic `L∞`-invertibility of *non-real shifts* of essentially real symbols.

This file provides a functional-analytic bridge repeatedly used in Kapustin’s
Krein–Hilbert–Pólya constructions.

### Mathematical content

Let `a` be an essentially real multiplier (`conj (a x) = a x` almost everywhere) on the
weighted measure space `(α, |p|·μ)`. For any scalar `λ` with nonzero imaginary part, the
shifted symbol

```
m := a - λ·1
```

is *a.e. nonvanishing*, hence it is invertible in the `L∞` algebra with inverse `m⁻¹`.
Consequently multiplication by `m` is a boundedly invertible operator on the Hilbert space
`L²(α, |p|·μ)`.

On top of that, we package the shift `M_a - λI` as a `ContinuousLinearEquiv` using the
`mulEquiv` API (`Krein/WeightedL2MulEquiv.lean`).

### Why this matters

Kapustin’s eigenvalues are typically non-real when the corresponding zeta zeros are off the
critical line. In that regime, the shift `M_a - λI` is automatically invertible, so the
rank-one eigenvector ansatz reduces to verifying the *scalar* condition

`⟪J u, (a-λ)⁻¹ • u⟫ = 1`.

This file removes the need to manually supply an inverse symbol `mInv` and the identities
`m*mInv = 1` / `mInv*m = 1` in downstream developments.
-/

import KapustinFormalization.Krein.WeightedL2KapustinEigenvalue

namespace Krein

namespace WeightedL2

open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α]
variable (μ : MeasureTheory.Measure α)

variable {𝕜 : Type*} [IsROrC 𝕜]

/-!
## Scalar preliminaries

The key elementary fact is:

*if `z` is real (in the sense `conj z = z`) and `λ` has nonzero imaginary part, then
`z - λ ≠ 0`.*

This is what ensures nonvanishing of `a(x) - λ` when `a` is essentially real.
-/

namespace Scalar

lemma im_eq_zero_of_conj_eq_self {z : 𝕜} (hz : IsROrC.conj z = z) : IsROrC.im z = 0 := by
  -- Apply `im` to `conj z = z` and use `im_conj = -im`.
  have him : IsROrC.im (IsROrC.conj z) = IsROrC.im z := congrArg IsROrC.im hz
  have hneg : - IsROrC.im z = IsROrC.im z := by
    simpa [IsROrC.im_conj] using him
  have hsymm : IsROrC.im z = - IsROrC.im z := by
    simpa using hneg.symm
  have hsum : IsROrC.im z + IsROrC.im z = 0 := (eq_neg_iff_add_eq_zero).1 hsymm
  have hmul : (2 : ℝ) * IsROrC.im z = 0 := by
    calc
      (2 : ℝ) * IsROrC.im z = IsROrC.im z + IsROrC.im z := by
        simp [two_mul]
      _ = 0 := hsum
  have : (2 : ℝ) = 0 ∨ IsROrC.im z = 0 := mul_eq_zero.mp hmul
  cases this with
  | inl h2 =>
      -- Contradiction since `2 ≠ 0` in `ℝ`.
      exact (False.elim ((two_ne_zero : (2 : ℝ) ≠ 0) h2))
  | inr hz0 =>
      exact hz0

lemma sub_ne_zero_of_conj_eq_of_im_ne_zero {z λ : 𝕜}
    (hz : IsROrC.conj z = z) (hλ : IsROrC.im λ ≠ 0) : z - λ ≠ 0 := by
  intro h
  have hzλ : z = λ := sub_eq_zero.mp h
  have hiz : IsROrC.im z = 0 := im_eq_zero_of_conj_eq_self (z := z) hz
  have himEq : IsROrC.im λ = IsROrC.im z := (congrArg IsROrC.im hzλ).symm
  have : IsROrC.im λ = 0 := by simpa [hiz] using himEq
  exact hλ this

end Scalar

/-!
## `L∞` invertibility of a non-real shift
-/

section Shift

local notation "μp" => absWeight (μ := μ) (p := (p : α → ℝ))

variable {p : α → ℝ}

variable (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
variable (λ : 𝕜)

/-- The shifted `L∞` symbol `a - λ·1`. -/
noncomputable def shiftSymbol :
    MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p) :=
  a - λ • (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))

@[simp] lemma shiftSymbol_apply (x : α) : shiftSymbol (μ := μ) (p := p) a λ x = a x - λ := by
  simp [shiftSymbol]

/-- If `a` is essentially real and `Im λ ≠ 0`, then `a - λ` is a.e. nonzero. -/
lemma ae_shiftSymbol_ne_zero
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0) :
    ∀ᵐ x ∂(absWeight (μ := μ) p), shiftSymbol (μ := μ) (p := p) a λ x ≠ 0 := by
  -- Reduce pointwise to the scalar lemma.
  filter_upwards [ha] with x hx
  -- `shiftSymbol a λ x = a x - λ`.
  simpa [shiftSymbol_apply (μ := μ) (p := p) (a := a) (λ := λ)] using
    (Scalar.sub_ne_zero_of_conj_eq_of_im_ne_zero (z := a x) (λ := λ) hx hλ)

/-- On the non-real shift, `m * m⁻¹ = 1` in the `L∞` algebra. -/
lemma shiftSymbol_mul_inv
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0) :
    shiftSymbol (μ := μ) (p := p) a λ * (shiftSymbol (μ := μ) (p := p) a λ)⁻¹
      = (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) := by
  classical
  -- Equality in `Lp` is a.e. equality.
  ext x
  have hne : ∀ᵐ x ∂(absWeight (μ := μ) p), shiftSymbol (μ := μ) (p := p) a λ x ≠ 0 :=
    ae_shiftSymbol_ne_zero (μ := μ) (p := p) (a := a) (λ := λ) ha hλ
  filter_upwards [hne] with x hx
  simp [hx]

/-- On the non-real shift, `m⁻¹ * m = 1` in the `L∞` algebra. -/
lemma inv_mul_shiftSymbol
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0) :
    (shiftSymbol (μ := μ) (p := p) a λ)⁻¹ * shiftSymbol (μ := μ) (p := p) a λ
      = (1 : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p)) := by
  classical
  ext x
  have hne : ∀ᵐ x ∂(absWeight (μ := μ) p), shiftSymbol (μ := μ) (p := p) a λ x ≠ 0 :=
    ae_shiftSymbol_ne_zero (μ := μ) (p := p) (a := a) (λ := λ) ha hλ
  filter_upwards [hne] with x hx
  simp [hx]

/-- The boundedly invertible multiplication operator corresponding to the non-real shift
`a - λ·1`.

This is the canonical `ContinuousLinearEquiv` representation of the resolvent symbol.
-/
noncomputable def mulEquivShift
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0) :
    (L2 (μ := μ) 𝕜 p) ≃L[𝕜] (L2 (μ := μ) 𝕜 p) :=
  mulEquiv (μ := μ) (𝕜 := 𝕜) p
    (shiftSymbol (μ := μ) (p := p) a λ)
    (shiftSymbol (μ := μ) (p := p) a λ)⁻¹
    (shiftSymbol_mul_inv (μ := μ) (p := p) (a := a) (λ := λ) ha hλ)
    (inv_mul_shiftSymbol (μ := μ) (p := p) (a := a) (λ := λ) ha hλ)

@[simp] lemma mulEquivShift_apply
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0)
    (f : L2 (μ := μ) 𝕜 p) :
    mulEquivShift (μ := μ) (p := p) (a := a) (λ := λ) ha hλ f
      = (shiftSymbol (μ := μ) (p := p) a λ) • f := by
  rfl

@[simp] lemma mulEquivShift_symm_apply
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0)
    (f : L2 (μ := μ) 𝕜 p) :
    (mulEquivShift (μ := μ) (p := p) (a := a) (λ := λ) ha hλ).symm f
      = (shiftSymbol (μ := μ) (p := p) a λ)⁻¹ • f := by
  rfl

end Shift

/-!
## Eigenpair lemma specialized to the non-real shift

This is the user-facing lemma that allows one to apply the Kapustin rank-one eigenvector
ansatz without manually providing an inverse symbol.
-/

theorem kapustinMul_eigenpair_of_nonrealShift
    {p : α → ℝ}
    (a : MeasureTheory.Lp (α := α) 𝕜 ⊤ (absWeight (μ := μ) p))
    (u : L2 (μ := μ) 𝕜 p)
    (λ : 𝕜)
    (ha : (∀ᵐ x ∂(absWeight (μ := μ) p), IsROrC.conj (a x) = a x))
    (hλ : IsROrC.im λ ≠ 0)
    (hu : u ≠ 0)
    (hscalar :
      ⟪(K (μ := μ) (𝕜 := 𝕜) p).J u,
        ((shiftSymbol (μ := μ) (p := p) a λ)⁻¹ • u)⟫_𝕜 = 1) :
    ∃ f : L2 (μ := μ) 𝕜 p, f ≠ 0 ∧
      kapustinMul (μ := μ) (𝕜 := 𝕜) p a u f = λ • f := by
  classical
  -- Apply the general `invSymbol` eigenpair lemma with `m = a - λ·1` and `mInv = m⁻¹`.
  refine
    kapustinMul_eigenpair_of_invSymbol (μ := μ) (𝕜 := 𝕜)
      (p := p) (a := a) (u := u) (λ := λ)
      (m := shiftSymbol (μ := μ) (p := p) a λ)
      (mInv := (shiftSymbol (μ := μ) (p := p) a λ)⁻¹)
      (hm := rfl)
      (h₁ := shiftSymbol_mul_inv (μ := μ) (p := p) (a := a) (λ := λ) ha hλ)
      (h₂ := inv_mul_shiftSymbol (μ := μ) (p := p) (a := a) (λ := λ) ha hλ)
      (hu := hu)
      (hscalar := by
        -- `mInv • u` is exactly the `L²` vector in the scalar condition.
        simpa using hscalar)

end WeightedL2

end Krein
