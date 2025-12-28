/--
Eigenvalue calculus for the bounded Kapustin rank-one perturbation.

Kapustin's basic bounded operator has the form

`T := A - [·,u]u = A - |u⟩⟨J u|`

in the fundamental-symmetry model (`[x,u] = ⟪J x, u⟫`).

On the resolvent set of `A`, the eigenvalue problem for `T` reduces to a scalar condition
involving the resolvent `(A - zI)⁻¹`.

This file packages that reduction as reusable lemmas, isolating the *purely algebraic* part
of Kapustin's arguments.
-/

import KapustinFormalization.Krein.KapustinOperator
import KapustinFormalization.Krein.RankOneEigenvalue

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-!
## Kapustin eigenvector ansatz on the resolvent set

We reuse the general rank-one eigenvalue lemmas with `v = J u`.
-/

/-- If `A - zI` is boundedly invertible and `x` satisfies the eigenvalue equation

`(A - [·,u]u) x = z • x`,

then `x` is colinear with `(A - zI)⁻¹ u`.
-/
lemma eq_smul_symm_u_of_kapustin_apply_eq_smul
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u x : E)
    (hx : (mkKapustinOperator (K := K) A u) x = z • x) :
    x = (⟪K.J u, x⟫_𝕜) • (Az.symm u) := by
  -- `mkKapustinOperator A u = A - rankOne u (J u)`.
  have hx' : (A - rankOne (K := K) u (K.J u)) x = z • x := by
    simpa [mkKapustinOperator, kreinRankOne] using hx
  -- Apply the general rank-one eigenvector ansatz.
  simpa using
    (eq_smul_symm_u_of_sub_rankOne_apply_eq_smul (K := K)
      (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := K.J u) (x := x) hx')

/-- If `A - zI` is boundedly invertible and the Kapustin scalar condition

`⟪J u, (A - zI)⁻¹ u⟫ = 1`

holds, then `(A - zI)⁻¹ u` is an eigenvector of `A - [·,u]u` with eigenvalue `z`.
-/
lemma kapustin_apply_symm_u_eq_smul
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u : E)
    (h : ⟪K.J u, Az.symm u⟫_𝕜 = 1) :
    (mkKapustinOperator (K := K) A u) (Az.symm u) = z • (Az.symm u) := by
  -- Reduce to the general rank-one eigenvector statement with `v = J u`.
  have :=
    (sub_rankOne_apply_symm_u_eq_smul (K := K)
      (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := K.J u) h)
  simpa [mkKapustinOperator, kreinRankOne] using this

/-!
## The Kapustin scalar condition is *forced* (resolvent regime)

On the resolvent set of `A`, the Kapustin eigenvector ansatz gives

`x = ⟪J u, x⟫ • (A - zI)⁻¹ u`.

Hence any nonzero eigenvector satisfies `⟪J u, x⟫ ≠ 0`, and cancelling this scalar after taking
inner products yields the *necessary* scalar condition

`⟪J u, (A - zI)⁻¹ u⟫ = 1`.

This is the precise algebraic statement underpinning the “zeros ↔ eigenvalues” reduction in
Kapustin’s Krein–Hilbert–Pólya framework.
-/

lemma inner_ne_zero_of_kapustin_apply_eq_smul
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u x : E)
    (hx : (mkKapustinOperator (K := K) A u) x = z • x)
    (hx0 : x ≠ 0) :
    ⟪K.J u, x⟫_𝕜 ≠ 0 := by
  -- Specialize the corresponding rank-one statement with `v = J u`.
  have hx' : (A - rankOne (K := K) u (K.J u)) x = z • x := by
    simpa [mkKapustinOperator, kreinRankOne] using hx
  exact inner_ne_zero_of_sub_rankOne_apply_eq_smul (K := K)
    (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := K.J u) (x := x) hx' hx0

lemma inner_symm_u_eq_one_of_kapustin_apply_eq_smul
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u x : E)
    (hx : (mkKapustinOperator (K := K) A u) x = z • x)
    (hx0 : x ≠ 0) :
    ⟪K.J u, Az.symm u⟫_𝕜 = 1 := by
  -- Reduce to the rank-one scalar-condition lemma with `v = J u`.
  have hx' : (A - rankOne (K := K) u (K.J u)) x = z • x := by
    simpa [mkKapustinOperator, kreinRankOne] using hx
  exact inner_symm_u_eq_one_of_sub_rankOne_apply_eq_smul (K := K)
    (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := K.J u) (x := x) hx' hx0

/-!
## Eigenvalue existence is equivalent to the Kapustin scalar condition (resolvent regime)

Under a bounded resolvent hypothesis for `A - zI`, the Kapustin perturbation

`T := A - [·,u]u`

admits a nontrivial eigenvector with eigenvalue `z` if and only if

`⟪J u, (A - zI)⁻¹ u⟫ = 1`.

This is the clean algebraic interface used downstream: analytic work only needs to produce the
candidate vector `(A - zI)⁻¹ u` (or its unbounded surrogate) and verify the scalar condition.
-/

theorem exists_nonzero_eigenvector_kapustin_iff_inner_eq_one
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u : E) :
    (∃ x : E, x ≠ 0 ∧ (mkKapustinOperator (K := K) A u) x = z • x)
      ↔ ⟪K.J u, Az.symm u⟫_𝕜 = 1 := by
  -- Specialize the general rank-one equivalence to `v = J u`.
  simpa [mkKapustinOperator, kreinRankOne] using
    (exists_nonzero_eigenvector_sub_rankOne_iff_inner_eq_one (K := K)
      (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := K.J u))

/-!
## Kapustin eigenvector criterion without resolvent hypotheses

For spectral parameters on the Hilbert-spectrum of the base operator `A`, the bounded resolvent
`(A - zI)⁻¹` need not exist. Kapustin’s analytic eigenvector constructions nonetheless produce a
vector `x` for which the inhomogeneous shift equation `(A - zI)x = u` holds, together with the
normalization `⟪J u, x⟫ = 1`.

The following lemma isolates this algebraic mechanism.
-/

/-- **Kapustin eigenvector criterion without a resolvent hypothesis.**

If `x` satisfies `(A - zI) x = u` and `⟪J u, x⟫ = 1`, then `x` is an eigenvector of
`A - [·,u]u` with eigenvalue `z`.
-/
lemma kapustin_apply_eq_smul_of_shift_apply_eq_u_of_inner_eq_one
    (A : E →L[𝕜] E) (z : 𝕜) (u x : E)
    (hx : shift (K := K) A z x = u)
    (hinner : ⟪K.J u, x⟫_𝕜 = 1) :
    (mkKapustinOperator (K := K) A u) x = z • x := by
  -- Reduce to the general rank-one statement with `v = J u`.
  have :=
    sub_rankOne_apply_eq_smul_of_shift_apply_eq_u_of_inner_eq_one (K := K)
      (A := A) (z := z) (u := u) (v := K.J u) (x := x) hx hinner
  simpa [mkKapustinOperator, kreinRankOne] using this

end FundamentalSymmetry

end Krein
