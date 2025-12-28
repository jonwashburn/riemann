/--
Eigenvalue calculus for rank-one perturbations.

This file refines the kernel-level theory in `Krein/RankOneResolvent.lean` to an
eigenvalue/spectral-parameter statement.

For a bounded operator `A` and vectors `u v`, consider the rank-one perturbation

`T := A - |u⟩⟨v|`.

Fix a spectral parameter `z : 𝕜`. The eigenvalue equation

`T x = z • x`

is equivalent to the kernel equation

`(A - z I - |u⟩⟨v|) x = 0`.

Once `A - z I` is known to be boundedly invertible, the kernel computation from
`Krein/RankOneResolvent.lean` gives the standard eigenvector ansatz.

The intent is to isolate the purely algebraic part of Kapustin-style arguments:
all analytic work (showing the relevant resolvents exist and computing the scalar
condition) should be done separately.
-/

import Mathlib.Tactic
import KapustinFormalization.Krein.RankOneResolvent

namespace Krein

variable {𝕜 : Type*} [IsROrC 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

namespace FundamentalSymmetry

variable (K : FundamentalSymmetry 𝕜 E)

/-!
## The shift operator `A - zI`

We keep the definition bundled as a bounded operator to make rewriting robust.
-/

/-- The shifted operator `A - z • I`. -/
noncomputable def shift (A : E →L[𝕜] E) (z : 𝕜) : E →L[𝕜] E :=
  A - z • ContinuousLinearMap.id 𝕜 E

@[simp] lemma shift_apply (A : E →L[𝕜] E) (z : 𝕜) (x : E) :
    shift (K := K) A z x = A x - z • x := by
  simp [shift, ContinuousLinearMap.sub_apply]

/-- Eigenvalue equation as a kernel equation for the shifted perturbation. -/
lemma sub_rankOne_apply_eq_smul_iff_shift_sub_rankOne_apply_eq_zero
    (A : E →L[𝕜] E) (u v x : E) (z : 𝕜) :
    (A - rankOne (K := K) u v) x = z • x ↔
      (shift (K := K) A z - rankOne (K := K) u v) x = 0 := by
  constructor
  · intro hx
    -- Expand the shift; the goal is exactly `(T x) - z•x = 0`.
    have : (shift (K := K) A z - rankOne (K := K) u v) x
        = (A - rankOne (K := K) u v) x - z • x := by
      simp [shift, ContinuousLinearMap.sub_apply, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm, smul_add, add_smul]
    -- Substitute the eigenvalue equation.
    simp [this, hx]
  · intro hx
    -- Reverse the computation from the first implication.
    have : (shift (K := K) A z - rankOne (K := K) u v) x
        = (A - rankOne (K := K) u v) x - z • x := by
      simp [shift, ContinuousLinearMap.sub_apply, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm, smul_add, add_smul]
    -- From `T x - z•x = 0`, conclude `T x = z•x`.
    have h' : (A - rankOne (K := K) u v) x - z • x = 0 := by
      simpa [this] using hx
    -- `a - b = 0` implies `a = b`.
    simpa [sub_eq_zero] using h'

/-!
## Eigenvector ansatz on the resolvent set

We assume a boundedly invertible realization of `A - zI` as a `ContinuousLinearEquiv`.
This avoids any commitment to a particular characterization of the resolvent set.
-/

/-- If `A - zI` is boundedly invertible and `x` satisfies
`(A - |u⟩⟨v|) x = z • x`, then `x` is colinear with `(A - zI)⁻¹ u`.

This is the standard rank-one eigenvector ansatz on the resolvent set of `A`.
-/
lemma eq_smul_symm_u_of_sub_rankOne_apply_eq_smul
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u v x : E)
    (hx : (A - rankOne (K := K) u v) x = z • x) :
    x = (⟪v, x⟫_𝕜) • (Az.symm u) := by
  -- Turn the eigenvalue equation into a kernel equation for `Az - |u⟩⟨v|`.
  have hx0 : (Az.toContinuousLinearMap - rankOne (K := K) u v) x = 0 := by
    -- Use the kernel characterization for the shifted operator.
    have : (shift (K := K) A z - rankOne (K := K) u v) x = 0 :=
      (sub_rankOne_apply_eq_smul_iff_shift_sub_rankOne_apply_eq_zero (K := K)
        (A := A) (u := u) (v := v) (x := x) (z := z)).1 hx
    -- Rewrite `shift A z` as `Az`.
    simpa [hAz] using this
  -- Apply the kernel ansatz from `RankOneResolvent`.
  exact eq_smul_symm_u_of_sub_rankOne_apply_eq_zero (K := K) (A := Az)
    (u := u) (v := v) (x := x) hx0

/-- If `A - zI` is boundedly invertible and the scalar condition
`⟪v, (A - zI)⁻¹ u⟫ = 1` holds, then `(A - zI)⁻¹ u` is an eigenvector of
`A - |u⟩⟨v|` with eigenvalue `z`.
-/
lemma sub_rankOne_apply_symm_u_eq_smul
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u v : E)
    (h : ⟪v, Az.symm u⟫_𝕜 = 1) :
    (A - rankOne (K := K) u v) (Az.symm u) = z • (Az.symm u) := by
  -- Kernel statement for `Az - |u⟩⟨v|` at the candidate vector.
  have hk0 : (Az.toContinuousLinearMap - rankOne (K := K) u v) (Az.symm u) = 0 := by
    simpa using (sub_rankOne_apply_symm_u_eq_zero (K := K) (A := Az) (u := u) (v := v) h)

  -- Rewrite `Az` as `A - zI` and rearrange.
  -- From
  --   (A - zI - |u⟩⟨v|) (Az⁻¹ u) = 0
  -- deduce
  --   (A - |u⟩⟨v|) (Az⁻¹ u) = z • (Az⁻¹ u).
  have hk : (shift (K := K) A z - rankOne (K := K) u v) (Az.symm u) = 0 := by
    simpa [hAz] using hk0
  -- Use the equivalence between the eigenvalue and kernel equations.
  exact (sub_rankOne_apply_eq_smul_iff_shift_sub_rankOne_apply_eq_zero (K := K)
    (A := A) (u := u) (v := v) (x := Az.symm u) (z := z)).2 hk

/-!
## The scalar condition is *forced* by a nontrivial eigenvector

On the resolvent set of `A`, the rank-one eigenvector ansatz gives

`x = ⟪v,x⟫ • (A - zI)⁻¹ u`.

Consequently, a nonzero eigenvector must satisfy `⟪v,x⟫ ≠ 0`, and cancelling this scalar after
taking inner products yields the *necessary* scalar condition `⟪v, (A - zI)⁻¹ u⟫ = 1`.

This is the algebraic heart of the “zeros ↔ eigenvalues” reduction in Kapustin’s constructions.
-/

lemma inner_ne_zero_of_sub_rankOne_apply_eq_smul
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u v x : E)
    (hx : (A - rankOne (K := K) u v) x = z • x)
    (hx0 : x ≠ 0) :
    ⟪v, x⟫_𝕜 ≠ 0 := by
  -- Use the eigenvector ansatz `x = ⟪v,x⟫ • (A-zI)⁻¹ u`.
  have hx' := eq_smul_symm_u_of_sub_rankOne_apply_eq_smul (K := K)
    (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := v) (x := x) hx
  intro hinner
  -- If `⟪v,x⟫ = 0`, then the ansatz forces `x = 0`.
  have : x = 0 := by
    simpa [hinner] using hx'
  exact hx0 this

lemma inner_symm_u_eq_one_of_sub_rankOne_apply_eq_smul
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u v x : E)
    (hx : (A - rankOne (K := K) u v) x = z • x)
    (hx0 : x ≠ 0) :
    ⟪v, Az.symm u⟫_𝕜 = 1 := by
  -- Let `α := ⟪v,x⟫`. The eigenvector ansatz gives `x = α • (A-zI)⁻¹ u`.
  have hx' := eq_smul_symm_u_of_sub_rankOne_apply_eq_smul (K := K)
    (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := v) (x := x) hx
  have hα : ⟪v, x⟫_𝕜 ≠ 0 :=
    inner_ne_zero_of_sub_rankOne_apply_eq_smul (K := K)
      (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := v) (x := x) hx hx0

  -- Take the inner product with `v` and cancel `α`.
  have hmul : (⟪v, x⟫_𝕜) * ⟪v, Az.symm u⟫_𝕜 = ⟪v, x⟫_𝕜 := by
    -- `⟪v, x⟫ = ⟪v, α•(Az.symm u)⟫ = α * ⟪v, Az.symm u⟫`.
    calc
      (⟪v, x⟫_𝕜) * ⟪v, Az.symm u⟫_𝕜
          = ⟪v, (⟪v, x⟫_𝕜) • (Az.symm u)⟫_𝕜 := by
              simp [inner_smul_right]
      _ = ⟪v, x⟫_𝕜 := by
              simpa [hx']

  -- Rearrange to `α * (⟪v, Az.symm u⟫ - 1) = 0` and use `α ≠ 0`.
  have hzero : (⟪v, x⟫_𝕜) * (⟪v, Az.symm u⟫_𝕜 - 1) = 0 := by
    -- From `α*β = α`, subtract `α`.
    have : (⟪v, x⟫_𝕜) * ⟪v, Az.symm u⟫_𝕜 - ⟪v, x⟫_𝕜 = 0 := by
      -- Replace the left product using `hmul`.
      simpa [hmul]
    -- Rewrite as `α*(β-1)=0`.
    simpa [mul_sub, mul_one, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

  have : ⟪v, Az.symm u⟫_𝕜 - 1 = 0 := (mul_eq_zero.mp hzero).resolve_left hα
  exact sub_eq_zero.mp this

/-!
## Eigenvalue existence is equivalent to the scalar condition (resolvent regime)

Under a resolvent hypothesis for `A - zI`, the rank-one perturbation

`T := A - |u⟩⟨v|`

has a nontrivial eigenvector with eigenvalue `z` if and only if

`⟪v, (A - zI)⁻¹ u⟫ = 1`.

This packages the forward/backward algebraic reductions into a single lemma.
-/

theorem exists_nonzero_eigenvector_sub_rankOne_iff_inner_eq_one
    (A : E →L[𝕜] E) (z : 𝕜)
    (Az : E ≃L[𝕜] E)
    (hAz : Az.toContinuousLinearMap = shift (K := K) A z)
    (u v : E) :
    (∃ x : E, x ≠ 0 ∧ (A - rankOne (K := K) u v) x = z • x)
      ↔ ⟪v, Az.symm u⟫_𝕜 = 1 := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    exact inner_symm_u_eq_one_of_sub_rankOne_apply_eq_smul (K := K)
      (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := v) (x := x) hx hx0
  · intro h
    refine ⟨Az.symm u, ?_, ?_⟩
    · -- Nontriviality follows from `⟪v, Az.symm u⟫ = 1`.
      intro h0
      have : (0 : 𝕜) = 1 := by
        simpa [h0] using h
      exact zero_ne_one this
    · exact sub_rankOne_apply_symm_u_eq_smul (K := K)
        (A := A) (z := z) (Az := Az) (hAz := hAz) (u := u) (v := v) h

/-!
## Eigenvector construction without invertibility

The resolvent-based ansatz is sufficient for *non-real* spectral parameters in Kapustin’s
applications, but the core HPO statements also cover parameters that lie on the (Hilbert)
continuous spectrum of the base multiplication operator.

At the bounded level, the eigenvector computation does **not** require invertibility of
`A - zI` if one can directly exhibit a vector `x` solving the inhomogeneous shifted equation

`(A - zI) x = u`.

This is exactly what happens in Kapustin’s analytic constructions: the would-be resolvent
`(a-λ)⁻¹` may fail to be essentially bounded, but the product `(a-λ)⁻¹ u` can still belong to
`L²` (typically because of cancellation at the singularities).

The lemma below isolates this purely algebraic mechanism.
-/

/-- **Rank-one eigenvector criterion without a resolvent hypothesis.**

Let `T := A - |u⟩⟨v|`. If `x` satisfies the *shift equation*

`(A - zI) x = u`

and the scalar normalization `⟪v, x⟫ = 1`, then `x` is an eigenvector of `T` with eigenvalue `z`.

No invertibility of `A - zI` is assumed.
-/
lemma sub_rankOne_apply_eq_smul_of_shift_apply_eq_u_of_inner_eq_one
    (A : E →L[𝕜] E) (z : 𝕜) (u v x : E)
    (hx : shift (K := K) A z x = u)
    (hinner : ⟪v, x⟫_𝕜 = 1) :
    (A - rankOne (K := K) u v) x = z • x := by
  -- Expand the shift equation to `A x - z•x = u`.
  have hx' : A x - z • x = u := by
    simpa [shift_apply (K := K) (A := A) (z := z) (x := x)] using hx
  -- Rearrange it to `A x = z•x + u`.
  have hAx : A x = z • x + u := by
    -- `a - b = c` implies `a = c + b`.
    have : A x = u + z • x := (sub_eq_iff_eq_add).1 hx'
    simpa [add_comm, add_left_comm, add_assoc] using this
  -- Now compute the rank-one perturbation at `x`.
  calc
    (A - rankOne (K := K) u v) x
        = A x - (⟪v, x⟫_𝕜) • u := by
            simp [ContinuousLinearMap.sub_apply, rankOne_apply]
    _ = (z • x + u) - (⟪v, x⟫_𝕜) • u := by
            simp [hAx]
    _ = z • x := by
            -- Use `⟪v,x⟫ = 1`.
            simp [hinner, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, add_smul]

end FundamentalSymmetry

end Krein
