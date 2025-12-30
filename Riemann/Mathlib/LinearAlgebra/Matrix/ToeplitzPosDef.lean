/-

# Positive (semi)definite Toeplitz matrices

This file provides basic lemmas relating Toeplitz matrices (as in PR 1) to
`Matrix.PosSemidef`/`Matrix.PosDef` and the standard Hermitian symmetry condition on the symbol
`c : ℤ → 𝕜`.

The key entry point is:

* `Matrix.isHermitian_toeplitz` : if `c (-k) = star (c k)` for all `k`, then `toeplitz c` is Hermitian.

These lemmas are designed to be used downstream for Carathéodory–Fejér–type structure theorems.
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Matrix.PosDef
import Riemann.Mathlib.LinearAlgebra.Matrix.Toeplitz

open scoped BigOperators
open scoped ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : ℕ}

local notation "ι" => Fin n

/-- Conjugate symmetry of a Toeplitz symbol. This is the condition ensuring the associated Toeplitz
matrix is Hermitian. -/
def ToeplitzSymm (c : ℤ → 𝕜) : Prop :=
  ∀ k : ℤ, c (-k) = star (c k)

@[simp] lemma toeplitzSymm_0 {c : ℤ → 𝕜} (hc : ToeplitzSymm c) : c 0 = star (c 0) := by
  simpa [ToeplitzSymm] using hc 0

omit [RCLike 𝕜] in
@[simp] lemma toeplitz_diag (c : ℤ → 𝕜) (i : ι) :
    toeplitz (n := n) c i i = c 0 := by
  simp [toeplitz_apply]

/-- Conjugate transpose of a Toeplitz matrix is Toeplitz with a transformed symbol. -/
theorem conjTranspose_toeplitz (c : ℤ → 𝕜) :
    (toeplitz (n := n) c).conjTranspose = toeplitz (n := n) (fun k => star (c (-k))) := by
  classical
  ext i j
  simp only [Matrix.conjTranspose_apply, toeplitz_apply]
  congr 1
  simp only [diagOffset, neg_sub]

/-- If a Toeplitz symbol satisfies `c (-k) = star (c k)`, the Toeplitz matrix is Hermitian. -/
theorem isHermitian_toeplitz {c : ℤ → 𝕜} (hc : ToeplitzSymm c) :
    (toeplitz (n := n) c).IsHermitian := by
  classical
  -- `IsHermitian` is `A = A.conjTranspose`.
  rw [IsHermitian, conjTranspose_toeplitz]
  ext i j
  simp only [toeplitz_apply]; grind only [ToeplitzSymm]

/-- A "local" symmetry statement extracted from hermitianity of `toeplitz c`. -/
theorem toeplitzSymmOn_diagOffset_of_isHermitian {c : ℤ → 𝕜}
    (h : (toeplitz (n := n) c).IsHermitian) (i j : ι) :
    c (-diagOffset (n := n) i j) = star (c (diagOffset (n := n) i j)) := by
  -- Read off the (i,j) coefficient of `A = Aᴴ`.
  have hij :
      c (diagOffset (n := n) i j) = star (c (diagOffset (n := n) j i)) := by
    have := congrArg (fun M => M i j) h
    simp only [Matrix.conjTranspose_apply, toeplitz_apply] at this
    exact this.symm
  -- Replace `diagOffset j i` by `- diagOffset i j` and star both sides.
  have hij' :
      c (diagOffset (n := n) i j) = star (c (-diagOffset (n := n) i j)) := by
    rw [diagOffset_swap] at hij
    simp; grind only [diagOffset_swap, starRingEnd_apply]
  have := congrArg star hij'
  -- `star (star _) = _`.
  simpa using this.symm

/-- For a Toeplitz matrix with globally symmetric symbol, `PosSemidef` reduces to the quadratic-form
inequality (as hermitianity is automatic). -/
theorem posSemidef_toeplitz_iff {c : ℤ → 𝕜} (hc : ToeplitzSymm c) :
    (toeplitz (n := n) c).PosSemidef ↔
      ∀ x : ι → 𝕜, 0 ≤ RCLike.re (star x ⬝ᵥ (toeplitz (n := n) c).mulVec x) := by
  constructor
  · intro h x
    exact h.re_dotProduct_nonneg x
  · intro h; try?
    exact ⟨isHermitian_toeplitz hc, fun x => h x⟩

/-- For a Toeplitz matrix with globally symmetric symbol, `PosDef` reduces to the strict
quadratic-form inequality (as hermitianity is automatic). -/
theorem posDef_toeplitz_iff {c : ℤ → 𝕜} (hc : ToeplitzSymm c) :
    (toeplitz (n := n) c).PosDef ↔
      ∀ x : ι → 𝕜, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (toeplitz (n := n) c).mulVec x) := by
  constructor
  · intro h
    exact h.pos
  · intro h
    exact ⟨isHermitian_toeplitz hc, h⟩

/-- Extract symbol symmetry on all diagonal offsets from positive semidefiniteness. -/
theorem toeplitzSymmOn_diagOffset_of_posSemidef {c : ℤ → 𝕜}
    (h : (toeplitz (n := n) c).PosSemidef) (i j : ι) :
    c (-diagOffset (n := n) i j) = star (c (diagOffset (n := n) i j)) := by
  exact toeplitzSymmOn_diagOffset_of_isHermitian (n := n) h.isHermitian i j

end Matrix
