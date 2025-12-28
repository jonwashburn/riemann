/-
Copyright (c) 2025
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import Riemann.Mathlib.LinearAlgebra.Matrix.Toeplitz
import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive (semi)definite Toeplitz matrices

This file provides the basic API connecting Toeplitz matrices to Hermitian-ness and
positive semidefiniteness/definiteness.

The key lemma is an explicit expansion of the quadratic form `xᴴ T x` for a Toeplitz matrix `T`,
and a convenient corollary that rewrites the `PosSemidef` inequality in “double-sum” form.

This is the matrix-analytic core used when relating positive Toeplitz matrices to positive
linear functionals on truncations of `C*(ℤ)` (cf. the discussion around Toeplitz matrices and
positive linear forms). :contentReference[oaicite:2]{index=2}
-/

open scoped BigOperators

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n m : ℕ}

/-- A coefficient function `c : ℤ → 𝕜` is *Toeplitz-Hermitian* if it is conjugate-symmetric. -/
def ToeplitzCoeffSymm (c : ℤ → 𝕜) : Prop :=
  ∀ k : ℤ, star (c (-k)) = c k

/-- Conjugate-transpose of a Toeplitz matrix corresponds to conjugate-symmetry of the coefficients. -/
@[simp] theorem conjTranspose_toeplitz (c : ℤ → 𝕜) :
    (toeplitz (n := n) c).conjTranspose = toeplitz (n := n) (fun k => star (c (-k))) := by
  ext i j
  -- `conjTranspose_apply` + the definition of `toeplitz` + `diagOffset` symmetry
  simp [toeplitz, diagOffset, sub_eq_neg_sub]

/-- Entrywise characterization of Hermitian Toeplitz matrices. -/
theorem isHermitian_toeplitz_iff (c : ℤ → 𝕜) :
    (toeplitz (n := n) c).IsHermitian ↔
      ∀ i j : Fin n, star (c (-diagOffset i j)) = c (diagOffset i j) := by
  constructor
  · intro h i j
    have h' : toeplitz (n := n) (fun k => star (c (-k))) = toeplitz (n := n) c := by
      simpa [Matrix.IsHermitian, conjTranspose_toeplitz] using (show
        (toeplitz (n := n) c).conjTranspose = toeplitz (n := n) c from h)
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M i j) h'
    simpa [toeplitz] using hij
  · intro h
    -- unfold `IsHermitian` and use the explicit formula for `conjTranspose` computed above
    show (toeplitz (n := n) c).conjTranspose = toeplitz (n := n) c
    ext i j
    -- rewrite the LHS using `conjTranspose_toeplitz` then apply `h`
    simpa [conjTranspose_toeplitz, toeplitz] using (h i j)

/-- A globally conjugate-symmetric coefficient function yields a Hermitian Toeplitz matrix (any size). -/
theorem isHermitian_toeplitz_of_coeffSymm {c : ℤ → 𝕜} (hc : ToeplitzCoeffSymm c) :
    (toeplitz (n := n) c).IsHermitian := by
  refine (isHermitian_toeplitz_iff (n := n) c).2 ?_
  intro i j
  simpa using hc (diagOffset i j)

/-- Compressing a Toeplitz matrix along `Fin.castLEEmb` gives the smaller Toeplitz matrix. -/
theorem toeplitz_submatrix_castLEEmb (hnm : n ≤ m) (c : ℤ → 𝕜) :
    (toeplitz (n := m) c).submatrix (Fin.castLEEmb hnm) (Fin.castLEEmb hnm)
      = toeplitz (n := n) c := by
  ext i j
  simp [toeplitz, diagOffset]

/-- “Order-`n` Toeplitz positivity”: the (finite) Toeplitz matrix is positive semidefinite. -/
def ToeplitzPosSemidef (c : ℤ → 𝕜) (n : ℕ) : Prop :=
  (toeplitz (n := n) c).PosSemidef

/-- Toeplitz positivity is monotone under truncation (principal compression). -/
theorem ToeplitzPosSemidef.of_le {c : ℤ → 𝕜} {m n : ℕ} (hnm : n ≤ m)
    (hm : ToeplitzPosSemidef c m) : ToeplitzPosSemidef c n := by
  classical
  -- `PosSemidef.submatrix` is in core matrix positivity API. :contentReference[oaicite:3]{index=3}
  have hsub :
      ((toeplitz (n := m) c).submatrix (Fin.castLEEmb hnm) (Fin.castLEEmb hnm)).PosSemidef :=
    Matrix.PosSemidef.submatrix (M := toeplitz (n := m) c) hm (Fin.castLEEmb hnm)
  -- identify the compressed matrix with the smaller Toeplitz matrix
  simpa [ToeplitzPosSemidef, toeplitz_submatrix_castLEEmb (n := n) (m := m) hnm c] using hsub

/-- Quadratic form expansion for Toeplitz matrices. -/
theorem star_dotProduct_mulVec_toeplitz (c : ℤ → 𝕜) (x : Fin n → 𝕜) :
    star x ⬝ᵥ (toeplitz (n := n) c).mulVec x
      = ∑ i : Fin n, ∑ j : Fin n, star (x i) * (c (diagOffset i j) * x j) := by
  classical
  -- expand `dotProduct` and `mulVec`
  simp [Matrix.dotProduct, Matrix.mulVec, toeplitz, Finset.mul_sum, mul_assoc]

/-- If a Toeplitz matrix is positive semidefinite, then the Toeplitz quadratic form has nonnegative real part. -/
theorem ToeplitzPosSemidef.re_quadraticForm_nonneg {c : ℤ → 𝕜} (h : ToeplitzPosSemidef c n)
    (x : Fin n → 𝕜) :
    0 ≤ RCLike.re (∑ i : Fin n, ∑ j : Fin n, star (x i) * (c (diagOffset i j) * x j)) := by
  -- `PosSemidef.re_dotProduct_nonneg` is provided by `Analysis.Matrix.PosDef`. :contentReference[oaicite:4]{index=4}
  simpa [ToeplitzPosSemidef, star_dotProduct_mulVec_toeplitz (n := n) c x] using
    (Matrix.PosSemidef.re_dotProduct_nonneg (M := toeplitz (n := n) c) h x)

end Matrix
