/-

! This file is intended as infrastructure for Carathéodory–Fejér type theorems.
-/
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Int.Basic

/-!
# Toeplitz matrices

A matrix `M : Matrix (Fin n) (Fin n) α` is *Toeplitz* if its entries are constant along diagonals,
i.e. depend only on the integer offset `j - i`.

We deliberately define offsets in `ℤ` (via coercions `Fin n → ℤ`) rather than using `Fin n`'s
arithmetic, to avoid any modular behavior.

## Main definitions
* `Matrix.diagOffset i j : ℤ` is the offset `j - i` for `i j : Fin n`.
* `Matrix.IsToeplitz M` means entries depend only on this offset.
* `Matrix.toeplitz c` builds the Toeplitz matrix with coefficients `c : ℤ → α`.

## Basic API
We provide:
* `isToeplitz_toeplitz : IsToeplitz (toeplitz c)`;
* closure under entrywise maps, addition, scalar multiplication;
* closure under transpose and conjugate-transpose;
* a noncomputable `toeplitzSeq` and `IsToeplitz_iff_exists_toeplitz`.
-/

namespace Matrix

open scoped BigOperators

section Basic

variable {α : Type*} {n : ℕ}

/-- The integer diagonal offset `j - i` for indices `i j : Fin n`. -/
def diagOffset (i j : Fin n) : ℤ :=
  (j : ℤ) - (i : ℤ)

@[simp] lemma diagOffset_self (i : Fin n) : diagOffset i i = 0 := by
  simp [diagOffset]

lemma diagOffset_swap (i j : Fin n) : diagOffset j i = - diagOffset i j := by
  -- `simp` uses `neg_sub` in `ℤ`.
  simp [diagOffset, sub_eq_add_neg]

/-- A matrix is Toeplitz if its entries depend only on the diagonal offset `j - i`. -/
def IsToeplitz (M : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ ⦃i j k l : Fin n⦄, diagOffset i j = diagOffset k l → M i j = M k l

/-- Construct a Toeplitz matrix from a bi-infinite sequence of diagonal coefficients. -/
def toeplitz (c : ℤ → α) : Matrix (Fin n) (Fin n) α :=
  fun i j => c (diagOffset i j)

@[simp] lemma toeplitz_apply (c : ℤ → α) (i j : Fin n) :
    toeplitz (n := n) c i j = c (diagOffset i j) := rfl

lemma isToeplitz_toeplitz (c : ℤ → α) : IsToeplitz (n := n) (toeplitz (n := n) c) := by
  intro i j k l h
  simp [toeplitz, h]

lemma IsToeplitz.eq_of_diagOffset_eq {M : Matrix (Fin n) (Fin n) α} (hM : IsToeplitz (n := n) M)
    {i j k l : Fin n} (h : diagOffset i j = diagOffset k l) :
    M i j = M k l :=
  hM h

lemma IsToeplitz.diagonal_eq {M : Matrix (Fin n) (Fin n) α} (hM : IsToeplitz (n := n) M)
    (i j : Fin n) : M i i = M j j := by
  refine hM ?_
  simp [diagOffset]

end Basic

section Pointwise

variable {α : Type*} {n : ℕ}
variable {M N : Matrix (Fin n) (Fin n) α}

/-- Toeplitz-ness is preserved by entrywise maps. -/
lemma IsToeplitz.map {β : Type*} (f : α → β) (hM : IsToeplitz (n := n) M) :
    IsToeplitz (n := n) (M.map f) := by
  intro i j k l h
  -- goal: f (M i j) = f (M k l)
  simpa [Matrix.map] using congrArg f (hM h)

lemma isToeplitz_zero [Zero α] : IsToeplitz (n := n) (0 : Matrix (Fin n) (Fin n) α) := by
  intro i j k l h
  simp

lemma IsToeplitz.add [Add α] (hM : IsToeplitz (n := n) M) (hN : IsToeplitz (n := n) N) :
    IsToeplitz (n := n) (M + N) := by
  intro i j k l h
  -- pointwise addition
  change M i j + N i j = M k l + N k l
  simpa using (by simp [hM h, hN h])

lemma IsToeplitz.smul {R : Type*} [SMul R α] (r : R) (hM : IsToeplitz (n := n) M) :
    IsToeplitz (n := n) (r • M) := by
  intro i j k l h
  -- pointwise scalar action
  change r • M i j = r • M k l
  simpa using congrArg (fun x => r • x) (hM h)

lemma IsToeplitz.transpose (hM : IsToeplitz (n := n) M) :
    IsToeplitz (n := n) M.transpose := by
  intro i j k l h
  -- Need: M j i = M l k.
  have h' : diagOffset j i = diagOffset l k := by
    -- `diagOffset j i = -diagOffset i j`, similarly for `l k`.
    calc
      diagOffset j i = - diagOffset i j := diagOffset_swap (i := i) (j := j)
      _ = - diagOffset k l := by simp [h]
      _ = diagOffset l k := by
        simp [diagOffset_swap (i := k) (j := l)]
  -- unfold transpose
  simpa [Matrix.transpose] using hM (i := j) (j := i) (k := l) (l := k) h'

lemma IsToeplitz.conjTranspose [Star α] (hM : IsToeplitz (n := n) M) :
    IsToeplitz (n := n) Mᴴ := by
  intro i j k l h
  -- Need: star (M j i) = star (M l k).
  have h' : diagOffset j i = diagOffset l k := by
    calc
      diagOffset j i = - diagOffset i j := diagOffset_swap (i := i) (j := j)
      _ = - diagOffset k l := by simp [h]
      _ = diagOffset l k := by
        simp [diagOffset_swap (i := k) (j := l)]
  -- unfold conjTranspose
  simpa [Matrix.conjTranspose] using congrArg star (hM (i := j) (j := i) (k := l) (l := k) h')

end Pointwise

section ChooseCoeffs

variable {α : Type*} {n : ℕ} [Inhabited α]

/--
A noncomputable “coefficient function” for a Toeplitz matrix.
Values away from the range of `diagOffset` are irrelevant.
-/
noncomputable def toeplitzSeq (M : Matrix (Fin n) (Fin n) α) : ℤ → α :=
  fun z =>
    if h : ∃ i j : Fin n, diagOffset i j = z then
      M (Classical.choose h) (Classical.choose (Classical.choose_spec h))
    else
      default

lemma toeplitz_toeplitzSeq {M : Matrix (Fin n) (Fin n) α} (hM : IsToeplitz (n := n) M) :
    toeplitz (n := n) (toeplitzSeq (n := n) M) = M := by
  classical
  ext i j
  -- Let `h` witness that the offset `diagOffset i j` occurs.
  have h : ∃ a b : Fin n, diagOffset a b = diagOffset i j := ⟨i, j, rfl⟩
  -- Unfold `toeplitz` and `toeplitzSeq` at this offset.
  -- The chosen pair `(choose h, choose (choose_spec h))` has the same offset as `(i,j)`.
  set a0 : Fin n := Classical.choose h
  set b0 : Fin n := Classical.choose (Classical.choose_spec h)
  have hab : diagOffset a0 b0 = diagOffset i j := by
    subst a0 b0
    exact Classical.choose_spec (Classical.choose_spec h)
  have hMb : M a0 b0 = M i j := hM hab
  have hSeq : toeplitzSeq (n := n) M (diagOffset i j) = M a0 b0 := by
    subst a0 b0
    -- `simp` selects the `if_pos` branch and reduces to the matrix entry at the chosen indices.
    simp [toeplitzSeq, h]
  -- Conclude.
  calc
    toeplitz (n := n) (toeplitzSeq (n := n) M) i j
        = toeplitzSeq (n := n) M (diagOffset i j) := rfl
    _ = M a0 b0 := hSeq
    _ = M i j := hMb

/-- A matrix is Toeplitz iff it is `toeplitz c` for some coefficient function `c : ℤ → α`. -/
theorem IsToeplitz_iff_exists_toeplitz (M : Matrix (Fin n) (Fin n) α) :
    IsToeplitz (n := n) M ↔ ∃ c : ℤ → α, M = toeplitz (n := n) c := by
  constructor
  · intro hM
    refine ⟨toeplitzSeq (n := n) M, (toeplitz_toeplitzSeq (n := n) (M := M) hM).symm⟩
  · rintro ⟨c, rfl⟩
    exact isToeplitz_toeplitz (n := n) c

end ChooseCoeffs

end Matrix
