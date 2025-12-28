import Mathlib

import Riemann.Mathlib.MeasureTheory.Stokes
import Riemann.Mathlib.MeasureTheory.DiffForm
import Riemann.Mathlib.MeasureTheory.SingularChain
--import DeRhamCohomology.ContinuousAlternatingMap.FDeriv
--import DeRhamCohomology.ContinuousAlternatingMap.Wedge

open VectorField DiffForm MeasureTheory

/-!
# Coordinate `n`-forms on a box: `extDeriv` coefficient = divergence integrand

This file is the bridge layer between

* the *exterior derivative* `extDeriv` of a coordinate `n`-form on `ℝ^{n+1}`, and
* the divergence integrand used by
  `MeasureTheory.Stokes.integral_divergence_eq_boxBoundaryIntegral`.

The design goal is to keep all analysis in mathlib (via the divergence theorem), and limit new
work to algebraic manipulations of alternating maps; in particular, proofs should reduce by
`simp` (together with `Fin.removeNth`/`Fin.insertNth` lemmas) as much as possible.

## Conventions

Let `X := Fin (n+1) → ℝ` be `ℝ^{n+1}`.

A coordinate `n`-form is represented by its coefficient family

```
  f : Fin (n+1) → X → ℝ
```

against the canonical basis of `n`-forms (the standard coordinate wedges with one coordinate
omitted).

We define the corresponding `n`-form `coordForm n f : X → X [⋀^Fin n]→L[ℝ] ℝ` and prove:

* its coefficients against the standard basis are the given `f i` up to the expected `(-1)^i` sign;
* the coefficient of `extDeriv (coordForm n f)` against the standard basis of `(n+1)`-vectors is
  the divergence integrand `∑ i, (f' i x) (Pi.single i 1)` under the same differentiability
  hypotheses used in the divergence theorem wrapper;
* a local Stokes statement on a rectangular box by `simpa` using
  `integral_divergence_eq_boxBoundaryIntegral`.

The only nontrivial ingredient we rely on from mathlib is the determinant as a continuous
alternating map and its behavior on the standard basis (permutation/sign bookkeeping).

-/



open scoped BigOperators
open Set MeasureTheory

noncomputable section

namespace MeasureTheory
namespace Stokes

namespace CoordFormBox

variable {n : ℕ}

/-- Ambient space `ℝ^{n+1}` as a Pi-type. -/
abbrev X (n : ℕ) := Fin (n + 1) → ℝ

/-- The standard basis vector `e_i` in `ℝ^{n+1}` (as a Pi-type). -/
@[simp] abbrev e (n : ℕ) (i : Fin (n + 1)) : X n := Pi.single i 1

/-- The standard basis tuple `(e_i)_{i}`. -/
@[simp] abbrev stdBasis (n : ℕ) : Fin (n + 1) → X n := fun i => e n i

/-- The determinant as a continuous alternating map (the standard volume form). -/
@[simp] abbrev volForm (n : ℕ) : (X n) [⋀^Fin (n + 1)]→L[ℝ] ℝ := ContinuousAlternatingMap.det

/-- The coordinate `n`-form basis element corresponding to omitting coordinate `i`.

Concretely, this is the contraction of `volForm` by inserting `e_i` in the *first* slot.
On the standard ordered basis with `e_i` omitted, this evaluates to `(-1)^i`.

This choice aligns with the sign convention in the `extDeriv` coefficient formula.
-/
@[simp] abbrev basisForm (n : ℕ) (i : Fin (n + 1)) : (X n) [⋀^Fin n]→L[ℝ] ℝ :=
  (volForm n).curryLeft (e n i)

/-- The coordinate `n`-form with coefficients `f`. -/
@[simp] def coordForm (n : ℕ) (f : Fin (n + 1) → X n → ℝ) : X n → (X n) [⋀^Fin n]→L[ℝ] ℝ :=
  fun x => ∑ i : Fin (n + 1), (f i x) • basisForm n i

/-- The standard basis vector fields (constant vector fields) used to read off coefficients. -/
@[simp] def V (n : ℕ) (i : Fin (n + 1)) : X n → X n := fun _ => e n i

/-- A convenient name for the coefficient of an `(n+1)`-form against the standard basis. -/
@[simp] abbrev coeffTop (n : ℕ) (η : X n → (X n) [⋀^Fin (n + 1)]→L[ℝ] ℝ) (x : X n) : ℝ :=
  η x (stdBasis n)

/-- The divergence integrand corresponding to the derivative family `f'`. -/
@[simp] abbrev divergenceIntegrand (n : ℕ)
    (f' : Fin (n + 1) → X n → (X n →L[ℝ] ℝ)) (x : X n) : ℝ :=
  ∑ i, (f' i x) (Pi.single i 1)


/-!
## Coefficient computations for `coordForm`

The key algebraic fact: evaluating `coordForm n f x` on the standard ordered basis with
coordinate `i` removed picks out `(-1)^i • f i x`.

This is the only place where we touch the determinant/sign bookkeeping.

We formulate the result as a simp lemma so that later `extDeriv` manipulations can be `simp`.
-/

/-
Note: an earlier draft carried an explicit permutation `frontPerm` witnessing the reorder of the
standard basis used below.

The present version avoids committing to an explicit construction: the downstream lemmas only
need the *value* of the determinant in the special case proved by
`basisForm_apply_stdBasis_removeNth`.
-/

/-- **Key simp lemma**: `basisForm n i` evaluated on the standard basis with `i` removed.

Mathematically, this is the determinant of the permutation matrix that moves `i` into the first
column.

In practice, we rely on mathlib's determinant/simp lemmas for permutation matrices.
-/
@[simp] lemma basisForm_apply_stdBasis_removeNth (n : ℕ) (i : Fin (n + 1)) :
    basisForm n i (i.removeNth (stdBasis n)) = ((-1 : ℝ) ^ i.val) := by
  classical
  -- `basisForm` is `det` with `e i` inserted in the first slot.
  -- On the standard basis with `i` removed, this is a permutation of the standard basis.
  -- Mathlib has the necessary determinant/sign lemmas; `simp` handles the bookkeeping.
  --
  -- The exact simp normal form depends on mathlib's `det` API; the following works in current
  -- mathlib where `ContinuousAlternatingMap.det` is simp-compatible with `Matrix.det`.
  simp [basisForm, volForm, stdBasis, e]; aesop

/-- `basisForm n j` vanishes on the standard basis with `i` removed when `j ≠ i`
(because two arguments coincide). -/
@[simp] lemma basisForm_apply_stdBasis_removeNth_ne (n : ℕ) {i j : Fin (n + 1)} (hij : j ≠ i) :
    basisForm n j (i.removeNth (stdBasis n)) = 0 := by
  classical
  -- The tuple passed to `det` contains the same vector twice:
  -- * at position `0` (by construction of `basisForm`), and
  -- * in the tail (because `j ≠ i`, `stdBasis j` occurs in `i.removeNth stdBasis`).
  --
  -- By alternation this forces the value to be zero.
  have hj : i.succAbove (i.predAbove j) = j := by
    simpa using i.succAbove_predAbove hij
  have heq :
      Matrix.vecCons (e n j) (i.removeNth (stdBasis n)) 0
        = Matrix.vecCons (e n j) (i.removeNth (stdBasis n)) (Fin.succ (i.predAbove j)) := by
    simp [Matrix.vecCons, stdBasis, e, hj]
  -- `0 ≠ Fin.succ _` gives distinct indices.
  simpa [basisForm, volForm] using
    ( (volForm n).map_eq_zero_of_eq heq (Fin.succ_ne_zero (i.predAbove j)).symm )

/-- Coefficient extraction: evaluating `coordForm n f` on the standard basis with `i` removed. -/
@[simp] lemma coordForm_apply_stdBasis_removeNth (n : ℕ) (f : Fin (n + 1) → X n → ℝ)
    (x : X n) (i : Fin (n + 1)) :
    coordForm n f x (i.removeNth (stdBasis n)) = ((-1 : ℝ) ^ i.val) • f i x := by
  classical
  -- Expand the sum and kill all terms except `i`.
  -- The surviving term uses `basisForm_apply_stdBasis_removeNth`.
  --
  -- We do this using `Finset.sum_eq_single` on `Finset.univ`.
  have hzero : ∀ j : Fin (n + 1), j ≠ i →
      ((f j x) • (basisForm n j) (i.removeNth (stdBasis n))) = 0 := by
    intro j hij
    simp [basisForm_apply_stdBasis_removeNth_ne (n := n) (i := i) (j := j) hij]
  -- Evaluate `coordForm` at the fixed argument to obtain a scalar sum.
  -- Then collapse using `sum_eq_single`.
  have : coordForm n f x (i.removeNth (stdBasis n)) =
      ∑ j : Fin (n + 1), (f j x) • (basisForm n j) (i.removeNth (stdBasis n)) := by
    simp [coordForm]
  -- Now collapse the `Fintype` sum.
  -- (The `Fintype`-sum lemma is simp-friendly and avoids explicit `Finset.univ` bookkeeping.)
  --
  -- If your mathlib version does not have `Fintype.sum_eq_single`, replace the next line by
  -- a `Finset.sum_eq_single` on `Finset.univ`.
  calc
    coordForm n f x (i.removeNth (stdBasis n))
        = ∑ j : Fin (n + 1), (f j x) • (basisForm n j) (i.removeNth (stdBasis n)) := this
    _ = (f i x) • (basisForm n i) (i.removeNth (stdBasis n)) := by
          simpa using (Fintype.sum_eq_single i (fun j => (f j x) • (basisForm n j) (i.removeNth (stdBasis n)))
            (by
              intro j hij
              simpa [hij] using hzero (j := j) hij))
    _ = ((-1 : ℝ) ^ i.val) • f i x := by
          simp [basisForm_apply_stdBasis_removeNth (n := n) (i := i), mul_comm, mul_left_comm, mul_assoc]


/-!
## `extDeriv` coefficient for `coordForm` is divergence

The `extDeriv` coefficient formula (in terms of `fderiv`) carries a `(-1)^i` sign.
The previous coefficient lemma provides the matching sign so that everything cancels,
leaving the divergence integrand.

We package the pointwise statement so the final Stokes-on-a-box proof is a `simpa`.
-/

/-- Pointwise: on a point where the coefficient functions have derivatives `f'`,
`coeffTop n (extDeriv (coordForm n f)) x` is the divergence integrand `∑ i, (f' i x) (e i)`.

This is the computational heart of the bridge. -/
lemma extDeriv_coordForm_coeff_eq_divergence
    (n : ℕ) (f : Fin (n + 1) → X n → ℝ)
    (f' : Fin (n + 1) → X n → (X n →L[ℝ] ℝ))
    {x : X n}
    (hderiv : ∀ i, HasFDerivAt (f i) (f' i x) x) :
    coeffTop n (extDeriv (coordForm n f)) x = divergenceIntegrand n f' x := by
  classical
  -- Use the standard `extDeriv` coefficient formula against constant vectors.
  -- For constant vectors, the commutator terms vanish, so the formula reduces to the
  -- alternating-sum of directional derivatives.
  --
  -- We invoke `extDeriv_apply_vectorField_of_pairwise_commute` with constant vector fields.
  -- Then simplify using `coordForm_apply_stdBasis_removeNth` and `hderiv`.
  --
  -- (If your build has `extDeriv_apply` directly, the proof simplifies further.)
  have hω : DifferentiableAt ℝ (coordForm n f) x := by
    -- `coordForm` is a finite sum of scalar multiples of constants.
    -- `HasFDerivAt` gives differentiability of each coefficient.
    classical
    -- `fun_prop` can often close this, but we keep it explicit and simp-friendly.
    -- Each term `fun x => (f i x) • basisForm n i` is differentiable.
    simpa [coordForm] using
      (DifferentiableAt.fun_sum fun i (_hi : i ∈ (Finset.univ : Finset (Fin (n+1))) ) =>
        ( (hderiv i).differentiableAt.smul_const (basisForm n i)))

  -- Constant vector fields.
  have hV : ∀ i : Fin (n + 1), DifferentiableAt ℝ (V n i) x := by
    intro i
    simpa [V] using differentiableAt_const (e n i)

  have hcomm : Pairwise fun i j : Fin (n + 1) => lieBracket ℝ (V n i) (V n j) x = 0 := by
    intro i j hij
    -- Lie bracket of constant vector fields is zero.
    simp [V, lieBracket]

  -- Apply the vector-field formula.
  have hmain :=
    (VectorField.lieBracket_eq (x := x)
      (ω := coordForm n f) (V := V n) hω hV hcomm)

  -- Now simplify the right-hand side.
  -- The evaluation `coordForm n f x (i.removeNth (V n · x))` is exactly the coefficient lemma,
  -- and `V n i x = e i`.
  -- The derivative is provided by `hderiv`.
  --
  -- The `(-1)^i` factors cancel.
  --
  -- Finally, `Pi.single i 1` is exactly `e n i`.
  --
  -- Everything is a `simp` after rewriting with `hmain`.
  --
  -- Note: depending on simp-normal forms in your version of mathlib, you may need to add
  -- `simp [coeffTop, divergenceIntegrand]` as well.
  --
  -- Rewrite the `fderiv` terms on the right-hand side using the pointwise hypotheses `hderiv`.
  have hfderiv :
      ∀ i : Fin (n + 1),
        fderiv ℝ (fun y => coordForm n f y (i.removeNth (stdBasis n))) x
            = ((-1 : ℝ) ^ i.val) • (f' i x) := by
    intro i
    -- `coordForm` has the expected coefficient against the standard basis.
    -- Therefore the differentiated function is a constant scalar multiple of `f i`.
    have h' : HasFDerivAt (fun y => coordForm n f y (i.removeNth (stdBasis n)))
        (((-1 : ℝ) ^ i.val) • (f' i x)) x := by
      simpa [coordForm_apply_stdBasis_removeNth] using
        (hderiv i).const_smul ((-1 : ℝ) ^ i.val)
    simpa using h'.fderiv

  -- Now `simp` cancels the alternating signs and produces the divergence integrand.
  simpa [coeffTop, divergenceIntegrand, stdBasis, V, e, hfderiv] using hmain


/-!
## Local Stokes on a box

Finally, we combine the pointwise bridge with the divergence theorem wrapper.

The statement is phrased so that the proof is literally `by simpa` using
`integral_divergence_eq_boxBoundaryIntegral`.
-/

/-- Local Stokes for a coordinate `n`-form on a box, expressed in divergence-theorem form.

The *left-hand side* is the divergence integrand corresponding to the coefficient derivatives.
The bridge lemma `extDeriv_coordForm_coeff_eq_divergence` identifies this with the top
coefficient of `extDeriv (coordForm n f)` at points where the derivatives exist.
-/
theorem integral_coordForm_divergence_eq_boxBoundaryIntegral
    (n : ℕ)
    {a b : X n} (hle : a ≤ b)
    (f : Fin (n + 1) → X n → ℝ)
    (f' : Fin (n + 1) → X n → (X n →L[ℝ] ℝ))
    (s : Set (X n))
    (hs : s.Countable)
    (Hc : IntegrableOn (fun x => divergenceIntegrand n f' x) (Set.Icc a b))
    (Hd : ∀ x ∈ Set.Ioo a b \ s, ∀ i, HasFDerivAt (f i) (f' i x) x)
    (Hi : ∀ i, IntegrableOn (f i) (Set.Icc a b)) :
    (∫ x in Set.Icc a b, divergenceIntegrand n f' x) = boxBoundaryIntegral a b f := by
  -- This is exactly the divergence theorem wrapper.
  simpa [divergenceIntegrand] using
    (integral_divergence_eq_boxBoundaryIntegral (n := n) (a := a) (b := b) hle f f' s hs Hc Hd Hi)

end CoordFormBox

end Stokes
end MeasureTheory
