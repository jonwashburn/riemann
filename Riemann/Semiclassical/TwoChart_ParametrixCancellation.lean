/-
  TwoChart_ParametrixCancellation

  Symbolic cancellation for the parametrix recursion.

  Paper correspondence: Lemma 2.3 (interior pseudodifferential chart), Step 2
  ("composition and remainder").

  The parametrix recursion (paper (2.8)) is designed so that, when one expands
  the Weyl product via the Moyal coefficients `P_n`, the coefficients of `h^j`
  cancel for every `j` with `1 ≤ j ≤ N-1`.

  This file formalizes that cancellation statement purely at the symbolic level.

  * We define the coefficient `moyalCoeff a b j` (the `h^j`-coefficient of
    `a # (\sum_k h^k b_k)` in the formal Moyal expansion).
  * We show that, under the pointwise inverse identity `a*b0 = 1` and the
    recursion `ParametrixRec a b0 b`, one has

        moyalCoeff a b 0 = 1
        moyalCoeff a b (j+1) = 0  for all j.

  In particular, all coefficients through order `N-1` cancel exactly.

  No placeholders and no additional axioms are introduced in this file.
-/

import Riemann.Semiclassical.TwoChart_ParametrixRecursion

import Mathlib

open scoped BigOperators

namespace TwoChartEgorov

noncomputable section

/-- The `h^j`-coefficient in the formal Moyal expansion of `a # (\sum_k h^k b_k)`.

Concretely, if `b` is the coefficient family, then the coefficient at order `j`
comes from summing `P_n(a, b_{j-n})` over `n = 0..j`.
-/
def moyalCoeff
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (j : ℕ) : (ℝ → ℝ → ℝ → ℂ) :=
  fun h t τ => ∑ n ∈ Finset.Icc 0 j, Pn n a (b (j - n)) h t τ

/-- The base Moyal coefficient is pointwise multiplication: `P_0(c,d) = c*d`. -/
lemma Pn_zero (c d : ℝ → ℝ → ℝ → ℂ) :
    Pn 0 c d = fun h t τ => c h t τ * d h t τ := by
  funext h t τ
  -- `range (0+1) = {0}` and all prefactors are `1`.
  simp [TwoChartEgorov.Pn, TwoChartEgorov.dtdτ]

/-- The coefficient at order `0` is `a*b_0`. -/
lemma moyalCoeff_zero
    (a : ℝ → ℝ → ℝ → ℂ) (b : ℕ → (ℝ → ℝ → ℝ → ℂ)) :
    moyalCoeff a b 0 = fun h t τ => a h t τ * b 0 h t τ := by
  funext h t τ
  simp [moyalCoeff, Pn_zero]

/-- Split `Icc 0 (j+1)` into the `0` element plus `Icc 1 (j+1)`.

This is a small finitary lemma that lets us isolate the `n=0` term in the sum defining
`moyalCoeff` at order `j+1`.
-/
lemma Icc_zero_succ_eq_insert (j : ℕ) :
    Finset.Icc 0 (j + 1) = insert 0 (Finset.Icc 1 (j + 1)) := by
  ext n
  by_cases hn0 : n = 0
  · subst hn0
    simp
  · have hn1 : 1 ≤ n := by
      -- `n ≠ 0` gives `0 < n`, hence `1 ≤ n`.
      exact Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hn0)
    -- Away from `0`, membership in `Icc 0 (j+1)` is equivalent to membership in
    -- `Icc 1 (j+1)`.
    simp [Finset.mem_Icc, hn0, hn1]

/-- Expand the order-`j+1` coefficient into the `n=0` term and the sum over `n ≥ 1`. -/
lemma moyalCoeff_succ_expand
    (a : ℝ → ℝ → ℝ → ℂ) (b : ℕ → (ℝ → ℝ → ℝ → ℂ)) (j : ℕ) :
    moyalCoeff a b (j + 1)
      = fun h t τ =>
          a h t τ * b (j + 1) h t τ
            + ∑ n ∈ Finset.Icc 1 (j + 1), Pn n a (b (j + 1 - n)) h t τ := by
  funext h t τ
  -- Split the sum by inserting `0`.
  have hsplit : Finset.Icc 0 (j + 1) = insert 0 (Finset.Icc 1 (j + 1)) :=
    Icc_zero_succ_eq_insert (j := j)
  -- `0 ∉ Icc 1 (j+1)`.
  have h0not : (0 : ℕ) ∉ Finset.Icc 1 (j + 1) := by
    simp [Finset.mem_Icc]
  -- Expand.
  simp [moyalCoeff, hsplit, Finset.sum_insert, h0not, Pn_zero]

/-- Main cancellation statement:

Assume:
* `a*b0 = 1` pointwise (this is the ellipticity/inverse seed of the paper), and
* `b` satisfies the parametrix recursion (2.8).

Then every higher Moyal coefficient vanishes: `moyalCoeff a b (j+1) = 0`.
-/
theorem moyalCoeff_succ_eq_zero
    {a b0 : ℝ → ℝ → ℝ → ℂ}
    {b : ℕ → (ℝ → ℝ → ℝ → ℂ)}
    (hInv : ∀ h t τ, a h t τ * b0 h t τ = (1 : ℂ))
    (hRec : ParametrixRec a b0 b) :
    ∀ j : ℕ, moyalCoeff a b (j + 1) = fun _ _ _ => (0 : ℂ) := by
  intro j
  funext h t τ
  -- Abbreviate the inner sum from the recursion.
  set S : ℂ := ∑ n ∈ Finset.Icc 1 (j + 1), Pn n a (b (j + 1 - n)) h t τ

  -- Evaluate the recursion formula for `b (j+1)`.
  have hb : b (j + 1) h t τ = (-1 : ℂ) * b0 h t τ * S := by
    -- `hRec.2 j` is an equality of functions; evaluate it at `h,t,τ`.
    have := congrArg (fun f => f h t τ) (hRec.2 j)
    -- Unfold `S`.
    simpa [S, mul_assoc, mul_left_comm, mul_comm] using this

  -- Expand the Moyal coefficient at order `j+1`.
  have hExp : moyalCoeff a b (j + 1) h t τ = a h t τ * b (j + 1) h t τ + S := by
    simpa [S] using
      congrArg (fun f => f h t τ) (moyalCoeff_succ_expand (a := a) (b := b) j)

  -- Reduce using `hb` and `a*b0 = 1`.
  have hab0 : a h t τ * b0 h t τ = (1 : ℂ) := hInv h t τ

  -- `a * b(j+1) = a * ((-1)*b0*S) = (-1) * (a*b0) * S = -S`, so `a*b(j+1) + S = 0`.
  calc
    moyalCoeff a b (j + 1) h t τ
        = a h t τ * b (j + 1) h t τ + S := hExp
    _ = a h t τ * ((-1 : ℂ) * b0 h t τ * S) + S := by
          simp [hb]
    _ = (-1 : ℂ) * (a h t τ * b0 h t τ) * S + S := by
          ring
    _ = (-1 : ℂ) * (1 : ℂ) * S + S := by
          simp [hab0]
    _ = (0 : ℂ) := by
          ring

/-- At order `0`, the coefficient equals `1` provided `b 0 = b0` and `a*b0 = 1`. -/
lemma moyalCoeff_zero_eq_one
    {a b0 : ℝ → ℝ → ℝ → ℂ}
    {b : ℕ → (ℝ → ℝ → ℝ → ℂ)}
    (hInv : ∀ h t τ, a h t τ * b0 h t τ = (1 : ℂ))
    (hRec : ParametrixRec a b0 b) :
    moyalCoeff a b 0 = fun _ _ _ => (1 : ℂ) := by
  funext h t τ
  have hb0 : b 0 h t τ = b0 h t τ := by
    -- `hRec.1` says `b 0 = b0`.
    simp [hRec.1]
  -- Use `moyalCoeff_zero` and the inverse identity.
  simp [moyalCoeff_zero, hb0, hInv h t τ]

/-- The truncated series of Moyal coefficients up to order `N-1`.

This is the polynomial that appears when one collects terms of total power `< N`
from the double expansion in `h`.
-/
def moyalSeriesTrunc
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (N : ℕ) : (ℝ → ℝ → ℝ → ℂ) :=
  fun h t τ => ∑ j ∈ Finset.range N, (h ^ j : ℂ) * moyalCoeff a b j h t τ

/-- Exact cancellation of all coefficients of order `h^j` for `1 ≤ j ≤ N-1`.

Under the inverse seed `a*b0 = 1` and the recursion, the truncated coefficient sum
reduces to the constant `1`.

This is the formal backbone behind the paper’s identity (2.12) (before inserting the
Moyal Taylor remainder at order `h^N`).
-/
theorem moyalSeriesTrunc_eq_one
    {a b0 : ℝ → ℝ → ℝ → ℂ}
    {b : ℕ → (ℝ → ℝ → ℝ → ℂ)}
    (hInv : ∀ h t τ, a h t τ * b0 h t τ = (1 : ℂ))
    (hRec : ParametrixRec a b0 b)
    {N : ℕ} (hN : 1 ≤ N) :
    moyalSeriesTrunc a b N = fun _ _ _ => (1 : ℂ) := by
  classical
  funext h t τ
  -- Isolate the `j=0` term in the finite sum.
  have h0mem : (0 : ℕ) ∈ Finset.range N := by
    -- `hN : 1 ≤ N` implies `0 < N`, hence `0 ∈ range N`.
    have : 0 < N := (Nat.succ_le_iff).1 hN
    simpa using (Finset.mem_range.2 this)

  -- Every `j ≠ 0` contributes `0` because `moyalCoeff a b j = 0` for `j ≥ 1`.
  have hzero : ∀ j ∈ Finset.range N, j ≠ 0 → (h ^ j : ℂ) * moyalCoeff a b j h t τ = 0 := by
    intro j hj hj0
    rcases Nat.exists_eq_succ_of_ne_zero hj0 with ⟨k, rfl⟩
    -- Evaluate `moyalCoeff_succ_eq_zero` at `k`.
    have hk : moyalCoeff a b (k + 1) h t τ = 0 := by
      simpa using congrArg (fun f => f h t τ) (moyalCoeff_succ_eq_zero (a:=a) (b0:=b0) (b:=b) hInv hRec k)
    simp [hk]

  -- Reduce the sum to the single term `j=0`.
  have hsum_single :
      (∑ j ∈ Finset.range N, (h ^ j : ℂ) * moyalCoeff a b j h t τ)
        = (h ^ (0 : ℕ) : ℂ) * moyalCoeff a b 0 h t τ := by
    refine
      Finset.sum_eq_single_of_mem (a := (0 : ℕ)) (s := Finset.range N)
        (f := fun j => (h ^ j : ℂ) * moyalCoeff a b j h t τ) ?_ ?_
    · -- `0 ∈ range N`.
      exact h0mem
    · -- Any other term vanishes.
      intro j hj hjne
      exact hzero j hj hjne

  -- Compute the `j=0` term: `h^0 * 1 = 1`.
  have hcoeff0 : moyalCoeff a b 0 h t τ = (1 : ℂ) := by
    simpa using congrArg (fun f => f h t τ) (moyalCoeff_zero_eq_one (a:=a) (b0:=b0) (b:=b) hInv hRec)

  -- Conclude.
  simp [moyalSeriesTrunc, hsum_single, hcoeff0]

end
end TwoChartEgorov
