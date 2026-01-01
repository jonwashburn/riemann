/-
  TwoChart_ParametrixTotalDegree

  Next symbolic step after `TwoChart_ParametrixTrunc`.

  Paper correspondence: Lemma 2.3 (interior pseudodifferential chart), Step 2.

  The file `TwoChart_ParametrixCancellation` establishes the *formal coefficient
  cancellations* implied by the parametrix recursion. In the paper, one then
  applies the Moyal expansion to the truncated symbol

      b_N := \sum_{j=0}^{N-1} h^j b_j

  and regroups terms by the **total power of h**.

  To model this regrouping in a principled way, we introduce a *truncated* Moyal
  coefficient operator `moyalCoeffTrunc a b N j`: it matches the usual
  coefficient `moyalCoeff a b j`, except that any term requiring an index `b k`
  with `k ≥ N` is dropped.

  This is precisely the bookkeeping step needed to identify the first nontrivial
  remainder coefficient at total order `N` as

      \sum_{n=1..N} P_n(a, b_{N-n}),

  i.e. the explicit remainder symbol already isolated in
  `TwoChart_ParametrixRemainderSymbol`.

  This file is purely symbolic: it does not assume the operator-level Moyal
  remainder theorem yet.  It supplies the exact coefficient identity which will
  later be combined with the analytic Moyal remainder bounds.
-/

import Riemann.Semiclassical.TwoChart_ParametrixCancellation
import Riemann.Semiclassical.TwoChart_ParametrixRemainderSymbol

import Mathlib.Tactic

open scoped BigOperators

namespace TwoChartEgorov

noncomputable section

/-- Total-degree Moyal coefficient for the product with a **truncated** series.

This is the same as `moyalCoeff a b j`, except we drop any contribution that would
use an index `b k` with `k ≥ N`. Concretely, the only such contribution at total
degree `j` is the `n=0` term when `j = N`, which would involve `b N` (absent from
`bTrunc b N`).

We formalize this by inserting the guard `j-n < N`.
-/
def moyalCoeffTrunc
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (N j : ℕ) : (ℝ → ℝ → ℝ → ℂ) :=
  fun h t τ =>
    ∑ n ∈ Finset.Icc 0 j,
      if (j - n) < N then Pn n a (b (j - n)) h t τ else (0 : ℂ)

/-- For degrees `j < N`, truncation has no effect: `moyalCoeffTrunc = moyalCoeff`. -/
lemma moyalCoeffTrunc_eq_moyalCoeff_of_lt
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    {N j : ℕ} (hj : j < N) :
    moyalCoeffTrunc a b N j = moyalCoeff a b j := by
  funext h t τ
  -- For every `n ≤ j`, we have `j-n ≤ j < N`, so the `if`-guard is always true.
  have hguard : ∀ n ∈ Finset.Icc 0 j, (j - n) < N := by
    intro n hn
    have hle : j - n ≤ j := Nat.sub_le _ _
    exact lt_of_le_of_lt hle hj
  -- Rewrite termwise using the guard.
  refine (Finset.sum_congr rfl ?_)
  intro n hn
  have : (j - n) < N := hguard n hn
  simp [this]

/-- At the first omitted total degree `N`, the coefficient is exactly the explicit remainder symbol
`∑_{n=1..N} Pn n a (b (N-n))`.

This is the symbolic content behind the appearance of the remainder symbol in the paper’s
identity (2.12).
-/
lemma moyalCoeffTrunc_at_N_eq_remainderSymbol
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (N : ℕ) :
    moyalCoeffTrunc a b N N = remainderSymbol a b N := by
  classical
  cases N with
  | zero =>
      funext h t τ
      simp [moyalCoeffTrunc, remainderSymbol]
  | succ N' =>
      -- Write `N = N'+1`.
      funext h t τ
      have hsplit : Finset.Icc 0 (N' + 1) = Finset.insert 0 (Finset.Icc 1 (N' + 1)) :=
        Icc_zero_succ_eq_insert (j := N')
      have h0not : (0 : ℕ) ∉ Finset.Icc 1 (N' + 1) := by
        simp [Finset.mem_Icc]
      -- Simplify the `if`-guard on `Icc 1 (N'+1)` (it is always true there).
      have hcond : ∀ n ∈ Finset.Icc 1 (N' + 1), (N' + 1 - n) < (N' + 1) := by
        intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
        have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ 0) hn1
        exact Nat.sub_lt_self (Nat.succ_pos N') hnpos
      have hsum :
          (∑ n ∈ Finset.Icc 1 (N' + 1),
              if (N' + 1 - n) < (N' + 1) then Pn n a (b (N' + 1 - n)) h t τ else 0)
            = ∑ n ∈ Finset.Icc 1 (N' + 1), Pn n a (b (N' + 1 - n)) h t τ := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        have : (N' + 1 - n) < (N' + 1) := hcond n hn
        simp [this]
      -- Put everything together.
      simp [moyalCoeffTrunc, remainderSymbol, hsplit]

/-- Total-degree truncated series built from `moyalCoeffTrunc`. -/
def moyalSeriesTruncTrunc
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (N : ℕ) : (ℝ → ℝ → ℝ → ℂ) :=
  fun h t τ => ∑ j ∈ Finset.range N, (h ^ j : ℂ) * moyalCoeffTrunc a b N j h t τ

/-- The truncated series built from `moyalCoeffTrunc` equals the standard truncated series from
`TwoChart_ParametrixCancellation` (since for every `j ∈ range N` we have `j < N`). -/
lemma moyalSeriesTruncTrunc_eq_moyalSeriesTrunc
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (N : ℕ) :
    moyalSeriesTruncTrunc a b N = moyalSeriesTrunc a b N := by
  funext h t τ
  refine (Finset.sum_congr rfl ?_)
  intro j hj
  have hjlt : j < N := Finset.mem_range.1 hj
  have hcoeff :
      moyalCoeffTrunc a b N j h t τ = moyalCoeff a b j h t τ := by
    exact congrArg (fun f => f h t τ) (moyalCoeffTrunc_eq_moyalCoeff_of_lt (a := a) (b := b) (N := N) hjlt)
  simp [hcoeff]

/-- Exact cancellation of total-degree coefficients `< N` for the truncated series.

This is the same cancellation statement as `moyalSeriesTrunc_eq_one`, but expressed in terms of
the truncated coefficient operator `moyalCoeffTrunc`, which is the correct bookkeeping for the
symbol `bTrunc b N = ∑_{j=0}^{N-1} h^j b_j`.
-/
theorem moyalSeriesTruncTrunc_eq_one
    {a b0 : ℝ → ℝ → ℝ → ℂ}
    {b : ℕ → (ℝ → ℝ → ℝ → ℂ)}
    (hInv : ∀ h t τ, a h t τ * b0 h t τ = (1 : ℂ))
    (hRec : ParametrixRec a b0 b)
    {N : ℕ} (hN : 1 ≤ N) :
    moyalSeriesTruncTrunc a b N = fun _ _ _ => (1 : ℂ) := by
  -- Reduce to the already-proved cancellation lemma.
  have := moyalSeriesTrunc_eq_one (a := a) (b0 := b0) (b := b) hInv hRec (N := N) hN
  simpa [moyalSeriesTruncTrunc_eq_moyalSeriesTrunc (a := a) (b := b) (N := N), moyalSeriesTruncTrunc] using this



/-- Total-degree truncated series including the first omitted degree `N`.

This is the polynomial obtained by collecting total `h`-powers `≤ N` in the formal
expansion of `a # (bTrunc b N)`.

It differs from `moyalSeriesTruncTrunc a b N` only by the additional `j = N` term.
-/
def moyalSeriesTruncTruncSucc
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (N : ℕ) : (ℝ → ℝ → ℝ → ℂ) :=
  fun h t τ => ∑ j ∈ Finset.range (N + 1), (h ^ j : ℂ) * moyalCoeffTrunc a b N j h t τ

/-- Explicit cancellation up to total degree `N-1`, with the first nontrivial term at degree `N`.

Under the inverse seed `a*b0 = 1` and the parametrix recursion, the total-degree polynomial
through degree `N` is

`1 + h^N · (∑_{n=1..N} Pn n a (b (N-n)))`.

This is the symbolic identity that the paper feeds into the analytic Moyal remainder theorem.
-/
theorem moyalSeriesTruncTruncSucc_eq_one_add_hpow_mul_remainderSymbol
    {a b0 : ℝ → ℝ → ℝ → ℂ}
    {b : ℕ → (ℝ → ℝ → ℝ → ℂ)}
    (hInv : ∀ h t τ, a h t τ * b0 h t τ = (1 : ℂ))
    (hRec : ParametrixRec a b0 b)
    {N : ℕ} (hN : 1 ≤ N) :
    moyalSeriesTruncTruncSucc a b N =
      fun h t τ => (1 : ℂ) + (h ^ N : ℂ) * remainderSymbol a b N h t τ := by
  classical
  funext h t τ
  -- Let `f j` denote the `j`th term in the total-degree polynomial.
  let f : ℕ → ℂ := fun j => (h ^ j : ℂ) * moyalCoeffTrunc a b N j h t τ
  have hsum : (∑ j ∈ Finset.range (N + 1), f j) = (∑ j ∈ Finset.range N, f j) + f N := by
    simpa using (Finset.sum_range_succ (f := f) N)
  have hcancel : (∑ j ∈ Finset.range N, f j) = (1 : ℂ) := by
    -- `∑_{j < N} f j = moyalSeriesTruncTrunc a b N`, which cancels to `1`.
    have hc :=
      congrArg (fun g => g h t τ)
        (moyalSeriesTruncTrunc_eq_one (a := a) (b0 := b0) (b := b) hInv hRec (N := N) hN)
    simpa [moyalSeriesTruncTrunc, f] using hc
  have hremainder : f N = (h ^ N : ℂ) * remainderSymbol a b N h t τ := by
    have hcoeff :=
      congrArg (fun g => g h t τ) (moyalCoeffTrunc_at_N_eq_remainderSymbol (a := a) (b := b) N)
    simpa [f, hcoeff]
  -- Conclude.
  calc
    moyalSeriesTruncTruncSucc a b N h t τ
        = (∑ j ∈ Finset.range (N + 1), f j) := by
            simp [moyalSeriesTruncTruncSucc, f]
    _ = (∑ j ∈ Finset.range N, f j) + f N := by simpa using hsum
    _ = (1 : ℂ) + (h ^ N : ℂ) * remainderSymbol a b N h t τ := by
            simpa [hcancel, hremainder, add_assoc]

end
end TwoChartEgorov
