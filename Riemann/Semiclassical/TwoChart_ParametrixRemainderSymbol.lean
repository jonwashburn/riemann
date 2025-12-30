/-
  TwoChart_ParametrixRemainderSymbol

  Continuation after `TwoChart_ParametrixCancellation`.

  Paper correspondence: the symbol `r_{N,h}(z)` appearing in (2.12), i.e.

      a_{h,z} # b_{N,h}(z) = 1 + h^N r_{N,h}(z),

  after canceling the coefficients of `h^j` for `1 ≤ j ≤ N-1`.

  In the paper, `r_{N,h}(z)` arises from the Moyal Taylor remainder and is shown
  to belong to `S^{-N}_λ`.  In the present formalization layer we isolate the
  purely symbolic part of that statement: we package an explicit finite
  combination of `P_n`-terms that has the correct order `-N`, and we prove that
  it is indeed a λ-dependent symbol of order `-N`.

  This is the exact lemma needed later when we specialize the general Weyl
  kernel estimate/Schur test to the parametrix remainder symbol.
-/

import Riemann.Semiclassical.TwoChart_ParametrixRecursion


open scoped BigOperators

namespace TwoChartEgorov

noncomputable section

/-- The explicit finite Moyal combination with total order `-N`:

`∑_{n=1}^N P_n(a, b_{N-n})`.

This is the natural symbolic candidate for the remainder symbol of order `N`.
It is a genuine symbol family (depends on `h`) and can be estimated in `S^{-N}_λ`
using only the already-formalized mapping properties of `P_n`.
-/
def remainderSymbol
    (a : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (N : ℕ) : (ℝ → ℝ → ℝ → ℂ) :=
  fun h t τ => ∑ n ∈ Finset.Icc 1 N, Pn n a (b (N - n)) h t τ

namespace remainderSymbol

variable {Y : Set ℝ} {h0 : ℝ} {m : ℝ}
variable {a b0 : ℝ → ℝ → ℝ → ℂ}
variable {b : ℕ → (ℝ → ℝ → ℝ → ℂ)}

/-- Symbol-class estimate for the remainder symbol.

Assumptions:
* `a ∈ S^m_λ`, and has commuting mixed partials (`MixedComm a`),
* the coefficient family `b_j` satisfies `b_j ∈ S^{-m-j}_λ` with commuting mixed partials.

Then `∑_{n=1}^N P_n(a, b_{N-n}) ∈ S^{-N}_λ`.

This is the exact order bookkeeping used in the paper: `P_n` lowers order by `n`.
-/
theorem mem_SmLambda
    (hh0 : h0 ≤ 1)
    (ha : SmLambda Y h0 m a)
    (haComm : MixedComm a)
    (hb : ∀ j : ℕ, SmLambda Y h0 (-m - (j : ℝ)) (b j))
    (hbComm : ∀ j : ℕ, MixedComm (b j))
    (N : ℕ) :
    SmLambda Y h0 (-(N : ℝ)) (remainderSymbol a b N) := by
  classical

  -- Termwise membership: for each `n ∈ [1..N]`, we have
  -- `P_n(a, b_{N-n}) ∈ S^{m + (-m - (N-n)) - n}_λ = S^{-N}_λ`.
  have hterm :
      ∀ n ∈ Finset.Icc 1 N,
        SmLambda Y h0 (-(N : ℝ)) (fun h t τ => Pn n a (b (N - n)) h t τ) := by
    intro n hn
    have ha' : SmLambda Y h0 m a := ha
    have hb' : SmLambda Y h0 (-m - ((N - n : ℕ) : ℝ)) (b (N - n)) := hb (N - n)
    have hbComm' : MixedComm (b (N - n)) := hbComm (N - n)

    -- Apply the mapping property of `P_n`.
    have hPn : SmLambda Y h0 (m + (-m - ((N - n : ℕ) : ℝ)) - (n : ℝ)) (Pn n a (b (N - n))) :=
      Pn.mem_SmLambda (Y := Y) (h0 := h0) (m₁ := m) (m₂ := (-m - ((N - n : ℕ) : ℝ)))
        (c := a) (d := b (N - n))
        hh0 ha' haComm hb' hbComm' n

    -- Simplify the order:
    --   m + (-m - (N-n)) - n = -(N).
    have horder : m + (-m - ((N - n : ℕ) : ℝ)) - (n : ℝ) = -(N : ℝ) := by
      -- Note: `((N - n : ℕ) : ℝ) + (n : ℝ) = (N : ℝ)` because `n ≤ N`.
      have hn_le : n ≤ N := by
        -- `n ∈ Icc 1 N` implies `n ≤ N`.
        exact (Finset.mem_Icc.1 hn).2
      have hcast : ((N - n : ℕ) : ℝ) + (n : ℝ) = (N : ℝ) := by
        -- `N - n + n = N` when `n ≤ N`.
        have : (N - n) + n = N := Nat.sub_add_cancel hn_le
        exact_mod_cast this
      nlinarith [hcast]

    -- Conclude termwise.
    simpa [remainderSymbol, horder] using hPn

  -- Sum the finitely many terms.
  -- Each term has order `-N`, hence the sum does.
  simpa [remainderSymbol] using
    (SmLambda.sum (Y := Y) (h0 := h0) (m := (-(N : ℝ))) hh0 (s := Finset.Icc 1 N)
      (f := fun n => fun h t τ => Pn n a (b (N - n)) h t τ) hterm)

end remainderSymbol

end
end TwoChartEgorov
