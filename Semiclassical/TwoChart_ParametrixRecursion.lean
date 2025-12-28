import TwoChart_Pn

import Mathlib.Tactic

open scoped BigOperators

namespace TwoChartEgorov

noncomputable section

/-- Coefficient recursion (paper (2.8)). -/
def ParametrixRec
    (a b0 : ℝ → ℝ → ℝ → ℂ)
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ)) : Prop :=
  b 0 = b0 ∧
    ∀ j : ℕ,
      b (j + 1) =
        (fun h t τ =>
          (-1 : ℂ) * b0 h t τ *
            (∑ n in Finset.Icc 1 (j + 1),
              TwoChartEgorov.Pn n a (b (j + 1 - n)) h t τ))

/-- Truncated parametrix symbol `b_N := Σ_{j=0}^{N-1} h^j b_j` (paper (2.7)). -/
def bTrunc
    (b : ℕ → (ℝ → ℝ → ℝ → ℂ))
    (N : ℕ) : (ℝ → ℝ → ℝ → ℂ) :=
  fun h t τ =>
    ∑ j in Finset.range N, (h ^ j : ℂ) * b j h t τ

namespace Parametrix

variable {Y : Set ℝ} {h0 : ℝ} {m : ℝ}
variable {a b0 : ℝ → ℝ → ℝ → ℂ}
variable {b : ℕ → (ℝ → ℝ → ℝ → ℂ)}

/--
Main bookkeeping statement: under the recursion (2.8), the coefficient `b_j` has order `-m-j`.

More precisely: assume

* `a ∈ S^m_λ`,
* `b0 ∈ S^{-m}_λ`,
* `b` satisfies the parametrix recursion with inputs `(a,b0)`,
* and we have commutation of mixed partials (`MixedComm`) for `a` and for each `b j`.

Then for every `j`, `b j ∈ S^{-m-j}_λ`.

This is the purely symbolic part of Lemma 2.3: it produces the full coefficient family with the
correct order drop, independently of the operator-level Moyal remainder.
-/
theorem coeff_mem_SmLambda
    (hh0 : h0 ≤ 1)
    (ha : TwoChartEgorov.SmLambda Y h0 m a)
    (haComm : TwoChartEgorov.MixedComm a)
    (hb0 : TwoChartEgorov.SmLambda Y h0 (-m) b0)
    (hbRec : TwoChartEgorov.ParametrixRec a b0 b)
    (hbComm : ∀ j : ℕ, TwoChartEgorov.MixedComm (b j)) :
    ∀ j : ℕ, TwoChartEgorov.SmLambda Y h0 (-m - (j : ℝ)) (b j) := by
  classical
  -- Strong induction because the recursion for `b (j+1)` uses all smaller indices.
  intro j
  refine Nat.strong_induction_on j ?_
  intro j ih
  cases j with
  | zero =>
      -- `b 0 = b0`.
      simpa [hbRec.1] using hb0
  | succ j' =>
      -- Use the recursion for `b (j'+1)`.
      have hrec : b (j' + 1) =
          (fun h t τ =>
            (-1 : ℂ) * b0 h t τ *
              (∑ n in Finset.Icc 1 (j' + 1),
                TwoChartEgorov.Pn n a (b (j' + 1 - n)) h t τ)) := by
        simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using (hbRec.2 j')

      -- First show that the inner sum has order `-(j'+1)`.
      have hsum : TwoChartEgorov.SmLambda Y h0 (-(j' + 1 : ℕ) : ℝ)
          (fun h t τ =>
            ∑ n in Finset.Icc 1 (j' + 1),
              TwoChartEgorov.Pn n a (b (j' + 1 - n)) h t τ) := by
        -- Termwise membership for each `n` in the Icc.
        have hterm :
            ∀ n ∈ Finset.Icc 1 (j' + 1),
              TwoChartEgorov.SmLambda Y h0 (-(j' + 1 : ℕ) : ℝ)
                (fun h t τ => TwoChartEgorov.Pn n a (b (j' + 1 - n)) h t τ) := by
          intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
          have hnj : n ≤ j' + 1 := (Finset.mem_Icc.1 hn).2
          -- `j'+1 - n < j'+1` since `1 ≤ n`.
          have hlt : j' + 1 - n < j' + 1 := by
            -- `Nat.sub_lt` expects positivity of the subtrahend.
            have hnpos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ 0) hn1
            exact Nat.sub_lt (Nat.succ_pos _) hnpos

          -- Apply the strong induction hypothesis to `k := j'+1-n`.
          have hbSmall : TwoChartEgorov.SmLambda Y h0 (-m - ((j' + 1 - n : ℕ) : ℝ))
              (b (j' + 1 - n)) := ih (j' + 1 - n) hlt

          -- Mapping law for `Pₙ`.
          have hPn : TwoChartEgorov.SmLambda Y h0 (m + (-m - ((j' + 1 - n : ℕ) : ℝ)) - (n : ℝ))
              (TwoChartEgorov.Pn n a (b (j' + 1 - n))) :=
            TwoChartEgorov.Pn.mem_SmLambda
              (Y:=Y) (h0:=h0) (m₁:=m) (m₂:= -m - ((j' + 1 - n : ℕ) : ℝ))
              (c:=a) (d:=b (j' + 1 - n))
              hh0 ha haComm hbSmall (hbComm (j' + 1 - n)) n

          -- Simplify the order to `-(j'+1)`.
          have horder : m + (-m - ((j' + 1 - n : ℕ) : ℝ)) - (n : ℝ) = (-(j' + 1 : ℕ) : ℝ) := by
            -- `m - m` cancels; remaining term is `-(j'+1-n) - n = -(j'+1)`.
            have hcast : ((j' + 1 - n : ℕ) : ℝ) + (n : ℝ) = (j' + 1 : ℝ) := by
              -- since `n ≤ j'+1`.
              exact_mod_cast (Nat.sub_add_cancel hnj)
            nlinarith [hcast]

          simpa [horder] using hPn

        -- Sum over `n` in `Icc`.
        simpa using
          (TwoChartEgorov.SmLambda.sum (Y:=Y) (h0:=h0) (m:= (-(j' + 1 : ℕ) : ℝ))
            hh0 (Finset.Icc 1 (j' + 1))
            (fun n => fun h t τ => TwoChartEgorov.Pn n a (b (j' + 1 - n)) h t τ)
            hterm)

      -- Multiply by `b0` (order `-m`) and the scalar `-1`.
      have hprod : TwoChartEgorov.SmLambda Y h0 ((-m) + (-(j' + 1 : ℕ) : ℝ))
          (fun h t τ => b0 h t τ *
            (∑ n in Finset.Icc 1 (j' + 1),
              TwoChartEgorov.Pn n a (b (j' + 1 - n)) h t τ)) := by
        simpa [mul_assoc] using
          (TwoChartEgorov.SmLambda.mul (Y:=Y) (h0:=h0)
            (m₁:= -m) (m₂:= (-(j' + 1 : ℕ) : ℝ))
            (a:=b0)
            (b:=fun h t τ =>
              ∑ n in Finset.Icc 1 (j' + 1),
                TwoChartEgorov.Pn n a (b (j' + 1 - n)) h t τ)
            hh0 hb0 hsum)

      have hneg : TwoChartEgorov.SmLambda Y h0 ((-m) + (-(j' + 1 : ℕ) : ℝ))
          (fun h t τ => (-1 : ℂ) * (b0 h t τ *
            (∑ n in Finset.Icc 1 (j' + 1),
              TwoChartEgorov.Pn n a (b (j' + 1 - n)) h t τ))) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (TwoChartEgorov.SmLambda.const_mul (Y:=Y) (h0:=h0)
            (m:= (-m) + (-(j' + 1 : ℕ) : ℝ))
            hh0 (-1 : ℂ) hprod)

      -- Conclude, rewriting the recursion formula.
      have hfinal : TwoChartEgorov.SmLambda Y h0 (-m - (j' + 1 : ℕ) : ℝ) (b (j' + 1)) := by
        -- `(-m) + (-(j'+1)) = -m - (j'+1)`.
        have harith : (-m) + (-(j' + 1 : ℕ) : ℝ) = (-m - (j' + 1 : ℕ) : ℝ) := by
          nlinarith
        -- match the exact RHS of the recursion
        simpa [hrec, harith, mul_assoc] using hneg

      -- Convert `j'+1` to the requested form `-m - ((Nat.succ j') : ℝ)`.
      simpa [Nat.succ_eq_add_one, add_assoc] using hfinal

end Parametrix

end

end TwoChartEgorov
