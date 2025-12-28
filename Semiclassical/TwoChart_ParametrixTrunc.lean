import TwoChart_ParametrixRecursion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators

namespace TwoChartEgorov

namespace SmLambda

variable {Y : Set ℝ} {h0 : ℝ}
variable {m₁ m₂ : ℝ}
variable {a : ℝ → ℝ → ℝ → ℂ}

/-- For a base `x ≥ 1`, the map `r ↦ x^r` is monotone in the exponent. -/
lemma rpow_le_rpow_of_one_le {x : ℝ} (hx : (1 : ℝ) ≤ x) {r s : ℝ} (hrs : r ≤ s) :
    x ^ r ≤ x ^ s := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hmul : r * Real.log x ≤ s * Real.log x :=
    mul_le_mul_of_nonneg_right hrs hxlog
  have hexp : Real.exp (r * Real.log x) ≤ Real.exp (s * Real.log x) :=
    (Real.exp_le_exp).2 hmul
  simpa [Real.rpow_def_of_pos hxpos] using hexp

/-- Order monotonicity: if `m₁ ≤ m₂` then `S^{m₁}_λ ⊆ S^{m₂}_λ`. -/
theorem mono_order (hm : m₁ ≤ m₂) (ha : SmLambda Y h0 m₁ a) : SmLambda Y h0 m₂ a := by
  classical
  intro α β
  rcases ha α β with ⟨C, M, hC, hbound⟩
  refine ⟨C, M, hC, ?_⟩
  intro h hh t ht τ
  have hmain := hbound (h:=h) hh (t:=t) ht τ
  have hwt : japaneseBracket τ ^ (m₁ - (β : ℝ)) ≤ japaneseBracket τ ^ (m₂ - (β : ℝ)) := by
    refine rpow_le_rpow_of_one_le (x := japaneseBracket τ) (one_le_japaneseBracket τ) ?_
    linarith
  have hfac : 0 ≤ C * (h⁻¹) ^ M := by
    refine mul_nonneg hC ?_
    refine pow_nonneg ?_ M
    exact inv_nonneg.2 (le_of_lt hh.1)
  calc
    ‖dtdτ α β a h t τ‖
        ≤ C * (h⁻¹) ^ M * japaneseBracket τ ^ (m₁ - (β : ℝ)) := hmain
    _ ≤ C * (h⁻¹) ^ M * japaneseBracket τ ^ (m₂ - (β : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hwt hfac

/-- The symbol `(t,τ) ↦ h^j` has order `0` in `S^0_λ` provided `h0 ≤ 1`. -/
theorem hpow (hh0 : h0 ≤ 1) (j : ℕ) :
    SmLambda Y h0 (0 : ℝ) (fun h _ _ => (h ^ j : ℂ)) := by
  classical
  intro α β
  refine ⟨1, 0, by simp, ?_⟩
  intro h hh t ht τ
  cases α with
  | zero =>
      cases β with
      | zero =>
          have hle1 : h ≤ 1 := le_trans hh.2 hh0
          have hnonneg : 0 ≤ h := le_of_lt hh.1
          have hpow_le : h ^ j ≤ 1 := pow_le_one j hnonneg hle1
          have hpow_nonneg : 0 ≤ h ^ j := pow_nonneg hnonneg j
          have hnorm : ‖(h ^ j : ℂ)‖ = Real.abs (h ^ j) := by simp
          have habs : Real.abs (h ^ j) = h ^ j := by simpa [Real.abs_of_nonneg hpow_nonneg]
          -- RHS is `1` since `M=0`, `m=0`, `α=β=0`.
          simpa [dtdτ, hnorm, habs] using hpow_le
      | succ β' =>
          -- any τ-derivative is zero
          simp [dtdτ]
  | succ α' =>
      -- any t-derivative is zero
      simp [dtdτ]

end SmLambda

namespace Parametrix

variable {Y : Set ℝ} {h0 m : ℝ}
variable {b : ℕ → ℝ → ℝ → ℝ → ℂ}
variable (N : ℕ)

/-- If `b_j ∈ S^{-m-j}_λ` for all `j`, then `bTrunc b N ∈ S^{-m}_λ`. -/
theorem bTrunc_mem_SmLambda (hh0 : h0 ≤ 1)
    (hb : ∀ j : ℕ, SmLambda Y h0 (-m - (j : ℝ)) (b j)) :
    SmLambda Y h0 (-m) (bTrunc b N) := by
  classical
  -- each summand has order `-m`
  have hterm : ∀ j : ℕ, j ∈ Finset.range N →
      SmLambda Y h0 (-m) (fun h t τ => (h ^ j : ℂ) * b j h t τ) := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
    have hmj : (-m - (j : ℝ)) ≤ (-m) := by linarith
    have hb' : SmLambda Y h0 (-m) (b j) := SmLambda.mono_order (Y := Y) (h0 := h0)
      (m₁ := -m - (j : ℝ)) (m₂ := -m) (a := b j) hmj (hb j)
    have hhj : SmLambda Y h0 (0 : ℝ) (fun h _ _ => (h ^ j : ℂ)) :=
      SmLambda.hpow (Y := Y) (h0 := h0) (hh0 := hh0) j
    -- product has order `0 + (-m) = -m`
    simpa [zero_add] using (SmLambda.mul (Y := Y) (h0 := h0) (hh0 := hh0) hhj hb')
  -- sum of finitely many `S^{-m}` symbols stays in `S^{-m}`
  have hsum : SmLambda Y h0 (-m)
      (fun h t τ => ∑ j in Finset.range N, (h ^ j : ℂ) * b j h t τ) :=
    SmLambda.sum (Y := Y) (h0 := h0) (m := -m) (hh0 := hh0)
      (s := Finset.range N) (f := fun j => fun h t τ => (h ^ j : ℂ) * b j h t τ) hterm
  simpa [bTrunc] using hsum

end Parametrix

end TwoChartEgorov

/-- Convenience wrapper: build `bTrunc` as an `S^{-m}_λ` symbol from the recursion hypotheses
via `Parametrix.coeff_mem_SmLambda`. -/
theorem bTrunc_mem_SmLambda_of_rec
    {Y : Set ℝ} {h0 m : ℝ}
    {a b0 : ℝ → ℝ → ℝ → ℂ}
    {b : ℕ → ℝ → ℝ → ℝ → ℂ}
    (hh0 : h0 ≤ 1)
    (ha : TwoChartEgorov.SmLambda Y h0 m a)
    (haComm : TwoChartEgorov.MixedComm a)
    (hb0 : TwoChartEgorov.SmLambda Y h0 (-m) b0)
    (hbRec : TwoChartEgorov.ParametrixRec a b0 b)
    (hbComm : ∀ j : ℕ, TwoChartEgorov.MixedComm (b j))
    (N : ℕ) :
    TwoChartEgorov.SmLambda Y h0 (-m) (TwoChartEgorov.bTrunc b N) := by
  -- First obtain the full coefficient family bounds.
  have hb : ∀ j : ℕ, TwoChartEgorov.SmLambda Y h0 (-m - (j : ℝ)) (b j) :=
    TwoChartEgorov.Parametrix.coeff_mem_SmLambda (Y:=Y) (h0:=h0) (m:=m) (a:=a)
      (b0:=b0) (b:=b) hh0 ha haComm hb0 hbRec hbComm
  -- Then sum the finitely many terms.
  exact TwoChartEgorov.Parametrix.bTrunc_mem_SmLambda (Y:=Y) (h0:=h0) (m:=m)
    (b:=b) (N:=N) hh0 hb
