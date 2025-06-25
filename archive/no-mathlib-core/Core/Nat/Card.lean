/-
  Nat.Card
  --------
  Elementary counting lemmas for finite types.
  Using mathlib4 for standard results.

  Author: Jonathan Washburn
  Recognition Science Institute
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Basic

namespace RecognitionScience.Nat.Card

/-- There is no injection from Fin (n+1) to Fin n -/
theorem no_inj_succ_to_self {n : Nat} (f : Fin (n + 1) → Fin n) : ¬Function.Injective f := by
  intro h_inj
  -- Use the fact that an injective function preserves cardinality inequalities
  have : Fintype.card (Fin (n + 1)) ≤ Fintype.card (Fin n) := Fintype.card_le_of_injective f h_inj
  -- But card (Fin (n+1)) = n+1 and card (Fin n) = n
  simp [Fintype.card_fin] at this
  -- So we have n + 1 ≤ n, which is false
  exact Nat.not_succ_le_self n this

/-- If Fin n is in bijection with Fin m, then n = m -/
theorem bij_fin_eq {n m : Nat} (h : Fin n ≃ Fin m) : n = m := by
  -- Bijections preserve cardinality
  have : Fintype.card (Fin n) = Fintype.card (Fin m) := Fintype.card_congr h
  -- card (Fin n) = n and card (Fin m) = m
  simp [Fintype.card_fin] at this
  exact this

end RecognitionScience.Nat.Card
