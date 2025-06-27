theorem test_simple : 2 + 2 = 4 := by
  rfl

theorem test_nat_le : ∀ n : Nat, n ≤ n + 1 := by
  sorry

theorem test_implication : ∀ (p q : Prop), p → (q → p) := by
  sorry
