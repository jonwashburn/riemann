import Riemann.Semiclassical.Defs

open scoped BigOperators
/-
  Step 2 (prerequisite layer): standard semiclassical symbols `S^m` and their
  relationship to the λ-dependent symbol class `S^m_λ`.

  Paper correspondence:
    • Definition 3.1  -> `Sm`
    • The inclusion S^m ⊆ S^m_λ (choose exponent M=0)
    • Stability of S^m under multiplication (nontrivial Leibniz/seminorm bookkeeping)

  No axioms, no placeholders, no `sorry`.
-/
namespace TwoChartEgorov

/-- Standard semiclassical symbol class `S^m(T*Y)` (paper Definition 3.1).

This is the `h`-uniform variant of `SmLambda`: the derivative bounds do *not* allow any
polynomial loss in `h⁻¹`.

We work in the same 1D setting as the paper: `t ∈ Y ⊆ ℝ`, `τ ∈ ℝ`.
-/
def Sm (Y : Set ℝ) (h0 m : ℝ) (a : ℝ → ℝ → ℝ → ℂ) : Prop :=
  (∀ h : ℝ, ContDiff ℝ ⊤ (fun p : ℝ × ℝ => a h p.1 p.2)) ∧
    ∀ α β : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ ⦃h : ℝ⦄, h ∈ Set.Ioc (0 : ℝ) h0 →
          ∀ ⦃t : ℝ⦄, t ∈ Y →
            ∀ τ : ℝ,
              ‖TwoChartEgorov.dtdτ α β a h t τ‖ ≤
                C * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ))

namespace Sm

variable {Y : Set ℝ} {h0 : ℝ} {m m₁ m₂ : ℝ}
variable {a b : ℝ → ℝ → ℝ → ℂ}

/-- `S^m ⊆ S^m_λ` by taking the polynomial exponent `M=0`.

This is the exact formal analogue of the remark in §3 of the paper that the λ-dependent
symbol class only weakens the uniform-in-h bounds by allowing polynomial losses.
-/
theorem toSmLambda (ha : Sm Y h0 m a) : TwoChartEgorov.SmLambda Y h0 m a := by
  refine ⟨ha.1, ?_⟩
  intro α β
  rcases ha.2 α β with ⟨C, hC, hbound⟩
  refine ⟨C, 0, hC, ?_⟩
  intro h hh t ht τ
  -- `(h⁻¹)^0 = 1`.
  simpa using (by
    have := hbound (h := h) hh (t := t) ht τ
    simpa using this)

/-- Pointwise multiplication stability for standard symbols:

If `a ∈ S^{m₁}` and `b ∈ S^{m₂}`, then `a*b ∈ S^{m₁+m₂}`.

This is the nontrivial Leibniz bookkeeping analogue of Remark 3.3 in the paper, but in the
`h`-uniform setting (no polynomial losses).
-/
theorem mul
    (ha : Sm Y h0 m₁ a)
    (hb : Sm Y h0 m₂ b) :
    Sm Y h0 (m₁ + m₂) (fun h t τ => a h t τ * b h t τ) := by
  classical
  refine ⟨?_, ?_⟩
  · intro h
    exact (ha.1 h).mul (hb.1 h)
  -- Choose witnesses globally.
  choose Ca hCa using ha.2
  choose Cb hCb using hb.2
  have hCa_nonneg : ∀ α β, 0 ≤ Ca α β := fun α β => (hCa α β).1
  have hCb_nonneg : ∀ α β, 0 ≤ Cb α β := fun α β => (hCb α β).1
  have hboundA :
      ∀ α β ⦃h : ℝ⦄, h ∈ Set.Ioc (0 : ℝ) h0 →
        ∀ ⦃t : ℝ⦄, t ∈ Y →
          ∀ τ : ℝ,
            ‖TwoChartEgorov.dtdτ α β a h t τ‖ ≤ Ca α β * (TwoChartEgorov.japaneseBracket τ) ^ (m₁ - (β : ℝ)) :=
    fun α β {h} hh {t} ht τ => (hCa α β).2 hh ht τ
  have hboundB :
      ∀ α β ⦃h : ℝ⦄, h ∈ Set.Ioc (0 : ℝ) h0 →
        ∀ ⦃t : ℝ⦄, t ∈ Y →
          ∀ τ : ℝ,
            ‖TwoChartEgorov.dtdτ α β b h t τ‖ ≤ Cb α β * (TwoChartEgorov.japaneseBracket τ) ^ (m₂ - (β : ℝ)) :=
    fun α β {h} hh {t} ht τ => (hCb α β).2 hh ht τ

  intro α β

  -- Double Leibniz index set: i ∈ [0..α], j ∈ [0..β].
  let I : Finset (ℕ × ℕ) :=
    (Finset.range (α + 1)).product (Finset.range (β + 1))

  -- Constant for each term and the sum constant.
  let constTerm : (ℕ × ℕ) → ℝ := fun p =>
    (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) * (Ca p.1 p.2) * (Cb (α - p.1) (β - p.2))
  let C : ℝ := I.sum constTerm

  refine ⟨C, ?_, ?_⟩
  · -- C ≥ 0
    refine Finset.sum_nonneg ?_
    intro p hp
    have hCa' : 0 ≤ Ca p.1 p.2 := hCa_nonneg p.1 p.2
    have hCb' : 0 ≤ Cb (α - p.1) (β - p.2) := hCb_nonneg (α - p.1) (β - p.2)
    have hchooseA : 0 ≤ (Nat.choose α p.1 : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have hchooseB : 0 ≤ (Nat.choose β p.2 : ℝ) := by exact_mod_cast (Nat.zero_le _)
    have : 0 ≤ (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) * Ca p.1 p.2 *
        Cb (α - p.1) (β - p.2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hchooseA hchooseB) hCa') hCb'
    simpa [constTerm, mul_assoc] using this
  · intro h hh t ht τ
    -- (1) Leibniz expansion.
    have hLeib :
        TwoChartEgorov.dtdτ α β (fun h t τ => a h t τ * b h t τ) h t τ =
          ∑ p ∈ I,
            (Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              TwoChartEgorov.dtdτ p.1 p.2 a h t τ *
              TwoChartEgorov.dtdτ (α - p.1) (β - p.2) b h t τ := by
      -- Reuse the mixed Leibniz formula from `TwoChartEgorov.SmLambda`.
      simpa [I] using
        (TwoChartEgorov.SmLambda.dtdτ_mul (a := a) (b := b) (h := h) (ha := ha.1 h) (hb := hb.1 h)
          α β t τ)

    -- (2) `‖Σ‖ ≤ Σ ‖·‖`.
    have hnorm_sum :
        ‖TwoChartEgorov.dtdτ α β (fun h t τ => a h t τ * b h t τ) h t τ‖ ≤
          ∑ p ∈ I,
            ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              TwoChartEgorov.dtdτ p.1 p.2 a h t τ *
              TwoChartEgorov.dtdτ (α - p.1) (β - p.2) b h t τ‖ := by
      simpa [hLeib] using (norm_sum_le I
        (fun p => (Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
          TwoChartEgorov.dtdτ p.1 p.2 a h t τ *
          TwoChartEgorov.dtdτ (α - p.1) (β - p.2) b h t τ))

    -- (3) Termwise bounds.
    have hterm :
        ∀ p ∈ I,
          ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              TwoChartEgorov.dtdτ p.1 p.2 a h t τ *
              TwoChartEgorov.dtdτ (α - p.1) (β - p.2) b h t τ‖
            ≤ constTerm p * (TwoChartEgorov.japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
      intro p hp
      -- i ≤ α, j ≤ β from membership.
      have hj : p.2 ≤ β := by
        have : p.2 ∈ Finset.range (β + 1) := (Finset.mem_product.1 hp).2
        exact Nat.le_of_lt_succ (Finset.mem_range.1 this)

      have hAder := hboundA p.1 p.2 (h:=h) hh (t:=t) ht τ
      have hBder := hboundB (α - p.1) (β - p.2) (h:=h) hh (t:=t) ht τ

      -- Weight combination.
      have hbr_pos : 0 < TwoChartEgorov.japaneseBracket τ := TwoChartEgorov.japaneseBracket_pos τ
      have hnat : (p.2 + (β - p.2)) = β := Nat.add_sub_of_le hj
      have hcast : (p.2 : ℝ) + ((β - p.2 : ℕ) : ℝ) = (β : ℝ) := by
        exact_mod_cast hnat
      have hexp :
          (m₁ - (p.2 : ℝ)) + (m₂ - ((β - p.2 : ℕ) : ℝ)) = (m₁ + m₂) - (β : ℝ) := by
        nlinarith [hcast]
      have hweight :
          (TwoChartEgorov.japaneseBracket τ) ^ (m₁ - (p.2 : ℝ)) *
              (TwoChartEgorov.japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ))
            = (TwoChartEgorov.japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
        have := (Real.rpow_add hbr_pos (m₁ - (p.2 : ℝ)) (m₂ - ((β - p.2 : ℕ) : ℝ))).symm
        simpa [hexp, mul_assoc, mul_left_comm, mul_comm] using this

      -- Norm factorization.
      have hnorm_chooseA : ‖(Nat.choose α p.1 : ℂ)‖ = (Nat.choose α p.1 : ℝ) := by simp
      have hnorm_chooseB : ‖(Nat.choose β p.2 : ℂ)‖ = (Nat.choose β p.2 : ℝ) := by simp

      calc
        ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              TwoChartEgorov.dtdτ p.1 p.2 a h t τ *
              TwoChartEgorov.dtdτ (α - p.1) (β - p.2) b h t τ‖
            = (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) *
                ‖TwoChartEgorov.dtdτ p.1 p.2 a h t τ‖ *
                ‖TwoChartEgorov.dtdτ (α - p.1) (β - p.2) b h t τ‖ := by
              simp [mul_assoc]
        _ ≤ (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) *
              (Ca p.1 p.2 * (TwoChartEgorov.japaneseBracket τ) ^ (m₁ - (p.2 : ℝ))) *
              (Cb (α - p.1) (β - p.2) * (TwoChartEgorov.japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ))) := by
              have hA0 : 0 ≤ Ca p.1 p.2 * (TwoChartEgorov.japaneseBracket τ) ^ (m₁ - (p.2 : ℝ)) :=
                mul_nonneg (hCa_nonneg p.1 p.2)
                  (Real.rpow_nonneg (TwoChartEgorov.japaneseBracket_nonneg τ) _)
              have hB0 :
                  0 ≤ Cb (α - p.1) (β - p.2) *
                      (TwoChartEgorov.japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ)) :=
                mul_nonneg (hCb_nonneg (α - p.1) (β - p.2))
                  (Real.rpow_nonneg (TwoChartEgorov.japaneseBracket_nonneg τ) _)
              have hchooseA : 0 ≤ (Nat.choose α p.1 : ℝ) := by exact_mod_cast (Nat.zero_le _)
              have hchooseB : 0 ≤ (Nat.choose β p.2 : ℝ) := by exact_mod_cast (Nat.zero_le _)
              have hchooseAB : 0 ≤ (Nat.choose α p.1 : ℝ) * (Nat.choose β p.2 : ℝ) :=
                mul_nonneg hchooseA hchooseB
              have hmul_norm :
                  ‖TwoChartEgorov.dtdτ p.1 p.2 a h t τ‖ *
                      ‖TwoChartEgorov.dtdτ (α - p.1) (β - p.2) b h t τ‖
                    ≤
                    (Ca p.1 p.2 * (TwoChartEgorov.japaneseBracket τ) ^ (m₁ - (p.2 : ℝ))) *
                      (Cb (α - p.1) (β - p.2) *
                        (TwoChartEgorov.japaneseBracket τ) ^ (m₂ - ((β - p.2 : ℕ) : ℝ))) :=
                mul_le_mul hAder hBder (norm_nonneg _) hA0
              have hmul_total := mul_le_mul_of_nonneg_left hmul_norm hchooseAB
              simpa [mul_assoc] using hmul_total
        _ = constTerm p * (TwoChartEgorov.japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
              dsimp [constTerm]
              simp [mul_assoc, mul_left_comm, mul_comm, hweight]

    -- (4) Sum the termwise bounds and factor out the common weight.
    have hsum :
        (∑ p ∈ I,
          ‖(Nat.choose α p.1 : ℂ) * (Nat.choose β p.2 : ℂ) *
              TwoChartEgorov.dtdτ p.1 p.2 a h t τ *
              TwoChartEgorov.dtdτ (α - p.1) (β - p.2) b h t τ‖)
        ≤ C * (TwoChartEgorov.japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
      have := Finset.sum_le_sum (fun p hp => hterm p hp)
      have hfactor :
          (∑ p ∈ I, constTerm p * (TwoChartEgorov.japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)))
            = (∑ p ∈ I, constTerm p) * (TwoChartEgorov.japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ)) := by
        symm
        simpa [mul_assoc] using (Finset.sum_mul I (fun p => constTerm p)
          ((TwoChartEgorov.japaneseBracket τ) ^ ((m₁ + m₂) - (β : ℝ))))
      simpa [C, hfactor, mul_assoc, mul_left_comm, mul_comm] using this

    -- (5) Conclude.
    exact le_trans hnorm_sum hsum

end Sm

end TwoChartEgorov
