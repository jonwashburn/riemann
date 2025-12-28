/******************************************************************************
  Step 3 (next step): Weyl/Moyal bidifferential coefficients `Pₙ`.

  Context (paper): equation (2.9) defines `Pₙ(c,d)` via a finite sum of products of
  mixed derivatives of `c` and `d`. These coefficients are the algebraic heart of the
  semiclassical symbol calculus:

    c # d = Σ_{n=0}^{N-1} h^n Pₙ(c,d) + h^N R_N.

  This file stays purely at the symbol level (no oscillatory integrals yet) and
  implements the precise bookkeeping statement needed repeatedly later:

    if c ∈ S^{m₁}_λ and d ∈ S^{m₂}_λ, and mixed partials commute (a stand-in for the
    `C^∞` hypothesis of the paper), then Pₙ(c,d) ∈ S^{m₁+m₂-n}_λ.

  It also supplies the missing basic API lemmas for `S^m_λ`:
    • `0`, addition, scalar multiplication,
    • finite sums,
    • stability under taking mixed derivatives.

  No axioms, no placeholders, no `sorry`.
*******************************************************************************/

import TwoChart_SmLambda

import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace TwoChartEgorov

/-! ### Mixed-derivative commutation/additivity

The paper assumes `a_h ∈ C^∞(T^*Y)`; in particular all mixed partial derivatives commute, and
one can freely regroup mixed derivatives:

`∂_t^α ∂_τ^β (∂_t^{a0} ∂_τ^{b0} a) = ∂_t^{α+a0} ∂_τ^{β+b0} a`.

Our low-level operator `dtdτ` is implemented via nested `iteratedDeriv` (τ-then-t).  In order to
carry out the symbol calculus (Moyal coefficients, parametrix recursion), we need the above
regrouping property as an explicit hypothesis.

In a later refinement, this hypothesis should be *derived* from a smoothness layer
(`ContDiffOn` on `Y×ℝ`) using Mathlib's Clairaut/Schwarz theorems.
-/

/-- Regrouping law for mixed derivatives, expressing commutation of mixed partials.

This is the formal hypothesis needed to treat the nested `dtdτ` as genuine mixed partials.
-/
def MixedComm (a : ℝ → ℝ → ℝ → ℂ) : Prop :=
  ∀ (h t τ : ℝ) (α β a0 b0 : ℕ),
    TwoChartEgorov.dtdτ α β (fun h t τ => TwoChartEgorov.dtdτ a0 b0 a h t τ) h t τ =
      TwoChartEgorov.dtdτ (α + a0) (β + b0) a h t τ

namespace SmLambda

variable {Y : Set ℝ} {h0 : ℝ} {m m₁ m₂ : ℝ}
variable {a b : ℝ → ℝ → ℝ → ℂ}

/-- The zero symbol belongs to every `S^m_λ`. -/
theorem zero : TwoChartEgorov.SmLambda Y h0 m (fun _ _ _ => (0 : ℂ)) := by
  intro α β
  refine ⟨0, 0, by simp, ?_⟩
  intro h hh t ht τ
  simp [TwoChartEgorov.dtdτ]

/-- Addition stability for `S^m_λ` at fixed order.

We assume `h0 ≤ 1` so that for `h ∈ (0,h0]` we have `1 ≤ h⁻¹`, which makes the map
`M ↦ (h⁻¹)^M` monotone and allows us to unify the polynomial losses.
-/
theorem add
    (hh0 : h0 ≤ 1)
    (ha : TwoChartEgorov.SmLambda Y h0 m a)
    (hb : TwoChartEgorov.SmLambda Y h0 m b) :
    TwoChartEgorov.SmLambda Y h0 m (fun h t τ => a h t τ + b h t τ) := by
  classical
  choose Ca Ma hA using ha
  choose Cb Mb hB using hb
  have hCa_nonneg : ∀ α β, 0 ≤ Ca α β := fun α β => (hA α β).1
  have hCb_nonneg : ∀ α β, 0 ≤ Cb α β := fun α β => (hB α β).1

  intro α β
  let M : ℕ := max (Ma α β) (Mb α β)
  let C : ℝ := Ca α β + Cb α β
  refine ⟨C, M, ?_, ?_⟩
  · nlinarith [hCa_nonneg α β, hCb_nonneg α β]
  · intro h hh t ht τ
    have h1 : (1 : ℝ) ≤ h⁻¹ := one_le_inv_of_mem_Ioc (Y:=Y) (h0:=h0) hh0 hh
    have hpowA : (h⁻¹) ^ (Ma α β) ≤ (h⁻¹) ^ M := by
      apply pow_inv_mono_of_one_le (h:=h) h1
      exact le_max_left _ _
    have hpowB : (h⁻¹) ^ (Mb α β) ≤ (h⁻¹) ^ M := by
      apply pow_inv_mono_of_one_le (h:=h) h1
      exact le_max_right _ _
    have hwt_nonneg : 0 ≤ (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) := by
      exact Real.rpow_nonneg (TwoChartEgorov.japaneseBracket_nonneg τ) _
    have hAder := (hA α β).2 h hh t ht τ
    have hBder := (hB α β).2 h hh t ht τ
    calc
      ‖TwoChartEgorov.dtdτ α β (fun h t τ => a h t τ + b h t τ) h t τ‖
          = ‖TwoChartEgorov.dtdτ α β a h t τ + TwoChartEgorov.dtdτ α β b h t τ‖ := by
            -- linearity of iterated derivatives
            simp [TwoChartEgorov.dtdτ, iteratedDeriv_add]
      _ ≤ ‖TwoChartEgorov.dtdτ α β a h t τ‖ + ‖TwoChartEgorov.dtdτ α β b h t τ‖ := by
            simpa using norm_add_le _ _
      _ ≤ Ca α β * (h⁻¹) ^ (Ma α β) * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) +
            Cb α β * (h⁻¹) ^ (Mb α β) * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) := by
            nlinarith [hAder, hBder]
      _ ≤ Ca α β * (h⁻¹) ^ M * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) +
            Cb α β * (h⁻¹) ^ M * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) := by
            have hCa : 0 ≤ Ca α β := hCa_nonneg α β
            have hCb : 0 ≤ Cb α β := hCb_nonneg α β
            have hA' : Ca α β * (h⁻¹) ^ (Ma α β) * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) ≤
                Ca α β * (h⁻¹) ^ M * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) := by
              have := mul_le_mul_of_nonneg_left hpowA (mul_nonneg hCa hwt_nonneg)
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
            have hB' : Cb α β * (h⁻¹) ^ (Mb α β) * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) ≤
                Cb α β * (h⁻¹) ^ M * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) := by
              have := mul_le_mul_of_nonneg_left hpowB (mul_nonneg hCb hwt_nonneg)
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
            nlinarith [hA', hB']
      _ = (Ca α β + Cb α β) * (h⁻¹) ^ M * (TwoChartEgorov.japaneseBracket τ) ^ (m - (β : ℝ)) := by
            ring

/-- Constant scalar multiplication stability for `S^m_λ`.

We pull the constant out of mixed iterated derivatives using the corresponding
Mathlib linearity lemmas for `iteratedDeriv`.
-/
/-! ### Scalar multiplication via multiplication by a constant symbol

To avoid relying on a particular lemma name for linearity of `iteratedDeriv`, we treat
scalar multiplication as a special case of the already-proved multiplication closure
(`TwoChart_SmLambda.lean`, Remark 3.3): multiply by the constant symbol `(t,τ) ↦ c`.

This is also the most robust approach when later generalizing the calculus to
`NormedRing`-valued symbols.
-/

/-- The constant symbol `c` is a (λ-dependent) symbol of order `0`. -/
theorem const (c : ℂ) : TwoChartEgorov.SmLambda Y h0 (0 : ℝ) (fun _ _ _ => c) := by
  classical
  intro α β
  refine ⟨‖c‖, 0, by simp, ?_⟩
  intro h hh t ht τ
  -- Case split on the mixed derivative order.
  cases α with
  | zero =>
      cases β with
      | zero =>
          -- `dtdτ 0 0` is the identity.
          simp [TwoChartEgorov.dtdτ]
      | succ β' =>
          -- Any positive τ-derivative of a constant is 0.
          have hR : (0 : ℝ) ≤ ‖c‖ * (h⁻¹) ^ (0 : ℕ) *
              (TwoChartEgorov.japaneseBracket τ) ^ ((0 : ℝ) - ((Nat.succ β' : ℕ) : ℝ)) := by
            have : 0 ≤ (TwoChartEgorov.japaneseBracket τ) ^ ((0 : ℝ) - ((Nat.succ β' : ℕ) : ℝ)) := by
              exact Real.rpow_nonneg (TwoChartEgorov.japaneseBracket_nonneg τ) _
            nlinarith [norm_nonneg c, this]
          -- `simp` reduces the LHS to `0`.
          simpa [TwoChartEgorov.dtdτ] using hR
  | succ α' =>
      -- Any positive t-derivative of a constant is 0.
      have hR : (0 : ℝ) ≤ ‖c‖ * (h⁻¹) ^ (0 : ℕ) *
          (TwoChartEgorov.japaneseBracket τ) ^ ((0 : ℝ) - (β : ℝ)) := by
        have : 0 ≤ (TwoChartEgorov.japaneseBracket τ) ^ ((0 : ℝ) - (β : ℝ)) := by
          exact Real.rpow_nonneg (TwoChartEgorov.japaneseBracket_nonneg τ) _
        nlinarith [norm_nonneg c, this]
      simpa [TwoChartEgorov.dtdτ] using hR

/-- Scalar multiplication stability for `S^m_λ` (implemented via multiplication by a constant symbol). -/
theorem const_mul (hh0 : h0 ≤ 1) (c : ℂ) (ha : TwoChartEgorov.SmLambda Y h0 m a) :
    TwoChartEgorov.SmLambda Y h0 m (fun h t τ => c * a h t τ) := by
  -- `c` has order 0, so multiplying preserves order.
  have hc : TwoChartEgorov.SmLambda Y h0 (0 : ℝ) (fun _ _ _ => c) := const (Y:=Y) (h0:=h0) c
  -- Apply multiplication closure.
  simpa [zero_add] using
    (SmLambda.mul (Y:=Y) (h0:=h0) (m₁:=(0 : ℝ)) (m₂:=m)
      (a:=fun _ _ _ => c) (b:=a) hh0 hc ha)

/-- Finite sum stability for `S^m_λ`.

This is the induction principle used to pass from termwise bounds to bounds on
explicit finite combinations such as `Pₙ`.
-/
theorem sum
    (hh0 : h0 ≤ 1)
    {ι : Type*} (s : Finset ι) (f : ι → (ℝ → ℝ → ℝ → ℂ))
    (hf : ∀ i ∈ s, TwoChartEgorov.SmLambda Y h0 m (f i)) :
    TwoChartEgorov.SmLambda Y h0 m (fun h t τ => ∑ i in s, f i h t τ) := by
  classical
  -- Induction with a strengthened statement that carries the membership hypothesis.
  refine (Finset.induction_on s
    (p := fun s => (∀ i ∈ s, TwoChartEgorov.SmLambda Y h0 m (f i)) →
      TwoChartEgorov.SmLambda Y h0 m (fun h t τ => ∑ i in s, f i h t τ))
    ?base ?step) hf
  · intro _
    simpa using (zero (Y:=Y) (h0:=h0) (m:=m))
  · intro i s hi ih hf'
    have hfi : TwoChartEgorov.SmLambda Y h0 m (f i) := hf' i (by simp [hi])
    have hfs : ∀ j ∈ s, TwoChartEgorov.SmLambda Y h0 m (f j) := by
      intro j hj
      exact hf' j (by simp [hj, hi])
    have ihs : TwoChartEgorov.SmLambda Y h0 m (fun h t τ => ∑ j in s, f j h t τ) := ih hfs
    have hadd := add (Y:=Y) (h0:=h0) (m:=m) hh0 hfi ihs
    simpa [Finset.sum_insert, hi, add_comm, add_left_comm, add_assoc] using hadd

/-- Iterated-derivative composition in one variable.

This lemma is available in Mathlib as `iteratedDeriv_iteratedDeriv`.
We keep it as a local lemma to make later proofs more readable.
-/
lemma iteratedDeriv_iteratedDeriv' {f : ℝ → ℂ} (n m : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => iteratedDeriv m f y) x = iteratedDeriv (n + m) f x := by
  simpa using (iteratedDeriv_iteratedDeriv n m f x)

/-- Mixed-derivative stability: taking `∂_t^{a0} ∂_τ^{b0}` lowers the order by `b0`.

This is the order-shift mechanism used repeatedly in the Moyal coefficients.
-/
theorem dtdτ_mem (a0 b0 : ℕ)
    (ha : TwoChartEgorov.SmLambda Y h0 m a)
    (hcomm : TwoChartEgorov.MixedComm a) :
    TwoChartEgorov.SmLambda Y h0 (m - (b0 : ℝ)) (fun h t τ => TwoChartEgorov.dtdτ a0 b0 a h t τ) := by
  classical
  intro α β
  rcases ha (α + a0) (β + b0) with ⟨C, M, hC, hbound⟩
  refine ⟨C, M, hC, ?_⟩
  intro h hh t ht τ
  have hmain := hbound (h:=h) hh (t:=t) ht τ
  have hderiv :
      TwoChartEgorov.dtdτ α β (fun h t τ => TwoChartEgorov.dtdτ a0 b0 a h t τ) h t τ =
        TwoChartEgorov.dtdτ (α + a0) (β + b0) a h t τ := by
    simpa using (hcomm h t τ α β a0 b0)
  have hexp : m - ((β + b0 : ℕ) : ℝ) = (m - (b0 : ℝ)) - (β : ℝ) := by
    nlinarith
  simpa [hderiv, hexp] using hmain

end SmLambda

/-- The Weyl/Moyal bidifferential coefficient `Pₙ(c,d)` (paper (2.9)).

In 1D we parameterize the sum by `α ∈ {0,…,n}` and set `β = n-α`.
-/
def Pn (n : ℕ) (c d : ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℂ :=
  fun h t τ =>
    ∑ α in Finset.range (n + 1),
      ((1 : ℂ) / (Nat.factorial n : ℂ)) * ((Complex.I / 2) ^ n) *
        (let β : ℕ := n - α
         ((-1 : ℂ) ^ β) * (Nat.choose n α : ℂ) *
           TwoChartEgorov.dtdτ β α c h t τ *
           TwoChartEgorov.dtdτ α β d h t τ)

namespace Pn

variable {Y : Set ℝ} {h0 : ℝ} {m₁ m₂ : ℝ}
variable {c d : ℝ → ℝ → ℝ → ℂ}

/-- Main mapping property of `Pₙ` on λ-dependent symbols (paper-level bookkeeping).

If `c ∈ S^{m₁}_λ` and `d ∈ S^{m₂}_λ`, and mixed derivatives commute (captured by
`MixedComm`, a formal proxy for the `C^∞` assumption in the paper), then
`Pₙ(c,d) ∈ S^{m₁+m₂-n}_λ`.
-/
theorem mem_SmLambda
    (hh0 : h0 ≤ 1)
    (hc : TwoChartEgorov.SmLambda Y h0 m₁ c)
    (hcComm : TwoChartEgorov.MixedComm c)
    (hd : TwoChartEgorov.SmLambda Y h0 m₂ d)
    (hdComm : TwoChartEgorov.MixedComm d) (n : ℕ) :
    TwoChartEgorov.SmLambda Y h0 (m₁ + m₂ - (n : ℝ)) (TwoChartEgorov.Pn n c d) := by
  classical

  -- Termwise membership for each `α`.
  have hterm :
      ∀ α ∈ Finset.range (n + 1),
        TwoChartEgorov.SmLambda Y h0 (m₁ + m₂ - (n : ℝ))
          (fun h t τ =>
            ((1 : ℂ) / (Nat.factorial n : ℂ)) * ((Complex.I / 2) ^ n) *
              (let β : ℕ := n - α
               ((-1 : ℂ) ^ β) * (Nat.choose n α : ℂ) *
                 TwoChartEgorov.dtdτ β α c h t τ *
                 TwoChartEgorov.dtdτ α β d h t τ)) := by
    intro α hα
    -- let β = n-α
    set β : ℕ := n - α

    -- derivative shifts
    have hc' : TwoChartEgorov.SmLambda Y h0 (m₁ - (α : ℝ))
        (fun h t τ => TwoChartEgorov.dtdτ β α c h t τ) := by
      simpa [β] using
        (SmLambda.dtdτ_mem (Y:=Y) (h0:=h0) (m:=m₁) (a:=c) β α hc hcComm)
    have hd' : TwoChartEgorov.SmLambda Y h0 (m₂ - (β : ℝ))
        (fun h t τ => TwoChartEgorov.dtdτ α β d h t τ) := by
      simpa [β] using
        (SmLambda.dtdτ_mem (Y:=Y) (h0:=h0) (m:=m₂) (a:=d) α β hd hdComm)

    -- multiply them (Remark 3.3)
    have hmul : TwoChartEgorov.SmLambda Y h0 ((m₁ - (α : ℝ)) + (m₂ - (β : ℝ)))
        (fun h t τ => TwoChartEgorov.dtdτ β α c h t τ * TwoChartEgorov.dtdτ α β d h t τ) := by
      simpa [mul_assoc] using
        (SmLambda.mul (Y:=Y) (h0:=h0) (m₁:=m₁ - (α : ℝ)) (m₂:=m₂ - (β : ℝ))
          (a:=fun h t τ => TwoChartEgorov.dtdτ β α c h t τ)
          (b:=fun h t τ => TwoChartEgorov.dtdτ α β d h t τ)
          hh0 hc' hd')

    -- simplify the resulting order to `m₁+m₂-n`
    have hαle : α ≤ n := by
      exact Nat.le_of_lt_succ (Finset.mem_range.1 hα)
    have hab : α + β = n := by
      -- β = n-α
      simp [β, Nat.add_sub_of_le hαle]
    have horder : (m₁ - (α : ℝ)) + (m₂ - (β : ℝ)) = (m₁ + m₂ - (n : ℝ)) := by
      have hab' : (α : ℝ) + (β : ℝ) = (n : ℝ) := by
        exact_mod_cast hab
      nlinarith [hab']

    -- scalar coefficients do not change order
    have hcoeff1 : TwoChartEgorov.SmLambda Y h0 (m₁ + m₂ - (n : ℝ))
        (fun h t τ =>
          ((-1 : ℂ) ^ β) * (Nat.choose n α : ℂ) *
            (TwoChartEgorov.dtdτ β α c h t τ * TwoChartEgorov.dtdτ α β d h t τ)) := by
      -- combine the two scalar factors by repeated `const_mul`
      have h0' : TwoChartEgorov.SmLambda Y h0 (m₁ + m₂ - (n : ℝ))
          (fun h t τ => TwoChartEgorov.dtdτ β α c h t τ * TwoChartEgorov.dtdτ α β d h t τ) := by
        simpa [horder] using hmul
      have h1 := SmLambda.const_mul (Y:=Y) (h0:=h0) (m:=m₁ + m₂ - (n : ℝ)) hh0
          (Nat.choose n α : ℂ)
          (a:=fun h t τ => TwoChartEgorov.dtdτ β α c h t τ * TwoChartEgorov.dtdτ α β d h t τ)
          h0'
      have h2 := SmLambda.const_mul (Y:=Y) (h0:=h0) (m:=m₁ + m₂ - (n : ℝ)) hh0
          ((-1 : ℂ) ^ β)
          (a:=fun h t τ => (Nat.choose n α : ℂ) *
            (TwoChartEgorov.dtdτ β α c h t τ * TwoChartEgorov.dtdτ α β d h t τ))
          h1
      -- tidy
      simpa [mul_assoc, mul_left_comm, mul_comm] using h2

    have hcoeff2 := SmLambda.const_mul (Y:=Y) (h0:=h0) (m:=m₁ + m₂ - (n : ℝ)) hh0
        (((1 : ℂ) / (Nat.factorial n : ℂ)) * ((Complex.I / 2) ^ n))
        (a:=fun h t τ =>
          ((-1 : ℂ) ^ β) * (Nat.choose n α : ℂ) *
            (TwoChartEgorov.dtdτ β α c h t τ * TwoChartEgorov.dtdτ α β d h t τ))
        hcoeff1

    -- final rearrangement to match the term's exact shape
    simpa [β, mul_assoc, mul_left_comm, mul_comm] using hcoeff2

  -- Now use finite-sum stability.
  have hsum : TwoChartEgorov.SmLambda Y h0 (m₁ + m₂ - (n : ℝ))
      (fun h t τ =>
        ∑ α in Finset.range (n + 1),
          ((1 : ℂ) / (Nat.factorial n : ℂ)) * ((Complex.I / 2) ^ n) *
            (let β : ℕ := n - α
             ((-1 : ℂ) ^ β) * (Nat.choose n α : ℂ) *
               TwoChartEgorov.dtdτ β α c h t τ *
               TwoChartEgorov.dtdτ α β d h t τ)) := by
    -- apply `SmLambda.sum` with the termwise hypothesis `hterm`
    refine SmLambda.sum (Y:=Y) (h0:=h0) (m:=m₁ + m₂ - (n : ℝ)) hh0 (Finset.range (n + 1))
      (fun α =>
        fun h t τ =>
          ((1 : ℂ) / (Nat.factorial n : ℂ)) * ((Complex.I / 2) ^ n) *
            (let β : ℕ := n - α
             ((-1 : ℂ) ^ β) * (Nat.choose n α : ℂ) *
               TwoChartEgorov.dtdτ β α c h t τ *
               TwoChartEgorov.dtdτ α β d h t τ)) ?_
    intro α hα
    simpa using hterm α hα

  -- Finally, rewrite to the definition of `Pn`.
  simpa [TwoChartEgorov.Pn] using hsum

end Pn

end TwoChartEgorov
